module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import CFSG.Quasithin.Background.G2SL2

public section

namespace CFSG.Quasithin.F112R.St84

open Matrix
open scoped commutatorElement

section Form

variable {F : Type*} [Field F] {C : Type*} [Group C]

private theorem form_eq_det (Λ : (Fin 2 → F) → (Fin 2 → F) → C)
    (hl : ∀ x x' y, Λ (x + x') y = Λ x y * Λ x' y)
    (hr : ∀ x y y', Λ x (y + y') = Λ x y * Λ x y')
    (halt : ∀ x, Λ x x = 1)
    (hinv : ∀ (g : SpecialLinearGroup (Fin 2) F) (x y : Fin 2 → F),
      Λ ((g : Matrix (Fin 2) (Fin 2) F) *ᵥ x) ((g : Matrix (Fin 2) (Fin 2) F) *ᵥ y) = Λ x y)
    (x y : Fin 2 → F) :
    Λ x y = Λ ![1, 0] ![0, x 0 * y 1 - x 1 * y 0] := by
  have hl0 : ∀ y, Λ 0 y = 1 := fun y => by
    have h := hl 0 0 y
    rw [add_zero] at h
    exact mul_left_cancel (h.symm.trans (mul_one _).symm)
  have hr0 : ∀ x, Λ x 0 = 1 := fun x => by
    have h := hr x 0 0
    rw [add_zero] at h
    exact mul_left_cancel (h.symm.trans (mul_one _).symm)
  have hanti : ∀ x y, Λ y x = (Λ x y)⁻¹ := fun x y => by
    refine eq_inv_of_mul_eq_one_right ?_
    have h := halt (x + y)
    rwa [hl, hr, hr, halt, halt, one_mul, mul_one] at h
  have hneg : ∀ t : F, Λ ![1, 0] ![0, -t] = (Λ ![1, 0] ![0, t])⁻¹ := fun t => by
    refine eq_inv_of_mul_eq_one_right ?_
    rw [← hr]
    convert hr0 ![1, 0] using 2
    ext i
    fin_cases i <;> simp
  have h11 : ∀ a b : F, Λ ![a, 0] ![b, 0] = 1 := fun a b => by
    let g : SpecialLinearGroup (Fin 2) F := ⟨!![1, b; 0, 1], by simp [det_fin_two]⟩
    have e1 : (g : Matrix (Fin 2) (Fin 2) F) *ᵥ ![a, 0] = ![a, 0] := by
      ext i
      fin_cases i <;> simp [g]
    have e2 : (g : Matrix (Fin 2) (Fin 2) F) *ᵥ ![0, 1] = ![b, 0] + ![0, 1] := by
      ext i
      fin_cases i <;> simp [g]
    have h := hinv g ![a, 0] ![0, 1]
    rw [e1, e2, hr] at h
    exact mul_eq_right.mp h
  have h22 : ∀ a b : F, Λ ![0, a] ![0, b] = 1 := fun a b => by
    let g : SpecialLinearGroup (Fin 2) F := ⟨!![1, 0; b, 1], by simp [det_fin_two]⟩
    have e1 : (g : Matrix (Fin 2) (Fin 2) F) *ᵥ ![0, a] = ![0, a] := by
      ext i
      fin_cases i <;> simp [g]
    have e2 : (g : Matrix (Fin 2) (Fin 2) F) *ᵥ ![1, 0] = ![1, 0] + ![0, b] := by
      ext i
      fin_cases i <;> simp [g]
    have h := hinv g ![0, a] ![1, 0]
    rw [e1, e2, hr] at h
    exact mul_eq_left.mp h
  have h12 : ∀ a b : F, Λ ![a, 0] ![0, b] = Λ ![1, 0] ![0, a * b] := fun a b => by
    by_cases ha : a = 0
    · have e1 : (![a, 0] : Fin 2 → F) = 0 := by
        ext i
        fin_cases i <;> simp [ha]
      have e2 : (![0, a * b] : Fin 2 → F) = 0 := by
        ext i
        fin_cases i <;> simp [ha]
      rw [e1, e2, hl0, hr0]
    · let g : SpecialLinearGroup (Fin 2) F := ⟨!![a⁻¹, 0; 0, a], by simp [det_fin_two, ha]⟩
      have e1 : (g : Matrix (Fin 2) (Fin 2) F) *ᵥ ![a, 0] = ![1, 0] := by
        ext i
        fin_cases i <;> simp [g, ha]
      have e2 : (g : Matrix (Fin 2) (Fin 2) F) *ᵥ ![0, b] = ![0, a * b] := by
        ext i
        fin_cases i <;> simp [g, mul_comm]
      rw [← hinv g ![a, 0] ![0, b], e1, e2]
  have hx : x = ![x 0, 0] + ![0, x 1] := by
    ext i
    fin_cases i <;> simp
  have hy : y = ![y 0, 0] + ![0, y 1] := by
    ext i
    fin_cases i <;> simp
  have hsplit : (![0, x 0 * y 1 - x 1 * y 0] : Fin 2 → F) =
      ![0, x 0 * y 1] + ![0, -(y 0 * x 1)] := by
    ext i
    fin_cases i <;> simp [sub_eq_add_neg, mul_comm]
  rw [hsplit, hr, hneg, ← h12 (y 0) (x 1), ← h12 (x 0) (y 1), ← hanti]
  conv_lhs => rw [hx, hy, hl, hr, hr, h11, h22, one_mul, mul_one]

end Form

section Commutator

variable {G : Type*} [Group G]

private lemma commutatorElement_mul_left_of_commute {a b z : G} (hb : Commute z b) :
    ⁅a * z, b⁆ = ⁅a, b⁆ := by
  calc ⁅a * z, b⁆ = a * (z * b * z⁻¹) * a⁻¹ * b⁻¹ := by group
    _ = ⁅a, b⁆ := by rw [hb.mul_inv_cancel]; group

private lemma commutatorElement_mul_right_of_commute {a b z : G} (ha : Commute z a) :
    ⁅a, b * z⁆ = ⁅a, b⁆ := by
  calc ⁅a, b * z⁆ = a * b * (z * a⁻¹ * z⁻¹) * b⁻¹ := by group
    _ = ⁅a, b⁆ := by rw [ha.inv_right.mul_inv_cancel]; group

private lemma commutatorElement_mul_left_eq {x y z : G} (h : Commute x ⁅y, z⁆) :
    ⁅x * y, z⁆ = ⁅y, z⁆ * ⁅x, z⁆ := by
  calc ⁅x * y, z⁆ = x * ⁅y, z⁆ * x⁻¹ * ⁅x, z⁆ := by group
    _ = ⁅y, z⁆ * ⁅x, z⁆ := by rw [h.mul_inv_cancel]

private lemma commutatorElement_mul_right_eq {x y z : G} (h : Commute y ⁅x, z⁆) :
    ⁅x, y * z⁆ = ⁅x, y⁆ * ⁅x, z⁆ := by
  calc ⁅x, y * z⁆ = ⁅x, y⁆ * (y * ⁅x, z⁆ * y⁻¹) := by group
    _ = ⁅x, y⁆ * ⁅x, z⁆ := by rw [h.mul_inv_cancel]

private lemma mul_mul_mul_self_of_commute {a b : G} (ha : Commute ⁅b, a⁆ a)
    (hb : Commute ⁅b, a⁆ b) : a * b * (a * b) = a * a * (b * b) * ⁅b, a⁆ := by
  have hab : Commute ⁅b, a⁆ (a * a * (b * b)) := (ha.mul_right ha).mul_right (hb.mul_right hb)
  calc a * b * (a * b) = a * ⁅b, a⁆ * a * b * b := by group
    _ = ⁅b, a⁆ * (a * a * (b * b)) := by rw [← ha.eq]; group
    _ = a * a * (b * b) * ⁅b, a⁆ := hab.eq

end Commutator

theorem exists_sq_eq_det {G : Type*} [Group G] {F : Type*} [Field F] [CharP F 2]
    {Q Z L : Subgroup G} (hZQ : Z ≤ Q)
    (hZc : Q ≤ Subgroup.centralizer (Z : Set G)) (hZ2 : ∀ z ∈ Z, z * z = 1)
    (hLQ : L ≤ Subgroup.normalizer (Q : Set G)) (hLZ : L ≤ Subgroup.centralizer (Z : Set G))
    (α : L →* SpecialLinearGroup (Fin 2) F) (hα : Function.Surjective α)
    (β : Q →* Multiplicative (Matrix (Fin 2) (Fin 2) F)) (hβ : Function.Surjective β)
    (hβker : β.ker = Z.subgroupOf Q)
    (hβconj : ∀ (ℓ : L) (u v : Q), (v : G) = ℓ * u * ℓ⁻¹ →
      Multiplicative.toAdd (β v) = (α ℓ : Matrix (Fin 2) (Fin 2) F) * Multiplicative.toAdd (β u))
    (v₀ : Fin 2 → F) (hv₀ : v₀ ≠ 0)
    (hpure : ∀ u : Q, (∃ m : Fin 2 → F, Multiplicative.toAdd (β u) = vecMulVec v₀ m) →
      (u : G) * u = 1) :
    ∃ ζ : Multiplicative F →* G, (∀ c, ζ c ∈ Z) ∧
      (∀ u : Q, (u : G) * u = ζ (Multiplicative.ofAdd (Multiplicative.toAdd (β u)).det)) ∧
      ∀ u v : Q, ⁅(u : G), (v : G)⁆ = ζ (Multiplicative.ofAdd
        ((Multiplicative.toAdd (β u) + Multiplicative.toAdd (β v)).det +
          (Multiplicative.toAdd (β u)).det + (Multiplicative.toAdd (β v)).det)) := by
  classical
  have hcomQ : ∀ q ∈ Q, ∀ z ∈ Z, Commute z q := fun q hq z hz =>
    Subgroup.mem_centralizer_iff.mp (hZc hq) z hz
  have hsqZ : ∀ u : Q, (u : G) * u ∈ Z := fun u => by
    have h : u * u ∈ β.ker := by
      rw [MonoidHom.mem_ker, map_mul]
      apply Multiplicative.toAdd.injective
      rw [toAdd_mul, toAdd_one]
      ext i j
      simp [CharTwo.add_self_eq_zero]
    rw [hβker, Subgroup.mem_subgroupOf] at h
    simpa using h
  have hcomZ : ∀ u v : Q, ⁅(u : G), (v : G)⁆ ∈ Z := fun u v => by
    have h : ⁅u, v⁆ ∈ β.ker := by
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm,
        mul_comm]
    rw [hβker, Subgroup.mem_subgroupOf] at h
    simpa [commutatorElement_def] using h
  obtain ⟨σ, hσ⟩ : ∃ σ : Matrix (Fin 2) (Fin 2) F → Q, ∀ A, β (σ A) = Multiplicative.ofAdd A :=
    ⟨fun A => Function.surjInv hβ (Multiplicative.ofAdd A), fun A => Function.surjInv_eq hβ _⟩
  have hdiff : ∀ u u' : Q, β u = β u' → ∃ z ∈ Z, (u' : G) = u * z := fun u u' h => by
    have hk : u⁻¹ * u' ∈ β.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
    rw [hβker, Subgroup.mem_subgroupOf] at hk
    exact ⟨_, hk, by simp⟩
  have hsq_eq : ∀ u u' : Q, β u = β u' → (u' : G) * u' = u * u := fun u u' h => by
    obtain ⟨z, hz, hu'⟩ := hdiff u u' h
    rw [hu']
    calc (u : G) * z * (u * z) = u * (z * u) * z := by group
      _ = u * u * (z * z) := by rw [(hcomQ u u.2 z hz).eq]; group
      _ = u * u := by rw [hZ2 z hz, mul_one]
  have hcom_eq : ∀ u u' v v' : Q, β u = β u' → β v = β v' →
      ⁅(u' : G), (v' : G)⁆ = ⁅(u : G), (v : G)⁆ := fun u u' v v' hu hv => by
    obtain ⟨z, hz, hu'⟩ := hdiff u u' hu
    obtain ⟨w, hw, hv'⟩ := hdiff v v' hv
    rw [hu', hv', commutatorElement_mul_left_of_commute (hcomQ _ (Q.mul_mem v.2 (hZQ hw)) z hz),
      commutatorElement_mul_right_of_commute (hcomQ u u.2 w hw)]
  obtain ⟨s, hs⟩ : ∃ s : Matrix (Fin 2) (Fin 2) F → Z, ∀ A, (s A : G) = σ A * σ A :=
    ⟨fun A => ⟨_, hsqZ (σ A)⟩, fun A => rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : Matrix (Fin 2) (Fin 2) F → Matrix (Fin 2) (Fin 2) F → Z,
      ∀ A B, (c A B : G) = ⁅(σ A : G), (σ B : G)⁆ :=
    ⟨fun A B => ⟨_, hcomZ (σ A) (σ B)⟩, fun A B => rfl⟩
  have hσβ : ∀ u : Q, β u = β (σ (Multiplicative.toAdd (β u))) := fun u => by
    rw [hσ, ofAdd_toAdd]
  have hs_coe : ∀ u : Q, (s (Multiplicative.toAdd (β u)) : G) = u * u := fun u => by
    rw [hs]
    exact hsq_eq u _ (hσβ u)
  have hc_coe : ∀ u v : Q,
      (c (Multiplicative.toAdd (β u)) (Multiplicative.toAdd (β v)) : G) = ⁅(u : G), (v : G)⁆ :=
    fun u v => by
      rw [hc]
      exact hcom_eq u _ v _ (hσβ u) (hσβ v)
  have hs_add : ∀ A B, s (A + B) = s A * s B * c B A := fun A B => by
    apply Subtype.ext
    have hβ' : β (σ A * σ B) = β (σ (A + B)) := by
      rw [map_mul, hσ, hσ, hσ]
      rfl
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hs (A + B), hs A, hs B, hc B A,
      hsq_eq (σ A * σ B) (σ (A + B)) hβ', Subgroup.coe_mul]
    exact mul_mul_mul_self_of_commute (hcomQ _ (σ A).2 _ (hcomZ _ _))
      (hcomQ _ (σ B).2 _ (hcomZ _ _))
  have hc_addl : ∀ A A' B, c (A + A') B = c A B * c A' B := fun A A' B => by
    apply Subtype.ext
    have hβ' : β (σ A' * σ A) = β (σ (A + A')) := by
      rw [map_mul, hσ, hσ, hσ, add_comm A A']
      rfl
    rw [Subgroup.coe_mul, hc (A + A') B, hc A B, hc A' B,
      hcom_eq (σ A' * σ A) (σ (A + A')) (σ B) (σ B) hβ' rfl, Subgroup.coe_mul]
    exact commutatorElement_mul_left_eq (hcomQ _ (σ A').2 _ (hcomZ _ _)).symm
  have hc_addr : ∀ A B B', c A (B + B') = c A B * c A B' := fun A B B' => by
    apply Subtype.ext
    have hβ' : β (σ B * σ B') = β (σ (B + B')) := by
      rw [map_mul, hσ, hσ, hσ]
      rfl
    rw [Subgroup.coe_mul, hc A (B + B'), hc A B, hc A B',
      hcom_eq (σ A) (σ A) (σ B * σ B') (σ (B + B')) rfl hβ', Subgroup.coe_mul]
    exact commutatorElement_mul_right_eq (hcomQ _ (σ B).2 _ (hcomZ _ _)).symm
  have hconj : ∀ (ℓ : L) (u : Q), ∃ u' : Q, (u' : G) = ℓ * u * (ℓ : G)⁻¹ ∧
      β u' = Multiplicative.ofAdd ((α ℓ : Matrix (Fin 2) (Fin 2) F) *
        Multiplicative.toAdd (β u)) := fun ℓ u => by
    let u' : Q := ⟨ℓ * u * (ℓ : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hLQ ℓ.2) u).mp u.2⟩
    refine ⟨u', rfl, ?_⟩
    rw [← hβconj ℓ u u' rfl, ofAdd_toAdd]
  have hs_inv : ∀ (g : SpecialLinearGroup (Fin 2) F) A,
      s ((g : Matrix (Fin 2) (Fin 2) F) * A) = s A := fun g A => by
    obtain ⟨ℓ, rfl⟩ := hα g
    obtain ⟨u', hu', hβu'⟩ := hconj ℓ (σ A)
    apply Subtype.ext
    have hβ' : β u' = β (σ ((α ℓ : Matrix (Fin 2) (Fin 2) F) * A)) := by
      rw [hβu', hσ, hσ, toAdd_ofAdd]
    have hcom : Commute (ℓ : G) ((σ A : G) * σ A) :=
      (Subgroup.mem_centralizer_iff.mp (hLZ ℓ.2) _ (hsqZ (σ A))).symm
    rw [hs, hs, hsq_eq u' _ hβ', hu']
    calc (ℓ : G) * σ A * (ℓ : G)⁻¹ * (ℓ * σ A * (ℓ : G)⁻¹) = ℓ * (σ A * σ A) * (ℓ : G)⁻¹ := by
          group
      _ = σ A * σ A := hcom.mul_inv_cancel
  have hc_inv : ∀ (g : SpecialLinearGroup (Fin 2) F) A B,
      c ((g : Matrix (Fin 2) (Fin 2) F) * A) ((g : Matrix (Fin 2) (Fin 2) F) * B) = c A B :=
    fun g A B => by
      obtain ⟨ℓ, rfl⟩ := hα g
      obtain ⟨u', hu', hβu'⟩ := hconj ℓ (σ A)
      obtain ⟨v', hv', hβv'⟩ := hconj ℓ (σ B)
      apply Subtype.ext
      have hβA : β u' = β (σ ((α ℓ : Matrix (Fin 2) (Fin 2) F) * A)) := by
        rw [hβu', hσ, hσ, toAdd_ofAdd]
      have hβB : β v' = β (σ ((α ℓ : Matrix (Fin 2) (Fin 2) F) * B)) := by
        rw [hβv', hσ, hσ, toAdd_ofAdd]
      have hcom : Commute (ℓ : G) ⁅(σ A : G), (σ B : G)⁆ :=
        (Subgroup.mem_centralizer_iff.mp (hLZ ℓ.2) _ (hcomZ (σ A) (σ B))).symm
      rw [hc, hc, hcom_eq u' _ v' _ hβA hβB, hu', hv', ← conjugate_commutatorElement]
      exact hcom.mul_inv_cancel
  have hs0 : s 0 = 1 := by
    apply Subtype.ext
    rw [hs, hsq_eq 1 (σ 0) (by rw [map_one, hσ, ofAdd_zero])]
    simp
  have hs_pure : ∀ v m : Fin 2 → F, s (vecMulVec v m) = 1 := fun v m => by
    by_cases hv : v = 0
    · rw [hv, zero_vecMulVec, hs0]
    · obtain ⟨g, hg⟩ := CFSG.Quasithin.SL2Model.exists_smul_eq v₀ v hv₀ hv
      have hvm : vecMulVec v m = (g : Matrix (Fin 2) (Fin 2) F) * vecMulVec v₀ m := by
        rw [mul_vecMulVec, ← hg]
        rfl
      rw [hvm, hs_inv]
      apply Subtype.ext
      rw [hs]
      exact hpure _ ⟨m, by rw [hσ, toAdd_ofAdd]⟩
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : (Fin 2 → F) → (Fin 2 → F) → Z,
      ∀ x y, Λ x y = c (vecMulVec y ![0, 1]) (vecMulVec x ![1, 0]) :=
    ⟨_, fun _ _ => rfl⟩
  have hl : ∀ x x' y, Λ (x + x') y = Λ x y * Λ x' y := fun x x' y => by
    rw [hΛ, hΛ, hΛ, add_vecMulVec, hc_addr]
  have hr : ∀ x y y', Λ x (y + y') = Λ x y * Λ x y' := fun x y y' => by
    rw [hΛ, hΛ, hΛ, add_vecMulVec, hc_addl]
  have halt : ∀ x, Λ x x = 1 := fun x => by
    have h := hs_add (vecMulVec x ![1, 0]) (vecMulVec x ![0, 1])
    rw [← vecMulVec_add, hs_pure, hs_pure, hs_pure, one_mul, one_mul] at h
    rw [hΛ]
    exact h.symm
  have hinv : ∀ (g : SpecialLinearGroup (Fin 2) F) (x y : Fin 2 → F),
      Λ ((g : Matrix (Fin 2) (Fin 2) F) *ᵥ x) ((g : Matrix (Fin 2) (Fin 2) F) *ᵥ y) = Λ x y :=
    fun g x y => by
      rw [hΛ, hΛ, ← mul_vecMulVec, ← mul_vecMulVec, hc_inv]
  have hform := form_eq_det Λ hl hr halt hinv
  have hΛ0 : ∀ x, Λ x 0 = 1 := fun x => by
    have h := hr x 0 0
    rw [add_zero] at h
    exact mul_left_cancel (h.symm.trans (mul_one _).symm)
  let ζ' : Multiplicative F →* Z :=
    { toFun := fun t => Λ ![1, 0] ![0, Multiplicative.toAdd t]
      map_one' := by
        have h0 : (![0, Multiplicative.toAdd (1 : Multiplicative F)] : Fin 2 → F) = 0 := by
          ext i
          fin_cases i <;> rfl
        rw [h0, hΛ0]
      map_mul' := fun a b => by
        have hab : (![0, Multiplicative.toAdd (a * b)] : Fin 2 → F) =
            ![0, Multiplicative.toAdd a] + ![0, Multiplicative.toAdd b] := by
          ext i
          fin_cases i <;> simp
        rw [hab, hr] }
  have hζ' : ∀ t, ζ' t = Λ ![1, 0] ![0, Multiplicative.toAdd t] := fun _ => rfl
  have hsdet : ∀ A : Matrix (Fin 2) (Fin 2) F, s A = ζ' (Multiplicative.ofAdd A.det) := fun A => by
    have hA : A = vecMulVec (fun i => A i 0) ![1, 0] + vecMulVec (fun i => A i 1) ![0, 1] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [vecMulVec_apply]
    rw [congrArg s hA, hs_add, hs_pure, hs_pure, one_mul, one_mul, ← hΛ, hform, hζ',
      toAdd_ofAdd]
    exact congrArg (fun t => Λ ![1, 0] ![0, t]) (by simp only [det_fin_two]; ring)
  refine ⟨Z.subtype.comp ζ', fun t => (ζ' t).2, fun u => ?_, fun u v => ?_⟩
  · show (u : G) * u = ((ζ' (Multiplicative.ofAdd (Multiplicative.toAdd (β u)).det) : Z) : G)
    rw [← hs_coe u, hsdet]
  · show ⁅(u : G), (v : G)⁆ = ((ζ' (Multiplicative.ofAdd
        ((Multiplicative.toAdd (β u) + Multiplicative.toAdd (β v)).det +
          (Multiplicative.toAdd (β u)).det + (Multiplicative.toAdd (β v)).det)) : Z) : G)
    have hcYX : c (Multiplicative.toAdd (β v)) (Multiplicative.toAdd (β u)) =
        c (Multiplicative.toAdd (β u)) (Multiplicative.toAdd (β v)) := by
      apply Subtype.ext
      rw [hc, hc, ← commutatorElement_inv (σ (Multiplicative.toAdd (β u)) : G)]
      exact inv_eq_of_mul_eq_one_right (hZ2 _ (hcomZ _ _))
    have hZZ : ∀ z : Z, z * z = 1 := fun z => Subtype.ext (hZ2 z z.2)
    have h2 : c (Multiplicative.toAdd (β u)) (Multiplicative.toAdd (β v)) =
        s (Multiplicative.toAdd (β v)) * s (Multiplicative.toAdd (β u)) *
          s (Multiplicative.toAdd (β u) + Multiplicative.toAdd (β v)) := by
      rw [hs_add, hcYX]
      calc c (Multiplicative.toAdd (β u)) (Multiplicative.toAdd (β v)) =
            s (Multiplicative.toAdd (β v)) *
              (s (Multiplicative.toAdd (β u)) * s (Multiplicative.toAdd (β u))) *
              s (Multiplicative.toAdd (β v)) *
              c (Multiplicative.toAdd (β u)) (Multiplicative.toAdd (β v)) := by
            rw [hZZ, mul_one, hZZ, one_mul]
        _ = _ := by group
    rw [← hc_coe u v, h2, hsdet, hsdet, hsdet,
      show (Multiplicative.toAdd (β u) + Multiplicative.toAdd (β v)).det +
          (Multiplicative.toAdd (β u)).det + (Multiplicative.toAdd (β v)).det =
        (Multiplicative.toAdd (β v)).det + (Multiplicative.toAdd (β u)).det +
          (Multiplicative.toAdd (β u) + Multiplicative.toAdd (β v)).det by ring,
      ofAdd_add, ofAdd_add, map_mul, map_mul]

theorem injective_and_range_eq_of_commutator_mem {G : Type*} [Group G] {F : Type*} [Field F]
    [Finite F] {Q Z : Subgroup G} (ζ : Multiplicative F →* G) (hζZ : ∀ c, ζ c ∈ Z)
    (hcomm : ∀ u v : Q, ⁅(u : G), (v : G)⁆ ∈ ζ.range) (hZQQ : Z ≤ ⁅Q, Q⁆)
    (hcard : Nat.card Z = Nat.card F) : Function.Injective ζ ∧ ζ.range = Z := by
  have hrange : ζ.range = Z := by
    refine le_antisymm ?_ (hZQQ.trans ?_)
    · rintro _ ⟨c, rfl⟩
      exact hζZ c
    · rw [Subgroup.commutator_le]
      intro g₁ h₁ g₂ h₂
      exact hcomm ⟨g₁, h₁⟩ ⟨g₂, h₂⟩
  refine ⟨?_, hrange⟩
  have h := Subgroup.card_ker_mul_card_range ζ
  rw [hrange, hcard, Nat.card_congr (Multiplicative.toAdd : Multiplicative F ≃ F)] at h
  have hker : Nat.card ζ.ker = 1 :=
    Nat.eq_of_mul_eq_mul_right Nat.card_pos (h.trans (one_mul _).symm)
  exact (MonoidHom.ker_eq_bot_iff ζ).mp (Subgroup.card_eq_one.mp hker)

structure PointFormData {G : Type*} [Group G] (Q Z L : Subgroup G) (F : Type*) [Field F] where
  α : L →* SpecialLinearGroup (Fin 2) F
  α_surjective : Function.Surjective α
  β : Q →* Multiplicative (Matrix (Fin 2) (Fin 2) F)
  β_surjective : Function.Surjective β
  ker_β : β.ker = Z.subgroupOf Q
  β_conj : ∀ (ℓ : L) (u v : Q), (v : G) = ℓ * u * ℓ⁻¹ →
    Multiplicative.toAdd (β v) = (α ℓ : Matrix (Fin 2) (Fin 2) F) * Multiplicative.toAdd (β u)
  ζ : Multiplicative F →* G
  ζ_injective : Function.Injective ζ
  range_ζ : ζ.range = Z
  mul_self_eq : ∀ u : Q, (u : G) * u = ζ (Multiplicative.ofAdd (Multiplicative.toAdd (β u)).det)
  commutator_eq : ∀ u v : Q, ⁅(u : G), (v : G)⁆ = ζ (Multiplicative.ofAdd
    ((Multiplicative.toAdd (β u) + Multiplicative.toAdd (β v)).det +
      (Multiplicative.toAdd (β u)).det + (Multiplicative.toAdd (β v)).det))

end CFSG.Quasithin.F112R.St84

end
