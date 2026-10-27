module

public import CFSG.RankThree.PartTwo.Census.Carrier.G2EvenRank
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.Lift3

open CFSG.Open
open CFSG.RankThree.PartTwo.Census.Carrier (ThreeRankLeOne)

abbrev Blk : Type := ZMod 2 × ZMod 2

@[expose] def fB (x : Blk) : Blk := (x.2, x.1 + x.2)

@[expose] def gB (x : Blk) : Blk := (x.2, x.1)

theorem fB_add (x y : Blk) : fB (x + y) = fB x + fB y := by
  revert x y
  decide

theorem gB_add (x y : Blk) : gB (x + y) = gB x + gB y := by
  revert x y
  decide

theorem fB_fB_fB (x : Blk) : fB (fB (fB x)) = x := by
  revert x
  decide

theorem gB_gB (x : Blk) : gB (gB x) = x := by
  revert x
  decide

theorem gB_fB_gB (x : Blk) : gB (fB (gB x)) = fB (fB x) := by
  revert x
  decide

theorem fB_gB_fB (x : Blk) : fB (gB (fB x)) = gB x := by
  revert x
  decide

theorem fB_iterate_three (m : ℕ) (x : Blk) : fB^[m + 3] x = fB^[m] x := by
  rw [Function.iterate_add_apply]
  show fB^[m] (fB (fB (fB x))) = fB^[m] x
  rw [fB_fB_fB]

theorem fB_iterate_inj {a b : Fin 3} (h : fB^[a.val] ((1, 0) : Blk) = fB^[b.val] (1, 0)) :
    a = b := by
  revert a b
  decide

variable {k r : ℕ}

abbrev Pk (k r : ℕ) : Type := (Fin k → Blk) × (Fin r → ZMod 2)

@[expose] def onCoord (φ : Blk → Blk) (i : Fin k) (x : Pk k r) : Pk k r :=
  (fun j => if j = i then φ (x.1 j) else x.1 j, x.2)

theorem onCoord_fst (φ : Blk → Blk) (i j : Fin k) (x : Pk k r) :
    (onCoord φ i x).1 j = if j = i then φ (x.1 j) else x.1 j := rfl

theorem onCoord_snd (φ : Blk → Blk) (i : Fin k) (x : Pk k r) : (onCoord φ i x).2 = x.2 := rfl

theorem onCoord_comp (φ ψ : Blk → Blk) (i : Fin k) (x : Pk k r) :
    onCoord φ i (onCoord ψ i x) = onCoord (φ ∘ ψ) i x := by
  refine Prod.ext (funext fun j => ?_) rfl
  simp only [onCoord_fst, Function.comp_apply]
  split_ifs <;> rfl

theorem onCoord_comm (φ ψ : Blk → Blk) {i j : Fin k} (hij : i ≠ j) (x : Pk k r) :
    onCoord φ i (onCoord ψ j x) = onCoord ψ j (onCoord φ i x) := by
  refine Prod.ext (funext fun l => ?_) rfl
  simp only [onCoord_fst]
  by_cases hli : l = i
  · subst hli
    simp [hij]
  · simp [hli]

theorem onCoord_id (i : Fin k) (x : Pk k r) : onCoord id i x = x := by
  refine Prod.ext (funext fun l => ?_) rfl
  simp only [onCoord_fst, id]
  split_ifs <;> rfl

theorem onCoord_add {φ : Blk → Blk} (hφ : ∀ x y, φ (x + y) = φ x + φ y) (i : Fin k)
    (x y : Pk k r) : onCoord φ i (x + y) = onCoord φ i x + onCoord φ i y := by
  refine Prod.ext (funext fun l => ?_) rfl
  simp only [onCoord_fst, Prod.fst_add, Pi.add_apply]
  split_ifs
  · exact hφ _ _
  · rfl

theorem fB_iterate_add (m : ℕ) (u v : Blk) : fB^[m] (u + v) = fB^[m] u + fB^[m] v := by
  induction m generalizing u v with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_succ_apply,
      fB_add]
    exact ih _ _

theorem fB_iterate_three_mul (m : ℕ) (u : Blk) : fB^[3 * m] u = u := by
  induction m with
  | zero => rfl
  | succ m ih => rw [show 3 * (m + 1) = 3 * m + 3 by ring, fB_iterate_three, ih]

abbrev Mk (k r : ℕ) : Type := MulAut (Multiplicative (Pk k r))

@[expose] def onAut {φ ψ : Blk → Blk} (hφ : ∀ x y, φ (x + y) = φ x + φ y)
    (hφψ : ∀ x, φ (ψ x) = x) (hψφ : ∀ x, ψ (φ x) = x) (i : Fin k) : Mk k r where
  toFun x := Multiplicative.ofAdd (onCoord φ i (Multiplicative.toAdd x))
  invFun x := Multiplicative.ofAdd (onCoord ψ i (Multiplicative.toAdd x))
  left_inv x := by
    apply Multiplicative.toAdd.injective
    show onCoord ψ i (onCoord φ i (Multiplicative.toAdd x)) = Multiplicative.toAdd x
    rw [onCoord_comp]
    convert onCoord_id i (Multiplicative.toAdd x) using 2
    funext b
    exact hψφ b
  right_inv x := by
    apply Multiplicative.toAdd.injective
    show onCoord φ i (onCoord ψ i (Multiplicative.toAdd x)) = Multiplicative.toAdd x
    rw [onCoord_comp]
    convert onCoord_id i (Multiplicative.toAdd x) using 2
    funext b
    exact hφψ b
  map_mul' x y := by
    show Multiplicative.ofAdd (onCoord φ i (Multiplicative.toAdd x + Multiplicative.toAdd y)) = _
    rw [onCoord_add hφ]
    rfl

@[expose] def yA (i : Fin k) : Mk k r :=
  onAut (ψ := fB ∘ fB) fB_add (fun x => fB_fB_fB x) (fun x => fB_fB_fB x) i

@[expose] def tA (i : Fin k) : Mk k r :=
  onAut (ψ := gB) gB_add gB_gB gB_gB i

theorem yA_apply (i : Fin k) (x : Multiplicative (Pk k r)) :
    Multiplicative.toAdd (yA i x) = onCoord fB i (Multiplicative.toAdd x) := rfl

theorem tA_apply (i : Fin k) (x : Multiplicative (Pk k r)) :
    Multiplicative.toAdd (tA i x) = onCoord gB i (Multiplicative.toAdd x) := rfl

theorem ext_toAdd {a b : Mk k r}
    (h : ∀ x, Multiplicative.toAdd (a x) = Multiplicative.toAdd (b x)) : a = b :=
  MulEquiv.ext fun x => Multiplicative.toAdd.injective (h x)

theorem yA_pow_three (i : Fin k) : yA (r := r) i ^ 3 = 1 := by
  refine ext_toAdd fun x => ?_
  rw [pow_succ, pow_succ, pow_one]
  simp only [MulAut.mul_apply, MulAut.one_apply]
  rw [yA_apply, yA_apply, yA_apply, onCoord_comp, onCoord_comp]
  convert onCoord_id i (Multiplicative.toAdd x) using 2
  funext b
  exact fB_fB_fB b

theorem yA_comm (i j : Fin k) : yA (r := r) i * yA j = yA j * yA i := by
  by_cases hij : i = j
  · rw [hij]
  refine ext_toAdd fun x => ?_
  simp only [MulAut.mul_apply]
  rw [yA_apply, yA_apply, yA_apply, yA_apply, onCoord_comm _ _ hij]

theorem tA_yA_tA (i : Fin k) : tA (r := r) i * yA i * (tA i)⁻¹ = (yA i)⁻¹ := by
  rw [mul_inv_eq_iff_eq_mul, eq_inv_mul_iff_mul_eq]
  refine ext_toAdd fun x => ?_
  simp only [MulAut.mul_apply]
  rw [yA_apply, tA_apply, yA_apply, tA_apply, onCoord_comp, onCoord_comp]
  congr 1
  funext b
  exact fB_gB_fB b

theorem tA_yA_tA_of_ne {i j : Fin k} (hij : i ≠ j) :
    tA (r := r) i * yA j * (tA i)⁻¹ = yA j := by
  rw [mul_inv_eq_iff_eq_mul]
  refine ext_toAdd fun x => ?_
  simp only [MulAut.mul_apply]
  rw [yA_apply, tA_apply, tA_apply, yA_apply]
  exact onCoord_comm _ _ hij _

@[expose] def yPow (a : Fin k → ℕ) : Mk k r where
  toFun x := Multiplicative.ofAdd
    (fun j => fB^[a j] ((Multiplicative.toAdd x).1 j), (Multiplicative.toAdd x).2)
  invFun x := Multiplicative.ofAdd
    (fun j => fB^[2 * a j] ((Multiplicative.toAdd x).1 j), (Multiplicative.toAdd x).2)
  left_inv x := by
    refine Multiplicative.toAdd.injective (Prod.ext (funext fun j => ?_) rfl)
    show fB^[2 * a j] (fB^[a j] ((Multiplicative.toAdd x).1 j)) = (Multiplicative.toAdd x).1 j
    rw [← Function.iterate_add_apply, show 2 * a j + a j = 3 * a j by ring, fB_iterate_three_mul]
  right_inv x := by
    refine Multiplicative.toAdd.injective (Prod.ext (funext fun j => ?_) rfl)
    show fB^[a j] (fB^[2 * a j] ((Multiplicative.toAdd x).1 j)) = (Multiplicative.toAdd x).1 j
    rw [← Function.iterate_add_apply, show a j + 2 * a j = 3 * a j by ring, fB_iterate_three_mul]
  map_mul' x y := by
    refine Multiplicative.toAdd.injective (Prod.ext (funext fun j => ?_) rfl)
    exact fB_iterate_add _ _ _

theorem yPow_apply (a : Fin k → ℕ) (x : Multiplicative (Pk k r)) :
    Multiplicative.toAdd (yPow a x) =
      (fun j => fB^[a j] ((Multiplicative.toAdd x).1 j), (Multiplicative.toAdd x).2) := rfl

theorem yA_mul_yPow (i : Fin k) (a : Fin k → ℕ) :
    yA (r := r) i * yPow a = yPow (a + Pi.single i 1) := by
  refine ext_toAdd fun x => ?_
  rw [MulAut.mul_apply, yA_apply, yPow_apply, yPow_apply]
  refine Prod.ext (funext fun j => ?_) rfl
  simp only [onCoord_fst, Pi.add_apply]
  by_cases hji : j = i
  · subst hji
    simp only [Pi.single_eq_same, ↓reduceIte]
    rw [Function.iterate_succ_apply']
  · simp [hji]

theorem yPow_zero : yPow (k := k) (r := r) 0 = 1 := by
  refine ext_toAdd fun x => ?_
  rfl

theorem yPow_mem_closure (a : Fin k → ℕ) :
    yPow (r := r) a ∈ Subgroup.closure (Set.range (yA (r := r))) := by
  obtain ⟨N, hN⟩ : ∃ N, ∑ j, a j = N := ⟨_, rfl⟩
  induction N generalizing a with
  | zero =>
    have ha : a = 0 := funext fun j => Finset.sum_eq_zero_iff.mp hN j (Finset.mem_univ _)
    rw [ha, yPow_zero]
    exact Subgroup.one_mem _
  | succ N ih =>
    obtain ⟨i, hi⟩ : ∃ i, 0 < a i := by
      by_contra h
      push Not at h
      have : ∑ j, a j = 0 := Finset.sum_eq_zero fun j _ => Nat.le_zero.mp (h j)
      omega
    set a' : Fin k → ℕ := Function.update a i (a i - 1) with ha'
    have he : a = a' + Pi.single i 1 := by
      funext j
      by_cases hji : j = i
      · subst hji
        simp [ha']
        omega
      · simp [ha', Function.update_of_ne hji, Pi.single_eq_of_ne hji]
    have hsum : ∑ j, a' j = N := by
      have h1 : ∑ j, a j = ∑ j, a' j + ∑ j, (Pi.single i 1 : Fin k → ℕ) j := by
        rw [← Finset.sum_add_distrib]
        exact congrArg (fun f : Fin k → ℕ => ∑ j, f j) he
      rw [Finset.sum_pi_single'] at h1
      simp only [Finset.mem_univ, ↓reduceIte] at h1
      omega
    have hrec := ih a' hsum
    rw [he, ← yA_mul_yPow]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure ⟨i, rfl⟩) hrec

theorem card_closure_yA :
    3 ^ k ≤ Nat.card (Subgroup.closure (Set.range (yA (k := k) (r := r)))) := by
  classical
  have hinj : Function.Injective fun a : Fin k → Fin 3 =>
      (⟨yPow (r := r) fun j => (a j).val, yPow_mem_closure _⟩ :
        ↥(Subgroup.closure (Set.range (yA (k := k) (r := r))))) := by
    intro a b hab
    have h := congrArg (fun g : ↥(Subgroup.closure (Set.range (yA (k := k) (r := r)))) =>
      (Multiplicative.toAdd ((g : Mk k r)
        (Multiplicative.ofAdd ((fun _ => ((1, 0) : Blk)), 0)))).1) hab
    funext j
    exact fB_iterate_inj (congrFun h j)
  have := Nat.card_le_card_of_injective _ hinj
  rwa [Nat.card_eq_fintype_card (α := Fin k → Fin 3), Fintype.card_fun, Fintype.card_fin,
    Fintype.card_fin] at this

section Transfer

variable {W : Type} [CommGroup W] [Finite W]

theorem pk_sq (x : Multiplicative (Pk k r)) : x ^ 2 = 1 := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one, two_nsmul]
  exact Prod.ext (funext fun j => Prod.ext (CharTwo.add_self_eq_zero _)
    (CharTwo.add_self_eq_zero _)) (funext fun j => CharTwo.add_self_eq_zero _)

theorem card_pk : Nat.card (Multiplicative (Pk k r)) = 2 ^ (2 * k + r) := by
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_prod, Nat.card_fun, Nat.card_fun,
    Nat.card_prod, Nat.card_zmod, Nat.card_eq_fintype_card (α := Fin k),
    Nat.card_eq_fintype_card (α := Fin r), Fintype.card_fin, Fintype.card_fin, pow_add, pow_mul]
  norm_num

theorem nonempty_equiv (hW : ∀ w : W, w ^ 2 = 1) (hd : Nat.card W = 2 ^ (2 * k + r)) :
    Nonempty (W ≃* Multiplicative (Pk k r)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e₁⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2)
    (fun a b : W => mul_comm a b) hW hd
  obtain ⟨e₂⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2)
    (fun a b : Multiplicative (Pk k r) => mul_comm a b) pk_sq card_pk
  exact ⟨e₁.trans e₂.symm⟩

theorem exists_mulAut (hW : ∀ w : W, w ^ 2 = 1) {d k : ℕ} (hd : Nat.card W = 2 ^ d)
    (hk : 2 * k ≤ d) :
    ∃ (Y Tau : Fin k → MulAut W), (∀ i, Y i ^ 3 = 1) ∧ (∀ i j, Y i * Y j = Y j * Y i) ∧
      (∀ i, Tau i * Y i * (Tau i)⁻¹ = (Y i)⁻¹) ∧
      (∀ i j, i ≠ j → Tau i * Y j * (Tau i)⁻¹ = Y j) ∧
      3 ^ k ≤ Nat.card ↥(Subgroup.closure (Set.range Y)) := by
  obtain ⟨e⟩ := nonempty_equiv (k := k) (r := d - 2 * k) hW (by rw [hd]; congr 1; omega)
  set Φ : Mk k (d - 2 * k) ≃* MulAut W := (MulAut.congr e).symm with hΦ
  refine ⟨fun i => Φ (yA i), fun i => Φ (tA i), fun i => ?_, fun i j => ?_, fun i => ?_,
    fun i j hij => ?_, ?_⟩
  · rw [← map_pow, yA_pow_three, map_one]
  · rw [← map_mul, ← map_mul, yA_comm]
  · rw [← map_inv, ← map_mul, ← map_mul, tA_yA_tA, map_inv]
  · rw [← map_inv, ← map_mul, ← map_mul, tA_yA_tA_of_ne hij]
  · have h : Subgroup.closure (Set.range fun i => Φ (yA i)) =
        (Subgroup.closure (Set.range (yA (k := k) (r := d - 2 * k)))).map Φ.toMonoidHom := by
      rw [MonoidHom.map_closure, ← Set.range_comp]
      rfl
    rw [h, Subgroup.card_map_of_injective Φ.injective]
    exact card_closure_yA

end Transfer

section Lift

variable {X Y : Type*} [Group X] [Group Y]

theorem commute_of_central (π : X →* Y) (hker : ∀ c ∈ π.ker, ∀ g : X, c * g = g * c)
    {a b t : X} (ha : π (a ^ 3) = 1) (hab : π a * π b = π b * π a)
    (hta : π (t * a * t⁻¹) = (π a)⁻¹) (htb : π (t * b * t⁻¹) = π b) : a * b = b * a := by
  obtain ⟨c, hc⟩ : ∃ c, c = a * b * a⁻¹ * b⁻¹ := ⟨_, rfl⟩
  have hcker : c ∈ π.ker := by
    rw [MonoidHom.mem_ker, hc, map_mul, map_mul, map_mul, map_inv, map_inv, hab]
    group
  have hcz := hker c hcker
  obtain ⟨k₁, hk₁⟩ : ∃ k₁, k₁ = a * (t * a * t⁻¹) := ⟨_, rfl⟩
  obtain ⟨k₂, hk₂⟩ : ∃ k₂, k₂ = b⁻¹ * (t * b * t⁻¹) := ⟨_, rfl⟩
  have hz₁ := hker k₁ (by rw [MonoidHom.mem_ker, hk₁, map_mul, hta, mul_inv_cancel])
  have hz₂ := hker k₂ (by rw [MonoidHom.mem_ker, hk₂, map_mul, htb, map_inv, inv_mul_cancel])
  have hta' : t * a * t⁻¹ = a⁻¹ * k₁ := by rw [hk₁]; group
  have htb' : t * b * t⁻¹ = b * k₂ := by rw [hk₂]; group
  have h1 : c = a⁻¹ * b * a * b⁻¹ := by
    have htc : t * c * t⁻¹ = c := by rw [← hcz t, mul_inv_cancel_right]
    have e1 : t * c * t⁻¹ =
        (t * a * t⁻¹) * (t * b * t⁻¹) * (t * a * t⁻¹)⁻¹ * (t * b * t⁻¹)⁻¹ := by
      rw [hc]
      group
    rw [htc, hta', htb'] at e1
    rw [e1]
    have h12 : k₁ * k₂ * k₁⁻¹ = k₂ := by rw [hz₁ k₂, mul_inv_cancel_right]
    calc a⁻¹ * k₁ * (b * k₂) * (a⁻¹ * k₁)⁻¹ * (b * k₂)⁻¹
        = a⁻¹ * (k₁ * b) * k₂ * k₁⁻¹ * a * k₂⁻¹ * b⁻¹ := by group
      _ = a⁻¹ * (b * k₁) * k₂ * k₁⁻¹ * a * k₂⁻¹ * b⁻¹ := by rw [hz₁ b]
      _ = a⁻¹ * b * (k₁ * k₂ * k₁⁻¹) * a * k₂⁻¹ * b⁻¹ := by group
      _ = a⁻¹ * b * (k₂ * a) * k₂⁻¹ * b⁻¹ := by rw [h12]; group
      _ = a⁻¹ * b * (a * k₂) * k₂⁻¹ * b⁻¹ := by rw [hz₂ a]
      _ = a⁻¹ * b * a * b⁻¹ := by group
  have hab1 : a * b * a⁻¹ = c * b := by rw [hc]; group
  have hab2 : a⁻¹ * b * a = c * b := by rw [h1]; group
  have hac : ∀ m : ℕ, a * c ^ m = c ^ m * a := fun m =>
    ((Commute.pow_left (show Commute c a from hcz a) m).eq).symm
  have hc2 : c * c = 1 := by
    have e : b = c * c * b := by
      calc b = a * (a⁻¹ * b * a) * a⁻¹ := by group
        _ = a * (c * b) * a⁻¹ := by rw [hab2]
        _ = c * (a * b * a⁻¹) := by
            have := hac 1
            rw [pow_one] at this
            rw [← mul_assoc a c b, this, mul_assoc c a b]
            group
        _ = c * c * b := by rw [hab1, ← mul_assoc]
    have := congrArg (· * b⁻¹) e
    simpa using this.symm
  have hpow : ∀ m : ℕ, a ^ m * b * (a ^ m)⁻¹ = c ^ m * b := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      calc a ^ (m + 1) * b * (a ^ (m + 1))⁻¹ = a * (a ^ m * b * (a ^ m)⁻¹) * a⁻¹ := by
            rw [pow_succ']
            group
        _ = a * (c ^ m * b) * a⁻¹ := by rw [ih]
        _ = c ^ m * (a * b * a⁻¹) := by
            rw [← mul_assoc a (c ^ m) b, hac m, mul_assoc (c ^ m) a b]
            group
        _ = c ^ (m + 1) * b := by rw [hab1, pow_succ, mul_assoc]
  have ha3 : a ^ 3 * b * (a ^ 3)⁻¹ = b := by
    rw [hker _ ha b, mul_inv_cancel_right]
  have hc3 : c ^ 3 = 1 := by
    have h := (hpow 3).symm.trans ha3
    have := congrArg (· * b⁻¹) h
    simpa using this
  have hc1 : c = 1 := by
    calc c = c ^ 3 * (c * c)⁻¹ := by group
      _ = 1 := by rw [hc3, hc2]; group
  rw [hc] at hc1
  have h2 : a * b * a⁻¹ = b := by
    have := congrArg (· * b) hc1
    simpa using this
  calc a * b = a * b * a⁻¹ * a := by group
    _ = b * a := by rw [h2]

theorem le_pRank_of_image [Finite X] (π : X →* Y) {E : Subgroup X}
    (hE : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (h3 : ∀ a ∈ E, π a ^ 3 = 1) {k : ℕ}
    (hk : 3 ^ k ≤ Nat.card ↥(E.map π)) : k ≤ CFSG.Open.pRank 3 E := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let _ : CommGroup ↥E :=
    { (inferInstance : Group ↥E) with mul_comm := fun a b => Subtype.ext (hE a a.2 b b.2) }
  set cube : ↥E →* ↥E := powMonoidHom 3 with hcube
  set f : ↥E →* Y := π.comp E.subtype with hf
  have hrange : cube.range ≤ f.ker := by
    rintro _ ⟨x, rfl⟩
    show π ((x ^ 3 : ↥E) : X) = 1
    rw [Subgroup.coe_pow, map_pow, h3 _ x.2]
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup cube.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange cube).toEquiv] at h1
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv] at h2
  have hcardf : Nat.card ↥f.range = Nat.card ↥(E.map π) := by
    rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
  have h3' : Nat.card ↥cube.range ≤ Nat.card ↥f.ker := Subgroup.card_le_of_le hrange
  have hle : Nat.card ↥(E.map π) ≤ Nat.card ↥cube.ker := by
    have hpos : 0 < Nat.card ↥f.ker := Nat.card_pos
    have : Nat.card ↥f.range * Nat.card ↥f.ker ≤ Nat.card ↥cube.ker * Nat.card ↥f.ker := by
      rw [← h2, h1, mul_comm]
      exact Nat.mul_le_mul_left _ h3'
    rw [hcardf] at this
    exact Nat.le_of_mul_le_mul_right this hpos
  set Ω : Subgroup X := cube.ker.map E.subtype with hΩ
  have hΩE : Ω ≤ E := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hΩ : IsElemAbelian 3 Ω := by
    refine ⟨⟨⟨fun a b => Subtype.ext (hE _ (hΩE a.2) _ (hΩE b.2))⟩⟩, fun x hx => ?_⟩
    obtain ⟨y, hy, rfl⟩ := hx
    have : y ^ 3 = 1 := hy
    rw [Subgroup.coe_subtype, ← Subgroup.coe_pow, this, Subgroup.coe_one]
  have hcardΩ : Nat.card ↥Ω = Nat.card ↥cube.ker :=
    Subgroup.card_map_of_injective E.subtype_injective
  obtain ⟨m, hm⟩ : ∃ m, Nat.card ↥Ω = 3 ^ m := IsPGroup.iff_card.1 fun g =>
    ⟨1, by rw [pow_one]; exact Subtype.ext (hΩ.2 _ g.2)⟩
  have hkm : k ≤ m := by
    have : 3 ^ k ≤ 3 ^ m := by rw [← hm, hcardΩ]; exact hk.trans hle
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 this
  exact hkm.trans (CFSG.SectionRank.le_pRank (by norm_num) hΩE hΩ hm)

end Lift

theorem le_pRank_of_surjective {X : Type*} [Group X] [Finite X] {W : Type} [CommGroup W]
    [Finite W] (hW : ∀ w : W, w ^ 2 = 1) {d k : ℕ} (hd : Nat.card W = 2 ^ d) (hk : 2 * k ≤ d)
    (π : X →* MulAut W) (hπ : Function.Surjective π)
    (hker : ∀ c ∈ π.ker, ∀ g : X, c * g = g * c) : k ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  obtain ⟨Y, Tau, hY3, hYc, hT, hT', hcard⟩ := exists_mulAut hW hd hk
  choose y hy using fun i => hπ (Y i)
  choose τ hτ using fun i => hπ (Tau i)
  have hyc : ∀ i j, y i * y j = y j * y i := by
    intro i j
    by_cases hij : i = j
    · rw [hij]
    refine commute_of_central π hker (t := τ i) ?_ ?_ ?_ ?_
    · rw [map_pow, hy, hY3]
    · rw [hy, hy, hYc]
    · rw [map_mul, map_mul, map_inv, hy, hτ, hT]
    · rw [map_mul, map_mul, map_inv, hy, hτ, hT' i j hij]
  set E := Subgroup.closure (Set.range y) with hE
  have hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
    have : IsMulCommutative ↥E := Subgroup.isMulCommutative_closure (by
      rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ -
      exact hyc i j)
    intro a ha b hb
    exact congrArg Subtype.val (this.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hmap : E.map π = Subgroup.closure (Set.range Y) := by
    rw [hE, MonoidHom.map_closure, ← Set.range_comp]
    congr 1
    ext g
    simp [hy]
  have h3 : ∀ a ∈ E, π a ^ 3 = 1 := by
    have hYc' : ∀ a ∈ Subgroup.closure (Set.range Y), a ^ 3 = 1 := by
      have : IsMulCommutative ↥(Subgroup.closure (Set.range Y)) :=
        Subgroup.isMulCommutative_closure (by
          rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ -
          exact hYc i j)
      intro a ha
      induction ha using Subgroup.closure_induction with
      | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        exact hY3 i
      | one => exact one_pow 3
      | mul a b ha hb iha ihb =>
        have hcomm : a * b = b * a :=
          congrArg Subtype.val (this.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
        rw [(Commute.mul_pow hcomm 3), iha, ihb, one_mul]
      | inv a _ iha => rw [inv_pow, iha, inv_one]
    intro a ha
    exact hYc' _ (hmap ▸ Subgroup.mem_map_of_mem π ha)
  have hk' := le_pRank_of_image π hEc h3 (k := k) (by rw [hmap]; exact hcard)
  exact hk'.trans (CFSG.SectionRank.pRank_mono (by norm_num) le_top)

theorem not_threeRankLeOne {X Y : Type*} [Group X] [Group Y] [Finite X] (π : X →* Y)
    (hπ : Function.Surjective π) {a b : Y} (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) (hab : a * b = b * a)
    (ha1 : a ≠ 1) (hba : b ∉ Subgroup.zpowers a) :
    ¬ CFSG.RankThree.PartTwo.Census.Carrier.ThreeRankLeOne X := by
  classical
  intro h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite Y := Finite.of_surjective π hπ
  obtain ⟨P⟩ : Nonempty (Sylow 3 X) := inferInstance
  have hPc : IsCyclic ↥(P : Subgroup X) := by
    by_contra hnc
    have : Fact (IsPGroup 3 ↥(P : Subgroup X)) := ⟨P.isPGroup'⟩
    obtain ⟨S, -, hS9, hSe⟩ := CFSG.lemma_4_5_a (p := 3) (by norm_num) hnc
    have hSe' := (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 S).mp hSe
    obtain ⟨s₁, hs₁S, hs₁⟩ : ∃ s₁ ∈ S, s₁ ≠ 1 := by
      by_contra hc
      push Not at hc
      have : S = ⊥ := (Subgroup.eq_bot_iff_forall S).2 hc
      rw [this, Subgroup.card_bot] at hS9
      norm_num at hS9
    obtain ⟨s₂, hs₂S, hs₂⟩ : ∃ s₂ ∈ S, s₂ ∉ Subgroup.zpowers s₁ := by
      by_contra hc
      push Not at hc
      have hle : S ≤ Subgroup.zpowers s₁ := fun x hx => hc x hx
      have h1 := Subgroup.card_le_of_le hle
      rw [Nat.card_zpowers, hS9] at h1
      have h2 : orderOf s₁ ∣ 3 := orderOf_dvd_of_pow_eq_one (hSe'.2 s₁ hs₁S)
      have h3 := Nat.le_of_dvd (by norm_num) h2
      omega
    apply hs₂
    have hc := h (s₁ : X) (s₂ : X) (by rw [← Subgroup.coe_pow, hSe'.2 s₁ hs₁S]; rfl)
      (by rw [← Subgroup.coe_pow, hSe'.2 s₂ hs₂S]; rfl)
      (by
        rw [← Subgroup.coe_mul, ← Subgroup.coe_mul]
        exact congrArg Subtype.val (congrArg Subtype.val
          (hSe'.1.is_comm.comm ⟨s₁, hs₁S⟩ ⟨s₂, hs₂S⟩)))
      (fun h1 => hs₁ (Subtype.ext h1))
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hc
    exact Subgroup.mem_zpowers_iff.mpr ⟨m, Subtype.ext (by rw [Subgroup.coe_zpow, hm])⟩
  have hPYc : IsCyclic ↥((P : Subgroup X).map π) := by
    have hc : IsCyclic ↥(π.comp (P : Subgroup X).subtype).range :=
      isCyclic_of_surjective _ (MonoidHom.rangeRestrict_surjective _)
    have he : (π.comp (P : Subgroup X).subtype).range = (P : Subgroup X).map π := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    exact isCyclic_of_surjective (MulEquiv.subgroupCongr he).toMonoidHom (MulEquiv.surjective _)
  set B := Subgroup.closure ({a, b} : Set Y) with hB
  have hpair : ({a, b} : Set Y).Pairwise Commute := by
    intro x hx y hy _
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact Commute.refl _
    · exact hab
    · exact hab.symm
    · exact Commute.refl _
  have hBc : IsMulCommutative ↥B := Subgroup.isMulCommutative_closure hpair
  have hB3 : ∀ x ∈ B, x ^ 3 = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact ha
      · exact hb
    | one => exact one_pow 3
    | mul x y hx hy ihx ihy =>
      have hcomm : x * y = y * x := congrArg Subtype.val (hBc.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
      rw [(Commute.mul_pow hcomm 3), ihx, ihy, one_mul]
    | inv x _ ihx => rw [inv_pow, ihx, inv_one]
  have hBp : IsPGroup 3 ↥B := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, hB3 _ x.2, Subgroup.coe_one])⟩
  obtain ⟨Q, hBQ⟩ := hBp.exists_le_sylow
  have hQc : IsCyclic ↥(Q : Subgroup Y) := by
    have e := Sylow.equiv (P.mapSurjective hπ) Q
    have : IsCyclic ↥((P.mapSurjective hπ : Sylow 3 Y) : Subgroup Y) := hPYc
    exact isCyclic_of_surjective e.toMonoidHom e.surjective
  have : Fintype ↥(Q : Subgroup Y) := Fintype.ofFinite _
  have hle := IsCyclic.card_pow_eq_one_le (α := ↥(Q : Subgroup Y)) (n := 3) (by norm_num)
  have haQ : a ∈ (Q : Subgroup Y) := hBQ (Subgroup.subset_closure (Set.mem_insert _ _))
  have hbQ : b ∈ (Q : Subgroup Y) :=
    hBQ (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
  have ha2 : a⁻¹ ≠ 1 := fun h => ha1 (inv_eq_one.mp h)
  have haa : a ≠ a⁻¹ := by
    intro h
    apply ha1
    have h2 : a * a = 1 := by
      calc a * a = a * a⁻¹ := by rw [← h]
        _ = 1 := mul_inv_cancel a
    calc a = a ^ 3 * (a * a)⁻¹ := by group
      _ = 1 := by rw [ha, h2]; group
  have hb1 : b ≠ 1 := fun h => hba (h ▸ Subgroup.one_mem _)
  have hba1 : b ≠ a := fun h => hba (h ▸ Subgroup.mem_zpowers a)
  have hba2 : b ≠ a⁻¹ := fun h => hba (h ▸ Subgroup.inv_mem _ (Subgroup.mem_zpowers a))
  have hsub : ({⟨1, Subgroup.one_mem _⟩, ⟨a, haQ⟩, ⟨a⁻¹, Subgroup.inv_mem _ haQ⟩, ⟨b, hbQ⟩} :
      Finset ↥(Q : Subgroup Y)) ⊆ Finset.univ.filter fun x => x ^ 3 = 1 := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases hx with rfl | rfl | rfl | rfl
    · exact one_pow 3
    · exact Subtype.ext (by rw [Subgroup.coe_pow]; exact ha)
    · exact Subtype.ext (by rw [Subgroup.coe_pow, inv_pow, ha, inv_one]; rfl)
    · exact Subtype.ext (by rw [Subgroup.coe_pow]; exact hb)
  have h4 := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair] at h4
  · omega
  all_goals first
    | exact fun h => hba2 (congrArg Subtype.val h).symm
    | (simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.mk.injEq, not_or]
       exact ⟨haa, hba1.symm⟩)
    | (simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.mk.injEq, not_or]
       exact ⟨ha1.symm, ha2.symm, hb1.symm⟩)

section SL2'

variable {K : Type*} [Field K]

theorem sq_add_one_of_pow_three' {g : Matrix.SpecialLinearGroup (Fin 2) K}
    (hg : g ^ 3 = 1) (hg1 : g ≠ 1) :
    (g : Matrix (Fin 2) (Fin 2) K) ^ 2 + (g : Matrix (Fin 2) (Fin 2) K) + 1 = 0 := by
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin 2) (Fin 2) K, M = g := ⟨_, rfl⟩
  rw [← hM]
  obtain ⟨t, ht⟩ : ∃ t : K, t = M 0 0 + M 1 1 := ⟨_, rfl⟩
  have hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
    rw [← Matrix.det_fin_two, hM]
    exact g.2
  have hCH : M * M = t • M - 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, ht] <;>
      first | linear_combination (-1 : K) * hdet | ring
  have hM3 : M ^ 3 = 1 := by
    rw [hM, ← Matrix.SpecialLinearGroup.coe_pow, hg, Matrix.SpecialLinearGroup.coe_one]
  have h3 : M ^ 3 = (t * t - 1) • M - t • (1 : Matrix (Fin 2) (Fin 2) K) := by
    rw [pow_succ', pow_two, hCH, mul_sub, mul_one, Matrix.mul_smul, hCH, smul_sub, smul_smul,
      sub_smul, one_smul]
    abel
  have hlin : (t * t - 1) • M - t • (1 : Matrix (Fin 2) (Fin 2) K) = 1 := h3.symm.trans hM3
  by_cases ht1 : t = -1
  · rw [pow_two, hCH, ht1, neg_one_smul]
    abel
  exfalso
  have ht1' : t + 1 ≠ 0 := fun h => ht1 (eq_neg_of_add_eq_zero_left h)
  have htt : t * t - 1 ≠ 0 := by
    intro h
    rw [h, zero_smul, zero_sub] at hlin
    have h00 := congrFun (congrFun hlin 0) 0
    simp at h00
    exact ht1 (by linear_combination -h00)
  have hfac : t * t - 1 = (t - 1) * (t + 1) := by ring
  have htm : t - 1 ≠ 0 := fun h => htt (by rw [hfac, h, zero_mul])
  have hscal : M = (t - 1)⁻¹ • (1 : Matrix (Fin 2) (Fin 2) K) := by
    have h1 : (t * t - 1) • M = (t + 1) • (1 : Matrix (Fin 2) (Fin 2) K) := by
      rw [add_smul, one_smul, add_comm]
      exact eq_add_of_sub_eq hlin
    calc M = ((t * t - 1)⁻¹ * (t * t - 1)) • M := by rw [inv_mul_cancel₀ htt, one_smul]
      _ = (t * t - 1)⁻¹ • ((t + 1) • (1 : Matrix (Fin 2) (Fin 2) K)) := by rw [← smul_smul, h1]
      _ = (t - 1)⁻¹ • (1 : Matrix (Fin 2) (Fin 2) K) := by
        rw [smul_smul, hfac, mul_inv, mul_assoc, inv_mul_cancel₀ ht1', mul_one]
  obtain ⟨c, hc⟩ : ∃ c : K, c = (t - 1)⁻¹ := ⟨_, rfl⟩
  rw [← hc] at hscal
  have hc2 : c * c = 1 := by
    have h := hdet
    rw [hscal] at h
    simpa using h
  have hc3 : c ^ 3 = 1 := by
    have h := hM3
    rw [hscal, smul_pow, one_pow] at h
    have h00 := congrFun (congrFun h 0) 0
    simpa using h00
  have hc1 : c = 1 := by
    have e : c ^ 3 = c * (c * c) := by ring
    rw [hc2, mul_one] at e
    rw [← e, hc3]
  apply hg1
  ext i j
  have h := congrFun (congrFun hscal i) j
  rw [hc1, one_smul, hM] at h
  simpa using h

theorem threeRankLeOne_SL2' (h3 : (3 : K) ≠ 0) :
    ThreeRankLeOne (Matrix.SpecialLinearGroup (Fin 2) K) := by
  intro a b ha hb hab ha1
  by_cases hb1 : b = 1
  · rw [hb1]
    exact Subgroup.one_mem _
  by_cases hab1 : a * b = 1
  · rw [eq_inv_of_mul_eq_one_right hab1]
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers a)
  have hc : Commute a b := hab
  have hab3 : (a * b) ^ 3 = 1 := by rw [hc.mul_pow, ha, hb, one_mul]
  have hA := sq_add_one_of_pow_three' ha ha1
  have hB := sq_add_one_of_pow_three' hb hb1
  have hAB := sq_add_one_of_pow_three' hab3 hab1
  set A : Matrix (Fin 2) (Fin 2) K := (a : Matrix (Fin 2) (Fin 2) K)
  set B : Matrix (Fin 2) (Fin 2) K := (b : Matrix (Fin 2) (Fin 2) K)
  have hcAB : Commute A B := by
    change A * B = B * A
    rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul, hab]
  rw [Matrix.SpecialLinearGroup.coe_mul, hcAB.mul_pow] at hAB
  have hA2 : A ^ 2 = -A - 1 := by
    rw [← sub_eq_zero, ← hA]
    abel
  have hB2 : B ^ 2 = -B - 1 := by
    rw [← sub_eq_zero, ← hB]
    abel
  rw [hA2, hB2] at hAB
  have hS : 2 • (A * B) + A + B + 2 • (1 : Matrix (Fin 2) (Fin 2) K) = 0 := by
    rw [← hAB]
    noncomm_ring
  have hAA : A * A = -A - 1 := by rw [← pow_two]; exact hA2
  have key : (2 • A + 1) * (2 • (A * B) + A + B + 2 • (1 : Matrix (Fin 2) (Fin 2) K)) =
      3 • (A - B) := by
    have e1 : (2 • A + 1) * (2 • (A * B) + A + B + 2 • (1 : Matrix (Fin 2) (Fin 2) K)) =
        4 • (A * A * B) + 2 • (A * A) + 4 • (A * B) + 5 • A + B +
          2 • (1 : Matrix (Fin 2) (Fin 2) K) := by
      noncomm_ring
    rw [e1, hAA]
    noncomm_ring
  rw [hS, mul_zero] at key
  have hAB0 : A - B = 0 := by
    have h' : (3 : K) • (A - B) = 0 := by
      have e : (3 : K) • (A - B) = 3 • (A - B) := by
        rw [← Nat.cast_smul_eq_nsmul K]
        norm_num
      rw [e]
      exact key.symm
    exact (smul_eq_zero.mp h').resolve_left h3
  rw [show b = a from Subtype.ext (sub_eq_zero.mp hAB0).symm]
  exact Subgroup.mem_zpowers a

end SL2'

section Hom

variable {X : Type} [Group X]

theorem eq_one_of_pow_three_of_coprime' {N : Subgroup X} [Finite N]
    (hN : Nat.Coprime 3 (Nat.card N)) {x : X} (hx : x ∈ N) (h3 : x ^ 3 = 1) : x = 1 := by
  have h1 : orderOf (⟨x, hx⟩ : N) ∣ 3 :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using h3))
  have h2 : orderOf (⟨x, hx⟩ : N) ∣ Nat.card N := orderOf_dvd_natCard _
  have h := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hN) h2
  exact congrArg Subtype.val (orderOf_eq_one_iff.mp h)

theorem threeRankLeOne_of_hom' {K : Type*} [Field K] (h3 : (3 : K) ≠ 0)
    (ψ : X →* Matrix.SpecialLinearGroup (Fin 2) K)
    (hker : ∀ x ∈ ψ.ker, x ^ 3 = 1 → x = 1) : ThreeRankLeOne X := by
  intro a b ha hb hab ha1
  have hψa1 : ψ a ≠ 1 := fun h => ha1 (hker a h ha)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp
    (threeRankLeOne_SL2' h3 (ψ a) (ψ b) (by rw [← map_pow, ha, map_one])
      (by rw [← map_pow, hb, map_one]) (by rw [← map_mul, ← map_mul, hab]) hψa1)
  have hmem : b * (a ^ k)⁻¹ ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_zpow, hk, mul_inv_cancel]
  have hcomm : Commute b ((a ^ k)⁻¹) := (Commute.zpow_left (hab : Commute a b) k).symm.inv_right
  have hc3 : (b * (a ^ k)⁻¹) ^ 3 = 1 := by
    rw [hcomm.mul_pow, hb, one_mul, inv_pow, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, ha, one_zpow, inv_one]
  have h1 := hker _ hmem hc3
  rw [mul_inv_eq_one] at h1
  rw [h1]
  exact Subgroup.zpow_mem_zpowers a k

variable [Finite X]

theorem threeRankLeOne_of_case3' (h : A36Case3 X) : ThreeRankLeOne X := by
  obtain ⟨p, hp, hp3, -, ⟨eF⟩, e, ψ, -, hψk, -⟩ := h
  have : Fact p.Prime := ⟨hp⟩
  have h3 : (3 : ZMod p) ≠ 0 := by
    intro h0
    have h1 : ((3 : ℕ) : ZMod p) = 0 := by exact_mod_cast h0
    rw [ZMod.natCast_eq_zero_iff] at h1
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h1
    omega
  refine threeRankLeOne_of_hom' h3 ψ fun x hx hx3 => ?_
  rw [hψk] at hx
  have hcard : Nat.card ↥(CFSG.fittingSubgroup X) = p ^ 2 := by
    rw [Nat.card_congr eF.toEquiv, Nat.card_eq_fintype_card]
    simp
  have : Finite ↥(CFSG.fittingSubgroup X) := inferInstance
  refine eq_one_of_pow_three_of_coprime' ?_ hx hx3
  rw [hcard]
  exact Nat.Coprime.pow_right 2 ((Nat.coprime_primes Nat.prime_three hp).mpr (by omega))

theorem threeRankLeOne_of_case4' (h : A36Case4 X) : ThreeRankLeOne X := by
  obtain ⟨-, -, ⟨e⟩, hprimes⟩ := h
  have h3 : (3 : ZMod 5) ≠ 0 := by decide
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set ψ : X →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.fittingSubgroup X)) with hψ
  refine threeRankLeOne_of_hom' h3 ψ fun x hx hx3 => ?_
  have hxF : x ∈ CFSG.fittingSubgroup X := by
    rw [hψ, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
    exact hx
  refine eq_one_of_pow_three_of_coprime' ?_ hxF hx3
  rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
  intro h3F
  have := (hprimes 3 Nat.prime_three h3F).1
  omega

end Hom

end CFSG.Quasithin.Lift3
