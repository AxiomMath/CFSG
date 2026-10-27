module

public import CFSG.Quasithin.Recognition.St84.Gen.Sp4qAmalDefs

import CFSG.Quasithin.Recognition.St84.Gen.G2qAmalVertexTwoCoord
import CFSG.Quasithin.Recognition.St84.Gen.CoprimeComplement

public section

namespace CFSG.Quasithin.F112R.St84

open Matrix
open scoped MatrixGroups

variable {G : Type} [Group G]

section Scalar

variable {F : Type} [Field F]

private theorem eq_of_smul_eq_smul {n : ℕ} {c d : F} {v : Fin n → F} (hv : v ≠ 0)
    (h : c • v = d • v) : c = d := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  have h1 := congrFun h i
  simp only [Pi.smul_apply, smul_eq_mul] at h1
  exact mul_right_cancel₀ hi h1

private theorem exists_scalarHom {n : ℕ} [NeZero n] {X N : Subgroup G}
    (γ : ↥X →* Multiplicative (Fin n → F)) (hγ : Function.Surjective γ)
    (hN : ∀ g ∈ N, ∀ u ∈ X, g * u * g⁻¹ ∈ X)
    (hsc : ∀ g ∈ N, ∃ μ : F, ∀ u v : ↥X, (v : G) = g * u * g⁻¹ →
      Multiplicative.toAdd (γ v) = μ • Multiplicative.toAdd (γ u)) :
    ∃ μ : ↥N →* Fˣ, ∀ (g : ↥N) (u v : ↥X), (v : G) = g * u * g⁻¹ →
      Multiplicative.toAdd (γ v) = (μ g : F) • Multiplicative.toAdd (γ u) := by
  classical
  choose! μ₀ hμ₀ using hsc
  set v₀ : Fin n → F := Pi.single 0 1 with hv₀def
  have hv₀ : v₀ ≠ 0 := by
    intro h
    have h1 := congrFun h 0
    simp [v₀] at h1
  obtain ⟨u₀, hu₀⟩ := hγ (Multiplicative.ofAdd v₀)
  have hu₀' : Multiplicative.toAdd (γ u₀) = v₀ := by rw [hu₀, toAdd_ofAdd]
  have hne : ∀ g ∈ N, μ₀ g ≠ 0 := by
    intro g hg h0
    have hmem : g⁻¹ * u₀ * g⁻¹⁻¹ ∈ X := hN g⁻¹ (N.inv_mem hg) u₀ u₀.2
    have h1 := hμ₀ g hg ⟨g⁻¹ * u₀ * g⁻¹⁻¹, hmem⟩ u₀ (by
      change (u₀ : G) = g * (g⁻¹ * u₀ * g⁻¹⁻¹) * g⁻¹
      group)
    rw [h0, zero_smul, hu₀'] at h1
    exact hv₀ h1
  have hmul : ∀ g ∈ N, ∀ h ∈ N, μ₀ (g * h) = μ₀ g * μ₀ h := by
    intro g hg h hh
    let u₁ : ↥X := ⟨h * u₀ * h⁻¹, hN h hh u₀ u₀.2⟩
    let u₂ : ↥X := ⟨g * u₁ * g⁻¹, hN g hg u₁ u₁.2⟩
    have e1 := hμ₀ h hh u₀ u₁ rfl
    have e2 := hμ₀ g hg u₁ u₂ rfl
    have e3 := hμ₀ (g * h) (N.mul_mem hg hh) u₀ u₂ (by
      change g * (h * (u₀ : G) * h⁻¹) * g⁻¹ = g * h * u₀ * (g * h)⁻¹
      group)
    rw [e2, e1, smul_smul, hu₀'] at e3
    exact (eq_of_smul_eq_smul hv₀ e3).symm
  have hone : μ₀ 1 = 1 := by
    have h1 := hmul 1 N.one_mem 1 N.one_mem
    rw [mul_one] at h1
    exact mul_right_cancel₀ (hne 1 N.one_mem) (by rw [one_mul]; exact h1.symm)
  refine ⟨{ toFun := fun g => Units.mk0 (μ₀ g) (hne g g.2)
            map_one' := Units.ext hone
            map_mul' := fun g h => Units.ext (hmul g g.2 h h.2) }, ?_⟩
  intro g u v huv
  exact hμ₀ g g.2 u v huv

end Scalar

section Odd

variable {Q Z : Subgroup G}

private theorem commutator_mul_central_left' (hZc : ∀ z ∈ Z, ∀ x ∈ Q, z * x = x * z)
    {a b z : G} (hz : z ∈ Z) (hb : b ∈ Q) :
    (a * z) * b * (a * z)⁻¹ * b⁻¹ = a * b * a⁻¹ * b⁻¹ := by
  have h := hZc z hz b hb
  calc (a * z) * b * (a * z)⁻¹ * b⁻¹ = a * (z * b) * z⁻¹ * a⁻¹ * b⁻¹ := by group
    _ = a * (b * z) * z⁻¹ * a⁻¹ * b⁻¹ := by rw [h]
    _ = a * b * a⁻¹ * b⁻¹ := by group

private theorem commutator_mul_central_right' (hZc : ∀ z ∈ Z, ∀ x ∈ Q, z * x = x * z)
    {a b z : G} (hz : z ∈ Z) (ha : a ∈ Q) :
    a * (b * z) * a⁻¹ * (b * z)⁻¹ = a * b * a⁻¹ * b⁻¹ := by
  have h := hZc z hz a⁻¹ (Q.inv_mem ha)
  calc a * (b * z) * a⁻¹ * (b * z)⁻¹ = a * b * (z * a⁻¹) * z⁻¹ * b⁻¹ := by group
    _ = a * b * (a⁻¹ * z) * z⁻¹ * b⁻¹ := by rw [h]
    _ = a * b * a⁻¹ * b⁻¹ := by group

private theorem commutator_mem_of_sq' (hZc : ∀ z ∈ Z, ∀ x ∈ Q, z * x = x * z)
    (hQ2 : ∀ x ∈ Q, x ^ 2 ∈ Z) {x y : G} (hx : x ∈ Q) (hy : y ∈ Q) :
    x * y * x⁻¹ * y⁻¹ ∈ Z := by
  have hx2 := hQ2 x hx
  have hy2 := hQ2 y hy
  have hxy2 := hQ2 (x * y) (Q.mul_mem hx hy)
  have hc : (x ^ 2)⁻¹ * y = y * (x ^ 2)⁻¹ := hZc _ (Z.inv_mem hx2) y hy
  have key : x * y * x⁻¹ * y⁻¹ = (x * y) ^ 2 * (x ^ 2)⁻¹ * (y ^ 2)⁻¹ := by
    calc x * y * x⁻¹ * y⁻¹ = x * y * x * ((x ^ 2)⁻¹ * y) * (y ^ 2)⁻¹ := by
          simp only [sq]; group
      _ = x * y * x * (y * (x ^ 2)⁻¹) * (y ^ 2)⁻¹ := by rw [hc]
      _ = (x * y) ^ 2 * (x ^ 2)⁻¹ * (y ^ 2)⁻¹ := by simp only [sq]; group
  rw [key]
  exact Z.mul_mem (Z.mul_mem hxy2 (Z.inv_mem hx2)) (Z.inv_mem hy2)

private theorem conj_commutator_eq (hZQ : Z ≤ Q) (hZc : ∀ z ∈ Z, ∀ x ∈ Q, z * x = x * z)
    {n : G} (htriv : ∀ u ∈ Q, u⁻¹ * (n * u * n⁻¹) ∈ Z) {a b : G} (ha : a ∈ Q) (hb : b ∈ Q) :
    n * (a * b * a⁻¹ * b⁻¹) * n⁻¹ = a * b * a⁻¹ * b⁻¹ := by
  have h1 : n * (a * b * a⁻¹ * b⁻¹) * n⁻¹ =
      (a * (a⁻¹ * (n * a * n⁻¹))) * (b * (b⁻¹ * (n * b * n⁻¹))) *
        (a * (a⁻¹ * (n * a * n⁻¹)))⁻¹ * (b * (b⁻¹ * (n * b * n⁻¹)))⁻¹ := by group
  rw [h1, commutator_mul_central_left' hZc (htriv a ha) (Q.mul_mem hb (hZQ (htriv b hb))),
    commutator_mul_central_right' hZc (htriv b hb) ha]

private theorem conj_eq_of_odd (hZ2 : ∀ z ∈ Z, z * z = 1) {n : G} {k : ℕ} (hk : Odd k)
    (hnk : n ^ k = 1) (htriv : ∀ u ∈ Q, u⁻¹ * (n * u * n⁻¹) ∈ Z)
    (hfix : ∀ z ∈ Z, n * z * n⁻¹ = z) {u : G} (hu : u ∈ Q) : n * u * n⁻¹ = u := by
  set z := u⁻¹ * (n * u * n⁻¹) with hz
  have hzZ : z ∈ Z := htriv u hu
  have hnu : n * u * n⁻¹ = u * z := by rw [hz]; group
  have hpow : ∀ j : ℕ, n ^ j * u * (n ^ j)⁻¹ = u * z ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hzj : z ^ j ∈ Z := Z.pow_mem hzZ j
      calc n ^ (j + 1) * u * (n ^ (j + 1))⁻¹ = n * (n ^ j * u * (n ^ j)⁻¹) * n⁻¹ := by group
        _ = n * (u * z ^ j) * n⁻¹ := by rw [ih]
        _ = (n * u * n⁻¹) * (n * z ^ j * n⁻¹) := by group
        _ = u * z * z ^ j := by rw [hnu, hfix _ hzj]
        _ = u * z ^ (j + 1) := by rw [pow_succ', mul_assoc]
  have h1 := hpow k
  rw [hnk, one_mul, inv_one, mul_one] at h1
  have hzk : z ^ k = 1 := mul_left_cancel (h1.symm.trans (mul_one u).symm)
  obtain ⟨m, rfl⟩ := hk
  have hz2 : z ^ 2 = 1 := by rw [sq]; exact hZ2 z hzZ
  rw [pow_succ, pow_mul, hz2, one_pow, one_mul] at hzk
  rw [hnu, hzk, mul_one]

end Odd

section Torus

variable {F : Type} [Field F] [Finite F] [CharP F 2] {L Q Z N : Subgroup G}

theorem exists_torus_radCoord (hF : 4 ≤ Nat.card F) (hZQ : Z ≤ Q)
    (hZc : ∀ z ∈ Z, ∀ x ∈ Q, z * x = x * z) (hQ2 : ∀ x ∈ Q, x ^ 2 ∈ Z)
    (hZcen : ∀ x ∈ Q, (∀ y ∈ Q, x * y = y * x) → x ∈ Z)
    (hLQ : ∀ ℓ ∈ L, ∀ u ∈ Q, ℓ * u * ℓ⁻¹ ∈ Q) (hLZ : ∀ ℓ ∈ L, ∀ z ∈ Z, ℓ * z * ℓ⁻¹ ∈ Z)
    (α : ↥L →* SL(2, F)) (hα : Function.Surjective α)
    (γ : ↥Q →* Multiplicative (Fin 3 → F)) (hγ : Function.Surjective γ)
    (hγker : γ.ker = Z.subgroupOf Q)
    (hγeq : ∀ (ℓ : ↥L) (u v : ↥Q), (v : G) = ℓ * u * ℓ⁻¹ →
      Multiplicative.toAdd (γ v) = (sp4RadMat (α ℓ)).mulVec (Multiplicative.toAdd (γ u)))
    (δ : ↥Z ≃* Multiplicative (Fin 2 → F))
    (hδeq : ∀ (ℓ : ↥L) (u v : ↥Z), (v : G) = ℓ * u * ℓ⁻¹ →
      Multiplicative.toAdd (δ v) =
        (α ℓ : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (δ u)))
    (hNQ : ∀ n ∈ N, ∀ u ∈ Q, n * u * n⁻¹ ∈ Q) (hNZ : ∀ n ∈ N, ∀ z ∈ Z, n * z * n⁻¹ ∈ Z)
    (hNL : ∀ n ∈ N, ∀ ℓ : ↥L, ∃ ℓ' : ↥L, (ℓ' : G) = n * ℓ * n⁻¹ ∧ α ℓ' = α ℓ)
    (hNodd : Odd (Nat.card N)) (hNcard : Nat.card N = Nat.card F - 1)
    (hNQ1 : ∀ n ∈ N, (∀ u ∈ Q, n * u * n⁻¹ = u) → n = 1) :
    ∃ τ : ↥N ≃* Fˣ, ∃ c : F, c ≠ 0 ∧
      (∀ (n : ↥N) (u v : ↥Q), (v : G) = n * u * n⁻¹ →
        Multiplicative.toAdd (γ v) = ((τ n : F) ^ 2) • Multiplicative.toAdd (γ u)) ∧
      (∀ (n : ↥N) (z w : ↥Z), (w : G) = n * z * n⁻¹ →
        Multiplicative.toAdd (δ w) = ((τ n : F) ^ 3) • Multiplicative.toAdd (δ z)) ∧
      ∀ (u : ↥Q) (hu : (u : G) ^ 2 ∈ Z) (x b₀ b₁ : F),
        Multiplicative.toAdd (γ u) = ![x, b₀ ^ 2, b₁ ^ 2] →
          Multiplicative.toAdd (δ ⟨(u : G) ^ 2, hu⟩) = (c * (x + b₀ * b₁)) • ![b₀, b₁] := by
  classical
  obtain ⟨μ, hμ⟩ := exists_scalarHom γ hγ hNQ fun n hn =>
    exists_smul_radCoord_conj hF hLQ α hα γ hγ hγker hγeq (hNQ n hn) (hNZ n hn) (hNL n hn)
  obtain ⟨lam, hlam'⟩ := exists_scalarHom δ.toMonoidHom δ.surjective hNZ fun n hn =>
    exists_smul_natCoord_conj hLZ α hα δ hδeq (hNZ n hn) (hNL n hn)
  have hlam : ∀ (n : ↥N) (z w : ↥Z), (w : G) = n * z * n⁻¹ →
      Multiplicative.toAdd (δ w) = (lam n : F) • Multiplicative.toAdd (δ z) := hlam'
  have hZ2 : ∀ z ∈ Z, z * z = 1 := by
    intro z hz
    have h1 : δ (⟨z, hz⟩ * ⟨z, hz⟩) = δ 1 := by
      rw [map_mul, map_one]
      apply Multiplicative.toAdd.injective
      rw [toAdd_mul, toAdd_one]
      ext i
      simp only [Pi.add_apply, Pi.zero_apply]
      exact CharTwo.add_self_eq_zero _
    exact congrArg Subtype.val (δ.injective h1)
  have hdiff : ∀ u u' : ↥Q, γ u = γ u' → (u : G)⁻¹ * u' ∈ Z := by
    intro u u' h
    have h1 : u⁻¹ * u' ∈ γ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
    rw [hγker] at h1
    exact Subgroup.mem_subgroupOf.mp h1
  obtain ⟨u₀, hu₀⟩ := hγ (Multiplicative.ofAdd ![1, 0, 0])
  have hu₀Z : (u₀ : G) ∉ Z := by
    intro h
    have h1 : u₀ ∈ γ.ker := by rw [hγker]; exact Subgroup.mem_subgroupOf.mpr h
    rw [MonoidHom.mem_ker, hu₀, ← ofAdd_zero] at h1
    have h2 := congrFun (Multiplicative.ofAdd.injective h1) 0
    simp at h2
  obtain ⟨y, hyQ, hyu⟩ : ∃ y ∈ Q, (u₀ : G) * y ≠ y * u₀ := by
    by_contra hcon
    push Not at hcon
    exact hu₀Z (hZcen _ u₀.2 hcon)
  have hcZ := commutator_mem_of_sq' hZc hQ2 u₀.2 hyQ
  have hδc : Multiplicative.toAdd (δ ⟨_, hcZ⟩) ≠ 0 := by
    intro h0
    apply hyu
    have h1 : δ ⟨_, hcZ⟩ = δ 1 := by
      rw [map_one]
      exact Multiplicative.toAdd.injective (by rw [h0, toAdd_one])
    have h2 := congrArg Subtype.val (δ.injective h1)
    change (u₀ : G) * y * (u₀ : G)⁻¹ * y⁻¹ = 1 at h2
    calc (u₀ : G) * y = ((u₀ : G) * y * (u₀ : G)⁻¹ * y⁻¹) * y * u₀ := by group
      _ = y * u₀ := by rw [h2, one_mul]
  have hμinj : Function.Injective μ := by
    rw [injective_iff_map_eq_one]
    intro n hn1
    have htriv : ∀ u ∈ Q, u⁻¹ * (n * u * n⁻¹) ∈ Z := by
      intro u hu
      have h := hμ n ⟨u, hu⟩ ⟨n * u * n⁻¹, hNQ n n.2 u hu⟩ rfl
      rw [hn1, Units.val_one, one_smul] at h
      exact hdiff ⟨u, hu⟩ _ (Multiplicative.toAdd.injective h).symm
    have hlam1 : lam n = 1 := by
      have h := hlam n ⟨_, hcZ⟩ ⟨_, hcZ⟩ (conj_commutator_eq hZQ hZc htriv u₀.2 hyQ).symm
      have h' : (1 : F) • Multiplicative.toAdd (δ ⟨_, hcZ⟩) =
          ((lam n : Fˣ) : F) • Multiplicative.toAdd (δ ⟨_, hcZ⟩) := by
        rw [one_smul]; exact h
      exact Units.ext (eq_of_smul_eq_smul hδc h').symm
    have hfixZ : ∀ z ∈ Z, n * z * n⁻¹ = z := by
      intro z hz
      have h := hlam n ⟨z, hz⟩ ⟨n * z * n⁻¹, hNZ n n.2 z hz⟩ rfl
      rw [hlam1, Units.val_one, one_smul] at h
      exact congrArg Subtype.val (δ.injective (Multiplicative.toAdd.injective h))
    have hnk : (n : G) ^ Nat.card N = 1 := by
      rw [← Subgroup.coe_pow, pow_card_eq_one', Subgroup.coe_one]
    exact Subtype.ext (hNQ1 n n.2 fun u hu => conj_eq_of_odd hZ2 hNodd hnk htriv hfixZ hu)
  have hμbij : Function.Bijective μ :=
    hμinj.bijective_of_nat_card_le (by rw [Nat.card_units, hNcard])
  have hsqinj : Function.Injective (powMonoidHom 2 : Fˣ →* Fˣ) := by
    intro s t h
    apply Units.ext
    have h1 : (s : F) ^ 2 = (t : F) ^ 2 := by
      have := congrArg Units.val h
      simpa using this
    exact CharTwo.sq_injective h1
  let sqE : Fˣ ≃* Fˣ := MulEquiv.ofBijective (powMonoidHom 2) (Finite.injective_iff_bijective.mp hsqinj)
  let τ : ↥N ≃* Fˣ := (MulEquiv.ofBijective μ hμbij).trans sqE.symm
  have hτ : ∀ n : ↥N, ((τ n : Fˣ) : F) ^ 2 = (μ n : F) := by
    intro n
    have h : (τ n) ^ 2 = μ n := sqE.apply_symm_apply (μ n)
    rw [← Units.val_pow_eq_pow_val, h]
  have hγτ : ∀ (n : ↥N) (u v : ↥Q), (v : G) = n * u * n⁻¹ →
      Multiplicative.toAdd (γ v) = ((τ n : F) ^ 2) • Multiplicative.toAdd (γ u) := by
    intro n u v h
    rw [hτ]
    exact hμ n u v h
  have hlamτ : ∀ n : ↥N, (lam n : F) = (τ n : F) ^ 3 := by
    intro n
    by_cases h1 : (τ n : F) = 1
    · have hn : n = 1 := τ.injective (by rw [map_one]; exact Units.ext h1)
      rw [hn, map_one, map_one, Units.val_one, one_pow]
    · obtain ⟨c, -, hχ, -⟩ := exists_sq_radCoord hZc hQ2 hZcen hLQ α hα γ hγ hγker hγeq δ
        hδeq (hNQ n n.2) (Units.ne_zero _) h1 (hγτ n) (hlam n)
      exact hχ
  obtain ⟨t, ht⟩ : ∃ t : Fˣ, t ≠ 1 := by
    haveI : Nontrivial Fˣ := Finite.one_lt_card_iff_nontrivial.mp (by rw [Nat.card_units]; omega)
    exact exists_ne 1
  have ht' : ((τ (τ.symm t) : Fˣ) : F) ≠ 1 := by
    rw [MulEquiv.apply_symm_apply]
    exact fun h => ht (Units.ext h)
  obtain ⟨c, hc0, -, hform⟩ := exists_sq_radCoord hZc hQ2 hZcen hLQ α hα γ hγ hγker hγeq δ
    hδeq (hNQ _ (τ.symm t).2) (Units.ne_zero _) ht' (hγτ _) (hlam _)
  refine ⟨τ, c, hc0, hγτ, fun n z w h => ?_, hform⟩
  rw [← hlamτ]
  exact hlam n z w h

theorem eq_one_of_commute_torus_radCoord (hF : 8 ≤ Nat.card F)
    (γ : ↥Q →* Multiplicative (Fin 3 → F)) (hγker : γ.ker = Z.subgroupOf Q)
    (δ : ↥Z ≃* Multiplicative (Fin 2 → F)) (τ : ↥N ≃* Fˣ)
    (hτγ : ∀ (n : ↥N) (u v : ↥Q), (v : G) = n * u * n⁻¹ →
      Multiplicative.toAdd (γ v) = ((τ n : F) ^ 2) • Multiplicative.toAdd (γ u))
    (hτδ : ∀ (n : ↥N) (z w : ↥Z), (w : G) = n * z * n⁻¹ →
      Multiplicative.toAdd (δ w) = ((τ n : F) ^ 3) • Multiplicative.toAdd (δ z))
    {x : G} (hxQ : x ∈ Q) (hx : ∀ n ∈ N, n * x * n⁻¹ = x) : x = 1 := by
  classical
  have hcardU : 7 ≤ Nat.card Fˣ := by rw [Nat.card_units]; omega
  obtain ⟨t, ht⟩ : ∃ t : Fˣ, t ≠ 1 := by
    haveI : Nontrivial Fˣ := Finite.one_lt_card_iff_nontrivial.mp (by omega)
    exact exists_ne 1
  obtain ⟨s, hs⟩ : ∃ s : Fˣ, s ^ 3 ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have h1 : Monoid.exponent Fˣ ∣ 3 := Monoid.exponent_dvd_of_forall_pow_eq_one hcon
    rw [IsCyclic.exponent_eq_card] at h1
    have := Nat.le_of_dvd (by norm_num) h1
    omega
  have hγx : γ ⟨x, hxQ⟩ = 1 := by
    by_contra hne
    have hv : Multiplicative.toAdd (γ ⟨x, hxQ⟩) ≠ 0 := fun h0 =>
      hne (Multiplicative.toAdd.injective (h0.trans toAdd_one.symm))
    have h := hτγ (τ.symm t) ⟨x, hxQ⟩ ⟨x, hxQ⟩ (hx _ (τ.symm t).2).symm
    rw [MulEquiv.apply_symm_apply] at h
    have h' : ((t : F) ^ 2) • Multiplicative.toAdd (γ ⟨x, hxQ⟩) =
        (1 : F) • Multiplicative.toAdd (γ ⟨x, hxQ⟩) := by rw [one_smul]; exact h.symm
    have ht2 := eq_of_smul_eq_smul hv h'
    apply ht
    apply Units.ext
    exact CharTwo.sq_injective (ht2.trans (one_pow 2).symm)
  have hxZ : x ∈ Z := by
    have h1 : (⟨x, hxQ⟩ : ↥Q) ∈ γ.ker := hγx
    rw [hγker] at h1
    exact Subgroup.mem_subgroupOf.mp h1
  by_contra hx1
  have hv : Multiplicative.toAdd (δ ⟨x, hxZ⟩) ≠ 0 := by
    intro h0
    have h1 : δ ⟨x, hxZ⟩ = δ 1 := by
      rw [map_one]; exact Multiplicative.toAdd.injective (h0.trans toAdd_one.symm)
    exact hx1 (congrArg Subtype.val (δ.injective h1))
  have h := hτδ (τ.symm s) ⟨x, hxZ⟩ ⟨x, hxZ⟩ (hx _ (τ.symm s).2).symm
  rw [MulEquiv.apply_symm_apply] at h
  have h' : ((s : F) ^ 3) • Multiplicative.toAdd (δ ⟨x, hxZ⟩) =
      (1 : F) • Multiplicative.toAdd (δ ⟨x, hxZ⟩) := by rw [one_smul]; exact h.symm
  apply hs
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one]
  exact eq_of_smul_eq_smul hv h'

end Torus

section Levi

variable {F : Type} [Field F]

theorem exists_leviHom_of_torus [Finite G] {L Q N : Subgroup G} (hQL : Q ≤ L)
    (hLQ : L ≤ Subgroup.normalizer (Q : Set G)) (hNQ : N ≤ Subgroup.normalizer (Q : Set G))
    (hcop : Nat.Coprime (Nat.card N) (Nat.card Q))
    (hcomm : ∀ n ∈ N, ∀ l ∈ L, n * l * n⁻¹ * l⁻¹ ∈ Q)
    (hfix : ∀ x ∈ Q, (∀ n ∈ N, n * x * n⁻¹ = x) → x = 1) (hNL : N ⊓ L = ⊥)
    (α : ↥L →* SL(2, F)) (hα : Function.Surjective α)
    (hker : ∀ x : ↥L, α x = 1 ↔ (x : G) ∈ Q) (τ : ↥N ≃* Fˣ) :
    ∃ ε : SL(2, F) × Fˣ →* G, Function.Injective ε ∧
      (∀ g : SL(2, F), ∃ hg : ε (g, 1) ∈ L, α ⟨ε (g, 1), hg⟩ = g) ∧
      (∀ t : Fˣ, ∃ ht : ε (1, t) ∈ N, τ ⟨ε (1, t), ht⟩ = t) ∧
      (∀ p : SL(2, F) × Fˣ, ε p = ε (p.1, 1) * ε (1, p.2)) ∧
      Q ⊔ ε.range = L ⊔ N ∧ Disjoint Q ε.range ∧
      ∀ x : ↥L, ∃ v ∈ Q, (x : G) = v * ε (α x, 1) := by
  classical
  set K := L ⊓ Subgroup.centralizer (N : Set G) with hKdef
  have hsup : Q ⊔ K = L := sup_inf_centralizer_eq_of_coprime hQL hLQ hNQ hcop hcomm
  have hinf : K ⊓ Q = ⊥ := inf_centralizer_inf_eq_bot_of_fixed hfix
  have hKL : K ≤ L := inf_le_left
  let αK : ↥K →* SL(2, F) := α.comp (Subgroup.inclusion hKL)
  have hαK_inj : Function.Injective αK := by
    rw [injective_iff_map_eq_one]
    intro k hk
    have hkQ : (k : G) ∈ Q := (hker (Subgroup.inclusion hKL k)).mp hk
    have h1 : (k : G) ∈ K ⊓ Q := ⟨k.2, hkQ⟩
    rw [hinf, Subgroup.mem_bot] at h1
    exact Subtype.ext h1
  have hdecomp : ∀ x : ↥L, ∃ v ∈ Q, ∃ k : ↥K, (x : G) = v * k := by
    intro x
    obtain ⟨v, hv, k, hk, hx⟩ :=
      exists_mul_mem_inf_centralizer_of_coprime hQL hLQ hNQ hcop hcomm x.2
    exact ⟨v, hv, ⟨k, hk⟩, hx⟩
  have hαdec : ∀ (x : ↥L) (v : G) (hv : v ∈ Q) (k : ↥K), (x : G) = v * k → α x = αK k := by
    intro x v hv k hx
    have hx' : x = ⟨v, hQL hv⟩ * Subgroup.inclusion hKL k := Subtype.ext hx
    rw [hx', map_mul, (hker _).mpr hv, one_mul]
    rfl
  have hαK_surj : Function.Surjective αK := by
    intro g
    obtain ⟨x, rfl⟩ := hα g
    obtain ⟨v, hv, k, hx⟩ := hdecomp x
    exact ⟨k, (hαdec x v hv k hx).symm⟩
  let e₁ : ↥K ≃* SL(2, F) := MulEquiv.ofBijective αK ⟨hαK_inj, hαK_surj⟩
  let κ : SL(2, F) →* G := K.subtype.comp e₁.symm.toMonoidHom
  let ν : Fˣ →* G := N.subtype.comp τ.symm.toMonoidHom
  have hκK : ∀ g, κ g ∈ K := fun g => (e₁.symm g).2
  have hνN : ∀ t, ν t ∈ N := fun t => (τ.symm t).2
  have hκL : ∀ g, κ g ∈ L := fun g => hKL (hκK g)
  have hcomm' : ∀ g t, Commute (κ g) (ν t) := by
    intro g t
    exact ((Subgroup.mem_centralizer_iff.mp (hκK g).2) (ν t) (hνN t)).symm
  have hκ_inj : Function.Injective κ := fun a b h => e₁.symm.injective (Subtype.ext h)
  have hν_inj : Function.Injective ν := fun a b h => τ.symm.injective (Subtype.ext h)
  have hκe : ∀ k : ↥K, κ (e₁ k) = k := by
    intro k
    change ((e₁.symm (e₁ k) : ↥K) : G) = k
    rw [MulEquiv.symm_apply_apply]
  have hντ : ∀ n : ↥N, ν (τ n) = n := by
    intro n
    change ((τ.symm (τ n) : ↥N) : G) = n
    rw [MulEquiv.symm_apply_apply]
  have hNLmem : ∀ x, x ∈ N → x ∈ L → x = 1 := by
    intro x hxN hxL
    have h1 : x ∈ N ⊓ L := ⟨hxN, hxL⟩
    rwa [hNL, Subgroup.mem_bot] at h1
  let ε : SL(2, F) × Fˣ →* G := κ.noncommCoprod ν hcomm'
  have hε : ∀ p, ε p = κ p.1 * ν p.2 := fun p => rfl
  have hεg : ∀ g, ε (g, 1) = κ g := by
    intro g
    rw [hε]
    change κ g * ν 1 = κ g
    rw [map_one, mul_one]
  have hεt : ∀ t, ε (1, t) = ν t := by
    intro t
    rw [hε]
    change κ 1 * ν t = ν t
    rw [map_one, one_mul]
  refine ⟨ε, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [injective_iff_map_eq_one]
    rintro ⟨g, t⟩ h
    change κ g * ν t = 1 at h
    have hνt : ν t = (κ g)⁻¹ := eq_inv_of_mul_eq_one_right h
    have h1 : ν t = 1 := hNLmem _ (hνN t) (by rw [hνt]; exact L.inv_mem (hκL g))
    have h2 : κ g = 1 := by rw [h1, mul_one] at h; exact h
    exact Prod.ext (hκ_inj (h2.trans (map_one κ).symm)) (hν_inj (h1.trans (map_one ν).symm))
  · intro g
    refine ⟨hεg g ▸ hκL g, ?_⟩
    have h1 : (⟨ε (g, 1), hεg g ▸ hκL g⟩ : ↥L) = Subgroup.inclusion hKL (e₁.symm g) :=
      Subtype.ext (hεg g)
    rw [h1]
    change e₁ (e₁.symm g) = g
    exact e₁.apply_symm_apply g
  · intro t
    refine ⟨hεt t ▸ hνN t, ?_⟩
    have h1 : (⟨ε (1, t), hεt t ▸ hνN t⟩ : ↥N) = τ.symm t := Subtype.ext (hεt t)
    rw [h1, MulEquiv.apply_symm_apply]
  · intro p
    rw [hεg, hεt]
    exact hε p
  · apply le_antisymm
    · refine sup_le (hQL.trans le_sup_left) ?_
      rintro _ ⟨p, rfl⟩
      rw [hε]
      exact (L ⊔ N).mul_mem (Subgroup.mem_sup_left (hκL _)) (Subgroup.mem_sup_right (hνN _))
    · refine sup_le ?_ ?_
      · rw [← hsup]
        refine sup_le le_sup_left ?_
        intro k hk
        exact Subgroup.mem_sup_right ⟨(e₁ ⟨k, hk⟩, 1), by rw [hεg, hκe]⟩
      · intro n hn
        exact Subgroup.mem_sup_right ⟨(1, τ ⟨n, hn⟩), by rw [hεt, hντ]⟩
  · rw [Subgroup.disjoint_def]
    rintro x hxQ ⟨⟨g, t⟩, rfl⟩
    change κ g * ν t ∈ Q at hxQ
    change κ g * ν t = 1
    have h1 : ν t ∈ L := by
      have h2 : ν t = (κ g)⁻¹ * (κ g * ν t) := by group
      rw [h2]
      exact L.mul_mem (L.inv_mem (hκL g)) (hQL hxQ)
    have h2 : ν t = 1 := hNLmem _ (hνN t) h1
    rw [h2, mul_one] at hxQ ⊢
    have h3 : κ g ∈ K ⊓ Q := ⟨hκK g, hxQ⟩
    rwa [hinf, Subgroup.mem_bot] at h3
  · intro x
    obtain ⟨v, hv, k, hx⟩ := hdecomp x
    refine ⟨v, hv, ?_⟩
    rw [hεg, hαdec x v hv k hx]
    change (x : G) = v * κ (e₁ k)
    rw [hκe]
    exact hx

end Levi

end CFSG.Quasithin.F112R.St84

end
