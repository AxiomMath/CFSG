module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.GroupTheory.PGroup
public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.RankThree.GF2n.Stroth80.HS9

theorem two_subgroup_gl_two_le {K : Type} [Field K] [Finite K] [CharP K 2]
    {X : Type*} [AddCommGroup X] [Module K X] [Finite X] (hX : Nat.card X = Nat.card K ^ 2)
    (S : Subgroup (X ≃ₗ[K] X)) (hS : IsPGroup 2 S) : Nat.card S ≤ Nat.card K := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  have hq2 : 2 ≤ Nat.card K := by
    have := Finite.one_lt_card (α := K)
    omega
  have hqev : 2 ∣ Nat.card K := by
    obtain ⟨n, -, hqn⟩ := FiniteField.card K 2
    rw [Nat.card_eq_fintype_card, hqn]
    exact dvd_pow_self 2 (PNat.ne_zero n)
  have hfr : Module.finrank K X = 2 := by
    have h := Module.natCard_eq_pow_finrank (K := K) (V := X)
    rw [hX] at h
    exact Nat.pow_right_injective hq2 h.symm
  let b : Module.Basis (Fin 2) K X := Module.finBasisOfFinrankEq K X hfr
  let e : GL (Fin 2) K ≃* (X ≃ₗ[K] X) :=
    (Matrix.GeneralLinearGroup.toLin' b).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv K X)
  have hcardGL : Nat.card (GL (Fin 2) K) =
      (Nat.card K ^ 2 - 1) * (Nat.card K ^ 2 - Nat.card K) := by
    have h := Matrix.card_GL_field (𝔽 := K) (n := 2)
    rw [Fin.prod_univ_two] at h
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one] at h
    rw [← Nat.card_eq_fintype_card] at h
    exact h
  have hcard : Nat.card (X ≃ₗ[K] X) =
      Nat.card K * ((Nat.card K - 1) * (Nat.card K ^ 2 - 1)) := by
    have h2 : Nat.card K ^ 2 - Nat.card K = Nat.card K * (Nat.card K - 1) := by
      rw [Nat.mul_sub_one, sq]
    rw [← Nat.card_congr e.toEquiv, hcardGL, h2]
    ring
  have hfin : Finite (X ≃ₗ[K] X) := Finite.of_equiv _ e.toEquiv
  obtain ⟨k, hk⟩ := hS.exists_card_eq
  have hdvd : Nat.card S ∣ Nat.card (X ≃ₗ[K] X) := Subgroup.card_subgroup_dvd_card S
  rw [hk, hcard] at hdvd
  have hodd1 : Odd (Nat.card K - 1) := by
    obtain ⟨c, hc⟩ := hqev
    exact ⟨c - 1, by omega⟩
  have hodd2 : Odd (Nat.card K ^ 2 - 1) := by
    obtain ⟨c, hc⟩ : 2 ∣ Nat.card K ^ 2 := dvd_pow hqev two_ne_zero
    have hpos : 1 ≤ Nat.card K ^ 2 := Nat.one_le_pow _ _ (by omega)
    exact ⟨c - 1, by omega⟩
  have hcop : Nat.Coprime (2 ^ k) ((Nat.card K - 1) * (Nat.card K ^ 2 - 1)) :=
    (Nat.coprime_two_left.mpr (hodd1.mul hodd2)).pow_left k
  have h2k : 2 ^ k ∣ Nat.card K := hcop.dvd_of_dvd_mul_right hdvd
  rw [hk]
  exact Nat.le_of_dvd Nat.card_pos h2k

section Idx2

variable {K : Type} [Field K] {E : Type*} [AddCommGroup E] [Module K E]

@[expose] noncomputable def idx2_map (S T : Submodule K E) (e : E →ₗ[K] E) (hS : ∀ s ∈ S, e s ∈ S)
    (hT : ∀ t ∈ T, e t ∈ T) : (↥S ⧸ T.comap S.subtype) →ₗ[K] (↥S ⧸ T.comap S.subtype) :=
  Submodule.mapQ _ _ (LinearMap.restrict e hS) fun x hx => by
    simpa using hT x.1 (Submodule.mem_comap.1 hx)

theorem idx2_map_mk (S T : Submodule K E) (e : E →ₗ[K] E) (hS : ∀ s ∈ S, e s ∈ S)
    (hT : ∀ t ∈ T, e t ∈ T) (s : ↥S) :
    idx2_map S T e hS hT (Submodule.Quotient.mk s) =
      Submodule.Quotient.mk (LinearMap.restrict e hS s) :=
  rfl

theorem idx2_map_comp_eq_id (S T : Submodule K E) (e₁ e₂ : E →ₗ[K] E)
    (h₁ : ∀ s ∈ S, e₁ s ∈ S) (h₁' : ∀ t ∈ T, e₁ t ∈ T)
    (h₂ : ∀ s ∈ S, e₂ s ∈ S) (h₂' : ∀ t ∈ T, e₂ t ∈ T) (he : ∀ s, e₁ (e₂ s) = s) :
    (idx2_map S T e₁ h₁ h₁').comp (idx2_map S T e₂ h₂ h₂') = LinearMap.id := by
  apply Submodule.linearMap_qext
  refine LinearMap.ext fun s => ?_
  simp only [LinearMap.comp_apply, Submodule.mkQ_apply, LinearMap.id_apply, idx2_map_mk]
  congr 1
  exact Subtype.ext (he s.1)

theorem idx2_apply_inv {Γ : Type*} [Group Γ] (α : Γ →* (E ≃ₗ[K] E)) (γ : Γ) (s : E) :
    α γ (α γ⁻¹ s) = s :=
  congrArg (fun φ : E ≃ₗ[K] E => φ s)
    (show α γ * α γ⁻¹ = 1 by rw [← map_mul, mul_inv_cancel, map_one])

theorem idx2_inv_apply {Γ : Type*} [Group Γ] (α : Γ →* (E ≃ₗ[K] E)) (γ : Γ) (s : E) :
    α γ⁻¹ (α γ s) = s :=
  congrArg (fun φ : E ≃ₗ[K] E => φ s)
    (show α γ⁻¹ * α γ = 1 by rw [← map_mul, inv_mul_cancel, map_one])

@[expose] noncomputable def idx2_equiv {Γ : Type*} [Group Γ] (S T : Submodule K E)
    (α : Γ →* (E ≃ₗ[K] E)) (hS : ∀ γ, ∀ s ∈ S, α γ s ∈ S) (hT : ∀ γ, ∀ t ∈ T, α γ t ∈ T)
    (γ : Γ) : (↥S ⧸ T.comap S.subtype) ≃ₗ[K] (↥S ⧸ T.comap S.subtype) :=
  LinearEquiv.ofLinearMap (idx2_map S T (α γ).toLinearMap (hS γ) (hT γ))
    (idx2_map S T (α γ⁻¹).toLinearMap (hS γ⁻¹) (hT γ⁻¹))
    (idx2_map_comp_eq_id S T (α γ).toLinearMap (α γ⁻¹).toLinearMap (hS γ) (hT γ)
      (hS γ⁻¹) (hT γ⁻¹) (idx2_apply_inv α γ))
    (idx2_map_comp_eq_id S T (α γ⁻¹).toLinearMap (α γ).toLinearMap (hS γ⁻¹) (hT γ⁻¹)
      (hS γ) (hT γ) (idx2_inv_apply α γ))

theorem idx2_equiv_mk {Γ : Type*} [Group Γ] (S T : Submodule K E)
    (α : Γ →* (E ≃ₗ[K] E)) (hS : ∀ γ, ∀ s ∈ S, α γ s ∈ S) (hT : ∀ γ, ∀ t ∈ T, α γ t ∈ T)
    (γ : Γ) (s : ↥S) :
    idx2_equiv S T α hS hT γ (Submodule.Quotient.mk s) =
      Submodule.Quotient.mk (LinearMap.restrict (α γ).toLinearMap (hS γ) s) :=
  rfl

theorem idx2_equiv_mul {Γ : Type*} [Group Γ] (S T : Submodule K E)
    (α : Γ →* (E ≃ₗ[K] E)) (hS : ∀ γ, ∀ s ∈ S, α γ s ∈ S) (hT : ∀ γ, ∀ t ∈ T, α γ t ∈ T)
    (γ γ' : Γ) (s : ↥S) :
    idx2_equiv S T α hS hT (γ * γ') (Submodule.Quotient.mk s) =
      idx2_equiv S T α hS hT γ (idx2_equiv S T α hS hT γ' (Submodule.Quotient.mk s)) := by
  rw [idx2_equiv_mk, idx2_equiv_mk, idx2_equiv_mk]
  congr 1
  apply Subtype.ext
  exact congrArg (fun φ : E ≃ₗ[K] E => φ s.1) (map_mul α γ γ')

@[expose] noncomputable def idx2_hom {Γ : Type*} [Group Γ] (S T : Submodule K E)
    (α : Γ →* (E ≃ₗ[K] E)) (hS : ∀ γ, ∀ s ∈ S, α γ s ∈ S) (hT : ∀ γ, ∀ t ∈ T, α γ t ∈ T) :
    Γ →* ((↥S ⧸ T.comap S.subtype) ≃ₗ[K] (↥S ⧸ T.comap S.subtype)) :=
  MonoidHom.mk' (idx2_equiv S T α hS hT) fun γ γ' => by
    apply LinearEquiv.ext
    intro x
    obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact idx2_equiv_mul S T α hS hT γ γ' s

theorem idx2_hom_apply {Γ : Type*} [Group Γ] (S T : Submodule K E)
    (α : Γ →* (E ≃ₗ[K] E)) (hS : ∀ γ, ∀ s ∈ S, α γ s ∈ S) (hT : ∀ γ, ∀ t ∈ T, α γ t ∈ T)
    (γ : Γ) : idx2_hom S T α hS hT γ = idx2_equiv S T α hS hT γ :=
  rfl

theorem idx2_hom_eq_one {Γ : Type*} [Group Γ] (S T : Submodule K E)
    (α : Γ →* (E ≃ₗ[K] E)) (hS : ∀ γ, ∀ s ∈ S, α γ s ∈ S) (hT : ∀ γ, ∀ t ∈ T, α γ t ∈ T)
    {γ : Γ} (h : α γ = 1) : idx2_hom S T α hS hT γ = 1 := by
  apply LinearEquiv.ext
  intro x
  obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [idx2_hom_apply, idx2_equiv_mk]
  show _ = Submodule.Quotient.mk s
  exact congrArg Submodule.Quotient.mk (Subtype.ext (congrArg (fun φ : E ≃ₗ[K] E => φ s.1) h))

theorem idx2_mem_ker {Γ : Type*} [Group Γ] (S T : Submodule K E)
    (α : Γ →* (E ≃ₗ[K] E)) (hS : ∀ γ, ∀ s ∈ S, α γ s ∈ S) (hT : ∀ γ, ∀ t ∈ T, α γ t ∈ T)
    (γ : Γ) : γ ∈ (idx2_hom S T α hS hT).ker ↔ ∀ s ∈ S, α γ s - s ∈ T := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h s hs
    have hx := congrArg (fun φ : (↥S ⧸ T.comap S.subtype) ≃ₗ[K] (↥S ⧸ T.comap S.subtype) =>
      φ (Submodule.Quotient.mk ⟨s, hs⟩)) h
    have hx' : Submodule.Quotient.mk (LinearMap.restrict (α γ).toLinearMap (hS γ) ⟨s, hs⟩) =
        Submodule.Quotient.mk ⟨s, hs⟩ := hx
    exact Submodule.mem_comap.1 ((Submodule.Quotient.eq _).1 hx')
  · intro h
    apply LinearEquiv.ext
    intro x
    obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    show Submodule.Quotient.mk (LinearMap.restrict (α γ).toLinearMap (hS γ) s) =
      Submodule.Quotient.mk s
    exact (Submodule.Quotient.eq _).2 (Submodule.mem_comap.2 (h s.1 s.2))

theorem idx2_isPGroup {Γ : Type*} [Group Γ] (S T : Submodule K E)
    (α : Γ →* (E ≃ₗ[K] E)) (hΓ : IsPGroup 2 α.range)
    (hS : ∀ γ, ∀ s ∈ S, α γ s ∈ S) (hT : ∀ γ, ∀ t ∈ T, α γ t ∈ T) :
    IsPGroup 2 (idx2_hom S T α hS hT).range := by
  rintro ⟨x, hx⟩
  obtain ⟨γ, rfl⟩ := MonoidHom.mem_range.1 hx
  obtain ⟨k, hk⟩ := hΓ ⟨α γ, MonoidHom.mem_range.2 ⟨γ, rfl⟩⟩
  have hk' : α γ ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  refine ⟨k, Subtype.ext ?_⟩
  simp only [Subgroup.coe_pow, Subgroup.coe_one]
  rw [← map_pow (idx2_hom S T α hS hT) γ (2 ^ k)]
  apply idx2_hom_eq_one S T α hS hT
  rw [map_pow]
  exact hk'

theorem idx2_card [Finite E] (S T : Submodule K E) (hTS : T ≤ S)
    (hcard : Nat.card S = Nat.card K ^ 2 * Nat.card T) :
    Nat.card (↥S ⧸ T.comap S.subtype) = Nat.card K ^ 2 := by
  have h1 := Submodule.card_eq_card_quotient_mul_card (T.comap S.subtype)
  have h2 : Nat.card ↥(T.comap S.subtype) = Nat.card T :=
    Nat.card_congr (Submodule.comapSubtypeEquivOfLe hTS).toEquiv
  have hpos : 0 < Nat.card T := Nat.card_pos
  have h3 : Nat.card (↥S ⧸ T.comap S.subtype) * Nat.card T = Nat.card ↥S := by
    rw [h1, h2, mul_comm]
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [h3, hcard]

end Idx2

theorem index_le_two_dim {K : Type} [Field K] [Finite K] [CharP K 2]
    {E : Type*} [AddCommGroup E] [Module K E] [Finite E]
    (S T : Submodule K E) (hTS : T ≤ S) (hcard : Nat.card S = Nat.card K ^ 2 * Nat.card T)
    {Γ : Type*} [Group Γ] (α : Γ →* (E ≃ₗ[K] E)) (hΓ : IsPGroup 2 α.range)
    (hS : ∀ γ, ∀ s ∈ S, α γ s ∈ S) (hT : ∀ γ, ∀ t ∈ T, α γ t ∈ T) :
    ∃ C : Subgroup Γ, (∀ γ, γ ∈ C ↔ ∀ s ∈ S, α γ s - s ∈ T) ∧ C.index ≤ Nat.card K := by
  haveI : Finite (↥S ⧸ T.comap S.subtype) := Finite.of_surjective _ (Submodule.mkQ_surjective _)
  refine ⟨(idx2_hom S T α hS hT).ker, idx2_mem_ker S T α hS hT, ?_⟩
  rw [Subgroup.index_ker]
  exact two_subgroup_gl_two_le (idx2_card S T hTS hcard) _ (idx2_isPGroup S T α hΓ hS hT)

end CFSG.RankThree.GF2n.Stroth80.HS9
