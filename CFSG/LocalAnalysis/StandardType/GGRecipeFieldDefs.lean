module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseNoBL5Aut
public import CFSG.LocalAnalysis.StandardType.GGLFourFourThreeMarking
public import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGRawInnFieldOn (S : LargeEvenLabel → Prop) : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → S lab →
    LargeEvenLabelAll lab (GGRawInnField p)

@[expose] def GGRawFieldCentralOn (S : LargeEvenLabel → Prop) : Prop :=
  ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → S lab → LargeEvenLabelAll lab GGRawFieldCentral

@[expose] def GGRawFieldConjOn (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → S p lab →
    LargeEvenLabelAll lab (GGRawFieldConj p)

@[expose] def GGRawFieldConjInputExc : Prop :=
  GGRawFieldConjOn fun p lab => ¬ (lab.tag = .triD4 ∧ p = 3)

theorem GGRawInnFieldOn.mono {S S' : LargeEvenLabel → Prop} (hS : ∀ lab, S' lab → S lab)
    (h : GGRawInnFieldOn S) : GGRawInnFieldOn S' :=
  fun p hp hp2 lab hlab hS' => h p hp hp2 lab hlab (hS lab hS')

theorem GGRawInnFieldOn.or {S S' : LargeEvenLabel → Prop} (h : GGRawInnFieldOn S)
    (h' : GGRawInnFieldOn S') : GGRawInnFieldOn fun lab => S lab ∨ S' lab := by
  rintro p hp hp2 lab hlab (hS | hS)
  · exact h p hp hp2 lab hlab hS
  · exact h' p hp hp2 lab hlab hS

theorem ggRawInnFieldInput_of_on {S : LargeEvenLabel → Prop} (hS : ∀ lab, LargeEvenInLambda2 lab → S lab)
    (h : GGRawInnFieldOn S) : GGRawInnFieldInput :=
  fun p hp hp2 lab hlab => h p hp hp2 lab hlab (hS lab hlab)

theorem GGRawFieldCentralOn.mono {S S' : LargeEvenLabel → Prop} (hS : ∀ lab, S' lab → S lab)
    (h : GGRawFieldCentralOn S) : GGRawFieldCentralOn S' :=
  fun lab hlab hS' => h lab hlab (hS lab hS')

theorem GGRawFieldCentralOn.or {S S' : LargeEvenLabel → Prop} (h : GGRawFieldCentralOn S)
    (h' : GGRawFieldCentralOn S') : GGRawFieldCentralOn fun lab => S lab ∨ S' lab := by
  rintro lab hlab (hS | hS)
  · exact h lab hlab hS
  · exact h' lab hlab hS

theorem ggRawFieldCentralInput_of_on {S : LargeEvenLabel → Prop}
    (hS : ∀ lab, LargeEvenInLambda2 lab → S lab) (h : GGRawFieldCentralOn S) :
    GGRawFieldCentralInput :=
  fun lab hlab => h lab hlab (hS lab hlab)

theorem GGRawFieldConjOn.mono {S S' : ℕ → LargeEvenLabel → Prop}
    (hS : ∀ p lab, S' p lab → S p lab) (h : GGRawFieldConjOn S) : GGRawFieldConjOn S' :=
  fun p hp hp2 lab hlab hS' => h p hp hp2 lab hlab (hS p lab hS')

theorem GGRawFieldConjOn.or {S S' : ℕ → LargeEvenLabel → Prop} (h : GGRawFieldConjOn S)
    (h' : GGRawFieldConjOn S') : GGRawFieldConjOn fun p lab => S p lab ∨ S' p lab := by
  rintro p hp hp2 lab hlab (hS | hS)
  · exact h p hp hp2 lab hlab hS
  · exact h' p hp hp2 lab hlab hS

theorem ggRawFieldConjInputExc_of_on {S : ℕ → LargeEvenLabel → Prop}
    (hS : ∀ p lab, LargeEvenInLambda2 lab → ¬ (lab.tag = .triD4 ∧ p = 3) → S p lab)
    (h : GGRawFieldConjOn S) : GGRawFieldConjInputExc :=
  fun p hp hp2 lab hlab hne => h p hp hp2 lab hlab (hS p lab hlab hne)

theorem GGRawFieldConjInput.exc (h : GGRawFieldConjInput) : GGRawFieldConjInputExc :=
  fun p hp hp2 lab hlab _ => h p hp hp2 lab hlab

theorem ggRawFieldConjInput_iff : GGRawFieldConjInput ↔ GGRawFieldConjInputExc ∧
    GGRawFieldConjOn fun p lab => lab.tag = .triD4 ∧ p = 3 := by
  refine ⟨fun h => ⟨h.exc, fun p hp hp2 lab hlab _ => h p hp hp2 lab hlab⟩, ?_⟩
  rintro ⟨h, h'⟩ p hp hp2 lab hlab
  by_cases hD : lab.tag = .triD4 ∧ p = 3
  · exact h' p hp hp2 lab hlab hD
  · exact h p hp hp2 lab hlab hD

theorem ringEquiv_mul_comm_of_finite {K : Type*} [Field K] [Finite K] (σ τ : K ≃+* K) :
    σ * τ = τ * σ := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨p, -, n, hp, hK⟩ := FiniteField.card' K
  have hK' : Nat.card K = p ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hK]
  have := (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic hp K hK').2
  exact (IsCyclic.isMulCommutative (α := RingAut K)).is_comm.comm σ τ

theorem mulAut_congr_conj {G H : Type*} [Group G] [Group H] (e : G ≃* H) (r : G) :
    MulAut.congr e (MulAut.conj r) = MulAut.conj (e r) := by
  ext x
  simp [MulAut.congr_apply, MulAut.conj_apply]

section Criteria

variable {R : Type} [Group R] {I F : Set (MulAut R)}

theorem eq_one_of_mem_closure_of_forall {M : Type*} [Group M] {S : Set M} (hS : ∀ s ∈ S, s = 1)
    {x : M} (hx : x ∈ Subgroup.closure S) : x = 1 := by
  have hle : Subgroup.closure S ≤ ⊥ := by
    rw [Subgroup.closure_le]
    intro s hs
    rw [SetLike.mem_coe, Subgroup.mem_bot]
    exact hS s hs
  exact Subgroup.mem_bot.mp (hle hx)

theorem ggRawInnField_of_subgroup {p : ℕ} (hp : p ≠ 1) (J : Subgroup (MulAut R))
    (hJ : (J : Set (MulAut R)) = I) (hinn : ∀ r : R, MulAut.conj r ∈ J)
    (hF : ∀ f ∈ F, f ∈ I → f = 1) : GGRawInnField p R I F := by
  subst hJ
  intro _ _
  refine ⟨fun φ hφ ψ hψ => J.mul_mem hφ hψ, fun φ hφ => J.inv_mem hφ, hinn, ?_⟩
  intro f hf hord hfI
  rw [hF f hf hfI, orderOf_one] at hord
  exact hp hord.symm

theorem ggRawInnField_of_forall_eq_one {p : ℕ} (hp : p ≠ 1) (J : Subgroup (MulAut R))
    (hJ : (J : Set (MulAut R)) = I) (hinn : ∀ r : R, MulAut.conj r ∈ J) (hF : ∀ f ∈ F, f = 1) :
    GGRawInnField p R I F :=
  ggRawInnField_of_subgroup hp J hJ hinn fun f hf _ => hF f hf

theorem ggRawFieldCentral_of_commutator_mem (h : ∀ α β : MulAut R, α * β * α⁻¹ * β⁻¹ ∈ I) :
    GGRawFieldCentral R I F :=
  fun _ _ α u _ f _ => h α (u * f)

theorem ggRawFieldCentral_of_hom {Q : Type*} [CommGroup Q] (Θ : MulAut R →* Q)
    (hker : ∀ φ : MulAut R, Θ φ = 1 → φ ∈ I) : GGRawFieldCentral R I F :=
  ggRawFieldCentral_of_commutator_mem fun α β => hker _ (by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_right_comm (Θ α), mul_inv_cancel,
      one_mul, mul_inv_cancel])

theorem ggRawFieldCentral_of_forall_eq_one (J : Subgroup (MulAut R)) [hJn : J.Normal]
    (hJ : (J : Set (MulAut R)) = I) (hF : ∀ f ∈ F, f = 1) : GGRawFieldCentral R I F := by
  subst hJ
  intro _ _ α u hu f hf
  rw [eq_one_of_mem_closure_of_forall hF hf, mul_one]
  exact J.mul_mem (hJn.conj_mem u hu α) (J.inv_mem hu)

theorem ggRawFieldConj_of_forall_eq_one {p : ℕ} (hF : ∀ f ∈ F, f = 1) :
    GGRawFieldConj p R I F := by
  intro _ _ u hu f hf huf _
  rw [eq_one_of_mem_closure_of_forall hF hf, mul_one] at huf
  exact absurd hu huf

end Criteria

theorem commutator_mem_of_eq_mul {M : Type*} [Group M] (D : Subgroup M) (X : Set M)
    (hX : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) (hXD : ∀ x ∈ X, ∀ d ∈ D, x * d * x⁻¹ ∈ D)
    (hform : ∀ a : M, ∃ d ∈ D, ∃ x ∈ X, a = d * x) (a b : M) : a * b * a⁻¹ * b⁻¹ ∈ D := by
  obtain ⟨d, hd, x, hx, rfl⟩ := hform a
  obtain ⟨e, he, y, hy, rfl⟩ := hform b
  have hxy : x * y * x⁻¹ * y⁻¹ = 1 := by rw [hX x hx y hy]; group
  have e1 : d * x * (e * y) * (d * x)⁻¹ * (e * y)⁻¹ =
      d * (x * e * x⁻¹) * (x * y * x⁻¹ * y⁻¹) * (y * d⁻¹ * y⁻¹) * e⁻¹ := by group
  rw [e1, hxy, mul_one]
  refine D.mul_mem (D.mul_mem (D.mul_mem hd (hXD x hx e he)) ?_) (D.inv_mem he)
  exact hXD y hy _ (D.inv_mem hd)

end CFSG.StandardType

end
