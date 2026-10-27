module

public import CFSG.LieType.Chevalley.CartanPositiveForm
public import CFSG.RankThree.PartOne.KE.E8TwoA2Family

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Pointwise MatrixGroups

variable {τ : Tag} {L : Type} [Field L]

theorem symmetrizedCartan_pair_comm (τ : Tag) (a b : Fin τ.rank → ℤ) :
    a ⬝ᵥ (τ.symmetrizedCartan *ᵥ b) = b ⬝ᵥ (τ.symmetrizedCartan *ᵥ a) := by
  have h1 : a ᵥ* τ.symmetrizedCartan = τ.symmetrizedCartan *ᵥ a := by
    rw [← Matrix.mulVec_transpose, (symmetrizedCartan_isSymm τ).eq]
  rw [Matrix.dotProduct_mulVec, h1, dotProduct_comm]

@[expose] def ThetaFree {ι' : Type} (S : Set (Fin τ.rank → ℤ))
    (P : ι' → Subgroup (ModGL τ L)) : Prop :=
  ∀ y ∈ torusGroup τ L ⊔ rootSpan τ L S, (∀ i, ∀ u ∈ P i, y * u = u * y) →
    y ∈ torusGroup τ L ∧ y ∈ Subgroup.centralizer (rootSpan τ L S : Set (ModGL τ L))

structure SigmaFactor {ι' : Type} (n : ModGL τ L) (Fr : L →+* L) (S : Set (Fin τ.rank → ℤ))
    (P : ι' → Subgroup (ModGL τ L)) (N : Subgroup (ModGL τ L)) : Prop where
  finite : ∀ i, Finite (P i)
  quasi : ∀ i, CFSG.IsQuasisimple (P i)
  le_root : ∀ i, P i ≤ rootSpan τ L S
  le_fix : ∀ i, P i ≤ twistedFixedPoints n (Units.map (entrywiseHom Fr))
  le_adj : ∀ i, P i ≤ adjointGroup τ L
  norm : ∀ i, ∀ y ∈ N, y ∈ twistedFixedPoints n (Units.map (entrywiseHom Fr)) →
    ∀ u ∈ P i, y * u * y⁻¹ ∈ P i
  thetaFree : ThetaFree S P

section Union

theorem exists_decomp_union (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {S₁ S₂ : Set (Fin τ.rank → ℤ)} (hS₁ : ∀ r ∈ S₁, IsRoot τ r) (hS₂ : ∀ r ∈ S₂, IsRoot τ r)
    (horth : ∀ α ∈ S₁, ∀ β ∈ S₂, α ⬝ᵥ (τ.symmetrizedCartan *ᵥ β) = 0) {y : ModGL τ L}
    (hy : y ∈ torusGroup τ L ⊔ rootSpan τ L (S₁ ∪ S₂)) :
    ∃ h ∈ torusGroup τ L, ∃ z₁ ∈ rootSpan τ L S₁, ∃ z₂ ∈ rootSpan τ L S₂, y = h * z₁ * z₂ := by
  have hS : ∀ r ∈ S₁ ∪ S₂, IsRoot τ r := fun r hr => hr.elim (hS₁ r) (hS₂ r)
  have e := Subgroup.coe_mul_of_left_le_normalizer_right (torusGroup τ L)
    (rootSpan τ L (S₁ ∪ S₂)) (torusGroup_le_normalizer_rootSpan hS)
  have hy' : y ∈ ((torusGroup τ L ⊔ rootSpan τ L (S₁ ∪ S₂) : Subgroup (ModGL τ L)) :
    Set (ModGL τ L)) := hy
  rw [e] at hy'
  obtain ⟨h, hh, q, hq, rfl⟩ := hy'
  rw [SetLike.mem_coe, rootSpan_union_eq] at hq
  have hcomm := rootSpan_commute_of_orth (L := L) hτ hS₁ hS₂ horth
  have hle : rootSpan τ L S₁ ≤ Subgroup.normalizer (rootSpan τ L S₂ : Set (ModGL τ L)) := by
    refine le_trans (fun g hg => ?_) (Subgroup.centralizer_le_normalizer _)
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact (hcomm g hg u hu).symm
  have e2 := Subgroup.coe_mul_of_left_le_normalizer_right (rootSpan τ L S₁) (rootSpan τ L S₂) hle
  have hq' : q ∈ ((rootSpan τ L S₁ ⊔ rootSpan τ L S₂ : Subgroup (ModGL τ L)) :
    Set (ModGL τ L)) := hq
  rw [e2] at hq'
  obtain ⟨z₁, hz₁, z₂, hz₂, rfl⟩ := hq'
  exact ⟨h, hh, z₁, hz₁, z₂, hz₂, by group⟩

theorem torus_sup_union_le_normalizers (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {S₁ S₂ : Set (Fin τ.rank → ℤ)} (hS₁ : ∀ r ∈ S₁, IsRoot τ r) (hS₂ : ∀ r ∈ S₂, IsRoot τ r)
    (horth : ∀ α ∈ S₁, ∀ β ∈ S₂, α ⬝ᵥ (τ.symmetrizedCartan *ᵥ β) = 0) :
    torusGroup τ L ⊔ rootSpan τ L (S₁ ∪ S₂) ≤
      Subgroup.normalizer (rootSpan τ L S₁ : Set (ModGL τ L)) ⊓
        Subgroup.normalizer (rootSpan τ L S₂ : Set (ModGL τ L)) := by
  have hcomm := rootSpan_commute_of_orth (L := L) hτ hS₁ hS₂ horth
  have hc1 : rootSpan τ L S₂ ≤ Subgroup.normalizer (rootSpan τ L S₁ : Set (ModGL τ L)) := by
    refine le_trans (fun g hg => ?_) (Subgroup.centralizer_le_normalizer _)
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact hcomm u hu g hg
  have hc2 : rootSpan τ L S₁ ≤ Subgroup.normalizer (rootSpan τ L S₂ : Set (ModGL τ L)) := by
    refine le_trans (fun g hg => ?_) (Subgroup.centralizer_le_normalizer _)
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact (hcomm g hg u hu).symm
  refine sup_le (le_inf (torusGroup_le_normalizer_rootSpan hS₁)
    (torusGroup_le_normalizer_rootSpan hS₂)) ?_
  rw [rootSpan_union_eq]
  exact sup_le (le_inf Subgroup.le_normalizer hc2) (le_inf hc1 Subgroup.le_normalizer)

theorem rootSpan_le_normalizer_of_orth (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {S₁ S₂ : Set (Fin τ.rank → ℤ)} (hS₁ : ∀ r ∈ S₁, IsRoot τ r) (hS₂ : ∀ r ∈ S₂, IsRoot τ r)
    (horth : ∀ α ∈ S₁, ∀ β ∈ S₂, α ⬝ᵥ (τ.symmetrizedCartan *ᵥ β) = 0) :
    rootSpan τ L S₁ ≤ Subgroup.normalizer (rootSpan τ L S₂ : Set (ModGL τ L)) := by
  have hcomm := rootSpan_commute_of_orth (L := L) hτ hS₁ hS₂ horth
  refine le_trans (fun g hg => ?_) (Subgroup.centralizer_le_normalizer _)
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  exact (hcomm g hg u hu).symm

theorem ThetaFree.one_sided (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {S₁ S₂ : Set (Fin τ.rank → ℤ)} (hS₁ : ∀ r ∈ S₁, IsRoot τ r) (hS₂ : ∀ r ∈ S₂, IsRoot τ r)
    (horth : ∀ α ∈ S₁, ∀ β ∈ S₂, α ⬝ᵥ (τ.symmetrizedCartan *ᵥ β) = 0) {ι₁ : Type}
    {P₁ : ι₁ → Subgroup (ModGL τ L)} (hθ : ThetaFree S₁ P₁)
    (hP₁ : ∀ i, P₁ i ≤ rootSpan τ L S₁) {y : ModGL τ L}
    (hy : y ∈ torusGroup τ L ⊔ rootSpan τ L (S₁ ∪ S₂))
    (hc : ∀ i, ∀ u ∈ P₁ i, y * u = u * y) :
    (∃ h ∈ torusGroup τ L, h ∈ Subgroup.centralizer (rootSpan τ L S₁ : Set (ModGL τ L)) ∧
        ∃ z ∈ rootSpan τ L S₂, y = h * z) ∧
      y ∈ Subgroup.centralizer (rootSpan τ L S₁ : Set (ModGL τ L)) := by
  have hcomm := rootSpan_commute_of_orth (L := L) hτ hS₁ hS₂ horth
  obtain ⟨h, hh, z₁, hz₁, z₂, hz₂, rfl⟩ := exists_decomp_union hτ hS₁ hS₂ horth hy
  have hhz : h * z₁ ∈ torusGroup τ L ⊔ rootSpan τ L S₁ :=
    mul_mem (Subgroup.mem_sup_left hh) (Subgroup.mem_sup_right hz₁)
  have hhzc : ∀ i, ∀ u ∈ P₁ i, (h * z₁) * u = u * (h * z₁) := by
    intro i u hu
    have h1 := hc i u hu
    have h2 : z₂ * u = u * z₂ := (hcomm u (hP₁ i hu) z₂ hz₂).symm
    have h3 : (h * z₁ * u) * z₂ = (u * (h * z₁)) * z₂ :=
      calc (h * z₁ * u) * z₂ = h * z₁ * (u * z₂) := by group
        _ = h * z₁ * (z₂ * u) := by rw [← h2]
        _ = (h * z₁ * z₂) * u := by group
        _ = u * (h * z₁ * z₂) := h1
        _ = (u * (h * z₁)) * z₂ := by group
    exact mul_right_cancel h3
  obtain ⟨hH, hC⟩ := hθ _ hhz hhzc
  refine ⟨⟨h * z₁, hH, hC, z₂, hz₂, by group⟩, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  have h3 := Subgroup.mem_centralizer_iff.1 hC g hg
  have h4 : z₂ * g = g * z₂ := hcomm g hg z₂ hz₂ |>.symm
  calc g * (h * z₁ * z₂) = (g * (h * z₁)) * z₂ := by group
    _ = ((h * z₁) * g) * z₂ := by rw [h3]
    _ = (h * z₁) * (g * z₂) := by group
    _ = (h * z₁) * (z₂ * g) := by rw [h4]
    _ = h * z₁ * z₂ * g := by group

theorem ThetaFree.union (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {S₁ S₂ : Set (Fin τ.rank → ℤ)} (hS₁ : ∀ r ∈ S₁, IsRoot τ r) (hS₂ : ∀ r ∈ S₂, IsRoot τ r)
    (horth : ∀ α ∈ S₁, ∀ β ∈ S₂, α ⬝ᵥ (τ.symmetrizedCartan *ᵥ β) = 0) {ι₁ ι₂ : Type}
    {P₁ : ι₁ → Subgroup (ModGL τ L)} {P₂ : ι₂ → Subgroup (ModGL τ L)}
    (hθ₁ : ThetaFree S₁ P₁) (hθ₂ : ThetaFree S₂ P₂) (hP₁ : ∀ i, P₁ i ≤ rootSpan τ L S₁) :
    ThetaFree (S₁ ∪ S₂) (Sum.elim P₁ P₂) := by
  intro y hy hc
  have hcomm := rootSpan_commute_of_orth (L := L) hτ hS₁ hS₂ horth
  obtain ⟨⟨h, hh, -, z, hz, rfl⟩, hC1⟩ := ThetaFree.one_sided hτ hS₁ hS₂ horth hθ₁ hP₁ hy
    (fun i u hu => hc (Sum.inl i) u hu)
  have hyQ2 : h * z ∈ torusGroup τ L ⊔ rootSpan τ L S₂ :=
    mul_mem (Subgroup.mem_sup_left hh) (Subgroup.mem_sup_right hz)
  obtain ⟨hH, hC2⟩ := hθ₂ _ hyQ2 (fun i u hu => hc (Sum.inr i) u hu)
  refine ⟨hH, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  rw [SetLike.mem_coe, rootSpan_union_eq] at hg
  have hle : rootSpan τ L S₁ ⊔ rootSpan τ L S₂ ≤
      Subgroup.centralizer ({h * z} : Set (ModGL τ L)) := by
    refine sup_le (fun g hg => ?_) (fun g hg => ?_)
    · rw [Subgroup.mem_centralizer_iff]
      intro u hu
      rw [Set.mem_singleton_iff] at hu
      subst hu
      exact (Subgroup.mem_centralizer_iff.1 hC1 g hg).symm
    · rw [Subgroup.mem_centralizer_iff]
      intro u hu
      rw [Set.mem_singleton_iff] at hu
      subst hu
      exact (Subgroup.mem_centralizer_iff.1 hC2 g hg).symm
  have := Subgroup.mem_centralizer_iff.1 (hle hg) (h * z) rfl
  exact this.symm

theorem SigmaFactor.union (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {S₁ S₂ : Set (Fin τ.rank → ℤ)} (hS₁ : ∀ r ∈ S₁, IsRoot τ r) (hS₂ : ∀ r ∈ S₂, IsRoot τ r)
    (horth : ∀ α ∈ S₁, ∀ β ∈ S₂, α ⬝ᵥ (τ.symmetrizedCartan *ᵥ β) = 0) {ι₁ ι₂ : Type}
    {n : ModGL τ L} {Fr : L →+* L} {P₁ : ι₁ → Subgroup (ModGL τ L)}
    {P₂ : ι₂ → Subgroup (ModGL τ L)} {N₁ N₂ : Subgroup (ModGL τ L)}
    (h₁ : SigmaFactor n Fr S₁ P₁ N₁) (h₂ : SigmaFactor n Fr S₂ P₂ N₂) :
    SigmaFactor n Fr (S₁ ∪ S₂) (Sum.elim P₁ P₂) (N₁ ⊓ N₂) where
  finite := fun i => by
    cases i with
    | inl i => exact h₁.finite i
    | inr i => exact h₂.finite i
  quasi := fun i => by
    cases i with
    | inl i => exact h₁.quasi i
    | inr i => exact h₂.quasi i
  le_root := fun i => by
    rw [rootSpan_union_eq]
    cases i with
    | inl i => exact (h₁.le_root i).trans le_sup_left
    | inr i => exact (h₂.le_root i).trans le_sup_right
  le_fix := fun i => by
    cases i with
    | inl i => exact h₁.le_fix i
    | inr i => exact h₂.le_fix i
  le_adj := fun i => by
    cases i with
    | inl i => exact h₁.le_adj i
    | inr i => exact h₂.le_adj i
  norm := fun i y hy hyR u hu => by
    cases i with
    | inl i => exact h₁.norm i y hy.1 hyR u hu
    | inr i => exact h₂.norm i y hy.2 hyR u hu
  thetaFree := ThetaFree.union hτ hS₁ hS₂ horth h₁.thetaFree h₂.thetaFree h₁.le_root

theorem SigmaFactor.toSigma {S : Set (Fin τ.rank → ℤ)} {ι' : Type} {n : ModGL τ L}
    {Fr : L →+* L} {P : ι' → Subgroup (ModGL τ L)} {N : Subgroup (ModGL τ L)}
    (h : SigmaFactor n Fr S P N) (hN : torusGroup τ L ⊔ rootSpan τ L S ≤ N) :
    IsSigmaFamily n Fr S P :=
  ⟨h.finite, h.quasi, h.le_root, h.le_fix, h.le_adj, fun i y hy hyR u hu => h.norm i y (hN hy) hyR
    u hu, fun y hy hyR hc => by
    obtain ⟨hH, hC⟩ := h.thetaFree y hy hc
    exact Subgroup.mem_inf.2 ⟨mem_twistedTorusOf.2 ⟨hH, hyR⟩, hC⟩⟩

end Union

end CFSG.RankThree.PartOne.KE
