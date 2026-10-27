module

public import CFSG.RankThree.PartTwo.Sec4.Notation

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4

section Inner

variable {L : Type*} [Group L]

@[expose] def IsInnerAut (τ : MulAut L) : Prop :=
  τ ∈ (MulAut.conj : L →* MulAut L).range

theorem isInnerAut_conj (y : L) : IsInnerAut (MulAut.conj y) :=
  ⟨y, rfl⟩

variable {M : Type*} [Group M]

theorem congr_mulAutConj (e : L ≃* M) (y : L) :
    MulAut.congr e (MulAut.conj y) = MulAut.conj (e y) := by
  ext m
  simp [MulAut.congr_apply, map_mul, map_inv]

theorem map_innAut_congr (e : L ≃* M) :
    (MulAut.conj : L →* MulAut L).range.map (MulAut.congr e).toMonoidHom =
      (MulAut.conj : M →* MulAut M).range := by
  ext τ
  constructor
  · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
    exact ⟨e y, (congr_mulAutConj e y).symm⟩
  · rintro ⟨m, rfl⟩
    refine ⟨MulAut.conj (e.symm m), ⟨e.symm m, rfl⟩, ?_⟩
    change MulAut.congr e (MulAut.conj (e.symm m)) = MulAut.conj m
    rw [congr_mulAutConj, MulEquiv.apply_symm_apply]

theorem mul_mulAutConj_mul_inv (α : MulAut L) (y : L) :
    α * MulAut.conj y * α⁻¹ = MulAut.conj (α y) := by
  ext m
  simp [MulAut.mul_apply, map_mul, map_inv]

theorem isInnerAut_conj_iff (α τ : MulAut L) : IsInnerAut (α * τ * α⁻¹) ↔ IsInnerAut τ := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨α⁻¹ y, ?_⟩
    rw [← mul_mulAutConj_mul_inv, hy]
    group
  · rintro ⟨y, rfl⟩
    exact ⟨α y, (mul_mulAutConj_mul_inv α y).symm⟩

theorem congr_trans {N : Type*} [Group N] (e : L ≃* M) (e' : M ≃* N) (τ : MulAut L) :
    MulAut.congr (e.trans e') τ = MulAut.congr e' (MulAut.congr e τ) := by
  ext m
  rfl

theorem isInnerAut_congr (e : L ≃* M) (τ : MulAut L) :
    IsInnerAut (MulAut.congr e τ) ↔ IsInnerAut τ := by
  constructor
  · intro h
    rw [IsInnerAut, ← map_innAut_congr e] at h
    obtain ⟨σ, hσ, hστ⟩ := h
    rwa [(MulAut.congr e).injective hστ] at hσ
  · intro h
    rw [IsInnerAut, ← map_innAut_congr e]
    exact ⟨τ, h, rfl⟩

end Inner

structure PinnedAut (L : Type*) [Group L] where
  inndiag : Subgroup (MulAut L)
  inn_le : (MulAut.conj : L →* MulAut L).range ≤ inndiag
  field : Subgroup (MulAut L)
  graph : Set (MulAut L)

inductive AutKind
  | inner
  | diagonal
  | field
  | graph
  | graphField
  deriving DecidableEq

namespace PinnedAut

variable {L : Type*} [Group L] (P : PinnedAut L)

@[expose] def IsDiagonal (τ : MulAut L) : Prop :=
  τ ∈ P.inndiag ∧ ¬ IsInnerAut τ

@[expose] def IsField (τ : MulAut L) : Prop :=
  ∃ φ ∈ P.field, φ ≠ 1 ∧ ∃ d ∈ P.inndiag, τ = d * φ * d⁻¹

@[expose] def IsGraph (τ : MulAut L) : Prop :=
  ∃ γ ∈ P.graph, γ ≠ 1 ∧ ∃ d ∈ P.inndiag, τ = d * γ * d⁻¹

@[expose] def IsGraphField (τ : MulAut L) : Prop :=
  ∃ γ ∈ P.graph, γ ≠ 1 ∧ ∃ φ ∈ P.field, φ ≠ 1 ∧ ∃ d ∈ P.inndiag, τ = d * (γ * φ) * d⁻¹

@[expose] def HasKind (τ : MulAut L) : AutKind → Prop
  | .inner => IsInnerAut τ
  | .diagonal => P.IsDiagonal τ
  | .field => P.IsField τ
  | .graph => P.IsGraph τ
  | .graphField => P.IsGraphField τ

theorem hasKind_inner {τ : MulAut L} : P.HasKind τ .inner ↔ IsInnerAut τ :=
  Iff.rfl

theorem hasKind_diagonal {τ : MulAut L} : P.HasKind τ .diagonal ↔ P.IsDiagonal τ :=
  Iff.rfl

theorem hasKind_field {τ : MulAut L} : P.HasKind τ .field ↔ P.IsField τ :=
  Iff.rfl

theorem hasKind_graph {τ : MulAut L} : P.HasKind τ .graph ↔ P.IsGraph τ :=
  Iff.rfl

theorem hasKind_graphField {τ : MulAut L} : P.HasKind τ .graphField ↔ P.IsGraphField τ :=
  Iff.rfl

theorem isInnerDiagonal_of_isInnerAut {τ : MulAut L} (h : IsInnerAut τ) : τ ∈ P.inndiag :=
  P.inn_le h

theorem isField_of_mem {φ : MulAut L} (hφ : φ ∈ P.field) (h1 : φ ≠ 1) : P.IsField φ :=
  ⟨φ, hφ, h1, 1, one_mem _, by rw [one_mul, inv_one, mul_one]⟩

theorem isGraph_of_mem {γ : MulAut L} (hγ : γ ∈ P.graph) (h1 : γ ≠ 1) : P.IsGraph γ :=
  ⟨γ, hγ, h1, 1, one_mem _, by rw [one_mul, inv_one, mul_one]⟩

theorem isGraphField_of_mem {γ φ : MulAut L} (hγ : γ ∈ P.graph) (hγ1 : γ ≠ 1) (hφ : φ ∈ P.field)
    (hφ1 : φ ≠ 1) : P.IsGraphField (γ * φ) :=
  ⟨γ, hγ, hγ1, φ, hφ, hφ1, 1, one_mem _, by rw [one_mul, inv_one, mul_one]⟩

theorem isField_conj {τ d : MulAut L} (hd : d ∈ P.inndiag) (hτ : P.IsField τ) :
    P.IsField (d * τ * d⁻¹) := by
  obtain ⟨φ, hφ, h1, d', hd', rfl⟩ := hτ
  exact ⟨φ, hφ, h1, d * d', mul_mem hd hd', by group⟩

theorem isGraph_conj {τ d : MulAut L} (hd : d ∈ P.inndiag) (hτ : P.IsGraph τ) :
    P.IsGraph (d * τ * d⁻¹) := by
  obtain ⟨γ, hγ, h1, d', hd', rfl⟩ := hτ
  exact ⟨γ, hγ, h1, d * d', mul_mem hd hd', by group⟩

theorem isGraphField_conj {τ d : MulAut L} (hd : d ∈ P.inndiag) (hτ : P.IsGraphField τ) :
    P.IsGraphField (d * τ * d⁻¹) := by
  obtain ⟨γ, hγ, hγ1, φ, hφ, hφ1, d', hd', rfl⟩ := hτ
  exact ⟨γ, hγ, hγ1, φ, hφ, hφ1, d * d', mul_mem hd hd', by group⟩

theorem IsField.inFieldCoset {τ : MulAut L}
    (hnorm : P.field ≤ Subgroup.normalizer (P.inndiag : Set (MulAut L))) (hτ : P.IsField τ) : ∃ φ ∈ P.field, φ ≠ 1 ∧ τ * φ⁻¹ ∈ P.inndiag := by
  obtain ⟨φ, hφ, h1, d, hd, rfl⟩ := hτ
  refine ⟨φ, hφ, h1, ?_⟩
  have h2 : φ * d⁻¹ * φ⁻¹ ∈ P.inndiag :=
    (Subgroup.mem_normalizer_iff.mp (hnorm hφ) d⁻¹).mp (inv_mem hd)
  have h3 : d * φ * d⁻¹ * φ⁻¹ = d * (φ * d⁻¹ * φ⁻¹) := by group
  rw [h3]
  exact mul_mem hd h2

structure Stable : Prop where
  normal : P.inndiag.Normal
  field_conj : ∀ α φ : MulAut L, φ ∈ P.field → φ ≠ 1 →
    ∃ φ' ∈ P.field, φ' ≠ 1 ∧ ∃ d ∈ P.inndiag, α * φ * α⁻¹ = d * φ' * d⁻¹
  graph_conj : ∀ α γ : MulAut L, γ ∈ P.graph → γ ≠ 1 →
    ∃ γ' ∈ P.graph, γ' ≠ 1 ∧ ∃ d ∈ P.inndiag, α * γ * α⁻¹ = d * γ' * d⁻¹
  graphField_conj : ∀ α γ φ : MulAut L, γ ∈ P.graph → γ ≠ 1 → φ ∈ P.field → φ ≠ 1 →
    ∃ γ' ∈ P.graph, γ' ≠ 1 ∧ ∃ φ' ∈ P.field, φ' ≠ 1 ∧ ∃ d ∈ P.inndiag,
      α * (γ * φ) * α⁻¹ = d * (γ' * φ') * d⁻¹

variable {P}

theorem Stable.isField_conj (hP : P.Stable) (α : MulAut L) {τ : MulAut L} (hτ : P.IsField τ) :
    P.IsField (α * τ * α⁻¹) := by
  obtain ⟨φ, hφ, h1, d, hd, rfl⟩ := hτ
  obtain ⟨φ', hφ', h1', d', hd', h⟩ := hP.field_conj α φ hφ h1
  refine ⟨φ', hφ', h1', α * d * α⁻¹ * d', mul_mem (hP.normal.conj_mem d hd α) hd', ?_⟩
  calc α * (d * φ * d⁻¹) * α⁻¹ = α * d * α⁻¹ * (α * φ * α⁻¹) * (α * d * α⁻¹)⁻¹ := by group
    _ = α * d * α⁻¹ * d' * φ' * (α * d * α⁻¹ * d')⁻¹ := by rw [h]; group

theorem Stable.isGraph_conj (hP : P.Stable) (α : MulAut L) {τ : MulAut L} (hτ : P.IsGraph τ) :
    P.IsGraph (α * τ * α⁻¹) := by
  obtain ⟨γ, hγ, h1, d, hd, rfl⟩ := hτ
  obtain ⟨γ', hγ', h1', d', hd', h⟩ := hP.graph_conj α γ hγ h1
  refine ⟨γ', hγ', h1', α * d * α⁻¹ * d', mul_mem (hP.normal.conj_mem d hd α) hd', ?_⟩
  calc α * (d * γ * d⁻¹) * α⁻¹ = α * d * α⁻¹ * (α * γ * α⁻¹) * (α * d * α⁻¹)⁻¹ := by group
    _ = α * d * α⁻¹ * d' * γ' * (α * d * α⁻¹ * d')⁻¹ := by rw [h]; group

theorem Stable.isGraphField_conj (hP : P.Stable) (α : MulAut L) {τ : MulAut L}
    (hτ : P.IsGraphField τ) : P.IsGraphField (α * τ * α⁻¹) := by
  obtain ⟨γ, hγ, hγ1, φ, hφ, hφ1, d, hd, rfl⟩ := hτ
  obtain ⟨γ', hγ', hγ1', φ', hφ', hφ1', d', hd', h⟩ := hP.graphField_conj α γ φ hγ hγ1 hφ hφ1
  refine ⟨γ', hγ', hγ1', φ', hφ', hφ1', α * d * α⁻¹ * d',
    mul_mem (hP.normal.conj_mem d hd α) hd', ?_⟩
  calc α * (d * (γ * φ) * d⁻¹) * α⁻¹ =
      α * d * α⁻¹ * (α * (γ * φ) * α⁻¹) * (α * d * α⁻¹)⁻¹ := by group
    _ = α * d * α⁻¹ * d' * (γ' * φ') * (α * d * α⁻¹ * d')⁻¹ := by rw [h]; group

theorem Stable.hasKind_conj (hP : P.Stable) (α τ : MulAut L) (k : AutKind) :
    P.HasKind (α * τ * α⁻¹) k ↔ P.HasKind τ k := by
  have key : ∀ (β σ : MulAut L), P.HasKind σ k → P.HasKind (β * σ * β⁻¹) k := by
    intro β σ hσ
    cases k
    · exact (isInnerAut_conj_iff β σ).2 hσ
    · exact ⟨hP.normal.conj_mem σ hσ.1 β, fun h => hσ.2 ((isInnerAut_conj_iff β σ).1 h)⟩
    · exact hP.isField_conj β hσ
    · exact hP.isGraph_conj β hσ
    · exact hP.isGraphField_conj β hσ
  refine ⟨fun h => ?_, key α τ⟩
  have h2 := key α⁻¹ _ h
  rwa [show α⁻¹ * (α * τ * α⁻¹) * α⁻¹⁻¹ = τ by group] at h2

variable (P)

variable {M : Type*} [Group M]

@[expose] def comap (Q : PinnedAut M) (e : L ≃* M) : PinnedAut L where
  inndiag := Q.inndiag.comap (MulAut.congr e).toMonoidHom
  inn_le := by
    rintro _ ⟨y, rfl⟩
    change MulAut.congr e (MulAut.conj y) ∈ Q.inndiag
    rw [congr_mulAutConj]
    exact Q.inn_le ⟨e y, rfl⟩
  field := Q.field.comap (MulAut.congr e).toMonoidHom
  graph := (MulAut.congr e) ⁻¹' Q.graph

theorem mem_comap_inndiag (Q : PinnedAut M) (e : L ≃* M) {τ : MulAut L} :
    τ ∈ (Q.comap e).inndiag ↔ MulAut.congr e τ ∈ Q.inndiag :=
  Iff.rfl

theorem mem_comap_field (Q : PinnedAut M) (e : L ≃* M) {τ : MulAut L} :
    τ ∈ (Q.comap e).field ↔ MulAut.congr e τ ∈ Q.field :=
  Iff.rfl

theorem mem_comap_graph (Q : PinnedAut M) (e : L ≃* M) {τ : MulAut L} :
    τ ∈ (Q.comap e).graph ↔ MulAut.congr e τ ∈ Q.graph :=
  Iff.rfl

theorem symm_mem_comap_inndiag (Q : PinnedAut M) (e : L ≃* M) {σ : MulAut M}
    (h : σ ∈ Q.inndiag) : (MulAut.congr e).symm σ ∈ (Q.comap e).inndiag :=
  (mem_comap_inndiag Q e).2 (by rwa [MulEquiv.apply_symm_apply])

theorem symm_mem_comap_field (Q : PinnedAut M) (e : L ≃* M) {σ : MulAut M}
    (h : σ ∈ Q.field) : (MulAut.congr e).symm σ ∈ (Q.comap e).field :=
  (mem_comap_field Q e).2 (by rwa [MulEquiv.apply_symm_apply])

theorem symm_mem_comap_graph (Q : PinnedAut M) (e : L ≃* M) {σ : MulAut M}
    (h : σ ∈ Q.graph) : (MulAut.congr e).symm σ ∈ (Q.comap e).graph :=
  (mem_comap_graph Q e).2 (by rwa [MulEquiv.apply_symm_apply])

theorem congr_conj_mul (e : L ≃* M) (d φ : MulAut L) :
    MulAut.congr e (d * φ * d⁻¹) =
      MulAut.congr e d * MulAut.congr e φ * (MulAut.congr e d)⁻¹ := by
  rw [map_mul, map_mul, map_inv]

theorem isDiagonal_comap (Q : PinnedAut M) (e : L ≃* M) {τ : MulAut L} :
    (Q.comap e).IsDiagonal τ ↔ Q.IsDiagonal (MulAut.congr e τ) := by
  rw [IsDiagonal, IsDiagonal, isInnerAut_congr]
  rfl

theorem isField_comap (Q : PinnedAut M) (e : L ≃* M) {τ : MulAut L} :
    (Q.comap e).IsField τ ↔ Q.IsField (MulAut.congr e τ) := by
  constructor
  · rintro ⟨φ, hφ, h1, d, hd, rfl⟩
    refine ⟨MulAut.congr e φ, hφ, fun h => h1 ?_, MulAut.congr e d, hd, congr_conj_mul e d φ⟩
    exact (MulAut.congr e).injective (h.trans (map_one _).symm)
  · rintro ⟨φ', hφ', h1, d', hd', hτ⟩
    refine ⟨(MulAut.congr e).symm φ', symm_mem_comap_field Q e hφ', fun h => h1 ?_,
      (MulAut.congr e).symm d', symm_mem_comap_inndiag Q e hd', ?_⟩
    · rw [← MulEquiv.apply_symm_apply (MulAut.congr e) φ', h, map_one]
    · apply (MulAut.congr e).injective
      rw [congr_conj_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, hτ]

theorem isGraph_comap (Q : PinnedAut M) (e : L ≃* M) {τ : MulAut L} :
    (Q.comap e).IsGraph τ ↔ Q.IsGraph (MulAut.congr e τ) := by
  constructor
  · rintro ⟨γ, hγ, h1, d, hd, rfl⟩
    refine ⟨MulAut.congr e γ, hγ, fun h => h1 ?_, MulAut.congr e d, hd, congr_conj_mul e d γ⟩
    exact (MulAut.congr e).injective (h.trans (map_one _).symm)
  · rintro ⟨γ', hγ', h1, d', hd', hτ⟩
    refine ⟨(MulAut.congr e).symm γ', symm_mem_comap_graph Q e hγ', fun h => h1 ?_,
      (MulAut.congr e).symm d', symm_mem_comap_inndiag Q e hd', ?_⟩
    · rw [← MulEquiv.apply_symm_apply (MulAut.congr e) γ', h, map_one]
    · apply (MulAut.congr e).injective
      rw [congr_conj_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, hτ]

theorem isGraphField_comap (Q : PinnedAut M) (e : L ≃* M) {τ : MulAut L} :
    (Q.comap e).IsGraphField τ ↔ Q.IsGraphField (MulAut.congr e τ) := by
  constructor
  · rintro ⟨γ, hγ, hγ1, φ, hφ, hφ1, d, hd, rfl⟩
    refine ⟨MulAut.congr e γ, hγ, fun h => hγ1 ?_, MulAut.congr e φ, hφ, fun h => hφ1 ?_,
      MulAut.congr e d, hd, by rw [congr_conj_mul, map_mul]⟩
    · exact (MulAut.congr e).injective (h.trans (map_one _).symm)
    · exact (MulAut.congr e).injective (h.trans (map_one _).symm)
  · rintro ⟨γ', hγ', hγ1, φ', hφ', hφ1, d', hd', hτ⟩
    refine ⟨(MulAut.congr e).symm γ', symm_mem_comap_graph Q e hγ', fun h => hγ1 ?_,
      (MulAut.congr e).symm φ', symm_mem_comap_field Q e hφ', fun h => hφ1 ?_,
      (MulAut.congr e).symm d', symm_mem_comap_inndiag Q e hd', ?_⟩
    · rw [← MulEquiv.apply_symm_apply (MulAut.congr e) γ', h, map_one]
    · rw [← MulEquiv.apply_symm_apply (MulAut.congr e) φ', h, map_one]
    · apply (MulAut.congr e).injective
      rw [congr_conj_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply,
        MulEquiv.apply_symm_apply, hτ]

theorem hasKind_comap (Q : PinnedAut M) (e : L ≃* M) (τ : MulAut L) (k : AutKind) :
    (Q.comap e).HasKind τ k ↔ Q.HasKind (MulAut.congr e τ) k := by
  cases k
  · exact (isInnerAut_congr e τ).symm
  · exact isDiagonal_comap Q e
  · exact isField_comap Q e
  · exact isGraph_comap Q e
  · exact isGraphField_comap Q e

end PinnedAut

section Induced

variable {G : Type*} [Group G] [Finite G] (L : Subgroup G) {M : Type*} [Group M]

@[expose] noncomputable def inducedAutHom (e : L ⧸ aschbacherSolvableCore 3 L ≃* M) :
    Subgroup.normalizer (L : Set G) →* MulAut M :=
  (MulAut.congr e).toMonoidHom.comp ((thetaQuotMulAut L).comp (compAction L))

theorem inducedAutHom_apply (e : L ⧸ aschbacherSolvableCore 3 L ≃* M)
    (x : Subgroup.normalizer (L : Set G)) :
    inducedAutHom L e x = MulAut.congr e (thetaQuotMulAut L (compAction L x)) :=
  rfl

@[expose] def InducesKind (P : PinnedAut M) (e : L ⧸ aschbacherSolvableCore 3 L ≃* M) (x : G)
    (k : AutKind) : Prop :=
  ∃ hx : x ∈ Subgroup.normalizer (L : Set G), P.HasKind (inducedAutHom L e ⟨x, hx⟩) k

theorem hasKind_inner_inducedAutHom_iff (P : PinnedAut M)
    (e : L ⧸ aschbacherSolvableCore 3 L ≃* M) {x : G} (hx : x ∈ Subgroup.normalizer (L : Set G)) :
    P.HasKind (inducedAutHom L e ⟨x, hx⟩) .inner ↔ ¬ InducesOuterTheta x L := by
  rw [PinnedAut.hasKind_inner, inducedAutHom_apply, isInnerAut_congr, InducesOuterTheta]
  constructor
  · rintro h ⟨hx', h'⟩
    exact h' h
  · intro h
    by_contra h'
    exact h ⟨hx, h'⟩

theorem inducesKind_inner_iff (P : PinnedAut M) (e : L ⧸ aschbacherSolvableCore 3 L ≃* M)
    (x : G) :
    InducesKind L P e x .inner ↔
      x ∈ Subgroup.normalizer (L : Set G) ∧ ¬ InducesOuterTheta x L := by
  constructor
  · rintro ⟨hx, h⟩
    exact ⟨hx, (hasKind_inner_inducedAutHom_iff L P e hx).mp h⟩
  · rintro ⟨hx, h⟩
    exact ⟨hx, (hasKind_inner_inducedAutHom_iff L P e hx).mpr h⟩

theorem inducedAutHom_pow_eq_one (e : L ⧸ aschbacherSolvableCore 3 L ≃* M) {x : G}
    (hx : x ∈ Subgroup.normalizer (L : Set G)) {m : ℕ} (hxm : x ^ m = 1) :
    inducedAutHom L e ⟨x, hx⟩ ^ m = 1 := by
  have h : (⟨x, hx⟩ : Subgroup.normalizer (L : Set G)) ^ m = 1 :=
    Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact hxm)
  rw [← map_pow, h, map_one]

theorem not_isInnerAut_inducedAutHom_iff (e : L ⧸ aschbacherSolvableCore 3 L ≃* M) {x : G}
    (hx : x ∈ Subgroup.normalizer (L : Set G)) :
    ¬ IsInnerAut (inducedAutHom L e ⟨x, hx⟩) ↔ InducesOuterTheta x L := by
  rw [inducedAutHom_apply, isInnerAut_congr]
  exact ⟨fun h => ⟨hx, h⟩, fun ⟨_, h⟩ => h⟩

theorem inducesKind_comap {N : Type*} [Group N] (Q : PinnedAut N)
    (e : L ⧸ aschbacherSolvableCore 3 L ≃* M) (e' : M ≃* N) (x : G) (k : AutKind) :
    InducesKind L (Q.comap e') e x k ↔ InducesKind L Q (e.trans e') x k := by
  have key : ∀ hx : x ∈ Subgroup.normalizer (L : Set G),
      inducedAutHom L (e.trans e') ⟨x, hx⟩ = MulAut.congr e' (inducedAutHom L e ⟨x, hx⟩) :=
    fun hx => congr_trans e e' _
  constructor
  · rintro ⟨hx, h⟩
    refine ⟨hx, ?_⟩
    rw [PinnedAut.hasKind_comap] at h
    rwa [key]
  · rintro ⟨hx, h⟩
    refine ⟨hx, ?_⟩
    rw [PinnedAut.hasKind_comap, ← key]
    exact h

theorem inducedAutHom_eq_conj (e₁ e₂ : L ⧸ aschbacherSolvableCore 3 L ≃* M)
    (x : Subgroup.normalizer (L : Set G)) :
    inducedAutHom L e₂ x = (e₁.symm.trans e₂) * inducedAutHom L e₁ x * (e₁.symm.trans e₂)⁻¹ := by
  ext m
  simp [inducedAutHom_apply, MulAut.mul_apply, MulAut.inv_def]

theorem inducesKind_iff_of_stable {P : PinnedAut M} (hP : P.Stable)
    (e₁ e₂ : L ⧸ aschbacherSolvableCore 3 L ≃* M) (x : G) (k : AutKind) :
    InducesKind L P e₁ x k ↔ InducesKind L P e₂ x k := by
  constructor
  · rintro ⟨hx, h⟩
    exact ⟨hx, by rw [inducedAutHom_eq_conj L e₁ e₂]; exact (hP.hasKind_conj _ _ k).2 h⟩
  · rintro ⟨hx, h⟩
    exact ⟨hx, by
      rw [inducedAutHom_eq_conj L e₁ e₂] at h
      exact (hP.hasKind_conj _ _ k).1 h⟩

end Induced

end CFSG.RankThree.PartTwo.KFacts
