module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection5.PFsection5_1
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection5.PFsection5_2
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection4.PFsection4_9
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ChiefFactors.Core
import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.SolvableDimension

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 6: basic notation

This file records the book-facing vocabulary for Peterfalvi, Section 6,
`Some Coherence Theorems`.

The quotient-heavy hypotheses from the book are packaged as named predicates so
that the numbered statements can stay close to the source text.
-/

noncomputable section

open scoped BigOperators
open scoped Classical

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section6

universe u

/-- The family `S(A)` from PF Section 6. -/
@[expose] public def inducedKernelFamily
    {L : Type u} [Group L] [Finite L]
    (K A : Subgroup L)
    (S : Finset (Section1.ClassFunction L)) : Prop :=
  A ≤ K ∧
    ∀ χ : Section1.ClassFunction L,
      χ ∈ S ↔
        ∃ θ : Section1.ClassFunction K,
          Section1.IsIrreducibleCharacterOnGroup θ ∧
            Section1.subgroupInKernel' θ (A.subgroupOf K) ∧
            θ ≠ Section1.principalCharacter K ∧
            χ = Section1.inducedCF K θ


public theorem subgroupInKernel'_subgroupOf_mono
    {G : Type u} [Group G]
    {A B K : Subgroup G} (hBA : B ≤ A)
    (φ : Section1.ClassFunction K)
    (hφ : Section1.subgroupInKernel' φ (A.subgroupOf K)) :
    Section1.subgroupInKernel' φ (B.subgroupOf K) := by
  intro b
  exact hφ ⟨b.1, hBA b.2⟩

public theorem subgroupInKernel'_conjugateCharacter
    {G : Type u} [Group G]
    {A : Subgroup G} (φ : Section1.ClassFunction G)
    (hφ : Section1.subgroupInKernel' φ A) :
    Section1.subgroupInKernel' (Section1.conjugateCharacter φ) A := by
  intro a
  simp [Section1.degree, Section1.conjugateCharacter, hφ a]

public theorem inducedKernelFamily_subset_of_le
    {L : Type u} [Group L] [Finite L]
    {K A B : Subgroup L}
    {SA SB : Finset (Section1.ClassFunction L)}
    (hSA : inducedKernelFamily K A SA)
    (hSB : inducedKernelFamily K B SB)
    (hBA : B ≤ A) :
    SA ⊆ SB := by
  intro χ hχ
  rcases (hSA.2 χ).mp hχ with ⟨θ, hθirr, hθker, hθne, hχeq⟩
  exact (hSB.2 χ).mpr
    ⟨θ, hθirr, subgroupInKernel'_subgroupOf_mono hBA θ hθker, hθne, hχeq⟩

public theorem inducedKernelFamily_subset_base
    {L : Type u} [Group L] [Finite L]
    {K A : Subgroup L}
    {S SA : Finset (Section1.ClassFunction L)}
    (hS : inducedKernelFamily K ⊥ S)
    (hSA : inducedKernelFamily K A SA) :
    SA ⊆ S :=
  inducedKernelFamily_subset_of_le hSA hS bot_le

public theorem inducedKernelFamily_unique
    {L : Type u} [Group L] [Finite L]
    {K A : Subgroup L}
    {S₁ S₂ : Finset (Section1.ClassFunction L)}
    (hS₁ : inducedKernelFamily K A S₁)
    (hS₂ : inducedKernelFamily K A S₂) :
    S₁ = S₂ := by
  ext χ
  exact (hS₁.2 χ).trans (hS₂.2 χ).symm


/-- The canonical finite family `S(A)` inside a base family `S = S(1)`. -/
public noncomputable def inducedKernelFamilyOf
    {L : Type u} [Group L] [Finite L]
    (K A : Subgroup L)
    (S : Finset (Section1.ClassFunction L)) :
    Finset (Section1.ClassFunction L) := by
  classical
  exact S.filter fun χ =>
    ∃ θ : Section1.ClassFunction K,
      Section1.IsIrreducibleCharacterOnGroup θ ∧
        Section1.subgroupInKernel' θ (A.subgroupOf K) ∧
        θ ≠ Section1.principalCharacter K ∧
        χ = Section1.inducedCF K θ

public theorem inducedKernelFamilyOf_isFamily
    {L : Type u} [Group L] [Finite L]
    {K A : Subgroup L}
    {S : Finset (Section1.ClassFunction L)}
    (hS : inducedKernelFamily K ⊥ S)
    (hAK : A ≤ K) :
    inducedKernelFamily K A (inducedKernelFamilyOf K A S) := by
  classical
  refine ⟨hAK, ?_⟩
  intro χ
  constructor
  · intro hχ
    exact (Finset.mem_filter.mp hχ).2
  · intro hχ
    refine Finset.mem_filter.mpr ⟨?_, hχ⟩
    rcases hχ with ⟨θ, hθirr, hθker, hθne, hχeq⟩
    have hbot : Section1.subgroupInKernel' θ ((⊥ : Subgroup L).subgroupOf K) :=
      subgroupInKernel'_subgroupOf_mono (A := A) (B := ⊥) bot_le θ hθker
    exact (hS.2 χ).mpr ⟨θ, hθirr, hbot, hθne, hχeq⟩

public theorem inducedKernelFamilyOf_eq_of_family
    {L : Type u} [Group L] [Finite L]
    {K A : Subgroup L}
    {S SA : Finset (Section1.ClassFunction L)}
    (hS : inducedKernelFamily K ⊥ S)
    (hSA : inducedKernelFamily K A SA) :
    inducedKernelFamilyOf K A S = SA :=
  inducedKernelFamily_unique (inducedKernelFamilyOf_isFamily hS hSA.1) hSA

set_option backward.isDefEq.respectTransparency false in
public theorem characterInflationByHom_isIrreducibleCharacterOnGroup
    {T Q : Type u} [Group T] [Finite T] [Group Q]
    (π : T →* Q) (χ : Q →* ℂˣ) :
    Section1.IsIrreducibleCharacterOnGroup
      (Section1.characterInflationByHom π χ) := by
  let lambda : T →* ℂˣ := χ.comp π
  let ρ0 : Representation ℂ T (Fin 1 → ℂ) := Representation.trivial ℂ T (Fin 1 → ℂ)
  have hρ0irr : Representation.IsIrreducible ρ0 := by
    rw [Representation.irreducible_iff_isSimpleModule_asModule, isSimpleModule_iff]
    exact is_simple_module_of_finrank_eq_one
      (K := ℂ) (A := MonoidAlgebra ℂ T) (V := ρ0.asModule) (by
        change Module.finrank ℂ (Fin 1 → ℂ) = 1
        simp)
  let ρ : Representation ℂ T (Fin 1 → ℂ) :=
    Section1.representationTwistByCharacter lambda ρ0
  have hρirr : Representation.IsIrreducible ρ :=
    Section1.irreducible_twistByCharacter lambda ρ0 hρ0irr
  have hρ0char : ρ0.character = Section1.principalCharacter T := by
    ext t
    simp [ρ0, Section1.principalCharacter, Representation.character, Representation.trivial]
  have hchar :
      Section1.characterInflationByHom π χ = ρ.character := by
    calc
      Section1.characterInflationByHom π χ =
          (fun t : T => (lambda t : ℂ)) * Section1.principalCharacter T := by
            ext t
            simp [lambda, Section1.characterInflationByHom, Section1.principalCharacter]
      _ = (fun t : T => (lambda t : ℂ)) * ρ0.character := by rw [hρ0char]
      _ = ρ.character := by
            simpa [ρ] using
              (Section1.representationTwistByCharacter_character lambda ρ0).symm
  exact ⟨1, ρ, hρirr, hchar⟩

public theorem quotientCharacterInflation_isIrreducibleCharacterOnGroup
    {G : Type u} [Group G] (H T : Subgroup G) [Finite T] [(H.subgroupOf T).Normal]
    (χ : (T ⧸ H.subgroupOf T) →* ℂˣ) :
    Section1.IsIrreducibleCharacterOnGroup
      (Section1.quotientCharacterInflation H T χ) := by
  change Section1.IsIrreducibleCharacterOnGroup
    (Section1.characterInflationByHom (QuotientGroup.mk' (H.subgroupOf T)) χ)
  exact
    characterInflationByHom_isIrreducibleCharacterOnGroup
      (QuotientGroup.mk' (H.subgroupOf T)) χ

public theorem quotientCharacterInflation_injective
    {G : Type u} [Group G] (H T : Subgroup G) [(H.subgroupOf T).Normal] :
    Function.Injective
      (fun χ : (T ⧸ H.subgroupOf T) →* ℂˣ =>
        Section1.quotientCharacterInflation H T χ) := by
  intro χ η hEq
  ext q
  obtain ⟨t, ht⟩ := QuotientGroup.mk'_surjective (H.subgroupOf T) q
  have hval := congrFun hEq t
  simpa [Section1.quotientCharacterInflation, ← ht] using hval

public theorem quotientCharacterInflation_ne_principal_of_ne_one
    {G : Type u} [Group G] (H T : Subgroup G) [(H.subgroupOf T).Normal]
    {χ : (T ⧸ H.subgroupOf T) →* ℂˣ} (hχ : χ ≠ 1) :
    Section1.quotientCharacterInflation H T χ ≠ Section1.principalCharacter T := by
  intro hprin
  apply hχ
  have hone :
      Section1.quotientCharacterInflation H T (1 : (T ⧸ H.subgroupOf T) →* ℂˣ) =
        Section1.principalCharacter T := by
    ext t
    simp [Section1.quotientCharacterInflation, Section1.principalCharacter]
  exact quotientCharacterInflation_injective H T (hprin.trans hone.symm)

public theorem subgroupInKernel'_quotientCharacterInflation
    {G : Type u} [Group G] (H T : Subgroup G) [(H.subgroupOf T).Normal]
    (χ : (T ⧸ H.subgroupOf T) →* ℂˣ) :
    Section1.subgroupInKernel'
      (Section1.quotientCharacterInflation H T χ) (H.subgroupOf T) := by
  intro h
  rw [Section1.quotientCharacterInflation_one_on_subgroup H T χ h]
  rw [Section1.quotientCharacterInflation_degree]

public theorem exists_nontrivial_linear_character_of_solvable
    (G : Type u) [Group G] [Finite G] [Group.IsSolvable G] [Nontrivial G] :
    ∃ χ : G →* ℂˣ, χ ≠ 1 := by
  classical
  rcases exist_index_p_of_solvable G with ⟨H, hHnorm, hprime⟩
  let : H.Normal := hHnorm
  let Q := G ⧸ H
  have hcardQ : Nat.card Q = H.index := by
    simpa [Q] using (Subgroup.index_eq_card H).symm
  have : Fact (Nat.Prime H.index) := ⟨hprime⟩
  have : IsCyclic Q := isCyclic_of_prime_card (α := Q) (p := H.index) hcardQ
  let : CommGroup Q := IsCyclic.commGroup
  have hQ_nontrivial : Nontrivial Q := by
    have hQcard_gt : 1 < Nat.card Q := by
      rw [hcardQ]
      exact hprime.one_lt
    exact (Finite.one_lt_card_iff_nontrivial (α := Q)).mp hQcard_gt
  let : Nontrivial Q := hQ_nontrivial
  obtain ⟨q, hq⟩ := exists_ne (1 : Q)
  have : HasEnoughRootsOfUnity ℂ (Monoid.exponent Q) := by
    have : NeZero (Monoid.exponent Q) := by infer_instance
    exact Section1.complex_hasEnoughRootsOfUnity (Monoid.exponent Q)
  rcases CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity Q ℂ hq with
    ⟨η, hη⟩
  exact ⟨η.comp (QuotientGroup.mk' H), by
    intro hηone
    obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective H q
    have hval := congrFun (congrArg DFunLike.coe hηone) g
    have hqone : η q = 1 := by
      simpa [MonoidHom.comp_apply, hg] using hval
    exact hη hqone⟩

public theorem inducedKernelFamily_exists_degree_relIndex_of_lt
    {L : Type u} [Group L] [Finite L]
    {K A : Subgroup L} {SA : Finset (Section1.ClassFunction L)}
    (hKsolv : Group.IsSolvable K) (hAnorm : A.Normal) (hAK : A < K)
    (hSA : inducedKernelFamily K A SA) :
    ∃ χ : Section1.ClassFunction L,
      χ ∈ SA ∧ Section1.degree χ = (K.relIndex (⊤ : Subgroup L) : ℂ) := by
  classical
  let : (A.subgroupOf K).Normal := hAnorm.subgroupOf K
  let : Group.IsSolvable K := hKsolv
  have hquot_nontrivial : Nontrivial (K ⧸ A.subgroupOf K) := by
    rw [QuotientGroup.nontrivial_iff]
    intro htop
    have hKleA : K ≤ A := by
      simpa [Subgroup.subgroupOf_eq_top] using htop
    exact hAK.not_ge hKleA
  let : Nontrivial (K ⧸ A.subgroupOf K) := hquot_nontrivial
  rcases exists_nontrivial_linear_character_of_solvable (K ⧸ A.subgroupOf K) with
    ⟨χ, hχne⟩
  let θ : Section1.ClassFunction K := Section1.quotientCharacterInflation A K χ
  refine ⟨Section1.inducedCF K θ, ?_, ?_⟩
  · refine (hSA.2 (Section1.inducedCF K θ)).mpr ?_
    exact ⟨θ,
      quotientCharacterInflation_isIrreducibleCharacterOnGroup A K χ,
      subgroupInKernel'_quotientCharacterInflation A K χ,
      quotientCharacterInflation_ne_principal_of_ne_one A K hχne,
      rfl⟩
  · rw [Section1.degree_inducedClassFunction K θ]
    rw [Section1.quotientCharacterInflation_degree]
    simp [Subgroup.relIndex_top_right]

public theorem inducedKernelFamily_nonempty_of_solvable_proper
    {L : Type u} [Group L] [Finite L]
    {K A : Subgroup L} {SA : Finset (Section1.ClassFunction L)}
    (hKsolv : Group.IsSolvable K) (hAnorm : A.Normal) (hAK : A < K)
    (hSA : inducedKernelFamily K A SA) :
    ∃ χ : Section1.ClassFunction L, χ ∈ SA := by
  rcases inducedKernelFamily_exists_degree_relIndex_of_lt hKsolv hAnorm hAK hSA with
    ⟨χ, hχ, _hdeg⟩
  exact ⟨χ, hχ⟩

public noncomputable def representationSubrepresentationCompOrderIso
    {G H k V : Type*} [Monoid G] [Monoid H] [Field k]
    [AddCommGroup V] [Module k V]
    (ρ : Representation k H V) (φ : G →* H) (hφ : Function.Surjective φ) :
    Subrepresentation (ρ.comp φ) ≃o Subrepresentation ρ where
  toFun σ :=
    { toSubmodule := σ.toSubmodule
      apply_mem_toSubmodule := by
        intro h v hv
        rcases hφ h with ⟨g, rfl⟩
        exact σ.apply_mem_toSubmodule g hv }
  invFun τ :=
    { toSubmodule := τ.toSubmodule
      apply_mem_toSubmodule := by
        intro g v hv
        exact τ.apply_mem_toSubmodule (φ g) hv }
  left_inv σ := by
    apply Subrepresentation.toSubmodule_injective
    rfl
  right_inv τ := by
    apply Subrepresentation.toSubmodule_injective
    rfl
  map_rel_iff' := by
    intro σ τ
    rfl

public theorem representation_isIrreducible_comp_surjective
    {G H k V : Type*} [Monoid G] [Monoid H] [Field k]
    [AddCommGroup V] [Module k V]
    (ρ : Representation k H V) (φ : G →* H) (hφ : Function.Surjective φ)
    (hρ : Representation.IsIrreducible ρ) :
    Representation.IsIrreducible (ρ.comp φ) := by
  have : Representation.IsIrreducible ρ := hρ
  exact OrderIso.isSimpleOrder
    (representationSubrepresentationCompOrderIso ρ φ hφ)

public theorem representation_isIrreducible_of_comp_surjective
    {G H k V : Type*} [Monoid G] [Monoid H] [Field k]
    [AddCommGroup V] [Module k V]
    (ρ : Representation k H V) (φ : G →* H) (hφ : Function.Surjective φ)
    (hρ : Representation.IsIrreducible (ρ.comp φ)) :
    Representation.IsIrreducible ρ := by
  have : Representation.IsIrreducible (ρ.comp φ) := hρ
  exact OrderIso.isSimpleOrder
    (representationSubrepresentationCompOrderIso ρ φ hφ).symm

public theorem inducedKernelFamily_degree_eq_relIndex_of_quotient_commutative
    {L : Type u} [Group L] [Finite L]
    {K A : Subgroup L} {SA : Finset (Section1.ClassFunction L)}
    (hSA : inducedKernelFamily K A SA)
    (hAnorm : A.Normal)
    (hcomm : IsMulCommutative (K ⧸ A.subgroupOf K))
    {χ : Section1.ClassFunction L} (hχ : χ ∈ SA) :
    Section1.degree χ = (K.relIndex (⊤ : Subgroup L) : ℂ) := by
  classical
  have : (A.subgroupOf K).Normal := hAnorm.subgroupOf K
  rcases (hSA.2 χ).mp hχ with ⟨θ, hθirr, hθker, _hθne, hχeq⟩
  rcases hθirr with ⟨n, ρ, hρirr, hθeq⟩
  let q : K →* K ⧸ A.subgroupOf K := QuotientGroup.mk' (A.subgroupOf K)
  have hθkerρ : Section1.subgroupInKernel' ρ.character (A.subgroupOf K) := by
    simpa [hθeq] using hθker
  have hker : Section1.subgroupInRepresentationKernel ρ (A.subgroupOf K) :=
    (Section1.subgroupInKernel'_character_iff_subgroupInRepresentationKernel ρ
      (A.subgroupOf K)).mp hθkerρ
  let ρq : Representation ℂ (K ⧸ A.subgroupOf K) (Fin n → ℂ) :=
    Section1.quotientRepresentationOfKernelSubgroup ρ (A.subgroupOf K) hker
  have hcomp_eq : ρq.comp q = ρ := by
    apply MonoidHom.ext
    intro k
    exact Section1.quotientRepresentationOfKernelSubgroup_mk ρ
      (A.subgroupOf K) hker k
  have hρqirr : Representation.IsIrreducible ρq := by
    apply representation_isIrreducible_of_comp_surjective ρq q
      (QuotientGroup.mk'_surjective (A.subgroupOf K))
    simpa [hcomp_eq] using hρirr
  have : IsMulCommutative (K ⧸ A.subgroupOf K) := hcomm
  have hn : n = 1 := by
    have : Representation.IsIrreducible ρq := hρqirr
    simpa using
      (Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative (ρ := ρq))
  rw [hχeq, Section1.degree_inducedClassFunction K θ]
  rw [hθeq, Section1.degree_representation_character]
  simp [hn, Subgroup.relIndex_top_right]

public theorem inducedKernelFamily_degree_data
    {L : Type u} [Group L] [Finite L]
    {K A : Subgroup L} {SA : Finset (Section1.ClassFunction L)}
    (hSA : inducedKernelFamily K A SA)
    {χ : Section1.ClassFunction L} (hχ : χ ∈ SA) :
    ∃ dθ dχ : ℕ,
      Section1.degree χ = (dχ : ℂ) ∧
        dχ = K.relIndex (⊤ : Subgroup L) * dθ ∧
          K.relIndex (⊤ : Subgroup L) ∣ dχ := by
  classical
  rcases (hSA.2 χ).mp hχ with ⟨θ, hθirr, _hθker, _hθne, hχeq⟩
  rcases hθirr with ⟨n, ρ, _hρirr, hθeq⟩
  refine ⟨n, K.relIndex (⊤ : Subgroup L) * n, ?_, rfl, dvd_mul_right _ _⟩
  rw [hχeq, Section1.degree_inducedClassFunction K θ]
  rw [hθeq, Section1.degree_representation_character]
  simp [Subgroup.relIndex_top_right, Nat.cast_mul]

public theorem inducedKernelFamily_conjugate_mem
    {L : Type u} [Group L] [Finite L]
    {K A : Subgroup L} [K.Normal]
    {S : Finset (Section1.ClassFunction L)}
    (hS : inducedKernelFamily K A S)
    {χ : Section1.ClassFunction L}
    (hχ : χ ∈ S) :
    Section1.conjugateCharacter χ ∈ S := by
  rcases (hS.2 χ).mp hχ with ⟨θ, hθirr, hθker, hθne, hχeq⟩
  refine (hS.2 (Section1.conjugateCharacter χ)).mpr ?_
  refine ⟨Section1.conjugateCharacter θ,
    Section1.isIrreducibleCharacterOnGroup_conjugateCharacter hθirr,
    subgroupInKernel'_conjugateCharacter θ hθker, ?_, ?_⟩
  · intro hprin
    apply hθne
    calc
      θ = Section1.conjugateCharacter (Section1.conjugateCharacter θ) := by
        ext k
        simp [Section1.conjugateCharacter]
      _ = Section1.conjugateCharacter (Section1.principalCharacter K) := by
        rw [hprin]
      _ = Section1.principalCharacter K :=
        Section1.conjugateCharacter_principalCharacter
  · rw [hχeq, Section1.conjugateCharacter_inducedCF K θ]

public theorem inducedKernelFamily_conjugate_closed
    {L : Type u} [Group L] [Finite L]
    {K A : Subgroup L} [K.Normal]
    {S : Finset (Section1.ClassFunction L)}
    (hS : inducedKernelFamily K A S) :
    ∀ χ : Section1.ClassFunction L, χ ∈ S →
      Section1.conjugateCharacter χ ∈ S := by
  intro χ hχ
  exact inducedKernelFamily_conjugate_mem hS hχ

public theorem inducedKernelFamily_union_conjugate_closed
    {L : Type u} [Group L] [Finite L]
    {K A B : Subgroup L} [K.Normal]
    {SA SB : Finset (Section1.ClassFunction L)}
    (hSA : inducedKernelFamily K A SA)
    (hSB : inducedKernelFamily K B SB) :
    ∀ χ : Section1.ClassFunction L, χ ∈ SA ∪ SB →
      Section1.conjugateCharacter χ ∈ SA ∪ SB := by
  intro χ hχ
  rcases Finset.mem_union.mp hχ with hχA | hχB
  · exact Finset.mem_union.mpr (Or.inl (inducedKernelFamily_conjugate_mem hSA hχA))
  · exact Finset.mem_union.mpr (Or.inr (inducedKernelFamily_conjugate_mem hSB hχB))


/-- Coherence of a sec6 family, always relative to the punctured support. -/
@[expose] public def coherentFamily
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    (S : Finset (Section1.ClassFunction L))
    (T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G) : Prop :=
  Section5.definition_5_1_statement Section5.puncturedSet S T

public theorem coherentFamily_mono
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    {S₁ S₂ : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (hsub : S₁ ⊆ S₂)
    (hnonempty : Section5.integerSpanOnNonempty S₁ Section5.puncturedSet) :
    coherentFamily S₂ T → coherentFamily S₁ T := by
  intro hcoh
  exact Section5.IsCoherentTriple_mono hsub hnonempty hcoh

public theorem not_coherentFamily_union_of_right
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    {S₁ S₂ : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (hnonempty : Section5.integerSpanOnNonempty S₂ Section5.puncturedSet)
    (hnot : ¬ coherentFamily S₂ T) :
    ¬ coherentFamily (S₁ ∪ S₂) T := by
  intro hcoh
  exact hnot (coherentFamily_mono (by intro χ hχ; simp [hχ]) hnonempty hcoh)

public theorem inducedKernelFamily_integerSpanOnNonempty_of_mem
    {L : Type u} [Group L] [Finite L]
    {K A : Subgroup L} [K.Normal]
    {S SA : Finset (Section1.ClassFunction L)}
    (hsetup : Section5.hypothesis_5_2_setup_statement S)
    (h52a : Section5.hypothesis_5_2_a_statement S)
    (hsub : SA ⊆ S)
    (hSA : inducedKernelFamily K A SA)
    {χ : Section1.ClassFunction L}
    (hχ : χ ∈ SA) :
    Section5.integerSpanOnNonempty SA Section5.puncturedSet := by
  let X : S := ⟨χ, hsub hχ⟩
  have hχbar : Section1.conjugateCharacter χ ∈ SA :=
    inducedKernelFamily_conjugate_mem hSA hχ
  have hχne : χ ≠ Section1.conjugateCharacter χ := (h52a X).2
  have hχchar : Section1.IsCharacter χ := hsetup.2 X
  exact Section5.integerSpanOnNonempty_of_conjugate_pair hχ hχbar hχne hχchar

public theorem finset_closed_maximal_obstruction
    {α : Type u} [DecidableEq α]
    (conj : α → α)
    (hconj : ∀ x, conj (conj x) = x)
    (P : Finset α → Prop)
    (A U : Finset α)
    (hAU : A ⊆ U)
    (hAcl : ∀ x, x ∈ A → conj x ∈ A)
    (hUcl : ∀ x, x ∈ U → conj x ∈ U)
    (hPA : P A)
    (hnotU : ¬ P U) :
    ∃ S x,
      A ⊆ S ∧ S ⊆ U ∧
      (∀ y, y ∈ S → conj y ∈ S) ∧ P S ∧
      x ∈ U ∧ x ∉ S ∧ ¬ P (S ∪ ({x, conj x} : Finset α)) := by
  classical
  let candidates : Finset (Finset α) :=
    U.powerset.filter fun S => A ⊆ S ∧ (∀ y, y ∈ S → conj y ∈ S) ∧ P S
  have hA_mem : A ∈ candidates := by
    simp [candidates, hAU, hPA]
    exact hAcl
  have hnonempty : candidates.Nonempty := ⟨A, hA_mem⟩
  rcases Finset.exists_max_image candidates Finset.card hnonempty with ⟨S, hS_mem, hmax⟩
  have hS_data : S ⊆ U ∧ A ⊆ S ∧ (∀ y, y ∈ S → conj y ∈ S) ∧ P S := by
    simpa [candidates] using hS_mem
  rcases hS_data with ⟨hSU, hAS, hScl, hPS⟩
  have hS_ne_U : S ≠ U := by
    intro hEq
    apply hnotU
    simpa [hEq] using hPS
  have hS_ssub_U : S ⊂ U := Finset.ssubset_iff_subset_ne.mpr ⟨hSU, hS_ne_U⟩
  rcases Finset.exists_of_ssubset hS_ssub_U with ⟨x, hxU, hxS⟩
  refine ⟨S, x, hAS, hSU, hScl, hPS, hxU, hxS, ?_⟩
  intro hPnew
  let Snew : Finset α := S ∪ ({x, conj x} : Finset α)
  have hSnew_subset_U : Snew ⊆ U := by
    intro y hy
    rcases Finset.mem_union.mp hy with hyS | hypair
    · exact hSU hyS
    · simp at hypair
      rcases hypair with rfl | rfl
      · exact hxU
      · exact hUcl x hxU
  have hASnew : A ⊆ Snew := by
    intro y hy
    exact Finset.mem_union.mpr (Or.inl (hAS hy))
  have hSnew_closed : ∀ y, y ∈ Snew → conj y ∈ Snew := by
    intro y hy
    rcases Finset.mem_union.mp hy with hyS | hypair
    · exact Finset.mem_union.mpr (Or.inl (hScl y hyS))
    · simp at hypair
      rcases hypair with rfl | rfl
      · simp [Snew]
      · have hx : conj (conj x) = x := hconj x
        simp [Snew, hx]
  have hSnew_mem : Snew ∈ candidates := by
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_powerset.mpr hSnew_subset_U, hASnew, hSnew_closed, ?_⟩
    simpa [Snew] using hPnew
  have hSsubnew : S ⊆ Snew := by
    intro y hy
    exact Finset.mem_union.mpr (Or.inl hy)
  have hxSnew : x ∈ Snew := by
    simp [Snew]
  have hS_ssub_new : S ⊂ Snew :=
    (Finset.ssubset_iff_of_subset hSsubnew).2 ⟨x, hxSnew, hxS⟩
  have hlt : S.card < Snew.card := Finset.card_lt_card hS_ssub_new
  have hle : Snew.card ≤ S.card := hmax Snew hSnew_mem
  exact not_lt_of_ge hle hlt

public theorem inducedKernelFamily_closed_obstruction
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    {K A B : Subgroup L} [K.Normal]
    {SA SB : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (hSA : inducedKernelFamily K A SA)
    (hSB : inducedKernelFamily K B SB)
    (hcoh : coherentFamily SA T)
    (hnotUnion : ¬ coherentFamily (SA ∪ SB) T) :
    ∃ S1 ψ,
      SA ⊆ S1 ∧ S1 ⊆ SA ∪ SB ∧
        (∀ χ, χ ∈ S1 → Section1.conjugateCharacter χ ∈ S1) ∧
          coherentFamily S1 T ∧
            ψ ∈ SB ∧ ψ ∉ S1 ∧
              ¬ coherentFamily (S1 ∪ ({ψ, Section1.conjugateCharacter ψ} :
                Finset (Section1.ClassFunction L))) T := by
  classical
  rcases finset_closed_maximal_obstruction
      (conj := Section1.conjugateCharacter)
      (hconj := by intro χ; ext g; simp [Section1.conjugateCharacter])
      (P := fun U => coherentFamily U T)
      (A := SA) (U := SA ∪ SB)
      (hAU := by intro χ hχ; exact Finset.mem_union.mpr (Or.inl hχ))
      (hAcl := inducedKernelFamily_conjugate_closed hSA)
      (hUcl := inducedKernelFamily_union_conjugate_closed hSA hSB)
      (hPA := hcoh) (hnotU := hnotUnion) with
    ⟨S1, ψ, hSA_S1, hS1_U, hS1_closed, hS1_coh, hψU, hψS1, hnotPair⟩
  have hψSB : ψ ∈ SB := by
    rcases Finset.mem_union.mp hψU with hψSA | hψSB
    · exact (hψS1 (hSA_S1 hψSA)).elim
    · exact hψSB
  exact ⟨S1, ψ, hSA_S1, hS1_U, hS1_closed, hS1_coh, hψSB, hψS1, hnotPair⟩

public theorem inducedKernelFamily_closed_obstruction_of_mem
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    {K A B : Subgroup L} [K.Normal]
    {S SA SB : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (hsetup : Section5.hypothesis_5_2_setup_statement S)
    (h52a : Section5.hypothesis_5_2_a_statement S)
    (hSBsub : SB ⊆ S)
    (hSA : inducedKernelFamily K A SA)
    (hSB : inducedKernelFamily K B SB)
    (hcoh : coherentFamily SA T)
    (hnot : ¬ coherentFamily SB T)
    {χ : Section1.ClassFunction L}
    (hχ : χ ∈ SB) :
    ∃ S1 ψ,
      SA ⊆ S1 ∧ S1 ⊆ SA ∪ SB ∧
        (∀ η, η ∈ S1 → Section1.conjugateCharacter η ∈ S1) ∧
          coherentFamily S1 T ∧
            ψ ∈ SB ∧ ψ ∉ S1 ∧
              ¬ coherentFamily (S1 ∪ ({ψ, Section1.conjugateCharacter ψ} :
                Finset (Section1.ClassFunction L))) T := by
  have hnonempty : Section5.integerSpanOnNonempty SB Section5.puncturedSet :=
    inducedKernelFamily_integerSpanOnNonempty_of_mem
      hsetup h52a hSBsub hSB hχ
  exact inducedKernelFamily_closed_obstruction hSA hSB hcoh
    (not_coherentFamily_union_of_right hnonempty hnot)

/-- The chain-and-centrality package from PF `(6.2)(a)`:
`B ≤ D ≤ C ≤ K` and `D/B ≤ Z(C/B)`.

The quotient centrality is recorded in the equivalent commutator form
`⁅D, C⁆ ≤ B`, under the normality hypotheses from the book.
-/
@[expose] public def centralQuotientHypothesis
    {L : Type u} [Group L]
    (K B C D : Subgroup L) : Prop :=
  B ≤ D ∧ D ≤ C ∧ C ≤ K ∧
    B.Normal ∧ C.Normal ∧ D.Normal ∧
    ⁅D, C⁆ ≤ B

public theorem centralQuotient_B_le_D
    {L : Type u} [Group L] {K B C D : Subgroup L}
    (h : centralQuotientHypothesis K B C D) : B ≤ D :=
  h.1

public theorem centralQuotient_D_lt_C
    {L : Type u} [Group L] {K B C D : Subgroup L}
    (h : centralQuotientHypothesis K B C D) : D ≤ C :=
  h.2.1

public theorem centralQuotient_C_le_K
    {L : Type u} [Group L] {K B C D : Subgroup L}
    (h : centralQuotientHypothesis K B C D) : C ≤ K :=
  h.2.2.1

public theorem centralQuotient_B_normal
    {L : Type u} [Group L] {K B C D : Subgroup L}
    (h : centralQuotientHypothesis K B C D) : B.Normal :=
  h.2.2.2.1


public theorem centralQuotient_commutator_le
    {L : Type u} [Group L] {K B C D : Subgroup L}
    (h : centralQuotientHypothesis K B C D) : ⁅D, C⁆ ≤ B :=
  h.2.2.2.2.2.2


/-- The quotient `K/M` is nilpotent. -/
@[expose] public def nilpotentQuotient
    {L : Type u} [Group L] [Finite L]
    (M K : Subgroup L) : Prop :=
  ∃ _hMK : M ≤ K, ∃ _hMnormK : (M.subgroupOf K).Normal,
    M.Normal ∧ K.Normal ∧ Group.IsNilpotent (K ⧸ M.subgroupOf K)

public theorem nilpotent_normal_inf_center_ne_bot
    {G : Type*} [Group G] [Group.IsNilpotent G]
    (N : Subgroup G) [N.Normal] (hN : N ≠ ⊥) :
    N ⊓ Subgroup.center G ≠ ⊥ := by
  classical
  rcases Group.IsNilpotent.nilpotent G with ⟨n, hn⟩
  let P : ℕ → Prop := fun n => N ⊓ Subgroup.upperCentralSeries G n ≠ ⊥
  have hExists : ∃ n, P n := by
    refine ⟨n, ?_⟩
    dsimp [P]
    rw [hn, inf_top_eq]
    exact hN
  set m := Nat.find hExists with hm_def
  have hmP : P m := by
    rw [hm_def]
    exact Nat.find_spec hExists
  have hm_min : ∀ k < m, ¬ P k := by
    intro k hk
    exact Nat.find_min hExists (by simpa [hm_def] using hk)
  by_cases hm0 : m = 0
  · rw [hm0] at hmP
    dsimp [P] at hmP
    rw [inf_bot_eq] at hmP
    exact (hmP rfl).elim
  · rcases Nat.exists_eq_succ_of_ne_zero hm0 with ⟨k, hk⟩
    have hmPsucc : P (k + 1) := by
      simpa [hk] using hmP
    have hprev_bot : N ⊓ Subgroup.upperCentralSeries G k = ⊥ := by
      by_contra hne
      exact hm_min k (by rw [hk]; exact Nat.lt_succ_self k) hne
    apply fun hbot => hmPsucc ?_
    apply le_antisymm ?_ bot_le
    intro x hx
    have hxN : x ∈ N := hx.1
    have hxU : x ∈ Subgroup.upperCentralSeries G (k + 1) := hx.2
    have hxcenter : x ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro y
      have hcommU : x * y * x⁻¹ * y⁻¹ ∈ Subgroup.upperCentralSeries G k :=
        (Subgroup.mem_upperCentralSeries_succ_iff).mp hxU y
      have hcommN : x * y * x⁻¹ * y⁻¹ ∈ N := by
        have hyxinv : y * x⁻¹ * y⁻¹ ∈ N := by
          exact (inferInstance : N.Normal).conj_mem (x⁻¹) (N.inv_mem hxN) y
        simpa [mul_assoc] using N.mul_mem hxN hyxinv
      have hcommInf : x * y * x⁻¹ * y⁻¹ ∈ N ⊓ Subgroup.upperCentralSeries G k :=
        ⟨hcommN, hcommU⟩
      have hcommOne : x * y * x⁻¹ * y⁻¹ = 1 := by
        simpa [hprev_bot] using hcommInf
      have hxy : x * y = y * x := by
        calc
          x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
          _ = y * x := by rw [hcommOne]; simp
      exact hxy.symm
    simpa [hbot] using (show x ∈ N ⊓ Subgroup.center G from ⟨hxN, hxcenter⟩)

public theorem nilpotent_commutator_lt_self_of_normal
    {G : Type*} [Group G] [Group.IsNilpotent G]
    (N : Subgroup G) [N.Normal] (hN : N ≠ ⊥) :
    ⁅N, (⊤ : Subgroup G)⁆ < N := by
  have hle : ⁅N, (⊤ : Subgroup G)⁆ ≤ N :=
    Subgroup.commutator_le_left (H₁ := N) (H₂ := (⊤ : Subgroup G))
  refine lt_of_le_of_ne hle ?_
  intro hEq
  have hEq' : N = ⁅N, (⊤ : Subgroup G)⁆ := hEq.symm
  have hN_le_lcs : ∀ n, N ≤ (⊤ : Subgroup G).lowerCentralSeries n := by
    intro n
    induction n with
    | zero =>
        simp [Subgroup.lowerCentralSeries_zero]
    | succ n ih =>
        calc
          N = ⁅N, (⊤ : Subgroup G)⁆ := hEq'
          _ ≤ ⁅(⊤ : Subgroup G).lowerCentralSeries n, (⊤ : Subgroup G)⁆ :=
            Subgroup.commutator_mono ih le_rfl
          _ = (⊤ : Subgroup G).lowerCentralSeries (n + 1) := rfl
  rcases (Subgroup.nilpotent_iff_lowerCentralSeries (G := G)).1
      (show Group.IsNilpotent G from inferInstance) with ⟨n, hn⟩
  apply hN
  exact le_bot_iff.mp (by simpa [hn] using hN_le_lcs n)

public theorem nilpotentQuotient_of_le_right
    {L : Type u} [Group L] [Finite L]
    {M B H : Subgroup L}
    (hnil : nilpotentQuotient M H)
    (hMB : M ≤ B) (hBnorm : B.Normal) :
    Group.IsNilpotent (H ⧸ B.subgroupOf H) := by
  rcases hnil with ⟨_hMH, hMnormH, _hMnorm, _hHnorm, hnilHM⟩
  let Msub : Subgroup H := M.subgroupOf H
  let Bsub : Subgroup H := B.subgroupOf H
  have : Msub.Normal := hMnormH
  have : Bsub.Normal := hBnorm.subgroupOf H
  let q : H →* H ⧸ Msub := QuotientGroup.mk' Msub
  let Bbar : Subgroup (H ⧸ Msub) := Bsub.map q
  have : Bbar.Normal := QuotientGroup.map_normal Msub Bsub
  have hMsubBsub : Msub ≤ Bsub := by
    intro x hx
    exact hMB hx
  have hnilQuot : Group.IsNilpotent ((H ⧸ Msub) ⧸ Bbar) := by
    infer_instance
  exact Group.nilpotent_of_mulEquiv
    (G := (H ⧸ Msub) ⧸ Bbar)
    (G' := H ⧸ Bsub)
    (QuotientGroup.quotientQuotientEquivQuotient Msub Bsub hMsubBsub)

/-- `H₁/M` is the commutator subgroup of `K/M`. -/
@[expose] public def commutatorQuotientHypothesis
    {L : Type u} [Group L] [Finite L]
    (M H1 K : Subgroup L) : Prop :=
  ∃ _hMK : M ≤ K, ∃ _hH1K : H1 ≤ K, ∃ _hMH1 : M ≤ H1,
    ∃ _hMnormK : (M.subgroupOf K).Normal,
      M.Normal ∧ H1.Normal ∧ K.Normal ∧
        (H1.subgroupOf K).map (QuotientGroup.mk' (M.subgroupOf K)) =
          commutator (K ⧸ M.subgroupOf K)

public theorem commutatorQuotientHypothesis_quotient_commutative
    {L : Type u} [Group L] [Finite L]
    {M H1 K : Subgroup L}
    (hH1norm : H1.Normal)
    (hcomm : commutatorQuotientHypothesis M H1 K) :
    IsMulCommutative (K ⧸ H1.subgroupOf K) := by
  classical
  rcases hcomm with
    ⟨_hMK, _hH1K, hMH1, hMnormK, _hMnorm, _hH1norm', _hKnorm, hcommEq⟩
  have : (M.subgroupOf K).Normal := hMnormK
  have : (H1.subgroupOf K).Normal := hH1norm.subgroupOf K
  apply Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr
  intro x hx
  let q : K →* K ⧸ M.subgroupOf K := QuotientGroup.mk' (M.subgroupOf K)
  have hmap_comm : (commutator K).map q = commutator (K ⧸ M.subgroupOf K) := by
    rw [show commutator K = ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ from rfl]
    rw [Subgroup.map_commutator]
    have hqtop :
        (⊤ : Subgroup K).map q = (⊤ : Subgroup (K ⧸ M.subgroupOf K)) := by
      rw [eq_top_iff]
      intro y _hy
      rcases QuotientGroup.mk'_surjective (M.subgroupOf K) y with ⟨k, rfl⟩
      exact ⟨k, by simp, rfl⟩
    rw [hqtop]
    rfl
  have hqx_mem : q x ∈ (H1.subgroupOf K).map q := by
    rw [hcommEq]
    rw [← hmap_comm]
    exact ⟨x, hx, rfl⟩
  rcases hqx_mem with ⟨y, hyH1, hyq⟩
  have hxyM : x / y ∈ M.subgroupOf K := by
    exact (QuotientGroup.eq_iff_div_mem).mp hyq.symm
  have hxyH1 : x / y ∈ H1.subgroupOf K := by
    exact hMH1 hxyM
  have hx_eq : x = (x / y) * y := by
    exact (div_mul_cancel x y).symm
  rw [hx_eq]
  exact mul_mem hxyH1 hyH1

/-- The quotient `K/H₁` is a chief factor of `L`. -/
@[expose] public def chiefFactorQuotient
    {L : Type u} [Group L]
    (H1 K : Subgroup L) : Prop :=
  IsChiefFactor H1 K

/-- The quotient `K/M` is a nonabelian `p`-group. -/
@[expose] public def nonabelianPQuotient
    {L : Type u} [Group L] [Finite L]
    (M K : Subgroup L) (p : ℕ) : Prop :=
  ∃ _hMK : M ≤ K, ∃ _hMnormK : (M.subgroupOf K).Normal,
    M.Normal ∧ K.Normal ∧ Nat.Prime p ∧
      IsPGroup p (K ⧸ M.subgroupOf K) ∧
        ¬ IsMulCommutative (K ⧸ M.subgroupOf K)

/-- `L/H₁` is a Frobenius group with kernel `K/H₁`.

The complement is left unnamed, as in the source statement.
-/
@[expose] public def frobeniusQuotientWithKernel
    {L : Type u} [Group L]
    (K H1 : Subgroup L) : Prop :=
  ∃ hH1 : H1.Normal,
    let : H1.Normal := hH1
    H1 ≤ K ∧ K.Normal ∧
      ∃ R : Subgroup (L ⧸ H1),
        (K.map (QuotientGroup.mk' H1)).IsComplement' R ∧
          (K.map (QuotientGroup.mk' H1)) ≠ ⊥ ∧
          R ≠ ⊥ ∧
          ∀ r : R, r ≠ 1 →
            Section2.centralizerIn (K.map (QuotientGroup.mk' H1)) (r : L ⧸ H1) = ⊥

public theorem frobeniusQuotientWithKernel_left_lt
    {L : Type u} [Group L]
    {K H1 : Subgroup L}
    (hfrob : frobeniusQuotientWithKernel K H1) :
    H1 < K := by
  rcases hfrob with ⟨hH1norm, hH1K, _hKnorm, _R, _hcomp, hKbar_ne_bot, _hRne, _hcent⟩
  have : H1.Normal := hH1norm
  refine lt_of_le_of_ne hH1K ?_
  intro hKH1
  apply hKbar_ne_bot
  rw [eq_bot_iff]
  intro x hx
  rcases hx with ⟨k, hkK, rfl⟩
  have hkH1 : k ∈ H1 := by
    simpa [hKH1] using hkK
  simpa using (QuotientGroup.eq_one_iff (N := H1) (x := k)).2 hkH1

/-- `|C_L(z)|` is constant on `Z#`. -/
@[expose] public def constantCentralizerOrderOnNonidentity
    {L : Type u} [Group L] [Finite L]
    (Z L0 : Subgroup L) : Prop :=
  ∀ z1 z2 : Z, z1 ≠ 1 → z2 ≠ 1 →
    Nat.card (Section2.centralizerIn L0 (z1 : L)) =
      Nat.card (Section2.centralizerIn L0 (z2 : L))

/-- The regular character of a finite group, used as `ρ_Z` in PF `(6.8.2.2)`. -/
@[expose] public def regularCharacter
    (G : Type u) [One G] [Finite G] : Section1.ClassFunction G :=
  fun g => if g = 1 then (Nat.card G : ℂ) else 0

/-- A class function is constant on `Z#`. -/
@[expose] public def constantOnNonidentitySubgroup
    {L : Type u} [Group L]
    (Z : Subgroup L)
    (χ : Section1.ClassFunction L) : Prop :=
  ∀ z1 z2 : Z, z1 ≠ 1 → z2 ≠ 1 → χ z1 = χ z2

public theorem constantOnNonidentitySubgroup_restriction_eq_regular_add
    {L : Type u} [Group L] [Finite L]
    {Z : Subgroup L}
    {χ : Section1.ClassFunction L}
    (hconst : constantOnNonidentitySubgroup Z χ)
    (z0 : Z) (hz0 : z0 ≠ 1) :
    ∃ a b : ℂ,
      Section1.subgroupRestriction Z χ =
        a • regularCharacter Z + b • Section1.principalCharacter Z := by
  classical
  refine ⟨(χ 1 - χ z0) / (Nat.card Z : ℂ), χ z0, ?_⟩
  ext z
  by_cases hz : z = 1
  · subst z
    simp [regularCharacter, Section1.subgroupRestriction, Section1.principalCharacter]
  · have hzconst : χ z = χ z0 := hconst z z0 hz hz0
    simp [regularCharacter, Section1.subgroupRestriction, Section1.principalCharacter, hz,
      hzconst]

/--
The congruence convention used in PF `(6.7)`: `α ≡ β (mod n)` means that
`α`, `β`, and `(α - β) / n` are algebraic integers.
-/
@[expose] public def algebraicIntegerCongruentModNat
    (n : ℕ) (α β : ℂ) : Prop :=
  IsIntegral ℤ α ∧ IsIntegral ℤ β ∧ IsIntegral ℤ ((α - β) / (n : ℂ))

/-- A conjugacy class of the ambient group meets `Z#`. -/
@[expose] public def conjugacyClassMeetsPuncturedSubgroup
    {G : Type u} [Group G]
    (c : ConjClasses G) (Z : Subgroup G) : Prop :=
  ∃ z : G, z ∈ c.carrier ∧ z ∈ Z ∧ z ≠ 1

/-- A conjugacy class of the ambient group is disjoint from `Z`. -/
@[expose] public def conjugacyClassDisjointFromSubgroup
    {G : Type u} [Group G]
    (c : ConjClasses G) (Z : Subgroup G) : Prop :=
  ∀ z : G, z ∈ c.carrier → z ∉ Z

/-- The class multiplication coefficients `aᵢⱼₛ` from PF `(6.7)`. -/
@[expose] public def classProductCoefficientData
    {G : Type u} [Group G]
    (a : ConjClasses G → ConjClasses G → ConjClasses G → ℕ) : Prop :=
  ∀ i j s : ConjClasses G, ∀ x : G, x ∈ s.carrier →
    a i j s =
      Nat.card {p : i.carrier × j.carrier // p.1.1 * p.2.1 = x}

/-- The common value `α = ω(C_s)` on conjugacy classes meeting `Z#` in PF `(6.7)`. -/
@[expose] public def theorem_6_7_alphaData
    {G : Type u} [Group G] [Finite G]
    (Z : Subgroup G) (ψ : Section1.ClassFunction G) (α : ℂ) : Prop :=
  ∀ s : ConjClasses G, conjugacyClassMeetsPuncturedSubgroup s Z →
    ∃ z : G, z ∈ s.carrier ∧ z ∈ Z ∧ z ≠ 1 ∧
      α = (Nat.card s.carrier : ℂ) * ψ z / ψ 1

/-- The coefficient `aᵢⱼ = ∑_{Cₛ ∩ Z# ≠ ∅} aᵢⱼₛ` from PF `(6.7.2)`. -/
@[expose] public noncomputable def theorem_6_7_aij
    {G : Type u} [Group G] [Finite G]
    (Z : Subgroup G)
    (a : ConjClasses G → ConjClasses G → ConjClasses G → ℕ)
    (i j : ConjClasses G) : ℕ := by
  classical
  exact (Finset.univ.filter fun s : ConjClasses G =>
    conjugacyClassMeetsPuncturedSubgroup s Z).sum (fun s => a i j s)

/-- The image of the punctured subgroup `H#` in an ambient group containing `L`. -/
@[expose] public def subgroupImagePuncturedSet
    {G : Type u} [Group G]
    (L : Subgroup G) (H : Subgroup L) : Set G :=
  {g | ∃ h : H, ((h : L) : G) = g ∧ (h : L) ≠ 1}

/-- The map `T` agrees with induction on `Z[S, L#]`. -/
@[expose] public def transformAgreesWithInductionOn
    {G : Type u} [Group G] [Finite G]
    (L : Subgroup G)
    (S : Finset (Section1.ClassFunction L))
    (T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G) : Prop :=
  ∀ χ : Section1.ClassFunction L,
    Section5.integerSpanOn S Section5.puncturedSet χ →
      T χ = Section1.inducedCF L χ

/-- A named extension witnessing coherence of a family. -/
@[expose] public def coherentExtension
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    (S : Finset (Section1.ClassFunction L))
    (T T' : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G) : Prop :=
  Section5.isCFLinearIsometryOnSpan S T' ∧
    Section5.mapsIntegerSpanToVirtualCharacters S T' ∧
      Section5.agreesOnIntegerSpanOn S Section5.puncturedSet T T'

/-- A class function on `G` is constant on the image of `Z# ≤ L#` in `G`. -/
@[expose] public def constantOnSubgroupImageNonidentity
    {G : Type u} [Group G]
    (L : Subgroup G) (Z : Subgroup L)
    (χ : Section1.ClassFunction G) : Prop :=
  ∀ z1 z2 : Z, z1 ≠ 1 → z2 ≠ 1 → χ ((z1 : L) : G) = χ ((z2 : L) : G)

/-- Orthogonality to the transformed image of a finite family. -/
@[expose] public def orthogonalToTransformedFinset
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    (S : Finset (Section1.ClassFunction L))
    (T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (X : Section1.ClassFunction G) : Prop :=
  ∀ η : Section1.ClassFunction L, η ∈ S → Section1.scalarProduct G X (T η) = 0

/-- `L₀` is a Frobenius group with kernel `K`. -/
@[expose] public def frobeniusWithKernel
    {L : Type u} [Group L]
    (L0 K : Subgroup L) : Prop :=
  K ≤ L0 ∧
    (K.subgroupOf L0).Normal ∧
    ∃ R : Subgroup L0,
      (K.subgroupOf L0).IsComplement' R ∧
        (K.subgroupOf L0) ≠ ⊥ ∧
        R ≠ ⊥ ∧
        ∀ r : R, r ≠ 1 →
          Section2.centralizerIn (K.subgroupOf L0) (r : L0) = ⊥

/-- The auxiliary notation witnessing the sec4 Hypothesis `(4.6)` in
PF `(6.8)`, case `(c2)`, with `K = H` and `A = H#`.

The Section 6 arguments only use the PF5-facing Section `(4.6)` consequences,
so the supported package is the intended interface here. -/
public structure caseC2FullData
    {G : Type u} [Group G] [Finite G]
    (L : Subgroup G)
    (H W1 W2 W : Subgroup L)
    (T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G) : Type (u + 1) where
  I : Type u
  J : Type u
  instFintypeI : Fintype I
  instFintypeJ : Fintype J
  instDecidableEqI : DecidableEq I
  instDecidableEqJ : DecidableEq J
  i0 : I
  j0 : J
  omega : I → J → Section1.ClassFunction W
  sigmaL : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction L
  sigma : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G
  piChar : I → J → Section1.ClassFunction L
  xChar : J → Section1.ClassFunction H
  deltaSign : J → ℂ
  H_A : G → Subgroup G
  H_A0 : G → Subgroup G
  fullHypothesis :
    let : Fintype I := instFintypeI
    let : Fintype J := instFintypeJ
    let : DecidableEq I := instDecidableEqI
    let : DecidableEq J := instDecidableEqJ
    Section4Scratch.hypothesis_4_6_supported_statement L H W1 W2 W H
      ({h : L | h ∈ H ∧ h ≠ 1})
      i0 j0 omega sigmaL sigma piChar xChar deltaSign T H_A

/-- The sec6 case `(c2)` package from PF `(6.8)`. -/
@[expose] public def caseC2Hypothesis
    {G : Type u} [Group G] [Finite G]
    (L : Subgroup G)
    (H W1 W2 W : Subgroup L)
    (T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G) : Prop :=
  Nonempty (caseC2FullData L H W1 W2 W T) ∧
    (∃ p : ℕ, Nat.Prime p ∧ Nat.card W2 = p) ∧
    W2 ≤ ⁅H, H⁆

/-- PF `(6.8)`, case `(A)`: `Z(H) ∩ W₂ = 1`, with `Z = Z(H) ∩ H'`. -/
@[expose] public def theorem_6_8_caseAData
    {L : Type u} [Group L]
    (H W2 Z : Subgroup L) : Prop :=
  centerIn H ⊓ W2 = ⊥ ∧
    Z = centerIn H ⊓ ⁅H, H⁆

/-- PF `(6.8)`, case `(B)`: `1 ≠ W₂ ≤ Z(H)`, with `Z = W₂`. -/
@[expose] public def theorem_6_8_caseBData
    {L : Type u} [Group L]
    (H W2 Z : Subgroup L) : Prop :=
  W2 ≠ ⊥ ∧
    W2 ≤ centerIn H ∧
      W2 ≤ ⁅H, H⁆ ∧
        Z = W2

/-- The local families `X = S - S(Z)` and `Y = S(H')` used in PF `(6.8)`. -/
@[expose] public def theorem_6_8_familyData
    {L : Type u} [Group L] [Finite L]
    (H Z : Subgroup L)
    (S SZ X Y : Finset (Section1.ClassFunction L)) : Prop :=
  Z ≤ H ∧
    inducedKernelFamily H Z SZ ∧
      X = S \ SZ ∧
        inducedKernelFamily H ⁅H, H⁆ Y

/-- The common `Y` occurring in PF `(6.8.2.2)`, independent of `φ`. -/
@[expose] public def theorem_6_8_2_2_commonY
    {G : Type u} [Group G] [Finite G]
    (L : Subgroup G)
    (H Z : Subgroup L)
    (Yset : Finset (Section1.ClassFunction L))
    (T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (η₁ : Section1.ClassFunction L)
    (Ycf : Section1.ClassFunction G) : Prop :=
  η₁ ∈ Yset ∧
    (Ycf = τ₁ η₁ ∨
      ∃ η₂ : Section1.ClassFunction L,
        Yset.card = 2 ∧ η₂ ∈ Yset ∧ η₂ ≠ η₁ ∧ Ycf = -τ₁ η₂) ∧
    ∀ φ : Section1.ClassFunction Z,
      Section1.IsIrreducibleCharacterOnGroup φ →
        φ ≠ Section1.principalCharacter Z →
          ∃ X : Section1.ClassFunction G,
            orthogonalToTransformedFinset Yset τ₁ X ∧
              T (Section1.inducedCF Z φ - (Z.relIndex H : ℂ) • η₁) =
                X - (Z.relIndex H : ℂ) • Ycf

end CFSG.Section6
