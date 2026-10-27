module

public import CFSG.Quasithin.Vol2.Ch3Sec2Conj

public section

namespace CFSG.Quasithin.H13

open scoped IsMulCommutative Pointwise

theorem exists_mem_irrPlusOn_iso {G : Type*} [Group G] {V : Type*} [CommGroup V]
    [MulDistribMulAction G V] {X T : Subgroup G} [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    (hTX : T ≤ Subgroup.normalizer (X : Set G)) (hT2 : IsPGroup 2 ↥T) {I : Subgroup V}
    (hI : I ∈ IrrPlus X ⊤) :
    ∃ I' ∈ IrrPlusOn X ⊤ T, XMod.Iso ↥X (tilde X ⊤ I') (tilde X ⊤ I) := by
  have hW : ∀ t ∈ T, ∀ w ∈ (⊤ : Subgroup V), t • w ∈ (⊤ : Subgroup V) :=
    fun _ _ _ _ => Subgroup.mem_top _
  let := quotAct hTX hW
  have hnorm := normalizes_quot hTX hW
  obtain ⟨hirr, hcomm⟩ := isIrr_tilde hI
  have hQ : ∀ q : V ⧸ modFix X ⊤, q ^ 2 = 1 := by
    intro q
    refine QuotientGroup.induction_on q fun v => ?_
    rw [← QuotientGroup.mk_pow, hV v, QuotientGroup.mk_one]
  obtain ⟨L', -, hL'irr, hL'iso, hL'H⟩ := XMod.exists_isHomComp_of_isIrr hQ hnorm hT2 hirr
  have hL'comm : XMod.commOf ↥X L' = L' := XMod.commOf_eq_of_iso hirr hL'irr hL'iso hcomm
  have hle : L' ≤ tilde X ⊤ ⊤ := by
    rw [tilde, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
    exact le_top
  obtain ⟨hI'mem, hI'tilde⟩ := lift_mem_irrPlus hL'irr hL'comm hle
  refine ⟨_, (mem_irrPlusOn_iff hTX hW).2 ⟨hI'mem, ?_⟩, ?_⟩
  · rw [hI'tilde]
    exact hL'H
  · rw [hI'tilde]
    exact hL'iso

variable {G : Type} [Group G]

theorem exists_isIrrPlusIn_sectionIso [Finite G] {A X T I : Subgroup G} [IsMulCommutative ↥A]
    (hA2 : ∀ a ∈ A, a ^ 2 = 1) (hX : X ≤ Subgroup.normalizer (A : Set G))
    (hT : T ≤ Subgroup.normalizer (A : Set G)) (hTX : T ≤ Subgroup.normalizer (X : Set G))
    (hT2 : IsPGroup 2 ↥T) (hI : IsIrrPlusBase X A I) :
    ∃ V₀ : Subgroup G, IsIrrPlusIn X A T V₀ ∧
      IsXSectionIso₂ X V₀ (V₀ ⊓ Subgroup.centralizer (X : Set G)) I
        (I ⊓ Subgroup.centralizer (X : Set G)) := by
  have hIA : I ≤ A := hI.1
  have hI' := (isIrrPlusBase_iff hX hIA).1 hI
  have hTX' : onA A T ≤ Subgroup.normalizer ((onA A X : Subgroup _) : Set _) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro n
    exact Subgroup.mem_normalizer_iff.1 (hTX (Subgroup.mem_subgroupOf.1 ht)) (n : G)
  have hT2' : IsPGroup 2 ↥(onA A T) := hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hT).symm
  have hV : ∀ v : ↥A, v ^ 2 = 1 := fun v => Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hA2 v v.2)
  obtain ⟨I'', hI''on, hiso⟩ := exists_mem_irrPlusOn_iso hV hTX' hT2' hI'
  refine ⟨I''.map A.subtype, isIrrPlusIn_map_of_mem_irrPlusOn hX hT hI''on, ?_⟩
  have h := isXSectionIso₂_of_iso_tilde hX hiso
  rwa [Subgroup.map_subgroupOf_eq_of_le hIA] at h

end CFSG.Quasithin.H13
