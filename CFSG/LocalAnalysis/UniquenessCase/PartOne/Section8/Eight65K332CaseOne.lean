module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight65FrattiniWeak

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.RankThreeUC (uniqueSet)

theorem centralizer_le_of_normalClosure_le_pPrimeCore_sup {G : Type} [Group G] [Finite G]
    {D : Data G} {Q Z C : Subgroup G} {S : Subgroup ↥C}
    (hZU : Z ∈ uniqueSet D.M)
    (hO3 : ∀ O : Subgroup G, Q ≤ Subgroup.normalizer (O : Set G) →
      Nat.Coprime 3 (Nat.card O) → O ≤ D.M)
    (hQC : Q ≤ C) (hZQ : Z ≤ Q) (hZcard : Nat.card Z = 3)
    (hwc : CFSG.ASVolI.ChIJK.IsWeaklyClosedIn Z (Subgroup.normalizer (Z : Set G)))
    (hS : IsPGroup 3 S) (hZS : Z.subgroupOf C ≤ S)
    (hKS : Subgroup.normalClosure ((Z.subgroupOf C : Subgroup ↥C) : Set ↥C) ≤
      CFSG.pPrimeCore 3 ↥C ⊔ S) :
    C ≤ D.M := by
  have hNM : Subgroup.normalizer (Z : Set G) ≤ D.M :=
    CFSG.LocalAnalysis.RankThreeUC.normalizer_le_of_mem_uniqueSet D.maxLocal hZU
  have hZ3 : IsPGroup 3 Z := IsPGroup.of_card (n := 1) (by simpa using hZcard)
  set S₁ : Subgroup G := S.map C.subtype with hS₁def
  have hS₁p : IsPGroup 3 S₁ := hS₁def ▸ hS.map C.subtype
  have hZS₁ : Z ≤ S₁ := by
    intro z hz
    have hzC : z ∈ C := hZQ.trans hQC hz
    exact Subgroup.mem_map.mpr
      ⟨⟨z, hzC⟩, hZS (Subgroup.mem_subgroupOf.mpr hz), rfl⟩
  have hS₁M : S₁ ≤ D.M :=
    CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.le_of_mem_uniqueSet_of_isPGroup
      D.maxLocal hZU hZS₁ hS₁p
  set O : Subgroup G := (CFSG.pPrimeCore 3 ↥C).map C.subtype with hOdef
  have hOcard : Nat.Coprime 3 (Nat.card O) := by
    rw [hOdef, Subgroup.card_map_of_injective C.subtype_injective]
    exact CFSG.pPrimeCore_coprime_card
  have hQO : Q ≤ Subgroup.normalizer (O : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro q hq x hx
    rw [hOdef] at hx ⊢
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hx
    refine Subgroup.mem_map.mpr ⟨⟨q, hQC hq⟩ * z * ⟨q, hQC hq⟩⁻¹, ?_, ?_⟩
    · simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using
        (CFSG.pPrimeCore_normal (p := 3) (G := ↥C)).conj_mem z hz ⟨q, hQC hq⟩
    · simp
  have hOM : O ≤ D.M := hO3 O hQO hOcard
  set K' : Subgroup ↥C :=
    Subgroup.normalClosure ((Z.subgroupOf C : Subgroup ↥C) : Set ↥C) with hK'def
  set K : Subgroup G := K'.map C.subtype with hKdef
  have hKle : K ≤ O ⊔ S₁ := by
    calc K = K'.map C.subtype := hKdef
      _ ≤ (CFSG.pPrimeCore 3 ↥C ⊔ S).map C.subtype := by
        rw [hK'def]
        exact Subgroup.map_mono hKS
      _ = O ⊔ S₁ := by rw [Subgroup.map_sup, hOdef, hS₁def]
  have hKleM : K ≤ D.M := hKle.trans (sup_le hOM hS₁M)
  have hKsub : K.subgroupOf C = K' := by
    rw [hKdef]
    exact Subgroup.comap_map_eq_self_of_injective C.subtype_injective K'
  have hKn : (K.subgroupOf C).Normal := by
    rw [hKsub]
    exact Subgroup.normalClosure_normal
  have hKC : K ≤ C := by
    rw [hKdef]
    exact Subgroup.map_subtype_le K'
  have hZK : Z ≤ K := by
    intro z hz
    have hzC : z ∈ C := hZQ.trans hQC hz
    rw [hKdef]
    exact Subgroup.mem_map.mpr
      ⟨⟨z, hzC⟩, Subgroup.subset_normalClosure (Subgroup.mem_subgroupOf.mpr hz), rfl⟩
  obtain ⟨T, hT⟩ := (hZ3.comap_subtype (K := C)).exists_le_sylow
  let P : Subgroup G := (T : Subgroup ↥C).map C.subtype
  have hP : CFSG.ABGLocalTools.IsSylowOf 3 P C := ⟨T, rfl⟩
  have hZP : Z ≤ P := by
    intro z hz
    have hzC : z ∈ C := hZQ.trans hQC hz
    exact Subgroup.mem_map.mpr
      ⟨⟨z, hzC⟩, hT (Subgroup.mem_subgroupOf.mpr hz), rfl⟩
  have hKeq : C = K ⊔ (Subgroup.normalizer (Z : Set G) ⊓ C) :=
    eq_sup_inf_normalizer_of_isWeaklyClosedIn_normalizer hKC hKn hZK hP hZP hwc
  rw [hKeq]
  exact sup_le hKleM (inf_le_left.trans hNM)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
