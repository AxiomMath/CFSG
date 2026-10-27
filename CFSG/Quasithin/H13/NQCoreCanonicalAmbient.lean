module

public import CFSG.Quasithin.H13.NQCoreUniqueNormalizer
public import CFSG.Quasithin.H13.NQCoreLocalChar
public import CFSG.Quasithin.H13.NQBlockComplementaryLayer

public section

namespace CFSG.Quasithin.H13.NQCore

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

structure SNAmbient (T D : Subgroup G) : Prop where
  pCore_ne_bot : pCoreOf 2 D ≠ ⊥
  cComp_normalizer : D ∈ cComp (normalizer (D : Set G))
  cComp_self : D ∈ cComp D
  cComp_sup : D ∈ cComp (D ⊔ T)
  isCComponent_top : CFSG.IsCComponent (⊤ : Subgroup ↥D)
  genFitting : quasithinGenFitting D = pCoreOf 2 D
  sqt : CFSG.IsStronglyQuasithin ↥D
  sqtk : CFSG.SectionRank.IsSQTKCat ↥(normalizer (D : Set G))
  charTwo_normalizer : CharTwo (normalizer (D : Set G))
  charTwo_sup : CharTwo (D ⊔ T)
  normalizer_eq : normalizer (D : Set G) = normalizer (pCoreOf 2 D : Set G)
  unique : U3.UniqueMaxTwoLocal (D ⊔ T) (normalizer (D : Set G))

omit [Finite G] in
theorem pCoreOf_ne_bot_of_quasithinV2_ne_bot {D : Subgroup G} (h : quasithinV2 D ≠ ⊥) :
    pCoreOf 2 D ≠ ⊥ := by
  intro hbot
  apply h
  have hZ : Subgroup.closure {z | z ∈ pCoreOf 2 D ⊓ centralizer (pCoreOf 2 D : Set G) ∧
      z ^ 2 = 1} = ⊥ := by
    refine eq_bot_iff.mpr ((Subgroup.closure_le _).mpr fun z hz => ?_)
    have : z ∈ pCoreOf 2 D := hz.1.1
    rw [hbot] at this
    exact this
  rw [quasithinV2, hZ, Subgroup.commutator_bot_left]

theorem snAmbient (hA7u : U3.SylowNormalizedMaximalLocalUniqueNormalizer)
    (hA7n : NQBlock.SylowNormalizedLocalNormalComponent) [hs : IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hQ : quasithinIsQTKECat G) {T D : Subgroup G}
    (hT : quasithinIsSylowTwo T) (hDmax : quasithinIsMaximalLocal T D)
    (hDf : quasithinIsFaithfulLocal T D) (hTD : T ≤ normalizer (D : Set G)) :
    SNAmbient T D := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO2 : pCoreOf 2 D ≠ ⊥ := pCoreOf_ne_bot_of_quasithinV2_ne_bot hDf.2.2.2
  obtain ⟨hNeq, hU, -⟩ := hA7u G T D hs hnab hQ hT hDmax hTD hO2
  set J := normalizer (D : Set G) with hJ
  have hJ2 : pCoreOf 2 J ≠ ⊥ := pCoreOf_ne_bot_of_isTwoLocal hU.1.1
  have hTJ : T ≤ J := hTD
  have hT' : IsSylowTwoOf T ⊤ := isSylowTwoOf_of_quasithinIsSylowTwo hT le_top
  have hTJs : IsSylowTwoOf T J := isSylowTwoOf_of_quasithinIsSylowTwo hT hTJ
  have hDJ : D ≤ J := le_normalizer
  obtain ⟨L, ⟨hLc, hDL⟩, -, -, hmax⟩ := hA7n G hnab hQ J T D hJ2 hTJs hDJ hDmax.1 hTD
  obtain ⟨hLD, -⟩ := hmax hDmax
  rw [hLD] at hLc
  have hDself : D ∈ cComp D := cComp_mem_of_le hLc le_rfl hDJ
  have hDsup : D ∈ cComp (D ⊔ T) := cComp_of_isLocal hDmax.1
  have hDtop : CFSG.IsCComponent (⊤ : Subgroup ↥D) := by
    have h3 := mem_cComp_top_iff_isCComponent.mp (subgroupOf_mem_cComp hDself)
    rwa [subgroupOf_self] at h3
  have hsqtkJ : CFSG.SectionRank.IsSQTKCat ↥J := (qt_positive_two_core_SQTK hnab hQ hJ2).2
  have hsqtkD : CFSG.SectionRank.IsSQTKCat ↥D := (qt_positive_two_core_SQTK hnab hQ hO2).2
  have hDT2 : pCoreOf 2 (D ⊔ T) ≠ ⊥ := hDmax.1.2.2.2
  exact
    { pCore_ne_bot := hO2
      cComp_normalizer := hLc
      cComp_self := hDself
      cComp_sup := hDsup
      isCComponent_top := hDtop
      genFitting := hDf.2.2.1
      sqt := hsqtkD.1
      sqtk := hsqtkJ
      charTwo_normalizer := charTwo_of_isSylowTwoOf_le_of_pCore_ne_bot hQ.2.1 hT' hTJ hJ2
      charTwo_sup := charTwo_of_isSylowTwoOf_le_of_pCore_ne_bot hQ.2.1 hT' le_sup_right hDT2
      normalizer_eq := hNeq
      unique := hU }

end CFSG.Quasithin.H13.NQCore
