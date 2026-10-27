module

public import CFSG.Quasithin.H13.L32A76S2e
public import CFSG.Quasithin.Vol2.Ch1Prop121
public import CFSG.Quasithin.Vol2.Ch1Comm
public import CFSG.Quasithin.Background.A4Aut
public import CFSG.Assembly.Subnormal
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CharacteristicPrimeLocal
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.OrderingMax
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43

public section

namespace CFSG.Quasithin.H13.L32A.S2

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.A4

theorem eq_bot_or_eq_top_of_subnormal {X : Type*} [Group X] [IsSimpleGroup X] {H K : Subgroup X}
    (h : IsSubnormal H K) (hK : K = ⊤) : H = ⊥ ∨ H = ⊤ :=
  by subst hK; exact h.eq_bot_or_top

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_centralizer_of_autOn_eq_bot {A X : Subgroup G}
    (hX : X ≤ Subgroup.normalizer (A : Set G)) (h : autOn X A = ⊥) :
    X ≤ Subgroup.centralizer (A : Set G) := by
  intro x hx
  have hmem : conjAct A ⟨x, hX hx⟩ ∈ autOn X A := Subgroup.mem_map.mpr ⟨⟨x, hX hx⟩, hx, rfl⟩
  rw [h, Subgroup.mem_bot] at hmem
  exact CFSG.Quasithin.A4.conjAct_eq_one_iff.mp hmem

omit [Finite G] in
theorem autOn_eq_bot_of_le_centralizer {A X : Subgroup G}
    (hX : X ≤ Subgroup.centralizer (A : Set G)) : autOn X A = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨y, hy, rfl⟩
  exact CFSG.Quasithin.A4.conjAct_eq_one_iff.mpr (hX hy)

theorem autOn_pCoreOf_eq_bot {A : Subgroup G} (hA : IsElemAbelian 2 A) (h8 : Nat.card A = 8)
    (hGL : autOn (Subgroup.normalizer (A : Set G)) A = ⊤) :
    autOn (pCoreOf 2 (Subgroup.normalizer (A : Set G))) A = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := Subgroup.normalizer (A : Set G) with hNdef
  refine E8.eq_bot_of_isPGroup_of_normal hA h8 ?_ ?_
  · refine ⟨fun a ha g => ?_⟩
    have hg : g ∈ autOn N A := hGL ▸ Subgroup.mem_top g
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hg
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp ha
    refine Subgroup.mem_map.mpr ⟨y * z * y⁻¹, ?_, by simp⟩
    have hzO : (z : G) ∈ pCoreOf 2 N := hz
    show (y : G) * z * (y : G)⁻¹ ∈ pCoreOf 2 N
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 N hy) _).mp hzO
  · exact ((pCoreOf_isPGroup 2 N).comap_of_injective N.subtype N.subtype_injective).map
      (conjAct A)

theorem exists_LA (hK : quasithinIsQTKECat G) (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (h37 : A37ForSQTK) (h39 : A39ForSQTK) {A : Subgroup G}
    (hA : IsElemAbelian 2 A) (h8 : Nat.card A = 8)
    (hGL : autOn (Subgroup.normalizer (A : Set G)) A = ⊤) :
    ∃ LA ∈ cComp (Subgroup.normalizer (A : Set G)),
      Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (LA : Set G) ∧ autOn LA A = ⊤ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := Subgroup.normalizer (A : Set G) with hNdef
  have hsimp := E8.isSimpleGroup_mulAut hA h8
  have hA2 : IsPGroup 2 A := fun x => ⟨1, Subtype.ext (by simpa using hA.2 x x.2)⟩
  have hAO : A ≤ pCoreOf 2 N := le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl hA2
  have hA1 : A ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at h8
    norm_num at h8
  have hO : pCoreOf 2 N ≠ ⊥ := fun h => hA1 (le_bot_iff.mp (h ▸ hAO))
  obtain ⟨L, hL, hLA⟩ : ∃ L ∈ cComp N, autOn L A ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    have hspan : cCompSpan N ≤ Subgroup.centralizer (A : Set G) :=
      sSup_le fun L hL => le_centralizer_of_autOn_eq_bot ((le_of_mem_cComp hL).trans le_rfl)
        (hcon L hL)
    rw [lemma_1_2_1_one hK hs hnab h39 hO] at hspan
    have hmap : autOn (perfectCore N) A = ⊤ := by
      have e1 : (perfectCore (⊤ : Subgroup ↥N)).map N.subtype = perfectCore N := by
        rw [map_perfectCore, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
      have e2 : (perfectCore N).subgroupOf N = perfectCore (⊤ : Subgroup ↥N) := by
        apply Subgroup.map_injective N.subtype_injective
        rw [Subgroup.map_subgroupOf_eq_of_le (perfectCore_le _), e1]
      have e3 : (⊤ : Subgroup ↥N).map (conjAct A) = ⊤ := by
        have : autOn N A = (⊤ : Subgroup ↥N).map (conjAct A) := by
          unfold autOn
          rw [Subgroup.subgroupOf_self]
        rw [← this, hGL]
      unfold autOn
      rw [e2, map_perfectCore, e3]
      exact perfectCore_eq_self_of_perfect (E8.commutator_top hA h8)
    have hbot : autOn (perfectCore N) A = ⊥ := autOn_eq_bot_of_le_centralizer hspan
    have h1 : (⊤ : Subgroup (MulAut ↥A)) = ⊥ := hmap.symm.trans hbot
    have := E8.card_mulAut hA h8
    rw [← Subgroup.card_top, h1, Subgroup.card_bot] at this
    norm_num at this
  have hLtop : autOn L A = ⊤ := by
    have hsub : IsSubnormal (autOn L A) (autOn N A) := autOn_subnormal (subnormal_of_mem_cComp hL)
    rcases eq_bot_or_eq_top_of_subnormal hsub hGL with h | h
    · exact absurd h hLA
    · exact h
  refine ⟨L, hL, ?_, hLtop⟩
  intro x hx
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  by_contra hne
  have hLx := map_conj_mem_cComp hL hx
  obtain ⟨hc, hcO⟩ := lemma_1_2_1_two hK hs hnab h37 hO hL hLx (Ne.symm hne)
  have hO2 : autOn (pCoreOf 2 N) A = ⊥ := autOn_pCoreOf_eq_bot hA h8 hGL
  have hcomm : ⁅autOn L A, autOn (L.map (MulAut.conj x).toMonoidHom) A⁆ = ⊥ := by
    have hle : ⁅L, L.map (MulAut.conj x).toMonoidHom⁆ ≤ pCoreOf 2 N := hc.trans hcO
    have hLN : L ≤ N := le_of_mem_cComp hL
    have hLxN : L.map (MulAut.conj x).toMonoidHom ≤ N := le_of_mem_cComp hLx
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro a ha b hb
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hb
    have hyz : (y : G) * z * (y : G)⁻¹ * (z : G)⁻¹ ∈ pCoreOf 2 N :=
      hle (Subgroup.commutator_mem_commutator hy hz)
    have h1 : conjAct A (y * z * y⁻¹ * z⁻¹) ∈ autOn (pCoreOf 2 N) A :=
      Subgroup.mem_map.mpr ⟨y * z * y⁻¹ * z⁻¹, hyz, rfl⟩
    rw [hO2, Subgroup.mem_bot] at h1
    rw [Subgroup.mem_bot, commutatorElement_def]
    simpa [map_mul, map_inv] using h1
  have hLxtop : autOn (L.map (MulAut.conj x).toMonoidHom) A = ⊤ := by
    have hsub : IsSubnormal (autOn (L.map (MulAut.conj x).toMonoidHom) A) (autOn N A) :=
      autOn_subnormal (subnormal_of_mem_cComp hLx)
    rcases eq_bot_or_eq_top_of_subnormal hsub hGL with h | h
    · exfalso
      have hle := le_centralizer_of_autOn_eq_bot (le_of_mem_cComp hLx) h
      apply hLA
      rw [eq_bot_iff]
      rintro _ ⟨y, hy, rfl⟩
      rw [Subgroup.mem_bot, CFSG.Quasithin.A4.conjAct_eq_one_iff]
      intro a ha
      have hy' : x * y * x⁻¹ ∈ L.map (MulAut.conj x).toMonoidHom := ⟨y, hy, rfl⟩
      have h1 := Subgroup.mem_centralizer_iff.mp (hle hy') (x * a * x⁻¹)
        ((Subgroup.mem_normalizer_iff.mp hx a).mp ha)
      have h2 : x * (a * y) * x⁻¹ = x * (y * a) * x⁻¹ := by
        calc x * (a * y) * x⁻¹ = (x * a * x⁻¹) * (x * y * x⁻¹) := by group
          _ = (x * y * x⁻¹) * (x * a * x⁻¹) := h1
          _ = x * (y * a) * x⁻¹ := by group
      have h3 : a * y = y * a := by simpa using h2
      exact h3
    · exact h
  rw [hLtop, hLxtop] at hcomm
  rw [E8.commutator_top hA h8] at hcomm
  have := E8.card_mulAut hA h8
  rw [← Subgroup.card_top, hcomm, Subgroup.card_bot] at this
  norm_num at this

end CFSG.Quasithin.H13.L32A.S2

end
