module

public import CFSG.Quasithin.Vol2.Ch4Sec2T425A
public import CFSG.Quasithin.EmptyFaithful.S14113Stage

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]

namespace Set425

variable {T M L Mm I H : Subgroup G} (s : Set425 G T M L Mm I H)
include s

theorem charTwo_M : CharTwo M :=
  charTwo_of_isTwoLocal_of_isSylowTwoOf_le s.hyp.qtke.2.1 (isSylowTwoOf_top s.hyp.sylow)
    s.hyp.maxTwoLocal.1 s.hyp.T_le

theorem oddCoreIn_M : oddCoreIn M = ⊥ := by
  set O := oddCoreIn M with hO
  have hOM : O ≤ M := C2Nine.oddCoreIn_le_self M
  have hdis : O ⊓ pCoreOf 2 M = ⊥ := C2Nine.oddCoreIn_inf_eq_bot (pCoreOf_isPGroup 2 M) M
  have hc : ⁅O, pCoreOf 2 M⁆ = ⊥ := by
    have h1 : ⁅O, pCoreOf 2 M⁆ ≤ O ⊓ pCoreOf 2 M :=
      le_inf (Subgroup.le_normalizer_iff_commutator_le_left.mp
          ((pCoreOf_le 2 M).trans (C2Nine.le_normalizer_oddCoreIn M)))
        (Subgroup.le_normalizer_iff_commutator_le_right.mp
          (hOM.trans (le_normalizer_pCoreOf 2 M)))
    rw [hdis] at h1
    exact le_bot_iff.mp h1
  have hOC : O ≤ M ⊓ Subgroup.centralizer (pCoreOf 2 M : Set G) :=
    le_inf hOM (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc)
  have h2 : O ≤ O ⊓ pCoreOf 2 M := le_inf le_rfl (hOC.trans s.charTwo_M)
  rw [hdis] at h2
  exact le_bot_iff.mp h2

theorem pCoreOf_inf_eq : pCoreOf 2 (H ⊓ M) = pCoreOf 2 H :=
  a4_4_1 (pCoreOf_le_oTwoFstarIn H) (le_inf (oTwoFstarIn_le H) s.le) (a44Hyp_oTwoFstarIn H)

theorem normalizer_Q : Subgroup.normalizer (pCoreOf 2 (H ⊓ M) : Set G) = H := by
  rw [s.pCoreOf_inf_eq]
  exact eq_normalizer_pCoreOf_of_isMaxTwoLocal s.inM.1

theorem isTwoRadicalIn_Q : IsTwoRadicalIn M (pCoreOf 2 (H ⊓ M)) := by
  refine ⟨(pCoreOf_le 2 _).trans inf_le_right, ?_, ?_⟩
  · rw [s.pCoreOf_inf_eq]
    exact pCoreOf_ne_bot_of_isTwoLocal s.inM.1.1
  · rw [s.normalizer_Q, inf_comm]

theorem hypC23 : HypC23 M (pCoreOf 2 (H ⊓ M)) (H ⊓ M) := by
  have hcc : conjClosure (pCoreOf 2 (H ⊓ M)) (H ⊓ M) = pCoreOf 2 (H ⊓ M) :=
    conjClosure_eq_self (le_normalizer_pCoreOf 2 _)
  refine ⟨sqtkGroup_of_pCoreOf_ne_bot s.hyp.qtke s.hyp.simple s.hyp.nonabelian
      (pCoreOf_ne_bot_of_isTwoLocal s.hyp.maxTwoLocal.1), s.isTwoRadicalIn_Q, inf_le_right,
    ?_, ?_⟩
  · exact a4_4_2 (pCoreOf_le_oTwoFstarIn H) (le_inf (oTwoFstarIn_le H) s.le)
      (a44Hyp_oTwoFstarIn H) s.inM.1
  · rw [hcc]
    refine ⟨le_rfl, pCoreOf_isPGroup 2 _, ?_⟩
    rw [Subgroup.subgroupOf_self, Subgroup.index_top]
    decide

theorem pCoreOf_M_le : pCoreOf 2 M ≤ pCoreOf 2 (H ⊓ M) :=
  c2_1_pCore_le s.isTwoRadicalIn_Q

theorem lemma_4_2_7_one (c : Inp425 G) :
    perfectCore (L ⊓ H) = L ∧ L ≤ H ∧ L ∈ cComp H := by
  have hLc : L ∈ cComp M := s.hyp.mem_cComp c.a37 c.a39
  have hO2L : pCoreOf 2 L ≤ H := fun x hx =>
    (pCoreOf_le 2 _).trans inf_le_left
      (s.pCoreOf_M_le (A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hLc) hx))
  have hLH : L ≤ H := (s.hyp.le_perfectCore_sup c.a37 c.a38 c.a39 s.inM.2).trans
    (_root_.sup_le ((perfectCore_le _).trans inf_le_right) hO2L)
  have hLHeq : perfectCore (L ⊓ H) = L := by
    rw [inf_eq_left.mpr hLH]
    exact perfectCore_eq_self_of_perfect s.hyp.perfect
  refine ⟨hLHeq, hLH, ?_⟩
  have := (s.lemma_4_2_6_two c).2.1
  rwa [hLHeq] at this

theorem inf_eq (c : Inp425 G) : H ⊓ M = H ⊓ Subgroup.normalizer (L : Set G) := by
  have h := (s.lemma_4_2_6_two c).2.2.1
  rwa [(s.lemma_4_2_7_one c).1] at h

theorem relIndex_eq (c : Inp425 G) : (H ⊓ M).relIndex H = 2 :=
  (s.lemma_4_2_6_two c).2.2.2

theorem inf_normal (c : Inp425 G) : ((H ⊓ M).subgroupOf H).Normal :=
  Subgroup.normal_of_index_eq_two (s.relIndex_eq c)

theorem le_normalizer_inf (c : Inp425 G) : H ≤ Subgroup.normalizer ((H ⊓ M : Subgroup G) : Set G) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mp (s.inf_normal c)

end Set425

end CFSG.Quasithin.H13.Ch4
