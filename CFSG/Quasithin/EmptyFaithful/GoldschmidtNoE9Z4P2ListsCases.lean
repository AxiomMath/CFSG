module

public import CFSG.Quasithin.EmptyFaithful.S146zXCore
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P2Cfg
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P2ExCrit2
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P2FinInst
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P2ListsSmall

public section

namespace CFSG.Quasithin.E9P2L

open CFSG.Open hiding StatedClassicalModel StatedSL StatedLieTag
open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.EmptyFaithfulMultiple CFSG.Quasithin.He4

variable {G : Type} [Group G] [Finite G] {T M H PQ : Subgroup G} {p : ℕ}

theorem invariant_data (hA3 : A3Orbits G) (S : Setting146 G T M) {K L : Subgroup G}
    (hL : L ∈ cComp (mcOf T)) (hXL : K ≤ conjClosure L T)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) :
    mcOf T ≤ Subgroup.normalizer (L : Set G) ∧ K ≤ L := by
  have hTMc : T ≤ mcOf T := S.isHTM_mcOf.1.1
  have hsylMc : IsSylowTwoOf T (mcOf T) := isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.sylow hTMc
  have hSQ : IsSQTKIn (mcOf T) := S.sqtkGroup_of_isHTM S.isHTM_mcOf
  refine ⟨S146zX.le_normalizer_of_invariant hA3 hSQ hsylMc hL hTL, hXL.trans ?_⟩
  exact conjClosure_le fun g hg l hl => (Subgroup.mem_normalizer_iff.mp (hTL hg) l).mp hl

theorem e9Local_of_inv (h35 : Lemma1435) (S : Setting146 G T M) (hred : IsRedCE T M H PQ p)
    (hshape : IsE9Z4Shape T H p) {L : Subgroup G} (hL : L ∈ cComp (mcOf T))
    (hKc : conjClosure (oTwoUpper H) (mcOf T) = L) :
    ∃ Eh : Subgroup (OTwoQuot (mcOf T)),
      E9Local (imageOTwoQuot (mcOf T) L) (imageOTwoQuot (mcOf T) T)
        (imageOTwoQuot (mcOf T) H) Eh (imageOTwoQuot (mcOf T) (pCoreOf 2 H)) ∧
      Nonempty (↥(imageOTwoQuot (mcOf T) L) ≃* (↥L ⧸ CFSG.pCore 2 ↥L)) := by
  obtain ⟨Eh, -, hloc⟩ := e9Local_of_config h35 S hred hshape
  rw [hKc] at hloc
  obtain ⟨eK⟩ := q_oTwoQuot_equiv_image (subnormal_of_mem_cComp hL)
  exact ⟨Eh, hloc, ⟨eK.symm.trans (Der6D.oTwoQuotEquiv L)⟩⟩

theorem false_of_l33
    (h35 : Lemma1435) (S : Setting146 G T M)
    (hred : IsRedCE T M H PQ p) (hshape : IsE9Z4Shape T H p) {L : Subgroup G}
    (hL : L ∈ cComp (mcOf T)) (hKc : conjClosure (oTwoUpper H) (mcOf T) = L)
    (h : StatedClassicalModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 3 1 ∨
      Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ≃* ↥(StatedSL 3 (ZMod 3)))) : False := by
  obtain ⟨Eh, hloc, ⟨hLt⟩⟩ := e9Local_of_inv h35 S hred hshape hL hKc
  rcases h with h | ⟨⟨e⟩⟩
  · have hmod : StatedClassicalModel ↥(imageOTwoQuot (mcOf T) L) .PSL 3 3 1 :=
      CFSG.SectionRank.statedClassicalModel_of_mulEquiv hLt h
    exact hloc.false_of_smallFacts (smallFacts_l33 (Or.inl hmod) (noInvCommNine_l33 hmod))
  · have h' : Nonempty (↥(imageOTwoQuot (mcOf T) L) ≃* ↥(StatedSL 3 (ZMod 3))) := ⟨hLt.trans e⟩
    have hmod := statedClassicalModel_of_statedSL_three_three h'
    exact hloc.false_of_smallFacts (smallFacts_l33 (Or.inr h') (noInvCommNine_l33 hmod))

theorem false_of_m11
    (h35 : Lemma1435)
    (S : Setting146 G T M) (hred : IsRedCE T M H PQ p) (hshape : IsE9Z4Shape T H p)
    {L : Subgroup G} (hL : L ∈ cComp (mcOf T))
    (hKc : conjClosure (oTwoUpper H) (mcOf T) = L)
    (h : Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ≃*
      CFSG.Blueprint.NativeSporadic.Carrier TauCeti.SporadicName.M11)) : False := by
  obtain ⟨Eh, hloc, ⟨hLt⟩⟩ := e9Local_of_inv h35 S hred hshape hL hKc
  obtain ⟨e⟩ := h
  have h' : Nonempty (↥(imageOTwoQuot (mcOf T) L) ≃*
      CFSG.Blueprint.NativeSporadic.Carrier TauCeti.SporadicName.M11) := ⟨hLt.trans e⟩
  exact hloc.false_of_smallFacts (smallFacts_m11 h' (noInvCommNine_m11 h'))

theorem false_of_sl_binary (h35 : Lemma1435) (S : Setting146 G T M)
    (hred : IsRedCE T M H PQ p) (hshape : IsE9Z4Shape T H p) {L : Subgroup G}
    (hL : L ∈ cComp (mcOf T)) (hKc : conjClosure (oTwoUpper H) (mcOf T) = L) {n : ℕ}
    (hn : n = 4 ∨ n = 5)
    (e : Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2))) :
    False := by
  obtain ⟨Eh, hloc, ⟨hLt⟩⟩ := e9Local_of_inv h35 S hred hshape hL hKc
  obtain ⟨e⟩ := e
  rcases hn with rfl | rfl
  · exact hloc.false_of_binCrit (hLt.trans e) binCrit_sl4
  · exact hloc.false_of_binCrit (hLt.trans e) binCrit_sl5

end CFSG.Quasithin.E9P2L
