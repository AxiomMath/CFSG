module

public import CFSG.Quasithin.H13.A5S1328Sym4
public import CFSG.Quasithin.Recognition.GoldschmidtF112A5
public import CFSG.Quasithin.Vol2.Ch9Sec3LSide

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

private theorem vA5_of_quasithinO2QuotientIso_alt_five {G : Type}
    [Group G] {L : Subgroup G} (h : quasithinO2QuotientIso L (alternatingGroup (Fin 5))) :
    CFSG.Quasithin.F112R.VA5 L := by
  obtain ⟨φ, hφ, hker⟩ := h
  have e : ↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.quotientMulEquivOfEq ((CFSG.pCore_eq_open ↥L 2).trans hker.symm)).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφ)
  exact CFSG.Quasithin.H13.Ch9.isL2Quot_two_of_alt_five ⟨e⟩

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem f112_of_borels_corrected_A5
    (hA5 : CFSG.Quasithin.F112R.F112SliceA5) {H K VH : Subgroup G}
    (S' : Setting G T K VH) (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H)
    (hHK : H = K ⊔ T) (h : Hyp111R L K T) :
    ∃ L1' L2' : Subgroup G, ((L1' = L ∧ L2' = K) ∨ (L1' = K ∧ L2' = L)) ∧
      F112ListC L1' L2' (Sp L K T) := by
  have hhyp := S.hyp111_Sp S' hH hHK h
  have hnorm : ((Sp L K T).subgroupOf (Sp L K T ⊔ borelOf L (Sp L K T))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left, S.borelOf_Sp_left h]
    exact sup_le Subgroup.le_normalizer
      ((le_sup_left.trans le_sup_left : borelOf L T ≤ bigB L K T).trans
        (le_normalizer_pCoreOf 2 _))
  obtain ⟨L1', L2', hsw, -, hlist, -⟩ :=
    hA5 G L K (Sp L K T) ⟨hhyp, S.isQuasithinSub _, Or.inl hnorm⟩
      (Or.inl ⟨vA5_of_quasithinO2QuotientIso_alt_five S.a5,
        vA5_of_quasithinO2QuotientIso_alt_five S'.a5⟩)
  exact ⟨L1', L2', hsw, hlist⟩

end Setting

end CFSG.Quasithin.H13.A5

end
