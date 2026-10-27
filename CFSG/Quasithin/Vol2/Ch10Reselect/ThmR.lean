module

public import CFSG.Quasithin.Vol2.Ch10Reselect.Lemma3
public import CFSG.Quasithin.Vol2.Ch10Reselect.Lemma6
public import CFSG.Quasithin.Vol2.Ch10Reselect.H2G
public import CFSG.Quasithin.Vol2.Ch10Reselect.ThmRB
public import CFSG.Quasithin.Vol2.Ch10Reselect.ThmRC
public import CFSG.Quasithin.Vol2.Ch10Reselect.AutSL2Proved
public import CFSG.Quasithin.Vol2.Ch10Reselect.ModelAlgLine

public section

namespace CFSG.Quasithin.Vol2.Ch10Reselect

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open CFSG.Quasithin.Vol2.Ch10 CFSG.Quasithin.Vol2.Ch10.SecA
open scoped IsMulCommutative commutatorElement

theorem ch10Reselect_of (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h322 : Ch10.TmpL6_3_2_2_two) : Ch10.Ch10Reselect := by
  intro G _ _ T L I hfsu hlt hcomm hA hiv
  obtain ⟨K, hF, hfin, hchar, hK4, ⟨M⟩⟩ := exists_uModel hfsu hiv
  have hL3 : ∀ k ∈ fsuM T L, (∀ l ∈ fsuL0 T L,
      ⁅k, l⁆ ∈ Subgroup.centralizer (fsuVM T L I : Set G)) →
      k ∈ Subgroup.centralizer (fsuVM T L I : Set G) :=
    fun k hk hk0 => lemma3 h37 h38 h322 hfsu hlt hA M hk hk0
  obtain ⟨w, hw0, hw⟩ := exists_fixed_line autSL2Exists hK4 (actML M) (actML_add M)
    (actML_hnorm M) (hH2_of autSL2Exists h37 h38 hfsu hlt hA hK4 hL3 M)
  haveI : Nontrivial K := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨t, ht, htn⟩ := Set.not_subset.mp (not_le_normalizer_of_lt hlt)
  have hJ := jData_of_line hfsu hlt hA M hw0 hw
  have hVR := fsuVM_le_reducedAggregate h37 h38 h322 hfsu hlt hL3
  have hirr := irrPlus_lineJ h37 h38 hfsu hlt hA M hw0 hw hVR
  have hJfsu : FSU G T L (M.lineJ w) :=
    ⟨hfsu.simple, hfsu.nonabelian, hfsu.qtke, hfsu.sylow, hfsu.maximal, hfsu.faithful,
      hfsu.quasisimple, hirr⟩
  refine ⟨M.lineJ w, hJfsu, hJ.le_fsuVM, hJ.fsuVM_eq h37 h38 ht htn, hJ.fsuUL_eq h37 h38 ht htn,
    ?_⟩
  intro x hx hcomm' hiv'
  exact false_of_caseIV_lineJ h37 h38 hfsu hlt hA hK4 M hw0 hw hJfsu hx hiv'

end CFSG.Quasithin.Vol2.Ch10Reselect
