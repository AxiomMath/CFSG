module

public import CFSG.Quasithin.Vol2.Ch7Lem755
public import CFSG.Quasithin.Vol2.Ch7E61
public import CFSG.Quasithin.Vol2.Ch3T326H2
public import CFSG.Quasithin.Vol2.Ch1A3Proved
public import CFSG.Quasithin.Vol2.Ch3Sec2Lem322Eight
public import CFSG.Quasithin.Background.ONanE68Holds
public import CFSG.Quasithin.H13.NQCatE68Borel

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3

theorem input7_5_5_of_stmt3_2
    (h325 : Stmt3_2_5) (h326 : Stmt3_2_6C) : Input7_5_5 := by
  intro G _ _ T L I hyp hV U hU hmax₁ hn
  have h37 := a37ForSQTK_proved
  have h38 := a38ForSQTK_proved
  have h39 := a39ForSQTK_proved
  have h3228 : Stmt3_2_2_eight := stmt3_2_2_eight_proved
  have hmod : StmtFSUModule := stmtFSUModule_of_eight h3228
  have hTI : IsTISetUnder (fsuV T I) (fsuM T L) := by
    rcases eq_or_lt_of_le (le_fsuL0 T L) with hL0 | hL0
    · exact isTISetUnder_of_stmt3_2_5 h325 hyp.fsu hL0
    · rcases stmt3_2_6Lt_of_C h326 G T L I hyp.fsu hL0 with ⟨-, -, hVM, -⟩ | h3
      · intro g hg hgn
        exfalso
        apply hgn
        rw [hVM]
        exact le_normalizer_conjClosure _ _ hg
      · exact absurd ⟨hL0, h3⟩ hyp.notThree
  have hE := hypE61_of_ti h37 h38 h39 hmod h3228 hyp hTI
  have hmax : ∀ W : Subgroup G, U < W → W ≤ fsuV T I →
      Subgroup.centralizer (W : Set G) ≤ fsuM T L := by
    intro W hW hWV
    by_contra hCW
    exact (ne_of_lt hW) (hmax₁ W hW.le hWV hCW).symm
  obtain ⟨L', X, hLC, -, -, -, hXLM, hcyc, hcard, -⟩ :=
    E6.e611Strong_of E6.E68Proof.e68Stmt_holds VolI.asc129Statement_holds
      NQCat.e68BorelKernel_holds G T (fsuM T L) (fsuV T I) U hV hE hU hmax hn
  obtain ⟨y, hy⟩ := hcyc.exists_generator
  have hXC : X ≤ fsuM T L ⊓ Subgroup.centralizer (U : Set G) :=
    le_inf (hXLM.trans inf_le_right) (hXLM.trans (inf_le_left.trans hLC))
  refine ⟨(y : MulAut (IntMod (fsuV T I) hV)), autI_mono hV hXC y.2, ?_⟩
  rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hy, hcard]

end CFSG.Quasithin.H13
