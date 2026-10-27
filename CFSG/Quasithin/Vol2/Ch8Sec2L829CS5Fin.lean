module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829CS4Final
public import CFSG.Quasithin.Vol2.Ch8Sec2L829P7
public import CFSG.Quasithin.Vol2.Ch8Sec2L829CS5U34
public import CFSG.Quasithin.Vol2.Ch8Sec2L829CS5U3Br
public import CFSG.Quasithin.Vol2.Ch8Sec2L829CS5S7

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.E3 CFSG.Quasithin.H
  CFSG.Quasithin.ASInputs
open scoped IsMulCommutative commutatorElement

theorem rankOneU3_cs5 : RankOneU3 := fun _ _ _ _ _ _ hn hX hS =>
  rankOneSyl_of_isPSU_three_cs5 hn hX hS

theorem cocode829Sweep_of (hE22 : E2.E22StatementC) (hS825 : Stmt8_2_5)
    (hLU : HLU82) (hcard : Mathieu.StmtH13Card) (h827 : Step827) (h828 : Stmt8_2_8)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h3228 : Stmt3_2_2_eight) (h325 : Stmt3_2_5) (h331 : Stmt3_3_1) (hC58 : TheoremC58)
    (h317 : AS317Sylow) (h711n : Stmt7_1_1_normal)
    (h828c : Stmt8_2_8Cocode) (hC6 : C6Odd829) :
    Cocode829Sweep := by
  intro G _ _ T L I hyp h731 h821 hc hrow H h k hH hh hC hcoc
  obtain ⟨K, hKc, hHK, hq, hcase, n, hn2, hX⟩ := step2_reduced_829 hE22 hS825 hLU hcard h827 h828
    h37 h38 h39 h3228 h325 h331 hC58 h317 h711n hyp h731 h821 hrow hcoc hH hh hC
  have hP7 := stmt8_2_2P7_of h37 h38 h39 h3228 h325 h331 hC58 h317 h711n G T L I hyp h731 h821 hc
    hrow H h k hH hh hC
  have hC5 : Concl825 T L I h k := hS825 G T L I hyp h731 h821 hc hrow H h k hH hh hC
  have hC8 : Concl828 T L I h := h828 G T L I hyp h731 h821 hc hrow H h k hH hh hC
  have hk : k = 2 := k_eq_two_cocode_829 hC5 hcoc
  obtain ⟨hV, hN⟩ := stmtFSUModule_of_eight h3228 G T L I hyp.fsu
  have hT : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo hyp.fsu.sylow hH.1.1
  have hVT : fsuV T I ≤ T := fsuV_le_T hyp.fsu hV hN
  have hTM : T ≤ fsuM T L := le_normalizer_conjClosure L T
  obtain ⟨hTK, -, n', -, hBor⟩ := hcase
  obtain ⟨-, hhI, -, -, -, -, hMIeq, hker, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := id hC
  have hI60 := (concl822_cocode_829 hC hk).1
  rcases hX with hL2 | ⟨hU3, -⟩
  · left
    exact l2_branch_cs5 hT hTM hHK hTK hVT hV hP7 hh hker hI60 hn2 hL2 hBor
  · right
    obtain ⟨x, hxA, hx5, hx1, hxI⟩ :=
      u3_branch_cs5 rankOneU3_cs5 u34Facts_cs5 hT hTM hHK hTK hVT hV hP7 hh hker hI60 hn2 hU3 hBor
    obtain ⟨-, -, -, -, -, -, -, hTU, -, -, -, -, hIU⟩ := hC5
    obtain ⟨-, h828two, -, -, -⟩ := hC8
    have hHIT : H = ch82I (fsuV T I) h ⊔ T := H_eq_ch82I_sup_T_829 (stmtFSUModule_of_eight h3228)
      hyp hH hC
    obtain ⟨hPP, hOP, hGL⟩ := h828c G T L I hyp h731 h821 hc hrow H h k hH hh hC hcoc _ _ _ rfl rfl
      rfl
    have hxcI := step7_core_cs5 hT.2.1 hV hP7 hh hhI hker hMIeq hHIT hIU hTU h828two hPP hOP hGL
      hxA.1.1 hxA.1.2 hx5 hxI
    have hVI : fsuV T I ≤ ch82I (fsuV T I) h := le_sup_left
    have hxV : ∀ v ∈ fsuV T I, x * v = v * x := fun v hv => hxcI v (hVI hv)
    have hxo : Odd (orderOf x) := by
      obtain ⟨a, ha⟩ := hx5
      exact Odd.of_dvd_nat (Odd.pow (by decide)) (orderOf_dvd_of_pow_eq_one ha)
    refine ⟨Subgroup.zpowers x, ?_, ?_, ?_⟩
    · intro hb
      exact hx1 (Subgroup.zpowers_eq_bot.mp hb)
    · refine Subgroup.zpowers_le.mpr ?_
      rw [Subgroup.mem_centralizer_iff]
      intro i hi
      exact (hxcI i hi).symm
    · refine hC6 G T L I hyp h731 h821 hc hrow hcoc (Subgroup.zpowers x)
        (Subgroup.zpowers_le.mpr hxA.1.2) ?_ inferInstance ?_ ?_
      · intro hb
        exact hx1 (Subgroup.zpowers_eq_bot.mp hb)
      · rw [Nat.card_zpowers]
        exact hxo
      · refine Subgroup.zpowers_le.mpr ?_
        rw [Subgroup.mem_centralizer_iff]
        intro v hv
        exact (hxV v hv).symm

theorem step829Cocode_holds (hE22 : E2.E22StatementC) (hS825 : Stmt8_2_5)
    (hLU : HLU82) (hcard : Mathieu.StmtH13Card) (h827 : Step827) (h828 : Stmt8_2_8)
    (hmod : StmtFSUModule) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h3228 : Stmt3_2_2_eight) (h325 : Stmt3_2_5) (h331 : Stmt3_3_1) (hC58 : TheoremC58)
    (h317 : AS317Sylow) (h711n : Stmt7_1_1_normal)
    (h828c : Stmt8_2_8Cocode) (hC6 : C6Odd829) :
    Step829Cocode :=
  step829Cocode_of' hmod h37 h38 h39 h3228 h325 h331 hC58 h317 h711n
    (cocode829Sweep_of hE22 hS825 hLU hcard h827 h828 h37 h38 h39 h3228 h325 h331 hC58 h317 h711n
      h828c hC6)

end CFSG.Quasithin.H13
