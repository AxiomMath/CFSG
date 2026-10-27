module

public import CFSG.Quasithin.Vol2.GoldschmidtF431G2F48Torus
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qF48Gen

public section

namespace CFSG.Quasithin.H13.F431.G2.F48

open CFSG.GH74.BNPair CFSG.GH74.GLS.Stage4.Hex CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.QuasithinUnique
  CFSG.Quasithin.H13.F431 CFSG.Quasithin.H13.F431.BN CFSG.Quasithin.H13.F431.F45
  CFSG.Quasithin.H13.F431.D4q.F48


set_option linter.unusedSectionVars false

variable {F : Type} [Field F] [Finite F] (hF : 3 ≤ Nat.card F)
  (hU : IsSylowTwoOf (g2ModelSystem F hF).U ⊤) {D : Type} [Group D] (hfin : Finite D)
  (A : LieAmalgamExt D)

include hU

theorem cartanFPF_g2Model (h4 : 4 ≤ Nat.card F)
    {Φ : AdjointQuotient Tag.G2 F →* (A.setting hfin 6 (by norm_num)).ι.G0}
    (XD : XDatum (A.setting hfin 6 (by norm_num)) Φ (Γ (g2ModelSystem F hF))
      (v (g2ModelSystem F hF) true) (v (g2ModelSystem F hF) false)) :
    (A.setting hfin 6 (by norm_num)).CartanFPF := by
  obtain ⟨u, hu, hu2⟩ := exists_unit_sq_ne_one h4
  exact cartanFPF_of_rankTwo_radical (g2ModelSystem F hF) hU hfin (by norm_num) A true XD
    (torG2_mem_cartan hF u) fun y hy hc => g2Model_fix_Q hF hU u hu hu2 hy hc

theorem faithfulOnType_g2Model [IsSimpleGroup (AdjointQuotient Tag.G2 F)]
    {Φ : AdjointQuotient Tag.G2 F →* (A.setting hfin 6 (by norm_num)).ι.G0} (b : Bool)
    (XD : XDatum (A.setting hfin 6 (by norm_num)) Φ (Γ (g2ModelSystem F hF))
      (v (g2ModelSystem F hF) b) (v (g2ModelSystem F hF) (!b)))
    (hcent : ∀ k : (A.setting hfin 6 (by norm_num)).ι.G0, (∀ y, k * Φ y = Φ y * k) → k = 1)
    (s : Bool) : (A.setting hfin 6 (by norm_num)).FaithfulOnType s :=
  faithfulOnType_of_rankTwo (g2ModelSystem F hF) hU hfin (by norm_num) A b XD hcent s

end CFSG.Quasithin.H13.F431.G2.F48
