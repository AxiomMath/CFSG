module

public import CFSG.Quasithin.EmptyFaithful.S146zUAMain
public import CFSG.Quasithin.EmptyFaithful.S146zUD3Main
public import CFSG.Quasithin.EmptyFaithful.S146zUF4Main
public import CFSG.Quasithin.EmptyFaithful.S146zUG1Main

public section

namespace CFSG.Quasithin.S146zU

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped Pointwise commutatorElement

theorem input14615SetupFourR_proved
    (hA21 : AsA21SQTKSection) (h56 : AsB56) (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (hD36 : D36)
    (hD37 : D37) (hD321 : D321) (hI5 : Insp5a) (h36 : A36ForSQTK) (hlist : SQTKList3Dvd)
    (iS : Input14614NoSz) : SBc16.Input14615SetupFourR := by
  intro G _ _ T M S H PQ p hred hmax H₀ H₁ H₂ t hdec hctx K₁ s hK₁ hK₂ hsT hsN hKz hG e
  obtain ⟨rfl, -⟩ := hctx
  have hTG : T ≤ mcOf T := S.isHTM_mcOf.1.1
  have hn : mcOf T ≤ Subgroup.normalizer
      ((conjClosure (oTwoUpper H) (mcOf T) : Subgroup G) : Set G) := le_normalizer_conjClosure _ _
  have hK₀eq : conjClosure K₁ T = K₁ ⊔ conjSub s K₁ :=
    UB.conjClosure_eq_sup_conjSub hsT hKz (hTG.trans hn)
  have hK₀ : conjClosure K₁ T ⊔ T = mcOf T := UB.conjClosure_sup_eq hsT hKz hn hG
  obtain ⟨hF, I, hV₁I, hIU, W, hW, hirr, hcases⟩ :=
    UB.exists_f5_cases hA37 hA38 hD36 hD37 hD321 hI5 S hK₁ hsT hsN hK₀ e
  have hclaim := claim_of_setting hA21 h56 S hK₁ hK₂ hsT hsN hK₀ hK₀eq e hF hV₁I hIU W hW hirr
  have hD : ⁅⁅uOfL22 T M, K₁⁆, conjSub s K₁⁆ ≤ quasithinOmegaOneCenter T := by
    by_cases hc : UG1.F5CaseOne hF hIU
    · exact (UD3.caseI_false h36 hlist iS S hred hmax hdec hK₁ hsT hsN hKz e hF hIU hclaim hc).elim
    · exact UG1.hD_of_modSplit hK₂ hsT hsN e hF hIU hclaim
        (UG1.f5Split_of_not_caseOne hF hIU hsT hcases hc)
  exact closing_of_decomp S hred hdec hK₁ hK₂ hsT hsN hKz e hD

end CFSG.Quasithin.S146zU
