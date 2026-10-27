module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelConcl
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelE6Kernel
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelQ8Kernel
public import CFSG.LocalAnalysis.StandardType.GGTableBThreeTBE6
public import CFSG.LocalAnalysis.StandardType.GGTableBThreeTBTwE6
public import CFSG.LocalAnalysis.StandardType.GGTableBThreeTBTwE6Q8
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6TwoThreeAct

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem odd_of_dvd_three {k : ℕ} (h : k ∣ 3) : Odd k := by
  rcases (Nat.dvd_prime Nat.prime_three).mp h with rfl | rfl
  · exact odd_one
  · exact ⟨1, rfl⟩

section NoCerts

theorem ggE6DivModuleInput_of_model (hM : GGE6ThreeModelInput) : GGE6DivModuleInput :=
  fun K _ _ n hn hK h3 => ggTableBModuleSCr_of_model (hM.1 K n hn hK h3)

theorem ggTwE6ThreeModuleInput_of_model (hM : GGE6ThreeModelInput) : GGTwE6ThreeModuleInput :=
  fun K _ _ n hn hK h3 => ggTableBModuleSCr_of_model (hM.2 K n hn hK h3)

theorem ggTwE6TwoThreeActionOddInput_of_model (hM : GGE6ThreeModelInput) :
    GGTwE6TwoThreeActionOddInput :=
  fun K _ _ hK L₁ _ _ ψ₁ hψ hker hperf hodd A₁ hA hAI hr hsc => by
    obtain ⟨Φ, T, w, hd⟩ := (hM.2 K 1 le_rfl hK (by norm_num) L₁ ψ₁ hψ hker hperf A₁ hA hAI hr
      hsc).exists_data
    exact hd.actConcl hodd

end NoCerts

section Certs113


theorem ggE6DivTorusNbrInput_of_model (hM : GGE6ThreeModelInput) : GGE6DivTorusNbrInput :=
  fun K _ _ n hn hK h3 => ggTorusNbrSCrK_of_model (hM.1 K n hn hK h3)

theorem ggE6DivTvInput_of_model (hM : GGE6ThreeModelInput) : GGE6DivTvInput :=
  fun K _ _ n hn hK h3 => ggNoTransvectionSCr_of_model (hM.1 K n hn hK h3)

theorem ggTwE6ThreeTorusNbrInput_of_model (hM : GGE6ThreeModelInput) :
    GGTwE6ThreeTorusNbrInput :=
  fun K _ _ n hn hK h3 => ggTorusNbrSCrK_of_model (hM.2 K n hn hK h3)

theorem ggTwE6ThreeTvInput_of_model (hM : GGE6ThreeModelInput) : GGTwE6ThreeTvInput :=
  fun K _ _ n hn hK h3 => ggNoTransvectionSCr_of_model (hM.2 K n hn hK h3)

end Certs113

section CertsE


theorem ggE6DivActionInput_of_model (hM : GGE6ThreeModelInput) : GGE6DivActionInput :=
  fun K _ _ n hn hK h3 => ggTableBActionSCr_of_model (hM.1 K n hn hK h3)
    fun _ _ _ _ hψ hker hperf =>
      odd_of_dvd_three (TableBExc.E6Three.card_ker_dvd_three_e6 hn hK hψ hker hperf)

end CertsE

section CertsT


theorem ggTwE6ThreeActionInputQ8_of_model (hM : GGE6ThreeModelInput) :
    GGTwE6ThreeActionInputQ8 :=
  fun K _ _ n hn hK h3 => ggTableBActionSCr_of_model (hM.2 K n (by omega) hK h3)
    fun _ _ _ _ hψ hker hperf =>
      odd_of_dvd_three (TwE6Delta.card_ker_dvd_three_q8 hn hK hψ hker hperf)

theorem ggYS203Inputs_of_model (hM : GGE6ThreeModelInput) :
    GGE6DivTorusNbrInput ∧ GGE6DivModuleInput ∧ GGE6DivActionInput ∧ GGE6DivTvInput ∧
      GGTwE6ThreeTorusNbrInput ∧ GGTwE6ThreeModuleInput ∧ GGTwE6ThreeTvInput ∧
      GGTwE6ThreeActionInputQ8 ∧ GGTwE6TwoThreeActionOddInput :=
  ⟨ggE6DivTorusNbrInput_of_model hM, ggE6DivModuleInput_of_model hM,
    ggE6DivActionInput_of_model hM, ggE6DivTvInput_of_model hM,
    ggTwE6ThreeTorusNbrInput_of_model hM, ggTwE6ThreeModuleInput_of_model hM,
    ggTwE6ThreeTvInput_of_model hM, ggTwE6ThreeActionInputQ8_of_model hM,
    ggTwE6TwoThreeActionOddInput_of_model hM⟩

end CertsT

end CFSG.StandardType
