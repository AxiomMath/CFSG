module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qModel
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qModelHex
public import CFSG.Quasithin.Vol2.GoldschmidtF431BNFacts

public section

namespace CFSG.Quasithin.H13.F431.D4q.Hex

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg CFSG.LieType.Steinberg.TwistedD4
  CFSG.GH74.GLS.Stage4.Hex CFSG.Quasithin.H13.F431


theorem f431Facts45_d4 (f : ℕ) (hm : F431ModelFacts .trialityD4 0 f) :
    F431Facts45 .trialityD4 0 f hm := by
  intro D _ hD A
  obtain ⟨hf, K, hF, hFin, σ, hK, hσ, ⟨e⟩⟩ := d4q_model_data hD
  have hq : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨eC⟩ := exists_d4Model_equiv σ hf hK hσ
  have := isSimpleGroup_d4Model σ.toRingHom hq hK hσ
  exact BN.facts45L_of_rankTwo (d4ModelSystem σ.toRingHom hq hK hσ)
    (d4ModelSystem_isSylow σ hf hK hσ hq) (hm D hD).1 (by norm_num) (eC.trans e.symm) A

end CFSG.Quasithin.H13.F431.D4q.Hex
