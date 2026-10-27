module

public import CFSG.Quasithin.Recognition.St84.Gen.BigL2Slice
import CFSG.Quasithin.Recognition.F112RShapes
import CFSG.Quasithin.Recognition.St84.Gen.U4qBlock
import CFSG.Quasithin.Recognition.St84.Gen.U4qConcl
import CFSG.Quasithin.Recognition.St84.Gen.U4qExt
import CFSG.Quasithin.Recognition.St84.Gen.U4qIdent
import CFSG.Quasithin.Recognition.St84.Gen.U4qRadical

public section

namespace CFSG.Quasithin.F112R

theorem y9U4q : Y9U4q := by
  intro G _ _ L1 L2 S f hF hf h1 h2 hA
  obtain ⟨hB, ho1, ho2, K, _, h, hd⟩ := hA.elim (u4q_ident_psu hf) (u4q_ident_ext hF hf)
  rcases hd with ⟨⟨e1⟩, ⟨e2⟩⟩ | he
  · have hsp := IsSpecialPow.of_mulEquiv e1.symm (isSpecialPow_radQ h)
    obtain ⟨hz, hb, ho⟩ := y9U4q_concl hF hf h1 h2 hB ho1 ho2 hsp
      (isShort2_perfectCore_parP2 h) (isOmega4MinusType_perfectCore_parP2 h) e2
    exact ⟨hz, hsp, hb, ho, fun hA' => perfectOver_u4q hF.1 hf h1 h2 hA'⟩
  · exact absurd he (not_nonempty_perfectCore_sup_mulEquiv_parP
      (bigB_le_normalizer hF.1).2 hB hf h2 ho2 h)

end CFSG.Quasithin.F112R
