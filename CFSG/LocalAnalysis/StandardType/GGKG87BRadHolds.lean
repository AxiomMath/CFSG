module

public import CFSG.LocalAnalysis.StandardType.GGKG87BRadInner
public import CFSG.LocalAnalysis.StandardType.GGKG87BRad
public import Certificates.Certificate1952
public import Certificates.Certificate3951
public import Certificates.Certificate8064
public import Certificates.Certificate13659
public import Certificates.Certificate13660
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangTwisted
import CFSG.LocalAnalysis.StandardType.GGTableBOutdiag

public section

namespace CFSG.StandardType.KG87B

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

theorem ggNbrKGFieldTwE6ThreeAddHeisRad_holds :
    GGNbrKGFieldTwE6ThreeAddHeisRad := by
  intro lab hlab ht h3
  have hF : LargeEvenLabelAll lab (GGRawFieldConj 3) :=
    ggRawFieldConjInputExc_holds 3 Nat.prime_three (by norm_num) lab hlab (by simp [ht])
  have hR : LargeEvenLabelAll lab fun R _ I F => GGRawFieldConj 3 R I F → IsSimpleGroup R →
      (∃ a b : R, a * b ≠ b * a) → GGHeisFieldCompRad 3 5 R I F := by
    obtain ⟨t, l, n⟩ := lab
    obtain ⟨hn, -⟩ := hlab
    dsimp only at ht h3
    subst ht
    intro Q hQ
    refine recipeTwisted_and (P := fun R _ I F => GGRawFieldConj 3 R I F → IsSimpleGroup R →
      (∃ a b : R, a * b ≠ b * a) → GGHeisFieldCompRad 3 5 R I F)
      (fun K _ _ hK hc hs hna => ?_) hQ
    have : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, ← pow_mul])
    obtain ⟨σ, hσ⟩ : ∃ σ : K ≃+* K, ∀ c, σ c = c ^ 2 ^ n :=
      ⟨iterateFrobeniusEquiv K 2 n, fun c => by
        rw [iterateFrobeniusEquiv_apply, iterateFrobenius_def]⟩
    have hK3 : ringChar K ≠ 3 := by
      rw [ringChar.eq K 2]
      norm_num
    exact ggHeisFieldCompRad_recipe_of_lineLang hn h3 hK σ hσ (fun h hh1 hh3 =>
      d4t2pl_nonempty_lineLangIota K σ (2 ^ n) hK3 hσ hK
        (le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hn)) h hh1 hh3) hc hs hna
  intro Q hQ
  exact largeEvenRawDatum_mono (fun _ _ _ _ h' => ⟨h'.1.1, h'.2 h'.1.2⟩) (hR _ (hF Q hQ))

end CFSG.StandardType.KG87B

namespace CFSG.StandardType

theorem ggNbrKGFieldTwE6ThreeAddHeis_holds :
    GGNbrKGFieldTwE6ThreeAddHeis :=
  ggNbrKGFieldTwE6ThreeAddHeis_of_rad KG87B.ggNbrKGFieldTwE6ThreeAddHeisRad_holds

end CFSG.StandardType
