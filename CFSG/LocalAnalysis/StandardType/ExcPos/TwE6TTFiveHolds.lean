module

public import CFSG.LocalAnalysis.StandardType.ExcPos.TwE6TTUnits
import CFSG.LocalAnalysis.StandardType.ExcPos.TwE6TTBridge
import CFSG.LocalAnalysis.StandardType.ExcPos.TwE6TTFiveToral
import CFSG.LocalAnalysis.StandardType.GGTwE6LemmaKFive

public section

namespace CFSG.StandardType.LieKnownR2.ExcPos

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.StandardType.GGFinModel
  CFSG.Open

theorem twE6TTFive_holds :
    TwE6TTFive := by
  intro f hf h5 E hE hel hcard
  have hfin : Finite E := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have htor := isToralE6_of_le_ggFixGp_five hE hel hfin
  let K := GaloisField 2 (2 * f)
  letI : Algebra K GGL := (ggRatEmb (2 * f)).toAlgebra
  haveI : Fact (Nat.Prime 2) := Nat.fact_prime_two
  haveI : IsScalarTower (ZMod 2) K GGL :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_zmod _ _)
  haveI : IsAlgClosure K GGL :=
    { isAlgClosed := inferInstance
      isAlgebraic := Algebra.IsAlgebraic.tower_top (K := ZMod 2) (L := K) }
  obtain ⟨g, hg, hgn, hgt⟩ :=
    TwE6LemmaK.ggTwE6FiveToralTypeMinusOne (X := E) hf h5 GGL (ggFrobT f)
      (ggFrobT_apply f) (fun x hx => hE hx) hel hfin htor
  exact twE6LawPos_of_lang (p := 5) (f := f) (E := E) (by norm_num) h5 hE hg hgn hgt

end CFSG.StandardType.LieKnownR2.ExcPos
