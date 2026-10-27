module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Perm
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallPSp43Model
public import CFSG.Quasithin.Recognition.CertOvergroup
public import Certificates.Data.U42F431Check

public section

namespace CFSG.Quasithin.H13.F431.U42

open CFSG.Quasithin U42F431

theorem x45_eq : x45 = CFSG.ComponentClassification.CatFactsSmall.PSp43.x45 := by
  ext j
  have h : ∀ j : Fin 45, (CFSG.ComponentClassification.CatFactsSmall.PSp43.tauFun 0 j).val =
      xL.getD j 0 := by decide +kernel
  exact (h j).symm

theorem y45_eq : y45 = CFSG.ComponentClassification.CatFactsSmall.PSp43.y45 := by
  ext j
  have h : ∀ j : Fin 45, (CFSG.ComponentClassification.CatFactsSmall.PSp43.y45 j).val =
      yL.getD j 0 := by decide +kernel
  exact (h j).symm

theorem Xs_eq : Xs = CFSG.ComponentClassification.CatFactsSmall.PSp43.QP45.originalSubgroup := by
  rw [CFSG.ComponentClassification.CatFactsSmall.PSp43.QP45_closure, Xs, x45_eq, y45_eq]

theorem card_Xs : Nat.card Xs = 25920 := by
  rw [Xs_eq, ← CFSG.Certificates.RawSchreierDatum.orderCertificate_eq_card _
    CFSG.ComponentClassification.CatFactsSmall.PSp43.QP45_ok]
  exact CFSG.ComponentClassification.CatFactsSmall.PSp43.QP45_valid.2

end CFSG.Quasithin.H13.F431.U42
