module

public import CFSG.Quasithin.Recognition.M12AmalAutClass
public import Certificates.Certificate17039

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.M12AmalAut
open CFSG.ComponentClassification.M12Cover CFSG.Sporadic.Schreier

theorem bA_eq_m12A1 : bA = m12A1 :=
  Certificates.certificate17039.1

theorem bB_eq_m12B1 : bB = m12B1 :=
  Certificates.certificate17039.2.1

theorem bS_eq_m12Sigma : bS = m12Sigma :=
  Certificates.certificate17039.2.2

theorem autM12Model_eq_autModel :
    autM12Model = autModel := by
  rw [autModel_eq_closure]
  unfold autM12Model
  rw [bA_eq_m12A1, bB_eq_m12B1, bS_eq_m12Sigma]

theorem autM12PermModel
    : AutM12PermModel :=
  ⟨(MulEquiv.subgroupCongr autM12Model_eq_autModel).trans autModelEquiv⟩

theorem autM12_f6YBridge'
    (D : Type) [Group D] [Finite D] (H₁ H₂ : Subgroup D)
    (h : F6.IsYAmalgam F6.IsAutM12 H₁ H₂) :
    IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups H₁ H₂)
      (fun Y _ => Nonempty (Y ≃* MulAut quasithinM12)) :=
  autM12_f6YBridge autM12PermModel D H₁ H₂ h

end CFSG.Quasithin
