module

public import CFSG.Sporadic.Recognition.McLASThompson
public import Certificates.Certificate6105
public import Certificates.Certificate6106

public section

namespace CFSG.Sporadic.Recognition.McLAS

theorem threeFacts_cert' : ThreeFacts :=
  Certificates.certificate6105.2.2.1

theorem sylowThreeOK_eq_true' : sylowThreeOK = true :=
  Certificates.certificate6105.2.2.2.2.2

theorem threeLocalCheck_eq_true : threeLocalCheck = true := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := Certificates.certificate6106
  simp only [threeLocalCheck, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩

theorem mcl_threeLocal_of_certificate :
    ∃ (x : CFSG.Blueprint.NativeSporadic.McL) (R T A : Subgroup CFSG.Blueprint.NativeSporadic.McL),
      ThreeLocalAut CFSG.Blueprint.NativeSporadic.McL x R T A :=
  mcl_threeLocal threeFacts_cert' sylowThreeOK_eq_true' threeLocalCheck_eq_true

theorem mcl_thompson_of_certificate :
    ∃ (x : CFSG.Blueprint.NativeSporadic.McL) (R T A : Subgroup CFSG.Blueprint.NativeSporadic.McL),
      ThreeLocalAut CFSG.Blueprint.NativeSporadic.McL x R T A ∧
        CFSG.IsElementaryAbelian 3 ↥A ∧ Nat.card ↥A = 81 ∧ CFSG.thompsonSubgroup T = A :=
  mcl_thompson threeFacts_cert' sylowThreeOK_eq_true' threeLocalCheck_eq_true

end CFSG.Sporadic.Recognition.McLAS
