module

public import CFSG.Sporadic.Recognition.McLASInvolutions
public import CFSG.Sporadic.Recognition.McLASThreeCentral
public import Certificates.Certificate6105

public section

namespace CFSG.Sporadic.Recognition.McLAS

open Subgroup CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative CFSG.Blueprint
  CFSG.ComponentClassification.OuterAutomorphisms

theorem m11Check_eq_true : m11Check = true :=
  Certificates.certificate6105.1

theorem invProdCheck_eq_true : invProdCheck = true :=
  Certificates.certificate6105.2.1

theorem threeFacts_cert : ThreeFacts :=
  Certificates.certificate6105.2.2.1

theorem fiveOuterCheck_eq_true : fiveOuterCheck = true :=
  Certificates.certificate6105.2.2.2.1

theorem fivePowerCheck_eq_true : fivePowerCheck = true :=
  Certificates.certificate6105.2.2.2.2.1

theorem sylowThreeOK_eq_true : sylowThreeOK = true :=
  Certificates.certificate6105.2.2.2.2.2

theorem mcl_outer_involutions_of_certificate :
    (∃ σ : MulAut NativeSporadic.McL, orderOf σ = 2 ∧ σ ∉ inner NativeSporadic.McL) ∧
    (∀ σ τ : MulAut NativeSporadic.McL, orderOf σ = 2 → σ ∉ inner NativeSporadic.McL →
      orderOf τ = 2 → τ ∉ inner NativeSporadic.McL →
        ∃ g : NativeSporadic.McL, mclConj g * σ * (mclConj g)⁻¹ = τ) ∧
    (∀ σ : MulAut NativeSporadic.McL, orderOf σ = 2 → σ ∉ inner NativeSporadic.McL →
      Nonempty (↥(mclFixed σ) ≃* ↥NativeSporadic.M11)) :=
  mcl_outer_involutions m11Check_eq_true

theorem mcl_inverted_odd_order_of_certificate
    {x t : NativeSporadic.McL}
    (ht : orderOf t = 2) (hinv : t * x * t⁻¹ = x⁻¹) (hodd : Odd (orderOf x)) :
    x = 1 ∨ orderOf x = 3 ∨ orderOf x = 5 :=
  mcl_inverted_odd_order invProdCheck_eq_true ht hinv hodd

theorem mcl_two_classes_order_three_of_certificate :
    ∃ x₁ x₂ : NativeSporadic.McL, orderOf x₁ = 3 ∧ orderOf x₂ = 3 ∧
      Nat.card ↥(centralizer ({x₁} : Set NativeSporadic.McL)) = 29160 ∧
      Nat.card ↥(centralizer ({x₂} : Set NativeSporadic.McL)) = 972 ∧
      ¬ IsConj x₁ x₂ ∧
      ∀ y : NativeSporadic.McL, orderOf y = 3 → IsConj y x₁ ∨ IsConj y x₂ :=
  mcl_two_classes_order_three threeFacts_cert

theorem mcl_two_classes_order_five_of_certificate :
    ∃ x₁ x₂ : NativeSporadic.McL, orderOf x₁ = 5 ∧ orderOf x₂ = 5 ∧
      Nat.card ↥(centralizer ({x₁} : Set NativeSporadic.McL)) = 750 ∧
      Nat.card ↥(centralizer ({x₂} : Set NativeSporadic.McL)) = 25 ∧
      ¬ IsConj x₁ x₂ ∧
      ∀ y : NativeSporadic.McL, orderOf y = 5 → IsConj y x₁ ∨ IsConj y x₂ :=
  mcl_two_classes_order_five fiveOuterCheck_eq_true

theorem mcl_two_classes_subgroups_order_five_of_certificate :
    ∃ X X₂ : Subgroup NativeSporadic.McL, TwoClassesSubgroups NativeSporadic.McL 5 750 25 X X₂ :=
  mcl_two_classes_subgroups_order_five fiveOuterCheck_eq_true fivePowerCheck_eq_true

theorem mcl_threeCentral_transitive_of_certificate :
    (∃ H : Subgroup NativeSporadic.McL, IsPCentralSubgroup 3 H) ∧
    ∀ H K : Subgroup NativeSporadic.McL, IsPCentralSubgroup 3 H → IsPCentralSubgroup 3 K →
      ∃ g : NativeSporadic.McL,
        H.map (@MulAut.conj NativeSporadic.McL inferInstance g).toMonoidHom = K :=
  mcl_threeCentral_transitive sylowThreeOK_eq_true

end CFSG.Sporadic.Recognition.McLAS
