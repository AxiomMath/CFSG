module

public import CFSG.GH74.E2.OuterRankInputs

public section

open CFSG
open CFSG.GH74
open CFSG.GH74.E2
open CFSG.GH74.E2.OuterRank
open CFSG.Semidihedral
attribute [local instance] CFSG.GH74.E2.OuterRank.instDecEqSD

public section

open CFSG
open CFSG.GH74
open CFSG.GH74.E2
open CFSG.GH74.E2.OuterRank
open CFSG.Semidihedral
attribute [local instance] CFSG.GH74.E2.OuterRank.instDecEqSD

namespace CertificateChecks.Batch5016

open CFSG
open CFSG.GH74
open CFSG.GH74.E2
open CFSG.GH74.E2.OuterRank
open CFSG.Semidihedral

private theorem chi_surj_0 : ∀ v w : Multiplicative (ZMod 2), ∃ m : SD,
    Multiplicative.ofAdd (ZMod.castHom (by decide : 2 ∣ modulus 4) (ZMod 2) (Multiplicative.toAdd m.left)) = v ∧ m.right = w := by
  decide +kernel

private theorem nf_spec_1 : ∀ a : SD, R0 ^ (nf a).1 * S0 ^ (nf a).2 = a := by
  decide +kernel

private theorem rel_2 : R0 ^ 8 = 1 ∧ R0 ^ 4 ≠ 1 ∧ S0 * S0 = 1 ∧ S0 ≠ 1 ∧ S0 * R0 * S0⁻¹ = R0 ^ 3 := by
  decide +kernel

private theorem imgs_chi_3 : ∀ a b : SD, Rel5 a b →
    (Multiplicative.ofAdd (ZMod.castHom (by decide : 2 ∣ modulus 4) (ZMod 2) (Multiplicative.toAdd a.left)) = Multiplicative.ofAdd (ZMod.castHom (by decide : 2 ∣ modulus 4) (ZMod 2) (Multiplicative.toAdd R0.left)) ∧ a.right = R0.right ∧
      Multiplicative.ofAdd (ZMod.castHom (by decide : 2 ∣ modulus 4) (ZMod 2) (Multiplicative.toAdd b.left)) = Multiplicative.ofAdd (ZMod.castHom (by decide : 2 ∣ modulus 4) (ZMod 2) (Multiplicative.toAdd S0.left)) ∧ b.right = S0.right) := by
  decide +kernel

private theorem fix_w_4 : ∀ a b w : SD, Rel5 a b → Hyp3 a b w →
    (Multiplicative.ofAdd (ZMod.castHom (by decide : 2 ∣ modulus 4) (ZMod 2) (Multiplicative.toAdd w.left)) = 1 ∧ w.right = 1) := by
  decide +kernel

private theorem chiL_map_one_check_5 : Multiplicative.ofAdd (ZMod.castHom (by decide : 2 ∣ modulus 4) (ZMod 2) (Multiplicative.toAdd (1 : SD).left)) = 1 := by
  decide +kernel

private theorem chiL_map_mul_check_6 : ∀ x y : SD,
    Multiplicative.ofAdd (ZMod.castHom (by decide : 2 ∣ modulus 4) (ZMod 2) (Multiplicative.toAdd (x * y).left)) =
      Multiplicative.ofAdd (ZMod.castHom (by decide : 2 ∣ modulus 4) (ZMod 2) (Multiplicative.toAdd x.left)) * Multiplicative.ofAdd (ZMod.castHom (by decide : 2 ∣ modulus 4) (ZMod 2) (Multiplicative.toAdd y.left)) := by
  decide +kernel

private theorem chiR_map_mul_check_7 : ∀ x y : SD, (x * y).right = x.right * y.right := by
  decide +kernel

end CertificateChecks.Batch5016

namespace Certificates

open CertificateChecks

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.E2 in
open CFSG.GH74.E2.OuterRank in
open CFSG.Semidihedral in
theorem certificate5016 : (∀ v w : Multiplicative (ZMod 2), ∃ m : SD,
    Multiplicative.ofAdd (ZMod.castHom (by decide : 2 ∣ modulus 4) (ZMod 2) (Multiplicative.toAdd m.left)) = v ∧ m.right = w)
    ∧ (∀ a : SD, R0 ^ (nf a).1 * S0 ^ (nf a).2 = a)
    ∧ (R0 ^ 8 = 1 ∧ R0 ^ 4 ≠ 1 ∧ S0 * S0 = 1 ∧ S0 ≠ 1 ∧ S0 * R0 * S0⁻¹ = R0 ^ 3)
    ∧ (∀ a b : SD, Rel5 a b →
    (Multiplicative.ofAdd (ZMod.castHom (by decide : 2 ∣ modulus 4) (ZMod 2) (Multiplicative.toAdd a.left)) = Multiplicative.ofAdd (ZMod.castHom (by decide : 2 ∣ modulus 4) (ZMod 2) (Multiplicative.toAdd R0.left)) ∧ a.right = R0.right ∧
      Multiplicative.ofAdd (ZMod.castHom (by decide : 2 ∣ modulus 4) (ZMod 2) (Multiplicative.toAdd b.left)) = Multiplicative.ofAdd (ZMod.castHom (by decide : 2 ∣ modulus 4) (ZMod 2) (Multiplicative.toAdd S0.left)) ∧ b.right = S0.right))
    ∧ (∀ a b w : SD, Rel5 a b → Hyp3 a b w →
    (Multiplicative.ofAdd (ZMod.castHom (by decide : 2 ∣ modulus 4) (ZMod 2) (Multiplicative.toAdd w.left)) = 1 ∧ w.right = 1))
    ∧ (Multiplicative.ofAdd (ZMod.castHom (by decide : 2 ∣ modulus 4) (ZMod 2) (Multiplicative.toAdd (1 : SD).left)) = 1)
    ∧ (∀ x y : SD,
    Multiplicative.ofAdd (ZMod.castHom (by decide : 2 ∣ modulus 4) (ZMod 2) (Multiplicative.toAdd (x * y).left)) =
      Multiplicative.ofAdd (ZMod.castHom (by decide : 2 ∣ modulus 4) (ZMod 2) (Multiplicative.toAdd x.left)) * Multiplicative.ofAdd (ZMod.castHom (by decide : 2 ∣ modulus 4) (ZMod 2) (Multiplicative.toAdd y.left)))
    ∧ (∀ x y : SD, (x * y).right = x.right * y.right) := by
  exact ⟨CertificateChecks.Batch5016.chi_surj_0, CertificateChecks.Batch5016.nf_spec_1, CertificateChecks.Batch5016.rel_2, CertificateChecks.Batch5016.imgs_chi_3, CertificateChecks.Batch5016.fix_w_4, CertificateChecks.Batch5016.chiL_map_one_check_5, CertificateChecks.Batch5016.chiL_map_mul_check_6, CertificateChecks.Batch5016.chiR_map_mul_check_7⟩

end Certificates
