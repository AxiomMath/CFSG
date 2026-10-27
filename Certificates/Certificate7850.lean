module

public import Certificates.Kernel.J4NP7850.SoundFix
public import Certificates.Kernel.J4NP7850.SoundOrb

public section

namespace Certificates

open CertificateChecks.KernelJ4NP7850 in
open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Quasithin.KGC31.J4M4 in
theorem certificate7850 :
    (∀ j < 10, ∀ k < 31, fJn j • kwRow k = kwRow k) ∧
    (∀ c < 2048, (∀ k < 31, eta uJ 11 c • (gJ • kwRow k) = gJ • kwRow k) ↔
      c ∈ [0, 12, 16, 28, 129, 141, 145, 157, 352, 364, 368, 380, 481, 493, 497, 509, 576, 588,
        592, 604, 705, 717, 721, 733, 800, 812, 816, 828, 929, 941, 945, 957, 1060, 1064, 1076,
        1080, 1189, 1193, 1205, 1209, 1348, 1352, 1364, 1368, 1477, 1481, 1493, 1497, 1636, 1640,
        1652, 1656, 1765, 1769, 1781, 1785, 1796, 1800, 1812, 1816, 1925, 1929, 1941, 1945]) ∧
    759 * Nat.card ↥(Hj ⊓ Subgroup.normalizer ((Eg uJ 11 ⊓
      fixingSubgroup J {v : Row | ∃ k < 31, v = gJ • kwRow k} : Subgroup J) : Set J)) ≤
        Nat.card ↥Hj ∧
    (∃ k < 31, ∀ k' < 31, eta uJ 11 4 • (gJ • kwRow k) ≠ gJ • kwRow k') ∧
    ∀ x : J, (∀ j < 10, (gJ * fJn j * gJ⁻¹) • (x • CFSG.Sporadic.J4.QT2.w₀) =
      x • CFSG.Sporadic.J4.QT2.w₀) → ∃ k < 31, x • CFSG.Sporadic.J4.QT2.w₀ = gJ • kwRow k :=
  have hF := Certificates.certificate3084
  ⟨kwFix_sound hF.mat, y8_sound hF.mat, orb_sound hF.mat (y8_sound hF.mat), move_sound hF.mat,
    fix_sound hF⟩

end Certificates
