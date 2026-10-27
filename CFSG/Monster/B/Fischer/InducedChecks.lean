
module

public import CFSG.Monster.B.Fischer.InducedChecksBase

public import CFSG.Monster.B.Fischer.InducedEncoding
public meta import CFSG.Monster.B.Fischer.InducedEncoding
public import CFSG.Monster.B.Fischer.InducedChecksInputs
public import Certificates.Certificate3034
public import Certificates.Certificate3034Base

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.Fischer

open CFSG.Monster.Code CFSG.Monster.B.Classical.Mog22 CFSG.Monster.B.TwoA CFSG.Sporadic.Mathieu

theorem check_X :
    ∀ g < 2, ∀ t < 22, (indM22Gen g)[t]! = genAB' g t :=
  Certificates.certificate3034.1

theorem check_W :
    ∀ g < 2, ∀ u < 1024, (indM22Gen g)[22 + u]! = 22 + linW g u :=
  Certificates.certificate3034.2.1

theorem zCheck_all :
    (List.range 2).all (fun g => (List.range 77).all (zCheckOne g)) = true :=
  Certificates.certificate3034.2.2.1

theorem check_Z : ∀ g < 2, ∀ i < 77,
    dFind (wordCat (kappaWord g i)) < dCert.pts.size ∧
    (dCert.pts[dFind (wordCat (kappaWord g i))]!).extract 0 22 = wordCat (kappaWord g i) ∧
    zFib g i < 77 ∧ ∀ q < 32, (indM22Gen g)[1046 + 32 * i + q]! =
      1046 + 32 * zFib g i + (dCert.pts[dFind (wordCat (kappaWord g i))]!)[22 + q]! := by
  intro g hg i hi
  have h := zCheck_all
  simp only [List.all_eq_true, List.mem_range] at h
  have h1 := h g hg i hi
  simp only [zCheckOne, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    List.mem_range] at h1
  exact ⟨h1.1.1.1, h1.1.1.2, h1.1.2, h1.2⟩

theorem check_D_snd :
    ∀ p < 5760, ∀ q < 32, (dCert.pts[p]!)[22 + q]! < 32 :=
  Certificates.certificate3034.2.2.2.1

theorem check_T : ∀ t < 10, (∀ n < 22, (indTransGen t)[n]! = n) ∧
    (∀ u < 1024, (indTransGen t)[22 + u]! = 22 + (u ^^^ 2 ^ t)) ∧
    ∀ i < 77, zShift t i < 32 ∧ ∀ q < 32,
      (indTransGen t)[1046 + 32 * i + q]! = 1046 + 32 * i + (q ^^^ zShift t i) :=
  Certificates.certificate3034.2.2.2.2.1

theorem check_shift : ∀ t < 10, ∀ i < 77,
    red 17 pivQ rowQ (wordMask (invWord (blockWord i)) (spreadW (2 ^ t)) ^^^
      spreadQ (zShift t i)) = 0 :=
  Certificates.certificate3034.2.2.2.2.2.1

theorem check_size : ∀ g < 2, (indM22Gen g).size = 3510 :=
  Certificates.certificate3034.2.2.2.2.2.2

end CFSG.Monster.B.Fischer
