module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHeCertificate

public import CFSG.Quasithin.Vol2.Ch5Sec1L34FiveSpor
public import CFSG.Quasithin.Vol2.KGFactAutSylowM11
public import CFSG.Quasithin.Vol2.KGFactAutSylowM12
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHe
import all CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHe

public section

namespace CFSG.Quasithin.H13.FiveNorm

open CFSG.QuasithinUnique CFSG.Blueprint.NativeSporadic

theorem noFiveOver_M11 :
    NoFiveOver (Carrier .M11) := by
  have hcard0 : Nat.card (Carrier .M11) = 7920 := CFSG.Sporadic.Mathieu.card_M11
  have : Finite (Carrier .M11) := Nat.finite_of_card_ne_zero (by rw [hcard0]; norm_num)
  have hcard : Nat.card (Carrier .M11) = 2 ^ 4 * 495 := by
    rw [hcard0]
    norm_num
  exact noFiveOver_of_rows CFSG.Quasithin.H13.KGSporLat.m11Mems hcard (by decide) (by decide)
    (by decide)
    (fun S H hS hSH => CFSG.Quasithin.H13.KGSporLat.m11_overgroups ⟨MulEquiv.refl _⟩ hS hSH)

theorem noFiveOver_M12 :
    NoFiveOver (Carrier .M12) := by
  have hcard0 : Nat.card (Carrier .M12) = 95040 := CFSG.Sporadic.Mathieu.card_M12
  have : Finite (Carrier .M12) := Nat.finite_of_card_ne_zero (by rw [hcard0]; norm_num)
  have hcard : Nat.card (Carrier .M12) = 2 ^ 6 * 1485 := by
    rw [hcard0]
    norm_num
  exact noFiveOver_of_rows CFSG.Quasithin.H13.KGSporLat.m12Mems hcard (by decide) (by decide)
    (by decide)
    (fun S H hS hSH => CFSG.Quasithin.H13.KGSporLat.m12_overgroups ⟨MulEquiv.refl _⟩ hS hSH)

theorem noFiveOver_M24 :
    NoFiveOver (Carrier .M24) := by
  have hcard0 : Nat.card (Carrier .M24) = 244823040 := CFSG.Sporadic.Mathieu.card_M24
  have : Finite (Carrier .M24) := Nat.finite_of_card_ne_zero (by rw [hcard0]; norm_num)
  have hcard : Nat.card (Carrier .M24) = 2 ^ 10 * 239085 := by
    rw [hcard0]
    norm_num
  exact noFiveOver_of_rows CFSG.QuasithinUnique.Ch1.SporLat.M24.m24Mems hcard (by decide)
    (by decide) (by decide)
    (fun S H hS hSH => CFSG.QuasithinUnique.Ch1.SporLat.M24.m24_overgroups ⟨MulEquiv.refl _⟩ hS
      hSH)

theorem noFiveOver_He :
    NoFiveOver (Carrier .He) := by
  have hcard0 : Nat.card (Carrier .He) = 4030387200 := CFSG.Sporadic.He.card_He
  have : Finite (Carrier .He) := Nat.finite_of_card_ne_zero (by rw [hcard0]; norm_num)
  have hcard : Nat.card (Carrier .He) = 2 ^ 10 * 3935925 := by
    rw [hcard0]
    norm_num
  exact noFiveOver_of_rows CFSG.QuasithinUnique.Ch1.SporLat.He.heMems hcard (by decide)
    (by decide) (by decide)
    (fun S H hS hSH => CFSG.QuasithinUnique.Ch1.SporLat.He.he_overgroups ⟨MulEquiv.refl _⟩ hS
      hSH)

end CFSG.Quasithin.H13.FiveNorm
