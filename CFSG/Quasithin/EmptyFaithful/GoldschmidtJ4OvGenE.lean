
module


public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4OvMax
public import Certificates.Certificate4205

public section

namespace CFSG.Quasithin.J4Ov

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2 Matrix

theorem genE
    (hF : J4Facts) {ℓ : ℕ}
    (h1 : 1 ≤ ℓ) (h4 : ℓ ≤ 4) {D : Subgroup J} (hE : Eg uJ 11 ≤ D)
    (hc : ∀ e ∈ Eg uJ 11, uEl ℓ * e * (uEl ℓ)⁻¹ ∈ D) : D = ⊤ := by
  obtain ⟨hgen, j, hj, hj'⟩ := Certificates.certificate4205 ℓ h1 h4
  have hmap : (Eg uJ 11).map (MulAut.conj (uEl ℓ)).toMonoidHom ≤ D := by
    rintro _ ⟨e, he, rfl⟩
    exact hc e he
  have hHD : Hj ≤ D := hgen.trans (sup_le hE hmap)
  have hne : D ≠ Hj := by
    rintro rfl
    exact hj' (hc _ (Subgroup.subset_closure ⟨j, hj, rfl⟩))
  exact hj_maximal hF D hHD hne

end CFSG.Quasithin.J4Ov
