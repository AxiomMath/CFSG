module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4OvLat
public import Certificates.Certificate4207
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4OvMax

public section

namespace CFSG.Quasithin.J4Ov

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2 Matrix

section Main


theorem genP [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat] (hF : J4Facts) {i : ℕ} (hi : i < 49)
    (hexc : (repData.getD i ⟨0, "", true, 0⟩).exc = false) {D : Subgroup J} (hP : P0 ≤ D)
    (hc : ∀ x ∈ Eg uJ 11, (zEl (repData.getD i ⟨0, "", true, 0⟩))⁻¹ * x *
      zEl (repData.getD i ⟨0, "", true, 0⟩) ∈ D) : D = ⊤ := by
  obtain ⟨⟨s, hsG, hsH, hsE, p, hp, hpE⟩, j, hj, hj'⟩ :=
    Certificates.certificate4207 i hi hexc
  have hmap : (Eg uJ 11).map
      (MulAut.conj (zEl (repData.getD i ⟨0, "", true, 0⟩))⁻¹).toMonoidHom ≤ D := by
    rintro _ ⟨x, hx, rfl⟩
    simpa using hc x hx
  have hHD : Hj ≤ D := Hj_le_of_elt hP (sup_le hP hmap hsG) hsH hsE hp hpE
  have hne : D ≠ Hj := by
    rintro rfl
    exact hj' (hc _ (Subgroup.subset_closure ⟨j, hj, rfl⟩))
  exact hj_maximal hF D hHD hne

end Main

end CFSG.Quasithin.J4Ov
