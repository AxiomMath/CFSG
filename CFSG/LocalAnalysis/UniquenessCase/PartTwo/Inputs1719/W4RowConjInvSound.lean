module

public import Certificates.Data.W4RowConjInv

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

open CFSG.QuasithinUnique.Setup.X1 CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

theorem ne_of_eqA_eq_false {n : ℕ} {t u : Array ℕ} {g h : Equiv.Perm (Fin n)}
    (ht : Rep n t g) (hu : Rep n u h) (he : eqA n t u = false) : g ≠ h := by
  intro hgh
  have htrue : eqA n t u = true := (eqA_iff ht hu).2 hgh
  rw [htrue] at he
  exact Bool.false_ne_true he.symm

theorem inv_of_conjInvCheck {n : ℕ} {t h x : PArr} {gt gh gx : Equiv.Perm (Fin n)}
    (ht : PRep n t gt) (hh : PRep n h gh) (hx : PRep n x gx)
    (hc : conjInvCheck n t h x = true) :
    gt * (gh * gx * gh⁻¹) * gt⁻¹ = (gh * gx * gh⁻¹)⁻¹ := by
  simp only [conjInvCheck] at hc
  have hl : Rep n (compA n (compA n t.1 (compA n (compA n h.1 x.1) h.2)) t.2)
      (gt * (gh * gx * gh⁻¹) * gt⁻¹) := by
    have := rep_compA (rep_compA ht.1 (rep_compA (rep_compA hh.1 hx.1) hh.2)) ht.2
    simpa [mul_assoc] using this
  have hr : Rep n (compA n (compA n h.1 x.2) h.2) ((gh * gx * gh⁻¹)⁻¹) := by
    have := rep_compA (rep_compA hh.1 hx.2) hh.2
    rw [mul_inv_rev, mul_inv_rev]
    simpa [mul_assoc] using this
  exact (eqA_iff hl hr).1 hc

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row
