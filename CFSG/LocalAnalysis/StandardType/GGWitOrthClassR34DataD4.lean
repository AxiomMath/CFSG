module

public import CFSG.LocalAnalysis.StandardType.GGWitOrthClassR34Data

public section

namespace CFSG.StandardType.ZS

@[expose] def owR34_wD4 : Fin 4 → ZMod 3 := ![1, 1, 1, 1]

@[expose] def owR34_aD4 : Fin 4 → Fin 4 → ZMod 3 :=
  ![![0, 0, 0, 1], ![1, 1, 1, 1], ![0, 0, 1, 0], ![0, 1, 0, 0]]

@[expose] def owR34_XD4 : Fin 12 → Fin 4 → ZMod 3 :=
  ![![0, 0, 0, 1], ![1, 1, 1, 1], ![0, 0, 1, 0], ![0, 1, 0, 0], ![1, 1, 1, 2], ![1, 1, 2, 1], ![1, 2, 1, 1], ![1, 1, 2, 2], ![1, 2, 1, 2], ![1, 2, 2, 1], ![1, 2, 2, 2], ![2, 0, 0, 0]]

theorem owR34_normD4 : ∀ i : Fin 4,
    ∑ k, owR34_wD4 k * (owR34_aD4 i k * owR34_aD4 i k) = 1 := by
  decide +kernel

theorem owR34_cartanD4 : ∀ i j : Fin 4,
    (2 * (1 : ZMod 3)⁻¹) * ∑ k, owR34_wD4 k * (owR34_aD4 j k * owR34_aD4 i k) =
      (CartanMatrix.D 4 i j : ZMod 3) := by
  decide +kernel

theorem owR34_diagD4 : ∀ i : Fin 4, (CartanMatrix.D 4 i i : ZMod 3) = 2 := fun i => by
  simp

theorem owR34_detD4 : ((CartanMatrix.D 4).map (fun x : ℤ => (x : ZMod 3))).det = 1 := by
  rw [← Int.cast_det (CartanMatrix.D 4)]
  have h : (CartanMatrix.D 4).det = 4 := by decide +kernel
  rw [h]
  decide

theorem owR34_normXD4 : ∀ k : Fin 12,
    ∑ i, owR34_wD4 i * (owR34_XD4 k i * owR34_XD4 k i) = 1 := by
  decide +kernel

theorem owR34_coverD4 : ∀ y : Fin 4 → ZMod 3,
    ∑ k, owR34_wD4 k * (y k * y k) = 1 →
      ∃ k : Fin 12, y = owR34_XD4 k ∨ y = -owR34_XD4 k := by
  decide +kernel

theorem owR34_chainD4_0 :
    owR34_XD4 4 = owR34_reflect owR34_wD4 (owR34_aD4 1) (owR34_XD4 0) := by
  decide +kernel

theorem owR34_chainD4_1 :
    owR34_XD4 5 = owR34_reflect owR34_wD4 (owR34_aD4 2) (owR34_XD4 1) := by
  decide +kernel

theorem owR34_chainD4_2 :
    owR34_XD4 6 = owR34_reflect owR34_wD4 (owR34_aD4 3) (owR34_XD4 1) := by
  decide +kernel

theorem owR34_chainD4_3 :
    owR34_XD4 7 = owR34_reflect owR34_wD4 (owR34_aD4 2) (owR34_XD4 4) := by
  decide +kernel

theorem owR34_chainD4_4 :
    owR34_XD4 8 = owR34_reflect owR34_wD4 (owR34_aD4 3) (owR34_XD4 4) := by
  decide +kernel

theorem owR34_chainD4_5 :
    owR34_XD4 9 = owR34_reflect owR34_wD4 (owR34_aD4 3) (owR34_XD4 5) := by
  decide +kernel

theorem owR34_chainD4_6 :
    owR34_XD4 10 = owR34_reflect owR34_wD4 (owR34_aD4 3) (owR34_XD4 7) := by
  decide +kernel

theorem owR34_chainD4_7 :
    owR34_XD4 11 = owR34_reflect owR34_wD4 (owR34_aD4 1) (owR34_XD4 10) := by
  decide +kernel

end CFSG.StandardType.ZS

end
