module

public import CFSG.Quasithin.Background.HSL4Q13

public section

namespace CFSG.Quasithin.H.Q13

open Matrix

@[expose] def pq : Fin 6 → Fin 4 × Fin 4 := ![(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]

@[expose] def wm4 (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  Matrix.of fun k l => g (pq k).1 (pq l).1 * g (pq k).2 (pq l).2 -
    g (pq k).1 (pq l).2 * g (pq k).2 (pq l).1

theorem card_fix_nat :
    (Finset.univ.filter (fun v : Fin 4 → ZMod 2 => ∀ k, sc k *ᵥ v = v)).card ≤ 2 := by
  decide +kernel

theorem card_fix_dual :
    (Finset.univ.filter (fun v : Fin 4 → ZMod 2 => ∀ k, (sci k)ᵀ *ᵥ v = v)).card ≤ 2 := by
  decide +kernel

theorem card_fix_wedge :
    (Finset.univ.filter (fun c : Fin 6 → ZMod 2 => ∀ k, wm4 (sc k) *ᵥ c = c)).card ≤ 4 := by
  decide +kernel

theorem card_fix_wedge_dual :
    (Finset.univ.filter (fun c : Fin 6 → ZMod 2 => ∀ k, wm4 (sci k)ᵀ *ᵥ c = c)).card ≤ 4 := by
  decide +kernel

end CFSG.Quasithin.H.Q13
