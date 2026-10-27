module

public import CFSG.LocalAnalysis.StandardType.GGTBJReflPlain

public section

namespace CFSG.StandardType

theorem exists_not_commute_reflection_four {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {ι : Type} [Nonempty ι] (f : ι → (Fin 4 → ZMod p) → ZMod p) (v : ι → (Fin 4 → ZMod p))
    (hadd : ∀ i x y, f i (x + y) = f i x + f i y)
    (hsmul : ∀ i (c : ZMod p) x, f i (c • x) = c * f i x)
    (hfv : ∀ i, f i (v i) = 2)
    (hconn : ∀ S : Set ι, S.Nonempty →
      (∀ i j, (f i (v j) ≠ 0 ∨ f j (v i) ≠ 0) → (i ∈ S ↔ j ∈ S)) → S = Set.univ)
    (hcard : p ^ 2 * Nat.card {w : Fin 4 → ZMod p // ∀ i, f i w = 0} ≤ p ^ 4) :
    ∃ (i j : ι) (w : Fin 4 → ZMod p),
      (w - f j w • v j) - f i (w - f j w • v j) • v i ≠
        (w - f i w • v i) - f j (w - f i w • v i) • v j := by
  have hV : Nat.card (Fin 4 → ZMod p) = p ^ 4 := by
    rw [Nat.card_fun, Nat.card_fin, Nat.card_zmod]
  exact @exists_not_commute_reflection_plain p _ hp2 (Fin 4 → ZMod p) Pi.addCommGroup
    (Pi.Function.module (Fin 4) (ZMod p) (ZMod p)) inferInstance ι _ f v hadd hsmul hfv hconn
    (hV ▸ hcard)

end CFSG.StandardType

end
