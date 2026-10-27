module

public import CFSG.ClassicalInvolution.Phan.Defs

public section

namespace CFSG.StandardType.QTwo

open CFSG.ClassicalInvolution.Phan

variable (K : Type) [Field K] [Finite K] [CharP K 2]

structure QTwoPhanFamily (Y : Type) [Group Y] (n : ℕ) extends PhanFamily K 2 1 Y n where
  four : ∀ (i : Fin n) (h : (i : ℕ) + 2 < n), ∃ Θ : Su K 2 1 4 →* Y,
    Θ.comp (blockEmb K 2 1 4 3 0 (by norm_num)) = θ i ∧
      Θ.comp (blockEmb K 2 1 4 3 1 (by norm_num)) = θ ⟨i + 1, by omega⟩
  farNodeEdge : ∀ i j : Fin n, (j : ℕ) + 1 < n → ((i : ℕ) + 1 < j ∨ (j : ℕ) + 2 < i) →
    ∀ a b, ι i a * θ j b = θ j b * ι i a
  farEdgeEdge : ∀ i j : Fin n, (j : ℕ) + 1 < n → (i : ℕ) + 2 < j →
    ∀ a b, θ i a * θ j b = θ j b * θ i a

variable {K}

@[expose] def QTwoPhanFamily.restrict {Y : Type} [Group Y] {n : ℕ}
    (F : QTwoPhanFamily K Y (n + 1)) : QTwoPhanFamily K Y n where
  ι i := F.ι i.castSucc
  θ i := F.θ i.castSucc
  left i h := F.left i.castSucc (by rw [Fin.coe_castSucc]; omega)
  right i h := by
    rw [F.right i.castSucc (by rw [Fin.coe_castSucc]; omega)]
    rfl
  comm i j h a b := F.comm i.castSucc j.castSucc (by simpa using h) a b
  four i h := by
    obtain ⟨Θ, h0, h1⟩ := F.four i.castSucc (by rw [Fin.coe_castSucc]; omega)
    exact ⟨Θ, h0, h1⟩
  farNodeEdge i j hj hij a b :=
    F.farNodeEdge i.castSucc j.castSucc (by rw [Fin.coe_castSucc]; omega) (by simpa using hij) a b
  farEdgeEdge i j hj hij a b :=
    F.farEdgeEdge i.castSucc j.castSucc (by rw [Fin.coe_castSucc]; omega) (by simpa using hij) a b

variable (K)

@[expose] def QTwoPhanUniversalAt (n : ℕ) : Prop :=
  ∀ {Y : Type} [Group Y] (F : QTwoPhanFamily K Y n), ∃ ψ : Su K 2 1 (n + 1) →* Y,
    (∀ i : Fin n, ψ.comp (blockEmb2 K 2 1 n i) = F.ι i) ∧
      ∀ (i : Fin n) (h : (i : ℕ) + 1 < n), ψ.comp (blockEmb3 K 2 1 n i h) = F.θ i

end CFSG.StandardType.QTwo

end
