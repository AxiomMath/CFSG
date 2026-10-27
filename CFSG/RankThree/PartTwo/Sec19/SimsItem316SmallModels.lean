module

public import CFSG.RankThree.PartTwo.Sec19.SimsItem316SmallHeart

public section

namespace CFSG.RankThree.PartTwo.Sec19.SimsItem316Small

open CFSG.RankThree.PartTwo CFSG.QuasithinUnique Matrix
open CFSG.Assembly.RankThreeEven (orthogonalPlus orthogonalMinus plusQuadForm minusQuadForm)

@[expose] def S3 : Fin 0 ⊕ Fin 0 ⊕ Fin 2 → Fin 3 → ZMod 2 :=
  Sum.elim ![] (Sum.elim ![] ![![1, 1, 0], ![0, 1, 1]])

@[expose] def c3 : Fin 3 → Fin 0 ⊕ Fin 0 ⊕ Fin 2 → ZMod 2 :=
  ![Sum.elim ![] (Sum.elim ![] ![0, 0]), Sum.elim ![] (Sum.elim ![] ![1, 0]),
    Sum.elim ![] (Sum.elim ![] ![1, 1])]

@[expose] def model3 : HeartModel 3 (Fin 0 ⊕ Fin 0 ⊕ Fin 2) (minusQuadForm 0 (1 : ZMod 2) 1) where
  S := S3
  c := c3
  three_le := le_rfl
  odd_or_four_dvd := Or.inl ⟨1, rfl⟩
  CP := by decide +kernel
  sum_S := by decide +kernel
  PC := by decide +kernel
  sum_c := by decide +kernel
  Q_eq := by decide +kernel
  hA := by decide +kernel
  hB := by decide +kernel
  hS2 := by decide +kernel
  hS3 := by decide +kernel

theorem omegaMinusTwo_zero_model :
    ∃ (φ : omegaMinusTwo 0 ≃* alternatingGroup (Fin 3))
      (ψ : (Fin 0 ⊕ Fin 0 ⊕ Fin 2 → ZMod 2) ≃+ altHeart 3),
      ∀ (g : omegaMinusTwo 0) (w : Fin 0 ⊕ Fin 0 ⊕ Fin 2 → ZMod 2) (x : evenWeight 3),
        ψ w = (x : altHeart 3) →
        ψ (((g : GL (Fin 0 ⊕ Fin 0 ⊕ Fin 2) (ZMod 2)) :
            Matrix (Fin 0 ⊕ Fin 0 ⊕ Fin 2) (Fin 0 ⊕ Fin 0 ⊕ Fin 2) (ZMod 2)) *ᵥ w) =
          (evenWeightPerm (φ g : Equiv.Perm (Fin 3)) x : altHeart 3) :=
  ⟨model3.φ, model3.ψ, model3.intertwine⟩

@[expose] def S5 : Fin 1 ⊕ Fin 1 ⊕ Fin 2 → Fin 5 → ZMod 2 :=
  Sum.elim ![![1, 1, 1, 1, 0]] (Sum.elim ![![1, 1, 1, 0, 1]] ![![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0]])

@[expose] def c5 : Fin 5 → Fin 1 ⊕ Fin 1 ⊕ Fin 2 → ZMod 2 :=
  ![Sum.elim ![0] (Sum.elim ![0] ![0, 0]), Sum.elim ![0] (Sum.elim ![0] ![1, 0]),
    Sum.elim ![0] (Sum.elim ![0] ![0, 1]), Sum.elim ![1] (Sum.elim ![0] ![1, 1]),
    Sum.elim ![0] (Sum.elim ![1] ![1, 1])]

@[expose] def model5 : HeartModel 5 (Fin 1 ⊕ Fin 1 ⊕ Fin 2) (minusQuadForm 1 (1 : ZMod 2) 1) where
  S := S5
  c := c5
  three_le := by norm_num
  odd_or_four_dvd := Or.inl ⟨2, rfl⟩
  CP := by decide +kernel
  sum_S := by decide +kernel
  PC := by decide +kernel
  sum_c := by decide +kernel
  Q_eq := by decide +kernel
  hA := by decide +kernel
  hB := by decide +kernel
  hS2 := by decide +kernel
  hS3 := by decide +kernel

theorem omegaMinusTwo_one_model :
    ∃ (φ : omegaMinusTwo 1 ≃* alternatingGroup (Fin 5))
      (ψ : (Fin 1 ⊕ Fin 1 ⊕ Fin 2 → ZMod 2) ≃+ altHeart 5),
      ∀ (g : omegaMinusTwo 1) (w : Fin 1 ⊕ Fin 1 ⊕ Fin 2 → ZMod 2) (x : evenWeight 5),
        ψ w = (x : altHeart 5) →
        ψ (((g : GL (Fin 1 ⊕ Fin 1 ⊕ Fin 2) (ZMod 2)) :
            Matrix (Fin 1 ⊕ Fin 1 ⊕ Fin 2) (Fin 1 ⊕ Fin 1 ⊕ Fin 2) (ZMod 2)) *ᵥ w) =
          (evenWeightPerm (φ g : Equiv.Perm (Fin 5)) x : altHeart 5) :=
  ⟨model5.φ, model5.ψ, model5.intertwine⟩

@[expose] def S8 : Fin 3 ⊕ Fin 3 → Fin 8 → ZMod 2 :=
  Sum.elim ![![1, 1, 1, 1, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 1, 1, 0], ![0, 1, 1, 0, 0, 0, 1, 1]]
    ![![1, 1, 1, 0, 1, 0, 0, 0], ![1, 1, 0, 0, 0, 1, 0, 1], ![0, 1, 0, 1, 1, 1, 0, 0]]

@[expose] def c8 : Fin 8 → Fin 3 ⊕ Fin 3 → ZMod 2 :=
  ![Sum.elim ![0, 0, 0] ![0, 0, 0], Sum.elim ![0, 0, 1] ![0, 0, 1],
    Sum.elim ![0, 1, 0] ![0, 1, 1], Sum.elim ![1, 1, 1] ![0, 1, 0],
    Sum.elim ![0, 1, 1] ![1, 1, 0], Sum.elim ![1, 0, 1] ![1, 0, 0],
    Sum.elim ![1, 1, 0] ![1, 0, 1], Sum.elim ![1, 0, 0] ![1, 1, 1]]

@[expose] def model8 : HeartModel 8 (Fin 3 ⊕ Fin 3) (plusQuadForm 3) where
  S := S8
  c := c8
  three_le := by norm_num
  odd_or_four_dvd := Or.inr ⟨2, rfl⟩
  CP := by decide +kernel
  sum_S := by decide +kernel
  PC := by decide +kernel
  sum_c := by decide +kernel
  Q_eq := by decide +kernel
  hA := by decide +kernel
  hB := by decide +kernel
  hS2 := by decide +kernel
  hS3 := by decide +kernel

theorem omegaPlusTwo_three_model :
    ∃ (φ : omegaPlusTwo 3 ≃* alternatingGroup (Fin 8))
      (ψ : (Fin 3 ⊕ Fin 3 → ZMod 2) ≃+ altHeart 8),
      ∀ (g : omegaPlusTwo 3) (w : Fin 3 ⊕ Fin 3 → ZMod 2) (x : evenWeight 8),
        ψ w = (x : altHeart 8) →
        ψ (((g : GL (Fin 3 ⊕ Fin 3) (ZMod 2)) :
            Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)) *ᵥ w) =
          (evenWeightPerm (φ g : Equiv.Perm (Fin 8)) x : altHeart 8) :=
  ⟨model8.φ, model8.ψ, model8.intertwine⟩

end CFSG.RankThree.PartTwo.Sec19.SimsItem316Small
