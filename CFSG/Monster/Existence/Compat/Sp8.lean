module

import CFSG.HardMathSupport.Foote.E27.Q2Sp
public import CFSG.Blueprint.Catalog

public section

namespace CFSG.Monster.Existence.Compat

open CFSG.Assembly.LowTwoRank CFSG.Blueprint Matrix

theorem fromBlocks_eq_neg_J (n : ℕ) (K : Type) [Field K] :
    (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
      -Matrix.J (Fin n) K := by
  simp [Matrix.J, Matrix.fromBlocks_neg]

theorem stated_mem_iff (n : ℕ) (K : Type) [Field K] (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) :
    Aᵀ * Matrix.fromBlocks 0 1 (-1) 0 * A = Matrix.fromBlocks 0 1 (-1) 0 ↔
      A ∈ Matrix.symplecticGroup (Fin n) K := by
  rw [fromBlocks_eq_neg_J, Matrix.mul_neg, Matrix.neg_mul, neg_inj, SymplecticGroup.mem_iff']

@[expose] noncomputable def spHom (n : ℕ) (K : Type) [Field K] :
    Matrix.symplecticGroup (Fin n) K →* GL (Fin n ⊕ Fin n) K :=
  MonoidHom.toHomUnits (Matrix.symplecticGroup (Fin n) K).subtype

theorem spHom_injective (n : ℕ) (K : Type) [Field K] : Function.Injective (spHom n K) := by
  intro A B h
  apply Subtype.ext
  exact congrArg (fun u : GL (Fin n ⊕ Fin n) K => (u : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)) h

theorem coe_spHom (n : ℕ) (K : Type) [Field K] (A : Matrix.symplecticGroup (Fin n) K) :
    ((spHom n K A : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = A := rfl

theorem range_spHom (n : ℕ) (K : Type) [Field K] : (spHom n K).range = StatedSp n K := by
  apply le_antisymm
  · rintro _ ⟨A, rfl⟩
    exact Subgroup.subset_closure ((stated_mem_iff n K _).2 A.2)
  · refine Subgroup.closure_le _ |>.2 fun A hA => ?_
    exact ⟨⟨A, (stated_mem_iff n K _).1 hA⟩, Units.ext rfl⟩

@[expose] noncomputable def statedSpEquiv (n : ℕ) (K : Type) [Field K] :
    StatedSp n K ≃* Matrix.symplecticGroup (Fin n) K :=
  ((MonoidHom.ofInjective (spHom_injective n K)).trans
    (MulEquiv.subgroupCongr (range_spHom n K))).symm

@[expose] noncomputable def sympMapEquiv {l : Type} [DecidableEq l] [Fintype l] {K K' : Type}
    [Field K] [Field K'] (e : K ≃+* K') :
    Matrix.symplecticGroup l K ≃* Matrix.symplecticGroup l K' where
  toFun A := ⟨(A : Matrix (l ⊕ l) (l ⊕ l) K).map e, SymplecticGroup.map_mem A.2 e⟩
  invFun A := ⟨(A : Matrix (l ⊕ l) (l ⊕ l) K').map e.symm, SymplecticGroup.map_mem A.2 e.symm⟩
  left_inv A := Subtype.ext (by ext i j; simp)
  right_inv A := Subtype.ext (by ext i j; simp)
  map_mul' A B := Subtype.ext (by simp [Matrix.map_mul])

theorem subsingleton_units_of_card_two {K : Type} [Field K] [Finite K] (h : Nat.card K = 2) :
    Subsingleton Kˣ := by
  classical
  have := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card] at h
  rw [← Fintype.card_le_one_iff_subsingleton, Fintype.card_units, h]

theorem statedScalars_eq_bot {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [Finite K]
    (h : Nat.card K = 2) : StatedScalars ι K = ⊥ :=
  CFSG.HardMathSupport.Foote.E27.Q2.statedScalars_eq_bot h

@[expose] noncomputable def statedProjEquivOfBot {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] (H : Subgroup (GL ι K)) (hb : StatedScalars ι K = ⊥) : StatedProj H ≃* H :=
  (QuotientGroup.quotientMulEquivOfEq (by rw [hb, Subgroup.bot_subgroupOf])).trans
    QuotientGroup.quotientBot

noncomputable def ringEquivZMod2 {K : Type} [Field K] [Finite K] (h : Nat.card K = 2) :
    K ≃+* ZMod 2 := by
  have := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card] at h
  exact FiniteField.ringEquivOfCardEq (by rw [h, ZMod.card])

theorem sp8_equiv_of_lieModel (X : Type) [Group X] (h : LieModel X .PSp 4 2 1) :
    Nonempty (X ≃* Matrix.symplecticGroup (Fin 4) (ZMod 2)) := by
  rcases h with ⟨-, -, K, _, hfin, hK, ⟨e⟩⟩ | ⟨h4, -⟩ | ⟨h4, -⟩ | ⟨h4, -⟩
  · have hK2 : Nat.card K = 2 := by simpa using hK
    exact ⟨e.trans ((statedProjEquivOfBot _ (statedScalars_eq_bot hK2)).trans
      ((statedSpEquiv 4 K).trans (sympMapEquiv (ringEquivZMod2 hK2))))⟩
  all_goals exact absurd h4 (by norm_num)

end CFSG.Monster.Existence.Compat
