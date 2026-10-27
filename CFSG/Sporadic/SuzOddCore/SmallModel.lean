module

public import CFSG.Sporadic.SuzOddCore.CertChain
public import CFSG.Sporadic.SuzOddCore.LiftedValid

public noncomputable section

namespace CFSG.Sporadic.SuzOddCore

open CFSG.Certificates CFSG.Monster.B.Co2

theorem mem_suzU_toList {x : SuzK} :
    x ∈ suzU.toList ↔ x = (suzA0, suzB0) ∨ x = (suzA1, suzB1) := by
  rw [schreier_vector_mem_toList_iff_get]
  constructor
  · rintro ⟨i, rfl⟩
    rw [suzU_get, certChain_original_eq, suzBGen]
    have hi : (i : ℕ) < 2 := lt_of_lt_of_eq i.2 certChain_originalCount
    interval_cases h : (i : ℕ)
    · left
      rw [show Fin.cast certChain_originalCount i = 0 from Fin.ext h]
      simp only [Matrix.cons_val_zero]
    · right
      rw [show Fin.cast certChain_originalCount i = 1 from Fin.ext h]
      simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
  · rintro (rfl | rfl)
    · refine ⟨⟨0, by rw [certChain_originalCount]; norm_num⟩, ?_⟩
      rw [suzU_get, certChain_original_eq, suzBGen]
      rfl
    · refine ⟨⟨1, by rw [certChain_originalCount]; norm_num⟩, ?_⟩
      rw [suzU_get, certChain_original_eq, suzBGen]
      rfl

theorem certChain_liftedOriginalSubgroup : certChain.liftedOriginalSubgroup suzU = suzH := by
  rw [RawSchreierDatum.liftedOriginalSubgroup, suzH]
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  exact mem_suzU_toList

theorem suzU_image (j : Fin certChain.originalCount) :
    suzPhi (suzU.get j) = certChain.original.get j := by
  rw [suzU_get]
  rfl

theorem suzLiftedValid :
    ValidLiftedSchreier certChain suzPhi suzU := by
  refine validLiftedSchreier_of_injOn certChain_valid suzU_image fun x hx h1 => ?_
  rw [certChain_liftedOriginalSubgroup] at hx
  exact suzH_fst_injective hx suzH.one_mem h1

@[expose] def suzEquivM :
    Blueprint.NativeSporadic.Suz ≃* suzM := suzEquivP.trans suzTheta

theorem suzEquivM_seedA :
    suzEquivM suzSeedA = suzB0M := by
  rw [suzEquivM, MulEquiv.trans_apply, suzEquivP_seedA, suzTheta_a0]

theorem suzEquivM_seedB :
    suzEquivM suzSeedB = suzB1M := by
  rw [suzEquivM, MulEquiv.trans_apply, suzEquivP_seedB, suzTheta_a1]

theorem suzM_not_comm :
    ∃ x y : suzM, x * y ≠ y * x := by
  by_contra h
  have h' : ∀ x y : suzM, x * y = y * x := fun x y => by
    by_contra hxy
    exact h ⟨x, y, hxy⟩
  have : IsMulCommutative suzM := ⟨⟨h'⟩⟩
  have hp := (Group.is_simple_iff_prime_card (α := suzM)).1 suzM_isSimpleGroup
  rw [suzM_card] at hp
  norm_num at hp

theorem CTUC_Suz_small_faithful_permutation_model :
    ValidLiftedSchreier certChain suzPhi suzU ∧
    (∃! θ : suzP ≃* suzM, θ suzA0P = suzB0M ∧ θ suzA1P = suzB1M) ∧
    ((suzSeedA : Matrix (Fin 64) (Fin 64) (ZMod 3)) =
        Blueprint.NativeSporadic.decode 3 64 1 Blueprint.NativeSporadic.SuzSeed1 ∧
      (suzSeedB : Matrix (Fin 64) (Fin 64) (ZMod 3)) =
        Blueprint.NativeSporadic.decode 3 64 1 Blueprint.NativeSporadic.SuzSeed2) ∧
    (suzEquivP suzSeedA = suzA0P ∧ suzEquivP suzSeedB = suzA1P ∧
      ∀ e : Blueprint.NativeSporadic.Suz ≃* suzP, e suzSeedA = suzA0P → e suzSeedB = suzA1P →
        e = suzEquivP) ∧
    suzEquivM = suzEquivP.trans suzTheta ∧ suzEquivM suzSeedA = suzB0M ∧
    suzEquivM suzSeedB = suzB1M ∧
    IsSimpleGroup suzM ∧ (∃ x y : suzM, x * y ≠ y * x) ∧ Nat.card suzM = 448345497600 :=
  ⟨suzLiftedValid, ⟨suzTheta, ⟨suzTheta_a0, suzTheta_a1⟩, fun e he => suzTheta_unique e he.1 he.2⟩,
    ⟨suzSeedA_val, suzSeedB_val⟩, ⟨suzEquivP_seedA, suzEquivP_seedB, suzEquivP_unique⟩, rfl,
    suzEquivM_seedA, suzEquivM_seedB, suzM_isSimpleGroup, suzM_not_comm, suzM_card⟩

end CFSG.Sporadic.SuzOddCore
