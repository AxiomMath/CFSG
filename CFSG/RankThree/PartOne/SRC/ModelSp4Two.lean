module

public import CFSG.RankThree.PartOne.SRC.ModelSp4
public import CFSG.RankThree.PartOne.SRC.CentralizerTwo
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Pairs

public section

namespace CFSG.RankThree.PartOne.SRC

open Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.RankThree.PartTwo.Census
open CFSG.LieType.Universal.Symplectic.SpExtras (mat)
open scoped MatrixGroups

variable {K : Type} [Field K]

@[expose] noncomputable def sp4Emb0 : SL(2, K) →* StatedProj (StatedSp 2 K) :=
  (QuotientGroup.mk' ((StatedScalars (Fin 2 ⊕ Fin 2) K).subgroupOf (StatedSp 2 K))).comp
    (longBlock K 2 0)

theorem sp4Emb0_injective : Function.Injective (sp4Emb0 (K := K)) := by
  rw [injective_iff_map_eq_one]
  intro A hA
  rw [sp4Emb0, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf] at hA
  obtain ⟨u, hu⟩ := hA
  have h := congrArg (fun g : GL (Fin 2 ⊕ Fin 2) K => (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) hu
  have e := congrFun (congrFun h (Sum.inl 1)) (Sum.inl 1)
  have e1 : (((longBlock K 2 0 A : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) (Sum.inl 1) (Sum.inl 1) = 1 := by
    change mat 2 K (longBlock K 2 0 A) (Sum.inl 1) (Sum.inl 1) = 1
    rw [mat_longBlock, blockMat_apply_of_not_mem (0 : Fin 2) _ (by simp [mem_coords])]
    simp
  rw [e1] at e
  have hu0 : (u : K) = 1 := by simpa [Matrix.GeneralLinearGroup.coe_scalar] using e
  have hu1 : u = 1 := Units.ext hu0
  subst hu1
  have hA1 : longBlock K 2 0 A = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [← hu]
    simp
  exact longBlock_injective 0 (hA1.trans (map_one _).symm)

@[expose] noncomputable def sp4Invol0 : StatedProj (StatedSp 2 K) :=
  QuotientGroup.mk' ((StatedScalars (Fin 2 ⊕ Fin 2) K).subgroupOf (StatedSp 2 K))
    (longInv K 2 0)

theorem longInv_not_mem (h2 : (2 : K) ≠ 0) :
    longInv K 2 0 ∉ (StatedScalars (Fin 2 ⊕ Fin 2) K).subgroupOf (StatedSp 2 K) := by
  rintro ⟨u, hu⟩
  have hu' := congrArg (fun g : GL (Fin 2 ⊕ Fin 2) K => (g : Matrix (Fin 2 ⊕ Fin 2)
    (Fin 2 ⊕ Fin 2) K)) hu
  change Matrix.scalar _ (u : K) = mat 2 K (longInv K 2 0) at hu'
  rw [mat_longInv] at hu'
  have e0 : (u : K) = -1 := by
    have := congrArg (fun M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K => M (Sum.inl 0) (Sum.inl 0))
      hu'
    simpa [mem_coords] using this
  have e1 : (u : K) = 1 := by
    have := congrArg (fun M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K => M (Sum.inl 1) (Sum.inl 1))
      hu'
    simpa [mem_coords] using this
  apply h2
  linear_combination e0 - e1

theorem orderOf_sp4Invol0 (h2 : (2 : K) ≠ 0) :
    orderOf (sp4Invol0 : StatedProj (StatedSp 2 K)) = 2 := by
  have hsq : (sp4Invol0 : StatedProj (StatedSp 2 K)) ^ 2 = 1 := by
    rw [sp4Invol0, ← map_pow]
    have : longInv K 2 0 ^ 2 = 1 := by
      rw [longInv, ← map_pow]
      have h : (-1 : SL(2, K)) ^ 2 = 1 := by simp
      rw [h, map_one]
    rw [this, map_one]
  refine orderOf_eq_prime hsq fun h1 => ?_
  rw [sp4Invol0, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact longInv_not_mem h2 h1

theorem sp4Emb0_comm (A : SL(2, K)) (h2 : (2 : K) ≠ 0) :
    sp4Emb0 A * sp4Invol0 = sp4Invol0 * sp4Emb0 A := by
  have h1 : longBlock K 2 0 A ∈ longRootSp2 K 2 0 := by
    rw [longRootSp2_eq_suppGroup, ← range_longBlock]
    exact ⟨A, rfl⟩
  have hc := longInv_commute_longRootSp2 h2 0 0 h1
  rw [sp4Emb0, sp4Invol0, MonoidHom.comp_apply, ← map_mul, ← map_mul, hc.symm.eq]

theorem sp4Emb_comm0 (A : SL(2, K)) (h2 : (2 : K) ≠ 0) :
    sp4Emb A * sp4Invol0 = sp4Invol0 * sp4Emb A := by
  have h1 : longBlock K 2 1 A ∈ longRootSp2 K 2 1 := by
    rw [longRootSp2_eq_suppGroup, ← range_longBlock]
    exact ⟨A, rfl⟩
  have hc := longInv_commute_longRootSp2 h2 0 1 h1
  rw [sp4Emb, sp4Invol0, MonoidHom.comp_apply, ← map_mul, ← map_mul, hc.symm.eq]

theorem sp4Emb_comm_sp4Emb0 (A B : SL(2, K)) : sp4Emb A * sp4Emb0 B = sp4Emb0 B * sp4Emb A := by
  have h1 : longBlock K 2 1 A ∈ longRootSp2 K 2 1 := by
    rw [longRootSp2_eq_suppGroup, ← range_longBlock]
    exact ⟨A, rfl⟩
  have h2 : longBlock K 2 0 B ∈ longRootSp2 K 2 0 := by
    rw [longRootSp2_eq_suppGroup, ← range_longBlock]
    exact ⟨B, rfl⟩
  have hc := commute_longRootSp2 (show (1 : Fin 2) ≠ 0 by decide) h1 h2
  rw [sp4Emb, sp4Emb0, MonoidHom.comp_apply, MonoidHom.comp_apply, ← map_mul, ← map_mul, hc.eq]


theorem rankFourCover_psp4_two {p e : ℕ} [Fact p.Prime] [Finite K] [CharP K p]
    (hK : Nat.card K = p ^ e) (hp2 : p ≠ 2) (he : 2 ≤ e) (h9 : Nat.card K ≠ 9) :
    RankFourCover p (StatedProj (StatedSp 2 K)) := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq K p]; exact hp2)
  exact rankFourCover_of_two_SL2 hK hK hp2 he he h9 h9 sp4Emb sp4Emb0 sp4Emb_injective
    sp4Emb0_injective sp4Emb_comm_sp4Emb0 (orderOf_sp4Invol0 h2) (fun a => sp4Emb_comm0 a h2)
    (fun b => sp4Emb0_comm b h2)

end CFSG.RankThree.PartOne.SRC
