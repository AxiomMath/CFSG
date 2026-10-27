module

public import CFSG.RankThree.SubgroupLists.MitchellFrameGroup
public import CFSG.RankThree.SubgroupLists.SymplecticTwoRotations
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.RankThree.SubgroupLists

open Matrix CFSG.Assembly.LowTwoRank Module
open scoped MatrixGroups

local notation "V₄" => Fin 2 ⊕ Fin 2

local notation "⟪" x "⟫" => Units.val x

variable {K K' : Type} [Field K] [Field K']

theorem map_ker_eq_bot_or_orders {X P Q : Type*} [Group X] [Group P] [Group Q] (α : X →* Q)
    (β : X →* P) (e : β.range ≃* alternatingGroup (Fin 5)) :
    (∀ x ∈ α.ker, β x = 1) ∨
      ((∃ x ∈ α.ker, orderOf (β x) = 5) ∧ ∃ x ∈ α.ker, orderOf (β x) = 2) := by
  haveI : IsSimpleGroup β.range := e.isSimpleGroup
  haveI : Finite β.range := Finite.of_equiv _ e.symm.toEquiv
  have hnorm : (α.ker.map β.rangeRestrict).Normal :=
    α.normal_ker.map _ β.rangeRestrict_surjective
  have hcard : Nat.card β.range = 60 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    simp [Nat.factorial]
  rcases Subgroup.Normal.eq_bot_or_eq_top (α.ker.map β.rangeRestrict) with h | h
  · left
    intro x hx
    have hx' : β.rangeRestrict x ∈ α.ker.map β.rangeRestrict := Subgroup.mem_map_of_mem _ hx
    rw [h, Subgroup.mem_bot] at hx'
    exact congrArg Subtype.val hx'
  · right
    have key : ∀ q : ℕ, q.Prime → q ∣ 60 → ∃ x ∈ α.ker, orderOf (β x) = q := by
      intro q hq hdvd
      haveI := Fact.mk hq
      obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' q (hcard ▸ hdvd)
      have hy' : y ∈ α.ker.map β.rangeRestrict := h ▸ Subgroup.mem_top y
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy'
      exact ⟨x, hx, by rw [← hy, ← Subgroup.orderOf_coe]; rfl⟩
    exact ⟨key 5 (by norm_num) (by norm_num), key 2 (by norm_num) (by norm_num)⟩

@[expose] noncomputable def framePlusBar (h2 : (2 : K') ≠ 0) (φ : K →+* K') (k : GL V₄ K')
    (X : Subgroup (GL V₄ K)) (hX : ∀ g ∈ X, frameHom φ k g ∈ stdCent K') :
    X →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K' :=
  (QuotientGroup.mk' (Subgroup.center SL(2, K'))).comp ((plusHom h2).comp
    (((frameHom φ k).comp X.subtype).codRestrict (stdCent K') fun g => hX g g.2))

theorem frameMat_pow (φ : K →+* K') (k : GL V₄ K') (g : GL V₄ K) (j : ℕ) :
    frameMat φ k ⟪g ^ j⟫ = frameMat φ k ⟪g⟫ ^ j := by
  rw [← coe_frameHom, ← coe_frameHom, map_pow, Units.val_pow_eq_pow_val]

theorem swap_conj_comm_iff (M : Matrix V₄ V₄ K') :
    swapMat * M * swapMat * tStdMat = tStdMat * (swapMat * M * swapMat) ↔
      M * tStdMat = tStdMat * M := by
  have hss : ∀ X : Matrix V₄ V₄ K', swapMat * (swapMat * X) = X := fun X => by
    rw [← Matrix.mul_assoc, swapMat_mul_self, Matrix.one_mul]
  have hT : (swapMat : Matrix V₄ V₄ K') * tStdMat = -(tStdMat * swapMat) := by
    calc (swapMat : Matrix V₄ V₄ K') * tStdMat = swapMat * tStdMat * swapMat * swapMat := by
          rw [Matrix.mul_assoc _ swapMat swapMat, swapMat_mul_self, Matrix.mul_one]
      _ = -(tStdMat * swapMat) := by rw [swap_conj_tStdMat, Matrix.neg_mul]
  have hT' : (tStdMat : Matrix V₄ V₄ K') * swapMat = -(swapMat * tStdMat) := by
    rw [hT, neg_neg]
  have e1 : swapMat * M * swapMat * tStdMat = -(swapMat * (M * tStdMat) * swapMat) := by
    simp only [Matrix.mul_assoc, hT, Matrix.mul_neg]
  have e2 : tStdMat * (swapMat * M * swapMat) = -(swapMat * (tStdMat * M) * swapMat) := by
    rw [← Matrix.mul_assoc tStdMat, ← Matrix.mul_assoc tStdMat, hT', Matrix.neg_mul,
      Matrix.neg_mul]
    simp only [Matrix.mul_assoc]
  have hconj : ∀ X Y : Matrix V₄ V₄ K', swapMat * X * swapMat = swapMat * Y * swapMat → X = Y := by
    intro X Y h
    have := congrArg (fun Z => swapMat * Z * swapMat) h
    simpa [Matrix.mul_assoc, hss, swapMat_mul_self] using this
  rw [e1, e2, neg_inj]
  exact ⟨hconj _ _, fun h => by rw [h]⟩

theorem frameHom_swap_mem_stdCent_iff (φ : K →+* K') {k : GL V₄ K'} (hk : k ∈ StatedSp 2 K')
    {G : Subgroup (GL V₄ K)} (hGS : G ≤ StatedSp 2 K) {g : GL V₄ K} (hg : g ∈ G) :
    frameHom φ (k * swapGL) g ∈ stdCent K' ↔ frameHom φ k g ∈ stdCent K' := by
  have h1 := frameHom_mem_statedSp φ (mul_mem hk swapGL_mem) (hGS hg)
  have h2 := frameHom_mem_statedSp φ hk (hGS hg)
  rw [mem_stdCent, mem_stdCent, coe_frameHom, coe_frameHom, frameMat_mul_swap,
    swap_conj_comm_iff]
  simp only [h1, h2, true_and]

section Finite

variable [Finite K']

theorem framePlusBar_eq_one_iff (h2 : (2 : K') ≠ 0) (φ : K →+* K') (k : GL V₄ K')
    {X : Subgroup (GL V₄ K)} (hX : ∀ g ∈ X, frameHom φ k g ∈ stdCent K') (g : X) :
    framePlusBar h2 φ k X hX g = 1 ↔ plusBlock (frameMat φ k ⟪(g : GL V₄ K)⟫) = 1 ∨
      plusBlock (frameMat φ k ⟪(g : GL V₄ K)⟫) = -1 := by
  have h := plusBar_eq_one_iff h2 (G := ⊤) (x := frameHom φ k g) (Subgroup.mem_top _)
    (hX g g.2)
  rw [coe_frameHom] at h
  rw [← h, Subtype.ext_iff]
  rfl

theorem framePlusBar_pow_eq_one_iff (h2 : (2 : K') ≠ 0) (φ : K →+* K') (k : GL V₄ K')
    {X : Subgroup (GL V₄ K)} (hX : ∀ g ∈ X, frameHom φ k g ∈ stdCent K') (g : X) (j : ℕ) :
    framePlusBar h2 φ k X hX g ^ j = 1 ↔ plusBlock (frameMat φ k ⟪(g : GL V₄ K)⟫) ^ j = 1 ∨
      plusBlock (frameMat φ k ⟪(g : GL V₄ K)⟫) ^ j = -1 := by
  have hc : frameMat φ k ⟪(g : GL V₄ K)⟫ * tStdMat = tStdMat * frameMat φ k ⟪(g : GL V₄ K)⟫ := by
    have := (mem_stdCent.mp (hX g g.2)).2
    rwa [coe_frameHom] at this
  rw [← map_pow, framePlusBar_eq_one_iff]
  simp only [Subgroup.coe_pow, frameMat_pow]
  rw [plusBlock_pow h2 hc]

end Finite

end CFSG.RankThree.SubgroupLists
