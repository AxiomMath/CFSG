module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec118Center
public import CFSG.RankThree.GF2n.Stroth80.Sec11CM
public import CFSG.ClassicalGroups.Symplectic.Sp4GraphA2
import CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194SpBlocks

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped Matrix

variable {G : Type} [Group G] {M Q Z B : Subgroup G}

theorem image_mul_self_eq_one_and_ne_one [Finite G]
    [(Q.subgroupOf M).Normal] {a : ↥M} {h : (a : G) ∈ LB M Q B ∧ IsA2 Q Z (a : G)}
    {H : Type*} [Group H] (ψ : ↥(Xbar M Q Z B) ≃* H) :
    ψ ⟨QuotientGroup.mk a, mk_mem_Xbar_of_LB M Q Z B a h.1 h.2⟩ *
      ψ ⟨QuotientGroup.mk a, mk_mem_Xbar_of_LB M Q Z B a h.1 h.2⟩ = 1 ∧
    ψ ⟨QuotientGroup.mk a, mk_mem_Xbar_of_LB M Q Z B a h.1 h.2⟩ ≠ 1 := by
  have h2 : orderOf (QuotientGroup.mk a : Mbar M Q) = 2 :=
    Ctx.orderOf_eq_two_of_mem_A2Set (Ctx.mk_mem_A2Set a.2 h.2)
  have hx : orderOf (⟨QuotientGroup.mk a, mk_mem_Xbar_of_LB M Q Z B a h.1 h.2⟩ :
      ↥(Xbar M Q Z B)) = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact h2
  have hψ : orderOf (ψ ⟨QuotientGroup.mk a, mk_mem_Xbar_of_LB M Q Z B a h.1 h.2⟩) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact hx
  refine ⟨?_, fun h1 => ?_⟩
  · have := pow_orderOf_eq_one
      (ψ ⟨QuotientGroup.mk a, mk_mem_Xbar_of_LB M Q Z B a h.1 h.2⟩)
    rwa [hψ, sq] at this
  · rw [h1, orderOf_one] at hψ
    exact absurd hψ (by norm_num)

private theorem one_le_rank_of_ne_zero {m n : Type} [Fintype m] [Fintype n] [DecidableEq n]
    {K : Type} [Field K] {N : Matrix m n K} (hN : N ≠ 0) : 1 ≤ N.rank := by
  rw [Matrix.rank_eq_finrank_span_cols]
  obtain ⟨i, j, hij⟩ : ∃ i j, N i j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hN (by ext i j; exact hcon i j)
  have hcol : N.col j ≠ 0 := fun h => hij (congrFun h i)
  have hmem : N.col j ∈ Submodule.span K (Set.range N.col) := Submodule.subset_span ⟨j, rfl⟩
  exact Module.finrank_pos_iff_exists_ne_zero.mpr
    ⟨⟨N.col j, hmem⟩, fun h => hcol (congrArg Subtype.val h)⟩

section Certificates


theorem Ctx.cmSpTransvAt_of_rank_eq_one [Finite G]
    [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {m x : ℕ}
    (hLm : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSp m 2 x)
    {a : ↥M} {h : (a : G) ∈ LB M Q B ∧ IsA2 Q Z (a : G)}
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ x)
    (ψ : ↥(Xbar M Q Z B) ≃* StatedSp m K)
    (hr : Matrix.rank ((((ψ ⟨QuotientGroup.mk a, mk_mem_Xbar_of_LB M Q Z B a h.1 h.2⟩ :
      StatedSp m K) : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) - 1) = 1) :
    CMSpTransvAt M Q Z B m x a h := by
  have hcenter := hc.center_Xbar_eq_bot_of_lieModel_psp hLm
  let hquot : XbarMod M Q Z B ≃* ↥(Xbar M Q Z B) :=
    (QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot
  exact ⟨K, inferInstance, inferInstance, hK,
    hquot.trans (ψ.trans CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.statedProjEquivSp.symm),
    ψ ⟨QuotientGroup.mk a, mk_mem_Xbar_of_LB M Q Z B a h.1 h.2⟩, hr, rfl⟩

theorem Ctx.rank_ne_one_of_not_cmSpTransvAt [Finite G]
    [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {m x : ℕ}
    (hLm : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSp m 2 x)
    {a : ↥M} {h : (a : G) ∈ LB M Q B ∧ IsA2 Q Z (a : G)}
    (hnT : ¬ CMSpTransvAt M Q Z B m x a h)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ x)
    (ψ : ↥(Xbar M Q Z B) ≃* StatedSp m K) :
    Matrix.rank ((((ψ ⟨QuotientGroup.mk a, mk_mem_Xbar_of_LB M Q Z B a h.1 h.2⟩ :
      StatedSp m K) : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) - 1) ≠ 1 :=
  fun hr => hnT (hc.cmSpTransvAt_of_rank_eq_one hLm hK ψ hr)

theorem Ctx.type_c2_of_not_cmSpTransvAt [Finite G]
    [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {x : ℕ}
    (hLm : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSp 2 2 x)
    {a : ↥M} {h : (a : G) ∈ LB M Q B ∧ IsA2 Q Z (a : G)}
    (hnT : ¬ CMSpTransvAt M Q Z B 2 x a h)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ x)
    (ψ : ↥(Xbar M Q Z B) ≃* StatedSp 2 K) :
    Matrix.rank ((((ψ ⟨QuotientGroup.mk a, mk_mem_Xbar_of_LB M Q Z B a h.1 h.2⟩ :
      StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) - 1) = 2 ∧
    ∃ v, CFSG.ClassicalGroups.Symplectic.spForm 2 K v
      (((((ψ ⟨QuotientGroup.mk a, mk_mem_Xbar_of_LB M Q Z B a h.1 h.2⟩ : StatedSp 2 K) :
        GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) - 1) *ᵥ v) ≠ 0 := by
  obtain ⟨hg2, hg1⟩ := image_mul_self_eq_one_and_ne_one (h := h) ψ
  have hne1 := hc.rank_ne_one_of_not_cmSpTransvAt hLm hnT hK ψ
  set g : StatedSp 2 K := ψ ⟨QuotientGroup.mk a, mk_mem_Xbar_of_LB M Q Z B a h.1 h.2⟩ with hg
  have hgm : ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = 1 := by
    rw [← Units.val_mul, ← Subgroup.coe_mul, hg2]
    rfl
  have hle := CFSG.ClassicalGroups.Symplectic.rank_sub_one_le_two_of_mul_self_eq_one hgm
  have hge : 1 ≤ Matrix.rank (((g : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) - 1) := by
    refine one_le_rank_of_ne_zero (sub_ne_zero.mpr fun h1 => hg1 ?_)
    exact Subtype.ext (Units.ext h1)
  have hrk2 : Matrix.rank (((g : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) - 1) = 2 := by omega
  refine ⟨hrk2, ?_⟩
  by_contra hcon
  push Not at hcon
  have hτ := CFSG.ClassicalGroups.Symplectic.tauSp_sub_one_rank_eq_one_of_a2 g hg2 hrk2 hcon
  exact hnT (hc.cmSpTransvAt_of_rank_eq_one hLm hK
    (ψ.trans CFSG.QuasithinUnique.Lin2.Five.tauEquiv) hτ)

end Certificates

end CFSG.RankThree.GF2n.Stroth80
