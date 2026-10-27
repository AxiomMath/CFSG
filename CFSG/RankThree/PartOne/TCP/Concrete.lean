module

public import CFSG.RankThree.PartOne.S11d.PSLVacuity
public import CFSG.RankThree.PartOne.S11d.FixedFactsPSp
public import CFSG.RankThree.PartOne.KF.F128Cls
public import CFSG.RankThree.PartOne.KF.ClsSpUpper
public import CFSG.RankThree.PartOne.TCP.Block

public section

namespace CFSG.RankThree.PartOne.TCP

open Subgroup CFSG CFSG.Blueprint CFSG.RankThree.PartOne CFSG.RankThree.PartOne.Sec66T
  CFSG.RankThree.PartOne.FieldFix
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedProj StatedSp)
open CFSG.LieType.CurtisTits (lieModel_of_mulEquiv)

theorem orderOf_natCast_pow_prime {p q Q : ℕ} (hp : p.Prime) (hQ : Q = q ^ p) :
    orderOf (Q : ZMod p) = orderOf (q : ZMod p) := by
  have : Fact p.Prime := ⟨hp⟩
  have h : (Q : ZMod p) = (q : ZMod p) := by
    rw [hQ]
    push_cast
    exact ZMod.pow_card _
  rw [h]

theorem blockDim_le_of_two_le_pRank {K : Type} [Field K] [Finite K] {p n : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpK : ¬ p ∣ Nat.card K) (h : 2 ≤ CFSG.pRank p ↥(StatedSp n K)) :
    blockDim (orderOf (Nat.card K : ZMod p)) ≤ n := by
  by_contra hlt
  push Not at hlt
  have hd0 := orderOf_natCast_pos hp hpK
  have h1 : CFSG.pRank p ↥(StatedSp n K) ≤ 1 := by
    refine pRank_statedSp_le_one hp hp2 hpK ?_
    unfold blockDim at hlt
    split_ifs at hlt ⊢ with hev
    · refine Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hd0).2 ?_)
      omega
    · refine Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hd0).2 ?_)
      omega
  omega

theorem psp_concrete {T : Type} [Group T] [Finite T] {p n f₀ : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hrank : LocalRankLeTwo p T) (hf₀ : 1 ≤ f₀) (hM : LieModel T .PSp n 2 (p * f₀))
    {α : MulAut T} (hαp : α ^ p = 1) (hαinn : α ∉ innerAut T) (hLR : LocalRankAut p T α)
    (hFix : FixModel .PSp n f₀ α) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (k₀ : Type) (_ : Field k₀) (_ : Finite k₀),
      2 ≤ n ∧ Nat.card K = 2 ^ (p * f₀) ∧ Nat.card k₀ = 2 ^ f₀ ∧
      Nonempty (T ≃* ↥(StatedSp n K)) ∧ Nonempty (↥(fixRes α) ≃* ↥(StatedSp n k₀)) := by
  classical
  have hFF : FixedFacts p α := tagFixedFacts_PSp T p hp hp5 hrank n f₀ hf₀ hM α hαp hαinn hLR
    hFix α hαp hαinn hLR ⟨1, fun h => by
      have := Int.eq_one_of_dvd_one (by positivity) h
      omega, by
      rw [zpow_one, mul_inv_cancel]
      exact (innerAut T).one_mem⟩
  have hC : StatedClassicalModel T .PSp n 2 (p * f₀) := (lieModel_classical_iff (by decide)).mp hM
  have hn2 : 2 ≤ n := hC.1.2.2.1
  have hZ : Subgroup.center ↥(fixRes α) = ⊥ := center_eq_bot_of_nonLocalized hFF.nonLocalized
  have hMF : LieModel ↥(fixRes α) .PSp n 2 f₀ := by
    rcases hFix with h | ⟨ht, -⟩
    · exact lieModel_of_mulEquiv (centerQuotientEquivSelf hZ) h
    · exact absurd ht (by decide)
  have hCF : StatedClassicalModel ↥(fixRes α) .PSp n 2 f₀ :=
    (lieModel_classical_iff (by decide)).mp hMF
  obtain ⟨-, K, _, _, hK, ⟨e0⟩⟩ := hC
  obtain ⟨-, k₀, _, _, hk₀, ⟨e1⟩⟩ := hCF
  have : CharP K 2 := K128.charP_two_of_card_eq_two_pow hK
  have : CharP k₀ 2 := K128.charP_two_of_card_eq_two_pow hk₀
  exact ⟨K, inferInstance, inferInstance, k₀, inferInstance, inferInstance, hn2, hK, hk₀,
    ⟨e0.trans (KFU.spEquivProj (by omega)).symm⟩, ⟨e1.trans (KFU.spEquivProj (by omega)).symm⟩⟩

end CFSG.RankThree.PartOne.TCP
