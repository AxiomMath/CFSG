module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970API
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_18
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27Infra
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.MinimalCounterexample
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.FinalTheorem
import Mathlib.GroupTheory.Transfer
import Mathlib.GroupTheory.Complement
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The layer `E(M)` is trivial in Lemma 2.7

The paper's first consequence of the divisible-by-four step is `E(M)=1`:
the layer is a normal subgroup of `M`, every component is quasisimple (hence
of order divisible by four), so the divisible-by-four step puts `t` in it,
contradicting `t ∉ E(M)`.

The quasisimple four-divisibility fact is proved here from scratch: a
quasisimple group is perfect and non-solvable, so it has even order; if its
order were `2 · odd`, its cyclic Sylow `2`-subgroup would have a normal
complement (Burnside transfer, `IsCyclic.isComplement'`), making the group
solvable-by-abelian with a perfect subgroup forcing the complement to be the
whole group, an odd-order contradiction.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

private local instance fact_prime_two : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- A quasisimple group has order divisible by four. -/
public theorem isQuasisimple_four_dvd_card {Q : Type u} [Group Q] [Finite Q]
    (hQ : IsQuasisimple Q) : 4 ∣ Nat.card Q := by
  classical
  have : Nontrivial Q := hQ.1
  have : Group.IsPerfect Q := (Group.isPerfect_def).2 hQ.2.1
  have h2 : 2 ∣ Nat.card Q := by
    by_contra hnot
    have hodd : Odd (Nat.card Q) := by
      rw [← Nat.not_even_iff_odd]
      intro heven
      exact hnot (even_iff_two_dvd.mp heven)
    have hsolv : IsSolvable Q := odd_order_theorem Q hodd
    exact Group.IsPerfect.not_isSolvable Q hsolv
  by_contra hnot4
  have hodd2 : Odd (Nat.card Q / 2) := by
    rcases h2 with ⟨m, hm⟩
    have hmodd : Odd m := by
      by_contra hmeven
      have hEven : Even m := Nat.not_odd_iff_even.mp hmeven
      rcases hEven with ⟨k, hk⟩
      have h4 : 4 ∣ Nat.card Q := by
        rw [hm, hk]
        use k
        ring
      exact hnot4 h4
    rwa [hm, Nat.mul_div_right _ (by norm_num : 0 < 2)]
  let P : Sylow 2 Q := Classical.choice Sylow.nonempty
  have hPne : (P : Subgroup Q) ≠ ⊥ := Sylow.ne_bot_of_dvd_card (G := Q) P h2
  rcases (IsPGroup.iff_card (p := 2) (G := ↥(P : Subgroup Q))).mp P.isPGroup' with
    ⟨n, hPn⟩
  have hPn_ne : n ≠ 0 := by
    intro h0
    rw [h0] at hPn
    have hPcard1 : Nat.card (↥(P : Subgroup Q)) = 1 := by simpa using hPn
    exact hPne ((Subgroup.eq_bot_iff_card (H := (P : Subgroup Q))).2 hPcard1)
  have hPn_le : n ≤ 1 := by
    by_contra h
    have h2le : 2 ≤ n := by omega
    have h4P : 4 ∣ Nat.card (↥(P : Subgroup Q)) := by
      rw [hPn]
      exact pow_dvd_pow 2 h2le
    have h4Q : 4 ∣ Nat.card Q :=
      h4P.trans (Subgroup.card_subgroup_dvd_card (P : Subgroup Q))
    exact hnot4 h4Q
  have hn1 : n = 1 := by omega
  have hPcard2 : Nat.card (↥(P : Subgroup Q)) = 2 := by
    rw [hPn, hn1]
    norm_num
  have hPcyc : IsCyclic P := isCyclic_of_prime_card (p := 2) hPcard2
  have hminFac : (Nat.card Q).minFac = 2 :=
    (Nat.minFac_eq_two_iff (Nat.card Q)).2 h2
  have hcomp :
      (MonoidHom.transferSylow P
        (IsCyclic.normalizer_le_centralizer hminFac hPcyc)).ker.IsComplement'
        (P : Subgroup Q) :=
    IsCyclic.isComplement' hminFac hPcyc
  let N : Subgroup Q :=
    (MonoidHom.transferSylow P
      (IsCyclic.normalizer_le_centralizer hminFac hPcyc)).ker
  have : N.Normal := by dsimp [N]; infer_instance
  have hNodd : Odd (Nat.card (↥N)) := by
    rcases h2 with ⟨m, hm⟩
    have hmodd : Odd m := by
      by_contra hmeven
      have hEven : Even m := Nat.not_odd_iff_even.mp hmeven
      rcases hEven with ⟨k, hk⟩
      have h4 : 4 ∣ Nat.card Q := by
        rw [hm, hk]
        use k
        ring
      exact hnot4 h4
    have hNm : Nat.card (↥N) = m := by
      have hNmul : Nat.card (↥N) * 2 = 2 * m := by
        calc
          Nat.card (↥N) * 2 = Nat.card (↥N) * Nat.card (↥(P : Subgroup Q)) := by rw [hPcard2]
          _ = Nat.card Q := hcomp.card_mul
          _ = 2 * m := hm
      exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2)
        (by simpa [mul_comm] using hNmul)
    rwa [hNm]
  have hQN : Q ⧸ N ≃* ↥(P : Subgroup Q) := hcomp.symm.QuotientMulEquiv
  have hPcomm : IsMulCommutative (↥(P : Subgroup Q)) :=
    (isCyclic_of_prime_card (p := 2) hPcard2).isMulCommutative
  have hQNcomm : IsMulCommutative (Q ⧸ N) :=
    by
      simpa using isMulCommutative_of_surjective (f := hQN.symm.toMonoidHom)
        hQN.symm.toEquiv.surjective hPcomm
  have hcomm_le : commutator Q ≤ N := by
    rw [← Subgroup.Normal.quotient_commutative_iff_commutator_le]
    exact hQNcomm
  have htop_le : (⊤ : Subgroup Q) ≤ N := by
    rw [← hQ.2.1]
    exact hcomm_le
  have hNtop : N = ⊤ := le_antisymm le_top htop_le
  have hQodd : Odd (Nat.card Q) := by
    rw [show Nat.card Q = Nat.card (↥N) by
      rw [hNtop]
      simp]
    exact hNodd
  exact (Nat.not_odd_iff_even.mpr (even_iff_two_dvd.mpr h2)) hQodd

/-- The layer is nontrivial iff it contains a nontrivial component. -/
private theorem componentLayerOf_ne_bot_iff {G : Type u} [Group G]
    (N : Subgroup G) :
    componentLayerOf N ≠ ⊥ ↔ ∃ S : Subgroup G, IsComponentOf S N ∧ S ≠ ⊥ := by
  constructor
  · intro hE
    by_contra hnone
    push_neg at hnone
    apply hE
    apply le_bot_iff.mp
    rw [componentLayerOf]
    refine sSup_le ?_
    intro S hS
    have hSbot : S = ⊥ := hnone S hS
    simpa [hSbot]
  · rintro ⟨S, hS, hSne⟩ hbot
    have hSle : S ≤ componentLayerOf N := le_sSup hS
    have hSbot' : S = ⊥ := le_bot_iff.mp (hSle.trans (le_of_eq hbot))
    exact hSne hSbot'

/-- Lemma 2.7's `E(M)=1`: the divisible-by-four step puts `t` into every
nontrivial component layer, contradicting `t ∉ componentLayerOf M`. -/
public theorem componentLayerOf_eq_bot_of_Lemma27Hypothesis
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (M : Subgroup G)
    (hM : Lemma27Hypothesis c M) (h26 : CentralizerStructure c) :
    componentLayerOf M = ⊥ := by
  classical
  have hEt : c.t ∉ componentLayerOf M := hM.2.2.2.1
  by_contra hEne
  rcases (componentLayerOf_ne_bot_iff M).1 hEne with ⟨S, hS, hSne⟩
  have hS4 : 4 ∣ Nat.card (↥S) := isQuasisimple_four_dvd_card hS.2.2
  let E : Subgroup G := componentLayerOf M
  have hSE : S ≤ E := le_sSup hS
  have hE4 : 4 ∣ Nat.card (↥E) :=
    hS4.trans (Subgroup.card_dvd_of_le hSE)
  have hEM : E ≤ M := (componentLayerOf_isNormalIn M).1
  let EN : Subgroup (↥M) := E.subgroupOf M
  have hEN4 : 4 ∣ Nat.card EN := by
    have e : EN ≃* E := Subgroup.subgroupOfEquivOfLe hEM
    rw [show Nat.card EN = Nat.card (↥E) by exact Nat.card_congr e.toEquiv]
    exact hE4
  have hENnormal : EN.Normal := by
    apply (Subgroup.normal_subgroupOf_iff hEM).2
    intro h k hh hk
    exact (componentLayerOf_isNormalIn M).2 k hk h hh
  have htEN : c.t ∈ EN.map M.subtype :=
    normal_subgroup_of_card_div_four_contains_t hmin c M hM h26
      (N := EN) hENnormal hEN4
  have htE : c.t ∈ E := by
    have hmap : EN.map M.subtype = E := Subgroup.map_subgroupOf_eq_of_le hEM
    simpa [hmap] using htEN
  exact hEt htE

end CFSG.GorensteinWalter
