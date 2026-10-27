module

public import CFSG.RankThree.GF2n.Smith81.S81UElem
public import CFSG.RankThree.GF2n.Smith81.TiLemmaC

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80

@[expose] def NormQuotE3UStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), Smith1981Below (Nat.card G) →
    SmithECfg M Q Z B → InCaseE3U M Q Z B → ∀ E : Subgroup G, E ≤ H0 M Z → IsPGroup 2 E →
      Nat.card ↥E ≤ 2 * Nat.card ↥(E ⊓ Lgen M (LB M Q B))

@[expose] def Smith28aE3UStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), Smith1981Below (Nat.card G) →
    SmithECfg M Q Z B → InCaseE3U M Q Z B → ∀ (X : Subgroup G) (x : G), Sit M Q Z X x →
      Q ⊓ QB X ≠ ⊥

section Eight

variable {G : Type} [Group G] [Finite G]

theorem smith28aE3U_of_normQuot (hN : NormQuotE3UStatement) (hB : ElemBoundE3UStatement) :
    Smith28aE3UStatement := by
  intro G _ _ M Q Z B IH hc h3U X x hs hQ
  haveI := hc.ctx.normal_Q_in_M
  obtain ⟨n, m, hw, hnm⟩ := hc.e.exists_width
  have h115 := smith115Statement_holds G M Q Z X x hs n hw hQ
  have hel : IsElemAbelian 2 (Lx M X) := h115.1.mono le_sup_right
  have hLQ : Lx M X ⊓ Q = ⊥ := by
    refine eq_bot_iff.mpr fun g hg => ?_
    have h1 : g ∈ Q ⊓ QB X := ⟨hg.2, hg.1.1⟩
    rw [hQ] at h1
    exact h1
  have hcard : Nat.card Z ^ n ≤ Nat.card ↥(Lx M X) := hs.card_Lx_ge hw
  have hLH0 : Lx M X ≤ H0 M Z := Lx_le_H0 hs (smith_1_12 hs)
  have hL2 : IsPGroup 2 (Lx M X) :=
    ((IsZConjugate.isPGroup_QB hs.hyp hs.conj).to_le (inf_le_left : Lx M X ≤ QB X))
  have hidx := hN G M Q Z B IH hc h3U (Lx M X) hLH0 hL2
  have hSM : Lx M X ⊓ Lgen M (LB M Q B) ≤ M := inf_le_left.trans inf_le_right
  have hSQ : (Lx M X ⊓ Lgen M (LB M Q B)) ⊓ Q = ⊥ :=
    eq_bot_iff.mpr fun g hg => by
      have : g ∈ Lx M X ⊓ Q := ⟨hg.1.1, hg.2⟩
      rw [hLQ] at this
      exact this
  have hSel : IsElemAbelian 2 (Lx M X ⊓ Lgen M (LB M Q B)) := hel.mono inf_le_left
  have hle : bar M Q (Lx M X ⊓ Lgen M (LB M Q B)) ≤ bar M Q (Lgen M (LB M Q B)) :=
    Subgroup.map_mono fun y hy => hy.2
  have hbound := hB G M Q Z B IH hc h3U n hw (bar M Q (Lx M X ⊓ Lgen M (LB M Q B))) hle
    ((hSel.subgroupOf M).map _)
  rw [card_bar_eq_of_inf_eq_bot hSM hSQ] at hbound
  have hq : 4 ≤ Nat.card Z := hc.ctx.hyp.q4
  have hn : 1 ≤ n := by have := hnm.ten_le; omega
  have hpow : Nat.card Z ^ n = Nat.card Z * Nat.card Z ^ (n - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hpos : 0 < Nat.card Z ^ (n - 1) := pow_pos (by omega) _
  nlinarith

end Eight

end CFSG.RankThree.GF2n.Smith81
