module

public import CFSG.Quasithin.Background.ONanE68LieFacts
public import CFSG.Quasithin.Background.ONanE68RankOneModel
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.BorelFacts
public import CFSG.Quasithin.Background.ONanE68RankOneU3
import CFSG.Quasithin.Background.ONanE68RankOneCore
import CFSG.Quasithin.Background.ONanE68RankOneOver
import CFSG.Quasithin.Background.ONanE68RankOneSz
import CFSG.Timmesfeld.Bridge.Asc72Bender

public section

namespace CFSG.Quasithin.E6.E68Proof

open CFSG.Open

namespace RankOne

open CFSG.ProperTwoGeneratedCore.TheoremC

variable {S : Type} [Group S] [Finite S]

structure Basic (q k : ℕ) (Q : Sylow 2 S) : Prop where
  borel : fusionBenderBorel S q k
  facts : BenderBorelFacts S (Q : Subgroup S)
  cent : ∀ y : S, (∀ p ∈ (Q : Subgroup S), y * p = p * y) → y ∈ (Q : Subgroup S)

theorem basic_of_model {q k : ℕ} (hM : ModelOf S q k)
    (Q : Sylow 2 S) : Basic q k Q := by
  have hIB := hM.isBenderGroup
  have hF := Timmesfeld.Bridge.Asc72.IsBenderGroup.benderBorelFacts hIB Q
  have hsimple := Timmesfeld.Bridge.Asc72.IsBenderGroup.isSimpleGroup hIB
  obtain ⟨a, b, hab⟩ := Timmesfeld.Bridge.Asc72.IsBenderGroup.exists_not_commute hIB
  have hZ : Subgroup.center S = ⊥ := by
    have hN : (Subgroup.center S).Normal := inferInstance
    rcases hN.eq_bot_or_eq_top with h0 | h0
    · exact h0
    · exact absurd (Subgroup.mem_center_iff.mp (h0 ▸ Subgroup.mem_top a : a ∈ Subgroup.center S)
        b).symm hab
  exact ⟨hM.fusionBenderBorel, hF, centralizer_le_of_facts hF hZ⟩

theorem order_three_of_k_one {q : ℕ} {Q : Sylow 2 S} (hb : Basic q 1 Q) (hq4 : 4 ≤ q) :
    ∀ c ∈ Subgroup.normalizer ((Q : Subgroup S) : Set S), orderOf c = 3 →
      4 < ((Q : Subgroup S) ⊓ Subgroup.centralizer ({c} : Set S)).relIndex (Q : Subgroup S) ∨
        (Nat.card (Q : Subgroup S) = 4 ∧
          (Q : Subgroup S) ⊓ Subgroup.centralizer ({c} : Set S) = ⊥) := by
  obtain ⟨D, hDcyc, -, hQD, hsup, htrans⟩ := exists_cyclic_torus hb.borel Q hb.facts
  have hcard : Nat.card (Q : Subgroup S) = q := by simpa using (hb.borel Q).2.2.2.2
  have hZ : Subgroup.center (Q : Subgroup S) = ⊤ := by
    rw [← Subgroup.card_eq_iff_eq_top, (hb.borel Q).2.2.2.1, hcard]
  have hab : ∀ x ∈ (Q : Subgroup S), ∀ y ∈ (Q : Subgroup S), x * y = y * x := by
    intro x hx y hy
    have := Subgroup.mem_center_iff.mp (hZ ▸ Subgroup.mem_top (⟨x, hx⟩ : (Q : Subgroup S))) ⟨y, hy⟩
    exact congrArg Subtype.val this.symm
  intro c hc hc3
  have hbot := inf_centralizer_eq_bot_of_abelian hDcyc hQD hsup hab htrans hb.cent hc hc3
  rw [hbot, Subgroup.relIndex_bot_left, hcard]
  by_cases h4 : q = 4
  · exact Or.inr ⟨h4, rfl⟩
  · exact Or.inl (by omega)

theorem order_three_of_bound {q : ℕ} {P : Subgroup S} (hq4 : 4 ≤ q) (hP : Nat.card P = q ^ 3)
    (h : OTB P q) : ∀ c ∈ Subgroup.normalizer (P : Set S), orderOf c = 3 →
      4 < (P ⊓ Subgroup.centralizer ({c} : Set S)).relIndex P ∨
        (Nat.card P = 4 ∧ P ⊓ Subgroup.centralizer ({c} : Set S) = ⊥) := by
  intro c hc hc3
  left
  have hmul := Subgroup.relIndex_mul_card (P ⊓ Subgroup.centralizer ({c} : Set S)) P
  rw [inf_of_le_left inf_le_left, hP] at hmul
  have hle := h c hc hc3
  have hpos : 0 < Nat.card ↥(P ⊓ Subgroup.centralizer ({c} : Set S)) := Nat.card_pos
  by_contra hcon
  push Not at hcon
  have h1 : (P ⊓ Subgroup.centralizer ({c} : Set S)).relIndex P *
      Nat.card ↥(P ⊓ Subgroup.centralizer ({c} : Set S)) ≤ 4 * q :=
    Nat.mul_le_mul hcon hle
  have h2 : 4 * q < q ^ 3 := by
    have : 4 * q < q * q * q := by nlinarith
    calc 4 * q < q * q * q := this
      _ = q ^ 3 := by ring
  omega

end RankOne

theorem e68RankOneData_holds
    (S : Type) [Group S] [Finite S] (n : ℕ)
    (h : (2 ≤ n ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel S
        CFSG.Assembly.LowTwoRank.StatedLieTag.PSL 2 2 n) ∨
      (Odd n ∧ 3 ≤ n ∧ CFSG.Blueprint.SuzukiModel S 2 n) ∨
      (2 ≤ n ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel S
        CFSG.Assembly.LowTwoRank.StatedLieTag.PSU 3 2 n))
    (P : Subgroup S) (hP : CFSG.QuasithinUnique.IsSylowTwoOf P ⊤) : E68RankOneData P n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, rfl⟩ : ∃ Q : Sylow 2 S, (Q : Subgroup S) = P :=
    ⟨IsPGroup.toSylow hP.2.1 (by
      have h := hP.2.2
      rwa [← Subgroup.relIndex, Subgroup.relIndex_top_right] at h), rfl⟩
  have key : ∀ {k : ℕ}, ModelOf S (2 ^ n) k →
      (∀ c ∈ Subgroup.normalizer ((Q : Subgroup S) : Set S), orderOf c = 3 →
        4 < ((Q : Subgroup S) ⊓ Subgroup.centralizer ({c} : Set S)).relIndex (Q : Subgroup S) ∨
          (Nat.card (Q : Subgroup S) = 4 ∧
            (Q : Subgroup S) ⊓ Subgroup.centralizer ({c} : Set S) = ⊥)) →
      E68RankOneData (Q : Subgroup S) n := by
    intro k hM hord
    have hb := RankOne.basic_of_model hM Q
    obtain ⟨D, hDcyc, -, -, hsup⟩ := (hb.borel Q).2.1
    exact
      { centralizer_le := hb.cent
        quot_comm := RankOne.quot_comm_of_sup hDcyc hsup
        order_three := hord
        card_root := RankOne.card_omegaCenter hb.borel Q
        singer := RankOne.singer_of_torus hb.borel Q hb.facts
        bender := fun Y hQY hY => RankOne.normalizer_of_proper_overgroup hM Q hb.cent hQY hY }
  rcases h with ⟨hn, hPSL⟩ | ⟨-, -, hSz⟩ | ⟨hn, hPSU⟩
  · have hM := modelOf_of_stated_psl hn hPSL
    exact key hM (RankOne.order_three_of_k_one (RankOne.basic_of_model hM Q)
      (hM.params.1))
  · have hM := modelOf_of_suzuki hSz
    refine key hM fun c _ hc3 => ?_
    exfalso
    obtain ⟨a, ha, ⟨e⟩⟩ := hM.sz
    have h3 : 3 ∣ Nat.card (Sz a) := by
      rw [← Nat.card_congr e.toEquiv]
      exact hc3 ▸ orderOf_dvd_natCard c
    exact RankOne.not_three_dvd_card_sz ha h3
  · have hM := modelOf_of_stated_psu hn hPSU
    obtain ⟨f, hf, hq, ⟨e⟩⟩ := hM.psu
    have hfn : f = n := Nat.pow_right_injective (le_refl 2) hq.symm
    subst hfn
    refine key hM (RankOne.order_three_of_bound hM.params.1 ?_ ?_)
    · simpa using (RankOne.basic_of_model hM Q).borel Q |>.2.2.2.2
    · exact RankOne.orderThreeBound_psu hf e Q

end CFSG.Quasithin.E6.E68Proof
