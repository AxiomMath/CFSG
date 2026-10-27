module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23Unique
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeY2
public import CFSG.LocalAnalysis.WeakClosure81.FourteenFour

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem c23_pRank_top_le_two {H : Type} [Group H] [Finite H] {p : ℕ} (hp : p.Prime)
    (h : ¬ p ^ 3 ∣ Nat.card H) : CFSG.Open.pRank p (⊤ : Subgroup H) ≤ 2 := by
  refine csSup_le ⟨0, ⊥, le_top, CFSG.Open.isElemAbelian_bot p, by simp⟩ ?_
  rintro k ⟨E, -, -, hE⟩
  by_contra hk
  exact h ((pow_dvd_pow p (by omega : 3 ≤ k)).trans (hE ▸ Subgroup.card_subgroup_dvd_card E))

theorem c23_evenRank_eq_three (D : Data G) (hx : DataExt D) (h115 : F11.R115 D) (h127 : R127 D)
    (h1217 : R1217 D) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D V₀ V L hV)
    (hc : Case167_2 D V₀ V hV L ∨ Case167_3 D V₀ V hV L) : CFSG.Open.evenRank G = 3 := by
  obtain ⟨p, hp, -, hpσ, -, hnd⟩ := c23_exists_prime D h1217 hS hc
  have h151 := hS.setting.hyp151
  have hpf := h151.hyp125.pairFacts
  haveI : ((F11.CTilde D.M V₀ V).subgroupOf D.M).Normal :=
    WeakClosure81.cTilde_subgroupOf_normal hV hpf.le_normalizer hpf.le_normalizer₀
  have hH11 : F11.Hyp11 D V₀ V := Hyp125.hyp11 h127 h151.hyp125
  obtain ⟨-, hle, -⟩ := h115 V₀ V hH11 (c23_card_v0_le_four D hS.setting.hyp16) p hpσ
  have hle' : CFSG.Open.pRank p D.M - 1 ≤
      CFSG.Open.pRank p (⊤ : Subgroup (F11.MBar11 D.M V₀ V)) := hle
  have hMs : D.M ≤ stabTil V₀ V := le_stabTil hpf.le_normalizer hpf.le_normalizer₀
  obtain ⟨e, -⟩ := s15_Three_barImage_equiv (D := D) (V₀ := V₀) (V := V) hV hMs
  have hcard : Nat.card (F11.MBar11 D.M V₀ V) = Nat.card (Mbar D.M V₀ V hV) :=
    Nat.card_congr e.toEquiv
  have h2 := c23_pRank_top_le_two (H := F11.MBar11 D.M V₀ V) hp (by rw [hcard]; exact hnd)
  have h3 := hx.three_le p hpσ
  refine le_antisymm ?_ D.standing.rank
  by_contra h
  have h4 := hx.four_le (not_le.1 h) p hpσ
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
