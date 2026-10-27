module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2Seventeen
public import CFSG.Quasithin.Background.SmithD321CaseI
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16h_delta15_eq_zero_of_inf_fixV (D : Data G) {V₀ V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (h0 : V₀ = ⊥)
    (h : wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L) = ⊥) : delta15 D.M V₀ V hV L = 0 := by
  unfold delta15
  rw [s16c167_v1Sub_eq_bot_of_inf_fixV D hV h0 h, bot_inf_eq]
  simp [mSub, rk]

private theorem s16h_odd_card_of_isElemAbelianOfRank_three {X : Type} [Group X] {r : ℕ}
    (h : IsElemAbelianOfRank 3 r X) : Odd (Nat.card X) := by
  have hcard : Nat.card X = 3 ^ r := by
    obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv]
    simp [Nat.card_eq_fintype_card, Fintype.card_multiplicative, Fintype.card_fun, ZMod.card]
  rw [hcard]
  exact Odd.pow (by decide : Odd 3)

private theorem s16h_odd_card_of_isElemAbelianOfRank_of_eq_three_or_seven {X : Type} [Group X]
    {p r : ℕ} (hp : p = 3 ∨ p = 7) (h : IsElemAbelianOfRank p r X) : Odd (Nat.card X) := by
  have hpnz : p ≠ 0 := by rcases hp with h | h <;> rw [h] <;> norm_num
  haveI : NeZero p := ⟨hpnz⟩
  have hpodd : Odd p := by rcases hp with h | h <;> rw [h] <;> decide
  have hcard : Nat.card X = p ^ r := by
    obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv]
    simp [Nat.card_eq_fintype_card, Fintype.card_multiplicative, Fintype.card_fun, ZMod.card]
  rw [hcard]
  exact hpodd.pow

private theorem s16h_odd_card_of_isPOnePlusTwo_three {X : Type} [Group X]
    (h : IsPOnePlusTwo 3 X) : Odd (Nat.card X) := by
  rw [h.2.1]
  decide

theorem s16h_odd_card_of_conc4_133 {W : Type} [CommGroup W] {A : Subgroup (MulAut W)}
    {t : MulAut W} {L : Subgroup (MulAut W)} (h : Conc4_133 A t L) : Odd (Nat.card ↥L) := by
  obtain ⟨p, hp, -, -, -, hcases⟩ := h
  rcases hcases with
    ⟨hc, -⟩ | ⟨hc, -⟩ | ⟨hc, -⟩ | ⟨hc, -⟩ | ⟨hc, -⟩ | h6 | ⟨hc, -⟩
  · rw [hc.2]; decide
  · rw [hc.2]; decide
  · exact s16h_odd_card_of_isPOnePlusTwo_three hc
  · exact s16h_odd_card_of_isElemAbelianOfRank_three hc
  · rw [hc.2]; decide
  · obtain ⟨r, m, hpr, -, hab, -, -⟩ := h6
    exact s16h_odd_card_of_isElemAbelianOfRank_of_eq_three_or_seven
      (by rcases hpr with ⟨hp3, -⟩ | ⟨hp7, -⟩
          · exact Or.inl hp3
          · exact Or.inr hp7) hab
  · exact s16h_odd_card_of_isElemAbelianOfRank_three hc

theorem s16h_commSub_inf_fixV_eq_bot_of_tensor {W : Type} [CommGroup W]
    {L : Subgroup (MulAut W)} {d a : ℕ} (hd : 2 ≤ d) (h : NatTensor L (commSub ⊤ L) ⊥ d a) :
    commSub ⊤ L ⊓ fixV L = ⊥ := by
  obtain ⟨K, _, _, _, hReal⟩ := h
  obtain ⟨π, hVia⟩ := hReal
  obtain ⟨β, -, hβk, hβe⟩ := FFModel.RealizesVia.coord rfl rfl hVia
  refine le_bot_iff.1 fun w hw => ?_
  obtain ⟨hwU, hwfix⟩ := Subgroup.mem_inf.1 hw
  have hfix : ∀ γ : (FFModel.tensorNat d K).Gam,
      tensorAct d K γ (β ⟨w, hwU⟩) = β ⟨w, hwU⟩ := by
    intro γ
    have hfixw : ((π γ : ↥L) : MulAut W) w = w := (mem_fixV.1 hwfix) (π γ) (π γ).2
    have hu : ((π γ : ↥L) : MulAut W) w ∈ commSub ⊤ L := by rw [hfixw]; exact hwU
    have h1 := hβe γ ⟨w, hwU⟩ hu
    have h2 : (⟨((π γ : ↥L) : MulAut W) w, hu⟩ : ↥(commSub ⊤ L)) = ⟨w, hwU⟩ :=
      Subtype.ext hfixw
    rw [h2] at h1
    exact h1.symm
  exact (hβk ⟨w, hwU⟩).1
    (CFSG.Quasithin.SmithD321.eq_one_of_forall_tensorAct (K := K) hd hfix)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
