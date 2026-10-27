module

public import CFSG.LocalAnalysis.StandardType.GGNSJoinBaseLabel
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanPrimDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyQFourTBSmall
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRefl
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrOfEnnola

public section

namespace CFSG.StandardType

open CFSG.Assembly

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
  {𝒦 : Finset (Subgroup G)}

theorem ggLabel_n_eq_one_of_rk1
    (hRk1 : GGSecFiveRk1PhanInput) (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hns : ¬ GGSplitLie p L) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)} (hP : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3) {r : MulAut ↥Bs} (hrA : r ∈ ggAutomizer L Bs)
    (hrC : r ∈ ggCoxRefl M e) (hr6 : Nat.card (ggRankOneIn L Bs r) = 6) {lab : LargeEvenLabel}
    (hΛ : LargeEvenInLambda2 lab) (hlab : GGHasLabel lab (↥L ⧸ Subgroup.center ↥L)) :
    lab.n = 1 := by
  obtain ⟨F, hF, hFfin, θ, -, hθinj, hθrange, -, -, -, hlabF⟩ :=
    hRk1 G p B Bs x L D J 𝒦 hcfg hns ι M e hP hle3 L (Or.inl rfl) r hrA hrC
  letI : Field F := hF
  haveI : Finite F := hFfin
  have hcardSL : Nat.card (ggRankOneIn L Bs r) =
      Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) := by
    rw [← hθrange]
    exact Nat.card_congr (MonoidHom.ofInjective hθinj).toEquiv.symm
  rw [hcardSL, ggSL2_card F] at hr6
  have hq2 : 2 ≤ Nat.card F := Finite.one_lt_card
  have hF2 : Nat.card F = 2 := by
    by_contra hne
    have h3 : 3 ≤ Nat.card F := by omega
    have h9 : 9 ≤ Nat.card F ^ 2 := by simpa using Nat.pow_le_pow_left h3 2
    have h24 : 3 * 8 ≤ Nat.card F * (Nat.card F ^ 2 - 1) := Nat.mul_le_mul h3 (by omega)
    omega
  have hn : 2 ^ lab.n ≤ 2 := hF2 ▸ hlabF lab hΛ hlab
  by_contra hge
  have h2n : 2 ≤ lab.n := by
    have h1 : 1 ≤ lab.n := hΛ.1
    have hne : 1 ≠ lab.n := fun h => hge h.symm
    exact Nat.succ_le_of_lt (lt_of_le_of_ne h1 hne)
  have h4 : 4 ≤ 2 ^ lab.n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ lab.n := Nat.pow_le_pow_right (by norm_num) h2n
  omega

theorem ggL_baseLabel_qTwo_of_rk1
    (hRk1 : GGSecFiveRk1PhanInput) (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hns : ¬ GGSplitLie p L) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)} (hP : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3) {r : MulAut ↥Bs} (hrA : r ∈ ggAutomizer L Bs)
    (hrC : r ∈ ggCoxRefl M e) (hr6 : Nat.card (ggRankOneIn L Bs r) = 6) :
    GGInnerDiagOnLabel (fun p lab => lab.n = 1 ∧ (ggRowP_ESU p lab ∨ ggRowP_EOmM p lab ∨
      ggRowP_ETwE6 p lab ∨ (p = 3 ∧ (ggRowP_EOmP p lab ∨ ggRowP_EE7 p lab ∨ ggRowP_EE8 p lab ∨
        ggRowP_NF4 p lab)))) p Bs L := by
  have hbase := ggL_baseLabel_of_nonSplit hcfg hP hle3 hns
  refine GGInnerDiagOnLabel.mono_label_of_hasLabel ?_ hbase
  intro lab hΛ hlab hS
  rcases hS with h1 | h2 | h3 | ⟨hn, hp3, h4⟩
  · exact ⟨ggLabel_n_eq_one_of_rk1 hRk1 hcfg hns hP hle3 hrA hrC hr6 hΛ hlab, Or.inl h1⟩
  · exact ⟨ggLabel_n_eq_one_of_rk1 hRk1 hcfg hns hP hle3 hrA hrC hr6 hΛ hlab, Or.inr (Or.inl h2)⟩
  · exact ⟨ggLabel_n_eq_one_of_rk1 hRk1 hcfg hns hP hle3 hrA hrC hr6 hΛ hlab,
      Or.inr (Or.inr (Or.inl h3))⟩
  · exact ⟨hn, Or.inr (Or.inr (Or.inr ⟨hp3, h4⟩))⟩

end CFSG.StandardType

end
