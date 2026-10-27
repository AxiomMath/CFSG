module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1TwoCommonBase
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveSeventeen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenCfg2Fix
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeS

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

section Abstract

variable {W₁ W₂ : Type} [CommGroup W₁] [CommGroup W₂]

private theorem s16e_twoNi_stable_comap {κ : W₁ →* W₂} {A : Subgroup (MulAut W₁)}
    {B : Subgroup (MulAut W₂)}
    (hAB : ∀ a ∈ A, ∃ b ∈ B, ∀ w, κ (a w) = b (κ w)) {I : Subgroup W₂}
    (hI : StableUnder B I) : StableUnder A (I.comap κ) := by
  intro a ha w hw
  obtain ⟨b, hb, hab⟩ := hAB a ha
  show κ (a w) ∈ I
  rw [hab]
  exact hI b hb _ hw

private theorem s16e_twoNi_not_irr_top {κ : W₁ →* W₂} (hκ : Function.Surjective κ)
    {A : Subgroup (MulAut W₁)} {B : Subgroup (MulAut W₂)}
    (hAB : ∀ a ∈ A, ∃ b ∈ B, ∀ w, κ (a w) = b (κ w))
    (hBA : ∀ b ∈ B, ∃ a ∈ A, ∀ w, κ (a w) = b (κ w)) (hfixB : fixV B = ⊥)
    {J₀ : Subgroup W₂} (hJ₀ : StableUnder B J₀) (hbot : J₀ ≠ ⊥) (htop : J₀ ≠ ⊤) :
    (⊤ : Subgroup W₁) ∉ irrSet A := by
  intro h
  obtain ⟨-, -, -, -, hmin⟩ := h
  have hY : StableUnder A (J₀.comap κ) := s16e_twoNi_stable_comap hAB hJ₀
  have hfix : ∀ w ∈ fixV A, κ w = 1 := by
    intro w hw
    have : κ w ∈ fixV B := by
      rw [mem_fixV]
      intro b hb
      obtain ⟨a, ha, hab⟩ := hBA b hb
      rw [← hab, (mem_fixV.1 hw) a ha]
    rw [hfixB, Subgroup.mem_bot] at this
    exact this
  have hle : ⊤ ⊓ fixV A ≤ J₀.comap κ := fun w hw => by
    show κ w ∈ J₀
    rw [hfix w hw.2]
    exact J₀.one_mem
  rcases hmin _ hY hle le_top with h | h
  · apply hbot
    rw [← Subgroup.map_comap_eq_self_of_surjective hκ J₀, h, eq_bot_iff]
    rintro _ ⟨w, hw, rfl⟩
    rw [hfix w hw.2]
    exact Subgroup.one_mem _
  · apply htop
    rw [← Subgroup.map_comap_eq_self_of_surjective hκ J₀, h, Subgroup.map_top,
      MonoidHom.range_eq_top_of_surjective κ hκ]

end Abstract

private theorem s16e_twoNi_kappa_AB {V₀ V₁ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (h01 : V₀ ≤ V₁)
    (hL₁ : L ≤ stabTil V₁ V) :
    ∀ a ∈ barSub V₀ V hV L, ∃ b ∈ barSub V₁ V hV L, ∀ w : Vtil V₀ V hV,
      s15T7Kappa V₀ V₁ V hV h01 (a w) = b (s15T7Kappa V₀ V₁ V hV h01 w) := by
  intro a ha
  obtain ⟨g, hgL, rfl⟩ := (mem_barSub V₀ V hV L a).1 ha
  have hg1 : (g : G) ∈ stabTil V₁ V := hL₁ hgL
  exact ⟨actTil V₁ V hV ⟨g, hg1⟩, actTil_mem_barSub V₁ V hV hgL hg1,
    fun w => s15_T7_kappa_act V₀ V₁ V hV h01 g.2 hg1 w⟩

private theorem s16e_twoNi_kappa_BA {V₀ V₁ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (h01 : V₀ ≤ V₁)
    (hL₀ : L ≤ stabTil V₀ V) :
    ∀ b ∈ barSub V₁ V hV L, ∃ a ∈ barSub V₀ V hV L, ∀ w : Vtil V₀ V hV,
      s15T7Kappa V₀ V₁ V hV h01 (a w) = b (s15T7Kappa V₀ V₁ V hV h01 w) := by
  intro b hb
  obtain ⟨g, hgL, rfl⟩ := (mem_barSub V₁ V hV L b).1 hb
  have hg0 : (g : G) ∈ stabTil V₀ V := hL₀ hgL
  exact ⟨actTil V₀ V hV ⟨g, hg0⟩, actTil_mem_barSub V₀ V hV hgL hg0,
    fun w => s15_T7_kappa_act V₀ V₁ V hV h01 hg0 g.2 w⟩

private theorem s16e_twoNi_summands (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D)
    (h1214 : F12.R1214 D) {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hset : Setting16 D V₀ V L) (hL : barSub V₀ V hV L ≠ ⊥) (hs : s15 D.M V₀ V hV L = 1)
    {P : s16e_two_NatPred (vStar D.M V₀ V hV L)} (hF : s16e_two_Fam D V₀ V L hV P) :
    ∃ J₀ J₁ : Subgroup (vStar D.M V₀ V hV L),
      P (lStar D.M V₀ V hV L) J₀ ⊥ ∧ P (lStar D.M V₀ V hV L) J₁ ⊥ ∧
      J₀ ⊓ J₁ = ⊥ ∧ J₀ ⊔ J₁ = ⊤ := by
  have h1217 : R1217 D := r1217_of_twelve_seventeen D hx h61 h127 h1214
  have hwtop : wStar D.M V₀ V hV L = ⊤ := s15_Three_wStar_eq_top D h1217 hset.hyp151 hV hL hs
  have hsum : SumOfNat P (lStar D.M V₀ V hV L) ⊤ ⊥ 2 := by
    have h := hF.sum
    rwa [hwtop] at h
  exact s16c167_sumOfNat_two hsum

private theorem s16e_twoNi_fixV (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D)
    (h1214 : F12.R1214 D) {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hset : Setting16 D V₀ V L) (hL : barSub V₀ V hV L ≠ ⊥) (hs : s15 D.M V₀ V hV L = 1)
    {P : s16e_two_NatPred (vStar D.M V₀ V hV L)} (hF : s16e_two_Fam D V₀ V L hV P) :
    fixV (lStar D.M V₀ V hV L) = ⊥ := by
  obtain ⟨J₀, J₁, hN₀, hN₁, hinf, hsup⟩ :=
    s16e_twoNi_summands D hx h61 h127 h1214 hV hset hL hs hF
  exact s16c167_fixV_eq_bot_of_two (hF.natFacts.irr J₀ hN₀).2.2.1 (hF.natFacts.irr J₁ hN₁).2.2.1
    (hF.natFacts.fixV_inf J₀ hN₀) (hF.natFacts.fixV_inf J₁ hN₁) hinf hsup

theorem s16e_two_not_irr_til (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D)
    (h1214 : F12.R1214 D) {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hset : Setting16 D V₀ V L) (hL : barSub V₀ V hV L ≠ ⊥) (hs : s15 D.M V₀ V hV L = 1)
    {P : s16e_two_NatPred (vStar D.M V₀ V hV L)} (hF : s16e_two_Fam D V₀ V L hV P) :
    (⊤ : Subgroup (Vtil V₀ V hV)) ∉ irrSet (lBar V₀ V hV L) := by
  obtain ⟨J₀, J₁, hN₀, hN₁, hinf, hsup⟩ :=
    s16e_twoNi_summands D hx h61 h127 h1214 hV hset hL hs hF
  have hh := hset.hyp151
  have hMs₀ : D.M ≤ stabTil V₀ V :=
    le_stabTil hh.hyp125.pairFacts.le_normalizer hh.hyp125.pairFacts.le_normalizer₀
  have hMs₁ := s15_T7_le_stabTil_v1Sub hh
  have h01 := s15_Infra_le_v1Sub D.M V₀ V hV L
  have hirr₀ := hF.natFacts.irr J₀ hN₀
  have hirr₁ := hF.natFacts.irr J₁ hN₁
  have hfix := s16e_twoNi_fixV D hx h61 h127 h1214 hV hset hL hs hF
  have hbot₀ : J₀ ≠ ⊥ := by
    have h := hirr₀.2.1
    rw [hfix, inf_bot_eq] at h
    exact h.ne'
  have hbot₁ : J₁ ≠ ⊥ := by
    have h := hirr₁.2.1
    rw [hfix, inf_bot_eq] at h
    exact h.ne'
  have htop : J₀ ≠ ⊤ := by
    intro h
    rw [h, top_inf_eq] at hinf
    exact hbot₁ hinf
  exact s16e_twoNi_not_irr_top (s15_T7_kappa_surjective V₀ _ V hV h01)
    (s16e_twoNi_kappa_AB hV h01 (hh.le.trans hMs₁)) (s16e_twoNi_kappa_BA hV h01 (hh.le.trans hMs₀))
    hfix hirr₀.2.2.1 hbot₀ htop

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
