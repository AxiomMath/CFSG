module

public import CFSG.Quasithin.EmptyFaithful.S153D0All
public import CFSG.Quasithin.EmptyFaithful.T1531Stage1

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
open scoped commutatorElement

section Rank

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp : Subgroup G} {t : G}

theorem Hyp153.pRank_le_two_of_le (h113 : StageLemma14113) (h : Hyp153 G T Mc M) {X : Subgroup G}
    (hXY : X ≤ Y153 Mc M) : CFSG.Open.pRank 3 X ≤ 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp1 : 1 < 3 := by norm_num
  obtain ⟨φ, -⟩ := h.exists_mulEquiv_imageOTwoQuot_of_le_Y153 h113 hXY
  have hnd : ¬ 3 ∣ Nat.card (CFSG.Open.pCore 2 ↥X) := by
    intro hd
    obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥X) 2).exists_card_eq
    rw [hk] at hd
    exact absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow hd)) (by norm_num)
  have e1 := CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp1 φ
  have e2 := CFSG.SectionRank.pRank_quotient_eq (p := 3) (CFSG.Open.pCore 2 ↥X) hnd
  have e3 := pRank_top_subtype (p := 3) X
  have h4 := CFSG.SectionRank.pRank_top_le_of_injective hp1
    (Subgroup.inclusion (imageOTwoQuot_mono hXY : imageOTwoQuot M X ≤ imageOTwoQuot M (Y153 Mc M)))
    (Subgroup.inclusion_injective _)
  have h5 := pRank_Ystar_le h
  calc CFSG.Open.pRank 3 X = CFSG.Open.pRank 3 (⊤ : Subgroup ↥X) := e3.symm
    _ = CFSG.Open.pRank 3 (⊤ : Subgroup (OTwoQuot X)) := e2.symm
    _ = CFSG.Open.pRank 3 (⊤ : Subgroup ↥(imageOTwoQuot M X)) := e1
    _ ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥(imageOTwoQuot M (Y153 Mc M))) := h4
    _ ≤ 2 := h5

end Rank

namespace Hyp15310

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp : Subgroup G} {t : G}

theorem pRank_Yp_le_two (h113 : StageLemma14113) (h : Hyp15310 G T Mc M V₁ V₂ Yp t) :
    CFSG.Open.pRank 3 Yp ≤ 2 :=
  h.hyp.pRank_le_two_of_le h113 h.Yp_le_Y153

theorem one_le_pRank_Yp (h113 : StageLemma14113) (h : Hyp15310 G T Mc M V₁ V₂ Yp t)
    {I : Subgroup G} (hI : IsHPlus Yp (Sgp153 T V₁) M I) : 1 ≤ CFSG.Open.pRank 3 Yp := by
  have hne : Yp ≠ ⊥ := fun hb => h.Yp_not_le_centralizer_UI h113 hI (hb ▸ bot_le)
  obtain ⟨y, hyY, hyodd, hy1⟩ : ∃ y ∈ Yp, Odd (orderOf y) ∧ y ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply hne
    rw [← h.oTwoUpper_eq, eq_bot_iff]
    refine (Subgroup.closure_le ⊥).mpr fun x hx => ?_
    exact Subgroup.mem_bot.mpr (hcon x hx.1 hx.2)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : y ^ 3 = 1 := h.Yp_pow_three_of_odd h113 hyY hyodd
  have hord : orderOf y = 3 := orderOf_eq_prime h3 hy1
  refine CFSG.SectionRank.le_pRank (by norm_num) (E := Subgroup.zpowers y)
    (Subgroup.zpowers_le.mpr hyY) ⟨inferInstance, fun x hx => ?_⟩ (k := 1) ?_
  · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h3, one_zpow]
  · rw [Nat.card_zpowers, hord]
    norm_num

end Hyp15310

section Blocks

@[expose] def Stage15325 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp : Subgroup G) (t : G),
    Hyp15310 G T Mc M V₁ V₂ Yp t → ∀ I : Subgroup G, IsHPlus Yp (Sgp153 T V₁) M I → ¬ CharTwo I

@[expose] def Stage15325One : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp : Subgroup G) (t : G),
    Hyp15310 G T Mc M V₁ V₂ Yp t → CFSG.Open.pRank 3 Yp = 1 →
      ∀ I : Subgroup G, IsHPlus Yp (Sgp153 T V₁) M I → ¬ CharTwo I

@[expose] def StageComponentCase : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp : Subgroup G) (t : G),
    Hyp15310 G T Mc M V₁ V₂ Yp t → ∀ I : Subgroup G, IsHPlus Yp (Sgp153 T V₁) M I →
      (∀ K : Subgroup G, IsHPlus Yp (Sgp153 T V₁) M K → K ≤ I → K = I) → ¬ CharTwo I → False

theorem stage15325_of_blocks (h113 : StageLemma14113) (h13 : Stage15313) (h1 : Stage15325One) :
    Stage15325 := by
  intro G _ _ T Mc M V₁ V₂ Yp t h I hI
  have hle := h.pRank_Yp_le_two h113
  have hge := h.one_le_pRank_Yp h113 hI
  rcases (by omega : CFSG.Open.pRank 3 Yp = 1 ∨ CFSG.Open.pRank 3 Yp = 2) with h1' | h2'
  · exact h1 G T Mc M V₁ V₂ Yp t h h1' I hI
  · exact h13 G T Mc M V₁ V₂ Yp t h h2' I hI

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp : Subgroup G} {t : G}

theorem exists_isHPlus_of_not_isUniqueM (h : Hyp15310 G T Mc M V₁ V₂ Yp t)
    (hnu : ¬ IsUniqueM (Yp ⊔ Sgp153 T V₁) M) :
    ∃ I : Subgroup G, IsHPlus Yp (Sgp153 T V₁) M I := by
  have hXM : Yp ⊔ Sgp153 T V₁ ≤ M :=
    sup_le (h.Yp_le_Y153.trans (Y153_le Mc M)) (inf_le_left.trans h.hyp.T_le)
  have hInM : InM (Yp ⊔ Sgp153 T V₁) M := ⟨h.hyp.inM.1, hXM⟩
  have hex : ∃ M', InM (Yp ⊔ Sgp153 T V₁) M' ∧ M' ≠ M := by
    by_contra hcon
    push Not at hcon
    exact hnu ⟨hInM, hcon⟩
  obtain ⟨M', hM', hne⟩ := hex
  refine ⟨M', ⟨hM'.2, pCoreOf_ne_bot_of_isTwoLocal hM'.1.1⟩, fun hle => hne ?_⟩
  exact (hM'.1.2 M h.hyp.inM.1.1 hle).symm

theorem stage15344_of_blocks (h25 : Stage15325) (hc : StageComponentCase) : Stage15344 := by
  intro G _ _ T Mc M V₁ V₂ Yp t h
  by_contra hnu
  obtain ⟨I, hI⟩ := exists_isHPlus_of_not_isUniqueM h hnu
  obtain ⟨J, ⟨hJ, hJI⟩, hmin⟩ := (wellFounded_lt (α := Subgroup G)).has_min
    {K : Subgroup G | IsHPlus Yp (Sgp153 T V₁) M K ∧ K ≤ I} ⟨I, hI, le_rfl⟩
  refine hc G T Mc M V₁ V₂ Yp t h J hJ (fun K hK hKJ => ?_) (h25 G T Mc M V₁ V₂ Yp t h J hJ)
  by_contra hne
  exact hmin K ⟨hK, hKJ.trans hJI⟩ (lt_of_le_of_ne hKJ hne)

theorem stage15344_of_inputs
    (h11 : StageLemma14111) (h113 : StageLemma14113)
    (hC27 : ∀ (G : Type) [Group G] [Finite G], ASC27Statement G)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (hcover : AsA36NoOddCover)
    (h15 : Input15315Two) (h16 : Input15316One) (h17 : Input15317)
    (h18 : Input15318) (h19 : Input15319) (h20 : Input15320) (h21 : Input15321)
    (h23 : Input15323) (h24 : Input15324) (h1 : Stage15325One) (hc : StageComponentCase) :
    Stage15344 :=
  stage15344_of_blocks
    (stage15325_of_blocks h113
      (theorem15313_of_stages h11 h113 hC27 h37 h38 hcover h15 h16 h17 h18 h19 h20 h21 h23 h24)
      h1) hc

end Blocks

end CFSG.Quasithin
