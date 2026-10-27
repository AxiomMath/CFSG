module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1TwoCommonBase
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveSeventeen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenCfg2Fix
import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.ModuleChief
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeS

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

section Abstract

variable {W₁ W₂ : Type} [CommGroup W₁] [CommGroup W₂]

private theorem s16e_twoLf_commSub_map {κ : W₁ →* W₂} {A : Subgroup (MulAut W₁)}
    {B : Subgroup (MulAut W₂)}
    (hAB : ∀ a ∈ A, ∃ b ∈ B, ∀ w, κ (a w) = b (κ w))
    (hBA : ∀ b ∈ B, ∃ a ∈ A, ∀ w, κ (a w) = b (κ w)) (S : Subgroup W₁) :
    (commSub S A).map κ = commSub (S.map κ) B := by
  unfold commSub
  rw [MonoidHom.map_closure]
  congr 1
  ext c
  constructor
  · rintro ⟨_, ⟨a, ha, w, hw, rfl⟩, rfl⟩
    obtain ⟨b, hb, hab⟩ := hAB a ha
    exact ⟨b, hb, κ w, ⟨w, hw, rfl⟩, by rw [map_mul, map_inv, hab]⟩
  · rintro ⟨b, hb, _, ⟨w, hw, rfl⟩, rfl⟩
    obtain ⟨a, ha, hab⟩ := hBA b hb
    exact ⟨a w * w⁻¹, ⟨a, ha, w, hw, rfl⟩, by rw [map_mul, map_inv, hab]⟩

private theorem s16e_twoLf_stable_comap {κ : W₁ →* W₂} {A : Subgroup (MulAut W₁)}
    {B : Subgroup (MulAut W₂)}
    (hAB : ∀ a ∈ A, ∃ b ∈ B, ∀ w, κ (a w) = b (κ w)) {I : Subgroup W₂}
    (hI : StableUnder B I) : StableUnder A (I.comap κ) := by
  intro a ha w hw
  obtain ⟨b, hb, hab⟩ := hAB a ha
  show κ (a w) ∈ I
  rw [hab]
  exact hI b hb _ hw

private theorem s16e_twoLf_stable_map {κ : W₁ →* W₂} {A : Subgroup (MulAut W₁)}
    {B : Subgroup (MulAut W₂)}
    (hBA : ∀ b ∈ B, ∃ a ∈ A, ∀ w, κ (a w) = b (κ w)) {J : Subgroup W₁}
    (hJ : StableUnder A J) : StableUnder B (J.map κ) := by
  rintro b hb _ ⟨w, hw, rfl⟩
  obtain ⟨a, ha, hab⟩ := hBA b hb
  exact ⟨a w, hJ a ha w hw, hab w⟩

private theorem s16e_twoLf_stable_commSub {A : Subgroup (MulAut W₁)} {Y : Subgroup W₁}
    (hY : StableUnder A Y) : StableUnder A (commSub Y A) :=
  fun g hg c hc => CFSG.Quasithin.B15P4.map_commSub_mem (Subgroup.le_normalizer hg) (hY g hg) c hc

private theorem s16e_twoLf_commSub_commSub {A : Subgroup (MulAut W₁)} (hperf : ⁅A, A⁆ = A)
    {Y : Subgroup W₁} (hY : StableUnder A Y) : commSub (commSub Y A) A = commSub Y A := by
  have hL : commutator ↥A = ⊤ := Group.isPerfect_def.1 (Subgroup.isPerfect_iff.2 hperf)
  refine le_antisymm (commSub_le_of_invariant (s16e_twoLf_stable_commSub hY)) ?_
  exact CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.isCentralSec_iff_commSub_le.1
    (CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.IsCentralSec.trans_of_perfect hL
      (CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.isCentralSec_iff_commSub_le.2
        le_rfl)
      (CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.isCentralSec_iff_commSub_le.2
        le_rfl))

private theorem s16e_twoLf_lift_irr_abs {κ : W₁ →* W₂} (hκ : Function.Surjective κ)
    {A : Subgroup (MulAut W₁)} {B : Subgroup (MulAut W₂)} (hperf : ⁅A, A⁆ = A)
    (hAB : ∀ a ∈ A, ∃ b ∈ B, ∀ w, κ (a w) = b (κ w))
    (hBA : ∀ b ∈ B, ∃ a ∈ A, ∀ w, κ (a w) = b (κ w))
    (hker : ∀ w, κ w = 1 → w ∈ fixV A) (hfixB : fixV B = ⊥)
    {I : Subgroup W₂} (hI : I ∈ irrSet B) : ∃ J ∈ irrSet A, J.map κ = I := by
  obtain ⟨hcomm, hlt, hstabI, hstabN, hmin⟩ := hI
  have hN : I ⊓ fixV B = ⊥ := by rw [hfixB, inf_bot_eq]
  rw [hN] at hlt hmin
  have hYst : StableUnder A (I.comap κ) := s16e_twoLf_stable_comap hAB hstabI
  have hκY : (I.comap κ).map κ = I := Subgroup.map_comap_eq_self_of_surjective hκ I
  have hJst : StableUnder A (commSub (I.comap κ) A) := s16e_twoLf_stable_commSub hYst
  have hκJ : (commSub (I.comap κ) A).map κ = I := by
    rw [s16e_twoLf_commSub_map hAB hBA, hκY, hcomm]
  have hJJ : commSub (commSub (I.comap κ) A) A = commSub (I.comap κ) A :=
    s16e_twoLf_commSub_commSub hperf hYst
  set J := commSub (I.comap κ) A with hJdef
  refine ⟨J, ⟨hJJ, ?_⟩, hκJ⟩
  have hNle : J ⊓ fixV A ≤ J := inf_le_left
  refine ⟨lt_of_le_of_ne hNle ?_, hJst, ?_, ?_⟩
  · intro h
    have hJfix : J ≤ fixV A := by
      have : J ≤ J ⊓ fixV A := h.ge
      exact this.trans inf_le_right
    have hJbot : J = ⊥ := by
      rw [← hJJ]
      exact commSub_eq_bot_iff.2 hJfix
    rw [hJbot, Subgroup.map_bot] at hκJ
    rw [← hκJ] at hlt
    exact lt_irrefl _ hlt
  · intro a ha u hu
    have hu2 : u ∈ fixV A := hu.2
    refine ⟨hJst a ha u hu.1, ?_⟩
    show a u ∈ fixV A
    rw [(mem_fixV.1 hu2) a ha]
    exact hu2
  · intro J' hJ' hNJ' hJ'J
    have hBst : StableUnder B (J'.map κ) := s16e_twoLf_stable_map hBA hJ'
    have hle : J'.map κ ≤ I := hκJ ▸ Subgroup.map_mono hJ'J
    rcases hmin _ hBst bot_le hle with h | h
    · left
      refine le_antisymm (fun w hw => ⟨hJ'J hw, hker w ?_⟩ ) hNJ'
      have : κ w ∈ J'.map κ := ⟨w, hw, rfl⟩
      rw [h, Subgroup.mem_bot] at this
      exact this
    · right
      refine le_antisymm hJ'J (fun j hj => ?_)
      have hκj : κ j ∈ J'.map κ := by rw [h, ← hκJ]; exact ⟨j, hj, rfl⟩
      obtain ⟨j', hj', hjj'⟩ := hκj
      have h1 : j * j'⁻¹ ∈ J ⊓ fixV A := by
        refine ⟨J.mul_mem hj (J.inv_mem (hJ'J hj')), hker _ ?_⟩
        rw [map_mul, map_inv, hjj', mul_inv_cancel]
      have h2 : j * j'⁻¹ * j' ∈ J' := J'.mul_mem (hNJ' h1) hj'
      simpa using h2

end Abstract

private theorem s16e_twoLf_kappa_AB {V₀ V₁ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (h01 : V₀ ≤ V₁)
    (hL₁ : L ≤ stabTil V₁ V) :
    ∀ a ∈ barSub V₀ V hV L, ∃ b ∈ barSub V₁ V hV L, ∀ w : Vtil V₀ V hV,
      s15T7Kappa V₀ V₁ V hV h01 (a w) = b (s15T7Kappa V₀ V₁ V hV h01 w) := by
  intro a ha
  obtain ⟨g, hgL, rfl⟩ := (mem_barSub V₀ V hV L a).1 ha
  have hg1 : (g : G) ∈ stabTil V₁ V := hL₁ hgL
  exact ⟨actTil V₁ V hV ⟨g, hg1⟩, actTil_mem_barSub V₁ V hV hgL hg1,
    fun w => s15_T7_kappa_act V₀ V₁ V hV h01 g.2 hg1 w⟩

private theorem s16e_twoLf_kappa_BA {V₀ V₁ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (h01 : V₀ ≤ V₁)
    (hL₀ : L ≤ stabTil V₀ V) :
    ∀ b ∈ barSub V₁ V hV L, ∃ a ∈ barSub V₀ V hV L, ∀ w : Vtil V₀ V hV,
      s15T7Kappa V₀ V₁ V hV h01 (a w) = b (s15T7Kappa V₀ V₁ V hV h01 w) := by
  intro b hb
  obtain ⟨g, hgL, rfl⟩ := (mem_barSub V₁ V hV L b).1 hb
  have hg0 : (g : G) ∈ stabTil V₀ V := hL₀ hgL
  exact ⟨actTil V₀ V hV ⟨g, hg0⟩, actTil_mem_barSub V₀ V hV hgL hg0,
    fun w => s15_T7_kappa_act V₀ V₁ V hV h01 hg0 g.2 w⟩

private theorem s16e_twoLf_kappa_ker (D : Data G) {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L)
    (hV : IsElemAbelian 2 V) (w : Vtil V₀ V hV)
    (hw : s15T7Kappa V₀ (v1Sub D.M V₀ V hV L) V hV (s15_Infra_le_v1Sub D.M V₀ V hV L) w = 1) :
    w ∈ fixV (barSub V₀ V hV L) := by
  obtain ⟨x, rfl⟩ := mkTil_surjective V₀ V hV w
  have hx : x.val ∈ v1Sub D.M V₀ V hV L := by
    have h1 : mkTil (v1Sub D.M V₀ V hV L) V hV x = 1 := hw
    exact (QuotientGroup.eq_one_iff (N := modNull (v1Sub D.M V₀ V hV L) V hV) x).1 h1
  have hmem : mkTil V₀ V hV x ∈ imgTil V₀ V hV (v1Sub D.M V₀ V hV L) :=
    (mem_imgTil V₀ V hV _ _).2 ⟨x, hx, rfl⟩
  have hfix := s15_Core_imgTil_v1Sub_le_fixV h (m := (1 : G)) D.M.one_mem
  simpa only [conjSubgroup_one] using hfix hmem

private theorem s16e_twoLf_summands (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D)
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

private theorem s16e_twoLf_fixV (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D)
    (h1214 : F12.R1214 D) {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hset : Setting16 D V₀ V L) (hL : barSub V₀ V hV L ≠ ⊥) (hs : s15 D.M V₀ V hV L = 1)
    {P : s16e_two_NatPred (vStar D.M V₀ V hV L)} (hF : s16e_two_Fam D V₀ V L hV P) :
    fixV (lStar D.M V₀ V hV L) = ⊥ := by
  obtain ⟨J₀, J₁, hN₀, hN₁, hinf, hsup⟩ :=
    s16e_twoLf_summands D hx h61 h127 h1214 hV hset hL hs hF
  exact s16c167_fixV_eq_bot_of_two (hF.natFacts.irr J₀ hN₀).2.2.1 (hF.natFacts.irr J₁ hN₁).2.2.1
    (hF.natFacts.fixV_inf J₀ hN₀) (hF.natFacts.fixV_inf J₁ hN₁) hinf hsup

theorem s16e_two_lift_irr (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D)
    (h1214 : F12.R1214 D) {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hset : Setting16 D V₀ V L) (hL : barSub V₀ V hV L ≠ ⊥) (hs : s15 D.M V₀ V hV L = 1)
    {P : s16e_two_NatPred (vStar D.M V₀ V hV L)} (hF : s16e_two_Fam D V₀ V L hV P) :
    ∀ I ∈ irrSet (lStar D.M V₀ V hV L), ∃ J ∈ irrSet (lBar V₀ V hV L),
      J.map (s15T7Kappa V₀ (v1Sub D.M V₀ V hV L) V hV (s15_Infra_le_v1Sub D.M V₀ V hV L)) = I := by
  intro I hI
  have hh := hset.hyp151
  have hMs₀ : D.M ≤ stabTil V₀ V :=
    le_stabTil hh.hyp125.pairFacts.le_normalizer hh.hyp125.pairFacts.le_normalizer₀
  have hMs₁ := s15_T7_le_stabTil_v1Sub hh
  have h01 := s15_Infra_le_v1Sub D.M V₀ V hV L
  exact s16e_twoLf_lift_irr_abs (s15_T7_kappa_surjective V₀ _ V hV h01) hF.perfect
    (s16e_twoLf_kappa_AB hV h01 (hh.le.trans hMs₁)) (s16e_twoLf_kappa_BA hV h01 (hh.le.trans hMs₀))
    (fun w hw => s16e_twoLf_kappa_ker D hh hV w hw)
    (s16e_twoLf_fixV D hx h61 h127 h1214 hV hset hL hs hF) hI

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
