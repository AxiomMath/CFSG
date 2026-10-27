module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2UniCover
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2UniExc
import CFSG.LocalAnalysis.StandardType.GGTableBThreeTBTwE6
import CFSG.LocalAnalysis.StandardType.GGResLeaf
import CFSG.LocalAnalysis.StandardType.GGTableBThreeTBTwE6Holds
import CFSG.LocalAnalysis.StandardType.GGTablePThreeF4Comp
import CFSG.LocalAnalysis.StandardType.GGKnownInputsPsuOrder
import CFSG.LocalAnalysis.StandardType.GGTwE6KGLNoJ1Ppd
import CFSG.LocalAnalysis.StandardType.GGTableBExcBasic
import CFSG.LocalAnalysis.StandardType.MarkingClassical
import CFSG.Timmesfeld.Orders.Classical
import CFSG.Timmesfeld.Orders.ExceptionalUntwisted

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial CFSG.Open

@[expose] def GGBstarAbelianPreimageJUniS1OnDeg (S : ℕ → ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → GGInnerDiagOn Bs L →
      ∀ (hN : Bs ≤ Subgroup.normalizer (J : Set G)) (d m : ℕ),
        (p = 3 ∧ (d = 3 ∨ d = 6)) ∨ (p = 5 ∧ d = 5) → p ∣ 2 ^ m + 1 → ¬ (d = 3 ∧ m = 1) →
        ∀ (E : Type) [Field E] (hE : UnitaryFieldData 2 m E)
          (θ : ↥J ⧸ Subgroup.center ↥J ≃* LargeEvenProj (LargeEvenSUGroup (Fin d) E (2 ^ m))),
          GGInnerDiagOnLab (fun p lab => S p d lab) p Bs L →
          IsMulCommutative
            ((((ggBsAut hN).range).map (kgInducedAut θ)).comap
              (CFSG.HardMathSupport.C14Cl.uniConj hE d))

theorem GGInnerDiagOnLab.mono_at_prime {G : Type} [Group G] {S T : ℕ → LargeEvenLabel → Prop}
    {p : ℕ} {Bs L : Subgroup G} (hST : ∀ lab, S p lab → T p lab)
    (h : GGInnerDiagOnLab S p Bs L) : GGInnerDiagOnLab T p Bs L :=
  largeEvenMarking_mono (fun _ _ _ _ _ _ hP => ⟨hST _ hP.1, hP.2⟩) h

theorem GGInnerDiagOnLab.mono_of_split {G : Type} [Group G] {S T : ℕ → LargeEvenLabel → Prop}
    {p : ℕ} {Bs L : Subgroup G} (hST : ∀ lab, S p lab → LargeEvenSplit p lab → T p lab)
    (h : GGInnerDiagOnLab S p Bs L) : GGInnerDiagOnLab T p Bs L :=
  largeEvenMarking_mono (fun _ _ _ _ _ _ hP => ⟨hST _ hP.1 hP.2.1, hP.2⟩) h

theorem GGBstarAbelianPreimageJUniS1OnDeg.mono {S T : ℕ → ℕ → LargeEvenLabel → Prop}
    (hST : ∀ p d lab, ((p = 3 ∧ (d = 3 ∨ d = 6)) ∨ (p = 5 ∧ d = 5)) → S p d lab → T p d lab)
    (h : GGBstarAbelianPreimageJUniS1OnDeg T) : GGBstarAbelianPreimageJUniS1OnDeg S := by
  intro G _ _ p B Bs x L D J hcfg hID hN d m hshape hpm hdm E _ hE θ hlab
  exact h G p B Bs x L D J hcfg hID hN d m hshape hpm hdm E hE θ
    (GGInnerDiagOnLab.mono_at_prime (S := fun p lab => S p d lab) (T := fun p lab => T p d lab)
      (fun lab hS => hST p d lab hshape hS) hlab)

theorem GGBstarAbelianPreimageJUniS1OnDeg.or {S T : ℕ → ℕ → LargeEvenLabel → Prop}
    (hS : GGBstarAbelianPreimageJUniS1OnDeg S) (hT : GGBstarAbelianPreimageJUniS1OnDeg T) :
    GGBstarAbelianPreimageJUniS1OnDeg (fun p d lab => S p d lab ∨ T p d lab) := by
  intro G _ _ p B Bs x L D J hcfg hID hN d m hshape hpm hdm E _ hE θ hlab
  rcases GGInnerDiagOnLab.elim_or (S := fun p lab => S p d lab) (T := fun p lab => T p d lab)
    hlab with h | h
  · exact hS G p B Bs x L D J hcfg hID hN d m hshape hpm hdm E hE θ h
  · exact hT G p B Bs x L D J hcfg hID hN d m hshape hpm hdm E hE θ h

theorem ggBstarAbelianPreimageJUniS1On_of_deg {S : ℕ → LargeEvenLabel → Prop}
    (h : GGBstarAbelianPreimageJUniS1OnDeg (fun p _ lab => S p lab)) :
    GGBstarAbelianPreimageJUniS1On S := by
  intro G _ _ p B Bs x L D J hcfg hID hN d m hshape hpm hdm E _ hE θ hlab
  exact h G p B Bs x L D J hcfg hID hN d m hshape hpm hdm E hE θ hlab

theorem GGBstarAbelianPreimageJUniS1On.toDeg {S : ℕ → LargeEvenLabel → Prop}
    (h : GGBstarAbelianPreimageJUniS1On S) :
    GGBstarAbelianPreimageJUniS1OnDeg (fun p _ lab => S p lab) := by
  intro G _ _ p B Bs x L D J hcfg hID hN d m hshape hpm hdm E _ hE θ hlab
  exact h G p B Bs x L D J hcfg hID hN d m hshape hpm hdm E hE θ hlab

theorem GGBstarAbelianPreimageJUniS1OnDeg.of_rLevel {S : ℕ → LargeEvenLabel → Prop}
    {T : ℕ → ℕ → LargeEvenLabel → Prop} (h : Q2URLevel S)
    (hTS : ∀ p d lab, ((p = 3 ∧ (d = 3 ∨ d = 6)) ∨ (p = 5 ∧ d = 5)) → T p d lab → S p lab) :
    GGBstarAbelianPreimageJUniS1OnDeg T :=
  GGBstarAbelianPreimageJUniS1OnDeg.mono hTS (ggBstarAbelianPreimageJUniS1On_of_rLevel h).toDeg

theorem GGBstarAbelianPreimageJUniS1OnDeg.of_rLevelToral
    {Toral : (R : Type) → [Group R] → Subgroup (MulAut R) → Prop}
    {S : ℕ → LargeEvenLabel → Prop} {T : ℕ → ℕ → LargeEvenLabel → Prop}
    (hTor : Q2UConfigToral Toral S) (h : Q2URLevelOn Toral S)
    (hTS : ∀ p d lab, ((p = 3 ∧ (d = 3 ∨ d = 6)) ∨ (p = 5 ∧ d = 5)) → T p d lab → S p lab) :
    GGBstarAbelianPreimageJUniS1OnDeg T :=
  GGBstarAbelianPreimageJUniS1OnDeg.mono hTS
    (ggBstarAbelianPreimageJUniS1On_of_rLevelToral hTor h).toDeg

private theorem not_ggLabelIso_C_three_twA {n r m : ℕ} :
    ¬ GGLabelIso (⟨.C, 3, n⟩ : LargeEvenLabel) (⟨.twA, r, m⟩ : LargeEvenLabel) := by
  intro h
  simp only [GGLabelIso] at h
  rcases h with h | h | h | h | h | h | h | h <;> simp_all

private theorem pow_four_le_card_gamma_J_of_torusLift {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig 3 B Bs x L D J)
    (hN : Bs ≤ Subgroup.normalizer (J : Set G)) {R : Type} [Group R]
    (θ : ↥J ⧸ Subgroup.center ↥J ≃* R) (hT : GGTorusLift 3 3 R)
    (hBs : 3 ^ 6 ≤ Nat.card Bs) :
    3 ^ 4 ≤ Nat.card (ggGamma J hN).range := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hJperf : commutator ↥J = ⊤ := hcfg.2.2.1.2.2.2.2.2.1.2.2.1
  set E : Subgroup G := Bs ⊓ Subgroup.centralizer (J : Set G) with hEdef
  have hEel : IsElemAbelian 3 E := TableB.isElemAbelian_mono hcfg.2.1.2.1 inf_le_left
  have hEC : E ≤ Subgroup.centralizer (J : Set G) := inf_le_right
  have hlift := CFSG.LocalAnalysis.GLTheoremA.S265.SF.pow_mul_card_le_of_torusLift
    (Ω := G) (K := J) (D := E) hp hJperf θ hT hEel hEC
  have hrank : CFSG.Open.GLATwoLocalRank 3 G = LargeEvenTwoLocalRank 3 G := rfl
  rw [hrank] at hlift
  have hgamma := hcfg.pow_le_card_gamma_J hN
  have hker : (ggGamma J hN).ker = (Subgroup.centralizer (J : Set G)).subgroupOf Bs := by
    ext b
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ggGamma_eq_one_iff]
  have hkerCard : Nat.card ↥((Subgroup.centralizer (J : Set G)).subgroupOf Bs) = Nat.card E := by
    rw [hEdef, ← Subgroup.inf_subgroupOf_left]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hcount := TableB.card_range_mul_card_ker (ggGamma J hN)
  rw [hker, hkerCard] at hcount
  by_contra hlt
  have hlt' : Nat.card (ggGamma J hN).range < 81 := by
    have h := not_le.mp hlt
    have h4 : (3 : ℕ) ^ 4 = 81 := by norm_num
    simpa only [h4] using h
  have ha80 : Nat.card (ggGamma J hN).range ≤ 80 := by omega
  have he10 : 10 ≤ Nat.card E := by
    by_contra h
    have he9 : Nat.card E ≤ 9 := by omega
    have hmul' : Nat.card (ggGamma J hN).range * Nat.card E ≤ 80 * 9 :=
      Nat.mul_le_mul ha80 he9
    omega
  have h270 : 270 ≤ 3 ^ LargeEvenTwoLocalRank 3 G := by
    have hlift' : 27 * Nat.card E ≤ 3 ^ LargeEvenTwoLocalRank 3 G := by
      simpa using hlift
    omega
  have hM : 6 ≤ LargeEvenTwoLocalRank 3 G := by
    have h1 : 3 ^ 5 < 3 ^ LargeEvenTwoLocalRank 3 G := by
      have h243 : (3 : ℕ) ^ 5 = 243 := by norm_num
      rw [h243]
      exact lt_of_lt_of_le (by norm_num) h270
    exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).mp h1
  have ha : 3 ^ 4 ≤ Nat.card (ggGamma J hN).range :=
    (Nat.pow_le_pow_right (by norm_num : 0 < 3)
      (show 4 ≤ LargeEvenTwoLocalRank 3 G - 2 by omega)).trans hgamma
  have ha81 : (81 : ℕ) ≤ Nat.card (ggGamma J hN).range := by
    have h4 : (3 : ℕ) ^ 4 = 81 := by norm_num
    simpa only [h4] using ha
  omega

private theorem not_ordTwistedA_two_dvd_ordE6_two {m : ℕ} (hm : 3 ≤ m) :
    ¬ ordTwistedA 2 (2 ^ m) ∣ ordE6 2 := by
  intro hdvd
  obtain ⟨p, hp, hpU⟩ :=
    CFSG.StandardType.SCFourCover.exists_ppd_dvd_ordTwistedA_two (m := m) (by omega)
  have hZ := ((CFSG.SeitzReduction.F4Pilot.EvenExc.profile_ordE6' (e := 1) le_rfl).prim
    p (6 * m) hp (by omega)).1 (hpU.trans hdvd)
  rcases hZ with h | h | h | h | h | h <;>
    (have hle := Nat.le_of_dvd (by norm_num) h; omega)

private theorem ordTwistedA_dvd_card_of_unitary_component
    {R : Type} [Group R] {d m : ℕ} {E : Type} [Field E]
    (hE : UnitaryFieldData 2 m E) (hadm : StatedLieAdmissible .PSU d 2 m) {J : Subgroup R}
    (θ : ↥J ⧸ Subgroup.center ↥J ≃*
      LargeEvenProj (LargeEvenSUGroup (Fin d) E (2 ^ m))) :
    ordTwistedA (d - 1) (2 ^ m) ∣ Nat.card R := by
  haveI : Finite E := hE.finite
  have hcardJZ : Nat.card (↥J ⧸ Subgroup.center ↥J) = ordTwistedA (d - 1) (2 ^ m) := by
    rw [Nat.card_congr θ.toEquiv]
    have hEcard : Nat.card E = (2 ^ m) ^ 2 := by
      rw [hE.card, ← pow_mul, Nat.mul_comm 2 m]
    exact (CFSG.Timmesfeld.card_statedClassicalModel_two
      (statedClassicalModel_unitary (K := E) d m hEcard hadm)).2.1 rfl
  calc ordTwistedA (d - 1) (2 ^ m)
      = Nat.card (↥J ⧸ Subgroup.center ↥J) := hcardJZ.symm
    _ ∣ Nat.card ↥J := Subgroup.card_quotient_dvd_card _
    _ ∣ Nat.card R := Subgroup.card_subgroup_dvd_card J

private theorem not_ordTwistedA_dvd_ordE6_two_of_shape {d m : ℕ} (hd36 : d = 3 ∨ d = 6)
    (hm1 : 1 ≤ m) (hpm : 3 ∣ 2 ^ m + 1) (hdm : ¬ (d = 3 ∧ m = 1)) :
    ¬ ordTwistedA (d - 1) (2 ^ m) ∣ ordE6 2 := by
  rcases hd36 with rfl | rfl
  · have hm3 : 3 ≤ m := by
      have hne1 : m ≠ 1 := fun h => hdm ⟨rfl, h⟩
      have hne2 : m ≠ 2 := fun h =>
        (by norm_num : ¬ (3 ∣ 2 ^ 2 + 1)) (by simpa [h] using hpm)
      omega
    exact not_ordTwistedA_two_dvd_ordE6_two hm3
  · intro h
    exact CFSG.StandardType.SCFourCover.not_ordTwistedA_five_dvd_ordE6 (g := 1) (n := m)
      le_rfl hm1 (one_dvd m) (by simpa using h)

section ExcThree


private theorem q2URLevel_E6Two :
    Q2URLevel (fun p lab => lab.tag = .E6 ∧ lab.n = 1 ∧ p = 3) := by
  intro p d m lab hlab hS hsplit hshape hpm hdm Q hQ
  obtain ⟨tag, rank, n⟩ := lab
  dsimp only at hS
  obtain ⟨htag, hn1, hp3⟩ := hS
  subst htag
  subst hn1
  subst hp3
  have hd36 : d = 3 ∨ d = 6 := by
    rcases hshape with ⟨_, h⟩ | ⟨h, _⟩
    · exact h
    · omega
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, fieldK, finiteK, hK, hQK⟩ := hQ
  letI : Field K := fieldK
  letI : Finite K := finiteK
  have hK2 : Nat.card K = 2 := by rw [hK]; norm_num
  have hRcard : Nat.card (LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 6) K false))
      = ordE6 2 := by
    change Nat.card (TableBExc.RecipeGroup .E6 K) = ordE6 2
    rw [Nat.card_congr (TableBExc.recipeEquiv .E6 K).toEquiv,
      CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E6, hK2]
  refine ⟨K, fieldK, finiteK, hK, hQK, ?_⟩
  intro A hAbil hAI _ u hu huord J hJ hAJ E _ hE hJE M hM
  obtain ⟨θ⟩ := hJE
  have hadm : StatedLieAdmissible .PSU d 2 m := by
    have hd3 : 3 ≤ d := by rcases hd36 with rfl | rfl <;> norm_num
    have hne : (d, 2 ^ m) ≠ (3, 2) := by
      intro h
      obtain ⟨hd, h2⟩ := Prod.mk.inj h
      exact hdm ⟨hd, Nat.pow_right_injective (le_refl 2) (h2.trans (by norm_num))⟩
    exact ⟨Nat.prime_two, hE.one_le, hd3, hne⟩
  have hdvd : ordTwistedA (d - 1) (2 ^ m) ∣ ordE6 2 := by
    rw [← hRcard]
    exact ordTwistedA_dvd_card_of_unitary_component hE hadm θ
  exact (not_ordTwistedA_dvd_ordE6_two_of_shape hd36 hE.one_le hpm hdm hdvd).elim

theorem ggBstarAbelianPreimageJUniS1On_E6Two :
    GGBstarAbelianPreimageJUniS1On (fun p lab => lab.tag = .E6 ∧ lab.n = 1 ∧ p = 3) :=
  ggBstarAbelianPreimageJUniS1On_of_rLevel q2URLevel_E6Two

theorem ggBstarAbelianPreimageJUniS1On_F4Three :
    GGBstarAbelianPreimageJUniS1On (fun p lab => lab.tag = .F4 ∧ p = 3) := by
  intro G _ _ p B Bs x L D J hcfg hID hN d m hshape hpm hdm E _ hE θ hlab
  have hmark : GGInnerDiagOnLabel (fun _ lab => lab.tag = .F4) p Bs L :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ h => ⟨h.1.1, h.2.2.1, h.2.2.2⟩) hlab
  obtain ⟨_hperf, _lab0, _hlab0, hraw0⟩ := hlab
  obtain ⟨R0, _hR0, I0, F0, hQ0⟩ := largeEvenRawDatum_exists hraw0
  obtain ⟨_hs0, _hna0, hθ0⟩ := hQ0
  obtain ⟨_θ0, hP0⟩ := hθ0
  obtain ⟨hS0, _hsplit0, _hNL0, _hact0⟩ := hP0
  have hp3 : p = 3 := hS0.2
  subst hp3
  obtain ⟨δ, hdat, huniq⟩ :=
    exists_ggTorsionDatum_unique_of_innerDiagOnLabel (fun lab => lab.tag = .F4)
      hcfg.1 hcfg.2.2 hcfg.2.1.1 hmark
  have hF4 := ggTorsion_f4_comp hdat
  obtain ⟨_hXL, labX, hlabX, hrawX⟩ := hF4
  obtain ⟨RX, _hRX, IX, FX, hQX⟩ := largeEvenRawDatum_exists hrawX
  obtain ⟨_hsX, _hnaX, hθX⟩ := hQX
  obtain ⟨_θX, hPX⟩ := hθX
  obtain ⟨_htagX, hcompX⟩ := hPX
  have hJL : J ≤ L := hcfg.2.2.1.2.2.2.2.2.1.1.trans inf_le_left
  have hm : 1 ≤ m := hE.one_le
  have hd36 : d = 3 ∨ d = 6 := by
    rcases hshape with ⟨_, h⟩ | ⟨h, _⟩
    · exact h
    · exact absurd h (by norm_num)
  have hΛtwA : LargeEvenInLambda2 (⟨.twA, d - 1, m⟩ : LargeEvenLabel) := by
    refine ⟨hm, show 2 ≤ d - 1 by omega, ?_⟩
    show d - 1 = 2 → 2 ≤ m
    intro h
    have hd3 : d = 3 := by omega
    by_contra hm2
    exact hdm ⟨hd3, by omega⟩
  have hHasTwA : GGHasLabel (⟨.twA, d - 1, m⟩ : LargeEvenLabel)
      (↥J ⧸ Subgroup.center ↥J) := by
    haveI : Finite E := hE.finite
    dsimp only [GGHasLabel, LargeEvenRawDatum, LargeEvenRecipeUnitary]
    refine ⟨E, inferInstance, inferInstance, ?_, ?_⟩
    · rw [hE.card, ← pow_mul, Nat.mul_comm 2 m]
    · rw [Nat.sub_add_cancel (by omega : 1 ≤ d)]
      exact ⟨θ⟩
  rcases hcompX with ⟨J', hJ'comp, hJ'ne⟩ | hC3
  · exact absurd (huniq J' hJ'comp) hJ'ne
  · have hC3' : GGHasLabel (⟨.C, 3, labX.n⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J) :=
      ggHasLabel_of_mulEquiv (centerQuotCongr (Subgroup.subgroupOfEquivOfLe hJL)) hC3
    have hΛC : LargeEvenInLambda2 (⟨.C, 3, labX.n⟩ : LargeEvenLabel) := by
      refine ⟨hlabX.1, by norm_num, ?_⟩
      intro h
      norm_num at h
    exact (not_ggLabelIso_C_three_twA
      (ggLabelRigidInput_holds (⟨.C, 3, labX.n⟩ : LargeEvenLabel)
        (⟨.twA, d - 1, m⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J)
        hΛC hΛtwA hC3' hHasTwA)).elim

theorem ggBstarAbelianPreimageJUniS1OnDeg_twE6_d3 :
    GGBstarAbelianPreimageJUniS1OnDeg
      (fun p d lab => d = 3 ∧ lab.tag = .twE6 ∧ p = 3) := by
  intro G _ _ p B Bs x L D J hcfg hInner hN d m hshape hpm hdm E _ hE θ hlab
  obtain ⟨_, lab, hΛ, hraw⟩ := hlab
  obtain ⟨tag, rank, n⟩ := lab
  obtain ⟨_, _, _, _, _, _, _, hP, hrest⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨hd3, htag0, hp3⟩ := hP
  dsimp only at htag0
  subst htag0
  subst hp3
  subst hd3
  obtain ⟨hsplit, _, _⟩ := hrest
  have hd : 3 ∣ 2 ^ n + 1 := by
    have hs := hsplit
    simp [LargeEvenSplit, LargeEvenUntwisted] at hs
    rcases hs with h | h
    · exact h
    · rw [h]; norm_num
  obtain ⟨K, instK, finK, hK, hQ⟩ := hraw
  obtain ⟨-, -, θL, -⟩ := hQ
  have hlift := ggTorusLift_twE6Three hΛ.1 hK hd
  exact q2Uni_comm_of_torusLift hcfg hInner hN (by norm_num) hdm hE θ
    Nat.prime_three (by norm_num) hpm hInner.1 θL hlift (by norm_num)

theorem ggBstarAbelianPreimageJUniS1OnDeg_twE6_d6 :
    GGBstarAbelianPreimageJUniS1OnDeg
      (fun p d lab => d = 6 ∧ lab.tag = .twE6 ∧ p = 3) := by
  intro G _ _ p B Bs x L D J hcfg hInner hN d m _ hpm hdm E _ hE θ hlab
  have hlab' := hlab
  obtain ⟨_, lab, _, hraw⟩ := hlab
  obtain ⟨_, _, _, _, _, _, _, hPlab, _⟩ := largeEvenRawDatum_exists hraw
  have hp3 : p = 3 := hPlab.2.2
  have hd6 : d = 6 := hPlab.1
  have hmarkLab : GGInnerDiagOnLab GGTableBTwE6ThreeLabel p Bs L :=
    GGInnerDiagOnLab.mono_of_split
      (S := fun p lab => d = 6 ∧ lab.tag = .twE6 ∧ p = 3)
      (T := GGTableBTwE6ThreeLabel)
      (fun lab hS hsplit => by
        refine ⟨hS.2.1, hS.2.2, ?_⟩
        rw [hS.2.2] at hsplit
        unfold LargeEvenSplit at hsplit
        rcases hsplit with hu | h2 | h3 | h4
        · rw [hS.2.1] at hu
          exact absurd hu.1 (by simp [LargeEvenUntwisted])
        · exact h2.2.2
        · rcases h3.1 with h | h
          · rw [hS.2.1] at h
            exact absurd h (by intro hh; cases hh)
          · rw [hS.2.1] at h
            exact absurd h (by intro hh; cases hh)
        · rw [h4.1]
          norm_num) hlab'
  subst hp3
  have hNL : Bs ≤ Subgroup.normalizer (L : Set G) :=
    GGDichotomy.le_normalizer_of_innerDiagOn hInner
  have h5 : 3 ^ 5 ≤ Nat.card (ggGamma L hNL).range :=
    ggTwE6ThreeBstarRankInput_holds G 3 B Bs x L D J hcfg hmarkLab hNL
  obtain ⟨hpr, hBsE, hxBs, hLx, -⟩ := hcfg.tableB_facts
  have hS : LargeEvenSStar 3 B x L := hcfg.1.2.2.2.2.2.2.1
  have hmul := card_range_ggGamma_mul_of hpr hBsE hxBs hS.2.2.1 hLx hS.2.2.2.2 hNL
  have hbs6 : 3 ^ 6 ≤ Nat.card Bs := by
    calc 3 ^ 6 = 3 ^ 5 * 3 := by norm_num
      _ ≤ Nat.card (ggGamma L hNL).range * 3 := Nat.mul_le_mul_right 3 h5
      _ = Nat.card Bs := hmul
  subst hd6
  haveI : Finite E := hE.finite
  have hK : Nat.card E = (2 ^ m) ^ 2 := by
    rw [hE.card, ← pow_mul, Nat.mul_comm 2 m]
  have hm : 1 ≤ m := hE.one_le
  have hlift : GGTorusLift 3 (ggUnitaryTorusRank 3 6)
      (LargeEvenProj (LargeEvenSUGroup (Fin 6) E (2 ^ m))) :=
    ggTorusLift_unitary (K := E) (n := m) (d := 6) hK hm (by norm_num) (by simp)
      Nat.prime_three hpm
  have hlift3 : GGTorusLift 3 3
      (LargeEvenProj (LargeEvenSUGroup (Fin 6) E (2 ^ m))) := by
    simpa [ggUnitaryTorusRank] using hlift
  have hcard : 3 ^ (6 / 3 + 2) ≤ Nat.card (ggGamma J hN).range :=
    pow_four_le_card_gamma_J_of_torusLift hcfg hN θ hlift3 hbs6
  exact q2Uni_comm_of_large_gamma hcfg hInner hN (by norm_num) hdm hE θ (by norm_num) hpm hcard

theorem ggBstarAbelianPreimageJUniS1On_excThree :
    GGBstarAbelianPreimageJUniS1On (fun p lab => (lab.tag = .E6 ∧ lab.n = 1 ∧ p = 3) ∨
      (lab.tag = .F4 ∧ p = 3) ∨ (lab.tag = .twE6 ∧ p = 3)) := by
  refine ggBstarAbelianPreimageJUniS1On_of_deg
    (GGBstarAbelianPreimageJUniS1OnDeg.mono (fun p d lab hshape hres => ?_)
      (ggBstarAbelianPreimageJUniS1On_E6Two.toDeg.or
        (ggBstarAbelianPreimageJUniS1On_F4Three.toDeg.or
          (ggBstarAbelianPreimageJUniS1OnDeg_twE6_d3.or
            ggBstarAbelianPreimageJUniS1OnDeg_twE6_d6))))
  rcases hres with hE6 | hF4 | ⟨ht, hp⟩
  · exact Or.inl hE6
  · exact Or.inr (Or.inl hF4)
  · have hd : d = 3 ∨ d = 6 := by
      rcases hshape with ⟨_, h⟩ | ⟨h5, _⟩
      · exact h
      · omega
    rcases hd with hd | hd
    · exact Or.inr (Or.inr (Or.inl ⟨hd, ht, hp⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hd, ht, hp⟩))

end ExcThree

end CFSG.StandardType
