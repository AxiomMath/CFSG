module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Std
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Fix
public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerGaussUnitary
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC34Unique
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Q1A
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5JP
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem s16h_bb_conjSubgroup_le_of_mem {A M : Subgroup G} (hA : A ≤ M) {x : G}
    (hx : x ∈ M) : conjSubgroup A x ≤ M := by
  intro y hy
  rw [mem_conjSubgroup_iff] at hy
  have h1 : x⁻¹ * (x * y * x⁻¹) * x ∈ M := M.mul_mem (M.mul_mem (M.inv_mem hx) (hA hy)) hx
  have e : x⁻¹ * (x * y * x⁻¹) * x = y := by group
  rwa [e] at h1

private theorem s16h_bb_barSub_sup {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    {A B : Subgroup G} (hA : A ≤ stabTil V₀ V) (hB : B ≤ stabTil V₀ V) :
    barSub V₀ V hV (A ⊔ B) = barSub V₀ V hV A ⊔ barSub V₀ V hV B := by
  unfold barSub
  rw [Subgroup.subgroupOf_sup hA hB, Subgroup.map_sup]

private theorem s16h_bb_exists_Eb_of_dvd_CTilde (D : Data G) (S : s16h_Std D)
    {V₀ V L : Subgroup G} (h : Setting16 D V₀ V L)
    (hs2 : s15 D.M V₀ V h.hyp151.isElemAbelian L = 2)
    (hcomp : IsComponentOf (lBar V₀ V h.hyp151.isElemAbelian L)
      (Mbar D.M V₀ V h.hyp151.isElemAbelian))
    (h3L : 3 ∣ Nat.card ↥(lBar V₀ V h.hyp151.isElemAbelian L))
    (h3C : 3 ∣ Nat.card ↥(F11.CTilde D.M V₀ V)) :
    ∃ E : Subgroup G, E ≤ D.M ∧ IsElemAbelian 3 E ∧ Nat.card ↥E = 9 ∧
      E ≤ preBarSub D.M V₀ V h.hyp151.isElemAbelian
        (centSub (wTil V₀ V h.hyp151.isElemAbelian L)) := by
  have hV := h.hyp151.isElemAbelian
  have hnorm : D.M ≤ normalizer (V : Set G) := h.hyp151.hyp125.pairFacts.le_normalizer
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil hnorm h.hyp151.hyp125.pairFacts.le_normalizer₀
  obtain ⟨x, hx, hxn⟩ := s16c34_exists_not_mem_nBar D h.hyp151 (by rw [hs2]; norm_num)
  have hLxM : conjSubgroup L x ≤ D.M := s16h_bb_conjSubgroup_le_of_mem h.hyp151.le hx
  have hCTM : F11.CTilde D.M V₀ V ≤ D.M := fun g hg => ((mem_cTilde_iff hV hnorm).1 hg).1
  let Hsub : Subgroup G := conjSubgroup L x ⊔ F11.CTilde D.M V₀ V
  have hHM : Hsub ≤ D.M := sup_le hLxM hCTM
  have hHstab : Hsub ≤ stabTil V₀ V := sup_le (hLxM.trans hMs) (hCTM.trans hMs)
  let φ : ↥Hsub →* MulAut (Vtil V₀ V hV) :=
    (actTil V₀ V hV).comp (Subgroup.inclusion hHstab)
  have hker : φ.ker = (F11.CTilde D.M V₀ V).subgroupOf Hsub := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hg
      refine (mem_cTilde_iff hV hnorm).2 ⟨hHM g.2, hHstab g.2, ?_⟩
      show actTil V₀ V hV (Subgroup.inclusion hHstab g) = 1
      exact hg
    · intro hg
      obtain ⟨-, hgs, h1⟩ := (mem_cTilde_iff hV hnorm).1 hg
      show φ g = 1
      change actTil V₀ V hV (Subgroup.inclusion hHstab g) = 1
      rw [show Subgroup.inclusion hHstab g = (⟨(g : G), hgs⟩ : stabTil V₀ V) from
        Subtype.ext rfl, h1]
  have hrangeH : φ.range = barSub V₀ V hV Hsub := by
    ext ψ
    constructor
    · rintro ⟨g, rfl⟩
      exact actTil_mem_barSub V₀ V hV g.2 (hHstab g.2)
    · intro hψ
      obtain ⟨g, hgH, hgψ⟩ := (mem_barSub V₀ V hV Hsub ψ).1 hψ
      exact ⟨⟨g, hgH⟩, hgψ⟩
  have hCT_le_H : F11.CTilde D.M V₀ V ≤ Hsub := le_sup_right
  have hbarCT : barSub V₀ V hV (F11.CTilde D.M V₀ V) = ⊥ := by
    rw [cTilde_eq_preBarSub_bot hV hnorm, barSub_preBarSub]
    exact (bot_inf_eq (Mbar D.M V₀ V hV) : (⊥ : Subgroup (MulAut (Vtil V₀ V hV))) ⊓
      Mbar D.M V₀ V hV = ⊥)
  have hrange : φ.range = barSub V₀ V hV (conjSubgroup L x) := by
    rw [hrangeH]
    change barSub V₀ V hV (conjSubgroup L x ⊔ F11.CTilde D.M V₀ V) =
      barSub V₀ V hV (conjSubgroup L x)
    rw [s16h_bb_barSub_sup hV (hLxM.trans hMs) (hCTM.trans hMs), hbarCT, sup_bot_eq]
  have hHsubX : Hsub ≤ preBarSub D.M V₀ V hV (centSub (wTil V₀ V hV L)) := by
    refine sup_le ?_ ?_
    · intro g hg
      have hgM : g ∈ D.M := hLxM hg
      have hgs : g ∈ stabTil V₀ V := hMs hgM
      refine (mem_preBarSub D.M V₀ V hV _).2 ⟨hgM, hgs, ?_⟩
      have hmem : actTil V₀ V hV ⟨g, hgs⟩ ∈ barSub V₀ V hV (conjSubgroup L x) :=
        actTil_mem_barSub V₀ V hV hg hgs
      have hcent : barSub V₀ V hV (conjSubgroup L x) ≤ centSub (wTil V₀ V hV L) := by
        intro y hy
        rw [mem_centSub]
        intro u hu
        exact (commSub_eq_bot_iff.mp (h.hyp151.commute x hx hxn).2 hu) y hy
      exact hcent hmem
    · intro g hg
      obtain ⟨hgM, hgs, h1⟩ := (mem_cTilde_iff hV hnorm).1 hg
      refine (mem_preBarSub D.M V₀ V hV _).2 ⟨hgM, hgs, ?_⟩
      rw [h1]
      exact Subgroup.one_mem _
  haveI : Group.IsPerfect ↥(barSub V₀ V hV L) := ⟨hcomp.2.2.1⟩
  have hperfBar : Group.IsPerfect ↥(barSub V₀ V hV (conjSubgroup L x)) := by
    rw [s15_Infra_barSub_conjSubgroup V₀ V hV (hMs hx) L]
    exact Group.IsPerfect.map (MulAut.conj (actTil V₀ V hV ⟨x, hMs hx⟩)⁻¹).toMonoidHom
  have hiso : (↥Hsub ⧸ φ.ker) ≃*
      ↥(barSub V₀ V hV (conjSubgroup L x)) :=
    (QuotientGroup.quotientKerEquivRange φ).trans (MulEquiv.subgroupCongr hrange)
  have hperf : Group.IsPerfect (↥Hsub ⧸ φ.ker) :=
    Group.IsPerfect.ofSurjective (f := hiso.symm.toMonoidHom) hiso.symm.surjective
  have hcard1 : Nat.card (↥Hsub ⧸ φ.ker) =
      Nat.card ↥(barSub V₀ V hV (conjSubgroup L x)) := Nat.card_congr hiso.toEquiv
  have hcard2 : Nat.card ↥(barSub V₀ V hV (conjSubgroup L x)) =
      Nat.card ↥(lBar V₀ V hV L) := by
    rw [s15_Infra_barSub_conjSubgroup V₀ V hV (hMs hx) L]
    exact Subgroup.card_map_of_injective (MulAut.conj _).injective
  have h1 : 3 ∣ Nat.card (↥Hsub ⧸ φ.ker) := by
    rw [hcard1, hcard2]
    exact h3L
  have hcardC : Nat.card ↥φ.ker = Nat.card ↥(F11.CTilde D.M V₀ V) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCT_le_H).toEquiv
  have h2 : 3 ∣ Nat.card ↥φ.ker := by
    rw [hcardC]
    exact h3C
  obtain ⟨P, hPp, hPc⟩ := s16h_exists_noncyclic_pgroup_of_perfect_quotient
    (H := ↥Hsub) (C := φ.ker) Nat.prime_three (by norm_num) hperf h1 h2
  let P' : Subgroup G := P.map Hsub.subtype
  have hP'le : P' ≤ Hsub := Subgroup.map_subtype_le P
  have hPe : P ≃* P' := Subgroup.equivMapOfInjective P Hsub.subtype Hsub.subtype_injective
  have hP'p : IsPGroup 3 P' := hPp.of_equiv hPe
  have hP'c : ¬ IsCyclic ↥P' := fun hc => hPc (hPe.isCyclic.2 hc)
  haveI : Fact (IsPGroup 3 ↥P') := ⟨hP'p⟩
  obtain ⟨E', _, hE'card, hE'el⟩ := CFSG.lemma_4_5_a (p := 3) (R := ↥P') (by norm_num) hP'c
  let E : Subgroup G := E'.map P'.subtype
  have hE_le_P' : E ≤ P' := Subgroup.map_subtype_le E'
  have hEP : E ≤ Hsub := hE_le_P'.trans hP'le
  have hEab : IsElemAbelian 3 E := by
    have hE'ab : IsElemAbelian 3 E' :=
      (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 E').mp hE'el
    exact CFSG.SectionRank.isElemAbelian_map (E := E') hE'ab P'.subtype
  have hEcard : Nat.card ↥E = 9 := by
    rw [Subgroup.card_subtype P' E', hE'card]
    norm_num
  exact ⟨E, hEP.trans hHM, hEab, hEcard, hEP.trans hHsubX⟩

theorem s16h_e3_l3_three_ne_bot_dim_le_two_not_dvd_CTilde
    (D : Data G) (S : s16h_Std D) (hσ : D.sig = D.sig1)
    (hJP : K_JonesParshallH1) {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    (hs2 : s15 D.M ⊥ V h.hyp151.isElemAbelian L = 2)
    {t : MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)} (ht : t ∈ Mbar D.M ⊥ V h.hyp151.isElemAbelian)
    (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) (htr : rk ↥(commSub ⊤ (zpowers t)) ≤ 3)
    (hW : Conc4_136W (Mbar D.M ⊥ V h.hyp151.isElemAbelian) t (lBar ⊥ V h.hyp151.isElemAbelian L))
    (hcomp : IsComponentOf (lBar ⊥ V h.hyp151.isElemAbelian L)
      (Mbar D.M ⊥ V h.hyp151.isElemAbelian))
    (hthin : ∀ q : ℕ, q.Prime → q ≠ 2 →
      CFSG.Open.pRank q (lBar ⊥ V h.hyp151.isElemAbelian L) ≤ 1)
    (hZ : commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L) ≠ ⊥)
    (hbad : ∀ q ∈ D.sig, ∀ E : Subgroup G, E ≤ D.M → IsElemAbelian q E →
      Nat.card ↥(E ⊓ preBarSub D.M ⊥ V h.hyp151.isElemAbelian
        (centSub (wTil ⊥ V h.hyp151.isElemAbelian L))) < q ^ 2)
    (hrow : s16h_H5RowL3 (lBar ⊥ V h.hyp151.isElemAbelian L)
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L))
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L)))
    (hL3 : s16h_H5L3Sum (lBar ⊥ V h.hyp151.isElemAbelian L)
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L))
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) 3)
    (hd2 : rk ↥(commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) ≤ 2)
    (hsig : D.sig = {3}) :
    ¬ 3 ∣ Nat.card ↥(F11.CTilde D.M ⊥ V) := by
  intro h3C
  have hV := h.hyp151.isElemAbelian
  obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := hL3.1
  have h168 : Nat.card ↥(lBar ⊥ V hV L) = 168 := by
    rw [Nat.card_congr e.toEquiv,
      CFSG.Open.StatedAPI.card_statedSL_three_of_card_eq_two (K := K) (by simpa using hKcard)]
  have h3L : 3 ∣ Nat.card ↥(lBar ⊥ V hV L) := by
    rw [h168]
    norm_num
  obtain ⟨E, hEM, hEab, hEcard, hEX⟩ :=
    s16h_bb_exists_Eb_of_dvd_CTilde D S h hs2 hcomp h3L h3C
  have h3mem : 3 ∈ D.sig := by rw [hsig]; exact Set.mem_singleton 3
  have hlt := hbad 3 h3mem E hEM hEab
  have hEq : E ⊓ preBarSub D.M ⊥ V h.hyp151.isElemAbelian
      (centSub (wTil ⊥ V h.hyp151.isElemAbelian L)) = E := inf_eq_left.mpr hEX
  rw [hEq, hEcard] at hlt
  norm_num at hlt

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
