module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2UniBlockType
public import CFSG.LocalAnalysis.StandardType.GGCentInnerDiagModel
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthogonalBasic
import CFSG.GroupTheory.ABGDGroups.LinearCentralizers
import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2OmegaSelect
import CFSG.GroupTheory.IsComponentOfMap
import CFSG.GroupTheory.ConjKerCenter
import CFSG.LocalAnalysis.ComponentInitial.DerivedFixedLayer
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Label
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinDict
import CFSG.LocalAnalysis.StandardType.MarkingClassical
import CFSG.LocalAnalysis.StandardType.GGTypeANbrLabels
import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCatTypeDet
import CFSG.Timmesfeld.Orders.Distinct
import CFSG.Timmesfeld.Orders.Classical

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial
open CFSG.Open (StatedOmega)
open CFSG.StandardType.ClassicalPosition CFSG.StandardType.ClassicalBlocks
open CFSG.LocalAnalysis.GLTheoremA.Y10F

private theorem cuq2om_card_D {X : Type} [Group X] {r n : ℕ} (hr : 4 ≤ r) (hn : 1 ≤ n)
    (hX : GGHasLabel (⟨.D, r, n⟩ : LargeEvenLabel) X) :
    Nat.card X = CFSG.Open.ordD r (2 ^ n) := by
  classical
  dsimp only [GGHasLabel, CFSG.StandardType.LargeEvenRawDatum] at hX
  rw [if_neg (by omega : r ≠ 3)] at hX
  obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := hX
  letI : Field K := hKf
  letI : Finite K := hKfin
  have hadm : CFSG.Open.StatedLieAdmissible .POmegaPlus r 2 n := ⟨Nat.prime_two, hn, hr⟩
  have hM := statedClassicalModel_omegaPlus r n hKcard hadm
  exact (CFSG.Timmesfeld.card_statedClassicalModel_two
    (CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e.symm hM)).2.2.2.1 rfl

private theorem cuq2om_card_twD {X : Type} [Group X] {r n : ℕ} (hr : 4 ≤ r) (hn : 1 ≤ n)
    (hX : GGHasLabel (⟨.twD, r, n⟩ : LargeEvenLabel) X) :
    Nat.card X = CFSG.Open.ordTwistedD r (2 ^ n) := by
  classical
  dsimp only [GGHasLabel, CFSG.StandardType.LargeEvenRawDatum] at hX
  rw [if_neg (by omega : r ≠ 2), if_neg (by omega : r ≠ 3)] at hX
  obtain ⟨K, hKf, hKfin, hKcard, b, c, hbc, ⟨e⟩⟩ := hX
  letI : Field K := hKf
  letI : Finite K := hKfin
  have hadm : CFSG.Open.StatedLieAdmissible .POmegaMinus r 2 n := ⟨Nat.prime_two, hn, hr⟩
  have hM := statedClassicalModel_omegaMinus r n hKcard b c hbc hadm
  exact (CFSG.Timmesfeld.card_statedClassicalModel_two
    (CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e.symm hM)).2.2.2.2 rfl

private theorem cuq2om_card_A {X : Type} [Group X] {r n : ℕ}
    (hΛ : LargeEvenInLambda2 (⟨.A, r, n⟩ : LargeEvenLabel))
    (hX : GGHasLabel (⟨.A, r, n⟩ : LargeEvenLabel) X) :
    Nat.card X = CFSG.Open.ordA r (2 ^ n) := by
  have hM := statedClassicalModel_of_hasLabel_typeA hΛ hX
  simpa using (CFSG.Timmesfeld.card_statedClassicalModel_two hM).1 rfl

private theorem cuq2om_card_twA {X : Type} [Group X] {n : ℕ} (hn : 1 ≤ n)
    (hX : GGHasLabel (⟨.twA, 3, n⟩ : LargeEvenLabel) X) :
    Nat.card X = CFSG.Open.ordTwistedA 3 (2 ^ n) := by
  classical
  dsimp only [GGHasLabel, CFSG.StandardType.LargeEvenRawDatum] at hX
  obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := hX
  letI : Field K := hKf
  letI : Finite K := hKfin
  have hadm : CFSG.Open.StatedLieAdmissible .PSU 4 2 n :=
    ⟨Nat.prime_two, hn, by norm_num, by rintro ⟨h, -⟩⟩
  have hM := statedClassicalModel_unitary 4 n hKcard hadm
  simpa using (CFSG.Timmesfeld.card_statedClassicalModel_two
    (CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e.symm hM)).2.1 rfl

private theorem cuq2om_card_target {d m : ℕ} {E : Type} [Field E]
    (hE : UnitaryFieldData 2 m E) (hd : 3 ≤ d) (hdm : ¬ (d = 3 ∧ m = 1)) :
    Nat.card (LargeEvenProj (LargeEvenSUGroup (Fin d) E (2 ^ m))) =
      CFSG.Open.ordTwistedA (d - 1) (2 ^ m) := by
  haveI : Finite E := hE.finite
  have hcardE : Nat.card E = (2 ^ m) ^ 2 := by
    rw [hE.card, show 2 * m = m * 2 by omega, pow_mul]
  have hadm : CFSG.Open.StatedLieAdmissible .PSU d 2 m := by
    refine ⟨Nat.prime_two, hE.one_le, hd, ?_⟩
    intro h
    obtain ⟨h3, h2⟩ := Prod.ext_iff.mp h
    simp only at h3 h2
    have hmle : m ≤ 1 := by
      by_contra h
      have h2le : 2 ≤ m := by omega
      have hpow : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) h2le
      rw [h2] at hpow
      norm_num at hpow
    exact hdm ⟨h3, le_antisymm hmle hE.one_le⟩
  have hM := statedClassicalModel_unitary d m hcardE hadm
  exact (CFSG.Timmesfeld.card_statedClassicalModel_two hM).2.1 rfl

theorem q2UniOmega_fixedBlock_false {H : Type} [Group H] {F C : Subgroup H}
    (hC : IsComponentOf C F) {ι₁ K : Type} [Fintype ι₁] [DecidableEq ι₁] [Field K] [Finite K]
    [CharP K 2] (Φ₁ : QuadraticForm K (ι₁ → K))
    (hΦ₁ : (QuadraticMap.polarBilin Φ₁).Nondegenerate) (e : ↥F ≃* ↥(StatedOmega ⇑Φ₁))
    {d m : ℕ} {E : Type} [Field E] (hE : UnitaryFieldData 2 m E) (hd : 3 ≤ d) (hd4 : d ≠ 4)
    (hdm : ¬ (d = 3 ∧ m = 1))
    (θ : ↥C ⧸ Subgroup.center ↥C ≃* LargeEvenProj (LargeEvenSUGroup (Fin d) E (2 ^ m))) :
    False := by
  classical
  obtain ⟨lab, hlab, hdisj⟩ :=
    exists_label_of_isComponentOf_iso_statedOmega Φ₁ hΦ₁ e hC
  obtain ⟨hΛ, -, hGH⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.ggHasLabel_of_hasLabel hlab
  have hcardCθ : Nat.card (↥C ⧸ Subgroup.center ↥C) =
      CFSG.Open.ordTwistedA (d - 1) (2 ^ m) :=
    (Nat.card_congr θ.toEquiv).trans (cuq2om_card_target hE hd hdm)
  obtain ⟨tag, rank, n⟩ := lab
  rcases hdisj with (⟨hD, hr⟩ | ⟨hA1, _⟩) | (⟨hA3, _⟩ | ⟨htwA, hr⟩)
  · rcases hD with hD | hD
    · subst hD
      have hord : Nat.card (↥C ⧸ Subgroup.center ↥C) = CFSG.Open.ordD rank (2 ^ n) :=
        cuq2om_card_D hr hΛ.1 hGH
      exact (CFSG.Timmesfeld.Orders.ordD_ne_ordTwistedA (n := rank) (f := n) (u := d - 1)
        (g := m) hr hΛ.1 (by omega) hE.one_le) (hord.symm.trans hcardCθ)
    · subst hD
      have hord : Nat.card (↥C ⧸ Subgroup.center ↥C) =
          CFSG.Open.ordTwistedD rank (2 ^ n) :=
        cuq2om_card_twD hr hΛ.1 hGH
      exact (CFSG.Timmesfeld.Orders.ordTwistedD_ne_ordTwistedA (n := rank) (f := n)
        (u := d - 1) (g := m) hr hΛ.1 (by omega) hE.one_le) (hord.symm.trans hcardCθ)
  · subst hA1
    have hord : Nat.card (↥C ⧸ Subgroup.center ↥C) = CFSG.Open.ordA rank (2 ^ n) :=
      cuq2om_card_A hΛ hGH
    exact (CFSG.Timmesfeld.Orders.ordA_ne_ordTwistedA (n := rank) (f := n) (u := d - 1)
      (g := m) hΛ.2.1 hΛ.1 (by omega) hE.one_le) (hord.symm.trans hcardCθ)
  · subst hA3
    have hord : Nat.card (↥C ⧸ Subgroup.center ↥C) = CFSG.Open.ordA rank (2 ^ n) :=
      cuq2om_card_A hΛ hGH
    exact (CFSG.Timmesfeld.Orders.ordA_ne_ordTwistedA (n := rank) (f := n) (u := d - 1)
      (g := m) hΛ.2.1 hΛ.1 (by omega) hE.one_le) (hord.symm.trans hcardCθ)
  · subst htwA
    subst hr
    have hord : Nat.card (↥C ⧸ Subgroup.center ↥C) =
        CFSG.Open.ordTwistedA 3 (2 ^ n) :=
      cuq2om_card_twA hΛ.1 hGH
    have h1 : CFSG.Open.ordTwistedA 3 (2 ^ n) =
        CFSG.Open.ordTwistedA (d - 1) (2 ^ m) := hord.symm.trans hcardCθ
    have hnf : (3, n) ≠ (2, 1) := by
      intro h
      obtain ⟨h1, h2⟩ := Prod.ext_iff.mp h
      simp only at h1 h2
      omega
    have hug : (d - 1, m) ≠ (2, 1) := by
      intro h
      obtain ⟨hd1, hm1⟩ := Prod.ext_iff.mp h
      simp only at hd1 hm1
      exact hdm ⟨by omega, hm1⟩
    obtain ⟨hrank, -⟩ := CFSG.SeitzReduction.UnitaryPilot.ordTwistedA_inj_two_pow
      (n := 3) (u := d - 1) (f := n) (g := m) (by norm_num) (by omega) hΛ.1 hE.one_le
      hnf hug h1
    exact hd4 (by omega)

theorem q2UniOmega_block {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [Finite K] [CharP K 2]
    (Φ : QuadraticForm K (ι → K)) (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate)
    (h8 : 8 ≤ Fintype.card ι) (s : ↥(StatedOmega ⇑Φ)) (hso : Odd (orderOf s))
    (C : Subgroup ↥(StatedOmega ⇑Φ))
    (hC : IsComponentOf C (Subgroup.centralizer ({s} : Set ↥(StatedOmega ⇑Φ))))
    {d m : ℕ} {E : Type} [Field E] (hE : UnitaryFieldData 2 m E) (hd : 3 ≤ d) (hd4 : d ≠ 4)
    (hdm : ¬ (d = 3 ∧ m = 1))
    (hJE : Nonempty (↥C ⧸ Subgroup.center ↥C ≃*
      LargeEvenProj (LargeEvenSUGroup (Fin d) E (2 ^ m)))) :
    Q2UniBlockHom (Subgroup.centralizer ({s} : Set ↥(StatedOmega ⇑Φ))) C := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨θ⟩ := hJE
  have hodd : Odd (orderOf (s : GL ι K)) := by rwa [Subgroup.orderOf_coe]
  obtain ⟨P, hP, -, -, hc, hsup, -⟩ :=
    centralizer_block_decomp_Omega Φ hΦ h8 (s : GL ι K) s.2 hodd
  have hcent : Subgroup.centralizer ({s} : Set ↥(StatedOmega ⇑Φ)) =
      (Subgroup.centralizer {(s : GL ι K)}).comap (StatedOmega ⇑Φ).subtype := by
    ext g
    simp only [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff, Subgroup.coe_subtype,
      Subtype.ext_iff, Subgroup.coe_mul]
  rw [hcent] at hC ⊢
  rw [← hsup] at hC
  obtain ⟨ε, hε, hCε⟩ := exists_isComponentOf_block P _ hc hC
  rcases blockGroup_iso_Omega_cases Φ hΦ h8 (s : GL ι K) s.2 hodd (hP ε hε) with
    ⟨ι₁, _, _, Φ₁, hΦ₁, ⟨e⟩⟩ | hsol | ⟨b, D, _, _, _, ⟨e⟩⟩ | ⟨a, Q, D, _, _, _, hDQ, ⟨e⟩⟩
  · exact (q2UniOmega_fixedBlock_false hCε Φ₁ hΦ₁ e hE hd hd4 hdm θ).elim
  · exact (ResU3Three.not_isComponentOf_of_isSolvable hsol hCε).elim
  · exact (q2Uni_linearBlock_false hCε e hE hd hdm θ).elim
  · obtain ⟨k, rfl, hD⟩ := exists_unitaryFieldData_two hDQ
    have e' := e.trans (guFullEquivUnitGroup hD)
    obtain ⟨ha, hak⟩ := q2Uni_unitaryBlock_params hCε hD e' hE hd hdm θ
    exact q2UniBlockHom_of_unitaryBlock
      (omegaBlockHom Φ hΦ h8 (s : GL ι K) s.2 hodd ε (hP ε hε))
      (fun g c => by
        simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using
          omegaBlockHom_conj Φ hΦ h8 (s : GL ι K) s.2 hodd ε (hP ε hε) g c)
      hD ha hak e' hCε

theorem q2UniOmegaQuotient_lift {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [Finite K]
    [CharP K 2] (Q : (ι → K) → K) (Φ : QuadraticForm K (ι → K)) (hΦfun : ⇑Φ = Q)
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) (h8 : 8 ≤ Fintype.card ι)
    (hscal : (LargeEvenScalars ι K).subgroupOf (LargeEvenOmega Q) = ⊥)
    (hconj : Function.Injective
      (MulAut.conj : ↥(LargeEvenOmega Q) →* MulAut ↥(LargeEvenOmega Q)))
    {A : Subgroup (MulAut (LargeEvenProj (LargeEvenOmega Q)))} (hA : IsMulCommutative ↥A)
    (hAI : ∀ a ∈ A, a ∈ LargeEvenInnSet (LargeEvenProj (LargeEvenOmega Q)))
    {u : MulAut (LargeEvenProj (LargeEvenOmega Q))} (hu : u ∈ A) (huodd : Odd (orderOf u))
    {J : Subgroup (LargeEvenProj (LargeEvenOmega Q))}
    (hJ : IsComponentOf J (ggAutFixedSubgroup u)) (hAJ : ∀ a ∈ A, ∀ j ∈ J, a j ∈ J)
    {d m : ℕ} {E : Type} [Field E] (hE : UnitaryFieldData 2 m E) (hd : 3 ≤ d) (hd4 : d ≠ 4)
    (hdm : ¬ (d = 3 ∧ m = 1))
    (hJE : Nonempty (↥J ⧸ Subgroup.center ↥J ≃*
      LargeEvenProj (LargeEvenSUGroup (Fin d) E (2 ^ m))))
    (M : Subgroup (MulAut (↥J ⧸ Subgroup.center ↥J)))
    (hM : ∀ α ∈ M, ∃ a ∈ A, ∀ j j' : ↥J,
      (j' : LargeEvenProj (LargeEvenOmega Q)) = a (j : LargeEvenProj (LargeEvenOmega Q)) →
        α (QuotientGroup.mk j) = QuotientGroup.mk j') :
    Q2UnitaryLift M := by
  classical
  subst hΦfun
  let e : ↥(LargeEvenOmega ⇑Φ) ≃* LargeEvenProj (LargeEvenOmega ⇑Φ) :=
    TableBOrth.projMkEquiv hscal
  have hZ : Subgroup.center ↥(LargeEvenOmega ⇑Φ) = ⊥ := by
    rw [← CFSG.GroupTheory.ker_conj_eq_center]
    exact (MonoidHom.ker_eq_bot_iff _).mpr hconj
  have hZR : Subgroup.center (LargeEvenProj (LargeEvenOmega ⇑Φ)) = ⊥ := by
    rw [← Subgroup.map_center_eq e, hZ, Subgroup.map_bot]
  have hconjR : Function.Injective
      (MulAut.conj : LargeEvenProj (LargeEvenOmega ⇑Φ) →*
        MulAut (LargeEvenProj (LargeEvenOmega ⇑Φ))) :=
    (MonoidHom.ker_eq_bot_iff _).mp (CFSG.GroupTheory.ker_conj_eq_center.trans hZR)
  refine q2UnitaryLift_of_innerActor hconjR hA hAI hu ?_ hAJ M hM
  intro s hs
  have hsodd : Odd (orderOf (e.symm s)) := by
    have hord : orderOf u = orderOf s := by
      rw [← hs]
      exact orderOf_injective _ hconjR s
    rw [MulEquiv.orderOf_eq, ← hord]
    exact huodd
  have hJc : IsComponentOf J
      (Subgroup.centralizer ({s} : Set (LargeEvenProj (LargeEvenOmega ⇑Φ)))) := by
    have h := hJ
    rw [← hs, ggAutFixedSubgroup_mulAut_conj] at h
    exact h
  have hmap : (Subgroup.centralizer ({s} : Set (LargeEvenProj (LargeEvenOmega ⇑Φ)))).map
      e.symm.toMonoidHom = Subgroup.centralizer ({e.symm s} : Set ↥(LargeEvenOmega ⇑Φ)) := by
    have h := CFSG.ABGDGroups.map_inf_centralizer_of_injective e.symm.toMonoidHom
      e.symm.injective ⊤ s
    rwa [top_inf_eq, Subgroup.map_top_of_surjective _ e.symm.surjective, top_inf_eq] at h
  have hJm : IsComponentOf (J.map e.symm.toMonoidHom)
      (Subgroup.centralizer ({e.symm s} : Set ↥(LargeEvenOmega ⇑Φ))) := by
    have h := CFSG.isComponentOf_map_mulEquiv e.symm
      (CFSG.Assembly.isComponentOf_iff_open.mp hJc)
    rw [hmap] at h
    exact CFSG.Assembly.isComponentOf_iff_open.mpr h
  obtain ⟨θ⟩ := hJE
  let eJ : ↥J ≃* ↥(J.map e.symm.toMonoidHom) :=
    Subgroup.equivMapOfInjective J e.symm.toMonoidHom e.symm.injective
  let eJc : ↥J ⧸ Subgroup.center ↥J ≃*
      ↥(J.map e.symm.toMonoidHom) ⧸ Subgroup.center ↥(J.map e.symm.toMonoidHom) :=
    QuotientGroup.congr _ _ eJ (Subgroup.map_center_eq eJ)
  refine Q2UniBlockHom.of_mulEquiv e.symm ?_
  rw [hmap]
  exact q2UniOmega_block Φ hΦ h8 (e.symm s) hsodd (J.map e.symm.toMonoidHom) hJm hE hd hd4 hdm
    ⟨eJc.symm.trans θ⟩

end CFSG.StandardType
