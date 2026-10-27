module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2CensusDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2CensusTwA
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2CensusOmegaSel
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2CensusOmegaNonsplit
import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1DSmall
import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBVac
import CFSG.LocalAnalysis.StandardType.GGTableBTwDThree
import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticOmega
import CFSG.LocalAnalysis.StandardType.KGLangS1ALinTypeDet
import CFSG.LocalAnalysis.StandardType.GGOmegaMinusRootGenIso
import CFSG.LocalAnalysis.StandardType.GGLayerCycModelOmegaSec
import CFSG.LocalAnalysis.StandardType.GGCentInnerDiagConcl
import CFSG.LocalAnalysis.ComponentInitial.DerivedFixedLayer
import CFSG.LocalAnalysis.ComponentInitial.BlockCentralQuotient
import CFSG.Mathlib.GroupTheory.Automorphism.ConjCommute

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly
open CFSG.LocalAnalysis.ComponentInitial


private theorem q2cOM_rank_two :
    Q2CensusRLevel (fun lab => lab.tag = .twD ∧ lab.rank = 2)
      (fun kind => kind = .orthogonalMinus) := by
  intro p d m lab hp hp2 hΛ hsplit hS hd hm hpd hpm Q hQ
  obtain ⟨htag, hrank⟩ := hS
  have hlin : GGLinearTwoLabel lab := Or.inr ⟨htag, hrank⟩
  have hlt := largeEvenLabelAll_card_lt_linearTwo hp hp2 hΛ hlin
  refine largeEvenRawDatum_mono ?_ (hlt Q hQ)
  rintro R _ I F ⟨hq, hlt'⟩
  refine ⟨hq, fun A hA hAI _ h3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ => ?_⟩
  exact absurd h3 (not_le.2 (hlt' A (fun a ha => hAI a ha) hA))

private theorem q2cOM_labelAll_twD3_twA3 {n : ℕ} {P P' : LargeEvenRawCont}
    (himp : ∀ (R : Type) [Group R] (I F : Set (MulAut R)), P' R I F → P R I F)
    (h : LargeEvenLabelAll (⟨.twA, 3, n⟩ : LargeEvenLabel) P') :
    LargeEvenLabelAll (⟨.twD, 3, n⟩ : LargeEvenLabel) P := by
  intro Q hQ
  have hQ' : LargeEvenRawDatum (⟨.twA, 3, n⟩ : LargeEvenLabel) Q :=
    (Q1DSmall.rawDatum_twD3_iff_twA3 n Q).1 hQ
  have hres := h Q hQ'
  refine largeEvenRawDatum_mono ?_ ((Q1DSmall.rawDatum_twD3_iff_twA3 n _).2 hres)
  rintro R _ I F ⟨hQr, hP'⟩
  exact ⟨hQr, himp R I F hP'⟩

private theorem q2cOM_rank_three :
    Q2CensusRLevel (fun lab => lab.tag = .twD ∧ lab.rank = 3)
      (fun kind => kind = .orthogonalMinus) := by
  intro p d m lab hp hp2 hΛ hsplit hS hd hm hpd hpm Q hQ
  obtain ⟨htag, hrank⟩ := hS
  obtain ⟨t, l, n⟩ := lab
  dsimp only [LargeEvenLabel.tag, LargeEvenLabel.rank] at htag hrank
  subst htag
  subst hrank
  by_cases hpq : p ∣ 2 ^ n - 1
  · have hlabel : GGTableBTwDThreeLabel p (⟨.twD, 3, n⟩ : LargeEvenLabel) :=
      ⟨rfl, rfl, hpq⟩
    have hlt := largeEvenLabelAll_card_lt_twDThree hp hΛ hlabel
    refine largeEvenRawDatum_mono ?_ (hlt Q hQ)
    rintro R _ I F ⟨hq, hlt'⟩
    refine ⟨hq, fun A hA hAI _ h3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ => ?_⟩
    exact absurd h3 (not_le.2 (hlt' A (fun a ha => hAI a ha) hA))
  · have hΛ' : LargeEvenInLambda2 (⟨.twA, 3, n⟩ : LargeEvenLabel) :=
      ⟨hΛ.1, by norm_num, fun h => by simp at h⟩
    have hsplit' : LargeEvenSplit p (⟨.twA, 3, n⟩ : LargeEvenLabel) := by
      rcases hsplit with h | ⟨-, -, hpq2⟩ | ⟨-, hpq1⟩ | ⟨hn1, hp3⟩
      · exfalso
        simpa [LargeEvenUntwisted] using h.1
      · exact Or.inr (Or.inl ⟨by simp [LargeEvenUntwisted],
          ⟨(fun h => by cases h), hpq2⟩⟩)
      · exact absurd hpq1 hpq
      · exact Or.inr (Or.inr (Or.inr ⟨hn1, hp3⟩))
    have htwA := q2c_rLevel_twA (p := p) (d := d) (m := m) (lab := ⟨.twA, 3, n⟩)
      hp hp2 hΛ' hsplit' rfl hd hm hpd hpm
    refine q2cOM_labelAll_twD3_twA3 ?_ htwA Q hQ
    intro R _ I F hP' A hA hAI hbig h3 hlo hup u hu huo J hJ huniq hAJ K _ _ hK hne
    obtain ⟨kind, hk, -⟩ :=
      hP' A hA hAI hbig h3 hlo hup u hu huo J hJ huniq hAJ K hK hne
    exact hk.elim

private theorem q2cOM_torusLift {p : ℕ} {lab : LargeEvenLabel}
    (hΛ : LargeEvenInLambda2 lab) (htag : lab.tag = .twD) (h4 : 4 ≤ lab.rank)
    (hp : p.Prime) (hp2 : p ≠ 2) :
    LargeEvenLabelAll lab (fun R _ _ _ =>
      p ∣ 2 ^ lab.n - 1 → GGTorusLift p (lab.rank - 1) R) := by
  intro Q hQ
  obtain ⟨t, l, n⟩ := lab
  dsimp only [LargeEvenLabel.tag, LargeEvenLabel.rank] at htag h4
  subst htag
  simp only [LargeEvenRawDatum, if_neg (show ¬ l = 2 by omega),
    if_neg (show ¬ l = 3 by omega)] at hQ ⊢
  obtain ⟨K, i1, i2, hK, b, c, hbc, hQ'⟩ := hQ
  refine ⟨K, i1, i2, hK, b, c, hbc, hQ', ?_⟩
  intro hpq
  haveI : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK
  have hpqK : p ∣ Nat.card K - 1 := by rw [hK]; exact hpq
  exact TableBSymp.ggTorusLift_omegaMinus (K := K) (m := l - 1) hp hp2 hpqK (by omega) b c

theorem q2cOM_block_structure {p d m : ℕ} {lab : LargeEvenLabel}
    (hΛ : LargeEvenInLambda2 lab) (htag : lab.tag = .twD) (h4 : 4 ≤ lab.rank)
    (hp : p.Prime) (hp2 : p ≠ 2) (hsplit : LargeEvenSplit p lab) (hpd : p ∣ d) (hm : 2 ≤ m) :
    LargeEvenLabelAll lab (fun R _ I _ =>
      ∀ A : Subgroup (MulAut R), IsElemAbelian p A → (∀ a ∈ A, a ∈ I) →
      (∀ r : ℕ, GGTorusLift p r R → p ^ r ≤ Nat.card A) →
      p ^ 3 ≤ Nat.card A → p ^ (d - 1) ≤ Nat.card A → Nat.card A ≤ p ^ d →
      ∀ u ∈ A, orderOf u = p →
      ∀ J : Subgroup R, CFSG.Open.IsComponentOf J (ggAutFixedSubgroup u) →
        (∀ J' : Subgroup R, CFSG.Open.IsComponentOf J' (ggAutFixedSubgroup u) → J' = J) →
        (∀ a ∈ A, ∀ j ∈ J, a j ∈ J) →
        ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ m →
          Nonempty (↥J ⧸ Subgroup.center ↥J ≃*
            LargeEvenProj (LargeEvenSLGroup (Fin d) K)) →
          (p ∣ 2 ^ lab.n - 1 →
            ∃ (a : ℕ) (F : Type) (_ : Field F) (_ : Finite F),
              Nat.card F = 2 ^ lab.n ∧ 3 ≤ a ∧ a + 1 ≤ lab.rank ∧
              Nonempty (↥J ⧸ Subgroup.center ↥J ≃*
                LargeEvenProj (LargeEvenSLGroup (Fin a) F)))
          ∧ (¬ p ∣ 2 ^ lab.n - 1 → False)) := by
  intro Q hQ
  obtain ⟨t, l, n⟩ := lab
  dsimp only [LargeEvenLabel.tag, LargeEvenLabel.rank] at htag h4
  subst htag
  simp only [LargeEvenRawDatum, if_neg (show ¬ l = 2 by omega),
    if_neg (show ¬ l = 3 by omega)] at hQ ⊢
  obtain ⟨F, iF, iFin, hFcard, b, c, hbc, hQcont⟩ := hQ
  refine ⟨F, iF, iFin, hFcard, b, c, hbc, hQcont, ?_⟩
  intro A _ hAI _ h3 _ hup u hu huo J hJ _ _ K iK iFinK hKcard hne
  have hd : 3 ≤ d := (Nat.pow_le_pow_iff_right hp.one_lt).mp (h3.trans hup)
  let Φ : QuadraticForm F (LargeEvenMinusIdx (l - 1) → F) :=
    (TableBOrth.qMinusForm F (l - 1) b c).copy (LargeEvenQMinus (l - 1) b c)
      (TableBOrth.coe_qMinusForm (l - 1) b c).symm
  have hΦeq : Φ = TableBOrth.qMinusForm F (l - 1) b c := by
    dsimp only [Φ]
    exact QuadraticMap.copy_eq _ _ _
  haveI hcharF : CharP F 2 :=
    CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hFcard
  have hscal : (LargeEvenScalars (LargeEvenMinusIdx (l - 1)) F).subgroupOf
      (LargeEvenOmega (LargeEvenQMinus (l - 1) b c)) = ⊥ :=
    TableBOrth.scalars_subgroupOf_omegaMinus_eq_bot (K := F) (m := l - 1) b c
  have hZstd : Subgroup.center
      (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus ((l - 1) + 1) F b c)) = ⊥ :=
    center_statedOmega_quadMinus_eq_bot (K := F) (n := (l - 1) + 1) (by omega) hbc
  have hZΩ : Subgroup.center ↥(LargeEvenOmega (LargeEvenQMinus (l - 1) b c)) = ⊥ := by
    rw [← Subgroup.map_center_eq
      (LayerCyc.largeEvenOmegaMinusEquiv (l - 1) F b c).symm, hZstd, Subgroup.map_bot]
  have hZR : Subgroup.center
      (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (l - 1) b c))) = ⊥ := by
    have hmap := Subgroup.map_center_eq (TableBOrth.projMkEquiv hscal)
    rw [hZΩ, Subgroup.map_bot] at hmap
    exact hmap.symm
  let e : LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (l - 1) b c)) ≃*
      ↥(LargeEvenOmega (LargeEvenQMinus (l - 1) b c)) :=
    (TableBOrth.projMkEquiv hscal).symm
  have hAinn : u ∈ LargeEvenInnSet
      (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (l - 1) b c))) := hAI u hu
  obtain ⟨s, hs⟩ := hAinn
  have hfix : ggAutFixedSubgroup u =
      Subgroup.centralizer
        ({s} : Set (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (l - 1) b c)))) := by
    rw [← hs]
    exact ggAutFixedSubgroup_mulAut_conj s
  have hconj : Function.Injective
      (MulAut.conj : (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (l - 1) b c))) →* _) :=
    CFSG.mulAut_conj_injective hZR
  have hord : orderOf u = orderOf s := by
    rw [← hs]
    exact orderOf_injective _ hconj s
  have hsord : orderOf s = p := by rw [← hord]; exact huo
  have hJO : CFSG.Assembly.IsComponentOf J
      (Subgroup.centralizer
        ({s} : Set (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (l - 1) b c))))) := by
    rw [← hfix]
    exact CFSG.Assembly.isComponentOf_iff_open.mpr hJ
  let sΩ : ↥(LargeEvenOmega (LargeEvenQMinus (l - 1) b c)) := e s
  have hsΩord : orderOf sΩ = p := by
    change orderOf (e.toMonoidHom s) = p
    rw [orderOf_injective e.toMonoidHom e.injective s]
    exact hsord
  let C : Subgroup ↥(LargeEvenOmega (LargeEvenQMinus (l - 1) b c)) := J.map e.toMonoidHom
  have hC : CFSG.Assembly.IsComponentOf C
      (Subgroup.centralizer
        ({sΩ} : Set ↥(LargeEvenOmega (LargeEvenQMinus (l - 1) b c)))) := by
    have hmap : CFSG.Assembly.IsComponentOf (J.map e.toMonoidHom)
        ((Subgroup.centralizer
          ({s} : Set (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (l - 1) b c))))).map
            e.toMonoidHom) :=
      (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff
        (f := e.toMonoidHom) e.injective).mpr hJO
    have hcentmap :
        (Subgroup.centralizer
          ({s} : Set (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (l - 1) b c))))).map
            e.toMonoidHom =
          Subgroup.centralizer
            ({sΩ} : Set ↥(LargeEvenOmega (LargeEvenQMinus (l - 1) b c))) := by
      dsimp only [sΩ]
      exact CFSG.LocalAnalysis.ComponentInitial.map_centralizer_singleton_mulEquiv e s
    rw [hcentmap] at hmap
    exact hmap
  have hcenter : (Subgroup.center ↥J).map (e.subgroupMap J).toMonoidHom =
      Subgroup.center ↥C := by
    dsimp only [C]
    exact Subgroup.map_center_eq (e.subgroupMap J)
  let eQ : (↥J ⧸ Subgroup.center ↥J) ≃* (↥C ⧸ Subgroup.center ↥C) :=
    QuotientGroup.congr (Subgroup.center ↥J) (Subgroup.center ↥C) (e.subgroupMap J) hcenter
  let θ : ↥C ⧸ Subgroup.center ↥C ≃*
      LargeEvenProj (LargeEvenSLGroup (Fin d) K) := eQ.symm.trans hne.some
  have h8 : 8 ≤ Fintype.card (LargeEvenMinusIdx (l - 1)) := by
    simp only [LargeEvenMinusIdx, Fintype.card_sum, Fintype.card_fin]
    omega
  have hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate := by
    rw [hΦeq]
    exact TableBOrth.nondegenerate_qMinusForm (K := F) (m := l - 1) (b := b) (c := c) hbc
  have hw : ∀ W : Submodule F (LargeEvenMinusIdx (l - 1) → F),
      (∀ x ∈ W, Φ x = 0) → Module.finrank F W ≤ l - 1 := by
    intro W hW
    refine TableBOrth.finrank_le_of_singular_qMinus (K := F) (m := l - 1)
      (b := b) (c := c) hbc W ?_
    intro x hx
    simpa only [hΦeq] using hW x hx
  refine ⟨fun hpq => ?_, fun hnpq => ?_⟩
  · have hpF : p ∣ Nat.card F - 1 := by rw [hFcard]; exact hpq
    have hres := q2cOS_selected_block (K := F) (K' := K) (Φ := Φ) (p := p) (d := d)
      (w := l - 1) (m := m) hΦ h8 hp hp2 hd hpd hpF hm hKcard hw sΩ hsΩord C hC θ
    obtain ⟨hcard, hdle⟩ := hres
    exact ⟨d, K, iK, iFinK, by rw [hcard, hFcard], hd, by omega, ⟨hne.some⟩⟩
  · have hpqF : p ∣ Nat.card F + 1 := by
      rw [hFcard]
      rcases hsplit with h | h | h | ⟨hn1, hp3⟩
      · exact absurd h.2 hnpq
      · exact h.2.2
      · exact absurd h.2 hnpq
      · have hn1' : n = 1 := hn1
        rw [hn1', hp3]
        norm_num
    exact q2cON_nonsplit (F := F) (K := K) (Φ := Φ) (p := p) (d := d) (m := m)
      hΦ h8 hp hp2 hpqF hd hpd hm hKcard sΩ hsΩord C hC θ

private theorem q2cOM_rank_ge_four :
    Q2CensusRLevel (fun lab => lab.tag = .twD ∧ 4 ≤ lab.rank)
      (fun kind => kind = .orthogonalMinus) := by
  intro p d m lab hp hp2 hΛ hsplit hS hd hm hpd hpm Q hQ
  obtain ⟨htag, h4⟩ := hS
  have hstruct := q2cOM_block_structure (p := p) (d := d) (m := m) hΛ htag h4 hp hp2 hsplit hpd hm
  have htor := q2cOM_torusLift (p := p) hΛ htag h4 hp hp2
  have hall := largeEvenLabelAll_and hstruct htor
  refine largeEvenRawDatum_mono ?_ (hall Q hQ)
  rintro R _ I F ⟨hq, hstruct', htor'⟩
  refine ⟨hq, fun A hA hAI hbig h3 hlo hup u hu huo J hJ huniq hAJ K _ _ hK hne => ?_⟩
  have hne' : ↥J ⧸ Subgroup.center ↥J ≃*
      LargeEvenProj (LargeEvenSLGroup (Fin d) K) := hne.some
  have hconj := hstruct' A hA hAI hbig h3 hlo hup u hu huo J hJ huniq hAJ K hK hne
  by_cases hpq : p ∣ 2 ^ lab.n - 1
  · obtain ⟨a, F, iF, iFin, hF, ha3, hale, hJiso⟩ := hconj.1 hpq
    obtain ⟨hJiso'⟩ := hJiso
    have hψ : LinearFlag.projectiveSL d K ≃*
        LargeEvenProj (LargeEvenSLGroup (Fin a) F) :=
      (TypeA.recipeEquiv d K).symm.trans (hne'.symm.trans hJiso')
    obtain ⟨hda, hcardKF⟩ :=
      kgLangS1A_psl_typeDet (d := d) (d₁ := a) (m := m) (F₀ := K) (E := F)
        hd hm hK hψ
    have hlift : GGTorusLift p (lab.rank - 1) R := htor' hpq
    have hpow : p ^ (lab.rank - 1) ≤ Nat.card A := hbig (lab.rank - 1) hlift
    have hrank_le : lab.rank ≤ d + 1 := by
      have h' : lab.rank - 1 ≤ d :=
        (Nat.pow_le_pow_iff_right hp.one_lt).mp (hpow.trans hup)
      omega
    have hd_le : d + 1 ≤ lab.rank := by rw [← hda]; exact hale
    have hrank_eq : lab.rank = d + 1 := le_antisymm hrank_le hd_le
    have hfield : 2 ^ m = 2 ^ lab.n := by rw [← hK, ← hcardKF, hF]
    exact ⟨.orthogonalMinus, rfl, hp, hp2, hpd, hpm, htag, hrank_eq, hfield⟩
  · exact (hconj.2 hpq).elim

theorem q2c_rLevel_orthogonalMinus :
    Q2CensusRLevel (fun lab => lab.tag = .twD) (fun kind => kind = .orthogonalMinus) := by
  refine Q2CensusRLevel.mono ?_ (fun kind hk => hk.elim id fun h => h.elim id id)
    (Q2CensusRLevel.or q2cOM_rank_two (Q2CensusRLevel.or q2cOM_rank_three q2cOM_rank_ge_four))
  intro lab hΛ hS
  have h2 : 2 ≤ lab.rank := by
    have h := hΛ
    simp only [LargeEvenInLambda2, hS] at h
    exact h.2
  rcases (by omega : lab.rank = 2 ∨ lab.rank = 3 ∨ 4 ≤ lab.rank) with h | h | h
  · exact Or.inl ⟨hS, h⟩
  · exact Or.inr (Or.inl ⟨hS, h⟩)
  · exact Or.inr (Or.inr ⟨hS, h⟩)

end CFSG.StandardType
