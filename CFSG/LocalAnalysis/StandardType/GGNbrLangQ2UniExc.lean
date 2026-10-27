module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2UniCover
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1Regimes
public import Certificates.Certificate13723
public import Certificates.Certificate13724
import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1Holds
import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1TorUniTor
import CFSG.LocalAnalysis.StandardType.GGTableBExcTorus
import CFSG.LocalAnalysis.StandardType.GGTableBExcE6Three
import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylExcPlusLift
import CFSG.LocalAnalysis.StandardType.GGTableBF4Torus
import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTwE6Lift
import CFSG.LocalAnalysis.StandardType.GGResLeaf
import CFSG.LocalAnalysis.StandardType.GGTableBRank
import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1SmallRows
import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1Absence
import CFSG.LocalAnalysis.StandardType.GGTableBExcSmall
import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRestTri
import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRestTwF4
import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRanksTri
import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRanksTwF4
import CFSG.LocalAnalysis.StandardType.GGTwF4SUThreeRank

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial
open CFSG.StandardType.S2MathAs51642Interfaces (SmallDerived)

section Exc


theorem q2Uni_comm_of_large_gamma {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hInner : GGInnerDiagOn Bs L)
    (hN : Bs ≤ Subgroup.normalizer (J : Set G)) {d m : ℕ} (hd : 3 ≤ d) (hdm : ¬ (d = 3 ∧ m = 1))
    {E : Type} [Field E] (hE : UnitaryFieldData 2 m E)
    (θ : ↥J ⧸ Subgroup.center ↥J ≃* LargeEvenProj (LargeEvenSUGroup (Fin d) E (2 ^ m)))
    (hp2 : p ≠ 2) (hpm : p ∣ 2 ^ m + 1)
    (hcard : p ^ (d / p + 2) ≤ Nat.card (ggGamma J hN).range) :
    IsMulCommutative
      ((((ggBsAut hN).range).map (kgInducedAut θ)).comap
        (CFSG.HardMathSupport.C14Cl.uniConj hE d)) := by
  classical
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hBs : IsElemAbelian p Bs := hcfg.2.1.2.1
  have hQ1 : GGInnerDiagOn Bs J := ggBstarInnerDiagJInput_holds G p B Bs x L D J hcfg hInner
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  have hm : 1 ≤ m := hE.one_le
  haveI : Finite E := hE.finite
  have hEcard : Nat.card E = (2 ^ m) ^ 2 := by
    rw [hE.card, ← pow_mul, Nat.mul_comm 2 m]
  have hΛ : LargeEvenInLambda2 (⟨.twA, d', m⟩ : LargeEvenLabel) := by
    refine ⟨hm, show 2 ≤ d' by omega, fun h => ?_⟩
    have hd2 : d' = 2 := h
    show 2 ≤ m
    by_contra h2
    exact hdm ⟨by omega, by omega⟩
  have hhas : GGHasLabel (⟨.twA, d', m⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J) := by
    unfold GGHasLabel
    dsimp only [CFSG.StandardType.LargeEvenRawDatum, LargeEvenRecipeUnitary]
    exact ⟨E, inferInstance, inferInstance, hEcard, ⟨θ⟩⟩
  obtain ⟨hJperf, lab', -, hraw⟩ :=
    ggInnerDiagOn_relabel ggLabelRigidInput_holds hQ1 hΛ hhas
  obtain ⟨_, _, _, _, _, _, _, hlab', _⟩ := largeEvenRawDatum_exists hraw
  subst hlab'
  obtain ⟨F, _, _, hFcard, -, -, θJ, -, -, hact⟩ := hraw
  haveI : Finite F := (unitaryFieldData_of_card hm hFcard).finite
  set Eimg : Subgroup (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin (d' + 1)) F (2 ^ m)))) :=
    (ggGamma J hN).range.map (ggInducedAut θJ) with hEimg
  have hEimgAb : IsElemAbelian p Eimg := by
    rw [hEimg]
    exact (ggBsAut_range_isElemAbelian hBs hN).map (ggInducedAut θJ)
  have hcardEimg : Nat.card Eimg = Nat.card (ggGamma J hN).range := by
    rw [hEimg]
    exact Subgroup.card_map_of_injective (ggInducedAut_injective_of_perfect hJperf θJ)
  have hIE : ∀ b : ↥Bs, ggInducedAut θJ (ggGamma J hN b) ∈
      LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin (d' + 1)) F (2 ^ m)))
        (LargeEvenGUSet (Fin (d' + 1)) F (2 ^ m)) := by
    intro b
    have h := ggLAut_mem_of_induces (L := J) (θ := θJ) hN hact b.2
    have h2 : ggInducedAut θJ (ggGamma J hN b) = ggLAut J θJ ⟨b, hN b.2⟩ := by
      rw [ggLAut_eq_ggInducedAut, ggGamma]
      congr 1
    rw [h2]
    exact h
  have hEI : ∀ a ∈ Eimg, a ∈ LargeEvenMatConjImage
      (LargeEvenProjMk (LargeEvenSUGroup (Fin (d' + 1)) F (2 ^ m)))
      (LargeEvenGUSet (Fin (d' + 1)) F (2 ^ m)) := by
    intro a ha
    rw [hEimg] at ha
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp hx
    rw [← hb]
    exact hIE b
  have hdq : ¬ ((d' + 1) = 3 ∧ 2 ^ m = 2) := fun ⟨h3, h2⟩ =>
    hdm ⟨h3, Nat.pow_right_injective (le_refl 2) (h2.trans (by norm_num : (2 : ℕ) = 2 ^ 1))⟩
  have hcardEimg' : p ^ ((d' + 1) / p + 2) ≤ Nat.card Eimg := by
    rw [hcardEimg]
    exact hcard
  have hT : ToralUni _ Eimg :=
    toralUni_of_card (d := d' + 1) (m := m) (p := p) (K := F) (by omega) hm hdq hFcard hp hpm
      hEimgAb hEI hcardEimg'
  let θ' : LargeEvenProj (LargeEvenSUGroup (Fin (d' + 1)) F (2 ^ m)) ≃*
      LargeEvenProj (LargeEvenSUGroup (Fin (d' + 1)) E (2 ^ m)) := θJ.symm.trans θ
  have hcommProj : IsMulCommutative
      ((Eimg.map (MulAut.congr θ').toMonoidHom).comap
        (TableB.projConj (LargeEvenSUGroup (Fin (d' + 1)) E (2 ^ m)))) :=
    hT (d' + 1) m E inferInstance inferInstance hEcard θ'
  have hθ : θJ.trans θ' = θ := by
    ext x
    simp [θ', MulEquiv.trans_apply]
  have hEmap : Eimg.map (MulAut.congr θ').toMonoidHom =
      (ggBsAut hN).range.map (kgInducedAut θ) := by
    rw [hEimg, Subgroup.map_map]
    have hcomp : (MulAut.congr θ').toMonoidHom.comp (ggInducedAut θJ) = kgInducedAut θ := by
      show (MulAut.congr θ').toMonoidHom.comp
          ((MulAut.congr θJ).toMonoidHom.comp (centerQuotAut ↥J)) =
        (MulAut.congr θ).toMonoidHom.comp (centerQuotAut ↥J)
      rw [← MonoidHom.comp_assoc]
      congr 1
      rw [← show (MulAut.congr θJ).trans (MulAut.congr θ') = MulAut.congr θ from by
        rw [← hθ]
        ext x y
        simp [MulAut.congr_apply, MulEquiv.trans_apply]]
      rfl
    rw [hcomp]
    rfl
  have hcommUni : IsMulCommutative
      (((ggBsAut hN).range.map (kgInducedAut θ)).comap
        (CFSG.HardMathSupport.C14Cl.uniConj hE (d' + 1))) := by
    haveI : IsMulCommutative
        (((ggBsAut hN).range.map (kgInducedAut θ)).comap
          (TableB.projConj (LargeEvenSUGroup (Fin (d' + 1)) E (2 ^ m)))) := by
      rw [← hEmap]
      exact hcommProj
    rw [show CFSG.HardMathSupport.C14Cl.uniConj hE (d' + 1) =
        (TableB.projConj (LargeEvenSUGroup (Fin (d' + 1)) E (2 ^ m))).comp
          (Subgroup.inclusion (CFSG.HardMathSupport.C14Cl.uniGroup_le_normalizer hE)) from rfl,
      ← Subgroup.comap_comap]
    exact Subgroup.comap_injective_isMulCommutative
      (((ggBsAut hN).range.map (kgInducedAut θ)).comap
        (TableB.projConj (LargeEvenSUGroup (Fin (d' + 1)) E (2 ^ m))))
      (Subgroup.inclusion_injective _)
  exact hcommUni

private theorem cuq2e2_smallExc_absence :
    ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
      (L D J : Subgroup G), GGConfig p B Bs x L D J →
      LargeEvenMarking L (fun lab _ _ _ _ _ => SmallDerived p lab ∨ lab.tag = .G2 ∨
        lab.tag = .triD4 ∨ lab.tag = .twB2 ∨ lab.tag = .twF4) → False := by
  intro G _ _ p B Bs x L D J hcfg hM
  refine ggConfig_false_of_rigid_label
    (S := fun p lab => SmallDerived p lab ∨ lab.tag = .G2 ∨ lab.tag = .triD4 ∨
      lab.tag = .twB2 ∨ lab.tag = .twF4) ggLabelRigidInput_holds ?_ ?_ hcfg hM
  · intro p lab lab' hS h
    rcases hS with hS | hS | hS | hS | hS
    · simp only [SmallDerived] at hS
      refine ggLabelIso_eq_of_exceptional ?_ ?_ ?_ ?_ ?_ ?_ h <;>
        (rcases hS with ht | ht | ht <;> simp [ht])
    · refine ggLabelIso_eq_of_exceptional ?_ ?_ ?_ ?_ ?_ ?_ h <;> (rw [hS]; decide)
    · refine ggLabelIso_eq_of_exceptional ?_ ?_ ?_ ?_ ?_ ?_ h <;> (rw [hS]; decide)
    · refine ggLabelIso_eq_of_exceptional ?_ ?_ ?_ ?_ ?_ ?_ h <;> (rw [hS]; decide)
    · refine ggLabelIso_eq_of_exceptional ?_ ?_ ?_ ?_ ?_ ?_ h <;> (rw [hS]; decide)
  · intro p lab hp hΛ hS hsplit
    rcases hS with hS | hS | hS | hS | hS
    · obtain rfl := smallDerived_split_three hp hΛ hS hsplit
      simp only [SmallDerived] at hS
      rcases hS with ht | ht | ht
      · exact ggCSR_B2der hΛ ht
      · exact ggCSR_G2der hΛ ht
      · exact ggCSR_twF4der hΛ ht
    · exact TableBExc.largeEvenLabelAll_card_lt_G2 hp hΛ hS hsplit
    · exact TableBExcSmallRest.largeEvenLabelAll_card_lt_triD4
        (fun _ => TableBExcSmallRanks.ggTriD4ThreeRankInput_holds) hp hΛ hS hsplit
    · exact TableBExc.largeEvenLabelAll_card_lt_twB2 hp hΛ hS hsplit
    · exact TableBExcSmallRest.largeEvenLabelAll_card_lt_twF4
        (TableBExcSmallRanks.ggTwF4RankInput_of_three TwF4SUThree.ggTwF4ThreeRankInput_holds)
        hp hΛ hS hsplit

theorem ggBstarAbelianPreimageJUniS1On_smallExc :
    GGBstarAbelianPreimageJUniS1On (fun p lab => SmallDerived p lab ∨ lab.tag = .G2 ∨
      lab.tag = .triD4 ∨ lab.tag = .twB2 ∨ lab.tag = .twF4) := by
  intro G _ _ p B Bs x L D J hcfg _ hN d m hshape hpm hdm E _ hE θ hlab
  have hM : LargeEvenMarking L (fun lab _ _ _ _ _ => SmallDerived p lab ∨ lab.tag = .G2 ∨
      lab.tag = .triD4 ∨ lab.tag = .twB2 ∨ lab.tag = .twF4) :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.1) hlab
  exact (cuq2e2_smallExc_absence G p B Bs x L D J hcfg hM).elim

private theorem cuq2e3_div_add_three_le_six {p d : ℕ}
    (hshape : (p = 3 ∧ (d = 3 ∨ d = 6)) ∨ (p = 5 ∧ d = 5)) : d / p + 3 ≤ 6 := by
  rcases hshape with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num

private theorem cuq2e3_prime_of_shape {p d : ℕ}
    (hshape : (p = 3 ∧ (d = 3 ∨ d = 6)) ∨ (p = 5 ∧ d = 5)) : p.Prime := by
  rcases hshape with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> norm_num

private theorem cuq2e3_ne_two_of_shape {p d : ℕ}
    (hshape : (p = 3 ∧ (d = 3 ∨ d = 6)) ∨ (p = 5 ∧ d = 5)) : p ≠ 2 := by
  rcases hshape with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> norm_num

private theorem cuq2e3_three_le_of_shape {p d : ℕ}
    (hshape : (p = 3 ∧ (d = 3 ∨ d = 6)) ∨ (p = 5 ∧ d = 5)) : 3 ≤ d := by
  rcases hshape with ⟨_, h | h⟩ | ⟨_, h⟩ <;> omega

theorem q2Uni_comm_of_torusLift {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hInner : GGInnerDiagOn Bs L)
    (hN : Bs ≤ Subgroup.normalizer (J : Set G)) {d m : ℕ} (hd : 3 ≤ d)
    (hdm : ¬ (d = 3 ∧ m = 1))
    {E : Type} [Field E] (hE : UnitaryFieldData 2 m E)
    (θ : ↥J ⧸ Subgroup.center ↥J ≃* LargeEvenProj (LargeEvenSUGroup (Fin d) E (2 ^ m)))
    (hp : p.Prime) (hp2 : p ≠ 2) (hpm : p ∣ 2 ^ m + 1)
    (hperf : commutator L = ⊤)
    {R : Type} [Group R] (θL : L ⧸ Subgroup.center L ≃* R)
    {r : ℕ} (hlift : GGTorusLift p r R) (hr : d / p + 3 ≤ r) :
    IsMulCommutative
      ((((ggBsAut hN).range).map (kgInducedAut θ)).comap
        (CFSG.HardMathSupport.C14Cl.uniConj hE d)) := by
  have hS : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
  have hm := succ_le_twoLocalRank_of_torusLift hp hS.2.2.2.1.1 (hS.1.1.2 x hS.2.1)
    hS.2.2.1 hperf θL hlift
  have hc := hcfg.pow_le_card_gamma_J hN
  have hcard : p ^ (d / p + 2) ≤ Nat.card (ggGamma J hN).range :=
    (Nat.pow_le_pow_right hp.pos (show d / p + 2 ≤ r - 1 by omega)).trans
      ((Nat.pow_le_pow_right hp.pos
        (show r - 1 ≤ LargeEvenTwoLocalRank p G - 2 by omega)).trans hc)
  exact q2Uni_comm_of_large_gamma hcfg hInner hN hd hdm hE θ hp2 hpm hcard

theorem ggBstarAbelianPreimageJUniS1On_E7 :
    GGBstarAbelianPreimageJUniS1On (fun _ lab => lab.tag = .E7) := by
  intro G _ _ p B Bs x L D J hcfg hID hN d m hshape hpm hdm E _ hE θ hlab
  have hp : p.Prime := cuq2e3_prime_of_shape hshape
  have hp2 : p ≠ 2 := cuq2e3_ne_two_of_shape hshape
  have hd : 3 ≤ d := cuq2e3_three_le_of_shape hshape
  have hr6 : d / p + 3 ≤ 6 := cuq2e3_div_add_three_le_six hshape
  let P' : LargeEvenRawCont := fun R _ _ _ => ∃ r, d / p + 3 ≤ r ∧ GGTorusLift p r R
  have hall : ∀ lab, LargeEvenInLambda2 lab → (lab.tag = .E7 ∧ LargeEvenSplit p lab) →
      LargeEvenLabelAll lab P' := by
    intro lab hΛ hS
    obtain ⟨htag, hsplit⟩ := hS
    intro Q hQ
    obtain ⟨tag, rank, n⟩ := lab
    subst htag
    obtain ⟨K, hKf, hKfin, hKcard, hQ'⟩ := hQ
    have hsplit' : p ∣ 2 ^ n - 1 ∨ (n = 1 ∧ p = 3) := by
      simpa [LargeEvenSplit, LargeEvenUntwisted] using hsplit
    rcases hsplit' with hpn | ⟨hn1, hp3⟩
    · haveI : CharP K 2 := charP_two_of_card hKcard
      have hpK : p ∣ Nat.card K - 1 := by rw [hKcard]; exact hpn
      exact ⟨K, hKf, hKfin, hKcard, hQ', 7, le_trans hr6 (by norm_num),
        TableBExc.ggTorusLift_E7 (K := K) hp hp2 hpK⟩
    · subst hn1
      subst hp3
      haveI : CharP K 2 := charP_two_of_card hKcard
      have hpq : 3 ∣ Nat.card K + 1 := by rw [hKcard]; norm_num
      exact ⟨K, hKf, hKfin, hKcard, hQ', 6, le_trans hr6 (by norm_num),
        ggTorusLift_E7Plus (K := K) (p := 3) (by norm_num) (by norm_num) hpq⟩
  let P0 : LargeEvenMarkProp ↥L := fun (lab : LargeEvenLabel) (R : Type) [Group R]
      (I F : Set (MulAut R)) (θ : ↥L ⧸ Subgroup.center ↥L ≃* R) =>
      lab.tag = .E7 ∧ LargeEvenSplit p lab ∧
      Bs ≤ Subgroup.normalizer (L : Set G) ∧
      ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' : ↥L => (l' : G) = b⁻¹ * l * b) φ
  have hmark0 : LargeEvenMarking ↥L P0 := hlab
  have hSfun : ∀ (lab : LargeEvenLabel) (R : Type) [Group R] (I F : Set (MulAut R))
      (θ : ↥L ⧸ Subgroup.center ↥L ≃* R), P0 lab R I F θ →
      lab.tag = .E7 ∧ LargeEvenSplit p lab := by
    intro lab R _ I F θ hP
    exact ⟨hP.1, hP.2.1⟩
  have hmark := largeEvenMarking_and_labelAll (P := P0) (S := fun lab => lab.tag = .E7 ∧
      LargeEvenSplit p lab) (P' := P') hall hSfun hmark0
  obtain ⟨hperf, _lab, _hΛ, hraw'⟩ := hmark
  obtain ⟨_R, _hR, _I, _F, hQ⟩ := largeEvenRawDatum_exists hraw'
  obtain ⟨_hsimple, _hna, θL, _hP0', hP'⟩ := hQ
  obtain ⟨r, hr, hlift⟩ := hP'
  exact q2Uni_comm_of_torusLift hcfg hID hN hd hdm hE θ hp hp2 hpm hperf θL hlift hr

theorem ggBstarAbelianPreimageJUniS1On_E8 :
    GGBstarAbelianPreimageJUniS1On (fun _ lab => lab.tag = .E8) := by
  intro G _ _ p B Bs x L D J hcfg hID hN d m hshape hpm hdm E _ hE θ hlab
  have hp : p.Prime := cuq2e3_prime_of_shape hshape
  have hp2 : p ≠ 2 := cuq2e3_ne_two_of_shape hshape
  have hd : 3 ≤ d := cuq2e3_three_le_of_shape hshape
  have hr6 : d / p + 3 ≤ 6 := cuq2e3_div_add_three_le_six hshape
  let P' : LargeEvenRawCont := fun R _ _ _ => ∃ r, d / p + 3 ≤ r ∧ GGTorusLift p r R
  have hall : ∀ lab, LargeEvenInLambda2 lab → (lab.tag = .E8 ∧ LargeEvenSplit p lab) →
      LargeEvenLabelAll lab P' := by
    intro lab hΛ hS
    obtain ⟨htag, hsplit⟩ := hS
    intro Q hQ
    obtain ⟨tag, rank, n⟩ := lab
    subst htag
    obtain ⟨K, hKf, hKfin, hKcard, hQ'⟩ := hQ
    have hsplit' : p ∣ 2 ^ n - 1 ∨ (n = 1 ∧ p = 3) := by
      simpa [LargeEvenSplit, LargeEvenUntwisted] using hsplit
    rcases hsplit' with hpn | ⟨hn1, hp3⟩
    · haveI : CharP K 2 := charP_two_of_card hKcard
      have hpK : p ∣ Nat.card K - 1 := by rw [hKcard]; exact hpn
      exact ⟨K, hKf, hKfin, hKcard, hQ', 8, le_trans hr6 (by norm_num),
        TableBExc.ggTorusLift_E8 (K := K) hp hp2 hpK⟩
    · subst hn1
      subst hp3
      haveI : CharP K 2 := charP_two_of_card hKcard
      have hpq : 3 ∣ Nat.card K + 1 := by rw [hKcard]; norm_num
      exact ⟨K, hKf, hKfin, hKcard, hQ', 7, le_trans hr6 (by norm_num),
        ggTorusLift_E8Plus (K := K) (p := 3) (by norm_num) (by norm_num) hpq⟩
  let P0 : LargeEvenMarkProp ↥L := fun (lab : LargeEvenLabel) (R : Type) [Group R]
      (I F : Set (MulAut R)) (θ : ↥L ⧸ Subgroup.center ↥L ≃* R) =>
      lab.tag = .E8 ∧ LargeEvenSplit p lab ∧
      Bs ≤ Subgroup.normalizer (L : Set G) ∧
      ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' : ↥L => (l' : G) = b⁻¹ * l * b) φ
  have hmark0 : LargeEvenMarking ↥L P0 := hlab
  have hSfun : ∀ (lab : LargeEvenLabel) (R : Type) [Group R] (I F : Set (MulAut R))
      (θ : ↥L ⧸ Subgroup.center ↥L ≃* R), P0 lab R I F θ →
      lab.tag = .E8 ∧ LargeEvenSplit p lab := by
    intro lab R _ I F θ hP
    exact ⟨hP.1, hP.2.1⟩
  have hmark := largeEvenMarking_and_labelAll (P := P0) (S := fun lab => lab.tag = .E8 ∧
      LargeEvenSplit p lab) (P' := P') hall hSfun hmark0
  obtain ⟨hperf, _lab, _hΛ, hraw'⟩ := hmark
  obtain ⟨_R, _hR, _I, _F, hQ⟩ := largeEvenRawDatum_exists hraw'
  obtain ⟨_hsimple, _hna, θL, _hP0', hP'⟩ := hQ
  obtain ⟨r, hr, hlift⟩ := hP'
  exact q2Uni_comm_of_torusLift hcfg hID hN hd hdm hE θ hp hp2 hpm hperf θL hlift hr

theorem ggBstarAbelianPreimageJUniS1On_E6 :
    GGBstarAbelianPreimageJUniS1On (fun p lab => lab.tag = .E6 ∧ ¬ (lab.n = 1 ∧ p = 3)) := by
  intro G _ _ p B Bs x L D J hcfg hInner hN d m hshape hpm hdm E _ hE θ hlab
  obtain ⟨_, lab, _, hraw⟩ := hlab
  obtain ⟨tag, rank, n⟩ := lab
  obtain ⟨_, _, _, _, _, _, _, hP, hrest⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨htag0, hnot13⟩ := hP
  dsimp only at htag0
  subst htag0
  obtain ⟨hsplit, _, _⟩ := hrest
  have hpn : p ∣ 2 ^ n - 1 := by
    have hs := hsplit
    simp [LargeEvenSplit, LargeEvenUntwisted] at hs
    rcases hs with h | h
    · exact h
    · exact absurd h hnot13
  obtain ⟨K, instK, finK, hK, hQ⟩ := hraw
  haveI : CharP K 2 := charP_two_of_card hK
  obtain ⟨-, -, θL, -⟩ := hQ
  by_cases hp3 : p = 3
  · subst hp3
    have hlift := TableBExc.ggTorusLift_E6_three (K := K) (by rw [hK]; exact hpn)
    have hr : d / 3 + 2 ≤ 5 - 1 := by
      rcases hshape with ⟨_, h | h⟩ | ⟨h, _⟩
      · subst h; norm_num
      · subst h; norm_num
      · exact absurd h (by norm_num)
    exact q2Uni_comm_of_torusLift hcfg hInner hN (cuq2e3_three_le_of_shape hshape) hdm hE θ
      (cuq2e3_prime_of_shape hshape) (cuq2e3_ne_two_of_shape hshape) hpm hInner.1 θL hlift
      (by omega)
  · obtain ⟨hp5, hd5⟩ : p = 5 ∧ d = 5 := by
      rcases hshape with ⟨h3, _⟩ | ⟨h5, hd5⟩
      · exact absurd h3 hp3
      · exact ⟨h5, hd5⟩
    subst hp5
    subst hd5
    have hpq : 5 ∣ Nat.card K - 1 := by rw [hK]; exact hpn
    have hlift := TableBExc.ggTorusLift_E6 (K := K) Nat.prime_five (by norm_num)
      (by norm_num) hpq
    have hr : 5 / 5 + 2 ≤ 6 - 1 := by norm_num
    exact q2Uni_comm_of_torusLift hcfg hInner hN (cuq2e3_three_le_of_shape hshape) hdm hE θ
      (cuq2e3_prime_of_shape hshape) (cuq2e3_ne_two_of_shape hshape) hpm hInner.1 θL hlift
      (by omega)

theorem ggBstarAbelianPreimageJUniS1On_F4 :
    GGBstarAbelianPreimageJUniS1On (fun p lab => lab.tag = .F4 ∧ p ≠ 3) := by
  intro G _ _ p B Bs x L D J hcfg hInner hN d m hshape hpm hdm E _ hE θ hlab
  obtain ⟨_, lab, _, hraw⟩ := hlab
  obtain ⟨tag, rank, n⟩ := lab
  obtain ⟨_, _, _, _, _, _, _, hP, hrest⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨htag0, hp3⟩ := hP
  dsimp only at htag0
  subst htag0
  obtain ⟨hsplit, _, _⟩ := hrest
  have hpn : p ∣ 2 ^ n - 1 := by
    have hs := hsplit
    simp [LargeEvenSplit, LargeEvenUntwisted] at hs
    rcases hs with h | h
    · exact h
    · exact absurd h.2 hp3
  obtain ⟨hp5, hd5⟩ : p = 5 ∧ d = 5 := by
    rcases hshape with ⟨h3, _⟩ | ⟨h5, hd5⟩
    · exact absurd h3 hp3
    · exact ⟨h5, hd5⟩
  subst hp5
  subst hd5
  obtain ⟨K, instK, finK, hK, hQ⟩ := hraw
  haveI : CharP K 2 := charP_two_of_card hK
  obtain ⟨-, -, θL, -⟩ := hQ
  have hpq : 5 ∣ Nat.card K - 1 := by rw [hK]; exact hpn
  have hlift := TableBF4.ggTorusLift_F4 (K := K) Nat.prime_five (by norm_num) hpq
  have hr : 5 / 5 + 2 ≤ 4 - 1 := by norm_num
  exact q2Uni_comm_of_torusLift hcfg hInner hN (cuq2e3_three_le_of_shape hshape) hdm hE θ
    (cuq2e3_prime_of_shape hshape) (cuq2e3_ne_two_of_shape hshape) hpm hInner.1 θL hlift
    (by omega)

theorem ggBstarAbelianPreimageJUniS1On_twE6 :
    GGBstarAbelianPreimageJUniS1On (fun p lab => lab.tag = .twE6 ∧ p ≠ 3) := by
  intro G _ _ p B Bs x L D J hcfg hInner hN d m hshape hpm hdm E _ hE θ hlab
  obtain ⟨_, lab, hΛ, hraw⟩ := hlab
  obtain ⟨tag, rank, n⟩ := lab
  obtain ⟨_, _, _, _, _, _, _, hP, hrest⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨htag0, hp3⟩ := hP
  dsimp only at htag0
  subst htag0
  obtain ⟨hsplit, _, _⟩ := hrest
  have hpn : p ∣ 2 ^ n + 1 := by
    have hs := hsplit
    simp [LargeEvenSplit, LargeEvenUntwisted] at hs
    rcases hs with h | h
    · exact h
    · exact absurd h.2 hp3
  obtain ⟨hp5, hd5⟩ : p = 5 ∧ d = 5 := by
    rcases hshape with ⟨h3, _⟩ | ⟨h5, hd5⟩
    · exact absurd h3 hp3
    · exact ⟨h5, hd5⟩
  subst hp5
  subst hd5
  obtain ⟨K, instK, finK, hK, hQ⟩ := hraw
  obtain ⟨-, -, θL, -⟩ := hQ
  have hlift := ggTorusLift_twE6Add_holds (K := K) (n := n) hΛ.1 hK Nat.prime_five hpn
  have hlift5 : GGTorusLift 5 5 (TwE6Delta.RecipeR K n) := by
    simpa [TwE6Delta.liftRank] using hlift
  have hr : 5 / 5 + 2 ≤ 5 - 1 := by norm_num
  exact q2Uni_comm_of_torusLift hcfg hInner hN (cuq2e3_three_le_of_shape hshape) hdm hE θ
    (cuq2e3_prime_of_shape hshape) (cuq2e3_ne_two_of_shape hshape) hpm hInner.1 θL hlift5
    (by omega)

theorem ggBstarAbelianPreimageJUniS1On_of_classical_excRest
    (h : GGBstarAbelianPreimageJUniS1On (fun p lab => lab.tag = .B ∨ lab.tag = .C ∨ lab.tag = .D ∨
      lab.tag = .twD ∨ (lab.tag = .E6 ∧ lab.n = 1 ∧ p = 3) ∨ (lab.tag = .F4 ∧ p = 3) ∨
      (lab.tag = .twE6 ∧ p = 3))) :
    GGBstarAbelianPreimageJUniS1On (fun _ lab => lab.tag ≠ .A ∧ lab.tag ≠ .twA) := by
  refine GGBstarAbelianPreimageJUniS1On.mono (fun p lab hlab => ?_)
    (h.or (ggBstarAbelianPreimageJUniS1On_smallExc.or
      (ggBstarAbelianPreimageJUniS1On_E7.or (ggBstarAbelianPreimageJUniS1On_E8.or
        (ggBstarAbelianPreimageJUniS1On_E6.or (ggBstarAbelianPreimageJUniS1On_F4.or
          ggBstarAbelianPreimageJUniS1On_twE6))))))
  obtain ⟨hA, hTwA⟩ := hlab
  obtain ⟨tag, rank, n⟩ := lab
  have hA' : tag ≠ .A := hA
  have hTwA' : tag ≠ .twA := hTwA
  by_cases h13 : n = 1 ∧ p = 3
  · obtain ⟨rfl, rfl⟩ := h13
    cases tag <;> simp_all [SmallDerived]
  · by_cases hp3 : p = 3
    · subst hp3
      cases tag <;> simp_all [SmallDerived]
    · cases tag <;> simp_all [SmallDerived]

end Exc

end CFSG.StandardType
