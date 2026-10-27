module

public import CFSG.LocalAnalysis.StandardType.GGTBJNoRankOneDefs
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs

import CFSG.LocalAnalysis.StandardType.GGTBJNoRankOneMarking
import CFSG.LocalAnalysis.StandardType.GGTBJNoRankOneCard
import CFSG.LocalAnalysis.StandardType.GGTBJNoRankOneTorus
import CFSG.LocalAnalysis.StandardType.GGTBJNoRankOneToral
import CFSG.LocalAnalysis.StandardType.GGTBJNoRankOneCaseOne
import CFSG.LocalAnalysis.StandardType.GGTBJNoRankOneCases
import CFSG.LocalAnalysis.StandardType.GGOneFiveNormalizer
import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic
import CFSG.LocalAnalysis.StandardType.GGFieldCaseL4546Defs
import CFSG.LocalAnalysis.StandardType.GGTBJConfigFacts
import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeReduction
import CFSG.GroupTheory.PLayer.CenterQuotientAction
import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
import CFSG.CharacterTheory.Wreathed.WreathCentralSquare

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGRankOneShapeAt (n : ℕ) (lab : LargeEvenLabel) (R : Type) [Group R]
    (I : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
    ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
    ∀ (e : MulAut L') (J : Subgroup L') (a : MulAut L'),
      GGRankOneSetup I ψ 3 e J n a →
      ∃ m : ℕ, 1 ≤ m ∧ n = 3 * m ∧
        ((lab = (⟨.A, 2 * 3 - 1, m⟩ : LargeEvenLabel) ∧ 3 ∣ 2 ^ m - 1) ∨
          (lab = (⟨.twA, 2 * 3 - 1, m⟩ : LargeEvenLabel) ∧ 3 ∣ 2 ^ m + 1)) ∧
        ¬ ∃ r : R, ∀ l : L', ψ (e l) = r * ψ l * r⁻¹

@[expose] def GGSU6NoParabolicAtN (n : ℕ) {R : Type} [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
    ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
    ∀ (e : MulAut L') (J : Subgroup L') (a : MulAut L'),
      GGRankOneSetup I ψ 3 e J n a →
      ∀ A : Subgroup (MulAut L'), IsElemAbelian 3 A → Nat.card A = 3 ^ 3 → e ∈ A → a ∈ A →
        (∀ c ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (c l)) →
        (∀ c ∈ A, ∀ j ∈ J, c j ∈ J) →
        ∀ V : Subgroup (MulAut R), V ≠ ⊥ → IsPGroup 2 V → V ≤ Subgroup.closure I →
          ¬ ∀ c ∈ A, ∀ φ : MulAut R, (∀ l : L', φ (ψ l) = ψ (c l)) →
              ∀ v ∈ V, φ * v * φ⁻¹ ∈ V

private def l48nU_KD2 (n : ℕ) (lab : LargeEvenLabel) : LargeEvenRawCont :=
  fun R _ I _ => GGRankOneShapeAt n lab R I

private def l48nU_P2 (n : ℕ) (lab : LargeEvenLabel) : LargeEvenRawCont :=
  fun _ _ I _ => (∃ f : ℕ, lab = ⟨.twA, 5, f⟩ ∧ 3 ∣ 2 ^ f + 1) →
    GGSU6DiagInvertedAt I ∧ GGSU6NoParabolicAtN n I

private def l48nU_PAll (n : ℕ) (lab : LargeEvenLabel) : LargeEvenRawCont :=
  fun R _ I F => l48nU_KD2 n lab R I F ∧ l48nU_P2 n lab R I F

private theorem l48nU_P2_labelAll (n : ℕ) (hKD5b : GGSU6DiagInvertedKnown)
    (hKD5c : ∀ f : ℕ, 3 ∣ 2 ^ f + 1 →
      LargeEvenLabelAll (⟨.twA, 5, f⟩ : LargeEvenLabel)
        fun R _ I _ => GGSU6NoParabolicAtN n I)
    (lab : LargeEvenLabel)
    (hlab2 : LargeEvenInLambda2 lab) : LargeEvenLabelAll lab (l48nU_P2 n lab) := by
  by_cases hf : ∃ f : ℕ, lab = ⟨.twA, 5, f⟩ ∧ 3 ∣ 2 ^ f + 1
  · obtain ⟨f, heq, h3⟩ := hf
    have hb := hKD5b f h3
    have hc := hKD5c f h3
    rw [← heq] at hb hc
    have hAall : LargeEvenLabelAll lab
        (fun _ _ I _ => GGSU6DiagInvertedAt I ∧ GGSU6NoParabolicAtN n I) :=
      largeEvenLabelAll_and hb hc
    exact fun Q hQ => largeEvenRawDatum_mono
      (fun R _ I F hq => ⟨hq.1, fun _ => hq.2⟩) (hAall Q hQ)
  · exact fun Q hQ => largeEvenRawDatum_mono
      (fun R _ I F hq => ⟨hq, fun hex => absurd hex hf⟩) hQ

private theorem l48nU_KD2_labelAll (n : ℕ)
    (hKD2 : ∀ lab, LargeEvenInLambda2 lab →
      LargeEvenLabelAll lab (fun R _ I _ => GGRankOneShapeAt n lab R I))
    (lab : LargeEvenLabel) (hlab : LargeEvenInLambda2 lab) :
    LargeEvenLabelAll lab (l48nU_KD2 n lab) :=
  hKD2 lab hlab

private theorem l48nU_pAll (n : ℕ)
    (hKD2 : ∀ lab, LargeEvenInLambda2 lab →
      LargeEvenLabelAll lab (fun R _ I _ => GGRankOneShapeAt n lab R I))
    (hKD5b : GGSU6DiagInvertedKnown)
    (hKD5c : ∀ f : ℕ, 3 ∣ 2 ^ f + 1 →
      LargeEvenLabelAll (⟨.twA, 5, f⟩ : LargeEvenLabel)
        fun R _ I _ => GGSU6NoParabolicAtN n I) :
    ∀ lab, LargeEvenInLambda2 lab → LargeEvenLabelAll lab (l48nU_PAll n lab) := by
  intro lab hlab
  exact largeEvenLabelAll_and (l48nU_KD2_labelAll n hKD2 lab hlab)
    (l48nU_P2_labelAll n hKD5b hKD5c lab hlab)

theorem ggRankOne_su6_at {n : ℕ} (hn : 2 ≤ n)
    (hKD2 : ∀ lab, LargeEvenInLambda2 lab →
      LargeEvenLabelAll lab (fun R _ I _ => GGRankOneShapeAt n lab R I))
    (hKD5b : GGSU6DiagInvertedKnown)
    (hKD5c : ∀ f : ℕ, 3 ∣ 2 ^ f + 1 →
      LargeEvenLabelAll (⟨.twA, 5, f⟩ : LargeEvenLabel) fun R _ I _ => GGSU6NoParabolicAtN n I)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig 3 B Bs x L D J)
    (hJ : GGHasLabel (⟨.A, 1, n⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J)) : False := by
  obtain ⟨-, -, hrank, hBcard, -⟩ := ggRankOne_card hcfg hn hJ
  obtain ⟨-, hx1, hx3, hperf⟩ := hcfg.data_L
  have hS : LargeEvenSStar 3 B x L := hcfg.1.2.2.2.2.2.2.1
  have hst : LargeEvenStandardType 3 B x L := hcfg.1.2.2.2.2.2.2.2
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hS.2.2.2.1.1
  have hB : IsElemAbelian 3 B := hS.1.1
  have hall := l48nU_pAll n hKD2 hKD5b hKD5c
  obtain ⟨lab, R, _, I, F, θ, e, a, J', A, hlam, hlabel, hP, hcommL, hsetup, hAab, hAcardmul,
    heA, haA, hAb, hAI0, hAJ⟩ := ggRankOne_marking hcfg hn hJ hall
  have hKD2body : l48nU_KD2 n lab R I F := hP.1
  have hP2 : l48nU_P2 n lab R I F := hP.2
  let ψ : ↥L →* R := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
  have hψsurj : Function.Surjective ψ :=
    θ.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center ↥L))
  have hψker : ψ.ker ≤ Subgroup.center ↥L := by
    intro l hl
    rw [MonoidHom.mem_ker] at hl
    have h2 : QuotientGroup.mk' (Subgroup.center ↥L) l = 1 :=
      θ.injective (by simpa [ψ, MonoidHom.comp_apply] using hl)
    have h3 : (l : ↥L ⧸ Subgroup.center ↥L) = 1 := by
      simpa only [QuotientGroup.mk'_apply] using h2
    exact (QuotientGroup.eq_one_iff l).mp h3
  have hsetup' : GGRankOneSetup I ψ 3 e J' n a := hsetup
  obtain ⟨m, hm1, hnm, hshape, houter⟩ :=
    hKD2body ↥L ψ hψsurj hψker hcommL e J' a hsetup'
  rcases hshape with ⟨hl, hpm⟩ | ⟨hl, hpm⟩
  · have hlabL : GGHasLabel (⟨.A, 2 * 3 - 1, m⟩ : LargeEvenLabel)
        (↥L ⧸ Subgroup.center ↥L) := by
      rw [hl] at hlabel
      exact hlabel
    have h5 := ggRankOne_linear_rank (p := 3) (m := m) (by norm_num) (by norm_num) hpm hLx hx3
      hx1 hcommL hlabL
    omega
  · have hlabT : GGHasLabel (⟨.twA, 5, m⟩ : LargeEvenLabel)
        (↥L ⧸ Subgroup.center ↥L) := by
      rw [hl] at hlabel
      exact hlabel
    have hP2app : GGSU6DiagInvertedAt I ∧ GGSU6NoParabolicAtN n I := hP2 ⟨m, hl, hpm⟩
    obtain ⟨hb, hc⟩ := hP2app
    obtain ⟨E, hEL, hE, hEcard, hEc⟩ := ggRankOne_toral_four hpm hcommL hlabT
    have hE3 : IsPGroup 3 E := fun g => ⟨1, by
      apply Subtype.ext
      simpa using hE.2 (g : G) g.2⟩
    have hEncyc : ¬ IsCyclic E := by
      intro hcyc
      obtain ⟨b, hb⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := E)
      have hdvd : Nat.card E ∣ 3 := hb ▸ orderOf_dvd_of_pow_eq_one
        (Subtype.ext (hE.2 b.val b.property) : b ^ 3 = 1)
      have hle := Nat.le_of_dvd (by norm_num : 0 < 3) hdvd
      rw [hEcard] at hle
      omega
    have hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup 3 S ∧ ¬ IsCyclic S := ⟨E, hEL, hE3, hEncyc⟩
    have hBL : B ≤ Subgroup.normalizer (L : Set G) := by
      intro b hb
      apply mem_normalizer_of_sstar hS hnc
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (hB.1.is_comm.comm (⟨b, hb⟩ : ↥B) ⟨x, hS.2.1⟩)
    obtain ⟨T, hTx, hT2, hBT, hTcomm⟩ := hst.2.1
    have hTL : T ≤ Subgroup.normalizer (L : Set G) := fun t ht =>
      mem_normalizer_of_sstar hS hnc (hTx ht)
    let ac : MulAut ↥L →* MulAut (↥L ⧸ Subgroup.center ↥L) :=
      CFSG.HardMathSupport.Timmesfeld.Coordinator.autCenterQuot ↥L
    let ρ : ↥T →* MulAut R := (MulAut.congr θ).toMonoidHom.comp
      (ac.comp ((Subgroup.normalizerMonoidHom (H := L)).comp (Subgroup.inclusion hTL)))
    let U : Subgroup (MulAut R) := ρ.range
    have hU2 : IsPGroup 2 U :=
      show IsPGroup 2 (ρ.range) from
        hT2.of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
    by_cases hUbot : U = ⊥
    · have hcent : L ≤ Subgroup.centralizer (T : Set G) := by
        intro l hl
        rw [Subgroup.mem_centralizer_iff]
        intro t ht
        have hρ1 : ρ ⟨t, ht⟩ = 1 := by
          have hmemU : ρ ⟨t, ht⟩ ∈ U := ⟨⟨t, ht⟩, rfl⟩
          rw [hUbot] at hmemU
          exact Subgroup.mem_bot.mp hmemU
        have h2 : ac (Subgroup.normalizerMonoidHom (H := L)
            (Subgroup.inclusion hTL ⟨t, ht⟩)) = 1 := by
          refine (MulAut.congr θ).injective ?_
          rw [map_one]
          simpa [ρ, ac, MonoidHom.comp_apply] using hρ1
        have h3 : Subgroup.normalizerMonoidHom (H := L) (Subgroup.inclusion hTL ⟨t, ht⟩) = 1 :=
          CFSG.HardMathSupport.Timmesfeld.Coordinator.autCenterQuot_injective_of_perfect
            (K := ↥L) hperf (by simpa [ac] using h2)
        have hmem : (⟨t, ht⟩ : ↥T).1 ∈ Subgroup.centralizer (L : Set G) := by
          have hker : Subgroup.inclusion hTL ⟨t, ht⟩ ∈
              (Subgroup.normalizerMonoidHom (H := L)).ker := by
            rw [MonoidHom.mem_ker]
            exact h3
          rw [Subgroup.normalizerMonoidHom_ker] at hker
          exact Subgroup.mem_subgroupOf.mp hker
        exact (Subgroup.mem_centralizer_iff.mp hmem l hl).symm
      have hTne : T ≠ ⊥ := by
        intro hTb
        apply hTcomm
        rw [hTb]
        exact Subgroup.commutator_bot_left B
      have h5 := ggRankOne_su6_case_one (m := m) hpm hLx hx3 hx1 hcommL hTne hT2 hTx hcent
        hlabT
      omega
    · have hAcard : Nat.card A = 3 ^ 3 := by
        have h := hAcardmul
        rw [hBcard] at h
        norm_num at h ⊢
        omega
      have hAI : ∀ c ∈ A, ∃ φ ∈ I, ∀ l : ↥L, φ (ψ l) = ψ (c l) := by
        intro c hcA
        obtain ⟨φ, hφI, hφ⟩ := hAI0 c hcA
        exact ⟨φ, hφI, fun l => by simpa [ψ, MonoidHom.comp_apply] using hφ l⟩
      have hAU : ∀ c ∈ A, ∀ φ : MulAut R, (∀ l : ↥L, φ (ψ l) = ψ (c l)) →
          ∀ u ∈ U, φ * u * φ⁻¹ ∈ U := by
        intro c hcA φ hφ u hu
        obtain ⟨t, ht⟩ := MonoidHom.mem_range.mp hu
        rw [← ht]
        obtain ⟨b, hbB, hcb⟩ := hAb c hcA
        have hbt : b * (t : G) * b⁻¹ ∈ T :=
          ((Subgroup.mem_normalizer_iff.mp (hBT hbB)) (t : G)).mp t.2
        let cb : MulAut ↥L :=
          Subgroup.normalizerMonoidHom (H := L) (Subgroup.inclusion hBL ⟨b, hbB⟩)
        let ctt : MulAut ↥L :=
          Subgroup.normalizerMonoidHom (H := L) (Subgroup.inclusion hTL t)
        let ctbt : MulAut ↥L :=
          Subgroup.normalizerMonoidHom (H := L)
            (Subgroup.inclusion hTL ⟨b * (t : G) * b⁻¹, hbt⟩)
        have hc_eq : c = cb := by
          ext l
          simpa [cb, Subgroup.normalizerMonoidHom_apply_apply_coe] using hcb l
        have hct_eq : ctbt = cb * ctt * cb⁻¹ := by
          have hx : (Subgroup.inclusion hTL ⟨b * (t : G) * b⁻¹, hbt⟩ :
                ↥(Subgroup.normalizer (L : Set G))) =
              Subgroup.inclusion hBL ⟨b, hbB⟩ * Subgroup.inclusion hTL t *
                (Subgroup.inclusion hBL ⟨b, hbB⟩)⁻¹ := by
            ext
            rfl
          show Subgroup.normalizerMonoidHom (H := L)
                (Subgroup.inclusion hTL ⟨b * (t : G) * b⁻¹, hbt⟩) =
              Subgroup.normalizerMonoidHom (H := L) (Subgroup.inclusion hBL ⟨b, hbB⟩) *
              Subgroup.normalizerMonoidHom (H := L) (Subgroup.inclusion hTL t) *
              (Subgroup.normalizerMonoidHom (H := L) (Subgroup.inclusion hBL ⟨b, hbB⟩))⁻¹
          rw [hx, map_mul, map_mul, map_inv]
        have hφ_eq : φ = (MulAut.congr θ) (ac c) := by
          ext r
          obtain ⟨l, rfl⟩ := hψsurj r
          rw [hφ l]
          change θ (QuotientGroup.mk' (Subgroup.center ↥L) (c l)) =
            θ (ac c (θ.symm (θ (QuotientGroup.mk' (Subgroup.center ↥L) l))))
          rw [MulEquiv.symm_apply_apply]
          rw [show ac c (QuotientGroup.mk' (Subgroup.center ↥L) l) =
              QuotientGroup.mk' (Subgroup.center ↥L) (c l) from
            CFSG.HardMathSupport.Timmesfeld.Coordinator.autCenterQuot_mk c l]
        have hconj : φ * ρ t * φ⁻¹ = ρ ⟨b * (t : G) * b⁻¹, hbt⟩ := by
          rw [hφ_eq]
          have hrt : ρ t = (MulAut.congr θ) (ac ctt) := rfl
          have hrtb : ρ ⟨b * (t : G) * b⁻¹, hbt⟩ = (MulAut.congr θ) (ac ctbt) := rfl
          rw [hrt, hrtb, ← map_inv, ← map_mul, ← map_mul]
          congr 1
          rw [← map_inv, ← map_mul, ← map_mul]
          congr 1
          rw [hc_eq, hct_eq]
        exact ⟨⟨b * (t : G) * b⁻¹, hbt⟩, hconj.symm⟩
      exact ggRankOne_su6_cases_at hb ψ hψsurj hψker hcommL hsetup' houter
        (hc ↥L ψ hψsurj hψker hcommL e J' a hsetup') A hAab hAcard
        heA haA hAI hAJ U hUbot hU2 hAU

end CFSG.StandardType

end
