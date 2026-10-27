module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.BNGenerationOpp
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFactsNineteenElevenTwentyOne
public import CFSG.LocalAnalysis.UniquenessCase.UC22S218GLift
import CFSG.LocalAnalysis.UniquenessCase.UC22P21k
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ParabolicTransfer
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K534Group
import CFSG.RankThree.PartOne.S12.Sec15Frattini
import CFSG.GroupTheory.ConjQuot
import CFSG.GroupTheory.CommutingConjugatePair
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

section Tools

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_of_mk_mem_barOfInter {M D : Subgroup G} (hO2 : pCoreOf 2 D ≤ M) {x : ↥D}
    (hx : QuotientGroup.mk' (CFSG.pCore 2 ↥D) x ∈ barOfInter M D) : (x : G) ∈ M := by
  obtain ⟨y, hy, hyx⟩ := hx
  have h1 : y⁻¹ * x ∈ CFSG.pCore 2 ↥D := QuotientGroup.eq.1 hyx
  have h2 : ((y⁻¹ * x : ↥D) : G) ∈ M := hO2 ((CFSG.mem_openPCoreOf_iff _).2 h1)
  have h3 : (y : G) ∈ M := (Subgroup.mem_subgroupOf.1 hy).2
  have h4 : (x : G) = (y : G) * ((y⁻¹ * x : ↥D) : G) := by simp
  rw [h4]
  exact M.mul_mem h3 h2

open CFSG.ABGLocalTools in
theorem isSylowOf_of_isParabolicTwo_barOfInter {M D P₀ : Subgroup G}
    (hpar : IsParabolicTwo (Bar2 D) (barOfInter M D)) (hO2 : pCoreOf 2 D ≤ M)
    (hP₀ : IsSylowOf 2 P₀ (D ⊓ M)) : IsSylowOf 2 P₀ D := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPO : ParabolicOf D (D ⊓ M) :=
    ⟨le_inf (Subgroup.map_subtype_le _) hO2, inf_le_left, hpar⟩
  obtain ⟨-, Q, hQ⟩ := parabolicOf_iff.1 hPO
  have hQ' : IsSylowOf 2 ((Q : Subgroup ↥D).map D.subtype) D := ⟨Q, rfl⟩
  have hQM : (Q : Subgroup ↥D).map D.subtype ≤ D ⊓ M := by
    rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.mem_subgroupOf.1 (hQ (Subgroup.le_normalizer hx))
  have hQ'' := hQ'.of_le hQM inf_le_left
  refine isSylowOf_of_card (hP₀.le.trans inf_le_left) ?_
  rw [hP₀.card_eq, ← hQ''.card_eq, hQ'.card_eq]

theorem mem_of_mem_solvableRadical_barOfInter {M D : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple (Bar2 D)) (hpar : IsParabolicTwo (Bar2 D) (barOfInter M D))
    (hO2 : pCoreOf 2 D ≤ M) {x : ↥D} (hx : x ∈ CFSG.solvableRadical ↥D) : (x : G) ∈ M := by
  refine mem_of_mk_mem_barOfInter hO2 (hpar.center_le ?_)
  rw [← uc22p21k_map_solvableRadical_eq_center hq]
  exact Subgroup.mem_map_of_mem _ hx

theorem mem_of_mem_normalizer_sylow_barOfInter {M D : Subgroup G}
    (hpar : IsParabolicTwo (Bar2 D) (barOfInter M D)) (hO2 : pCoreOf 2 D ≤ M) (Q : Sylow 2 ↥D)
    (hQM : (Q : Subgroup ↥D) ≤ (D ⊓ M).subgroupOf D) {x : ↥D}
    (hx : x ∈ normalizer ((Q : Subgroup ↥D) : Set ↥D)) : (x : G) ∈ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Qb : Sylow 2 (Bar2 D) := Q.mapSurjective (QuotientGroup.mk'_surjective _) with hQb
  have hQbM : (Qb : Subgroup (Bar2 D)) ≤ barOfInter M D := by
    rw [hQb, Sylow.coe_mapSurjective]
    exact Subgroup.map_mono hQM
  have e : (Qb : Subgroup (Bar2 D)) = (Q : Subgroup ↥D).map (QuotientGroup.mk' _) := by
    rw [hQb, Sylow.coe_mapSurjective]
  have hN : normalizer ((Qb : Subgroup (Bar2 D)) : Set (Bar2 D)) ≤ barOfInter M D :=
    hpar.normalizer_le Qb hQbM
  refine mem_of_mk_mem_barOfInter hO2 (hN ?_)
  rw [e]
  exact Subgroup.le_normalizer_map _ (Subgroup.mem_map_of_mem _ hx)

theorem mem_of_piInf_mem_normalizer {M D : Subgroup G} (hq : CFSG.Open.IsQuasisimple (Bar2 D))
    (hpar : IsParabolicTwo (Bar2 D) (barOfInter M D)) (hO2 : pCoreOf 2 D ≤ M) (Q : Sylow 2 ↥D)
    (hQM : (Q : Subgroup ↥D) ≤ (D ⊓ M).subgroupOf D) {x : ↥D}
    (hx : piInf D x ∈
      normalizer (((Q : Subgroup ↥D).map (piInf D) : Subgroup (BarInf D)) : Set (BarInf D))) :
    (x : G) ∈ M := by
  rw [normalizer_map_sylow_eq (piInf D) (QuotientGroup.mk'_surjective _) Q] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  have h1 : y⁻¹ * x ∈ CFSG.solvableRadical ↥D := QuotientGroup.eq.1 hyx
  have h2 := M.mul_mem (mem_of_mem_normalizer_sylow_barOfInter hpar hO2 Q hQM hy)
    (mem_of_mem_solvableRadical_barOfInter hq hpar hO2 h1)
  simpa using h2

theorem map_piInf_ne_bot {M D : Subgroup G} (hq : CFSG.Open.IsQuasisimple (Bar2 D))
    (hpar : IsNontrivialParabolic (Bar2 D) (barOfInter M D)) (Q : Sylow 2 ↥D)
    (hQM : (Q : Subgroup ↥D) ≤ (D ⊓ M).subgroupOf D) :
    (Q : Subgroup ↥D).map (piInf D) ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hbot
  apply hpar.2.1
  set Qb : Sylow 2 (Bar2 D) := Q.mapSurjective (QuotientGroup.mk'_surjective _) with hQb
  have hQbM : (Qb : Subgroup (Bar2 D)) ≤ barOfInter M D := by
    rw [hQb, Sylow.coe_mapSurjective]
    exact Subgroup.map_mono hQM
  have hQZ : (Qb : Subgroup (Bar2 D)) ≤ center (Bar2 D) := by
    rw [hQb, Sylow.coe_mapSurjective, ← uc22p21k_map_solvableRadical_eq_center hq]
    apply Subgroup.map_mono
    intro x hx
    have h1 : piInf D x ∈ (Q : Subgroup ↥D).map (piInf D) := Subgroup.mem_map_of_mem _ hx
    rw [hbot, Subgroup.mem_bot] at h1
    exact (QuotientGroup.eq_one_iff x).1 h1
  have hn : (Qb : Subgroup (Bar2 D)).Normal := Subgroup.normal_of_le_center hQZ
  have hN : normalizer ((Qb : Subgroup (Bar2 D)) : Set (Bar2 D)) ≤ barOfInter M D :=
    hpar.1.normalizer_le Qb hQbM
  rw [Subgroup.normalizer_eq_top_iff.2 hn] at hN
  exact eq_top_iff.2 hN

theorem eq_top_of_map_piInf_eq_top {D : Subgroup G} (hq : CFSG.Open.IsQuasisimple (Bar2 D))
    {J : Subgroup ↥D} (hO : CFSG.pCore 2 ↥D ≤ J) (hJ : J.map (piInf D) = ⊤) : J = ⊤ := by
  have h1 : J ⊔ CFSG.solvableRadical ↥D = ⊤ := by
    have h := Subgroup.comap_map_eq (piInf D) J
    rw [hJ, Subgroup.comap_top] at h
    have hk : (piInf D).ker = CFSG.solvableRadical ↥D := QuotientGroup.ker_mk' _
    rw [← hk, ← h]
  have h2 : J.map (QuotientGroup.mk' (CFSG.pCore 2 ↥D)) ⊔ center (Bar2 D) = ⊤ := by
    rw [← uc22p21k_map_solvableRadical_eq_center hq, ← Subgroup.map_sup, h1,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  have h3 := CFSG.LocalAnalysis.RankThreeUC.S15.K534Proof.eq_top_of_sup_center_eq_top hq h2
  have h4 := Subgroup.comap_map_eq (QuotientGroup.mk' (CFSG.pCore 2 ↥D)) J
  rw [h3, Subgroup.comap_top, QuotientGroup.ker_mk', sup_eq_left.2 hO] at h4
  exact h4.symm

end Tools

theorem k_19_21_BN_of_eq_bot {G : Type} [Group G] {M Dsub A E : Subgroup G} {r : ℕ}
    (hP : ∃ P₀ : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 2 P₀ (Dsub ⊓ M) ∧
      A ≤ normalizer (P₀ : Set G)) (hE : E = ⊥) :
    ∃ R P : Subgroup G, IsPGroup r R ∧ E ≤ R ∧ R ≤ M ∧
      CFSG.ABGLocalTools.IsSylowOf 2 P (Dsub ⊓ M) ∧
      Dsub ≤ P ⊔ (Dsub ⊓ normalizer (R : Set G)) := by
  obtain ⟨P₀, hP₀, -⟩ := hP
  refine ⟨⊥, P₀, IsPGroup.of_bot, hE.le, bot_le, hP₀, ?_⟩
  rw [Subgroup.normalizer_eq_top_iff.2 inferInstance, inf_top_eq]
  exact le_sup_right

open CFSG.ABGLocalTools in
theorem k_19_21_BN_of_opp
    (hopp : ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → List19_16_5 S → K_19_21_opp S) :
    K_19_21_BN := by
  intro G _ _ M D A E r hq hL hpar hO2 hAM hAN _hAab hAodd hP hr hEA hE
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact r.Prime := ⟨hr⟩
  by_cases hr2 : r = 2
  · subst hr2
    refine k_19_21_BN_of_eq_bot hP ?_
    have h := CFSG.GroupTheory.inf_eq_bot_of_isPGroup_two_of_odd hE hAodd
    rwa [inf_eq_left.2 hEA] at h
  obtain ⟨P₀, hP₀, hAP₀⟩ := hP
  have hP₀D : IsSylowOf 2 P₀ D := isSylowOf_of_isParabolicTwo_barOfInter hpar.1 hO2 hP₀
  obtain ⟨Q₀, hQ₀⟩ := hP₀D.exists_sylow_eq_subgroupOf
  have hQ₀M : (Q₀ : Subgroup ↥D) ≤ (D ⊓ M).subgroupOf D := by
    rw [hQ₀]
    intro x hx
    exact Subgroup.mem_subgroupOf.2 ⟨x.2, (hP₀.le (Subgroup.mem_subgroupOf.1 hx)).2⟩
  set Uh : Sylow 2 (BarInf D) := Q₀.mapSurjective (QuotientGroup.mk'_surjective _) with hUh
  have hUhc : (Uh : Subgroup (BarInf D)) = (Q₀ : Subgroup ↥D).map (piInf D) := by
    rw [hUh, Sylow.coe_mapSurjective]
    rfl
  have hUne : (Uh : Subgroup (BarInf D)) ≠ ⊥ := by
    rw [hUhc]
    exact map_piInf_ne_bot hq hpar Q₀ hQ₀M
  have hEN : E ≤ normalizer (D : Set G) := hEA.trans hAN
  set φ : ↥E →* MulAut (BarInf D) := (rhoInf D).comp (Subgroup.inclusion hEN) with hφ
  have hφapp : ∀ (e : G) (he : e ∈ E) (y : ↥D), φ ⟨e, he⟩ (piInf D y) =
      piInf D (Subgroup.normalizerMonoidHom D ⟨e, hEN he⟩ y) := fun _ _ _ => rfl
  set Eh : Subgroup (MulAut (BarInf D)) := φ.range with hEhdef
  have hEh : IsPGroup r Eh := hE.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  have hEhU : ∀ α ∈ Eh, (Uh : Subgroup (BarInf D)).map (MulEquiv.toMonoidHom α) = Uh := by
    rintro _ ⟨e, rfl⟩
    rw [hUhc, Subgroup.map_map]
    have hcomp : (MulEquiv.toMonoidHom (φ e)).comp (piInf D) =
        (piInf D).comp (Subgroup.normalizerMonoidHom D ⟨e, hEN e.2⟩ : ↥D →* ↥D) := by
      ext y
      rfl
    rw [hcomp, ← Subgroup.map_map, hQ₀,
      CFSG.GroupTheory.map_subgroupOf_normalizerMonoidHom_eq (hEN e.2) (hAP₀ (hEA e.2))]
  obtain ⟨H, nh, hHU, hnH, hHE, hnE, hgen⟩ :=
    hopp (BarInf D)
      ((MulEquiv.isSimpleGroup_congr (uc22p21k_barInf_equiv hq).some).mpr hq.2)
      hL Uh hUne r hr hr2 Eh hEh hEhU
  set Ht : Subgroup G := (H.comap (piInf D)).map D.subtype with hHt
  have hHtD : Ht ≤ D := Subgroup.map_subtype_le _
  have hmemHt : ∀ y : ↥D, (y : G) ∈ Ht ↔ piInf D y ∈ H := fun y => by
    rw [hHt]
    exact Subgroup.mem_map_iff_mem D.subtype_injective
  obtain ⟨n, hn⟩ := QuotientGroup.mk'_surjective (CFSG.solvableRadical ↥D) nh
  have hn' : piInf D n = nh := hn
  have hEHt : E ≤ normalizer (Ht : Set G) := by
    intro e he
    have hmapH : H.map (MulEquiv.toMonoidHom (φ ⟨e, he⟩)) = H := hHE _ ⟨⟨e, he⟩, rfl⟩
    have key : ∀ y : ↥D, piInf D y ∈ H ↔
        piInf D (Subgroup.normalizerMonoidHom D ⟨e, hEN he⟩ y) ∈ H := fun y => by
      rw [← hφapp e he y]
      conv_rhs => rw [← hmapH]
      rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hz : e * D.subtype y * e⁻¹ =
          ((Subgroup.normalizerMonoidHom D ⟨e, hEN he⟩ y : ↥D) : G) :=
        (rhoInf_mk_coe D ⟨e, hEN he⟩ y).symm
      rw [hz, hmemHt]
      exact (key y).1 hy
    · intro hx
      have hxD : x ∈ D := (Subgroup.mem_normalizer_iff.1 (hEN he) x).2 (hHtD hx)
      have hz : e * x * e⁻¹ =
          ((Subgroup.normalizerMonoidHom D ⟨e, hEN he⟩ ⟨x, hxD⟩ : ↥D) : G) :=
        (rhoInf_mk_coe D ⟨e, hEN he⟩ ⟨x, hxD⟩).symm
      rw [hz, hmemHt] at hx
      exact (hmemHt ⟨x, hxD⟩).2 ((key _).2 hx)
  have hnHt : (n : G) ∈ normalizer (Ht : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have e1 : (n : G) * D.subtype y * (n : G)⁻¹ = ((n * y * n⁻¹ : ↥D) : G) := by simp
      rw [e1, hmemHt, map_mul, map_mul, map_inv, hn']
      exact (Subgroup.mem_normalizer_iff.1 hnH _).1 hy
    · intro hx
      have hxD : x ∈ D := by
        have := D.mul_mem (D.mul_mem (D.inv_mem n.2) (hHtD hx)) n.2
        simpa [mul_assoc] using this
      have e1 : (n : G) * x * (n : G)⁻¹ = ((n * ⟨x, hxD⟩ * n⁻¹ : ↥D) : G) := by simp
      rw [e1, hmemHt, map_mul, map_mul, map_inv, hn'] at hx
      exact (hmemHt ⟨x, hxD⟩).2 ((Subgroup.mem_normalizer_iff.1 hnH _).2 hx)
  have hcomm : ∀ e ∈ E, (n : G) * e * (n : G)⁻¹ * e⁻¹ ∈ Ht := by
    intro e he
    set w : ↥D := n * Subgroup.normalizerMonoidHom D ⟨e, hEN he⟩ n⁻¹ with hw
    have hwv : (w : G) = (n : G) * e * (n : G)⁻¹ * e⁻¹ := by
      rw [hw, Subgroup.coe_mul, rhoInf_mk_coe]
      simp [mul_assoc]
    rw [← hwv, hmemHt]
    have hpw : piInf D w = nh * (φ ⟨e, he⟩ nh)⁻¹ := by
      rw [hw, map_mul, ← hφapp e he, map_inv, map_inv, hn']
    rw [hpw]
    have h1 := hnE (φ ⟨e, he⟩) ⟨⟨e, he⟩, rfl⟩
    have h2 := (Subgroup.mem_normalizer_iff.1 hnH _).1 (H.inv_mem h1)
    convert h2 using 1
    group
  set T : Subgroup G := Ht ⊔ E with hT
  have hTN : T ≤ normalizer (Ht : Set G) := sup_le Subgroup.le_normalizer hEHt
  have hnT : (n : G) ∈ normalizer (T : Set G) := by
    have hle : T.map (MulAut.conj (n : G)).toMonoidHom ≤ T := by
      rw [Subgroup.map_le_iff_le_comap]
      refine sup_le (fun x hx => ?_) (fun e he => ?_)
      · show (n : G) * x * (n : G)⁻¹ ∈ T
        exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.1 hnHt x).1 hx)
      · show (n : G) * e * (n : G)⁻¹ ∈ T
        have e1 : (n : G) * e * (n : G)⁻¹ = ((n : G) * e * (n : G)⁻¹ * e⁻¹) * e := by group
        rw [e1]
        exact T.mul_mem (Subgroup.mem_sup_left (hcomm e he)) (Subgroup.mem_sup_right he)
    have heq : T.map (MulAut.conj (n : G)).toMonoidHom = T :=
      Subgroup.eq_of_le_of_card_ge hle
        (le_of_eq (Subgroup.card_map_of_injective (MulAut.conj (n : G)).injective).symm)
    exact Subgroup.mem_normalizer_iff_map_conj_eq.2 heq
  obtain ⟨Q, hEQ⟩ := (hE.comap_subtype (K := T)).exists_le_sylow
  set R : Subgroup G := (Q : Subgroup ↥T).map T.subtype with hR
  have hRT : IsSylowOf r R T := ⟨Q, rfl⟩
  have hER : E ≤ R := fun e he => ⟨⟨e, Subgroup.mem_sup_right he⟩, hEQ he, rfl⟩
  obtain ⟨k, hkT, hkn⟩ :=
    CFSG.RankThree.PartOne.Sec15Frattini.exists_mem_normalizer_of_isSylowOf hRT hnT
  have hRN : R ≤ normalizer (Ht : Set G) := hRT.le.trans hTN
  have hTR : T ≤ Ht ⊔ R := sup_le le_sup_left (hER.trans le_sup_right)
  have hk2 : k ∈ ((Ht ⊔ R : Subgroup G) : Set G) := hTR hkT
  rw [Subgroup.coe_mul_of_right_le_normalizer_left Ht R hRN] at hk2
  obtain ⟨h', hh', ρ, hρ, rfl⟩ := hk2
  have hh'D : h' ∈ D := hHtD hh'
  have hm'R : h'⁻¹ * (n : G) ∈ normalizer (R : Set G) := by
    have e1 : h'⁻¹ * (n : G) = ρ * ((h' * ρ)⁻¹ * (n : G)) := by group
    rw [e1]
    exact (normalizer (R : Set G)).mul_mem (Subgroup.le_normalizer hρ) hkn
  have hm'D : h'⁻¹ * (n : G) ∈ D := D.mul_mem (D.inv_mem hh'D) n.2
  have hh'H : piInf D ⟨h', hh'D⟩ ∈ H := (hmemHt ⟨h', hh'D⟩).1 hh'
  have hpm' : piInf D (⟨h', hh'D⟩⁻¹ * n) = (piInf D ⟨h', hh'D⟩)⁻¹ * nh := by
    rw [map_mul, map_inv, hn']
  have hHtM : Ht ≤ M := by
    rintro _ ⟨y, hy, rfl⟩
    have hy' : piInf D y ∈ normalizer ((Uh : Subgroup (BarInf D)) : Set (BarInf D)) := hHU hy
    rw [hUhc] at hy'
    exact mem_of_piInf_mem_normalizer hq hpar.1 hO2 Q₀ hQ₀M hy'
  have hRM : R ≤ M := hRT.le.trans (sup_le hHtM (hEA.trans hAM))
  set J : Subgroup G := P₀ ⊔ (D ⊓ normalizer (R : Set G)) with hJ
  have hJ' : J.subgroupOf D = ⊤ := by
    have hQJ : (Q₀ : Subgroup ↥D) ≤ J.subgroupOf D := by
      rw [hQ₀]
      intro x hx
      exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.1 hx))
    refine eq_top_of_map_piInf_eq_top hq ?_ ?_
    · have : (CFSG.pCore 2 ↥D).Normal := CFSG.pCore_normal
      exact (CFSG.pCore_isPGroup.le_sylow_of_normal Q₀).trans hQJ
    · rw [eq_top_iff, ← hgen _ (H.inv_mem hh'H)]
      refine sup_le ?_ ?_
      · rw [hUhc]
        exact Subgroup.map_mono hQJ
      · rw [Subgroup.zpowers_le, ← hpm']
        refine Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 ?_)
        exact Subgroup.mem_sup_right (Subgroup.mem_inf.2 ⟨hm'D, hm'R⟩)
  exact ⟨R, P₀, hRT.isPGroup, hER, hRM, hP₀, Subgroup.subgroupOf_eq_top.1 hJ'⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

end
