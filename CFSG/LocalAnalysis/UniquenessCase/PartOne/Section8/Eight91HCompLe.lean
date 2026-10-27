module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91Defs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsGroup
public import CFSG.LocalAnalysis.AGLEmbedding.CatalogSchreier
import CFSG.CGT.Foote82.T66.BranchAGen
import CFSG.Adapters.LieModelL3U3Torus
import CFSG.GroupTheory.ComponentCovering
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddChain
import CFSG.ClassicalInvolution.RouteD.GapsPerfect
import CFSG.HardMathSupport.Timmesfeld.Coordinator.CentralExtRank
import CFSG.GroupTheory.Fitting.LayerContainment
import CFSG.HardMathSupport.Malle.E27Lie.Cross.PerfectQuotient
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.UniqueConjCtx
import all CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups.IsExtraspecialExpP
public import CFSG.LocalAnalysis.AGLEmbedding.ComponentRank
import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.LocalAnalysis.RankThreeUC (uniqueSet)
open CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups (IsExtraspecialExpP)
open scoped commutatorElement
open Pointwise
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner perfect_action_inner solvable_of_centerQuotient)

private theorem k891hcomple_noncentral_three {G : Type} [Group G] [Finite G] {K : Subgroup G}
    (hKq : CFSG.Open.IsQuasisimple K) (h3 : 3 ∣ Nat.card K) :
    ∃ y ∈ K, IsPGroup 3 (Subgroup.zpowers y) ∧ ∃ l ∈ K, y * l ≠ l * y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hKperf : commutator ↥K = ⊤ := hKq.1
  let P : Sylow 3 ↥K := Classical.choice Sylow.nonempty
  have hnot := CFSG.HardMathSupport.Malle.E27Lie.not_sylow_le_center_of_perfect hKperf h3 P
  obtain ⟨y, hyP, hyZ⟩ := Set.not_subset.mp hnot
  have hyq : IsPGroup 3 (Subgroup.zpowers y) :=
    P.isPGroup'.to_le (Subgroup.zpowers_le.mpr hyP)
  have hyZ' : ∃ l : ↥K, y * l ≠ l * y := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hyZ (Subgroup.mem_center_iff.mpr fun g => (h g).symm)
  obtain ⟨l, hl⟩ := hyZ'
  refine ⟨(y : G), y.2, ?_, (l : G), l.2, ?_⟩
  · have hm := hyq.map K.subtype
    rwa [MonoidHom.map_zpowers K.subtype y] at hm
  · exact fun h => hl (Subtype.ext h)

private theorem k891hcomple_component_count {E : Type} [Group E] [Finite E]
    (hrank : CFSG.Open.pRank 3 (⊤ : Subgroup E) ≤ 5) :
    Nat.card {A : Subgroup E // CFSG.Open.IsComponentOf A ⊤ ∧ 3 ∣ Nat.card A} ≤ 5 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcomp : ∀ i : {A : Subgroup E // CFSG.Open.IsComponentOf A ⊤ ∧ 3 ∣ Nat.card A},
      CFSG.Open.IsComponentOf i.1 ⊤ := fun i => i.2.1
  have hinj : Function.Injective
      (fun i : {A : Subgroup E // CFSG.Open.IsComponentOf A ⊤ ∧ 3 ∣ Nat.card A} => i.1) :=
    fun i j h => Subtype.ext h
  have hdvd : ∀ i : {A : Subgroup E // CFSG.Open.IsComponentOf A ⊤ ∧ 3 ∣ Nat.card A},
      3 ∣ Nat.card i.1 := fun i => i.2.2
  have h := CFSG.AGLEmbedding.le_pRank_of_components (q := 3) Nat.prime_three
    (fun i : {A : Subgroup E // CFSG.Open.IsComponentOf A ⊤ ∧ 3 ∣ Nat.card A} => i.1)
    hcomp hinj (⊤ : Subgroup E)
    (fun i => Classical.choose (k891hcomple_noncentral_three (i.2.1.2.2) (hdvd i)))
    (fun i => Subgroup.mem_top _)
    (fun i => (Classical.choose_spec (k891hcomple_noncentral_three (i.2.1.2.2) (hdvd i))).1)
    (fun i => (Classical.choose_spec (k891hcomple_noncentral_three (i.2.1.2.2) (hdvd i))).2.1)
    (fun i => (Classical.choose_spec (k891hcomple_noncentral_three (i.2.1.2.2) (hdvd i))).2.2)
  exact h.trans hrank

private theorem k891hcomple_rank_Hstar {G : Type} [Group G] [Finite G]
    (L S : Subgroup G) (hH3 : CFSG.Open.pRank 3 (R891H L S) ≤ 3)
    (hZorder : Nat.card (R891Z L S) = 3) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (R891Star (R891H L S) (R891Z L S))) ≤ 5 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZH : R891Z L S ≤ R891H L S := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_iff.mp hz.2 y hy.1
  have hZcard : Nat.card ((R891Z L S).subgroupOf (R891H L S)) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZH).toEquiv]
    exact hZorder
  have hZc : (R891Z L S).subgroupOf (R891H L S) ≤ Subgroup.center ↥(R891H L S) := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp g.2 z (Subgroup.mem_subgroupOf.mp hz)).symm
  have : ((R891Z L S).subgroupOf (R891H L S)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hZH).mpr
      (Subgroup.centralizer_le_normalizer (R891Z L S : Set G))
  have hbound := CFSG.HardMathSupport.Timmesfeld.Coordinator.pRank_quotient_le_of_central
      (L := ↥(R891H L S)) (p := 3) Nat.prime_three (by norm_num : (3 : ℕ) ≠ 2)
      ((R891Z L S).subgroupOf (R891H L S)) hZc hZcard
  have hHtop_le : CFSG.Open.pRank 3 (⊤ : Subgroup ↥(R891H L S)) ≤ 3 :=
    (le_of_eq (CFSG.SectionRank.pRank_eq_pRank_top_subgroup (R891H L S)).symm).trans hH3
  have hQ_le : CFSG.Open.pRank 3
      (⊤ : Subgroup (↥(R891H L S) ⧸ (R891Z L S).subgroupOf (R891H L S))) ≤ 5 := by
    have h1 : CFSG.Open.pRank 3
        (⊤ : Subgroup (↥(R891H L S) ⧸ (R891Z L S).subgroupOf (R891H L S))) / 2 ≤ 2 := by
      omega
    have h2 := (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2)).mp
      (show CFSG.Open.pRank 3
        (⊤ : Subgroup (↥(R891H L S) ⧸ (R891Z L S).subgroupOf (R891H L S))) / 2 < 3 by omega)
    omega
  have : (CFSG.pPrimeCore 3 ↥(R891H L S)).Normal := inferInstance
  have hKer_eq : R891Ker (R891H L S) (R891Z L S) =
      CFSG.pPrimeCore 3 ↥(R891H L S) ⊔ (R891Z L S).subgroupOf (R891H L S) := by
    unfold R891Ker
    refine le_antisymm ?_ ?_
    · refine Subgroup.normalClosure_le_normal ?_
      intro x hx
      rcases hx with hx | hx
      · exact Subgroup.mem_sup_left hx
      · exact Subgroup.mem_sup_right hx
    · exact sup_le
        (fun x hx => Subgroup.subset_normalClosure (Set.subset_union_left hx))
        (fun x hx => Subgroup.subset_normalClosure (Set.subset_union_right hx))
  have hZleKer : (R891Z L S).subgroupOf (R891H L S) ≤ R891Ker (R891H L S) (R891Z L S) := by
    rw [hKer_eq]; exact le_sup_right
  have hKbar : (R891Ker (R891H L S) (R891Z L S)).map
      (QuotientGroup.mk' ((R891Z L S).subgroupOf (R891H L S))) =
      (CFSG.pPrimeCore 3 ↥(R891H L S)).map
        (QuotientGroup.mk' ((R891Z L S).subgroupOf (R891H L S))) := by
    rw [hKer_eq, Subgroup.map_sup]
    have hbot : ((R891Z L S).subgroupOf (R891H L S)).map
        (QuotientGroup.mk' ((R891Z L S).subgroupOf (R891H L S))) = ⊥ := by
      rw [Subgroup.map_eq_bot_iff]
      intro z hz
      exact (QuotientGroup.eq_one_iff z).mpr hz
    rw [hbot, sup_bot_eq]
  have hKbar_coprime : ¬ 3 ∣ Nat.card ((R891Ker (R891H L S) (R891Z L S)).map
      (QuotientGroup.mk' ((R891Z L S).subgroupOf (R891H L S)))) := by
    rw [hKbar]
    intro hd
    have hcop : Nat.Coprime 3 (Nat.card (CFSG.pPrimeCore 3 ↥(R891H L S))) :=
      CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥(R891H L S))
    exact (Nat.prime_three.coprime_iff_not_dvd).mp hcop
      (hd.trans (Subgroup.card_map_dvd (CFSG.pPrimeCore 3 ↥(R891H L S))
        (QuotientGroup.mk' ((R891Z L S).subgroupOf (R891H L S)))))
  have : ((R891Ker (R891H L S) (R891Z L S)).map
      (QuotientGroup.mk' ((R891Z L S).subgroupOf (R891H L S)))).Normal :=
    ((inferInstance : (R891Ker (R891H L S) (R891Z L S)).Normal).map
      (QuotientGroup.mk' ((R891Z L S).subgroupOf (R891H L S)))
      (QuotientGroup.mk'_surjective _))
  have hiso := QuotientGroup.quotientQuotientEquivQuotient
      (N := (R891Z L S).subgroupOf (R891H L S))
      (M := R891Ker (R891H L S) (R891Z L S)) hZleKer
  have hrankQbar : CFSG.Open.pRank 3
      (⊤ : Subgroup ((↥(R891H L S) ⧸ (R891Z L S).subgroupOf (R891H L S)) ⧸
        (R891Ker (R891H L S) (R891Z L S)).map
          (QuotientGroup.mk' ((R891Z L S).subgroupOf (R891H L S))))) =
      CFSG.Open.pRank 3
        (⊤ : Subgroup (↥(R891H L S) ⧸ (R891Z L S).subgroupOf (R891H L S))) :=
    CFSG.SectionRank.pRank_quotient_eq
      (N := (R891Ker (R891H L S) (R891Z L S)).map
        (QuotientGroup.mk' ((R891Z L S).subgroupOf (R891H L S)))) hKbar_coprime
  have hrankIso : CFSG.Open.pRank 3
      (⊤ : Subgroup (↥(R891H L S) ⧸ R891Ker (R891H L S) (R891Z L S))) =
      CFSG.Open.pRank 3
        (⊤ : Subgroup ((↥(R891H L S) ⧸ (R891Z L S).subgroupOf (R891H L S)) ⧸
          (R891Ker (R891H L S) (R891Z L S)).map
            (QuotientGroup.mk' ((R891Z L S).subgroupOf (R891H L S))))) :=
    (CFSG.SectionRank.pRank_top_eq_of_mulEquiv Nat.prime_three.one_lt hiso).symm
  change CFSG.Open.pRank 3
    (⊤ : Subgroup (↥(R891H L S) ⧸ R891Ker (R891H L S) (R891Z L S))) ≤ 5
  rw [hrankIso, hrankQbar]
  exact hQ_le

private theorem k891hcomple_conj_comp {G : Type} [Group G] (a b : G) :
    (MulAut.conj a).toMonoidHom.comp (MulAut.conj b).toMonoidHom =
      (MulAut.conj (a * b)).toMonoidHom := by
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

private theorem k891hcomple_conj_inv_comp {G : Type} [Group G] (a : G) :
    (MulAut.conj a⁻¹).toMonoidHom.comp (MulAut.conj a).toMonoidHom = MonoidHom.id G := by
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    MonoidHom.id_apply]
  group

private theorem k891hcomple_sylow_le_M {G : Type} [Group G] [Finite G] (D : Data G)
    (L S R A : Subgroup G) (n : ℕ) (hst : R891State D L S R A n) {P : Subgroup G}
    (hP : IsSylowOf 3 P (R891H L S)) (hRP : R ≤ P) : P ≤ D.M := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hRcard, hexpR, -, -⟩ := (show Nat.card R = 3 ^ (1 + 2 * 1) ∧
      Monoid.exponent ↥R = 3 ∧ commutator ↥R = center ↥R ∧
      Nat.card (center ↥R) = 3 from hst.ctx.xShape.rExtra)
  have hR3 : IsPGroup 3 R := IsPGroup.of_card (by rw [hRcard])
  obtain ⟨x, hxR, hxZ⟩ : ∃ x ∈ R, x ∉ R891Z L S := by
    by_contra h
    push Not at h
    have hcard := Subgroup.card_le_of_le (h : R ≤ R891Z L S)
    rw [hRcard, hst.basic.zOrder] at hcard
    norm_num at hcard
  let B : Subgroup G := Subgroup.zpowers x
  have hBR : B ≤ R := Subgroup.zpowers_le.mpr hxR
  have hBcard : Nat.card B = 3 := by
    have hx3R : (⟨x, hxR⟩ : ↥R) ^ 3 = 1 := by
      have h := Monoid.pow_exponent_eq_one (⟨x, hxR⟩ : ↥R)
      rwa [hexpR] at h
    have hx3 : x ^ 3 = 1 := by simpa using congrArg Subtype.val hx3R
    have hx1 : x ≠ 1 := fun h1 => hxZ (h1 ▸ (R891Z L S).one_mem)
    have horder : orderOf x = 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hx3) with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hx1
      · exact h
    rw [show B = Subgroup.zpowers x from rfl, Nat.card_zpowers, horder]
  have hBL : B ≤ L := hBR.trans (hst.ctx.xShape.rSylow.trans inf_le_right)
  rcases hst.ctx.classes.classes B hBL hBcard with ⟨l, hlL, hBl⟩ | ⟨l, hlL, hBl⟩
  · exfalso
    have hlM : l ∈ D.M := (CFSG.Open.IsSubnormal.le hst.set.mem.1) hlL
    have hZl : (R891Z L S).map (MulAut.conj l).toMonoidHom ≤ R891X L (R891Z L S) n := by
      rw [← hBl]; exact hBR.trans hst.ctx.xShape.rLe
    have hZeq := hst.ctx.xShape.zWeak l hlM hZl
    have hxZ' : x ∈ R891Z L S := by
      have hx1 : x ∈ B := Subgroup.mem_zpowers x
      rw [hBl, hZeq] at hx1
      exact hx1
    exact hxZ hxZ'
  · have hlM : l ∈ D.M := (CFSG.Open.IsSubnormal.le hst.set.mem.1) hlL
    have hBlM : (A.map (MulAut.conj l).toMonoidHom) ≤ D.M := by
      calc A.map (MulAut.conj l).toMonoidHom ≤ D.M.map (MulAut.conj l).toMonoidHom :=
            Subgroup.map_mono hst.uniq.1
        _ = D.M := Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hlM)
    have hBuniq : B ∈ uniqueSet D.M := by
      rw [hBl]
      refine CFSG.LocalAnalysis.AGL81TheoremCD.Section12.mem_uniqueSet_of_memUniqueConj
        D.maxLocal hBlM ?_
      intro g hg
      have hAlg : A ≤ D.M.map (MulAut.conj (l⁻¹ * g)).toMonoidHom := by
        have h1 := Subgroup.map_mono (f := (MulAut.conj l⁻¹).toMonoidHom) hg
        rw [Subgroup.map_map, Subgroup.map_map, k891hcomple_conj_inv_comp l,
          k891hcomple_conj_comp l⁻¹ g, Subgroup.map_id] at h1
        exact h1
      have hgM : l⁻¹ * g ∈ D.M :=
        (CFSG.LocalAnalysis.AGL81TheoremCD.Section12.memUniqueConj_of_mem_uniqueSet
          D.maxLocal hst.uniq) (l⁻¹ * g) hAlg
      have : g = l * (l⁻¹ * g) := by group
      rw [this]
      exact D.M.mul_mem hlM hgM
    exact CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.le_of_mem_uniqueSet_of_isPGroup
      D.maxLocal hBuniq (hBR.trans hRP) hP.isPGroup

private theorem k891hcomple_cQ_eq_map_Z {G : Type} [Group G] [Finite G]
    (X Z : Subgroup G) (hZX : Z ≤ X) (hZcX : Z ≤ Subgroup.centralizer (X : Set G))
    (_hQ : CFSG.Open.IsQuasisimple (Bar2 X))
    (hcQ3 : Nat.card (Subgroup.center (Bar2 X)) = 3) (hZ3 : Nat.card Z = 3) :
    Subgroup.center (Bar2 X) =
      Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 ↥X)) (Z.subgroupOf X) := by
  set O2X : Subgroup ↥X := CFSG.pCore 2 ↥X with hO2X
  set Zi : Subgroup ↥X := Z.subgroupOf X with hZi
  let q : ↥X →* Bar2 X := QuotientGroup.mk' O2X
  have hZi_center : Zi ≤ Subgroup.center ↥X := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro x
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp (hZcX (Subgroup.mem_subgroupOf.mp hz)) (x : G) x.2)
  have hmap_le : Zi.map q ≤ Subgroup.center (Bar2 X) := by
    rw [hZi]
    exact ((Subgroup.map_mono hZi_center).trans
      (Subgroup.map_center_le_center (f := q) (QuotientGroup.mk'_surjective O2X)))
  have hZi_card : Nat.card Zi = 3 := by
    rw [hZi, CFSG.natCard_subgroupOf_eq _ _ hZX, hZ3]
  have hmap_card_dvd : Nat.card (Zi.map q) ∣ 3 := by
    rw [← hZi_card]
    exact Subgroup.card_map_dvd Zi q
  have hmap_card_ne_one : Nat.card (Zi.map q) ≠ 1 := by
    intro h1
    have hbot : Zi.map q = ⊥ := Subgroup.eq_bot_of_card_eq (H := Zi.map q) h1
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥X)).exists_card_eq
    have h3dvd : 3 ∣ Nat.card O2X := by
      have h := Subgroup.card_dvd_of_le hbot
      rwa [hZi_card] at h
    rw [hk] at h3dvd
    exact absurd (Nat.prime_three.dvd_of_dvd_pow h3dvd) (by norm_num)
  have hmap_card : Nat.card (Zi.map q) = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hmap_card_dvd with h | h
    · exact absurd h hmap_card_ne_one
    · exact h
  exact (Subgroup.eq_of_le_of_card_ge hmap_le (by rw [hmap_card, hcQ3])).symm

private theorem k891hcomple_inf_pprimeCore_le_pCore {G : Type} [Group G] [Finite G]
    (H X : Subgroup G) (hXH : X ≤ H)
    (hQ : CFSG.Open.IsQuasisimple (Bar2 X))
    (hcQ3 : Nat.card (Subgroup.center (Bar2 X)) = 3) :
    ((CFSG.pPrimeCore 3 ↥H).map H.subtype).subgroupOf X ≤ CFSG.pCore 2 ↥X := by
  set Vg : Subgroup G := (CFSG.pPrimeCore 3 ↥H).map H.subtype with hVg
  let q : ↥X →* Bar2 X := QuotientGroup.mk' (CFSG.pCore 2 ↥X)
  set M : Subgroup (Bar2 X) := (Vg.subgroupOf X).map q with hM
  have hconjV : ∀ h ∈ H, ∀ v ∈ Vg, h * v * h⁻¹ ∈ Vg := by
    intro h hh v hv
    rw [hVg] at hv ⊢
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hv
    have := CFSG.pPrimeCore_normal.conj_mem w hw (⟨h, hh⟩ : ↥H)
    exact Subgroup.mem_map_of_mem H.subtype this
  have hsubXNorm : (Vg.subgroupOf X).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hconjV (g : G) (hXH g.2) (n : G) hn
  have hMnorm : M.Normal := by
    rw [hM]
    exact hsubXNorm.map q (QuotientGroup.mk'_surjective _)
  have hVcop : Nat.Coprime 3 (Nat.card Vg) := by
    rw [hVg, Subgroup.card_map_of_injective H.subtype_injective]
    exact CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥H)
  have hMcard_cop : Nat.Coprime 3 (Nat.card M) := by
    have hcard1 : Nat.card M ∣ Nat.card (Vg.subgroupOf X) := Subgroup.card_map_dvd _ q
    have hcard2 : Nat.card (Vg.subgroupOf X) = Nat.card ↥(Vg ⊓ X) := by
      have h := Subgroup.card_map_of_injective (K := Vg.subgroupOf X) (f := X.subtype)
        X.subtype_injective
      rw [Subgroup.subgroupOf_map_subtype Vg X] at h
      exact h.symm
    have hcard3 : Nat.card ↥(Vg ⊓ X) ∣ Nat.card Vg := Subgroup.card_dvd_of_le inf_le_left
    exact Nat.Coprime.of_dvd_right (hcard1.trans (hcard2 ▸ hcard3)) hVcop
  have h3dvdQ : 3 ∣ Nat.card (Bar2 X) := by
    rw [← hcQ3, ← Subgroup.card_top (G := Bar2 X)]
    exact Subgroup.card_dvd_of_le (le_top : Subgroup.center (Bar2 X) ≤ ⊤)
  have hQ' : CFSG.IsQuasisimple (Bar2 X) :=
    ⟨Group.isPerfect_def.2 hQ.1, hQ.2,
      CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hQ⟩
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hQ' hMnorm with htop | hcen
  · exfalso
    have hcopQ : Nat.Coprime 3 (Nat.card (Bar2 X)) := by
      rw [← Subgroup.card_top (G := Bar2 X)]
      rw [htop] at hMcard_cop
      exact hMcard_cop
    exact (Nat.prime_three.coprime_iff_not_dvd.mp hcopQ) h3dvdQ
  · have hMcard_dvd : Nat.card M ∣ 3 := by
      rw [← hcQ3]
      exact Subgroup.card_dvd_of_le hcen
    have hMcard : Nat.card M = 1 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp hMcard_dvd with h | h
      · exact h
      · exfalso
        rw [h] at hMcard_cop
        exact (Nat.prime_three.coprime_iff_not_dvd.mp hMcard_cop) dvd_rfl
    have hMbot : M = ⊥ := Subgroup.eq_bot_of_card_eq (H := M) hMcard
    rw [hM] at hMbot
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hMbot
    exact hMbot

private theorem k891hcomple_fker_le_gker {G : Type} [Group G] [Finite G]
    (H X Z : Subgroup G) (hXH : X ≤ H) (hZX : Z ≤ X)
    (hZcX : Z ≤ Subgroup.centralizer (X : Set G))
    (hZcH : Z ≤ Subgroup.centralizer (H : Set G)) (hZ3 : Nat.card Z = 3)
    (hQ : CFSG.Open.IsQuasisimple (Bar2 X))
    (hcQ3 : Nat.card (Subgroup.center (Bar2 X)) = 3) :
    ((QuotientGroup.mk' (R891Ker H Z)).comp (Subgroup.inclusion hXH)).ker ≤
      ((QuotientGroup.mk' (Subgroup.center (Bar2 X))).comp
        (QuotientGroup.mk' (CFSG.pCore 2 ↥X))).ker := by
  intro x hx
  have hxN : (⟨(x : G), hXH x.2⟩ : ↥H) ∈ R891Ker H Z := by
    have h := MonoidHom.mem_ker.mp hx
    rw [MonoidHom.comp_apply] at h
    exact (QuotientGroup.eq_one_iff _).mp h
  let V : Subgroup ↥H := CFSG.pPrimeCore 3 ↥H
  let Zs : Subgroup ↥H := Z.subgroupOf H
  have : V.Normal := CFSG.pPrimeCore_normal
  have hZs_center : Zs ≤ Subgroup.center ↥H := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro h
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp (hZcH (Subgroup.mem_subgroupOf.mp hz)) (h : G) h.2)
  have : Zs.Normal := Subgroup.normal_of_le_center hZs_center
  have hkerN : R891Ker H Z = V ⊔ Zs := by
    unfold R891Ker
    rw [normalClosure_union, normalClosure_eq_self, normalClosure_eq_self]
  rw [hkerN] at hxN
  obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup_of_normal_left.mp hxN
  have hbZ : (b : G) ∈ Z := Subgroup.mem_subgroupOf.mp hb
  have haV : (a : G) ∈ V.map H.subtype := Subgroup.mem_map_of_mem H.subtype ha
  have habG : (a : G) * (b : G) = (x : G) := by
    have := congrArg (fun y : ↥H => (y : G)) hab
    simpa using this
  have haX : (a : G) ∈ X := by
    have h : (a : G) = (x : G) * (b : G)⁻¹ := by rw [← habG]; group
    rw [h]
    exact X.mul_mem x.2 (X.inv_mem (hZX hbZ))
  have hbX : (b : G) ∈ X := hZX hbZ
  let a' : ↥X := ⟨(a : G), haX⟩
  let b' : ↥X := ⟨(b : G), hbX⟩
  have habX : a' * b' = x := by
    apply Subtype.ext
    simpa [a', b'] using habG
  have ha'O : a' ∈ CFSG.pCore 2 ↥X := by
    refine k891hcomple_inf_pprimeCore_le_pCore H X hXH hQ hcQ3 ?_
    rw [Subgroup.mem_subgroupOf]
    exact haV
  have hb'cQ : QuotientGroup.mk' (CFSG.pCore 2 ↥X) b' ∈ Subgroup.center (Bar2 X) := by
    have hb'Zi : b' ∈ Z.subgroupOf X := by
      rw [Subgroup.mem_subgroupOf]
      exact hbZ
    rw [k891hcomple_cQ_eq_map_Z X Z hZX hZcX hQ hcQ3 hZ3]
    exact Subgroup.mem_map_of_mem _ hb'Zi
  have hqa : QuotientGroup.mk' (CFSG.pCore 2 ↥X) a' = 1 :=
    (QuotientGroup.eq_one_iff _).mpr ha'O
  have hqx : QuotientGroup.mk' (CFSG.pCore 2 ↥X) x ∈ Subgroup.center (Bar2 X) := by
    rw [← habX, map_mul, hqa, one_mul]
    exact hb'cQ
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
  exact (QuotientGroup.eq_one_iff _).mpr hqx

private theorem k891hcomple_gker_eq {G : Type} [Group G] [Finite G]
    (X Z : Subgroup G) (hZX : Z ≤ X) (hZcX : Z ≤ Subgroup.centralizer (X : Set G))
    (hQ : CFSG.Open.IsQuasisimple (Bar2 X))
    (hcQ3 : Nat.card (Subgroup.center (Bar2 X)) = 3) (hZ3 : Nat.card Z = 3) :
    ((QuotientGroup.mk' (Subgroup.center (Bar2 X))).comp
        (QuotientGroup.mk' (CFSG.pCore 2 ↥X))).ker =
      CFSG.pCore 2 ↥X ⊔ Z.subgroupOf X := by
  have hcQ := k891hcomple_cQ_eq_map_Z X Z hZX hZcX hQ hcQ3 hZ3
  rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk', hcQ,
    Subgroup.comap_map_eq (f := QuotientGroup.mk' (CFSG.pCore 2 ↥X)) (Z.subgroupOf X),
    QuotientGroup.ker_mk', sup_comm]

private theorem k891hcomple_X_le_H {G : Type} [Group G] [Finite G] (D : Data G)
    (L S R A : Subgroup G) (n : ℕ) (hn : 2 ≤ n) (_hst : R891State D L S R A n) :
    R891X L (R891Z L S) n ≤ R891H L S := by
  have hn1 : n ≠ 1 := by omega
  rw [R891X, if_neg hn1]
  exact (Subgroup.map_subtype_le _).trans inf_le_right

private theorem k891hcomple_Z_le_X {G : Type} [Group G] [Finite G] (D : Data G)
    (L S R A : Subgroup G) (n : ℕ) (_hn : 2 ≤ n) (hst : R891State D L S R A n) :
    R891Z L S ≤ R891X L (R891Z L S) n :=
  hst.ctx.xShape.zLe.trans hst.ctx.xShape.rLe

private theorem k891hcomple_X_perfect {G : Type} [Group G] [Finite G] (D : Data G)
    (L S R A : Subgroup G) (n : ℕ) (hn : 2 ≤ n) (_hst : R891State D L S R A n) :
    Group.IsPerfect ↥(R891X L (R891Z L S) n) := by
  have hn1 : n ≠ 1 := by omega
  rw [R891X, if_neg hn1]
  have hperf : Group.IsPerfect ↥((⨅ k : ℕ, derivedSeries
      ↥(L ⊓ Subgroup.centralizer (R891Z L S : Set G)) k) :
        Subgroup ↥(L ⊓ Subgroup.centralizer (R891Z L S : Set G))) :=
    CFSG.perfect_residual_characterization.2.2.1
  have := hperf
  exact Group.IsPerfect.map (L ⊓ Subgroup.centralizer (R891Z L S : Set G)).subtype

private theorem k891hcomple_Bar2_quasisimple {G : Type} [Group G] [Finite G] (D : Data G)
    (L S R A : Subgroup G) (n : ℕ) (hn : 2 ≤ n) (hst : R891State D L S R A n) :
    CFSG.Open.IsQuasisimple (Bar2 (R891X L (R891Z L S) n)) := by
  rcases hst.ctx.xShape.xShape with ⟨h1, -⟩ | ⟨-, -, hc⟩ | ⟨-, -, hc⟩
  · omega
  · exact hc.1
  · exact hc.1

private theorem k891hcomple_center_Bar2_card {G : Type} [Group G] [Finite G] (D : Data G)
    (L S R A : Subgroup G) (n : ℕ) (hn : 2 ≤ n) (hst : R891State D L S R A n) :
    Nat.card (Subgroup.center (Bar2 (R891X L (R891Z L S) n))) = 3 := by
  rcases hst.ctx.xShape.xShape with ⟨h1, -⟩ | ⟨-, -, hc⟩ | ⟨-, -, hc⟩
  · omega
  · exact hc.2.1
  · exact hc.2.1

private theorem k891hcomple_f_range {G : Type} [Group G] [Finite G] (D : Data G)
    (L S R A : Subgroup G) (n : ℕ) (hn : 2 ≤ n) (hst : R891State D L S R A n) :
    ((QuotientGroup.mk' (R891Ker (R891H L S) (R891Z L S))).comp
        (Subgroup.inclusion (k891hcomple_X_le_H D L S R A n hn hst))).range =
      R891Img (R891H L S) (R891Z L S) (R891X L (R891Z L S) n) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr x.2)
  · intro hy
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨(x : G), Subgroup.mem_subgroupOf.mp hx⟩, hxy⟩

private theorem k891hcomple_phi {G : Type} [Group G] [Finite G] (D : Data G)
    (L S R A : Subgroup G) (n : ℕ) (hn : 2 ≤ n) (hst : R891State D L S R A n) :
    ∃ φ : ↥(R891Img (R891H L S) (R891Z L S) (R891X L (R891Z L S) n)) →*
        (Bar2 (R891X L (R891Z L S) n) ⧸
          Subgroup.center (Bar2 (R891X L (R891Z L S) n))),
      Function.Surjective φ ∧ IsPGroup 2 φ.ker := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set H : Subgroup G := R891H L S with hH
  set Z : Subgroup G := R891Z L S with hZ
  set X : Subgroup G := R891X L Z n with hX
  set N : Subgroup ↥H := R891Ker H Z with hN
  have hXH : X ≤ H := k891hcomple_X_le_H D L S R A n hn hst
  have hZX : Z ≤ X := k891hcomple_Z_le_X D L S R A n hn hst
  have hZcH : Z ≤ Subgroup.centralizer (H : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [hH] at hh
    exact (Subgroup.mem_centralizer_iff.mp hh z hz).symm
  have hZcX : Z ≤ Subgroup.centralizer (X : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (Subgroup.mem_centralizer_iff.mp (hXH hx) z hz).symm
  have hZ3 : Nat.card Z = 3 := hst.basic.zOrder
  have hQ : CFSG.Open.IsQuasisimple (Bar2 X) := k891hcomple_Bar2_quasisimple D L S R A n hn hst
  have hcQ3 : Nat.card (Subgroup.center (Bar2 X)) = 3 :=
    k891hcomple_center_Bar2_card D L S R A n hn hst
  let f : ↥X →* (↥H ⧸ N) := (QuotientGroup.mk' N).comp (Subgroup.inclusion hXH)
  have hfmem : ∀ x : ↥X, f x ∈ R891Img H Z X := fun x =>
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr x.2)
  have hfrange : f.range = R891Img H Z X := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact hfmem x
    · intro hy
      obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
      exact ⟨⟨(x : G), Subgroup.mem_subgroupOf.mp hx⟩, hxy⟩
  let g : ↥X →* (Bar2 X ⧸ Subgroup.center (Bar2 X)) :=
    (QuotientGroup.mk' (Subgroup.center (Bar2 X))).comp (QuotientGroup.mk' (CFSG.pCore 2 ↥X))
  have hle : f.ker ≤ g.ker := k891hcomple_fker_le_gker H X Z hXH hZX hZcX hZcH hZ3 hQ hcQ3
  let he : (↥X ⧸ f.ker) ≃* ↥(R891Img H Z X) :=
    (QuotientGroup.quotientKerEquivRange f).trans (MulEquiv.subgroupCongr hfrange)
  have hZs_center : Z.subgroupOf H ≤ Subgroup.center ↥H := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro h
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp (hZcH (Subgroup.mem_subgroupOf.mp hz)) (h : G) h.2)
  have : (Z.subgroupOf H).Normal := Subgroup.normal_of_le_center hZs_center
  have hkerN : R891Ker H Z = CFSG.pPrimeCore 3 ↥H ⊔ Z.subgroupOf H := by
    unfold R891Ker
    rw [normalClosure_union, normalClosure_eq_self, normalClosure_eq_self]
  have hZi_le_fker : Z.subgroupOf X ≤ f.ker := by
    intro z hz
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
    refine (QuotientGroup.eq_one_iff _).mpr ?_
    have : (CFSG.pPrimeCore 3 ↥H).Normal := CFSG.pPrimeCore_normal
    have hzN : (⟨(z : G), hXH z.2⟩ : ↥H) ∈ R891Ker H Z := by
      rw [hkerN]
      refine Subgroup.mem_sup_of_normal_left.mpr ⟨1, Subgroup.one_mem _, ?_⟩
      refine ⟨⟨(z : G), hXH z.2⟩, ?_, ?_⟩
      · exact hz
      · simp
    exact hzN
  have he_apply : ∀ x : ↥X, (he (QuotientGroup.mk' f.ker x) : R891Star H Z) = f x :=
    fun x => rfl
  let gbar : (↥X ⧸ f.ker) →* (Bar2 X ⧸ Subgroup.center (Bar2 X)) :=
    QuotientGroup.lift f.ker g hle
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center (Bar2 X)) y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥X) z
    exact ⟨x, rfl⟩
  have hgbar : Function.Surjective gbar :=
    QuotientGroup.lift_surjective_of_surjective (N := f.ker) g hg hle
  let φ : ↥(R891Img H Z X) →* (Bar2 X ⧸ Subgroup.center (Bar2 X)) :=
    gbar.comp he.symm.toMonoidHom
  have hφ_surj : Function.Surjective φ := hgbar.comp he.symm.surjective
  have hφ_apply : ∀ x : ↥X, φ ⟨f x, hfmem x⟩ = g x := by
    intro x
    have h1 : he.symm ⟨f x, hfmem x⟩ = QuotientGroup.mk' f.ker x := by
      apply he.injective
      rw [MulEquiv.apply_symm_apply]
      apply Subtype.ext
      exact he_apply x
    change gbar (he.symm ⟨f x, hfmem x⟩) = g x
    rw [h1]
    rfl
  have hgker : g.ker = CFSG.pCore 2 ↥X ⊔ Z.subgroupOf X :=
    k891hcomple_gker_eq X Z hZX hZcX hQ hcQ3 hZ3
  have hφker_le : φ.ker ≤ ((CFSG.pCore 2 ↥X).map f).subgroupOf (R891Img H Z X) := by
    intro y hy
    have hyval : (y : R891Star H Z) ∈ f.range := by
      rw [hfrange]; exact y.2
    obtain ⟨x, hxy⟩ := MonoidHom.mem_range.mp hyval
    have hy_eq : y = ⟨f x, hfmem x⟩ := by
      apply Subtype.ext
      exact hxy.symm
    have hgx : g x = 1 := by
      have := MonoidHom.mem_ker.mp hy
      rw [hy_eq, hφ_apply] at this
      exact this
    have hx_gker : x ∈ g.ker := MonoidHom.mem_ker.mpr hgx
    rw [hgker] at hx_gker
    have hfx_mem : f x ∈ (CFSG.pCore 2 ↥X).map f := by
      have h := Subgroup.mem_map_of_mem f hx_gker
      rwa [Subgroup.map_sup, (Subgroup.map_eq_bot_iff (H := Z.subgroupOf X) (f := f)).mpr hZi_le_fker, sup_bot_eq] at h
    rw [Subgroup.mem_subgroupOf]
    rw [← hxy]
    exact hfx_mem
  have hO2le : (CFSG.pCore 2 ↥X).map f ≤ R891Img H Z X :=
    (Subgroup.map_le_range _ _).trans (le_of_eq hfrange)
  have hO2sub_2 : IsPGroup 2 (((CFSG.pCore 2 ↥X).map f).subgroupOf (R891Img H Z X)) := by
    have h := (CFSG.pCore_isPGroup (p := 2) (G := ↥X)).map f
    exact h.of_equiv (Subgroup.subgroupOfEquivOfLe hO2le).symm
  exact ⟨φ, hφ_surj, hO2sub_2.to_le hφker_le⟩

private theorem k891hcomple_perfect_le_normalizer_of_card_le_five'
    {E : Type} [Group E] [Finite E] {X : Subgroup E}
    (hXperf : commutator X = ⊤)
    (hXO2 : IsSimpleGroup (↥X ⧸ CFSG.pCore 2 ↥X))
    (hbig : 120 < Nat.card (↥X ⧸ CFSG.pCore 2 ↥X))
    (S : Set (Subgroup E)) (hS : S.Finite) (hcard : S.ncard ≤ 5)
    (hstable : ∀ g ∈ X, ∀ A ∈ S, A.map (MulAut.conj g).toMonoidHom ∈ S)
    {A : Subgroup E} (hA : A ∈ S) : X ≤ Subgroup.normalizer (A : Set E) := by
  classical
  have hperfX : Group.IsPerfect ↥X := ⟨hXperf⟩
  have : Finite S := hS.to_subtype
  let _ : MulAction ↥X S :=
    { smul := fun g B => ⟨(ConjAct.toConjAct (g : E)) • B.1, by
          rw [CFSG.ClassicalInvolution.RouteD.Gaps.conjAct_smul_eq_map]
          exact hstable g g.2 B.1 B.2⟩
      one_smul := fun B => Subtype.ext (by
        show (ConjAct.toConjAct ((1 : ↥X) : E)) • B.1 = B.1
        rw [Subgroup.coe_one, map_one, one_smul])
      mul_smul := fun g h B => Subtype.ext (by
        show (ConjAct.toConjAct (((g * h : ↥X)) : E)) • B.1 =
          (ConjAct.toConjAct (g : E)) • ((ConjAct.toConjAct (h : E)) • B.1)
        rw [Subgroup.coe_mul, map_mul, mul_smul]) }
  have hact : MulAction.toPermHom ↥X S = 1 := by
    by_contra hne
    have hker_ne : (MulAction.toPermHom ↥X S).ker ≠ ⊤ := fun htop =>
      hne (MonoidHom.ker_eq_top_iff.mp htop)
    let N : Subgroup ↥X := (MulAction.toPermHom ↥X S).ker
    have hNnorm : N.Normal := (MulAction.toPermHom ↥X S).normal_ker
    have hNmap : (N.map (QuotientGroup.mk' (CFSG.pCore 2 ↥X))).Normal :=
      hNnorm.map _ (QuotientGroup.mk'_surjective _)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (N.map (QuotientGroup.mk' (CFSG.pCore 2 ↥X))) with hbar | hbar
    · have hNO2 : N ≤ CFSG.pCore 2 ↥X := by
        have h := (Subgroup.map_eq_bot_iff (H := N)
          (f := QuotientGroup.mk' (CFSG.pCore 2 ↥X))).mp hbar
        rwa [QuotientGroup.ker_mk'] at h
      have hquot_le : Nat.card (↥X ⧸ CFSG.pCore 2 ↥X) ≤
          Nat.card ↥(MulAction.toPermHom ↥X S).range := by
        let ψ : ↥X →* (↥X ⧸ CFSG.pCore 2 ↥X) := QuotientGroup.mk' (CFSG.pCore 2 ↥X)
        have hle : N ≤ ψ.ker := by rw [QuotientGroup.ker_mk']; exact hNO2
        let Ψ : (↥X ⧸ N) →* (↥X ⧸ CFSG.pCore 2 ↥X) := QuotientGroup.lift N ψ hle
        have hΨ : Function.Surjective Ψ :=
          QuotientGroup.lift_surjective_of_surjective N ψ (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥X)) hle
        have h1 : Nat.card (↥X ⧸ CFSG.pCore 2 ↥X) ≤ Nat.card (↥X ⧸ N) :=
          Nat.card_le_card_of_surjective Ψ hΨ
        have h2 : Nat.card (↥X ⧸ N) = Nat.card ↥(MulAction.toPermHom ↥X S).range :=
          Nat.card_congr (QuotientGroup.quotientKerEquivRange (MulAction.toPermHom ↥X S)).toEquiv
        rwa [h2] at h1
      have hrange_le : Nat.card ↥(MulAction.toPermHom ↥X S).range ≤ 120 := by
        have h1 : Nat.card ↥(MulAction.toPermHom ↥X S).range ≤ Nat.card (Equiv.Perm S) :=
          Subgroup.card_le_card_group _
        rw [Nat.card_perm] at h1
        have h2 : Nat.card S ≤ 5 := by rwa [Nat.card_coe_set_eq]
        have h3 : Nat.factorial (Nat.card S) ≤ 120 := by
          have := Nat.factorial_le h2
          norm_num at this
          exact this
        exact h1.trans h3
      omega
    · exfalso
      have hsurj : Function.Surjective ((QuotientGroup.mk' N).comp (CFSG.pCore 2 ↥X).subtype) := by
        intro q
        obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N q
        have hx : QuotientGroup.mk' (CFSG.pCore 2 ↥X) x ∈
            N.map (QuotientGroup.mk' (CFSG.pCore 2 ↥X)) := by rw [hbar]; exact Subgroup.mem_top _
        obtain ⟨n, hn, hnx⟩ := Subgroup.mem_map.mp hx
        have hker : n * x⁻¹ ∈ CFSG.pCore 2 ↥X := by
          apply (QuotientGroup.eq_one_iff (n * x⁻¹)).mp
          change (QuotientGroup.mk' (CFSG.pCore 2 ↥X)) (n * x⁻¹) = 1
          rw [map_mul, map_inv, hnx, mul_inv_cancel]
        have hconj : n⁻¹ * x ∈ CFSG.pCore 2 ↥X := by
          have hz : (n * x⁻¹)⁻¹ ∈ CFSG.pCore 2 ↥X := (CFSG.pCore 2 ↥X).inv_mem hker
          have := (inferInstance : (CFSG.pCore 2 ↥X).Normal).conj_mem (n * x⁻¹)⁻¹ hz n⁻¹
          rwa [show n⁻¹ * (n * x⁻¹)⁻¹ * (n⁻¹)⁻¹ = n⁻¹ * x by group] at this
        refine ⟨⟨n⁻¹ * x, hconj⟩, ?_⟩
        rw [MonoidHom.comp_apply, Subgroup.coe_subtype]
        have hn1 : (QuotientGroup.mk' N) n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
        have hx' : x = n * (n⁻¹ * x) := by group
        conv_rhs => rw [hx', map_mul, hn1, one_mul]
      have : Group.IsNilpotent ↥(CFSG.pCore 2 ↥X) := (CFSG.pCore_isPGroup (p := 2)).isNilpotent
      have hsolv : Group.IsSolvable (↥X ⧸ N) :=
        Group.isSolvable_of_surjective
          (f := (QuotientGroup.mk' N).comp (CFSG.pCore 2 ↥X).subtype) hsurj
      have hperf : Group.IsPerfect (↥X ⧸ N) :=
        hperfX.ofSurjective (QuotientGroup.mk'_surjective N)
      have hsub : Subsingleton (↥X ⧸ N) := by
        by_contra hnt
        have : Nontrivial (↥X ⧸ N) := not_subsingleton_iff_nontrivial.mp hnt
        exact Group.IsPerfect.not_isSolvable _ hsolv
      have hNtop : N = ⊤ := by
        rw [eq_top_iff]
        intro x _
        exact (QuotientGroup.eq_one_iff x).mp (Subsingleton.elim _ _)
      exact hker_ne hNtop
  intro g hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hg1 : MulAction.toPermHom ↥X S ⟨g, hg⟩ = 1 := by
    rw [hact, MonoidHom.one_apply]
  have hfix : (⟨g, hg⟩ : ↥X) • (⟨A, hA⟩ : S) = ⟨A, hA⟩ := by
    have := congrArg (fun f : Equiv.Perm S => f ⟨A, hA⟩) hg1
    simpa using this
  have hfix' := congrArg Subtype.val hfix
  change (ConjAct.toConjAct g) • A = A at hfix'
  rwa [CFSG.ClassicalInvolution.RouteD.Gaps.conjAct_smul_eq_map] at hfix'

private theorem k891hcomple_Xstar_perfect {G : Type} [Group G] [Finite G] (D : Data G)
    (L S R A : Subgroup G) (n : ℕ) (hn : 2 ≤ n) (hst : R891State D L S R A n) :
    commutator ↥(R891Img (R891H L S) (R891Z L S) (R891X L (R891Z L S) n)) = ⊤ := by
  have hXH : R891X L (R891Z L S) n ≤ R891H L S := k891hcomple_X_le_H D L S R A n hn hst
  let f0 : ↥(R891X L (R891Z L S) n) →* R891Star (R891H L S) (R891Z L S) :=
    (QuotientGroup.mk' (R891Ker (R891H L S) (R891Z L S))).comp (Subgroup.inclusion hXH)
  let f' : ↥(R891X L (R891Z L S) n) →*
      ↥(R891Img (R891H L S) (R891Z L S) (R891X L (R891Z L S) n)) :=
    f0.codRestrict _ fun x => Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr x.2)
  have hsurj : Function.Surjective f' := by
    intro y
    have hy : (y : R891Star (R891H L S) (R891Z L S)) ∈ f0.range := by
      rw [show f0.range = R891Img (R891H L S) (R891Z L S) (R891X L (R891Z L S) n) from
        k891hcomple_f_range D L S R A n hn hst]
      exact y.2
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, Subtype.ext hx⟩
  exact ((k891hcomple_X_perfect D L S R A n hn hst).ofSurjective hsurj).commutator_eq_top

private theorem k891hcomple_isPerfect_of_simple {Q : Type} [Group Q] [IsSimpleGroup Q]
    (hnc : ∃ a b : Q, a * b ≠ b * a) : Group.IsPerfect Q := by
  have hcomm : commutator Q ≠ ⊥ := by
    intro h
    obtain ⟨a, b, hab⟩ := hnc
    have hmem : ⁅a, b⁆ ∈ (⊥ : Subgroup Q) := by
      rw [← h, commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    exact hab (commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp hmem))
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator Q) with h | h
  · exact absurd h hcomm
  · exact ⟨h⟩

private theorem k891hcomple_Xstar_O2 {G : Type} [Group G] [Finite G] (D : Data G)
    (L S R A : Subgroup G) (n : ℕ) (hn : 2 ≤ n) (hst : R891State D L S R A n) :
    IsSimpleGroup (↥(R891Img (R891H L S) (R891Z L S) (R891X L (R891Z L S) n)) ⧸ CFSG.pCore 2 ↥(R891Img (R891H L S) (R891Z L S) (R891X L (R891Z L S) n))) := by
  classical
  obtain ⟨φ, hφsurj, hφker⟩ := k891hcomple_phi D L S R A n hn hst
  have hQ := k891hcomple_Bar2_quasisimple D L S R A n hn hst
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnc : ∃ a b : (Bar2 (R891X L (R891Z L S) n) ⧸
      Subgroup.center (Bar2 (R891X L (R891Z L S) n))), a * b ≠ b * a :=
    CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hQ
  have hSsimple : IsSimpleGroup (Bar2 (R891X L (R891Z L S) n) ⧸
      Subgroup.center (Bar2 (R891X L (R891Z L S) n))) := hQ.2
  have hSperf : Group.IsPerfect (Bar2 (R891X L (R891Z L S) n) ⧸
      Subgroup.center (Bar2 (R891X L (R891Z L S) n))) := k891hcomple_isPerfect_of_simple hnc
  have hSnt : Nontrivial (Bar2 (R891X L (R891Z L S) n) ⧸
      Subgroup.center (Bar2 (R891X L (R891Z L S) n))) := by
    obtain ⟨a, b, hab⟩ := hnc
    exact ⟨a, 1, fun ha => hab (by rw [ha, one_mul, mul_one])⟩
  have hker_le : φ.ker ≤ CFSG.pCore 2 ↥(R891Img (R891H L S) (R891Z L S) (R891X L (R891Z L S) n)) :=
    CFSG.LieType.BorelTits.le_pCore 2 (inferInstance : φ.ker.Normal) hφker
  have hcore_le : CFSG.pCore 2 ↥(R891Img (R891H L S) (R891Z L S) (R891X L (R891Z L S) n)) ≤ φ.ker := by
    rw [← Subgroup.map_eq_bot_iff (H := CFSG.pCore 2 ↥(R891Img (R891H L S) (R891Z L S) (R891X L (R891Z L S) n))) (f := φ)]
    have : ((CFSG.pCore 2 ↥(R891Img (R891H L S) (R891Z L S) (R891X L (R891Z L S) n))).map φ).Normal :=
      (inferInstance : (CFSG.pCore 2 ↥(R891Img (R891H L S) (R891Z L S) (R891X L (R891Z L S) n))).Normal).map φ hφsurj
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((CFSG.pCore 2 ↥(R891Img (R891H L S) (R891Z L S) (R891X L (R891Z L S) n))).map φ) with h | h
    · exact h
    · exfalso
      have hsurj : Function.Surjective (φ.comp (CFSG.pCore 2 ↥(R891Img (R891H L S) (R891Z L S) (R891X L (R891Z L S) n))).subtype) := by
        intro q
        obtain ⟨x, rfl⟩ := hφsurj q
        have hx : φ x ∈ (CFSG.pCore 2 ↥(R891Img (R891H L S) (R891Z L S) (R891X L (R891Z L S) n))).map φ := by rw [h]; exact Subgroup.mem_top _
        obtain ⟨o, ho, hox⟩ := Subgroup.mem_map.mp hx
        exact ⟨⟨o, ho⟩, hox⟩
      have : Group.IsNilpotent ↥(CFSG.pCore 2 ↥(R891Img (R891H L S) (R891Z L S) (R891X L (R891Z L S) n))) :=
        (CFSG.pCore_isPGroup (p := 2)).isNilpotent
      have hsolv : Group.IsSolvable (Bar2 (R891X L (R891Z L S) n) ⧸
          Subgroup.center (Bar2 (R891X L (R891Z L S) n))) :=
        Group.isSolvable_of_surjective (f := φ.comp (CFSG.pCore 2 ↥(R891Img (R891H L S) (R891Z L S) (R891X L (R891Z L S) n))).subtype) hsurj
      exact Group.IsPerfect.not_isSolvable _ hsolv
  have hker_eq : φ.ker = CFSG.pCore 2 ↥(R891Img (R891H L S) (R891Z L S) (R891X L (R891Z L S) n)) := le_antisymm hker_le hcore_le
  have : IsSimpleGroup (↥(R891Img (R891H L S) (R891Z L S) (R891X L (R891Z L S) n)) ⧸ φ.ker) :=
    MulEquiv.isSimpleGroup (QuotientGroup.quotientKerEquivOfSurjective φ hφsurj)
  exact MulEquiv.isSimpleGroup (QuotientGroup.quotientMulEquivOfEq hker_eq).symm

private theorem k891hcomple_Xstar_O2_card {G : Type} [Group G] [Finite G] (D : Data G)
    (L S R A : Subgroup G) (n : ℕ) (hn : 2 ≤ n) (hst : R891State D L S R A n) :
    120 < Nat.card (↥(R891Img (R891H L S) (R891Z L S) (R891X L (R891Z L S) n)) ⧸
      CFSG.pCore 2 ↥(R891Img (R891H L S) (R891Z L S) (R891X L (R891Z L S) n))) := by
  classical
  obtain ⟨φ, hφsurj, hφker⟩ := k891hcomple_phi D L S R A n hn hst
  have hQ := k891hcomple_Bar2_quasisimple D L S R A n hn hst
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnc : ∃ a b : (Bar2 (R891X L (R891Z L S) n) ⧸
      Subgroup.center (Bar2 (R891X L (R891Z L S) n))), a * b ≠ b * a :=
    CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hQ
  have hSsimple : IsSimpleGroup (Bar2 (R891X L (R891Z L S) n) ⧸
      Subgroup.center (Bar2 (R891X L (R891Z L S) n))) := hQ.2
  have hSperf : Group.IsPerfect (Bar2 (R891X L (R891Z L S) n) ⧸
      Subgroup.center (Bar2 (R891X L (R891Z L S) n))) := k891hcomple_isPerfect_of_simple hnc
  have hSnt : Nontrivial (Bar2 (R891X L (R891Z L S) n) ⧸
      Subgroup.center (Bar2 (R891X L (R891Z L S) n))) := by
    obtain ⟨a, b, hab⟩ := hnc
    exact ⟨a, 1, fun ha => hab (by rw [ha, one_mul, mul_one])⟩
  have hker_le : φ.ker ≤ CFSG.pCore 2 ↥(R891Img (R891H L S) (R891Z L S) (R891X L (R891Z L S) n)) :=
    CFSG.LieType.BorelTits.le_pCore 2 (inferInstance : φ.ker.Normal) hφker
  have hcore_le : CFSG.pCore 2 ↥(R891Img (R891H L S) (R891Z L S) (R891X L (R891Z L S) n)) ≤ φ.ker := by
    rw [← Subgroup.map_eq_bot_iff (H := CFSG.pCore 2 ↥(R891Img (R891H L S) (R891Z L S) (R891X L (R891Z L S) n))) (f := φ)]
    have : ((CFSG.pCore 2 ↥(R891Img (R891H L S) (R891Z L S) (R891X L (R891Z L S) n))).map φ).Normal :=
      (inferInstance : (CFSG.pCore 2 ↥(R891Img (R891H L S) (R891Z L S) (R891X L (R891Z L S) n))).Normal).map φ hφsurj
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((CFSG.pCore 2 ↥(R891Img (R891H L S) (R891Z L S) (R891X L (R891Z L S) n))).map φ) with h | h
    · exact h
    · exfalso
      have hsurj : Function.Surjective (φ.comp (CFSG.pCore 2 ↥(R891Img (R891H L S) (R891Z L S) (R891X L (R891Z L S) n))).subtype) := by
        intro q
        obtain ⟨x, rfl⟩ := hφsurj q
        have hx : φ x ∈ (CFSG.pCore 2 ↥(R891Img (R891H L S) (R891Z L S) (R891X L (R891Z L S) n))).map φ := by rw [h]; exact Subgroup.mem_top _
        obtain ⟨o, ho, hox⟩ := Subgroup.mem_map.mp hx
        exact ⟨⟨o, ho⟩, hox⟩
      have : Group.IsNilpotent ↥(CFSG.pCore 2 ↥(R891Img (R891H L S) (R891Z L S) (R891X L (R891Z L S) n))) :=
        (CFSG.pCore_isPGroup (p := 2)).isNilpotent
      have hsolv : Group.IsSolvable (Bar2 (R891X L (R891Z L S) n) ⧸
          Subgroup.center (Bar2 (R891X L (R891Z L S) n))) :=
        Group.isSolvable_of_surjective (f := φ.comp (CFSG.pCore 2 ↥(R891Img (R891H L S) (R891Z L S) (R891X L (R891Z L S) n))).subtype) hsurj
      exact Group.IsPerfect.not_isSolvable _ hsolv
  have hker_eq : φ.ker = CFSG.pCore 2 ↥(R891Img (R891H L S) (R891Z L S) (R891X L (R891Z L S) n)) :=
    le_antisymm hker_le hcore_le
  have hSbig : 3600 < Nat.card (Bar2 (R891X L (R891Z L S) n) ⧸
      Subgroup.center (Bar2 (R891X L (R891Z L S) n))) := by
    have hx := hst.ctx.xShape.xShape
    unfold R891SL3Two at hx
    rcases hx with ⟨hn1, -⟩ | ⟨-, -, htc⟩ | ⟨-, -, htc⟩
    · omega
    · exact CFSG.Blueprint.LieModel.three_thousand_six_hundred_lt_card_psl3 htc.2.2
        (by have h2 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
            norm_num at h2; omega)
    · exact CFSG.Blueprint.LieModel.three_thousand_six_hundred_lt_card_psu3 htc.2.2
        (by have h2 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
            norm_num at h2; omega)
  have hiso : (↥(R891Img (R891H L S) (R891Z L S) (R891X L (R891Z L S) n)) ⧸
      CFSG.pCore 2 ↥(R891Img (R891H L S) (R891Z L S) (R891X L (R891Z L S) n))) ≃*
      (Bar2 (R891X L (R891Z L S) n) ⧸ Subgroup.center (Bar2 (R891X L (R891Z L S) n))) :=
    (QuotientGroup.quotientMulEquivOfEq hker_eq).symm.trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφsurj)
  rw [Nat.card_congr hiso.toEquiv]
  omega

private theorem k891hcomple_inf_ker_le_Z {G : Type} [Group G] [Finite G] (D : Data G)
    (L S R A : Subgroup G) (n : ℕ) (hst : R891State D L S R A n) :
    R ⊓ (R891Ker (R891H L S) (R891Z L S)).map (R891H L S).subtype ≤ R891Z L S := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZH : R891Z L S ≤ R891H L S := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_iff.mp hz.2 y hy.1
  have hZs_center : (R891Z L S).subgroupOf (R891H L S) ≤ Subgroup.center ↥(R891H L S) := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro h
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp h.2 z (Subgroup.mem_subgroupOf.mp hz)).symm
  have hZsN : ((R891Z L S).subgroupOf (R891H L S)).Normal := Subgroup.normal_of_le_center hZs_center
  have hker : R891Ker (R891H L S) (R891Z L S) =
      CFSG.pPrimeCore 3 ↥(R891H L S) ⊔ (R891Z L S).subgroupOf (R891H L S) := by
    unfold R891Ker
    rw [normalClosure_union, normalClosure_eq_self, normalClosure_eq_self]
  have hdisj : Disjoint R ((CFSG.pPrimeCore 3 ↥(R891H L S)).map (R891H L S).subtype) := by
    refine Subgroup.disjoint_of_coprime_natCard (H := R)
      (K := (CFSG.pPrimeCore 3 ↥(R891H L S)).map (R891H L S).subtype) ?_
    rw [Subgroup.card_map_of_injective (R891H L S).subtype_injective,
      show Nat.card R = 3 ^ (1 + 2 * 1) from hst.ctx.xShape.rExtra.1]
    exact (CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥(R891H L S))).pow_left (1 + 2 * 1)
  intro x hx
  obtain ⟨hxR, hxK⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨xH, hxH, rfl⟩ := Subgroup.mem_map.mp hxK
  have hxH' : xH ∈ CFSG.pPrimeCore 3 ↥(R891H L S) ⊔ (R891Z L S).subgroupOf (R891H L S) := by
    rw [← hker]; exact hxH
  obtain ⟨v, hv, z, hz, hvz⟩ := Subgroup.mem_sup_of_normal_left.mp hxH'
  have hval : (v : G) * (z : G) = (xH : G) := congrArg Subtype.val hvz
  have hvR : (v : G) ∈ R := by
    have hzR : (z : G) ∈ R := hst.ctx.xShape.zLe (Subgroup.mem_subgroupOf.mp hz)
    have h : (v : G) = (xH : G) * (z : G)⁻¹ := by
      rw [← hval, mul_assoc, mul_inv_cancel, mul_one]
    rw [h]; exact R.mul_mem hxR (R.inv_mem hzR)
  have hv1 : v = 1 := by
    have hmem : (v : G) ∈ R ⊓ (CFSG.pPrimeCore 3 ↥(R891H L S)).map (R891H L S).subtype :=
      ⟨hvR, Subgroup.mem_map_of_mem _ hv⟩
    rw [disjoint_iff.mp hdisj] at hmem
    exact Subtype.ext (Subgroup.mem_bot.mp hmem)
  have hxz : (xH : G) = (z : G) := by
    rw [hv1] at hval
    simpa using hval.symm
  show (xH : G) ∈ R891Z L S
  rw [hxz]
  exact Subgroup.mem_subgroupOf.mp hz

private theorem k891hcomple_three_dvd_Xstar {G : Type} [Group G] [Finite G] (D : Data G)
    (L S R A : Subgroup G) (n : ℕ) (hn : 2 ≤ n) (hst : R891State D L S R A n) :
    3 ∣ Nat.card (R891Img (R891H L S) (R891Z L S) (R891X L (R891Z L S) n)) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hXH : R891X L (R891Z L S) n ≤ R891H L S := k891hcomple_X_le_H D L S R A n hn hst
  have hAcard : Nat.card A = 3 := hst.ctx.classes.aOrder
  obtain ⟨a, haA, ha1⟩ : ∃ a ∈ A, a ≠ 1 := by
    by_contra h; push Not at h
    have hAbot : A = ⊥ := (Subgroup.eq_bot_iff_forall A).mpr h
    rw [hAbot] at hAcard
    simp at hAcard
  have hordA : orderOf (⟨a, haA⟩ : ↥A) = 3 := by
    have hdvd : orderOf (⟨a, haA⟩ : ↥A) ∣ 3 := by
      rw [← hAcard]; exact orderOf_dvd_natCard _
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) (fun he => ha1 (congrArg Subtype.val he))
    · exact h
  have hord : orderOf a = 3 := by
    rw [← Subgroup.orderOf_mk a haA]; exact hordA
  have haX : a ∈ R891X L (R891Z L S) n := (hst.ctx.aLeR.trans hst.ctx.xShape.rLe) haA
  have haKer : a ∉ (R891Ker (R891H L S) (R891Z L S)).map (R891H L S).subtype := by
    intro hmem
    have haZ : a ∈ R891Z L S :=
      k891hcomple_inf_ker_le_Z D L S R A n hst ⟨hst.ctx.aLeR haA, hmem⟩
    have hAeqZ : A = R891Z L S := by
      have h1 : Subgroup.zpowers a = A := by
        apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr haA)
        rw [Nat.card_zpowers, hord, hAcard]
      have h2 : Subgroup.zpowers a = R891Z L S := by
        apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr haZ)
        rw [Nat.card_zpowers, hord, hst.basic.zOrder]
      rw [← h1, h2]
    exact hst.ctx.classes.notConj 1 (by simp) (by
      have h1 : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
        ext y; simp
      rw [h1, Subgroup.map_id, hAeqZ])
  have ha3 : (⟨a, haX⟩ : ↥(R891X L (R891Z L S) n)) ^ 3 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow]
    have := pow_orderOf_eq_one a
    rwa [hord] at this
  have ha3H : (Subgroup.inclusion hXH ⟨a, haX⟩ : ↥(R891H L S)) ^ 3 = 1 := by
    rw [← MonoidHom.map_pow, ha3, map_one]
  let g : ↥(R891Img (R891H L S) (R891Z L S) (R891X L (R891Z L S) n)) :=
    ⟨(QuotientGroup.mk' (R891Ker (R891H L S) (R891Z L S)))
        (Subgroup.inclusion hXH ⟨a, haX⟩),
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr haX)⟩
  have hfa : g ≠ 1 := by
    intro h1
    apply haKer
    exact Subgroup.mem_map_of_mem _ ((QuotientGroup.eq_one_iff _).mp (Subtype.ext_iff.mp h1))
  have hpow : g ^ 3 = 1 := by
    apply Subtype.ext
    change ((QuotientGroup.mk' (R891Ker (R891H L S) (R891Z L S)))
      (Subgroup.inclusion hXH ⟨a, haX⟩)) ^ 3 = 1
    rw [← MonoidHom.map_pow, ha3H, map_one]
  have hof : orderOf g = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hpow) with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hfa
    · exact h
  have hdvd := orderOf_dvd_natCard g
  rwa [hof] at hdvd

private theorem k891hcomple_Xstar_le_of_sup_O2_eq_top {G : Type} [Group G] [Finite G] (D : Data G)
    (L S R A : Subgroup G) (n : ℕ) (hn : 2 ≤ n) (hst : R891State D L S R A n)
    (Ys : Subgroup (R891Star (R891H L S) (R891Z L S)))
    (hXsN : R891Img (R891H L S) (R891Z L S) (R891X L (R891Z L S) n) ≤
      Subgroup.normalizer (Ys : Set (R891Star (R891H L S) (R891Z L S))))
    (htop : (R891Img (R891H L S) (R891Z L S) (R891X L (R891Z L S) n) ⊓ Ys).subgroupOf
        (R891Img (R891H L S) (R891Z L S) (R891X L (R891Z L S) n)) ⊔
      CFSG.pCore 2 ↥(R891Img (R891H L S) (R891Z L S) (R891X L (R891Z L S) n)) = ⊤) :
    R891Img (R891H L S) (R891Z L S) (R891X L (R891Z L S) n) ≤ Ys := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Xstar : Subgroup (R891Star (R891H L S) (R891Z L S)) :=
    R891Img (R891H L S) (R891Z L S) (R891X L (R891Z L S) n)
  let N : Subgroup ↥Xstar := (Xstar ⊓ Ys).subgroupOf Xstar
  have hNnorm : N.Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr ?_
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      exact ⟨Xstar.mul_mem (Xstar.mul_mem hx hy.1) (Xstar.inv_mem hx),
        (Subgroup.mem_normalizer_iff.mp (hXsN hx) y).mp hy.2⟩
    · intro hy
      have hyY : y ∈ Ys := (Subgroup.mem_normalizer_iff.mp (hXsN hx) y).mpr hy.2
      have hyX : y ∈ Xstar := by
        have h : x⁻¹ * (x * y * x⁻¹) * x = y := by group
        rw [← h]
        exact Xstar.mul_mem (Xstar.mul_mem (Xstar.inv_mem hx) hy.1) hx
      exact ⟨hyX, hyY⟩
  have hsurj : Function.Surjective ((QuotientGroup.mk' N).comp (CFSG.pCore 2 ↥Xstar).subtype) := by
    intro q
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective N q
    have hz : z ∈ N ⊔ CFSG.pCore 2 ↥Xstar := by
      change z ∈ (Xstar ⊓ Ys).subgroupOf Xstar ⊔ CFSG.pCore 2 ↥Xstar
      rw [show (Xstar ⊓ Ys).subgroupOf Xstar ⊔ CFSG.pCore 2 ↥Xstar = ⊤ from htop]
      exact Subgroup.mem_top z
    obtain ⟨n', hn', o, ho, hno⟩ := Subgroup.mem_sup_of_normal_left.mp hz
    refine ⟨⟨o, ho⟩, ?_⟩
    rw [MonoidHom.comp_apply, Subgroup.coe_subtype]
    have hψn : (QuotientGroup.mk' N) n' = 1 := (QuotientGroup.eq_one_iff n').mpr hn'
    have : (QuotientGroup.mk' N) z = (QuotientGroup.mk' N) o := by
      rw [← hno, map_mul, hψn, one_mul]
    exact this.symm
  have : Group.IsNilpotent ↥(CFSG.pCore 2 ↥Xstar) := (CFSG.pCore_isPGroup (p := 2)).isNilpotent
  have hsolv : Group.IsSolvable (↥Xstar ⧸ N) :=
    Group.isSolvable_of_surjective (f := (QuotientGroup.mk' N).comp (CFSG.pCore 2 ↥Xstar).subtype) hsurj
  have : Group.IsPerfect (↥Xstar ⧸ N) :=
    (show Group.IsPerfect ↥Xstar from ⟨k891hcomple_Xstar_perfect D L S R A n hn hst⟩).ofSurjective
      (QuotientGroup.mk'_surjective N)
  have hsub : Subsingleton (↥Xstar ⧸ N) := by
    by_contra hnt
    have : Nontrivial (↥Xstar ⧸ N) := not_subsingleton_iff_nontrivial.mp hnt
    exact Group.IsPerfect.not_isSolvable _ hsolv
  intro x hx
  change x ∈ Xstar at hx
  have hxN : (⟨x, hx⟩ : ↥Xstar) ∈ N := by
    rw [← QuotientGroup.eq_one_iff]
    exact Subsingleton.elim _ _
  exact (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hxN)).2

private theorem k891hcomple_action_ker_le_O2 {E : Type} [Group E] [Finite E]
    {X K : Subgroup E} (hXperf : commutator X = ⊤)
    (hXO2 : IsSimpleGroup (↥X ⧸ CFSG.pCore 2 ↥X))
    (hXK : X ≤ Subgroup.normalizer (K : Set E))
    (hc : ¬ X ≤ Subgroup.centralizer (K : Set E)) :
    (K.normalizerMonoidHom.comp (Subgroup.inclusion hXK)).ker ≤ CFSG.pCore 2 ↥X := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let action : X →* MulAut ↥K := K.normalizerMonoidHom.comp (Subgroup.inclusion hXK)
  have hactker : action.ker = (Subgroup.centralizer (K : Set E)).subgroupOf X := by
    change (K.normalizerMonoidHom.comp (Subgroup.inclusion hXK)).ker = _
    rw [← MonoidHom.comap_ker, K.normalizerMonoidHom_ker]
    exact Subgroup.comap_inclusion_subgroupOf hXK (Subgroup.centralizer (K : Set E))
  rw [hactker]
  let C : Subgroup ↥X := (Subgroup.centralizer (K : Set E)).subgroupOf X
  have hCnorm : C.Normal := by rw [show C = action.ker from hactker.symm]; infer_instance
  by_contra hle
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (C.map (QuotientGroup.mk' (CFSG.pCore 2 ↥X))) with h | h
  · rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
    exact hle h
  · exfalso
    have hsup : C ⊔ CFSG.pCore 2 ↥X = ⊤ := by
      rw [eq_top_iff]
      intro z _
      have hz : QuotientGroup.mk' (CFSG.pCore 2 ↥X) z ∈
          C.map (QuotientGroup.mk' (CFSG.pCore 2 ↥X)) := by rw [h]; exact Subgroup.mem_top _
      obtain ⟨c, hc', hcz⟩ := Subgroup.mem_map.mp hz
      have hker : z * c⁻¹ ∈ CFSG.pCore 2 ↥X := by
        apply (QuotientGroup.eq_one_iff (z * c⁻¹)).mp
        change (QuotientGroup.mk' (CFSG.pCore 2 ↥X)) (z * c⁻¹) = 1
        rw [map_mul, map_inv, hcz, mul_inv_cancel]
      have hconj : c⁻¹ * z ∈ CFSG.pCore 2 ↥X := by
        have hc2 := (inferInstance : (CFSG.pCore 2 ↥X).Normal).conj_mem (z * c⁻¹) hker c⁻¹
        rwa [show c⁻¹ * (z * c⁻¹) * (c⁻¹)⁻¹ = c⁻¹ * z by group] at hc2
      have hz' : z = c * (c⁻¹ * z) := by group
      rw [hz']
      exact (C ⊔ CFSG.pCore 2 ↥X).mul_mem (Subgroup.mem_sup_left hc') (Subgroup.mem_sup_right hconj)
    have hsurj : Function.Surjective ((QuotientGroup.mk' C).comp (CFSG.pCore 2 ↥X).subtype) := by
      intro q
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective C q
      have hx : x ∈ C ⊔ CFSG.pCore 2 ↥X := by rw [hsup]; exact Subgroup.mem_top x
      obtain ⟨n', hn', o, ho, hno⟩ := Subgroup.mem_sup_of_normal_left.mp hx
      refine ⟨⟨o, ho⟩, ?_⟩
      rw [MonoidHom.comp_apply, Subgroup.coe_subtype]
      have hψn : (QuotientGroup.mk' C) n' = 1 := (QuotientGroup.eq_one_iff n').mpr hn'
      have : (QuotientGroup.mk' C) x = (QuotientGroup.mk' C) o := by
        rw [← hno, map_mul, hψn, one_mul]
      exact this.symm
    have : Group.IsNilpotent ↥(CFSG.pCore 2 ↥X) := (CFSG.pCore_isPGroup (p := 2)).isNilpotent
    have hsolv : Group.IsSolvable (↥X ⧸ C) :=
      Group.isSolvable_of_surjective (f := (QuotientGroup.mk' C).comp (CFSG.pCore 2 ↥X).subtype) hsurj
    have : Group.IsPerfect (↥X ⧸ C) :=
      (show Group.IsPerfect ↥X from ⟨hXperf⟩).ofSurjective (QuotientGroup.mk'_surjective C)
    have hsub : Subsingleton (↥X ⧸ C) := by
      by_contra hnt
      have : Nontrivial (↥X ⧸ C) := not_subsingleton_iff_nontrivial.mp hnt
      exact Group.IsPerfect.not_isSolvable _ hsolv
    apply hc
    intro x hx
    have : (⟨x, hx⟩ : ↥X) ∈ C := by
      rw [← QuotientGroup.eq_one_iff]
      exact Subsingleton.elim _ _
    exact Subgroup.mem_subgroupOf.mp this

private theorem k891hcomple_conj_commutator_action {E : Type} [Group E]
    (X K : Subgroup E) (hXK : X ≤ Subgroup.normalizer (K : Set E))
    (s : ↥K) (x : ↥X) (hcommX : ⁅(s : E), (x : E)⁆ ∈ X) :
    ⁅MulAut.conj s, (K.normalizerMonoidHom.comp (Subgroup.inclusion hXK)) x⁆ =
      (K.normalizerMonoidHom.comp (Subgroup.inclusion hXK)) ⟨⁅(s : E), (x : E)⁆, hcommX⟩ := by
  have hconj : MulAut.conj s =
      K.normalizerMonoidHom ⟨(s : E), Subgroup.le_normalizer s.2⟩ := by
    ext k
    rfl
  rw [hconj]
  rw [show (K.normalizerMonoidHom.comp (Subgroup.inclusion hXK)) x =
    K.normalizerMonoidHom ⟨(x : E), hXK x.2⟩ from rfl]
  rw [show (K.normalizerMonoidHom.comp (Subgroup.inclusion hXK)) ⟨⁅(s : E), (x : E)⁆, hcommX⟩ =
    K.normalizerMonoidHom ⟨⁅(s : E), (x : E)⁆, hXK hcommX⟩ from rfl]
  rw [← map_commutatorElement]
  rfl

private theorem k891hcomple_mem_pCore_of_action_mem {E : Type} [Group E]
    (X K : Subgroup E) (hXK : X ≤ Subgroup.normalizer (K : Set E))
    (hker_le : (K.normalizerMonoidHom.comp (Subgroup.inclusion hXK)).ker ≤ CFSG.pCore 2 ↥X)
    (w : ↥X)
    (hw : (K.normalizerMonoidHom.comp (Subgroup.inclusion hXK)) w ∈
      (CFSG.pCore 2 ↥X).map (K.normalizerMonoidHom.comp (Subgroup.inclusion hXK))) :
    w ∈ CFSG.pCore 2 ↥X := by
  obtain ⟨u, hu, huw⟩ := Subgroup.mem_map.mp hw
  have hker : u * w⁻¹ ∈ (K.normalizerMonoidHom.comp (Subgroup.inclusion hXK)).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, huw, mul_inv_cancel]
  have h1 : u * w⁻¹ ∈ CFSG.pCore 2 ↥X := hker_le hker
  have h2 : w * u⁻¹ ∈ CFSG.pCore 2 ↥X := by
    simpa using (CFSG.pCore 2 ↥X).inv_mem h1
  have h3 : w = (w * u⁻¹) * u := by group
  rw [h3]
  exact (CFSG.pCore 2 ↥X).mul_mem h2 hu

private theorem k891hcomple_mem_O2_of_commutator_le {E : Type} [Group E] [Finite E]
    {X K : Subgroup E} (hXperf : commutator X = ⊤)
    (hXO2 : IsSimpleGroup (↥X ⧸ CFSG.pCore 2 ↥X))
    (hXK : X ≤ Subgroup.normalizer (K : Set E))
    (hker_le : (K.normalizerMonoidHom.comp (Subgroup.inclusion hXK)).ker ≤ CFSG.pCore 2 ↥X)
    {t : MulAut ↥K}
    (htA : t ∈ (K.normalizerMonoidHom.comp (Subgroup.inclusion hXK)).range)
    (ht : ∀ y ∈ (K.normalizerMonoidHom.comp (Subgroup.inclusion hXK)).range,
      ⁅t, y⁆ ∈ (CFSG.pCore 2 ↥X).map (K.normalizerMonoidHom.comp (Subgroup.inclusion hXK))) :
    t ∈ (CFSG.pCore 2 ↥X).map (K.normalizerMonoidHom.comp (Subgroup.inclusion hXK)) := by
  classical
  obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp htA
  have hx : x ∈ CFSG.pCore 2 ↥X := by
    have hcent : ∀ z : ↥X, ⁅x, z⁆ ∈ CFSG.pCore 2 ↥X := by
      intro z
      have hcommX : ⁅(x : E), (z : E)⁆ ∈ X := by
        rw [commutatorElement_def]
        exact X.mul_mem (X.mul_mem (X.mul_mem x.2 z.2) (X.inv_mem x.2)) (X.inv_mem z.2)
      have h2 : ⁅(K.normalizerMonoidHom.comp (Subgroup.inclusion hXK)) x,
          (K.normalizerMonoidHom.comp (Subgroup.inclusion hXK)) z⁆ =
          (K.normalizerMonoidHom.comp (Subgroup.inclusion hXK)) ⟨⁅(x : E), (z : E)⁆, hcommX⟩ := by
        rw [show (K.normalizerMonoidHom.comp (Subgroup.inclusion hXK)) x =
            K.normalizerMonoidHom ⟨(x : E), hXK x.2⟩ from rfl,
          show (K.normalizerMonoidHom.comp (Subgroup.inclusion hXK)) z =
            K.normalizerMonoidHom ⟨(z : E), hXK z.2⟩ from rfl,
          show (K.normalizerMonoidHom.comp (Subgroup.inclusion hXK)) ⟨⁅(x : E), (z : E)⁆, hcommX⟩ =
            K.normalizerMonoidHom ⟨⁅(x : E), (z : E)⁆, hXK hcommX⟩ from rfl,
          ← map_commutatorElement]
        rfl
      have h1 : (K.normalizerMonoidHom.comp (Subgroup.inclusion hXK)) ⟨⁅(x : E), (z : E)⁆, hcommX⟩ ∈
          (CFSG.pCore 2 ↥X).map (K.normalizerMonoidHom.comp (Subgroup.inclusion hXK)) := by
        rw [← h2]
        exact ht _ (MonoidHom.mem_range.mpr ⟨z, rfl⟩)
      exact k891hcomple_mem_pCore_of_action_mem X K hXK hker_le _ h1
    have hcenter : QuotientGroup.mk' (CFSG.pCore 2 ↥X) x ∈
        Subgroup.center (↥X ⧸ CFSG.pCore 2 ↥X) := by
      rw [Subgroup.mem_center_iff]
      intro w
      obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥X) w
      have h1 : ⁅QuotientGroup.mk' (CFSG.pCore 2 ↥X) x,
          QuotientGroup.mk' (CFSG.pCore 2 ↥X) z⁆ = 1 := by
        rw [← map_commutatorElement]
        exact (QuotientGroup.eq_one_iff ⁅x, z⁆).mpr (hcent z)
      exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
    have hcenter_bot : Subgroup.center (↥X ⧸ CFSG.pCore 2 ↥X) = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        (Subgroup.center (↥X ⧸ CFSG.pCore 2 ↥X)) with h | h
      · exact h
      · have hbot : commutator (↥X ⧸ CFSG.pCore 2 ↥X) = ⊥ := by
          rw [_root_.commutator_def]
          exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
            (fun a _ b _ => Subgroup.mem_center_iff.mp (h.symm ▸ Subgroup.mem_top a) b)
        have hperf : commutator (↥X ⧸ CFSG.pCore 2 ↥X) = ⊤ :=
          ((show Group.IsPerfect ↥X from ⟨hXperf⟩).ofSurjective
            (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥X))).commutator_eq_top
        rw [hperf] at hbot
        exact h.trans hbot
    rw [hcenter_bot] at hcenter
    exact (QuotientGroup.eq_one_iff x).mp (Subgroup.mem_bot.mp hcenter)
  exact Subgroup.mem_map_of_mem _ hx

private theorem k891hcomple_three_dvd_action_range {E : Type} [Group E] [Finite E]
    {X K : Subgroup E} (hXK : X ≤ Subgroup.normalizer (K : Set E))
    (hker_le : (K.normalizerMonoidHom.comp (Subgroup.inclusion hXK)).ker ≤ CFSG.pCore 2 ↥X)
    (h3X : 3 ∣ Nat.card ↥X) :
    3 ∣ Nat.card ↥((K.normalizerMonoidHom.comp (Subgroup.inclusion hXK)).range) := by
  classical
  let action : ↥X →* MulAut ↥K := K.normalizerMonoidHom.comp (Subgroup.inclusion hXK)
  have hcard : Nat.card ↥X = Nat.card ↥action.range * Nat.card ↥action.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup action.ker]
    congr 1
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange action).toEquiv
  have hker2 : IsPGroup 2 ↥action.ker :=
    (CFSG.pCore_isPGroup (p := 2)).to_le hker_le
  obtain ⟨k, hk⟩ := hker2.exists_card_eq
  have hcop : Nat.Coprime 3 (Nat.card ↥action.ker) := by
    rw [hk]
    exact (by norm_num : Nat.Coprime 3 2).pow_right k
  rw [hcard] at h3X
  exact hcop.dvd_of_dvd_mul_right h3X

private theorem k891hcomple_step6_o2' {E : Type} [Group E] [Finite E]
    (hKSch : CFSG.LocalAnalysis.RankThreeUC.S15.KSch)
    (hE : CFSG.Open.IsKGroup E)
    {X K S : Subgroup E}
    (hXperf : commutator X = ⊤)
    (hXO2 : IsSimpleGroup (↥X ⧸ CFSG.pCore 2 ↥X))
    (hXK : X ≤ Subgroup.normalizer (K : Set E))
    (hK : IsComponentOf K ⊤)
    (hSyl : IsSylowOf 3 S K)
    (hSX : ⁅X, S⁆ ≤ (CFSG.pCore 2 ↥X).map X.subtype)
    (h3X : 3 ∣ Nat.card X)
    (hc : ¬ X ≤ Subgroup.centralizer (K : Set E)) : False := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Group.IsPerfect X := ⟨hXperf⟩
  have hKq : CFSG.Open.IsQuasisimple K := hK.2.2
  have hKq' : CFSG.IsQuasisimple K :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native K).1 hKq
  have hnonab : ∃ a b : K ⧸ Subgroup.center K, a * b ≠ b * a := hKq'.2.2
  have : IsSimpleGroup (K ⧸ Subgroup.center K) := hKq.2
  have hSS : CFSG.ComponentClassification.LBalance.SchreierSections E :=
    hKSch.schreierSections hE
  have hOutSolQ : Group.IsSolvable (Outer (K ⧸ Subgroup.center K)) :=
    hSS.outer_solvable K hnonab (QuotientGroup.mk' (Subgroup.center K))
      (QuotientGroup.mk'_surjective _)
  have : Group.IsPerfect ↥K := ⟨hK.2.2.1⟩
  have : Group.IsSolvable (Outer (K ⧸ Subgroup.center K)) := hOutSolQ
  have hOutSol : Group.IsSolvable (Outer ↥K) := solvable_of_centerQuotient ↥K
  have : Group.IsSolvable (Outer ↥K) := hOutSol
  have hOut : ∀ P : Subgroup (MulAut ↥K), Group.IsPerfect P →
      P ≤ (MulAut.conj : ↥K →* MulAut ↥K).range := by
    intro P hP
    have : Group.IsPerfect P := hP
    intro p hp
    obtain ⟨element, heq⟩ :=
      perfect_action_inner (A := P) (G := ↥K) P.subtype ⟨p, hp⟩
    exact ⟨element, by simpa using heq.symm⟩
  have hXKC : X ≤ K ⊔ Subgroup.centralizer (K : Set E) :=
    CFSG.GroupTheory.le_sup_centralizer_of_perfect_of_perfect_aut_inner
      (K := X) (C := K) hXK hOut
  let action : X →* MulAut ↥K := K.normalizerMonoidHom.comp (Subgroup.inclusion hXK)
  have hact : ∀ (x : ↥X) (k : ↥K),
      ((action x) k : E) = (x : E) * (k : E) * (x : E)⁻¹ := by
    intro x k
    change ((K.normalizerMonoidHom ⟨(x : E), hXK x.2⟩) k : E) = _
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
  have hkconj : ∀ (s : ↥K) (k : ↥K),
      (((MulAut.conj s) k : ↥K) : E) = (s : E) * (k : E) * (s : E)⁻¹ := by
    intro s k
    simp
  have hactker : action.ker = (Subgroup.centralizer (K : Set E)).subgroupOf X := by
    change (K.normalizerMonoidHom.comp (Subgroup.inclusion hXK)).ker = _
    rw [← MonoidHom.comap_ker, K.normalizerMonoidHom_ker]
    exact Subgroup.comap_inclusion_subgroupOf hXK (Subgroup.centralizer (K : Set E))
  have hAperf : Group.IsPerfect ↥action.range := Group.IsPerfect.range action
  obtain ⟨S₀, hS₀⟩ := hSyl.exists_sylow_eq_subgroupOf
  let I : Subgroup (MulAut ↥K) := (MulAut.conj : ↥K →* MulAut ↥K).range
  have hAinn : action.range ≤ I := hOut action.range hAperf
  let SbarSyl : Sylow 3 I := S₀.mapSurjective (MulAut.conj.rangeRestrict_surjective)
  have hSbar : (SbarSyl : Subgroup I).map I.subtype =
      (S.subgroupOf K).map (MulAut.conj : ↥K →* MulAut ↥K) := by
    change ((S₀.mapSurjective (MulAut.conj.rangeRestrict_surjective) : Sylow 3 I) :
      Subgroup I).map I.subtype = _
    rw [Sylow.coe_mapSurjective, Subgroup.map_map, hS₀]
    rfl
  have hker_le : action.ker ≤ CFSG.pCore 2 ↥X :=
    k891hcomple_action_ker_le_O2 hXperf hXO2 hXK hc
  have hSNX : S ≤ Subgroup.normalizer (X : Set E) :=
    Subgroup.le_normalizer_iff_commutator_le_right.mpr
      (by rw [Subgroup.commutator_comm]; exact hSX.trans (Subgroup.map_subtype_le _))
  have hSbar3 : IsPGroup 3 ((S.subgroupOf K).map (MulAut.conj : ↥K →* MulAut ↥K)) := by
    rw [← hSbar]
    exact SbarSyl.isPGroup'.map I.subtype
  have hSbar_le_I : (S.subgroupOf K).map (MulAut.conj : ↥K →* MulAut ↥K) ≤ I := by
    rw [← hSbar]
    exact Subgroup.map_subtype_le _
  have hcommSbarA : ⁅(S.subgroupOf K).map (MulAut.conj : ↥K →* MulAut ↥K), action.range⁆ ≤
      (CFSG.pCore 2 ↥X).map action := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hb
    have h1 : ⁅(s : E), (x : E)⁆ ∈ ⁅S, X⁆ :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.mp hs) x.2
    rw [Subgroup.commutator_comm] at h1
    have hcommX : ⁅(s : E), (x : E)⁆ ∈ X := Subgroup.map_subtype_le _ (hSX h1)
    rw [k891hcomple_conj_commutator_action X K hXK s x hcommX]
    refine Subgroup.mem_map_of_mem action ?_
    obtain ⟨u, hu, huv⟩ := Subgroup.mem_map.mp (hSX h1)
    rw [show (⟨⁅(s : E), (x : E)⁆, hcommX⟩ : ↥X) = u from Subtype.ext huv.symm]
    exact hu
  have hSbar_norm : (S.subgroupOf K).map (MulAut.conj : ↥K →* MulAut ↥K) ≤
      Subgroup.normalizer (action.range : Set (MulAut ↥K)) :=
    Subgroup.le_normalizer_iff_commutator_le_right.mpr
      (hcommSbarA.trans (Subgroup.map_le_range (H := CFSG.pCore 2 ↥X) action))
  have hSbar_syl_I : IsSylowOf 3 ((S.subgroupOf K).map (MulAut.conj : ↥K →* MulAut ↥K)) I :=
    ⟨SbarSyl, hSbar⟩
  have hT : IsSylowOf 3 ((S.subgroupOf K).map (MulAut.conj : ↥K →* MulAut ↥K) ⊓ action.range)
      action.range :=
    IsSylowOf.inf_of_le_normalizer
      (IsSylowOf.of_le hSbar_syl_I le_sup_right (sup_le hAinn hSbar_le_I))
      le_sup_left (sup_le (Subgroup.le_normalizer) hSbar_norm)
  have hTle : (S.subgroupOf K).map (MulAut.conj : ↥K →* MulAut ↥K) ⊓ action.range ≤
      (CFSG.pCore 2 ↥X).map action := by
    intro t ht
    exact k891hcomple_mem_O2_of_commutator_le hXperf hXO2 hXK hker_le ht.2
      (fun y hy => (Subgroup.commutator_le.mp hcommSbarA) t ht.1 y hy)
  have h3A : 3 ∣ Nat.card ↥action.range :=
    k891hcomple_three_dvd_action_range hXK hker_le h3X
  obtain ⟨Q, hQ⟩ := hT
  refine Sylow.ne_bot_of_dvd_card Q h3A ?_
  have hQle : (Q : Subgroup ↥action.range).map action.range.subtype ≤
      (CFSG.pCore 2 ↥X).map action := by
    rw [hQ]; exact hTle
  have hdisj : Disjoint ((Q : Subgroup ↥action.range).map action.range.subtype)
      ((CFSG.pCore 2 ↥X).map action) :=
    IsPGroup.disjoint_of_ne 3 2 (by norm_num) _ _
      (Q.isPGroup'.map action.range.subtype) ((CFSG.pCore_isPGroup (p := 2)).map action)
  have hmap : (Q : Subgroup ↥action.range).map action.range.subtype = ⊥ := by
    rw [← inf_of_le_left hQle]
    exact disjoint_iff.mp hdisj
  have h := (Subgroup.map_eq_bot_iff (H := (Q : Subgroup ↥action.range))
    (f := action.range.subtype)).mp hmap
  rw [Subgroup.ker_subtype] at h
  exact le_bot_iff.mp h

theorem s891_h_comp_le
    {G : Type} [Group G] [Finite G] (D : Data G) (L S R A : Subgroup G) (n : ℕ)
    (hn : 2 ≤ n) (hst : R891State D L S R A n) (hnorm : R891Norm895 D L S n)
    (hH3 : CFSG.Open.pRank 3 (R891H L S) ≤ 3) (Ys : Subgroup (R891Star (R891H L S) (R891Z L S))) (hc : IsComponentOf Ys ⊤)
    (h3 : 3 ∣ Nat.card Ys)
    (hnc : ¬ R891Img (R891H L S) (R891Z L S) (R891X L (R891Z L S) n) ≤ centralizer ((Ys : Subgroup (R891Star (R891H L S) (R891Z L S))) : Set (R891Star (R891H L S) (R891Z L S)))) :
    R891Img (R891H L S) (R891Z L S) (R891X L (R891Z L S) n) ≤ Ys := by
  have hKSch := CFSG.LocalAnalysis.RankThreeUC.S15.kSch_of_catalog
    CFSG.AGLEmbedding.kFactCatalogSchreier_holds
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let Xstar : Subgroup (R891Star (R891H L S) (R891Z L S)) :=
    R891Img (R891H L S) (R891Z L S) (R891X L (R891Z L S) n)
  have hrank : CFSG.Open.pRank 3 (⊤ : Subgroup (R891Star (R891H L S) (R891Z L S))) ≤ 5 :=
    k891hcomple_rank_Hstar L S hH3 hst.basic.zOrder
  have hcount := k891hcomple_component_count hrank
  have hstable : ∀ g ∈ Xstar,
      ∀ A ∈ {A : Subgroup (R891Star (R891H L S) (R891Z L S)) |
        IsComponentOf A ⊤ ∧ 3 ∣ Nat.card A},
      A.map (MulAut.conj g).toMonoidHom ∈ {A : Subgroup (R891Star (R891H L S) (R891Z L S)) |
        IsComponentOf A ⊤ ∧ 3 ∣ Nat.card A} := by
    intro g hg A hA
    obtain ⟨hAc, h3A⟩ := hA
    exact ⟨CFSG.CGT.Foote82.BranchAAux.isComponentOf_conj hAc (Subgroup.mem_top g),
      by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]; exact h3A⟩
  have hXsN : Xstar ≤ Subgroup.normalizer (Ys : Set (R891Star (R891H L S) (R891Z L S))) :=
    k891hcomple_perfect_le_normalizer_of_card_le_five'
      (k891hcomple_Xstar_perfect D L S R A n hn hst)
      (k891hcomple_Xstar_O2 D L S R A n hn hst)
      (k891hcomple_Xstar_O2_card D L S R A n hn hst)
      {A : Subgroup (R891Star (R891H L S) (R891Z L S)) | IsComponentOf A ⊤ ∧ 3 ∣ Nat.card A}
      (Set.toFinite _) (by rw [← Nat.card_coe_set_eq]; exact hcount) hstable ⟨hc, h3⟩
  have hR3 : IsPGroup 3 R := IsPGroup.of_card (by rw [hst.ctx.xShape.rExtra.1])
  have hRH : R ≤ R891H L S := by
    intro r hr
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (Subgroup.mem_centralizer_iff.mp hz.2 (r : G)
      (hst.ctx.xShape.rSylow hr)).symm
  obtain ⟨T, hT⟩ := (hR3.comap_subtype (K := R891H L S)).exists_le_sylow
  let P : Subgroup G := (T : Subgroup ↥(R891H L S)).map (R891H L S).subtype
  have hPsyl : IsSylowOf 3 P (R891H L S) := ⟨T, rfl⟩
  have hRP : R ≤ P := by
    intro r hr
    exact ⟨⟨r, hRH hr⟩, hT (Subgroup.mem_subgroupOf.mpr hr), rfl⟩
  have hPM : P ≤ D.M := k891hcomple_sylow_le_M D L S R A n hst hPsyl hRP
  let Pstar : Subgroup (R891Star (R891H L S) (R891Z L S)) :=
    (T : Subgroup ↥(R891H L S)).map (QuotientGroup.mk' (R891Ker (R891H L S) (R891Z L S)))
  have hPstarM : Pstar ≤ R891Img (R891H L S) (R891Z L S) D.M := by
    have hTM : (T : Subgroup ↥(R891H L S)) ≤ D.M.subgroupOf (R891H L S) := by
      intro x hx
      exact hPM (Subgroup.mem_map_of_mem _ hx)
    exact Subgroup.map_mono hTM
  have hPstarN : Pstar ≤ Subgroup.normalizer (Xstar : Set (R891Star (R891H L S) (R891Z L S))) :=
    hPstarM.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hnorm.1).mp hnorm.2)
  let PstarSyl : Sylow 3 (R891Star (R891H L S) (R891Z L S)) :=
    T.mapSurjective (QuotientGroup.mk'_surjective (R891Ker (R891H L S) (R891Z L S)))
  have hPstarSyl_coe : (PstarSyl : Subgroup (R891Star (R891H L S) (R891Z L S))) = Pstar := by
    rw [Sylow.coe_mapSurjective]
  have hPstarSyl : IsSylowOf 3 Pstar (⊤ : Subgroup (R891Star (R891H L S) (R891Z L S))) := by
    let e : R891Star (R891H L S) (R891Z L S) ≃*
        ↥(⊤ : Subgroup (R891Star (R891H L S) (R891Z L S))) := Subgroup.topEquiv.symm
    have he : Function.Surjective e.toMonoidHom := fun y => ⟨e.symm y, e.apply_symm_apply y⟩
    refine ⟨PstarSyl.mapSurjective he, ?_⟩
    rw [Sylow.coe_mapSurjective, Subgroup.map_map]
    have hcomp : ((⊤ : Subgroup (R891Star (R891H L S) (R891Z L S))).subtype).comp e.toMonoidHom =
        MonoidHom.id (R891Star (R891H L S) (R891Z L S)) := by ext x; rfl
    rw [hcomp, hPstarSyl_coe]
    exact Subgroup.map_id Pstar
  have hSylQ : IsSylowOf 3 (Pstar ⊓ Ys) Ys :=
    CFSG.ABGLocalTools.IsSylowOf.inf_of_isSubnormal hPstarSyl hc.2.1
  have hInorm : ((Xstar ⊓ Ys).subgroupOf Xstar).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr ?_
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      exact ⟨Xstar.mul_mem (Xstar.mul_mem hx hy.1) (Xstar.inv_mem hx),
        (Subgroup.mem_normalizer_iff.mp (hXsN hx) y).mp hy.2⟩
    · intro hy
      have hyY : y ∈ Ys := (Subgroup.mem_normalizer_iff.mp (hXsN hx) y).mpr hy.2
      have hyX : y ∈ Xstar := by
        have h : x⁻¹ * (x * y * x⁻¹) * x = y := by group
        rw [← h]
        exact Xstar.mul_mem (Xstar.mul_mem (Xstar.inv_mem hx) hy.1) hx
      exact ⟨hyX, hyY⟩
  have hO2simple : IsSimpleGroup (↥Xstar ⧸ CFSG.pCore 2 ↥Xstar) :=
    k891hcomple_Xstar_O2 D L S R A n hn hst
  have hIbar : (((Xstar ⊓ Ys).subgroupOf Xstar).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥Xstar))).Normal :=
    hInorm.map _ (QuotientGroup.mk'_surjective _)
  have hE : CFSG.Open.IsKGroup (R891Star (R891H L S) (R891Z L S)) := by
    have hsimple : IsSimpleGroup G := D.standing.simple
    have hHne : R891H L S ≠ ⊤ := by
      intro htop
      have hZcG : R891Z L S ≤ Subgroup.center G := by
        intro z hz
        rw [Subgroup.mem_center_iff]
        intro g
        have hgH : g ∈ R891H L S := by rw [htop]; exact Subgroup.mem_top g
        exact (Subgroup.mem_centralizer_iff.mp hgH z hz).symm
      have hcenter : Subgroup.center G = ⊥ := by
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
        · exact h
        · exfalso
          obtain ⟨a, b, hab⟩ := D.standing.nonab
          exact hab ((isMulCommutative_iff.mp (Subgroup.center_eq_top_iff.mp h)) a b)
      have hZbot : R891Z L S = ⊥ := le_bot_iff.mp (hZcG.trans (le_of_eq hcenter))
      have hz3 : Nat.card (R891Z L S) = 3 := hst.basic.zOrder
      rw [hZbot, Subgroup.card_bot] at hz3
      norm_num at hz3
    exact (D.standing.kProper.isKGroup (R891H L S) hHne).quotient
      (R891Ker (R891H L S) (R891Z L S))
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (((Xstar ⊓ Ys).subgroupOf Xstar).map (QuotientGroup.mk' (CFSG.pCore 2 ↥Xstar))) with hbar | hbar
  · exfalso
    have hIle : (Xstar ⊓ Ys).subgroupOf Xstar ≤ CFSG.pCore 2 ↥Xstar := by
      have h := (Subgroup.map_eq_bot_iff (H := (Xstar ⊓ Ys).subgroupOf Xstar)
        (f := QuotientGroup.mk' (CFSG.pCore 2 ↥Xstar))).mp hbar
      rwa [QuotientGroup.ker_mk'] at h
    have hle_gen : Xstar ⊓ Ys ≤ (CFSG.pCore 2 ↥Xstar).map Xstar.subtype := by
      intro x hx
      exact ⟨⟨x, hx.1⟩, hIle (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
    have hSX : ⁅Xstar, Pstar ⊓ Ys⁆ ≤ (CFSG.pCore 2 ↥Xstar).map Xstar.subtype := by
      have h1 : ⁅Xstar, Pstar ⊓ Ys⁆ ≤ Xstar := by
        rw [Subgroup.commutator_comm]
        exact Subgroup.le_normalizer_iff_commutator_le_right.mp (inf_le_left.trans hPstarN)
      have h2 : ⁅Xstar, Pstar ⊓ Ys⁆ ≤ Ys :=
        (Subgroup.commutator_mono le_rfl inf_le_right).trans
          (Subgroup.le_normalizer_iff_commutator_le_right.mp hXsN)
      exact (le_inf h1 h2).trans hle_gen
    exact k891hcomple_step6_o2' hKSch hE
      (k891hcomple_Xstar_perfect D L S R A n hn hst) hO2simple hXsN hc hSylQ hSX
      (k891hcomple_three_dvd_Xstar D L S R A n hn hst) hnc
  · refine k891hcomple_Xstar_le_of_sup_O2_eq_top D L S R A n hn hst Ys hXsN ?_
    rw [eq_top_iff]
    intro z _
    have hz : QuotientGroup.mk' (CFSG.pCore 2 ↥Xstar) z ∈
        ((Xstar ⊓ Ys).subgroupOf Xstar).map (QuotientGroup.mk' (CFSG.pCore 2 ↥Xstar)) := by
      rw [hbar]; exact Subgroup.mem_top _
    obtain ⟨w, hw, hwz⟩ := Subgroup.mem_map.mp hz
    have hker : z * w⁻¹ ∈ CFSG.pCore 2 ↥Xstar := by
      apply (QuotientGroup.eq_one_iff (z * w⁻¹)).mp
      change (QuotientGroup.mk' (CFSG.pCore 2 ↥Xstar)) (z * w⁻¹) = 1
      rw [map_mul, map_inv, hwz, mul_inv_cancel]
    have hconj : w⁻¹ * z ∈ CFSG.pCore 2 ↥Xstar := by
      have := (inferInstance : (CFSG.pCore 2 ↥Xstar).Normal).conj_mem (z * w⁻¹) hker w⁻¹
      rwa [show w⁻¹ * (z * w⁻¹) * (w⁻¹)⁻¹ = w⁻¹ * z by group] at this
    have hz' : z = w * (w⁻¹ * z) := by group
    rw [hz']
    exact ((Xstar ⊓ Ys).subgroupOf Xstar ⊔ CFSG.pCore 2 ↥Xstar).mul_mem
      (Subgroup.mem_sup_left hw) (Subgroup.mem_sup_right hconj)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
