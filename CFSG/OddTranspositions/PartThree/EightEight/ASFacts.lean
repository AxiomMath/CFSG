module

public import CFSG.OddTranspositions.PartThree.EightEight.ASFibres
public import CFSG.Mathlib.GroupTheory.Monolith

import CFSG.OddTranspositions.BlockGraph
import CFSG.OddTranspositions.PartThree.EightEight.KOneRadical
import CFSG.OddTranspositions.PartThree.EightEight.StarBlocks
import CFSG.OddTranspositions.PartThree.EightEight.StarConj
import CFSG.OddTranspositions.PartThree.EightEight.StarOrbit
import CFSG.Timmesfeld.RootSubgroupBasic

public section

namespace CFSG.OddTranspositions.PartThree.EightEight

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.OddTranspositions.QZ

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem StandingAS.rad {hC : HypothesisC D} (h : StandingAS hC) :
    ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥ := h.1

theorem StandingAS.not_isSolvable {hC : HypothesisC D} (h : StandingAS hC) :
    ¬ Group.IsSolvable (Halpha D hC.alpha) := h.2.2.1

theorem StandingAS.faithful {hC : HypothesisC D} (h : StandingAS hC) :
    FaithfulOnBlocks hC.alpha := h.2.2.2.1

theorem StandingAS.not_o4 {hC : HypothesisC D} (h : StandingAS hC) : ¬ O4PairData G D :=
  h.2.2.2.2.1

theorem StandingAS.derivedSeries_ne {hC : HypothesisC D} (h : StandingAS hC) :
    derivedSeries (Halpha D hC.alpha) 1 ≠ derivedSeries (Halpha D hC.alpha) 2 := by
  intro heq
  apply h.2.2.2.2.2.1
  rw [← map_derivedSeries_eq (QuotientGroup.mk'_surjective _) 1,
    ← map_derivedSeries_eq (QuotientGroup.mk'_surjective _) 2, heq]

@[expose] noncomputable def starBar (D ρ : Set G) (p : G) :
    Halpha D ρ ⧸ CFSG.solvableRadical (Halpha D ρ) := by
  classical
  exact if hp : p ∈ Halpha D ρ then QuotientGroup.mk' _ ⟨p, hp⟩ else 1

theorem starBar_of_mem {ρ : Set G} {p : G} (hp : p ∈ Halpha D ρ) :
    starBar D ρ p = QuotientGroup.mk' _ ⟨p, hp⟩ := by
  simp [starBar, hp]

theorem starBar_of_notMem {ρ : Set G} {p : G} (hp : p ∉ Halpha D ρ) : starBar D ρ p = 1 := by
  simp [starBar, hp]

@[simp] theorem starBar_coe {ρ : Set G} (p : Halpha D ρ) :
    starBar D ρ (p : G) = QuotientGroup.mk' _ p :=
  starBar_of_mem p.2

theorem starBar_mul {ρ : Set G} {p q : G} (hp : p ∈ Halpha D ρ) (hq : q ∈ Halpha D ρ) :
    starBar D ρ (p * q) = starBar D ρ p * starBar D ρ q := by
  rw [starBar_of_mem (Subgroup.mul_mem _ hp hq), starBar_of_mem hp, starBar_of_mem hq, ← map_mul]
  rfl

theorem starBar_inv {ρ : Set G} {p : G} (hp : p ∈ Halpha D ρ) :
    starBar D ρ p⁻¹ = (starBar D ρ p)⁻¹ := by
  rw [starBar_of_mem (Subgroup.inv_mem _ hp), starBar_of_mem hp, ← map_inv]
  rfl

theorem starBar_pow {ρ : Set G} {p : G} (hp : p ∈ Halpha D ρ) (k : ℕ) :
    starBar D ρ (p ^ k) = starBar D ρ p ^ k := by
  rw [starBar_of_mem (Subgroup.pow_mem _ hp k), starBar_of_mem hp, ← map_pow]
  rfl

theorem starBar_conj {ρ : Set G} {h p : G} (hh : h ∈ Halpha D ρ) (hp : p ∈ Halpha D ρ) :
    starBar D ρ (h * p * h⁻¹) = starBar D ρ h * starBar D ρ p * (starBar D ρ h)⁻¹ := by
  rw [starBar_mul (Subgroup.mul_mem _ hh hp) (Subgroup.inv_mem _ hh), starBar_mul hh hp,
    starBar_inv hh]

theorem starBar_commute {ρ : Set G} {p q : G} (hp : p ∈ Halpha D ρ) (hq : q ∈ Halpha D ρ)
    (h : Commute p q) : Commute (starBar D ρ p) (starBar D ρ q) := by
  rw [starBar_of_mem hp, starBar_of_mem hq]
  exact (show Commute (⟨p, hp⟩ : Halpha D ρ) ⟨q, hq⟩ from Subtype.ext h.eq).map _

omit [Finite G] in
theorem mem_Halpha_of_mem_DalphaStar {ρ : Set G} {p : G} (hp : p ∈ DalphaStar D ρ) :
    p ∈ Halpha D ρ :=
  Subgroup.subset_closure hp

theorem starBar_mem_imageClass (hC : HypothesisC D) {p : G} (hp : p ∈ DalphaStar D hC.alpha) :
    starBar D hC.alpha p ∈ imageClass hC := by
  rw [starBar_of_mem (mem_Halpha_of_mem_DalphaStar hp)]
  exact ⟨_, hp, rfl⟩

theorem exists_starBar_eq_of_mem_imageClass (hC : HypothesisC D)
    {a : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)} (ha : a ∈ imageClass hC) :
    ∃ p ∈ DalphaStar D hC.alpha, starBar D hC.alpha p = a := by
  obtain ⟨p, hp, rfl⟩ := ha
  exact ⟨p, hp, starBar_coe p⟩

abbrev starSocle (D ρ : Set G) : Subgroup (Halpha D ρ ⧸ CFSG.solvableRadical (Halpha D ρ)) :=
  CFSG.monolith _

theorem StandingAS.starSocle_spec {hC : HypothesisC D} (h : StandingAS hC) :
    Timmesfeld.Bridge.Asc72.IsMinimalNormal (starSocle D hC.alpha) ∧
      (∀ N, Timmesfeld.Bridge.Asc72.IsMinimalNormal N → N = starSocle D hC.alpha) ∧
      IsSimpleGroup (starSocle D hC.alpha) ∧
      Subgroup.centralizer ((starSocle D hC.alpha : Subgroup (Halpha D hC.alpha ⧸
        CFSG.solvableRadical (Halpha D hC.alpha))) : Set (Halpha D hC.alpha ⧸
          CFSG.solvableRadical (Halpha D hC.alpha))) = ⊥ ∧
      2 < (starSocle D hC.alpha).index ∧
      WidthOne (QuotientGroup.mk' (starSocle D hC.alpha) '' imageClass hC) := by
  obtain ⟨M, _, hmin, huniq, hsimp, hcen, hidx, hwid, _⟩ := h.2.2.2.2.2.2
  have heq : M = starSocle D hC.alpha :=
    (CFSG.monolith_eq_of_unique hmin.1 hmin.2.1 fun N hN hN0 hNmin =>
      huniq N ⟨hN, hN0, hNmin⟩).symm
  subst heq
  exact ⟨hmin, huniq, hsimp, hcen, hidx, hwid⟩

theorem StandingAS.mul_self_eq_one_of_mem_imageClass {hC : HypothesisC D} (hSt : StandingAS hC)
    {a : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)} (ha : a ∈ imageClass hC) :
    a * a = 1 := by
  rw [← pow_two, ← orderOf_dvd_iff_pow_eq_one, imageClass_involutions hC hSt.not_isSolvable a ha]

theorem StandingAS.inv_mul_mem_starSocle_of_commute_mk {hC : HypothesisC D}
    (hSt : StandingAS hC)
    {a b : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)} (ha : a ∈ imageClass hC)
    (hb : b ∈ imageClass hC)
    (hab : Commute (QuotientGroup.mk' (starSocle D hC.alpha) a)
      (QuotientGroup.mk' (starSocle D hC.alpha) b)) :
    a⁻¹ * b ∈ starSocle D hC.alpha := by
  obtain ⟨-, -, -, -, -, hW⟩ := hSt.starSocle_spec
  by_contra hne
  set π := QuotientGroup.mk' (starSocle D hC.alpha) with hπ
  have hne' : π a ≠ π b := fun h => hne (QuotientGroup.eq.mp h)
  have hS2 : ∀ s ∈ ({π a, π b} : Set _), s * s = 1 := by
    rintro s (rfl | rfl)
    · rw [← map_mul, hSt.mul_self_eq_one_of_mem_imageClass ha, map_one]
    · rw [← map_mul, hSt.mul_self_eq_one_of_mem_imageClass hb, map_one]
  have hSc : ({π a, π b} : Set _).Pairwise Commute := by
    rintro s (rfl | rfl) t (rfl | rfl) -
    · exact Commute.refl _
    · exact hab
    · exact hab.symm
    · exact Commute.refl _
  have hP : IsPGroup 2 (Subgroup.closure ({π a, π b} : Set _)) := by
    intro g
    refine ⟨1, Subtype.ext ?_⟩
    have h := CFSG.Timmesfeld.mul_self_eq_one_of_mem_closure hSc hS2 g.2
    simpa [pow_two] using h
  obtain ⟨S, hS⟩ := hP.exists_le_sylow
  have hsub : ({π a, π b} : Set _) ⊆ (π '' imageClass hC) ∩ (S : Set _) := by
    intro s hs
    refine ⟨?_, hS (Subgroup.subset_closure hs)⟩
    rcases hs with rfl | rfl
    · exact ⟨a, ha, rfl⟩
    · exact ⟨b, hb, rfl⟩
  have h2 := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_pair hne', hW S] at h2
  omega

theorem StandingAS.inv_mul_mem_starSocle_of_commute {hC : HypothesisC D} (hSt : StandingAS hC)
    {a b : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)} (ha : a ∈ imageClass hC)
    (hb : b ∈ imageClass hC) (hab : Commute a b) : a⁻¹ * b ∈ starSocle D hC.alpha :=
  hSt.inv_mul_mem_starSocle_of_commute_mk ha hb (hab.map _)

theorem StandingAS.exists_notMem_coset {hC : HypothesisC D} (hSt : StandingAS hC) {x : G}
    (hx : x ∈ DalphaStar D hC.alpha) :
    ∃ c ∈ DalphaStar D hC.alpha,
      (starBar D hC.alpha x)⁻¹ * starBar D hC.alpha c ∉ starSocle D hC.alpha := by
  obtain ⟨-, -, -, -, hidx, -⟩ := hSt.starSocle_spec
  by_contra hall
  push Not at hall
  set π := QuotientGroup.mk' (starSocle D hC.alpha) with hπ
  set t := π (starBar D hC.alpha x) with ht
  have himg : π '' imageClass hC ⊆ {t} := by
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨c, hc, rfl⟩ := exists_starBar_eq_of_mem_imageClass hC ha
    exact (QuotientGroup.eq.mpr (hall c hc)).symm
  have htop : Subgroup.closure ({t} : Set _) = ⊤ := by
    refine top_le_iff.mp ?_
    have h1 : Subgroup.closure (π '' imageClass hC) = ⊤ := by
      rw [← MonoidHom.map_closure, imageClass_gen hC, Subgroup.map_top_of_surjective _
        (QuotientGroup.mk'_surjective _)]
    rw [← h1]
    exact Subgroup.closure_mono himg
  have ht2 : t * t = 1 := by
    rw [ht, ← map_mul,
      hSt.mul_self_eq_one_of_mem_imageClass (starBar_mem_imageClass hC hx), map_one]
  have hcard : Nat.card ((Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ⧸
      starSocle D hC.alpha) ≤ 2 := by
    rw [← Subgroup.card_top, ← htop, ← Subgroup.zpowers_eq_closure, Nat.card_zpowers]
    exact orderOf_le_of_pow_eq_one two_pos (by rw [pow_two, ht2])
  rw [Subgroup.index_eq_card] at hidx
  omega

theorem StandingAS.mk_starBar_pow_eq (h86 : Lemma8_6) (h87 : Theorem8_7) {hC : HypothesisC D}
    (hSt : StandingAS hC) {x w y : G} {n : ℕ} (hT : IsStarTriangle hC x w y) (hn : Odd n)
    (hord : orderOf (x * y * w) = 2 * n) {a : G}
    (ha : a ∈ conjOrbit (localGroup D ((x * y * w) ^ n)) x) :
    QuotientGroup.mk' (starSocle D hC.alpha) (starBar D hC.alpha ((x * y * w) ^ n)) =
      QuotientGroup.mk' (starSocle D hC.alpha) (starBar D hC.alpha a) := by
  have hΔ := conjOrbit_subset_DalphaStar hC hSt.derivedSeries_ne hT.1 hT.2.2.1 hT.2.2.2.1
    hT.2.2.2.2.1 hn hord
  obtain ⟨c, hc, hac⟩ := exists_not_commute_of_mem_conjOrbit h86 h87 hC hSt.rad hSt.not_o4
    hSt.faithful hSt.derivedSeries_ne hT.1 hn hord ha
  obtain ⟨c', hc', hc'c, hcc', -⟩ := exists_setOf_commute_mem_conjOrbit_eq h86 h87 hC hSt.rad
    hSt.not_o4 hSt.faithful hSt.derivedSeries_ne hT.1 hn hord hc
  obtain ⟨-, m, hm, -, -, hpow⟩ := isTriangle_and_pow_eq_of_mem_conjOrbit h86 h87 hC hSt.rad
    hSt.not_o4 hSt.faithful hSt.derivedSeries_ne hT.1 hn hord hc hc' ha (Ne.symm hc'c) hcc'
    (fun h => hac h.symm)
  have hcH := mem_Halpha_of_mem_DalphaStar (hΔ hc)
  have hc'H := mem_Halpha_of_mem_DalphaStar (hΔ hc')
  have haH := mem_Halpha_of_mem_DalphaStar (hΔ ha)
  set π := QuotientGroup.mk' (starSocle D hC.alpha) with hπ
  have hcc'π : π (starBar D hC.alpha c) = π (starBar D hC.alpha c') :=
    QuotientGroup.eq.mpr (hSt.inv_mul_mem_starSocle_of_commute
      (starBar_mem_imageClass hC (hΔ hc)) (starBar_mem_imageClass hC (hΔ hc'))
      (starBar_commute hcH hc'H hcc'))
  have hc2 : π (starBar D hC.alpha c') * π (starBar D hC.alpha c') = 1 := by
    rw [← map_mul, hSt.mul_self_eq_one_of_mem_imageClass (starBar_mem_imageClass hC (hΔ hc')),
      map_one]
  have ha2 : π (starBar D hC.alpha a) * π (starBar D hC.alpha a) = 1 := by
    rw [← map_mul, hSt.mul_self_eq_one_of_mem_imageClass (starBar_mem_imageClass hC (hΔ ha)),
      map_one]
  rw [← hpow, starBar_pow (Subgroup.mul_mem _ (Subgroup.mul_mem _ hcH hc'H) haH),
    starBar_mul (Subgroup.mul_mem _ hcH hc'H) haH, starBar_mul hcH hc'H, map_pow, map_mul,
    map_mul, hcc'π, hc2, one_mul]
  obtain ⟨j, rfl⟩ := hm
  rw [pow_succ, pow_mul, sq, ha2, one_pow, one_mul]

theorem StandingAS.inv_mul_mem_starSocle_of_mem_conjOrbit (h86 : Lemma8_6) (h87 : Theorem8_7)
    {hC : HypothesisC D} (hSt : StandingAS hC) {x w y : G} {n : ℕ}
    (hT : IsStarTriangle hC x w y) (hn : Odd n) (hord : orderOf (x * y * w) = 2 * n) {a : G}
    (ha : a ∈ conjOrbit (localGroup D ((x * y * w) ^ n)) x) :
    (starBar D hC.alpha x)⁻¹ * starBar D hC.alpha a ∈ starSocle D hC.alpha :=
  QuotientGroup.eq.mp ((hSt.mk_starBar_pow_eq h86 h87 hT hn hord
    (self_mem_conjOrbit _ x)).symm.trans (hSt.mk_starBar_pow_eq h86 h87 hT hn hord ha))

theorem StandingAS.inv_mul_starBar_pow_mem_starSocle (h86 : Lemma8_6) (h87 : Theorem8_7)
    {hC : HypothesisC D} (hSt : StandingAS hC) {x w y : G} {n : ℕ}
    (hT : IsStarTriangle hC x w y) (hn : Odd n) (hord : orderOf (x * y * w) = 2 * n) :
    (starBar D hC.alpha x)⁻¹ * starBar D hC.alpha ((x * y * w) ^ n) ∈ starSocle D hC.alpha :=
  QuotientGroup.eq.mp (hSt.mk_starBar_pow_eq h86 h87 hT hn hord (self_mem_conjOrbit _ x)).symm

theorem StandingAS.inv_mul_mem_starSocle_of_commute_starBar_pow (h86 : Lemma8_6)
    (h87 : Theorem8_7) {hC : HypothesisC D} (hSt : StandingAS hC) {x w y : G} {n : ℕ}
    (hT : IsStarTriangle hC x w y) (hn : Odd n) (hord : orderOf (x * y * w) = 2 * n) {p : G}
    (hp : p ∈ DalphaStar D hC.alpha)
    (hpz : Commute (starBar D hC.alpha p) (starBar D hC.alpha ((x * y * w) ^ n))) :
    (starBar D hC.alpha x)⁻¹ * starBar D hC.alpha p ∈ starSocle D hC.alpha := by
  refine hSt.inv_mul_mem_starSocle_of_commute_mk (starBar_mem_imageClass hC hT.2.2.1)
    (starBar_mem_imageClass hC hp) ?_
  rw [← hSt.mk_starBar_pow_eq h86 h87 hT hn hord (self_mem_conjOrbit _ x)]
  exact (hpz.map _).symm

theorem StandingAS.inv_mul_mem_starSocle_of_mem_block (h86 : Lemma8_6) (h87 : Theorem8_7)
    {hC : HypothesisC D} (hSt : StandingAS hC) {x w y : G} (hT : IsStarTriangle hC x w y)
    {ρ : Set G} (hρ : ρ ∈ Dalpha D hC.alpha) {p p' : G} (hp : p ∈ ρ) (hp' : p' ∈ ρ) :
    (starBar D hC.alpha p)⁻¹ * starBar D hC.alpha p' ∈ starSocle D hC.alpha := by
  have ht := hT.1
  have hpS : p ∈ DalphaStar D hC.alpha := ⟨ρ, hρ, hp⟩
  have hp'S : p' ∈ DalphaStar D hC.alpha := ⟨ρ, hρ, hp'⟩
  obtain ⟨h, hh, rfl⟩ := hC.Halpha_transitive x hT.2.2.1 p hpS
  have hnorm : h ∈ Subgroup.normalizer (DalphaStar D hC.alpha) :=
    Halpha_le_normalizer hC.setup.normal hh
  have hqS : h * y * h⁻¹ ∈ DalphaStar D hC.alpha := (hnorm y).mp hT.2.2.2.2.1
  have hpq : Commute (h * x * h⁻¹) (h * y * h⁻¹) := by
    show h * x * h⁻¹ * (h * y * h⁻¹) = h * y * h⁻¹ * (h * x * h⁻¹)
    calc h * x * h⁻¹ * (h * y * h⁻¹) = h * (x * y) * h⁻¹ := by group
      _ = h * (y * x) * h⁻¹ := by rw [ht.2.2.2.2.1.eq]
      _ = h * y * h⁻¹ * (h * x * h⁻¹) := by group
  have hqρ : h * y * h⁻¹ ∉ ρ := by
    intro hq
    refine not_commute_of_mem_of_mem h86 h87 hC hSt.rad hSt.not_o4 hSt.faithful
      hSt.derivedSeries_ne hρ.1 hp hq ?_ hpq
    intro heq
    exact ht.2.2.2.1 (by simpa using heq)
  have hqp' : Commute (h * y * h⁻¹) p' := commute_of_mem_block hC.setup.normal hC.setup.oddT
    (isBlock_of_mem_blockClass hC.setup.normal hC.isBlock_alpha hρ.1) hp
    (DalphaStar_subset hC.isBlock_alpha hqS) hqρ hpq p' hp'
  have h1 := hSt.inv_mul_mem_starSocle_of_commute (starBar_mem_imageClass hC hpS)
    (starBar_mem_imageClass hC hqS) (starBar_commute (mem_Halpha_of_mem_DalphaStar hpS)
      (mem_Halpha_of_mem_DalphaStar hqS) hpq)
  have h2 := hSt.inv_mul_mem_starSocle_of_commute (starBar_mem_imageClass hC hqS)
    (starBar_mem_imageClass hC hp'S) (starBar_commute (mem_Halpha_of_mem_DalphaStar hqS)
      (mem_Halpha_of_mem_DalphaStar hp'S) hqp')
  have h3 := Subgroup.mul_mem _ h1 h2
  rwa [mul_assoc, mul_inv_cancel_left] at h3

end CFSG.OddTranspositions.PartThree.EightEight

end
