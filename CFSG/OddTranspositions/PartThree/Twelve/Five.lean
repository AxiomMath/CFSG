module

public import CFSG.OddTranspositions.PartThree.Twelve.Three
public import CFSG.OddTranspositions.PartFour.Fourteen.RootBlockSp
public import CFSG.OddTranspositions.PartFour.Fourteen.RootBlockUnitary
import CFSG.OddTranspositions.PartFour.SpLineCount
import CFSG.LocalAnalysis.WeakClosure81.EightSixBorelSpNormal
import CFSG.RankThree.PartOne.KC.SymplecticFullRankTwo
import CFSG.GroupTheory.ABGLocalTools.PStabilityQSL2
import CFSG.ClassicalGroups.Unitary.Transitivity
import CFSG.LocalAnalysis.WeakClosure81.W16Gt2KFactsI
import CFSG.LieType.Steinberg.CentralExt.UnitaryField
import CFSG.OddTranspositions.WidthSylow
public import CFSG.CGT.Timmesfeld75.Cfg214Gen
public import CFSG.CGT.Timmesfeld75.Derivations
public import CFSG.CGT.Timmesfeld75.Form2
public import CFSG.CGT.Timmesfeld75.Main
public import CFSG.LargeExtraspecial.S9TIXC
public import CFSG.LocalAnalysis.WeakClosure81.SevenKGen
public import CFSG.LocalAnalysis.WeakClosure81.SevenTwelveConfPSU
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeLinear
public import CFSG.RankThree.PartOne.KC.UnitaryPrimaryAlgebra
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Basic
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
import CFSG.OddTranspositions.O4PairTenWidth
import CFSG.OddTranspositions.Width

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.OddTranspositions.PartFour
open CFSG.LocalAnalysis.WeakClosure81.SevenK CFSG.Open CFSG.RankThree.Classical
  CFSG.RankThree.PartOne.KCSpFull CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoOther
  CFSG.LocalAnalysis.WeakClosure81
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem ncard_blockLine_eq_ncard_rootBlock_add_one (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    {s₀ : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)}
    (hs₀ : s₀ ∈ imageClass hC)
    (hb1 : ∀ B, IsBlock (imageClass hC) B → s₀ ∈ B → B ⊆ rootBlock (imageClass hC) s₀)
    (hne : rootBlock (imageClass hC) s₀ ≠ imageClass hC) (hα : hC.alpha = {hC.d})
    {β : Set G} (hβ : β ∈ Dalpha D hC.alpha) {b : Halpha D hC.alpha} (hb : (b : G) ∈ β) :
    (blockLine D hC.alpha β).ncard = (rootBlock (imageClass hC)
      (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) b)).ncard + 1 := by
  classical
  have hinj := injOn_mk_DstarH_of_rootBlock_ne hC hMZ hs₀ hne
  set π := QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) with hπ
  have hsingle : ∀ γ ∈ blockClass hC.alpha, ∃ c : G, γ = {c} := by
    intro γ hγ
    obtain ⟨g, rfl⟩ := mem_blockClass_iff.mp hγ
    exact ⟨g * hC.d * g⁻¹, by rw [hα, Set.image_singleton]⟩
  have hαD : hC.alpha ⊆ D := hC.isBlock_alpha.subset
  have hαβ : hC.alpha ∈ perp D hC.alpha ∩ perp D β :=
    ⟨mem_perp_iff.mpr (Or.inr rfl), mem_perp_iff.mpr (Or.inl (mem_Dalpha_symm hβ hαD))⟩
  have hL : ∀ γ ∈ blockLine D hC.alpha β \ {hC.alpha}, γ ∈ Dalpha D hC.alpha := by
    rintro γ ⟨hγL, hγα⟩
    rcases mem_perp_iff.mp (hγL.2 _ hαβ) with h | h
    · exact h
    · exact absurd h hγα
  have hαL : hC.alpha ∈ blockLine D hC.alpha β := by
    refine ⟨mem_blockClass_self _, fun γ hγ => ?_⟩
    rcases mem_perp_iff.mp hγ.1 with h | h
    · exact mem_perp_iff.mpr (Or.inl (mem_Dalpha_symm h hαD))
    · exact mem_perp_iff.mpr (Or.inr h.symm)
  set T : Set (Halpha D hC.alpha) :=
    {c | ∃ γ ∈ blockLine D hC.alpha β \ {hC.alpha}, (c : G) ∈ γ} with hT
  have hTstar : T ⊆ DstarH hC := fun c ⟨γ, hγ, hc⟩ => ⟨γ, hL γ hγ, hc⟩
  have himg : lineImage hC β = π '' T := by
    ext x
    simp only [lineImage, Set.mem_iUnion, Set.mem_image, exists_prop]
    constructor
    · rintro ⟨γ, hγ, c, hc, rfl⟩
      exact ⟨c, ⟨γ, hγ, hc⟩, rfl⟩
    · rintro ⟨c, ⟨γ, hγ, hc⟩, rfl⟩
      exact ⟨γ, hγ, c, hc, rfl⟩
  have h1 : (lineImage hC β).ncard = T.ncard := by
    rw [himg]
    exact (hinj.mono hTstar).ncard_image
  have h2 : blockLine D hC.alpha β \ {hC.alpha} =
      (fun c : Halpha D hC.alpha => ({(c : G)} : Set G)) '' T := by
    ext γ
    constructor
    · intro hγ
      obtain ⟨c, rfl⟩ := hsingle γ hγ.1.1
      have hcH : c ∈ Halpha D hC.alpha := Subgroup.subset_closure ⟨{c}, hL _ hγ, rfl⟩
      exact ⟨⟨c, hcH⟩, ⟨{c}, hγ, rfl⟩, rfl⟩
    · rintro ⟨c, ⟨γ, hγ, hcγ⟩, rfl⟩
      obtain ⟨c', rfl⟩ := hsingle γ hγ.1.1
      show ({(c : G)} : Set G) ∈ _
      rw [Set.mem_singleton_iff.mp hcγ]
      exact hγ
  have h3 : (blockLine D hC.alpha β \ {hC.alpha}).ncard = T.ncard := by
    rw [h2]
    exact Set.ncard_image_of_injective _
      (fun c c' h => Subtype.ext (Set.singleton_eq_singleton_iff.mp h))
  rw [← Set.ncard_diff_singleton_add_one hαL (Set.toFinite _), h3, ← h1,
    lineImage_eq_rootBlock hC hMZ hs₀ hb1 hne hβ hb]

theorem ncard_rootBlock_of_isSymplecticTransvection {X : Type} [Group X] {E : Set X}
    (hcls : ∃ d₀ : X, E = {g | IsConj d₀ g}) (hZ : Subgroup.center X = ⊥) {s : X} (hs : s ∈ E)
    {m f : ℕ} (h : IsSymplecticTransvection X m f s) : (rootBlock E s).ncard = 2 ^ f - 1 := by
  classical
  obtain ⟨k, -, F, _, _, hF, e, hrank⟩ := h
  have : CharP F 2 := CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow Nat.prime_two hF
  set ψ : X →* StatedSp k F := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))
    with hψdef
  have hψinj : Function.Injective ψ := by
    intro a b hab
    have h1 : QuotientGroup.mk' (Subgroup.center X) a = QuotientGroup.mk' (Subgroup.center X) b :=
      e.injective hab
    rw [QuotientGroup.mk'_eq_mk'] at h1
    obtain ⟨z, hz, hzb⟩ := h1
    rw [hZ, Subgroup.mem_bot] at hz
    rw [hz, mul_one] at hzb
    exact hzb
  have hψsurj : Function.Surjective ψ :=
    e.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨u, c, hu, hc, hψs⟩ := borel86_spn_eq_spTransvection hrank
  change ψ s = spTransvection u c at hψs
  have hcomm : ∀ x y : X, Commute x y ↔ Commute (ψ x) (ψ y) := fun x y =>
    ⟨fun h => h.map ψ, fun h => hψinj (by rw [map_mul, map_mul]; exact h.eq)⟩
  have hEs : ∀ x, x ∈ E ↔ IsConj s x := by
    obtain ⟨d₀, rfl⟩ := hcls
    intro x
    exact ⟨fun hx => (isConj_comm.mp hs).trans hx, fun hx => (show IsConj d₀ s from hs).trans hx⟩
  have hconj : ∀ v, v ≠ 0 → ∃ y ∈ E, ψ y = spTransvection v c := by
    intro v hv
    obtain ⟨g, hg⟩ := exists_spEnd_eq hu hv
    obtain ⟨g', hg'⟩ := hψsurj g
    refine ⟨g' * s * g'⁻¹, (hEs _).mpr (isConj_iff.mpr ⟨g', rfl⟩), ?_⟩
    rw [map_mul, map_mul, map_inv, hg', hψs, conj_spTransvection, hg]
  have hEtr : ∀ x ∈ E, ∃ v, v ≠ 0 ∧ ψ x = spTransvection v c := by
    intro x hx
    obtain ⟨g, rfl⟩ := isConj_iff.mp ((hEs x).mp hx)
    refine ⟨spEnd (ψ g) u, fun h0 => hu ?_, ?_⟩
    · rw [← spEnd_spEnd_inv_apply (ψ g)⁻¹ u, inv_inv, h0, map_zero]
    · rw [map_mul, map_mul, map_inv, hψs, conj_spTransvection]
  have himg : ψ '' rootBlock E s = (fun c' => spTransvection u c') '' {c' : F | c' ≠ 0} := by
    ext t
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨w, hw, hyw⟩ := hEtr y hy.1
      by_cases hprop : ∃ a : F, w = a • u
      · obtain ⟨a, rfl⟩ := hprop
        have ha : a ≠ 0 := by
          rintro rfl
          exact hw (zero_smul _ _)
        exact ⟨a * a * c, mul_ne_zero (mul_ne_zero ha ha) hc,
          by rw [hyw, spTransvection_smul_eq]⟩
      · push Not at hprop
        exfalso
        obtain ⟨x, hxu, hxw⟩ := exists_spForm_eq_zero_ne_zero hu hprop
        have hx0 : x ≠ 0 := by
          rintro rfl
          exact hxw (by simp)
        obtain ⟨z, hz, hψz⟩ := hconj x hx0
        have h1 : Commute z s := by
          rw [hcomm, hψz, hψs, commute_spTransvection_iff hc hc]
          exact hxu
        have h2 := (hy.2 z hz).mpr h1
        rw [hcomm, hψz, hyw, commute_spTransvection_iff hc hc] at h2
        exact hxw h2
    · rintro ⟨c', hc', rfl⟩
      obtain ⟨r, hr⟩ := isSquare_of_charTwo' (c' / c)
      have hr0 : r ≠ 0 := by
        rintro rfl
        rw [mul_zero, div_eq_zero_iff] at hr
        exact hr.elim hc' hc
      obtain ⟨y, hy, hψy⟩ := hconj (r • u) (smul_ne_zero hr0 hu)
      refine ⟨y, ⟨hy, fun z hz => ?_⟩, ?_⟩
      · obtain ⟨v, -, hzv⟩ := hEtr z hz
        rw [hcomm, hcomm, hzv, hψy, hψs, commute_spTransvection_iff hc hc,
          commute_spTransvection_iff hc hc, map_smul, smul_eq_mul, mul_eq_zero, or_iff_right hr0]
      · rw [hψy, spTransvection_smul_eq]
        congr 1
        rw [← hr]
        field_simp
  have hTinj : Function.Injective (fun c' : F => spTransvection u c') := by
    intro c₁ c₂ h12
    obtain ⟨z, hz⟩ : ∃ z, spForm k F z u ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hu (spForm_nondegenerate.2 u hcon)
    have h1 := congrArg (fun g => spEnd g z) h12
    simp only [spEnd_spTransvection] at h1
    exact mul_right_cancel₀ hz (smul_left_injective F hu (add_left_cancel h1))
  have hcard : {c' : F | c' ≠ 0}.ncard = 2 ^ f - 1 := by
    have : {c' : F | c' ≠ 0} = Set.univ \ {0} := by
      ext x
      simp
    rw [this, Set.ncard_diff_singleton_of_mem (Set.mem_univ _), Set.ncard_univ,
      hF]
  rw [← Set.ncard_image_of_injective _ hψinj, himg, Set.ncard_image_of_injective _ hTinj, hcard]

section UnitaryCount

open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

variable {F : Type} [Field F] {σ : F ≃+* F} {m : ℕ}

theorem suTv_smul_eq (hσ : IsUnitaryInvolution σ) {u : Fin m → F} (hu : herm σ u u = 0)
    (a : F) {c : F} (hc : c + σ c = 0) : suTv hσ (a • u) c = suTv hσ u (σ a * a * c) := by
  have hau : herm σ (a • u) (a • u) = 0 := by
    rw [herm_smul_left, herm_smul_right, hu, mul_zero, mul_zero]
  have hc' : σ a * a * c + σ (σ a * a * c) = 0 := by
    rw [map_mul, map_mul, hσ.invol]
    linear_combination (σ a * a) * hc
  refine ext_smul σ fun v => ?_
  rw [suTv_smul hσ hau hc, suTv_smul hσ hu hc', herm_smul_left, smul_smul]
  module

end UnitaryCount

section UnitaryModelCount

open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}

theorem kFactsSuProj_suTv_injOn (hF : Nat.card F = (2 ^ n) ^ 2) {m : ℕ} {u : Fin m → F}
    (hu0 : u ≠ 0) (hu : herm (unitaryInvolution F 2 n) u u = 0) :
    Set.InjOn (fun c => kFactsSuProj hF m (suTv (isUnitaryInvolution_unitaryInvolution hF) u c))
      {c | c + unitaryInvolution F 2 n c = 0} := by
  set σ := unitaryInvolution F 2 n with hσdef
  have hσ : IsUnitaryInvolution σ := isUnitaryInvolution_unitaryInvolution hF
  intro c₁ hc₁ c₂ hc₂ h12
  obtain ⟨l, hl⟩ := (kFacts_suProj_eq_iff hF _ _).mp h12
  have hv : ∀ v : Fin m → F, suTv hσ u c₂ • v = (l : F) • (suTv hσ u c₁ • v) := by
    intro v
    rw [smul_def, smul_def, hl, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mulVec]
  have hl1 : (l : F) = 1 := by
    have h1 := hv u
    simp only [suTv_smul hσ hu hc₂, suTv_smul hσ hu hc₁, hu, mul_zero, zero_smul,
      add_zero] at h1
    have h3 : ((l : F) - 1) • u = 0 := by rw [sub_smul, one_smul, ← h1, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right hu0)
  obtain ⟨z, hz⟩ := exists_herm_ne_zero σ hu0
  have h1 := hv z
  rw [hl1, one_smul, suTv_smul hσ hu hc₂, suTv_smul hσ hu hc₁] at h1
  exact (mul_right_cancel₀ hz (smul_left_injective F hu0 (add_left_cancel h1))).symm

theorem ncard_rootBlock_of_isUnitaryTransvection {X : Type} [Group X] {E : Set X}
    (hcls : ∃ d₀ : X, E = {g | IsConj d₀ g}) (hZ : Subgroup.center X = ⊥) {s : X} (hs : s ∈ E)
    {m f : ℕ} (hm : 4 ≤ m) (h : IsUnitaryTransvection X m f s) :
    (rootBlock E s).ncard = 2 ^ f - 1 := by
  classical
  obtain ⟨F, _, _, hF, e, hrank⟩ := h
  have : Fintype F := Fintype.ofFinite F
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2 * f)
    (by rw [← Nat.card_eq_fintype_card, hF, ← pow_mul, mul_comm])
  set σ := unitaryInvolution F 2 f with hσdef
  have hσ : IsUnitaryInvolution σ := isUnitaryInvolution_unitaryInvolution hF
  have hinv := hσ.invol
  have h1 : (1 : F) + σ 1 = 0 := by rw [map_one]; exact CharTwo.add_self_eq_zero 1
  set π := kFactsSuProj hF m with hπdef
  have hπsurj : Function.Surjective π := kFacts_suProj_surjective hF m
  set ψ : X →* StatedProj (StatedSU m (2 ^ f) F) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X)) with hψdef
  have hψinj : Function.Injective ψ := by
    intro a b hab
    have h2 : QuotientGroup.mk' (Subgroup.center X) a = QuotientGroup.mk' (Subgroup.center X) b :=
      e.injective hab
    rw [QuotientGroup.mk'_eq_mk'] at h2
    obtain ⟨z, hz, hzb⟩ := h2
    rw [hZ, Subgroup.mem_bot] at hz
    rw [hz, mul_one] at hzb
    exact hzb
  have hψsurj : Function.Surjective ψ :=
    e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hcomm : ∀ x y : X, Commute x y ↔ Commute (ψ x) (ψ y) := fun x y =>
    ⟨fun h => h.map ψ, fun h => hψinj (by rw [map_mul, map_mul]; exact h.eq)⟩
  obtain ⟨u, hu0, hu, hψs⟩ := kFacts_su_exists_centre hF hrank
  change ψ s = π (suTv hσ u 1) at hψs
  replace hu : herm σ u u = 0 := hu
  have hEs : ∀ x, x ∈ E ↔ IsConj s x := by
    obtain ⟨d₀, rfl⟩ := hcls
    intro x
    exact ⟨fun hx => (isConj_comm.mp hs).trans hx, fun hx => (show IsConj d₀ s from hs).trans hx⟩
  have hEmem : ∀ v, v ≠ 0 → herm σ v v = 0 → ∃ y ∈ E, ψ y = π (suTv hσ v 1) := by
    intro v hv0 hv
    obtain ⟨t, -, ht⟩ := exists_mem_T_smul_eq_of_iso hσ (by omega) hu0 hu hv0 hv
    obtain ⟨g, hg⟩ := hψsurj (π t)
    refine ⟨g * s * g⁻¹, (hEs _).mpr (isConj_iff.mpr ⟨g, rfl⟩), ?_⟩
    rw [map_mul, map_mul, map_inv, hg, hψs, ← map_inv, ← map_mul, ← map_mul,
      suTv_conj hσ t hu h1, ht]
  have hEtr : ∀ x ∈ E, ∃ v, v ≠ 0 ∧ herm σ v v = 0 ∧ ψ x = π (suTv hσ v 1) := by
    intro x hx
    obtain ⟨g, rfl⟩ := isConj_iff.mp ((hEs x).mp hx)
    obtain ⟨g', hg'⟩ := hπsurj (ψ g)
    refine ⟨g' • u, fun h0 => hu0 (by rw [← inv_smul_smul g' u, h0, smul_zero]),
      by rw [herm_smul_smul, hu], ?_⟩
    rw [map_mul, map_mul, map_inv, hψs, ← hg', ← map_inv, ← map_mul, ← map_mul,
      suTv_conj hσ g' hu h1]
  have hcommE : ∀ a b : Fin m → F, a ≠ 0 → herm σ a a = 0 → herm σ b b = 0 →
      (Commute (π (suTv hσ a 1)) (π (suTv hσ b 1)) ↔ herm σ a b = 0) := by
    intro a b ha0 ha hb
    exact ⟨herm_eq_zero_of_commute_kFactsSuProjTv hF (by omega) ha0 ha hb,
      fun hab => kFacts_suProjTv_comm_of_herm_eq_zero hF ha hb hab h1 h1⟩
  have himg : ψ '' rootBlock E s =
      (fun c' => π (suTv hσ u c')) '' {c' : F | c' + σ c' = 0 ∧ c' ≠ 0} := by
    ext t
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨w, hw0, hw, hyw⟩ := hEtr y hy.1
      have hsy : Commute s y := (hy.2 s hs).mpr (Commute.refl s)
      have huw : herm σ u w = 0 := by
        rw [hcomm, hψs, hyw, hcommE u w hu0 hu hw] at hsy
        exact hsy
      by_cases hprop : ∃ a : F, w = a • u
      · obtain ⟨a, rfl⟩ := hprop
        have ha : a ≠ 0 := by
          rintro rfl
          exact hw0 (zero_smul _ _)
        refine ⟨σ a * a * 1, ⟨?_, ?_⟩, by rw [hyw, suTv_smul_eq hσ hu a h1]⟩
        · rw [map_mul, map_mul, hinv]
          linear_combination (σ a * a) * h1
        · exact mul_ne_zero (mul_ne_zero ((map_ne_zero σ).mpr ha) ha) one_ne_zero
      · push Not at hprop
        exfalso
        obtain ⟨d, hd, hud, hwd⟩ := exists_iso_perp hσ hu0 hu hw huw hprop
        have hd0 : d ≠ 0 := by
          rintro rfl
          exact hwd (herm_zero_right σ w)
        obtain ⟨z, hz, hψz⟩ := hEmem d hd0 hd
        have h2 : Commute z s := by
          rw [hcomm, hψz, hψs, hcommE d u hd0 hd hu]
          exact herm_eq_zero_comm σ hinv hud
        have h3 := (hy.2 z hz).mpr h2
        rw [hcomm, hψz, hyw, hcommE d w hd0 hd hw] at h3
        exact hwd (herm_eq_zero_comm σ hinv h3)
    · rintro ⟨c', ⟨hc'0, hc'⟩, rfl⟩
      have hfix : σ c' = c' := by
        have h2 : σ c' = -c' := by linear_combination hc'0
        rw [h2, CharTwo.neg_eq]
      obtain ⟨a, ha⟩ := hσ.exists_norm hfix
      have ha0 : a ≠ 0 := by
        rintro rfl
        rw [map_zero, zero_mul] at ha
        exact hc' ha.symm
      have hau0 : a • u ≠ 0 := smul_ne_zero ha0 hu0
      have hau : herm σ (a • u) (a • u) = 0 := by
        rw [herm_smul_left, herm_smul_right, hu, mul_zero, mul_zero]
      obtain ⟨y, hy, hψy⟩ := hEmem (a • u) hau0 hau
      refine ⟨y, ⟨hy, fun z hz => ?_⟩, ?_⟩
      · obtain ⟨v, hv0, hv, hzv⟩ := hEtr z hz
        rw [hcomm, hcomm, hzv, hψy, hψs, hcommE v _ hv0 hv hau, hcommE v u hv0 hv hu,
          herm_smul_right, mul_eq_zero, or_iff_right ha0]
      · rw [hψy, suTv_smul_eq hσ hu a h1, ha, mul_one]
  have hcard : {c' : F | c' + σ c' = 0 ∧ c' ≠ 0}.ncard = 2 ^ f - 1 := by
    have h2 : {c' : F | c' + σ c' = 0 ∧ c' ≠ 0} =
        ((traceZero σ : AddSubgroup F) : Set F) \ {0} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_diff, SetLike.mem_coe, Set.mem_singleton_iff]
      rfl
    rw [h2, Set.ncard_diff_singleton_of_mem (by exact (traceZero σ).zero_mem),
      ← Nat.card_coe_set_eq, SetLike.coe_sort_coe, hσdef,
      CFSG.LieType.Steinberg.card_traceZero hF]
  rw [← Set.ncard_image_of_injective _ hψinj, himg,
    (kFactsSuProj_suTv_injOn hF hu0 hu).mono (fun c hc => hc.1) |>.ncard_image, hcard]

end UnitaryModelCount

theorem ncard_rootBlock_eq_of_mem_imageClass (hC : HypothesisC D)
    {s₀ t : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)}
    (hs₀ : s₀ ∈ imageClass hC) (ht : t ∈ imageClass hC) :
    (rootBlock (imageClass hC) t).ncard = (rootBlock (imageClass hC) s₀).ncard := by
  obtain ⟨d₀, hd₀⟩ := imageClass_isClass hC
  have hst : IsConj s₀ t := by
    rw [hd₀] at hs₀ ht
    exact (isConj_comm.mp hs₀).trans ht
  obtain ⟨g, rfl⟩ := isConj_iff.mp hst
  rw [← image_conj_rootBlock (imageClass_isNormalSet hC) g s₀]
  exact Set.ncard_image_of_injective _ fun x y h => by simpa using h

theorem ncard_blockLine_eq_ncard_rootBlock_add_one_of_mem (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    {s₀ : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)}
    (hs₀ : s₀ ∈ imageClass hC)
    (hb1 : ∀ B, IsBlock (imageClass hC) B → s₀ ∈ B → B ⊆ rootBlock (imageClass hC) s₀)
    (hne : rootBlock (imageClass hC) s₀ ≠ imageClass hC) (hα : hC.alpha = {hC.d})
    {β : Set G} (hβ : β ∈ Dalpha D hC.alpha) :
    (blockLine D hC.alpha β).ncard = (rootBlock (imageClass hC) s₀).ncard + 1 := by
  obtain ⟨b, hb⟩ := nonempty_of_mem_blockClass ⟨hC.d, hC.d_mem_alpha⟩ hβ.1
  have hbH : b ∈ Halpha D hC.alpha := Subgroup.subset_closure ⟨β, hβ, hb⟩
  rw [ncard_blockLine_eq_ncard_rootBlock_add_one hC hMZ hs₀ hb1 hne hα hβ (b := ⟨b, hbH⟩) hb,
    ncard_rootBlock_eq_of_mem_imageClass hC hs₀ ⟨⟨b, hbH⟩, ⟨β, hβ, hb⟩, rfl⟩]

theorem center_Hbar_eq_bot (hC : HypothesisC D) :
    Subgroup.center (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) = ⊥ := by
  have h1 := center_le_solvableRadical
    (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))
  rw [solvableRadical_quotient_H hC] at h1
  exact le_bot_iff.mp h1

theorem twelveFive_of_isSymplecticTransvection (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hα : hC.alpha = {hC.d}) {s : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)}
    (hs : s ∈ imageClass hC) {m f : ℕ}
    (h : IsSymplecticTransvection
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) m f s)
    {β : Set G} (hβ : β ∈ Dalpha D hC.alpha) :
    (blockLine D hC.alpha β).ncard = 2 ^ f := by
  have hZ := center_Hbar_eq_bot hC
  obtain ⟨hb1, hne⟩ :=
    subset_rootBlock_and_ne_of_isSymplecticTransvection (imageClass_isClass hC) hZ hs h
  rw [ncard_blockLine_eq_ncard_rootBlock_add_one_of_mem hC hMZ hs hb1 hne hα hβ,
    ncard_rootBlock_of_isSymplecticTransvection (imageClass_isClass hC) hZ hs h]
  have : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  omega

theorem twelveFive_of_isUnitaryTransvection (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hα : hC.alpha = {hC.d}) {s : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)}
    (hs : s ∈ imageClass hC) {m f : ℕ} (hm : 4 ≤ m)
    (h : IsUnitaryTransvection
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) m f s)
    {β : Set G} (hβ : β ∈ Dalpha D hC.alpha) :
    (blockLine D hC.alpha β).ncard = 2 ^ f := by
  have hZ := center_Hbar_eq_bot hC
  obtain ⟨hb1, hne⟩ :=
    subset_rootBlock_and_ne_of_isUnitaryTransvection (imageClass_isClass hC) hZ hs hm h
  rw [ncard_blockLine_eq_ncard_rootBlock_add_one_of_mem hC hMZ hs hb1 hne hα hβ,
    ncard_rootBlock_of_isUnitaryTransvection (imageClass_isClass hC) hZ hs hm h]
  have : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  omega

theorem twelveFive_of_rootBlock_eq_singleton (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hα : hC.alpha = {hC.d})
    {s₀ : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)}
    (hs₀ : s₀ ∈ imageClass hC)
    (hb1 : ∀ B, IsBlock (imageClass hC) B → s₀ ∈ B → B ⊆ rootBlock (imageClass hC) s₀)
    (hne : rootBlock (imageClass hC) s₀ ≠ imageClass hC)
    (hsing : rootBlock (imageClass hC) s₀ = {s₀}) {β : Set G} (hβ : β ∈ Dalpha D hC.alpha) :
    (blockLine D hC.alpha β).ncard = 2 := by
  rw [ncard_blockLine_eq_ncard_rootBlock_add_one_of_mem hC hMZ hs₀ hb1 hne hα hβ, hsing,
    Set.ncard_singleton]

end CFSG.OddTranspositions.PartThree
