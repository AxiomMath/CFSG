module

public import CFSG.RankThree.PartTwo.Sec6.Item611FixProofTools
public import CFSG.RankThree.PartTwo.Sec6.Item611Res3ProofMinus
import CFSG.RankThree.PartTwo.Sec6.Item612UsedOf

public section

namespace CFSG.RankThree.PartTwo.Sec6

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open scoped Pointwise
open Res611Minus

section Certs


theorem item611ChooseMinus_holdsFix (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8)
    (h49 : Sec4.Item4_9) (hKf : KFacts.KS6OuterIndex) (h41 : Sec4.Item4_1LargePrime)
    (h413 : Sec4.Item4_13_forwardFix) : Item611ChooseMinus := by
  intro G _ _ hst A hA hrank c hcA hc1 L hL hCA E hE T hT
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hEmem, hEA⟩ := hE
  have hEab := hEmem.1
  have hE3 : IsPGroup 3 E := Sec5.isPGroup_of_isElemAbelian hEab
  obtain ⟨hEN, hTab, hT4⟩ := mem_fourGroups_iff.mp hT.1
  have hT2 : IsPGroup 2 T := IsPGroup.of_card (n := 2) (by rw [hT4]; norm_num)
  have he := hst.evenRank_eq
  obtain ⟨c', ⟨hc'E, hc'T⟩, hc'1, L', hL', hTN, hLT, -, -⟩ :=
    rank3II_6_12_sec21_of_used h45 h48 h49 hKf G hst A hA E ⟨hEmem, hEA⟩ T hT.1
  have hc'A : c' ∈ A := hEA hc'E
  have hL'c : L' ∈ thetaComponentsAt 3 c' := hL'.1
  have hL's : L' ∈ lStar A := hL'.2.2
  have hcyc := rank3II_6_6_of_used h45 h48 h49 G hst A hA L' hL's
  have hCA' : A ⊓ thetaQuotCentralizer L' = Subgroup.zpowers c' :=
    Res611.eq_zpowers_of_isCyclic hA.1.1 inf_le_left hcyc
      ⟨hc'A, mem_thetaQuotCentralizer_of_mem_thetaComponentsAt hL'c⟩ hc'1
  obtain ⟨B, hBL, hBe, hB81⟩ :=
    Res611Fix.exists_elemAbelian_le h45 h41 h413 hst hA hrank hc'A hc'1 hL' hCA'
  set C' := thetaQuotCentralizer L' with hC'
  have hAL' := le_normalizer_of_mem_thetaComponentsAt h45 hst.toTheoremFourHyp hA.1.1 hc'A hc'1
  have hEL' : E ≤ Subgroup.normalizer (L' : Set G) := hEA.trans (hAL' L' hL'c)
  have hCN := normalizer_le_normalizer_thetaQuotCentralizer L'
  have hEC : E ≤ Subgroup.normalizer (C' : Set G) := hEL'.trans hCN
  have hTC'N : T ≤ Subgroup.normalizer (C' : Set G) := hTN.trans hCN
  have hTLC : T ≤ L' ⊔ C' := by
    set H := Subgroup.centralizer ({c'} : Set G) with hH
    obtain ⟨hLH, hL''⟩ := mem_thetaComponentsIn_iff.mp hL'c
    have hEH : E ≤ H := fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hEab.1.is_comm.comm ⟨x, hx⟩ ⟨c', hc'E⟩))
    have hTH : T ≤ H := fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr
      ((Subgroup.mem_centralizer_iff.mp hc'T x hx))
    have hH4 : SectionFourHyp H :=
      hst.toTheoremFourHyp.sectionFourHyp (centralizer_ne_top_of_ne_one hst.toTheoremFourHyp hc'1)
    have h3Z : 3 ∣ Nat.card (Subgroup.center H) := by
      set c'' : H := ⟨c', Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
      have hc''3 : orderOf c'' = 3 := by
        rw [Subgroup.orderOf_mk]
        exact orderOf_eq_prime (hEab.2 c' hc'E) hc'1
      have hle : Subgroup.zpowers c'' ≤ Subgroup.center H := by
        rw [Subgroup.zpowers_le, Subgroup.mem_center_iff]
        intro g
        exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp g.2)
      have := Subgroup.card_dvd_of_le hle
      rwa [Nat.card_zpowers, hc''3] at this
    have hXK : ∀ K ∈ thetaComponents 3 H, E.subgroupOf H ≤ Subgroup.normalizer (K : Set H) := by
      intro K hK x hx
      exact mem_normalizer_of_mem_normalizer_map
        (hEA.trans (hAL' (K.map H.subtype) ⟨K, hK, rfl⟩) (Subgroup.mem_subgroupOf.mp hx))
    have hTEeq : ⁅E, T⁆ = T := by
      rw [Subgroup.commutator_comm]
      exact hT.2.symm
    have hT' : T.subgroupOf H ∈ invariantPiSubgroups ⊤ (E.subgroupOf H) (piOf 2) :=
      (mem_invariantPiSubgroups_piOf_iff Nat.prime_two).mpr ⟨le_top,
        hT2.comap_of_injective H.subtype H.subtype_injective,
        subgroupOf_le_normalizer_subgroupOf hEN⟩
    have hTE' : ⁅E.subgroupOf H, T.subgroupOf H⁆ = T.subgroupOf H := by
      apply Subgroup.map_injective H.subtype_injective
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hEH,
        Subgroup.map_subgroupOf_eq_of_le hTH]
      exact hTEeq
    have h49' := h49 H hH4 h3Z (L'.subgroupOf H) hL'' (E.subgroupOf H)
      (hE3.comap_of_injective H.subtype H.subtype_injective) hXK (T.subgroupOf H) hT' hTE'
    have h1 := Subgroup.map_mono (f := H.subtype) h49'
    rw [Subgroup.map_subgroupOf_eq_of_le hTH, Subgroup.map_sup,
      Subgroup.map_subgroupOf_eq_of_le hLH] at h1
    refine h1.trans (sup_le_sup_left ?_ L')
    have h2 := map_thetaQuotCentralizer_le (L'.subgroupOf H)
    rwa [Subgroup.map_subgroupOf_eq_of_le hLH] at h2
  obtain ⟨R, hR, hTR, hRT⟩ := exists_invariant_two_subgroup_cover hE3 hEL' hT2 hEN hTN hTLC
  obtain ⟨hRL', hR2, hER⟩ := (mem_invariantPiSubgroups_piOf_iff Nat.prime_two).mp hR
  have hRC'N : R ≤ Subgroup.normalizer (C' : Set G) :=
    (hRL'.trans Subgroup.le_normalizer).trans hCN
  have hTC : T ⊓ C' = ⊥ :=
    Res611Res3.inf_thetaQuotCentralizer_eq_bot_of_le he hBe hBL hB81 hTab
  have hRC : R ⊓ C' = ⊥ := inf_thetaQuotCentralizer_eq_bot_of_isPGroup he hBe hBL hB81 hR2
  have hdecT : ∀ t ∈ T, ∃ r ∈ R, ∃ z ∈ C', t = r * z := fun t ht =>
    exists_mul_eq_of_mem_sup hRC'N (hTR ht)
  have hdecR : ∀ r ∈ R, ∃ t ∈ T, ∃ z ∈ C', r = t * z := fun r hr =>
    exists_mul_eq_of_mem_sup hTC'N (hRT hr)
  have hmemC : ∀ {x y : G}, x ∈ C' → y ∈ C' → x⁻¹ * y ∈ C' := fun hx hy =>
    C'.mul_mem (C'.inv_mem hx) hy
  have hcard : Nat.card R = 4 := by
    classical
    let f : T → R := fun t => ⟨(hdecT t t.2).choose, (hdecT t t.2).choose_spec.1⟩
    have hf : Function.Injective f := by
      intro t₁ t₂ h
      obtain ⟨-, z₁, hz₁, ht₁⟩ := (hdecT t₁ t₁.2).choose_spec
      obtain ⟨-, z₂, hz₂, ht₂⟩ := (hdecT t₂ t₂.2).choose_spec
      have h' : (hdecT t₁ t₁.2).choose = (hdecT t₂ t₂.2).choose := congrArg Subtype.val h
      have hmem : (t₁ : G)⁻¹ * t₂ ∈ T ⊓ C' := ⟨T.mul_mem (T.inv_mem t₁.2) t₂.2, by
        rw [ht₁, ht₂, h', show ((hdecT t₂ t₂.2).choose * z₁)⁻¹ * ((hdecT t₂ t₂.2).choose * z₂) =
          z₁⁻¹ * z₂ by group]
        exact hmemC hz₁ hz₂⟩
      rw [hTC, Subgroup.mem_bot] at hmem
      exact Subtype.ext (eq_of_inv_mul_eq_one hmem)
    let g : R → T := fun r => ⟨(hdecR r r.2).choose, (hdecR r r.2).choose_spec.1⟩
    have hg : Function.Injective g := by
      intro r₁ r₂ h
      obtain ⟨-, z₁, hz₁, hr₁⟩ := (hdecR r₁ r₁.2).choose_spec
      obtain ⟨-, z₂, hz₂, hr₂⟩ := (hdecR r₂ r₂.2).choose_spec
      have h' : (hdecR r₁ r₁.2).choose = (hdecR r₂ r₂.2).choose := congrArg Subtype.val h
      have hmem : (r₁ : G)⁻¹ * r₂ ∈ R ⊓ C' := ⟨R.mul_mem (R.inv_mem r₁.2) r₂.2, by
        rw [hr₁, hr₂, h', show ((hdecR r₂ r₂.2).choose * z₁)⁻¹ * ((hdecR r₂ r₂.2).choose * z₂) =
          z₁⁻¹ * z₂ by group]
        exact hmemC hz₁ hz₂⟩
      rw [hRC, Subgroup.mem_bot] at hmem
      exact Subtype.ext (eq_of_inv_mul_eq_one hmem)
    have h1 := Nat.card_le_card_of_injective f hf
    have h2 := Nat.card_le_card_of_injective g hg
    omega
  have hRsq : ∀ r ∈ R, r ^ 2 = 1 := by
    intro r hr
    obtain ⟨t, ht, z, hz, rfl⟩ := hdecR r hr
    have hmem : (t * z) ^ 2 ∈ R ⊓ C' := by
      refine ⟨R.pow_mem hr 2, ?_⟩
      rw [pow_two, show t * z * (t * z) = (t * z * t⁻¹) * (t * t) * z by group,
        show t * t = 1 by rw [← pow_two]; exact hTab.2 t ht, mul_one]
      exact C'.mul_mem ((Subgroup.mem_normalizer_iff.mp (hTC'N ht) z).mp hz) hz
    rw [hRC, Subgroup.mem_bot] at hmem
    exact hmem
  have hRab : CFSG.Assembly.IsElemAbelian 2 R := by
    refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, hRsq⟩
    have hx := hRsq x x.2
    have hy := hRsq y y.2
    have hxy := hRsq _ (R.mul_mem x.2 y.2)
    have e1 : (x : G) * x = 1 := by rw [← pow_two]; exact hx
    have e2 : (y : G) * y = 1 := by rw [← pow_two]; exact hy
    have e3 : (x : G) * y * ((x : G) * y) = 1 := by
      rw [← pow_two]
      exact hxy
    have i1 : (x : G)⁻¹ = x := inv_eq_of_mul_eq_one_right e1
    have i2 : (y : G)⁻¹ = y := inv_eq_of_mul_eq_one_right e2
    calc ((x * y : R) : G) = (x : G) * y := rfl
      _ = ((x : G) * y)⁻¹ := eq_inv_of_mul_eq_one_left e3
      _ = (y : G) * x := by rw [mul_inv_rev, i1, i2]
  have hRU : R ∈ fourGroups E := mem_fourGroups_iff.mpr ⟨hER, hRab, hcard⟩
  have hCE : E ⊓ Subgroup.centralizer (R : Set G) = E ⊓ Subgroup.centralizer (T : Set G) := by
    apply le_antisymm
    · rintro e ⟨heE, heR⟩
      refine ⟨heE, Subgroup.mem_centralizer_iff.mpr fun t ht => ?_⟩
      obtain ⟨r, hr, z, hz, rfl⟩ := hdecT t ht
      have hre : e * r * e⁻¹ = r := by
        rw [(Subgroup.mem_centralizer_iff.mp heR r hr).symm, mul_inv_cancel_right]
      have hmem : (r * z)⁻¹ * (e * (r * z) * e⁻¹) ∈ T ⊓ C' := by
        refine ⟨T.mul_mem (T.inv_mem ht) ((Subgroup.mem_normalizer_iff.mp (hEN heE) _).mp ht), ?_⟩
        rw [show (r * z)⁻¹ * (e * (r * z) * e⁻¹) = z⁻¹ * (r⁻¹ * (e * r * e⁻¹)) * (e * z * e⁻¹) by
          group, hre, inv_mul_cancel, mul_one]
        exact hmemC hz ((Subgroup.mem_normalizer_iff.mp (hEC heE) z).mp hz)
      rw [hTC, Subgroup.mem_bot] at hmem
      have h1 := eq_of_inv_mul_eq_one hmem
      calc r * z * e = e * (r * z) * e⁻¹ * e := by rw [← h1]
        _ = e * (r * z) := by group
    · rintro e ⟨heE, heT⟩
      refine ⟨heE, Subgroup.mem_centralizer_iff.mpr fun r hr => ?_⟩
      obtain ⟨t, ht, z, hz, rfl⟩ := hdecR r hr
      have hte : e * t * e⁻¹ = t := by
        rw [(Subgroup.mem_centralizer_iff.mp heT t ht).symm, mul_inv_cancel_right]
      have hmem : (t * z)⁻¹ * (e * (t * z) * e⁻¹) ∈ R ⊓ C' := by
        refine ⟨R.mul_mem (R.inv_mem hr) ((Subgroup.mem_normalizer_iff.mp (hER heE) _).mp hr), ?_⟩
        rw [show (t * z)⁻¹ * (e * (t * z) * e⁻¹) = z⁻¹ * (t⁻¹ * (e * t * e⁻¹)) * (e * z * e⁻¹) by
          group, hte, inv_mul_cancel, mul_one]
        exact hmemC hz ((Subgroup.mem_normalizer_iff.mp (hEC heE) z).mp hz)
      rw [hRC, Subgroup.mem_bot] at hmem
      have h1 := eq_of_inv_mul_eq_one hmem
      calc t * z * e = e * (t * z) * e⁻¹ * e := by rw [← h1]
        _ = e * (t * z) := by group
  have hRm : R ∈ fourGroupsMinus E := by
    rcases mem_fourGroupsPlus_or_mem_fourGroupsMinus hE3 hRU with hp | ⟨hm, -⟩
    · exfalso
      have hER' : E ≤ Subgroup.centralizer (R : Set G) := (mem_fourGroupsPlus_iff.mp hp).2
      have hET : E ≤ Subgroup.centralizer (T : Set G) := by
        intro e he
        have h1 : e ∈ E ⊓ Subgroup.centralizer (T : Set G) := hCE ▸ ⟨he, hER' he⟩
        exact h1.2
      have hTp : T ∈ fourGroupsPlus E := mem_fourGroupsPlus_iff.mpr ⟨hT.1, hET⟩
      exact Set.disjoint_left.mp (disjoint_fourGroupsPlus_fourGroupsMinus E) hTp hT
    · exact hm
  have hRθ : R ⊓ inSubgroup (aschbacherSolvableCore 3) L' = ⊥ :=
    le_bot_iff.mp ((inf_le_inf_left R (theta_le_thetaQuotCentralizer L')).trans hRC.le)
  have hR1 : R ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcard
    omega
  have hRnθ : ¬ ⁅R, E⁆ ≤ inSubgroup (aschbacherSolvableCore 3) L' := by
    rw [← hRm.2]
    intro h
    apply hR1
    rw [eq_bot_iff, ← hRθ]
    exact le_inf le_rfl h
  refine ⟨c', hc'A, hc'1, L', hL', hCA',
    ⟨mem_thetaComponentFamily_iff.mpr ⟨c', hc'E, hc'1, hL'c⟩, R, hR, hRnθ⟩,
    R, hRm, hRL', hRθ, hCE⟩

end Certs

end CFSG.RankThree.PartTwo.Sec6
