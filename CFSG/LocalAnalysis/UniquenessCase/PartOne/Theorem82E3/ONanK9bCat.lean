module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanKFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L27.SmallLookup
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitC9a
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Proving.ONThreeCent
public import CFSG.Sporadic.Schreier.SteinbergBIONOuterTwo
public import CFSG.Sporadic.FischerOddCore.AlmostSimple
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Proving.ONRigidInputs
public import CFSG.LargeExtraspecial.S12Seven

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan

open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsSpor IsAlt)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

private def check360 (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n p f o : ℕ) : Bool :=
  decide (o = 360 → t = .PSL ∧ n = 2 ∧ p ^ f = 9)

private theorem lieSearch_360 :
    CFSG.EvenSmallLie.Child3.lieSearchV
      CFSG.EvenSporadicStandard.HNRecog.Harada.L27.lookupPrimes 348364800 check360 = true := by
  decide +kernel

private theorem lieOrd_eq_360 {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n p f : ℕ}
    (ht : t ∈ CFSG.EvenSmallLie.CatalogOrders.searchTags) (hp : Nat.Prime p) (hf : 1 ≤ f)
    (hn : CFSG.EvenSmallLie.CatalogOrders.lieMin t ≤ n)
    (hn0 : CFSG.EvenSmallLie.CatalogOrders.lieMin t = 0 → n = 0)
    (hnB : n ≤ CFSG.EvenSmallLie.CatalogOrders.lieExp t n + 1)
    (hadm : CFSG.EvenSmallLie.CatalogOrders.lieAdm t p f = true)
    (hord : CFSG.EvenSmallLie.CatalogOrders.lieOrd t n (p ^ f) = 360) :
    t = .PSL ∧ n = 2 ∧ p ^ f = 9 := by
  have hdvd : CFSG.EvenSmallLie.CatalogOrders.lieOrd t n (p ^ f) ∣ 348364800 := by
    rw [hord]
    norm_num
  have hC := CFSG.EvenSmallLie.Child3.lieSearchV_sound
    CFSG.EvenSporadicStandard.HNRecog.Harada.L27.primes_lookup lieSearch_360
    ht hp hf hn hn0 hnB hadm hdvd
  simp only [check360, decide_eq_true_eq] at hC
  exact hC hord

section K9Certificates

private theorem catalog_card_360_isAlt {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hcat : CFSG.Blueprint.Catalog S) (hnonab : ∃ a b : S, a * b ≠ b * a)
    (hcard : Nat.card S = 360) : IsAlt S 6 := by
  rcases CFSG.EvenSmallLie.Child3.catalog_model_cases hcat hnonab with
    ⟨n, hn, ⟨e⟩⟩ | ⟨t, n, p, f, ht, hp, hf, hmin, hmin0, hB, hadm, hcardLie, hmodel⟩ |
      ⟨p, f, hRee⟩ | ⟨p, f, hTits⟩ | ⟨s, ⟨e⟩⟩
  ·
    haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
    have hcardAlt : Nat.card S = n.factorial / 2 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    have h360 : n.factorial / 2 = 360 := by rw [← hcardAlt, hcard]
    have hn6 : n = 6 := by
      have hle6 : n ≤ 6 := by
        by_contra hle
        push Not at hle
        have h7 : 7 ≤ n := by omega
        have hfac : Nat.factorial 7 ≤ Nat.factorial n := Nat.factorial_le h7
        have hdiv : Nat.factorial 7 / 2 ≤ Nat.factorial n / 2 := Nat.div_le_div_right hfac
        norm_num at hdiv
        omega
      interval_cases n
      · norm_num at h360
      · rfl
    rw [hn6] at e
    exact ⟨e⟩
  ·
    have hL : CFSG.EvenSmallLie.CatalogOrders.lieOrd t n (p ^ f) = 360 := by
      rw [← hcardLie, hcard]
    obtain ⟨rfl, rfl, hq⟩ := lieOrd_eq_360 ht hp hf hmin hmin0 hB hadm hL
    have hm : CFSG.Blueprint.LieModel S .PSL 2 p f := hmodel
    exact (CFSG.ComponentClassification.HarrisLit.C9.card_eq_and_equiv_of_lieModel_nine hm hq).2
  ·
    have h13 : 13 ∣ Nat.card S :=
      CFSG.EvenSmallLie.CatalogOrders.thirteen_dvd_card_of_reeTitsModel_twistedF4 hRee
    rw [hcard] at h13
    norm_num at h13
  ·
    have h13 : 13 ∣ Nat.card S :=
      CFSG.EvenSmallLie.CatalogOrders.thirteen_dvd_card_of_reeTitsModel_Tits hTits
    rw [hcard] at h13
    norm_num at h13
  ·
    obtain ⟨-, -, hc⟩ := CFSG.EvenSmallLie.Child3.sporadic_cases (T := S) (N := 6480) e
      (by rw [hcard]; norm_num) (by decide) (by decide)
    rw [hcard] at hc
    have h360 : CFSG.EvenSmallLie.Child3.sporadicCard s = 360 := hc.symm
    cases s <;>
      norm_num [CFSG.EvenSmallLie.Child3.sporadicCard, CFSG.Open.monsterBabyOrder] at h360

theorem K9bCat_holds :
    ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      CFSG.Blueprint.Catalog S → Nat.card S ∣ 6480 → IsAlt S 5 ∨ IsAlt S 6 := by
  intro S _ _ hsimple hnonab hcat hdvd
  have hle : Nat.card S ≤ 16200 := by
    have h6480 : Nat.card S ≤ 6480 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  have hmem : Nat.card S ∈ CFSG.EvenSporadicStandard.HNRecog.Harada.L27.smallSimpleOrders :=
    CFSG.EvenSporadicStandard.HNRecog.Harada.L27.smallSimpleLookup_of_certificates
      S hcat hnonab (hdvd.trans (by norm_num)) hle
  simp only [CFSG.EvenSporadicStandard.HNRecog.Harada.L27.smallSimpleOrders, List.mem_cons,
    List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h | h | h | h
  · left
    exact CFSG.BenderSuzuki.nonempty_mulEquiv_alternatingGroup_five h
  · exfalso
    rw [h] at hdvd
    norm_num at hdvd
  · right
    exact catalog_card_360_isAlt hcat hnonab h
  · exfalso
    rw [h] at hdvd
    norm_num at hdvd
  · exfalso
    rw [h] at hdvd
    norm_num at hdvd
  · exfalso
    rw [h] at hdvd
    norm_num at hdvd

end K9Certificates

section K6

private theorem orderOf_mk'_center_eq_three {Y : Type*} [Group Y] {x : Y}
    (hx3 : orderOf x = 3) (hxZ : x ∉ Subgroup.center Y) :
    orderOf (QuotientGroup.mk' (Subgroup.center Y) x) = 3 := by
  refine orderOf_eq_prime ?_ ?_
  · rw [← map_pow, ← hx3, pow_orderOf_eq_one, map_one]
  · intro h
    exact hxZ ((QuotientGroup.eq_one_iff x).mp h)

private theorem conj_mul_inv_not_mem_center {G : Type*} [Group G] {x g : G}
    (hx : x ∉ Subgroup.center G) : g * x * g⁻¹ ∉ Subgroup.center G := by
  intro h
  apply hx
  have h' : x = g⁻¹ * (g * x * g⁻¹) * g := by group
  rw [h']
  have hnorm : (Subgroup.center G).Normal := inferInstance
  simpa using hnorm.conj_mem _ h g⁻¹

private theorem exists_conj_eq_on_center_quotient
    {Y : Type} [Group Y]
    (e : Y ⧸ Subgroup.center Y ≃* CFSG.Blueprint.NativeSporadic.ON)
    {x y : Y} (hx3 : orderOf x = 3) (hxZ : x ∉ Subgroup.center Y)
    (hy3 : orderOf y = 3) (hyZ : y ∉ Subgroup.center Y) :
    ∃ g : Y, orderOf (g * x * g⁻¹) = 3 ∧ g * x * g⁻¹ ∉ Subgroup.center Y ∧
      (g * x * g⁻¹)⁻¹ * y ∈ Subgroup.center Y := by
  let π : Y →* Y ⧸ Subgroup.center Y := QuotientGroup.mk' (Subgroup.center Y)
  have hxbar3 : orderOf (π x) = 3 := orderOf_mk'_center_eq_three hx3 hxZ
  have hybar3 : orderOf (π y) = 3 := orderOf_mk'_center_eq_three hy3 hyZ
  have hxON : orderOf (e (π x)) = 3 := by rw [MulEquiv.orderOf_eq, hxbar3]
  have hyON : orderOf (e (π y)) = 3 := by rw [MulEquiv.orderOf_eq, hybar3]
  obtain ⟨k, hk⟩ := CFSG.RankThree.Native.onThree_fusion
    (x := e (π x)) (y := e (π y)) hxON hyON
  have hkq : e.symm k * π x * (e.symm k)⁻¹ = π y := by
    apply e.injective
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply, hk]
  obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective (Subgroup.center Y) (e.symm k)
  refine ⟨g, ?_, ?_, ?_⟩
  · have h := MulEquiv.orderOf_eq (MulAut.conj g) x
    rw [MulAut.conj_apply] at h
    exact h.trans hx3
  · exact conj_mul_inv_not_mem_center hxZ
  · have hconjbar : π (g * x * g⁻¹) = π y := by
      have hmap : π (g * x * g⁻¹) = e.symm k * π x * (e.symm k)⁻¹ := by
        rw [map_mul, map_mul, map_inv, hg]
      exact hmap.trans hkq
    have h := (QuotientGroup.eq).mp hconjbar
    simpa using h

private theorem card_comap_centralizer_mk'_eq_9720
    {Y : Type} [Group Y]
    [Finite Y] (e : Y ⧸ Subgroup.center Y ≃* CFSG.Blueprint.NativeSporadic.ON)
    {x : Y} (hx3 : orderOf x = 3) (hxZ : x ∉ Subgroup.center Y)
    (hZcard : Nat.card (Subgroup.center Y) = 3)
    (hC0card : Nat.card (Subgroup.centralizer ({x} : Set Y)) = 3240) :
    Nat.card (Subgroup.comap (QuotientGroup.mk' (Subgroup.center Y))
      (Subgroup.centralizer
        ({(QuotientGroup.mk' (Subgroup.center Y)) x} :
          Set (Y ⧸ Subgroup.center Y)))) = 9720 := by
  let Z : Subgroup Y := Subgroup.center Y
  let π : Y →* Y ⧸ Z := QuotientGroup.mk' Z
  let C0 : Subgroup Y := Subgroup.centralizer ({x} : Set Y)
  let Cbar : Subgroup (Y ⧸ Z) := Subgroup.centralizer ({π x} : Set (Y ⧸ Z))
  let Cstar : Subgroup Y := Cbar.comap π
  have hxbar3 : orderOf (π x) = 3 := orderOf_mk'_center_eq_three hx3 hxZ
  have hCbarcard : Nat.card Cbar = 3240 :=
    CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Proving.card_centralizer_three_ON
      e hxbar3
  have hC0le : C0 ≤ Cstar := by
    intro c hc
    rw [Subgroup.mem_comap]
    rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
    rw [← map_mul, ← map_mul, hc]
  have hYcard : Nat.card Y = 3 * Nat.card (Y ⧸ Z) := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup Z
    rw [show Nat.card Z = 3 from hZcard] at h
    rw [h]
    ring
  have h1 : Nat.card Cstar * Cstar.index = Nat.card Y := Subgroup.card_mul_index Cstar
  have h2 : Nat.card Cbar * Cbar.index = Nat.card (Y ⧸ Z) :=
    Subgroup.card_mul_index Cbar
  have hidx : Cstar.index = Cbar.index :=
    Subgroup.index_comap_of_surjective Cbar (QuotientGroup.mk'_surjective Z)
  have hindexpos : 0 < Cbar.index := by
    have hquot : Nat.card (Y ⧸ Z) ≠ 0 :=
      Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩
    by_contra h0
    have hz : Cbar.index = 0 := Nat.eq_zero_of_not_pos h0
    rw [hz, mul_zero] at h2
    exact hquot h2.symm
  have hCstarcard : Nat.card Cstar = 9720 := by
    have hmain : Nat.card Cstar * Cbar.index = (3 * Nat.card Cbar) * Cbar.index := by
      calc Nat.card Cstar * Cbar.index
          = Nat.card Cstar * Cstar.index := by rw [hidx]
        _ = Nat.card Y := h1
        _ = 3 * Nat.card (Y ⧸ Z) := hYcard
        _ = 3 * (Nat.card Cbar * Cbar.index) := by rw [h2]
        _ = (3 * Nat.card Cbar) * Cbar.index := by ring
    have hcancel := Nat.mul_right_cancel hindexpos hmain
    rw [hCbarcard] at hcancel
    norm_num at hcancel ⊢
    exact hcancel
  exact hCstarcard

private theorem stabilizer_eq_centralizer_subgroupOf {Y : Type*} [Group Y]
    {C : Subgroup Y} [MulAction C Y] {x : Y}
    (hsmul : ∀ c : C, c • x = (c : Y) * x * (c : Y)⁻¹) :
    MulAction.stabilizer C x = (Subgroup.centralizer ({x} : Set Y)).subgroupOf C := by
  ext c
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf,
    Subgroup.mem_centralizer_singleton_iff]
  rw [hsmul]
  constructor
  · intro h
    have h' : (↑c : Y) * x * (↑c)⁻¹ = x := by simpa using h
    calc (c : Y) * x = ((c : Y) * x * (c : Y)⁻¹) * (c : Y) := by group
      _ = x * (c : Y) := by rw [h']
  · intro h
    have h' : (↑c : Y) * x = x * (↑c) := by simpa using h
    calc (c : Y) * x * (c : Y)⁻¹ = (x * (c : Y)) * (c : Y)⁻¹ := by rw [h']
      _ = x := by group

private theorem orbit_ncard_eq_three_of_card_stabilizer {Y : Type*} [Group Y]
    {C : Subgroup Y} [MulAction C Y] {x : Y}
    (hstabcard : Nat.card (MulAction.stabilizer C x) = 3240)
    (hCcard : Nat.card C = 9720) : (MulAction.orbit C x).ncard = 3 := by
  have hindex := MulAction.index_stabilizer C x
  have hcard := Subgroup.card_mul_index (MulAction.stabilizer C x)
  rw [hstabcard, hCcard] at hcard
  have hcard' : 3240 * (MulAction.stabilizer C x).index = 3240 * 3 := by
    simpa using hcard
  have hidx3 : (MulAction.stabilizer C x).index = 3 :=
    Nat.mul_left_cancel (by norm_num) hcard'
  rw [hidx3] at hindex
  exact hindex.symm

private theorem centralizer_le_comap_centralizer_mk' {Y : Type*} [Group Y] {x : Y} :
    Subgroup.centralizer ({x} : Set Y) ≤
      (Subgroup.centralizer ({(QuotientGroup.mk' (Subgroup.center Y)) x} :
        Set (Y ⧸ Subgroup.center Y))).comap (QuotientGroup.mk' (Subgroup.center Y)) := by
  intro c hc
  rw [Subgroup.mem_comap]
  rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
  rw [← map_mul, ← map_mul, hc]

private theorem orbit_subset_mul_center {Y : Type*} [Group Y] {C : Subgroup Y}
    [MulAction C Y] {x : Y}
    (hsmul : ∀ c : C, c • x = (c : Y) * x * (c : Y)⁻¹)
    (hC : C ≤ Subgroup.comap (QuotientGroup.mk' (Subgroup.center Y))
      (Subgroup.centralizer
        ({(QuotientGroup.mk' (Subgroup.center Y)) x} : Set (Y ⧸ Subgroup.center Y)))) :
    MulAction.orbit C x ⊆ (fun z : Subgroup.center Y => x * (z : Y)) '' Set.univ := by
  intro u hu
  rw [MulAction.mem_orbit_iff] at hu
  obtain ⟨c, rfl⟩ := hu
  rw [hsmul]
  have hcC : (c : Y) ∈ C := c.2
  have hcbar : (QuotientGroup.mk' (Subgroup.center Y)) (c : Y) ∈
      Subgroup.centralizer
        ({(QuotientGroup.mk' (Subgroup.center Y)) x} : Set (Y ⧸ Subgroup.center Y)) :=
    hC hcC
  have hcomm : (QuotientGroup.mk' (Subgroup.center Y)) (c : Y) *
        (QuotientGroup.mk' (Subgroup.center Y)) x =
      (QuotientGroup.mk' (Subgroup.center Y)) x *
        (QuotientGroup.mk' (Subgroup.center Y)) (c : Y) :=
    Subgroup.mem_centralizer_singleton_iff.mp hcbar
  have hz : ((c : Y) * x * (c : Y)⁻¹) * x⁻¹ ∈ Subgroup.center Y := by
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply]
    simp only [map_mul, map_inv]
    calc (QuotientGroup.mk' (Subgroup.center Y)) (c : Y) *
          (QuotientGroup.mk' (Subgroup.center Y)) x *
          ((QuotientGroup.mk' (Subgroup.center Y)) (c : Y))⁻¹ *
          ((QuotientGroup.mk' (Subgroup.center Y)) x)⁻¹
        = ((QuotientGroup.mk' (Subgroup.center Y)) x *
          (QuotientGroup.mk' (Subgroup.center Y)) (c : Y)) *
          ((QuotientGroup.mk' (Subgroup.center Y)) (c : Y))⁻¹ *
          ((QuotientGroup.mk' (Subgroup.center Y)) x)⁻¹ := by rw [hcomm]
      _ = 1 := by group
  refine ⟨⟨((c : Y) * x * (c : Y)⁻¹) * x⁻¹, hz⟩, Set.mem_univ _, ?_⟩
  have hcent : x * (((c : Y) * x * (c : Y)⁻¹) * x⁻¹) =
      (((c : Y) * x * (c : Y)⁻¹) * x⁻¹) * x := by
    exact Subgroup.mem_center_iff.mp hz x
  change x * (((c : Y) * x * (c : Y)⁻¹) * x⁻¹) = (c : Y) * x * (c : Y)⁻¹
  rw [hcent]
  group

private theorem exists_smul_eq_mul_of_ncard_orbit_eq {Y : Type*} [Group Y] [Finite Y]
    {C : Subgroup Y} [MulAction C Y] {x : Y}
    (hsmul : ∀ c : C, c • x = (c : Y) * x * (c : Y)⁻¹)
    (hC : C ≤ Subgroup.comap (QuotientGroup.mk' (Subgroup.center Y))
      (Subgroup.centralizer
        ({(QuotientGroup.mk' (Subgroup.center Y)) x} : Set (Y ⧸ Subgroup.center Y))))
    (hZcard : Nat.card (Subgroup.center Y) = 3)
    (horbit : (MulAction.orbit C x).ncard = 3) (z : Subgroup.center Y) :
    ∃ c : C, c • x = x * (z : Y) := by
  let img : Set Y := (fun z : Subgroup.center Y => x * (z : Y)) '' Set.univ
  have himgcard : img.ncard = 3 := by
    have hinj : Function.Injective (fun z : Subgroup.center Y => x * (z : Y)) := by
      intro a b h
      exact Subtype.ext (mul_left_cancel h)
    rw [Set.ncard_image_of_injective Set.univ hinj, Set.ncard_univ]
    exact hZcard
  have hsub : MulAction.orbit C x ⊆ img := orbit_subset_mul_center hsmul hC
  have himgeq : MulAction.orbit C x = img := by
    refine Set.eq_of_subset_of_ncard_le hsub ?_
    rw [himgcard, horbit]
  have hzmem : x * (z : Y) ∈ MulAction.orbit C x := by
    rw [himgeq]
    exact ⟨z, Set.mem_univ z, rfl⟩
  exact MulAction.mem_orbit_iff.mp hzmem

theorem K6_of_K2
    (hK2 : K2ONanCentralizer) : K6ONanClasses := by
  intro Y _ _ hCover x y hx3 hxZ hy3 hyZ
  have hcov : CFSG.LocalAnalysis.UniquenessCase.UCK.ThreeCover
      (fun Y _ => IsSpor Y .ONan) Y := hCover
  obtain ⟨-, hZcard, hspor⟩ := hCover
  let Z : Subgroup Y := Subgroup.center Y
  let π : Y →* Y ⧸ Z := QuotientGroup.mk' Z
  obtain ⟨eC⟩ := hspor
  let e : (Y ⧸ Z) ≃* CFSG.Blueprint.NativeSporadic.ON := eC
  obtain ⟨g, hx'3, hx'Z, hz⟩ := exists_conj_eq_on_center_quotient e hx3 hxZ hy3 hyZ
  let x' : Y := g * x * g⁻¹
  let C0 : Subgroup Y := Subgroup.centralizer ({x'} : Set Y)
  have hC0card : Nat.card C0 = 3240 := (hK2 Y hcov x' hx'3 hx'Z).1
  let Cstar : Subgroup Y := (Subgroup.centralizer ({π x'} : Set (Y ⧸ Z))).comap π
  have hCstarcard : Nat.card Cstar = 9720 :=
    card_comap_centralizer_mk'_eq_9720 e hx'3 hx'Z hZcard hC0card
  letI : MulAction Cstar Y :=
    MulAction.compHom Y ((ConjAct.toConjAct (G := Y)).toMonoidHom.comp Cstar.subtype)
  have hsmul : ∀ c : Cstar, c • x' = (c : Y) * x' * (c : Y)⁻¹ := fun c => rfl
  have hC0le : C0 ≤ Cstar := centralizer_le_comap_centralizer_mk'
  have hstabcard : Nat.card (MulAction.stabilizer Cstar x') = 3240 := by
    rw [stabilizer_eq_centralizer_subgroupOf hsmul,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hC0le).toEquiv, hC0card]
  have horbitcard : (MulAction.orbit Cstar x').ncard = 3 :=
    orbit_ncard_eq_three_of_card_stabilizer hstabcard hCstarcard
  let z0 : Z := ⟨x'⁻¹ * y, hz⟩
  obtain ⟨c, hc⟩ := exists_smul_eq_mul_of_ncard_orbit_eq hsmul le_rfl hZcard
    horbitcard z0
  refine ⟨(c : Y) * g, ?_⟩
  have hc' : (c : Y) * x' * (c : Y)⁻¹ = x' * (z0 : Y) := by
    rw [← hsmul c]
    exact hc
  calc ((c : Y) * g) * x * ((c : Y) * g)⁻¹
      = (c : Y) * (g * x * g⁻¹) * (c : Y)⁻¹ := by group
    _ = (c : Y) * x' * (c : Y)⁻¹ := by rw [show x' = g * x * g⁻¹ from rfl]
    _ = x' * (z0 : Y) := hc'
    _ = x' * (x'⁻¹ * y) := by rfl
    _ = y := by group

end K6

section K4ord

private theorem center_eq_bot_of_isSpor_onan
    {Y : Type} [Group Y] (hY : IsSpor Y .ONan) : Subgroup.center Y = ⊥ := by
  obtain ⟨eY⟩ := hY
  exact CFSG.Sporadic.FischerOddCore.center_eq_bot_of_mulEquiv eY
    (CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Proving.center_ON_eq_bot)

private theorem injective_conj_of_center_eq_bot {Y : Type*} [Group Y]
    (hZY : Subgroup.center Y = ⊥) :
    Function.Injective (MulAut.conj : Y →* MulAut Y) := by
  rw [injective_iff_map_eq_one]
  intro y hy
  have hyZ : y ∈ Subgroup.center Y := by
    rw [Subgroup.mem_center_iff]
    intro h
    have h2 : y * h * y⁻¹ = h := by
      have hc := congrArg (fun φ : MulAut Y => φ h) hy
      simpa only [MulAut.conj_apply, MulAut.one_apply] using hc
    calc h * y = (y * h * y⁻¹) * y := by rw [h2]
      _ = y * h := by group
  rw [hZY] at hyZ
  exact Subgroup.mem_bot.1 hyZ

private theorem outer_order_dvd_two_of_isSpor_onan
    {Y : Type} [Group Y] (hY : IsSpor Y .ONan) : Nat.card (Outer Y) ∣ 2 :=
  CFSG.Sporadic.SteinbergBI.cti_on_outer_order_divides_two hY

private theorem mk'_inner_eq_one_of_orderOf_eq_three {Y : Type*} [Group Y] [Finite Y]
    {σ : MulAut Y} (hσ3 : orderOf σ = 3) (hOut : Nat.card (Outer Y) ∣ 2) :
    QuotientGroup.mk' ((MulAut.conj : Y →* MulAut Y).range) σ = 1 := by
  let Inn : Subgroup (MulAut Y) := (MulAut.conj : Y →* MulAut Y).range
  let q : MulAut Y →* Outer Y := QuotientGroup.mk' Inn
  have hq3 : (q σ) ^ 3 = 1 := by
    rw [← map_pow]
    have : σ ^ 3 = 1 := by simpa [hσ3] using pow_orderOf_eq_one σ
    rw [this, map_one]
  have hq_dvd3 : orderOf (q σ) ∣ 3 := orderOf_dvd_of_pow_eq_one hq3
  have hq_dvdOut : orderOf (q σ) ∣ Nat.card (Outer Y) := by
    rw [← Nat.card_zpowers]
    exact Subgroup.card_subgroup_dvd_card (Subgroup.zpowers (q σ))
  have hq1 : q σ = 1 := by
    have hgcd : orderOf (q σ) ∣ Nat.gcd 3 (Nat.card (Outer Y)) :=
      Nat.dvd_gcd hq_dvd3 hq_dvdOut
    have hg1 : Nat.gcd 3 (Nat.card (Outer Y)) = 1 := by
      have hle : Nat.card (Outer Y) ≤ 2 := Nat.le_of_dvd (by norm_num) hOut
      have hpos : 0 < Nat.card (Outer Y) := Nat.card_pos
      interval_cases h : Nat.card (Outer Y) <;> norm_num
    rw [hg1] at hgcd
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hgcd)
  exact hq1

private theorem exists_orderOf_eq_three_of_mem_inner {Y : Type*} [Group Y]
    {σ : MulAut Y} (hinj : Function.Injective (MulAut.conj : Y →* MulAut Y))
    (hσ3 : orderOf σ = 3) (hσ : σ ∈ (MulAut.conj : Y →* MulAut Y).range) :
    ∃ x : Y, MulAut.conj x = σ ∧ orderOf x = 3 := by
  obtain ⟨x, hx⟩ := hσ
  have hx3 : orderOf x = 3 := by
    have hx3pow : x ^ 3 = 1 := by
      apply hinj
      rw [map_pow, hx]
      simpa [hσ3] using pow_orderOf_eq_one σ
    have hxne : x ≠ 1 := by
      intro hx1
      have hσ1 : σ = 1 := by rw [← hx, hx1, map_one]
      have : orderOf σ = 1 := by rw [hσ1]; exact orderOf_one
      omega
    exact orderOf_eq_prime hx3pow hxne
  exact ⟨x, hx, hx3⟩

private theorem comap_inf_centralizer_conj_eq_centralizer {Y : Type*} [Group Y]
    {H : Subgroup (MulAut Y)} {x : Y} {σ : MulAut Y}
    (hinj : Function.Injective (MulAut.conj : Y →* MulAut Y))
    (hx : MulAut.conj x = σ) (hInn : (MulAut.conj : Y →* MulAut Y).range ≤ H) :
    (H ⊓ Subgroup.centralizer ({σ} : Set (MulAut Y))).comap
        (MulAut.conj : Y →* MulAut Y) =
      Subgroup.centralizer ({x} : Set Y) := by
  ext y
  rw [Subgroup.mem_comap, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨-, hc⟩
    rw [← hx] at hc
    have hconj : MulAut.conj (y * x * y⁻¹) = MulAut.conj x := by
      calc MulAut.conj (y * x * y⁻¹)
          = MulAut.conj y * MulAut.conj x * (MulAut.conj y)⁻¹ := by
            rw [map_mul, map_mul, map_inv]
        _ = (MulAut.conj x * MulAut.conj y) * (MulAut.conj y)⁻¹ := by rw [hc]
        _ = MulAut.conj x := by group
    have hyx : y * x * y⁻¹ = x := hinj hconj
    calc y * x = (y * x * y⁻¹) * y := by group
      _ = x * y := by rw [hyx]
  · intro hc
    constructor
    · exact hInn ⟨y, rfl⟩
    · rw [← hx]
      calc MulAut.conj y * MulAut.conj x = MulAut.conj (y * x) := by rw [map_mul]
        _ = MulAut.conj (x * y) := by rw [hc]
        _ = MulAut.conj x * MulAut.conj y := by rw [map_mul]

private theorem card_inf_centralizer_conj_eq_3240 {Y : Type*} [Group Y] [Finite Y]
    {H : Subgroup (MulAut Y)} {x : Y} {σ : MulAut Y}
    (hinj : Function.Injective (MulAut.conj : Y →* MulAut Y))
    (hx : MulAut.conj x = σ) (hInn : (MulAut.conj : Y →* MulAut Y).range ≤ H)
    (hC0card : Nat.card (Subgroup.centralizer ({x} : Set Y)) = 3240) :
    Nat.card ↥(H ⊓ Subgroup.centralizer ({σ} : Set (MulAut Y)) ⊓
      (MulAut.conj : Y →* MulAut Y).range) = 3240 := by
  have hpre := comap_inf_centralizer_conj_eq_centralizer hinj hx hInn
  have hmap : (Subgroup.centralizer ({x} : Set Y)).map
      (MulAut.conj : Y →* MulAut Y) =
      (H ⊓ Subgroup.centralizer ({σ} : Set (MulAut Y)) ⊓
        (MulAut.conj : Y →* MulAut Y).range) := by
    rw [← hpre, Subgroup.map_comap_eq, inf_comm]
  have hmapcard : Nat.card ((Subgroup.centralizer ({x} : Set Y)).map
      (MulAut.conj : Y →* MulAut Y)) =
      Nat.card (Subgroup.centralizer ({x} : Set Y)) :=
    (Nat.card_congr (Subgroup.equivMapOfInjective _ _ hinj).toEquiv).symm
  rw [← hmap, hmapcard, hC0card]

private theorem card_ker_mk'_comp_subtype_eq_3240 {Y : Type*} [Group Y] [Finite Y]
    {H : Subgroup (MulAut Y)} {x : Y} {σ : MulAut Y}
    (hinj : Function.Injective (MulAut.conj : Y →* MulAut Y))
    (hx : MulAut.conj x = σ) (hInn : (MulAut.conj : Y →* MulAut Y).range ≤ H)
    (hC0card : Nat.card (Subgroup.centralizer ({x} : Set Y)) = 3240) :
    Nat.card (MonoidHom.ker
      ((QuotientGroup.mk' ((MulAut.conj : Y →* MulAut Y).range)).comp
        (H ⊓ Subgroup.centralizer ({σ} : Set (MulAut Y))).subtype)) = 3240 := by
  let Inn : Subgroup (MulAut Y) := (MulAut.conj : Y →* MulAut Y).range
  let Cσ : Subgroup (MulAut Y) := H ⊓ Subgroup.centralizer ({σ} : Set (MulAut Y))
  let f : Cσ →* Outer Y := (QuotientGroup.mk' Inn).comp Cσ.subtype
  have hcardInn : Nat.card ↥(Cσ ⊓ Inn) = 3240 :=
    card_inf_centralizer_conj_eq_3240 hinj hx hInn hC0card
  have hker : f.ker = ((Cσ ⊓ Inn : Subgroup (MulAut Y))).subgroupOf Cσ := by
    ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro ha
      exact ⟨a.2, (QuotientGroup.eq_one_iff (a : MulAut Y)).mp ha⟩
    · rintro ⟨-, hin⟩
      exact (QuotientGroup.eq_one_iff (a : MulAut Y)).mpr hin
  change Nat.card f.ker = 3240
  rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv, hcardInn]

private theorem card_inf_centralizer_dvd_6480 {Y : Type*} [Group Y] [Finite Y]
    {H : Subgroup (MulAut Y)} {σ : MulAut Y} (hOut : Nat.card (Outer Y) ∣ 2)
    (hkercard : Nat.card (MonoidHom.ker
      ((QuotientGroup.mk' ((MulAut.conj : Y →* MulAut Y).range)).comp
        (H ⊓ Subgroup.centralizer ({σ} : Set (MulAut Y))).subtype)) = 3240) :
    Nat.card ↥(H ⊓ Subgroup.centralizer ({σ} : Set (MulAut Y))) ∣ 6480 := by
  let Inn : Subgroup (MulAut Y) := (MulAut.conj : Y →* MulAut Y).range
  let Cσ : Subgroup (MulAut Y) := H ⊓ Subgroup.centralizer ({σ} : Set (MulAut Y))
  let f : Cσ →* Outer Y := (QuotientGroup.mk' Inn).comp Cσ.subtype
  have hkercard' : Nat.card f.ker = 3240 := hkercard
  have hrange : Nat.card f.range ∣ 2 :=
    (Subgroup.card_subgroup_dvd_card f.range).trans hOut
  change Nat.card Cσ ∣ 6480
  have h := Subgroup.card_ker_mul_card_range f
  rw [hkercard'] at h
  obtain ⟨c, hc⟩ := hrange
  rw [← h]
  refine ⟨c, ?_⟩
  calc 6480 = 3240 * 2 := by norm_num
    _ = 3240 * (Nat.card f.range * c) := by rw [hc]
    _ = (3240 * Nat.card f.range) * c := by ring

theorem K4ord_holds :
    ∀ (Y : Type) [Group Y] [Finite Y], IsSpor Y .ONan →
      ∀ H : Subgroup (MulAut Y), (MulAut.conj : Y →* MulAut Y).range ≤ H →
        ∀ σ ∈ H, orderOf σ = 3 →
          Nat.card ↥(H ⊓ Subgroup.centralizer ({σ} : Set (MulAut Y))) ∣ 6480 := by
  intro Y _ _ hY H hInn σ hσH hσ3
  let inn : Y →* MulAut Y := MulAut.conj
  let Inn : Subgroup (MulAut Y) := inn.range
  have hZY : Subgroup.center Y = ⊥ := center_eq_bot_of_isSpor_onan hY
  have hinj : Function.Injective inn := injective_conj_of_center_eq_bot hZY
  have hOut : Nat.card (Outer Y) ∣ 2 := outer_order_dvd_two_of_isSpor_onan hY
  have hq1 : QuotientGroup.mk' Inn σ = 1 :=
    mk'_inner_eq_one_of_orderOf_eq_three hσ3 hOut
  have hσinner : σ ∈ Inn := (QuotientGroup.eq_one_iff σ).mp hq1
  obtain ⟨x, hx, hx3⟩ := exists_orderOf_eq_three_of_mem_inner hinj hσ3 hσinner
  obtain ⟨eY⟩ := hY
  let Cσ : Subgroup (MulAut Y) := H ⊓ Subgroup.centralizer ({σ} : Set (MulAut Y))
  let C0 : Subgroup Y := Subgroup.centralizer ({x} : Set Y)
  have hC0card : Nat.card C0 = 3240 := by
    have h :=
      CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Proving.card_centralizer_three_ON
        eY hx3
    simpa [C0] using h
  have hkercard : Nat.card (MonoidHom.ker ((QuotientGroup.mk' Inn).comp Cσ.subtype)) =
      3240 :=
    card_ker_mk'_comp_subtype_eq_3240 hinj hx hInn hC0card
  exact card_inf_centralizer_dvd_6480 hOut hkercard

end K4ord

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan

end
