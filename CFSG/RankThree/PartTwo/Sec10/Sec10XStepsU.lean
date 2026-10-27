module

public import CFSG.RankThree.PartTwo.Sec10.Sec10XProofTen
public import CFSG.RankThree.PartTwo.KFacts.KS10L27Aut

public section

namespace CFSG.RankThree.PartTwo.Sec10

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.GroupTheory
open scoped commutatorElement

namespace Sec10XSteps

section General

variable {G : Type} [Group G]

theorem isElemAbelian_map {X : Type*} [Group X] {p : ℕ} (f : X →* G) {B : Subgroup X}
    (hB : CFSG.Assembly.IsElemAbelian p B) : CFSG.Assembly.IsElemAbelian p (B.map f) :=
  CFSG.SectionRank.isElemAbelian_map hB _

theorem centralizer_le_normalizer_zpowers [Finite G] (c : G) :
    Subgroup.centralizer ({c} : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
  fun g hg => Sec10.mem_normalizer_zpowers_of_conj_mem (by
    rw [Subgroup.mem_centralizer_singleton_iff.mp hg, mul_inv_cancel_right]
    exact Subgroup.mem_zpowers c)

end General

section Std


variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R : Subgroup G}

theorem exists_mulEquiv_psl2_L (h : Sec10Std G A c L a R) :
    Nonempty (L ≃* GorensteinWalter.PSL2 (GaloisField 3 3)) := by
  obtain ⟨e⟩ := h.nonempty_mulEquiv
  exact ⟨e.trans (Sec4.projSLEquivPSL _)⟩

theorem eq_one_of_pow_two_pow_of_commute (h45 : Sec4.Item4_5) (h : Sec10Std G A c L a R) {t : G}
    (htH : t ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G)) {k : ℕ} (htk : t ^ 2 ^ k = 1)
    {x : G} (hxL : x ∈ L) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) (htx : t * x = x * t) : t = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := exists_mulEquiv_psl2_L h
  have htN : t ∈ Subgroup.normalizer (L : Set G) := h.normalizer_le_normalizer_L h45 htH
  set τ := Sec4.compAction L ⟨t, htN⟩ with hτ
  have hτk : τ ^ 2 ^ k = 1 := by
    have h1 : (⟨t, htN⟩ : Subgroup.normalizer (L : Set G)) ^ 2 ^ k = 1 :=
      Subtype.ext (by simpa using htk)
    rw [hτ, ← map_pow, h1, map_one]
  have hτx : τ ⟨x, hxL⟩ = ⟨x, hxL⟩ := Subtype.ext (by
    rw [hτ, Sec4.compAction, Sec4.normalizerMonoidHom_apply_coe, htx, mul_inv_cancel_right])
  have hτ1 : τ = 1 := KFacts.eq_one_of_mulAut_of_mulEquiv_psl2_27 e hτk
    (Subtype.ext (by simpa using hx3)) (fun h1 => hx1 (congrArg Subtype.val h1)) hτx
  have htC : t ∈ Subgroup.centralizer (L : Set G) := by
    have h1 : (⟨t, htN⟩ : Subgroup.normalizer (L : Set G)) ∈ (Sec4.compAction L).ker := hτ1
    rw [Sec4.compAction_ker] at h1
    exact Subgroup.mem_subgroupOf.mp h1
  have hT2 : IsPGroup 2 (Subgroup.zpowers t) := by
    intro y
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp y.2
    refine ⟨k, Subtype.ext ?_⟩
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, htk, one_zpow]
  have hLT : L ≤ Subgroup.centralizer (Subgroup.zpowers t : Set G) := by
    rw [← Subgroup.le_centralizer_iff, Subgroup.zpowers_le]
    exact htC
  have hT := h.eq_bot_of_inf_le_normalizer hT2
    (inf_le_right.trans (hLT.trans (Subgroup.centralizer_le_normalizer _)))
  rwa [Subgroup.zpowers_eq_bot] at hT

theorem le_of_isPGroup_two (h45 : Sec4.Item4_5) (h : Sec10Std G A c L a R) {X : Subgroup G}
    (hXH : X ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G)) (hX2 : IsPGroup 2 X) {x : G}
    (hxL : x ∈ L) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hxX : x ∈ Subgroup.normalizer (X : Set G)) : X ≤ L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXL : X ≤ Subgroup.normalizer (L : Set G) := hXH.trans (h.normalizer_le_normalizer_L h45)
  have hxN : Subgroup.zpowers x ≤ Subgroup.normalizer (X : Set G) := Subgroup.zpowers_le.mpr hxX
  have hxL' : Subgroup.zpowers x ≤ L := Subgroup.zpowers_le.mpr hxL
  have hP : IsPGroup 3 (Subgroup.zpowers x) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, orderOf_eq_prime hx3 hx1, pow_one])
  set φ : Subgroup.zpowers x →* MulAut X :=
    X.normalizerMonoidHom.comp (Subgroup.inclusion hxN) with hφ
  have hφapp : ∀ (g : Subgroup.zpowers x) (y : X),
      ((φ g y : X) : G) = (g : G) * y * (g : G)⁻¹ := fun _ _ => rfl
  set N := L.subgroupOf X with hN
  have hNn : N.Normal := ⟨fun n hn y => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (Subgroup.mem_normalizer_iff.mp (hXL y.2) n).mp hn⟩
  have hN3 : ¬ 3 ∣ Nat.card N := by
    obtain ⟨m, hm⟩ := (hX2.to_subgroup N).exists_card_eq
    rw [hm]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  have hφN : ∀ g, ∀ n ∈ N, φ g n ∈ N := by
    intro g n hn
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    rw [hφapp]
    have hgL : (g : G) ∈ L := hxL' g.2
    exact L.mul_mem (L.mul_mem hgL hn) (L.inv_mem hgL)
  intro x₀ hx₀
  have hy : ∀ g, ((φ g ⟨x₀, hx₀⟩ : X) : X ⧸ N) = ((⟨x₀, hx₀⟩ : X) : X ⧸ N) := by
    intro g
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hφapp]
    have hgL : (g : G) ∈ L := hxL' g.2
    have h1 : x₀⁻¹ * (g : G)⁻¹ * x₀ ∈ L := by
      have := (Subgroup.mem_normalizer_iff.mp (hXL (X.inv_mem hx₀)) _).mp (L.inv_mem hgL)
      simpa using this
    have h2 : ((g : G) * x₀ * (g : G)⁻¹)⁻¹ * x₀ = g * (x₀⁻¹ * (g : G)⁻¹ * x₀) := by group
    rw [h2]
    exact L.mul_mem hgL h1
  obtain ⟨y', hy'eq, hy'fix⟩ := KFacts.exists_fixed_of_coprime hP φ N hN3 hφN _ hy
  have hy'x : (y' : G) * x = x * y' := by
    have h1 := congrArg Subtype.val (hy'fix ⟨x, Subgroup.mem_zpowers x⟩)
    rw [hφapp] at h1
    calc (y' : G) * x = x * y' * x⁻¹ * x := by rw [h1]
      _ = x * y' := by group
  obtain ⟨m, hm⟩ := hX2 y'
  have hm' : (y' : G) ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  have hy'1 := eq_one_of_pow_two_pow_of_commute h45 h (hXH y'.2) hm' hxL hx3 hx1 hy'x
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at hy'eq
  simpa [hy'1] using hy'eq

theorem exists_mulEquiv_inf_centralizer (h : Sec10Std G A c L a R) :
    ∃ F : Subfield (GaloisField 3 3), Nat.card F = 3 ∧
      Nonempty ((L ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) ≃*
        GorensteinWalter.PSL2 F) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := exists_mulEquiv_psl2_L h
  obtain ⟨haN, hout⟩ := h.toHyp81.inducesOuterTheta
  set α := Sec4.compAction L ⟨a, haN⟩ with hα
  have hαapp : ∀ y : L, ((α y : L) : G) = a * y * a⁻¹ := fun _ => rfl
  have hα3 : α ^ 3 = 1 := by
    have h1 : (⟨a, haN⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 :=
      Subtype.ext (by simpa using h.pow_three h.a_mem)
    rw [hα, ← map_pow, h1, map_one]
  have hinn : ¬ KFacts.IsInnerAut α := by
    rintro ⟨l, hl⟩
    apply hout
    refine ⟨((l : L) : L ⧸ aschbacherSolvableCore 3 L), ?_⟩
    ext q
    induction q using QuotientGroup.induction_on with
    | H w =>
      rw [Sec4.thetaQuotMulAut_mk, ← hl]
      rfl
  obtain ⟨σ, hσ3, ⟨f⟩⟩ := Item1014Proof.exists_eqLocus_mulEquiv_of_mulEquiv_psl2 e hα3 hinn
  have hF3 : Nat.card (GH74.GLS.IVK.fixedField σ) = 3 :=
    KFacts.card_fixedField_of_orderOf_eq_three hσ3 (q₀ := 3) (GaloisField.card 3 3 (by norm_num))
  refine ⟨_, hF3, ⟨?_⟩⟩
  set E := α.toMonoidHom.eqLocus (MonoidHom.id L) with hE
  have hmap : E.map L.subtype = L ⊓ Subgroup.centralizer ({a} : Set G) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have h1 : ((α y : L) : G) = y := congrArg Subtype.val (hy : α y = y)
      rw [hαapp] at h1
      calc (y : G) * a = a * y * a⁻¹ * a := by rw [h1]
        _ = a * y := by group
    · rintro ⟨hxL, hxa⟩
      refine ⟨⟨x, hxL⟩, ?_, rfl⟩
      show α ⟨x, hxL⟩ = ⟨x, hxL⟩
      apply Subtype.ext
      rw [hαapp]
      have hxa' : x * a = a * x := Subgroup.mem_centralizer_singleton_iff.mp hxa
      calc a * x * a⁻¹ = x * a * a⁻¹ := by rw [← hxa']
        _ = x := by group
  exact ((MulEquiv.subgroupCongr hmap).symm.trans
    (E.equivMapOfInjective L.subtype L.subtype_injective).symm).trans f

theorem sec10U_facts (h : Sec10Std G A c L a R) :
    Nat.card (L ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) = 12 ∧
      Nat.card (sec10U L a) = 4 ∧ CFSG.Assembly.IsElemAbelian 2 (sec10U L a) ∧
      ∃ u ∈ L ⊓ Subgroup.centralizer ({a} : Set G), ∃ v ∈ sec10U L a, u * v * u⁻¹ ≠ v := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨F, hF3, ⟨ι⟩⟩ := exists_mulEquiv_inf_centralizer h
  have : Fintype F := Fintype.ofFinite F
  have : CharP F 3 := charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card, hF3])
  set Y := L ⊓ Subgroup.centralizer ({a} : Set G) with hY
  have hYcard : Nat.card Y = 12 := by
    rw [Nat.card_congr ι.toEquiv, KFacts.card_psl2_of_card_three hF3]
  set V := KFacts.psl2FourGroup F with hV
  have hVn : V.Normal := KFacts.psl2FourGroup_normal_of_card_three hF3
  set V₀ := V.map ι.symm.toMonoidHom with hV₀
  have hV₀n : V₀.Normal := hVn.map _ ι.symm.surjective
  set V' := V₀.map Y.subtype with hV'
  have hV'card : Nat.card V' = 4 := by
    rw [hV', Subgroup.card_map_of_injective Y.subtype_injective, hV₀,
      Subgroup.card_map_of_injective ι.symm.injective,
      KFacts.card_psl2FourGroup_of_card_three hF3]
  have hV'2 : IsPGroup 2 V' := (KFacts.isPGroup_psl2FourGroup.map _).map _
  have hV'Y : V' ≤ Y := Subgroup.map_subtype_le _
  have hYV' : Y ≤ Subgroup.normalizer (V' : Set G) := fun y hy => by
    have hy' : (⟨y, hy⟩ : Y) ∈ Subgroup.normalizer (V₀ : Set Y) := by
      rw [Subgroup.normalizer_eq_top_iff.mpr hV₀n]
      exact Subgroup.mem_top _
    exact Sec10XProof.mem_normalizer_map_subtype hy'
  have hU : sec10U L a = inSubgroup (CFSG.pCore 2) Y := rfl
  have hV'U : V' ≤ sec10U L a := by
    rw [hU]
    exact SteinbergBY.le_inSubgroup_pCore hV'2 hV'Y hYV'
  have hUcard : Nat.card (sec10U L a) ≤ 4 := by
    obtain ⟨m, hm⟩ := (SteinbergBY.isPGroup_inSubgroup_pCore 2 Y).exists_card_eq
    have hdvd : 2 ^ m ∣ 12 := by
      rw [← hm, ← hYcard]
      exact Subgroup.card_dvd_of_le (SteinbergBY.inSubgroup_pCore_le 2 Y)
    have hm2 : m ≤ 2 := by
      by_contra hm2
      have : 2 ^ 3 ∣ 12 := (Nat.pow_dvd_pow 2 (by omega)).trans hdvd
      norm_num at this
    rw [hU, hm]
    calc 2 ^ m ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hm2
      _ = 4 := by norm_num
  have hUeq : V' = sec10U L a :=
    Subgroup.eq_of_le_of_card_ge hV'U (by rw [hV'card]; exact hUcard)
  refine ⟨hYcard, hUeq ▸ hV'card, ?_, ?_⟩
  · rw [← hUeq]
    exact isElemAbelian_map _ (isElemAbelian_map _ KFacts.isElemAbelian_psl2FourGroup)
  · refine ⟨(ι.symm (KFacts.psl2U1 F) : G), (ι.symm (KFacts.psl2U1 F)).2,
      (ι.symm (KFacts.psl2QI F) : G), ?_, ?_⟩
    · rw [← hUeq]
      exact ⟨_, ⟨_, Subgroup.subset_closure (by simp), rfl⟩, rfl⟩
    · intro heq
      apply KFacts.psl2U1_conj_psl2QI_ne (F := F)
      apply ι.symm.injective
      apply Subtype.ext
      simpa [map_mul, map_inv] using heq

theorem inf_centralizer_eq_bot (h : Sec10Std G A c L a R) {x : G}
    (hxY : x ∈ L ⊓ Subgroup.centralizer ({a} : Set G)) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) :
    sec10U L a ⊓ Subgroup.centralizer ({x} : Set G) = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hYcard, hU4, hUe, u, huY, v, hvU, huv⟩ := sec10U_facts h
  set Y := L ⊓ Subgroup.centralizer ({a} : Set G) with hY
  set U := sec10U L a with hUdef
  have hUY : U ≤ Y := SteinbergBY.inSubgroup_pCore_le 2 Y
  have hYU : Y ≤ Subgroup.normalizer (U : Set G) := SteinbergBY.le_normalizer_inSubgroup_pCore 2 Y
  have hx3' : IsPGroup 3 (Subgroup.zpowers x) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, orderOf_eq_prime hx3 hx1, pow_one])
  have hmod := Sec6.card_inf_centralizer_modEq hx3' (Subgroup.zpowers_le.mpr (hYU hxY))
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure, hU4] at hmod
  have hdvd : Nat.card (U ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) ∣ 4 :=
    hU4 ▸ Subgroup.card_dvd_of_le inf_le_left
  have hcases : Nat.card (U ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) = 1 ∨
      Nat.card (U ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) = 4 := by
    obtain ⟨n, hn⟩ : ∃ n, Nat.card (U ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) = n :=
      ⟨_, rfl⟩
    rw [hn] at hmod hdvd ⊢
    have hpos : 0 < n := hn ▸ Nat.card_pos
    have hle : n ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases n
    · exact Or.inl rfl
    · exact absurd hmod (by decide)
    · exact absurd hdvd (by decide)
    · exact Or.inr rfl
  rcases hcases with h1 | h4
  · exact Subgroup.eq_bot_of_card_eq _ h1
  · exfalso
    have hUx : U ≤ Subgroup.centralizer ({x} : Set G) := by
      have heq := Subgroup.eq_of_le_of_card_ge (inf_le_left :
        U ⊓ Subgroup.centralizer ({x} : Set G) ≤ U) (by rw [h4, hU4])
      rw [← heq]
      exact inf_le_right
    set Z := Y ⊓ Subgroup.centralizer (U : Set G) with hZ
    have hUZ : U ≤ Z := fun y hy => ⟨hUY hy, Subgroup.mem_centralizer_iff.mpr fun z hz =>
      congrArg Subtype.val (hUe.1.1.comm ⟨z, hz⟩ ⟨y, hy⟩)⟩
    have hxZ : x ∈ Z := ⟨hxY, Subgroup.mem_centralizer_iff.mpr fun z hz =>
      Subgroup.mem_centralizer_singleton_iff.mp (hUx hz)⟩
    have h4' : 4 ∣ Nat.card Z := hU4 ▸ Subgroup.card_dvd_of_le hUZ
    have h3' : 3 ∣ Nat.card Z := orderOf_eq_prime hx3 hx1 ▸ Subgroup.orderOf_dvd_natCard Z hxZ
    have h12 := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 4 3) h4' h3'
    have hZY : Z = Y := Subgroup.eq_of_le_of_card_ge inf_le_left
      (by rw [hYcard]; exact Nat.le_of_dvd Nat.card_pos h12)
    have huZ : u ∈ Z := hZY ▸ huY
    apply huv
    rw [(Subgroup.mem_centralizer_iff.mp huZ.2 v hvU).symm]
    group

theorem exists_mem_inf_orderOf (h45 : Sec4.Item4_5) (h : Sec10Std G A c L a R) :
    ∃ d ∈ A, d ∈ L ∧ orderOf d = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA3 : IsPGroup 3 A := fun x => ⟨1, Subtype.ext (by simpa using h.pow_three x.2)⟩
  have hAc : A ≤ Subgroup.centralizer ({c} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (h.comm hx h.mem_A)
  have hAL : A ≤ Subgroup.normalizer (L : Set G) :=
    Sec11.le_normalizer_of_isPGroup_of_le_centralizer h45 h.toTheoremFourHyp
      (h.pow_three h.mem_A) h.ne_one hA3 hAc L h.mem_thetaComponentsAt
  obtain ⟨d, ⟨hdL, hdA⟩, hdo⟩ := KFacts.exists_mem_centralizer_orderOf_eq hA3 hAL
    ((by norm_num : (3 : ℕ) ∣ 27).trans h.twentyseven_dvd_card)
  have hd3 : d ^ 3 = 1 := by rw [← hdo]; exact pow_orderOf_eq_one d
  refine ⟨d, Sec15.mem_of_mem_partTwoF h.mem_partTwoF hd3 fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hdA y hy), hdL,
    hdo⟩

theorem le_commutator (h : Sec10Std G A c L a R) (hAU : A ≤ Subgroup.normalizer
      (sec10U L a : Set G)) {d : G} (hdA : d ∈ A) (hdL : d ∈ L) (hdo : orderOf d = 3) :
    sec10U L a ≤ ⁅sec10U L a, A⁆ := by
  have hd3 : d ^ 3 = 1 := by rw [← hdo]; exact pow_orderOf_eq_one d
  have hd1 : d ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hdo
    norm_num at hdo
  have hdY : d ∈ L ⊓ Subgroup.centralizer ({a} : Set G) :=
    ⟨hdL, Subgroup.mem_centralizer_singleton_iff.mpr (h.comm hdA h.a_mem)⟩
  have hUd := inf_centralizer_eq_bot h hdY hd3 hd1
  set U := sec10U L a with hUdef
  have hdN := hAU hdA
  have hmem : ∀ v ∈ U, v * d * v⁻¹ * d⁻¹ ∈ U := fun v hv => by
    have h1 : d * v⁻¹ * d⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp hdN _).mp (U.inv_mem hv)
    have h2 := U.mul_mem hv h1
    simpa [mul_assoc] using h2
  set f : U → U := fun v => ⟨(v : G) * d * (v : G)⁻¹ * d⁻¹, hmem v v.2⟩ with hf
  have hfinj : Function.Injective f := by
    intro v w hvw
    have h1 : (v : G) * d * (v : G)⁻¹ * d⁻¹ = (w : G) * d * (w : G)⁻¹ * d⁻¹ :=
      congrArg Subtype.val hvw
    have h2 : ((w : G)⁻¹ * v) * d = d * ((w : G)⁻¹ * v) := by
      calc ((w : G)⁻¹ * v) * d = (w : G)⁻¹ * ((v : G) * d * (v : G)⁻¹ * d⁻¹) * d * v := by group
        _ = (w : G)⁻¹ * ((w : G) * d * (w : G)⁻¹ * d⁻¹) * d * v := by rw [h1]
        _ = d * ((w : G)⁻¹ * v) := by group
    have h3 : (w : G)⁻¹ * v ∈ U ⊓ Subgroup.centralizer ({d} : Set G) :=
      ⟨U.mul_mem (U.inv_mem w.2) v.2, Subgroup.mem_centralizer_singleton_iff.mpr h2⟩
    rw [hUd, Subgroup.mem_bot] at h3
    exact Subtype.ext (inv_mul_eq_one.mp h3).symm
  have hfsurj : Function.Surjective f := Finite.injective_iff_surjective.mp hfinj
  intro u hu
  obtain ⟨v, hv⟩ := hfsurj ⟨u, hu⟩
  have h1 : u = ⁅(v : G), d⁆ := by
    rw [commutatorElement_def]
    exact (congrArg Subtype.val hv).symm
  rw [h1]
  exact Subgroup.commutator_mem_commutator v.2 hdA

end Std

end Sec10XSteps

section Main

open Sec10XSteps


theorem step1010U_holds : Step1010U := by
  intro h45 G _ _ A c L a R h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set U := sec10U L a with hUdef
  set Y := L ⊓ Subgroup.centralizer ({a} : Set G) with hY
  set H := Subgroup.normalizer (Subgroup.zpowers c : Set G) with hH
  obtain ⟨-, hU4, hUe, -⟩ := sec10U_facts h
  have hUY : U ≤ Y := SteinbergBY.inSubgroup_pCore_le 2 Y
  have hU2 : IsPGroup 2 U := SteinbergBY.isPGroup_inSubgroup_pCore 2 Y
  have hHL : H ≤ Subgroup.normalizer (L : Set G) := h.normalizer_le_normalizer_L h45
  have hCH := centralizer_le_normalizer_zpowers c
  have hA3 : IsPGroup 3 A := fun x => ⟨1, Subtype.ext (by simpa using h.pow_three x.2)⟩
  have hAc : A ≤ Subgroup.centralizer ({c} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (h.comm hx h.mem_A)
  have hAL : A ≤ Subgroup.normalizer (L : Set G) := hAc.trans (hCH.trans hHL)
  have hAa : A ≤ Subgroup.centralizer ({a} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (h.comm hx h.a_mem)
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := fun x hx =>
    SteinbergBY.mem_normalizer_inf (hAL hx) (Subgroup.le_normalizer (hAa hx))
  have hAU : A ≤ Subgroup.normalizer (U : Set G) :=
    hAY.trans (SteinbergBY.normalizer_le_normalizer_inSubgroup_pCore 2 Y)
  obtain ⟨d, hdA, hdL, hdo⟩ := exists_mem_inf_orderOf h45 h
  have hd3 : d ^ 3 = 1 := by rw [← hdo]; exact pow_orderOf_eq_one d
  have hd1 : d ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hdo
    norm_num at hdo
  have hUH : U ≤ H := hUY.trans (inf_le_left.trans (h.le_centralizer_c.trans hCH))
  refine ⟨⟨mem_fourGroups_iff.mpr ⟨hAU, hUe, hU4⟩, le_antisymm (le_commutator h hAU hdA hdL hdo)
    (Subgroup.le_normalizer_iff_commutator_le_left.mp hAU)⟩, ?_, ?_⟩
  ·
    set X := Subgroup.centralizer ((Subgroup.closure {c, a} : Subgroup G) : Set G) with hX
    have hXca : X = Subgroup.centralizer ({c, a} : Set G) := by
      rw [hX, Subgroup.centralizer_closure]
    have hXc : X ≤ Subgroup.centralizer ({c} : Set G) := by
      rw [hXca]
      exact Subgroup.centralizer_le (by simp)
    have hXa : X ≤ Subgroup.centralizer ({a} : Set G) := by
      rw [hXca]
      exact Subgroup.centralizer_le (by simp)
    have hYX : Y ≤ X := by
      rw [hXca]
      intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rcases hz with rfl | hz
      · exact (Subgroup.mem_centralizer_singleton_iff.mp (h.le_centralizer_c hy.1)).symm
      · rw [Set.mem_singleton_iff] at hz
        subst hz
        exact (Subgroup.mem_centralizer_singleton_iff.mp hy.2).symm
    have hXY : X ≤ Subgroup.normalizer (Y : Set G) := fun x hx =>
      SteinbergBY.mem_normalizer_inf (hHL (hCH (hXc hx))) (Subgroup.le_normalizer (hXa hx))
    have hUX : U = Y ⊓ inSubgroup (CFSG.pCore 2) X :=
      SteinbergBY.inSubgroup_pCore_eq_inf hYX hXY
    have hdX : d ∈ X := hYX ⟨hdL, hAa hdA⟩
    have hQL : inSubgroup (CFSG.pCore 2) X ≤ L :=
      le_of_isPGroup_two h45 h ((SteinbergBY.inSubgroup_pCore_le 2 X).trans (hXc.trans hCH))
        (SteinbergBY.isPGroup_inSubgroup_pCore 2 X) hdL hd3 hd1
        (SteinbergBY.le_normalizer_inSubgroup_pCore 2 X hdX)
    have hQY : inSubgroup (CFSG.pCore 2) X ≤ Y :=
      le_inf hQL ((SteinbergBY.inSubgroup_pCore_le 2 X).trans hXa)
    rw [hUX, inf_eq_right.mpr hQY]
  ·
    rw [mem_maxInvariantPiSubgroups_iff]
    refine ⟨⟨hUH, (isPiSubgroup_piOf_iff Nat.prime_two _).mpr hU2, hAU⟩, fun X hXinv hUX => ?_⟩
    obtain ⟨hXH, hX2, hXA⟩ := hXinv
    have hX2' : IsPGroup 2 X := (isPiSubgroup_piOf_iff Nat.prime_two X).mp hX2
    have hXL : X ≤ L := le_of_isPGroup_two h45 h hXH hX2' hdL hd3 hd1 (hXA hdA)
    obtain ⟨e⟩ := exists_mulEquiv_psl2_L h
    have hLcard : Nat.card L = 9828 := by
      rw [Nat.card_congr e.toEquiv, KFacts.card_psl2_27]
    obtain ⟨m, hm⟩ := hX2'.exists_card_eq
    have hdvd : 2 ^ m ∣ 9828 := by
      rw [← hm, ← hLcard]
      exact Subgroup.card_dvd_of_le hXL
    have hm2 : m ≤ 2 := by
      by_contra hm2
      have : 2 ^ 3 ∣ 9828 := (Nat.pow_dvd_pow 2 (by omega)).trans hdvd
      norm_num at this
    refine (Subgroup.eq_of_le_of_card_ge hUX ?_).symm
    rw [hU4, hm]
    calc 2 ^ m ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hm2
      _ = 4 := by norm_num

end Main

end CFSG.RankThree.PartTwo.Sec10
