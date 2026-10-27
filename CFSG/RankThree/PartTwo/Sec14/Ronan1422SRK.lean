module

public import CFSG.RankThree.PartTwo.Sec14.Ronan1422SPoint
public import CFSG.RankThree.PartTwo.KFacts.KP4

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan1422S

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Late
  CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G] {A L : Subgroup G} {c : G}

namespace Pt

theorem le_centralizer (h : Pt A c L) : L ≤ Subgroup.centralizer ({c} : Set G) :=
  h.std.toSec13Data.le_centralizer

theorem mem_A (h : Pt A c L) : c ∈ A := h.std.toSec13Data.mem_A

theorem A_le_normalizer_of_le (h : Pt A c L) {U : Subgroup G} (hUL : U ≤ L)
    (hBU : A ⊓ L ≤ Subgroup.normalizer (U : Set G)) : A ≤ Subgroup.normalizer (U : Set G) := by
  rw [h.eq_sup]
  refine sup_le ?_ hBU
  rw [Subgroup.zpowers_le]
  refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun u hu => ?_)
  exact (Subgroup.mem_centralizer_singleton_iff.mp (h.le_centralizer (hUL hu)))

end Pt

section R

variable {R : Subgroup G}

theorem Pt.R_facts (h : Pt A c L) (hR : R ∈ scriptQPiStar A (lB A) L (piOf 2)) :
    R ≤ L ∧ IsPGroup 2 R ∧ A ≤ Subgroup.normalizer (R : Set G) ∧
      ∀ U : Subgroup G, U ≤ L → IsPGroup 2 U → A ≤ Subgroup.normalizer (U : Set G) → R ≤ U →
        U = R := by
  obtain ⟨⟨⟨hRQ, hRL⟩, hRpi⟩, hRmax⟩ := hR
  refine ⟨hRL, (isPiSubgroup_piOf_iff Nat.prime_two R).mp hRpi, hRQ.1.2.2, ?_⟩
  intro U hUL hU2 hAU hRU
  have hUmem : U ∈ scriptQPi A (lB A) L (piOf 2) :=
    ⟨⟨h.iq U hU2 hAU, hUL⟩, (isPiSubgroup_piOf_iff Nat.prime_two U).mpr hU2⟩
  exact le_antisymm (hRmax hUmem hRU) hRU

omit [Finite G] in
theorem mem_normalizer_map_subtype {U : Subgroup ↥L} {b : ↥L} :
    (b : G) ∈ Subgroup.normalizer ((U.map L.subtype : Subgroup G) : Set G) ↔
      b ∈ Subgroup.normalizer (U : Set ↥L) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro hb u
    have h := hb (u : G)
    constructor
    · intro hu
      obtain ⟨v, hv, hvu⟩ := h.mp ⟨u, hu, rfl⟩
      have : v = b * u * b⁻¹ := Subtype.ext (by simpa using hvu)
      rw [← this]
      exact hv
    · intro hu
      obtain ⟨v, hv, hvu⟩ := h.mpr ⟨b * u * b⁻¹, hu, rfl⟩
      have : v = u := Subtype.ext hvu
      rw [← this]
      exact hv
  · intro hb g
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨b * u * b⁻¹, (hb u).mp hu, rfl⟩
    · rintro ⟨w, hw, hwg⟩
      have hgL : g ∈ L := by
        have : g = (b : G)⁻¹ * (w : G) * b := by
          rw [Subgroup.coe_subtype] at hwg
          rw [hwg]
          group
        rw [this]
        exact mul_mem (mul_mem (inv_mem b.2) w.2) b.2
      refine ⟨⟨g, hgL⟩, (hb ⟨g, hgL⟩).mpr ?_, rfl⟩
      have : b * ⟨g, hgL⟩ * b⁻¹ = w := Subtype.ext (by
        rw [Subgroup.coe_subtype] at hwg
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
        exact hwg.symm)
      rw [this]
      exact hw

omit [Finite G] in
theorem le_normalizer_subgroupOf {X : Subgroup G} (hXL : X ≤ L)
    (hAX : A ≤ Subgroup.normalizer (X : Set G)) :
    (A ⊓ L).subgroupOf L ≤ Subgroup.normalizer ((X.subgroupOf L : Subgroup ↥L) : Set ↥L) := by
  intro b hb
  rw [← mem_normalizer_map_subtype, Subgroup.map_subgroupOf_eq_of_le hXL]
  exact hAX (Subgroup.mem_subgroupOf.mp hb).1

theorem Pt.mem_maxInvariant (h : Pt A c L) (hR : R ∈ scriptQPiStar A (lB A) L (piOf 2)) :
    R.subgroupOf L ∈ maxInvariantPiSubgroups ⊤ ((A ⊓ L).subgroupOf L) (piOf 2) := by
  obtain ⟨hRL, hR2, hAR, hmax⟩ := h.R_facts hR
  refine ⟨⟨le_top, (isPiSubgroup_piOf_iff Nat.prime_two _).mpr hR2.comap_subtype,
    le_normalizer_subgroupOf hRL hAR⟩, fun U hU hRU => ?_⟩
  obtain ⟨-, hUpi, hBU⟩ := hU
  have hU2 : IsPGroup 2 U := (isPiSubgroup_piOf_iff Nat.prime_two U).mp hUpi
  set U₀ : Subgroup G := U.map L.subtype with hU₀
  have hU₀L : U₀ ≤ L := Subgroup.map_subtype_le U
  have hBU₀ : A ⊓ L ≤ Subgroup.normalizer (U₀ : Set G) := by
    intro b hb
    have hbL : b ∈ L := hb.2
    have : (⟨b, hbL⟩ : ↥L) ∈ Subgroup.normalizer (U : Set ↥L) :=
      hBU (Subgroup.mem_subgroupOf.mpr hb)
    exact mem_normalizer_map_subtype.mpr this
  have hRU₀ : R ≤ U₀ := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hRL]
    exact Subgroup.map_mono hRU
  have heq := hmax U₀ hU₀L (hU2.map L.subtype) (h.A_le_normalizer_of_le hU₀L hBU₀) hRU₀
  intro u hu
  have : (u : G) ∈ R := heq ▸ (⟨u, hu, rfl⟩ : (u : G) ∈ U₀)
  exact Subgroup.mem_subgroupOf.mpr this

section KP4

theorem Pt.card_B_L (h : Pt A c L) : Nat.card ((A ⊓ L).subgroupOf L) = 9 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv, h.card_B]

theorem Pt.R_kp4 (h : Pt A c L) (hR : R ∈ scriptQPiStar A (lB A) L (piOf 2)) :
    CFSG.Assembly.IsElemAbelian 2 R ∧ Nat.card R = 16 ∧
      (∃ d e : G, d ∈ A ⊓ L ∧ e ∈ A ⊓ L ∧
        ∀ x ∈ R, x * d = d * x → x * e = e * x → x = 1) ∧
      R ⊓ Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G) = ⊥ := by
  obtain ⟨hRL, -, -, -⟩ := h.R_facts hR
  have hmem := h.mem_maxInvariant hR
  rw [← KFacts.KP4.m22_maxInvariant_threePrime_eq_two h.m22 h.card_B_L] at hmem
  obtain ⟨hel, h16, a, b, haB, hbB, -, hRa, hRb, hinf, -⟩ :=
    KFacts.KP4.m22_maxInvariant_structure h.m22 h.card_B_L hmem
  obtain ⟨hcomm, hsq⟩ := CFSG.RankThree.Asc83Table.isElementaryAbelian_iff.mp hel
  have hab : ∀ x ∈ R, x * (a : G) = a * x → x * (b : G) = b * x → x = 1 := by
    intro x hxR hxa' hxb'
    have hxL : x ∈ L := hRL hxR
    have hxa : (⟨x, hxL⟩ : ↥L) ∈ R.subgroupOf L ⊓ Subgroup.centralizer ({a} : Set ↥L) :=
      ⟨Subgroup.mem_subgroupOf.mpr hxR, Subgroup.mem_centralizer_singleton_iff.mpr
        (Subtype.ext hxa')⟩
    have hxb : (⟨x, hxL⟩ : ↥L) ∈ R.subgroupOf L ⊓ Subgroup.centralizer ({b} : Set ↥L) :=
      ⟨Subgroup.mem_subgroupOf.mpr hxR, Subgroup.mem_centralizer_singleton_iff.mpr
        (Subtype.ext hxb')⟩
    rw [hRa] at hxa
    rw [hRb] at hxb
    have h1 : (⟨x, hxL⟩ : ↥L) ∈ (⊥ : Subgroup ↥L) := hinf ▸ ⟨hxa, hxb⟩
    rw [Subgroup.mem_bot] at h1
    exact congrArg Subtype.val h1
  refine ⟨⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩, ?_,
    ⟨a, b, Subgroup.mem_subgroupOf.mp haB, Subgroup.mem_subgroupOf.mp hbB, hab⟩, ?_⟩
  · have := hcomm ⟨x, hRL x.2⟩ (Subgroup.mem_subgroupOf.mpr x.2) ⟨y, hRL y.2⟩
      (Subgroup.mem_subgroupOf.mpr y.2)
    simpa using congrArg Subtype.val this
  · have := hsq ⟨x, hRL hx⟩ (Subgroup.mem_subgroupOf.mpr hx)
    exact congrArg Subtype.val this
  · rw [← h16, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRL).toEquiv]
  · rw [eq_bot_iff]
    intro x ⟨hxR, hxC⟩
    rw [Subgroup.mem_bot]
    exact hab x hxR (Subgroup.mem_centralizer_iff.mp hxC _ (Subgroup.mem_subgroupOf.mp haB)).symm
      (Subgroup.mem_centralizer_iff.mp hxC _ (Subgroup.mem_subgroupOf.mp hbB)).symm

theorem Pt.K_kp4 (h : Pt A c L) (hR : R ∈ scriptQPiStar A (lB A) L (piOf 2)) :
    Nat.card (L ⊓ Subgroup.normalizer (R : Set G) : Subgroup G) = 5760 ∧
      ∃ f : ↥(L ⊓ Subgroup.normalizer (R : Set G)) →* alternatingGroup (Fin 6),
        Function.Surjective f ∧ f.ker = R.subgroupOf (L ⊓ Subgroup.normalizer (R : Set G)) := by
  obtain ⟨hRL, -, -, -⟩ := h.R_facts hR
  obtain ⟨hcard, ⟨q⟩⟩ := KFacts.KP4.m22_normalizer_quotient h.m22 h.card_B_L
    (h.mem_maxInvariant hR)
  set R' : Subgroup ↥L := R.subgroupOf L with hR'
  set N' : Subgroup ↥L := Subgroup.normalizer (R' : Set ↥L) with hN'
  set K : Subgroup G := L ⊓ Subgroup.normalizer (R : Set G) with hK
  have hRmap : R'.map L.subtype = R := Subgroup.map_subgroupOf_eq_of_le hRL
  have hmap : N'.map L.subtype = K := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, ?_⟩
      have := mem_normalizer_map_subtype.mpr hy
      rwa [hRmap] at this
    · rintro ⟨hxL, hxN⟩
      refine ⟨⟨x, hxL⟩, ?_, rfl⟩
      rw [← hRmap] at hxN
      exact mem_normalizer_map_subtype.mp hxN
  let e : ↥N' ≃* ↥K := (N'.equivMapOfInjective L.subtype L.subtype_injective).trans
    (MulEquiv.subgroupCongr hmap)
  refine ⟨by rw [← hcard, Nat.card_congr e.toEquiv.symm], ?_⟩
  let π : ↥N' →* ↥N' ⧸ R'.subgroupOf N' := QuotientGroup.mk' _
  refine ⟨q.toMonoidHom.comp (π.comp e.symm.toMonoidHom), ?_, ?_⟩
  · exact q.surjective.comp ((QuotientGroup.mk'_surjective _).comp e.symm.surjective)
  · ext k
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    have : ((e.symm k : ↥N') : ↥L) = ⟨(k : G), k.2.1⟩ := by
      apply Subtype.ext
      have h1 : (e (e.symm k) : G) = (k : G) := by rw [MulEquiv.apply_symm_apply]
      exact h1
    have h2 : (((e.symm k : ↥N') : ↥L) : G) = (k : G) := by rw [this]
    change (((e.symm k : ↥N') : ↥L) : G) ∈ R ↔ (k : G) ∈ R
    rw [h2]

end KP4

omit [Finite G] in
theorem R_le_K (hRL : R ≤ L) : R ≤ L ⊓ Subgroup.normalizer (R : Set G) :=
  le_inf hRL Subgroup.le_normalizer

omit [Finite G] in
theorem B_le_K (hAR : A ≤ Subgroup.normalizer (R : Set G)) :
    A ⊓ L ≤ L ⊓ Subgroup.normalizer (R : Set G) :=
  fun _ hb => ⟨hb.2, hAR hb.1⟩

omit [Finite G] in
theorem mem_normalizer_normalizer {X : Subgroup G} {a : G}
    (ha : a ∈ Subgroup.normalizer (X : Set G)) :
    a ∈ Subgroup.normalizer ((Subgroup.normalizer (X : Set G) : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact mul_mem (mul_mem ha hx) (inv_mem ha)
  · intro hx
    have := mul_mem (mul_mem (inv_mem ha) hx) ha
    simpa [mul_assoc] using this

end R

end CFSG.RankThree.PartTwo.Sec14.Ronan1422S
