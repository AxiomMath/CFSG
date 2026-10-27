module

public import CFSG.Sporadic.SuzRecog.LocalRBasic
public import CFSG.LocalAnalysis.OddStandard.Seitz77L34Inv
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourAlternatingExclusion
public import CFSG.RankThree.PartOne.K1214.Basic
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.SuzRecog.LocalR.Comp

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AS81
  CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification

variable {G : Type} [Group G] {z : G} {A R : Subgroup G}

noncomputable def quotEquiv (hZ : center A = ⊥) : ↥A ≃* rankTwoQuot A :=
  QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)

theorem inf_inf_eq (hc : Comp z A R) {r : G} (hr : r ∈ R) :
    A ⊓ (centralizer ({r} : Set G) ⊓ centralizer ({z} : Set G)) =
      A ⊓ centralizer ({z} : Set G) := by
  ext x
  constructor
  · rintro ⟨hxA, -, hxz⟩
    exact ⟨hxA, hxz⟩
  · rintro ⟨hxA, hxz⟩
    exact ⟨hxA, hc.le_centralizer_of_mem hr hxA, hxz⟩

theorem inf_R_eq_bot (hc : Comp z A R) (hZ : center A = ⊥) : A ⊓ R = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hxc : (⟨x, hx.1⟩ : A) ∈ center A := mem_center_iff.2 fun g =>
    Subtype.ext (mem_centralizer_iff.1 (hc.R_le_centralizer hx.2) g g.2)
  rw [hZ, mem_bot] at hxc
  exact mem_bot.2 (congrArg Subtype.val hxc)

theorem commute_R (hc : Comp z A R) : ∀ x ∈ A, ∀ y ∈ R, x * y = y * x := fun x hx _ hy =>
  mem_centralizer_iff.1 (hc.R_le_centralizer hy) x hx

theorem sup_R_le (hc : Comp z A R) {r : G} (hr : r ∈ R) :
    A ⊔ R ≤ centralizer ({r} : Set G) :=
  sup_le (hc.le_centralizer_of_mem hr) (hc.R_le_centralizer_of_mem hr)

theorem inf_sup_R_eq [Finite G] (hc : Comp z A R) {r : G} (hr : r ∈ R) :
    (centralizer ({r} : Set G) ⊓ centralizer ({z} : Set G)) ⊓ (A ⊔ R) =
      (A ⊓ centralizer ({z} : Set G)) ⊔ R := by
  have hset := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute A R hc.commute_R).2
  apply le_antisymm
  · rintro y ⟨⟨-, hyz⟩, hy⟩
    have hy' : y ∈ ((A ⊔ R : Subgroup G) : Set G) := hy
    rw [hset] at hy'
    obtain ⟨a, ha, s, hs, rfl⟩ := hy'
    have hsz := hc.R_le_M hs
    have haz : a ∈ centralizer ({z} : Set G) := by
      have e : a = a * s * s⁻¹ := by group
      rw [e]
      exact mul_mem hyz (inv_mem hsz)
    exact mul_mem (mem_sup_left ⟨ha, haz⟩) (mem_sup_right hs)
  · refine sup_le (le_inf (le_inf ?_ inf_le_right) (inf_le_left.trans le_sup_left))
      (le_inf (le_inf (hc.R_le_centralizer_of_mem hr) hc.R_le_M) le_sup_right)
    exact inf_le_left.trans (hc.le_centralizer_of_mem hr)

section L34

noncomputable def equivS (hc : Comp z A R) (hZ : center A = ⊥) : ↥A ≃* PSL3Four.S :=
  (quotEquiv hZ).trans (Classical.choice (PSL3Four.nonempty_equiv_of_stated _ hc.type))

theorem card_A (hc : Comp z A R) (hZ : center A = ⊥) : Nat.card A = 20160 := by
  rw [Nat.card_congr (hc.equivS hZ).toEquiv, PSL3Four.card_S]

theorem card_inf_M (hc : Comp z A R) (hZ : center A = ⊥) (hz : orderOf z = 2) :
    Nat.card (A ⊓ centralizer ({z} : Set G) : Subgroup G) = 64 := by
  have h := (PSL3Four.facts_of_equiv_S.{0} (hc.equivS hZ)).2.1 ⟨z, hc.z_mem⟩
    (by rwa [Subgroup.orderOf_mk])
  rw [← h]
  exact Nat.card_congr
    { toFun := fun x => ⟨⟨x, x.2.1⟩, mem_centralizer_singleton_iff.2
        (Subtype.ext (mem_centralizer_singleton_iff.1 x.2.2))⟩
      invFun := fun y => ⟨y.1.1, y.1.2, mem_centralizer_singleton_iff.2
        (congrArg Subtype.val (mem_centralizer_singleton_iff.1 y.2))⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem exists_mul_mem (hc : Comp z A R) (hz : orderOf z = 2) {r : G} (hr : r ∈ R)
    (hr1 : r ≠ 1) {x : G} (hx : x ∈ centralizer ({r} : Set G)) :
    ∃ a ∈ A, a * x ∈ centralizer ({r} : Set G) ⊓ centralizer ({z} : Set G) := by
  have hxN := hc.le_normalizer r hr hr1 hx
  have hxz : x * z * x⁻¹ ∈ A := (mem_normalizer_iff.1 hxN z).1 hc.z_mem
  have hxz2 : orderOf (x * z * x⁻¹) = 2 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hz
  obtain ⟨a, ha, hax⟩ := CFSG.OddStandard.Seitz77.involutions_conj_of_mem hc.odd
    (Classical.choice (PSL3Four.nonempty_equiv_of_stated _ hc.type)) hxz hc.z_mem hxz2 hz
  refine ⟨a, ha, mem_inf.2 ⟨mul_mem (hc.le_centralizer_of_mem hr ha) hx,
    mem_centralizer_singleton_iff.2 ?_⟩⟩
  calc a * x * z = a * (x * z * x⁻¹) * a⁻¹ * (a * x) := by group
    _ = z * (a * x) := by rw [hax]

theorem centralizer_eq_sup (hc : Comp z A R) (hz : orderOf z = 2) {r : G} (hr : r ∈ R)
    (hr1 : r ≠ 1) :
    centralizer ({r} : Set G) = A ⊔ (centralizer ({r} : Set G) ⊓ centralizer ({z} : Set G)) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨a, ha, hax⟩ := hc.exists_mul_mem hz hr hr1 hx
    have e : x = a⁻¹ * (a * x) := by group
    rw [e]
    exact mul_mem (mem_sup_left (inv_mem ha)) (mem_sup_right hax)
  · exact sup_le (hc.le_centralizer_of_mem hr) inf_le_left

variable [Finite G]

theorem card_sup_R (hc : Comp z A R) (hZ : center A = ⊥) :
    Nat.card (A ⊔ R : Subgroup G) = 80640 := by
  have h := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute A R hc.commute_R).1
  rw [hc.inf_R_eq_bot hZ, Subgroup.card_bot, hc.card_A hZ, hc.card] at h
  omega

variable (hM : Nat.card (centralizer ({z} : Set G)) = 3317760) (hH : NonCentralSylow z)
include hM hH

theorem card_centralizer (hc : Comp z A R) (hz : orderOf z = 2) {r : G} (hr : r ∈ R)
    (hr1 : r ≠ 1) : Nat.card (centralizer ({r} : Set G)) = 161280 := by
  have hZ := hc.center_eq_bot hM hH
  have hVN : centralizer ({r} : Set G) ⊓ centralizer ({z} : Set G) ≤ normalizer (A : Set G) :=
    inf_le_left.trans (hc.le_normalizer r hr hr1)
  have h := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hVN
  rw [← hc.centralizer_eq_sup hz hr hr1, hc.inf_inf_eq hr, hc.card_inf_M hZ hz, hc.card_A hZ,
    (hc.isSylowOf_inf hM hH hr hr1).2] at h
  omega

theorem relIndex_sup_R (hc : Comp z A R) (hz : orderOf z = 2) {r : G} (hr : r ∈ R)
    (hr1 : r ≠ 1) : (A ⊔ R).relIndex (centralizer ({r} : Set G)) = 2 := by
  have h := Subgroup.relIndex_mul_card (H := A ⊔ R) (K := centralizer ({r} : Set G))
  rw [inf_of_le_left (hc.sup_R_le hr), hc.card_sup_R (hc.center_eq_bot hM hH),
    hc.card_centralizer hM hH hz hr hr1] at h
  omega

theorem centralizer_inf_sup_centralizer (hc : Comp z A R) {r : G} (hr : r ∈ R) (hr1 : r ≠ 1) :
    centralizer ({r} : Set G) ⊓ (A ⊔ centralizer (A : Set G)) = A ⊔ R := by
  apply le_antisymm
  · rintro y ⟨hyr, hy⟩
    obtain ⟨a, ha, c, hcA, rfl⟩ := CFSG.RankThree.PartOne.K1214.mem_sup_centralizer_iff A |>.1 hy
    have hcr : c ∈ centralizer ({r} : Set G) := by
      have e : c = a⁻¹ * (a * c) := by group
      rw [e]
      exact mul_mem (inv_mem (hc.le_centralizer_of_mem hr ha)) hyr
    have hcR : c ∈ R := by
      rw [← hc.centralizer_inf_eq hM hH hr hr1]
      exact ⟨hcr, hcA⟩
    exact mul_mem (mem_sup_left ha) (mem_sup_right hcR)
  · exact le_inf (hc.sup_R_le hr) (sup_le_sup_left hc.R_le_centralizer A)

omit hM hH in
theorem isSimpleGroup_A (hc : Comp z A R) (hZ : center A = ⊥) : IsSimpleGroup ↥A := by
  have : IsSimpleGroup (rankTwoQuot A) := hc.standard.1.2
  have : Nontrivial ↥A := by
    rw [← Finite.one_lt_card_iff_nontrivial, hc.card_A hZ]
    norm_num
  exact IsSimpleGroup.isSimpleGroup_of_surjective (quotEquiv hZ).symm.toMonoidHom
    (quotEquiv hZ).symm.surjective

theorem mem_A_of_odd (hc : Comp z A R) (hz : orderOf z = 2) {r : G} (hr : r ∈ R) (hr1 : r ≠ 1)
    {x : G} (hx : x ∈ centralizer ({r} : Set G)) (hodd : Odd (orderOf x)) : x ∈ A := by
  have hZ := hc.center_eq_bot hM hH
  set H := centralizer ({r} : Set G)
  have hAH : A ≤ H := hc.le_centralizer_of_mem hr
  have hN : (A.subgroupOf H).Normal :=
    (normal_subgroupOf_iff_le_normalizer hAH).2 (hc.le_normalizer r hr hr1)
  have hcard : Nat.card (↥H ⧸ A.subgroupOf H) = 8 := by
    have h := (A.subgroupOf H).card_eq_card_quotient_mul_card_subgroup
    rw [Nat.card_congr (subgroupOfEquivOfLe hAH).toEquiv, hc.card_A hZ,
      hc.card_centralizer hM hH hz hr hr1] at h
    omega
  have hP : IsPGroup 2 (↥H ⧸ A.subgroupOf H) := IsPGroup.of_card (n := 3) (by rw [hcard]; norm_num)
  set q : ↥H ⧸ A.subgroupOf H := QuotientGroup.mk ⟨x, hx⟩
  obtain ⟨k, hk⟩ := hP q
  have hdvd : orderOf q ∣ orderOf x := by
    have h1 := orderOf_map_dvd (QuotientGroup.mk' (A.subgroupOf H)) (⟨x, hx⟩ : H)
    rwa [Subgroup.orderOf_mk] at h1
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hk)
  have hj0 : j = 0 := by
    by_contra hne
    have h2 : 2 ∣ orderOf x := (dvd_pow_self 2 hne).trans (hj ▸ hdvd)
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h2)
  rw [hj0, pow_zero, orderOf_eq_one_iff] at hj
  have hmem : (⟨x, hx⟩ : H) ∈ A.subgroupOf H := (QuotientGroup.eq_one_iff _).1 hj
  exact hmem

theorem closure_odd_eq (hc : Comp z A R) (hz : orderOf z = 2) {r : G} (hr : r ∈ R)
    (hr1 : r ≠ 1) :
    closure {x : G | x ∈ centralizer ({r} : Set G) ∧ Odd (orderOf x)} = A := by
  have hZ := hc.center_eq_bot hM hH
  set X := {x : G | x ∈ centralizer ({r} : Set G) ∧ Odd (orderOf x)}
  apply le_antisymm
  · exact (closure_le A).2 fun x hx => hc.mem_A_of_odd hM hH hz hr hr1 hx.1 hx.2
  have := hc.isSimpleGroup_A hZ
  have hconj : ∀ a ∈ A, ∀ y ∈ closure X, a * y * a⁻¹ ∈ closure X := by
    intro a ha y hy
    have hmap : (closure X).map (MulAut.conj a).toMonoidHom ≤ closure X := by
      rw [MonoidHom.map_closure]
      refine closure_mono ?_
      rintro _ ⟨x, hx, rfl⟩
      refine ⟨?_, ?_⟩
      · exact mul_mem (mul_mem (hc.le_centralizer_of_mem hr ha) hx.1)
          (inv_mem (hc.le_centralizer_of_mem hr ha))
      · show Odd (orderOf (MulAut.conj a x))
        rw [MulEquiv.orderOf_eq]
        exact hx.2
    exact hmap ⟨y, hy, rfl⟩
  have hN : ((closure X).subgroupOf A).Normal :=
    ⟨fun n hn g => by
      rw [mem_subgroupOf] at hn ⊢
      exact hconj g g.2 n hn⟩
  rcases hN.eq_bot_or_eq_top with h | h
  · exfalso
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥A) 7
      (by rw [hc.card_A hZ]; norm_num)
    have hyX : ((y : A) : G) ∈ closure X := subset_closure
      ⟨hc.le_centralizer_of_mem hr y.2, by rw [Subgroup.orderOf_coe, hy]; decide⟩
    have hy1 : y ∈ (closure X).subgroupOf A := hyX
    rw [h, mem_bot] at hy1
    rw [hy1, orderOf_one] at hy
    exact absurd hy (by norm_num)
  · intro a ha
    have : (⟨a, ha⟩ : A) ∈ (closure X).subgroupOf A := h ▸ mem_top _
    exact this

end L34

end CFSG.Sporadic.SuzRecog.LocalR.Comp
