module

public import CFSG.RankThree.GF2n.Tim81.Sec7.Stmts
import CFSG.RankThree.GF2n.Tim81.Sec4.CentralQuot
import CFSG.Adapters.QiuzhenLegacy.Compat.G6.CentralizerControl
import CFSG.GroupTheory.CoprimeActionSupport.NormalPSubgroupMeetsCenter
import CFSG.CharacterTheory.Semidihedral.Local.CoprimeCentralizerQuotient

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Tim78
open CFSG.RankThree.GF2n.Tim81.Sec7 (yOf rOf oOf)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M V : Subgroup G}

structure EpsIn (M V : Subgroup G) (h : G) : Prop where
  root : RootHyp M V
  le_p0 : V ≤ p0Of M V (Subgroup.zpowers h)
  cen : rOf M h ⊓ cenOf (p0Of M V (Subgroup.zpowers h)) = oOf M h ⊔ V
  maxEA : Maximal (fun U : Subgroup G => U ≤ rOf M h ∧
    rOf M h ≤ Subgroup.normalizer (U : Set G) ∧ Assembly.IsElemAbelian 2 U) V
  moved : ∃ c ∈ yOf h, conjSubgroup c V ≠ V ∧ conjSubgroup c V ≤ M

abbrev YBar (h : G) : Type := ↥(yOf h) ⧸ pPrimeCore 2 ↥(yOf h)

abbrev barY (h : G) (K : Subgroup G) : Subgroup (YBar h) :=
  (K.subgroupOf (yOf h)).map (QuotientGroup.mk' (pPrimeCore 2 ↥(yOf h)))

abbrev barMap (h : G) {K : Subgroup G} (hK : K ≤ yOf h) : ↥K →* YBar h :=
  (QuotientGroup.mk' (pPrimeCore 2 ↥(yOf h))).comp (Subgroup.inclusion hK)

theorem barY_eq_range_barMap (h : G) {K : Subgroup G} (hK : K ≤ yOf h) :
    barY h K = (barMap h hK).range := by
  ext x
  rw [barY, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨(y : G), Subgroup.mem_subgroupOf.mp hy⟩, rfl⟩
  · rintro ⟨k, rfl⟩
    exact ⟨⟨(k : G), hK k.2⟩, Subgroup.mem_subgroupOf.mpr k.2, rfl⟩

theorem mem_barY_iff (h : G) {K : Subgroup G} (hK : K ≤ yOf h) {x : YBar h} :
    x ∈ barY h K ↔ ∃ k : ↥K, barMap h hK k = x := by
  rw [barY_eq_range_barMap h hK]
  exact MonoidHom.mem_range

theorem barY_mono (h : G) {K L : Subgroup G} (hKL : K ≤ L) : barY h K ≤ barY h L :=
  Subgroup.map_mono (Subgroup.subgroupOf_mono (yOf h) hKL)

theorem barY_map_subtype (h : G) (K : Subgroup ↥(yOf h)) :
    barY h (K.map (yOf h).subtype) =
      K.map (QuotientGroup.mk' (pPrimeCore 2 ↥(yOf h))) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨k, hk, hky⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hy)
    refine ⟨k, hk, ?_⟩
    have hyk : y = (⟨(k : G), k.2⟩ : ↥(yOf h)) := Subtype.ext hky.symm
    rw [hyk]
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨(k : G), k.2⟩,
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_map_of_mem (yOf h).subtype hk), rfl⟩

theorem barY_conj (h : G) {y : G} (hy : y ∈ yOf h) {K : Subgroup G} (hK : K ≤ yOf h) :
    conjSubgroup (QuotientGroup.mk' (pPrimeCore 2 ↥(yOf h)) ⟨y, hy⟩) (barY h K) =
      barY h (conjSubgroup y K) := by
  have hconjK : conjSubgroup y K ≤ yOf h := by
    rintro z ⟨k, hk, rfl⟩
    exact (yOf h).mul_mem ((yOf h).mul_mem hy (hK hk)) ((yOf h).inv_mem hy)
  ext x
  constructor
  · intro hx
    rw [mem_conjSubgroup] at hx
    rw [mem_barY_iff h hK] at hx
    obtain ⟨k, hk⟩ := hx
    have hxeq : x = (QuotientGroup.mk' (pPrimeCore 2 ↥(yOf h)) ⟨y, hy⟩) *
        barMap h hK k * (QuotientGroup.mk' (pPrimeCore 2 ↥(yOf h)) ⟨y, hy⟩)⁻¹ := by
      rw [hk]
      group
    refine (mem_barY_iff h hconjK).mpr ⟨⟨(y : G) * (k : G) * y⁻¹, ?_⟩, ?_⟩
    · exact Subgroup.mem_map.mpr ⟨k, k.2, MulAut.conj_apply y (k : G)⟩
    · rw [hxeq]
      change (QuotientGroup.mk' (pPrimeCore 2 ↥(yOf h)))
          (Subgroup.inclusion hconjK
            (⟨(y : G) * (k : G) * y⁻¹, Subgroup.mem_map.mpr
              ⟨k, k.2, MulAut.conj_apply y (k : G)⟩⟩ : ↥(conjSubgroup y K))) =
        (QuotientGroup.mk' (pPrimeCore 2 ↥(yOf h)) ⟨y, hy⟩) *
          (QuotientGroup.mk' (pPrimeCore 2 ↥(yOf h))) (Subgroup.inclusion hK k) *
          (QuotientGroup.mk' (pPrimeCore 2 ↥(yOf h)) ⟨y, hy⟩)⁻¹
      have hcomp : (Subgroup.inclusion hconjK
          (⟨(y : G) * (k : G) * y⁻¹, Subgroup.mem_map.mpr
            ⟨k, k.2, MulAut.conj_apply y (k : G)⟩⟩ : ↥(conjSubgroup y K)) : ↥(yOf h)) =
          (⟨y, hy⟩ : ↥(yOf h)) * Subgroup.inclusion hK k * (⟨y, hy⟩ : ↥(yOf h))⁻¹ := by
        apply Subtype.ext
        simp [MulAut.conj_apply, mul_assoc]
      rw [hcomp]
      simp only [map_mul, map_inv]
  · intro hx
    rw [mem_barY_iff h hconjK] at hx
    obtain ⟨⟨z, hzK⟩, hz⟩ := hx
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hzK
    refine (mem_conjSubgroup).mpr ?_
    rw [mem_barY_iff h hK]
    refine ⟨⟨k, hk⟩, ?_⟩
    rw [← hz]
    change (QuotientGroup.mk' (pPrimeCore 2 ↥(yOf h))) (Subgroup.inclusion hK ⟨k, hk⟩) =
      (QuotientGroup.mk' (pPrimeCore 2 ↥(yOf h)) ⟨y, hy⟩)⁻¹ *
        (QuotientGroup.mk' (pPrimeCore 2 ↥(yOf h)))
          (Subgroup.inclusion hconjK ⟨(MulAut.conj y) k, hzK⟩) *
        (QuotientGroup.mk' (pPrimeCore 2 ↥(yOf h)) ⟨y, hy⟩)
    have hcomp : (Subgroup.inclusion hconjK
        (⟨(MulAut.conj y) k, hzK⟩ : ↥(conjSubgroup y K)) : ↥(yOf h)) =
        (⟨y, hy⟩ : ↥(yOf h)) * Subgroup.inclusion hK ⟨k, hk⟩ * (⟨y, hy⟩ : ↥(yOf h))⁻¹ := by
      apply Subtype.ext
      simp [MulAut.conj_apply, mul_assoc]
    rw [hcomp]
    simp only [map_mul, map_inv]
    group

namespace EpsIn

variable {h : G} (hE : EpsIn M V h)

theorem le_yOf (hE : EpsIn M V h) : V ≤ yOf h := by
  exact hE.le_p0.trans inf_le_right

theorem conjSubgroup_le_yOf (hE : EpsIn M V h) {y : G} (hy : y ∈ yOf h) :
    conjSubgroup y V ≤ yOf h := by
  rintro x ⟨v, hv, rfl⟩
  exact (yOf h).mul_mem ((yOf h).mul_mem hy (hE.le_yOf hv)) ((yOf h).inv_mem hy)

theorem le_rOf (hE : EpsIn M V h) : V ≤ rOf M h := by
  exact le_inf hE.root.le_M hE.le_yOf

theorem oOf_le_rOf : oOf M h ≤ rOf M h := by
  exact Subgroup.map_subtype_le _

theorem rOf_le_yOf : rOf M h ≤ yOf h := by
  exact inf_le_right

theorem odd_oOf (hE : EpsIn M V h) : Odd (Nat.card (oOf M h)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [oOf, inSubgroup, Subgroup.card_map_of_injective (rOf M h).subtype_injective]
  exact Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := ↥(rOf M h)))

theorem odd_oddCore_yOf (hE : EpsIn M V h) :
    Odd (Nat.card (inSubgroup (pPrimeCore 2) (yOf h))) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [inSubgroup, Subgroup.card_map_of_injective (yOf h).subtype_injective]
  exact Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := ↥(yOf h)))

theorem oOf_le_centralizer_p0 (hE : EpsIn M V h) :
    oOf M h ≤ cenOf (p0Of M V (Subgroup.zpowers h)) := by
  calc oOf M h ≤ oOf M h ⊔ V := le_sup_left
    _ = rOf M h ⊓ cenOf (p0Of M V (Subgroup.zpowers h)) := hE.cen.symm
    _ ≤ cenOf (p0Of M V (Subgroup.zpowers h)) := inf_le_right

theorem oOf_commute_V (hE : EpsIn M V h) {o v : G} (ho : o ∈ oOf M h) (hv : v ∈ V) :
    o * v = v * o := by
  have hvP : v ∈ p0Of M V (Subgroup.zpowers h) := hE.le_p0 hv
  exact (Subgroup.mem_centralizer_iff.mp (hE.oOf_le_centralizer_p0 ho) v hvP).symm

theorem oddCore_yOf_le (hE : EpsIn M V h) :
    inSubgroup (pPrimeCore 2) (yOf h) ≤ oOf M h ∧
      ∀ y ∈ yOf h, inSubgroup (pPrimeCore 2) (yOf h) ≤ cenOf (conjSubgroup y V) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set OY : Subgroup G := inSubgroup (pPrimeCore 2) (yOf h) with hOY
  have hOYodd : Odd (Nat.card OY) := by
    rw [hOY]
    exact hE.odd_oddCore_yOf
  have hOYcop : Nat.Coprime 2 (Nat.card OY) := hOYodd.coprime_two_left
  have hOYnorm : yOf h ≤ Subgroup.normalizer (OY : Set G) := by
    rw [hOY]
    exact le_normalizer_map_subtype (yOf h) (pPrimeCore 2 ↥(yOf h))
  constructor
  · have hcomm : OY ≤ Subgroup.centralizer (V : Set G) :=
      CentralTI.le_centralizer_of_odd_card (T := V) (O := OY) hE.root.elem
        hE.root.four_le_card hE.root.ti (hE.le_yOf.trans hOYnorm) hOYodd
    have hOYM : OY ≤ M := by
      calc OY ≤ Subgroup.centralizer (V : Set G) := hcomm
        _ ≤ Subgroup.normalizer (V : Set G) := Subgroup.centralizer_le_normalizer _
        _ = M := hE.root.normalizer_eq
    have hOYR : OY ≤ rOf M h :=
      le_inf hOYM (Subgroup.map_subtype_le (pPrimeCore 2 ↥(yOf h)))
    haveI hOYnormal : (OY.subgroupOf (rOf M h)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hOYR).mpr
        ((inf_le_right : rOf M h ≤ yOf h).trans hOYnorm)
    exact subgroupOf_le_pPrimeCore_map (p := 2) hOYR hOYcop
  · intro y hy
    refine CentralTI.le_centralizer_of_odd_card (T := conjSubgroup y V) (O := OY)
      (isElemAbelian_conjSubgroup hE.root.elem y) ?_ (isTI_conjSubgroup hE.root.ti y) ?_ hOYodd
    · rw [card_conjSubgroup]
      exact hE.root.four_le_card
    · exact (hE.conjSubgroup_le_yOf hy).trans hOYnorm

theorem disjoint_conj_oddCore (hE : EpsIn M V h) {y : G} (hy : y ∈ yOf h) :
    Disjoint (conjSubgroup y V) (inSubgroup (pPrimeCore 2) (yOf h)) := by
  rw [disjoint_iff]
  refine le_bot_iff.mp ?_
  intro x hx
  obtain ⟨hxV, hxO⟩ := Subgroup.mem_inf.mp hx
  have hV2 : IsPGroup 2 (conjSubgroup y V) :=
    hE.root.isPGroup_V.map (MulAut.conj y).toMonoidHom
  have hodd : Odd (orderOf x) :=
    hE.odd_oddCore_yOf.of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hxO)
  exact Subgroup.mem_bot.mpr (eq_one_of_odd_of_isPGroup hV2 hxV hodd)

theorem mem_conj_of_mul_self_eq_one_of_mem_sup (hE : EpsIn M V h) {y x : G}
    (hy : y ∈ yOf h)
    (hx : x ∈ conjSubgroup y V ⊔ inSubgroup (pPrimeCore 2) (yOf h)) (hx2 : x * x = 1) :
    x ∈ conjSubgroup y V := by
  set OY : Subgroup G := inSubgroup (pPrimeCore 2) (yOf h) with hOY
  have hcomm : OY ≤ Subgroup.centralizer (conjSubgroup y V : Set G) := by
    rw [hOY]
    exact (hE.oddCore_yOf_le).2 y hy
  have hUV : OY ≤ Subgroup.normalizer (conjSubgroup y V : Set G) :=
    hcomm.trans (Subgroup.centralizer_le_normalizer _)
  obtain ⟨v, hv, o, ho, hvo⟩ := exists_mul_of_mem_sup hUV hx
  have hv2 : v * v = 1 := by
    have := (isElemAbelian_conjSubgroup hE.root.elem y).2 v hv
    rwa [pow_two] at this
  have hov : o * v = v * o :=
    (Subgroup.mem_centralizer_iff.mp (hcomm ho) v hv).symm
  have hx2' : (v * o) * (v * o) = 1 := by
    rw [← hvo]
    exact hx2
  have ho2 : o * o = 1 := by
    calc o * o = (v * v) * (o * o) := by rw [hv2, one_mul]
      _ = v * (v * o) * o := by group
      _ = v * (o * v) * o := by rw [hov]
      _ = (v * o) * (v * o) := by group
      _ = 1 := hx2'
  have hodd : Odd (orderOf o) :=
    hE.odd_oddCore_yOf.of_dvd_nat (Subgroup.orderOf_dvd_natCard OY ho)
  have ho1 : o = 1 := by
    have hdvd : orderOf o ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact ho2)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact orderOf_eq_one_iff.mp h
    · rw [h] at hodd
      exact absurd hodd (by norm_num)
  rw [hvo, ho1, mul_one]
  exact hv

theorem barMap_injective_of_disjoint (hE : EpsIn M V h) {K : Subgroup G} (hK : K ≤ yOf h)
    (hdisj : Disjoint K (inSubgroup (pPrimeCore 2) (yOf h))) :
    Function.Injective (barMap h hK) := by
  intro a b hab
  apply Subtype.ext
  have hdiv : (Subgroup.inclusion hK a / Subgroup.inclusion hK b) ∈
      pPrimeCore 2 ↥(yOf h) :=
    (QuotientGroup.eq_iff_div_mem).mp hab
  have hmemO : (a : G) * (b : G)⁻¹ ∈ inSubgroup (pPrimeCore 2) (yOf h) := by
    refine ⟨Subgroup.inclusion hK a / Subgroup.inclusion hK b, hdiv, ?_⟩
    simp [Subgroup.coe_inclusion, div_eq_mul_inv]
  have hmemV : (a : G) * (b : G)⁻¹ ∈ K :=
    K.mul_mem a.2 (K.inv_mem b.2)
  have hbot : (a : G) * (b : G)⁻¹ = 1 := by
    have hmem_bot : (a : G) * (b : G)⁻¹ ∈ (⊥ : Subgroup G) := by
      rw [← disjoint_iff.mp hdisj]
      exact Subgroup.mem_inf.mpr ⟨hmemV, hmemO⟩
    exact Subgroup.mem_bot.mp hmem_bot
  calc (a : G) = (a : G) * (b : G)⁻¹ * (b : G) := by group
    _ = (b : G) := by rw [hbot, one_mul]

theorem card_barY (hE : EpsIn M V h) {y : G} (hy : y ∈ yOf h) :
    Nat.card (barY h (conjSubgroup y V)) = Nat.card V := by
  have hK : conjSubgroup y V ≤ yOf h := hE.conjSubgroup_le_yOf hy
  let φ := barMap h hK
  have hinj : Function.Injective φ :=
    hE.barMap_injective_of_disjoint hK (hE.disjoint_conj_oddCore hy)
  have hbij : Function.Bijective φ.rangeRestrict :=
    ⟨fun a b hab => hinj (congrArg Subtype.val hab), MonoidHom.rangeRestrict_surjective φ⟩
  have hcard : Nat.card (barY h (conjSubgroup y V)) = Nat.card ↥(conjSubgroup y V) := by
    rw [barY_eq_range_barMap h hK]
    exact (Nat.card_congr (MulEquiv.ofBijective φ.rangeRestrict hbij).toEquiv).symm
  rw [hcard, card_conjSubgroup]

theorem mem_V_of_mem_oOf_sup_V (hE : EpsIn M V h) {z : G} (hz : z ∈ oOf M h ⊔ V)
    (hz2 : ∃ k, orderOf z = 2 ^ k) : z ∈ V := by
  obtain ⟨k, hk⟩ := hz2
  have hOVnorm : V ≤ Subgroup.normalizer (oOf M h : Set G) :=
    hE.le_rOf.trans (le_normalizer_map_subtype (rOf M h) (pPrimeCore 2 ↥(rOf M h)))
  obtain ⟨o, ho, v, hv, hzv⟩ := exists_mul_of_mem_sup hOVnorm hz
  have hcomm : Commute o v := hE.oOf_commute_V ho hv
  rcases k with _ | k
  · have hz1 : z = 1 := orderOf_eq_one_iff.mp (by simpa using hk)
    rw [hz1]
    exact V.one_mem
  · have hv2 : v * v = 1 := by
      have := hE.root.elem.2 v hv
      rwa [pow_two] at this
    have hvn : v ^ 2 ^ (k + 1) = 1 := by
      rw [pow_succ', pow_mul, pow_two, hv2, one_pow]
    have hzn : z ^ 2 ^ (k + 1) = 1 := by
      rw [← hk, pow_orderOf_eq_one]
    have hon : o ^ 2 ^ (k + 1) = 1 := by
      have h := hzn
      rw [hzv, hcomm.mul_pow, hvn, mul_one] at h
      exact h
    have hodd : Odd (orderOf o) :=
      hE.odd_oOf.of_dvd_nat (Subgroup.orderOf_dvd_natCard (oOf M h) ho)
    have hdvd : orderOf o ∣ 2 ^ (k + 1) := orderOf_dvd_of_pow_eq_one hon
    have hcop : Nat.Coprime (orderOf o) (2 ^ (k + 1)) :=
      hodd.coprime_two_right.pow_right (k + 1)
    have ho1 : o = 1 :=
      orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop (dvd_refl _) hdvd)
    rw [hzv, ho1, one_mul]
    exact hv

theorem eq_of_barMap_eq (hE : EpsIn M V h) {y v w : G} (hy : y ∈ yOf h)
    (hv : v ∈ V) (hw : w ∈ conjSubgroup y V)
    (himg : barMap h hE.le_yOf ⟨v, hv⟩ =
      barMap h (hE.conjSubgroup_le_yOf hy) ⟨w, hw⟩) : v = w := by
  set o : G := v * w⁻¹ with ho
  have hdiv := (QuotientGroup.eq_iff_div_mem).mp himg
  have ho_mem : o ∈ inSubgroup (pPrimeCore 2) (yOf h) := by
    refine ⟨Subgroup.inclusion hE.le_yOf ⟨v, hv⟩ /
      Subgroup.inclusion (hE.conjSubgroup_le_yOf hy) ⟨w, hw⟩, hdiv, ?_⟩
    simp [ho, Subgroup.coe_inclusion, div_eq_mul_inv]
  have hOV : inSubgroup (pPrimeCore 2) (yOf h) ≤ cenOf V := by
    have h1 := (hE.oddCore_yOf_le).2 1 (Subgroup.one_mem _)
    simpa [conjSubgroup_one] using h1
  have hOVy : inSubgroup (pPrimeCore 2) (yOf h) ≤ cenOf (conjSubgroup y V) :=
    (hE.oddCore_yOf_le).2 y hy
  have hov : o * v = v * o :=
    (Subgroup.mem_centralizer_iff.mp (hOV ho_mem) v hv).symm
  have how : o * w = w * o :=
    (Subgroup.mem_centralizer_iff.mp (hOVy ho_mem) w hw).symm
  have hv2 : v * v = 1 := by
    have := hE.root.elem.2 v hv
    rwa [pow_two] at this
  have hw2 : w * w = 1 := by
    have := (isElemAbelian_conjSubgroup hE.root.elem y).2 w hw
    rwa [pow_two] at this
  have hvw : v = o * w := by
    rw [ho]
    group
  have ho2 : o * o = 1 := by
    have h2 : (o * w) * (o * w) = o * o := by
      calc (o * w) * (o * w) = o * (w * o) * w := by group
        _ = o * (o * w) * w := by rw [how]
        _ = (o * o) * (w * w) := by group
        _ = o * o := by rw [hw2, mul_one]
    calc o * o = (o * w) * (o * w) := h2.symm
      _ = v * v := by rw [hvw]
      _ = 1 := hv2
  have hodd : Odd (orderOf o) :=
    hE.odd_oddCore_yOf.of_dvd_nat
      (Subgroup.orderOf_dvd_natCard (inSubgroup (pPrimeCore 2) (yOf h)) ho_mem)
  have ho1 : o = 1 := by
    have hdvd : orderOf o ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact ho2)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
    · exact orderOf_eq_one_iff.mp h1
    · rw [h1] at hodd
      exact absurd hodd (by norm_num)
  rw [hvw, ho1, one_mul]

theorem isTI_barY (hE : EpsIn M V h) :
    CGT.Timmesfeld75.IsTI (barY h V) := by
  intro g
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥(yOf h)) g
  rw [barY_conj h y.2 hE.le_yOf]
  by_cases hbot : barY h V ⊓ barY h (conjSubgroup (y : G) V) = ⊥
  · exact Or.inl hbot
  · right
    obtain ⟨x, hxne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hbot
    obtain ⟨hxV, hxVy⟩ := Subgroup.mem_inf.mp x.2
    rw [mem_barY_iff h hE.le_yOf] at hxV
    rw [mem_barY_iff h (hE.conjSubgroup_le_yOf y.2)] at hxVy
    obtain ⟨a, ha⟩ := hxV
    obtain ⟨b, hb⟩ := hxVy
    have hq : barMap h hE.le_yOf a = barMap h (hE.conjSubgroup_le_yOf y.2) b := by
      rw [ha, hb]
    have hab : (a : G) = (b : G) := hE.eq_of_barMap_eq y.2 a.2 b.2 hq
    have hane : (a : G) ≠ 1 := by
      intro h1
      apply hxne
      apply Subtype.ext
      have ha1 : a = 1 := Subtype.ext h1
      rw [← ha, ha1]
      simp [barMap]
    have hmem : (a : G) ∈ V ⊓ conjSubgroup (y : G) V :=
      ⟨a.2, hab.symm ▸ b.2⟩
    have hne : V ⊓ conjSubgroup (y : G) V ≠ ⊥ := by
      intro hbot'
      have : (a : G) = 1 := Subgroup.mem_bot.mp (hbot' ▸ Subgroup.mem_inf.mpr hmem)
      exact hane this
    rw [conjSubgroup_eq_of_isTI hE.root.ti hne, inf_idem]

theorem normalizer_barY (hE : EpsIn M V h) :
    Subgroup.normalizer (barY h V : Set (YBar h)) = barY h (rOf M h) := by
  ext g
  constructor
  · intro hg
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥(yOf h)) g
    have hconj : conjSubgroup (QuotientGroup.mk' (pPrimeCore 2 ↥(yOf h))
        (⟨(y : G), y.2⟩ : ↥(yOf h))) (barY h V) = barY h V :=
      conjSubgroup_eq_self_iff.mpr hg
    rw [barY_conj h y.2 hE.le_yOf] at hconj
    have hle : conjSubgroup (y : G) V ≤ V := by
      intro x hx
      have hxY : (x : G) ∈ yOf h := hE.conjSubgroup_le_yOf y.2 hx
      have hxbar : (QuotientGroup.mk' (pPrimeCore 2 ↥(yOf h))
          (⟨x, hxY⟩ : ↥(yOf h))) ∈ barY h V := by
        rw [← hconj]
        rw [mem_barY_iff h (hE.conjSubgroup_le_yOf y.2)]
        exact ⟨⟨x, hx⟩, rfl⟩
      rw [mem_barY_iff h hE.le_yOf] at hxbar
      obtain ⟨v, hv⟩ := hxbar
      have hvx : (v : G) = x := by
        have hb : barMap h hE.le_yOf v =
            barMap h (hE.conjSubgroup_le_yOf y.2) ⟨x, hx⟩ := by
          rw [hv]
          apply congrArg (QuotientGroup.mk' (pPrimeCore 2 ↥(yOf h)))
          apply Subtype.ext
          rfl
        exact hE.eq_of_barMap_eq y.2 v.2 hx hb
      rw [← hvx]
      exact v.2
    have hyV : conjSubgroup (y : G) V = V :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjSubgroup])
    have hyM : (y : G) ∈ M := hE.root.normalizer_eq ▸ conjSubgroup_eq_self_iff.mp hyV
    have hyR : (y : G) ∈ rOf M h := ⟨hyM, y.2⟩
    rw [mem_barY_iff h (rOf_le_yOf (M := M) (h := h))]
    exact ⟨⟨(y : G), hyR⟩, by
      apply congrArg (QuotientGroup.mk' (pPrimeCore 2 ↥(yOf h)))
      apply Subtype.ext
      rfl⟩
  · intro hg
    rw [mem_barY_iff h (rOf_le_yOf (M := M) (h := h))] at hg
    obtain ⟨r, hr⟩ := hg
    rw [← hr]
    have hrM : (r : G) ∈ M := (Subgroup.mem_inf.mp r.2).1
    have hrY : (r : G) ∈ yOf h := (Subgroup.mem_inf.mp r.2).2
    have hV : conjSubgroup (r : G) V = V :=
      conjSubgroup_eq_self_iff.mpr (hE.root.le_normalizer hrM)
    have hq : barMap h (rOf_le_yOf (M := M) (h := h)) r =
        QuotientGroup.mk' (pPrimeCore 2 ↥(yOf h)) ⟨(r : G), hrY⟩ := by
      apply congrArg (QuotientGroup.mk' (pPrimeCore 2 ↥(yOf h)))
      apply Subtype.ext
      rfl
    rw [← conjSubgroup_eq_self_iff]
    rw [hq, barY_conj h hrY hE.le_yOf, hV]

theorem inf_centralizer_le_V (hE : EpsIn M V h) {T : Subgroup G} (hTR : T ≤ rOf M h)
    (hP0T : p0Of M V (Subgroup.zpowers h) ≤ T) (hT2 : IsPGroup 2 T) :
    T ⊓ Subgroup.centralizer (T : Set G) ≤ V := by
  intro z hz
  obtain ⟨hzT, hzC⟩ := Subgroup.mem_inf.mp hz
  have hzR : z ∈ rOf M h := hTR hzT
  have hzP0 : z ∈ cenOf (p0Of M V (Subgroup.zpowers h)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    exact Subgroup.mem_centralizer_iff.mp hzC p (hP0T hp)
  have hzOV : z ∈ oOf M h ⊔ V := by
    rw [← hE.cen]
    exact ⟨hzR, hzP0⟩
  have hz2 : ∃ k, orderOf z = 2 ^ k := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hT2) ⟨z, hzT⟩
    exact ⟨k, by simpa using hk⟩
  exact hE.mem_V_of_mem_oOf_sup_V hzOV hz2

private theorem conjSubgroup_eq_of_normalizes_twoGroup (hE : EpsIn M V h)
    {T : Subgroup G} {x : G} (hT2 : IsPGroup 2 T) (hTne : T ≠ ⊥)
    (hZT : T ⊓ Subgroup.centralizer (T : Set G) ≤ V)
    (hxT : x ∈ Subgroup.normalizer (T : Set G)) :
    conjSubgroup x V = V := by
  haveI : Nontrivial ↥T := (Subgroup.nontrivial_iff_ne_bot T).mpr hTne
  haveI : Nontrivial ↥(Subgroup.center ↥T) := hT2.center_nontrivial
  obtain ⟨w, hw1⟩ := exists_ne (1 : Subgroup.center ↥T)
  let Z : Subgroup G := T ⊓ Subgroup.centralizer (T : Set G)
  have hwT : ((w : ↥T) : G) ∈ T := (w : ↥T).2
  have hwC : ((w : ↥T) : G) ∈ Subgroup.centralizer (T : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun t ht =>
      congrArg Subtype.val (Subgroup.mem_center_iff.mp w.2 ⟨t, ht⟩)
  have hwZ : ((w : ↥T) : G) ∈ Z := ⟨hwT, hwC⟩
  have hwne : ((w : ↥T) : G) ≠ 1 := by
    intro h
    exact hw1 (Subtype.ext (Subtype.ext h))
  have hZne : Z ≠ ⊥ := fun hbot => hwne (Subgroup.mem_bot.mp (hbot ▸ hwZ))
  have hWZ : (Subgroup.center ↥T).map T.subtype = Z := by
    ext z
    constructor
    · rintro ⟨c, hc, rfl⟩
      refine ⟨(c : ↥T).2, ?_⟩
      exact Subgroup.mem_centralizer_iff.mpr fun t ht =>
        congrArg Subtype.val (Subgroup.mem_center_iff.mp hc ⟨t, ht⟩)
    · rintro ⟨hzT, hzC⟩
      refine ⟨⟨z, hzT⟩, ?_, rfl⟩
      refine Subgroup.mem_center_iff.mpr fun t => ?_
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp hzC t t.2
  have hxNZ : x ∈ Subgroup.normalizer (Z : Set G) := by
    rw [← hWZ]
    exact mem_normalizer_map_subtype_of_characteristic hxT (Subgroup.center ↥T)
  have hVx : V ⊓ conjSubgroup x V ≠ ⊥ := by
    intro hbot
    obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZne
    have hzV : (z : G) ∈ V := hZT z.2
    have hzVx : (z : G) ∈ conjSubgroup x V := by
      rw [mem_conjSubgroup]
      have hxinvNZ : x⁻¹ ∈ Subgroup.normalizer (Z : Set G) := Subgroup.inv_mem _ hxNZ
      have hmemZ : x⁻¹ * (z : G) * x ∈ Z := by
        simpa only [inv_inv] using
          (Subgroup.mem_normalizer_iff.mp hxinvNZ (z : G)).mp z.2
      exact hZT hmemZ
    have hzbot : (z : G) ∈ (⊥ : Subgroup G) := by
      rw [← hbot]
      exact Subgroup.mem_inf.mpr ⟨hzV, hzVx⟩
    exact hz1 (Subtype.ext (Subgroup.mem_bot.mp hzbot))
  exact conjSubgroup_eq_of_isTI hE.root.ti hVx

private theorem exists_sylow_above_p0 :
    ∃ S : Sylow 2 ↥(yOf h), p0Of M V (Subgroup.zpowers h) ≤
      ((S : Subgroup ↥(yOf h)).map (yOf h).subtype) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP0_2 : IsPGroup 2 (p0Of M V (Subgroup.zpowers h)) := by
    rw [p0Of]
    exact (inSubgroup_pCore_two M).1.to_le (inf_le_left.trans inf_le_left)
  obtain ⟨S, hP0S⟩ : ∃ S : Sylow 2 ↥(yOf h),
      (p0Of M V (Subgroup.zpowers h)).subgroupOf (yOf h) ≤
        (S : Subgroup ↥(yOf h)) :=
    (hP0_2.comap_subtype).exists_le_sylow
  refine ⟨S, ?_⟩
  have hmap : p0Of M V (Subgroup.zpowers h) =
      ((p0Of M V (Subgroup.zpowers h)).subgroupOf (yOf h)).map (yOf h).subtype :=
    (Subgroup.map_subgroupOf_eq_of_le (inf_le_right :
      p0Of M V (Subgroup.zpowers h) ≤ yOf h)).symm
  rw [hmap]
  exact Subgroup.map_mono hP0S

private theorem sylow_le_rOf (hE : EpsIn M V h) {S : Sylow 2 ↥(yOf h)} {P0 : Subgroup G}
    (hP0 : P0 = p0Of M V (Subgroup.zpowers h))
    (hP0S : P0 ≤ ((S : Subgroup ↥(yOf h)).map (yOf h).subtype)) :
    ((S : Subgroup ↥(yOf h)).map (yOf h).subtype) ≤ rOf M h := by
  let Sfun : Subgroup G := (S : Subgroup ↥(yOf h)).map (yOf h).subtype
  have hS2 : IsPGroup 2 Sfun := (S.isPGroup').map (yOf h).subtype
  have hSfunY : Sfun ≤ yOf h := Subgroup.map_subtype_le _
  have hP0_R : P0 ≤ rOf M h := by
    rw [hP0]
    exact le_inf (inf_le_left.trans hE.root.Pc_le_M) inf_le_right
  by_contra hnot
  let T : Subgroup G := Sfun ⊓ rOf M h
  have hTlt : T < Sfun := by
    refine lt_of_le_of_ne inf_le_left ?_
    intro hEq
    apply hnot
    change Sfun ≤ rOf M h
    rw [← hEq]
    exact inf_le_right
  have hgrowth := CFSG.GroupTheory.FT63ChII.lt_inf_normalizer_of_lt (q := 2) hS2 hTlt
  obtain ⟨x, hxN, hxT⟩ := SetLike.exists_of_lt hgrowth
  have hxS : x ∈ Sfun := (Subgroup.mem_inf.mp hxN).1
  have hxNT : x ∈ Subgroup.normalizer (T : Set G) := (Subgroup.mem_inf.mp hxN).2
  have hxY : x ∈ yOf h := hSfunY hxS
  have hT2 : IsPGroup 2 T := hS2.to_le inf_le_left
  have hP0_T : P0 ≤ T := le_inf hP0S hP0_R
  have hP0_T' : p0Of M V (Subgroup.zpowers h) ≤ T := by rwa [← hP0]
  have hVT : V ≤ T := hE.le_p0.trans hP0_T'
  have hTne : T ≠ ⊥ := fun hbot => hE.root.ne_bot (le_bot_iff.mp (hVT.trans_eq hbot))
  let Z : Subgroup G := T ⊓ Subgroup.centralizer (T : Set G)
  have hZV : Z ≤ V := hE.inf_centralizer_le_V inf_le_right hP0_T' hT2
  have hxV : conjSubgroup x V = V :=
    hE.conjSubgroup_eq_of_normalizes_twoGroup hT2 hTne hZV hxNT
  have hxM : x ∈ M := hE.root.normalizer_eq ▸ conjSubgroup_eq_self_iff.mp hxV
  exact hxT (Subgroup.mem_inf.mpr ⟨hxS, ⟨hxM, hxY⟩⟩)

private theorem eq_one_of_commute_of_odd_orderOf_of_dvd_two {H : Type*} [Group H]
    {a b : H} (hcomm : Commute a b) (ha : Odd (orderOf a)) (hb : orderOf b ∣ 2)
    {k : ℕ} (hk : orderOf (a * b) = 2 ^ k) : a = 1 := by
  have hcop : Nat.Coprime (orderOf a) (orderOf b) :=
    (Nat.coprime_two_right.mpr ha).coprime_dvd_right hb
  have hmul := hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hcop
  have hdvd : orderOf a ∣ 2 ^ k := by
    calc orderOf a ∣ orderOf a * orderOf b := dvd_mul_right _ _
      _ = orderOf (a * b) := hmul.symm
      _ = 2 ^ k := hk
  exact orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes (ha.coprime_two_right.pow_right k) (dvd_refl _) hdvd)

private theorem exists_mem_V_centralized (hE : EpsIn M V h) {S : Sylow 2 ↥(yOf h)}
    (hP0S : p0Of M V (Subgroup.zpowers h) ≤
      ((S : Subgroup ↥(yOf h)).map (yOf h).subtype))
    (hSZ : ((S : Subgroup ↥(yOf h)).map (yOf h).subtype) ⊓
      Subgroup.centralizer (((S : Subgroup ↥(yOf h)).map (yOf h).subtype) : Set G) ≤ V)
    {c : ↥(yOf h)}
    (hcCent : c ∈ Subgroup.centralizer ((S : Subgroup ↥(yOf h)) : Set ↥(yOf h))) :
    ∃ z : G, z ∈ V ∧ z ≠ 1 ∧ (c : G) * z = z * (c : G) := by
  let Sfun : Subgroup G := (S : Subgroup ↥(yOf h)).map (yOf h).subtype
  have hSne : (S : Subgroup ↥(yOf h)) ≠ ⊥ := by
    intro hbot
    have hbot' : Sfun ≤ ⊥ := by simpa [Sfun, hbot]
    exact hE.root.ne_bot (le_bot_iff.mp (hE.le_p0.trans (hP0S.trans hbot')))
  haveI : Nontrivial ↥(S : Subgroup ↥(yOf h)) :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr hSne
  haveI : Nontrivial ↥(Subgroup.center ↥(S : Subgroup ↥(yOf h))) :=
    S.isPGroup'.center_nontrivial
  obtain ⟨sZ, hsZ1⟩ := exists_ne (1 : Subgroup.center ↥(S : Subgroup ↥(yOf h)))
  let s : ↥(yOf h) := ((sZ : ↥(S : Subgroup ↥(yOf h))) : ↥(yOf h))
  let z : G := (s : G)
  have hsS : s ∈ (S : Subgroup ↥(yOf h)) := (sZ : ↥(S : Subgroup ↥(yOf h))).2
  have hzSfun : z ∈ Sfun := ⟨s, hsS, rfl⟩
  have hzCent : z ∈ Subgroup.centralizer (Sfun : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    obtain ⟨tY, htY, rfl⟩ := Subgroup.mem_map.mp ht
    have hcommS := Subgroup.mem_center_iff.mp sZ.2 ⟨tY, htY⟩
    have hcommY : tY * s = s * tY := by
      have := congrArg (fun x : ↥(S : Subgroup ↥(yOf h)) => (x : ↥(yOf h))) hcommS
      simpa [s] using this
    exact Subtype.ext_iff.mp hcommY
  have hzV : z ∈ V := hSZ ⟨hzSfun, hzCent⟩
  have hzne : z ≠ 1 := by
    intro h
    apply hsZ1
    exact Subtype.ext (Subtype.ext (Subtype.ext h))
  have hcz : (c : G) * z = z * (c : G) := by
    have h := Subgroup.mem_centralizer_iff.mp hcCent
      (⟨s, hsS⟩ : ↥(S : Subgroup ↥(yOf h))) hsS
    exact (Subtype.ext_iff.mp h).symm
  exact ⟨z, hzV, hzne, hcz⟩

private theorem exists_mem_sup_of_mem_centralizer (hE : EpsIn M V h)
    {S : Sylow 2 ↥(yOf h)} {Sbar : Sylow 2 (YBar h)}
    (hP0S : p0Of M V (Subgroup.zpowers h) ≤
      ((S : Subgroup ↥(yOf h)).map (yOf h).subtype))
    (hSZ : ((S : Subgroup ↥(yOf h)).map (yOf h).subtype) ⊓
      Subgroup.centralizer (((S : Subgroup ↥(yOf h)).map (yOf h).subtype) : Set G) ≤ V)
    (hSbar_map : (Sbar : Subgroup (YBar h)) =
      (S : Subgroup ↥(yOf h)).map (QuotientGroup.mk' (pPrimeCore 2 ↥(yOf h))))
    {zbar : YBar h} (hzbar : zbar ∈ (Sbar : Subgroup (YBar h)) ⊓
      Subgroup.centralizer ((Sbar : Subgroup (YBar h)) : Set (YBar h))) :
    ∃ c : ↥(yOf h), (c : G) ∈ oOf M h ⊔ V ∧
      QuotientGroup.mk' (pPrimeCore 2 ↥(yOf h)) c = zbar := by
  let Sfun : Subgroup G := (S : Subgroup ↥(yOf h)).map (yOf h).subtype
  obtain ⟨hzSbar, hzCbar⟩ := Subgroup.mem_inf.mp hzbar
  have hNodd : ¬ 2 ∣ Nat.card (pPrimeCore 2 ↥(yOf h)) := by
    have hcop := pPrimeCore_coprime_card (p := 2) (G := ↥(yOf h))
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp hcop
  have hcentmap := CFSG.Semidihedral.Local.map_centralizer_eq_of_coprime (p := 2)
    (G := ↥(yOf h)) (pPrimeCore 2 ↥(yOf h)) hNodd (S : Subgroup ↥(yOf h)) S.isPGroup'
  rw [hSbar_map] at hzCbar
  rw [← hcentmap] at hzCbar
  obtain ⟨c, hcCent, hcq⟩ := Subgroup.mem_map.mp hzCbar
  obtain ⟨z, hzV, hzne, hcz⟩ := hE.exists_mem_V_centralized hP0S hSZ hcCent
  have hcM : (c : G) ∈ M :=
    hE.root.centralizer_le_M hzV hzne
      (Subgroup.mem_centralizer_iff.mpr fun y hy => by
        rw [Set.mem_singleton_iff] at hy
        subst y
        exact hcz.symm)
  have hcP0 : (c : G) ∈ cenOf (p0Of M V (Subgroup.zpowers h)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    have hpS : p ∈ Sfun := hP0S hp
    obtain ⟨pY, hpY, hpYeq⟩ := Subgroup.mem_map.mp hpS
    have hcomm := Subgroup.mem_centralizer_iff.mp hcCent pY hpY
    have hcomm' : (pY : G) * (c : G) = (c : G) * (pY : G) :=
      congrArg (fun x : ↥(yOf h) => (x : G)) hcomm
    simpa [← hpYeq] using hcomm'
  have hcR : (c : G) ∈ rOf M h := ⟨hcM, c.2⟩
  refine ⟨c, ?_, hcq⟩
  rw [← hE.cen]
  exact ⟨hcR, hcP0⟩

private theorem mem_barY_of_mem_sup (hE : EpsIn M V h) {Sbar : Sylow 2 (YBar h)}
    {zbar : YBar h} (hzSbar : zbar ∈ (Sbar : Subgroup (YBar h)))
    {c : ↥(yOf h)} (hcOV : (c : G) ∈ oOf M h ⊔ V)
    (hcq : QuotientGroup.mk' (pPrimeCore 2 ↥(yOf h)) c = zbar) :
    zbar ∈ barY h V := by
  have hOVnorm : V ≤ Subgroup.normalizer (oOf M h : Set G) :=
    hE.le_rOf.trans
      (le_normalizer_map_subtype (rOf M h) (pPrimeCore 2 ↥(rOf M h)))
  obtain ⟨o, ho, v, hv, hcov⟩ := exists_mul_of_mem_sup hOVnorm hcOV
  have hoY : o ∈ yOf h := rOf_le_yOf (oOf_le_rOf ho)
  have hvY : v ∈ yOf h := hE.le_yOf hv
  let q := QuotientGroup.mk' (pPrimeCore 2 ↥(yOf h))
  let qo : YBar h := q ⟨o, hoY⟩
  let qv : YBar h := q ⟨v, hvY⟩
  have hqc : q c = qo * qv := by
    have hcY : c = (⟨o, hoY⟩ : ↥(yOf h)) * ⟨v, hvY⟩ := by
      apply Subtype.ext
      simpa using hcov
    rw [hcY, map_mul]
  have hcomm_ov : o * v = v * o := hE.oOf_commute_V ho hv
  have hcomm_q : Commute qo qv := by
    have hcomm_sub : (⟨o, hoY⟩ : ↥(yOf h)) * ⟨v, hvY⟩ =
        (⟨v, hvY⟩ : ↥(yOf h)) * ⟨o, hoY⟩ := by
      apply Subtype.ext
      simpa using hcomm_ov
    rw [commute_iff_eq,
      show qo = q ⟨o, hoY⟩ from rfl, show qv = q ⟨v, hvY⟩ from rfl,
      ← map_mul, ← map_mul, hcomm_sub]
  have hodd_qo : Odd (orderOf qo) :=
    Odd.of_dvd_nat
      (hE.odd_oOf.of_dvd_nat (Subgroup.orderOf_dvd_natCard (oOf M h) ho))
      (by simpa [qo, Subgroup.orderOf_coe] using orderOf_map_dvd q ⟨o, hoY⟩)
  have hv2 : v * v = 1 := by
    have := hE.root.elem.2 v hv
    rwa [pow_two] at this
  have hdvd_qv : orderOf qv ∣ 2 := by
    have hvpow : (⟨v, hvY⟩ : ↥(yOf h)) ^ 2 = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, pow_two]
      exact hv2
    have hqv2 : qv ^ 2 = 1 := by
      rw [show qv = q ⟨v, hvY⟩ from rfl, ← map_pow, hvpow, map_one]
    exact orderOf_dvd_of_pow_eq_one (by simpa [pow_two] using hqv2)
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp Sbar.isPGroup') ⟨zbar, hzSbar⟩
  have horder_qc : orderOf (q c) = 2 ^ k := by
    rw [hcq]
    simpa using hk
  have hqo1 : qo = 1 := by
    refine eq_one_of_commute_of_odd_orderOf_of_dvd_two (k := k) hcomm_q hodd_qo hdvd_qv ?_
    rw [← hqc]
    exact horder_qc
  have hqv_bar : qv ∈ barY h V := by
    rw [mem_barY_iff h hE.le_yOf]
    refine ⟨⟨v, hv⟩, ?_⟩
    apply congrArg q
    apply Subtype.ext
    rfl
  rw [← hcq, hqc, hqo1, one_mul]
  exact hqv_bar

theorem exists_sylow (hE : EpsIn M V h) :
    ∃ (S : Sylow 2 ↥(yOf h)) (Sbar : Sylow 2 (YBar h)),
      ((S : Subgroup ↥(yOf h)).map (yOf h).subtype) ≤ rOf M h ∧
      p0Of M V (Subgroup.zpowers h) ≤ ((S : Subgroup ↥(yOf h)).map (yOf h).subtype) ∧
      ((S : Subgroup ↥(yOf h)).map (yOf h).subtype) ⊓
        Subgroup.centralizer (((S : Subgroup ↥(yOf h)).map (yOf h).subtype) : Set G) ≤ V ∧
      (Sbar : Subgroup (YBar h)) =
        barY h ((S : Subgroup ↥(yOf h)).map (yOf h).subtype) ∧
      (Sbar : Subgroup (YBar h)) ⊓
        Subgroup.centralizer ((Sbar : Subgroup (YBar h)) : Set (YBar h)) ≤ barY h V := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P0 : Subgroup G := p0Of M V (Subgroup.zpowers h) with hP0
  obtain ⟨S, hP0_Sfun⟩ := exists_sylow_above_p0 (M := M) (V := V) (h := h)
  rw [← hP0] at hP0_Sfun
  let Sfun : Subgroup G := (S : Subgroup ↥(yOf h)).map (yOf h).subtype
  have hS2 : IsPGroup 2 Sfun := (S.isPGroup').map (yOf h).subtype
  have hSR : Sfun ≤ rOf M h := hE.sylow_le_rOf hP0 hP0_Sfun
  let Sbar : Sylow 2 (YBar h) :=
    Sylow.mapSurjective (QuotientGroup.mk'_surjective (pPrimeCore 2 ↥(yOf h))) S
  have hSbar_map : (Sbar : Subgroup (YBar h)) =
      (S : Subgroup ↥(yOf h)).map (QuotientGroup.mk' (pPrimeCore 2 ↥(yOf h))) :=
    Sylow.coe_mapSurjective (QuotientGroup.mk'_surjective (pPrimeCore 2 ↥(yOf h))) S
  have hSbar_eq : (Sbar : Subgroup (YBar h)) = barY h Sfun := by
    rw [hSbar_map, barY_map_subtype]
  have hSZ : Sfun ⊓ Subgroup.centralizer (Sfun : Set G) ≤ V :=
    hE.inf_centralizer_le_V hSR hP0_Sfun hS2
  have hZbar : (Sbar : Subgroup (YBar h)) ⊓
      Subgroup.centralizer ((Sbar : Subgroup (YBar h)) : Set (YBar h)) ≤ barY h V := by
    intro zbar hzbar
    obtain ⟨c, hcOV, hcq⟩ :=
      hE.exists_mem_sup_of_mem_centralizer hP0_Sfun hSZ hSbar_map hzbar
    exact hE.mem_barY_of_mem_sup (Subgroup.mem_inf.mp hzbar).1 hcOV hcq
  exact ⟨S, Sbar, hSR, hP0_Sfun, hSZ, hSbar_eq, hZbar⟩

theorem mem_rOf_of_bar_mem (hE : EpsIn M V h) {z : G} (hz : z ∈ yOf h)
    (hbar : (QuotientGroup.mk' (pPrimeCore 2 ↥(yOf h))) ⟨z, hz⟩ ∈
      barY h (rOf M h)) : z ∈ rOf M h := by
  rw [mem_barY_iff h (rOf_le_yOf (M := M) (h := h))] at hbar
  obtain ⟨r, hr⟩ := hbar
  have hdiv := (QuotientGroup.eq_iff_div_mem).mp hr.symm
  have hmemO : z * (r : G)⁻¹ ∈ inSubgroup (pPrimeCore 2) (yOf h) := by
    refine ⟨⟨z, hz⟩ / Subgroup.inclusion (rOf_le_yOf (M := M) (h := h)) r, hdiv, ?_⟩
    simp [Subgroup.coe_inclusion, div_eq_mul_inv]
  have hmemR : z * (r : G)⁻¹ ∈ rOf M h :=
    (oOf_le_rOf (M := M) (h := h)) ((hE.oddCore_yOf_le).1 hmemO)
  rw [show z = (z * (r : G)⁻¹) * r by group]
  exact (rOf M h).mul_mem hmemR r.2

theorem commute_of_conj_mem_rOf (hE : EpsIn M V h) {x v : G} (hx : x ∈ yOf h)
    (hv : v ∈ V) (hv1 : v ≠ 1) (hmem : x * v * x⁻¹ ∈ rOf M h) :
    ∀ a ∈ V, ∀ b ∈ conjSubgroup x V, a * b = b * a := by
  have hz : x * v * x⁻¹ ∈ conjSubgroup x V := by
    rw [mem_conjSubgroup]
    rw [show x⁻¹ * (x * v * x⁻¹) * x = v by group]
    exact hv
  have hzM : x * v * x⁻¹ ∈ M := (Subgroup.mem_inf.mp hmem).1
  have hz1 : x * v * x⁻¹ ≠ 1 := by
    intro h
    apply hv1
    rw [show v = x⁻¹ * (x * v * x⁻¹) * x by group, h, mul_one]
    group
  have hne : conjSubgroup x V ⊓ M ≠ ⊥ := by
    intro hbot
    exact hz1 (Subgroup.mem_bot.mp (hbot ▸ Subgroup.mem_inf.mpr ⟨hz, hzM⟩))
  exact hE.root.commute_of_conj_inf_ne_bot hE.root.rootType hne

private theorem exists_central_pCore {K : Subgroup (YBar h)} {Sbar : Sylow 2 (YBar h)}
    (hSbarK : (Sbar : Subgroup (YBar h)) ≤ K) (hK : pCore 2 ↥K ≠ ⊥) :
    ∃ wK : ↥K, wK ∈ pCore 2 ↥K ∧ wK ≠ 1 ∧
      ((wK : YBar h) ∈ (Sbar : Subgroup (YBar h)) ∧
        (wK : YBar h) ∈
          Subgroup.centralizer ((Sbar : Subgroup (YBar h)) : Set (YBar h))) := by
  let SK : Sylow 2 ↥K := Sbar.subtype hSbarK
  let Q : Subgroup ↥K := pCore 2 ↥K
  have hQ2 : IsPGroup 2 Q := pCore_isPGroup
  have hQn : Q.Normal := pCore_normal
  have hQSK : Q ≤ (SK : Subgroup ↥K) := hQ2.le_sylow_of_normal SK
  let Q' : Subgroup ↥(SK : Subgroup ↥K) := Q.subgroupOf (SK : Subgroup ↥K)
  have hQ'n : Q'.Normal := hQn.subgroupOf (SK : Subgroup ↥K)
  have hQ'ne : Q' ≠ ⊥ := by
    intro hbot
    apply hK
    rw [eq_bot_iff]
    intro q hq
    have hqSK : q ∈ (SK : Subgroup ↥K) := hQSK hq
    have hmem : (⟨q, hqSK⟩ : ↥(SK : Subgroup ↥K)) ∈ Q' := by
      change (⟨q, hqSK⟩ : ↥(SK : Subgroup ↥K)) ∈ Q.subgroupOf (SK : Subgroup ↥K)
      exact Subgroup.mem_subgroupOf.mpr hq
    rw [hbot] at hmem
    have hq1 : (⟨q, hqSK⟩ : ↥(SK : Subgroup ↥K)) = 1 := Subgroup.mem_bot.mp hmem
    exact Subgroup.mem_bot.mpr
      (congrArg (fun x : ↥(SK : Subgroup ↥K) => ((x : ↥K))) hq1)
  have hQinf : Q' ⊓ Subgroup.center ↥(SK : Subgroup ↥K) ≠ ⊥ :=
    CFSG.GroupTheory.CoprimeActionSupport.NormalPSubgroupMeetsCenter.inf_center_ne_bot
      SK.isPGroup' Q' hQ'ne
  obtain ⟨w, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hQinf
  let wSK : ↥(SK : Subgroup ↥K) := (w : ↥(SK : Subgroup ↥K))
  let wK : ↥K := (wSK : ↥K)
  have hwQ' : wSK ∈ Q' := (Subgroup.mem_inf.mp w.2).1
  have hwC : wSK ∈ Subgroup.center ↥(SK : Subgroup ↥K) := (Subgroup.mem_inf.mp w.2).2
  have hwQ : wK ∈ Q := Subgroup.mem_subgroupOf.mp hwQ'
  have hwSK : wK ∈ (SK : Subgroup ↥K) := wSK.2
  have hwneK : wK ≠ 1 := by
    intro h
    exact hw1 (Subtype.ext (Subtype.ext h))
  refine ⟨wK, hwQ, hwneK, ?_, ?_⟩
  · rw [show (SK : Subgroup ↥K) = (Sbar : Subgroup (YBar h)).subgroupOf K from
      Sylow.coe_subtype Sbar hSbarK] at hwSK
    exact Subgroup.mem_subgroupOf.mp hwSK
  · rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have hsK : s ∈ K := hSbarK hs
    have hsSK : (⟨s, hsK⟩ : ↥K) ∈ (SK : Subgroup ↥K) := by
      rw [show (SK : Subgroup ↥K) = (Sbar : Subgroup (YBar h)).subgroupOf K from
        Sylow.coe_subtype Sbar hSbarK]
      exact Subgroup.mem_subgroupOf.mpr hs
    have hcomm := Subgroup.mem_center_iff.mp hwC
      (⟨⟨s, hsK⟩, hsSK⟩ : ↥(SK : Subgroup ↥K))
    exact congrArg (fun x : ↥(SK : Subgroup ↥K) => (((x : ↥K) : YBar h))) hcomm

private theorem map_pCore_le_barY (hE : EpsIn M V h) {K : Subgroup (YBar h)}
    {Sbar : Sylow 2 (YBar h)} (hSbarK : (Sbar : Subgroup (YBar h)) ≤ K)
    {wY : YBar h}
    (hwCbar : wY ∈ Subgroup.centralizer ((Sbar : Subgroup (YBar h)) : Set (YBar h)))
    (hwVbar : wY ∈ barY h V) (hwne : wY ≠ 1) :
    (pCore 2 ↥K).map K.subtype ≤ barY h (rOf M h) := by
  intro z hz
  rw [Subgroup.mem_map] at hz
  obtain ⟨q, hq, rfl⟩ := hz
  let SK : Sylow 2 ↥K := Sbar.subtype hSbarK
  have hQSK : pCore 2 ↥K ≤ (SK : Subgroup ↥K) :=
    pCore_isPGroup.le_sylow_of_normal SK
  have hqSK : q ∈ (SK : Subgroup ↥K) := hQSK hq
  have hqSbar : (q : YBar h) ∈ (Sbar : Subgroup (YBar h)) := by
    rw [show (SK : Subgroup ↥K) = (Sbar : Subgroup (YBar h)).subgroupOf K from
      Sylow.coe_subtype Sbar hSbarK] at hqSK
    exact Subgroup.mem_subgroupOf.mp hqSK
  have hcomm : (q : YBar h) * wY = wY * (q : YBar h) :=
    Subgroup.mem_centralizer_iff.mp hwCbar (q : YBar h) hqSbar
  have hmemconj : wY ∈ conjSubgroup (q : YBar h) (barY h V) := by
    rw [mem_conjSubgroup]
    rw [show (q : YBar h)⁻¹ * wY * (q : YBar h) = wY by
      calc (q : YBar h)⁻¹ * wY * (q : YBar h) =
          (q : YBar h)⁻¹ * (wY * (q : YBar h)) := by group
        _ = (q : YBar h)⁻¹ * ((q : YBar h) * wY) := by rw [← hcomm]
        _ = wY := by group]
    exact hwVbar
  have hinter : barY h V ⊓ conjSubgroup (q : YBar h) (barY h V) ≠ ⊥ := by
    intro hbot
    have hmem : wY ∈ (⊥ : Subgroup (YBar h)) := by
      rw [← hbot]
      exact Subgroup.mem_inf.mpr ⟨hwVbar, hmemconj⟩
    exact hwne (Subgroup.mem_bot.mp hmem)
  have hN : (q : YBar h) ∈ Subgroup.normalizer (barY h V : Set (YBar h)) := by
    rw [← conjSubgroup_eq_self_iff]
    rcases hE.isTI_barY (q : YBar h) with hbot | hT
    · exact absurd hbot hinter
    · have hle : barY h V ≤ conjSubgroup (q : YBar h) (barY h V) :=
        (hT.symm.le).trans inf_le_right
      have heq : barY h V = conjSubgroup (q : YBar h) (barY h V) :=
        Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjSubgroup])
      exact heq.symm
  rwa [hE.normalizer_barY] at hN

private theorem commute_of_mem_comap (hE : EpsIn M V h) {K : Subgroup (YBar h)}
    {wK : ↥K} (hwQ : wK ∈ pCore 2 ↥K) {v : ↥V} {hvY : (v : G) ∈ yOf h}
    (hvbar : (QuotientGroup.mk' (pPrimeCore 2 ↥(yOf h))) ⟨(v : G), hvY⟩ =
      (wK : YBar h))
    (hvne : (v : G) ≠ 1)
    (hQbar : (pCore 2 ↥K).map K.subtype ≤ barY h (rOf M h)) :
    ∀ x ∈ (K.comap (QuotientGroup.mk' (pPrimeCore 2 ↥(yOf h)))).map (yOf h).subtype,
      ∀ a ∈ V, ∀ b ∈ conjSubgroup x V, a * b = b * a := by
  let qY := QuotientGroup.mk' (pPrimeCore 2 ↥(yOf h))
  intro x hx a ha b hb
  obtain ⟨xY, hxY, rfl⟩ := Subgroup.mem_map.mp hx
  have hqK : qY xY ∈ K := hxY
  have hconjQ : (⟨qY xY, hqK⟩ : ↥K) * wK * (⟨qY xY, hqK⟩ : ↥K)⁻¹ ∈ pCore 2 ↥K :=
    pCore_normal.conj_mem wK hwQ ⟨qY xY, hqK⟩
  have hconjQbar : (qY xY : YBar h) * (wK : YBar h) * (qY xY : YBar h)⁻¹ ∈
      (pCore 2 ↥K).map K.subtype := by
    refine Subgroup.mem_map.mpr ⟨(⟨qY xY, hqK⟩ : ↥K) * wK *
      (⟨qY xY, hqK⟩ : ↥K)⁻¹, hconjQ, ?_⟩
    rfl
  have hqbarR : (qY xY : YBar h) * (wK : YBar h) * (qY xY : YBar h)⁻¹ ∈
      barY h (rOf M h) := hQbar hconjQbar
  have hwYv : (qY ⟨(v : G), hvY⟩ : YBar h) = (wK : YBar h) := hvbar
  have hxYv : (xY : G) * (v : G) * (xY : G)⁻¹ ∈ yOf h :=
    (yOf h).mul_mem ((yOf h).mul_mem xY.2 (hE.le_yOf v.2)) ((yOf h).inv_mem xY.2)
  have hmemBar : qY ⟨(xY : G) * (v : G) * (xY : G)⁻¹, hxYv⟩ ∈
      barY h (rOf M h) := by
    have heq : qY ⟨(xY : G) * (v : G) * (xY : G)⁻¹, hxYv⟩ =
        (qY xY : YBar h) * (wK : YBar h) * (qY xY : YBar h)⁻¹ := by
      rw [show (⟨(xY : G) * (v : G) * (xY : G)⁻¹, hxYv⟩ : ↥(yOf h)) =
          xY * (⟨(v : G), hvY⟩ : ↥(yOf h)) * xY⁻¹ by
        apply Subtype.ext
        rfl]
      rw [map_mul, map_mul, map_inv, hwYv]
    rw [heq]
    exact hqbarR
  have hxvR : (xY : G) * (v : G) * (xY : G)⁻¹ ∈ rOf M h :=
    hE.mem_rOf_of_bar_mem hxYv hmemBar
  exact hE.commute_of_conj_mem_rOf xY.2 v.2 hvne hxvR a ha b hb

private theorem isElemAbelian_closure_conj (hE : EpsIn M V h) {K' : Subgroup G}
    (hCommVx : ∀ x ∈ K', ∀ a ∈ V, ∀ b ∈ conjSubgroup x V, a * b = b * a) :
    Assembly.IsElemAbelian 2
      (Subgroup.closure {y : G | ∃ x : G, x ∈ K' ∧ y ∈ conjSubgroup x V}) := by
  refine CFSG.Open.IsElemAbelian.closure_of_commute (p := 2) ?_ ?_
  · rintro a ⟨x, hx, ha⟩ b ⟨x', hx', hb⟩
    have hyK : x⁻¹ * x' ∈ K' := K'.mul_mem (K'.inv_mem hx) hx'
    have hC := hCommVx (x⁻¹ * x') hyK
    have ha' : x⁻¹ * a * x ∈ V := mem_conjSubgroup.mp ha
    have hb' : x⁻¹ * b * x ∈ conjSubgroup (x⁻¹ * x') V := by
      rw [mem_conjSubgroup]
      have hbV : x'⁻¹ * b * x' ∈ V := mem_conjSubgroup.mp hb
      convert hbV using 1
      group
    have hcomm := hC (x⁻¹ * a * x) ha' (x⁻¹ * b * x) hb'
    calc a * b = x * ((x⁻¹ * a * x) * (x⁻¹ * b * x)) * x⁻¹ := by group
      _ = x * ((x⁻¹ * b * x) * (x⁻¹ * a * x)) * x⁻¹ := by rw [hcomm]
      _ = b * a := by group
  · rintro a ⟨x, hx, ha⟩
    have hel := (isElemAbelian_conjSubgroup hE.root.elem x).2 a ha
    simpa [pow_two] using hel

private theorem closure_conj_eq_V (hE : EpsIn M V h) {K' : Subgroup G}
    (hK'Y : K' ≤ yOf h) (hRK' : rOf M h ≤ K')
    (hCommVx : ∀ x ∈ K', ∀ a ∈ V, ∀ b ∈ conjSubgroup x V, a * b = b * a)
    (hW_el : Assembly.IsElemAbelian 2
      (Subgroup.closure {y : G | ∃ x : G, x ∈ K' ∧ y ∈ conjSubgroup x V})) :
    Subgroup.closure {y : G | ∃ x : G, x ∈ K' ∧ y ∈ conjSubgroup x V} = V := by
  let s : Set G := {y : G | ∃ x : G, x ∈ K' ∧ y ∈ conjSubgroup x V}
  let W : Subgroup G := Subgroup.closure s
  have hVW : V ≤ W := by
    intro a ha
    exact Subgroup.subset_closure ⟨1, K'.one_mem, by simpa [conjSubgroup_one] using ha⟩
  have hgenR : ∀ x ∈ K', conjSubgroup x V ≤ rOf M h := by
    intro x hx
    refine le_inf ?_ (hE.conjSubgroup_le_yOf (hK'Y hx))
    have hcomm : ∀ a ∈ V, ∀ b ∈ conjSubgroup x V, a * b = b * a := hCommVx x hx
    have hC : conjSubgroup x V ≤ Subgroup.centralizer (V : Set G) := by
      intro b hb
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact hcomm a ha b hb
    calc conjSubgroup x V ≤ Subgroup.normalizer (V : Set G) :=
          hC.trans (Subgroup.centralizer_le_normalizer _)
      _ = M := hE.root.normalizer_eq
  have hWR : W ≤ rOf M h := by
    change Subgroup.closure s ≤ rOf M h
    rw [Subgroup.closure_le]
    rintro a ⟨x, hx, ha⟩
    exact hgenR x hx ha
  have hset : ∀ k ∈ K', (MulAut.conj k) '' s = s := by
    intro k hk
    ext y
    constructor
    · rintro ⟨a, ⟨x, hx, ha⟩, rfl⟩
      refine ⟨k * x, K'.mul_mem hk hx, ?_⟩
      rw [conjSubgroup_mul]
      exact Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
    · rintro ⟨x, hx, hy⟩
      refine ⟨k⁻¹ * y * k, ⟨k⁻¹ * x, K'.mul_mem (K'.inv_mem hk) hx, ?_⟩,
        by rw [MulAut.conj_apply]; group⟩
      rw [conjSubgroup_mul]
      exact Subgroup.mem_map.mpr ⟨y, hy, by simp [MulAut.conj_apply]⟩
  have hK'N : K' ≤ Subgroup.normalizer (W : Set G) := by
    intro k hk
    rw [← conjSubgroup_eq_self_iff]
    change (Subgroup.closure s).map (MulAut.conj k).toMonoidHom = Subgroup.closure s
    rw [MonoidHom.map_closure]
    change Subgroup.closure ((MulAut.conj k) '' s) = Subgroup.closure s
    rw [hset k hk]
  have hmax : W ≤ V :=
    hE.maxEA.le_of_ge ⟨hWR, hRK'.trans hK'N, hW_el⟩ hVW
  exact le_antisymm hmax hVW

theorem le_of_pCore_ne_bot (hE : EpsIn M V h) {K : Subgroup (YBar h)}
    (hRK : barY h (rOf M h) ≤ K) (hK : pCore 2 ↥K ≠ ⊥) : K ≤ barY h (rOf M h) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, Sbar, hSR, hP0S, hZS, hSbar_eq, hZbar⟩ := hE.exists_sylow
  have hSbarK : (Sbar : Subgroup (YBar h)) ≤ K :=
    hSbar_eq.symm ▸ (barY_mono h hSR).trans hRK
  obtain ⟨wK, hwQ, hwneK, hwSbar, hwCbar⟩ := exists_central_pCore hSbarK hK
  have hwVbar : (wK : YBar h) ∈ barY h V := hZbar ⟨hwSbar, hwCbar⟩
  obtain ⟨v, hvbar⟩ := (mem_barY_iff h hE.le_yOf).mp hwVbar
  have hwne : (wK : YBar h) ≠ 1 := fun h => hwneK (Subtype.ext h)
  have hvne : (v : G) ≠ 1 := by
    intro h
    apply hwne
    rw [← hvbar, show v = 1 from Subtype.ext h]
    simp [barMap]
  have hQbar : (pCore 2 ↥K).map K.subtype ≤ barY h (rOf M h) :=
    hE.map_pCore_le_barY hSbarK hwCbar hwVbar hwne
  let qY := QuotientGroup.mk' (pPrimeCore 2 ↥(yOf h))
  let K' : Subgroup G := (K.comap qY).map (yOf h).subtype
  have hK'Y : K' ≤ yOf h := Subgroup.map_subtype_le _
  have hK'bar : barY h K' = K := by
    rw [show K' = (K.comap qY).map (yOf h).subtype from rfl, barY_map_subtype]
    exact Subgroup.map_comap_eq_self_of_surjective
      (QuotientGroup.mk'_surjective (pPrimeCore 2 ↥(yOf h))) K
  have hRK' : rOf M h ≤ K' := by
    intro r hr
    have hrY : (r : G) ∈ yOf h := rOf_le_yOf (M := M) (h := h) hr
    have hqK : qY ⟨(r : G), hrY⟩ ∈ K := by
      have hqbar : qY ⟨(r : G), hrY⟩ ∈ barY h (rOf M h) := by
        rw [mem_barY_iff h (rOf_le_yOf (M := M) (h := h))]
        exact ⟨⟨(r : G), hr⟩, rfl⟩
      exact hRK hqbar
    exact ⟨⟨(r : G), hrY⟩, hqK, rfl⟩
  have hCommVx : ∀ x ∈ K', ∀ a ∈ V, ∀ b ∈ conjSubgroup x V, a * b = b * a :=
    hE.commute_of_mem_comap hwQ hvbar hvne hQbar
  let W : Subgroup G :=
    Subgroup.closure {y : G | ∃ x : G, x ∈ K' ∧ y ∈ conjSubgroup x V}
  have hW_el : Assembly.IsElemAbelian 2 W :=
    hE.isElemAbelian_closure_conj hCommVx
  have hWV : W = V := hE.closure_conj_eq_V hK'Y hRK' hCommVx hW_el
  have hK'R : K' ≤ rOf M h := by
    intro x hx
    have hVxW : conjSubgroup x V ≤ W := by
      intro a ha
      exact Subgroup.subset_closure ⟨x, hx, ha⟩
    have hVxV : conjSubgroup x V ≤ V := hVxW.trans (le_of_eq hWV)
    have hVxEq : conjSubgroup x V = V :=
      Subgroup.eq_of_le_of_card_ge hVxV (by rw [card_conjSubgroup])
    exact ⟨hE.root.normalizer_eq ▸ conjSubgroup_eq_self_iff.mp hVxEq, hK'Y hx⟩
  intro q hq
  obtain ⟨x, hxq⟩ := (mem_barY_iff h hK'Y).mp (hK'bar.symm ▸ hq)
  rw [← hxq]
  have hxR : (x : G) ∈ rOf M h := hK'R x.2
  refine (mem_barY_iff h (rOf_le_yOf (M := M) (h := h))).mpr ⟨⟨(x : G), hxR⟩, ?_⟩
  apply congrArg qY
  apply Subtype.ext
  rfl

end EpsIn

end CFSG.RankThree.GF2n.Tim81
