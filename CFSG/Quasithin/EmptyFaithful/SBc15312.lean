module

public import CFSG.Quasithin.EmptyFaithful.SBc15312Core

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

namespace SBc

section Basic

variable {G : Type} [Group G] [Finite G]

theorem normalizes_of_inner {Yp L : Subgroup G} (h : InducesInnerModO2153 Yp L) :
    Yp ≤ Subgroup.normalizer (L : Set G) := by
  intro y hy
  refine A4.mem_normalizer_of_conj_mem fun x hx => ?_
  obtain ⟨l, hl, hl'⟩ := h y hy
  have h1 : y * x * y⁻¹ * (l * x * l⁻¹)⁻¹ ∈ L := pCoreOf_le 2 L (hl' x hx)
  have h2 : l * x * l⁻¹ ∈ L := L.mul_mem (L.mul_mem hl hx) (L.inv_mem hl)
  have e : y * x * y⁻¹ = (y * x * y⁻¹ * (l * x * l⁻¹)⁻¹) * (l * x * l⁻¹) := by group
  rw [e]
  exact L.mul_mem h1 h2

theorem pow_three_of_odd_of_struct {Yp : Subgroup G}
    (hF : IsElemAbelianOfRank 3 2 (OTwoQuot Yp) ∨ IsPOnePlusTwo 3 (OTwoQuot Yp)) {y : G}
    (hy : y ∈ Yp) (hodd : Odd (orderOf y)) : y ^ 3 = 1 := by
  have hp2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq := exp_three_of_struct hF (QuotientGroup.mk ⟨y, hy⟩)
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hq
  have hmem : y ^ 3 ∈ pCoreOf 2 Yp := (mem_pCore_iff' (L := Yp) _).mp hq
  obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 Yp ⟨y ^ 3, hmem⟩
  have h2k : (y ^ 3) ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hodd3 : Odd (orderOf (y ^ 3)) := Odd.of_dvd_nat hodd (orderOf_pow_dvd 3)
  have hcop : Nat.Coprime (orderOf (y ^ 3)) (2 ^ k) :=
    (Nat.coprime_two_right.mpr hodd3).pow_right k
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop (orderOf_dvd_of_pow_eq_one h2k))

omit [Finite G] in
theorem centerless_of_quasisimple {L : Subgroup G} (hperf : ⁅L, L⁆ = L) (hq : CFSG.IsQuasisimple ↥L)
    (hc : centerOf L = pCoreOf 2 L) :
    ∀ y ∈ L, (∀ l ∈ L, l * y * l⁻¹ * y⁻¹ ∈ pCoreOf 2 L) → y ∈ pCoreOf 2 L := by
  intro y hyL hy
  have : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hq.2.1
  have key := S153D.mem_of_commutators_mem hperf (Subgroup.center ↥L) (y := ⟨y, hyL⟩) (fun l => by
    have hmem : l * y * l⁻¹ * y⁻¹ ∈ pCoreOf 2 L := hy l l.2
    rw [← hc] at hmem
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    simpa using (Subgroup.mem_centralizer_iff.mp hmem.2 g.1 g.2))
  rw [← hc]
  refine ⟨hyL, Subgroup.mem_centralizer_iff.mpr fun l hl => ?_⟩
  have := Subgroup.mem_center_iff.mp key ⟨l, hl⟩
  simpa using congrArg Subtype.val this

theorem centralizerSection_eq_inf_centralizer {Yp L : Subgroup G} (hq : CFSG.IsQuasisimple ↥L)
    (hc : centerOf L = pCoreOf 2 L) :
    centralizerSection Yp L (pCoreOf 2 L) = Yp ⊓ Subgroup.centralizer (L : Set G) := by
  apply le_antisymm
  · intro m hm
    have hmY : m ∈ Yp := hm.1
    refine ⟨hmY, ?_⟩
    have hK : centralizerSection Yp L (pCoreOf 2 L) ≤ Subgroup.centralizer (L : Set G) := by
      have h1 : ⁅L, centralizerSection Yp L (pCoreOf 2 L)⁆ ≤ pCoreOf 2 L :=
        ((le_centralizerSection_iff (pCoreOf_le 2 L)).mp le_rfl).2
      have h2 : ⁅L, centralizerSection Yp L (pCoreOf 2 L)⁆ ≤ Subgroup.centralizer (L : Set G) :=
        h1.trans (hc ▸ inf_le_right)
      have h3 := S153D.commutator_eq_bot_of_quasisimple hq h2
      exact Subgroup.le_centralizer_iff.mpr (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h3)
    exact hK hm
  · intro m hm
    refine (mem_centralizerSection_iff_of_le (pCoreOf_le 2 L)).mpr ⟨hm.1, fun z hz => ?_⟩
    have hcom : m * z = z * m := (Subgroup.mem_centralizer_iff.mp hm.2 z hz).symm
    have : z * m * z⁻¹ * m⁻¹ = 1 := by
      rw [← hcom]
      group
    rw [this]
    exact Subgroup.one_mem _

end Basic

section Main

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem YL153_ne_bot_of_normalizes (h : Hyp15310 G T Mc M V₁ V₂ Yp t)
    (hI : IsHPlus Yp (Sgp153 T V₁) M I) (h3 : CFSG.Open.pRank 3 Yp = 2) (hLI : L ≤ I)
    (hYN : Yp ≤ Subgroup.normalizer (L : Set G)) (hL3 : 1 ≤ CFSG.Open.pRank 3 L) :
    YL153 Yp L ≠ ⊥ := by
  have hp : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro hbot
  have hYI : Yp ≤ I := le_sup_left.trans hI.1.1
  have hLN : L ≤ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer
  obtain ⟨E, hEY, hE, hE9⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 3) Yp
  rw [h3] at hE9
  have hEL : E ⊓ L = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxE, hxL⟩
    have hx3 : x ^ 3 = 1 := hE.2 x hxE
    have hodd : Odd (orderOf x) :=
      Odd.of_dvd_nat (by decide : Odd 3) (orderOf_dvd_of_pow_eq_one hx3)
    have : x ∈ YL153 Yp L := mem_oTwoUpper_of_odd ⟨hEY hxE, hxL⟩ hodd
    rw [hbot] at this
    exact this
  obtain ⟨EL, hELL, hELe, hELc⟩ := CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank
    (p := 3) hL3
  have h3L : 3 ∣ Nat.card L := by
    have : Nat.card EL ∣ Nat.card L := Subgroup.card_dvd_of_le hELL
    rw [hELc] at this
    simpa using this
  set X : Subgroup G := L ⊔ Yp with hX
  have hXN : X ≤ Subgroup.normalizer (L : Set G) := sup_le hLN hYN
  have hn : (L.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hXN
  have h3X : 3 ≤ CFSG.Open.pRank 3 X :=
    S153D.three_le_pRank_of_acts le_sup_left hn (hEY.trans le_sup_right) hE
      (by rw [hE9]; norm_num) hEL h3L
  have hXI : X ≤ I := sup_le hLI hYI
  have h2 := pRank_le_two_of_pCoreOf_ne_bot h.hyp.qtfe.qtke hI.1.2 Nat.prime_three (by norm_num)
  have h4 := CFSG.SectionRank.pRank_mono (by norm_num : 1 < 3) hXI
  omega

end Main

end SBc

theorem input15312Two_holds : Input15312Two := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c hr1 hinner
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.hyp
  have hLmem : L ∈ cComp I := c.c33.mem
  have hLI : L ≤ I := le_of_mem_cComp hLmem
  have hperf : ⁅L, L⁆ = L := hLmem.2.1
  have hYN : Yp ≤ Subgroup.normalizer (L : Set G) := SBc.normalizes_of_inner hinner
  have hstruct := c.facts11.struct_Yp
  have hexp : ∀ y ∈ Yp, Odd (orderOf y) → y ^ 3 = 1 := fun y hy ho =>
    SBc.pow_three_of_odd_of_struct hstruct hy ho
  have hne : oTwoUpper (Yp ⊓ L) ≠ ⊥ :=
    SBc.YL153_ne_bot_of_normalizes hh c.inH c.rank hLI hYN c.c34.rank
  have hcenterless := SBc.centerless_of_quasisimple hperf c.c33.quasisimple c.c33.center_eq
  have h3dvd : 3 ∣ Nat.card ↥(Yp ⊓ L) :=
    (SBc.three_dvd_card_oTwoUpper hexp (inf_le_left : Yp ⊓ L ≤ Yp) hne).trans
      (Subgroup.card_dvd_of_le (oTwoUpper_le _))
  have hcore := SBc.core15312Two ⟨⟨hYN, hcenterless, hinner⟩, hexp, hr1, h3dvd⟩ hh.oTwoUpper_eq c.rank
    hne hstruct
  rwa [SBc.centralizerSection_eq_inf_centralizer c.c33.quasisimple c.c33.center_eq] at hcore

end CFSG.Quasithin
