module

public import CFSG.Quasithin.Vol2.Ch10SecKITr
public import CFSG.Quasithin.Vol2.Ch10SecKITl
public import CFSG.RankThree.ThinCatalog.MathieuThreeRank

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.C10KH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.Vol2.Ch10.SecF
open CFSG.Quasithin.Vol2.Ch10.SecC.C10KH (isPSL_of_top isAlt_of_top isHat_of_top)

variable {G : Type} [Group G] [Finite G] {M T L X X₁ X₂ : Subgroup G}

theorem simple_top_of {Y : Type} [Group Y] [Finite Y] [IsSimpleGroup Y] {r : ℕ}
    (hr : r ∣ Nat.card Y) : IsSimpleGroup ↥(⊤ : Subgroup Y) ∧ r ∣ Nat.card ↥(⊤ : Subgroup Y) :=
  ⟨Subgroup.topEquiv.isSimpleGroup, by rw [Subgroup.card_top]; exact hr⟩

theorem simple_dvd_of_L2 {Y : Type} [Group Y] [Finite Y] {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : IsPSL 2 p e Y) (he : 1 ≤ e) : IsSimpleGroup Y ∧ p ∣ Nat.card Y := by
  refine ⟨(CFSG.LieType.Simplicity.fam_PSL_simplicity Y 2 p e h).2, ?_⟩
  rw [Ch11.SecA.card_of_isPSL (by norm_num) h]
  have hI : Finset.Icc 2 2 = {2} := by decide
  rw [hI, Finset.prod_singleton, show 2 * (2 - 1) / 2 = 1 by norm_num, pow_one]
  have hodd : Odd (p ^ e) := (hp.odd_of_ne_two hp2).pow
  have hg : Nat.gcd 2 (p ^ e - 1) = 2 := by
    have : 2 ∣ p ^ e - 1 := by
      obtain ⟨k, hk⟩ := hodd
      omega
    exact Nat.gcd_eq_left this
  rw [hg]
  have h2 : 2 ∣ (p ^ e) ^ 2 - 1 := by
    have : Odd ((p ^ e) ^ 2) := hodd.pow
    obtain ⟨k, hk⟩ := this
    omega
  rw [Nat.mul_div_assoc _ h2]
  exact (dvd_pow_self p (by omega)).mul_right _


theorem false_of_typeB (hK2 : KGA7OneA5) (hK3 : KGTwoA5Generate) (hK5 : KGJ4NoA5Block)
    (hT : IsSylowTwoOf T M) (hL : L ∈ cComp M) (hX₁ : X₁ ∈ lFamily T) (hX₂ : X₂ ∈ lFamily T)
    (hX₁L : X₁ ≤ L) (hX₂L : X₂ ≤ L) (h₁ : IsNatBlock X₁ 2) (h₂ : IsNatBlock X₂ 2)
    (hne : modO2Image L X₁ ≠ modO2Image L X₂)
    (hc₁ : Nat.card ↥(modO2Image L X₁) = 60) (hc₂ : Nat.card ↥(modO2Image L X₂) = 60)
    (ho : OutA5 ↥(⊤ : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L))) : False := by
  have hTs := C10E4.isSylowTwoOf_quot hT hL
  have hB₁ := xbar_mem_lFamily hT hL hX₁ hX₁L
  have hB₂ := xbar_mem_lFamily hT hL hX₂ hX₂L
  have hU₁ := inf_eq_U_of_card h₁ le_rfl hX₁L hc₁
  have hU₂ := inf_eq_U_of_card h₂ le_rfl hX₂L hc₂
  have ha₁ := isAlt5_xbar h₁ hX₁L hU₁
  have ha₂ := isAlt5_xbar h₂ hX₂L hU₂
  have hpair := fun (hs : IsSimpleGroup ↥(modO2Image L X₁ ⊔ modO2Image L X₂)) {r : ℕ}
      (hr : GoodPrime r) (hrd : r ∣ Nat.card ↥(modO2Image L X₁ ⊔ modO2Image L X₂)) =>
    false_of_typeB_pair hT hL hX₁ hX₂ hX₁L hX₂L h₁ h₂ hU₁ hU₂ hs hr.1 hr.2.1 hr.2.2 hrd
  have hgen := hK3 _ _ hTs _ hB₁ _ hB₂ ha₁ ha₂ hne
  rcases ho with (h | h) | h | ⟨p, hp, hp5, hp8, h⟩ | h | h
  · exact hne (hK2 _ (Or.inl (isAlt_of_top h)) _ hTs _ hB₁ _ hB₂ ha₁ ha₂)
  · exact hne (hK2 _ (Or.inr (isHat_of_top h)) _ hTs _ hB₁ _ hB₂ ha₁ ha₂)
  ·
    have hY := isPSL_of_top h
    have htop := hgen.1 (Or.inr hY)
    obtain ⟨hs, -⟩ := simple_dvd_of_L2 Nat.prime_five (by norm_num) hY (by norm_num)
    have : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) := hs
    have h13 : 13 ∣ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) := by
      rw [Ch11.SecA.card_of_isPSL (by norm_num) hY]
      decide
    obtain ⟨hs', hd'⟩ := simple_top_of h13
    rw [← htop] at hs' hd'
    exact hpair hs' (r := 13) ⟨by norm_num, by decide⟩ hd'
  ·
    have hp2 : p ≠ 2 := by rintro rfl; omega
    have hY := isPSL_of_top h
    have htop := hgen.1 (Or.inl ⟨p, hp, hp5, hp8, hY⟩)
    obtain ⟨hs, hd⟩ := simple_dvd_of_L2 hp hp2 hY le_rfl
    obtain ⟨hs', hd'⟩ := simple_top_of hd
    rw [← htop] at hs' hd'
    exact hpair hs' (r := p) ⟨hp, hp2, by omega, by omega, by omega, by omega, by omega,
      by omega⟩ hd'
  ·
    obtain ⟨e⟩ := isSporadic_of_top h
    have hJ : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .J1) :=
      CFSG.Sporadic.J1.fam_j1_simplicity.2.2
    have hs : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) := e.isSimpleGroup
    rcases hgen.2 (isSporadic_of_top h) with htop | hL11
    · have h19 : 19 ∣ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) := by
        rw [Nat.card_congr e.toEquiv]
        change 19 ∣ Nat.card CFSG.Blueprint.NativeSporadic.J1
        rw [CFSG.Sporadic.J1.card_J1]
        decide
      obtain ⟨hs', hd'⟩ := simple_top_of h19
      rw [← htop] at hs' hd'
      exact hpair hs' (r := 19) ⟨by norm_num, by decide⟩ hd'
    · obtain ⟨hs', hd'⟩ := simple_dvd_of_L2 (by norm_num : Nat.Prime 11) (by norm_num) hL11
        le_rfl
      exact hpair hs' (r := 11) ⟨by norm_num, by decide⟩ hd'
  · exact false_of_J4 hK5 hT hL hX₁ hX₁L h₁ (Or.inl hc₁) h

theorem concl_M23 (hT : IsSylowTwoOf T M) (hL : L ∈ cComp M) (hX : X ∈ lFamily T)
    (hXL : X ≤ L) (h : IsNatBlock X 2) (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    (hc : Nat.card ↥(modO2Image L X) = 960)
    (hY : IsSporadic .M23 ↥(⊤ : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L))) :
    IsSporadic .M23 (↥L ⧸ CFSG.pCore 2 ↥L) ∧ CFSG.pCore 2 ↥L ≤ Subgroup.center ↥L ∧
      CFSG.Open.IsQuasisimple ↥L ∧
      ∃ E : Subgroup G, E ≤ L ∧ IsElemAbelian 3 E ∧ Nat.card ↥E = 3 ^ 2 := by
  have hA := inf_eq_bot_of_card h le_rfl hXL (hc.trans (by norm_num))
  have hLC := le_centralizer_pCoreOf hT hL hX hXL h hA hq
  obtain ⟨e⟩ := isSporadic_of_top hY
  have hM23 : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .M23) :=
    CFSG.Sporadic.Mathieu.fam_m23_simplicity.2.2
  have hsY : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) := e.isSimpleGroup
  have hZc : CFSG.pCore 2 ↥L ≤ Subgroup.center ↥L := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro l
    have hxQ : (x : G) ∈ pCoreOf 2 L := (C1Pack.coe_mem_pCoreOf_iff L x).mpr hx
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hLC l.2) _ hxQ).symm
  have hcY : Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) with hb | ht
    · exact hb
    · exfalso
      have hperf := hq.1.commutator_eq_top
      have hcomm : _root_.commutator (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥ := by
        rw [_root_.commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer, ← ht]
        intro z hz
        exact Subgroup.mem_centralizer_iff.mpr fun y _ => (Subgroup.mem_center_iff.mp hz y)
      rw [hcomm] at hperf
      obtain ⟨a, b, hab⟩ := exists_pair_ne (↥L ⧸ CFSG.pCore 2 ↥L)
      have ha : a ∈ (⊥ : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L)) := hperf ▸ Subgroup.mem_top a
      have hb : b ∈ (⊥ : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L)) := hperf ▸ Subgroup.mem_top b
      rw [Subgroup.mem_bot] at ha hb
      exact hab (ha.trans hb.symm)
  refine ⟨⟨e⟩, hZc, ⟨commutator_eq_top_of_perfect (perfect_of_mem_cComp hL), ?_⟩, ?_⟩
  · have hcen : Subgroup.center ↥L = CFSG.pCore 2 ↥L := by
      refine le_antisymm (fun z hz => ?_) hZc
      have hzY : QuotientGroup.mk' (CFSG.pCore 2 ↥L) z ∈
          Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) := by
        rw [Subgroup.mem_center_iff]
        intro y
        obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective _ y
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz l]
      rw [hcY, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hzY
      exact hzY
    exact (QuotientGroup.quotientMulEquivOfEq hcen).isSimpleGroup
  · have h2 := CFSG.RankThree.ThinCatalog.two_le_pRank_three_M23_sylow
      (S := ↥L ⧸ CFSG.pCore 2 ↥L) e
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at h2
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨E, -, hE, hEc⟩ := CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank h2
    exact exists_E9 hE hEc

end CFSG.Quasithin.Vol2.Ch10.SecB.C10KH
