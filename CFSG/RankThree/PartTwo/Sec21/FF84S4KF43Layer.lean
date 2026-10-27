module

public import CFSG.RankThree.PartTwo.Sec21.FF84S4Inputs
public import CFSG.Adapters.WholeGroupLayer
public import CFSG.LocalAnalysis.SteinbergCCExistingCLS
public import CFSG.Quasithin.Vol2.Ch10Reselect.Counting
public import CFSG.LocalAnalysis.SectionRank.SubgroupRank
public import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG
open CFSG.Assembly (InCatalog)
open CFSG.Assembly.RankThreeEven (localRank)

section Components

variable {Q : Type} [Group Q] [Finite Q]

theorem kf43_comp_isSimple (hrad : solvableRadical Q = ⊥) {L : Subgroup Q} (hL : IsComponent L) :
    IsSimpleGroup L ∧ (∃ a b : L, a * b ≠ b * a) ∧
      ∀ x : L, (∀ y : L, y * x = x * y) → x = 1 := by
  obtain ⟨hF, hFL⟩ := CFSG.LocalAnalysis.radical_free_generalized_fitting_layer hrad
  have hz : ∀ x : L, (∀ y : L, y * x = x * y) → x = 1 := by
    intro x hx
    have hxc : x ∈ Subgroup.center L := Subgroup.mem_center_iff.2 hx
    have h1 : (x : Q) ∈ Subgroup.centralizer ((layer Q : Subgroup Q) : Set Q) :=
      CFSG.LocalCores.center_component_le_centralizer_layer hL ⟨x, hxc, rfl⟩
    rw [← hFL] at h1
    have h2 := CFSG.Adapters.centralizer_generalizedFitting_le_fittingSubgroup Q h1
    rw [hF] at h2
    exact Subtype.ext (Subgroup.mem_bot.1 h2)
  have hbot : Subgroup.center L = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => hz x (Subgroup.mem_center_iff.1 hx)
  let e : L ≃* L ⧸ Subgroup.center L :=
    ((QuotientGroup.quotientMulEquivOfEq hbot).trans (QuotientGroup.quotientBot)).symm
  have hs : IsSimpleGroup (L ⧸ Subgroup.center L) := hL.1.2.1
  haveI := hs
  have hs' : IsSimpleGroup L := e.isSimpleGroup
  obtain ⟨a, b, hab⟩ := hL.1.2.2
  refine ⟨hs', ⟨e.symm a, e.symm b, fun h => hab ?_⟩, hz⟩
  have := congrArg e h
  simpa using this

theorem kf43_comp_commute {L L' : Subgroup Q} (hL : IsComponent L) (hL' : IsComponent L') (hne : L ≠ L')
    {x y : Q} (hx : x ∈ L) (hy : y ∈ L') : x * y = y * x :=
  CFSG.LocalCores.componentIndex_commute (G := Q)
    (show (⟨L, hL⟩ : CFSG.LocalCores.ComponentIndex Q) ≠ ⟨L', hL'⟩ from
      fun h => hne (congrArg Subtype.val h)) x y hx hy

theorem kf43_comp_exists_order_five (hSz : LemmaSz) (hrad : solvableRadical Q = ⊥)
    (hK : KCore.KGroupNonab InCatalog Q) (h3 : ¬ 3 ∣ Nat.card Q) {L : Subgroup Q}
    (hL : IsComponent L) : ∃ y ∈ L, orderOf y = 5 := by
  obtain ⟨hs, hn, -⟩ := kf43_comp_isSimple hrad hL
  have h3L : ¬ 3 ∣ Nat.card L := fun h => h3 (h.trans (Subgroup.card_subgroup_dvd_card L))
  have h5 : 5 ∣ Nat.card L :=
    hSz L hs hn (KCore.KGroupNonab.subgroup Assembly.inCatalog_isoInvariant hK L) h3L
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := L) 5 h5
  exact ⟨y, y.2, by rw [Subgroup.orderOf_coe]; exact hy⟩

theorem kf43_comp_exists_involution (hrad : solvableRadical Q = ⊥) {L : Subgroup Q}
    (hL : IsComponent L) : ∃ s ∈ L, orderOf s = 2 := by
  obtain ⟨hs, hn, -⟩ := kf43_comp_isSimple hrad hL
  have h2 : 2 ∣ Nat.card L := by
    by_contra hd
    have hodd : Odd (Nat.card L) := Nat.odd_iff.2 (by omega)
    obtain ⟨a, b, hab⟩ := hn
    exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd) a b)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := L) 2 h2
  exact ⟨y, y.2, by rw [Subgroup.orderOf_coe]; exact hy⟩

theorem kf43_comp_independent (hrad : solvableRadical Q = ⊥) {L₂ L₃ L₄ : Subgroup Q}
    (h₂ : IsComponent L₂) (h₃ : IsComponent L₃) (h₄ : IsComponent L₄)
    (h23 : L₂ ≠ L₃) (h24 : L₂ ≠ L₄) (h34 : L₃ ≠ L₄)
    {a b c : Q} (ha : a ∈ L₂) (hb : b ∈ L₃) (hc : c ∈ L₄)
    (oa : orderOf a = 5) (ob : orderOf b = 5) (oc : orderOf c = 5) :
    ∀ i j k : ℕ, a ^ i * b ^ j * c ^ k = 1 → 5 ∣ i ∧ 5 ∣ j ∧ 5 ∣ k := by
  intro i j k hijk
  have key : ∀ {L : Subgroup Q}, IsComponent L → ∀ {x w : Q}, x ∈ L → x = w⁻¹ →
      (∀ y ∈ L, y * w = w * y) → x = 1 := by
    intro L hL x w hx hxw hw
    have := (kf43_comp_isSimple hrad hL).2.2 ⟨x, hx⟩ (fun y => by
      apply Subtype.ext
      show (y : Q) * x = x * y
      rw [hxw]
      exact (Commute.inv_right (hw y y.2 : Commute (y : Q) w)).eq)
    exact congrArg Subtype.val this
  have hb' : b ^ j ∈ L₃ := pow_mem hb j
  have hc' : c ^ k ∈ L₄ := pow_mem hc k
  have ha' : a ^ i ∈ L₂ := pow_mem ha i
  have e1 : a ^ i = (b ^ j * c ^ k)⁻¹ := eq_inv_of_mul_eq_one_left (by rwa [← mul_assoc])
  have a1 : a ^ i = 1 := key h₂ ha' e1 fun y hy => by
    rw [← mul_assoc, kf43_comp_commute h₂ h₃ h23 hy hb', mul_assoc, kf43_comp_commute h₂ h₄ h24 hy hc',
      ← mul_assoc]
  rw [a1, one_mul] at hijk
  have e2 : b ^ j = (c ^ k)⁻¹ := eq_inv_of_mul_eq_one_left hijk
  have b1 : b ^ j = 1 := key h₃ hb' e2 fun y hy => kf43_comp_commute h₃ h₄ h34 hy hc'
  rw [b1, one_mul] at hijk
  exact ⟨by have := orderOf_dvd_iff_pow_eq_one.2 a1; rwa [oa] at this,
    by rw [← ob]; exact orderOf_dvd_iff_pow_eq_one.2 b1,
    by rw [← oc]; exact orderOf_dvd_iff_pow_eq_one.2 hijk⟩

theorem kf43_three_le_localRank_layer (hSz : LemmaSz) (hrad : solvableRadical Q = ⊥)
    (hK : KCore.KGroupNonab InCatalog Q) (h3 : ¬ 3 ∣ Nat.card Q)
    {L₁ L₂ L₃ L₄ : Subgroup Q} (h₁ : IsComponent L₁) (h₂ : IsComponent L₂)
    (h₃ : IsComponent L₃) (h₄ : IsComponent L₄)
    (h12 : L₁ ≠ L₂) (h13 : L₁ ≠ L₃) (h14 : L₁ ≠ L₄)
    (h23 : L₂ ≠ L₃) (h24 : L₂ ≠ L₄) (h34 : L₃ ≠ L₄) :
    3 ≤ localRank 5 ↥(layer Q) := by
  obtain ⟨s, hs, os⟩ := kf43_comp_exists_involution hrad h₁
  obtain ⟨a, ha, oa⟩ := kf43_comp_exists_order_five hSz hrad hK h3 h₂
  obtain ⟨b, hb, ob⟩ := kf43_comp_exists_order_five hSz hrad hK h3 h₃
  obtain ⟨c, hc, oc⟩ := kf43_comp_exists_order_five hSz hrad hK h3 h₄
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have ind := kf43_comp_independent hrad h₂ h₃ h₄ h23 h24 h34 ha hb hc oa ob oc
  let s' : ↥(layer Q) := ⟨s, CFSG.LocalCores.component_le_layer h₁ hs⟩
  let a' : ↥(layer Q) := ⟨a, CFSG.LocalCores.component_le_layer h₂ ha⟩
  let b' : ↥(layer Q) := ⟨b, CFSG.LocalCores.component_le_layer h₃ hb⟩
  let c' : ↥(layer Q) := ⟨c, CFSG.LocalCores.component_le_layer h₄ hc⟩
  have os' : orderOf s' = 2 := by rw [← Subgroup.orderOf_coe]; exact os
  have oa' : orderOf a' = 5 := by rw [← Subgroup.orderOf_coe]; exact oa
  have ob' : orderOf b' = 5 := by rw [← Subgroup.orderOf_coe]; exact ob
  have oc' : orderOf c' = 5 := by rw [← Subgroup.orderOf_coe]; exact oc
  have cab : a' * b' = b' * a' := Subtype.ext (kf43_comp_commute h₂ h₃ h23 ha hb)
  have cac : a' * c' = c' * a' := Subtype.ext (kf43_comp_commute h₂ h₄ h24 ha hc)
  have cbc : b' * c' = c' * b' := Subtype.ext (kf43_comp_commute h₃ h₄ h34 hb hc)
  have csa : a' * s' = s' * a' := Subtype.ext (kf43_comp_commute h₂ h₁ h12.symm ha hs)
  have csb : b' * s' = s' * b' := Subtype.ext (kf43_comp_commute h₃ h₁ h13.symm hb hs)
  have csc : c' * s' = s' * c' := Subtype.ext (kf43_comp_commute h₄ h₁ h14.symm hc hs)
  have ind' : ∀ i j k : ℕ, a' ^ i * b' ^ j * c' ^ k = 1 → 5 ∣ i ∧ 5 ∣ j ∧ 5 ∣ k := by
    intro i j k h
    exact ind i j k (congrArg Subtype.val h)
  obtain ⟨E, hEcl, -, -, -, hEc, hEe, hEcard⟩ :=
    Quasithin.Vol2.Ch10Reselect.exists_elemAbelian_card_pow_three oa' ob' oc' cab cac cbc ind'
  have hcent : Subgroup.closure ({a', b', c'} : Set ↥(layer Q)) ≤
      Subgroup.centralizer ({s'} : Set ↥(layer Q)) := by
    rw [Subgroup.closure_le]
    intro x hx
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    rcases hx with rfl | rfl | rfl
    · exact csa.symm
    · exact csb.symm
    · exact csc.symm
  have hEn : E ≤ Subgroup.normalizer (Subgroup.zpowers s' : Set ↥(layer Q)) := by
    intro x hx
    have hxc : x ∈ Subgroup.centralizer ({s'} : Set ↥(layer Q)) := hcent (hEcl hx)
    have hcomm : s' * x = x * s' := Subgroup.mem_centralizer_iff.1 hxc s' rfl
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have hcx : Commute x s' := hcomm.symm
    have hcz : ∀ t : ↥(layer Q), t ∈ Subgroup.zpowers s' → x * t * x⁻¹ = t := by
      rintro t ⟨n, rfl⟩
      exact (hcx.zpow_right n).mul_inv_cancel
    have hcz' : ∀ t : ↥(layer Q), t ∈ Subgroup.zpowers s' → x⁻¹ * t * x = t := by
      rintro t ⟨n, rfl⟩
      have := ((hcx.inv_left).zpow_right n).mul_inv_cancel
      simpa using this
    constructor
    · intro ht
      rw [hcz h ht]
      exact ht
    · intro ht
      have := hcz' _ ht
      rw [show x⁻¹ * (x * h * x⁻¹) * x = h by group] at this
      rw [this]
      exact ht
  have hloc : CFSG.Open.IsTwoLocal (Subgroup.normalizer (Subgroup.zpowers s' : Set ↥(layer Q))) := by
    refine ⟨Subgroup.zpowers s', ?_, ?_, rfl⟩
    · intro h
      rw [Subgroup.zpowers_eq_bot] at h
      have : orderOf s' = 1 := by rw [h]; exact orderOf_one
      omega
    · refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, os']
      norm_num
  have hrk : 3 ≤ CFSG.Open.pRank 5 (Subgroup.normalizer (Subgroup.zpowers s' : Set ↥(layer Q))) :=
    SectionRank.le_pRank (by norm_num) hEn ⟨hEc, hEe⟩ hEcard
  show 3 ≤ CFSG.Open.twoLocalPrimeRank 5 ↥(layer Q)
  refine hrk.trans (le_csSup ⟨Nat.card ↥(layer Q), ?_⟩ ⟨_, hloc, rfl⟩)
  rintro _ ⟨K, -, rfl⟩
  exact SectionRank.pRank_le_card_of_one_lt (by norm_num) K

end Components

end CFSG.RankThree.PartTwo.Sec21.FF84.S4
