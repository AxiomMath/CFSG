module

public import CFSG.Quasithin.Recognition.Stroth.Str83G5AbsConj
public import CFSG.GroupTheory.CoprimeCovering

public section

namespace CFSG.Quasithin.Stroth.G5

open Subgroup CFSG.Quasithin.OperatorJH
open scoped nonZeroDivisors commutatorElement

variable {G : Type} [Group G] {n : ℕ}

private theorem exists_isYSimple_of_mem_facMultiset {Y : Subgroup G} {β : Type}
    {f : Subgroup G → Subgroup G → β} {C D : Subgroup G} {l : List (Subgroup G)}
    (hl : IsYSeries Y C l D) :
    ∀ a ∈ facMultiset f l D, ∃ C' S' : Subgroup G, IsYSimple Y C' S' ∧ S' ≤ D ∧ a = f C' S' := by
  induction l generalizing D with
  | nil =>
    intro a ha
    exfalso
    simpa [facMultiset] using ha
  | cons S l ih =>
    intro a ha
    rw [facMultiset] at ha
    rcases Multiset.mem_cons.mp ha with rfl | ha
    · exact ⟨S, D, hl.1, le_rfl, rfl⟩
    · obtain ⟨C', S', hYS, hSD, rfl⟩ := ih hl.2 a ha
      exact ⟨C', S', hYS, hSD.trans hl.1.1.le, rfl⟩

namespace Conf

variable [Finite G] (c : Conf G n)

private theorem fst_eq_zero_or_isUnit_of_mem_chiLab {C S : Subgroup G}
    (hS : IsYSimple c.H C S) (hSQ : S ≤ c.Q₁) {φ : Coord n}
    (hφ : φ ∈ chiLab c.ζ c.d₁ c.d₂ C S) : φ.1 = 0 ∨ IsUnit φ.1 := by
  classical
  obtain ⟨β, hβ⟩ := hφ
  by_contra hcon
  push Not at hcon
  obtain ⟨hx0, hxunit⟩ := hcon
  have hn : n ≠ 0 := by
    have := c.three_le
    omega
  have hNpos : 0 < 2 ^ n - 1 := lt_of_lt_of_le (by norm_num) (seven_le c.three_le)
  haveI : NeZero (2 ^ n - 1) := ⟨hNpos.ne'⟩
  have hxne : φ.1 ∉ nonZeroDivisors (ZMod (2 ^ n - 1)) := fun hmem =>
    hxunit (isUnit_iff_mem_nonZeroDivisors_of_finite.mpr hmem)
  have hxright : φ.1 ∉ nonZeroDivisorsRight (ZMod (2 ^ n - 1)) := by
    intro hmem
    refine hxne ?_
    rw [nonZeroDivisors, Submonoid.mem_inf]
    exact ⟨by rwa [nonZeroDivisorsLeft_eq_right], hmem⟩
  obtain ⟨y, hyx, hy0⟩ :=
    (notMem_nonZeroDivisorsRight_iff (ZMod (2 ^ n - 1))).mp hxright
  have hyval : y.val ≠ 0 := fun h => hy0 ((ZMod.val_eq_zero y).mp h)
  have hyvlt : y.val < 2 ^ n - 1 := ZMod.val_lt y
  set δ : G := c.d₁ ^ y.val with hδdef
  have hδne : δ ≠ 1 := by
    rw [hδdef]
    exact pow_ne_one_of_lt_orderOf hyval (by rwa [c.orderOf₁])
  have hδH : δ ∈ c.H := by
    rw [hδdef]
    exact c.H.pow_mem c.d₁_mem_H y.val
  have hδmem : δ ∈ zpowers c.d₁ := by
    rw [hδdef]
    exact Subgroup.npow_mem_zpowers c.d₁ y.val
  have hδdvd : orderOf δ ∣ 2 ^ n - 1 := by
    have h1 : orderOf δ ∣ orderOf c.d₁ := by
      rw [hδdef]
      exact orderOf_pow_dvd y.val
    rwa [c.orderOf₁] at h1
  have hNodd : Odd (2 ^ n - 1) :=
    Nat.Even.sub_odd Nat.one_le_two_pow (even_two.pow_of_ne_zero hn) odd_one
  have hNyx : 2 ^ n - 1 ∣ φ.1.val * y.val := by
    refine (ZMod.natCast_eq_zero_iff (φ.1.val * y.val) (2 ^ n - 1)).mp ?_
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, mul_comm, hyx]
  have hζpow : (c.ζ ^ φ.1.val) ^ y.val = 1 := by
    rw [← pow_mul]
    exact orderOf_dvd_iff_pow_eq_one.mp (by rwa [c.orderOf_ζ])
  have hS₁ : c.d₁ ∈ Subgroup.normalizer (S : Set G) := hS.2.2.2.1 c.d₁_mem_H
  set R : Subgroup G := zpowers δ with hRdef
  have hRN : R ≤ Subgroup.normalizer (C : Set G) := by
    rw [hRdef]
    exact Subgroup.zpowers_le.mpr (hS.2.2.1 hδH)
  have hact : ∀ r ∈ R, ∀ s ∈ S, r * s * r⁻¹ ∈ S ∧ β (r * s * r⁻¹) = β s := by
    intro r hr s hs
    have hnat : ∀ t : ℕ, δ ^ t * s * (δ ^ t)⁻¹ ∈ S ∧
        β (δ ^ t * s * (δ ^ t)⁻¹) = β s := by
      intro t
      have hδt : δ ^ t = c.d₁ ^ (y.val * t) := by
        rw [hδdef, ← pow_mul]
      rw [hδt]
      obtain ⟨hm, hb⟩ := hβ.conj₁_pow hS₁ (y.val * t) s hs
      refine ⟨hm, ?_⟩
      rw [hb, pow_mul, hζpow, one_pow, one_mul]
    rw [hRdef] at hr
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hr
    rw [← hm]
    have he : δ ^ orderOf δ = 1 := pow_orderOf_eq_one δ
    have hepos : 0 < orderOf δ := Nat.pos_of_dvd_of_pos hδdvd hNpos
    have hez : (orderOf δ : ℤ) ≠ 0 := by exact_mod_cast hepos.ne'
    rw [zpow_eq_zpow_emod' m he]
    have h0 : 0 ≤ m % (orderOf δ : ℤ) := Int.emod_nonneg m hez
    have ht : (((m % (orderOf δ : ℤ)).toNat : ℕ) : ℤ) = m % (orderOf δ : ℤ) :=
      Int.toNat_of_nonneg h0
    rw [← ht, zpow_natCast]
    exact hnat _
  have hex : ∃ s ∈ S, s ∉ C := by
    by_contra h
    push Not at h
    exact hS.1.ne (le_antisymm hS.1.le h)
  obtain ⟨s₀, hs₀S, hs₀C⟩ := hex
  have hinv : β s₀⁻¹ = -β s₀ := by
    refine eq_neg_of_add_eq_zero_right ?_
    rw [← hβ.map_mul s₀ hs₀S s₀⁻¹ (S.inv_mem hs₀S), mul_inv_cancel, hβ.map_one]
  have hcomm : ∀ r ∈ R, ⁅s₀, r⁆ ∈ C := by
    intro r hr
    obtain ⟨h1, h2⟩ := hact r hr s₀⁻¹ (S.inv_mem hs₀S)
    have hceq : ⁅s₀, r⁆ = s₀ * (r * s₀⁻¹ * r⁻¹) := by
      rw [commutatorElement_def]
      group
    have hz : β ⁅s₀, r⁆ = 0 := by
      rw [hceq, hβ.map_mul s₀ hs₀S _ h1, h2, hinv]
      simp
    exact (hβ.eq_zero_iff _ (by rw [hceq]; exact S.mul_mem hs₀S h1)).mp hz
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hC2 : IsPGroup 2 ↥C := c.isPGroup₁.to_le (hS.1.le.trans hSQ)
  haveI : Group.IsNilpotent ↥C := hC2.isNilpotent
  have hsolv : Group.IsSolvable ↥C := inferInstance
  obtain ⟨a, ha⟩ := hC2.exists_card_eq
  have hRcard : Nat.card ↥R = orderOf δ := by
    rw [hRdef]
    exact Nat.card_zpowers δ
  have hRodd : Odd (Nat.card ↥R) := by
    rw [hRcard]
    exact hNodd.of_dvd_nat hδdvd
  have hcop : Nat.Coprime (Nat.card ↥C) (Nat.card ↥R) := by
    rw [ha]
    exact (Nat.coprime_two_left.mpr hRodd).pow_left a
  have hNorm : (C.subgroupOf S).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hS.1.le).mpr hS.2.1
  obtain ⟨y', hy'S, hy'cent, hy'C⟩ :=
    CFSG.GroupTheory.exists_mem_centralizer_of_commutator_mem hS.1.le hNorm hRN hsolv hcop
      hs₀S hcomm
  have hy'notC : y' ∉ C := by
    intro hy'Cmem
    apply hs₀C
    have h2 : s₀⁻¹ ∈ C := by
      simpa using C.mul_mem hy'C (C.inv_mem hy'Cmem)
    simpa using C.inv_mem h2
  have hy'β : β y' ≠ 0 := fun h => hy'notC ((hβ.eq_zero_iff y' hy'S).mp h)
  have hcentδ : y' ∈ Subgroup.centralizer ({δ} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact (hy'cent δ (Subgroup.mem_zpowers δ)).symm
  have hy'inf : y' ∈ c.Q₁ ⊓ Subgroup.centralizer ({δ} : Set G) := ⟨hSQ hy'S, hcentδ⟩
  rw [c.fixA δ hδmem hδne] at hy'inf
  have hcent : y' ∈ Subgroup.centralizer (Subgroup.zpowers c.d₁ : Set G) := hy'inf.2
  have hcd : c.d₁ * y' = y' * c.d₁ :=
    (Subgroup.mem_centralizer_iff.mp hcent) c.d₁ (Subgroup.mem_zpowers c.d₁)
  have hdy : c.d₁ * y' * c.d₁⁻¹ = y' := by
    rw [hcd]
    group
  have hβconj : c.ζ ^ φ.1.val * β y' = β y' := by
    rw [← hβ.conj₁ y' hy'S, hdy]
  have hζ1 : c.ζ ^ φ.1.val = 1 := by
    refine mul_right_cancel₀ hy'β ?_
    rwa [one_mul]
  have hNdvd : 2 ^ n - 1 ∣ φ.1.val := by
    have h1 : orderOf c.ζ ∣ φ.1.val := orderOf_dvd_iff_pow_eq_one.mpr hζ1
    rwa [c.orderOf_ζ] at h1
  have hval0 : φ.1.val = 0 := Nat.eq_zero_of_dvd_of_lt hNdvd (ZMod.val_lt φ.1)
  exact hx0 ((ZMod.val_eq_zero φ.1).mp hval0)

theorem fst_eq_zero_or_isUnit {C : Subgroup G} {l : List (Subgroup G)} {μ : Multiset (Coord n)}
    (hl : IsYSeries c.H C l c.Q₁) (hμ : facMultiset (chiLab c.ζ c.d₁ c.d₂) l c.Q₁ = clsSets μ) :
    ∀ φ ∈ μ, φ.1 = 0 ∨ IsUnit φ.1 := by
  intro φ hφ
  have hn : n ≠ 0 := by
    have := c.three_le
    omega
  have hmem : (cls φ : Set (Coord n)) ∈ facMultiset (chiLab c.ζ c.d₁ c.d₂) l c.Q₁ := by
    rw [hμ]
    exact Multiset.mem_map_of_mem (fun ψ : Coord n => (cls ψ : Set (Coord n))) hφ
  obtain ⟨C', S', hYS, hSQ, hcls⟩ :=
    exists_isYSimple_of_mem_facMultiset hl (cls φ : Set (Coord n)) hmem
  have hφlab : φ ∈ chiLab c.ζ c.d₁ c.d₂ C' S' := by
    rw [← hcls]
    simpa using mem_cls_self hn φ
  exact fst_eq_zero_or_isUnit_of_mem_chiLab c hYS hSQ hφlab

end Conf

end CFSG.Quasithin.Stroth.G5

end
