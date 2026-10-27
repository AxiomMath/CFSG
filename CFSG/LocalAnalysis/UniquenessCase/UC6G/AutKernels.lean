module

public import CFSG.LocalAnalysis.UniquenessCase.UC6G.AutLbar
public import CFSG.LocalAnalysis.UniquenessCase.UC6AutKernels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6G

open Subgroup CFSG.Open CFSG.ABGLocalTools
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC6
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

namespace Mz614

variable {G : Type} [Group G] [Finite G] {Dat : Data G} (m : Mz614 Dat)

theorem actLbar_fix_Ebar_of {y : ↥(normalizer (m.L : Set G))}
    (hfix : ∀ e ∈ m.EL, (y : G) * e * (y : G)⁻¹ * e⁻¹ ∈ m.OL) :
    ∀ ε ∈ m.Ebar, m.actLbar y ε = ε := by
  intro ε hε
  obtain ⟨e, he, rfl⟩ := m.mem_Ebar_iff.1 hε
  exact (m.actLbar_fix_iff y e).2 (hfix e he)

theorem commutator_le_iff_actLbar_eq_one {y : G} (hy : y ∈ normalizer (m.L : Set G)) :
    ⁅zpowers y, m.L⁆ ≤ m.OL ↔ m.actLbar ⟨y, hy⟩ = 1 := by
  rw [← m.mem_KerL_iff hy, m.actLbar_eq_one_iff]

theorem kc633_of_abs (h : AbsKC m.Lbar m.r m.Ebar) : m.KC633 := by
  intro y hy hord hfix
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  obtain ⟨k, hk⟩ := hord
  have hord' : ∃ j : ℕ, orderOf (m.actLbar ⟨y, hy⟩) = m.r ^ j := by
    have hdvd : orderOf (m.actLbar ⟨y, hy⟩) ∣ m.r ^ k := by
      have := m.orderOf_actLbar_dvd ⟨y, hy⟩
      rw [hk] at this
      exact this
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow m.hr).1 hdvd
    exact ⟨j, hj⟩
  obtain ⟨ε, hεE, hε⟩ := h _ hord' (m.actLbar_fix_Ebar_of hfix)
  obtain ⟨e, he, rfl⟩ := m.mem_Ebar_iff.1 hεE
  refine ⟨(e : G), he, ?_⟩
  have hmem : (e : G)⁻¹ * y ∈ normalizer (m.L : Set G) :=
    mul_mem (inv_mem (Subgroup.le_normalizer e.2)) hy
  rw [← m.mem_KerL_iff hmem, ← m.actLbar_eq_one_iff ⟨_, hmem⟩]
  have h1 : (⟨(e : G)⁻¹ * y, hmem⟩ : ↥(normalizer (m.L : Set G))) =
      ⟨((e⁻¹ : ↥m.L) : G), Subgroup.le_normalizer (e⁻¹).2⟩ * ⟨y, hy⟩ := Subtype.ext rfl
  rw [h1, map_mul, m.actLbar_of_mem_L (e⁻¹), hε, ← map_mul, ← QuotientGroup.mk_mul]
  simp

theorem kn633_of_abs (h : AbsKN m.Lbar m.r m.Ebar (m.r = 3 ∧ LieModel m.Lbar .PSL 3 2 2)) :
    m.KN633 := by
  intro X hXN hEX hrX
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  set Xs : Subgroup (MulAut m.Lbar) :=
    (X.subgroupOf (normalizer (m.L : Set G))).map m.actLbar with hXs
  have hmemXs : ∀ x : G, ∀ hx : x ∈ X, m.actLbar ⟨x, hXN hx⟩ ∈ Xs := fun x hx =>
    ⟨⟨x, hXN hx⟩, hx, rfl⟩
  have h1 : ∀ ε ∈ m.Ebar, ∀ x ∈ Xs, MulAut.conj ε * x * (MulAut.conj ε)⁻¹ ∈ Xs := by
    intro ε hε x hx
    obtain ⟨e, he, rfl⟩ := m.mem_Ebar_iff.1 hε
    obtain ⟨z, hz, rfl⟩ := hx
    have hz' : (z : G) ∈ X := hz
    have hezX : (e : G) * (z : G) * (e : G)⁻¹ ∈ X := (mem_normalizer_iff.1 (hEX he) (z : G)).1 hz'
    set eN : ↥(normalizer (m.L : Set G)) := ⟨(e : G), Subgroup.le_normalizer e.2⟩ with heN
    refine ⟨eN * z * eN⁻¹, ?_, ?_⟩
    · exact hezX
    · rw [map_mul, map_mul, map_inv, heN, m.actLbar_of_mem_L e]
  have h2 : ∀ x ∈ Xs, (∃ k : ℕ, orderOf x = m.r ^ k) → x = 1 := by
    rintro x ⟨z, hz, rfl⟩ ⟨j, hj⟩
    have hzX : (z : G) ∈ X := hz
    have hn : orderOf (z : G) ≠ 0 := (orderOf_pos _).ne'
    obtain ⟨a, t, ht, hzt⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn m.r m.hr.ne_one
    have ht0 : t ≠ 0 := right_ne_zero_of_mul (hzt ▸ hn)
    have hwX : (z : G) ^ t ∈ X := X.pow_mem hzX t
    have hwo : orderOf ((z : G) ^ t) = m.r ^ a := by
      rw [orderOf_pow_of_dvd ht0 (by rw [hzt]; exact Dvd.intro_left _ rfl), hzt]
      exact Nat.mul_div_cancel _ (Nat.pos_of_ne_zero ht0)
    have hcomm := hrX _ hwX ⟨a, hwo⟩
    have hone := (m.commutator_le_iff_actLbar_eq_one (hXN hwX)).1 hcomm
    have hpow : m.actLbar z ^ t = 1 := by
      have : (⟨(z : G) ^ t, hXN hwX⟩ : ↥(normalizer (m.L : Set G))) = (z : ↥(normalizer (m.L : Set G))) ^ t :=
        Subtype.ext rfl
      rw [← map_pow, ← this]
      exact hone
    have hdvd : orderOf (m.actLbar z) ∣ t := orderOf_dvd_of_pow_eq_one hpow
    rw [hj] at hdvd
    by_cases hj0 : j = 0
    · rw [hj0, pow_zero] at hj
      exact orderOf_eq_one_iff.1 hj
    · exact absurd ((dvd_pow_self m.r hj0).trans hdvd) ht
  obtain ⟨hcent, hdisj⟩ := h Xs h1 h2
  refine ⟨fun x hx e he => ?_, ?_⟩
  · have := hcent _ (hmemXs x hx) (QuotientGroup.mk ⟨e, he.2⟩)
      (m.mem_Ebar_iff.2 ⟨⟨e, he.2⟩, he, rfl⟩)
    exact (m.actLbar_fix_iff ⟨x, hXN hx⟩ ⟨e, he.2⟩).1 this
  · rcases hdisj with hbot | hL34
    · left
      rw [Subgroup.commutator_le]
      intro x hx l hl
      have hx1 : m.actLbar ⟨x, hXN hx⟩ = 1 := by
        have := hmemXs x hx
        rw [hbot] at this
        exact Subgroup.mem_bot.1 this
      have hker := (m.actLbar_eq_one_iff _).1 hx1
      rw [commutatorElement_def]
      exact (m.mem_CenL.1 hker).2 l hl
    · right
      exact hL34

theorem kinv633_of_abs (h : AbsKInv m.Lbar m.Ebar) : m.KInv633 := by
  intro x hx y hy hxo hyo hxE hyE hxn hyn
  have hxo' : ∃ j : ℕ, orderOf (m.actLbar ⟨x, hx⟩) = 2 ^ j := by
    obtain ⟨k, hk⟩ := hxo
    have hdvd : orderOf (m.actLbar ⟨x, hx⟩) ∣ 2 ^ k := by
      have := m.orderOf_actLbar_dvd ⟨x, hx⟩
      rw [hk] at this
      exact this
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    exact ⟨j, hj⟩
  have hyo' : ∃ j : ℕ, orderOf (m.actLbar ⟨y, hy⟩) = 2 ^ j := by
    obtain ⟨k, hk⟩ := hyo
    have hdvd : orderOf (m.actLbar ⟨y, hy⟩) ∣ 2 ^ k := by
      have := m.orderOf_actLbar_dvd ⟨y, hy⟩
      rw [hk] at this
      exact this
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    exact ⟨j, hj⟩
  have hxn' : m.actLbar ⟨x, hx⟩ ≠ 1 := fun h1 =>
    hxn ((m.commutator_le_iff_actLbar_eq_one hx).2 h1)
  have hyn' : m.actLbar ⟨y, hy⟩ ≠ 1 := fun h1 =>
    hyn ((m.commutator_le_iff_actLbar_eq_one hy).2 h1)
  have heq := h _ _ hxo' hyo' (m.actLbar_fix_Ebar_of hxE) (m.actLbar_fix_Ebar_of hyE) hxn' hyn'
  have hmem : x⁻¹ * y ∈ normalizer (m.L : Set G) := mul_mem (inv_mem hx) hy
  rw [m.commutator_le_iff_actLbar_eq_one hmem]
  have h1 : (⟨x⁻¹ * y, hmem⟩ : ↥(normalizer (m.L : Set G))) =
      (⟨x, hx⟩ : ↥(normalizer (m.L : Set G)))⁻¹ * ⟨y, hy⟩ := Subtype.ext rfl
  rw [h1, map_mul, map_inv, heq]
  simp

end Mz614

end CFSG.LocalAnalysis.UniquenessCase.UC6G
