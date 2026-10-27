module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K4bWreath

open Subgroup CFSG.Open
open scoped commutatorElement IsMulCommutative

section Nilpotent

variable {H : Type*} [Group H] (δ : H →* H)

theorem apply_cube_eq_one (h3 : δ.comp (δ.comp δ) = 1) (x : H) : δ (δ (δ x)) = 1 := by
  have := DFunLike.congr_fun h3 x
  simpa using this

theorem ker_le_ker_comp : δ.ker ≤ (δ.comp δ).ker := by
  intro x hx
  rw [MonoidHom.mem_ker] at hx ⊢
  simp [hx]

theorem ker_comp_ne_top (h2 : δ.comp δ ≠ 1) : (δ.comp δ).ker ≠ ⊤ := by
  intro h
  apply h2
  ext x
  have : x ∈ (δ.comp δ).ker := by rw [h]; trivial
  simpa using this

theorem range_le_ker_comp (h3 : δ.comp (δ.comp δ) = 1) : δ.range ≤ (δ.comp δ).ker := by
  rintro _ ⟨x, rfl⟩
  rw [MonoidHom.mem_ker]
  simpa using apply_cube_eq_one δ h3 x

theorem range_comp_le_ker (h3 : δ.comp (δ.comp δ) = 1) : (δ.comp δ).range ≤ δ.ker := by
  rintro _ ⟨x, rfl⟩
  rw [MonoidHom.mem_ker]
  simpa using apply_cube_eq_one δ h3 x

theorem ker_ne_ker_comp (h3 : δ.comp (δ.comp δ) = 1) (h2 : δ.comp δ ≠ 1) :
    δ.ker ≠ (δ.comp δ).ker := by
  intro h
  apply ker_comp_ne_top δ h2
  rw [eq_top_iff]
  intro x _
  have hx : δ x ∈ (δ.comp δ).ker := range_le_ker_comp δ h3 ⟨x, rfl⟩
  rw [← h, MonoidHom.mem_ker] at hx
  rw [MonoidHom.mem_ker]
  simpa using hx

theorem one_lt_card_ker [Finite H] (hS : Nat.card H = 27) (h3 : δ.comp (δ.comp δ) = 1) :
    1 < Nat.card δ.ker := by
  rw [Subgroup.one_lt_card_iff_ne_bot]
  intro hbot
  have hinj : Function.Injective δ := (MonoidHom.ker_eq_bot_iff δ).1 hbot
  have hall : ∀ x : H, x = 1 := by
    intro x
    apply hinj; apply hinj; apply hinj
    rw [apply_cube_eq_one δ h3 x, map_one, map_one, map_one]
  have : Nat.card H = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    exact ⟨⟨fun a b => (hall a).trans (hall b).symm⟩, ⟨1⟩⟩
  omega

theorem dvd_twentySeven {n : ℕ} (hn : n ∣ 27) : n = 1 ∨ n = 3 ∨ n = 9 ∨ n = 27 := by
  have : n ∈ Nat.divisors 27 := by simp [hn]
  have h27 : Nat.divisors 27 = {1, 3, 9, 27} := by decide
  rw [h27] at this
  simpa using this

theorem card_ker_range_of_nilpotent (hS : Nat.card H = 27) (h3 : δ.comp (δ.comp δ) = 1)
    (h2 : δ.comp δ ≠ 1) :
    Nat.card δ.range = 9 ∧ Nat.card (δ.comp δ).range = 3 ∧ Nat.card δ.ker = 3 ∧
      Nat.card (δ.comp δ).ker = 9 ∧ δ.range = (δ.comp δ).ker ∧ (δ.comp δ).range = δ.ker := by
  classical
  haveI : Finite H := Nat.finite_of_card_ne_zero (by omega)
  have hK1 := one_lt_card_ker δ hS h3
  have hlt12 : Nat.card δ.ker < Nat.card (δ.comp δ).ker :=
    Subgroup.card_lt_of_lt (lt_of_le_of_ne (ker_le_ker_comp δ) (ker_ne_ker_comp δ h3 h2))
  have hlt2 : Nat.card (δ.comp δ).ker < 27 := by
    rw [← hS]
    exact Subgroup.card_lt_of_lt (lt_top_iff_ne_top.2 (ker_comp_ne_top δ h2)) |>.trans_eq
      (by simp)
  have hd1 : Nat.card δ.ker ∣ 27 := hS ▸ Subgroup.card_subgroup_dvd_card _
  have hd2 : Nat.card (δ.comp δ).ker ∣ 27 := hS ▸ Subgroup.card_subgroup_dvd_card _
  have e1 : Nat.card δ.ker = 3 := by
    rcases dvd_twentySeven hd1 with h | h | h | h <;>
      rcases dvd_twentySeven hd2 with h' | h' | h' | h' <;> omega
  have e2 : Nat.card (δ.comp δ).ker = 9 := by
    rcases dvd_twentySeven hd1 with h | h | h | h <;>
      rcases dvd_twentySeven hd2 with h' | h' | h' | h' <;> omega
  have c1 := Subgroup.card_ker_mul_card_range δ
  have c2 := Subgroup.card_ker_mul_card_range (δ.comp δ)
  rw [e1, hS] at c1
  rw [e2, hS] at c2
  have r1 : Nat.card δ.range = 9 := by omega
  have r2 : Nat.card (δ.comp δ).range = 3 := by omega
  refine ⟨r1, r2, e1, e2, ?_, ?_⟩
  · exact Subgroup.eq_of_le_of_card_ge (range_le_ker_comp δ h3) (by rw [r1, e2])
  · exact Subgroup.eq_of_le_of_card_ge (range_comp_le_ker δ h3) (by rw [r2, e1])

end Nilpotent

variable {G : Type*} [Group G]

section CommEnd

variable (S : Subgroup G) [IsMulCommutative S] (y : G)

@[expose] def conjEnd (hy : ∀ s ∈ S, y * s * y⁻¹ ∈ S) : S →* S where
  toFun s := ⟨y * s * y⁻¹, hy s s.2⟩
  map_one' := by ext; simp
  map_mul' a b := by ext; simp [mul_assoc]

@[simp] theorem coe_conjEnd (hy : ∀ s ∈ S, y * s * y⁻¹ ∈ S) (s : S) :
    ((conjEnd S y hy s : S) : G) = y * s * y⁻¹ := rfl

@[expose] def commEnd (hy : ∀ s ∈ S, y * s * y⁻¹ ∈ S) : S →* S :=
  conjEnd S y hy * (MonoidHom.id S)⁻¹

@[simp] theorem coe_commEnd (hy : ∀ s ∈ S, y * s * y⁻¹ ∈ S) (s : S) :
    ((commEnd S y hy s : S) : G) = ⁅y, (s : G)⁆ := by
  simp [commEnd, commutatorElement_def]

theorem commEnd_apply_mul (hy : ∀ s ∈ S, y * s * y⁻¹ ∈ S) (s : S) :
    conjEnd S y hy s = commEnd S y hy s * s := by
  simp [commEnd]

theorem conjEnd_cube (hy : ∀ s ∈ S, y * s * y⁻¹ ∈ S) (hy3 : y ^ 3 ∈ S) (s : S) :
    conjEnd S y hy (conjEnd S y hy (conjEnd S y hy s)) = s := by
  ext
  simp only [coe_conjEnd]
  have h : (y ^ 3) * (s : G) = (s : G) * y ^ 3 := by
    have := mul_comm' (⟨y ^ 3, hy3⟩ : S) s
    exact congrArg Subtype.val this
  have hy3' : y ^ 3 = y * y * y := by simp [pow_succ, mul_assoc]
  calc y * (y * (y * (s : G) * y⁻¹) * y⁻¹) * y⁻¹ = (y * y * y) * (s : G) * (y * y * y)⁻¹ := by
        group
    _ = s := by rw [← hy3', h]; group

theorem commEnd_comp_cube (hy : ∀ s ∈ S, y * s * y⁻¹ ∈ S) (hS3 : ∀ s ∈ S, s ^ 3 = 1)
    (hy3 : y ^ 3 ∈ S) :
    (commEnd S y hy).comp ((commEnd S y hy).comp (commEnd S y hy)) = 1 := by
  ext s
  simp only [MonoidHom.comp_apply, MonoidHom.one_apply]
  have hS3' : ∀ t : S, t ^ 3 = 1 := fun t => Subtype.ext (by simpa using hS3 t t.2)
  set c := conjEnd S y hy with hcdef
  set δ := commEnd S y hy with hδdef
  have hc : ∀ t : S, c t = δ t * t := fun t => commEnd_apply_mul S y hy t
  have e2 : c (c s) = (δ (δ s) * δ s) * (δ s * s) := by
    rw [hc s, map_mul, hc (δ s), hc s]
  have e3 : c (c (c s)) = ((δ (δ (δ s)) * δ (δ s)) * (δ (δ s) * δ s)) *
      ((δ (δ s) * δ s) * (δ s * s)) := by
    rw [e2, map_mul, map_mul, map_mul, hc (δ (δ s)), hc (δ s), hc s]
  have key : c (c (c s)) = δ (δ (δ s)) * (δ (δ s)) ^ 3 * (δ s) ^ 3 * s := by
    rw [e3]
    simp only [pow_succ, pow_zero, one_mul]
    ac_rfl
  rw [conjEnd_cube S y hy hy3, hS3', hS3', mul_one, mul_one] at key
  simpa using key.symm

theorem mul_pow_three (hy : ∀ s ∈ S, y * s * y⁻¹ ∈ S) (hS3 : ∀ s ∈ S, s ^ 3 = 1)
    (hy3 : y ^ 3 ∈ S) (s : S) :
    (y * (s : G)) ^ 3 = ⁅y, ⁅y, (s : G)⁆⁆ * y ^ 3 := by
  have hS3' : ∀ t : S, t ^ 3 = 1 := fun t => Subtype.ext (by simpa using hS3 t t.2)
  set c := conjEnd S y hy with hcdef
  set δ := commEnd S y hy with hδdef
  have hc : ∀ t : S, c t = δ t * t := fun t => commEnd_apply_mul S y hy t
  have hcoe : ∀ t : S, ((c t : S) : G) = y * t * y⁻¹ := fun t => rfl
  have e2 : c (c s) = (δ (δ s) * δ s) * (δ s * s) := by
    rw [hc s, map_mul, hc (δ s), hc s]
  have h2 : c s * c (c s) * s = δ (δ s) := by
    rw [e2, hc s]
    have h1 := hS3' (δ s)
    have h' := hS3' s
    rw [pow_three] at h1 h'
    calc δ s * s * (δ (δ s) * δ s * (δ s * s)) * s
        = δ (δ s) * (δ s * (δ s * δ s)) * (s * (s * s)) := by ac_rfl
      _ = δ (δ s) := by rw [h1, h', mul_one, mul_one]
  have hcomm : (s : G) * y ^ 3 = y ^ 3 * (s : G) := by
    have := mul_comm' s (⟨y ^ 3, hy3⟩ : S)
    exact congrArg Subtype.val this
  have h3 : (δ (δ s) : G) = ⁅y, ⁅y, (s : G)⁆⁆ := by simp [δ]
  rw [← h3, ← h2]
  simp only [Subgroup.coe_mul, hcoe]
  calc (y * (s : G)) ^ 3 = y * s * (y * s * (y * s)) := by rw [pow_three]
    _ = y * s * y * s * y * s := by group
    _ = (y * s * y⁻¹) * (y * (y * s * y⁻¹) * y⁻¹) * (y ^ 3 * s) := by group
    _ = (y * s * y⁻¹) * (y * (y * s * y⁻¹) * y⁻¹) * (s * y ^ 3) := by rw [hcomm]
    _ = _ := by group

theorem commEnd_comp_ne_one (hy : ∀ s ∈ S, y * s * y⁻¹ ∈ S) (hJ : ∃ s ∈ S, ⁅y, ⁅y, s⁆⁆ ≠ 1) :
    (commEnd S y hy).comp (commEnd S y hy) ≠ 1 := by
  intro h
  obtain ⟨s, hs, hne⟩ := hJ
  apply hne
  have := congrArg (fun f : S →* S => ((f ⟨s, hs⟩ : S) : G)) h
  simpa using this

theorem map_ker_commEnd (hy : ∀ s ∈ S, y * s * y⁻¹ ∈ S) :
    (commEnd S y hy).ker.map S.subtype = S ⊓ centralizer {y} := by
  ext x
  simp only [Subgroup.mem_map, MonoidHom.mem_ker, Subgroup.mem_inf, Subgroup.coe_subtype,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨t.2, ?_⟩
    have := congrArg Subtype.val ht
    simp only [coe_commEnd, OneMemClass.coe_one] at this
    exact (commutatorElement_eq_one_iff_mul_comm.1 this).symm
  · rintro ⟨hxS, hxc⟩
    refine ⟨⟨x, hxS⟩, ?_, rfl⟩
    ext
    simpa using commutatorElement_eq_one_iff_mul_comm.2 hxc.symm

theorem commEnd_chain (hy : ∀ s ∈ S, y * s * y⁻¹ ∈ S) (hS : Nat.card S = 27)
    (hS3 : ∀ s ∈ S, s ^ 3 = 1) (hy3 : y ^ 3 ∈ S) (hJ : ∃ s ∈ S, ⁅y, ⁅y, s⁆⁆ ≠ 1) :
    Nat.card ↥(S ⊓ centralizer {y}) = 3 ∧
    Nat.card {t : S // ⁅y, ⁅y, (t : G)⁆⁆ = 1} = 9 ∧
    (∀ t ∈ S, ⁅y, ⁅y, t⁆⁆ = 1 → ∃ u ∈ S, ⁅y, u⁆ = t) ∧
    (∀ t ∈ S, ⁅y, t⁆ = 1 → ∃ u ∈ S, ⁅y, ⁅y, u⁆⁆ = t) := by
  set δ := commEnd S y hy with hδ
  have h3 := commEnd_comp_cube S y hy hS3 hy3
  obtain ⟨-, -, hk1, hk2, hr1, hr2⟩ :=
    card_ker_range_of_nilpotent δ hS h3 (commEnd_comp_ne_one S y hy hJ)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hk1, ← map_ker_commEnd S y hy, Subgroup.card_map_of_injective S.subtype_injective]
  · rw [← hk2]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun t => ?_)
    rw [MonoidHom.mem_ker]
    constructor
    · intro ht
      ext
      simpa [δ] using ht
    · intro ht
      simpa [δ] using congrArg Subtype.val ht
  · intro t ht hc
    have : (⟨t, ht⟩ : S) ∈ (δ.comp δ).ker := by
      rw [MonoidHom.mem_ker]; ext; simpa [δ] using hc
    rw [← hr1] at this
    obtain ⟨u, hu⟩ := this
    exact ⟨u, u.2, by simpa [δ] using congrArg Subtype.val hu⟩
  · intro t ht hc
    have : (⟨t, ht⟩ : S) ∈ δ.ker := by
      rw [MonoidHom.mem_ker]; ext; simpa [δ] using hc
    rw [← hr2] at this
    obtain ⟨u, hu⟩ := this
    exact ⟨u, u.2, by simpa [δ] using congrArg Subtype.val hu⟩

end CommEnd

structure Wreath81 (R S : Subgroup G) : Prop where
  le : S ≤ R
  card_R : Nat.card R = 81
  card_S : Nat.card S = 27
  elemAbelian : IsElemAbelian 3 S
  normal_in : ∀ r ∈ R, ∀ s ∈ S, r * s * r⁻¹ ∈ S
  jordan : ∃ y ∈ R, y ∉ S ∧ ∃ s ∈ S, ⁅y, ⁅y, s⁆⁆ ≠ 1

@[expose] def Clauses (R S : Subgroup G) : Prop :=
  Nat.card R = 81 ∧ IsElemAbelian 3 S ∧ Nat.card S = 27 ∧
  (∀ E : Subgroup G, E ≤ R → IsElemAbelian 3 E → Nat.card E = 27 → E = S) ∧
  (∃ y ∈ R, y ∉ S ∧ orderOf y = 3) ∧
  Nat.card ↥(R ⊓ centralizer (R : Set G)) = 3 ∧
  ∀ y ∈ R, y ∉ S → orderOf y = 3 →
    S ⊓ centralizer {y} = R ⊓ centralizer (R : Set G) ∧
    Nat.card ↥(R ⊓ centralizer {y}) = 9 ∧
    (∃ s ∈ S, ⁅y, ⁅y, s⁆⁆ ≠ 1) ∧
    (∀ x : G, y⁻¹ * x ∈ S → orderOf x = 3 → ∃ s ∈ S, x = s * y * s⁻¹) ∧
    Nat.card {x : G // y⁻¹ * x ∈ S ∧ orderOf x = 3} = 9

namespace Wreath81

variable {R S : Subgroup G} (h : Wreath81 R S)
include h

theorem normal_subgroupOf : (S.subgroupOf R).Normal :=
  ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using h.normal_in g g.2 n hn⟩

theorem card_quotient : Nat.card (R ⧸ S.subgroupOf R) = 3 := by
  have h1 := Subgroup.card_mul_index (S.subgroupOf R)
  have h2 : Nat.card (S.subgroupOf R) = 27 := by
    rw [← h.card_S]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.le).toEquiv
  rw [h2, h.card_R] at h1
  have : (S.subgroupOf R).index = 3 := by omega
  rw [← this]; rfl

theorem cube_mem {y : G} (hy : y ∈ R) : y ^ 3 ∈ S := by
  haveI := h.normal_subgroupOf
  have := Subgroup.pow_index_mem (S.subgroupOf R) (⟨y, hy⟩ : R)
  rw [show (S.subgroupOf R).index = 3 from h.card_quotient, Subgroup.mem_subgroupOf] at this
  simpa using this

theorem exists_pow_mul {y : G} (hy : y ∈ R) (hyS : y ∉ S) {r : G} (hr : r ∈ R) :
    ∃ i : ℕ, i < 3 ∧ ∃ s ∈ S, r = y ^ i * s := by
  haveI := h.normal_subgroupOf
  have hQ := h.card_quotient
  set g : R ⧸ S.subgroupOf R := QuotientGroup.mk ⟨y, hy⟩ with hg
  have hg1 : g ≠ 1 := by
    intro h1
    rw [hg, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
    exact hyS h1
  have hg3 : g ^ 3 = 1 := by
    rw [hg, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    simpa using h.cube_mem hy
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have htop : Subgroup.zpowers g = ⊤ := zpowers_eq_top_of_prime_card hQ hg1
  have hmem : (QuotientGroup.mk ⟨r, hr⟩ : R ⧸ S.subgroupOf R) ∈ Subgroup.zpowers g := by
    rw [htop]; trivial
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
  have hk3 : g ^ k = g ^ (k % 3) := zpow_eq_zpow_emod k (by simpa using hg3 : g ^ (3 : ℤ) = 1)
  have hnn : 0 ≤ k % 3 := Int.emod_nonneg _ (by norm_num)
  have hlt : k % 3 < 3 := Int.emod_lt_of_pos _ (by norm_num)
  have hi : g ^ k = g ^ ((k % 3).toNat) := by
    rw [hk3, ← zpow_natCast, Int.toNat_of_nonneg hnn]
  have hq : (QuotientGroup.mk ⟨r, hr⟩ : R ⧸ S.subgroupOf R) =
      QuotientGroup.mk ((⟨y, hy⟩ : R) ^ ((k % 3).toNat)) := by
    rw [← hk, hi, hg, QuotientGroup.mk_pow]
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at hq
  refine ⟨(k % 3).toNat, by omega, (y ^ ((k % 3).toNat))⁻¹ * r, ?_, by group⟩
  have := S.inv_mem hq
  simpa [mul_assoc] using this

theorem cube_mul {y s : G} (hy : y ∈ R) (hs : s ∈ S) :
    (y * s) ^ 3 = ⁅y, ⁅y, s⁆⁆ * y ^ 3 := by
  haveI := h.elemAbelian.1
  exact mul_pow_three S y (h.normal_in y hy) h.elemAbelian.2 (h.cube_mem hy) ⟨s, hs⟩

theorem cube_eq_iff {y s : G} (hy : y ∈ R) (hs : s ∈ S) :
    (y * s) ^ 3 = y ^ 3 ↔ ⁅y, ⁅y, s⁆⁆ = 1 := by
  rw [h.cube_mul hy hs]
  exact mul_eq_right

theorem cube_sq_coset {y : G} (hy : y ∈ R) (hconst : ∀ s ∈ S, (y * s) ^ 3 = y ^ 3) {w : G}
    (hw : w ∈ S) : (y ^ 2 * w) ^ 3 = (y ^ 3)⁻¹ := by
  have hw' : y ^ 3 * w ∈ S := S.mul_mem (h.cube_mem hy) hw
  have hw'' : y⁻¹ * (y ^ 3 * w)⁻¹ * y ∈ S := by
    have := h.normal_in y⁻¹ (R.inv_mem hy) _ (S.inv_mem hw')
    simpa using this
  have e1 : y ^ 2 * w = (y * (y⁻¹ * (y ^ 3 * w)⁻¹ * y))⁻¹ := by group
  rw [e1, inv_pow, hconst _ hw'']

theorem jordan_all {y : G} (hy : y ∈ R) (hyS : y ∉ S) : ∃ s ∈ S, ⁅y, ⁅y, s⁆⁆ ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hconst : ∀ s ∈ S, (y * s) ^ 3 = y ^ 3 := fun s hs => by
    rw [h.cube_mul hy hs, hcon s hs, one_mul]
  obtain ⟨y₀, hy₀, hy₀S, s₀, hs₀, hne⟩ := h.jordan
  obtain ⟨i, hi, u, hu, rfl⟩ := h.exists_pow_mul hy hyS hy₀
  have hconst₀ : ∀ s ∈ S, (y ^ i * u * s) ^ 3 = (y ^ i * u) ^ 3 := by
    intro s hs
    interval_cases i
    · exact absurd (by simpa using hu) hy₀S
    · have h1 : (y ^ 1 * u * s) ^ 3 = y ^ 3 := by
        rw [pow_one, mul_assoc]; exact hconst _ (S.mul_mem hu hs)
      have h2 : (y ^ 1 * u) ^ 3 = y ^ 3 := by rw [pow_one]; exact hconst _ hu
      rw [h1, h2]
    · have h1 : (y ^ 2 * u * s) ^ 3 = (y ^ 3)⁻¹ := by
        rw [mul_assoc]; exact h.cube_sq_coset hy hconst (S.mul_mem hu hs)
      have h2 : (y ^ 2 * u) ^ 3 = (y ^ 3)⁻¹ := h.cube_sq_coset hy hconst hu
      rw [h1, h2]
  apply hne
  exact (h.cube_eq_iff hy₀ hs₀).1 (hconst₀ s₀ hs₀)

theorem chain {y : G} (hy : y ∈ R) (hyS : y ∉ S) :
    Nat.card ↥(S ⊓ centralizer {y}) = 3 ∧
    Nat.card {t : S // ⁅y, ⁅y, (t : G)⁆⁆ = 1} = 9 ∧
    (∀ t ∈ S, ⁅y, ⁅y, t⁆⁆ = 1 → ∃ u ∈ S, ⁅y, u⁆ = t) ∧
    (∀ t ∈ S, ⁅y, t⁆ = 1 → ∃ u ∈ S, ⁅y, ⁅y, u⁆⁆ = t) := by
  haveI := h.elemAbelian.1
  exact commEnd_chain S y (h.normal_in y hy) h.card_S h.elemAbelian.2 (h.cube_mem hy)
    (h.jordan_all hy hyS)

theorem card_inf_centralizer {y : G} (hy : y ∈ R) (hyS : y ∉ S) :
    Nat.card ↥(S ⊓ centralizer {y}) = 3 := (h.chain hy hyS).1

theorem center_eq {y : G} (hy : y ∈ R) (hyS : y ∉ S) :
    R ⊓ centralizer (R : Set G) = S ⊓ centralizer {y} := by
  haveI := h.elemAbelian.1
  ext z
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, SetLike.mem_coe,
    Set.mem_singleton_iff, forall_eq]
  constructor
  · rintro ⟨hzR, hz⟩
    have hzS : z ∈ S := by
      by_contra hzS
      obtain ⟨s, hs, hne⟩ := h.jordan_all hzR hzS
      apply hne
      have : ⁅z, s⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 (hz s (h.le hs)).symm
      rw [this, commutatorElement_one_right]
    exact ⟨hzS, hz y hy⟩
  · rintro ⟨hzS, hzy⟩
    refine ⟨h.le hzS, fun r hr => ?_⟩
    obtain ⟨i, -, s, hs, rfl⟩ := h.exists_pow_mul hy hyS hr
    have h1 : y ^ i * z = z * y ^ i := (show Commute y z from hzy).pow_left i |>.eq
    have h2 : s * z = z * s := by
      have := mul_comm' (⟨s, hs⟩ : S) ⟨z, hzS⟩
      exact congrArg Subtype.val this
    calc y ^ i * s * z = y ^ i * (s * z) := by rw [mul_assoc]
      _ = y ^ i * (z * s) := by rw [h2]
      _ = (y ^ i * z) * s := by rw [mul_assoc]
      _ = (z * y ^ i) * s := by rw [h1]
      _ = z * (y ^ i * s) := by rw [mul_assoc]

theorem card_centralizer {y : G} (hy : y ∈ R) (hyS : y ∉ S) :
    Nat.card ↥(R ⊓ centralizer {y}) = 9 := by
  haveI := h.normal_subgroupOf
  have hQ := h.card_quotient
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set g : R ⧸ S.subgroupOf R := QuotientGroup.mk ⟨y, hy⟩ with hg
  have hg1 : g ≠ 1 := by
    intro h1
    rw [hg, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
    exact hyS h1
  have htop : Subgroup.zpowers g = ⊤ := zpowers_eq_top_of_prime_card hQ hg1
  set C : Subgroup G := R ⊓ centralizer {y} with hC
  let f : C →* R ⧸ S.subgroupOf R :=
    (QuotientGroup.mk' (S.subgroupOf R)).comp (Subgroup.inclusion (inf_le_left : C ≤ R))
  have hyC : y ∈ C := ⟨hy, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩
  have hrange : f.range = ⊤ := by
    rw [eq_top_iff, ← htop, Subgroup.zpowers_le]
    exact ⟨⟨y, hyC⟩, rfl⟩
  have hmap : f.ker.map C.subtype = S ⊓ centralizer {y} := by
    ext x
    simp only [Subgroup.mem_map, MonoidHom.mem_ker, Subgroup.mem_inf, Subgroup.coe_subtype]
    constructor
    · rintro ⟨⟨c, hc⟩, hfc, rfl⟩
      refine ⟨?_, hc.2⟩
      have : (QuotientGroup.mk ⟨c, hc.1⟩ : R ⧸ S.subgroupOf R) = 1 := hfc
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at this
      exact this
    · rintro ⟨hxS, hxc⟩
      refine ⟨⟨x, h.le hxS, hxc⟩, ?_, rfl⟩
      show (QuotientGroup.mk ⟨x, h.le hxS⟩ : R ⧸ S.subgroupOf R) = 1
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact hxS
  have hker : Nat.card f.ker = 3 := by
    rw [← Subgroup.card_map_of_injective C.subtype_injective, hmap]
    exact h.card_inf_centralizer hy hyS
  have := Subgroup.card_ker_mul_card_range f
  rw [hrange, Subgroup.card_top, hQ, hker] at this
  omega

theorem eq_of_isElemAbelian {E : Subgroup G} (hE : E ≤ R) (hEa : IsElemAbelian 3 E)
    (hE27 : Nat.card E = 27) : E = S := by
  haveI : Finite S := Nat.finite_of_card_ne_zero (by rw [h.card_S]; norm_num)
  by_contra hne
  have hnot : ¬ E ≤ S := fun hle =>
    hne (Subgroup.eq_of_le_of_card_ge hle (by rw [hE27, h.card_S]))
  obtain ⟨e, heE, heS⟩ := SetLike.not_le_iff_exists.1 hnot
  have heR : e ∈ R := hE heE
  have hle : E ≤ R ⊓ centralizer {e} := by
    intro x hx
    refine Subgroup.mem_inf.2 ⟨hE hx, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    haveI := hEa.1
    have := mul_comm' (⟨x, hx⟩ : E) ⟨e, heE⟩
    exact congrArg Subtype.val this
  have h9 := h.card_centralizer heR heS
  haveI : Finite ↥(R ⊓ centralizer {e}) := Nat.finite_of_card_ne_zero (by rw [h9]; norm_num)
  have := Subgroup.card_le_of_le hle
  omega

theorem exists_orderOf_three : ∃ y ∈ R, y ∉ S ∧ orderOf y = 3 := by
  haveI := h.elemAbelian.1
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y₀, hy₀, hy₀S, -⟩ := h.jordan
  have hy₃ : y₀ ^ 3 ∈ S := h.cube_mem hy₀
  obtain ⟨-, -, -, hr⟩ := h.chain hy₀ hy₀S
  have hcomm : ⁅y₀, (y₀ ^ 3)⁻¹⁆ = 1 := by
    rw [commutatorElement_def]; group
  obtain ⟨u, hu, hue⟩ := hr _ (S.inv_mem hy₃) hcomm
  have hyR : y₀ * u ∈ R := R.mul_mem hy₀ (h.le hu)
  have hyS : y₀ * u ∉ S := fun hmem => hy₀S (by simpa using S.mul_mem hmem (S.inv_mem hu))
  have hcube : (y₀ * u) ^ 3 = 1 := by
    rw [h.cube_mul hy₀ hu, hue, inv_mul_cancel]
  refine ⟨y₀ * u, hyR, hyS, orderOf_eq_prime hcube ?_⟩
  intro h1
  exact hyS (h1 ▸ S.one_mem)

theorem exists_conj {y : G} (hy : y ∈ R) (hyS : y ∉ S) (hy3 : orderOf y = 3) {x : G}
    (hx : y⁻¹ * x ∈ S) (hx3 : orderOf x = 3) : ∃ s ∈ S, x = s * y * s⁻¹ := by
  haveI := h.elemAbelian.1
  have hy3' : y ^ 3 = 1 := by rw [← hy3]; exact pow_orderOf_eq_one y
  have hx3' : x ^ 3 = 1 := by rw [← hx3]; exact pow_orderOf_eq_one x
  have hxe : x = y * (y⁻¹ * x) := by group
  have hker : ⁅y, ⁅y, y⁻¹ * x⁆⁆ = 1 := by
    have := h.cube_mul hy hx
    rw [← hxe, hx3', hy3', mul_one] at this
    exact this.symm
  obtain ⟨-, -, hr, -⟩ := h.chain hy hyS
  obtain ⟨u, hu, hue⟩ := hr _ hx hker
  refine ⟨y * u⁻¹ * y⁻¹, ?_, ?_⟩
  · simpa using h.normal_in y hy u⁻¹ (S.inv_mem hu)
  · have hcomm : u⁻¹ * (y * u * y⁻¹) = (y * u * y⁻¹) * u⁻¹ := by
      have := mul_comm' (⟨u⁻¹, S.inv_mem hu⟩ : S) ⟨y * u * y⁻¹, h.normal_in y hy u hu⟩
      exact congrArg Subtype.val this
    calc x = y * (y⁻¹ * x) := hxe
      _ = y * ⁅y, u⁆ := by rw [hue]
      _ = y * (y * u * y⁻¹ * u⁻¹) := by rw [commutatorElement_def]
      _ = y * (u⁻¹ * (y * u * y⁻¹)) := by rw [← hcomm]
      _ = y * u⁻¹ * y⁻¹ * y * (y * u⁻¹ * y⁻¹)⁻¹ := by group

theorem card_orderThree_coset {y : G} (hy : y ∈ R) (hyS : y ∉ S) (hy3 : orderOf y = 3) :
    Nat.card {x : G // y⁻¹ * x ∈ S ∧ orderOf x = 3} = 9 := by
  haveI := h.elemAbelian.1
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hy3' : y ^ 3 = 1 := by rw [← hy3]; exact pow_orderOf_eq_one y
  have key : ∀ t : G, t ∈ S → (orderOf (y * t) = 3 ↔ ⁅y, ⁅y, t⁆⁆ = 1) := by
    intro t ht
    have hne : y * t ≠ 1 := by
      intro h1
      apply hyS
      have : y = t⁻¹ := eq_inv_of_mul_eq_one_left h1
      rw [this]; exact S.inv_mem ht
    rw [orderOf_eq_prime_iff]
    constructor
    · rintro ⟨h1, -⟩
      have := h.cube_mul hy ht
      rw [h1, hy3', mul_one] at this
      exact this.symm
    · intro h1
      refine ⟨?_, hne⟩
      rw [h.cube_mul hy ht, h1, hy3', mul_one]
  have e : {x : G // y⁻¹ * x ∈ S ∧ orderOf x = 3} ≃ {t : S // ⁅y, ⁅y, (t : G)⁆⁆ = 1} :=
    { toFun := fun x => ⟨⟨y⁻¹ * x, x.2.1⟩, (key _ x.2.1).1 (by simpa using x.2.2)⟩
      invFun := fun t => ⟨y * t, by simp, (key _ t.1.2).2 t.2⟩
      left_inv := fun x => by ext; simp
      right_inv := fun t => by ext; simp }
  rw [Nat.card_congr e]
  exact (h.chain hy hyS).2.1

theorem clauses : Clauses R S := by
  refine ⟨h.card_R, h.elemAbelian, h.card_S, fun E hE hEa hE27 => h.eq_of_isElemAbelian hE hEa hE27,
    h.exists_orderOf_three, ?_, ?_⟩
  · obtain ⟨y, hy, hyS, -⟩ := h.exists_orderOf_three
    rw [h.center_eq hy hyS, h.card_inf_centralizer hy hyS]
  · intro y hy hyS hy3
    refine ⟨?_, h.card_centralizer hy hyS, h.jordan_all hy hyS,
      fun x hx hx3 => h.exists_conj hy hyS hy3 hx hx3, h.card_orderThree_coset hy hyS hy3⟩
    rw [h.center_eq hy hyS]

end Wreath81

theorem isElemAbelian_map {H : Type*} [Group H] {S : Subgroup G} (hS : IsElemAbelian 3 S)
    (φ : G →* H) : IsElemAbelian 3 (S.map φ) := by
  haveI := hS.1
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · obtain ⟨a, ha⟩ := a
    obtain ⟨b, hb⟩ := b
    obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.1 ha
    obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.1 hb
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← map_mul, ← map_mul]
    congr 1
    exact congrArg Subtype.val (mul_comm' (⟨a', ha'⟩ : S) ⟨b', hb'⟩)
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hS.2 x hx, map_one]

theorem Wreath81.map {H : Type*} [Group H] {R S : Subgroup G} (h : Wreath81 R S) (φ : G ≃* H) :
    Wreath81 (R.map φ.toMonoidHom) (S.map φ.toMonoidHom) where
  le := Subgroup.map_mono h.le
  card_R := by rw [Subgroup.card_map_of_injective φ.injective]; exact h.card_R
  card_S := by rw [Subgroup.card_map_of_injective φ.injective]; exact h.card_S
  elemAbelian := isElemAbelian_map h.elemAbelian _
  normal_in := by
    rintro _ ⟨r, hr, rfl⟩ _ ⟨s, hs, rfl⟩
    exact ⟨r * s * r⁻¹, h.normal_in r hr s hs, by simp⟩
  jordan := by
    obtain ⟨y, hy, hyS, s, hs, hne⟩ := h.jordan
    refine ⟨φ y, ⟨y, hy, rfl⟩, ?_, φ s, ⟨s, hs, rfl⟩, ?_⟩
    · rintro ⟨z, hz, hzy⟩
      exact hyS (φ.injective hzy ▸ hz)
    · intro h1
      apply hne
      apply φ.injective
      simpa [map_commutatorElement] using h1

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K4bWreath
