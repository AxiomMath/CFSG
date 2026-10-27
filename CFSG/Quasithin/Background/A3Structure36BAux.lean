module

public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.Tactic.ContinuousFunctionalCalculus

public section

namespace CFSG.Quasithin.A36B

open scoped commutatorElement

theorem hom_eq_one_of_isPGroup_range {G H : Type*} [Group G] [Group.IsPerfect G] [Group H]
    [Finite H] {p : ℕ} [Fact p.Prime] (f : G →* H) (hf : IsPGroup p f.range) : f = 1 := by
  by_contra hne
  have hperf : Group.IsPerfect f.range := Group.IsPerfect.range f
  have hnil : Group.IsNilpotent f.range := hf.isNilpotent
  have hnt : Nontrivial f.range := by
    rw [Subgroup.nontrivial_iff_ne_bot]
    intro hbot
    apply hne
    ext x
    have hx : f x ∈ f.range := ⟨x, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hx
    rw [hx]
    rfl
  exact Group.IsPerfect.not_isNilpotent f.range hnil

theorem eq_inv_of_fixedPointFree {R : Type*} [Group R] [Finite R] (σ : MulAut R)
    (hσ : ∀ x, σ (σ x) = x) (hfix : ∀ x, σ x = x → x = 1) :
    (∀ x, σ x = x⁻¹) ∧ ∀ x y : R, x * y = y * x := by
  have hinj : Function.Injective (fun x : R => x⁻¹ * σ x) := by
    intro x y hxy
    have hxy' : x⁻¹ * σ x = y⁻¹ * σ y := hxy
    have h : σ (y * x⁻¹) = y * x⁻¹ := by
      rw [map_mul, map_inv]
      have h1 : σ y = y * (x⁻¹ * σ x) := by
        rw [hxy']
        group
      rw [h1]
      group
    have h2 := hfix _ h
    exact (mul_inv_eq_one.1 h2).symm
  have hsurj := Finite.injective_iff_surjective.1 hinj
  have hinv : ∀ x, σ x = x⁻¹ := by
    intro z
    obtain ⟨x, rfl⟩ := hsurj z
    show σ (x⁻¹ * σ x) = (x⁻¹ * σ x)⁻¹
    rw [map_mul, map_inv, hσ]
    group
  refine ⟨hinv, fun x y => ?_⟩
  have h1 := hinv (x⁻¹ * y⁻¹)
  rw [map_mul, hinv, hinv] at h1
  simp only [inv_inv, mul_inv_rev] at h1
  exact h1

theorem comm_of_sq_central_odd {Y : Type*} [Group Y] {m : ℕ} (hm : Odd m) {a b : Y}
    (ha : a ^ 2 ∈ Subgroup.center Y) (ha' : (a ^ 2) ^ m = 1)
    (hc : ⁅a ^ m, b⁆ ∈ Subgroup.center Y) (hc' : ⁅a ^ m, b⁆ ^ m = 1) :
    a * b = b * a := by
  obtain ⟨j, hj⟩ := hm
  obtain ⟨s, hs⟩ : ∃ s, s = a ^ m := ⟨_, rfl⟩
  obtain ⟨c, hcdef⟩ : ∃ c, c = ⁅s, b⁆ := ⟨_, rfl⟩
  rw [← hs] at hc hc'
  rw [← hcdef] at hc hc'
  have hs2 : s ^ 2 = 1 := by
    rw [hs, ← pow_mul, mul_comm, pow_mul]
    exact ha'
  have hcb : c * b = s * b * s⁻¹ := by
    rw [hcdef, commutatorElement_def]
    group
  have hsc : s * c * s⁻¹ = c := by
    have := Subgroup.mem_center_iff.1 hc s
    rw [this]
    group
  have h2 : s ^ 2 * b * (s ^ 2)⁻¹ = c ^ 2 * b := by
    have e1 : s ^ 2 * b * (s ^ 2)⁻¹ = s * (s * b * s⁻¹) * s⁻¹ := by
      rw [pow_two, mul_inv_rev]
      simp only [mul_assoc]
    rw [e1, ← hcb]
    have e2 : s * (c * b) * s⁻¹ = (s * c * s⁻¹) * (s * b * s⁻¹) := by
      simp only [mul_assoc, inv_mul_cancel_left]
    rw [e2, hsc, ← hcb, pow_two, mul_assoc]
  rw [hs2] at h2
  have hc2 : c ^ 2 = 1 := by
    have : b = c ^ 2 * b := by simpa using h2
    exact (mul_eq_right.1 this.symm)
  have hc1 : c = 1 := by
    have : c ^ m = c := by
      rw [hj, pow_succ, pow_mul, hc2, one_pow, one_mul]
    rw [← this]
    exact hc'
  have hsb : s * b = b * s := by
    have : ⁅s, b⁆ = 1 := by rw [← hcdef]; exact hc1
    exact commutatorElement_eq_one_iff_mul_comm.1 this
  have hw : Commute (a ^ 2) b := (Subgroup.mem_center_iff.1 ha b).symm
  have hdecomp : a = ((a ^ 2) ^ j)⁻¹ * s := by
    have : s = (a ^ 2) ^ j * a := by rw [hs, hj, pow_succ, pow_mul]
    rw [this, inv_mul_cancel_left]
  rw [hdecomp]
  have h3 : Commute (((a ^ 2) ^ j)⁻¹) b := (hw.pow_left j).inv_left
  have h4 : Commute s b := hsb
  exact (h3.mul_left h4)

theorem commutator_mem_of_odd_central {X : Type*} [Group X] [Finite X] (N K O : Subgroup X)
    [N.Normal] (hKc : ∀ k ∈ K, ∀ g : X, ⁅k, g⁆ ∈ N) (hOK : ∀ t ∈ O, ∀ g : X, ⁅t, g⁆ ∈ K)
    (hsq : ∀ t ∈ O, t ^ 2 ∈ K) (hodd : Odd (Nat.card K)) {t : X} (ht : t ∈ O) (g : X) :
    ⁅t, g⁆ ∈ N := by
  have hcen : ∀ k ∈ K, QuotientGroup.mk' N k ∈ Subgroup.center (X ⧸ N) := by
    intro k hk
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective y
    have h1 : QuotientGroup.mk' N ⁅k, g'⁆ = 1 := (QuotientGroup.eq_one_iff _).2 (hKc k hk g')
    rw [map_commutatorElement] at h1
    exact (commutatorElement_eq_one_iff_mul_comm.1 h1).symm
  have hpowK : ∀ k ∈ K, k ^ Nat.card K = 1 := by
    intro k hk
    have := pow_card_eq_one' (G := K) (x := ⟨k, hk⟩)
    exact congrArg Subtype.val this
  have hmain := comm_of_sq_central_odd (m := Nat.card K) hodd
    (a := QuotientGroup.mk' N t) (b := QuotientGroup.mk' N g)
    (by rw [← map_pow]; exact hcen _ (hsq t ht))
    (by rw [← map_pow, ← map_pow, hpowK _ (hsq t ht), map_one])
    (by
      rw [← map_pow, ← map_commutatorElement]
      exact hcen _ (hOK _ (pow_mem ht _) g))
    (by
      rw [← map_pow, ← map_commutatorElement, ← map_pow, hpowK _ (hOK _ (pow_mem ht _) g),
        map_one])
  have h1 : QuotientGroup.mk' N ⁅t, g⁆ = 1 := by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 hmain
  exact (QuotientGroup.eq_one_iff _).1 h1

theorem relIndex_eq_card_map {X : Type*} [Group X] (N O : Subgroup X) [N.Normal] :
    N.relIndex O = Nat.card (O.map (QuotientGroup.mk' N)) := by
  have h := Subgroup.relIndex_ker (QuotientGroup.mk' N) (K := O)
  rwa [QuotientGroup.ker_mk'] at h

end CFSG.Quasithin.A36B
