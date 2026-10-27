module

public import CFSG.RankThree.GroupTheory.ClassTwoThree
import CFSG.CharacterTheory.OddOrderBasics.Solvability
import Mathlib.Data.Nat.Choose.Dvd

public section

open scoped commutatorElement

namespace CFSG.RankThree

variable {P : Type*} [Group P] {p : ℕ}

theorem prime_dvd_choose_two_three (hp : p.Prime) (hp3 : 3 < p) :
    p ∣ p.choose 2 ∧ p ∣ p.choose 3 :=
  ⟨hp.dvd_choose_self (by norm_num) (by omega), hp.dvd_choose_self (by norm_num) hp3⟩

theorem mul_pow_prime_eq_of_lcomm_pow_eq_one (hP : (⊤ : Subgroup P).lowerCentralSeries 3 = ⊥)
    (hp : p.Prime) (hp3 : 3 < p) (x y : P) (hr : lcomm y x ^ p = 1)
    (hs : lcomm (lcomm y x) x ^ p = 1) (ht : lcomm (lcomm y x) y ^ p = 1) :
    (x * y) ^ p = x ^ p * y ^ p := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := prime_dvd_choose_two_three hp hp3
  rw [mul_pow_of_class_three hP x y p, ha, hb,
    show 2 * (p * b) + p * a = p * (2 * b + a) by ring, pow_mul, pow_mul, pow_mul, hr, hs, ht]
  simp

theorem closure_torsion_pow_eq_one {M : Subgroup P}
    (hM : ∀ x ∈ M, ∀ y ∈ M, x ^ p = 1 → y ^ p = 1 → (x * y) ^ p = 1) {z : P}
    (hz : z ∈ Subgroup.closure {w : P | w ∈ M ∧ w ^ p = 1}) : z ∈ M ∧ z ^ p = 1 := by
  induction hz using Subgroup.closure_induction with
  | mem w hw => exact hw
  | one => exact ⟨M.one_mem, one_pow p⟩
  | mul w₁ w₂ _ _ h₁ h₂ => exact ⟨M.mul_mem h₁.1 h₂.1, hM _ h₁.1 _ h₂.1 h₁.2 h₂.2⟩
  | inv w _ h => exact ⟨M.inv_mem h.1, by rw [inv_pow, h.2, inv_one]⟩

theorem conj_mem_closure_torsion {M : Subgroup P} {g : P}
    (hg : ∀ w ∈ M, g⁻¹ * w * g ∈ M) {z : P}
    (hz : z ∈ Subgroup.closure {w : P | w ∈ M ∧ w ^ p = 1}) :
    g⁻¹ * z * g ∈ Subgroup.closure {w : P | w ∈ M ∧ w ^ p = 1} := by
  induction hz using Subgroup.closure_induction with
  | mem w hw =>
    refine Subgroup.subset_closure ⟨hg w hw.1, ?_⟩
    rw [show g⁻¹ * w * g = g⁻¹ * w * g⁻¹⁻¹ by rw [inv_inv], conj_pow, hw.2]
    group
  | one => simp
  | mul w₁ w₂ _ _ h₁ h₂ =>
    have := Subgroup.mul_mem _ h₁ h₂
    rwa [show g⁻¹ * w₁ * g * (g⁻¹ * w₂ * g) = g⁻¹ * (w₁ * w₂) * g by group] at this
  | inv w _ h =>
    have := Subgroup.inv_mem _ h
    rwa [show (g⁻¹ * w * g)⁻¹ = g⁻¹ * w⁻¹ * g by group] at this

variable [Finite P]

theorem torsion_mul_closed_aux (hp : p.Prime) (hp3 : 3 < p) (hP : IsPGroup p P)
    (hγ : (⊤ : Subgroup P).lowerCentralSeries 3 = ⊥) (n : ℕ) :
    ∀ Q : Subgroup P, Nat.card Q = n →
      ∀ x ∈ Q, ∀ y ∈ Q, x ^ p = 1 → y ^ p = 1 → (x * y) ^ p = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro Q hQ x hx y hy hxp hyp
  by_cases hxy : y ∈ Subgroup.zpowers x
  · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxy
    rw [(Commute.self_zpow x k).mul_pow, hxp, one_mul, ← zpow_natCast, ← zpow_mul, mul_comm,
      zpow_mul, zpow_natCast, hxp, one_zpow]
  set x' : Q := ⟨x, hx⟩
  have hne : Subgroup.zpowers x' ≠ ⊤ := by
    intro htop
    have hy' : (⟨y, hy⟩ : Q) ∈ Subgroup.zpowers x' := htop ▸ Subgroup.mem_top _
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy'
    exact hxy (Subgroup.mem_zpowers_iff.mpr ⟨k, by
      have := congrArg Subtype.val hk
      rwa [Subgroup.coe_zpow] at this⟩)
  obtain ⟨M, hM, hxM⟩ := (eq_top_or_exists_le_coatom (Subgroup.zpowers x')).resolve_left hne
  have hMn : M.Normal := (CFSG.OddOrderBasics.p_group_maximal_index (hP.to_subgroup Q) M hM).1
  set M' : Subgroup P := M.map Q.subtype with hM'
  have hM'card : Nat.card M' < n := by
    rw [hM', Subgroup.card_map_of_injective Q.subtype_injective, ← hQ]
    rw [← Subgroup.card_top (G := Q)]
    exact Subgroup.card_lt_of_lt hM.lt_top
  have hM'closed := ih _ hM'card M' rfl
  set W : Subgroup P := Subgroup.closure {w : P | w ∈ M' ∧ w ^ p = 1}
  have hW : ∀ z ∈ W, z ^ p = 1 := fun z hz => (closure_torsion_pow_eq_one hM'closed hz).2
  have hxM' : x ∈ M' := ⟨x', hxM (Subgroup.mem_zpowers x'), rfl⟩
  have hxW : x ∈ W := Subgroup.subset_closure ⟨hxM', hxp⟩
  have hyM : ∀ w ∈ M', y⁻¹ * w * y ∈ M' := by
    rintro _ ⟨m, hm, rfl⟩
    refine ⟨(⟨y, hy⟩ : Q)⁻¹ * m * ⟨y, hy⟩, ?_, rfl⟩
    simpa using hMn.conj_mem m hm (⟨y, hy⟩ : Q)⁻¹
  have hyW : ∀ z ∈ W, y⁻¹ * z * y ∈ W := fun z hz => conj_mem_closure_torsion hyM hz
  have hr : lcomm y x ∈ W := by
    have h := W.mul_mem (hyW _ (W.inv_mem hxW)) hxW
    rwa [show y⁻¹ * x⁻¹ * y * x = lcomm y x from rfl] at h
  have hs : lcomm (lcomm y x) x ∈ W := by
    have h := W.mul_mem (W.mul_mem (W.mul_mem (W.inv_mem hr) (W.inv_mem hxW)) hr) hxW
    rwa [show (lcomm y x)⁻¹ * x⁻¹ * lcomm y x * x = lcomm (lcomm y x) x from rfl] at h
  have ht : lcomm (lcomm y x) y ∈ W := by
    have h := W.mul_mem (W.inv_mem hr) (hyW _ hr)
    rwa [show (lcomm y x)⁻¹ * (y⁻¹ * lcomm y x * y) = lcomm (lcomm y x) y by
      simp only [lcomm]; group] at h
  rw [mul_pow_prime_eq_of_lcomm_pow_eq_one hγ hp hp3 x y (hW _ hr) (hW _ hs) (hW _ ht), hxp,
    hyp, one_mul]

theorem omega_one_eq_torsion_and_powHom_of_class_three (hp : p.Prime) (hp3 : 3 < p)
    (hP : IsPGroup p P) (hγ : (⊤ : Subgroup P).lowerCentralSeries 3 = ⊥) :
    ((omega₁ P (p := p) : Subgroup P) : Set P) = {x : P | x ^ p = 1} ∧
      (∀ x ∈ omega₁ P (p := p), x ^ p = 1) ∧
      (commutator P ≤ omega₁ P (p := p) → ∃ θ : P →* P, ⇑θ = fun x => x ^ p) := by
  have hclosed : ∀ x y : P, x ^ p = 1 → y ^ p = 1 → (x * y) ^ p = 1 := fun x y hx hy =>
    torsion_mul_closed_aux hp hp3 hP hγ _ ⊤ rfl x (Subgroup.mem_top x) y (Subgroup.mem_top y)
      hx hy
  let T : Subgroup P :=
    { carrier := {x : P | x ^ p = 1}
      mul_mem' := fun {x y} hx hy => hclosed x y hx hy
      one_mem' := one_pow p
      inv_mem' := fun {x} hx => by
        change x⁻¹ ^ p = 1
        rw [inv_pow, show x ^ p = 1 from hx, inv_one] }
  have hΩ : omega₁ P (p := p) = T := by
    rw [omega₁, omega, pow_one]
    exact Subgroup.closure_eq T
  have hset : ((omega₁ P (p := p) : Subgroup P) : Set P) = {x : P | x ^ p = 1} := by
    rw [hΩ]
    rfl
  have hmem : ∀ x ∈ omega₁ P (p := p), x ^ p = 1 := fun x hx => by
    rw [← SetLike.mem_coe, hset] at hx
    exact hx
  refine ⟨hset, hmem, fun hcomm => ?_⟩
  have hc : ∀ c ∈ commutator P, c ^ p = 1 := fun c hc => hmem c (hcomm hc)
  have hmul : ∀ x y : P, (x * y) ^ p = x ^ p * y ^ p := fun x y =>
    mul_pow_prime_eq_of_lcomm_pow_eq_one hγ hp hp3 x y (hc _ (lcomm_mem_commutator y x))
      (hc _ (lcomm_mem_commutator _ x)) (hc _ (lcomm_mem_commutator _ y))
  exact ⟨MonoidHom.mk' (fun x => x ^ p) hmul, rfl⟩

end CFSG.RankThree
