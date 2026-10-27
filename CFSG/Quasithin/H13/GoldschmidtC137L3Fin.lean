module

public import CFSG.Quasithin.Background.B4L3Fin

public section

namespace CFSG.Quasithin.H13.U3.GC137

open CFSG.Quasithin.L3

@[expose] def stabΓ (c : Vec) : Subgroup Γ where
  carrier := {g | act g c = c}
  one_mem' := act_one c
  mul_mem' := fun {a b} ha hb => by
    have ha' : act a c = c := ha
    have hb' : act b c = c := hb
    show act (a * b) c = c
    rw [act_mul, hb', ha']
  inv_mem' := fun {a} ha => by
    have ha' : act a c = c := ha
    have h := act_inv_act a c
    rw [ha'] at h
    exact h

theorem mem_stabΓ {c : Vec} {g : Γ} : g ∈ stabΓ c ↔ act g c = c := Iff.rfl

set_option maxRecDepth 100000 in
theorem v4_stab : ∀ c : Vec, c ≠ 0 → ∀ g ∈ AS {0, c}, act g c = c := by decide +kernel

set_option maxRecDepth 100000 in
theorem v4_normal : ∀ c : Vec, c ≠ 0 → ∀ h : Γ, act h c = c → ∀ g ∈ AS {0, c},
    h * g * h⁻¹ ∈ AS {0, c} := by decide +kernel

@[expose] def IsOrd3 (y : Γ) : Prop := y * y * y = 1 ∧ y ≠ 1

instance : DecidablePred IsOrd3 := fun y => by unfold IsOrd3; infer_instance

set_option maxRecDepth 100000 in
theorem stab_not_v4 : ∀ c : Vec, c ≠ 0 → ∀ x : Γ, act x c = c → x ∉ AS {0, c} →
    ∃ g : Γ, act g c = c ∧ IsOrd3 (x * g * x⁻¹ * g⁻¹) := by decide +kernel

set_option maxRecDepth 100000 in
theorem v4_conj_trans : ∀ c : Vec, c ≠ 0 → ∀ a ∈ AS {0, c}, a ≠ 1 → ∀ b ∈ AS {0, c}, b ≠ 1 →
    ∃ g : Γ, act g c = c ∧ g * a * g⁻¹ = b := by decide +kernel

set_option maxRecDepth 100000 in
theorem v4_fix : ∀ c : Vec, c ≠ 0 → ∀ v : Vec, (∀ g ∈ AS {0, c}, act g v = v) →
    v = 0 ∨ v = c := by decide +kernel

@[expose] def v4Γ (c : Vec) (hc : c ≠ 0) : Subgroup Γ where
  carrier := {g | g ∈ AS {0, c}}
  one_mem' := Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun v => by
    rw [act_one, sub_self]; simp⟩
  mul_mem' := fun {a b} ha hb => AS_mul c hc a ha b hb
  inv_mem' := fun {a} ha => by
    have h := (AS_elem c hc a ha a ha).2
    have : a⁻¹ = a := inv_eq_of_mul_eq_one_right h
    show a⁻¹ ∈ AS {0, c}
    rw [this]
    exact ha

theorem mem_v4Γ {c : Vec} {hc : c ≠ 0} {g : Γ} : g ∈ v4Γ c hc ↔ g ∈ AS {0, c} := Iff.rfl

theorem v4Γ_le_stabΓ (c : Vec) (hc : c ≠ 0) : v4Γ c hc ≤ stabΓ c :=
  fun g hg => v4_stab c hc g hg

theorem v4Γ_normal (c : Vec) (hc : c ≠ 0) :
    ∀ h ∈ stabΓ c, ∀ n ∈ v4Γ c hc, h * n * h⁻¹ ∈ v4Γ c hc :=
  fun h hh n hn => v4_normal c hc h hh n hn

theorem card_v4Γ (c : Vec) (hc : c ≠ 0) : Nat.card (v4Γ c hc) = 4 := by
  have h := AS_card c hc
  rw [← h, ← Fintype.card_coe, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x => by
    simp only [mem_v4Γ])

theorem normal2_stab_eq (c : Vec) (hc : c ≠ 0) (N : Subgroup Γ) (hN : N ≤ stabΓ c)
    (hnorm : ∀ h ∈ stabΓ c, ∀ n ∈ N, h * n * h⁻¹ ∈ N) (hp : IsPGroup 2 N) (hne : N ≠ ⊥) :
    N = v4Γ c hc := by
  have hle : ∀ x ∈ N, x ∈ AS {0, c} := by
    intro x hx
    by_contra hxA
    obtain ⟨g, hg, h3, h1⟩ := stab_not_v4 c hc x (hN hx) hxA
    set y := x * g * x⁻¹ * g⁻¹ with hy
    have hcomm : y ∈ N := by
      have h2 : g * x⁻¹ * g⁻¹ ∈ N := hnorm g hg x⁻¹ (N.inv_mem hx)
      have := N.mul_mem hx h2
      simpa [hy, mul_assoc] using this
    obtain ⟨k, hk⟩ := hp ⟨_, hcomm⟩
    have hk' : y ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hy3 : y ^ 3 = 1 := by rw [pow_succ, pow_two]; exact h3
    have hd3 : orderOf y ∣ 3 := orderOf_dvd_of_pow_eq_one hy3
    have hd2 : orderOf y ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
    have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right _ (by norm_num)
    have : orderOf y ∣ 1 := hcop.gcd_eq_one ▸ Nat.dvd_gcd hd3 hd2
    exact h1 (orderOf_eq_one_iff.mp (Nat.dvd_one.mp this))
  obtain ⟨n, hn⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
  have hn1 : (n : Γ) ≠ 1 := fun h => hn (Subtype.ext h)
  ext y
  constructor
  · intro hy
    exact hle y hy
  · intro hy
    by_cases hy1 : y = 1
    · rw [hy1]; exact N.one_mem
    · obtain ⟨g, hg, hgy⟩ := v4_conj_trans c hc (n : Γ) (hle n n.2) hn1 y hy hy1
      rw [← hgy]
      exact hnorm g hg n n.2

end CFSG.Quasithin.H13.U3.GC137
