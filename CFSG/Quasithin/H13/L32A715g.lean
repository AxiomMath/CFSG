module

public import CFSG.Quasithin.H13.L32A715f
public import CFSG.Quasithin.H13.L32A714b
public import CFSG.Quasithin.H13.L32A715e

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.S153Q CFSG.Quasithin.S153Q.Q4A

namespace HeisMod

variable {W : Type} [CommGroup W]

theorem pow_three_apply_of_pt {c : MulAut W} (hc3 : c ^ 3 = 1) (hfpf : ∀ w : W, c w = w → w = 1)
    {o : Subgroup W} (ho : IsPt c o) {f : MulAut W} (hfc : f * c = c * f)
    (hfo : ∀ x ∈ o, f x ∈ o) {x : W} (hx : x ∈ o) : (f ^ 3) x = x := by
  have h3 : (f ^ 3) x = f (f (f x)) := by
    rw [pow_succ, pow_succ, pow_one]
    rfl
  rw [h3]
  by_cases hx1 : x = 1
  · rw [hx1, map_one, map_one, map_one]
  have hfx1 : f x ≠ 1 := fun e => hx1 (f.injective (e.trans (map_one f).symm))
  have hfc' : ∀ w : W, f (c w) = c (f w) := comm_apply hfc
  rcases pt_mem_cases hc3 hfpf ho hx hx1 (f x) (hfo x hx) with e | e | e | e
  · exact absurd e hfx1
  · rw [e, e, e]
  · simp only [e, hfc', z_cube_apply hc3]
  · simp only [e, hfc', z_cube_apply hc3]

theorem pow_three_eq_one_of_comm (hW2 : ∀ w : W, w * w = 1) {a c f : MulAut W}
    (hc3 : c ^ 3 = 1) (hfpf : ∀ w : W, c w = w → w = 1) (ha3 : a ^ 3 = 1)
    (hac : a * c = c * a) (h4 : ∀ j, j < 3 → Nat.card (wt a c j) = 4) (hfa : f * a = a * f)
    (hfc : f * c = c * f) : f ^ 3 = 1 := by
  have hpt : ∀ j, j < 3 → IsPt c (wt a c j) := fun j hj =>
    ⟨h4 j hj, fun x hx => wt_invariant hac hx⟩
  have hfw : ∀ j : ℕ, ∀ x ∈ wt a c j, f x ∈ wt a c j := by
    intro j x hx
    rw [mem_wt] at hx ⊢
    rw [← comm_apply hfa, hx, comm_apply ((Commute.pow_right (show Commute f c from hfc) j).eq)]
  have hfix : ∀ j, j < 3 → ∀ x ∈ wt a c j, (f ^ 3) x = x := fun j hj x hx =>
    pow_three_apply_of_pt hc3 hfpf (hpt j hj) hfc (hfw j) hx
  ext w
  rw [MulAut.one_apply]
  have e := proj_prod hW2 (a := a) hc3 hfpf w
  rw [← e, map_mul, map_mul, hfix 0 (by norm_num) _ (proj_mem hc3 ha3 hac 0 w),
    hfix 1 (by norm_num) _ (proj_mem hc3 ha3 hac 1 w),
    hfix 2 (by norm_num) _ (proj_mem hc3 ha3 hac 2 w)]

end HeisMod

section Gen

variable {Γ : Type*} [Group Γ] [Finite Γ]

theorem mem_of_pow_three_pow {X : Subgroup Γ} [X.Normal] (hX : IsPOnePlusTwo 3 ↥X)
    (hrank : Open.pRank 3 (⊤ : Subgroup Γ) ≤ 2) {W : Type} [CommGroup W]
    (hW2 : ∀ w : W, w * w = 1) (ρ : Γ →* MulAut W) (hρ : Function.Injective ρ) {c : Γ}
    (hcZ : c ∈ (Subgroup.center ↥X).map X.subtype) (hc1 : c ≠ 1)
    (hfpf : ∀ w : W, ρ c w = w → w = 1)
    (h4 : ∀ a ∈ X, a ∉ (Subgroup.center ↥X).map X.subtype → ∀ j, j < 3 →
      Nat.card (HeisMod.wt (ρ a) (ρ c) j) = 4)
    {y : Γ} {m : ℕ} (hy : y ^ 3 ^ m = 1) : y ∈ X := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hXc : ∀ x ∈ X, (x : Γ) ^ 3 = 1 := fun x hx => by
    have := Heis.pow_three_eq hX ⟨x, hx⟩
    simpa using congrArg Subtype.val this
  obtain ⟨c', hc'Z, rfl⟩ := hcZ
  obtain ⟨a, haX, haZ, b, hbX, hcomm⟩ := exists_comm_mul hX hy
  set y' := b * y with hy'
  have hX3 : IsPGroup 3 ↥X := IsPGroup.of_card hX.2.1
  have hy3 : IsPGroup 3 ↥(Subgroup.zpowers y) := by
    rintro ⟨g, hg⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    refine ⟨m, Subtype.ext ?_⟩
    change (y ^ n) ^ 3 ^ m = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy, one_zpow]
  have hXy3 : IsPGroup 3 ↥(X ⊔ Subgroup.zpowers y) := hX3.to_sup_of_normal_left hy3
  have hy'mem : y' ∈ X ⊔ Subgroup.zpowers y :=
    Subgroup.mul_mem _ (Subgroup.mem_sup_left hbX) (Subgroup.mem_sup_right (Subgroup.mem_zpowers y))
  obtain ⟨k, hk⟩ := hXy3 ⟨y', hy'mem⟩
  have hk' : y' ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hy'c : y' * (c' : Γ) = c' * y' := by
    have := conj_center_of_pow_odd hX (Odd.pow (by decide : Odd 3)) hk' ⟨c', hc'Z, rfl⟩
    change y' * (c' : Γ) * y'⁻¹ = c' at this
    calc y' * (c' : Γ) = y' * c' * y'⁻¹ * y' := by group
      _ = c' * y' := by rw [this]
  have hac : a * (c' : Γ) = c' * a := by
    have := congrArg Subtype.val (Subgroup.mem_center_iff.mp hc'Z ⟨a, haX⟩)
    exact this
  have hmulAut : ∀ g h : Γ, g * h = h * g → ρ g * ρ h = ρ h * ρ g := fun g h e => by
    rw [← map_mul, e, map_mul]
  have hρc3 : ρ c' ^ 3 = 1 := by rw [← map_pow, hXc _ c'.2, map_one]
  have hρa3 : ρ a ^ 3 = 1 := by rw [← map_pow, hXc a haX, map_one]
  have hcube : ρ y' ^ 3 = 1 :=
    HeisMod.pow_three_eq_one_of_comm hW2 hρc3 hfpf hρa3 (hmulAut _ _ hac) (h4 a haX haZ)
      (hmulAut _ _ hcomm) (hmulAut _ _ hy'c)
  have hy'3 : y' ^ 3 = 1 := hρ (by rw [map_pow, hcube, map_one])
  by_contra hyX
  have hy'X : y' ∉ X := fun h => hyX (by
    have := X.mul_mem (X.inv_mem hbX) h
    rwa [hy', ← mul_assoc, inv_mul_cancel, one_mul] at this)
  have hc'1 : c' ≠ 1 := fun e => hc1 (by rw [e]; rfl)
  refine absurd (three_le_pRank hy'3 (hXc a haX) (hXc _ c'.2) hcomm hy'c hac ?_)
    (by omega)
  intro i j l hi hj hl h
  have hi0 : i = 0 := by
    have hyi : y' ^ i ∈ X := by
      have e : y' ^ i = ((a : Γ) ^ j * (c' : Γ) ^ l)⁻¹ := eq_inv_of_mul_eq_one_left
        (by rw [← mul_assoc]; exact h)
      rw [e]
      exact X.inv_mem (X.mul_mem (X.pow_mem haX j) (X.pow_mem c'.2 l))
    interval_cases i
    · rfl
    · exact absurd (by simpa using hyi) hy'X
    · exfalso
      apply hy'X
      have e : y' = (y' ^ 2) ^ 2 * (y' ^ 3)⁻¹ := by group
      rw [e, hy'3, inv_one, mul_one]
      exact X.pow_mem hyi 2
  subst hi0
  rw [pow_zero, one_mul] at h
  have hajZ : (⟨a, haX⟩ : ↥X) ^ j ∈ Subgroup.center ↥X := by
    have e : (⟨a, haX⟩ : ↥X) ^ j = (c' ^ l)⁻¹ := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_inv, Subgroup.coe_pow]
      exact eq_inv_of_mul_eq_one_left h
    rw [e]
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hc'Z l)
  have haZ' : (⟨a, haX⟩ : ↥X) ∉ Subgroup.center ↥X := fun e => haZ ⟨_, e, rfl⟩
  have hj0 : j = 0 := by
    interval_cases j
    · rfl
    · exact absurd (by simpa using hajZ) haZ'
    · exact absurd (Heis.mem_center_of_sq hX hajZ) haZ'
  subst hj0
  rw [pow_zero, one_mul] at h
  refine ⟨rfl, rfl, ?_⟩
  have hc'3 : c' ^ 3 = 1 := Heis.pow_three_eq hX c'
  have hl' : c' ^ l = 1 := Subtype.ext (by simpa using h)
  interval_cases l
  · rfl
  · exact absurd (by simpa using hl') hc'1
  · exfalso
    apply hc'1
    have e : c' = c' ^ 3 * (c' ^ 2)⁻¹ := by group
    rw [e, hc'3, hl']
    simp

end Gen

end CFSG.Quasithin.H13.L32A
