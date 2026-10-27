module

public import CFSG.Quasithin.Recognition.Kleidman.ThreeLocalCentralizerAnalysis.BetaWords
public import CFSG.Quasithin.Recognition.Kleidman.ThreeLocalCentralizerAnalysis.BetaSplit
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Quasithin.Kleidman.ThreeLocal

open Subgroup

variable {K X : Type*} [Group K] [Group X]

theorem mem_complement_of_sq_eq_one {Γ : Type*} [Group Γ] {y : Γ} (hy : y ∈ center Γ)
    (hy3 : orderOf y = 3) {S : Subgroup Γ} (hinf : zpowers y ⊓ S = ⊥)
    (hsup : zpowers y ⊔ S = ⊤) {γ : Γ} (hγ : γ * γ = 1) : γ ∈ S := by
  have := normal_zpowers_of_mem_center hy
  have hγ' : γ ∈ S ⊔ zpowers y := by rw [sup_comm, hsup]; exact mem_top γ
  have hmul := Subgroup.mul_normal S (zpowers y)
  have : γ ∈ ((S ⊔ zpowers y : Subgroup Γ) : Set Γ) := hγ'
  rw [hmul] at this
  obtain ⟨s, hs, z, hz, rfl⟩ := this
  dsimp only at hγ ⊢
  have hzc : z ∈ center Γ := (zpowers_le.mpr hy) hz
  have hzs : z * s = s * z := ((Subgroup.mem_center_iff.mp hzc) s).symm
  have hy3' : ∀ w ∈ zpowers y, w ^ 3 = 1 := by
    intro w hw
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hw
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
      show y ^ 3 = 1 by simpa [hy3] using pow_orderOf_eq_one y, one_zpow]
  have hz3 := hy3' z hz
  have hsq : (s * s) * (z * z) = 1 := by
    calc (s * s) * (z * z) = s * (s * z) * z := by simp only [mul_assoc]
      _ = s * (z * s) * z := by rw [hzs]
      _ = (s * z) * (s * z) := by simp only [mul_assoc]
      _ = 1 := hγ
  have hzz : z * z ∈ S := by
    have : z * z = (s * s)⁻¹ := eq_inv_of_mul_eq_one_right hsq
    rw [this]; exact S.inv_mem (S.mul_mem hs hs)
  have hzz' : z * z ∈ zpowers y := (zpowers y).mul_mem hz hz
  have : z * z = 1 := by
    have : z * z ∈ zpowers y ⊓ S := ⟨hzz', hzz⟩
    rw [hinf] at this
    exact this
  have hz1 : z = 1 := by
    calc z = z ^ 3 * (z * z)⁻¹ := by group
      _ = 1 := by rw [hz3, this]; simp
  rw [hz1, mul_one]
  exact hs

theorem exists_lift_beta [Finite K] {y₀ : K} (hyc : y₀ ∈ center K) (hy3 : orderOf y₀ = 3)
    (κ : K →* X) (hκs : Function.Surjective κ) (hκk : κ.ker = zpowers y₀)
    (𝒮 : Subgroup X) (h𝒮 : Nat.card 𝒮 = 24)
    (hreal : ∀ x ∈ 𝒮, x ^ 3 = 1 → x ≠ 1 → ∃ u ∈ 𝒮, u * x * u⁻¹ = x⁻¹)
    (τ : Fin 7 → K) (hτ0 : τ 0 = y₀) (hτ𝒮 : ∀ i : Fin 7, i.val ≤ 3 → κ (τ i) ∈ 𝒮)
    (hτsq : ∀ i : Fin 7, 1 ≤ i.val → i.val ≤ 3 → τ i * τ i = 1)
    {s : X} (hs : s ∈ 𝒮)
    (hrel : ∀ r ∈ a2Rels, evalWord (fun i => if i = 6 then s else κ (τ i)) r = 1) :
    ∃ β : K, ∀ r ∈ a2Rels, evalWord (Function.update τ 6 β) r = 1 := by
  classical
  set Γ : Subgroup K := 𝒮.comap κ with hΓdef
  have hmemΓ : ∀ k : K, k ∈ Γ ↔ κ k ∈ 𝒮 := fun k => Iff.rfl
  have hκy : κ y₀ = 1 := by
    rw [← MonoidHom.mem_ker, hκk]; exact mem_zpowers y₀
  have hy₀Γ : y₀ ∈ Γ := by rw [hmemΓ, hκy]; exact 𝒮.one_mem
  let y' : Γ := ⟨y₀, hy₀Γ⟩
  let Φ : Γ →* X := κ.comp Γ.subtype
  have hΦ : ∀ γ : Γ, Φ γ = κ γ.1 := fun γ => rfl
  have hy'c : y' ∈ center Γ := by
    rw [Subgroup.mem_center_iff]
    intro γ
    exact Subtype.ext ((Subgroup.mem_center_iff.mp hyc) γ.1)
  have hy'3 : orderOf y' = 3 := by
    have h := Subgroup.orderOf_coe y'
    rw [← h]; exact hy3
  have hy'3' : y' ^ 3 = 1 := by simpa [hy'3] using pow_orderOf_eq_one y'
  have hkerΦ : Φ.ker = zpowers y' := by
    ext γ
    rw [MonoidHom.mem_ker, hΦ, ← MonoidHom.mem_ker, hκk, mem_zpowers_iff, mem_zpowers_iff]
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨n, Subtype.ext (by simpa using hn)⟩
    · rintro ⟨n, hn⟩
      exact ⟨n, by simpa using congrArg Subtype.val hn⟩
  have hrange : Φ.range = 𝒮 := by
    ext x
    constructor
    · rintro ⟨γ, rfl⟩
      exact γ.2
    · intro hx
      obtain ⟨k, rfl⟩ := hκs x
      exact ⟨⟨k, hx⟩, rfl⟩
  have hcard : Nat.card Γ = 72 := by
    have := Subgroup.card_ker_mul_card_range Φ
    rw [hkerΦ, hrange, h𝒮, Nat.card_zpowers, hy'3] at this
    omega
  have hΦreal : ∀ x : Γ, Φ x ^ 3 = 1 → Φ x ≠ 1 →
      ∃ u : Γ, Φ u * Φ x * (Φ u)⁻¹ = (Φ x)⁻¹ := by
    intro x h3 h1
    obtain ⟨u, hu, hconj⟩ := hreal (Φ x) x.2 h3 h1
    obtain ⟨k, hk⟩ := hκs u
    refine ⟨⟨k, by rw [hmemΓ, hk]; exact hu⟩, ?_⟩
    show κ k * κ x.1 * (κ k)⁻¹ = (κ x.1)⁻¹
    rw [hk]
    exact hconj
  have hno9 := no_order_nine hy'c hy'3 hcard Φ hkerΦ hΦreal
  obtain ⟨S, hinf, hsup⟩ := exists_complement_of_central_three hy'c hy'3 hcard hno9
  have := normal_zpowers_of_mem_center hy'c
  let ε : Fin 7 → Γ := fun i => if h : i.val ≤ 3 then ⟨τ i, hτ𝒮 i h⟩ else 1
  have hε0 : ε 0 = y' := by
    apply Subtype.ext
    simp [ε, hτ0, y']
  have hεS : ∀ i : Fin 7, 1 ≤ i.val → i.val ≤ 3 → ε i ∈ S := by
    intro i h1 h3
    refine mem_complement_of_sq_eq_one hy'c hy'3 hinf hsup ?_
    apply Subtype.ext
    simpa [ε, h3] using hτsq i h1 h3
  have hε_big : ∀ i : Fin 7, ¬ i.val ≤ 3 → ε i = 1 := fun i h => by simp [ε, h]
  have hΦε : ∀ i : Fin 7, i.val ≤ 3 → Φ (ε i) = κ (τ i) := fun i h => by simp [ε, h, hΦ]
  obtain ⟨γ0, hγ0⟩ : ∃ γ0 : Γ, Φ γ0 = s := by
    have : s ∈ Φ.range := hrange ▸ hs
    exact this
  have hγ0' : γ0 ∈ ((S ⊔ zpowers y' : Subgroup Γ) : Set Γ) := by
    rw [sup_comm, hsup]; exact mem_top γ0
  rw [Subgroup.mul_normal S (zpowers y')] at hγ0'
  obtain ⟨s0, hs0, z0, hz0, hγ0eq⟩ := hγ0'
  have hΦs0 : Φ s0 = s := by
    have hz0k : Φ z0 = 1 := by rw [← MonoidHom.mem_ker, hkerΦ]; exact hz0
    have : Φ (s0 * z0) = s := by rw [← hγ0]; exact congrArg Φ hγ0eq
    rw [map_mul, hz0k, mul_one] at this
    exact this
  refine ⟨((y' * s0 : Γ) : K), fun r hr => ?_⟩
  have hlet := a2Rels_letters r hr
  let τΓ : Fin 7 → Γ := fun i => if i = 6 then y' * s0 else ε i
  have hmapι : evalWord (Function.update τ 6 ((y' * s0 : Γ) : K)) r =
      Γ.subtype (evalWord τΓ r) := by
    rw [evalWord_map]
    apply evalWord_congr
    intro x hx
    have hx' := hlet x hx
    by_cases h6 : x.1 = 6
    · simp [τΓ, h6]
    · have h3 : x.1.val ≤ 3 := by
        rcases hx' with h | h
        · exact h
        · exact absurd (Fin.ext h) h6
      simp [τΓ, h6, ε, h3, Function.update_of_ne h6]
  rw [hmapι]
  let n : Fin 7 → ℤ := fun i => if i = 0 ∨ i = 6 then 1 else 0
  let σ : Fin 7 → Γ := fun i => if i = 0 then 1 else if i = 6 then s0 else ε i
  have hτΓ : ∀ i, τΓ i = y' ^ n i * σ i := by
    intro i
    by_cases h0 : i = 0
    · subst h0
      simp [τΓ, n, σ, hε0]
    · by_cases h6 : i = 6
      · subst h6
        simp [τΓ, n, σ]
      · simp [τΓ, n, σ, h0, h6]
  have hσS : ∀ i, σ i ∈ S := by
    intro i
    by_cases h0 : i = 0
    · simp [σ, h0, S.one_mem]
    · by_cases h6 : i = 6
      · simp only [σ, h6, if_true, if_false, h0]
        exact hs0
      · simp only [σ, h0, h6, if_false]
        by_cases h3 : i.val ≤ 3
        · exact hεS i (by
            rcases Nat.eq_zero_or_pos i.val with h | h
            · exact absurd (Fin.ext h) h0
            · exact h) h3
        · rw [hε_big i h3]; exact S.one_mem
  have hcentral : ∀ g : Γ, g * y' = y' * g := fun g => (Subgroup.mem_center_iff.mp hy'c) g
  have hev := evalWord_central hcentral n σ τΓ hτΓ r
  have hexp := a2Rels_exponent r hr
  have hw : evalWord σ r = 1 := by
    have hwS : evalWord σ r ∈ S := evalWord_mem (fun x _ => hσS x.1)
    have hwΦ : Φ (evalWord σ r) = 1 := by
      rw [evalWord_map, ← hrel r hr]
      apply evalWord_congr
      intro x hx
      by_cases h6 : x.1 = 6
      · simp [σ, h6, hΦs0]
      · have h3 : x.1.val ≤ 3 := by
          rcases hlet x hx with h | h
          · exact h
          · exact absurd (Fin.ext h) h6
        by_cases h0 : x.1 = 0
        · simp [σ, h0, h6, hτ0, hκy]
        · simp [σ, h0, h6, hΦε x.1 h3]
    have : evalWord σ r ∈ zpowers y' ⊓ S := ⟨by rw [← hkerΦ]; exact hwΦ, hwS⟩
    rw [hinf] at this
    exact this
  rw [hev, hw, mul_one]
  obtain ⟨m, hm⟩ := hexp
  rw [show (r.map fun x => if x.2 then n x.1 else - n x.1).sum = 3 * m from hm, zpow_mul]
  simp [hy'3']

end CFSG.Quasithin.Kleidman.ThreeLocal
