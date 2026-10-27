module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.PresentationLocalCarmichael

public section

namespace CFSG.Quasithin.C35Pf

open CFSG.ComponentClassification.PresentationLocal
open scoped commutatorElement

section Central

variable {K : Type*} [Group K]

theorem commutatorElement_mul_central_left {c : K} (hc : c ∈ Subgroup.center K) (h b : K) :
    ⁅h * c, b⁆ = ⁅h, b⁆ := by
  have e : c * b * c⁻¹ = b := by
    rw [← Subgroup.mem_center_iff.1 hc b, mul_inv_cancel_right]
  rw [commutatorElement_def, commutatorElement_def, mul_inv_rev]
  calc h * c * b * (c⁻¹ * h⁻¹) * b⁻¹ = h * (c * b * c⁻¹) * h⁻¹ * b⁻¹ := by group
    _ = h * b * h⁻¹ * b⁻¹ := by rw [e]

theorem commutatorElement_mul_central_right {c : K} (hc : c ∈ Subgroup.center K) (a h : K) :
    ⁅a, h * c⁆ = ⁅a, h⁆ := by
  have e : c * a⁻¹ * c⁻¹ = a⁻¹ := by
    rw [← Subgroup.mem_center_iff.1 hc a⁻¹, mul_inv_cancel_right]
  rw [commutatorElement_def, commutatorElement_def, mul_inv_rev]
  calc a * (h * c) * a⁻¹ * (c⁻¹ * h⁻¹) = a * h * (c * a⁻¹ * c⁻¹) * h⁻¹ := by group
    _ = a * h * a⁻¹ * h⁻¹ := by rw [e]

end Central

section Lift

variable {K G : Type*} [Group K] [Group G] (θ : K →* G)

@[expose] def SqOne (x : G) : Prop := ∀ y, θ y = x → y * y = 1

variable {θ} {z : K} (hz : z ∈ Subgroup.center K) (hker : ∀ y, θ y = 1 → y = 1 ∨ y = z)
  (hzz : z * z = 1)

include hz hker hzz in
theorem sqOne_of_lift {x : G} {y : K} (hy : θ y = x) (h1 : y * y = 1) : SqOne θ x := by
  intro y' hy'
  rcases hker (y⁻¹ * y') (by rw [map_mul, map_inv, hy, hy', inv_mul_cancel]) with h | h
  · have e : y' = y := by rw [← mul_inv_cancel_left y y', h, mul_one]
    rw [e, h1]
  · have e : y' = y * z := by rw [← h, mul_inv_cancel_left]
    have hzc := Subgroup.mem_center_iff.1 hz y
    rw [e]
    calc y * z * (y * z) = y * (z * y) * z := by group
      _ = y * (y * z) * z := by rw [← hzc]
      _ = (y * y) * (z * z) := by group
      _ = 1 := by rw [h1, hzz, one_mul]

include hz hker hzz in
theorem sq_eq_z_of_not_sqOne {x : G} (hx : ¬ SqOne θ x) (hxx : x * x = 1) {y : K}
    (hy : θ y = x) : y * y = z := by
  rcases hker (y * y) (by rw [map_mul, hy, hxx]) with h | h
  · exact absurd (sqOne_of_lift hz hker hzz hy h) hx
  · exact h

theorem sqOne_conj (hθ : Function.Surjective θ) {x : G} (h : SqOne θ x) (c : G) :
    SqOne θ (c * x * c⁻¹) := by
  intro y hy
  obtain ⟨d, hd⟩ := hθ c
  have h1 := h (d⁻¹ * y * d) (by rw [map_mul, map_mul, map_inv, hd, hy]; group)
  calc y * y = d * ((d⁻¹ * y * d) * (d⁻¹ * y * d)) * d⁻¹ := by group
    _ = 1 := by rw [h1]; group

theorem sqOne_conj_iff (hθ : Function.Surjective θ) (x c : G) :
    SqOne θ (c * x * c⁻¹) ↔ SqOne θ x := by
  refine ⟨fun h => ?_, fun h => sqOne_conj hθ h c⟩
  have := sqOne_conj hθ h c⁻¹
  rwa [show c⁻¹ * (c * x * c⁻¹) * c⁻¹⁻¹ = x by group] at this

include hker in
theorem commutator_eq_z (hz1 : z ≠ 1) {y y' : K} (hc : θ y * θ y' = θ y' * θ y)
    (h1 : y * y = 1) (h2 : y' * y' = z) (h3 : (y * y') * (y * y') = 1) : ⁅y, y'⁆ = z := by
  have hk : θ ⁅y, y'⁆ = 1 := by
    rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv, hc]
    group
  rcases hker _ hk with hk1 | hkz
  · exfalso
    apply hz1
    have hcomm : y * y' = y' * y := commutatorElement_eq_one_iff_mul_comm.1 hk1
    calc z = (y * y) * (y' * y') := by rw [h1, h2, one_mul]
      _ = y * (y * y') * y' := by group
      _ = y * (y' * y) * y' := by rw [hcomm]
      _ = (y * y') * (y * y') := by group
      _ = 1 := h3
  · exact hkz

end Lift

section Carmichael

variable {K G : Type} [Group K] [Group G] {θ : K →* G} {z : K}

theorem exists_not_sqOne_carmichael {n : ℕ} (hn : 3 ≤ n) (hθ : Function.Surjective θ)
    (hz : z ∈ Subgroup.center K) (hθz : θ z = 1) (hker : ∀ y, θ y = 1 → y = 1 ∨ y = z)
    (hzz : z * z = 1) (hperf : commutator K = ⊤) (L : CarmichaelIndex n → G)
    (hL3 : ∀ k, L k ^ 3 = 1) (hgen : Subgroup.closure (Set.range L) = ⊤)
    (hcard : Nat.card (alternatingGroup (Fin n)) < Nat.card K) :
    ∃ k l, k ≠ l ∧ ¬ SqOne θ (L k * L l) := by
  classical
  by_contra hcon
  push Not at hcon
  have hkc : ∀ y, θ y = 1 → y ∈ Subgroup.center K := fun y hy => by
    rcases hker y hy with rfl | rfl
    · exact Subgroup.one_mem _
    · exact hz
  choose y hy using fun k => hθ (L k)
  let x : CarmichaelIndex n → K := fun k => if y k ^ 3 = 1 then y k else y k * z
  have hx : ∀ k, θ (x k) = L k := fun k => by
    simp only [x]
    split_ifs
    · exact hy k
    · rw [map_mul, hy k, hθz, mul_one]
  have hx3 : ∀ k, x k ^ 3 = 1 := fun k => by
    simp only [x]
    split_ifs with h
    · exact h
    · have h3 : y k ^ 3 = z := by
        rcases hker (y k ^ 3) (by rw [map_pow, hy k, hL3]) with h' | h'
        · exact absurd h' h
        · exact h'
      have hzc : Commute (y k) z := Subgroup.mem_center_iff.1 hz (y k)
      calc (y k * z) ^ 3 = y k ^ 3 * z ^ 3 := hzc.mul_pow 3
        _ = z * (z * z * z) := by rw [h3, pow_succ, pow_two]
        _ = 1 := by rw [hzz, one_mul, hzz]
  have hxx : ∀ k l, k ≠ l → (x k * x l) ^ 2 = 1 := fun k l hkl => by
    rw [pow_two]
    exact hcon k l hkl _ (by rw [map_mul, hx, hx])
  obtain ⟨φ, hφ⟩ := exists_hom_carmichaelCycle hn x hx3 hxx
  have hdec : ∀ a : K, ∃ h ∈ φ.range, h⁻¹ * a ∈ Subgroup.center K := by
    intro a
    have hle : Subgroup.closure (Set.range L) ≤ φ.range.map θ := by
      rw [Subgroup.closure_le]
      rintro _ ⟨k, rfl⟩
      exact ⟨x k, ⟨carmichaelCycle k, hφ k⟩, hx k⟩
    rw [hgen] at hle
    obtain ⟨h, hh, hha⟩ := hle (Subgroup.mem_top (θ a))
    exact ⟨h, hh, hkc _ (by rw [map_mul, map_inv, hha, inv_mul_cancel])⟩
  have htop : φ.range = ⊤ := by
    rw [eq_top_iff, ← hperf, commutator_def, Subgroup.commutator_le]
    intro a _ b _
    obtain ⟨h, hh, hha⟩ := hdec a
    obtain ⟨h', hh', hhb⟩ := hdec b
    have e : ⁅a, b⁆ = ⁅h, h'⁆ := by
      rw [show a = h * (h⁻¹ * a) by group, show b = h' * (h'⁻¹ * b) by group,
        commutatorElement_mul_central_left hha, commutatorElement_mul_central_right hhb]
    rw [e, commutatorElement_def]
    exact φ.range.mul_mem (φ.range.mul_mem (φ.range.mul_mem hh hh') (φ.range.inv_mem hh))
      (φ.range.inv_mem hh')
  have hle : Nat.card K ≤ Nat.card (alternatingGroup (Fin n)) := by
    rw [← Subgroup.card_top (G := K), ← htop]
    exact Nat.card_le_card_of_surjective _ φ.rangeRestrict_surjective
  omega

end Carmichael

end CFSG.Quasithin.C35Pf
