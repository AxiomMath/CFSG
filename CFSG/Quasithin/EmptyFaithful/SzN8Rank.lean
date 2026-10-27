module

public import CFSG.Quasithin.EmptyFaithful.SzN8Basic
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.Quasithin

open CFSG.Open
open scoped Pointwise

section Rank

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem szN8_le_normalizer_of_commute {X N : Subgroup G} (hc : ∀ x ∈ X, ∀ y ∈ N, x * y = y * x) :
    X ≤ Subgroup.normalizer (N : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have := hc x hx h hh
    have e : x * h * x⁻¹ = h := by rw [this]; group
    rwa [e]
  · intro hh
    have h1 := hc x⁻¹ (X.inv_mem hx) _ hh
    have e : x⁻¹ * (x * h * x⁻¹) * x = h := by group
    have e2 : x⁻¹ * (x * h * x⁻¹) = (x * h * x⁻¹) * x⁻¹ := h1
    rw [e2] at e
    have e3 : (x * h * x⁻¹) * x⁻¹ * x = x * h * x⁻¹ := by group
    rw [e3] at e
    rwa [← e]

theorem szN8_card_le_three_of_pRank {L E : Subgroup G} (hEL : E ≤ L) (hE3 : IsPGroup 3 E)
    (hEe : ∀ x ∈ E, x ^ 3 = 1) (hr : pRank 3 L = 1) : Nat.card E ≤ 3 := by
  classical
  by_contra hlt
  push Not at hlt
  have hp3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Nontrivial ↥E := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have hEg : IsPGroup 3 ↥E := hE3
  have := hEg.center_nontrivial
  obtain ⟨z, hz1⟩ := exists_ne (1 : ↥(Subgroup.center ↥E))
  have hzc : ∀ g : ↥E, g * (z : ↥E) = (z : ↥E) * g := fun g =>
    (Subgroup.mem_center_iff.mp z.2 g)
  have hz1' : (z : ↥E) ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hz3 : (z : ↥E) ^ 3 = 1 := Subtype.ext (hEe _ (z : ↥E).2)
  have hzord : orderOf (z : ↥E) = 3 := orderOf_eq_prime hz3 hz1'
  obtain ⟨x, hx⟩ : ∃ x : ↥E, x ∉ Subgroup.zpowers (z : ↥E) := by
    by_contra hall
    push Not at hall
    have : Subgroup.zpowers (z : ↥E) = ⊤ := eq_top_iff.mpr fun x _ => hall x
    have hc := Nat.card_zpowers (z : ↥E)
    rw [this, hzord, Subgroup.card_top] at hc
    omega
  have hx3 : x ^ 3 = 1 := Subtype.ext (hEe _ x.2)
  have hx1 : x ≠ 1 := fun h => hx (h ▸ Subgroup.one_mem _)
  have hxord : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  let x' : G := (x : G)
  let z' : G := ((z : ↥E) : G)
  have hxz : x' * z' = z' * x' := by
    have := hzc x
    exact congrArg (fun g : ↥E => (g : G)) this
  have hx'3 : x' ^ 3 = 1 := by simpa using congrArg (fun g : ↥E => (g : G)) hx3
  have hz'3 : z' ^ 3 = 1 := by simpa using congrArg (fun g : ↥E => (g : G)) hz3
  have hx'1 : x' ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hz'1 : z' ≠ 1 := fun h => hz1' (Subtype.ext h)
  have hx'ord : orderOf x' = 3 := orderOf_eq_prime hx'3 hx'1
  have hz'ord : orderOf z' = 3 := orderOf_eq_prime hz'3 hz'1
  let X : Subgroup G := Subgroup.zpowers x'
  let N : Subgroup G := Subgroup.zpowers z'
  have hXcard : Nat.card X = 3 := by rw [Nat.card_zpowers, hx'ord]
  have hNcard : Nat.card N = 3 := by rw [Nat.card_zpowers, hz'ord]
  have hcXN : ∀ a ∈ X, ∀ b ∈ N, a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact ((Commute.zpow_zpow ((hxz : Commute x' z')) i j)).eq
  have hXN : X ≤ Subgroup.normalizer (N : Set G) := szN8_le_normalizer_of_commute hcXN
  have hXNbot : X ⊓ N = ⊥ := by
    have hd : Nat.card ↥(X ⊓ N) ∣ 3 := by
      rw [← hXcard]
      exact Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h3
    · exact Subgroup.card_eq_one.mp h1
    · exfalso
      have heq : X ⊓ N = X := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hXcard, h3])
      have hxN : x' ∈ N := (heq.ge (Subgroup.mem_zpowers x')).2
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxN
      apply hx
      refine Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext ?_⟩
      simpa [z'] using hk
  have hcard := szN8_card_sup_mul_card_inf hXN
  rw [hXNbot, Subgroup.card_bot, mul_one, hXcard, hNcard] at hcard
  have hFE : X ⊔ N ≤ E := by
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]
      exact x.2
    · rw [Subgroup.zpowers_le]
      exact (z : ↥E).2
  have hFcomm : ∀ f ∈ X ⊔ N, ∀ g ∈ X ⊔ N, f * g = g * f := by
    intro f hf g hg
    have hset := Subgroup.coe_mul_of_left_le_normalizer_right X N hXN
    have hf' : f ∈ (X : Set G) * (N : Set G) := by rw [← hset]; exact hf
    have hg' : g ∈ (X : Set G) * (N : Set G) := by rw [← hset]; exact hg
    obtain ⟨a, ha, b, hb, rfl⟩ := hf'
    obtain ⟨c, hc, d, hd, rfl⟩ := hg'
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.mp hd
    have hcomm : Commute x' z' := (hxz : Commute x' z')
    have e1 : x' ^ i * z' ^ j * (x' ^ k * z' ^ l) = x' ^ (i + k) * z' ^ (j + l) := by
      calc x' ^ i * z' ^ j * (x' ^ k * z' ^ l) = x' ^ i * (z' ^ j * x' ^ k) * z' ^ l := by group
        _ = x' ^ i * (x' ^ k * z' ^ j) * z' ^ l := by rw [(Commute.zpow_zpow hcomm.symm j k).eq]
        _ = x' ^ (i + k) * z' ^ (j + l) := by rw [zpow_add, zpow_add]; group
    have e2 : x' ^ k * z' ^ l * (x' ^ i * z' ^ j) = x' ^ (k + i) * z' ^ (l + j) := by
      calc x' ^ k * z' ^ l * (x' ^ i * z' ^ j) = x' ^ k * (z' ^ l * x' ^ i) * z' ^ j := by group
        _ = x' ^ k * (x' ^ i * z' ^ l) * z' ^ j := by rw [(Commute.zpow_zpow hcomm.symm l i).eq]
        _ = x' ^ (k + i) * z' ^ (l + j) := by rw [zpow_add, zpow_add]; group
    rw [e1, e2, add_comm i k, add_comm j l]
  have hF : IsElemAbelian 3 (X ⊔ N) :=
    ⟨⟨⟨fun a b => Subtype.ext (hFcomm a a.2 b b.2)⟩⟩, fun f hf => hEe f (hFE hf)⟩
  have hF9 : Nat.card ↥(X ⊔ N) = 3 ^ 2 := by rw [hcard]; norm_num
  have hle := CFSG.SectionRank.le_pRank (by norm_num : 1 < 3) (hFE.trans hEL) hF hF9
  omega

end Rank

end CFSG.Quasithin
