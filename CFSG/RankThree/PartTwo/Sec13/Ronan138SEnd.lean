module

public import CFSG.RankThree.PartTwo.Sec13.Ronan138SP
import CFSG.RankThree.PartTwo.Sec13.Item138ProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec13.Ronan138S

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec13.Item138Proof
open scoped commutatorElement

section Facts

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_zpowers_of_conj_mem {c s : G} (h : s * c * s⁻¹ ∈ Subgroup.zpowers c) :
    s ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
  apply mem_normalizer_of_map_le
  rw [MonoidHom.map_zpowers]
  exact Subgroup.zpowers_le.mpr h

theorem false_of_conj {c d u : G} (hinf : Subgroup.zpowers c ⊓ Subgroup.zpowers d = ⊥)
    (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1) (huc : u ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    (hud : u * d * u⁻¹ = d⁻¹) {α β : ℕ} (hβ : ¬ 3 ∣ β)
    (hw : u * (c ^ α * d ^ β) * u⁻¹ = c ^ α * d ^ β) : False := by
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp
    ((Subgroup.mem_normalizer_iff.mp huc c).mp (Subgroup.mem_zpowers c))
  have e1 : u * (c ^ α * d ^ β) * u⁻¹ = (c ^ m) ^ α * (d⁻¹) ^ β := by
    rw [hm, ← hud, conj_pow, conj_pow]
    group
  rw [e1] at hw
  have e2 : (c ^ α)⁻¹ * (c ^ m) ^ α = d ^ β * d ^ β := by
    have : (c ^ m) ^ α = c ^ α * d ^ β * ((d⁻¹) ^ β)⁻¹ := by
      rw [← hw]
      group
    rw [this, inv_pow, inv_inv]
    group
  have hmem : d ^ β * d ^ β ∈ Subgroup.zpowers c ⊓ Subgroup.zpowers d := by
    refine Subgroup.mem_inf.mpr ⟨?_, mul_mem (pow_mem (Subgroup.mem_zpowers d) β)
      (pow_mem (Subgroup.mem_zpowers d) β)⟩
    rw [← e2]
    exact mul_mem (inv_mem (pow_mem (Subgroup.mem_zpowers c) α))
      (pow_mem (zpow_mem (Subgroup.mem_zpowers c) m) α)
  rw [hinf, Subgroup.mem_bot, ← pow_add] at hmem
  have hord : orderOf d = 3 := orderOf_eq_prime hd3 hd1
  have := orderOf_dvd_of_pow_eq_one hmem
  rw [hord] at this
  omega

end Facts

section Main

variable {G : Type} [Group G] [Finite G] {E F : Subgroup G} {x y : G}

theorem mem_normalizer_left_of_conj (hframe : HeisFrame (E ⊓ F) x y) (hxE : x ∈ E)
    (hE27 : Nat.card E = 27) (h9 : Nat.card (E ⊓ F : Subgroup G) = 9) {s : G}
    (hsZ : ∀ z ∈ E ⊓ F, s * z * s⁻¹ ∈ E ⊓ F) (hsx : s * x * s⁻¹ ∈ E) :
    s ∈ Subgroup.normalizer (E : Set G) := by
  apply mem_normalizer_of_map_le
  rintro _ ⟨p, hp, rfl⟩
  obtain ⟨i, z, hz, rfl⟩ := isNF_of_mem_left hframe hxE hE27 h9 hp
  change s * (x ^ i * y ^ 0 * z) * s⁻¹ ∈ E
  rw [pow_zero, mul_one, show s * (x ^ i * z) * s⁻¹ = (s * x * s⁻¹) ^ i * (s * z * s⁻¹) by
    rw [conj_pow]; group]
  exact mul_mem (pow_mem hsx i) (Subgroup.mem_inf.mp (hsZ z hz)).1

theorem mem_normalizer_right_of_conj (hframe : HeisFrame (E ⊓ F) x y) (hyF : y ∈ F)
    (hF27 : Nat.card F = 27) (h9 : Nat.card (E ⊓ F : Subgroup G) = 9) {s : G}
    (hsZ : ∀ z ∈ E ⊓ F, s * z * s⁻¹ ∈ E ⊓ F) (hsy : s * y * s⁻¹ ∈ F) :
    s ∈ Subgroup.normalizer (F : Set G) := by
  apply mem_normalizer_of_map_le
  rintro _ ⟨p, hp, rfl⟩
  obtain ⟨j, z, hz, rfl⟩ := isNF_of_mem_right hframe hyF hF27 h9 hp
  change s * (x ^ 0 * y ^ j * z) * s⁻¹ ∈ F
  rw [pow_zero, one_mul, show s * (y ^ j * z) * s⁻¹ = (s * y * s⁻¹) ^ j * (s * z * s⁻¹) by
    rw [conj_pow]; group]
  exact mul_mem (pow_mem hsy j) (Subgroup.mem_inf.mp (hsZ z hz)).2

theorem conj_mem_right_of_conj (hframe : HeisFrame (E ⊓ F) x y) (hxE : x ∈ E)
    (hE27 : Nat.card E = 27) (h9 : Nat.card (E ⊓ F : Subgroup G) = 9) {s : G}
    (hsZ : ∀ z ∈ E ⊓ F, s * z * s⁻¹ ∈ E ⊓ F) (hsx : s * x * s⁻¹ ∈ F) {p : G} (hp : p ∈ E) :
    s * p * s⁻¹ ∈ F := by
  obtain ⟨i, z, hz, rfl⟩ := isNF_of_mem_left hframe hxE hE27 h9 hp
  rw [pow_zero, mul_one, show s * (x ^ i * z) * s⁻¹ = (s * x * s⁻¹) ^ i * (s * z * s⁻¹) by
    rw [conj_pow]; group]
  exact mul_mem (pow_mem hsx i) (Subgroup.mem_inf.mp (hsZ z hz)).2

theorem coord_of_sq (hframe : HeisFrame (E ⊓ F) x y) (hd1 : ⁅x, y⁆ ≠ 1) (hxE : x ∈ E)
    (hyF : y ∈ F) (hE27 : Nat.card E = 27) (hF27 : Nat.card F = 27)
    (h9 : Nat.card (E ⊓ F : Subgroup G) = 9) (hFN : F ≤ Subgroup.normalizer (E : Set G))
    (hEab : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hFab : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a)
    {s : G} (hsP : s ∈ Subgroup.normalizer ((E ⊔ F : Subgroup G) : Set G))
    (hs2 : s * (s * y * s⁻¹) * s⁻¹ ∈ F) :
    ∀ a b a' b' : ℕ, IsNF (E ⊓ F) x y (s * x * s⁻¹) a b →
      IsNF (E ⊓ F) x y (s * y * s⁻¹) a' b' → (a' : ZMod 3) * (a + b') = 0 := by
  intro a b a' b' hab hab'
  have hsZ := conj_mem_inf_of_mem_normalizer hframe hd1 hxE hyF hE27 hF27 h9 hFN hEab hFab hsP
  have himg := IsNF.conj hframe hsZ hab hab' hab'
  have h1 := (mem_right_iff hframe hyF hF27 h9 himg).mp hs2
  push_cast at h1
  linear_combination h1

theorem exists_mem_normalizer_of_frame (hframe : HeisFrame (E ⊓ F) x y) (hd1 : ⁅x, y⁆ ≠ 1)
    (hxE : x ∈ E) (hyF : y ∈ F) (hE27 : Nat.card E = 27) (hF27 : Nat.card F = 27)
    (h9 : Nat.card (E ⊓ F : Subgroup G) = 9) (hFN : F ≤ Subgroup.normalizer (E : Set G))
    (hEab : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hFab : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a)
    {c : G} (hcZ : c ∈ E ⊓ F) (hcd : Subgroup.zpowers c ⊓ Subgroup.zpowers ⁅x, y⁆ = ⊥)
    (hZgen : ∀ z ∈ E ⊓ F, ∃ α β : ℕ, z = c ^ α * ⁅x, y⁆ ^ β)
    {s t : G} (hsP : s ∈ Subgroup.normalizer ((E ⊔ F : Subgroup G) : Set G))
    (hsH : s ∉ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    (hsE : s ∉ Subgroup.normalizer (E : Set G)) (hsd : s * ⁅x, y⁆ * s⁻¹ = ⁅x, y⁆⁻¹)
    (hσ : ∀ a b a' b' : ℕ, IsNF (E ⊓ F) x y (s * x * s⁻¹) a b →
      IsNF (E ⊓ F) x y (s * y * s⁻¹) a' b' → (a' : ZMod 3) * (a + b') = 0)
    (htE : t ∈ Subgroup.normalizer (E : Set G)) (htc : t * c = c * t)
    (htd : t * ⁅x, y⁆ * t⁻¹ = ⁅x, y⁆⁻¹) :
    ∃ s' ∈ Subgroup.normalizer (F : Set G),
      s' ∉ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
  set d := ⁅x, y⁆ with hd
  have hsZ := conj_mem_inf_of_mem_normalizer hframe hd1 hxE hyF hE27 hF27 h9 hFN hEab hFab hsP
  obtain ⟨a, b, hab⟩ := isNF_of_mem_sup hframe hxE hyF hE27 hF27 h9 hFN
    ((Subgroup.mem_normalizer_iff.mp hsP x).mp (Subgroup.mem_sup_left hxE))
  obtain ⟨a', b', hab'⟩ := isNF_of_mem_sup hframe hxE hyF hE27 hF27 h9 hFN
    ((Subgroup.mem_normalizer_iff.mp hsP y).mp (Subgroup.mem_sup_right hyF))
  have hdet : ((a * b' + 2 * a' * b : ℕ) : ZMod 3) = 2 := by
    have h1 := IsNF.commutator hframe hab hab'
    have h2 : ⁅s * x * s⁻¹, s * y * s⁻¹⁆ = s * d * s⁻¹ := by
      rw [hd, commutatorElement_def, commutatorElement_def]
      group
    rw [h2, hsd, ← hd] at h1
    have hd3 : d ^ 3 = 1 := hframe.comm_pow_three
    have hord : orderOf d = 3 := hframe.orderOf_comm hd1
    have h3 : d ^ (a * b' + 2 * a' * b) = d ^ 2 := by
      rw [← h1, eq_comm, eq_inv_iff_mul_eq_one, ← pow_succ, hd3]
    rw [pow_eq_pow_iff_modEq, hord] at h3
    have := (ZMod.natCast_eq_natCast_iff _ _ 3).mpr h3
    simpa using this
  have hb : (b : ZMod 3) ≠ 0 := by
    intro hb0
    apply hsE
    exact mem_normalizer_left_of_conj hframe hxE hE27 h9 hsZ
      ((mem_left_iff hframe hxE hE27 h9 hab).mpr hb0)
  have hcase := zmod3_of_sq a b a' b' (by exact_mod_cast hdet) hb
    (by exact_mod_cast hσ a b a' b' hab hab')
  rcases hcase with ha' | ha
  ·
    exact ⟨s, mem_normalizer_right_of_conj hframe hyF hF27 h9 hsZ
      ((mem_right_iff hframe hyF hF27 h9 hab').mpr ha'), hsH⟩
  ·
    have hsxF : s * x * s⁻¹ ∈ F := (mem_right_iff hframe hyF hF27 h9 hab).mpr ha
    have hsEF : ∀ p ∈ E, s * p * s⁻¹ ∈ F := fun p hp =>
      conj_mem_right_of_conj hframe hxE hE27 h9 hsZ hsxF hp
    have hmapEF : E.map (MulAut.conj s).toMonoidHom = F := by
      refine Subgroup.eq_of_le_of_card_ge ?_ (by
        rw [Subgroup.card_map_of_injective (MulAut.conj s).injective, hE27, hF27])
      rintro _ ⟨p, hp, rfl⟩
      exact hsEF p hp
    have hsFE : ∀ f ∈ F, s⁻¹ * f * s ∈ E := by
      intro f hf
      rw [← hmapEF] at hf
      obtain ⟨p, hp, rfl⟩ := hf
      change s⁻¹ * (s * p * s⁻¹) * s ∈ E
      rw [show s⁻¹ * (s * p * s⁻¹) * s = p by group]
      exact hp
    refine ⟨s * t * s⁻¹, ?_, ?_⟩
    · apply mem_normalizer_of_map_le
      rintro _ ⟨f, hf, rfl⟩
      change s * t * s⁻¹ * f * (s * t * s⁻¹)⁻¹ ∈ F
      have h1 := (Subgroup.mem_normalizer_iff.mp htE _).mp (hsFE f hf)
      have h2 := hsEF _ h1
      rw [show s * t * s⁻¹ * f * (s * t * s⁻¹)⁻¹ = s * (t * (s⁻¹ * f * s) * t⁻¹) * s⁻¹ by group]
      exact h2
    · intro hu
      have hd3 : d ^ 3 = 1 := hframe.comm_pow_three
      obtain ⟨α, β, hw⟩ := hZgen _ (hsZ c hcZ)
      have hβ : ¬ 3 ∣ β := by
        rintro ⟨m, rfl⟩
        apply hsH
        apply mem_normalizer_zpowers_of_conj_mem
        rw [hw, pow_mul, hd3, one_pow, mul_one]
        exact pow_mem (Subgroup.mem_zpowers c) α
      have hsd' : s⁻¹ * d * s = d⁻¹ := by
        calc s⁻¹ * d * s = (s⁻¹ * d⁻¹ * s)⁻¹ := by group
          _ = (s⁻¹ * (s * d * s⁻¹) * s)⁻¹ := by rw [hsd]
          _ = d⁻¹ := by group
      have hud : s * t * s⁻¹ * d * (s * t * s⁻¹)⁻¹ = d⁻¹ := by
        calc s * t * s⁻¹ * d * (s * t * s⁻¹)⁻¹ = s * (t * (s⁻¹ * d * s) * t⁻¹) * s⁻¹ := by group
          _ = s * (t * d * t⁻¹)⁻¹ * s⁻¹ := by rw [hsd']; group
          _ = s * d * s⁻¹ := by rw [htd]; group
          _ = d⁻¹ := hsd
      have huw : s * t * s⁻¹ * (c ^ α * d ^ β) * (s * t * s⁻¹)⁻¹ = c ^ α * d ^ β := by
        rw [← hw]
        calc s * t * s⁻¹ * (s * c * s⁻¹) * (s * t * s⁻¹)⁻¹ = s * (t * c * t⁻¹) * s⁻¹ := by group
          _ = s * c * s⁻¹ := by rw [htc, mul_inv_cancel_right]
      exact false_of_conj hcd hd3 hd1 hu hud hβ huw

end Main

end CFSG.RankThree.PartTwo.Sec13.Ronan138S
