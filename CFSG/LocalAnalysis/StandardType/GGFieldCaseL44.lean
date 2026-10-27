module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseDefs
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly
open scoped Pointwise

section General

variable {G : Type*} [Group G]

theorem mul_comm_of_isElemAbelian {p : ℕ} {E : Subgroup G} (h : IsElemAbelian p E) {a b : G}
    (ha : a ∈ E) (hb : b ∈ E) : a * b = b * a := CFSG.Open.IsElemAbelian.comm h ha hb

theorem pow_eq_pow_mod_of_pow_eq_one {x : G} {p : ℕ} (hxp : x ^ p = 1) (m : ℕ) :
    x ^ m = x ^ (m % p) := by
  conv_lhs => rw [← Nat.div_add_mod m p, pow_add, pow_mul, hxp, one_pow, one_mul]

theorem exists_mem_mul_pow_of_mem_sup [Finite G] {B₁ : Subgroup G} {x : G}
    (hx : ∀ b ∈ B₁, x * b = b * x) {c : G} (hc : c ∈ B₁ ⊔ Subgroup.zpowers x) :
    ∃ b ∈ B₁, ∃ j : ℕ, c = b * x ^ j := by
  have hxN : Subgroup.zpowers x ≤ Subgroup.normalizer (B₁ : Set G) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun b hb => (hx b hb).symm)
  have hc' : c ∈ ((B₁ : Set G) * (Subgroup.zpowers x : Set G)) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left B₁ _ hxN]
    exact hc
  obtain ⟨b, hb, z, hz, rfl⟩ := hc'
  obtain ⟨j, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hz)
  exact ⟨b, hb, j, rfl⟩

theorem conj_mul_inv_mem_of_pow_centralizes [Finite G] {p : ℕ} [Fact p.Prime]
    {V B₁ : Subgroup G} {x g : G} (hV : IsElemAbelian p V) (hB₁V : B₁ ≤ V) (hxV : x ∈ V)
    (hVeq : V = B₁ ⊔ Subgroup.zpowers x) (hgV : g ∈ Subgroup.normalizer (V : Set G))
    (hgB₁ : ∀ b ∈ B₁, g * b = b * g) {k : ℕ} (hgk : g ^ p ^ k * x = x * g ^ p ^ k) :
    g * x * g⁻¹ * x⁻¹ ∈ B₁ := by
  have hxB : ∀ b ∈ B₁, x * b = b * x := fun b hb => mul_comm_of_isElemAbelian hV hxV (hB₁V hb)
  have hcV : g * x * g⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hgV x).mp hxV
  obtain ⟨b, hb, j, hc⟩ := exists_mem_mul_pow_of_mem_sup hxB (hVeq ▸ hcV)
  have hiter : ∀ n : ℕ, ∃ b' ∈ B₁, g ^ n * x * (g ^ n)⁻¹ = b' * x ^ (j ^ n) := by
    intro n
    induction n with
    | zero => exact ⟨1, B₁.one_mem, by simp⟩
    | succ n ih =>
      obtain ⟨b', hb', h'⟩ := ih
      refine ⟨b' * b ^ (j ^ n), B₁.mul_mem hb' (B₁.pow_mem hb _), ?_⟩
      have hcomm : Commute b (x ^ j) :=
        mul_comm_of_isElemAbelian hV (hB₁V hb) (V.pow_mem hxV j)
      have hgb' : g * b' * g⁻¹ = b' := by rw [hgB₁ b' hb', mul_inv_cancel_right]
      calc g ^ (n + 1) * x * (g ^ (n + 1))⁻¹ = g * (g ^ n * x * (g ^ n)⁻¹) * g⁻¹ := by
              rw [pow_succ', mul_inv_rev]; simp only [mul_assoc]
        _ = (g * b' * g⁻¹) * (g * x * g⁻¹) ^ (j ^ n) := by
              rw [h', conj_pow]; simp only [mul_assoc, inv_mul_cancel_left]
        _ = b' * b ^ (j ^ n) * x ^ (j ^ (n + 1)) := by
              rw [hgb', hc, hcomm.mul_pow, ← pow_mul, pow_succ', mul_assoc]
  obtain ⟨b', hb', h'⟩ := hiter (p ^ k)
  have hxp : x ^ p = 1 := hV.2 x hxV
  have hjmod : x ^ (j ^ p ^ k) = x ^ j := by
    have hz : ((j ^ p ^ k : ℕ) : ZMod p) = (j : ZMod p) := by
      push_cast
      exact ZMod.pow_card_pow (p := p) _
    rw [pow_eq_pow_mod_of_pow_eq_one hxp, pow_eq_pow_mod_of_pow_eq_one hxp j,
      (ZMod.natCast_eq_natCast_iff' _ _ _).mp hz]
  have hx' : x = b' * x ^ j := by
    rw [← hjmod, ← h', hgk, mul_inv_cancel_right]
  have hcx : g * x * g⁻¹ * x⁻¹ = b * b'⁻¹ := by
    calc g * x * g⁻¹ * x⁻¹ = (b * x ^ j) * (b' * x ^ j)⁻¹ := by rw [← hc, ← hx']
      _ = b * b'⁻¹ := by group
  rw [hcx]
  exact B₁.mul_mem hb (B₁.inv_mem hb')

end General

section L44

variable {G : Type} [Group G] [Finite G]

theorem ggL44i_of_ggL43 {p : ℕ} [Fact p.Prime] {Bs X : Subgroup G} {x : G}
    (hBs : IsElemAbelian p Bs) (hxBs : x ∈ Bs) (hXN : X ≤ Subgroup.normalizer (Bs : Set G))
    (hXp : ∀ g ∈ X, ∃ k : ℕ, g ^ p ^ k ∈ Subgroup.centralizer (Bs : Set G))
    (h43 : GGL43 Bs x X) : GGL44i p Bs x X := by
  set B₁ : Subgroup G := Bs ⊓ Subgroup.centralizer (X : Set G) with hB₁def
  have hB₁V : B₁ ≤ Bs := inf_le_left
  have hgB₁ : ∀ g ∈ X, ∀ b ∈ B₁, g * b = b * g := fun g hg b hb =>
    Subgroup.mem_centralizer_iff.mp hb.2 g hg
  have hxB : ∀ b ∈ B₁, x * b = b * x := fun b hb => mul_comm_of_isElemAbelian hBs hxBs (hB₁V hb)
  have key : ∀ g ∈ X, g * x * g⁻¹ * x⁻¹ ∈ B₁ := by
    intro g hg
    obtain ⟨k, hk⟩ := hXp g hg
    exact conj_mul_inv_mem_of_pow_centralizes hBs hB₁V hxBs h43.2 (hXN hg) (hgB₁ g hg)
      (Subgroup.mem_centralizer_iff.mp hk x hxBs).symm
  have ha : ∀ g ∈ X, g * x = x * g → g ∈ Subgroup.centralizer (Bs : Set G) := by
    intro g hg hgx
    have hle : Bs ≤ Subgroup.centralizer ({g} : Set G) := by
      rw [h43.2]
      refine sup_le (fun b hb => ?_) ((Subgroup.zpowers_le).mpr ?_)
      · rw [Subgroup.mem_centralizer_iff]
        rintro h rfl
        exact hgB₁ h hg b hb
      · rw [Subgroup.mem_centralizer_iff]
        rintro h rfl
        exact hgx
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact ((Subgroup.mem_centralizer_iff.mp (hle hh)) g rfl).symm
  refine ⟨ha, ?_, ?_⟩
  ·
    intro g hg b hb
    obtain ⟨b₁, hb₁, i, rfl⟩ := exists_mem_mul_pow_of_mem_sup hxB (h43.2 ▸ hb)
    set c₀ := g * x * g⁻¹ * x⁻¹ with hc₀def
    have hc₀ : c₀ ∈ B₁ := key g hg
    have e1 : g * x * g⁻¹ = c₀ * x := by rw [hc₀def, inv_mul_cancel_right]
    have hcx : Commute c₀ x := (hxB c₀ hc₀).symm
    have hb₁c : Commute b₁ (c₀ ^ i) := mul_comm_of_isElemAbelian hBs (hB₁V hb₁)
      (Bs.pow_mem (hB₁V hc₀) i)
    have e2 : g * (b₁ * x ^ i) * g⁻¹ = b₁ * (c₀ ^ i * x ^ i) := by
      calc g * (b₁ * x ^ i) * g⁻¹ = (g * b₁) * (x ^ i * g⁻¹) := by simp only [mul_assoc]
        _ = b₁ * (g * x ^ i * g⁻¹) := by rw [hgB₁ g hg b₁ hb₁]; simp only [mul_assoc]
        _ = b₁ * (c₀ ^ i * x ^ i) := by rw [← conj_pow, e1, hcx.mul_pow]
    rw [e2]
    have e3 : b₁ * (c₀ ^ i * x ^ i) * (b₁ * x ^ i)⁻¹ = c₀ ^ i := by
      calc b₁ * (c₀ ^ i * x ^ i) * (b₁ * x ^ i)⁻¹ = b₁ * c₀ ^ i * b₁⁻¹ := by group
        _ = c₀ ^ i := by rw [hb₁c.eq, mul_inv_cancel_right]
    rw [e3]
    exact B₁.pow_mem hc₀ i
  ·
    let θ : X →* G := MonoidHom.mk' (fun g => (g : G) * x * (g : G)⁻¹ * x⁻¹) (by
      intro g h
      have ht := key h h.2
      have hu := key g g.2
      have hgt := hgB₁ g g.2 _ ht
      have hut : Commute ((g : G) * x * (g : G)⁻¹ * x⁻¹) ((h : G) * x * (h : G)⁻¹ * x⁻¹) :=
        mul_comm_of_isElemAbelian hBs (hB₁V hu) (hB₁V ht)
      simp only [Subgroup.coe_mul, mul_inv_rev]
      calc (g : G) * h * x * ((h : G)⁻¹ * (g : G)⁻¹) * x⁻¹
          = (g : G) * ((h : G) * x * (h : G)⁻¹) * (g : G)⁻¹ * x⁻¹ := by simp only [mul_assoc]
        _ = ((g : G) * ((h : G) * x * (h : G)⁻¹ * x⁻¹)) * x * (g : G)⁻¹ * x⁻¹ := by group
        _ = ((h : G) * x * (h : G)⁻¹ * x⁻¹) * ((g : G) * x * (g : G)⁻¹ * x⁻¹) := by
            rw [hgt]; simp only [mul_assoc]
        _ = ((g : G) * x * (g : G)⁻¹ * x⁻¹) * ((h : G) * x * (h : G)⁻¹ * x⁻¹) := hut.eq.symm)
    have hθ : ∀ g : X, θ g = (g : G) * x * (g : G)⁻¹ * x⁻¹ := fun _ => rfl
    have hker : ∀ g : X, θ g = 1 → (g : G) ∈ Subgroup.centralizer (Bs : Set G) := by
      intro g hg
      refine ha g g.2 ?_
      rw [hθ] at hg
      have := congrArg (· * x) hg
      simp only [inv_mul_cancel_right, one_mul] at this
      calc (g : G) * x = (g : G) * x * (g : G)⁻¹ * (g : G) := by group
        _ = x * g := by rw [this]
    refine ⟨fun g hg h hh => ?_, fun g hg => ?_⟩
    · have h1 := hker ((⟨g, hg⟩ : X) * ⟨h, hh⟩ * (⟨g, hg⟩ : X)⁻¹ * (⟨h, hh⟩ : X)⁻¹) (by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← commutatorElement_def,
          commutatorElement_eq_one_iff_mul_comm]
        exact mul_comm_of_isElemAbelian hBs (hB₁V (key g hg)) (hB₁V (key h hh)))
      simpa using h1
    · have h1 := hker (⟨g, hg⟩ ^ p) (by
        rw [map_pow, hθ]
        exact hBs.2 _ (hB₁V (key g hg)))
      simpa using h1

end L44

end CFSG.StandardType

end
