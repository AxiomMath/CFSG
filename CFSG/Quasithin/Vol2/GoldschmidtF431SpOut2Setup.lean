module

public import CFSG.Quasithin.Vol2.GoldschmidtF431SpOut2Frob
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Basic
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.Quasithin.H13.F431

open Matrix CFSG.ComponentClassification.UnbalancedCatalog.SpChain
  CFSG.QuasithinUnique.Setup.X7b CFSG.RankThree.PartOne.KCRootAxis CFSG.Quasithin.H13.F431.SpModel
  CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin

universe u

namespace SpOut2

section Setup

variable {F : Type} [Field F] [Finite F] [CharP F 2] {H : Type u} [Group H]

structure OutProps (Φ : antiSp F →* H) (ψ : H) (k₀ : ℕ) : Prop where
  inj : Function.Injective Φ
  act : ∀ x, ψ * Φ x * ψ⁻¹ = Φ ((frobAut F ^ k₀) x)
  cen : ∀ h : H, (∀ x, h * Φ x * h⁻¹ = Φ x) → h = 1
  gen : ∀ h : H, ∃ (g : antiSp F) (s : ℕ), h = Φ g * ψ ^ s

variable {Φ : antiSp F →* H} {ψ : H} {k₀ : ℕ}

theorem OutProps.act_pow (P : OutProps Φ ψ k₀) (s : ℕ) (x : antiSp F) :
    ψ ^ s * Φ x * (ψ ^ s)⁻¹ = Φ ((frobAut F ^ (k₀ * s)) x) := by
  induction s generalizing x with
  | zero => simp
  | succ s ih =>
    have e : ψ ^ (s + 1) * Φ x * (ψ ^ (s + 1))⁻¹ = ψ ^ s * (ψ * Φ x * ψ⁻¹) * (ψ ^ s)⁻¹ := by
      rw [pow_succ, _root_.mul_inv_rev]
      group
    rw [e, P.act, ih, mul_add, mul_one, pow_add, MulAut.mul_apply]

theorem OutProps.range_normal (P : OutProps Φ ψ k₀) : Φ.range.Normal := by
  refine ⟨fun n hn h => ?_⟩
  obtain ⟨x, rfl⟩ := hn
  obtain ⟨g, s, rfl⟩ := P.gen h
  refine ⟨g * (frobAut F ^ (k₀ * s)) x * g⁻¹, ?_⟩
  have e : Φ g * ψ ^ s * Φ x * (Φ g * ψ ^ s)⁻¹ = Φ g * (ψ ^ s * Φ x * (ψ ^ s)⁻¹) * (Φ g)⁻¹ := by
    rw [_root_.mul_inv_rev]
    group
  rw [e, P.act_pow, map_mul, map_mul, map_inv]

theorem OutProps.pow_eq_one_iff (P : OutProps Φ ψ k₀) (s : ℕ) :
    ψ ^ s = 1 ↔ frobAut F ^ (k₀ * s) = 1 := by
  constructor
  · intro h
    refine MulEquiv.ext fun x => ?_
    apply P.inj
    rw [← P.act_pow s x, h]
    simp
  · intro h
    apply P.cen
    intro x
    rw [P.act_pow, h]
    simp

theorem OutProps.eq_one_of_mem_range {n : ℕ} (P : OutProps Φ ψ k₀) (hn : 1 ≤ n)
    (hF : Nat.card F = 2 ^ n) {s : ℕ} (h : ψ ^ s ∈ Φ.range) : ψ ^ s = 1 := by
  obtain ⟨g, hg⟩ := h
  have hc : MulAut.conj g = frobAut F ^ (k₀ * s) := by
    refine MulEquiv.ext fun x => ?_
    apply P.inj
    rw [← P.act_pow s x, ← hg]
    simp [MulAut.conj_apply]
  have hg1 : g = 1 := conj_eq_frobAut_pow hn hF hc
  rw [← hg, hg1, map_one]

omit [Finite F] [CharP F 2] in
theorem OutProps.mem_zpowers_iff [Finite H] (ψ : H) (x : H) :
    x ∈ Subgroup.zpowers ψ ↔ ∃ s : ℕ, ψ ^ s = x := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf]
  simp [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨s, -, hs⟩
    exact ⟨s, hs⟩
  · rintro ⟨s, hs⟩
    exact ⟨s % orderOf ψ, Nat.mod_lt _ (orderOf_pos ψ), by rw [pow_mod_orderOf, hs]⟩

theorem OutProps.inf_zpowers_eq_bot [Finite H] {n : ℕ} (P : OutProps Φ ψ k₀) (hn : 1 ≤ n)
    (hF : Nat.card F = 2 ^ n) : Φ.range ⊓ Subgroup.zpowers ψ = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxr, hxz⟩
  obtain ⟨s, rfl⟩ := (OutProps.mem_zpowers_iff ψ x).mp hxz
  rw [Subgroup.mem_bot]
  exact P.eq_one_of_mem_range hn hF hxr

theorem OutProps.sup_eq_top (P : OutProps Φ ψ k₀) : Subgroup.zpowers ψ ⊔ Φ.range = ⊤ := by
  rw [eq_top_iff]
  intro h _
  obtain ⟨g, s, rfl⟩ := P.gen h
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ⟨g, rfl⟩)
    (Subgroup.mem_sup_left (Subgroup.pow_mem _ (Subgroup.mem_zpowers ψ) s))

theorem OutProps.card_eq [Finite H] {n : ℕ} (P : OutProps Φ ψ k₀) (hn : 1 ≤ n)
    (hF : Nat.card F = 2 ^ n) : Nat.card H = Nat.card (antiSp F) * orderOf ψ := by
  have hnorm := P.range_normal
  have h1 := CFSG.QuasithinUnique.Lin2.card_sup_mul_card_inf
    (A := Subgroup.zpowers ψ) (B := Φ.range) Subgroup.le_normalizer_of_normal
  rw [inf_comm, P.inf_zpowers_eq_bot hn hF, Subgroup.card_bot, mul_one, P.sup_eq_top,
    Subgroup.card_top, Nat.card_zpowers] at h1
  rw [h1, mul_comm]
  congr 1
  exact (Nat.card_congr (MonoidHom.ofInjective P.inj).toEquiv).symm

end Setup

end SpOut2

end CFSG.Quasithin.H13.F431
