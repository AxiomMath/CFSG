module

public import CFSG.Open.LocalVocabulary
public import CFSG.Open.StatedDefs
public import CFSG.Quasithin.Background.G6Natural
public import CFSG.LocalAnalysis.SectionRank.CentralLift
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.Open.Defs

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.SectionRank
open scoped Matrix

@[expose] def s15kVecStab {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    (m : ι → K) : Subgroup (Matrix.GeneralLinearGroup ι K) where
  carrier := {g | (g : Matrix ι ι K) *ᵥ m = m}
  mul_mem' {g h} hg hh := by
    change ((g * h : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K) *ᵥ m = m
    rw [Units.val_mul, ← Matrix.mulVec_mulVec]
    change (g : Matrix ι ι K) *ᵥ ((h : Matrix ι ι K) *ᵥ m) = m
    rw [hh, hg]
  one_mem' := by
    change ((1 : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K) *ᵥ m = m
    rw [Units.val_one, Matrix.one_mulVec]
  inv_mem' {g} hg := by
    change ((g⁻¹ : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K) *ᵥ m = m
    have h : (g : Matrix ι ι K) *ᵥ m = m := hg
    calc ((g⁻¹ : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K) *ᵥ m
        = ((g⁻¹ : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K) *ᵥ
            ((g : Matrix ι ι K) *ᵥ m) := by rw [h]
      _ = m := by
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Matrix.one_mulVec]

@[expose] def s15kPermStab (n : ℕ) (x : CFSG.Quasithin.G6.PermMod n) :
    Subgroup (Equiv.Perm (Fin n)) where
  carrier := {σ | CFSG.Quasithin.G6.permAct n σ x = x}
  mul_mem' {σ τ} hσ hτ := by
    change CFSG.Quasithin.G6.permAct n (σ * τ) x = x
    rw [map_mul]
    change CFSG.Quasithin.G6.permAct n σ (CFSG.Quasithin.G6.permAct n τ x) = x
    have hσ' : CFSG.Quasithin.G6.permAct n σ x = x := hσ
    have hτ' : CFSG.Quasithin.G6.permAct n τ x = x := hτ
    rw [hτ', hσ']
  one_mem' := by
    change CFSG.Quasithin.G6.permAct n 1 x = x
    rw [map_one]
    rfl
  inv_mem' {σ} hσ := by
    change CFSG.Quasithin.G6.permAct n σ⁻¹ x = x
    have hσ' : CFSG.Quasithin.G6.permAct n σ x = x := hσ
    rw [map_inv]
    change (CFSG.Quasithin.G6.permAct n σ)⁻¹ x = x
    rw [MulAut.inv_apply]
    exact (MulEquiv.symm_apply_eq _).2 hσ'.symm

section Planes

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def s15kPlane (Q : QuadraticForm (ZMod 2) V) (z : V) : Prop :=
  ∃ a b : V, Q a = 1 ∧ Q b = 1 ∧ QuadraticMap.polar Q a b = 1 ∧ QuadraticMap.polar Q z a = 0 ∧
    QuadraticMap.polar Q z b = 0

@[expose] def s15kPlanePair (Q : QuadraticForm (ZMod 2) V) (z : V) : Prop :=
  ∃ a₀ b₀ a₁ b₁ : V, Q a₀ = 1 ∧ Q b₀ = 1 ∧ QuadraticMap.polar Q a₀ b₀ = 1 ∧
    Q a₁ = 1 ∧ Q b₁ = 1 ∧ QuadraticMap.polar Q a₁ b₁ = 1 ∧
    QuadraticMap.polar Q a₀ a₁ = 0 ∧ QuadraticMap.polar Q a₀ b₁ = 0 ∧
    QuadraticMap.polar Q b₀ a₁ = 0 ∧ QuadraticMap.polar Q b₀ b₁ = 0 ∧
    QuadraticMap.polar Q z a₀ = 0 ∧ QuadraticMap.polar Q z b₀ = 0 ∧
    QuadraticMap.polar Q z a₁ = 0 ∧ QuadraticMap.polar Q z b₁ = 0

end Planes

section Gens

variable {G : Type*} [Group G] [Finite G]

theorem s15k_table_one_le_pRank {H : Subgroup G} {x : G} (hxH : x ∈ H) (hx : x ^ 3 = 1)
    (hx1 : x ≠ 1) : 1 ≤ pRank 3 H := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf x = 3 := orderOf_eq_prime hx hx1
  refine le_pRank (by norm_num) (E := Subgroup.zpowers x) ?_ ?_ ?_
  · rw [Subgroup.zpowers_le]
    exact hxH
  · refine ⟨inferInstance, ?_⟩
    rintro _ ⟨k, rfl⟩
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hx, one_zpow]
  · rw [Nat.card_zpowers, hord, pow_one]

theorem s15k_table_two_le_pRank {H : Subgroup G} {x y : G} (hxH : x ∈ H) (hyH : y ∈ H)
    (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) (hxy : Commute x y) (hx1 : x ≠ 1)
    (hy1 : ∀ n : ℕ, x ^ n ≠ y) : 2 ≤ pRank 3 H := by
  haveI hp : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set B₀ : Subgroup G := ⊥
  have h₀ : ∀ b : B₀, B₀.subtype b = 1 := fun b => Subgroup.mem_bot.1 b.2
  have hc₀ : ∀ a b : B₀, a * b = b * a := fun a b => Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.mem_bot.1 a.2, Subgroup.mem_bot.1 b.2])
  have hp₀ : ∀ a : B₀, a ^ 3 = 1 := fun a => Subtype.ext (by
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [Subgroup.mem_bot.1 a.2, one_pow])
  have hcard₀ : Nat.card B₀ = 3 ^ 0 := by rw [pow_zero]; exact Subgroup.card_bot
  obtain ⟨F₁, hF₁, hc₁, hp₁, hcard₁, hr₁⟩ := exists_extend hc₀ hp₀ hcard₀ B₀.subtype
    Subtype.val_injective (y := x) hx (by
      rintro ⟨b, hb⟩
      exact hx1 (hb ▸ h₀ b))
    (fun b => by rw [h₀ b]; exact Commute.one_left x)
  have hr₁' : ∀ a, ∃ n : ℕ, F₁ a = x ^ n := fun a => by
    obtain ⟨b, n, hb⟩ := hr₁ a
    exact ⟨n, by rw [hb, h₀ b, one_mul]⟩
  obtain ⟨F₂, hF₂, hc₂, hp₂, hcard₂, hr₂⟩ := exists_extend hc₁ hp₁ hcard₁ F₁ hF₁ (y := y) hy
    (by
      rintro ⟨a, ha⟩
      obtain ⟨n, hn⟩ := hr₁' a
      exact hy1 n (hn ▸ ha))
    (fun a => by
      obtain ⟨n, hn⟩ := hr₁' a
      rw [hn]
      exact hxy.pow_left n)
  refine le_pRank_of_injective hp.out.one_lt hc₂ hp₂ hcard₂ F₂ hF₂ ?_
  rintro _ ⟨a, rfl⟩
  obtain ⟨b, m, hb⟩ := hr₂ a
  obtain ⟨n, hn⟩ := hr₁' b
  rw [hb, hn]
  exact H.mul_mem (H.pow_mem hxH n) (H.pow_mem hyH m)

end Gens

section Embed

variable {V' V : Type} [AddCommGroup V'] [Module (ZMod 2) V'] [AddCommGroup V]
  [Module (ZMod 2) V] (Q' : QuadraticForm (ZMod 2) V') (Q : QuadraticForm (ZMod 2) V)

theorem s15k_table_plane_of_embed (E : V' → V) (R : V → V') (hE : ∀ p, Q (E p) = Q' p)
    (hR : ∀ z p, QuadraticMap.polar Q z (E p) = QuadraticMap.polar Q' (R z) p)
    (hRE : ∀ p, R (E p) = p) (z : V) (h : s15kPlane Q' (R z)) : s15kPlane Q z := by
  obtain ⟨a, b, ha, hb, hab, hza, hzb⟩ := h
  refine ⟨E a, E b, (hE a).trans ha, (hE b).trans hb, ?_, ?_, ?_⟩
  · rw [hR, hRE]
    exact hab
  · rw [hR]
    exact hza
  · rw [hR]
    exact hzb

theorem s15k_table_planePair_of_embed (E : V' → V) (R : V → V') (hE : ∀ p, Q (E p) = Q' p)
    (hR : ∀ z p, QuadraticMap.polar Q z (E p) = QuadraticMap.polar Q' (R z) p)
    (hRE : ∀ p, R (E p) = p) (z : V) (h : s15kPlanePair Q' (R z)) : s15kPlanePair Q z := by
  obtain ⟨a₀, b₀, a₁, b₁, ha₀, hb₀, hab₀, ha₁, hb₁, hab₁, h01, h02, h03, h04, hza₀, hzb₀, hza₁,
    hzb₁⟩ := h
  refine ⟨E a₀, E b₀, E a₁, E b₁, (hE _).trans ha₀, (hE _).trans hb₀, ?_, (hE _).trans ha₁,
    (hE _).trans hb₁, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | rw [hR]; assumption
    | rw [hR, hRE]; assumption

end Embed

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
