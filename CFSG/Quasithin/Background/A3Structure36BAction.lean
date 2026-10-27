module

public import CFSG.Quasithin.Background.A3Structure36BAux
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Centralization

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.A36B

open Subgroup CFSG.SectionRank CFSG.SectionRank.Ccomm Matrix

variable {q : ℕ} [hq : Fact q.Prime]

theorem action_frattini_quotient (hq2 : q ≠ 2) {R : Type*} [Group R] [Finite R]
    (hR : IsPGroup q R) (hrank : CFSG.Open.pRank q (⊤ : Subgroup R) ≤ 2) (D : Subgroup R)
    [D.Characteristic] (hexp : ∀ x ∈ D, x ^ q = 1) (hker : IsPGroup q (frattiniAction D).ker)
    {H : Type*} [Group H] [Group.IsPerfect H] (α : H →* MulAut R) (hα : α ≠ 1)
    (ρ : H →* MulAut (D ⧸ frattini D)) (hρ : ρ = (frattiniAction D).comp α) :
    Nat.card (D ⧸ frattini D) = q ^ 2 ∧ ρ ≠ 1 ∧
      (∀ h : H, ρ h * ρ h = 1 → ρ h ≠ 1 → ∀ w, ρ h w = w⁻¹) ∧
      (∀ U : Subgroup (D ⧸ frattini D), Nat.card U = q → ∃ h : H, ∃ u ∈ U, ρ h u ∉ U) := by
  have hDp : IsPGroup q D := hR.to_subgroup D
  obtain ⟨-, hWcomm, hWpow⟩ := frattini_quotient_elementary hDp
  have hρ1 : ρ ≠ 1 := by
    intro hρ1
    apply hα
    have hle : α.range ≤ (frattiniAction D).ker := by
      rintro _ ⟨x, rfl⟩
      rw [MonoidHom.mem_ker]
      have := congrArg (· x) hρ1
      rw [hρ] at this
      exact this
    have hpg : IsPGroup q α.range := hker.to_le hle
    exact hom_eq_one_of_isPGroup_range α hpg
  have hDrank : CFSG.Open.pRank q (⊤ : Subgroup D) ≤ 2 :=
    (pRank_top_le_of_injective hq.out.one_lt D.subtype D.subtype_injective).trans hrank
  have hDexp : ∀ x : D, x ^ q = 1 := fun x =>
    Subtype.ext (by rw [SubgroupClass.coe_pow, OneMemClass.coe_one]; exact hexp _ x.2)
  obtain ⟨hD3, hW2⟩ := rank_two_exponent_prime_order_bound hDp hDexp hDrank
  obtain ⟨k, hk⟩ := (hDp.to_quotient (frattini D)).exists_card_eq
  have hk2 : k ≤ 2 := (Nat.pow_le_pow_iff_right hq.out.one_lt).1 (hk ▸ hW2)
  obtain ⟨e⟩ := nonempty_mulEquiv_of_elementary hWcomm hWpow hk
  have hk2' : k = 2 := by
    by_contra hk2'
    apply hρ1
    apply perfect_hom_eq_one_of_range_comm
    intro a _ b _
    apply (elemAutEquivGL e).injective
    rw [map_mul, map_mul]
    exact GL_comm_of_le_one (by omega) _ _
  subst hk2'
  set ψ := elemAutEquivGL e with hψ
  set J' := ρ.range.map ψ.toMonoidHom with hJ'
  have hJperf : Group.IsPerfect ρ.range := Group.IsPerfect.range ρ
  have hJ'perf : Group.IsPerfect J' := Group.IsPerfect.map _
  have hJne : ρ.range ≠ ⊥ := by
    intro hbot
    apply hρ1
    ext x
    have hx : ρ x ∈ ρ.range := ⟨x, rfl⟩
    rw [hbot, mem_bot] at hx
    rw [hx]
    rfl
  have hJ'ne : J' ≠ ⊥ := by
    rw [hJ', Ne, map_eq_bot_iff_of_injective _ ψ.injective]
    exact hJne
  refine ⟨hk, hρ1, ?_, ?_⟩
  ·
    intro h hsq hne
    have hmem : ψ (ρ h) ∈ J' := Subgroup.mem_map_of_mem _ ⟨h, rfl⟩
    have hdet := (perfect_linear_two_basics J' hJ'ne).1 _ hmem
    have hgg : ((ψ (ρ h) : GL (Fin 2) (ZMod q)) : Matrix (Fin 2) (Fin 2) (ZMod q)) *
        ((ψ (ρ h) : GL (Fin 2) (ZMod q)) : Matrix (Fin 2) (Fin 2) (ZMod q)) = 1 := by
      rw [← Units.val_mul, ← map_mul, hsq, map_one, Units.val_one]
    rcases eq_one_or_neg_one_of_sq_eq_one (two_ne_zero_zmod hq2) hdet hgg with h1 | h1
    · exfalso
      apply hne
      apply ψ.injective
      apply Units.ext
      rw [map_one, Units.val_one]
      exact h1
    · have : ψ (ρ h) = -1 := Units.ext (by rw [Units.val_neg, Units.val_one]; exact h1)
      exact (elemAutEquivGL_eq_neg_one_iff e (ρ h)).1 this
  ·
    intro U hU
    obtain ⟨u, huU, hu1⟩ : ∃ u ∈ U, u ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have hbot : U = ⊥ := (eq_bot_iff_forall U).2 hcon
      rw [hbot, card_bot] at hU
      exact hq.out.one_lt.ne hU
    have hUz : U = zpowers u := by
      symm
      refine eq_of_le_of_card_ge (zpowers_le.2 huU) ?_
      rw [hU, Nat.card_zpowers]
      exact (orderOf_eq_prime (hWpow u) hu1).ge
    set v := Multiplicative.toAdd (e u) with hvdef
    have hv : v ≠ 0 := by
      intro hv
      apply hu1
      apply e.injective
      rw [map_one]
      exact Multiplicative.toAdd.injective (hv.trans toAdd_one.symm)
    obtain ⟨g', hg'J, hg'⟩ := (perfect_linear_two_basics J' hJ'ne).2.1 v hv
    obtain ⟨g, hgJ, rfl⟩ := mem_map.1 hg'J
    obtain ⟨h, rfl⟩ := hgJ
    refine ⟨h, u, huU, fun hgu => ?_⟩
    rw [hUz] at hgu
    obtain ⟨n, hn⟩ := mem_zpowers_iff.1 hgu
    apply hg' (n : ZMod q)
    rw [MulEquiv.coe_toMonoidHom, elemAutEquivGL_mulVec, ← hn, map_zpow, toAdd_zpow,
      Int.cast_smul_eq_zsmul]

end CFSG.Quasithin.A36B
