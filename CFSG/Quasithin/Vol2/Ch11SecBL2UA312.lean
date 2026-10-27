module

public import CFSG.Quasithin.Vol2.Ch11SecBL2UOut
import CFSG.Quasithin.Vol2.Ch11SecQ9bKGB
public import CFSG.LieType.Simplicity.Suzuki

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open

theorem two_mul_card_isPSL_two {X : Type} [Group X] {p : ℕ} (hp2 : p ≠ 2)
    (h : IsPSL 2 p 1 X) : 2 * Nat.card X = p * (p ^ 2 - 1) :=
  CFSG.Quasithin.Vol2.Ch11.SecA.C11P9B.two_mul_card_of_isPSL2 hp2 h

section Quot

variable {K Y : Type} [Group K] [Group Y] [Finite Y] [IsSimpleGroup Y] [Group.IsPerfect K]
  (hY : ∃ a b : Y, a * b ≠ b * a) {N : Subgroup K} [N.Normal] (hN : IsPGroup 2 N)
  (hQ : CFSG.Open.IsQuasisimple (K ⧸ N)) (ψ : K →* Y) (hψ : Function.Surjective ψ)
include hY hN hQ hψ

theorem out_alt {X : Type} [Group X] [Finite X] (g : K →* X) (hg : Function.Surjective g)
    {n : ℕ} (hn5 : 5 ≤ n) (hn8 : n ≤ 8) (h : IsAlt n X) : A312Out Y := by
  obtain ⟨e⟩ : Nonempty (X ≃* alternatingGroup (Fin n)) := h
  exact a312Out_of_alt hY hN hQ ψ hψ g hg hn5 hn8 e

theorem out_card {X : Type} [Group X] [Finite X] (g : K →* X) (hg : Function.Surjective g)
    {c : ℕ} (hc : Nat.card X = c) (h1 : 1 < c) (h2 : c ≤ 20160) : A312Out Y :=
  a312Out_of_card_le hY hN hQ ψ hψ g hg (hc ▸ h1) (hc ▸ h2)

theorem out_hatAlt {X : Type} [Group X] [Finite X] (g : K →* X) (hg : Function.Surjective g)
    {n : ℕ} (hn5 : 5 ≤ n) (hn8 : n ≤ 8) (h : IsHat X (alternatingGroup (Fin n))) :
    A312Out Y := by
  obtain ⟨-, -, ⟨e⟩⟩ := h
  exact a312Out_of_alt hY hN hQ ψ hψ ((QuotientGroup.mk' (Subgroup.center X)).comp g)
    ((QuotientGroup.mk'_surjective _).comp hg) hn5 hn8 e

theorem out_sl2 {X : Type} [Group X] [Finite X] (g : K →* X) (hg : Function.Surjective g)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (h : IsSL2 p X) : A312Out Y := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨e⟩ : Nonempty (X ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) := h
  have hp5 : 5 ≤ p := by
    by_contra hlt
    have h4 : p = 4 := by omega
    rw [h4] at hp
    exact absurd hp (by decide)
  have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)) :=
    isSimpleGroup_psl2 hp5
  refine a312Out_of_simple hY hN hQ ψ hψ
    (((QuotientGroup.mk' _).comp e.toMonoidHom).comp g)
    (((QuotientGroup.mk'_surjective _).comp e.surjective).comp hg)
    (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, hp, by omega, two_mul_card_psl2 (by omega)⟩))))

theorem out_psl2 {X : Type} [Group X] [Finite X] (g : K →* X) (hg : Function.Surjective g)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (h : IsPSL 2 p 1 X) : A312Out Y := by
  have : IsSimpleGroup X := (CFSG.LieType.Simplicity.fam_PSL_simplicity X 2 p 1 h).2
  exact a312Out_of_simple hY hN hQ ψ hψ g hg
    (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, hp, by omega, two_mul_card_isPSL_two (by omega) h⟩))))

theorem out_psl22 {X : Type} [Group X] [Finite X] (g : K →* X) (hg : Function.Surjective g)
    {n : ℕ} (h : IsPSL 2 2 n X) : A312Out Y := by
  have : IsSimpleGroup X := (CFSG.LieType.Simplicity.fam_PSL_simplicity X 2 2 n h).2
  have hn : 2 ≤ n := by
    obtain ⟨⟨-, h1, -, h22, -⟩, -⟩ := h
    by_contra hlt
    exact h22 (by rw [show n = 1 by omega, pow_one])
  exact a312Out_of_simple hY hN hQ ψ hψ g hg (Or.inr (Or.inl ⟨n, hn, h⟩))

theorem out_sz {X : Type} [Group X] [Finite X] (g : K →* X) (hg : Function.Surjective g)
    {f : ℕ} (h : IsSz f X) : A312Out Y := by
  have : IsSimpleGroup X := (CFSG.LieType.Simplicity.fam_2b2_simplicity X 2 f h).2
  exact a312Out_of_simple hY hN hQ ψ hψ g hg (Or.inr (Or.inr (Or.inl ⟨f, h⟩)))

theorem out_m22 (hM : FactMathieuOrders) {X : Type} [Group X] [Finite X] (g : K →* X)
    (hg : Function.Surjective g) (h : IsSporadic .M22 X) : A312Out Y := by
  obtain ⟨e⟩ : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.Carrier .M22) := h
  have := hM.1
  have : IsSimpleGroup X := e.isSimpleGroup
  exact a312Out_of_simple hY hN hQ ψ hψ g hg
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by rw [Nat.card_congr e.toEquiv, hM.2.1]))))))

theorem out_m24 (hM : FactMathieuOrders) {X : Type} [Group X] [Finite X] (g : K →* X)
    (hg : Function.Surjective g) (h : IsSporadic .M24 X) : A312Out Y := by
  obtain ⟨e⟩ : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.Carrier .M24) := h
  have := hM.2.2.1
  have : IsSimpleGroup X := e.isSimpleGroup
  exact a312Out_of_simple hY hN hQ ψ hψ g hg
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by rw [Nat.card_congr e.toEquiv, hM.2.2.2]))))))

theorem out_hatM22 (hM : FactMathieuOrders) {X : Type} [Group X] [Finite X] (g : K →* X)
    (hg : Function.Surjective g) (h : IsHat X (CFSG.Blueprint.NativeSporadic.Carrier .M22)) :
    A312Out Y := by
  obtain ⟨-, -, ⟨e⟩⟩ := h
  have : Finite (CFSG.Blueprint.NativeSporadic.Carrier .M22) :=
    Finite.of_equiv _ e.toEquiv
  exact out_m22 hY hN hQ ψ hψ hM ((e.toMonoidHom.comp (QuotientGroup.mk' _)).comp g)
    ((e.surjective.comp (QuotientGroup.mk'_surjective _)).comp hg) ⟨MulEquiv.refl _⟩

end Quot

theorem out_ext {K X : Type} [Group K] [Group X] [Finite X] {P : Prop} (g : K →* X)
    (hg : Function.Surjective g) {PV PY : ∀ (V : Type) [Group V], Prop} (h : IsExt X PV PY)
    (hcont : ∀ (Z : Type) [Group Z] [Finite Z], PY Z → ∀ g' : K →* Z,
      Function.Surjective g' → P) : P := by
  obtain ⟨V, hVn, -, hPY⟩ := h
  exact hcont (X ⧸ V) hPY ((QuotientGroup.mk' V).comp g) ((QuotientGroup.mk'_surjective _).comp hg)

end CFSG.Quasithin.Vol2.Ch11.SecB
