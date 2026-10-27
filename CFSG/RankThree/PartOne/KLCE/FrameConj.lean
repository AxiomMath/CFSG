module

public import CFSG.RankThree.PartOne.KLCE.Descent

public noncomputable section

namespace CFSG.RankThree.PartOne.KLCE

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KE


section Frame

variable {τ : Tag} {K₀ K L : Type} [Field K₀] [Finite K₀] [Field K] [Finite K] [Field L]
  [Algebra K₀ K] [Algebra K L] [Algebra K₀ L] [IsScalarTower K₀ K L] [IsAlgClosure K₀ L]

@[expose] def towerHom (τ : Tag) (K₀ K : Type) [Field K₀] [Field K] [Algebra K₀ K] :
    adjointGroup τ K₀ →* adjointGroup τ K :=
  ((baseChangeGL (algebraMap K₀ K)).comp (adjointGroup τ K₀).subtype).codRestrict _
    (fun y => baseChangeGL_mem_adjointGroup _ y.2)

omit [Finite K₀] [Finite K] [IsAlgClosure K₀ L] in
theorem adjEmb_towerHom (y : adjointGroup τ K₀) :
    adjEmb τ K L (towerHom τ K₀ K y) = adjEmb τ K₀ L y := by
  rw [adjEmb_apply, adjEmb_apply]
  change baseChangeGL (algebraMap K L) (baseChangeGL (algebraMap K₀ K) (y : ModGL τ K₀)) = _
  rw [baseChangeGL_baseChangeGL, ← IsScalarTower.algebraMap_eq]

omit [Finite K] in
theorem frame_conj [CharP L 2] {d : ℕ}
    (hτ : (τ = .E6 ∧ d = 3) ∨ (τ = .E7 ∧ d = 2) ∨ (τ = .E8 ∧ d = 1)) {f₀ : ℕ} (hf₀ : 1 ≤ f₀)
    (hK₀ : Nat.card K₀ = 2 ^ f₀) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (n₀ : ModGL τ L) (hn₀C : n₀ ∈ adjointGroup τ L) (Z : Subgroup (ModGL τ L))
    (hZ : Z ≤ twistedTorusOf n₀ (Units.map (entrywiseHom (iterateFrobenius L 2 f₀))))
    {N₀ : ℕ} (hN₀ : N₀ ≠ 0) (hZcard : Nat.card Z = N₀)
    (hord : p ^ (Nat.card (adjointGroup τ K₀)).factorization p = p ^ N₀.factorization p) :
    ∃ g₀ : ModGL τ L, g₀ ∈ adjointGroup τ L ∧
      Units.map (entrywiseHom (iterateFrobenius L 2 f₀)) g₀ = g₀ * n₀ ∧
      ∀ x : adjointGroup τ K, orderOf x = p →
        Units.map (entrywiseHom (iterateFrobenius L 2 f₀)) (adjEmb τ K L x) = adjEmb τ K L x →
        ∃ c : adjointGroup τ K,
          Units.map (entrywiseHom (iterateFrobenius L 2 f₀)) (adjEmb τ K L c) = adjEmb τ K L c ∧
            c * x * c⁻¹ ∈ subtorusImage (adjEmb τ K L) g₀ Z := by
  classical
  have : CharP K₀ 2 := ⟨fun x => by
    rw [← (algebraMap K₀ L).injective.eq_iff, map_natCast, map_zero]
    exact CharP.cast_eq_zero_iff L 2 x⟩
  have : Fintype K₀ := Fintype.ofFinite K₀
  have : Finite (ModGL τ K₀) := finite_modGL
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K₀
  have : Algebra.IsAlgebraic K₀ L := IsAlgClosure.isAlgebraic
  set Φ₀ : L →+* L := iterateFrobenius L 2 f₀ with hΦ₀
  have hFr : ∀ c, Φ₀ c = c ^ Nat.card K₀ := fun c => by
    rw [hK₀]
    exact iterateFrobenius_def 2 f₀ c
  obtain ⟨g₀, hg₀C, hg₀, -, hconj⟩ := sigma_untwisted_sylow τ d hτ K₀ hf₀ hK₀ L hp hp3 n₀ hn₀C Z
    hZ hN₀ hZcard hord
  refine ⟨g₀, hg₀C, hg₀, fun x hx hxfix => ?_⟩
  have hordι : orderOf (adjEmb τ K L x) = p := by
    rw [orderOf_injective (adjEmb τ K L) adjEmb_injective x, hx]
  have hXfin : Finite (Subgroup.zpowers (adjEmb τ K L x)) :=
    Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers, hordι]; exact hp.ne_zero)
  have hXp : IsPGroup p (Subgroup.zpowers (adjEmb τ K L x)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hordι, pow_one])
  have hrat := finite_fixed_subgroup_rational_perfect (τ := τ) (K := K₀) (L := L) d hτ Φ₀ hFr
    (Subgroup.zpowers (adjEmb τ K L x))
    (Subgroup.zpowers_le.2 (adjEmb_mem x)) (fun y hy => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      rw [map_zpow, hxfix])
  have hmem : adjEmb τ K L x ∈ (adjEmb τ K₀ L).range := by
    rw [adjEmb_range]
    exact hrat.2.1 p hp hp3 _ le_rfl hXp (Subgroup.mem_zpowers _)
  obtain ⟨x₀, hx₀⟩ := hmem
  have hx₀ord : orderOf x₀ = p := by
    rw [← orderOf_injective (adjEmb τ K₀ L) adjEmb_injective x₀, hx₀, hordι]
  have hQp : IsPGroup p (Subgroup.zpowers x₀) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx₀ord, pow_one])
  obtain ⟨c₀, hc₀⟩ := hconj _ hQp
  have hc₀x := hc₀ x₀ (Subgroup.mem_zpowers _)
  refine ⟨towerHom τ K₀ K c₀, ?_, ?_⟩
  · rw [adjEmb_towerHom]
    exact adjEmb_frobenius Φ₀ hFr c₀
  · rw [mem_subtorusImage_iff] at hc₀x ⊢
    have hxe : adjEmb τ K L x = adjEmb τ K₀ L x₀ := hx₀.symm
    rw [map_mul, map_mul, map_inv, adjEmb_towerHom, hxe]
    rw [map_mul, map_mul, map_inv] at hc₀x
    exact hc₀x

end Frame

section Arith

theorem dvd_eval_of_dvd_eval_pow {p : ℕ} (hp : p.Prime) (f : Polynomial ℤ) {q : ℕ}
    (h : (p : ℤ) ∣ f.eval ((q : ℤ) ^ p)) : (p : ℤ) ∣ f.eval (q : ℤ) := by
  have : Fact p.Prime := ⟨hp⟩
  have h1 : (p : ℤ) ∣ (q : ℤ) ^ p - q := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.pow_card, sub_self]
  have h2 : (p : ℤ) ∣ f.eval ((q : ℤ) ^ p) - f.eval (q : ℤ) :=
    h1.trans (Polynomial.sub_dvd_eval_sub _ _ f)
  have h3 := dvd_sub h h2
  simpa using h3

end Arith

section Twisted

variable {τ : Tag} {L : Type} [Field L]

theorem twisted_pow_fixed {n₀ : ModGL τ L} {Φ₀ : ModGL τ L →* ModGL τ L} (hn : Φ₀ n₀ = n₀)
    (p : ℕ) {u : ModGL τ L} (hu : n₀ * Φ₀ u * n₀⁻¹ = u) :
    n₀ ^ p * (⇑Φ₀)^[p] u * (n₀ ^ p)⁻¹ = u := by
  have h := iterate_F0 Φ₀ hn p u
  rw [Function.iterate_fixed hu p] at h
  exact h.symm

theorem twistedTorusOf_le_pow {n₀ : ModGL τ L} {Φ₀ Φ : ModGL τ L →* ModGL τ L}
    (hn : Φ₀ n₀ = n₀) (p : ℕ) (hΦ : ∀ u, Φ u = (⇑Φ₀)^[p] u) :
    twistedTorusOf n₀ Φ₀ ≤ twistedTorusOf (n₀ ^ p) Φ := by
  intro u hu
  obtain ⟨hH, hfix⟩ := mem_twistedTorusOf.1 hu
  refine mem_twistedTorusOf.2 ⟨hH, ?_⟩
  rw [hΦ]
  exact twisted_pow_fixed hn p hfix

end Twisted

end CFSG.RankThree.PartOne.KLCE
