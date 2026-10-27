module

public import CFSG.RankThree.PartTwo.Sec18.Item189ListBorel
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.Goldschmidt.G3a (BorelSetup)

section Parity

theorem exists_sq_of_not_dvd_orderOf189 {Z : Type} [Group Z] [Finite Z] [IsCyclic Z] {k m : ℕ}
    (hm : Odd m) (hZ : Nat.card Z = 2 ^ k * m) {z : Z} (hz : ¬ 2 ^ k ∣ orderOf z) :
    ∃ w : Z, w ^ 2 = z := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Z)
  have hgo : orderOf g = 2 ^ k * m := by rw [orderOf_eq_card_of_forall_mem_zpowers hg, hZ]
  obtain ⟨i, hi⟩ : ∃ i : ℕ, g ^ i = z :=
    Submonoid.mem_powers_iff _ _ |>.mp ((mem_powers_iff_mem_zpowers).mpr (hg z))
  rcases Nat.even_or_odd i with ⟨j, hj⟩ | hodd
  · exact ⟨g ^ j, by rw [← pow_mul, ← hi]; congr 1; omega⟩
  · exfalso
    apply hz
    have hi0 : i ≠ 0 := by rintro rfl; exact absurd hodd (by decide)
    rw [← hi, orderOf_pow' _ hi0, hgo]
    have hcop : Nat.Coprime (2 ^ k) (Nat.gcd (2 ^ k * m) i) :=
      Nat.Coprime.pow_left _ (Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right _ _)
        (Nat.coprime_two_left.mpr hodd))
    have hq : 2 ^ k * m = Nat.gcd (2 ^ k * m) i * (2 ^ k * m / Nat.gcd (2 ^ k * m) i) :=
      (Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)).symm
    exact Nat.Coprime.dvd_of_dvd_mul_left hcop (hq ▸ dvd_mul_right _ _)

theorem exists_lift_normalizing189 {X : Type} [Group X] {Z : Type} [Group Z] (Λ : MulAut X →* Z)
    (hΛ : Function.Surjective Λ) (hinn : ∀ g : X, Λ (MulAut.conj g) = 1) {x : X}
    (hconj : ∀ x' : X, orderOf x' = 3 → ∃ g : X, g * x' * g⁻¹ ∈ Subgroup.zpowers x)
    (hx3 : orderOf x = 3) (ζ : Z) : ∃ θ₁ : MulAut X, Λ θ₁ = ζ ∧ θ₁ x ∈ Subgroup.zpowers x := by
  obtain ⟨θ₀, hθ₀⟩ := hΛ ζ
  have h3 : orderOf (θ₀ x) = 3 := by rw [← hx3]; exact θ₀.orderOf_eq x
  obtain ⟨g, hg⟩ := hconj _ h3
  refine ⟨MulAut.conj g * θ₀, ?_, ?_⟩
  · rw [map_mul, hinn, one_mul, hθ₀]
  · simpa [MulAut.mul_apply, MulAut.conj_apply] using hg

theorem smul_pair189 {X : Type} [Group X] {x : X} (hx3 : orderOf x = 3) {U U' : Sylow 2 X}
    (hne : U ≠ U')
    (hxU : x ∈ Subgroup.normalizer ((U : Subgroup X) : Set X))
    (hxU' : x ∈ Subgroup.normalizer ((U' : Subgroup X) : Set X))
    (hfix : ∀ V : Sylow 2 X, x ∈ Subgroup.normalizer ((V : Subgroup X) : Set X) → V = U ∨ V = U')
    {θ : MulAut X} (hθ : θ x ∈ Subgroup.zpowers x) :
    (θ • U = U ∧ θ • U' = U') ∨ (θ • U = U' ∧ θ • U' = U) := by
  have hy3 : orderOf (θ x) = 3 := by rw [← hx3]; exact θ.orderOf_eq x
  have hxmem : ∀ V : Sylow 2 X, x ∈ Subgroup.normalizer ((V : Subgroup X) : Set X) →
      x ∈ Subgroup.normalizer (((θ • V : Sylow 2 X) : Subgroup X) : Set X) := by
    intro V hV
    have h1 : θ x ∈ Subgroup.normalizer (((θ • V : Sylow 2 X) : Subgroup X) : Set X) :=
      CFSG.ComponentClassification.AschbacherToolkit.Bender.Omega.mem_normalizer_smul hV
    haveI : Finite (Subgroup.zpowers x) :=
      Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers, hx3]; norm_num)
    have hle : Subgroup.zpowers (θ x) ≤ Subgroup.zpowers x := Subgroup.zpowers_le.mpr hθ
    have hcard : Nat.card (Subgroup.zpowers x) ≤ Nat.card (Subgroup.zpowers (θ x)) := by
      rw [Nat.card_zpowers, Nat.card_zpowers, hy3, hx3]
    have heq : Subgroup.zpowers (θ x) = Subgroup.zpowers x :=
      Subgroup.eq_of_le_of_card_ge hle hcard
    have hxz : x ∈ Subgroup.zpowers (θ x) := heq ▸ Subgroup.mem_zpowers x
    exact (Subgroup.zpowers_le.mpr h1) hxz
  have hinj : θ • U ≠ θ • U' := fun h => hne (smul_left_cancel θ h)
  rcases hfix _ (hxmem U hxU) with h1 | h1 <;> rcases hfix _ (hxmem U' hxU') with h2 | h2
  · exact absurd (h1.trans h2.symm) hinj
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩
  · exact absurd (h1.trans h2.symm) hinj

theorem aut_apply_eq_or_inv189 {X : Type} [Group X] {x : X} (hx3 : orderOf x = 3) {θ : MulAut X}
    (hθ : θ x ∈ Subgroup.zpowers x) : θ x = x ∨ θ x = x⁻¹ := by
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hθ
  have hx3' : x ^ 3 = 1 := by rw [← hx3]; exact pow_orderOf_eq_one x
  have h1 := zpow_mod_orderOf x j
  rw [hx3] at h1
  push_cast at h1
  have hy3 : orderOf (θ x) = 3 := by rw [← hx3]; exact θ.orderOf_eq x
  have hcases : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
  rcases hcases with h | h | h
  · exfalso
    rw [h, zpow_zero] at h1
    rw [← hj, ← h1, orderOf_one] at hy3
    omega
  · left
    rw [h, zpow_one] at h1
    rw [← hj, ← h1]
  · right
    rw [h] at h1
    rw [← hj, ← h1]
    have e : x ^ ((2 : ℤ) + 1) = 1 := by
      have : ((2 : ℤ) + 1) = ((3 : ℕ) : ℤ) := by norm_num
      rw [this, zpow_natCast]
      exact hx3'
    rw [eq_inv_iff_mul_eq_one, ← zpow_add_one]
    exact e

theorem pair_cases189 {α : Type*} {W W' U U' V : α} (hU : U = W ∨ U = W')
    (hU' : U' = W ∨ U' = W') (hV : V = W ∨ V = W') (hne : U ≠ U') : V = U ∨ V = U' := by
  rcases hU with rfl | rfl <;> rcases hU' with rfl | rfl <;> rcases hV with rfl | rfl <;>
    simp_all

theorem two_pow_dvd_orderOf_of_swap189 {X : Type} [Group X] [Finite X]
    (hB : BorelOrderThree189 X) {Z : Type} [Group Z] [IsCyclic Z] (Λ : MulAut X →* Z)
    (hΛ : Function.Surjective Λ) {k m : ℕ} (hm : Odd m) (hZ : Nat.card Z = 2 ^ k * m)
    (hinn : ∀ g : X, Λ (MulAut.conj g) = 1)
    (hker : ∀ δ : MulAut X, Λ δ = 1 → ∃ r : ℕ, Odd r ∧ ∃ g : X, δ ^ r = MulAut.conj g)
    {x : X} (hx3 : orderOf x = 3) (hcard : Nat.card (Sylow 2 X) % 3 = 2)
    {U U' : Sylow 2 X} (hne : U ≠ U')
    (hxU : x ∈ Subgroup.normalizer ((U : Subgroup X) : Set X))
    (hxU' : x ∈ Subgroup.normalizer ((U' : Subgroup X) : Set X))
    {θ : MulAut X} (hθx : θ x = x) (hθU : θ • U = U') : 2 ^ k ∣ orderOf (Λ θ) := by
  classical
  by_contra hndvd
  haveI : Finite Z :=
    Nat.finite_of_card_ne_zero (by rw [hZ]; exact (Nat.mul_pos (by positivity) hm.pos).ne')
  obtain ⟨W, W', hWW', hxW, hxW', hWfix⟩ := exists_fixed_pair189 hB hx3 hcard
  have hfix : ∀ V : Sylow 2 X, x ∈ Subgroup.normalizer ((V : Subgroup X) : Set X) →
      V = U ∨ V = U' := fun V hV =>
    pair_cases189 (hWfix U hxU) (hWfix U' hxU') (hWfix V hV) hne
  obtain ⟨w, hw⟩ := exists_sq_of_not_dvd_orderOf189 hm hZ hndvd
  have hconj : ∀ x' : X, orderOf x' = 3 → ∃ g : X, g * x' * g⁻¹ ∈ Subgroup.zpowers x :=
    fun x' hx' => exists_conj_mem_zpowers189 hB hcard hx3 hx'
  obtain ⟨θ₁, hθ₁w, hθ₁x⟩ := exists_lift_normalizing189 Λ hΛ hinn hconj hx3 w
  have hθ₁sq_x : (θ₁ * θ₁) x = x := by
    rcases aut_apply_eq_or_inv189 hx3 hθ₁x with h | h
    · rw [MulAut.mul_apply, h, h]
    · rw [MulAut.mul_apply, h, map_inv, h, inv_inv]
  have hθ₁sqU : (θ₁ * θ₁) • U = U ∧ (θ₁ * θ₁) • U' = U' := by
    rcases smul_pair189 hx3 hne hxU hxU' hfix hθ₁x with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine ⟨?_, ?_⟩
      · rw [mul_smul, h1, h1]
      · rw [mul_smul, h2, h2]
    · refine ⟨?_, ?_⟩
      · rw [mul_smul, h1, h2]
      · rw [mul_smul, h2, h1]
  set δ : MulAut X := θ * (θ₁ * θ₁)⁻¹ with hδ
  have hδx : δ x = x := by
    have h1 : (θ₁ * θ₁)⁻¹ x = x := by
      calc (θ₁ * θ₁)⁻¹ x = (θ₁ * θ₁)⁻¹ ((θ₁ * θ₁) x) := by rw [hθ₁sq_x]
        _ = x := by simp
    rw [hδ, MulAut.mul_apply, h1, hθx]
  have hΛδ : Λ δ = 1 := by
    rw [hδ, map_mul, map_inv, map_mul, hθ₁w, ← hw, pow_two, mul_inv_cancel]
  have hδU : δ • U = U' := by
    have : (θ₁ * θ₁)⁻¹ • U = U := by
      rw [inv_smul_eq_iff]
      exact hθ₁sqU.1.symm
    rw [hδ, mul_smul, this]
    exact hθU
  have hswap : δ • U' = U := by
    rcases smul_pair189 hx3 hne hxU hxU' hfix (θ := δ)
        (by rw [hδx]; exact Subgroup.mem_zpowers x) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact absurd (h1.symm.trans hδU) hne
    · exact h2
  have hpow : ∀ V : Sylow 2 X, δ ^ 2 • V = V → ∀ j : ℕ, (δ ^ 2) ^ j • V = V := by
    intro V hV j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ, mul_smul, hV, ih]
  have hδ2U' : δ ^ 2 • U' = U' := by rw [pow_two, mul_smul, hswap, hδU]
  have hfixpow : ∀ n : ℕ, (δ ^ n) x = x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, MulAut.mul_apply, hδx, ih]
  obtain ⟨r, hr, g, hg⟩ := hker δ hΛδ
  obtain ⟨t, rfl⟩ := hr
  have hgU : g • U = U' := by
    rw [Sylow.smul_def, ← hg, pow_succ, mul_smul, hδU, pow_mul]
    exact hpow U' hδ2U' t
  have hgx : g * x = x * g := by
    have h1 : g * x * g⁻¹ = x := by
      have := hfixpow (2 * t + 1)
      rw [hg] at this
      simpa [MulAut.conj_apply] using this
    calc g * x = g * x * g⁻¹ * g := by group
      _ = x * g := by rw [h1]
  exact no_swap189 hB hne hxU hxU' hfix hgx hgU

theorem exists_hom_of_outShape189 {X : Type} [Group X] {k m : ℕ}
    (hOut : ∃ (Dd : Subgroup (Outer X)) (_ : Dd.Normal), Odd (Nat.card Dd) ∧
      IsCyclic (Outer X ⧸ Dd) ∧ Nat.card (Outer X ⧸ Dd) = 2 ^ k * m) :
    ∃ (Z : Type) (_ : Group Z) (_ : IsCyclic Z) (Λ : MulAut X →* Z),
      Function.Surjective Λ ∧ Nat.card Z = 2 ^ k * m ∧ (∀ g : X, Λ (MulAut.conj g) = 1) ∧
      ∀ δ : MulAut X, Λ δ = 1 → ∃ r : ℕ, Odd r ∧ ∃ g : X, δ ^ r = MulAut.conj g := by
  obtain ⟨Dd, hn, hodd, hcyc, hcard⟩ := hOut
  haveI := hn
  haveI : Finite Dd := Nat.finite_of_card_ne_zero hodd.pos.ne'
  refine ⟨Outer X ⧸ Dd, inferInstance, hcyc,
    (QuotientGroup.mk' Dd).comp
      (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner X)),
    (QuotientGroup.mk'_surjective Dd).comp (QuotientGroup.mk'_surjective _), hcard, ?_, ?_⟩
  · intro g
    have hmem : (MulAut.conj g) ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner X :=
      ⟨g, rfl⟩
    simp [(QuotientGroup.eq_one_iff _).mpr hmem]
  · intro δ hδ
    have hq : (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner X)) δ ∈
        Dd := (QuotientGroup.eq_one_iff _).mp hδ
    have h1 : ((⟨_, hq⟩ : Dd)) ^ Nat.card Dd = 1 := pow_card_eq_one'
    have h2 : (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner X))
        (δ ^ Nat.card Dd) = 1 := by
      rw [map_pow]
      have h1' := congrArg Subtype.val h1
      simp only [Subgroup.coe_pow, Subgroup.coe_one] at h1'
      exact h1'
    have h3 : δ ^ Nat.card Dd ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner X :=
      (QuotientGroup.eq_one_iff _).mp h2
    obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp h3
    exact ⟨Nat.card Dd, hodd, g, hg.symm⟩

end Parity

end CFSG.RankThree.PartTwo.Sec18
