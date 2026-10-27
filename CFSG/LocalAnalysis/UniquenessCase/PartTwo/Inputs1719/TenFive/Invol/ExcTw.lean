module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.ExcE6TwData
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.ExcD4TwData
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.ExcE6TwOuter
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.Families
public import CFSG.LieType.Chevalley.OddExceptionalOuterTwoRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Chevalley.ToralSign
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)

theorem mask_ne_zero_of_conj_ne_one {τ : Tag} {L : Type} [Field L] {x g₁ : ModGL τ L} {m : ℕ}
    (hx1 : x ≠ 1)
    (hgx : g₁ * x * g₁⁻¹ = rootDiagUnit τ (signCharTuple (k := L) (signMaskChar τ m))) :
    m ≠ 0 := by
  rintro rfl
  apply hx1
  have h1 : signCharTuple (k := L) (signMaskChar τ 0) = 1 := by
    funext i
    rw [signCharTuple, signMaskChar_single]
    simp
  rw [h1, rootDiagUnit_one] at hgx
  calc x = g₁⁻¹ * (g₁ * x * g₁⁻¹) * g₁ := by group
    _ = 1 := by rw [hgx]; group


theorem twistedInnerData_E6 {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hf : 1 ≤ f) (h3 : 3 < p ^ f)
    (L : Type) [Field L] [IsAlgClosed L] [CharP L p] : TwistedInnerData TwistTag.E6 L p f := by
  intro x hx hx2 hx1
  obtain ⟨r, hr, l, hl, g₁, hg₁, hgx, hgF⟩ := exists_conj_toral_twist_E6tw p hp2 hf hx hx2
  obtain ⟨ι⟩ := nonempty_galoisField_ringHom L p f
  obtain ⟨u, hu, hgood, hinv⟩ := exists_inv_good_E6tw_twist ι hp2
    (GaloisField.card p f (by omega)) h3 hr (mask_ne_zero_of_conj_ne_one hx1 hgx) hl
  exact ⟨g₁, hg₁, _, hgF, u, hu, hgood, by rw [hgx]; exact hinv⟩

theorem twistedInnerData_D4 {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hf : 1 ≤ f) (h3 : 3 < p ^ f)
    (L : Type) [Field L] [IsAlgClosed L] [CharP L p] : TwistedInnerData TwistTag.D4 L p f := by
  intro x hx hx2 hx1
  obtain ⟨r, hr, l, hl, g₁, hg₁, hgx, hgF⟩ := exists_conj_toral_twist_D4tw p hp2 hf hx hx2
  obtain ⟨ι⟩ := nonempty_galoisField_ringHom L p f
  obtain ⟨u, hu, hgood, hinv⟩ := exists_inv_good_D4tw_twist ι hp2
    (GaloisField.card p f (by omega)) h3 hr (mask_ne_zero_of_conj_ne_one hx1 hgx) hl
  exact ⟨g₁, hg₁, _, hgF, u, hu, hgood, by rw [hgx]; exact hinv⟩

theorem exists_inv_conj_twisted (t : TwistTag) {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ t.order)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f)) (L : Type) [Field L] [Algebra K L]
    [IsAlgClosure K L] [CharP L p] {R : ℕ → ℕ → Prop} (hdata : TwistedInnerDataOf t L p f R)
    (g : graphFixedRootGroup t K σ.toRingHom) (hg : orderOf (MulAut.conj g) = 2) :
    ∃ x : graphFixedRootGroup t K σ.toRingHom, orderOf x = p ∧ MulAut.conj g x = x⁻¹ ∧
      ∃ (H : Subgroup (graphFixedRootGroup t K σ.toRingHom)) (e n : ℕ), x ∈ H ∧
        IsSpecialType p e n ↥H ∧ R e n := by
  have hZ := exceptional_fixed_center_trivial t K σ
  have hg1 : g ≠ 1 := fun h => by
    rw [h, map_one, orderOf_one] at hg
    omega
  have hg2 : g ^ 2 = 1 := by
    have h1 : MulAut.conj (g ^ 2) = 1 := by rw [map_pow, ← hg, pow_orderOf_eq_one]
    have hc : g ^ 2 ∈ Subgroup.center (graphFixedRootGroup t K σ.toRingHom) :=
      Subgroup.mem_center_iff.2 fun y => by
        have h := DFunLike.congr_fun h1 y
        rw [MulAut.conj_apply, MulAut.one_apply] at h
        calc y * g ^ 2 = g ^ 2 * y * (g ^ 2)⁻¹ * g ^ 2 := by rw [h]
          _ = g ^ 2 * y := by group
    rwa [hZ, Subgroup.mem_bot] at hc
  obtain ⟨x, hx, hinv, hgood⟩ := exists_inv_inner_twisted t hp2 hf hK σ hσ L hdata g hg2 hg1
  exact ⟨x, hx, by rw [MulAut.conj_apply]; exact hinv, hgood⟩

theorem exists_inv_good_conj_twisted (t : TwistTag) {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ t.order)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f)) (L : Type) [Field L] [Algebra K L]
    [IsAlgClosure K L] [CharP L p] (hdata : TwistedInnerData t L p f)
    (g : graphFixedRootGroup t K σ.toRingHom) (hg : orderOf (MulAut.conj g) = 2) :
    ∃ x : graphFixedRootGroup t K σ.toRingHom, orderOf x = p ∧ MulAut.conj g x = x⁻¹ ∧
      (IsSpecialGood p x ∨ IsOrbitGood p x) := by
  obtain ⟨x, hx, hinv, hgood⟩ := exists_inv_conj_twisted t hp2 hf hK σ hσ L
    (R := fun e n => e ≤ n ∧ 3 < p ^ e) hdata g hg
  exact ⟨x, hx, hinv, Or.inl hgood⟩

theorem involInvertsGood_E6tw {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) (h3 : 3 < p ^ f) :
    InvolInvertsGood p (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) := by
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    hp (by omega : 1 ≤ 2 * f) (by rw [hK, ← pow_mul, mul_comm])
  have : CharP (AlgebraicClosure K) p :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective p
  intro α hα
  by_cases hin : α ∈ twistedE6Inn K σ
  · obtain ⟨g, rfl⟩ := hin
    exact exists_inv_good_conj_twisted TwistTag.E6 hp2 hf hK σ hσ (AlgebraicClosure K)
      (twistedInnerData_E6 hp2 hf h3 (AlgebraicClosure K)) g hα
  · have hα2 : α ^ 2 = 1 := by rw [← hα, pow_orderOf_eq_one]
    obtain ⟨x, hx, hinv, hgood⟩ := exists_inv_good_outer_E6tw hp hp2 hf hK σ hσ h3 α hα2 hin
    exact ⟨x, hx, hinv, Or.inl hgood⟩

theorem involQAt_twistedE6 : InvolQAt .twistedE6 := by
  intro S _ _ n p e hp2 h3 _ hS
  obtain ⟨⟨hp, he, -⟩, hm⟩ := hS.chevalleyExceptionalModel (by decide)
  obtain ⟨K, _, _, σ, hK, hσ, ⟨φ⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_card TwistTag.E6 hp he hm
  exact InvolInvertsGood.of_mulEquiv φ.symm (involInvertsGood_E6tw hp hp2 he hK σ hσ h3)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive
