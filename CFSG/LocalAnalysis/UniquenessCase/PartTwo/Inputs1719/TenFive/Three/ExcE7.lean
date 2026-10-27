module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.ExcTorus
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.ExcE7Twist
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.ExcIndexTransport
import CFSG.Fischer.Classification.Recognition.PSU6
import CFSG.LieType.Chevalley.CLSOddE6AllInvolutionFourGroup
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.ExcTransport
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.ExcTwistConj

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Chevalley.ToralSign CFSG.LieType.Steinberg.Adjoint
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)


theorem exists_inv_extraGood_inner_diagonal_E7 {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 3) (β : MulAut (adjointGroup .E7 K)) (hβ : β ^ 2 = 1) (hβ1 : β ≠ 1)
    (g : adjointGroup .E7 K) (a : Fin Tag.E7.rank → Kˣ)
    (hexpr : ∀ h : adjointGroup .E7 K, (β h : ModGL .E7 K) =
      (g : ModGL .E7 K) * rootDiagUnit .E7 a * h * (rootDiagUnit .E7 a)⁻¹ *
        (g : ModGL .E7 K)⁻¹) :
    ∃ x : adjointGroup .E7 K, orderOf x = 3 ∧ β x = x⁻¹ ∧ IsExtraGood x := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 3 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_three le_rfl (by rw [hK, pow_one])
  have hKodd : Odd (Nat.card K) := by
    rw [hK]
    decide
  set Lk := AlgebraicClosure K
  set ι : K →+* Lk := algebraMap K Lk with hιdef
  have : CharP Lk 3 := charP_of_injective_algebraMap (algebraMap K Lk).injective 3
  set Fr : Lk →+* Lk := iterateFrobenius Lk 3 1 with hFrdef
  have hFr : ∀ c, Fr c = c ^ Nat.card K := by
    intro c
    rw [hFrdef, iterateFrobenius_def, hK]
    rfl
  obtain ⟨hinj, hHG, hfaith, -⟩ :=
    exceptional_Lang_finite_root_centralizer_faithfulness .E7 K hKodd Lk ι
  obtain ⟨-, hHR, hRnorm, -⟩ :=
    exceptional_Lang_Frobenius_fixed_derived_root_group .E7 K hKodd Lk Fr hFr
  obtain ⟨hRfin, -, hidx⟩ := odd_E7_rational_derived_index_at_most_two K hKodd Lk Fr hFr
  set R : Subgroup (ModGL .E7 Lk) :=
    adjointGroup .E7 Lk ⊓ (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _) with hRdef
  have hS : frobTwistGL .E7 Lk 3 1 1 = Units.map (entrywiseHom Fr) := by
    ext u
    rw [frobTwistGL_apply, one_mul, inv_one, mul_one]
  have hReq : fixedPointsIn (adjointGroup .E7 Lk) (frobTwistGL .E7 Lk 3 1 1) = R := by
    rw [hS, hRdef]
  set x : ModGL .E7 K := (g : ModGL .E7 K) * rootDiagUnit .E7 a with hxdef
  set x' := baseChangeGL ι x with hx'def
  have hx'G : x' ∈ adjointGroup .E7 Lk := by
    rw [hx'def, hxdef, map_mul, baseChangeGL_rootDiagUnit]
    exact mul_mem (hHG ⟨_, g.2, rfl⟩) (exceptional_Lang_adjoint_diagonal_lift .E7 Lk _).1
  have hx'F : Units.map (entrywiseHom Fr) x' = x' :=
    units_map_entrywiseHom_baseChangeGL_algebraMap Fr hFr x
  have hβx : ∀ h : adjointGroup .E7 K, (β h : ModGL .E7 K) = x * h * x⁻¹ := fun h => by
    rw [hexpr h, hxdef, mul_inv_rev]
    group
  have hβx' : ∀ u : adjointGroup .E7 K, baseChangeGL ι (β u : ModGL .E7 K) =
      x' * baseChangeGL ι (u : ModGL .E7 K) * x'⁻¹ := fun u => by
    rw [hβx u, map_mul, map_mul, map_inv]
  have hx2 : x' ^ 2 = 1 := by
    refine hfaith _ (pow_mem hx'G 2) ?_
    rintro _ ⟨h, hh, rfl⟩
    have h1 : (β (β ⟨h, hh⟩) : ModGL .E7 K) = h := by
      rw [← MulAut.mul_apply, ← sq, hβ, MulAut.one_apply]
    rw [hβx, hβx] at h1
    have h2 : x ^ 2 * h = h * x ^ 2 := by
      calc x ^ 2 * h = (x * (x * h * x⁻¹) * x⁻¹) * x ^ 2 := by rw [pow_two]; group
        _ = h * x ^ 2 := by rw [h1]
    rw [hx'def, ← map_pow, ← map_mul, ← map_mul, h2]
  have hx'F' : frobTwistGL .E7 Lk 3 1 1 x' = x' := by
    rw [hS]
    exact hx'F
  obtain ⟨r, hr, l, hl, g₁, hg₁, hg₁x, hg₁F⟩ :=
    exists_conj_toral_twist_E7 3 (by norm_num) le_rfl (x := x')
      (mem_fixedPointsIn.2 ⟨hx'G, hx'F'⟩) hx2
  set b : Fin Tag.E7.rank → Lkˣ := signCharTuple (k := Lk) (signMaskChar .E7 r.mask) with hbdef
  set t : ModGL .E7 Lk := rootDiagUnit .E7 b with htdef
  have hgt : g₁ * x' * g₁⁻¹ = t := hg₁x
  rcases eq_or_ne l [] with hlnil | hl0
  ·
    subst hlnil
    have hN1 : wordWeylMatrix .E7 Lk ([] : List (Fin Tag.E7.rank)) = 1 := by
      simp [wordWeylMatrix]
    have hFg : frobTwistGL .E7 Lk 3 1 1 g₁ = g₁ := by
      have h1 : g₁ * (frobTwistGL .E7 Lk 3 1 1 g₁)⁻¹ = 1 := by rw [hg₁F, hN1]
      exact (mul_inv_eq_one.1 h1).symm
    have hg₁R : g₁ ∈ R := by
      rw [← hReq]
      exact mem_fixedPointsIn.2 ⟨hg₁, hFg⟩
    have hb : ∀ i, b i = 1 ∨ b i = -1 := fun i =>
      signCharTuple_sign (k := Lk) (signMaskChar .E7 r.mask) i
    obtain ⟨b₀, hb₀⟩ := CFSG.LieType.Chevalley.OddE6AllInvolution.exists_sign_preimage ι hb
    have hsign : ∀ i, b₀ i = 1 ∨ b₀ i = -1 := by
      intro i
      have hi := congrFun hb₀ i
      rcases hb i with h | h
      · left
        rw [h] at hi
        apply Units.ext
        apply ι.injective
        simpa using congrArg Units.val hi
      · right
        rw [h] at hi
        apply Units.ext
        apply ι.injective
        simpa using congrArg Units.val hi
    have hb₀1 : b₀ ≠ 1 := by
      intro hb0one
      apply hβ1
      have hb1 : b = 1 := by
        funext i
        rw [← congrFun hb₀ i]
        simp [hb0one]
      have hx'1 : x' = 1 := by
        have h1 : g₁ * x' * g₁⁻¹ = 1 := by rw [hgt, htdef, hb1, rootDiagUnit_one]
        calc x' = g₁⁻¹ * (g₁ * x' * g₁⁻¹) * g₁ := by group
          _ = 1 := by rw [h1]; group
      apply MulEquiv.ext
      intro u
      apply Subtype.ext
      apply hinj
      rw [MulAut.one_apply, hβx' u, hx'1]
      simp
    obtain ⟨w₀, hw₀o, hw₀inv, hw₀g⟩ :=
      exists_rootDiag_inv_extraGood (τ := .E7) (Or.inr (Or.inr (Or.inl rfl))) hK b₀ hsign hb₀1
    have hstep3 : rootDiagUnit .E7 b₀ * (w₀ : ModGL .E7 K) * (rootDiagUnit .E7 b₀)⁻¹ =
        ((w₀⁻¹ : adjointGroup .E7 K) : ModGL .E7 K) := by
      rw [← coe_rootDiagAut b₀ w₀]
      exact congrArg Subtype.val hw₀inv
    have hinv : g₁ * x' * g₁⁻¹ * baseChangeGL ι (w₀ : ModGL .E7 K) *
        (g₁ * x' * g₁⁻¹)⁻¹ = (baseChangeGL ι (w₀ : ModGL .E7 K))⁻¹ := by
      rw [hgt, htdef, ← hb₀, ← baseChangeGL_rootDiagUnit ι b₀]
      rw [← map_mul, ← map_inv, ← map_mul, hstep3]
      exact map_inv (baseChangeGL (τ := Tag.E7) ι) (w₀ : ModGL .E7 K)
    obtain ⟨w, hw, hwo, hwg⟩ := exists_inv_of_injective_conj (baseChangeGL ι) hinj β x' hβx'
      (hRnorm hg₁R) (Q := fun w => orderOf w = 3 ∧ IsExtraGood w)
      (fun θ hθ w hw => ⟨(orderOf_injective θ hθ w).trans hw.1, hw.2.map hθ⟩)
      ⟨hw₀o, hw₀g⟩ hinv
    exact ⟨w, hwo, hw, hwg⟩
  ·
    obtain ⟨u, hu, hgood, htu⟩ :=
      exists_inv_extraGood_E7_twist_three (k := Lk) hr hl hl0
    have hcop : Nat.Coprime
        (((adjointGroup .E7 K).map (baseChangeGL ι)).subgroupOf R).index 3 := by
      have hne : (((adjointGroup .E7 K).map (baseChangeGL ι)).subgroupOf R).index ≠ 0 := by
        have : Finite R := hRfin
        exact Subgroup.index_ne_zero_of_finite
      have hle : (((adjointGroup .E7 K).map (baseChangeGL ι)).subgroupOf R).index ≤ 2 := hidx
      have h12 : (((adjointGroup .E7 K).map (baseChangeGL ι)).subgroupOf R).index = 1 ∨
          (((adjointGroup .E7 K).map (baseChangeGL ι)).subgroupOf R).index = 2 := by omega
      rcases h12 with h1 | h2
      · rw [h1]
        exact Nat.coprime_one_left 3
      · rw [h2]
        exact (Nat.coprime_primes Nat.prime_two Nat.prime_three).mpr (by norm_num)
    have hTR : ∀ v ∈ fixedPointsIn (adjointGroup .E7 Lk)
        (frobTwistGL .E7 Lk 3 1 (wordWeylMatrix .E7 Lk l)), g₁⁻¹ * v * g₁ ∈ R := by
      intro v hv
      have hv' : v ∈ fixedPointsIn (adjointGroup .E7 Lk)
          (frobTwistGL .E7 Lk 3 1 (wordWeylMatrix .E7 Lk l * 1)) := by
        rw [mul_one]
        exact hv
      have h := conj_mem_fixedPointsIn_of_cocycle (p := 3) (D := 1)
        (N := wordWeylMatrix .E7 Lk l) (g₁ := g₁) hg₁ hg₁F hv'
      rwa [hReq] at h
    have hinv : g₁ * x' * g₁⁻¹ * (u : ModGL .E7 Lk) * (g₁ * x' * g₁⁻¹)⁻¹ =
        (u : ModGL .E7 Lk)⁻¹ := by
      rw [hgt]
      exact htu
    exact exists_inv_extraGood_of_conj_index (baseChangeGL ι) hinj β x' hβx' (R := R) hHR hRnorm
      hcop (T := fixedPointsIn (adjointGroup .E7 Lk)
        (frobTwistGL .E7 Lk 3 1 (wordWeylMatrix .E7 Lk l))) (y := g₁) hTR hu hgood hinv

theorem involGood_E7_three {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3) :
    InvolGood (adjointGroup .E7 K) := by
  classical
  intro β hβ
  have hβ2 : β ^ 2 = 1 := by rw [← hβ, pow_orderOf_eq_one]
  have hβ1 : β ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hβ
    omega
  obtain ⟨-, -, hnf⟩ :=
    ordinary_E_exact_automorphism_normal_form .E7 (Or.inr (Or.inl rfl)) K
  obtain ⟨g, a, σ, ε, hgaσ⟩ := hnf β
  obtain ⟨-, -, -, -, hsq, hfacts⟩ :=
    ordinary_E_field_graph_quotient_and_involutions .E7 (Or.inr (Or.inl rfl)) K
  have hQ : exactQ Tag.E7 K ε = 1 := rfl
  have hβ' : ∀ u : adjointGroup Tag.E7 K, (β u : ModGL Tag.E7 K) = (g : ModGL Tag.E7 K) *
      rootDiagUnit Tag.E7 a * Units.map (entrywiseHom σ.toRingHom) (u : ModGL Tag.E7 K) *
        (rootDiagUnit Tag.E7 a)⁻¹ * (g : ModGL Tag.E7 K)⁻¹ := fun u => by
    rw [hgaσ u, hQ, inv_one, mul_one, mul_one]
  by_cases hσ : σ = 1
  · subst hσ
    have h1 : ∀ h : adjointGroup Tag.E7 K, Units.map (entrywiseHom (1 : K ≃+* K).toRingHom)
        (h : ModGL Tag.E7 K) = h := fun h => Units.ext (entrywise_id _)
    obtain ⟨x, hx, hinv, hgood⟩ := exists_inv_extraGood_inner_diagonal_E7 hK β hβ2 hβ1 g a
      fun h => by rw [hβ' h, h1 h]
    exact Or.inl ⟨x, hx, hinv, hgood⟩
  · exact (Nat.not_even_one (hfacts 3 1 Nat.prime_three le_rfl (by rw [hK, pow_one]) σ
      (hsq β g a σ ε hgaσ hβ2) hσ).1).elim

theorem involAt_E7 : InvolAt .E7 := by
  intro S _ _ n _ _ hS
  obtain ⟨-, hm⟩ := hS.chevalleyExceptionalModel (by decide)
  obtain ⟨K, _, _, hK, ⟨φ⟩⟩ := nonempty_mulEquiv_adjointGroup .E7 hm
  exact InvolGood.of_mulEquiv φ.symm (involGood_E7_three (by rw [hK, pow_one]))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three
