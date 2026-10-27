module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.ExcTransport
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.ExcTorus
public import CFSG.LieType.Chevalley.CLSOddE6AllInvolutionFourGroup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.LieType.AlgebraicGroups
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)


theorem exists_inv_good_inner_diagonal {τ : Tag} (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E8)
    {K : Type} [Field K] [Finite K] {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) [CharP K p]
    (hK : Nat.card K = p ^ e) (h3 : 3 < p ^ e) (β : MulAut (adjointGroup τ K)) (hβ : β ^ 2 = 1)
    (hβ1 : β ≠ 1) (g : adjointGroup τ K) (a : Fin τ.rank → Kˣ)
    (hexpr : ∀ h : adjointGroup τ K, (β h : ModGL τ K) =
      (g : ModGL τ K) * rootDiagUnit τ a * h * (rootDiagUnit τ a)⁻¹ * (g : ModGL τ K)⁻¹) :
    ∃ x : adjointGroup τ K, orderOf x = p ∧ β x = x⁻¹ ∧ IsSpecialGood p x := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hKodd : Odd (Nat.card K) := by
    rw [hK]
    exact (hp.odd_of_ne_two hp2).pow
  set Lk := AlgebraicClosure K
  set ι : K →+* Lk := algebraMap K Lk with hιdef
  set p' := ringChar K with hp'def
  obtain ⟨e', hpp, hcardK⟩ := by
    letI : CharP K p' := ringChar.charP K
    exact FiniteField.card K p'
  obtain ⟨Fr, hFr⟩ : ∃ Fr : Lk →+* Lk, ∀ c, Fr c = c ^ Nat.card K := by
    have : Fact p'.Prime := ⟨hpp⟩
    have : CharP K p' := ringChar.charP K
    have : CharP Lk p' := charP_of_injective_algebraMap (algebraMap K Lk).injective p'
    refine ⟨iterateFrobenius Lk p' e', fun c => ?_⟩
    rw [iterateFrobenius_def, Nat.card_eq_fintype_card, hcardK]
  obtain ⟨hinj, hHG, hfaith, -⟩ :=
    exceptional_Lang_finite_root_centralizer_faithfulness τ K hKodd Lk ι
  obtain ⟨-, -, hRnorm, -⟩ :=
    exceptional_Lang_Frobenius_fixed_derived_root_group τ K hKodd Lk Fr hFr
  set x : ModGL τ K := (g : ModGL τ K) * rootDiagUnit τ a with hxdef
  set x' := baseChangeGL ι x with hx'def
  have hx'G : x' ∈ adjointGroup τ Lk := by
    rw [hx'def, hxdef, map_mul, baseChangeGL_rootDiagUnit]
    exact mul_mem (hHG ⟨_, g.2, rfl⟩) (exceptional_Lang_adjoint_diagonal_lift τ Lk _).1
  have hx'F : Units.map (entrywiseHom Fr) x' = x' :=
    units_map_entrywiseHom_baseChangeGL_algebraMap Fr hFr x
  have hβx : ∀ h : adjointGroup τ K, (β h : ModGL τ K) = x * h * x⁻¹ := fun h => by
    rw [hexpr h, hxdef, mul_inv_rev]
    group
  have hβx' : ∀ u : adjointGroup τ K, baseChangeGL ι (β u : ModGL τ K) =
      x' * baseChangeGL ι (u : ModGL τ K) * x'⁻¹ := fun u => by
    rw [hβx u, map_mul, map_mul, map_inv]
  have hx2 : x' ^ 2 = 1 := by
    refine hfaith _ (pow_mem hx'G 2) ?_
    rintro _ ⟨h, hh, rfl⟩
    have h1 : (β (β ⟨h, hh⟩) : ModGL τ K) = h := by
      rw [← MulAut.mul_apply, ← sq, hβ, MulAut.one_apply]
    rw [hβx, hβx] at h1
    have h2 : x ^ 2 * h = h * x ^ 2 := by
      calc x ^ 2 * h = (x * (x * h * x⁻¹) * x⁻¹) * x ^ 2 := by rw [pow_two]; group
        _ = h * x ^ 2 := by rw [h1]
    rw [hx'def, ← map_pow, ← map_mul, ← map_mul, h2]
  obtain ⟨h, hhR, b, hb, hhx, -⟩ :=
    G2_F4_E6_E8_rational_inner_diagonal_involution_fixed_p_components τ K Lk hτ hKodd Fr hFr
      ⟨hx'G, hx'F⟩ hx2
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
      have h1 : h * x' * h⁻¹ = 1 := by rw [hhx, hb1, rootDiagUnit_one]
      calc x' = h⁻¹ * (h * x' * h⁻¹) * h := by group
        _ = 1 := by rw [h1]; group
    apply MulEquiv.ext
    intro u
    apply Subtype.ext
    apply hinj
    rw [MulAut.one_apply, hβx' u, hx'1]
    simp
  have hτ5 : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by tauto
  obtain ⟨w₀, hw₀o, hw₀inv, hw₀g⟩ :=
    exists_rootDiag_inv_good (K := K) (p := p) (e := e) hτ5 hp hp2 hK h3 b₀ hsign hb₀1
  have hstep3 : rootDiagUnit τ b₀ * (w₀ : ModGL τ K) * (rootDiagUnit τ b₀)⁻¹ =
      ((w₀⁻¹ : adjointGroup τ K) : ModGL τ K) := by
    rw [← coe_rootDiagAut b₀ w₀]
    exact congrArg Subtype.val hw₀inv
  have hinv : h * x' * h⁻¹ * baseChangeGL ι (w₀ : ModGL τ K) *
      (h * x' * h⁻¹)⁻¹ = (baseChangeGL ι (w₀ : ModGL τ K))⁻¹ := by
    rw [hhx, ← hb₀, ← baseChangeGL_rootDiagUnit ι b₀]
    rw [← map_mul, ← map_inv, ← map_mul, hstep3]
    exact map_inv (baseChangeGL (τ := τ) ι) (w₀ : ModGL τ K)
  exact exists_inv_good_of_injective_conj (baseChangeGL (τ := τ) ι) hinj β x' hβx'
    (hRnorm hhR) hw₀o hw₀g hinv

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive
