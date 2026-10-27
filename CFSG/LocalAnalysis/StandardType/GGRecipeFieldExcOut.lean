module

public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExc
public import CFSG.LocalAnalysis.StandardType.MarkingChevalley
public import CFSG.LieType.Chevalley.EvenE7E8AutomorphismNormalForm
public import CFSG.LieType.Chevalley.EvenF4AutomorphismNormalForm
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenAutomorphisms

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem commutator_mem_inn_of_hom {Y : Type*} [Group Y] {Q : Type*} [Group Q]
    (hQ : ∀ x y : Q, x * y = y * x) (Θ : MulAut Y →* Q)
    (hker : Θ.ker = (MulAut.conj : Y →* MulAut Y).range) (α β : MulAut Y) :
    α * β * α⁻¹ * β⁻¹ ∈ (MulAut.conj : Y →* MulAut Y).range := by
  rw [← hker, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hQ (Θ α) (Θ β)]
  group

theorem commutator_mem_inn_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : ∀ α β : MulAut Y, α * β * α⁻¹ * β⁻¹ ∈ (MulAut.conj : Y →* MulAut Y).range)
    (α β : MulAut X) : α * β * α⁻¹ * β⁻¹ ∈ (MulAut.conj : X →* MulAut X).range := by
  obtain ⟨y, hy⟩ := h (MulAut.congr e α) (MulAut.congr e β)
  refine ⟨e.symm y, (MulAut.congr e).injective ?_⟩
  rw [mulAut_congr_conj, MulEquiv.apply_symm_apply, hy, map_mul, map_mul, map_mul, map_inv,
    map_inv]


@[expose] noncomputable def recipeChevEquiv (τ : Tag) (K : Type) [Field K] [Finite K] :
    LargeEvenCenterQuot (LargeEvenChevH τ.cartan K false) ≃* adjointGroup τ K :=
  (Classical.choice (centerQuot_chevGroup_equiv K τ)).trans
    ((QuotientGroup.quotientMulEquivOfEq (center_adjointGroup_eq_bot (τ := τ) (K := K))).trans
      QuotientGroup.quotientBot)

theorem ggRawFieldCentral_chev (τ : Tag) {K : Type} [Field K] [Finite K]
    (h : ∀ α β : MulAut (adjointGroup τ K),
      α * β * α⁻¹ * β⁻¹ ∈ (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)).range) :
    GGRawFieldCentral (LargeEvenCenterQuot (LargeEvenChevH τ.cartan K false))
      (LargeEvenChevIDImage τ.cartan K _) (LargeEvenChevFieldImage τ.cartan K _) :=
  ggRawFieldCentral_of_commutator_mem fun α β => by
    obtain ⟨r, hr⟩ := commutator_mem_inn_of_mulEquiv (recipeChevEquiv τ K) h α β
    rw [← hr]
    exact conj_mem_chevIDImage _ r

theorem commutator_mem_inn_E7_E8 {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ f) (τ : Tag) (hτ : τ = .E7 ∨ τ = .E8)
    (α β : MulAut (adjointGroup τ K)) :
    α * β * α⁻¹ * β⁻¹ ∈ (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)).range := by
  obtain ⟨-, Θ, -, -, hker, -⟩ := even_E7_E8_exact_inner_field_automorphism_normal_form hf K hK τ hτ
  exact commutator_mem_inn_of_hom ringEquiv_mul_comm_of_finite Θ hker α β

theorem commutator_mem_inn_G2 {f : ℕ} (hf : 2 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ f) (α β : MulAut (adjointGroup .G2 K)) :
    α * β * α⁻¹ * β⁻¹ ∈ (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)).range := by
  obtain ⟨-, Θ, -, -, hker, -⟩ :=
    CFSG.ComponentClassification.UnbalancedCatalog.even_G2_exact_automorphism_normal_form hf K hK
  exact commutator_mem_inn_of_hom ringEquiv_mul_comm_of_finite Θ hker α β

theorem commutator_mem_inn_F4 {f : ℕ} (hf : 1 ≤ f) (K : Type)
    [Field K] [Finite K] (hK : Nat.card K = 2 ^ f) (α β : MulAut (adjointGroup .F4 K)) :
    α * β * α⁻¹ * β⁻¹ ∈ (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)).range := by
  have : CharP K CFSG.LieType.Ree.ReeTag.F4.prime := charP_two_of_card hK
  obtain ⟨-, -, ⟨Θ, -, -, hker⟩, -⟩ := even_F4_exact_automorphism_normal_form hf K hK
  exact commutator_mem_inn_of_hom (fun x y => mul_comm x y) Θ hker α β

@[expose] def GGRecipeExcOutLabel (lab : LargeEvenLabel) : Prop :=
  lab.tag = .G2 ∨ lab.tag = .F4 ∨ lab.tag = .E7 ∨ lab.tag = .E8

theorem ggRawFieldCentralOn_excOut :
    GGRawFieldCentralOn GGRecipeExcOutLabel := by
  intro lab hlab hS Q hQ
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hn, hl⟩ := hlab
  rcases hS with ht | ht | ht | ht <;> dsimp only at ht <;> subst ht
  · obtain ⟨-, hn2⟩ := hl
    exact recipeChevalley_and (fun K _ _ hK =>
      ggRawFieldCentral_chev .G2 (commutator_mem_inn_G2 hn2 K hK)) hQ
  · exact recipeChevalley_and (fun K _ _ hK =>
      ggRawFieldCentral_chev .F4 (commutator_mem_inn_F4 hn K hK)) hQ
  · exact recipeChevalley_and (fun K _ _ hK =>
      ggRawFieldCentral_chev .E7 (commutator_mem_inn_E7_E8 hn K hK .E7 (Or.inl rfl))) hQ
  · exact recipeChevalley_and (fun K _ _ hK =>
      ggRawFieldCentral_chev .E8 (commutator_mem_inn_E7_E8 hn K hK .E8 (Or.inr rfl))) hQ

end CFSG.StandardType

end
