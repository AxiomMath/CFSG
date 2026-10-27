module

public import CFSG.LocalAnalysis.StandardType.GGStdSubIOneProperMoreE6
public import CFSG.LocalAnalysis.StandardType.GGTableBE6TwoPilotToral
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeTwoTorus

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace IOneMore

open TableBExc

variable
  {K : Type} [Field K] [Finite K]

theorem units_eq_one_of_card_two {r : ℕ} (hK : Nat.card K = 2) (a : Fin r → Kˣ) : a = 1 := by
  have : Fintype K := Fintype.ofFinite K
  funext i
  apply Units.ext
  have h := FiniteField.pow_card_sub_one_eq_one ((a i : Kˣ) : K) (a i).ne_zero
  rw [← Nat.card_eq_fintype_card, hK] at h
  simpa using h

theorem recipeID_E6_subset_inn_two (hK : Nat.card K = 2) :
    RecipeID .E6 K ⊆
      Set.range (MulAut.conj : RecipeGroup .E6 K →* MulAut (RecipeGroup .E6 K)) := by
  have hle : Subgroup.closure (LargeEvenInnSet (RecipeGroup .E6 K) ∪
      LargeEvenChevDiagImage Tag.E6.cartan K (LargeEvenChevH Tag.E6.cartan K false)) ≤
      (MulAut.conj : RecipeGroup .E6 K →* MulAut (RecipeGroup .E6 K)).range := by
    rw [Subgroup.closure_le]
    rintro ψ (hψ | hψ)
    · exact hψ
    · obtain ⟨a, ha⟩ := TableB.exists_isDiagOf hψ
      have ha1 : a = 1 := units_eq_one_of_card_two hK a
      subst ha1
      have hmem : TableB.diagHom Tag.E6.cartan K 1 ∈ LargeEvenChevH Tag.E6.cartan K false := by
        rw [map_one]
        exact one_mem _
      rw [TableB.isDiagOf_eq_conj ha hmem]
      exact ⟨_, rfl⟩
  exact fun φ hφ => hle hφ

theorem mem_range_conj_adjointE6_two (hK : Nat.card K = 2)
    {φ : MulAut (adjointGroup .E6 K)} (hφ : φ ^ 3 = 1) :
    φ ∈ (MulAut.conj : adjointGroup .E6 K →* MulAut (adjointGroup .E6 K)).range := by
  obtain ⟨Θ, -, -, hker, -, -⟩ := ordinary_E_field_graph_quotient_and_involutions .E6
    (Or.inl rfl) K
  have hcard : Nat.card (K ≃+* K) = 1 := by
    obtain ⟨-, -, -, -, hc, -⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
        Nat.prime_two (le_refl 1) (by rw [hK, pow_one])
    exact hc
  have hsq : ∀ y : Multiplicative (ZMod (exactE .E6)), y ^ 2 = 1 := by
    have h0 : ∀ z : ZMod 2, z + z = 0 := by decide
    intro y
    rw [pow_two]
    exact congrArg Multiplicative.ofAdd (h0 (Multiplicative.toAdd y))
  have h1 : (Θ φ).1 = 1 := by
    have : Subsingleton (K ≃+* K) := (Nat.card_eq_one_iff_unique.mp hcard).1
    exact Subsingleton.elim _ _
  have h2 : (Θ φ).2 = 1 := by
    refine eq_one_of_sq_of_pow_odd (p := 3) (by decide) (hsq _) ?_
    rw [← Prod.pow_snd, ← map_pow, hφ, map_one, Prod.snd_one]
  obtain ⟨g, a, hga⟩ := (hker _).1 (Prod.ext h1 h2)
  have hα : φ = MulAut.conj g * exactNormalAut .E6 K a 1 0 :=
    eq_conj_mul_exactNormalAut_of_apply (σ := 1) (ε := 0) fun h => by
      rw [hga h, exactQ_zero, AutSt.units_map_entrywiseHom_one, inv_one, mul_one, mul_one]
  have ha1 : a = 1 := units_eq_one_of_card_two hK a
  have hN : exactNormalAut .E6 K a 1 0 = 1 := by
    rw [ha1]
    exact map_one (AutSt.e6DiagHom K)
  rw [hα, hN, mul_one]
  exact ⟨g, rfl⟩

theorem mem_range_conj_recipeE6_two (hK : Nat.card K = 2) {φ : MulAut (RecipeGroup .E6 K)}
    (hφ : φ ^ 3 = 1) :
    φ ∈ (MulAut.conj : RecipeGroup .E6 K →* MulAut (RecipeGroup .E6 K)).range := by
  set e := recipeEquiv .E6 K with he
  have h1 : (MulAut.congr e φ) ^ 3 = 1 := by rw [← map_pow, hφ, map_one]
  obtain ⟨g, hg⟩ := mem_range_conj_adjointE6_two hK h1
  refine ⟨e.symm g, ?_⟩
  ext x
  have h2 := congrArg (fun χ : MulAut (adjointGroup .E6 K) => χ (e x)) hg
  simp only [MulAut.conj_apply, MulAut.congr_apply, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply] at h2
  rw [MulAut.conj_apply]
  apply e.injective
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, h2]

theorem ggIRankLe_E6_two
    (hK : Nat.card K = 2) : GGIRankLe 3 4 (RecipeGroup .E6 K) (RecipeID .E6 K) := by
  have : CharP K 2 := charP_two_of_card (m := 1) (by rw [hK, pow_one])
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  refine ggIRankLe_of_card_le fun X hXI hX => ?_
  have := finite_recipeGroup .E6 K
  obtain ⟨A, hA, hAc⟩ := TableBSymp.exists_of_subset_inn (center_recipeGroup_eq_bot .E6 K)
    (fun φ hφ => recipeID_E6_subset_inn_two hK (hXI hφ)) hX
  rw [← hAc]
  set A' := A.map (recipeEquiv .E6 K).toMonoidHom with hA'
  have hA'c : Nat.card A' = Nat.card A :=
    Subgroup.card_map_of_injective (recipeEquiv .E6 K).injective
  rw [← hA'c]
  by_contra hlt
  push Not at hlt
  obtain ⟨e, he⟩ := E6ThreeEnd.ggE6TwoToralInput_holds K h2 hK A'
    (TableB.isElemAbelian_map hA _) hlt.le
  have h1 : Nat.card (A'.map e.toMonoidHom) = Nat.card A' :=
    Subgroup.card_map_of_injective e.injective
  have h3 : Nat.card (TableBExc.E6Three.torusE6Two (K := K) h2).range = 3 ^ 4 := by
    rw [MonoidHom.range_eq_map,
      Subgroup.card_map_of_injective (TableBExc.E6Three.torusE6Two_injective h2),
      Subgroup.card_top]
    change Nat.card (Fin 4 → ZMod 3) = _
    rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  rw [he, h3] at h1
  omega

end IOneMore

open IOneMore

section Labels


@[expose] def GGIOneMoreE6TwoLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .E6 ∧ lab.n = 1 ∧ p = 3

theorem largeEvenLabelAll_bstarEq_e6Two {p : ℕ} {lab : LargeEvenLabel}
    (h : GGIOneMoreE6TwoLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => (∃ r, GGTorusLift p r R ∧ GGInnerDiagBound p r R I) ∧
      ∃ r, GGTorusLift p r R ∧ GGIRankLe p r R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, hn, rfl⟩ := h
  dsimp only at htag hn
  subst htag hn
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hq⟩ := hQ
  have hK2 : Nat.card K = 2 := by rw [hK, pow_one]
  have : CharP K 2 := charP_two_of_card hK
  have hlift := TableBExc.E6Three.ggTorusLift_E6_two (K := K)
  exact ⟨K, i1, i2, hK, hq, ⟨4, hlift, ggInnerDiagBound_of_forall_mem fun φ hφ =>
    Subgroup.subset_closure (Or.inl (mem_range_conj_recipeE6_two hK2 hφ))⟩, 4, hlift,
    ggIRankLe_E6_two hK2⟩

theorem ggStdSubIOneProperInputOn_e6Two (ha₀ : GGLNoncyclicInput) :
    GGStdSubIOneProperInputOn GGIOneMoreE6TwoLabel :=
  ggStdSubIOneProperInputOn_of_bstarEq ha₀ fun _ _ _ _ h _ => largeEvenLabelAll_bstarEq_e6Two h

end Labels

end CFSG.StandardType
