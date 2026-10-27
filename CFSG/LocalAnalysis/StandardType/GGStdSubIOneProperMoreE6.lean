module

public import CFSG.LocalAnalysis.StandardType.GGStdSubIOneProperMoreLabels
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6Aut
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTorus

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace IOneMore

open TableBExc

variable
  {K : Type} [Field K]

theorem mem_range_conj_adjointE6_of_pow [Finite K] {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hpf : ¬ p ∣ f)
    {φ : MulAut (adjointGroup .E6 K)} (hφ : φ ^ p = 1) :
    φ ∈ (MulAut.conj : adjointGroup .E6 K →* MulAut (adjointGroup .E6 K)).range := by
  obtain ⟨Θ, -, -, hker, -, -⟩ := ordinary_E_field_graph_quotient_and_involutions .E6
    (Or.inl rfl) K
  have hcard : Nat.card (K ≃+* K) = f := by
    obtain ⟨-, -, -, -, hc, -⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
        Nat.prime_two hf hK
    exact hc
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hsq : ∀ y : Multiplicative (ZMod (exactE .E6)), y ^ 2 = 1 := by
    have h0 : ∀ z : ZMod 2, z + z = 0 := by decide
    intro y
    rw [pow_two]
    exact congrArg Multiplicative.ofAdd (h0 (Multiplicative.toAdd y))
  have h1 : (Θ φ).1 = 1 := by
    have e1 : (Θ φ).1 ^ p = 1 := by rw [← Prod.pow_fst, ← map_pow, hφ, map_one, Prod.fst_one]
    have e2 : (Θ φ).1 ^ f = 1 := by
      rw [← hcard]
      exact pow_card_eq_one'
    have hcop : Nat.Coprime p f := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpf
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one e1)
      (orderOf_dvd_of_pow_eq_one e2))
  have h2 : (Θ φ).2 = 1 := by
    refine eq_one_of_sq_of_pow_odd hodd (hsq _) ?_
    rw [← Prod.pow_snd, ← map_pow, hφ, map_one, Prod.snd_one]
  have hΘ1 : Θ φ = 1 := Prod.ext h1 h2
  obtain ⟨g, a, hga⟩ := (hker _).1 hΘ1
  have hα : φ = MulAut.conj g * exactNormalAut .E6 K a 1 0 :=
    eq_conj_mul_exactNormalAut_of_apply (σ := 1) (ε := 0) fun h => by
      rw [hga h, exactQ_zero, AutSt.units_map_entrywiseHom_one, inv_one, mul_one, mul_one]
  obtain ⟨k, -, hk⟩ := Nat.exists_mul_mod_eq_one_of_coprime
    ((Nat.coprime_primes Nat.prime_three hp).2 (Ne.symm hp3)) hp.one_lt
  rw [← pow_mul_eq_self_of_mod hk hφ, pow_mul]
  exact Subgroup.pow_mem _ (pow_three_mem_inn_of_eq hα) k

theorem mem_range_conj_recipeE6_of_pow [Finite K] {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hpf : ¬ p ∣ f)
    {φ : MulAut (RecipeGroup .E6 K)} (hφ : φ ^ p = 1) :
    φ ∈ (MulAut.conj : RecipeGroup .E6 K →* MulAut (RecipeGroup .E6 K)).range := by
  set e := recipeEquiv .E6 K with he
  have h1 : (MulAut.congr e φ) ^ p = 1 := by rw [← map_pow, hφ, map_one]
  obtain ⟨g, hg⟩ := mem_range_conj_adjointE6_of_pow hf hK hp hp2 hp3 hpf h1
  refine ⟨e.symm g, ?_⟩
  ext x
  have h2 := congrArg (fun χ : MulAut (adjointGroup .E6 K) => χ (e x)) hg
  simp only [MulAut.conj_apply, MulAut.congr_apply, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply] at h2
  rw [MulAut.conj_apply]
  apply e.injective
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, h2]

theorem ggIRankLe_E6 [Finite K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hpq : p ∣ Nat.card K - 1) : GGIRankLe p 6 (RecipeGroup .E6 K) (RecipeID .E6 K) := by
  refine ggIRankLe_of_card_le fun X hXI hX => ?_
  have := finite_recipeGroup .E6 K
  obtain ⟨A', hA', hA'c⟩ := TableBSymp.exists_of_subset_inn (center_recipeGroup_eq_bot .E6 K)
    (fun φ hφ => ggOutdiagPrime_E6 hp hp3 φ (hXI hφ) (hX.2 φ hφ)) hX
  have hV : Nat.card (torusPow .E6 K p) = p ^ Tag.E6.rank := card_torusPow_E6 hp hp3 hpq
  have h3 := (ggExcToralRankInput_E6_of_ne_three hp hp2 hp3 hpq).card_le hV
    (E := A'.map (recipeEquiv .E6 K).toMonoidHom) (TableB.isElemAbelian_map hA' _)
  rw [Subgroup.card_map_of_injective (recipeEquiv .E6 K).injective] at h3
  rw [← hA'c]
  exact h3

theorem bstarEq_data_E6 [Finite K] [CharP K 2] {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) (hpq : p ∣ Nat.card K - 1) (hpf : ¬ p ∣ f) :
    (∃ r, GGTorusLift p r (RecipeGroup .E6 K) ∧
        GGInnerDiagBound p r (RecipeGroup .E6 K) (RecipeID .E6 K)) ∧
      ∃ r, GGTorusLift p r (RecipeGroup .E6 K) ∧
        GGIRankLe p r (RecipeGroup .E6 K) (RecipeID .E6 K) := by
  have hp2 : p ≠ 2 := ne_two_of_dvd_two_pow_sub_one hf (hK ▸ hpq)
  have hlift := ggTorusLift_E6 hp hp2 hp3 hpq
  exact ⟨⟨6, hlift, ggInnerDiagBound_of_forall_mem fun φ hφ =>
    Subgroup.subset_closure (Or.inl (mem_range_conj_recipeE6_of_pow hf hK hp hp2 hp3 hpf hφ))⟩,
    6, hlift, ggIRankLe_E6 hp hp2 hp3 hpq⟩

end IOneMore

open IOneMore

section Labels


@[expose] def GGIOneMoreE6CoprimeLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .E6 ∧ p ∣ 2 ^ lab.n - 1 ∧ p ≠ 3 ∧ ¬ p ∣ lab.n

theorem largeEvenLabelAll_bstarEq_e6Coprime {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGIOneMoreE6CoprimeLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => (∃ r, GGTorusLift p r R ∧ GGInnerDiagBound p r R I) ∧
      ∃ r, GGTorusLift p r R ∧ GGIRankLe p r R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, hpn, hp3, hpn'⟩ := h
  dsimp only at htag hpn hp3 hpn'
  subst htag
  have hn : 1 ≤ n := hlab.1
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hq⟩ := hQ
  have : CharP K 2 := charP_two_of_card hK
  have hpq : p ∣ Nat.card K - 1 := by rw [hK]; exact hpn
  exact ⟨K, i1, i2, hK, hq, bstarEq_data_E6 hn hK hp hp3 hpq hpn'⟩

theorem ggStdSubIOneProperInputOn_e6Coprime (ha₀ : GGLNoncyclicInput) :
    GGStdSubIOneProperInputOn GGIOneMoreE6CoprimeLabel :=
  ggStdSubIOneProperInputOn_of_bstarEq ha₀ fun _ _ hp hlab h _ =>
    largeEvenLabelAll_bstarEq_e6Coprime hp hlab h

end Labels

end CFSG.StandardType
