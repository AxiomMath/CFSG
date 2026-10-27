module

public import CFSG.LocalAnalysis.StandardType.GGStdSubIOneProperRestDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBExcThreeE8
public import CFSG.LocalAnalysis.StandardType.GGTableBF4Three

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

namespace IOneRest

open TableBExc

variable
  {τ : Tag} {K : Type} [Field K] [Finite K]

omit [Finite K] in
theorem mem_range_conj_adjoint_of_pow (hτ : τ = .E7 ∨ τ = .E8) {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) {p : ℕ} (hp : p.Prime) (hpf : ¬ p ∣ f)
    {φ : MulAut (adjointGroup τ K)} (hφ : φ ^ p = 1) :
    φ ∈ (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)).range := by
  obtain ⟨-, Θ, -, -, hker, -⟩ :=
    even_E7_E8_exact_inner_field_automorphism_normal_form hf K hK τ hτ
  have hcard : Nat.card (K ≃+* K) = f := by
    obtain ⟨-, -, -, -, hc, -⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
        Nat.prime_two hf hK
    exact hc
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  have h1 : (Θ φ) ^ p = 1 := by rw [← map_pow, hφ, map_one]
  have h2 : (Θ φ) ^ f = 1 := by
    rw [← hcard]
    exact pow_card_eq_one'
  have hcop : Nat.Coprime p f := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpf
  have h3 : orderOf (Θ φ) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h2)
  have hk : φ ∈ Θ.ker := by
    rw [MonoidHom.mem_ker, ← orderOf_eq_one_iff]
    exact h3
  rwa [hker] at hk

theorem mem_range_conj_recipe_of_pow (hτ : τ = .E7 ∨ τ = .E8) {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) {p : ℕ} (hp : p.Prime) (hpf : ¬ p ∣ f)
    {φ : MulAut (RecipeGroup τ K)} (hφ : φ ^ p = 1) :
    φ ∈ (MulAut.conj : RecipeGroup τ K →* MulAut (RecipeGroup τ K)).range := by
  set e := recipeEquiv τ K with he
  have h1 : (MulAut.congr e φ) ^ p = 1 := by rw [← map_pow, hφ, map_one]
  obtain ⟨g, hg⟩ := mem_range_conj_adjoint_of_pow hτ hf hK hp hpf h1
  refine ⟨e.symm g, ?_⟩
  ext x
  have h2 := congrArg (fun χ : MulAut (adjointGroup τ K) => χ (e x)) hg
  simp only [MulAut.conj_apply, MulAut.congr_apply, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply] at h2
  rw [MulAut.conj_apply]
  apply e.injective
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, h2]

theorem ggIRankLe_E7E8 [CharP K 2] (hτ : τ = .E7 ∨ τ = .E8) {p : ℕ} (hp : p.Prime)
    (hpq : p ∣ Nat.card K - 1) (hT : GGExcToralRankInput τ K p) :
    GGIRankLe p τ.rank (RecipeGroup τ K) (RecipeID τ K) := by
  refine ggIRankLe_of_card_le fun X hXI hX => ?_
  have := finite_recipeGroup τ K
  have hinn : RecipeID τ K ⊆
      Set.range (MulAut.conj : RecipeGroup τ K →* MulAut (RecipeGroup τ K)) := by
    rcases hτ with rfl | rfl
    · exact idImage_subset_inn_E7 K
    · exact idImage_subset_inn_E8 K
  obtain ⟨A', hA', hA'c⟩ := TableBSymp.exists_of_subset_inn (center_recipeGroup_eq_bot τ K)
    (fun φ hφ => hinn (hXI hφ)) hX
  have hV : Nat.card (torusPow τ K p) = p ^ τ.rank := by
    rcases hτ with rfl | rfl
    · exact card_torusPow_E7 hp hpq
    · exact card_torusPow_E8 hp hpq
  have h3 := hT.card_le hV (E := A'.map (recipeEquiv τ K).toMonoidHom)
    (TableB.isElemAbelian_map hA' _)
  rw [Subgroup.card_map_of_injective (recipeEquiv τ K).injective] at h3
  rw [← hA'c]
  exact h3

theorem ggExcToralRankInput_E7E8 [CharP K 2] (hτ : τ = .E7 ∨ τ = .E8) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1) : GGExcToralRankInput τ K p := by
  by_cases hp3 : p = 3
  · subst hp3
    rcases hτ with rfl | rfl
    · exact TableBExc.Three.ggExcToralRankInput_E7_three hpq
    · exact TableBExc.Three.ggExcToralRankInput_E8_three hpq
  · rcases hτ with rfl | rfl
    · exact ggExcToralRankInput_E7_of_ne_three hp hp2 hp3 hpq
    · exact ggExcToralRankInput_E8_of_ne_three hp hp2 hp3 hpq

theorem bstarEq_data_E7E8 [CharP K 2] (hτ : τ = .E7 ∨ τ = .E8) {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) {p : ℕ} (hp : p.Prime) (hpq : p ∣ Nat.card K - 1)
    (hpf : ¬ p ∣ f) :
    (∃ r, GGTorusLift p r (RecipeGroup τ K) ∧
        GGInnerDiagBound p r (RecipeGroup τ K) (RecipeID τ K)) ∧
      ∃ r, GGTorusLift p r (RecipeGroup τ K) ∧ GGIRankLe p r (RecipeGroup τ K) (RecipeID τ K) := by
  have hp2 : p ≠ 2 := ne_two_of_dvd_two_pow_sub_one hf (hK ▸ hpq)
  have hlift : GGTorusLift p τ.rank (RecipeGroup τ K) := by
    rcases hτ with rfl | rfl
    · exact ggTorusLift_E7 hp hp2 hpq
    · exact ggTorusLift_E8 hp hp2 hpq
  refine ⟨⟨τ.rank, hlift, ggInnerDiagBound_of_forall_mem fun φ hφ =>
    Subgroup.subset_closure (Or.inl (mem_range_conj_recipe_of_pow hτ hf hK hp hpf hφ))⟩,
    τ.rank, hlift, ggIRankLe_E7E8 hτ hp hpq (ggExcToralRankInput_E7E8 hτ hp hp2 hpq)⟩

section F4


theorem mem_range_conj_adjointF4_of_pow [CharP K 2] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpf : ¬ p ∣ f)
    {φ : MulAut (adjointGroup CFSG.LieType.Ree.ReeTag.F4.tag K)} (hφ : φ ^ p = 1) :
    φ ∈ (MulAut.conj : adjointGroup CFSG.LieType.Ree.ReeTag.F4.tag K →*
      MulAut (adjointGroup CFSG.LieType.Ree.ReeTag.F4.tag K)).range := by
  obtain ⟨-, -, ⟨Θ, -, -, hker⟩, -⟩ := even_F4_exact_automorphism_normal_form hf K hK
  have hc : Nat.card (Multiplicative (ZMod (2 * f))) = 2 * f := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  have : Finite (Multiplicative (ZMod (2 * f))) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; omega)
  have h1 : (Θ φ) ^ p = 1 := by rw [← map_pow, hφ, map_one]
  have h2 : (Θ φ) ^ (2 * f) = 1 := by
    have h := pow_card_eq_one' (G := Multiplicative (ZMod (2 * f))) (x := Θ φ)
    rwa [hc] at h
  have hcop : Nat.Coprime p (2 * f) := Nat.Coprime.mul_right
    ((Nat.coprime_primes hp Nat.prime_two).mpr hp2) ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpf)
  have h3 : orderOf (Θ φ) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h2)
  have hk : φ ∈ Θ.ker := by
    rw [MonoidHom.mem_ker, ← orderOf_eq_one_iff]
    exact h3
  rwa [hker] at hk

theorem mem_range_conj_recipeF4_of_pow [CharP K 2] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpf : ¬ p ∣ f)
    {φ : MulAut (TableBF4.RecipeGroup K)} (hφ : φ ^ p = 1) :
    φ ∈ (MulAut.conj : TableBF4.RecipeGroup K →* MulAut (TableBF4.RecipeGroup K)).range := by
  set e := TableBF4.recipeEquiv K with he
  have h1 : (MulAut.congr e φ) ^ p = 1 := by rw [← map_pow, hφ, map_one]
  obtain ⟨g, hg⟩ : ∃ g : adjointGroup .F4 K, MulAut.conj g = MulAut.congr e φ :=
    mem_range_conj_adjointF4_of_pow hf hK hp hp2 hpf h1
  refine ⟨e.symm g, ?_⟩
  ext x
  have h2 := congrArg (fun χ : MulAut (adjointGroup .F4 K) => χ (e x)) hg
  simp only [MulAut.conj_apply, MulAut.congr_apply, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply] at h2
  rw [MulAut.conj_apply]
  apply e.injective
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, h2]

theorem ggIRankLe_F4 {p : ℕ} (hp : p.Prime) (hpq : p ∣ Nat.card K - 1)
    (hT : GGF4ToralRankInput K p) :
    GGIRankLe p 4 (TableBF4.RecipeGroup K) (TableBF4.RecipeID K) := by
  refine ggIRankLe_of_card_le fun X hXI hX => ?_
  have := TableBF4.finite_recipeGroup (K := K)
  obtain ⟨A', hA', hA'c⟩ := TableBSymp.exists_of_subset_inn (TableBF4.center_recipeGroup_eq_bot K)
    (fun φ hφ => TableBF4.idImage_subset_inn K (hXI hφ)) hX
  have h3 := hT.card_le hp hpq (E := A'.map (TableBF4.recipeEquiv K).toMonoidHom)
    (TableB.isElemAbelian_map hA' _)
  rw [Subgroup.card_map_of_injective (TableBF4.recipeEquiv K).injective] at h3
  rw [← hA'c]
  exact h3

theorem bstarEq_data_F4 [CharP K 2] {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) {p : ℕ}
    (hp : p.Prime) (hpq : p ∣ Nat.card K - 1) (hpf : ¬ p ∣ f) :
    (∃ r, GGTorusLift p r (TableBF4.RecipeGroup K) ∧
        GGInnerDiagBound p r (TableBF4.RecipeGroup K) (TableBF4.RecipeID K)) ∧
      ∃ r, GGTorusLift p r (TableBF4.RecipeGroup K) ∧
        GGIRankLe p r (TableBF4.RecipeGroup K) (TableBF4.RecipeID K) := by
  have hp2 : p ≠ 2 := ne_two_of_dvd_two_pow_sub_one hf (hK ▸ hpq)
  have hlift := TableBF4.ggTorusLift_F4 hp hp2 hpq
  have hT : GGF4ToralRankInput K p := by
    by_cases hp3 : p = 3
    · subst hp3
      exact TableBF4.ggF4ToralRankInput_three hpq
    · have h5 : 5 ≤ p := by
        have := hp.two_le
        rcases (show p = 2 ∨ p = 3 ∨ p = 4 ∨ 5 ≤ p by omega) with h | h | h | h
        · exact absurd h hp2
        · exact absurd h hp3
        · subst h
          exact absurd hp (by decide)
        · exact h
      exact TableBF4.ggF4ToralRankInput_of_five_le hp h5 hpq
  exact ⟨⟨4, hlift, ggInnerDiagBound_of_forall_mem fun φ hφ =>
    Subgroup.subset_closure (Or.inl (mem_range_conj_recipeF4_of_pow hf hK hp hp2 hpf hφ))⟩,
    4, hlift, ggIRankLe_F4 hp hpq hT⟩

end F4

end IOneRest

open IOneRest


@[expose] def GGIOneExcSplitLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .E7 ∨ lab.tag = .E8 ∨ lab.tag = .F4) ∧ p ∣ 2 ^ lab.n - 1 ∧ ¬ p ∣ lab.n

theorem largeEvenLabelAll_bstarEq_excSplit {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGIOneExcSplitLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => (∃ r, GGTorusLift p r R ∧ GGInnerDiagBound p r R I) ∧
      ∃ r, GGTorusLift p r R ∧ GGIRankLe p r R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, hpn, hpn'⟩ := h
  dsimp only at htag hpn hpn'
  have hn : 1 ≤ n := hlab.1
  intro Q hQ
  rcases htag with rfl | rfl | rfl <;> dsimp only [LargeEvenRawDatum] at hQ ⊢ <;>
    obtain ⟨K, i1, i2, hK, hq⟩ := hQ <;>
    have : CharP K 2 := charP_two_of_card hK <;>
    have hpq : p ∣ Nat.card K - 1 := (by rw [hK]; exact hpn)
  · exact ⟨K, i1, i2, hK, hq, bstarEq_data_E7E8 (τ := .E7) (Or.inl rfl) hn hK hp hpq hpn'⟩
  · exact ⟨K, i1, i2, hK, hq, bstarEq_data_E7E8 (τ := .E8) (Or.inr rfl) hn hK hp hpq hpn'⟩
  · exact ⟨K, i1, i2, hK, hq, bstarEq_data_F4 hn hK hp hpq hpn'⟩

theorem ggStdSubIOneProperInputOn_excSplit (ha₀ : GGLNoncyclicInput) :
    GGStdSubIOneProperInputOn GGIOneExcSplitLabel :=
  ggStdSubIOneProperInputOn_of_bstarEq ha₀ fun _ _ hp hlab h _ =>
    largeEvenLabelAll_bstarEq_excSplit hp hlab h

end CFSG.StandardType
