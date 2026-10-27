module

public import CFSG.LocalAnalysis.StandardType.GGNbrKGTwE6ThreeAtDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic
public import CFSG.LocalAnalysis.StandardType.GGKG82Defs
public import CFSG.LocalAnalysis.StandardType.GGKG82Outdiag
public import CFSG.LocalAnalysis.StandardType.GGInndiagNormalOtherTwE6
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiag
public import CFSG.LocalAnalysis.StandardType.GGLFourFourThreeMarking
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldDefs
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.StandardType.KG82

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Open
open scoped Pointwise

section Stabilizer

variable {L : Type} [Group L]

theorem ggTwoLocalAut_of_le_stabilizer {E : Subgroup (MulAut L)} {U : Subgroup L} (hU : U ≠ ⊥)
    (hU2 : IsPGroup 2 U) (hE : E ≤ MulAction.stabilizer (MulAut L) U) : GGTwoLocalAut E := by
  refine ⟨U, hU, hU2, fun e he u hu => ?_⟩
  have h : e • u ∈ e • U := Subgroup.smul_mem_pointwise_smul u e U hu
  rw [MulAction.mem_stabilizer_iff.mp (hE he)] at h
  exact h

theorem mem_stabilizer_of_forall_eq {U : Subgroup L} {f : MulAut L} (hf : ∀ u ∈ U, f u = u) :
    f ∈ MulAction.stabilizer (MulAut L) U := by
  rw [MulAction.mem_stabilizer_iff]
  ext x
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def]
  constructor
  · intro h
    have e : f (f⁻¹ x) = f⁻¹ x := hf _ h
    rw [MulAut.apply_inv_self] at e
    rw [e]
    exact h
  · intro h
    have e : f⁻¹ (f x) = f⁻¹ x := by rw [hf x h]
    rw [MulAut.inv_apply_self] at e
    rw [← e]
    exact h

theorem conj_mem_stabilizer {U : Subgroup L} {g : L} (hg : g ∈ Subgroup.normalizer (U : Set L)) :
    MulAut.conj g ∈ MulAction.stabilizer (MulAut L) U := by
  rw [MulAction.mem_stabilizer_iff]
  ext x
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def, ← map_inv, MulAut.conj_apply,
    inv_inv]
  have h := Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) x
  rw [inv_inv] at h
  exact h.symm

end Stabilizer

theorem ggTwoLocalAt_of_cases {R : Type} [Group R] {p r : ℕ} [hp : Fact p.Prime]
    {I F : Set (MulAut R)} {D : Subgroup (MulAut R)} [D.Normal] (hD : I = D)
    (hZ : Subgroup.center R = ⊥)
    (h1 : ∃ E : Subgroup (MulAut R), (∀ φ ∈ E, φ ∈ I) ∧ IsElemAbelian p E ∧ p ^ r ≤ Nat.card E ∧
      GGTwoLocalAut E)
    (h1b : ∀ a ∈ I, a ∉ (MulAut.conj : R →* MulAut R).range → ∀ φ ∈ I,
      φ ∈ Subgroup.zpowers a ⊔ (MulAut.conj : R →* MulAut R).range)
    (h2 : ∀ f ∈ F, orderOf f = p → ∃ E U : Subgroup R, IsElemAbelian p E ∧ p ^ r ≤ Nat.card E ∧
      U ≠ ⊥ ∧ IsPGroup 2 U ∧ E ≤ Subgroup.normalizer (U : Set R) ∧ (∀ e ∈ E, f e = e) ∧
      (∀ u ∈ U, f u = u))
    (hconj : ∀ u ∈ I, ∀ f ∈ Subgroup.closure F, u * f ∉ I → (u * f) ^ p = 1 →
      ∃ f' ∈ F, ∃ u' ∈ I, orderOf f' = p ∧ u * f = u' * f' * u'⁻¹) :
    GGTwoLocalAt p r (r + 1) R I F := by
  intro hR a hap ha hna
  have hfin : Finite (MulAut R) :=
    Finite.of_injective (fun φ : MulAut R => (φ : R → R)) DFunLike.coe_injective
  by_cases haI : a ∈ I
  · obtain ⟨E, hEI, hEab, hEc, hEloc⟩ := h1
    exact ⟨E, fun φ hφ => h1b a haI hna φ (hEI φ hφ), hEab, hEloc, hEc, fun h => absurd haI h⟩
  have hcl : Subgroup.closure (I ∪ F) ≤ D ⊔ Subgroup.closure F := by
    rw [Subgroup.closure_le]
    rintro x (hx | hx)
    · rw [hD] at hx
      exact Subgroup.mem_sup_left hx
    · exact Subgroup.mem_sup_right (Subgroup.subset_closure hx)
  obtain ⟨u, hu, f, hf, rfl⟩ : ∃ u ∈ D, ∃ f ∈ Subgroup.closure F, u * f = a := by
    have h := hcl ha
    rw [← SetLike.mem_coe, Subgroup.normal_mul] at h
    exact Set.mem_mul.mp h
  have huI : u ∈ I := by
    rw [hD]
    exact hu
  obtain ⟨f', hf'F, u', -, hf'o, e⟩ := hconj u huI f hf haI hap
  obtain ⟨E₁, U, hE₁, hE₁c, hU, hU2, hEU, hfE, hfU⟩ := h2 f' hf'F hf'o
  have hf'N : f' ∉ (MulAut.conj : R →* MulAut R).range := fun h => hna (by
    rw [e]
    exact Subgroup.Normal.conj_mem inferInstance f' h u')
  have hf'p : f' ^ p = 1 := by
    rw [← hf'o]
    exact pow_orderOf_eq_one f'
  have hcomm : ∀ x ∈ Subgroup.zpowers f', ∀ y ∈ E₁.map (MulAut.conj : R →* MulAut R),
      x * y = y * x := by
    intro x hx y hy
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hy
    have h0 : Commute f' (MulAut.conj g) := by
      show f' * MulAut.conj g = MulAut.conj g * f'
      ext z
      simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, hfE g hg]
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact (h0.zpow_left k).eq
  set E₂ : Subgroup (MulAut R) := Subgroup.zpowers f' ⊔ E₁.map (MulAut.conj : R →* MulAut R)
    with hE₂def
  have hE₂ : IsElemAbelian p E₂ :=
    (isElemAbelian_zpowers hf'p).sup_of_commute (hE₁.map _) hcomm
  have hBlt : E₁.map (MulAut.conj : R →* MulAut R) < E₂ := by
    refine lt_of_le_of_ne le_sup_right fun h => hf'N ?_
    have hf'E : f' ∈ E₂ := Subgroup.mem_sup_left (Subgroup.mem_zpowers f')
    rw [← h] at hf'E
    exact Subgroup.map_le_range _ _ hf'E
  have hcardB : Nat.card (E₁.map (MulAut.conj : R →* MulAut R)) = Nat.card E₁ :=
    Subgroup.card_map_of_injective (mulAut_conj_injective hZ)
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hE₂.isPGroup
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp (hE₁.map (MulAut.conj : R →* MulAut R)).isPGroup
  have hjm : j < m := by
    have hdvd := Subgroup.card_dvd_of_le hBlt.le
    have hne : Nat.card (E₁.map (MulAut.conj : R →* MulAut R)) ≠ Nat.card E₂ := fun h =>
      hBlt.ne (Subgroup.eq_of_le_of_card_ge hBlt.le h.ge)
    rw [hm, hj] at hdvd hne
    exact lt_of_le_of_ne ((Nat.pow_dvd_pow_iff_le_right hp.out.one_lt).mp hdvd)
      fun h => hne (h ▸ rfl)
  have hrj : r ≤ j := by
    have h := hE₁c
    rw [← hcardB, hj] at h
    exact (Nat.pow_le_pow_iff_right hp.out.one_lt).mp h
  have hE₂c : p ^ (r + 1) ≤ Nat.card E₂ := by
    rw [hm]
    exact Nat.pow_le_pow_right hp.out.pos (by omega)
  have hst : E₂ ≤ MulAction.stabilizer (MulAut R) U := by
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]
      exact mem_stabilizer_of_forall_eq hfU
    · rw [Subgroup.map_le_iff_le_comap]
      intro x hx
      exact conj_mem_stabilizer (hEU hx)
  set φ : MulAut R →* MulAut R := (MulAut.conj u').toMonoidHom with hφ
  have hcard : Nat.card (E₂.map φ) = Nat.card E₂ :=
    Subgroup.card_map_of_injective (MulAut.conj u').injective
  refine ⟨E₂.map φ, ?_, hE₂.map φ, ?_, ?_, fun _ => ?_⟩
  · rw [Subgroup.map_le_iff_le_comap]
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le, Subgroup.mem_comap]
      show MulAut.conj u' f' ∈ _
      rw [MulAut.conj_apply, ← e]
      exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
    · rw [Subgroup.map_le_iff_le_comap]
      intro x _
      rw [Subgroup.mem_comap, Subgroup.mem_comap]
      show MulAut.conj u' (MulAut.conj x) ∈ _
      rw [MulAut.conj_apply]
      exact Subgroup.mem_sup_right ((inferInstance : (MulAut.conj : R →* MulAut R).range.Normal).conj_mem
        _ (MonoidHom.mem_range.mpr ⟨x, rfl⟩) u')
  · refine ggTwoLocalAut_of_le_stabilizer (U := u' • U) ?_ ?_ ?_
    · intro h
      apply hU
      rw [← inv_smul_smul u' U, h, Subgroup.smul_bot]
    · rw [Subgroup.pointwise_smul_def]
      exact hU2.map _
    · rintro _ ⟨x, hx, rfl⟩
      rw [MulAction.mem_stabilizer_iff]
      show (MulAut.conj u' x) • (u' • U) = u' • U
      rw [MulAut.conj_apply, mul_smul, mul_smul, inv_smul_smul,
        MulAction.mem_stabilizer_iff.mp (hst hx)]
  · rw [hcard]
    exact le_trans (Nat.pow_le_pow_right hp.out.pos (Nat.le_succ r)) hE₂c
  · rw [hcard]
    exact hE₂c

section Recipe

variable {n : ℕ} {K : Type} [Field K] [Finite K]


theorem ggTwoLocalAt_recipe_of
    (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (hS1 : ∃ E : Subgroup (MulAut (TwE6Delta.RecipeR K n)),
      (∀ φ ∈ E, φ ∈ TwE6Delta.RecipeI K n) ∧ IsElemAbelian 3 E ∧ 3 ^ 5 ≤ Nat.card E ∧
        GGTwoLocalAut E)
    (hS2 : ∀ f ∈ RecipeF K n, orderOf f = 3 → ∃ E U : Subgroup (TwE6Delta.RecipeR K n),
      IsElemAbelian 3 E ∧ 3 ^ 5 ≤ Nat.card E ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧
        E ≤ Subgroup.normalizer (U : Set (TwE6Delta.RecipeR K n)) ∧ (∀ e ∈ E, f e = e) ∧
          (∀ u ∈ U, f u = u))
    (hs : IsSimpleGroup (TwE6Delta.RecipeR K n))
    (hna : ∃ a b : TwE6Delta.RecipeR K n, a * b ≠ b * a)
    (hconj : GGRawFieldConj 3 (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n) (RecipeF K n)) :
    GGTwoLocalAt 3 5 6 (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n) (RecipeF K n) := by
  obtain ⟨D, hD⟩ : ∃ D : Subgroup (MulAut (TwE6Delta.RecipeR K n)),
      TwE6Delta.RecipeI K n = D := ⟨_, rfl⟩
  have hN : GGInndiagNormal (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n) :=
    InndiagE6.ggInndiagNormal_twE6 hn K hK
  have hle : ggInndiag (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n) ≤ D := by
    refine sup_le ?_ ?_
    · rintro _ ⟨x, rfl⟩
      have hx : MulAut.conj x ∈ TwE6Delta.RecipeI K n :=
        Subgroup.subset_closure (Or.inl ⟨x, rfl⟩)
      rw [hD] at hx
      exact hx
    · rw [Subgroup.closure_le, hD]
  have : D.Normal := ⟨fun φ hφ α => hle (hN α φ (by rw [hD]; exact hφ))⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact ggTwoLocalAt_of_cases (r := 5) hD (TwE6Delta.center_recipeR_eq_bot hn hK) hS1
    (fun a ha hna φ hφ => mem_zpowers_sup_inn_of_mem_recipeI hn hK ha hna hφ) hS2 (hconj hs hna)

end Recipe

theorem ggNbrKGTwE6ThreeAddTwoLocalAt_of_recipe
    (h : ∀ n : ℕ, 1 ≤ n → 3 ∣ 2 ^ n + 1 → ∀ (K : Type) [Field K] [Finite K],
      Nat.card K = (2 ^ n) ^ 2 → IsSimpleGroup (TwE6Delta.RecipeR K n) →
      (∃ a b : TwE6Delta.RecipeR K n, a * b ≠ b * a) →
      GGRawFieldConj 3 (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n) (RecipeF K n) →
      GGTwoLocalAt 3 5 6 (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n) (RecipeF K n))
    (hFC : GGRawFieldConjInputExc) : GGNbrKGTwE6ThreeAddTwoLocalAt := by
  intro lab hlab ht h3
  have hF : LargeEvenLabelAll lab (GGRawFieldConj 3) :=
    hFC 3 Nat.prime_three (by norm_num) lab hlab (by simp [ht])
  have hR : LargeEvenLabelAll lab fun R _ I F => GGRawFieldConj 3 R I F → IsSimpleGroup R →
      (∃ a b : R, a * b ≠ b * a) → GGTwoLocalAt 3 5 6 R I F := by
    obtain ⟨t, l, n⟩ := lab
    obtain ⟨hn, -⟩ := hlab
    dsimp only at ht h3
    subst ht
    intro Q hQ
    exact recipeTwisted_and (P := fun R _ I F => GGRawFieldConj 3 R I F → IsSimpleGroup R →
      (∃ a b : R, a * b ≠ b * a) → GGTwoLocalAt 3 5 6 R I F)
      (fun K _ _ hK hc hs hna => h n hn h3 K hK hs hna hc) hQ
  intro Q hQ
  exact largeEvenRawDatum_mono (fun _ _ _ _ h' => ⟨h'.1.1, h'.2 h'.1.2⟩) (hR _ (hF Q hQ))

end CFSG.StandardType.KG82
