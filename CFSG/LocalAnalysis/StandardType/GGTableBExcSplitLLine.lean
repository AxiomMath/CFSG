module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcSplitLVac
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOpenOrth
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestCenter
public import CFSG.LieType.Steinberg.CentralExt.FieldFourMultiplier

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.CentralCover
  TableB TableBSymp NbrInnerRest

namespace ExcSplitL

section Line

variable {p r : ℕ} {R : Type} [Group R]

theorem ggNoInvariantLineTorus_of_reflElt [Finite R] (hp : p.Prime) {I : Set (MulAut R)}
    (hI : I ⊆ Set.range (MulAut.conj : R →* MulAut R)) (hZ : Subgroup.center R = ⊥)
    (hC : GGCenterCoprime p R) (h : GGTorusReflElt p r R) : GGNoInvariantLineTorus p r R I := by
  intro Eh hEhI hEhA hr h3
  refine ⟨hC, fun Λ hΛ hΛp => ?_⟩
  have := TableBSymp.finite_mulAut (R := R)
  have hinj := OrthRest.conj_injective hZ
  set E := Eh.comap (MulAut.conj : R →* MulAut R) with hE
  have hmap : E.map (MulAut.conj : R →* MulAut R) = Eh := by
    rw [hE, Subgroup.map_comap_eq, inf_eq_right.mpr]
    intro φ hφ
    exact hI (hEhI hφ)
  have hcardE : Nat.card E = Nat.card Eh := by
    rw [Nat.card_congr (E.equivMapOfInjective _ hinj).toEquiv, hmap]
  have hEe : IsElemAbelian p E := by
    refine ⟨⟨⟨fun a b => Subtype.ext (hinj ?_)⟩⟩, fun x hx => hinj ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact TableB.IsElemAbelian.comm hEhA a.2 b.2
    · rw [map_pow, map_one]
      exact hEhA.2 _ hx
  obtain ⟨d, e, c, n, heE, -, hn, hirr⟩ := h E hEe (hcardE ▸ hr) (hcardE ▸ h3)
  have hWE : ∀ i, ∀ y ∈ E, n i * y * (n i)⁻¹ ∈ E := by
    intro i y hy
    rw [← heE] at hy ⊢
    obtain ⟨v, rfl⟩ := hy
    exact ⟨_, (hn i (Multiplicative.toAdd v)).symm⟩
  set Λ' := Λ.comap (MulAut.conj : R →* MulAut R) with hΛ'
  have hΛmap : Λ'.map (MulAut.conj : R →* MulAut R) = Λ := by
    rw [hΛ', Subgroup.map_comap_eq, inf_eq_right.mpr]
    intro φ hφ
    exact hI (hEhI (hΛ hφ))
  have hΛ'card : Nat.card Λ' = p := by
    rw [Nat.card_congr (Λ'.equivMapOfInjective _ hinj).toEquiv, hΛmap, hΛp]
  have hΛ'E : Λ' ≤ E := fun e he => hΛ he
  by_contra hcon
  push Not at hcon
  have hinv : ∀ i, ∀ y ∈ Λ', n i * y * (n i)⁻¹ ∈ Λ' := by
    intro i y hy
    have hwN : MulAut.conj (n i) ∈ Subgroup.normalizer (Eh : Set (MulAut R)) := by
      refine NbrLang.mem_normalizer_of_conj_mem fun b hb => ?_
      obtain ⟨z, rfl⟩ := hI (hEhI hb)
      have hz : z ∈ E := hb
      have h1 := hWE i z hz
      rw [← map_inv, ← map_mul, ← map_mul]
      exact h1
    have h1 := hcon (n i) hwN (MulAut.conj y) hy
    show MulAut.conj (n i * y * (n i)⁻¹) ∈ Λ
    rw [map_mul, map_mul, map_inv]
    exact h1
  rcases hirr Λ' hΛ'E hinv with hbot | htop
  · rw [hbot, Subgroup.card_bot] at hΛ'card
    exact hp.one_lt.ne hΛ'card
  · rw [htop, hcardE] at hΛ'card
    rw [hΛ'card] at h3
    have h4 : p ^ 1 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    rw [pow_one] at h4
    omega

end Line

section Center

variable
  {K : Type} [Field K] [Finite K] [CharP K 2]

theorem ggCenterPrime_recipe_E8 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    GGCenterPrime p (TableBExc.RecipeGroup .E8 K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (adjointGroup .E8 K) := generated_group_finite .E8 K
  obtain ⟨-, ⟨O⟩, -, -⟩ := CFSG.LieType.Steinberg.Adjoint.e8_conclusionB K
  obtain ⟨C, -, hC⟩ := CFSG.LieType.Steinberg.Adjoint.e8_commutatorFormula K O
  exact (OrthRest.center_data (TableBExc.recipeEquiv .E8 K).symm center_adjointGroup_eq_bot
    (fun E _ _ π hπ hcen hc =>
      CFSG.LieType.Steinberg.CentralExt.FieldFour.exists_section_of_coprime
        (CFSG.LieType.Steinberg.Adjoint.e8_isCTGroupDatum K)
        (CFSG.LieType.Steinberg.Adjoint.e8_steinbergExtras K)
        (CFSG.LieType.Steinberg.Adjoint.e8_chevalleyExtras K O C hC) E π hπ hcen hc)
    hp hp2).2

theorem ggCenterPrime_recipe_F4 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    GGCenterPrime p (TableBF4.RecipeGroup K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (adjointGroup .F4 K) := generated_group_finite .F4 K
  obtain ⟨-, ⟨O⟩, -, -⟩ := CFSG.LieType.Steinberg.Adjoint.f4_conclusionB K
  obtain ⟨C, -, hC⟩ := CFSG.LieType.Steinberg.Adjoint.f4_commutatorFormula K O
  exact (OrthRest.center_data (TableBF4.recipeEquiv K).symm center_adjointGroup_eq_bot
    (fun E _ _ π hπ hcen hc =>
      CFSG.LieType.Steinberg.CentralExt.FieldFour.exists_section_of_coprime
        (CFSG.LieType.Steinberg.Adjoint.f4_isCTGroupDatum K)
        (CFSG.LieType.Steinberg.Adjoint.f4_steinbergExtras K)
        (CFSG.LieType.Steinberg.Adjoint.f4_chevalleyExtras K O C hC) E π hπ hcen hc)
    hp hp2).2

theorem ggNoInvariantLineTorus_E8 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K - 1) :
    GGNoInvariantLineTorus p 8 (TableBExc.RecipeGroup .E8 K) (TableBExc.RecipeID .E8 K) := by
  have := TableBExc.finite_recipeGroup .E8 K
  exact ggNoInvariantLineTorus_of_reflElt hp (TableBExc.idImage_subset_inn_E8 K)
    (TableBExc.center_recipeGroup_eq_bot .E8 K)
    (CorFourTwoOpen.ggCenterCoprime_of_centerPrime (ggCenterPrime_recipe_E8 hp hp2))
    (CorFourTwoMore.ggTorusReflElt_of_mulEquiv (TableBExc.recipeEquiv .E8 K)
      (ggTorusReflElt_adjoint (τ := .E8) hp hpq
        (TableBExc.isUnit_det_cartan_of_eq hp CFSG.LieType.Chevalley.det_cartan_E8
          (Nat.coprime_one_left p))
        (cartanE_connected (by decide)) (fun i j h => cartanE_entry_ne_zero hp hp2 i j h)
        (TableBExc.card_torusPow_E8 hp hpq)
        (IOneRest.ggExcToralRankInput_E7E8 (Or.inr rfl) hp hp2 hpq)))

theorem ggNoInvariantLineTorus_F4 {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1) :
    GGNoInvariantLineTorus p 4 (TableBF4.RecipeGroup K) (TableBF4.RecipeID K) := by
  have := TableBF4.finite_recipeGroup (K := K)
  exact ggNoInvariantLineTorus_of_reflElt hp (TableBF4.idImage_subset_inn K)
    (TableBF4.center_recipeGroup_eq_bot K)
    (CorFourTwoOpen.ggCenterCoprime_of_centerPrime (ggCenterPrime_recipe_F4 hp hp2))
    (CorFourTwoMore.ggTorusReflElt_of_mulEquiv (TableBF4.recipeEquiv K)
      (ggTorusReflElt_adjointF4 hp hp2 hpq
        (ggF4ToralRankInput_of_three hp hp2 hpq fun _ => ggF4ThreeRankInput_holds)))

end Center

end ExcSplitL

open ExcSplitL

@[expose] def GGExcLLineLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .E8 ∨ lab.tag = .F4) ∧ p ∣ 2 ^ lab.n - 1

section Labels

theorem largeEvenLabelAll_noInvariantLine_excLLine {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGExcLLineLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ =>
      ∃ r, GGTorusLift p r R ∧ GGNoInvariantLineTorus p r R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, hpn⟩ := h
  have hn : 1 ≤ n := hlab.1
  dsimp only at htag hpn hn
  have hp2 : p ≠ 2 := ne_two_of_dvd_two_pow_sub_one hn hpn
  rcases htag with rfl | rfl
  · intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    refine recipeChevalley_and (fun K _ _ hK => ?_) hQ
    have : CharP K 2 := charP_two_of_card hK
    have hpq : p ∣ Nat.card K - 1 := by rw [hK]; exact hpn
    exact ⟨8, TableBExc.ggTorusLift_E8 hp hp2 hpq, ggNoInvariantLineTorus_E8 hp hp2 hpq⟩
  · intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    refine recipeChevalley_and (fun K _ _ hK => ?_) hQ
    have : CharP K 2 := charP_two_of_card hK
    have hpq : p ∣ Nat.card K - 1 := by rw [hK]; exact hpn
    exact ⟨4, TableBF4.ggTorusLift_F4 hp hp2 hpq, ggNoInvariantLineTorus_F4 hp hp2 hpq⟩

end Labels

end CFSG.StandardType

end
