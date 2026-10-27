module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcSplitLLineE7
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSplitLBstarE6
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRestUnitaryCenter

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.CentralCover
  TableB TableBSymp NbrInnerRest CFSG.LieType.Steinberg.Minuscule

namespace ExcSplitL

section Line

variable {p r : ℕ} {R : Type} [Group R]

theorem ggNoInvariantLineTorus_of_reflElt' [Finite R] (hp : p.Prime) {I : Set (MulAut R)}
    (hI : ∀ φ ∈ I, φ ^ p = 1 → φ ∈ Set.range (MulAut.conj : R →* MulAut R))
    (hZ : Subgroup.center R = ⊥)
    (hC : GGCenterCoprime p R) (h : GGTorusReflElt p r R) : GGNoInvariantLineTorus p r R I := by
  intro Eh hEhI hEhA hr h3
  refine ⟨hC, fun Λ hΛ hΛp => ?_⟩
  have := TableBSymp.finite_mulAut (R := R)
  have hinj := OrthRest.conj_injective hZ
  set E := Eh.comap (MulAut.conj : R →* MulAut R) with hE
  have hmap : E.map (MulAut.conj : R →* MulAut R) = Eh := by
    rw [hE, Subgroup.map_comap_eq, inf_eq_right.mpr]
    intro φ hφ
    exact hI φ (hEhI hφ) (hEhA.2 φ hφ)
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
    exact hI φ (hEhI (hΛ hφ)) (hEhA.2 φ (hΛ hφ))
  have hΛ'card : Nat.card Λ' = p := by
    rw [Nat.card_congr (Λ'.equivMapOfInjective _ hinj).toEquiv, hΛmap, hΛp]
  have hΛ'E : Λ' ≤ E := fun e he => hΛ he
  by_contra hcon
  push Not at hcon
  have hinv : ∀ i, ∀ y ∈ Λ', n i * y * (n i)⁻¹ ∈ Λ' := by
    intro i y hy
    have hwN : MulAut.conj (n i) ∈ Subgroup.normalizer (Eh : Set (MulAut R)) := by
      refine NbrLang.mem_normalizer_of_conj_mem fun b hb => ?_
      obtain ⟨z, rfl⟩ := hI b (hEhI hb) (hEhA.2 b hb)
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

section E6

variable
  {K : Type} [Field K] [Finite K] [CharP K 2]

theorem ggCenterPrime_recipe_E6 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    GGCenterPrime p (TableBExc.RecipeGroup .E6 K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := Fact.mk hp
  have := CFSG.LieType.Steinberg.CentralExt.FieldFour.finite_minGroup' (K := K) e6Data_valid
  obtain ⟨-, ⟨O⟩, -, -⟩ := CFSG.LieType.Steinberg.e6_conclusionB K
  obtain ⟨C, -, hC⟩ := e6Datum_commutatorFormula K _ (roots_eq isFiniteType_cartan_E6) O
  set f := CFSG.LieType.Steinberg.Isogeny.e6Isogeny K with hf
  set q : e6Data_valid.minGroup K →* TableBExc.RecipeGroup .E6 K :=
    (TableBExc.recipeEquiv .E6 K).symm.toMonoidHom.comp f with hqdef
  have hq : Function.Surjective q := (TableBExc.recipeEquiv .E6 K).symm.surjective.comp
    (CFSG.LieType.Steinberg.Isogeny.e6Isogeny_surjective K)
  have hnp : ∀ z ∈ q.ker, z ^ p = 1 → z = 1 := by
    intro z hz hzp
    have hz' : z ∈ f.ker := by
      rw [MonoidHom.mem_ker] at hz ⊢
      have h1 : (TableBExc.recipeEquiv .E6 K).symm (f z) = 1 := hz
      rwa [MulEquiv.map_eq_one_iff] at h1
    rw [hf, CFSG.LieType.Steinberg.CentralExt.FieldFour.e6Isogeny_ker_eq_center] at hz'
    obtain ⟨hcard, -⟩ := CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.card_center_e6 K
    have hdvd : Nat.card (Subgroup.center (e6Data_valid.minGroup K)) ∣ 3 := by
      rw [hcard]
      exact Nat.gcd_dvd_left 3 _
    obtain ⟨c, hc⟩ := hdvd
    have h3 : (⟨z, hz'⟩ : Subgroup.center (e6Data_valid.minGroup K)) ^ 3 = 1 := by
      rw [hc, pow_mul, pow_card_eq_one', one_pow]
    have h3' : z ^ 3 = 1 := congrArg Subtype.val h3
    have hcop : Nat.Coprime p 3 := (Nat.coprime_primes hp Nat.prime_three).2 hp3
    have h4 : orderOf z = 1 := Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hzp)
      (orderOf_dvd_of_pow_eq_one h3')
    exact orderOf_eq_one_iff.mp h4
  intro L' _ _ ψ hψ hker hperf hdvd
  have hnpL := StdSubRestU.noTorsion_ker_of_section hq
    (fun E _ _ π hπ hcen hc =>
      CFSG.LieType.Steinberg.CentralExt.FieldFour.exists_section_of_coprime
        (e6Datum_isCTGroupDatum K) (e6Datum_steinbergExtras K) (e6_chevalleyExtras K O C hC)
        E π hπ hcen hc) hp hp2 hnp hψ hker hperf
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hzk : (z : L') ∈ ψ.ker := by
    have h1 : ψ z ∈ Subgroup.center (TableBExc.RecipeGroup .E6 K) := by
      rw [Subgroup.mem_center_iff]
      intro r
      obtain ⟨l, rfl⟩ := hψ r
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp z.2 l]
    rw [TableBExc.center_recipeGroup_eq_bot .E6 K, Subgroup.mem_bot] at h1
    exact h1
  have hzp : (z : L') ^ p = 1 := by
    have := pow_orderOf_eq_one z
    rw [hz] at this
    exact congrArg Subtype.val this
  have h1 : z = 1 := Subtype.ext (hnpL _ hzk hzp)
  rw [h1, orderOf_one] at hz
  exact hp.one_lt.ne hz

theorem ggNoInvariantLineTorus_E6 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hpq : p ∣ Nat.card K - 1) :
    GGNoInvariantLineTorus p 6 (TableBExc.RecipeGroup .E6 K) (TableBExc.RecipeID .E6 K) := by
  have := TableBExc.finite_recipeGroup .E6 K
  exact ggNoInvariantLineTorus_of_reflElt' hp
    (fun φ hφ hφp => mem_range_conj_of_mem_recipeID_E6 hp hp3 hφ hφp)
    (TableBExc.center_recipeGroup_eq_bot .E6 K)
    (CorFourTwoOpen.ggCenterCoprime_of_centerPrime (ggCenterPrime_recipe_E6 hp hp2 hp3))
    (CorFourTwoMore.ggTorusReflElt_of_mulEquiv (TableBExc.recipeEquiv .E6 K)
      (ggTorusReflElt_adjoint (τ := .E6) hp hpq
        (TableBExc.isUnit_det_cartan_of_eq hp CFSG.LieType.Chevalley.det_cartan_E6
          ((Nat.coprime_primes Nat.prime_three hp).2 (Ne.symm hp3)))
        (cartanE_connected (by decide)) (fun i j h => cartanE_entry_ne_zero hp hp2 i j h)
        (TableBExc.card_torusPow_E6 hp hp3 hpq)
        (TableBExc.ggExcToralRankInput_E6_of_ne_three hp hp2 hp3 hpq)))

end E6

end ExcSplitL

open ExcSplitL

section Labels


theorem ggLNoInvariantLineInputOn_excLSplitE6 : GGLNoInvariantLineInputOn GGExcLSplitE6Label := by
  refine ggLNoInvariantLineInputOn_of_labels fun p lab hp hlab h => ?_
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, hp3, hpn⟩ := h
  have hn : 1 ≤ n := hlab.1
  dsimp only at htag hpn hn
  subst htag
  have hp2 : p ≠ 2 := ne_two_of_dvd_two_pow_sub_one hn hpn
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  refine recipeChevalley_and (fun K _ _ hK => ?_) hQ
  have : CharP K 2 := charP_two_of_card hK
  have hpq : p ∣ Nat.card K - 1 := by rw [hK]; exact hpn
  exact ⟨6, TableBExc.ggTorusLift_E6 hp hp2 hp3 hpq, ggNoInvariantLineTorus_E6 hp hp2 hp3 hpq⟩

@[expose] def GGExcLLineAllLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGExcLSplitLabel p lab ∨ GGExcLSplitE6Label p lab

theorem ggLNoInvariantLineInputOn_excLLineAll : GGLNoInvariantLineInputOn GGExcLLineAllLabel :=
  ggLNoInvariantLineInputOn_excLSplit.or ggLNoInvariantLineInputOn_excLSplitE6

theorem ggLNoInvariantLineInputOn_of_not_excLLineAll {S : ℕ → LargeEvenLabel → Prop}
    (h : GGLNoInvariantLineInputOn fun p lab => S p lab ∧ ¬ GGExcLLineAllLabel p lab) :
    GGLNoInvariantLineInputOn S := by
  have h' := ggLNoInvariantLineInputOn_excLLineAll.or h
  intro G _ _ p B Bs x L D J hC hL
  refine h' G p B Bs x L D J hC (hL.mono fun p lab hlab => ?_)
  by_cases h1 : GGExcLLineAllLabel p lab
  · exact Or.inl h1
  · exact Or.inr ⟨hlab, h1⟩

end Labels

end CFSG.StandardType

end
