module

public import CFSG.LocalAnalysis.StandardType.GGTBTorE7Cover
public import CFSG.LocalAnalysis.StandardType.GGTorusE7Lang
public import CFSG.LocalAnalysis.StandardType.GGTorusE7Split

public noncomputable section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.RootSystem
  CFSG.HardMathSupport.Timmesfeld.CrossChar


theorem ggTorusTorData_E7_split_standard {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq : p ∣ Nat.card K - 1) :
    GGTorusTorData (Nat.card K - 1) 7 (CartanMatrix.E 7) CoxeterMatrix.E₇
      (adjointGroup .E7 K) ((TableBExc.torusPow .E7 K p).map
        (MulAut.conj : adjointGroup .E7 K →* MulAut (adjointGroup .E7 K))) := by
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ζ, hζ, ι, hζo, hι, hrange, hact, hnorm⟩ := E7SplitTorus.exists_frame hp hp2 hq
  let E := TableBExc.torusPow .E7 K p
  let φ := E7SplitTorus.coordHom (K := K)
  let n := E7SplitTorus.simpleRep (K := K)
  obtain ⟨l⟩ := E8SplitTorus.exists_rootValue_equiv (K := K)
  have hζ1 : ζ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hζo
    exact hp.ne_one hζo.symm
  have hC : Tag.E7.cartan = CartanMatrix.E 7 := cartanE_eq 7
  have hM : coxeterMatrix (CFSG.LieType.Chevalley.isFiniteType_cartan .E7) = CoxeterMatrix.E₇ :=
    FrameRoute.coxeterE7_eq.symm
  suffices h : GGTorusTorData (Nat.card K - 1) Tag.E7.rank Tag.E7.cartan
      (coxeterMatrix (CFSG.LieType.Chevalley.isFiniteType_cartan .E7))
      (adjointGroup .E7 K) (E.map
        (MulAut.conj : adjointGroup .E7 K →* MulAut (adjointGroup .E7 K))) by
    rw [hM] at h
    simpa only [hC, Tag.rank] using h
  have hm : Odd (Nat.card K - 1) := by
    let : Fintype K := Fintype.ofFinite K
    have hEven : Even (Nat.card K) := by
      rw [Nat.even_iff, Nat.card_eq_fintype_card]
      exact FiniteField.even_card_of_char_two (ringChar.eq K 2)
    obtain ⟨k, hk⟩ := hEven
    have hpos : 1 < Nat.card K := Finite.one_lt_card
    exact ⟨k - 1, by omega⟩
  have hdet : IsUnit ((Tag.E7.cartan.det : ℤ) : ZMod (Nat.card K - 1)) := by
    rw [det_cartan_E7]
    simpa using (ZMod.isUnit_iff_coprime 2 (Nat.card K - 1)).mpr
      (Nat.coprime_two_left.mpr hm)
  obtain ⟨B, hCB', hBC'⟩ := exists_int_matrix_inverse_mod_of_isUnit_det Tag.E7.cartan hdet
  have hCsymm : Tag.E7.cartan.IsSymm := hC.symm ▸ CartanMatrix.E_isSymm 7
  obtain ⟨hnA, ρ, hρ, hρrange, hρsimple⟩ := exists_markedWeyl_innerHom
    (hp.odd_of_ne_two hp2) E mulAut_conj_injective_adjointGroup ι hι hrange n hact hnorm
  exact ggTorusTorData_of_scalarRootCoordinates_columns_mod l φ E7SplitTorus.coordHom_injective
    Tag.E7.cartan B hCB' hBC' center_adjointGroup_eq_bot E
    E7SplitTorus.mem_torusPow_iff ζ hζ hζ1 n hnA
    (fun k a => by rw [hCsymm.eq]; exact E7SplitTorus.simple_conj_coordHom k a)
    (E7SplitTorus.centralizer_le_range hp hp2 hq)
    (coxeterMatrix (CFSG.LieType.Chevalley.isFiniteType_cartan .E7)) ρ hρ hρrange hρsimple

theorem ggTorusTorData_E7_split {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq : p ∣ Nat.card K - 1)
    (E : Subgroup (adjointGroup .E7 K)) (hE : IsElemAbelian p E)
    (hcard : p ^ 7 ≤ Nat.card E) :
    GGTorusTorData (Nat.card K - 1) 7 (CartanMatrix.E 7) CoxeterMatrix.E₇
      (adjointGroup .E7 K) (E.map
        (MulAut.conj : adjointGroup .E7 K →* MulAut (adjointGroup .E7 K))) := by
  obtain ⟨g, hg⟩ := E7SplitTorus.exists_conj_torusPow hp hp2 hq E hE hcard
  let e : adjointGroup .E7 K ≃* adjointGroup .E7 K := MulAut.conj g
  have hA : (E.map (MulAut.conj : adjointGroup .E7 K →* MulAut (adjointGroup .E7 K))).map
      (MulAut.congr e).toMonoidHom = (TableBExc.torusPow .E7 K p).map
        (MulAut.conj : adjointGroup .E7 K →* MulAut (adjointGroup .E7 K)) := by
    rw [Subgroup.map_map, ← hg, Subgroup.map_map]
    exact congrArg (fun f => E.map f) (by
      apply MonoidHom.ext
      intro x
      exact congr_conj e x)
  exact GGTorusTorData.of_inner_model e hA (ggTorusTorData_E7_split_standard hp hp2 hq)


theorem ggTorusTorData_E7_plus {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq : p ∣ Nat.card K + 1)
    (E : Subgroup (adjointGroup .E7 K)) (hE : IsElemAbelian p E)
    (hcard : p ^ 6 ≤ Nat.card E)
    (hSC : ∀ g : adjointGroup .E7 K, (∀ x ∈ E, g * x = x * g) → g ^ p = 1 → g ∈ E) :
    GGTorusTorData (Nat.card K + 1) 7 (CartanMatrix.E 7) CoxeterMatrix.E₇
      (adjointGroup .E7 K) (E.map
        (MulAut.conj : adjointGroup .E7 K →* MulAut (adjointGroup .E7 K))) := by
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨F, Fr, ζ, hζ, ι, n, hFr, hΦ, hw, hζo, hι, hrange, -, hnb, hact, hnorm⟩ :=
    exists_e7_scalar_frame hp hp2 hq E hE hcard hSC
  let μ := rootsOfUnity (Nat.card K + 1) (AlgebraicClosure K)
  have hrat : ∀ X : Subgroup (ModGL .E7 (AlgebraicClosure K)), Finite X →
      X ≤ adjointGroup .E7 (AlgebraicClosure K) →
      (∀ x ∈ X, Units.map (entrywiseHom Fr) x = x) →
        X ≤ (adjointGroup .E7 K).map (baseChangeGL (algebraMap K (AlgebraicClosure K))) :=
    fun X hfin hXC hXF => by
      let : Finite X := hfin
      exact finite_fixed_le_map_adjointGroup_E7 Fr hFr X hXC hXF
  let φ := ScalarLangTorus.coordHom F.D Fr hFr hΦ F.n_eq hw hrat
  have hφ : Function.Injective φ := ScalarLangTorus.coordHom_injective F.D Fr hFr hΦ F.n_eq hw hrat
  obtain ⟨l⟩ := E8ScalarTorus.exists_rootValue_equiv (K := K)
  have hζm : ζ ^ (Nat.card K + 1) = 1 := by
    obtain ⟨k, hk⟩ := hq
    rw [hk, pow_mul, hζ, one_pow]
  let z : μ := ⟨ζ, (mem_rootsOfUnity _ _).mpr hζm⟩
  have hz : z ^ p = 1 := Subtype.ext hζ
  have hz1 : z ≠ 1 := by
    intro h
    have hζ1 : ζ = 1 := congrArg Subtype.val h
    rw [hζ1, orderOf_one] at hζo
    exact hp.ne_one hζo.symm
  have hC : Tag.E7.cartan = CartanMatrix.E 7 := cartanE_eq 7
  have hM : coxeterMatrix (CFSG.LieType.Chevalley.isFiniteType_cartan .E7) = CoxeterMatrix.E₇ :=
    FrameRoute.coxeterE7_eq.symm
  suffices h : GGTorusTorData (Nat.card K + 1) Tag.E7.rank Tag.E7.cartan
      (coxeterMatrix (CFSG.LieType.Chevalley.isFiniteType_cartan .E7))
      (adjointGroup .E7 K) (E.map
        (MulAut.conj : adjointGroup .E7 K →* MulAut (adjointGroup .E7 K))) by
    rw [hM] at h
    simpa only [hC, Tag.rank] using h
  have hm : Odd (Nat.card K + 1) := by
    let : Fintype K := Fintype.ofFinite K
    have hEven : Even (Nat.card K) := by
      rw [Nat.even_iff, Nat.card_eq_fintype_card]
      exact FiniteField.even_card_of_char_two (ringChar.eq K 2)
    exact hEven.add_one
  have hdet : IsUnit ((Tag.E7.cartan.det : ℤ) : ZMod (Nat.card K + 1)) := by
    rw [det_cartan_E7]
    simpa using (ZMod.isUnit_iff_coprime 2 (Nat.card K + 1)).mpr
      (Nat.coprime_two_left.mpr hm)
  obtain ⟨B, hCB', hBC'⟩ := exists_int_matrix_inverse_mod_of_isUnit_det Tag.E7.cartan hdet
  have hCsymm : Tag.E7.cartan.IsSymm := hC.symm ▸ CartanMatrix.E_isSymm 7
  obtain ⟨hnA, ρ, hρ, hρrange, hρsimple⟩ := exists_markedWeyl_innerHom
    (hp.odd_of_ne_two hp2) E mulAut_conj_injective_adjointGroup ι hι hrange n hact hnorm
  apply ggTorusTorData_of_scalarRootCoordinates_columns_mod l φ hφ Tag.E7.cartan B hCB' hBC'
    center_adjointGroup_eq_bot E (fun g => e7_scalar_mem_iff_coordinates F Fr hFr hΦ hw g)
    z hz hz1 n hnA _ _
    (coxeterMatrix (CFSG.LieType.Chevalley.isFiniteType_cartan .E7)) ρ hρ hρrange hρsimple
  · intro k a
    rw [hCsymm.eq]
    exact ScalarLangTorus.simple_conj_coordHom F.D Fr hFr hΦ F.n_eq hw hrat k (n k) (hnb k) a
  · have hlong : ExcIsLongest .E7 F.w := by
      intro α hα hpos i
      rw [hw, Pi.neg_apply]
      exact neg_nonpos.mpr (hpos i)
    exact e7_scalar_centralizer_le_coordinates hp hp2 F Fr hFr hΦ hq hlong hw


theorem ggTorusTorW_recipe_E7_split {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq : p ∣ Nat.card K - 1) :
    GGTorusTorW p 7 (Nat.card K - 1) 7 (CartanMatrix.E 7) CoxeterMatrix.E₇
      (TableBExc.RecipeGroup .E7 K) (TableBExc.RecipeID .E7 K) := by
  intro L _ _ ψ A hTB
  obtain ⟨e, -, E, hE, hcard, -, hA⟩ := exists_e7_model_of_tbGroup ψ A hTB
  have hr : p ^ 7 ≤ Nat.card E := by rw [hcard]; exact hTB.2.2.2.2.2.1
  exact GGTorusTorData.of_inner_model e hA (ggTorusTorData_E7_split hp hp2 hq E hE hr)

theorem ggTorusTorW_recipe_E7_plus {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq : p ∣ Nat.card K + 1) :
    GGTorusTorW p 6 (Nat.card K + 1) 7 (CartanMatrix.E 7) CoxeterMatrix.E₇
      (TableBExc.RecipeGroup .E7 K) (TableBExc.RecipeID .E7 K) := by
  intro L _ _ ψ A hTB
  obtain ⟨e, -, E, hE, hcard, hSC, hA⟩ := exists_e7_model_of_tbGroup ψ A hTB
  have hr : p ^ 6 ≤ Nat.card E := by rw [hcard]; exact hTB.2.2.2.2.2.1
  exact GGTorusTorData.of_inner_model e hA (ggTorusTorData_E7_plus hp hp2 hq E hE hr hSC)

theorem ggTBTorE7_holds : GGTBTorE7 := by
  intro p hp hp2 lab _ htag hpm
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hpm
  subst htag
  by_cases hminus : p ∣ 2 ^ n - 1
  · have hqpos : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have hplus : ¬ p ∣ 2 ^ n + 1 := by
      intro h
      have htwo : p ∣ 2 := by
        have := Nat.dvd_sub h hminus
        convert this using 1 <;> omega
      exact hp2 ((Nat.prime_two.dvd_iff_eq hp.ne_one).mp htwo).symm
    simp only [ggTorEnn, ggTorMpm, hplus, hminus, ↓reduceIte, Nat.sub_zero]
    intro Q hQ
    obtain ⟨K, i1, i2, hK, hQ'⟩ := hQ
    have : CharP K 2 := charP_two_of_card hK
    have hq : p ∣ Nat.card K - 1 := by rwa [hK]
    refine ⟨K, i1, i2, hK, hQ', ?_⟩
    change GGTorusTorW p 7 (2 ^ n - 1) 7 (CartanMatrix.E 7) CoxeterMatrix.E₇
      (TableBExc.RecipeGroup .E7 K) (TableBExc.RecipeID .E7 K)
    rw [← hK]
    exact ggTorusTorW_recipe_E7_split hp hp2 hq
  · have hplus : p ∣ 2 ^ n + 1 := (hp.dvd_mul.mp hpm).resolve_left hminus
    simp only [ggTorEnn, ggTorMpm, hplus, hminus, ↓reduceIte]
    intro Q hQ
    obtain ⟨K, i1, i2, hK, hQ'⟩ := hQ
    have : CharP K 2 := charP_two_of_card hK
    have hq : p ∣ Nat.card K + 1 := by rwa [hK]
    refine ⟨K, i1, i2, hK, hQ', ?_⟩
    change GGTorusTorW p 6 (2 ^ n + 1) 7 (CartanMatrix.E 7) CoxeterMatrix.E₇
      (TableBExc.RecipeGroup .E7 K) (TableBExc.RecipeID .E7 K)
    rw [← hK]
    exact ggTorusTorW_recipe_E7_plus hp hp2 hq

end CFSG.StandardType
