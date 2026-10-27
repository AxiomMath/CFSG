module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigDefs
public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigBridge
public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigShapeAInput
public import CFSG.LocalAnalysis.StandardType.GGQ2S08RoComponentsThreeInput
public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigRoExit
public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigATest
public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigABound
public import CFSG.LocalAnalysis.StandardType.GGQ2S08DatumCoxeter

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Matrix TestLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem ggQ2s08as_linRefl_conj {V V' : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [AddCommGroup V'] [Module (ZMod 3) V'] (κ : V ≃ₗ[ZMod 3] V')
    {T : V ≃ₗ[ZMod 3] V} (h : GGLinRefl T) : GGLinRefl (ggLinConj κ T) := by
  rw [ggDepA_linRefl_iff (p := 3) (by norm_num : (3 : ℕ) ≠ 2)] at h ⊢
  obtain ⟨c, f, hcf, hT⟩ := h
  refine ⟨κ c, f.comp κ.symm.toLinearMap, ?_, fun v => ?_⟩
  · change f (κ.symm (κ c)) = 2
    rw [LinearEquiv.symm_apply_apply]
    exact hcf
  · rw [ggLinConj_apply, hT (κ.symm v)]
    change κ (κ.symm v - f (κ.symm v) • c) = v - f (κ.symm v) • κ c
    simp only [map_sub, map_smul, LinearEquiv.apply_symm_apply]

theorem ggQ2s08_bigA_input_of_components (hB : GGQ2S08ROComponentsThreeInput)
    (hKG : GGReflClassLargeThree)
    (hTBW : GGTBWNormInputOn (fun p lab => p = 3 ∧ GGQ2S08BigLabel lab))
    (hCen : GGQ2S08BigCenterInput) (hOut : GGQ2S08BigInnerPartInput)
    (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput) (hΓi : GGQ2GammaXOffI1Input)
    (hTBN : GGQ2TableBNbr) : GGQ2S08BigShapeAInput := by
  classical
  intro G _ _ B Bs x L D J hS hI1 hCav hnc M hA lab hlab hmark hInn hMW htag h3 h12
    g φ hInd hRefl
  obtain ⟨e, he⟩ : ∃ e : Fin lab.rank ≃ M.Λ,
      M.coxeter = (CoxeterMatrix.A lab.rank).reindex e := by
    simpa [GGQ2LabelWeyl, htag] using hMW
  have hcard : Fintype.card M.Λ = lab.rank := by
    simpa using (Fintype.card_congr e).symm
  have hfr : Module.finrank (ZMod 3) M.V = lab.rank + 1 := by
    rw [hA.2.2.2.1, hcard]
  haveI : Finite M.V := Finite.of_equiv (Additive ↥Bs) M.model.toEquiv
  haveI : Module.Finite (ZMod 3) M.V := Module.Finite.of_finite
  let bV : Module.Basis (Fin (lab.rank + 1)) (ZMod 3) M.V :=
    Module.finBasisOfFinrankEq (ZMod 3) M.V hfr
  let κ : M.V ≃ₗ[ZMod 3] Vn (lab.rank + 1) := bV.equivFun
  let Mx : CoxeterMatrix (Fin lab.rank) := CoxeterMatrix.A lab.rank
  have hMx : ∀ i j, Mx i j = M.coxeter (e i) (e j) := fun i j => by
    change CoxeterMatrix.A lab.rank i j = M.coxeter (e i) (e j)
    rw [he, CoxeterMatrix.reindex_apply]
    simp
  let T : Fin lab.rank → M.V ≃ₗ[ZMod 3] M.V :=
    fun i => ggLin (p := 3) M.model (M.simple (e i))
  let s : Fin lab.rank → (Vn (lab.rank + 1) ≃ₗ[ZMod 3] Vn (lab.rank + 1)) :=
    fun i => ggLinConj κ (T i)
  have hs : ∀ i v, κ (ggLin (p := 3) M.model (M.simple (e i)) (κ.symm v)) = s i v :=
    fun i v => rfl
  have hWmap : (ggAutomizer L Bs).map (ggQ2CellLin M κ) = Subgroup.closure (Set.range s) :=
    ggQ2Cell_map_automizer_L M κ e s hs
  have h6 : ∀ i j : M.Λ, i ≠ j → M.coxeter i j ≠ 6 :=
    (ggQ2s08d_label_connected hlab M.coxeter hMW).2
  have hpair : ∀ i j : M.Λ, i ≠ j →
      LinearIndependent (ZMod 3) ![M.coroot i, M.coroot j] :=
    fun i j hij => ggQ2s08_big_pairIndep M hMW htag (by omega) i j hij
  have hsmul : ∀ i j, s i * s j = ggLinConj κ (T i * T j) := fun i j => by
    show ggLinConj κ (T i) * ggLinConj κ (T j) = ggLinConj κ (T i * T j)
    rw [← map_mul]
  have hsrefl : ∀ i, GGLinRefl (s i) := fun i =>
    ggQ2s08as_linRefl_conj κ (ggQ2s08d_simple_refl M (e i)).2.1
  have hdist : ∀ i j, i ≠ j → s i ≠ s j := by
    intro i j hij h
    have hij' : e i ≠ e j := fun hh => hij (e.injective hh)
    have hf := (ggQ2s08d_coxeter_facts_of_pair M h6 (e i) (e j) hij'
      (hpair (e i) (e j) hij')).2.1
    exact hf ((ggLinConj κ).injective h)
  have hrel : ∀ i j, i ≠ j → (s i * s j) ^ Mx i j = 1 := by
    intro i j hij
    have hij' : e i ≠ e j := fun hh => hij (e.injective hh)
    have hf := (ggQ2s08d_coxeter_facts_of_pair M h6 (e i) (e j) hij'
      (hpair (e i) (e j) hij')).1
    rw [hMx i j, hsmul i j, ← map_pow, hf, map_one]
  have hncomm : ∀ i j, i ≠ j → Mx i j ≠ 2 → s i * s j ≠ s j * s i := by
    intro i j hij h2 h
    have hij' : e i ≠ e j := fun hh => hij (e.injective hh)
    have hf := (ggQ2s08d_coxeter_facts_of_pair M h6 (e i) (e j) hij'
      (hpair (e i) (e j) hij')).2.2.2
    have hm : M.coxeter (e i) (e j) ≠ 2 := by
      rw [← hMx i j]
      exact h2
    exact hf hm ((ggLinConj κ).injective (by simpa [hsmul i j, hsmul j i] using h))
  have hcomp : ∀ f : Fin (lab.rank + 1) → M.V, GGQ2S08ROFrame M f → lab.tag = .twA →
      Even (lab.rank + 1) → GGQ2S08ROComponents M f := by
    intro f hf _ hEven
    exact hB hS hI1 M hA hmark.2.2 ⟨htag, hmark.1⟩ hlab hMW hEven h3 f hf
  let P : Subgroup (Vn (lab.rank + 1) ≃ₗ[ZMod 3] Vn (lab.rank + 1)) → Prop := fun A =>
    ∀ R : Subgroup (Vn (lab.rank + 1) ≃ₗ[ZMod 3] Vn (lab.rank + 1)),
      R ≤ A → 8 * Nat.card R < 3 ^ (lab.rank * (lab.rank - 1) / 2)
  have hPA : P ((ggAutomizer ⊤ Bs).map (ggQ2CellLin M κ)) :=
    ggQ2s08_bigA_bound hTBW hCen hOut hS hnc M hA hlab hmark.2.2 hInn hMW h12 κ
  let Q : (Vn (lab.rank + 1) ≃ₗ[ZMod 3] Vn (lab.rank + 1)) →
      (Vn (lab.rank + 1) ≃ₗ[ZMod 3] Vn (lab.rank + 1)) → Prop := fun r t =>
    GGQ2S08CoreRO (N := lab.rank + 1)
      (Subgroup.closure
        (((Subgroup.closure (Set.range s) :
          Subgroup (Vn (lab.rank + 1) ≃ₗ[ZMod 3] Vn (lab.rank + 1))) :
          Set (Vn (lab.rank + 1) ≃ₗ[ZMod 3] Vn (lab.rank + 1))) ∪ {r, t}))
      (Subgroup.closure (Set.range s)) r (κ M.xV)
  have htest : ∀ A Mg : Subgroup (Vn (lab.rank + 1) ≃ₗ[ZMod 3] Vn (lab.rank + 1)),
      TestHyp (Subgroup.closure (Set.range s)) (κ M.xV) A Mg → P A →
      ∀ r ∈ Mg, IsRefl r → ¬ FixesLine (κ M.xV) r →
      ∀ t ∈ A, IsRefl t → ¬ FixesLine (κ M.xV) t → t ∈ Mg ∨ Q r t := by
    intro A Mg hT hPAT r hr hrr hrx t ht htr htx
    have hT' : TestHyp ((ggAutomizer L Bs).map (ggQ2CellLin M κ)) (κ M.xV) A Mg :=
      hWmap.symm ▸ hT
    have hres := ggQ2s08_bigA_test hKG M hA hlab hMW htag h3 h12 κ hT' hPAT
      hr hrr hrx ht htr htx
    rcases hres with hmem | hco
    · exact Or.inl hmem
    · refine Or.inr ?_
      have hf := congrArg (fun A : Subgroup (Vn (lab.rank + 1) ≃ₗ[ZMod 3] Vn (lab.rank + 1)) =>
          GGQ2S08CoreRO (N := lab.rank + 1)
            (Subgroup.closure
              (((A : Set (Vn (lab.rank + 1) ≃ₗ[ZMod 3] Vn (lab.rank + 1))) ∪ {r, t})))
            A r (κ M.xV)) hWmap
      exact hf.mp hco
  have hQ : ∀ r ∈ (ggAutomizer (Subgroup.normalizer (ggG0 3 B x L D J : Set G)) Bs).map
        (ggQ2CellLin M κ), IsRefl r → ¬ FixesLine (κ M.xV) r →
        Q r (ggQ2CellLin M κ φ) →
        g ∈ Subgroup.normalizer (ggG0 3 B x L D J : Set G) := by
    intro r hr _ _ hQrt
    refine ggQ2s08_big_roExit_of_facts hLB hP hS (hΓi hS rfl hI1 hCav) hCav M hlab hMW
      κ e s Mx hMx hs hsrefl hdist hrel hncomm hcomp g φ hInd hr ?_
    exact hQrt
  exact ggQ2s08_cell_of_test_Q hLB hP hΓi hTBN hS hI1 hCav M κ rfl hWmap P hPA Q htest
    g φ hInd hRefl hQ

end CFSG.StandardType

end
