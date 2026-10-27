module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigDefs
public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigRoFrame
public import CFSG.LocalAnalysis.StandardType.GGQ2S08RoCloseR4

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Matrix TestLin

variable {G : Type} [Group G] {Bs L : Subgroup G} {x : G}

theorem ggQ2s08_big_roExit_of_facts [Finite G] (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    {B D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J) (hΓ : GGQ2GammaX 3 B Bs x L D J)
    (hCav : 4 ∣ Nat.card ↥(ggAutomizer J Bs)) (M : GGQ2LDatum 3 Bs L x)
    {lab : LargeEvenLabel} (hlab : GGQ2S08BigLabel lab) (hMW : GGQ2LabelWeyl lab M.coxeter)
    (κ : M.V ≃ₗ[ZMod 3] Vn (lab.rank + 1)) (e : Fin lab.rank ≃ M.Λ)
    (s : Fin lab.rank → (Vn (lab.rank + 1) ≃ₗ[ZMod 3] Vn (lab.rank + 1)))
    (Mx : CoxeterMatrix (Fin lab.rank))
    (hMx : ∀ i j, Mx i j = M.coxeter (e i) (e j))
    (hs : ∀ i v, κ (ggLin (p := 3) M.model (M.simple (e i)) (κ.symm v)) = s i v)
    (hsrefl : ∀ i, GGLinRefl (s i)) (hdist : ∀ i j, i ≠ j → s i ≠ s j)
    (hrel : ∀ i j, i ≠ j → (s i * s j) ^ Mx i j = 1)
    (hncomm : ∀ i j, i ≠ j → Mx i j ≠ 2 → s i * s j ≠ s j * s i)
    (hcomp : ∀ f : Fin (lab.rank + 1) → M.V, GGQ2S08ROFrame M f → lab.tag = .twA →
      Even (lab.rank + 1) → GGQ2S08ROComponents M f)
    (g : G) (φ : MulAut ↥Bs) (hInd : GGQ2Ind Bs g φ)
    {r : Vn (lab.rank + 1) ≃ₗ[ZMod 3] Vn (lab.rank + 1)}
    (hr : r ∈ (ggAutomizer (Subgroup.normalizer (ggG0 3 B x L D J : Set G)) Bs).map
      (ggQ2CellLin M κ))
    (hCO : GGQ2S08CoreRO (N := lab.rank + 1)
      (Subgroup.closure
        ((((Subgroup.closure (Set.range s)) :
            Subgroup (Vn (lab.rank + 1) ≃ₗ[ZMod 3] Vn (lab.rank + 1))) :
          Set (Vn (lab.rank + 1) ≃ₗ[ZMod 3] Vn (lab.rank + 1))) ∪ {r, ggQ2CellLin M κ φ}))
      (Subgroup.closure (Set.range s)) r (κ M.xV)) :
    g ∈ Subgroup.normalizer (ggG0 3 B x L D J : Set G) := by
  classical
  let Wsub := Subgroup.closure (Set.range s)
  let R := Subgroup.closure ((Wsub : Set _) ∪ {r, ggQ2CellLin M κ φ})
  let A := (ggAutomizer ⊤ Bs).map (ggQ2CellLin M κ)
  let Mg := (ggAutomizer (Subgroup.normalizer (ggG0 3 B x L D J : Set G)) Bs).map
      (ggQ2CellLin M κ)
  have hAJ : ggAutomizer J Bs ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at hCav
    exact absurd (Nat.le_of_dvd one_pos hCav) (by norm_num)
  have hWmap : (ggAutomizer L Bs).map (ggQ2CellLin M κ) = Wsub :=
    ggQ2Cell_map_automizer_L M κ e s hs
  have hH := ggQ2Cell_hyp hLB hP hS hΓ hAJ M κ rfl hWmap
  have hφA : φ ∈ ggAutomizer ⊤ Bs :=
    mem_ggAutomizer_iff.mpr ⟨g, Subgroup.mem_top _, hInd.1, hInd.2⟩
  obtain ⟨htag, hEven, f, hf, hRmono, hM0⟩ :=
    ggQ2s08_big_roFrame_of_facts (M := M) hlab hMW κ e s Mx hMx hs hsrefl hdist hrel hncomm hCO
  have hQ : GGQ2S08ROComponents M f := hcomp f hf htag hEven
  have hRA : R ≤ A := by
    change Subgroup.closure ((Wsub : Set _) ∪ {r, ggQ2CellLin M κ φ}) ≤ A
    refine (Subgroup.closure_le _).mpr ?_
    rintro a (ha | ha)
    · exact le_trans hH.W_le hH.le ha
    · rcases ha with rfl | rfl
      · exact hH.le hr
      · exact Subgroup.mem_map.mpr ⟨φ, hφA, rfl⟩
  have hM0le : GGQ2S08M0 R Wsub r (κ M.xV) ≤ Mg := by
    unfold GGQ2S08M0
    refine (Subgroup.closure_le _).mpr ?_
    rintro a (ha | ha)
    · rcases ha with haW | har
      · exact hH.W_le haW
      · have har' : a = r := Set.mem_singleton_iff.mp har
        subst har'
        exact hr
    · obtain ⟨haR, c, hc, hcx⟩ := ha
      have hkey : ∀ c : ZMod 3, c ≠ 0 → c = 1 ∨ c = -1 := by decide
      have hfix : FixesLine (κ M.xV) a := by
        rcases hkey c hc with h1 | h1
        · exact Or.inl (hcx.trans (by simp [h1]))
        · exact Or.inr (hcx.trans (by
            rw [h1]; funext i
            simp only [Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
            first
              | exact neg_one_mul _
              | rw [neg_one_mul]
              | ring_nf))
      exact hH.stab_mem a (hRA haR) hfix
  have hD' : ∀ g' : M.V ≃ₗ[ZMod 3] M.V, GGQ2S08MonoEven f g' →
      ∃ (k : G) (φ : MulAut ↥Bs), GGQ2Ind Bs k φ ∧
        k ∈ Subgroup.normalizer (ggG0 3 B x L D J : Set G) ∧
        ggLin (p := 3) M.model φ = g' := by
    intro g' hg'
    have hmono : GGQ2S08MonoEven (fun i => κ (f i)) (ggLinConj κ g') := by
      obtain ⟨σ, ε, hε, hprod, hg'f⟩ := hg'
      refine ⟨σ, ε, hε, hprod, fun i => ?_⟩
      exact (ggLinConj_apply κ g' (κ (f i))).trans
        ((congrArg (fun y => κ (g' y)) (LinearEquiv.symm_apply_apply κ (f i))).trans
          ((congrArg κ (hg'f i)).trans (map_smul κ (ε i) (f (σ i)))))
    have haMg : ggLinConj κ g' ∈ Mg := hM0le ((hM0 (ggLinConj κ g')).mpr hmono)
    obtain ⟨φ', hφ'mem, hφ'eq⟩ := Subgroup.mem_map.mp haMg
    obtain ⟨k, hkG0, hkN, hk⟩ := mem_ggAutomizer_iff.mp hφ'mem
    exact ⟨k, φ', ⟨hkN, hk⟩, hkG0, (ggLinConj κ).injective hφ'eq⟩
  have h2 : 2 ≤ lab.rank + 1 := by
    have h9 : 9 ≤ lab.rank := hlab.2.2
    omega
  have htR : ggQ2CellLin M κ φ ∈ R := Subgroup.subset_closure (by simp)
  have hmonoT := (hRmono (ggQ2CellLin M κ φ)).mp htR
  have hMono : GGQ2S08Mono f (ggLin (p := 3) M.model φ) := by
    obtain ⟨σ, ε, hε, htf⟩ := hmonoT
    refine ⟨σ, ε, hε, fun i => ?_⟩
    have h1 : ggQ2CellLin M κ φ (κ (f i)) =
        κ (ggLin (p := 3) M.model φ (f i)) :=
      (ggQ2CellLin_apply M κ φ (κ (f i))).trans
        (congrArg (fun y => κ (ggLin (p := 3) M.model φ y))
          (LinearEquiv.symm_apply_apply κ (f i)))
    have hkey : κ (ggLin (p := 3) M.model φ (f i)) = ε i • κ (f (σ i)) :=
      h1.symm.trans (htf i)
    have h2' := congrArg κ.symm hkey
    simpa only [map_smul, LinearEquiv.symm_apply_apply] using h2'
  exact ggQ2s08_roClose_of_components hLB hP hS hCav M h2 f hf hQ hD' g φ hInd hMono

theorem ggQ2s08_big_roExit [Finite G] (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    {B D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J) (hΓ : GGQ2GammaX 3 B Bs x L D J)
    (hCav : 4 ∣ Nat.card ↥(ggAutomizer J Bs)) (M : GGQ2LDatum 3 Bs L x)
    {lab : LargeEvenLabel} (hlab : GGQ2S08BigLabel lab) (hMW : GGQ2LabelWeyl lab M.coxeter)
    (hF3 : lab.tag = .twA → ¬ 3 ∣ lab.rank + 1)
    (κ : M.V ≃ₗ[ZMod 3] Vn (lab.rank + 1)) (e : Fin lab.rank ≃ M.Λ)
    (s : Fin lab.rank → (Vn (lab.rank + 1) ≃ₗ[ZMod 3] Vn (lab.rank + 1)))
    (Mx : CoxeterMatrix (Fin lab.rank)) (H : Submodule (ZMod 3) (Vn (lab.rank + 1)))
    (hMx : ∀ i j, Mx i j = M.coxeter (e i) (e j))
    (hs : ∀ i v, κ (ggLin (p := 3) M.model (M.simple (e i)) (κ.symm v)) = s i v)
    (hD : GGQ2S08BigLin s Mx (κ M.xV) H)
    (hcomp : ∀ f : Fin (lab.rank + 1) → M.V, GGQ2S08ROFrame M f → lab.tag = .twA →
      Even (lab.rank + 1) → ¬ 3 ∣ lab.rank + 1 → GGQ2S08ROComponents M f)
    (g : G) (φ : MulAut ↥Bs) (hInd : GGQ2Ind Bs g φ)
    {r : Vn (lab.rank + 1) ≃ₗ[ZMod 3] Vn (lab.rank + 1)}
    (hr : r ∈ (ggAutomizer (Subgroup.normalizer (ggG0 3 B x L D J : Set G)) Bs).map
      (ggQ2CellLin M κ))
    (hCO : GGQ2S08CoreRO (N := lab.rank + 1)
      (Subgroup.closure
        ((((Subgroup.closure (Set.range s)) :
            Subgroup (Vn (lab.rank + 1) ≃ₗ[ZMod 3] Vn (lab.rank + 1))) :
          Set (Vn (lab.rank + 1) ≃ₗ[ZMod 3] Vn (lab.rank + 1))) ∪ {r, ggQ2CellLin M κ φ}))
      (Subgroup.closure (Set.range s)) r (κ M.xV)) :
    g ∈ Subgroup.normalizer (ggG0 3 B x L D J : Set G) := by
  exact ggQ2s08_big_roExit_of_facts hLB hP hS hΓ hCav M hlab hMW κ e s Mx hMx hs hD.srefl
    hD.dist hD.rel hD.ncomm (fun f hf htag hEven => hcomp f hf htag hEven (hF3 htag))
    g φ hInd hr hCO

end CFSG.StandardType

end
