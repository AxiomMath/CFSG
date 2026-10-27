module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesE6QPlusThreeDiag
public import CFSG.LocalAnalysis.StandardType.GGLangRootSL2Rational
public import CFSG.LocalAnalysis.StandardType.GGTBJE6TwoBase
public import CFSG.LocalAnalysis.StandardType.GGTBJE6TwoClass
public import CFSG.LocalAnalysis.StandardType.GGTBJE6TwoWeylPair
public import CFSG.LocalAnalysis.StandardType.GGTBJE6TwoSolv
public import CFSG.LocalAnalysis.StandardType.GGTBJE6TwoWeylFixed
public import CFSG.LocalAnalysis.StandardType.GGTBJTwE6SplitWeyl

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.Lattice CFSG.StandardType.ExcFrames.E6QPlusThree CFSG.RankThree.PartOne.KE6
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.StandardType.E6Two

open scoped MatrixGroups Matrix


private theorem iform_neg_right' {τ : Tag} (x y : Fin τ.rank → ℤ) : iform x (-y) = -iform x y := by
  rw [← neg_one_smul ℤ y, CFSG.LieType.Steinberg.Adjoint.iform_smul_right]
  ring

private theorem iform_neg_left' {τ : Tag} (x y : Fin τ.rank → ℤ) : iform (-x) y = -iform x y := by
  rw [← neg_one_smul ℤ x, CFSG.LieType.Steinberg.Adjoint.iform_smul_left]
  ring

private noncomputable abbrev fa {K : Type} [Field K] (ζ : Kˣ) (hζ : ζ ^ 3 = 1) (t : Fin Tag.F4.rank → ZMod 3) :
    Fin Tag.E6.rank → Kˣ :=
  TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.twE6ThreeFrame t)

theorem e6Two_weylPoint {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    (S : LangSetup .E6 (AlgebraicClosure K) 5) (hq : S.D.q = Nat.card K)
    (hρ : ∀ β, IsRoot .E6 β → S.ρ β = e6W0 • β)
    {ζ : (AlgebraicClosure K)ˣ} {hζ : ζ ^ 3 = 1} (hζo : orderOf ζ = 3)
    (hT : ∀ s, e6ThreeDiag ζ hζ s ∈ S.D.torus)
    (t : Fin Tag.F4.rank → ZMod 3) (ht : t ≠ 0)
    (i : KernelComponent
      (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.twE6ThreeFrame t))))
    (hns : ¬ Group.IsSolvable ↥(rationalComponent S.ρ S.Γ
      (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.twE6ThreeFrame t))) i))
    {δ : Fin Tag.E6.rank → ℤ}
    (hδ : δ ∈ componentRoots
      (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.twE6ThreeFrame t))) i) :
    (permLattice TwistTag.E6.perm δ = δ →
      rootSL2 .E6 (AlgebraicClosure K) δ WSL ∈ rationalComponent S.ρ S.Γ
        (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.twE6ThreeFrame t))) i) ∧
    (permLattice TwistTag.E6.perm δ ≠ δ →
      rootSL2 .E6 (AlgebraicClosure K) δ WSL *
          rootSL2 .E6 (AlgebraicClosure K) (permLattice TwistTag.E6.perm δ) WSL ∈
        rationalComponent S.ρ S.Γ
          (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.twE6ThreeFrame t))) i) := by
  classical
  haveI hchar : CharP (AlgebraicClosure K) 2 :=
    (Algebra.charP_iff (K := K) (L := AlgebraicClosure K) 2).symm.mpr inferInstance
  have hq2 : S.D.q = 2 := hq.trans hK
  have hTa : rootDiagUnit Tag.E6 (fa ζ hζ t) ∈ S.D.torus := by
    have := hT (Multiplicative.ofAdd t)
    rwa [e6ThreeDiag_apply] at this
  have hρ' : ∀ β, IsRoot Tag.E6 β → S.ρ β = -permLattice TwistTag.E6.perm β := fun β hβ => by
    rw [hρ β hβ, e6W0_smul]
    rfl
  have hΨ := isRootComponent_componentRoots (χ := rootCharHom (fa ζ hζ t)) i
  have hδ' := hδ
  obtain ⟨hδk, hδi⟩ := hδ
  have hδr : IsRoot Tag.E6 δ := hδk.1
  have hδrat : δ ∈ rationalRoots S.ρ (rootCharHom (fa ζ hζ t)) i := ⟨0, δ, hδ', rfl⟩
  refine ⟨fun hfix => ?_, fun hne => ?_⟩
  · have hSρδ : S.ρ δ = -δ := (hρ' δ hδr).trans (congrArg Neg.neg hfix)
    have hkerδ : kerF t δ := (rootChar_eq_one_iff_kerF hζo t δ).1 hδk.2
    have h22 : ∀ x, IsRoot Tag.E6 x → iform x x = 2 := fun x hx =>
      CFSG.LieType.Chevalley.EvenOddRadical.iform_self_eq_two (Or.inr (Or.inl rfl)) hx
    have hδΨ : δ ∈ componentRoots (rootCharHom (fa ζ hζ t)) i := hδ'
    have hadj : ∀ x, IsRoot Tag.E6 x → rootChar (fa ζ hζ t) x = 1 → iform x δ ≠ 0 →
        x ∈ componentRoots (rootCharHom (fa ζ hζ t)) i := fun x hxr hxc hxδ =>
      ⟨⟨hxr, hxc⟩, (mk_eq_of_iform_ne_zero (α := ⟨x, ⟨hxr, hxc⟩⟩) (β := ⟨δ, hδk⟩) hxδ).trans hδi⟩
    rcases fixed_cases t ht hδr hfix hkerδ with
      ⟨γ, hγr, hγne, hγk, hγδ⟩ | ⟨α, hαδ, hαfix, hαk, hclosed⟩
    ·
      obtain ⟨γ', hγ'def⟩ : ∃ γ' : Fin Tag.E6.rank → ℤ, γ' = permLattice TwistTag.E6.perm γ :=
        ⟨_, rfl⟩
      have hγ'r : IsRoot Tag.E6 γ' := by
        rw [hγ'def]
        exact hγr.permLattice (TwistTag.cartan_perm TwistTag.E6)
      have hργ : S.ρ γ = -γ' := by rw [hγ'def]; exact hρ' γ hγr
      obtain ⟨hρρ, h0, -, -⟩ := LangRat.rho_orthogonal_of_latPerm_ne S (Or.inr (Or.inl rfl))
        TwistTag.E6.perm (TwistTag.cartan_perm TwistTag.E6) (ε := -1) (Or.inr rfl)
        (fun β hβ => by
          show S.ρ β = (-1 : ℤ) • permLattice TwistTag.E6.perm β
          rw [hρ' β hβ, neg_one_zsmul]) hγr hγne
      have h3 : iform γ γ' = 0 := by
        rw [hργ, iform_neg_right'] at h0
        omega
      have h2 : iform δ γ' = -1 := by
        have h1 := iform_permLattice_E6 δ γ
        rw [hfix] at h1
        rw [hγ'def]
        exact h1.trans ((CFSG.LieType.Steinberg.Adjoint.iform_comm δ γ).trans hγδ)
      have hργ' : S.ρ γ' = -γ := by
        have h1 : S.ρ (S.ρ γ) = γ := hρρ
        rw [hργ, S.frob.neg_eq] at h1
        exact neg_eq_iff_eq_neg.1 h1
      have hγc : rootChar (fa ζ hζ t) γ = 1 := (rootChar_eq_one_iff_kerF hζo t γ).2 hγk
      have hγ'c : rootChar (fa ζ hζ t) γ' = 1 := by
        have h1 := S.frob.rootChar_eq (fa ζ hζ t) hTa γ hγr
        rw [hργ, CFSG.RankThree.Chevalley.rootChar_neg', hγc, one_pow, inv_eq_one] at h1
        exact h1
      have hγΨ := hadj γ hγr hγc (by rw [hγδ]; decide)
      have hγ'Ψ := hadj γ' hγ'r hγ'c (by rw [iform_comm, h2]; decide)
      have hne1 : γ ≠ -δ := fun h => by
        rw [h, iform_neg_left', h22 δ hδr] at hγδ
        omega
      have hs1 : IsRoot Tag.E6 (γ + δ) :=
        isRoot_add_of_iform_neg hγr hδr hne1 (by rw [hγδ]; decide)
      have hne2 : δ ≠ -γ' := fun h => by
        rw [h, iform_neg_left', h22 γ' hγ'r] at h2
        omega
      have hs2 : IsRoot Tag.E6 (δ + γ') :=
        isRoot_add_of_iform_neg hδr hγ'r hne2 (by rw [h2]; decide)
      have h4 : iform (γ + δ) γ' = -1 := by
        rw [iform_add_left, h3, h2]
        norm_num
      have hne3 : γ + δ ≠ -γ' := fun h => by
        rw [h, iform_neg_left', h22 γ' hγ'r] at h4
        omega
      have hs3 : IsRoot Tag.E6 (γ + δ + γ') :=
        isRoot_add_of_iform_neg hs1 hγ'r hne3 (by rw [h4]; decide)
      have hΨ1 := hΨ.add_mem γ hγΨ δ hδΨ hs1
      have hΨ2 := hΨ.add_mem δ hδΨ γ' hγ'Ψ hs2
      have hΨ3 := hΨ.add_mem (γ + δ) hΨ1 γ' hγ'Ψ hs3
      have hmem : ∀ r ∈ aChainRoots (![γ, δ, γ'] : Fin 3 → Fin Tag.E6.rank → ℤ),
          r ∈ rationalRoots S.ρ (rootCharHom (fa ζ hζ t)) i := by
        have hΨ0 : ∀ x ∈ componentRoots (rootCharHom (fa ζ hζ t)) i,
            x ∈ rationalRoots S.ρ (rootCharHom (fa ζ hζ t)) i := fun x hx => ⟨0, x, hx, rfl⟩
        have hsum : ∀ p l : Fin 3, p ≤ l →
            ∑ k ∈ Finset.Icc p l, (![γ, δ, γ'] : Fin 3 → Fin Tag.E6.rank → ℤ) k ∈
              componentRoots (rootCharHom (fa ζ hζ t)) i := by
          intro p l hpl
          fin_cases p <;> fin_cases l <;> simp at hpl <;> simp [Finset.sum_Icc_succ_top]
          · exact hγΨ
          · rw [show Finset.Icc (0 : Fin 3) 1 = {0, 1} from by decide,
              Finset.sum_pair (by decide)]
            simpa using hΨ1
          · rw [show Finset.Icc (0 : Fin 3) 2 = {0, 1, 2} from by decide,
              Finset.sum_insert (by decide), Finset.sum_pair (by decide)]
            simpa [add_assoc] using hΨ3
          · exact hδΨ
          · rw [show Finset.Icc (1 : Fin 3) 2 = {1, 2} from by decide,
              Finset.sum_pair (by decide)]
            simpa using hΨ2
          · exact hγ'Ψ
        rintro r ⟨p, l, hpl, hr | hr⟩
        · rw [hr]; exact hΨ0 _ (hsum p l hpl)
        · rw [hr]; exact hΨ0 _ (hΨ.neg_mem _ (hsum p l hpl))
      exact fixedWeyl_mem_rationalComponent_of_a3 S (k := K) hK hq2 hρ i hγr hδr hγ'r hγδ h2 h3
        hργ hSρδ hργ' hmem
    ·
      exfalso
      have hαr : IsRoot Tag.E6 α := hαδ.isRoot_snd
      have hδα : iform δ α = -1 := by
        have h2' := hαδ.two_iform
        rw [h22 δ hδr] at h2'
        omega
      have hαc : rootChar (fa ζ hζ t) α = 1 := (rootChar_eq_one_iff_kerF hζo t α).2 hαk
      have hαΨ := hadj α hαr hαc (by rw [iform_comm, hδα]; decide)
      have hρα : S.ρ α = -α := (hρ' α hαr).trans (congrArg Neg.neg hαfix)
      have hρA2 : ∀ x ∈ a2Roots δ α, S.ρ x = -x := by
        intro x hx
        simp only [a2Roots, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with hx | hx | hx | hx | hx | hx <;> rw [hx]
        · exact hSρδ
        · rw [S.frob.neg_eq, hSρδ]
        · exact hρα
        · rw [S.frob.neg_eq, hρα]
        · rw [hρ _ hαδ.isRoot_add, smul_add, ← hρ δ hδr, ← hρ α hαr, hSρδ, hρα]
          abel
        · rw [S.frob.neg_eq, hρ _ hαδ.isRoot_add, smul_add, ← hρ δ hδr, ← hρ α hαr, hSρδ, hρα]
          abel
      have hZadj : ∀ z y : Fin Tag.E6.rank → ℤ, y ∈ a2Roots δ α → iform z y ≠ 0 →
          iform z δ ≠ 0 ∨ iform z α ≠ 0 := by
        intro z y hy hzy
        simp only [a2Roots, Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rcases hy with hy | hy | hy | hy | hy | hy <;> rw [hy] at hzy
        · exact Or.inl hzy
        · exact Or.inl (by rwa [iform_neg_right', neg_ne_zero] at hzy)
        · exact Or.inr hzy
        · exact Or.inr (by rwa [iform_neg_right', neg_ne_zero] at hzy)
        · by_contra hcon
          obtain ⟨hc1, hc2⟩ := not_or.1 hcon
          rw [iform_add_right, not_not.1 hc1, not_not.1 hc2] at hzy
          exact hzy (by norm_num)
        · by_contra hcon
          obtain ⟨hc1, hc2⟩ := not_or.1 hcon
          rw [iform_neg_right', iform_add_right, not_not.1 hc1, not_not.1 hc2] at hzy
          exact hzy (by norm_num)
      have hZeq : componentRoots (rootCharHom (fa ζ hζ t)) i = a2Roots δ α := by
        apply Set.Subset.antisymm
        · intro x hx
          obtain ⟨hxk, hxi⟩ := hx
          have hrel : Relation.EqvGen
              (fun u v : kernelRoots (rootCharHom (fa ζ hζ t)) =>
                (u : Fin Tag.E6.rank → ℤ) ⬝ᵥ (Tag.E6.symmetrizedCartan *ᵥ
                  (v : Fin Tag.E6.rank → ℤ)) ≠ 0) ⟨x, hxk⟩ ⟨δ, hδk⟩ :=
            Quotient.exact (hxi.trans hδi.symm)
          have key : ∀ u v : kernelRoots (rootCharHom (fa ζ hζ t)), Relation.EqvGen
              (fun u v : kernelRoots (rootCharHom (fa ζ hζ t)) =>
                (u : Fin Tag.E6.rank → ℤ) ⬝ᵥ (Tag.E6.symmetrizedCartan *ᵥ
                  (v : Fin Tag.E6.rank → ℤ)) ≠ 0) u v →
              ((u : Fin Tag.E6.rank → ℤ) ∈ a2Roots δ α ↔ (v : Fin Tag.E6.rank → ℤ) ∈ a2Roots δ α) := by
            intro u v h
            induction h with
            | rel u v hr =>
              rw [dotProduct_mulVec_eq_iform] at hr
              have hu := (rootChar_eq_one_iff_kerF hζo t u).1 u.2.2
              have hv := (rootChar_eq_one_iff_kerF hζo t v).1 v.2.2
              constructor
              · intro hu'
                exact hclosed v v.2.1 hv (hZadj _ _ hu' (by rwa [iform_comm]))
              · intro hv'
                exact hclosed u u.2.1 hu (hZadj _ _ hv' hr)
            | refl u => exact Iff.rfl
            | symm u v _ ih => exact ih.symm
            | trans u v w _ _ ih1 ih2 => exact ih1.trans ih2
          exact (key _ _ hrel).2 (by simp [a2Roots])
        · intro x hx
          simp only [a2Roots, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
          rcases hx with hx | hx | hx | hx | hx | hx <;> rw [hx]
          · exact hδΨ
          · exact hΨ.neg_mem _ hδΨ
          · exact hαΨ
          · exact hΨ.neg_mem _ hαΨ
          · exact hΨ.add_mem _ hδΨ _ hαΨ hαδ.isRoot_add
          · exact hΨ.neg_mem _ (hΨ.add_mem _ hδΨ _ hαΨ hαδ.isRoot_add)
      exact hns (isSolvable_rationalComponent_of_a2 S hq2 hTa i hαδ hZeq hρA2)
  · exact pairWeyl_mem_rationalComponent S (k' := K) (n := 1) le_rfl (by rw [hq2, pow_one]) hρ'
      i hδrat hne

theorem e6Two_twE6SplitWeyl_mem_rationalComponent
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    (S : LangSetup .E6 (AlgebraicClosure K) 5) (hq : S.D.q = Nat.card K)
    (hρ : ∀ β, IsRoot .E6 β → S.ρ β = e6W0 • β)
    {ζ : (AlgebraicClosure K)ˣ} {hζ : ζ ^ 3 = 1} (hζo : orderOf ζ = 3)
    (hT : ∀ s, e6ThreeDiag ζ hζ s ∈ S.D.torus)
    (t : Fin Tag.F4.rank → ZMod 3) (ht : t ≠ 0)
    (i : KernelComponent
      (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.twE6ThreeFrame t))))
    (hns : ¬ Group.IsSolvable ↥(rationalComponent S.ρ S.Γ
      (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.twE6ThreeFrame t))) i))
    {δ : Fin Tag.E6.rank → ℤ}
    (hδ : δ ∈ componentRoots
      (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.twE6ThreeFrame t))) i) :
    twE6SplitWeyl (AlgebraicClosure K) δ ∈ rationalComponent S.ρ S.Γ
      (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.twE6ThreeFrame t))) i := by
  obtain ⟨h1, h2⟩ := e6Two_weylPoint hK S hq hρ hζo hT t ht i hns hδ
  by_cases hfix : permLattice TwistTag.E6.perm δ = δ
  · have h3 : twE6SplitWeyl (AlgebraicClosure K) δ = rootSL2 .E6 (AlgebraicClosure K) δ WSL :=
      if_pos hfix
    rw [h3]
    exact h1 hfix
  · have h3 : twE6SplitWeyl (AlgebraicClosure K) δ = rootSL2 .E6 (AlgebraicClosure K) δ WSL *
        rootSL2 .E6 (AlgebraicClosure K) (permLattice TwistTag.E6.perm δ) WSL := if_neg hfix
    rw [h3]
    exact h2 hfix

end CFSG.StandardType

end
