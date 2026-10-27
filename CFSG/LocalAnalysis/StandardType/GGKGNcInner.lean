module

public import CFSG.LocalAnalysis.StandardType.GGKGNotCDefs

public section

namespace CFSG.StandardType.KG

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.RootAut
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple CFSG.StandardType.RecipeExcLang
  CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie CFSG.LocalAnalysis.GLTheoremA.KD264Lie.ExcUntw
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.PartOne.KE CFSG.Timmesfeld
  CFSG.ClassicalInvolution.WeakCT CFSG.Assembly.LowTwoRank
open scoped MatrixGroups Matrix
open CFSG.LocalAnalysis.GLTheoremA.CanonTriL

theorem kgNotC_rationalComponent_typeA
    {τ : CFSG.Blueprint.Chevalley.Tag}
    {L : Type}
    [Field L]
    [IsAlgClosed L]
    {p₀ : ℕ}
    (S : CFSG.HardMathSupport.Timmesfeld.LangTorus.LangSetup τ L p₀)
    {p : ℕ}
    (hp : Nat.Prime p)
    {a : Fin τ.rank → Lˣ}
    (hT : CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit τ a ∈ S.D.torus)
    (hap : ∀ (i : Fin τ.rank), a i ^ p = 1)
    (h1 : CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit τ a ≠ 1)
    (i : CFSG.LieType.Chevalley.KernelComponent (τ := τ) (M := Lˣ)
      (CFSG.LieType.AlgebraicGroups.rootCharHom a))
    (hA : 1 ≤
        CFSG.HardMathSupport.Timmesfeld.LangTorus.compRank
          (CFSG.LieType.Chevalley.componentRoots (CFSG.LieType.AlgebraicGroups.rootCharHom a) i) ∧
      (CFSG.LieType.Chevalley.componentRoots (CFSG.LieType.AlgebraicGroups.rootCharHom a) i).ncard =
        CFSG.HardMathSupport.Timmesfeld.LangTorus.compRank
            (CFSG.LieType.Chevalley.componentRoots (CFSG.LieType.AlgebraicGroups.rootCharHom a) i) *
          (CFSG.HardMathSupport.Timmesfeld.LangTorus.compRank
              (CFSG.LieType.Chevalley.componentRoots (CFSG.LieType.AlgebraicGroups.rootCharHom a) i)
                +
            1))
    (hqs : CFSG.IsQuasisimple
      ↥(CFSG.HardMathSupport.Timmesfeld.LangTorus.rationalComponent S.ρ S.Γ
        (CFSG.LieType.AlgebraicGroups.rootCharHom a) i)) :
    CFSG.StandardType.KG.KGNotCLieType (ringChar L)
      ↥(CFSG.HardMathSupport.Timmesfeld.LangTorus.rationalComponent S.ρ S.Γ
        (CFSG.LieType.AlgebraicGroups.rootCharHom a) i) := by
  obtain ⟨ν, f, -, -, -, hmodel⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.RationalModel.rationalComponent_typeA_model
      S hp hT hap h1 i hA hqs
  rcases hmodel with hM | hM
  · exact ⟨.PSL, ν, f, by decide, Or.inl ⟨by decide, hM⟩⟩
  · exact ⟨.PSU, ν, f, by decide, Or.inl ⟨by decide, hM⟩⟩

theorem kgNotC_innerRecog_D
    {τ : CFSG.Blueprint.Chevalley.Tag}
    (hτ : τ = CFSG.Blueprint.Chevalley.Tag.D4 ∨
      τ = CFSG.Blueprint.Chevalley.Tag.E6 ∨ τ = CFSG.Blueprint.Chevalley.Tag.E7 ∨ τ =
        CFSG.Blueprint.Chevalley.Tag.E8)
    {n : ℕ}
    (hn : 4 ≤ n)
    {K : Type}
    [Field K]
    [Finite K]
    {p : ℕ}
    {f : ℕ}
    (hp : Nat.Prime p)
    (hf : 0 < f)
    (hK : Nat.card K = p ^ f)
    {ι : Type}
    [Fintype ι]
    (β : ι → Fin τ.rank → ℤ)
    (hroot : ∀ (b : ι), CFSG.Blueprint.Chevalley.IsRoot τ (β b))
    (l : Fin n → ι)
    (hgram : ∀ (i j : Fin n),
      i ≠ j →
        ¬CFSG.Timmesfeld.edgeD n i j →
          ¬CFSG.Timmesfeld.edgeD n j i → CFSG.LieType.Steinberg.Adjoint.iform (β (l i)) (β (l j)) =
            0)
    (hframe : ∀ (i j : Fin n),
      CFSG.Timmesfeld.edgeD n i j →
        ∃ (θ : Matrix.SpecialLinearGroup (Fin 3) K →* CFSG.Blueprint.Chevalley.ModGL τ K),
          θ.comp (CFSG.ClassicalInvolution.WeakCT.blockSL K 3 2 0 (by omega)) =
            CFSG.LieType.Chevalley.rootSL2 τ K (β (l i)) ∧
            θ.comp (CFSG.ClassicalInvolution.WeakCT.blockSL K 3 2 1 (by omega)) =
              CFSG.LieType.Chevalley.rootSL2 τ K (β (l j))) :
    Eq (α :=
        Subgroup
          ↥(CFSG.Blueprint.Chevalley.rootSpan τ K
              (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.rootsOfFam β (Set.range l))))
        (commutator
          ↥(CFSG.Blueprint.Chevalley.rootSpan τ K
              (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.rootsOfFam β (Set.range l))))
        ⊤ ∧
      CFSG.StandardType.KG.KGNotCLieType p
        ↥(CFSG.Blueprint.Chevalley.rootSpan τ K
            (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.rootsOfFam β (Set.range l))) := by
  classical
  obtain ⟨U, ρ, hgen, hcomm, hρ, hψ⟩ := weakCT_data hτ β hroot l (edgeD n) hgram hframe
  have hadm : StatedLieAdmissible .POmegaPlus n p f := ⟨hp, hf, hn⟩
  obtain ⟨-, -, -, hqs, -, hmodel⟩ := weakCT_spinPlus_of_frame hadm (by omega) hK U
    hgen hcomm hρ hψ
  exact ⟨hqs.1.commutator_eq_top, ⟨.POmegaPlus, n, f, by decide, hmodel⟩⟩

theorem kgNotC_innerRecog_E6
    {τ : CFSG.Blueprint.Chevalley.Tag}
    (hτ : τ = CFSG.Blueprint.Chevalley.Tag.D4 ∨
      τ = CFSG.Blueprint.Chevalley.Tag.E6 ∨ τ = CFSG.Blueprint.Chevalley.Tag.E7 ∨ τ =
        CFSG.Blueprint.Chevalley.Tag.E8)
    {K : Type}
    [Field K]
    [Finite K]
    {p : ℕ}
    {f : ℕ}
    (hp : Nat.Prime p)
    (hf : 0 < f)
    (hK : Nat.card K = p ^ f)
    {ι : Type}
    [Fintype ι]
    (β : ι → Fin τ.rank → ℤ)
    (hroot : ∀ (b : ι), CFSG.Blueprint.Chevalley.IsRoot τ (β b))
    (l : Fin 6 → ι)
    (hgram : ∀ (i j : Fin 6),
      i ≠ j →
        ¬CFSG.Timmesfeld.edgeE 6 i j →
          ¬CFSG.Timmesfeld.edgeE 6 j i → CFSG.LieType.Steinberg.Adjoint.iform (β (l i)) (β (l j)) =
            0)
    (hframe : ∀ (i j : Fin 6),
      CFSG.Timmesfeld.edgeE 6 i j →
        ∃ (θ : Matrix.SpecialLinearGroup (Fin 3) K →* CFSG.Blueprint.Chevalley.ModGL τ K),
          θ.comp (CFSG.ClassicalInvolution.WeakCT.blockSL K 3 2 0 (by omega)) =
            CFSG.LieType.Chevalley.rootSL2 τ K (β (l i)) ∧
            θ.comp (CFSG.ClassicalInvolution.WeakCT.blockSL K 3 2 1 (by omega)) =
              CFSG.LieType.Chevalley.rootSL2 τ K (β (l j))) :
    Eq (α :=
        Subgroup
          ↥(CFSG.Blueprint.Chevalley.rootSpan τ K
              (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.rootsOfFam β (Set.range l))))
        (commutator
          ↥(CFSG.Blueprint.Chevalley.rootSpan τ K
              (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.rootsOfFam β (Set.range l))))
        ⊤ ∧
      CFSG.StandardType.KG.KGNotCLieType p
        ↥(CFSG.Blueprint.Chevalley.rootSpan τ K
            (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.rootsOfFam β (Set.range l))) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨U, ρ, hgen, hcomm, hρ, hψ⟩ := weakCT_data hτ β hroot l (edgeE 6) hgram hframe
  have hadm : StatedLieAdmissible .E6 0 p f := ⟨hp, hf, rfl⟩
  obtain ⟨-, -, -, hqs, -, hmodel⟩ := weakCT_e6_of_frame p f hadm hK U hgen hcomm hρ hψ
  exact ⟨hqs.1.commutator_eq_top, ⟨.E6, 0, f, by decide, hmodel⟩⟩

theorem kgNotC_innerRecog_E7
    {τ : CFSG.Blueprint.Chevalley.Tag}
    (hτ : τ = CFSG.Blueprint.Chevalley.Tag.D4 ∨
      τ = CFSG.Blueprint.Chevalley.Tag.E6 ∨ τ = CFSG.Blueprint.Chevalley.Tag.E7 ∨ τ =
        CFSG.Blueprint.Chevalley.Tag.E8)
    {K : Type}
    [Field K]
    [Finite K]
    {p : ℕ}
    {f : ℕ}
    (hp : Nat.Prime p)
    (hf : 0 < f)
    (hK : Nat.card K = p ^ f)
    {ι : Type}
    [Fintype ι]
    (β : ι → Fin τ.rank → ℤ)
    (hroot : ∀ (b : ι), CFSG.Blueprint.Chevalley.IsRoot τ (β b))
    (l : Fin 7 → ι)
    (hgram : ∀ (i j : Fin 7),
      i ≠ j →
        ¬CFSG.Timmesfeld.edgeE 7 i j →
          ¬CFSG.Timmesfeld.edgeE 7 j i → CFSG.LieType.Steinberg.Adjoint.iform (β (l i)) (β (l j)) =
            0)
    (hframe : ∀ (i j : Fin 7),
      CFSG.Timmesfeld.edgeE 7 i j →
        ∃ (θ : Matrix.SpecialLinearGroup (Fin 3) K →* CFSG.Blueprint.Chevalley.ModGL τ K),
          θ.comp (CFSG.ClassicalInvolution.WeakCT.blockSL K 3 2 0 (by omega)) =
            CFSG.LieType.Chevalley.rootSL2 τ K (β (l i)) ∧
            θ.comp (CFSG.ClassicalInvolution.WeakCT.blockSL K 3 2 1 (by omega)) =
              CFSG.LieType.Chevalley.rootSL2 τ K (β (l j))) :
    Eq (α :=
        Subgroup
          ↥(CFSG.Blueprint.Chevalley.rootSpan τ K
              (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.rootsOfFam β (Set.range l))))
        (commutator
          ↥(CFSG.Blueprint.Chevalley.rootSpan τ K
              (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.rootsOfFam β (Set.range l))))
        ⊤ ∧
      CFSG.StandardType.KG.KGNotCLieType p
        ↥(CFSG.Blueprint.Chevalley.rootSpan τ K
            (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.rootsOfFam β (Set.range l))) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨U, ρ, hgen, hcomm, hρ, hψ⟩ := weakCT_data hτ β hroot l (edgeE 7) hgram hframe
  have hadm : StatedLieAdmissible .E7 0 p f := ⟨hp, hf, rfl⟩
  obtain ⟨-, -, -, hqs, -, hmodel⟩ := weakCT_e7_of_frame p f hadm hK U hgen hcomm hρ hψ
  exact ⟨hqs.1.commutator_eq_top, ⟨.E7, 0, f, by decide, hmodel⟩⟩

theorem kgNotC_innerRecog_E8
    {τ : CFSG.Blueprint.Chevalley.Tag}
    (hτ : τ = CFSG.Blueprint.Chevalley.Tag.D4 ∨
      τ = CFSG.Blueprint.Chevalley.Tag.E6 ∨ τ = CFSG.Blueprint.Chevalley.Tag.E7 ∨ τ =
        CFSG.Blueprint.Chevalley.Tag.E8)
    {K : Type}
    [Field K]
    [Finite K]
    {p : ℕ}
    {f : ℕ}
    (hp : Nat.Prime p)
    (hf : 0 < f)
    (hK : Nat.card K = p ^ f)
    {ι : Type}
    [Fintype ι]
    (β : ι → Fin τ.rank → ℤ)
    (hroot : ∀ (b : ι), CFSG.Blueprint.Chevalley.IsRoot τ (β b))
    (l : Fin 8 → ι)
    (hgram : ∀ (i j : Fin 8),
      i ≠ j →
        ¬CFSG.Timmesfeld.edgeE 8 i j →
          ¬CFSG.Timmesfeld.edgeE 8 j i → CFSG.LieType.Steinberg.Adjoint.iform (β (l i)) (β (l j)) =
            0)
    (hframe : ∀ (i j : Fin 8),
      CFSG.Timmesfeld.edgeE 8 i j →
        ∃ (θ : Matrix.SpecialLinearGroup (Fin 3) K →* CFSG.Blueprint.Chevalley.ModGL τ K),
          θ.comp (CFSG.ClassicalInvolution.WeakCT.blockSL K 3 2 0 (by omega)) =
            CFSG.LieType.Chevalley.rootSL2 τ K (β (l i)) ∧
            θ.comp (CFSG.ClassicalInvolution.WeakCT.blockSL K 3 2 1 (by omega)) =
              CFSG.LieType.Chevalley.rootSL2 τ K (β (l j))) :
    Eq (α :=
        Subgroup
          ↥(CFSG.Blueprint.Chevalley.rootSpan τ K
              (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.rootsOfFam β (Set.range l))))
        (commutator
          ↥(CFSG.Blueprint.Chevalley.rootSpan τ K
              (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.rootsOfFam β (Set.range l))))
        ⊤ ∧
      CFSG.StandardType.KG.KGNotCLieType p
        ↥(CFSG.Blueprint.Chevalley.rootSpan τ K
            (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.rootsOfFam β (Set.range l))) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨U, ρ, hgen, hcomm, hρ, hψ⟩ := weakCT_data hτ β hroot l (edgeE 8) hgram hframe
  have hadm : StatedLieAdmissible .E8 0 p f := ⟨hp, hf, rfl⟩
  obtain ⟨-, -, -, hqs, -, hmodel⟩ := weakCT_e8_of_frame p f hadm hK U hgen hcomm hρ hψ
  exact ⟨hqs.1.commutator_eq_top, ⟨.E8, 0, f, by decide, hmodel⟩⟩

theorem kgNotC_of_innerCover
    {τ : CFSG.Blueprint.Chevalley.Tag}
    {L : Type}
    [Field L]
    [IsAlgClosed L]
    {p₀ : ℕ}
    (S : CFSG.HardMathSupport.Timmesfeld.LangTorus.LangSetup τ L p₀)
    {ta : Fin τ.rank → Lˣ}
    (hT : CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit τ ta ∈ S.D.torus)
    (i : CFSG.LieType.Chevalley.KernelComponent (τ := τ) (M := Lˣ)
      (CFSG.LieType.AlgebraicGroups.rootCharHom ta))
    (hinner : CFSG.HardMathSupport.Timmesfeld.LangTorus.twistInner
      (CFSG.LieType.Chevalley.componentRoots (CFSG.LieType.AlgebraicGroups.rootCharHom ta) i)
      (⇑S.ρ :
          (Fin τ.rank → ℤ) →
            Fin τ.rank →
              ℤ)^[CFSG.HardMathSupport.Timmesfeld.LangTorus.componentOrbitLength S.ρ
          (CFSG.LieType.Chevalley.componentRoots (CFSG.LieType.AlgebraicGroups.rootCharHom ta) i)])
    (hrec : ∀ (K : Subfield L),
      Finite ↥K →
        Nat.card ↥K =
            S.D.q ^
              CFSG.HardMathSupport.Timmesfeld.LangTorus.componentOrbitLength S.ρ
                (CFSG.LieType.Chevalley.componentRoots (CFSG.LieType.AlgebraicGroups.rootCharHom ta)
                  i) →
          Eq (α :=
              Subgroup ↥(CFSG.LieType.Chevalley.componentRootSpan (↥K)
                (CFSG.LieType.AlgebraicGroups.rootCharHom ta) i))
              (commutator ↥(CFSG.LieType.Chevalley.componentRootSpan (↥K)
                (CFSG.LieType.AlgebraicGroups.rootCharHom ta) i))
              ⊤ ∧
            CFSG.StandardType.KG.KGNotCLieType (ringChar L)
              ↥(CFSG.LieType.Chevalley.componentRootSpan (↥K)
                (CFSG.LieType.AlgebraicGroups.rootCharHom ta) i)) :
    CFSG.StandardType.KG.KGNotCLieType (ringChar L)
      ↥(CFSG.HardMathSupport.Timmesfeld.LangTorus.rationalComponent S.ρ S.Γ
        (CFSG.LieType.AlgebraicGroups.rootCharHom ta) i) := by
  classical
  obtain ⟨σ, hfin, hcard, f, hf1, hker, hf2⟩ := exists_inner_cover S hT i hinner
  obtain ⟨hperf, hT'⟩ := hrec (fixSubfield σ) hfin hcard
  have hCperf : ⁅componentRootSpan (fixSubfield σ) (rootCharHom ta) i,
      componentRootSpan (fixSubfield σ) (rootCharHom ta) i⁆ =
      componentRootSpan (fixSubfield σ) (rootCharHom ta) i :=
    Subgroup.isPerfect_iff.1 (Group.isPerfect_def.2 hperf)
  have hRf : f.range = rationalComponent S.ρ S.Γ (rootCharHom ta) i :=
    le_antisymm (hf2 hCperf) hf1
  have hmem : ∀ x, f x ∈ rationalComponent S.ρ S.Γ (rootCharHom ta) i := fun x =>
    hRf ▸ ⟨x, rfl⟩
  let g := f.codRestrict _ hmem
  have hg : Function.Surjective g := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx⟩ : y ∈ f.range := hRf ▸ hy
    exact ⟨x, Subtype.ext hx⟩
  have hgk : g.ker ≤
      Subgroup.center ↥(componentRootSpan (fixSubfield σ) (rootCharHom ta) i) := by
    intro x hx
    apply hker
    rw [MonoidHom.mem_ker] at hx ⊢
    exact congrArg Subtype.val hx
  exact hT'.of_surjective hperf g hg hgk

theorem kgNotC_of_tree
    {τ : CFSG.Blueprint.Chevalley.Tag}
    (K : CFSG.HardMathSupport.Timmesfeld.CrossChar.KacData τ)
    {L : Type}
    [Field L]
    [IsAlgClosed L]
    {p₀ : ℕ}
    (S : CFSG.HardMathSupport.Timmesfeld.LangTorus.LangSetup τ L p₀)
    {a : Fin τ.rank → Lˣ}
    (hTor : CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit τ a ∈ S.D.torus)
    (i : CFSG.LieType.Chevalley.KernelComponent (τ := τ) (M := Lˣ)
      (CFSG.LieType.AlgebraicGroups.rootCharHom a))
    (hinner : CFSG.HardMathSupport.Timmesfeld.LangTorus.twistInner
      (CFSG.LieType.Chevalley.componentRoots (CFSG.LieType.AlgebraicGroups.rootCharHom a) i)
      (⇑S.ρ :
          (Fin τ.rank → ℤ) →
            Fin τ.rank →
              ℤ)^[CFSG.HardMathSupport.Timmesfeld.LangTorus.componentOrbitLength S.ρ
          (CFSG.LieType.Chevalley.componentRoots (CFSG.LieType.AlgebraicGroups.rootCharHom a) i)])
    (v : CFSG.LieType.Chevalley.WeylGroup τ)
    {n : ℕ}
    (l : Fin n → Option (Fin τ.rank))
    (hroots : CFSG.LieType.Chevalley.componentRoots (CFSG.LieType.AlgebraicGroups.rootCharHom a) i =
      (fun (α : Fin τ.rank → ℤ) => v • α) '' K.rootsOf (Set.range l))
    (hrec : ∀ (K' : Type) [inst : Field K'] [Finite K'] (p f : ℕ),
      Nat.Prime p →
        0 < f →
          Nat.card K' = p ^ f →
            Eq (α :=
                Subgroup
                  ↥(CFSG.Blueprint.Chevalley.rootSpan τ K'
                      (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.rootsOfFam
                        (fun (x : Option (Fin τ.rank)) => v • K.extRoot x) (Set.range l))))
                (commutator
                  ↥(CFSG.Blueprint.Chevalley.rootSpan τ K'
                      (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.rootsOfFam
                        (fun (x : Option (Fin τ.rank)) => v • K.extRoot x) (Set.range l))))
                ⊤ ∧
              CFSG.StandardType.KG.KGNotCLieType p
                ↥(CFSG.Blueprint.Chevalley.rootSpan τ K'
                    (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.rootsOfFam
                      (fun (x : Option (Fin τ.rank)) => v • K.extRoot x) (Set.range l)))) :
    CFSG.StandardType.KG.KGNotCLieType (ringChar L)
      ↥(CFSG.HardMathSupport.Timmesfeld.LangTorus.rationalComponent S.ρ S.Γ
        (CFSG.LieType.AlgebraicGroups.rootCharHom a) i) := by
  classical
  refine kgNotC_of_innerCover S hTor i hinner (fun K' hK' _ => ?_)
  set β : Option (Fin τ.rank) → Fin τ.rank → ℤ := fun x => v • K.extRoot x with hβ
  have hsmulcombo : ∀ n' : Option (Fin τ.rank) → ℕ,
      v • K.combo n' = ∑ x, (n' x : ℤ) • β x := by
    intro n'
    unfold KacData.combo
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun x _ => smul_comm v ((n' x : ℕ) : ℤ) (K.extRoot x)
  have hset : (fun α => v • α) '' K.rootsOf (Set.range l) =
      rootsOfFam β (Set.range l) := by
    ext γ
    constructor
    · rintro ⟨γ₀, ⟨hr0, n', hn', hγ⟩, rfl⟩
      refine ⟨IsRoot.smul hr0 v, n', hn', ?_⟩
      rcases hγ with rfl | rfl
      · exact Or.inl (hsmulcombo n')
      · exact Or.inr (by show v • (-K.combo n') = _; rw [smul_neg, hsmulcombo])
    · rintro ⟨hr, n', hn', hγ⟩
      refine ⟨v⁻¹ • γ, ⟨IsRoot.smul hr v⁻¹, n', hn', ?_⟩, smul_inv_smul v γ⟩
      rcases hγ with rfl | rfl
      · left
        rw [← hsmulcombo, inv_smul_smul]
      · right
        rw [smul_neg, ← hsmulcombo, inv_smul_smul]
  have hcomp : componentRootSpan K' (rootCharHom a) i =
      rootSpan τ K' (rootsOfFam β (Set.range l)) := by
    show rootSpan τ K' (componentRoots (rootCharHom a) i) = _
    rw [hroots, hset]
  rw [hcomp]
  haveI : Fintype ↥K' := Fintype.ofFinite ↥K'
  haveI : CharP ↥K' (ringChar ↥K') := ringChar.charP ↥K'
  obtain ⟨f, hprime, hcardK⟩ := FiniteField.card ↥K' (ringChar ↥K')
  have hring : ringChar ↥K' = ringChar L := ringChar_subfield' K'
  rw [hring] at hprime hcardK
  have hK'card : Nat.card ↥K' = ringChar L ^ (f : ℕ) := by
    rw [Nat.card_eq_fintype_card, hcardK]
  exact hrec ↥K' (ringChar L) f hprime f.pos hK'card

theorem kgNotC_of_dClass
    {τ : CFSG.Blueprint.Chevalley.Tag}
    (hτ : τ = CFSG.Blueprint.Chevalley.Tag.D4 ∨
      τ = CFSG.Blueprint.Chevalley.Tag.E6 ∨ τ = CFSG.Blueprint.Chevalley.Tag.E7 ∨ τ =
        CFSG.Blueprint.Chevalley.Tag.E8)
    (K : CFSG.HardMathSupport.Timmesfeld.CrossChar.KacData τ)
    (hK : K.Facts)
    {E : List (ℕ × ℕ)}
    {tp : ℕ → ℕ → List ℕ}
    (hT : CFSG.HardMathSupport.Timmesfeld.CrossChar.IsTreePaths (τ.rank + 1) E tp)
    (hadj : ∀ (x y : Option (Fin τ.rank)),
      K.Adj x y ↔
        (CFSG.HardMathSupport.Timmesfeld.CrossChar.nodeIdx x,
          CFSG.HardMathSupport.Timmesfeld.CrossChar.nodeIdx y) ∈ E)
    {cands : List (List ℕ)}
    (hcheck : ((List.range (τ.rank + 1)).sublists.all fun (zl : List ℕ) =>
        !(fun (x : List ℕ) => Bool.true) zl ||
          zl.all fun (x : ℕ) =>
            cands.any
              (CFSG.HardMathSupport.Timmesfeld.CrossChar.sameSet
                (CFSG.HardMathSupport.Timmesfeld.CrossChar.compIdx (τ.rank + 1) tp zl x))) =
      Bool.true)
    (hlt : ∀ c ∈ cands, ∀ w ∈ c, w < τ.rank + 1)
    (hcard : ∀ c ∈ cands,
      Finset.card (α := Option (Fin τ.rank))
          (List.toFinset (List.map CFSG.HardMathSupport.Timmesfeld.CrossChar.idxNode c)) =
        c.length)
    {trees : List (List (Option (Fin τ.rank)))}
    (hcount : ∀ c ∈ cands,
      4 ≤ c.length →
        CFSG.HardMathSupport.Timmesfeld.LangTorus.kacCount τ K.θ
              (List.toFinset (List.map CFSG.HardMathSupport.Timmesfeld.CrossChar.idxNode c)) =
            2 * c.length * (c.length - 1) →
          ∃ P ∈ trees,
            CFSG.HardMathSupport.Timmesfeld.CrossChar.sameSet c
                (List.map CFSG.HardMathSupport.Timmesfeld.CrossChar.nodeIdx P) =
              Bool.true)
    (htrees : ∀ P ∈ trees,
      P.Nodup ∧
        4 ≤ P.length ∧
          (∀ (c d : Fin P.length),
              c ≠ d →
                ¬CFSG.Timmesfeld.edgeD P.length c d →
                  ¬CFSG.Timmesfeld.edgeD P.length d c →
                    CFSG.LieType.Steinberg.Adjoint.iform (K.extRoot (P.get c)) (K.extRoot (P.get d))
                      = 0) ∧
            ∀ (c d : Fin P.length),
              CFSG.Timmesfeld.edgeD P.length c d →
                (CFSG.HardMathSupport.Timmesfeld.CrossChar.nodeIdx (P.get c),
                    CFSG.HardMathSupport.Timmesfeld.CrossChar.nodeIdx (P.get d)) ∈
                  E)
    (hframes : ∀ {F : Type} [inst : Field F] (x y : Option (Fin τ.rank)),
      (CFSG.HardMathSupport.Timmesfeld.CrossChar.nodeIdx x,
        CFSG.HardMathSupport.Timmesfeld.CrossChar.nodeIdx y) ∈ E →
        ∃ (ρ : Matrix.SpecialLinearGroup (Fin 3) F →* CFSG.Blueprint.Chevalley.ModGL τ F) (σ :
          Fin 3 → Fin 3 → Fin τ.rank → ℤ),
          CFSG.RankThree.PartOne.KF4.IsA2Frame ρ σ ∧ σ 0 1 = K.extRoot x ∧ σ 1 2 = K.extRoot y)
    {L : Type}
    [Field L]
    [IsAlgClosed L]
    {p₀ : ℕ}
    {p : ℕ}
    (S : CFSG.HardMathSupport.Timmesfeld.LangTorus.LangSetup τ L p₀)
    (hp : Nat.Prime p)
    (hpL : (↑p : L) ≠ 0)
    {a : Fin τ.rank → Lˣ}
    (hTor : CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit τ a ∈ S.D.torus)
    (hTp : CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit τ a ^ p = 1)
    (i : CFSG.LieType.Chevalley.KernelComponent (τ := τ) (M := Lˣ)
      (CFSG.LieType.AlgebraicGroups.rootCharHom a))
    (h4 : 4 ≤
      CFSG.HardMathSupport.Timmesfeld.LangTorus.compRank
        (CFSG.LieType.Chevalley.componentRoots (CFSG.LieType.AlgebraicGroups.rootCharHom a) i))
    (hn : (CFSG.LieType.Chevalley.componentRoots (CFSG.LieType.AlgebraicGroups.rootCharHom a)
      i).ncard =
      2 *
          CFSG.HardMathSupport.Timmesfeld.LangTorus.compRank
            (CFSG.LieType.Chevalley.componentRoots (CFSG.LieType.AlgebraicGroups.rootCharHom a) i) *
        (CFSG.HardMathSupport.Timmesfeld.LangTorus.compRank
            (CFSG.LieType.Chevalley.componentRoots (CFSG.LieType.AlgebraicGroups.rootCharHom a) i) -
          1))
    (hinner : CFSG.HardMathSupport.Timmesfeld.LangTorus.twistInner
      (CFSG.LieType.Chevalley.componentRoots (CFSG.LieType.AlgebraicGroups.rootCharHom a) i)
      (⇑S.ρ :
          (Fin τ.rank → ℤ) →
            Fin τ.rank →
              ℤ)^[CFSG.HardMathSupport.Timmesfeld.LangTorus.componentOrbitLength S.ρ
          (CFSG.LieType.Chevalley.componentRoots (CFSG.LieType.AlgebraicGroups.rootCharHom a) i)]) :
    CFSG.StandardType.KG.KGNotCLieType (ringChar L)
      ↥(CFSG.HardMathSupport.Timmesfeld.LangTorus.rationalComponent S.ρ S.Γ
        (CFSG.LieType.AlgebraicGroups.rootCharHom a) i) := by
  classical
  obtain ⟨v, n, l, hn4, -, hroots, hnon, hE⟩ :=
    exists_tree_of_class K hK hT hadj hcheck hlt hcard edgeD 4 (fun n => 2 * n * (n - 1))
      hcount htrees (fun _ => True) (fun _ _ => trivial) S hp hpL hTp i h4 hn
  refine kgNotC_of_tree K S hTor i hinner v l hroots ?_
  intro K' _ _ p' f hp' hf hK'
  exact kgNotC_innerRecog_D hτ hn4 hp' hf hK' (fun x => v • K.extRoot x)
    (fun b => IsRoot.smul (K.isRoot_extRoot b) v) l
    (fun c d hcd h1 h2 => by
      show iform (v • K.extRoot (l c)) (v • K.extRoot (l d)) = 0
      rw [iform_smul]
      exact hnon c d hcd h1 h2)
    (treeFrames K hframes v l (edgeD n) hE)

theorem kgNotC_of_eClass
    {τ : CFSG.Blueprint.Chevalley.Tag}
    (hτ : τ = CFSG.Blueprint.Chevalley.Tag.D4 ∨
      τ = CFSG.Blueprint.Chevalley.Tag.E6 ∨ τ = CFSG.Blueprint.Chevalley.Tag.E7 ∨ τ =
        CFSG.Blueprint.Chevalley.Tag.E8)
    (K : CFSG.HardMathSupport.Timmesfeld.CrossChar.KacData τ)
    (hK : K.Facts)
    {E : List (ℕ × ℕ)}
    {tp : ℕ → ℕ → List ℕ}
    (hT : CFSG.HardMathSupport.Timmesfeld.CrossChar.IsTreePaths (τ.rank + 1) E tp)
    (hadj : ∀ (x y : Option (Fin τ.rank)),
      K.Adj x y ↔
        (CFSG.HardMathSupport.Timmesfeld.CrossChar.nodeIdx x,
          CFSG.HardMathSupport.Timmesfeld.CrossChar.nodeIdx y) ∈ E)
    {cands : List (List ℕ)}
    (hcheck : ((List.range (τ.rank + 1)).sublists.all fun (zl : List ℕ) =>
        !(fun (x : List ℕ) => Bool.true) zl ||
          zl.all fun (x : ℕ) =>
            cands.any
              (CFSG.HardMathSupport.Timmesfeld.CrossChar.sameSet
                (CFSG.HardMathSupport.Timmesfeld.CrossChar.compIdx (τ.rank + 1) tp zl x))) =
      Bool.true)
    (hlt : ∀ c ∈ cands, ∀ w ∈ c, w < τ.rank + 1)
    (hcard : ∀ c ∈ cands,
      Finset.card (α := Option (Fin τ.rank))
          (List.toFinset (List.map CFSG.HardMathSupport.Timmesfeld.CrossChar.idxNode c)) =
        c.length)
    {trees : List (List (Option (Fin τ.rank)))}
    (hcount : ∀ c ∈ cands,
      6 ≤ c.length →
        CFSG.HardMathSupport.Timmesfeld.LangTorus.kacCount τ K.θ
              (List.toFinset (List.map CFSG.HardMathSupport.Timmesfeld.CrossChar.idxNode c)) =
            CFSG.HardMathSupport.Solomon.Coordinator.LieComp.eRootCount c.length →
          ∃ P ∈ trees,
            CFSG.HardMathSupport.Timmesfeld.CrossChar.sameSet c
                (List.map CFSG.HardMathSupport.Timmesfeld.CrossChar.nodeIdx P) =
              Bool.true)
    (htrees : ∀ P ∈ trees,
      P.Nodup ∧
        6 ≤ P.length ∧
          (∀ (c d : Fin P.length),
              c ≠ d →
                ¬CFSG.Timmesfeld.edgeE P.length c d →
                  ¬CFSG.Timmesfeld.edgeE P.length d c →
                    CFSG.LieType.Steinberg.Adjoint.iform (K.extRoot (P.get c)) (K.extRoot (P.get d))
                      = 0) ∧
            ∀ (c d : Fin P.length),
              CFSG.Timmesfeld.edgeE P.length c d →
                (CFSG.HardMathSupport.Timmesfeld.CrossChar.nodeIdx (P.get c),
                    CFSG.HardMathSupport.Timmesfeld.CrossChar.nodeIdx (P.get d)) ∈
                  E)
    (hlen : ∀ P ∈ trees, P.length = 6 ∨ P.length = 7 ∨ P.length = 8)
    (hframes : ∀ {F : Type} [inst : Field F] (x y : Option (Fin τ.rank)),
      (CFSG.HardMathSupport.Timmesfeld.CrossChar.nodeIdx x,
        CFSG.HardMathSupport.Timmesfeld.CrossChar.nodeIdx y) ∈ E →
        ∃ (ρ : Matrix.SpecialLinearGroup (Fin 3) F →* CFSG.Blueprint.Chevalley.ModGL τ F) (σ :
          Fin 3 → Fin 3 → Fin τ.rank → ℤ),
          CFSG.RankThree.PartOne.KF4.IsA2Frame ρ σ ∧ σ 0 1 = K.extRoot x ∧ σ 1 2 = K.extRoot y)
    {L : Type}
    [Field L]
    [IsAlgClosed L]
    {p₀ : ℕ}
    {p : ℕ}
    (S : CFSG.HardMathSupport.Timmesfeld.LangTorus.LangSetup τ L p₀)
    (hp : Nat.Prime p)
    (hpL : (↑p : L) ≠ 0)
    {a : Fin τ.rank → Lˣ}
    (hTor : CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit τ a ∈ S.D.torus)
    (hTp : CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit τ a ^ p = 1)
    (i : CFSG.LieType.Chevalley.KernelComponent (τ := τ) (M := Lˣ)
      (CFSG.LieType.AlgebraicGroups.rootCharHom a))
    (h6 : 6 ≤
      CFSG.HardMathSupport.Timmesfeld.LangTorus.compRank
        (CFSG.LieType.Chevalley.componentRoots (CFSG.LieType.AlgebraicGroups.rootCharHom a) i))
    (hn : (CFSG.LieType.Chevalley.componentRoots (CFSG.LieType.AlgebraicGroups.rootCharHom a)
      i).ncard =
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.eRootCount
        (CFSG.HardMathSupport.Timmesfeld.LangTorus.compRank
          (CFSG.LieType.Chevalley.componentRoots (CFSG.LieType.AlgebraicGroups.rootCharHom a) i)))
    (hinner : CFSG.HardMathSupport.Timmesfeld.LangTorus.twistInner
      (CFSG.LieType.Chevalley.componentRoots (CFSG.LieType.AlgebraicGroups.rootCharHom a) i)
      (⇑S.ρ :
          (Fin τ.rank → ℤ) →
            Fin τ.rank →
              ℤ)^[CFSG.HardMathSupport.Timmesfeld.LangTorus.componentOrbitLength S.ρ
          (CFSG.LieType.Chevalley.componentRoots (CFSG.LieType.AlgebraicGroups.rootCharHom a) i)]) :
    CFSG.StandardType.KG.KGNotCLieType (ringChar L)
      ↥(CFSG.HardMathSupport.Timmesfeld.LangTorus.rationalComponent S.ρ S.Γ
        (CFSG.LieType.AlgebraicGroups.rootCharHom a) i) := by
  classical
  obtain ⟨v, n, l, hn6, hQ, hroots, hnon, hE⟩ :=
    exists_tree_of_class K hK hT hadj hcheck hlt hcard edgeE 6 eRootCount hcount htrees
      (fun n => n = 6 ∨ n = 7 ∨ n = 8) hlen S hp hpL hTp i h6 hn
  refine kgNotC_of_tree K S hTor i hinner v l hroots ?_
  intro K' _ _ p' f hp' hf hK'
  have hgr : ∀ c d : Fin n, c ≠ d → ¬ edgeE n c d → ¬ edgeE n d c →
      iform ((fun x => v • K.extRoot x) (l c)) ((fun x => v • K.extRoot x) (l d)) = 0 := by
    intro c d hcd h1 h2
    show iform (v • K.extRoot (l c)) (v • K.extRoot (l d)) = 0
    rw [iform_smul]
    exact hnon c d hcd h1 h2
  have hfr := treeFrames K hframes v l (edgeE n) hE (F := K')
  have hroot : ∀ b, IsRoot τ ((fun x => v • K.extRoot x) b) :=
    fun b => IsRoot.smul (K.isRoot_extRoot b) v
  rcases hQ with rfl | rfl | rfl
  · exact kgNotC_innerRecog_E6 hτ hp' hf hK' (fun x => v • K.extRoot x) hroot l hgr hfr
  · exact kgNotC_innerRecog_E7 hτ hp' hf hK' (fun x => v • K.extRoot x) hroot l hgr hfr
  · exact kgNotC_innerRecog_E8 hτ hp' hf hK' (fun x => v • K.extRoot x) hroot l hgr hfr

theorem kgNotC_inner_nonA_E6
    {L : Type}
    [Field L]
    [IsAlgClosed L]
    {p₀ : ℕ}
    {p : ℕ}
    (S : CFSG.HardMathSupport.Timmesfeld.LangTorus.LangSetup CFSG.Blueprint.Chevalley.Tag.E6 L p₀)
    (hp : Nat.Prime p)
    (hpL : (↑p : L) ≠ 0)
    {a : Fin CFSG.Blueprint.Chevalley.Tag.E6.rank → Lˣ}
    (hTor : CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit
      CFSG.Blueprint.Chevalley.Tag.E6 a ∈ S.D.torus)
    (hTp : CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit
      CFSG.Blueprint.Chevalley.Tag.E6 a ^ p = 1)
    (i : CFSG.LieType.Chevalley.KernelComponent (τ := CFSG.Blueprint.Chevalley.Tag.E6) (M := Lˣ)
      (CFSG.LieType.AlgebraicGroups.rootCharHom a))
    (hnonA : ¬(1 ≤
          CFSG.HardMathSupport.Timmesfeld.LangTorus.compRank
            (CFSG.LieType.Chevalley.componentRoots (CFSG.LieType.AlgebraicGroups.rootCharHom a) i) ∧
        (CFSG.LieType.Chevalley.componentRoots (CFSG.LieType.AlgebraicGroups.rootCharHom a) i).ncard
          =
          CFSG.HardMathSupport.Timmesfeld.LangTorus.compRank
              (CFSG.LieType.Chevalley.componentRoots (CFSG.LieType.AlgebraicGroups.rootCharHom a) i)
                *
            (CFSG.HardMathSupport.Timmesfeld.LangTorus.compRank
                (CFSG.LieType.Chevalley.componentRoots (CFSG.LieType.AlgebraicGroups.rootCharHom a)
                  i) +
              1)))
    (hinner : CFSG.HardMathSupport.Timmesfeld.LangTorus.twistInner
      (CFSG.LieType.Chevalley.componentRoots (CFSG.LieType.AlgebraicGroups.rootCharHom a) i)
      (⇑S.ρ :
          (Fin CFSG.Blueprint.Chevalley.Tag.E6.rank → ℤ) →
            Fin CFSG.Blueprint.Chevalley.Tag.E6.rank →
              ℤ)^[CFSG.HardMathSupport.Timmesfeld.LangTorus.componentOrbitLength S.ρ
          (CFSG.LieType.Chevalley.componentRoots (CFSG.LieType.AlgebraicGroups.rootCharHom a) i)]) :
    CFSG.StandardType.KG.KGNotCLieType (ringChar L)
      ↥(CFSG.HardMathSupport.Timmesfeld.LangTorus.rationalComponent S.ρ S.Γ
        (CFSG.LieType.AlgebraicGroups.rootCharHom a) i) := by
  obtain ⟨v, μ, x, c, -, hc, -, hlen, -, hrank, hncard⟩ :=
    exists_cand_of_class kacE6 facts_E6 e6_tree e6_adj e6_check e6_lt e6_card S hp hpL hTp i
  have hshape := e6_shape c hc hlen
  rw [← hncard, ← hrank] at hshape
  rcases hshape with hA | hD | hE
  · exact (hnonA hA).elim
  · exact kgNotC_of_dClass (Or.inr (Or.inl rfl)) kacE6 facts_E6 e6_tree e6_adj e6_check e6_lt
      e6_card e6_dcount e6_dtrees (fun {F} _ x y h => e6_frames x y h) S hp hpL hTor hTp i hD.1
      hD.2 hinner
  · exact kgNotC_of_eClass (Or.inr (Or.inl rfl)) kacE6 facts_E6 e6_tree e6_adj e6_check e6_lt
      e6_card e6_ecount e6_etrees e6_elen (fun {F} _ x y h => e6_frames x y h) S hp hpL hTor hTp
      i hE.1 hE.2 hinner

theorem kgNotC_inner_nonA_E7
    {L : Type}
    [Field L]
    [IsAlgClosed L]
    {p₀ : ℕ}
    {p : ℕ}
    (S : CFSG.HardMathSupport.Timmesfeld.LangTorus.LangSetup CFSG.Blueprint.Chevalley.Tag.E7 L p₀)
    (hp : Nat.Prime p)
    (hpL : (↑p : L) ≠ 0)
    {a : Fin CFSG.Blueprint.Chevalley.Tag.E7.rank → Lˣ}
    (hTor : CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit
      CFSG.Blueprint.Chevalley.Tag.E7 a ∈ S.D.torus)
    (hTp : CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit
      CFSG.Blueprint.Chevalley.Tag.E7 a ^ p = 1)
    (i : CFSG.LieType.Chevalley.KernelComponent (τ := CFSG.Blueprint.Chevalley.Tag.E7) (M := Lˣ)
      (CFSG.LieType.AlgebraicGroups.rootCharHom a))
    (hnonA : ¬(1 ≤
          CFSG.HardMathSupport.Timmesfeld.LangTorus.compRank
            (CFSG.LieType.Chevalley.componentRoots (CFSG.LieType.AlgebraicGroups.rootCharHom a) i) ∧
        (CFSG.LieType.Chevalley.componentRoots (CFSG.LieType.AlgebraicGroups.rootCharHom a) i).ncard
          =
          CFSG.HardMathSupport.Timmesfeld.LangTorus.compRank
              (CFSG.LieType.Chevalley.componentRoots (CFSG.LieType.AlgebraicGroups.rootCharHom a) i)
                *
            (CFSG.HardMathSupport.Timmesfeld.LangTorus.compRank
                (CFSG.LieType.Chevalley.componentRoots (CFSG.LieType.AlgebraicGroups.rootCharHom a)
                  i) +
              1)))
    (hinner : CFSG.HardMathSupport.Timmesfeld.LangTorus.twistInner
      (CFSG.LieType.Chevalley.componentRoots (CFSG.LieType.AlgebraicGroups.rootCharHom a) i)
      (⇑S.ρ :
          (Fin CFSG.Blueprint.Chevalley.Tag.E7.rank → ℤ) →
            Fin CFSG.Blueprint.Chevalley.Tag.E7.rank →
              ℤ)^[CFSG.HardMathSupport.Timmesfeld.LangTorus.componentOrbitLength S.ρ
          (CFSG.LieType.Chevalley.componentRoots (CFSG.LieType.AlgebraicGroups.rootCharHom a) i)]) :
    CFSG.StandardType.KG.KGNotCLieType (ringChar L)
      ↥(CFSG.HardMathSupport.Timmesfeld.LangTorus.rationalComponent S.ρ S.Γ
        (CFSG.LieType.AlgebraicGroups.rootCharHom a) i) := by
  obtain ⟨v, μ, x, c, -, hc, -, hlen, -, hrank, hncard⟩ :=
    exists_cand_of_class kacE7 facts_E7 e7_tree e7_adj e7_check e7_lt e7_card S hp hpL hTp i
  have hshape := e7_shape c hc hlen
  rw [← hncard, ← hrank] at hshape
  rcases hshape with hA | hD | hE
  · exact (hnonA hA).elim
  · exact kgNotC_of_dClass (Or.inr (Or.inr (Or.inl rfl))) kacE7 facts_E7 e7_tree e7_adj e7_check
      e7_lt e7_card e7_dcount e7_dtrees (fun {F} _ x y h => e7_frames x y h) S hp hpL hTor hTp i
      hD.1 hD.2 hinner
  · exact kgNotC_of_eClass (Or.inr (Or.inr (Or.inl rfl))) kacE7 facts_E7 e7_tree e7_adj e7_check
      e7_lt e7_card e7_ecount e7_etrees e7_elen (fun {F} _ x y h => e7_frames x y h) S hp hpL hTor
      hTp i hE.1 hE.2 hinner

theorem kgNotC_inner_nonA_E8
    {L : Type}
    [Field L]
    [IsAlgClosed L]
    {p₀ : ℕ}
    {p : ℕ}
    (S : CFSG.HardMathSupport.Timmesfeld.LangTorus.LangSetup CFSG.Blueprint.Chevalley.Tag.E8 L p₀)
    (hp : Nat.Prime p)
    (hpL : (↑p : L) ≠ 0)
    {a : Fin CFSG.Blueprint.Chevalley.Tag.E8.rank → Lˣ}
    (hTor : CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit
      CFSG.Blueprint.Chevalley.Tag.E8 a ∈ S.D.torus)
    (hTp : CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit
      CFSG.Blueprint.Chevalley.Tag.E8 a ^ p = 1)
    (i : CFSG.LieType.Chevalley.KernelComponent (τ := CFSG.Blueprint.Chevalley.Tag.E8) (M := Lˣ)
      (CFSG.LieType.AlgebraicGroups.rootCharHom a))
    (hnonA : ¬(1 ≤
          CFSG.HardMathSupport.Timmesfeld.LangTorus.compRank
            (CFSG.LieType.Chevalley.componentRoots (CFSG.LieType.AlgebraicGroups.rootCharHom a) i) ∧
        (CFSG.LieType.Chevalley.componentRoots (CFSG.LieType.AlgebraicGroups.rootCharHom a) i).ncard
          =
          CFSG.HardMathSupport.Timmesfeld.LangTorus.compRank
              (CFSG.LieType.Chevalley.componentRoots (CFSG.LieType.AlgebraicGroups.rootCharHom a) i)
                *
            (CFSG.HardMathSupport.Timmesfeld.LangTorus.compRank
                (CFSG.LieType.Chevalley.componentRoots (CFSG.LieType.AlgebraicGroups.rootCharHom a)
                  i) +
              1)))
    (hinner : CFSG.HardMathSupport.Timmesfeld.LangTorus.twistInner
      (CFSG.LieType.Chevalley.componentRoots (CFSG.LieType.AlgebraicGroups.rootCharHom a) i)
      (⇑S.ρ :
          (Fin CFSG.Blueprint.Chevalley.Tag.E8.rank → ℤ) →
            Fin CFSG.Blueprint.Chevalley.Tag.E8.rank →
              ℤ)^[CFSG.HardMathSupport.Timmesfeld.LangTorus.componentOrbitLength S.ρ
          (CFSG.LieType.Chevalley.componentRoots (CFSG.LieType.AlgebraicGroups.rootCharHom a) i)]) :
    CFSG.StandardType.KG.KGNotCLieType (ringChar L)
      ↥(CFSG.HardMathSupport.Timmesfeld.LangTorus.rationalComponent S.ρ S.Γ
        (CFSG.LieType.AlgebraicGroups.rootCharHom a) i) := by
  obtain ⟨v, μ, x, c, -, hc, -, hlen, -, hrank, hncard⟩ :=
    exists_cand_of_class kacE8 facts_E8 e8_tree e8_adj e8_check e8_lt e8_card S hp hpL hTp i
  have hshape := e8_shape c hc hlen
  rw [← hncard, ← hrank] at hshape
  rcases hshape with hA | hD | hE
  · exact (hnonA hA).elim
  · exact kgNotC_of_dClass (Or.inr (Or.inr (Or.inr rfl))) kacE8 facts_E8 e8_tree e8_adj e8_check
      e8_lt e8_card e8_dcount e8_dtrees (fun {F} _ x y h => e8_frames x y h) S hp hpL hTor hTp i
      hD.1 hD.2 hinner
  · exact kgNotC_of_eClass (Or.inr (Or.inr (Or.inr rfl))) kacE8 facts_E8 e8_tree e8_adj e8_check
      e8_lt e8_card e8_ecount e8_etrees e8_elen (fun {F} _ x y h => e8_frames x y h) S hp hpL hTor
      hTp i hE.1 hE.2 hinner

end CFSG.StandardType.KG
