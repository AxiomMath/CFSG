module

public import CFSG.LocalAnalysis.StandardType.GGLangCoroot
public import CFSG.LocalAnalysis.StandardType.GGTBJE8LeviEnnComp
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenRank
public import CFSG.RankThree.Classical2.SLnFrobeniusFormFixed
public import CFSG.LocalAnalysis.StandardType.GGLangRootSym3
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleSplit
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleLang
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleField
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenAsm

public section

namespace CFSG.StandardType.LangRat

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE CFSG.RankThree.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial

open scoped MatrixGroups

private theorem conjSLn_WSL_uSL_of_charTwo {L : Type} [Field L] [CharP L 2] (c : L) :
    CFSG.RankThree.Classical2.conjSLn (Matrix.SpecialLinearGroup.toGL WSL) (uSL c) = vSL c := by
  rw [CFSG.RankThree.Classical2.conjSLn_toGL]
  ext i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, coe_uSL,
    coe_vSL, coe_WSL]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two, CharTwo.neg_eq]

private theorem conjSLn_WSL_vSL_of_charTwo {L : Type} [Field L] [CharP L 2] (c : L) :
    CFSG.RankThree.Classical2.conjSLn (Matrix.SpecialLinearGroup.toGL WSL) (vSL c) = uSL c := by
  rw [CFSG.RankThree.Classical2.conjSLn_toGL]
  ext i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, coe_uSL,
    coe_vSL, coe_WSL]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two, CharTwo.neg_eq]

theorem step_rootSL2_of_rho_neg
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hρ : S.ρ α = -α) (Fr : L →+* L)
    (hFr : ∀ c, Fr c = c ^ S.D.q) (X : SL(2, L)) :
    S.D.step (rootSL2 τ L α X) =
      rootSL2 τ L α (CFSG.RankThree.Classical2.conjSLn (Matrix.SpecialLinearGroup.toGL WSL)
        (Matrix.SpecialLinearGroup.map Fr X)) := by
  have h : S.D.step.comp (rootSL2 τ L α) = (rootSL2 τ L α).comp
      ((CFSG.RankThree.Classical2.conjSLn (Matrix.SpecialLinearGroup.toGL WSL)).comp
        (Matrix.SpecialLinearGroup.map Fr)) :=
    MonoidHom.eq_of_eqOn_dense sl2_closure_upper_lower fun g hg => by
      rcases hg with ⟨c, rfl⟩ | ⟨c, rfl⟩
      · change S.D.step (rootSL2 τ L α (uSL c)) = rootSL2 τ L α
          (CFSG.RankThree.Classical2.conjSLn (Matrix.SpecialLinearGroup.toGL WSL)
            (Matrix.SpecialLinearGroup.map Fr (uSL c)))
        rw [rootSL2_uSL_of_charTwo hα, step_pinnedX_of_charTwo S hα, hρ, map_uSL,
          conjSLn_WSL_uSL_of_charTwo, rootSL2_vSL_of_charTwo hα, hFr]
      · change S.D.step (rootSL2 τ L α (vSL c)) = rootSL2 τ L α
          (CFSG.RankThree.Classical2.conjSLn (Matrix.SpecialLinearGroup.toGL WSL)
            (Matrix.SpecialLinearGroup.map Fr (vSL c)))
        rw [rootSL2_vSL_of_charTwo hα, step_pinnedX_of_charTwo S (IsRoot.neg hα),
          S.frob.neg_eq, hρ, neg_neg, map_vSL, conjSLn_WSL_vSL_of_charTwo,
          rootSL2_uSL_of_charTwo hα, hFr]
  exact DFunLike.congr_fun h X

theorem rootSL2_WSL_mem_rationalComponent_of_rho_neg
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {k' : Type} [Field k'] [Finite k'] [Algebra k' L] [IsAlgClosure k' L]
    {n : ℕ} (hn : 2 ≤ n) (hq : S.D.q = 2 ^ n)
    {a : Fin τ.rank → Lˣ} (i : KernelComponent (rootCharHom a))
    (hρ : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ = -γ)
    {α : Fin τ.rank → ℤ} (hα : α ∈ componentRoots (rootCharHom a) i) :
    rootSL2 τ L α WSL ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i := by
  classical
  have hΨ := isRootComponent_componentRoots (χ := rootCharHom a) i
  have hαr : IsRoot τ α := hΨ.isRoot α hα
  have hstab : ∀ γ ∈ componentRoots (rootCharHom a) i,
      S.ρ γ ∈ componentRoots (rootCharHom a) i := fun γ hγ => by
    rw [hρ γ hγ]
    exact hΨ.neg_mem γ hγ
  let Fr : L →+* L := iterateFrobenius L 2 n
  have hFr' : ∀ c, Fr c = c ^ 2 ^ n := fun c => iterateFrobenius_def 2 n c
  have hFr : ∀ c, Fr c = c ^ S.D.q := fun c => by rw [hq]; exact hFr' c
  let A : GL (Fin 2) L := Matrix.SpecialLinearGroup.toGL WSL
  let F' : SL(2, L) →* SL(2, L) :=
    (CFSG.RankThree.Classical2.conjSLn A).comp (Matrix.SpecialLinearGroup.map Fr)
  have hψF : ∀ X, S.D.step (rootSL2 τ L α X) = rootSL2 τ L α (F' X) :=
    step_rootSL2_of_rho_neg S hαr (hρ α hα) Fr hFr
  have h4 : 4 ≤ 2 ^ n :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨-, hQ⟩ := CFSG.RankThree.Classical2.isQuasisimple_eqLocus_conjSLn_frobenius_split
    (k' := k') (Ω := L) (ℓ := 2) (f := n) (n := 2) Nat.prime_two (by omega) le_rfl
    (Or.inr h4) Fr hFr' A
  have hKperf : ⁅F'.eqLocus (MonoidHom.id _), F'.eqLocus (MonoidHom.id _)⁆ =
      F'.eqLocus (MonoidHom.id _) := by
    haveI : Group.IsPerfect ↥(F'.eqLocus (MonoidHom.id _)) := hQ.1
    rw [← Subgroup.map_subtype_commutator, Group.IsPerfect.commutator_eq_top,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hWfix : Matrix.SpecialLinearGroup.map Fr WSL = WSL := by
    ext i j
    rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
      coe_WSL]
    fin_cases i <;> fin_cases j <;> simp
  have hW : WSL ∈ F'.eqLocus (MonoidHom.id _) := by
    change CFSG.RankThree.Classical2.conjSLn (Matrix.SpecialLinearGroup.toGL WSL)
      (Matrix.SpecialLinearGroup.map Fr WSL) = WSL
    rw [hWfix, CFSG.RankThree.Classical2.conjSLn_toGL]
    group
  have hsub : ({α, -α} : Set (Fin τ.rank → ℤ)) ⊆ componentRoots (rootCharHom a) i := by
    intro γ hγ
    rcases hγ with rfl | hγ
    · exact hα
    · rw [Set.mem_singleton_iff] at hγ
      rw [hγ]
      exact hΨ.neg_mem α hα
  exact CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSGen.map_fix_le_rationalComponent
    S i hstab (rootSL2 τ L α) (fun X => rootSpan_mono hsub
      (CFSG.HardMathSupport.Timmesfeld.CrossChar.rootSL2_mem_rootSpan_pair hαr X))
    (fun X => (exceptional_Lang_root_rank_one_data τ L α).2.2.2.2.1 X) F' hψF _ (fun y hy => hy)
    hKperf WSL hW

theorem eq_one_of_frobGL_eq_of_mem_torusGroup
    {τ : Tag} {L : Type} [Field L] {σ : L ≃+* L} (hσ : ∀ c, σ c = c ^ 2) {t : ModGL τ L}
    (ht : t ∈ torusGroup τ L) (hfix : frobGL σ t = t) : t = 1 := by
  obtain ⟨l, rfl⟩ := CFSG.LieType.Chevalley.exists_rootDiagUnit_eq_of_mem_torusGroup ht
  have h1 : (fun j => Units.map σ.toRingHom.toMonoidHom (l j)) = l := by
    apply CFSG.LieType.Chevalley.rootDiagUnit_injective
    rw [← CFSG.LieType.Chevalley.units_map_entrywiseHom_rootDiagUnit_ringEquiv]
    exact hfix
  have hl : l = 1 := funext fun j => by
    have h2 : σ (l j : L) = l j := congrArg (fun u : Lˣ => (u : L)) (congrFun h1 j)
    rw [hσ] at h2
    have hne : (l j : L) ≠ 0 := (l j).ne_zero
    have h3 : (l j : L) * ((l j : L) - 1) = 0 := by linear_combination h2
    exact Units.ext (by
      rcases mul_eq_zero.1 h3 with h | h
      · exact absurd h hne
      · simpa using sub_eq_zero.1 h)
  rw [hl]
  exact rootDiagUnit_one

theorem frobGL_eq_of_mem_CQ
    {τ : Tag} {L : Type} [Field L] (σ : L ≃+* L) {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {i : KernelComponent χ} {x : ModGL τ L}
    (hx : x ∈ CQ σ i) : frobGL σ x = x := by
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨γ, -, c, hc, rfl⟩ := hx
    rw [frobGL_pinnedX, hc]
  | one => exact map_one _
  | mul x y _ _ hx hy => rw [map_mul, hx, hy]
  | inv x _ hx => rw [map_inv, hx]

theorem rootSL2_WSL_mem_rationalComponent_of_neg_two
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ} (S : LangSetup τ L p₀)
    (hq2 : S.D.q = 2) {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a))
    (hρ : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ = -γ)
    (hneg : ∃ w ∈ Subgroup.closure {s : WeylGroup τ | ∃ γ ∈ componentRoots (rootCharHom a) i,
        s = rootReflection γ}, ∀ γ ∈ componentRoots (rootCharHom a) i, w • γ = -γ)
    (hperf : ∀ F : Subfield L, (∀ x : F, x = 0 ∨ x = 1) →
      Group.IsPerfect (componentRootSpan F (rootCharHom a) i))
    {α : Fin τ.rank → ℤ} (hα : α ∈ componentRoots (rootCharHom a) i) :
    rootSL2 τ L α WSL ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i := by
  classical
  have hΨ := isRootComponent_componentRoots (χ := rootCharHom a) i
  have hαr : IsRoot τ α := hΨ.isRoot α hα
  have hstab : ∀ γ ∈ componentRoots (rootCharHom a) i,
      S.ρ γ ∈ componentRoots (rootCharHom a) i := fun γ hγ => by
    rw [hρ γ hγ]
    exact hΨ.neg_mem γ hγ
  have hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[1]) := by
    obtain ⟨w, hw, hwγ⟩ := hneg
    exact ⟨w, hw, fun γ hγ => by rw [Function.iterate_one, hρ γ hγ, hwγ γ hγ]⟩
  obtain ⟨σ, z, hσ, hnorm, hz⟩ := exists_untwistT S hT i one_pos hinner
  have hσ2 : ∀ c, σ c = c ^ 2 := fun c => by rw [hσ, hq2, pow_one]
  let Fr : L →+* L := iterateFrobenius L 2 1
  have hFr : ∀ c, Fr c = c ^ S.D.q := fun c => by
    rw [hq2]
    show iterateFrobenius L 2 1 c = c ^ 2
    rw [iterateFrobenius_def, pow_one]
  have hWfix : Matrix.SpecialLinearGroup.map Fr WSL = WSL := by
    ext i j
    rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
      coe_WSL]
    fin_cases i <;> fin_cases j <;> simp
  set g := rootSL2 τ L α WSL with hg
  have hgstep : S.D.step g = g := by
    rw [hg, step_rootSL2_of_rho_neg S hαr (hρ α hα) Fr hFr WSL, hWfix,
      CFSG.RankThree.Classical2.conjSLn_toGL]
    congr 1
    group
  have hsub : ({α, -α} : Set (Fin τ.rank → ℤ)) ⊆ componentRoots (rootCharHom a) i := by
    intro γ hγ
    rcases hγ with rfl | hγ
    · exact hα
    · rw [Set.mem_singleton_iff] at hγ
      rw [hγ]
      exact hΨ.neg_mem α hα
  have hgS : g ∈ rootSpan τ L (componentRoots (rootCharHom a) i) :=
    rootSpan_mono hsub (CFSG.HardMathSupport.Timmesfeld.CrossChar.rootSL2_mem_rootSpan_pair hαr WSL)
  set h := z⁻¹ * g * z with hh
  have hzh : z * h * z⁻¹ = g := by rw [hh]; group
  have hhS : h ∈ rootSpan τ L (componentRoots (rootCharHom a) i) :=
    (hnorm i h).2 (by rw [hzh]; exact hgS)
  have hhfix : frobGL σ h = h := by
    have h1 := hz h hhS
    rw [iterHom_eq_iterate, Function.iterate_one, hzh, hgstep] at h1
    calc frobGL σ h = z⁻¹ * (z * frobGL σ h * z⁻¹) * z := by group
      _ = z⁻¹ * g * z := by rw [← h1]
      _ = h := hh.symm
  have hhU : h ∈ unionRootSpan L (rootCharHom a) ({i} : Set (KernelComponent (rootCharHom a))) := by
    rw [unionRootSpan, unionRoots_singleton]
    exact hhS
  obtain ⟨t, ht, x, hx, hhtx, htfix⟩ := exists_decomp (σ := σ) (i := i) hhU
    (Subgroup.one_mem _) (by rw [one_mul]; exact hhfix)
  have ht1 : t = 1 := eq_one_of_frobGL_eq_of_mem_torusGroup hσ2
    (unionTorus_le_torusGroup ht) (by rw [one_mul] at htfix; exact htfix)
  rw [ht1, one_mul] at hhtx
  have hF2 : ∀ y : fixSubfield σ, y = 0 ∨ y = 1 := by
    intro y
    have hy : σ (y : L) = y := y.2
    rw [hσ2] at hy
    have h3 : (y : L) * ((y : L) - 1) = 0 := by linear_combination hy
    rcases mul_eq_zero.1 h3 with h0 | h0
    · exact Or.inl (Subtype.ext h0)
    · exact Or.inr (Subtype.ext (by simpa using sub_eq_zero.1 h0))
  haveI hCperf : Group.IsPerfect (componentRootSpan (fixSubfield σ) (rootCharHom a) i) :=
    hperf (fixSubfield σ) hF2
  let ψ : ↥(componentRootSpan (fixSubfield σ) (rootCharHom a) i) →* ModGL τ L :=
    (MulAut.conj z).toMonoidHom.comp ((baseChangeGL (fixSubfield σ).subtype).comp
      (componentRootSpan (fixSubfield σ) (rootCharHom a) i).subtype)
  have hιCQ : ∀ y : ↥(componentRootSpan (fixSubfield σ) (rootCharHom a) i),
      baseChangeGL (fixSubfield σ).subtype (y : ModGL τ (fixSubfield σ)) ∈ CQ σ i := fun y => by
    rw [CQ_eq_map]
    exact ⟨y, y.2, rfl⟩
  have hψS : ∀ y, ψ y ∈ rootSpan τ L (componentRoots (rootCharHom a) i) := fun y =>
    (hnorm i _).1 (CQ_le_rootSpan σ i (hιCQ y))
  have hψA : ∀ y, ψ y ∈ adjointGroup τ L := fun y =>
    CFSG.LieType.Chevalley.rootSpan_le_adjointGroup L _ (hψS y)
  have hψF : ∀ y, S.D.step (ψ y) = ψ ((MonoidHom.id _) y) := fun y => by
    have h1 := hz _ (CQ_le_rootSpan σ i (hιCQ y))
    rw [iterHom_eq_iterate, Function.iterate_one, frobGL_eq_of_mem_CQ σ (hιCQ y)] at h1
    exact h1
  have hKperf : ⁅(⊤ : Subgroup ↥(componentRootSpan (fixSubfield σ) (rootCharHom a) i)),
      (⊤ : Subgroup ↥(componentRootSpan (fixSubfield σ) (rootCharHom a) i))⁆ =
      (⊤ : Subgroup ↥(componentRootSpan (fixSubfield σ) (rootCharHom a) i)) := by
    rw [← commutator_def]
    exact Group.IsPerfect.commutator_eq_top
  have hx' : x ∈ (componentRootSpan (fixSubfield σ) (rootCharHom a) i).map
      (baseChangeGL (fixSubfield σ).subtype) := by
    rw [← CQ_eq_map]
    exact hx
  obtain ⟨y, hyC, hyx⟩ := hx'
  have hgψ : g = ψ ⟨y, hyC⟩ := by
    change g = z * baseChangeGL (fixSubfield σ).subtype y * z⁻¹
    rw [hyx, ← hhtx, hzh]
  rw [hgψ]
  exact CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSGen.map_fix_le_rationalComponent
    S i hstab ψ hψS hψA (MonoidHom.id _) hψF ⊤ (fun _ _ => rfl) hKperf _ trivial

private theorem charP_algebraicClosure_two' {K : Type} [Field K] [CharP K 2] :
    CharP (AlgebraicClosure K) 2 :=
  (Algebra.charP_iff (K := K) (L := AlgebraicClosure K) 2).symm.mpr inferInstance

theorem realizes_rootReflection_of_mem
    {τ : Tag} {K : Type} [Field K] [Finite K] {p p₀ : ℕ} [NeZero p]
    (S : LangSetup τ (AlgebraicClosure K) p₀)
    (ι : adjointGroup τ K →* ModGL τ (AlgebraicClosure K)) (hι : Function.Injective ι)
    {ζ : (AlgebraicClosure K)ˣ} {hζ : ζ ^ p = 1}
    {ι₀ : Multiplicative (Fin τ.rank → ZMod p) →* adjointGroup τ K}
    (hιι₀ : ∀ s, ι (ι₀ (Multiplicative.ofAdd s)) = ExcFrames.frameDiag ζ hζ s)
    {a : Fin τ.rank → (AlgebraicClosure K)ˣ} (i : KernelComponent (rootCharHom a))
    {Y : Subgroup (adjointGroup τ K)}
    (hY : Y.map ι = rationalComponent S.ρ S.Γ (rootCharHom a) i)
    {c : Fin τ.rank → ℤ} (hcr : IsRoot τ c)
    (hmem : rootSL2 τ (AlgebraicClosure K) c WSL ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i) :
    ∃ g ∈ Y, ∀ s, g * ι₀ (Multiplicative.ofAdd s) * g⁻¹ =
      ι₀ (Multiplicative.ofAdd (TableBExc.torusAct τ p (rootReflection c) s)) := by
  classical
  obtain ⟨g, hgY, hgι⟩ := Subgroup.mem_map.mp (hY ▸ hmem)
  refine ⟨g, hgY, fun s => hι ?_⟩
  calc ι (g * ι₀ (Multiplicative.ofAdd s) * g⁻¹)
      = ι g * ι (ι₀ (Multiplicative.ofAdd s)) * (ι g)⁻¹ := by
          rw [map_mul, map_mul, map_inv]
    _ = rootSL2 τ (AlgebraicClosure K) c WSL * ExcFrames.frameDiag ζ hζ s *
          (rootSL2 τ (AlgebraicClosure K) c WSL)⁻¹ := by rw [hgι, hιι₀]
    _ = ExcFrames.frameDiag ζ hζ (TableBExc.torusAct τ p (rootReflection c) s) :=
          CFSG.StandardType.monomial_conj_frameDiag_gen hζ
            (CFSG.ClassicalInvolution.ModelFacts.Levi.rootSL2_WSL_mem_monomialSubgroup
              (τ := τ) (K := AlgebraicClosure K) hcr)
            (CFSG.ClassicalInvolution.ModelFacts.Levi.mapsRootLines_rootSL2_WSL
              (τ := τ) (K := AlgebraicClosure K) hcr) s
    _ = ι (ι₀ (Multiplicative.ofAdd (TableBExc.torusAct τ p (rootReflection c) s))) :=
          (hιι₀ _).symm

theorem rationalComponent_realizes_rootReflection
    {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2] {p p₀ : ℕ} [NeZero p]
    (S : LangSetup τ (AlgebraicClosure K) p₀)
    (ι : adjointGroup τ K →* ModGL τ (AlgebraicClosure K)) (hι : Function.Injective ι)
    {ζ : (AlgebraicClosure K)ˣ} {hζ : ζ ^ p = 1}
    {ι₀ : Multiplicative (Fin τ.rank → ZMod p) →* adjointGroup τ K}
    (hιι₀ : ∀ s, ι (ι₀ (Multiplicative.ofAdd s)) = ExcFrames.frameDiag ζ hζ s)
    {n : ℕ} (hn : 2 ≤ n) (hq : S.D.q = 2 ^ n)
    {a : Fin τ.rank → (AlgebraicClosure K)ˣ} (i : KernelComponent (rootCharHom a))
    (hρ : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ = -γ)
    {Y : Subgroup (adjointGroup τ K)}
    (hY : Y.map ι = rationalComponent S.ρ S.Γ (rootCharHom a) i) :
    ∀ c ∈ componentRoots (rootCharHom a) i, ∃ g ∈ Y, ∀ s,
      g * ι₀ (Multiplicative.ofAdd s) * g⁻¹ =
        ι₀ (Multiplicative.ofAdd (TableBExc.torusAct τ p (rootReflection c) s)) := by
  classical
  haveI : CharP (AlgebraicClosure K) 2 := charP_algebraicClosure_two'
  intro c hc
  have hcr : IsRoot τ c := (isRootComponent_componentRoots (χ := rootCharHom a) i).isRoot c hc
  exact realizes_rootReflection_of_mem S ι hι hιι₀ i hY hcr
    (rootSL2_WSL_mem_rationalComponent_of_rho_neg (k' := K) S hn hq i hρ hc)

end CFSG.StandardType.LangRat

end
