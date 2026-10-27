module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6RatLabel
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6FrobDefs
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6RatLabelOuterD
public import CFSG.RankThree.PartOne.KD4T.Emb
public import CFSG.RankThree.PartOne.KD4T.Inj
public import CFSG.RankThree.PartOne.KE.D4TranspositionInterface
public import CFSG.RankThree.PartOne.KE6.E6LAct
public import CFSG.LieType.Chevalley.WeylRoots
public import CFSG.LieType.Chevalley.KernelComponentRoots
public import CFSG.LieType.Chevalley.StandardParabolic
public import CFSG.LieType.Chevalley.StandardParabolicCells
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ExcD4Action
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExcD4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154NonCfgRank4B
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcTD4D4
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcTame
public import CFSG.ClassicalInvolution.Q3.Q3TWWMinus
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Lie
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPD4Rank4
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPD4Rank4All
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TriD4
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TwE6
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154NonCfgClass
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154NonCfgRank4
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaPlusIota
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphUnitaryNormal
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2RowNeighbour
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SixRevCommBasic
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14LUUnitary
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14ModelUnitary
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14PartnerCoset
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14SpAMain
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindUnitaryGlobal
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphFix
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphLevi
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaBMain
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaBRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaBShape
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaCTClass
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaCTRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaRowStepOneMinus
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowOmegaClass
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowOmegaUnitaryRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowUnitaryCover
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotInvolutionTwoPartEvenInner
public import CFSG.RankThree.PartOne.KEXC.Basic
public import CFSG.RankThree.PartOne.TCX.Ree.Perm

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section E6TwoRatLabelD

open CFSG.RankThree.PartOne.KD4T CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KE6
  CFSG.LocalAnalysis.GLTheoremA.K155X CFSG.RankThree.PartOne.KD4L
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.ExcUntw CFSG.LieType.Steinberg.Adjoint
  CFSG.RankThree.Lattice CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.Chevalley
  CFSG.RankThree.E6 CFSG.Timmesfeld.LevisSpin CFSG.ClassicalInvolution.WeakCT
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CompsPD4Tau
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CompsPD4Layers
  CFSG.Yardstones.Md0ec50421ce4

theorem e6TwoRatLabelD_permLattice_eq_one
    {τ : Tag} [E6Sub τ] {A : Set (Fin τ.rank)} {σ : Equiv.Perm (Fin τ.rank)} {y : WeylGroup τ}
    (hyfix : ∀ v : Fin τ.rank → ℤ, ∀ i, i ∉ A → (y • v) i = v i)
    (hσ : ∀ i, i ∉ A → σ i = i)
    (h : ∀ α ∈ parabolicRoots τ A, permLattice σ α = y • α) : σ = 1 := by
  have hpos : ∀ i, 0 < height (y • (Pi.single i 1 : Fin τ.rank → ℤ)) := by
    intro i
    by_cases hi : i ∈ A
    · have h1 : y • (Pi.single i 1 : Fin τ.rank → ℤ) = Pi.single (σ i) 1 := by
        rw [← h (Pi.single i 1) (single_mem_parabolicRoots hi), permLattice_single]
      rw [h1, height_single]
      exact one_pos
    · have hroot : IsRoot τ (y • (Pi.single i 1 : Fin τ.rank → ℤ)) :=
        IsRoot.smul (isRoot_single τ i) y
      rcases IsRoot.height_pos_or_neg hroot with hh | hh
      · exact hh
      · exfalso
        have hneg := (IsRoot.height_neg_iff hroot).1 hh i
        have hcoord := hyfix (Pi.single i 1 : Fin τ.rank → ℤ) i hi
        simp only [Pi.single_eq_same] at hcoord
        omega
  have hy1 : y = 1 := eq_one_of_forall_height_pos hpos
  subst hy1
  refine Equiv.ext fun i => ?_
  by_cases hi : i ∈ A
  · have h1 := h (Pi.single i 1) (single_mem_parabolicRoots hi)
    rw [one_smul, permLattice_single] at h1
    have h2 := congrFun h1 i
    by_contra hne
    have h3 : ¬ (i = σ i) := fun h4 => hne h4.symm
    simp [Pi.single_apply, h3] at h2
  · exact hσ i hi

theorem e6TwoRatLabelD_leafPerm_eq_one
    {τ : Tag} [E6Sub τ] {x : WeylGroup τ} (hx : x ∈ parabolicWeylGroup τ (d4Set τ))
    {π : Equiv.Perm (Fin τ.rank)} (hπfix : ∀ i, i ∉ d4Set τ → π i = i)
    (h : ∀ j ∈ d4Set τ, x • (Pi.single j 1 : Fin τ.rank → ℤ) = Pi.single (π j) 1) :
    π = 1 := by
  have hpos : ∀ i, 0 < height (x • (Pi.single i 1 : Fin τ.rank → ℤ)) := by
    intro i
    by_cases hi : i ∈ d4Set τ
    · rw [h i hi, height_single]
      exact one_pos
    · have hroot : IsRoot τ (x • (Pi.single i 1 : Fin τ.rank → ℤ)) :=
        IsRoot.smul (isRoot_single τ i) x
      rcases IsRoot.height_pos_or_neg hroot with hh | hh
      · exact hh
      · exfalso
        have hneg := (IsRoot.height_neg_iff hroot).1 hh i
        have hcoord := smul_apply_of_mem_parabolicWeylGroup hx (Pi.single i 1 : Fin τ.rank → ℤ) hi
        simp only [Pi.single_eq_same] at hcoord
        omega
  have hx1 : x = 1 := eq_one_of_forall_height_pos hpos
  subst hx1
  refine Equiv.ext fun i => ?_
  by_cases hi : i ∈ d4Set τ
  · have h1 := h i hi
    rw [one_smul] at h1
    have h2 := congrFun h1 i
    by_contra hne
    have h3 : ¬ (i = π i) := fun h4 => hne h4.symm
    simp [Pi.single_apply, h3] at h2
  · exact hπfix i hi

theorem e6TwoRatLabelD_conj_inv_mem_parabolic
    {τ : Tag} [E6Sub τ] (v : WeylGroup τ) {z : WeylGroup τ}
    (hz : z ∈ Subgroup.closure {s : WeylGroup τ |
      ∃ γ ∈ (fun α => v • α) '' parabolicRoots τ (d4Set τ), s = rootReflection γ}) :
    v⁻¹ * z * v ∈ Subgroup.closure {s : WeylGroup τ |
      ∃ α ∈ parabolicRoots τ (d4Set τ), s = rootReflection α} := by
  induction hz using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨γ, hγ, rfl⟩ := hx
    obtain ⟨α, hα, rfl⟩ := hγ
    rw [rootReflection_smul_root v hα.1]
    have he : v⁻¹ * (v * rootReflection α * v⁻¹) * v = rootReflection α := by group
    rw [he]
    exact Subgroup.subset_closure ⟨α, hα, rfl⟩
  | one => rw [mul_one, inv_mul_cancel]; exact one_mem _
  | mul x y hx hy ihx ihy =>
    have he : v⁻¹ * (x * y) * v = (v⁻¹ * x * v) * (v⁻¹ * y * v) := by group
    rw [he]
    exact mul_mem ihx ihy
  | inv x hx ihx =>
    have he : v⁻¹ * x⁻¹ * v = (v⁻¹ * x * v)⁻¹ := by group
    rw [he]
    exact inv_mem ihx

theorem e6TwoRatLabelD_closure_rootReflection_fixes
    {τ : Tag} {A : Set (Fin τ.rank)} {y : WeylGroup τ}
    (hy : y ∈ Subgroup.closure {s : WeylGroup τ | ∃ α ∈ parabolicRoots τ A, s = rootReflection α}) :
    ∀ v : Fin τ.rank → ℤ, ∀ i, i ∉ A → (y • v) i = v i := by
  induction hy using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨α, hα, rfl⟩ := hx
    intro v i hi
    rw [rootReflection_smul hα.1]
    simp only [Pi.sub_apply, Pi.smul_apply]
    rw [hα.2 i hi, smul_zero, sub_zero]
  | one => intro v i hi; rw [one_smul]
  | mul x y hx hy ihx ihy =>
    intro v i hi
    rw [mul_smul, ihx (y • v) i hi, ihy v i hi]
  | inv x hx ihx =>
    intro v i hi
    have h1 := ihx (x⁻¹ • v) i hi
    rw [smul_inv_smul] at h1
    exact h1.symm

theorem e6TwoRatLabelD_leaf_sq
    {τ : Tag} [E6Sub τ] {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    (hsearch : D4BaseSearch τ) (S : LangSetup τ L p) {w : WeylGroup τ}
    (hρw : ∀ γ, IsRoot τ γ → S.ρ γ = w • γ)
    {a : Fin τ.rank → Lˣ} (i : KernelComponent (rootCharHom a)) (v : WeylGroup τ)
    (hΨ : componentRoots (rootCharHom a) i = (fun α => v • α) '' parabolicRoots τ (d4Nodes τ))
    (hρ : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i)
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[2])) :
    ∀ (u : WeylGroup τ), u ∈ parabolicWeylGroup τ (d4Set τ) →
    ∀ (π : Equiv.Perm (Fin τ.rank)), IsD4LeafPerm π →
      (∀ α ∈ parabolicRoots τ (d4Set τ),
        (v⁻¹ * w * v) • α = u • permLattice π α) → π * π = 1 := by
  classical
  intro u hu π hπ hact
  let Ψ : Set (Fin τ.rank → ℤ) := componentRoots (rootCharHom a) i
  have hw : ∀ γ ∈ Ψ, w • γ ∈ Ψ := fun γ hγ => by
    rw [← hρw γ hγ.1.1]
    exact hρ γ hγ
  have hmem_of : ∀ α ∈ parabolicRoots τ (d4Set τ),
      v • α ∈ componentRoots (rootCharHom a) i := fun α hα =>
    hΨ.symm ▸ ⟨α, hα, rfl⟩
  have hmaps : MapsJ τ (d4Set τ) (v⁻¹ * w * v) := by
    intro α hα
    obtain ⟨β, hβ, hβe⟩ := (hΨ ▸ hw (v • α) (hmem_of α hα) :
      w • v • α ∈ (fun α => v • α) '' parabolicRoots τ (d4Set τ))
    rw [mul_smul, mul_smul, ← hβe, inv_smul_smul]
    exact hβ
  obtain ⟨u₀, hu₀, w₀, hw₀, hw₀maps, hpos⟩ :=
    exists_descent (d4Set τ) ((coxeterSystem τ).length (v⁻¹ * w * v)) (v⁻¹ * w * v) rfl hmaps
  obtain ⟨σ, hσ, hw₀inv⟩ := d4_base_of_pos hsearch hw₀maps.inv hpos
  have hπ₀ : IsD4LeafPerm σ⁻¹ := hσ.inv
  have hw₀π₀ : ∀ k ∈ d4Set τ, w₀ • (Pi.single k 1 : Fin τ.rank → ℤ) =
      Pi.single (σ⁻¹ k) 1 := by
    intro k hk
    have hk' : σ⁻¹ k ∈ d4Set τ := hσ.inv.mem_d4Set hk
    have h := hw₀inv (σ⁻¹ k) hk'
    have h2 : (Pi.single (σ⁻¹ k) 1 : Fin τ.rank → ℤ) =
        w₀ • (Pi.single k 1 : Fin τ.rank → ℤ) := by
      calc (Pi.single (σ⁻¹ k) 1 : Fin τ.rank → ℤ)
          = w₀ • (w₀⁻¹ • (Pi.single (σ⁻¹ k) 1 : Fin τ.rank → ℤ)) := by rw [smul_inv_smul]
        _ = w₀ • (Pi.single (σ (σ⁻¹ k)) 1 : Fin τ.rank → ℤ) := by rw [h]
        _ = w₀ • (Pi.single k 1 : Fin τ.rank → ℤ) := by
              rw [Equiv.Perm.inv_def, Equiv.apply_symm_apply]
    exact h2.symm
  have hlin0 : ∀ α ∈ parabolicRoots τ (d4Set τ), w₀ • α = permLattice σ⁻¹ α :=
    fun α hα => by
      have := smul_eq_of_simple (w := w₀) (u := 1) (π := σ⁻¹) (J := d4Set τ)
        (fun j hj => by rw [one_smul]; exact hw₀π₀ j hj) hα.2
      rwa [one_smul] at this
  have hact₀ : ∀ α ∈ parabolicRoots τ (d4Set τ),
      (v⁻¹ * w * v) • α = u₀ • permLattice σ⁻¹ α := fun α hα => by
    rw [hw₀, mul_smul, hlin0 α hα]
  have hfix_of_leaf : ∀ {ρ : Equiv.Perm (Fin τ.rank)}, IsD4LeafPerm ρ →
      ∀ i, i ∉ d4Set τ → ρ i = i := by
    intro ρ hρ i hi
    exact hρ.apply_of_ne
      (fun h => hi (h.symm ▸ e6Idx_mem_d4Set' 1 (by decide) (by decide)))
      (fun h => hi (h.symm ▸ e6Idx_mem_d4Set' 2 (by decide) (by decide)))
      (fun h => hi (h.symm ▸ e6Idx_mem_d4Set' 4 (by decide) (by decide)))
  have huniq : π = σ⁻¹ := by
    have hx : u₀⁻¹ * u ∈ parabolicWeylGroup τ (d4Set τ) := mul_mem (inv_mem hu₀) hu
    have hbase : ∀ k ∈ d4Set τ, (u₀⁻¹ * u) • (Pi.single k 1 : Fin τ.rank → ℤ) =
        Pi.single ((σ⁻¹ * π⁻¹) k) 1 := by
      intro k hk
      have hk' : π⁻¹ k ∈ d4Set τ := hπ.inv.mem_d4Set hk
      have e1 := hact (Pi.single (π⁻¹ k) 1) (single_mem_parabolicRoots hk')
      have e2 := hact₀ (Pi.single (π⁻¹ k) 1) (single_mem_parabolicRoots hk')
      rw [permLattice_single] at e1 e2
      have hEq : u • (Pi.single (π (π⁻¹ k)) 1 : Fin τ.rank → ℤ) =
          u₀ • (Pi.single (σ⁻¹ (π⁻¹ k)) 1 : Fin τ.rank → ℤ) := e1.symm.trans e2
      have h2 := congrArg (fun z => u₀⁻¹ • z) hEq
      simp only [smul_smul, inv_mul_cancel, one_smul] at h2
      rw [Equiv.Perm.inv_def, Equiv.apply_symm_apply] at h2
      rw [Equiv.Perm.mul_apply]
      exact h2
    have hσfix : ∀ i, i ∉ d4Set τ → (σ⁻¹ * π⁻¹) i = i := by
      intro i hi
      rw [Equiv.Perm.mul_apply, hfix_of_leaf hπ.inv i hi, hfix_of_leaf hπ₀ i hi]
    have h1 : σ⁻¹ * π⁻¹ = 1 :=
      e6TwoRatLabelD_leafPerm_eq_one hx hσfix hbase
    have h2 : σ⁻¹ = π := mul_inv_eq_one.mp h1
    exact h2.symm
  rw [huniq]
  obtain ⟨z, hz_mem, hz⟩ := hinner
  set z' : WeylGroup τ := v⁻¹ * z * v with hz'def
  have hz_mem' : z ∈ Subgroup.closure {s : WeylGroup τ |
      ∃ γ ∈ (fun α => v • α) '' parabolicRoots τ (d4Set τ), s = rootReflection γ} := by
    rw [hΨ] at hz_mem
    exact hz_mem
  have hz'_mem : z' ∈ Subgroup.closure {s : WeylGroup τ |
      ∃ α ∈ parabolicRoots τ (d4Set τ), s = rootReflection α} :=
    e6TwoRatLabelD_conj_inv_mem_parabolic v hz_mem'
  have hz'fix : ∀ v' : Fin τ.rank → ℤ, ∀ i, i ∉ d4Set τ → (z' • v') i = v' i :=
    e6TwoRatLabelD_closure_rootReflection_fixes hz'_mem
  have hx : w₀ * u₀ * w₀⁻¹ ∈ parabolicWeylGroup τ (d4Set τ) := by
    have hle : (parabolicWeylGroup τ (d4Set τ)).map (MulAut.conj w₀).toMonoidHom ≤
        parabolicWeylGroup τ (d4Set τ) := by
      rw [parabolicWeylGroup, MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨_, ⟨j, hj, rfl⟩, rfl⟩
      refine Subgroup.subset_closure ⟨σ⁻¹ j, hπ₀.mem_d4Set hj, ?_⟩
      change simple τ (σ⁻¹ j) = w₀ * simple τ j * w₀⁻¹
      rw [← rootReflection_single, ← rootReflection_eq_conj (hw₀π₀ j hj)]
    exact hle ⟨u₀, hu₀, rfl⟩
  set y : WeylGroup τ := u₀ * (w₀ * u₀ * w₀⁻¹) with hydef
  set y' : WeylGroup τ := y⁻¹ * z' with hy'def
  have hy'fix : ∀ v' : Fin τ.rank → ℤ, ∀ i, i ∉ d4Set τ → (y' • v') i = v' i := by
    intro v' i hi
    have h1 : (y⁻¹ • (z' • v')) i = (z' • v') i :=
      smul_apply_of_mem_parabolicWeylGroup (inv_mem (hydef.symm ▸ mul_mem hu₀ hx)) (z' • v') hi
    rw [hy'def, mul_smul, h1, hz'fix v' i hi]
  have hww : ∀ α ∈ parabolicRoots τ (d4Set τ), z' • α = (v⁻¹ * w * v) • ((v⁻¹ * w * v) • α) := by
    intro α hα
    have hmem : v • α ∈ Ψ := hmem_of α hα
    have hmem2 : w • (v • α) ∈ Ψ := by
      rw [← hρw (v • α) hmem.1.1]
      exact hρ (v • α) hmem
    have h1 : (S.ρ : (Fin τ.rank → ℤ) → _) (v • α) = w • (v • α) := hρw (v • α) hmem.1.1
    have h2 : (S.ρ : (Fin τ.rank → ℤ) → _) (w • (v • α)) = w • (w • (v • α)) :=
      hρw _ hmem2.1.1
    have h3 : ((S.ρ : (Fin τ.rank → ℤ) → _)^[2]) (v • α) = z • (v • α) := hz (v • α) hmem
    change (S.ρ : (Fin τ.rank → ℤ) → _) ((S.ρ : (Fin τ.rank → ℤ) → _) (v • α)) = z • (v • α) at h3
    rw [h1, h2] at h3
    calc z' • α = v⁻¹ • (z • (v • α)) := by
          simp only [hz'def, mul_smul]
      _ = v⁻¹ • (w • (w • (v • α))) := by rw [← h3]
      _ = (v⁻¹ * w * v) • ((v⁻¹ * w * v) • α) := by simp only [mul_smul, smul_inv_smul]
  have hbase₂ : ∀ α ∈ parabolicRoots τ (d4Set τ), permLattice (σ⁻¹ * σ⁻¹) α = y' • α := by
    intro α hα
    have hzα := hww α hα
    have hsq_act : (v⁻¹ * w * v) • ((v⁻¹ * w * v) • α) = y • (w₀ • (w₀ • α)) := by
      rw [hw₀]
      simp only [hydef, mul_smul, inv_smul_smul]
    have h1 : y • (w₀ • (w₀ • α)) = z' • α := hsq_act.symm.trans hzα.symm
    have h2 : w₀ • (w₀ • α) = y' • α := by
      calc w₀ • (w₀ • α) = y⁻¹ • (y • (w₀ • (w₀ • α))) := by rw [inv_smul_smul]
        _ = y⁻¹ • (z' • α) := by rw [h1]
        _ = y' • α := by simp only [hy'def, mul_smul]
    have h3 : w₀ • (w₀ • α) = permLattice (σ⁻¹ * σ⁻¹) α := by
      rw [hlin0 _ (hw₀maps α hα), hlin0 α hα, ← permLattice_mul]
    rw [← h3]
    exact h2
  have hσfix₂ : ∀ i, i ∉ d4Set τ → (σ⁻¹ * σ⁻¹) i = i := by
    intro i hi
    rw [Equiv.Perm.mul_apply, hfix_of_leaf hπ₀ i hi, hfix_of_leaf hπ₀ i hi]
  have hσ2 : σ⁻¹ * σ⁻¹ = 1 :=
    e6TwoRatLabelD_permLattice_eq_one (A := d4Set τ) (σ := σ⁻¹ * σ⁻¹) (y := y') hy'fix hσfix₂ hbase₂
  have : σ⁻¹ * σ⁻¹ = 1 := hσ2
  simpa using this

end E6TwoRatLabelD

end CFSG.StandardType.TablePThreeKG

end
