module

public import CFSG.LocalAnalysis.StandardType.GGLangRootSL2Rational
public import CFSG.LocalAnalysis.StandardType.GGLangCorootPair
public import CFSG.LocalAnalysis.StandardType.GGTBJE8LeviEnnComp
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitTwE6SplitFrame

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.RankThree.Chevalley CFSG.LocalAnalysis.ComponentInitial

open Matrix
open scoped MatrixGroups commutatorElement

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] noncomputable def twE6SplitWeyl
    (L : Type) [Field L] (β : Fin TwistTag.E6.tag.rank → ℤ) : ModGL TwistTag.E6.tag L :=
  if permLattice TwistTag.E6.perm β = β then rootSL2 TwistTag.E6.tag L β WSL
  else rootSL2 TwistTag.E6.tag L β WSL *
    rootSL2 TwistTag.E6.tag L (permLattice TwistTag.E6.perm β) WSL

private def tw_orbIdx : Fin TwistTag.E6.tag.rank → Fin Tag.F4.rank := ![0, 3, 1, 2, 1, 0]

private def tw_foldMatrix : Matrix (Fin TwistTag.E6.tag.rank) (Fin Tag.F4.rank) ℤ :=
  fun i a => if a = tw_orbIdx i then 1 else 0

private theorem tw_orbIdx_eq (i : Fin TwistTag.E6.tag.rank) :
    (show Fin Tag.F4.rank from TwistTag.E6.orbitIndex i) = tw_orbIdx i := by
  fin_cases i <;> rfl

private theorem tw_foldMap_eq_mulVec (u : Fin Tag.F4.rank → ℤ) :
    TwistTag.E6.foldMap (show Fin (TwistTag.E6.foldedTag.rank) → ℤ from u) =
      tw_foldMatrix *ᵥ u := by
  funext i
  rw [TwistTag.foldMap_apply_apply]
  change u (show Fin Tag.F4.rank from TwistTag.E6.orbitIndex i) = (tw_foldMatrix *ᵥ u) i
  rw [tw_orbIdx_eq]
  simp only [tw_foldMatrix, Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single (tw_orbIdx i)]
  · simp
  · intro b _ hb; rw [if_neg hb, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

private theorem tw_symmetrizedCartan_F4_eq (i j : Fin Tag.F4.rank) :
    Tag.F4.symmetrizedCartan i j =
      (tw_foldMatrixᵀ * TwistTag.E6.tag.symmetrizedCartan * tw_foldMatrix) i j := by
  fin_cases i <;> fin_cases j <;> decide +kernel

private theorem tw_iform_foldMap
    (u v : Fin Tag.F4.rank → ℤ) :
    iform u v = iform (tw_foldMatrix *ᵥ u) (tw_foldMatrix *ᵥ v) := by
  rw [← dotProduct_mulVec_eq_iform (τ := Tag.F4) u v,
    ← dotProduct_mulVec_eq_iform (τ := TwistTag.E6.tag) (tw_foldMatrix *ᵥ u)
      (tw_foldMatrix *ᵥ v)]
  have hS : Tag.F4.symmetrizedCartan =
      tw_foldMatrixᵀ * TwistTag.E6.tag.symmetrizedCartan * tw_foldMatrix :=
    Matrix.ext fun i j => tw_symmetrizedCartan_F4_eq i j
  rw [hS, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose]

private theorem tw_iform_self_eq_two_E6
    {γ : Fin TwistTag.E6.tag.rank → ℤ} (hγ : IsRoot TwistTag.E6.tag γ) : iform γ γ = 2 := by
  obtain ⟨j, hj⟩ := iform_self_of_isRoot hγ
  have : TwistTag.E6.tag.symmetrizer j j = 1 := by fin_cases j <;> rfl
  rw [this, mul_one] at hj
  exact hj

private theorem tw_sum_diagramOrbit (β : Fin TwistTag.E6.tag.rank → ℤ) :
    (∑ α ∈ TwistTag.E6.diagramOrbit β, α) =
      if permLattice TwistTag.E6.perm β = β then β
      else β + permLattice TwistTag.E6.perm β := by
  rw [SeitzReduction.diagramOrbit_eq_pair_twistedE6Classes]
  by_cases h : permLattice TwistTag.E6.perm β = β
  · rw [if_pos h, h]; simp
  · rw [if_neg h, Finset.sum_pair (fun hh => h hh.symm)]

private theorem tw_foldMap_rootReflection
    {β : Fin TwistTag.E6.tag.rank → ℤ} (hβ : IsRoot TwistTag.E6.tag β)
    {c : Fin Tag.F4.rank → ℤ} (hc : IsRoot Tag.F4 c)
    (hθ : TwistTag.E6.foldMap (show Fin (TwistTag.E6.foldedTag.rank) → ℤ from c) =
      ∑ α ∈ TwistTag.E6.diagramOrbit β, α) (u : Fin Tag.F4.rank → ℤ) :
    (if permLattice TwistTag.E6.perm β = β then rootReflection β
      else rootReflection β * rootReflection (permLattice TwistTag.E6.perm β)) •
        (tw_foldMatrix *ᵥ u) = tw_foldMatrix *ᵥ (rootReflection c • u) := by
  classical
  have hMfix : permLattice TwistTag.E6.perm (tw_foldMatrix *ᵥ u) = tw_foldMatrix *ᵥ u := by
    rw [← tw_foldMap_eq_mulVec]
    exact TwistTag.foldMap_mem_fixedLattice (t := TwistTag.E6)
      (show Fin (TwistTag.E6.foldedTag.rank) → ℤ from u)
  by_cases hfix : permLattice TwistTag.E6.perm β = β
  · rw [if_pos hfix]
    have hθβ : tw_foldMatrix *ᵥ c = β := by
      rw [← tw_foldMap_eq_mulVec]
      exact hθ.trans ((tw_sum_diagramOrbit β).trans (by rw [if_pos hfix]))
    rw [rootReflection_smul hβ, rootReflection_smul hc, Matrix.mulVec_sub, Matrix.mulVec_smul,
      hθβ]
    congr 1
    rw [corootPair, corootPair, tw_iform_foldMap c u, tw_iform_foldMap c c, hθβ]
  · rw [if_neg hfix]
    have hne : β ≠ permLattice TwistTag.E6.perm β := fun h => hfix h.symm
    have hθf : tw_foldMatrix *ᵥ c = β + permLattice TwistTag.E6.perm β := by
      rw [← tw_foldMap_eq_mulVec]
      exact hθ.trans ((tw_sum_diagramOrbit β).trans (by rw [if_neg hfix]))
    have hρβr : IsRoot TwistTag.E6.tag (permLattice TwistTag.E6.perm β) :=
      hβ.permLattice (TwistTag.cartan_perm TwistTag.E6)
    have h0 : iform β (permLattice TwistTag.E6.perm β) = 0 :=
      SeitzReduction.TwistedE6Pilot.iform_permLattice_eq_zero hβ hfix
    have hB : ∀ i j, Tag.E6.symmetrizedCartan (TwistTag.E6.perm i)
        (TwistTag.E6.perm j) = Tag.E6.symmetrizedCartan i j := by
      intro i j
      have h : Tag.E6.symmetrizedCartan = Tag.E6.cartan := by
        rw [Tag.symmetrizedCartan]; exact Matrix.one_mul _
      rw [h]; exact TwistTag.cartan_perm TwistTag.E6 i j
    have hk : iform (permLattice TwistTag.E6.perm β) (tw_foldMatrix *ᵥ u) =
        iform β (tw_foldMatrix *ᵥ u) := by
      have h1 := ToralSign.iform_permLattice hB β (tw_foldMatrix *ᵥ u)
      rwa [hMfix] at h1
    have hcorβ : corootPair β (tw_foldMatrix *ᵥ u) = iform β (tw_foldMatrix *ᵥ u) := by
      rw [corootPair, tw_iform_self_eq_two_E6 hβ]; omega
    have hcorρ : corootPair (permLattice TwistTag.E6.perm β) (tw_foldMatrix *ᵥ u) =
        iform β (tw_foldMatrix *ᵥ u) := by
      rw [corootPair, tw_iform_self_eq_two_E6 hρβr, hk]; omega
    have hcorc : corootPair c u = iform β (tw_foldMatrix *ᵥ u) := by
      rw [corootPair, tw_iform_foldMap c u, tw_iform_foldMap c c, hθf]
      have h1 : iform (β + permLattice TwistTag.E6.perm β) (tw_foldMatrix *ᵥ u) =
          2 * iform β (tw_foldMatrix *ᵥ u) := by
        rw [iform_add_left, hk, two_mul]
      have h2 : iform (β + permLattice TwistTag.E6.perm β)
          (β + permLattice TwistTag.E6.perm β) = 4 := by
        have h0' : iform (permLattice TwistTag.E6.perm β) β = 0 := by
          rw [iform_comm]; exact h0
        rw [iform_add_left, iform_add_right, iform_add_right, h0, h0',
          tw_iform_self_eq_two_E6 hβ, tw_iform_self_eq_two_E6 hρβr]
        ring
      rw [h1, h2]; omega
    rw [mul_smul, rootReflection_smul hρβr, hcorρ, smul_sub, rootReflection_smul hβ, hcorβ,
      smul_comm, rootReflection_smul_of_iform_eq_zero hβ h0, rootReflection_smul hc,
      Matrix.mulVec_sub, Matrix.mulVec_smul, hθf, hcorc, smul_add]
    abel

private theorem tw_redMod_foldMap_congr {p : ℕ} {u v : Fin Tag.F4.rank → ℤ}
    (h : TableBExc.redMod Tag.F4 p u = TableBExc.redMod Tag.F4 p v) :
    TableBExc.redMod TwistTag.E6.tag p (tw_foldMatrix *ᵥ u) =
      TableBExc.redMod TwistTag.E6.tag p (tw_foldMatrix *ᵥ v) := by
  have hcoord : ∀ (w : Fin Tag.F4.rank → ℤ) (i : Fin TwistTag.E6.tag.rank),
      (tw_foldMatrix *ᵥ w) i = w (tw_orbIdx i) := by
    intro w i
    simp only [tw_foldMatrix, Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single (tw_orbIdx i)]
    · simp
    · intro b _ hb; rw [if_neg hb, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  funext i
  simp only [TableBExc.redMod]
  rw [hcoord u i, hcoord v i]
  exact congrFun h (tw_orbIdx i)

private theorem tw_torusAct_splitTheta
    {p : ℕ} [NeZero p] {β : Fin TwistTag.E6.tag.rank → ℤ} (hβ : IsRoot TwistTag.E6.tag β)
    {c : Fin Tag.F4.rank → ℤ} (hc : IsRoot Tag.F4 c)
    (hθ : TwistTag.E6.foldMap (show Fin (TwistTag.E6.foldedTag.rank) → ℤ from c) =
      ∑ α ∈ TwistTag.E6.diagramOrbit β, α) (s : Fin Tag.F4.rank → ZMod p) :
    TableBExc.torusAct TwistTag.E6.tag p
        (if permLattice TwistTag.E6.perm β = β then rootReflection β
         else rootReflection β * rootReflection (permLattice TwistTag.E6.perm β))
        (ExcFrames.twE6SplitTheta p s) =
      ExcFrames.twE6SplitTheta p (TableBExc.torusAct Tag.F4 p (rootReflection c) s) := by
  classical
  set u : Fin Tag.F4.rank → ℤ := TableBExc.liftMod Tag.F4 p s with hu
  set w : WeylGroup TwistTag.E6.tag :=
    (if permLattice TwistTag.E6.perm β = β then rootReflection β
     else rootReflection β * rootReflection (permLattice TwistTag.E6.perm β)) with hw
  set X : Fin TwistTag.E6.tag.rank → ℤ := tw_foldMatrix *ᵥ u with hX
  have hcong : TableBExc.redMod TwistTag.E6.tag p
      (TableBExc.liftMod TwistTag.E6.tag p (ExcFrames.twE6SplitTheta p s)) =
      TableBExc.redMod TwistTag.E6.tag p X := by
    rw [TableBExc.redMod_liftMod, hX, hu]
    change TableBExc.redMod TwistTag.E6.tag p
        (TwistTag.E6.foldMap (show Fin (TwistTag.E6.foldedTag.rank) → ℤ from
          TableBExc.liftMod Tag.F4 p s)) =
      TableBExc.redMod TwistTag.E6.tag p (tw_foldMatrix *ᵥ TableBExc.liftMod Tag.F4 p s)
    rw [tw_foldMap_eq_mulVec]
  have h1 : TableBExc.torusAct TwistTag.E6.tag p w (ExcFrames.twE6SplitTheta p s) =
      TableBExc.redMod TwistTag.E6.tag p (w • X) :=
    TableBExc.redMod_smul_eq w hcong
  have h2 : w • X = tw_foldMatrix *ᵥ (rootReflection c • u) := by
    rw [hw, hX]; exact tw_foldMap_rootReflection hβ hc hθ u
  have h4 : TableBExc.redMod TwistTag.E6.tag p (tw_foldMatrix *ᵥ (rootReflection c • u)) =
      ExcFrames.twE6SplitTheta p (TableBExc.redMod Tag.F4 p (rootReflection c • u)) := by
    change TableBExc.redMod TwistTag.E6.tag p (tw_foldMatrix *ᵥ (rootReflection c • u)) =
      TableBExc.redMod TwistTag.E6.tag p
        (TwistTag.E6.foldMap (show Fin (TwistTag.E6.foldedTag.rank) → ℤ from
          TableBExc.liftMod Tag.F4 p (TableBExc.redMod Tag.F4 p (rootReflection c • u))))
    rw [tw_foldMap_eq_mulVec]
    exact tw_redMod_foldMap_congr (p := p) (u := rootReflection c • u)
      (v := TableBExc.liftMod Tag.F4 p (TableBExc.redMod Tag.F4 p (rootReflection c • u)))
      ((TableBExc.redMod_liftMod _).symm)
  rw [h1, h2, h4, hu]
  rfl

private theorem tw_map_fix_le_rationalComponent
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)
    {a : Fin τ.rank → Lˣ} (i : KernelComponent (rootCharHom a))
    {X : Type*} [Group X] (ψ : X →* ModGL τ L)
    (hψS : ∀ y, ψ y ∈ rootSpan τ L (rationalRoots S.ρ (rootCharHom a) i))
    (hψA : ∀ y, ψ y ∈ adjointGroup τ L) (F' : X →* X)
    (hψF : ∀ y, S.D.step (ψ y) = ψ (F' y)) (K : Subgroup X) (hK : ∀ y ∈ K, F' y = y)
    (hKperf : ⁅K, K⁆ = K) :
    ∀ y ∈ K, ψ y ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i := by
  intro y hy
  set P : Subgroup (ModGL τ L) := K.map ψ with hP
  have hPmodel : P ≤ S.D.model := by
    rintro _ ⟨u, hu, rfl⟩
    refine ⟨hψA u, ?_⟩
    change S.D.step (ψ u) = ψ u
    rw [hψF, hK u hu]
  have hPspan : P ≤ rootSpan τ L (rationalRoots S.ρ (rootCharHom a) i) := by
    rintro _ ⟨u, -, rfl⟩
    exact hψS u
  have hPperf : ⁅P, P⁆ = P := by
    rw [hP, ← Subgroup.map_commutator, hKperf]
  have hPΓ : P ≤ S.Γ := by
    rw [← hPperf]
    exact Subgroup.commutator_mono hPmodel hPmodel
  have hPrat : P ≤ rationalSpan S.ρ S.Γ (rootCharHom a) i :=
    fun g hg => ⟨hPspan hg, hPΓ hg⟩
  have hcomm : ⁅P, P⁆ ≤ rationalComponent S.ρ S.Γ (rootCharHom a) i :=
    Subgroup.commutator_mono hPrat hPrat
  rw [hPperf] at hcomm
  exact hcomm ⟨y, hy, rfl⟩

private theorem tw_step_rootSL2_of_charTwo
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ}
    (S : LangSetup τ L p₀) {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) (Fr : L →+* L)
    (hFr : ∀ c, Fr c = c ^ S.D.q) (X : SL(2, L)) :
    S.D.step (rootSL2 τ L α X) =
      rootSL2 τ L (S.ρ α) (Matrix.SpecialLinearGroup.map Fr X) := by
  have h : S.D.step.comp (rootSL2 τ L α) =
      (rootSL2 τ L (S.ρ α)).comp (Matrix.SpecialLinearGroup.map Fr) :=
    MonoidHom.eq_of_eqOn_dense sl2_closure_upper_lower fun g hg => by
      rcases hg with ⟨c, rfl⟩ | ⟨c, rfl⟩
      · change S.D.step (rootSL2 τ L α (uSL c)) =
          rootSL2 τ L (S.ρ α) (Matrix.SpecialLinearGroup.map Fr (uSL c))
        rw [rootSL2_uSL_of_charTwo hα, LangRat.step_pinnedX_of_charTwo S hα, map_uSL,
          rootSL2_uSL_of_charTwo ((S.frob.isRoot_iff α).2 hα), hFr]
      · change S.D.step (rootSL2 τ L α (vSL c)) =
          rootSL2 τ L (S.ρ α) (Matrix.SpecialLinearGroup.map Fr (vSL c))
        rw [rootSL2_vSL_of_charTwo hα, LangRat.step_pinnedX_of_charTwo S (IsRoot.neg hα),
          S.frob.neg_eq, map_vSL, rootSL2_vSL_of_charTwo ((S.frob.isRoot_iff α).2 hα), hFr]
  exact DFunLike.congr_fun h X

theorem twE6SplitWeyl_conj_frameDiag
    {L : Type} [Field L] {p : ℕ} [Fact p.Prime] [NeZero p] {ζ : Lˣ} (hζ : ζ ^ p = 1)
    {β : Fin TwistTag.E6.tag.rank → ℤ} (hβ : IsRoot TwistTag.E6.tag β)
    {c : Fin Tag.F4.rank → ℤ} (hc : IsRoot Tag.F4 c)
    (hθ : TwistTag.E6.foldMap c = ∑ α ∈ TwistTag.E6.diagramOrbit β, α)
    (s : Fin Tag.F4.rank → ZMod p) :
    twE6SplitWeyl L β * ExcFrames.frameDiag ζ hζ (ExcFrames.twE6SplitTheta p s) *
        (twE6SplitWeyl L β)⁻¹ =
      ExcFrames.frameDiag ζ hζ
        (ExcFrames.twE6SplitTheta p (TableBExc.torusAct .F4 p (rootReflection c) s)) := by
  have hρβr : IsRoot TwistTag.E6.tag (permLattice TwistTag.E6.perm β) :=
    hβ.permLattice (TwistTag.cartan_perm TwistTag.E6)
  have hm : twE6SplitWeyl L β ∈ monomialSubgroup TwistTag.E6.tag L := by
    by_cases hfix : permLattice TwistTag.E6.perm β = β
    · rw [twE6SplitWeyl, if_pos hfix]
      exact CFSG.ClassicalInvolution.ModelFacts.Levi.rootSL2_WSL_mem_monomialSubgroup hβ
    · rw [twE6SplitWeyl, if_neg hfix]
      exact mul_mem (CFSG.ClassicalInvolution.ModelFacts.Levi.rootSL2_WSL_mem_monomialSubgroup hβ)
        (CFSG.ClassicalInvolution.ModelFacts.Levi.rootSL2_WSL_mem_monomialSubgroup hρβr)
  have hmw : MapsRootLines (twE6SplitWeyl L β)
      (if permLattice TwistTag.E6.perm β = β then rootReflection β
       else rootReflection β * rootReflection (permLattice TwistTag.E6.perm β)) := by
    by_cases hfix : permLattice TwistTag.E6.perm β = β
    · rw [twE6SplitWeyl, if_pos hfix, if_pos hfix]
      exact CFSG.ClassicalInvolution.ModelFacts.Levi.mapsRootLines_rootSL2_WSL hβ
    · rw [twE6SplitWeyl, if_neg hfix, if_neg hfix]
      exact (CFSG.ClassicalInvolution.ModelFacts.Levi.mapsRootLines_rootSL2_WSL hβ).mul
        (CFSG.ClassicalInvolution.ModelFacts.Levi.mapsRootLines_rootSL2_WSL hρβr)
  rw [CFSG.StandardType.monomial_conj_frameDiag_gen hζ hm hmw]
  congr 1
  exact tw_torusAct_splitTheta hβ hc hθ s

theorem twE6SplitWeyl_mem_rationalComponent
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ}
    (S : LangSetup TwistTag.E6.tag L p₀)
    {k' : Type} [Field k'] [Finite k'] [Algebra k' L] [IsAlgClosure k' L]
    {n : ℕ} (hn : 2 ≤ n) (hq : S.D.q = 2 ^ n)
    (hρ : ∀ γ, IsRoot TwistTag.E6.tag γ → S.ρ γ = permLattice TwistTag.E6.perm γ)
    {a : Fin TwistTag.E6.tag.rank → Lˣ} (i : KernelComponent (rootCharHom a))
    {β : Fin TwistTag.E6.tag.rank → ℤ} (hβ : β ∈ rationalRoots S.ρ (rootCharHom a) i) :
    twE6SplitWeyl L β ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i := by
  classical
  have hβr : IsRoot TwistTag.E6.tag β := LangRat.isRoot_of_mem_rationalRoots S i hβ
  have h4n : 4 ≤ 2 ^ n :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  by_cases hfix : permLattice TwistTag.E6.perm β = β
  · rw [show twE6SplitWeyl L β = rootSL2 TwistTag.E6.tag L β WSL from by
      rw [twE6SplitWeyl, if_pos hfix]]
    let Fr : L →+* L := iterateFrobenius L 2 n
    have hFr : ∀ c, Fr c = c ^ S.D.q := fun c => by
      rw [hq]
      show iterateFrobenius L 2 n c = c ^ 2 ^ n
      rw [iterateFrobenius_def]
    let F' : SL(2, L) →* SL(2, L) :=
      (CFSG.RankThree.Classical2.conjSLn (1 : GL (Fin 2) L)).comp
        (Matrix.SpecialLinearGroup.map Fr)
    let X := F'.eqLocus (MonoidHom.id _)
    have hconjF : ∀ z : SL(2, L), F' z = Matrix.SpecialLinearGroup.map Fr z := fun z => by
      change CFSG.RankThree.Classical2.conjSLn (1 : GL (Fin 2) L)
        (Matrix.SpecialLinearGroup.map Fr z) = Matrix.SpecialLinearGroup.map Fr z
      rw [CFSG.RankThree.Classical2.conjSLn_one]
    obtain ⟨-, hQ⟩ := CFSG.RankThree.Classical2.isQuasisimple_eqLocus_conjSLn_frobenius_split
      (k' := k') (Ω := L) (ℓ := 2) (f := n) (n := 2) Nat.prime_two (by omega) le_rfl
      (Or.inr h4n) Fr (fun c => by rw [hFr, hq]) (1 : GL (Fin 2) L)
    let ψ : X →* ModGL TwistTag.E6.tag L := (rootSL2 TwistTag.E6.tag L β).comp X.subtype
    have hmapfix : ∀ y : X, Matrix.SpecialLinearGroup.map Fr (y : SL(2, L)) = (y : SL(2, L)) := by
      intro y
      have hy := y.2
      change F' (y : SL(2, L)) = (y : SL(2, L)) at hy
      rwa [hconjF] at hy
    have hψS : ∀ y, ψ y ∈ rootSpan TwistTag.E6.tag L (rationalRoots S.ρ (rootCharHom a) i) :=
      fun y => LangRat.rootSL2_mem_rootSpan_of_mem_rationalRoots S i hβ _
    have hψA : ∀ y, ψ y ∈ adjointGroup TwistTag.E6.tag L :=
      fun y => rootSpan_le_adjointGroup L _ (hψS y)
    have hψF : ∀ y, S.D.step (ψ y) = ψ ((MonoidHom.id X) y) := by
      intro y
      change S.D.step (rootSL2 TwistTag.E6.tag L β (y : SL(2, L))) =
        rootSL2 TwistTag.E6.tag L β (y : SL(2, L))
      rw [tw_step_rootSL2_of_charTwo S hβr Fr hFr (y : SL(2, L)),
        show S.ρ β = β from (hρ β hβr).trans hfix]
      congr 1
      exact hmapfix y
    haveI hperf : Group.IsPerfect X := hQ.1
    have hKperf : ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ = ⊤ := by
      rw [← commutator_def]
      exact Group.IsPerfect.commutator_eq_top
    have hres := tw_map_fix_le_rationalComponent S i ψ hψS hψA (MonoidHom.id X) hψF ⊤
      (fun _ _ => rfl) hKperf
    have hWfix : Matrix.SpecialLinearGroup.map Fr WSL = WSL := by
      ext i j
      rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
        coe_WSL]
      fin_cases i <;> fin_cases j <;> simp
    have hWX : (WSL : SL(2, L)) ∈ X := by
      change F' WSL = WSL
      rw [hconjF, hWfix]
    exact hres ⟨WSL, hWX⟩ (Subgroup.mem_top _)
  · rw [show twE6SplitWeyl L β = rootSL2 TwistTag.E6.tag L β WSL *
        rootSL2 TwistTag.E6.tag L (permLattice TwistTag.E6.perm β) WSL from by
      rw [twE6SplitWeyl, if_neg hfix]]
    have hρβr : IsRoot TwistTag.E6.tag (permLattice TwistTag.E6.perm β) :=
      hβr.permLattice (TwistTag.cartan_perm TwistTag.E6)
    obtain ⟨hρρ, h0, hsum, hdiff⟩ := LangRat.rho_orthogonal_of_latPerm_ne S
      (Or.inr (Or.inl rfl)) TwistTag.E6.perm (TwistTag.cartan_perm TwistTag.E6) (Or.inl rfl)
      (fun γ hγ => by rw [one_smul]; exact hρ γ hγ) hβr hfix
    have hcomm : ∀ Y Z : SL(2, L),
        Commute (rootSL2 TwistTag.E6.tag L β Y)
          (rootSL2 TwistTag.E6.tag L (S.ρ β) Z) := fun Y Z =>
      exceptional_Lang_strongly_orthogonal_root_rank_one_commutation TwistTag.E6.tag L hβr
        ((S.frob.isRoot_iff β).2 hβr) h0 hsum hdiff _
        (MonoidHom.mem_range.2 ⟨Y, rfl⟩) _ (MonoidHom.mem_range.2 ⟨Z, rfl⟩)
    obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : SL(2, L) × SL(2, L) →* ModGL TwistTag.E6.tag L,
        ∀ Y Z, Ψ (Y, Z) = rootSL2 TwistTag.E6.tag L β Y *
          rootSL2 TwistTag.E6.tag L (S.ρ β) Z :=
      ⟨MonoidHom.noncommCoprod (rootSL2 TwistTag.E6.tag L β)
        (rootSL2 TwistTag.E6.tag L (S.ρ β)) hcomm, fun Y Z => rfl⟩
    let Fr : L →+* L := iterateFrobenius L 2 n
    have hFr : ∀ c, Fr c = c ^ S.D.q := fun c => by
      rw [hq]
      show iterateFrobenius L 2 n c = c ^ 2 ^ n
      rw [iterateFrobenius_def]
    let Fr2 : L →+* L := Fr.comp Fr
    have hFr2 : ∀ c, Fr2 c = c ^ (2 : ℕ) ^ (2 * n) := by
      intro c
      change Fr (Fr c) = c ^ 2 ^ (2 * n)
      rw [hFr, hFr, hq]
      show (c ^ 2 ^ n) ^ 2 ^ n = c ^ 2 ^ (2 * n)
      rw [← pow_mul, show 2 * n = n + n by ring, pow_add]
    let F' : SL(2, L) →* SL(2, L) :=
      (CFSG.RankThree.Classical2.conjSLn (1 : GL (Fin 2) L)).comp
        (Matrix.SpecialLinearGroup.map Fr2)
    let X := F'.eqLocus (MonoidHom.id _)
    have hconjF : ∀ z : SL(2, L), F' z = Matrix.SpecialLinearGroup.map Fr2 z := fun z => by
      change CFSG.RankThree.Classical2.conjSLn (1 : GL (Fin 2) L)
        (Matrix.SpecialLinearGroup.map Fr2 z) = Matrix.SpecialLinearGroup.map Fr2 z
      rw [CFSG.RankThree.Classical2.conjSLn_one]
    have h42n : 4 ≤ 2 ^ (2 * n) :=
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
    obtain ⟨-, hQ⟩ := CFSG.RankThree.Classical2.isQuasisimple_eqLocus_conjSLn_frobenius_split
      (k' := k') (Ω := L) (ℓ := 2) (f := 2 * n) (n := 2) Nat.prime_two (by omega) le_rfl
      (Or.inr h42n) Fr2 hFr2 (1 : GL (Fin 2) L)
    let ψ : X →* ModGL TwistTag.E6.tag L := Ψ.comp
      ((X.subtype).prod ((Matrix.SpecialLinearGroup.map Fr).comp X.subtype))
    have hψapply : ∀ y : X, ψ y = rootSL2 TwistTag.E6.tag L β (y : SL(2, L)) *
        rootSL2 TwistTag.E6.tag L (S.ρ β)
          (Matrix.SpecialLinearGroup.map Fr (y : SL(2, L))) := fun y => by
      change Ψ ((y : SL(2, L)), Matrix.SpecialLinearGroup.map Fr (y : SL(2, L))) = _
      rw [hΨ]
    have hmapfix2 : ∀ y : X,
        Matrix.SpecialLinearGroup.map Fr2 (y : SL(2, L)) = (y : SL(2, L)) := by
      intro y
      have hy := y.2
      change F' (y : SL(2, L)) = (y : SL(2, L)) at hy
      rwa [hconjF] at hy
    have hmapFrFr : ∀ y : SL(2, L), Matrix.SpecialLinearGroup.map Fr2 y =
        Matrix.SpecialLinearGroup.map Fr (Matrix.SpecialLinearGroup.map Fr y) := by
      intro y
      ext i j
      rfl
    have hmapfixFr : ∀ y : X,
        Matrix.SpecialLinearGroup.map Fr (Matrix.SpecialLinearGroup.map Fr (y : SL(2, L))) =
          (y : SL(2, L)) := fun y => (hmapFrFr (y : SL(2, L))).symm.trans (hmapfix2 y)
    have hψS : ∀ y, ψ y ∈ rootSpan TwistTag.E6.tag L (rationalRoots S.ρ (rootCharHom a) i) := by
      intro y
      rw [hψapply]
      exact mul_mem (LangRat.rootSL2_mem_rootSpan_of_mem_rationalRoots S i hβ _)
        (LangRat.rootSL2_mem_rootSpan_of_mem_rationalRoots S i
          (show S.ρ β ∈ rationalRoots S.ρ (rootCharHom a) i from by
            obtain ⟨k, δ, hδ, hk⟩ := hβ
            exact ⟨k + 1, δ, hδ, by rw [hk, Function.iterate_succ_apply']⟩) _)
    have hψA : ∀ y, ψ y ∈ adjointGroup TwistTag.E6.tag L :=
      fun y => rootSpan_le_adjointGroup L _ (hψS y)
    have hψF : ∀ y, S.D.step (ψ y) = ψ ((MonoidHom.id X) y) := by
      intro y
      have h1 : ψ ((MonoidHom.id X) y) = rootSL2 TwistTag.E6.tag L β (y : SL(2, L)) *
          rootSL2 TwistTag.E6.tag L (S.ρ β)
            (Matrix.SpecialLinearGroup.map Fr (y : SL(2, L))) := by
        rw [MonoidHom.id_apply]; exact hψapply y
      rw [hψapply y, h1]
      rw [map_mul, tw_step_rootSL2_of_charTwo S hβr Fr hFr (y : SL(2, L)),
        tw_step_rootSL2_of_charTwo S ((S.frob.isRoot_iff β).2 hβr) Fr hFr
          (Matrix.SpecialLinearGroup.map Fr (y : SL(2, L))), hρρ, hmapfixFr y]
      exact (hcomm (y : SL(2, L)) (Matrix.SpecialLinearGroup.map Fr (y : SL(2, L)))).eq.symm
    haveI hperf : Group.IsPerfect X := hQ.1
    have hKperf : ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ = ⊤ := by
      rw [← commutator_def]
      exact Group.IsPerfect.commutator_eq_top
    have hres := tw_map_fix_le_rationalComponent S i ψ hψS hψA (MonoidHom.id X) hψF ⊤
      (fun _ _ => rfl) hKperf
    have hWfix : Matrix.SpecialLinearGroup.map Fr WSL = WSL := by
      ext i j
      rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
        coe_WSL]
      fin_cases i <;> fin_cases j <;> simp
    have hWX : (WSL : SL(2, L)) ∈ X := by
      change F' WSL = WSL
      rw [hconjF, hmapFrFr, hWfix, hWfix]
    have hmem := hres ⟨WSL, hWX⟩ (Subgroup.mem_top _)
    rw [hψapply, hWfix,
      show S.ρ β = permLattice TwistTag.E6.perm β from hρ β hβr] at hmem
    exact hmem

end CFSG.StandardType

end
