module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcE6SplitWeyl
import CFSG.LocalAnalysis.StandardType.GGLangRootSL2Rational
import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterFieldG2
import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigid

public section

namespace CFSG.StandardType.GGQ2Frame.ExcPlacement

open CFSG CFSG.Assembly CFSG.StandardType CFSG.StandardType.LangRat CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.Chevalley CFSG.RankThree.Classical2
  CFSG.HardMathSupport.Timmesfeld.CrossChar

noncomputable section


variable {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} {S : LangSetup .E6 L p}

private theorem conjSLn_WSL_uSL_of_charTwo' {L : Type} [Field L] [CharP L 2] (c : L) :
    CFSG.RankThree.Classical2.conjSLn (Matrix.SpecialLinearGroup.toGL WSL) (uSL c) = vSL c := by
  rw [CFSG.RankThree.Classical2.conjSLn_toGL]
  ext i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, coe_uSL,
    coe_vSL, coe_WSL]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two, CharTwo.neg_eq]

private theorem conjSLn_WSL_vSL_of_charTwo' {L : Type} [Field L] [CharP L 2] (c : L) :
    CFSG.RankThree.Classical2.conjSLn (Matrix.SpecialLinearGroup.toGL WSL) (vSL c) = uSL c := by
  rw [CFSG.RankThree.Classical2.conjSLn_toGL]
  ext i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, coe_uSL,
    coe_vSL, coe_WSL]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two, CharTwo.neg_eq]

private theorem step_rootSL2_pair_of_rho_neg
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {α α' : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hα' : IsRoot τ α') (hρ : S.ρ α = -α')
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ S.D.q) (X : SL2 L) :
    S.D.step (rootSL2 τ L α X) =
      rootSL2 τ L α' (CFSG.RankThree.Classical2.conjSLn (Matrix.SpecialLinearGroup.toGL WSL)
        (Matrix.SpecialLinearGroup.map Fr X)) := by
  have h : S.D.step.comp (rootSL2 τ L α) = (rootSL2 τ L α').comp
      ((CFSG.RankThree.Classical2.conjSLn (Matrix.SpecialLinearGroup.toGL WSL)).comp
        (Matrix.SpecialLinearGroup.map Fr)) :=
    MonoidHom.eq_of_eqOn_dense sl2_closure_upper_lower fun g hg => by
      rcases hg with ⟨c, rfl⟩ | ⟨c, rfl⟩
      · change S.D.step (rootSL2 τ L α (uSL c)) = rootSL2 τ L α'
          (CFSG.RankThree.Classical2.conjSLn (Matrix.SpecialLinearGroup.toGL WSL)
            (Matrix.SpecialLinearGroup.map Fr (uSL c)))
        rw [rootSL2_uSL_of_charTwo hα, step_pinnedX_of_charTwo S hα, hρ, map_uSL,
          conjSLn_WSL_uSL_of_charTwo', rootSL2_vSL_of_charTwo hα', hFr]
      · change S.D.step (rootSL2 τ L α (vSL c)) = rootSL2 τ L α'
          (CFSG.RankThree.Classical2.conjSLn (Matrix.SpecialLinearGroup.toGL WSL)
            (Matrix.SpecialLinearGroup.map Fr (vSL c)))
        rw [rootSL2_vSL_of_charTwo hα, step_pinnedX_of_charTwo S (IsRoot.neg hα),
          S.frob.neg_eq, hρ, neg_neg, map_vSL, conjSLn_WSL_vSL_of_charTwo',
          rootSL2_uSL_of_charTwo hα', hFr]
  exact DFunLike.congr_fun h X

theorem e6SplitWeyl_mem_e6SplitComponent (hS : E6SplitLangTwo S) {c : Finset (ExcRaw.Root 1)}
    {i : ExcRaw.Root 1} (hi : i ∈ c) (hshort : ExcRaw.tabFix1.getD i.val false = false) :
    e6SplitWeyl L i ∈ e6SplitComponent S c := by
  classical
  have hchar : CharP L 2 := charP_two_of_langSetup_q_eq_two_pow (f := 1) S
    (by rw [hS.1, pow_one])
  let γ := e6SplitRoot i
  let β := permLattice (τ := .E6) e6SplitPerm γ
  have hγ : IsRoot .E6 γ := isRoot_e6SplitRoot i
  have hβ : IsRoot .E6 β := isRoot_permLattice_e6SplitRoot i
  have hρ : S.ρ γ = -β := e6SplitRho_eq hS hγ
  have hρ' : S.ρ β = -γ := by
    rw [e6SplitRho_eq hS hβ, permLattice_permLattice_e6SplitRoot]
  have hs := e6SplitShortFacts i hshort
  have hcomm : ∀ X Y : SL2 L, rootSL2 .E6 L γ X * rootSL2 .E6 L β Y =
      rootSL2 .E6 L β Y * rootSL2 .E6 L γ X := by
    intro X Y
    exact exceptional_Lang_strongly_orthogonal_root_rank_one_commutation .E6 L hγ hβ hs.1
      hs.2.1 hs.2.2 _ ⟨X, rfl⟩ _ ⟨Y, rfl⟩
  let ψ : SL2 L × SL2 L →* ModGL .E6 L :=
    MonoidHom.noncommCoprod (rootSL2 .E6 L γ) (rootSL2 .E6 L β) hcomm
  have hψ_apply : ∀ X Y, ψ (X, Y) = rootSL2 .E6 L γ X * rootSL2 .E6 L β Y := fun X Y =>
    MonoidHom.noncommCoprod_apply _ _ _ (X, Y)
  let Fr : L →+* L := frobenius L 2
  have hFr : ∀ c, Fr c = c ^ S.D.q := by
    intro c
    rw [hS.1]
    exact frobenius_def 2 c
  let F' : SL2 L →* SL2 L :=
    (CFSG.RankThree.Classical2.conjSLn (Matrix.SpecialLinearGroup.toGL WSL)).comp
      (Matrix.SpecialLinearGroup.map Fr)
  have hstep : ∀ X Y, S.D.step (ψ (X, Y)) = ψ (F' Y, F' X) := by
    intro X Y
    rw [hψ_apply X Y, map_mul, hψ_apply (F' Y) (F' X)]
    rw [step_rootSL2_pair_of_rho_neg S hγ hβ hρ Fr hFr X,
      step_rootSL2_pair_of_rho_neg S hβ hγ hρ' Fr hFr Y]
    exact (hcomm (F' Y) (F' X)).symm
  let σ₄ : L ≃+* L := (frobeniusEquiv L 2).trans (frobeniusEquiv L 2)
  have hσ₄ : ∀ c, σ₄ c = c ^ 4 := by
    intro c
    change frobenius L 2 (frobenius L 2 c) = c ^ 4
    rw [frobenius_def, frobenius_def]
    ring_nf
  have hperf : Group.IsPerfect (SL2 ↥(fixSubfield σ₄)) :=
    outer_sl2_fix_perfect (r := 2) (n := 2) (by norm_num) (by norm_num) σ₄ hσ₄
  let ι : SL2 ↥(fixSubfield σ₄) →* SL2 L :=
    Matrix.SpecialLinearGroup.map (fixSubfield σ₄).subtype
  let j : SL2 ↥(fixSubfield σ₄) →* SL2 L × SL2 L :=
    { toFun := fun Y => (ι Y, F' (ι Y))
      map_one' := by simp [ι, F']
      map_mul' := by intro x y; simp [ι, F'] }
  let K : Subgroup (SL2 L × SL2 L) := j.range
  have hKperf : ⁅K, K⁆ = K := by
    rw [show K = (⊤ : Subgroup (SL2 ↥(fixSubfield σ₄))).map j from by
      simp [K, MonoidHom.range_eq_map]]
    rw [← Subgroup.map_commutator]
    have htop : ⁅(⊤ : Subgroup (SL2 ↥(fixSubfield σ₄))),
        (⊤ : Subgroup (SL2 ↥(fixSubfield σ₄)))⁆ =
        (⊤ : Subgroup (SL2 ↥(fixSubfield σ₄))) := by
      have : Group.IsPerfect (SL2 ↥(fixSubfield σ₄)) := hperf
      exact Group.IsPerfect.commutator_eq_top
    rw [htop]
  have hF'F' : ∀ X : SL2 L, (∀ i j, X i j ^ 4 = X i j) → F' (F' X) = X := by
    intro X hX
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [F', Fr, frobenius_def,
        CFSG.RankThree.Classical2.conjSLn_toGL,
        coe_WSL, CharTwo.neg_eq,
        Matrix.SpecialLinearGroup.map_apply_coe]
    all_goals ring_nf; exact hX _ _
  have hfix : ∀ c : ↥(fixSubfield σ₄), (c : L) ^ 4 = c := by
    intro c
    rw [← hσ₄ (c : L)]
    exact c.2
  have hιWSL : ι (WSL : SL2 ↥(fixSubfield σ₄)) = (WSL : SL2 L) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ι, Matrix.SpecialLinearGroup.map_apply_coe, coe_WSL]
  have hF'WSL : F' (WSL : SL2 L) = WSL := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [F', CFSG.RankThree.Classical2.conjSLn_toGL,
      coe_WSL, CharTwo.neg_eq]
  have hWSL_mem_K : (WSL, WSL) ∈ K := by
    refine ⟨(WSL : SL2 ↥(fixSubfield σ₄)), ?_⟩
    simp only [j, MonoidHom.coe_mk, OneHom.coe_mk]
    rw [hιWSL, hF'WSL]
  set P : Subgroup (ModGL .E6 L) := K.map ψ with hP
  have hPmodel : P ≤ S.D.model := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨Y, rfl⟩ := hy
    simp only [j, MonoidHom.coe_mk, OneHom.coe_mk]
    refine S.D.mem_model.2 ⟨?_, ?_⟩
    · rw [hψ_apply]
      exact mul_mem (rootSL2_mem_adjointGroup _ _) (rootSL2_mem_adjointGroup _ _)
    · change S.D.step (ψ (ι Y, F' (ι Y))) = ψ (ι Y, F' (ι Y))
      rw [hstep, hF'F' (ι Y) (fun i j => by
        change (Y i j : L) ^ 4 = Y i j
        exact hfix (Y i j))]
  have hPspan : P ≤ rootSpan .E6 L (e6SplitCodeRoots c) := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨Y, rfl⟩ := hy
    simp only [j, MonoidHom.coe_mk, OneHom.coe_mk]
    rw [hψ_apply]
    refine mul_mem ?_ ?_
    · have h1 : rootSL2 .E6 L γ (ι Y) ∈ rootSpan .E6 L {γ, -γ} :=
        CFSG.HardMathSupport.Timmesfeld.CrossChar.rootSL2_mem_rootSpan_pair hγ _
      exact rootSpan_mono (by
        intro x hx
        rcases hx with rfl | rfl
        · exact ⟨i, hi, Or.inl rfl⟩
        · exact ⟨i, hi, Or.inr (Or.inl rfl)⟩) h1
    · have h1 : rootSL2 .E6 L β (F' (ι Y)) ∈ rootSpan .E6 L {β, -β} :=
        CFSG.HardMathSupport.Timmesfeld.CrossChar.rootSL2_mem_rootSpan_pair hβ _
      exact rootSpan_mono (by
        intro x hx
        rcases hx with rfl | rfl
        · exact ⟨i, hi, Or.inr (Or.inr (Or.inl rfl))⟩
        · exact ⟨i, hi, Or.inr (Or.inr (Or.inr rfl))⟩) h1
  have hPperf : ⁅P, P⁆ = P := by
    rw [hP, ← Subgroup.map_commutator, hKperf]
  have hPΓ : P ≤ S.Γ := by
    rw [← hPperf]
    exact Subgroup.commutator_mono hPmodel hPmodel
  have hPcomp : P ≤ e6SplitComponent S c := by
    have hle : P ≤ rootSpan .E6 L (e6SplitCodeRoots c) ⊓ S.Γ :=
      le_inf hPspan hPΓ
    rw [← hPperf]
    exact Subgroup.commutator_mono hle hle
  have hψWSL : ψ (WSL, WSL) = e6SplitWeyl L i := by
    rw [hψ_apply, e6SplitWeyl, if_neg (by rw [hshort]; simp)]
  have : e6SplitWeyl L i ∈ P := by
    rw [← hψWSL]
    exact Subgroup.mem_map.2 ⟨(WSL, WSL), hWSL_mem_K, rfl⟩
  exact hPcomp this

end

end CFSG.StandardType.GGQ2Frame.ExcPlacement

end
