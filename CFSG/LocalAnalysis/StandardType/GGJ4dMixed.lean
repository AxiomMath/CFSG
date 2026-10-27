module

public import CFSG.LocalAnalysis.StandardType.GGJ4dMixedComm
public import CFSG.LocalAnalysis.StandardType.GGJ4dMixedComponents
public import CFSG.LocalAnalysis.StandardType.GGJ4dMixedChain
public import CFSG.LocalAnalysis.StandardType.GGJ4dE6Sigma
public import CFSG.LocalAnalysis.StandardType.GGJ4dFixedSpan
public import CFSG.LocalAnalysis.StandardType.GGJ4dComponentWeyl
import all CFSG.LocalAnalysis.StandardType.GGJ4dComponents
public import CFSG.LocalAnalysis.StandardType.GGJ4dKernel24
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenUni

public section

namespace CFSG.StandardType.LangRat

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.StandardType
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsL33d

theorem j4d_rationalRoots_eq_componentRoots
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {a : Fin τ.rank → Lˣ} (i : KernelComponent (rootCharHom a))
    (hstab : ∀ γ ∈ componentRoots (rootCharHom a) i,
      S.ρ γ ∈ componentRoots (rootCharHom a) i) :
    rationalRoots S.ρ (rootCharHom a) i = componentRoots (rootCharHom a) i := by
  ext γ
  constructor
  · rintro ⟨k, δ, hδ, rfl⟩
    induction k with
    | zero => exact hδ
    | succ k ih =>
        rw [Function.iterate_succ_apply']
        exact hstab _ ih
  · intro hγ
    exact ⟨0, γ, hγ, rfl⟩

private theorem e6Graph_latPerm_sq (x : Fin Tag.E6.rank → ℤ) :
    latPerm e6Graph (latPerm e6Graph x) = x := by
  ext i
  simp only [latPerm, Function.comp_apply]
  have h : ∀ j, e6Graph.symm (e6Graph.symm j) = j := by
    intro j
    fin_cases j <;> decide
  rw [h]

private theorem permLattice_eq_latPerm {τ : Tag} (π : Equiv.Perm (Fin τ.rank))
    (v : Fin τ.rank → ℤ) : permLattice π v = latPerm π v := rfl

private theorem j4d_rho_rho_apply
    {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup Tag.E6 L p₀)
    (hρ : ∀ γ, IsRoot Tag.E6 γ → S.ρ γ = -latPerm e6Graph γ)
    {x : Fin Tag.E6.rank → ℤ} (hx : IsRoot Tag.E6 x) :
    S.ρ (S.ρ x) = x := by
  have hxρ : IsRoot Tag.E6 (S.ρ x) := (S.frob.isRoot_iff x).2 hx
  rw [hρ (S.ρ x) hxρ, hρ x hx]
  have hlin : latPerm e6Graph (-latPerm e6Graph x) =
      -latPerm e6Graph (latPerm e6Graph x) := by
    ext i; simp [latPerm]
  rw [hlin, neg_neg, e6Graph_latPerm_sq]

theorem j4d_mixed_detects
    {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup Tag.E6 L p₀)
    (hq : S.D.q = 2) (hAlg : S.IsAlgebraic)
    {a b : Fin Tag.E6.rank → Lˣ} (i : KernelComponent (rootCharHom a))
    (hπ : ∀ j k, Tag.E6.cartan (e6Graph j) (e6Graph k) = Tag.E6.cartan j k)
    (hρ : ∀ γ, IsRoot Tag.E6 γ → S.ρ γ = -latPerm e6Graph γ)
    (hnoanti : ∀ γ, IsRoot Tag.E6 γ → latPerm e6Graph γ ≠ -γ)
    (hstab : ∀ γ ∈ componentRoots (rootCharHom a) i,
      S.ρ γ ∈ componentRoots (rootCharHom a) i)
    (hmoved : ∃ δ ∈ componentRoots (rootCharHom a) i, S.ρ δ ≠ -δ)
    (hle : rationalComponent S.ρ S.Γ (rootCharHom a) i ≤
      Subgroup.centralizer {rootDiagUnit Tag.E6 b}) :
    ∀ γ ∈ componentRoots (rootCharHom a) i, rootChar b γ = 1 := by
  classical
  intro γ hγ
  set Ψ := componentRoots (rootCharHom a) i with hΨdef
  have hΨ : IsRootComponent Ψ := isRootComponent_componentRoots i
  have hγr : IsRoot Tag.E6 γ := hΨ.isRoot γ hγ
  by_cases hγstable : S.ρ γ = -γ
  ·
    set F : Set (Fin Tag.E6.rank → ℤ) := {x | x ∈ Ψ ∧ S.ρ x = -x} with hFdef
    have hFγ : γ ∈ F := ⟨hγ, hγstable⟩
    have hρ' : ∀ x, IsRoot Tag.E6 x → S.ρ x = (-1 : ℤ) • latPerm e6Graph x := by
      intro x hx
      rw [hρ x hx, neg_one_smul]
    have hτE6 : SimplyLacedTag Tag.E6 := Or.inr (Or.inl rfl)
    have hFroot : ∀ x ∈ F, IsRoot Tag.E6 x := fun x hx =>
      j4d_stableRoots_isRoot hτE6 S hπ (ε := -1) rfl hρ' hΨ hx.1 hx.2
    have hFneg : ∀ x ∈ F, -x ∈ F := fun x hx =>
      j4d_stableRoots_neg hτE6 S hπ (ε := -1) rfl hρ' hΨ hx.1 hx.2
    have hFadd : ∀ x ∈ F, ∀ y ∈ F, IsRoot Tag.E6 (x + y) → x + y ∈ F :=
      fun x hx y hy hsum =>
        j4d_stableRoots_add hτE6 S hπ (ε := -1) rfl hρ' hΨ hx.1 hx.2 hy.1 hy.2 hsum
    have hFrefl : ∀ x ∈ F, ∀ y ∈ F, rootReflection y • x ∈ F :=
      fun x hx y hy =>
        j4d_stableRoots_reflection hτE6 S hπ (ε := -1) rfl hρ' hΨ hx.1 hx.2 hy.1 hy.2
    have hC : IsRootComponent (FComp F γ) :=
      j4d_fcomp_isRootComponent hFroot hFneg hFadd hFrefl hFγ
    have hCsub : FComp F γ ⊆ Ψ := fun x hx => hx.1.1
    have hCne : (FComp F γ).Nonempty := ⟨γ, hFγ, Relation.ReflTransGen.refl⟩
    obtain ⟨δ, hδΨ, hδmove⟩ := hmoved
    have hδnotF : δ ∉ F := fun h => hδmove h.2
    have hMne : ∃ m, m ∈ Ψ ∧ m ∉ FComp F γ :=
      ⟨δ, hδΨ, fun h => hδnotF h.1⟩
    obtain ⟨f0, hf0C, m, hmΨ, hmnotC, hfm⟩ :=
      j4d_exists_fixed_moved_edge hΨ hCsub hCne hMne
    have hmnotF : m ∉ F := fun hmF =>
      hfm (j4d_fcomp_orthogonal hf0C hmF hmnotC)
    have hmMove : S.ρ m ≠ -m := fun h => hmnotF ⟨hmΨ, h⟩
    obtain ⟨w, hw, hwγ⟩ :=
      exists_componentWeylGroup_smul_eq_of_mem hτE6 hC hf0C
        ⟨hFγ, Relation.ReflTransGen.refl⟩
    have hFstable : ∀ f ∈ FComp F γ, IsRoot Tag.E6 f ∧ S.ρ f = -f :=
      fun f hf => ⟨hFroot f hf.1, hf.1.2⟩
    have hwm : S.ρ (w • m) ≠ -(w • m) :=
      j4d_WF_stable_preserves_moved hτE6 S (ε := -1) rfl hρ' hFstable hw
        (hΨ.isRoot m hmΨ) hmMove
    set δ' : Fin Tag.E6.rank → ℤ := w • m with hδ'def
    have hδ'Ψ : δ' ∈ Ψ := j4d_componentWeyl_maps_mem hΨ hCsub hw hmΨ
    have hδ'r : IsRoot Tag.E6 δ' := hΨ.isRoot δ' hδ'Ψ
    have hδ'notneg : S.ρ δ' ≠ -δ' := hwm
    have hδ'notpos : S.ρ δ' ≠ δ' := by
      intro h
      apply hnoanti δ' hδ'r
      have h3 := hρ δ' hδ'r
      rw [h] at h3
      have h4 : latPerm e6Graph δ' = -δ' := by
        have h5 := congrArg Neg.neg h3
        simpa using h5.symm
      exact h4
    have hγδ' : iform γ δ' ≠ 0 := by
      intro h0
      apply hfm
      have h := iform_smul w f0 m
      rw [hwγ] at h
      rw [← h]
      simpa [hδ'def] using h0
    have hγne : γ ≠ δ' := by
      intro h
      apply hδ'notneg
      rw [← h]
      exact hγstable
    have hγneneg : γ ≠ -δ' := by
      intro h
      apply hδ'notneg
      have hδ'eq : δ' = -γ := by rw [h, neg_neg]
      rw [hδ'eq, S.frob.neg_eq, hγstable, neg_neg]
    have hγγ : iform γ γ = 2 := iform_self_eq_two_of_simplyLaced' hτE6 hγr
    have hσγ : latPerm e6Graph γ = γ := by
      have h3 := hρ γ hγr
      rw [hγstable] at h3
      exact (neg_inj.mp h3).symm
    have hδ'orthσ : iform δ' (latPerm e6Graph δ') = 0 := by
      have hσδ'ne : latPerm e6Graph δ' ≠ δ' := by
        intro h
        apply hδ'notneg
        rw [hρ δ' hδ'r, h]
      have h := j4dE6Sigma_moved_orthogonal hδ'r
        (by rwa [permLattice_eq_latPerm])
      simpa only [permLattice_eq_latPerm] using h
    rcases j4d_string_dichotomy hτE6 hγr hδ'r hγδ' hγne hγneneg with
      ⟨h1, hroot⟩ | ⟨h1, hroot⟩
    ·
      set x : Fin Tag.E6.rank → ℤ := γ - δ' with hxdef
      have hxΨ : x ∈ Ψ := by
        have hroot' : IsRoot Tag.E6 (γ + -δ') := by simpa [hxdef, sub_eq_add_neg] using hroot
        have h := hΨ.add_mem γ hγ (-δ') (hΨ.neg_mem δ' hδ'Ψ) hroot'
        simpa [hxdef, sub_eq_add_neg] using h
      have hxr : IsRoot Tag.E6 x := hroot
      have horthx : iform x (S.ρ x) = 0 := by
        have hxρ : S.ρ x = -latPerm e6Graph x := hρ x hxr
        rw [hxρ]
        have hlin : latPerm e6Graph x =
            latPerm e6Graph γ - latPerm e6Graph δ' := by
          ext i
          simp [hxdef, latPerm, sub_eq_add_neg]
        rw [hlin, hσγ]
        have h0 := j4d_chain_orth_one hτE6 hπ hγγ hσγ hδ'orthσ h1
        have h0' : iform (γ - δ') (-(γ - latPerm e6Graph δ')) = 0 := by
          rw [← neg_one_smul (R := ℤ) (γ - latPerm e6Graph δ'), iform_smul_right, h0,
            mul_zero]
        simpa [hxdef] using h0'
      have hxnotpos : S.ρ x ≠ x := by
        intro h
        have h2 : iform x x = 2 := iform_self_eq_two_of_simplyLaced' hτE6 hxr
        rw [h, h2] at horthx
        norm_num at horthx
      have hxnotneg : S.ρ x ≠ -x := by
        intro h
        have h2 : iform x x = 2 := iform_self_eq_two_of_simplyLaced' hτE6 hxr
        have hneg : iform x (-x) = -2 := by
          rw [← neg_one_smul (R := ℤ) x, iform_smul_right, h2]
          norm_num
        rw [h, hneg] at horthx
        norm_num at horthx
      have hxpair : rootChar b x = 1 :=
        j4dE6Sigma_pair_kills S (Or.inr (Or.inl rfl)) hq hAlg i hle hxΨ (hstab x hxΨ)
          hxr ((S.frob.isRoot_iff x).2 hxr) (j4d_rho_rho_apply S hρ hxr) horthx (Ne.symm hxnotpos)
      have hδ'pair : rootChar b δ' = 1 := by
        have hδ'orthρ : iform δ' (S.ρ δ') = 0 := by
          rw [hρ δ' hδ'r]
          rw [← neg_one_smul (R := ℤ) (latPerm e6Graph δ'), iform_smul_right,
            hδ'orthσ, mul_zero]
        exact j4dE6Sigma_pair_kills S (Or.inr (Or.inl rfl)) hq hAlg i hle hδ'Ψ
          (hstab δ' hδ'Ψ) hδ'r ((S.frob.isRoot_iff δ').2 hδ'r)
          (j4d_rho_rho_apply S hρ hδ'r) hδ'orthρ (Ne.symm hδ'notpos)
      exact j4dE6Sigma_stable_of_pair_pos b hδ'pair (by simpa [hxdef] using hxpair)
    ·
      set x : Fin Tag.E6.rank → ℤ := γ + δ' with hxdef
      have hxΨ : x ∈ Ψ := hΨ.add_mem γ hγ δ' hδ'Ψ hroot
      have hxr : IsRoot Tag.E6 x := hroot
      have horthx : iform x (S.ρ x) = 0 := by
        have hxρ : S.ρ x = -latPerm e6Graph x := hρ x hxr
        rw [hxρ]
        have hlin : latPerm e6Graph x =
            latPerm e6Graph γ + latPerm e6Graph δ' := by
          ext i
          simp [hxdef, latPerm, Pi.add_apply]
        rw [hlin, hσγ]
        have h0 := j4d_chain_orth_negone hτE6 hπ hγγ hσγ hδ'orthσ h1
        have h0' : iform (γ + δ') (-(γ + latPerm e6Graph δ')) = 0 := by
          rw [← neg_one_smul (R := ℤ) (γ + latPerm e6Graph δ'), iform_smul_right, h0,
            mul_zero]
        simpa [hxdef] using h0'
      have hxnotpos : S.ρ x ≠ x := by
        intro h
        have h2 : iform x x = 2 := iform_self_eq_two_of_simplyLaced' hτE6 hxr
        rw [h, h2] at horthx
        norm_num at horthx
      have hxnotneg : S.ρ x ≠ -x := by
        intro h
        have h2 : iform x x = 2 := iform_self_eq_two_of_simplyLaced' hτE6 hxr
        have hneg : iform x (-x) = -2 := by
          rw [← neg_one_smul (R := ℤ) x, iform_smul_right, h2]
          norm_num
        rw [h, hneg] at horthx
        norm_num at horthx
      have hxpair : rootChar b x = 1 :=
        j4dE6Sigma_pair_kills S (Or.inr (Or.inl rfl)) hq hAlg i hle hxΨ (hstab x hxΨ)
          hxr ((S.frob.isRoot_iff x).2 hxr) (j4d_rho_rho_apply S hρ hxr) horthx (Ne.symm hxnotpos)
      have hδ'pair : rootChar b δ' = 1 := by
        have hδ'orthρ : iform δ' (S.ρ δ') = 0 := by
          rw [hρ δ' hδ'r]
          rw [← neg_one_smul (R := ℤ) (latPerm e6Graph δ'), iform_smul_right,
            hδ'orthσ, mul_zero]
        exact j4dE6Sigma_pair_kills S (Or.inr (Or.inl rfl)) hq hAlg i hle hδ'Ψ
          (hstab δ' hδ'Ψ) hδ'r ((S.frob.isRoot_iff δ').2 hδ'r)
          (j4d_rho_rho_apply S hρ hδ'r) hδ'orthρ (Ne.symm hδ'notpos)
      exact j4dE6Sigma_stable_of_pair_neg b hδ'pair (by simpa [hxdef] using hxpair)
  ·
    have hγnotneg : S.ρ γ ≠ -γ := hγstable
    have hγnotpos : S.ρ γ ≠ γ := by
      intro h
      apply hnoanti γ hγr
      have h3 := hρ γ hγr
      rw [h] at h3
      have h4 : latPerm e6Graph γ = -γ := by
        have h5 := congrArg Neg.neg h3
        simpa using h5.symm
      exact h4
    have hγorth : iform γ (S.ρ γ) = 0 := by
      have hσγne : latPerm e6Graph γ ≠ γ := by
        intro h
        exact hγnotneg (by rw [hρ γ hγr, h])
      have h := j4dE6Sigma_moved_orthogonal hγr hσγne
      rw [hρ γ hγr, ← neg_one_smul (R := ℤ) (latPerm e6Graph γ), iform_smul_right]
      have h' : iform γ (latPerm e6Graph γ) = 0 := h
      rw [h', mul_zero]
    exact j4dE6Sigma_pair_kills S (Or.inr (Or.inl rfl)) hq hAlg i hle hγ (hstab γ hγ) hγr
      ((S.frob.isRoot_iff γ).2 hγr) (j4d_rho_rho_apply S hρ hγr) hγorth (Ne.symm hγnotpos)

end CFSG.StandardType.LangRat

end
