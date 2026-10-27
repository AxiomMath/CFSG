module

public import CFSG.LocalAnalysis.StandardType.GGK0StageDefs
import CFSG.HardMathSupport.Timmesfeld.LangTorus.FrobeniusOnRoots
import CFSG.HardMathSupport.Timmesfeld.LangTorus.ExcRoots
import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.WeylTorusAct
import CFSG.LieType.Chevalley.E6ToralGraphInvolution
import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigidTools
import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerF4Toral
import CFSG.LieType.Chevalley.ToralCentralizerBruhat
import CFSG.RankThree.PartOne.KE.A1Action
import CFSG.RankThree.PartOne.KE.A1Levi
import CFSG.RankThree.PartOne.KE.A1TwistedE6
import CFSG.RankThree.PartOne.KE.SigmaPerX
import CFSG.RankThree.PartOne.KGD.D4Frame
import CFSG.RankThree.PartOne.KGD.D4Twist

public section

namespace CFSG.StandardType.GGK0MarkedKacIface1587

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley
open CFSG.LieType.AlgebraicGroups
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
  {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}

omit [IsAlgClosed Omega] in
private theorem k0Units_eq_one_of_pow_two_pow (x : Omegaˣ) (n : ℕ)
    (h : x ^ (2 ^ n) = 1) : x = 1 := by
  have h' : ((x : Omega) - 1) ^ (2 ^ n) = 0 := by
    rw [sub_pow_char_pow, one_pow, ← Units.val_pow_eq_pow_val, h, Units.val_one, sub_self]
  have hne : 2 ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  exact Units.ext (sub_eq_zero.1 ((pow_eq_zero_iff hne).1 h'))

private noncomputable def k0Saturated (A : K0LangMark Omega lab p R I phi) :
    Submodule ℤ (Fin A.tau.rank → ℤ) where
  carrier := {v | ∃ m : ℕ, 0 < m ∧
    (m : ℤ) • v ∈ Submodule.span ℤ (kernelRoots (rootCharHom A.a))}
  zero_mem' := ⟨1, one_pos, by simp⟩
  add_mem' := by
    rintro v w ⟨m, hm, hvm⟩ ⟨n, hn, hwn⟩
    refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
    have heq : ((m * n : ℕ) : ℤ) • (v + w) =
        (n : ℤ) • ((m : ℤ) • v) + (m : ℤ) • ((n : ℤ) • w) := by
      ext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      push_cast
      ring
    rw [heq]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ hvm) (Submodule.smul_mem _ _ hwn)
  smul_mem' := by
    rintro c v ⟨m, hm, hvm⟩
    refine ⟨m, hm, ?_⟩
    rw [smul_smul, mul_comm, ← smul_smul]
    exact Submodule.smul_mem _ _ hvm

omit [CharP Omega 2] in
private theorem k0Saturated_mem (A : K0LangMark Omega lab p R I phi) (v : Fin A.tau.rank → ℤ) :
    v ∈ k0Saturated A ↔ ∃ m : ℕ, 0 < m ∧
      (m : ℤ) • v ∈ Submodule.span ℤ (kernelRoots (rootCharHom A.a)) :=
  Iff.rfl

private theorem k0Saturated_map_span (A : K0LangMark Omega lab p R I phi) :
    (Submodule.span ℤ (kernelRoots (rootCharHom A.a))).map A.frobLinear.toLinearMap =
      Submodule.span ℤ (kernelRoots (rootCharHom A.a)) := by
  classical
  set K : Set (Fin A.tau.rank → ℤ) := kernelRoots (rootCharHom A.a) with hKdef
  have hKroot : ∀ v ∈ K, IsRoot A.tau v ∧ rootChar A.a v = 1 := by
    intro v hv
    rwa [hKdef, kernelRoots_rootCharHom] at hv
  have hfwd : A.frobLinear '' K ⊆ K := by
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨hroot, hchar⟩ := hKroot v hv
    rw [hKdef, kernelRoots_rootCharHom, A.frob_roots v hroot]
    exact ⟨(A.setup.frob.isRoot_iff v).2 hroot,
      by rw [A.setup.frob.rootChar_eq A.a A.a_torus v hroot, hchar, one_pow]⟩
  have hbwd : K ⊆ A.frobLinear '' K := by
    intro v hv
    obtain ⟨hroot, hchar⟩ := hKroot v hv
    have hroot' : IsRoot A.tau (A.setup.ρ.symm v) :=
      (A.setup.frob.isRoot_iff (A.setup.ρ.symm v)).1 (by simpa using hroot)
    refine ⟨A.setup.ρ.symm v, ?_, ?_⟩
    · rw [hKdef, kernelRoots_rootCharHom]
      refine ⟨hroot', ?_⟩
      have h := A.setup.frob.rootChar_eq A.a A.a_torus (A.setup.ρ.symm v) hroot'
      simp only [Equiv.apply_symm_apply] at h
      have hq : rootChar A.a (A.setup.ρ.symm v) ^ (2 ^ lab.n) = 1 := by
        rw [← A.q_eq, ← h, hchar]
      exact k0Units_eq_one_of_pow_two_pow _ lab.n hq
    · rw [A.frob_roots _ hroot', Equiv.apply_symm_apply]
  have hmap : (Submodule.span ℤ K).map A.frobLinear.toLinearMap = Submodule.span ℤ K := by
    refine le_antisymm ?_ ?_
    · rw [Submodule.map_span (f := A.frobLinear.toLinearMap)]
      exact Submodule.span_le.2 (hfwd.trans Submodule.subset_span)
    · rw [Submodule.map_span (f := A.frobLinear.toLinearMap)]
      exact Submodule.span_le.2 (hbwd.trans Submodule.subset_span)
  simpa [hKdef] using hmap

private theorem k0Saturated_frob (A : K0LangMark Omega lab p R I phi) :
    ∀ v : Fin A.tau.rank → ℤ, v ∈ k0Saturated A ↔ A.frobLinear v ∈ k0Saturated A := by
  have hmap := k0Saturated_map_span A
  intro v
  constructor
  · rintro ⟨m, hm, hvm⟩
    refine ⟨m, hm, ?_⟩
    have h2 : A.frobLinear ((m : ℤ) • v) ∈
        (Submodule.span ℤ (kernelRoots (rootCharHom A.a))).map A.frobLinear.toLinearMap :=
      Submodule.mem_map.2 ⟨_, hvm, rfl⟩
    rw [hmap] at h2
    rwa [LinearEquiv.map_smul] at h2
  · rintro ⟨m, hm, hvm⟩
    refine ⟨m, hm, ?_⟩
    have hvm' : A.frobLinear ((m : ℤ) • v) ∈
        (Submodule.span ℤ (kernelRoots (rootCharHom A.a))).map A.frobLinear.toLinearMap := by
      rw [LinearEquiv.map_smul, hmap]
      exact hvm
    obtain ⟨w, hw, hwv⟩ := Submodule.mem_map.1 hvm'
    have : w = (m : ℤ) • v := A.frobLinear.injective hwv
    rwa [this] at hw

private theorem k0RootChar_mul {τ : Tag} {K : Type} [Field K]
    (a b : Fin τ.rank → Kˣ) (v : Fin τ.rank → ℤ) :
    rootChar (a * b) v = rootChar a v * rootChar b v := by
  simp only [rootChar, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]

private theorem k0RootChar_inv {τ : Tag} {K : Type} [Field K]
    (a : Fin τ.rank → Kˣ) (v : Fin τ.rank → ℤ) :
    rootChar a⁻¹ v = (rootChar a v)⁻¹ := by
  simp only [rootChar, Pi.inv_apply, inv_zpow, Finset.prod_inv_distrib]

private theorem k0RootChar_one {τ : Tag} {K : Type} [Field K] (v : Fin τ.rank → ℤ) :
    rootChar (1 : Fin τ.rank → Kˣ) v = 1 := by
  simp [rootChar]

private noncomputable def k0CentralTorus (A : K0LangMark Omega lab p R I phi) :
    Subgroup (ModGL A.tau Omega) where
  carrier := {g | ∃ b : Fin A.tau.rank → Omegaˣ, rootDiagUnit A.tau b = g ∧
    ∀ v ∈ k0Saturated A, rootChar b v = 1}
  one_mem' := ⟨1, rootDiagUnit_one, by intro v _; exact k0RootChar_one v⟩
  mul_mem' := by
    rintro g h ⟨b, rfl, hb⟩ ⟨c, rfl, hc⟩
    refine ⟨b * c, rootDiagUnit_mul b c, ?_⟩
    intro v hv
    rw [k0RootChar_mul, hb v hv, hc v hv, one_mul]
  inv_mem' := by
    rintro g ⟨b, rfl, hb⟩
    refine ⟨b⁻¹, rootDiagUnit_inv b, ?_⟩
    intro v hv
    rw [k0RootChar_inv, hb v hv, inv_one]

omit [CharP Omega 2] in
private theorem k0CentralTorus_mem (A : K0LangMark Omega lab p R I phi)
    (g : ModGL A.tau Omega) :
    g ∈ k0CentralTorus A ↔ ∃ b : Fin A.tau.rank → Omegaˣ, rootDiagUnit A.tau b = g ∧
      ∀ v ∈ k0Saturated A, rootChar b v = 1 :=
  Iff.rfl

private theorem k0Step_exists_aux {τ : Tag} {L : Type} [Field L]
    (D : LangDatum τ L) (b : Fin τ.rank → Lˣ) :
    ∃ b' : Fin τ.rank → Lˣ, rootDiagUnit τ b' = D.step (rootDiagUnit τ b) := by
  obtain ⟨Fr, hFr, P, hP, hΦ⟩ := D.steinberg
  obtain ⟨w, hn⟩ := D.n_weyl
  rcases hP with rfl | ⟨t, ht, rfl⟩
  · refine ⟨CFSG.HardMathSupport.Timmesfeld.Tables.T1b.weylAct w
      (fun i => Units.map Fr.toMonoidHom (b i)), ?_⟩
    rw [show D.step (rootDiagUnit τ b) = D.n * D.Φ (rootDiagUnit τ b) * D.n⁻¹ by
      simp [LangDatum.step, MulAut.conj_apply]]
    rw [hΦ, CFSG.HardMathSupport.Timmesfeld.CrossChar.units_map_entrywiseHom_rootDiagUnit]
    simp only [one_mul, inv_one, mul_one, hn]
    exact (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.canonicalRep_conj_rootDiagUnit w
      (fun i => Units.map Fr.toMonoidHom (b i))).symm
  · subst ht
    refine ⟨CFSG.HardMathSupport.Timmesfeld.Tables.T1b.weylAct w
      (fun i => Units.map Fr.toMonoidHom (b (t.perm.symm i))), ?_⟩
    rw [show D.step (rootDiagUnit t.tag b) = D.n * D.Φ (rootDiagUnit t.tag b) * D.n⁻¹ by
      simp [LangDatum.step, MulAut.conj_apply]]
    rw [hΦ, CFSG.HardMathSupport.Timmesfeld.CrossChar.units_map_entrywiseHom_rootDiagUnit]
    rw [hn]
    simp only [diagramAt]
    rw [show diagramMap t L * rootDiagUnit t.tag
        (fun i => Units.map Fr.toMonoidHom (b i)) * (diagramMap t L)⁻¹ =
        rootDiagUnit t.tag (fun i => Units.map Fr.toMonoidHom (b (t.perm.symm i))) from by
      rw [diagramMap_mul_rootDiagUnit, mul_assoc, mul_inv_cancel, mul_one]]
    exact (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.canonicalRep_conj_rootDiagUnit w
      (fun i => Units.map Fr.toMonoidHom (b (t.perm.symm i)))).symm

private noncomputable def k0TorusStepFun (A : K0LangMark Omega lab p R I phi)
    (b : Fin A.tau.rank → Omegaˣ) : Fin A.tau.rank → Omegaˣ :=
  Classical.choose (k0Step_exists_aux A.setup.D b)

omit [CharP Omega 2] in
private theorem k0TorusStepFun_spec (A : K0LangMark Omega lab p R I phi)
    (b : Fin A.tau.rank → Omegaˣ) :
    rootDiagUnit A.tau (k0TorusStepFun A b) =
      A.setup.D.step (rootDiagUnit A.tau b) :=
  Classical.choose_spec (k0Step_exists_aux A.setup.D b)

omit [CharP Omega 2] in
private theorem k0TorusStepFun_one (A : K0LangMark Omega lab p R I phi) :
    k0TorusStepFun A 1 = 1 := by
  apply rootDiagUnit_injective
  rw [k0TorusStepFun_spec, rootDiagUnit_one, map_one]

omit [CharP Omega 2] in
private theorem k0TorusStepFun_mul (A : K0LangMark Omega lab p R I phi)
    (b c : Fin A.tau.rank → Omegaˣ) :
    k0TorusStepFun A (b * c) = k0TorusStepFun A b * k0TorusStepFun A c := by
  apply rootDiagUnit_injective
  rw [k0TorusStepFun_spec, rootDiagUnit_mul, map_mul, ← k0TorusStepFun_spec,
    ← k0TorusStepFun_spec, ← rootDiagUnit_mul]

private noncomputable def k0TorusStep (A : K0LangMark Omega lab p R I phi) :
    (Fin A.tau.rank → Omegaˣ) →* (Fin A.tau.rank → Omegaˣ) where
  toFun := k0TorusStepFun A
  map_one' := k0TorusStepFun_one A
  map_mul' := k0TorusStepFun_mul A

omit [CharP Omega 2] in
private theorem k0TorusStep_diag (A : K0LangMark Omega lab p R I phi)
    (b : Fin A.tau.rank → Omegaˣ) :
    rootDiagUnit A.tau (k0TorusStep A b) = A.setup.D.step (rootDiagUnit A.tau b) :=
  k0TorusStepFun_spec A b

omit [CharP Omega 2] in
private theorem k0TorusStep_char_root
    (A : K0LangMark Omega lab p R I phi)
    (b : Fin A.tau.rank → Omegaˣ) {γ : Fin A.tau.rank → ℤ} (hγ : IsRoot A.tau γ) :
    rootChar (k0TorusStep A b) (A.setup.ρ γ) = (rootChar b γ) ^ A.setup.D.q := by
  obtain ⟨ρ', hroot', -, -, hstep'⟩ := exists_step_pinnedX A.setup.D
  obtain ⟨μ, hμ, hstep⟩ := hstep' γ hγ
  have hρ'root : IsRoot A.tau (ρ' γ) := (hroot' γ).2 hγ
  have hρroot : IsRoot A.tau (A.setup.ρ γ) := (A.setup.frob.isRoot_iff γ).2 hγ
  have hρeq : ρ' γ = A.setup.ρ γ := by
    have hmem : pinnedX A.tau Omega (ρ' γ) μ ∈ rootSubgroup A.tau Omega (A.setup.ρ γ) := by
      have hmem0 : A.setup.D.step (pinnedX A.tau Omega γ 1) ∈
          rootSubgroup A.tau Omega (A.setup.ρ γ) := by
        have h0 : A.setup.D.step (pinnedX A.tau Omega γ 1) ∈
            (rootSubgroup A.tau Omega γ).map A.setup.D.step :=
          Subgroup.mem_map.2 ⟨pinnedX A.tau Omega γ 1,
            Subgroup.subset_closure ⟨1, rfl⟩, rfl⟩
        rwa [A.setup.frob.map_rootSubgroup γ hγ] at h0
      rwa [hstep 1, one_pow, mul_one] at hmem0
    exact eq_of_pinnedX_mem_rootSubgroup hρ'root hρroot hμ hmem
  rw [← hρeq]
  have hfix : A.setup.D.step (rootDiagUnit A.tau b) = rootDiagUnit A.tau (k0TorusStep A b) :=
    (k0TorusStep_diag A b).symm
  have h1 : A.setup.D.step (rootDiagUnit A.tau b * pinnedX A.tau Omega γ 1 *
      (rootDiagUnit A.tau b)⁻¹) =
      A.setup.D.step (pinnedX A.tau Omega γ ((rootChar b γ : Omega) * 1)) := by
    rw [rootDiagUnit_conj_pinnedX b hγ]
  rw [map_mul, map_mul, map_inv, hfix, hstep, hstep,
    rootDiagUnit_conj_pinnedX (k0TorusStep A b) hρ'root] at h1
  have h2 := pinnedX_injective (τ := A.tau) (R := Omega) (ρ' γ) h1
  refine Units.ext ?_
  rw [Units.val_pow_eq_pow_val]
  have h3 : (rootChar (k0TorusStep A b) (ρ' γ) : Omega) * μ =
      μ * (rootChar b γ : Omega) ^ A.setup.D.q := by simpa using h2
  exact mul_right_cancel₀ hμ (by rw [h3]; ring)

private theorem k0Zpow_comm {G : Type} [CommGroup G] (a : G) (m n : ℤ) :
    (a ^ m) ^ n = (a ^ n) ^ m := by
  rw [← zpow_mul, ← zpow_mul, mul_comm]

omit [CharP Omega 2] in
private theorem k0TorusStep_char
    (A : K0LangMark Omega lab p R I phi)
    (b : Fin A.tau.rank → Omegaˣ) (v : Fin A.tau.rank → ℤ) :
    rootChar (k0TorusStep A b) (A.frobLinear v) = (rootChar b v) ^ A.setup.D.q := by
  classical
  have hv : v = ∑ i : Fin A.tau.rank, v i • (Pi.single i 1 : Fin A.tau.rank → ℤ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have hpt : ∀ i : Fin A.tau.rank,
      rootChar (k0TorusStep A b) (A.frobLinear (v i • Pi.single i 1)) =
        (rootChar b (v i • Pi.single i 1)) ^ A.setup.D.q := by
    intro i
    rw [LinearEquiv.map_smul, rootChar_zsmul, rootChar_zsmul,
      A.frob_roots _ (isRoot_single A.tau i),
      k0TorusStep_char_root A b (isRoot_single A.tau i), rootChar_single]
    rw [← zpow_natCast (b i) A.setup.D.q]
    exact k0Zpow_comm (b i) (A.setup.D.q) (v i)
  rw [hv, map_sum, rootChar_sum, rootChar_sum]
  rw [show (∏ i, rootChar (k0TorusStep A b) (A.frobLinear (v i • Pi.single i 1))) =
      ∏ i, (rootChar b (v i • Pi.single i 1)) ^ A.setup.D.q from
    Finset.prod_congr rfl fun i _ => hpt i]
  rw [← Finset.prod_pow]

theorem k0CentralTorus_nonempty
    (A : K0LangMark Omega lab p R I phi) : Nonempty (K0CentralTorus A) :=
  ⟨{ saturated := k0Saturated A
     saturated_mem := k0Saturated_mem A
     saturated_frob := k0Saturated_frob A
     centralTorus := k0CentralTorus A
     centralTorus_mem := k0CentralTorus_mem A
     torusStep := k0TorusStep A
     torusStep_diag := k0TorusStep_diag A
     torusStep_char := k0TorusStep_char A }⟩

end CFSG.StandardType.GGK0MarkedKacIface1587

end
