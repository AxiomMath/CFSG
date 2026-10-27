module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallOrthUnCount

public section

namespace CFSG.StandardType

namespace SmallOrthUn

open Module Polynomial CFSG.Assembly CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.Classical2 OrthRestOdd

section Split

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ} {a : V ≃ₗ[K] V}

theorem exists_split_orbit (hx : OddOrderIsometry Q p a) {h : K[X]} {Y : Submodule K V}
    (hYa : ∀ y ∈ Y, a y ∈ Y) {y : V} (hy : y ∈ Y) :
    ∃ u ∈ Y ⊓ orbitSpace a.toLinearMap h, ∃ r ∈ Y ⊓ othersSpace a.toLinearMap h, y = u + r := by
  classical
  set P := primaryFactors a.toLinearMap with hP
  have hsum : ∑ k ∈ P, primaryProjection a.toLinearMap k y = y := by
    have := congrArg (fun f : Module.End K V => f y)
      (sum_primaryProjection (x := a.toLinearMap) hx.squarefree_minpoly)
    simpa [LinearMap.sum_apply] using this
  have hYk : ∀ k, primaryProjection a.toLinearMap k y ∈ Y := fun k =>
    CFSG.LieType.SeitzGeneration.aeval_mem_of_stable (S := Y) (x := a.toLinearMap)
      (fun s hs => hYa s hs) _ hy
  refine ⟨∑ k ∈ P.filter (fun k => k = h ∨ k = reciprocalPolynomial h),
      primaryProjection a.toLinearMap k y, ?_,
    ∑ k ∈ P.filter (fun k => ¬ (k = h ∨ k = reciprocalPolynomial h)),
      primaryProjection a.toLinearMap k y, ?_, ?_⟩
  · refine ⟨Submodule.sum_mem _ fun k hk => hYk k, Submodule.sum_mem _ fun k hk => ?_⟩
    obtain ⟨hkP, hkh⟩ := Finset.mem_filter.mp hk
    have hmem := primaryProjection_mem hx.squarefree_minpoly hkP y
    rcases hkh with rfl | rfl
    · exact Submodule.mem_sup_left hmem
    · exact Submodule.mem_sup_right hmem
  · refine ⟨Submodule.sum_mem _ fun k hk => hYk k, Submodule.sum_mem _ fun k hk => ?_⟩
    obtain ⟨hkP, hkh⟩ := Finset.mem_filter.mp hk
    have hmem := primaryProjection_mem hx.squarefree_minpoly hkP y
    exact Submodule.mem_iSup_of_mem k (Submodule.mem_iSup_of_mem
      ⟨hkP, fun e => hkh (Or.inl e), fun e => hkh (Or.inr e)⟩ hmem)
  · rw [Finset.sum_filter_add_sum_filter_not, hsum]

theorem commute_of_fix_orbit (hx : OddOrderIsometry Q p a) {h : K[X]}
    (hh : h ∈ primaryFactors a.toLinearMap) {b d : V ≃ₗ[K] V}
    (hb : b ∈ Subgroup.centralizer ({a} : Set (V ≃ₗ[K] V)))
    (hbU : ∀ u ∈ orbitSpace a.toLinearMap h, b u = u) (hd : d ∈ supportedBlock Q a h) :
    b * d = d * b := by
  have hdc : d ∈ Subgroup.centralizer ({a} : Set (V ≃ₗ[K] V)) :=
    (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hd).1).2
  have hdR := (mem_supportedBlock.mp hd).2
  ext v
  obtain ⟨u, hu, r, hr, rfl⟩ := exists_add_of_isCompl (hx.isCompl_orbit_others hh) v
  have hbr : b r ∈ othersSpace a.toLinearMap h := mem_othersSpace_of_apply hb hr
  have hdu : d u ∈ orbitSpace a.toLinearMap h := mem_orbitSpace_of_apply hdc hu
  simp only [LinearEquiv.mul_apply, map_add]
  rw [hdR r hr, hbU u hu, hbU _ hdu, hdR _ hbr]

end Split

section Dichotomy

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ} {a : V ≃ₗ[K] V}

theorem conj_mem_commutator_supportedBlock {m f : V ≃ₗ[K] V} {h : K[X]}
    (hm : m ∈ isometryCentralizer Q a)
    (hf : f ∈ ⁅supportedBlock Q a h, supportedBlock Q a h⁆) :
    m * f * m⁻¹ ∈ ⁅supportedBlock Q a h, supportedBlock Q a h⁆ := by
  have hle : (supportedBlock Q a h).map (MulAut.conj m).toMonoidHom ≤ supportedBlock Q a h := by
    rintro _ ⟨g, hg, rfl⟩
    exact conj_mem_supportedBlock hm hg
  have h1 : ⁅supportedBlock Q a h, supportedBlock Q a h⁆.map (MulAut.conj m).toMonoidHom ≤
      ⁅supportedBlock Q a h, supportedBlock Q a h⁆ := by
    rw [Subgroup.map_commutator]
    exact Subgroup.commutator_mono hle hle
  exact h1 ⟨f, hf, rfl⟩

theorem commutator_supportedBlock_le (h : K[X]) :
    ⁅supportedBlock Q a h, supportedBlock Q a h⁆ ≤
      isometryCentralizer Q a ⊓ orthDerived Q := by
  have hBM : supportedBlock Q a h ≤ isometryCentralizer Q a :=
    supportedBlock_le_isometryCentralizer h
  have hBO : supportedBlock Q a h ≤ TauCeti.QuadraticMap.orthogonalGroup Q := fun g hg =>
    (Subgroup.mem_inf.mp (hBM hg)).1
  refine le_inf ?_ (Subgroup.commutator_mono hBO hBO)
  refine Subgroup.commutator_le.mpr fun g hg g' hg' => ?_
  rw [commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem (hBM hg) (hBM hg')) (inv_mem (hBM hg))) (inv_mem (hBM hg'))

theorem exists_block_of_endData (hx : OddOrderIsometry Q p a) {Rep : Finset K[X]}
    (hRep : IsOrbitRepresentatives a Rep) {D : Subgroup (V ≃ₗ[K] V)}
    (hDΩ : D ≤ orthDerived Q) (hDc : ∀ d ∈ D, d * a = a * d)
    (hDn : ∀ c ∈ orthDerived Q, c * a = a * c → ∀ d ∈ D, c * d * c⁻¹ ∈ D)
    (hDq : CFSG.IsQuasisimple D) :
    ∃ i ∈ Rep, D ≤ ⁅supportedBlock Q a i, supportedBlock Q a i⁆ := by
  classical
  set M := isometryCentralizer Q a with hM
  set C : Subgroup (V ≃ₗ[K] V) := M ⊓ orthDerived Q with hC
  have hDM : D ≤ M := fun d hd => mem_isometryCentralizer.mpr
    ⟨fun v => TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp
      (orthDerived_le_orthogonalGroup (hDΩ hd)) v, fun v => by
      have := congrArg (fun f : V ≃ₗ[K] V => f v) (hDc d hd)
      exact this⟩
  have hDC : D ≤ C := fun d hd => ⟨hDM hd, hDΩ hd⟩
  have hDn' : ∀ c ∈ C, ∀ d ∈ D, c * d * c⁻¹ ∈ D := fun c hc d hd =>
    hDn c hc.2 (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hc.1).2) d hd
  have hDle : ∀ d ∈ D, d ∈ ⨆ i : ↥Rep, ⁅supportedBlock Q a i, supportedBlock Q a i⁆ := by
    intro d hd
    have hperf : ⁅D, D⁆ = D := Subgroup.isPerfect_iff.1 hDq.1
    have hd0 : d ∈ ⁅D, D⁆ := by rw [hperf]; exact hd
    have hd1 : d ∈ ⁅M, M⁆ := Subgroup.commutator_mono hDM hDM hd0
    rw [hM, ← hx.blocks_iSup_eq hRep] at hd1
    obtain ⟨w, hw, hgw⟩ := exists_noncommProd_of_mem_commutator
      (fun i : ↥Rep => supportedBlock Q a i) (hx.blocks_commute hRep) hd1
    rw [hgw, Subgroup.noncommPiCoprod_apply]
    exact Subgroup.noncommProd_mem _ _ fun i _ =>
      le_iSup (fun i : ↥Rep => ⁅supportedBlock Q a i, supportedBlock Q a i⁆) i (hw i)
  by_contra hcon
  push Not at hcon
  have hcomm : ∀ i ∈ Rep, ∀ d ∈ D, ∀ b ∈ ⁅supportedBlock Q a i, supportedBlock Q a i⁆,
      d * b = b * d := by
    intro i hi d hd b hb
    have hBn : ∀ c ∈ C, ∀ b ∈ ⁅supportedBlock Q a i, supportedBlock Q a i⁆,
        c * b * c⁻¹ ∈ ⁅supportedBlock Q a i, supportedBlock Q a i⁆ := fun c hc b hb =>
      conj_mem_commutator_supportedBlock hc.1 hb
    rcases StdSubRestThree.le_or_commute_of_quasisimple hDC
      (commutator_supportedBlock_le i) hDn' hBn hDq with hle | hcm
    · exact absurd hle (hcon i hi)
    · exact hcm d hd b hb
  obtain ⟨d₁, hd₁, d₂, hd₂, hne⟩ := StdSubRestThree.exists_ne_comm_of_isQuasisimple hDq
  apply hne
  have hle : (⨆ i : ↥Rep, ⁅supportedBlock Q a i, supportedBlock Q a i⁆) ≤
      Subgroup.centralizer ({d₁} : Set (V ≃ₗ[K] V)) := by
    refine iSup_le fun i b hb => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hcomm i i.2 d₁ hd₁ b hb).symm
  have := Subgroup.mem_centralizer_singleton_iff.mp (hle (hDle d₂ hd₂))
  exact this.symm

end Dichotomy

end SmallOrthUn

end CFSG.StandardType

end
