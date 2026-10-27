module

public import CFSG.RankThree.PartOne.KC.OrthogonalSupportedBlocks

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary

section Glue

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {U R : Submodule K V}

@[expose] noncomputable def glue (hc : IsCompl U R) (a : U ≃ₗ[K] U) (b : R ≃ₗ[K] R) :
    V ≃ₗ[K] V :=
  (Submodule.prodEquivOfIsCompl U R hc).symm.trans
    ((LinearEquiv.prodCongr a b).trans (Submodule.prodEquivOfIsCompl U R hc))

theorem glue_apply (hc : IsCompl U R) (a : U ≃ₗ[K] U) (b : R ≃ₗ[K] R) (u : U) (r : R) :
    glue hc a b ((u : V) + r) = (a u : V) + (b r : V) := by
  have h : (Submodule.prodEquivOfIsCompl U R hc).symm ((u : V) + r) = (u, r) := by
    rw [LinearEquiv.symm_apply_eq]
    simp
  simp [glue, h]

theorem exists_coe_add_of_isCompl (hc : IsCompl U R) (v : V) :
    ∃ (u : U) (r : R), (u : V) + r = v := by
  obtain ⟨⟨u, r⟩, h⟩ := (Submodule.prodEquivOfIsCompl U R hc).surjective v
  exact ⟨u, r, by simpa using h⟩

theorem glue_mul (hc : IsCompl U R) (a a' : U ≃ₗ[K] U) (b b' : R ≃ₗ[K] R) :
    glue hc (a * a') (b * b') = glue hc a b * glue hc a' b' := by
  ext v
  obtain ⟨u, r, rfl⟩ := exists_coe_add_of_isCompl hc v
  simp only [LinearEquiv.mul_apply, glue_apply]

theorem glue_one (hc : IsCompl U R) : glue hc 1 1 = 1 := by
  ext v
  obtain ⟨u, r, rfl⟩ := exists_coe_add_of_isCompl hc v
  simp [glue_apply]


@[expose] noncomputable def restrictEquiv (U : Submodule K V) (g : V ≃ₗ[K] V)
    (h1 : ∀ u ∈ U, g u ∈ U) (h2 : ∀ u ∈ U, g.symm u ∈ U) : U ≃ₗ[K] U :=
  LinearEquiv.ofLinearMap (g.toLinearMap.restrict h1) (g.symm.toLinearMap.restrict h2)
    (LinearMap.ext fun u => Subtype.ext (g.apply_symm_apply u))
    (LinearMap.ext fun u => Subtype.ext (g.symm_apply_apply u))

@[simp] theorem coe_restrictEquiv (U : Submodule K V) (g : V ≃ₗ[K] V)
    (h1 : ∀ u ∈ U, g u ∈ U) (h2 : ∀ u ∈ U, g.symm u ∈ U) (u : U) :
    (restrictEquiv U g h1 h2 u : V) = g u := rfl

end Glue

section Fixed

variable {K : Type*} {V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

@[expose] def fixedSpace (x : V ≃ₗ[K] V) : Submodule K V := LinearMap.ker (x.toLinearMap - 1)

omit [FiniteDimensional K V] in
theorem mem_fixedSpace {w : V} : w ∈ fixedSpace x ↔ x w = w := by
  rw [fixedSpace, LinearMap.mem_ker]
  simp [sub_eq_zero]

omit [FiniteDimensional K V] in
theorem fixedSpace_eq_primaryComponent :
    fixedSpace x = primaryComponent x.toLinearMap (X - 1) := by
  ext w
  rw [mem_primaryComponent, mem_fixedSpace]
  simp [sub_eq_zero]

theorem fixedSpace_eq_bot_of_not_mem
    (hnot : (X - 1 : K[X]) ∉ primaryFactors x.toLinearMap) : fixedSpace x = ⊥ := by
  have hnd : ¬ (X - 1 : K[X]) ∣ minpoly K x.toLinearMap := fun hd =>
    hnot (mem_primaryFactors.mpr ⟨irreducible_X_sub_one, monic_X_sub_one, hd⟩)
  have hcop : IsCoprime (X - 1 : K[X]) (minpoly K x.toLinearMap) :=
    (irreducible_X_sub_one.coprime_iff_not_dvd).mpr hnd
  have hd := Polynomial.disjoint_ker_aeval_of_isCoprime x.toLinearMap hcop
  have hker : LinearMap.ker (aeval x.toLinearMap (minpoly K x.toLinearMap)) = ⊤ := by
    rw [minpoly.aeval, LinearMap.ker_zero]
  rw [hker, disjoint_top] at hd
  rw [fixedSpace_eq_primaryComponent]
  exact hd

theorem OddOrderIsometry.fixed_others (hx : OddOrderIsometry Q p x) :
    IsCompl (fixedSpace x) (othersSpace x.toLinearMap (X - 1)) ∧
      ∀ w ∈ fixedSpace x, ∀ r ∈ othersSpace x.toLinearMap (X - 1),
        QuadraticMap.polar Q w r = 0 := by
  classical
  by_cases hmem : (X - 1 : K[X]) ∈ primaryFactors x.toLinearMap
  · have hW : orbitSpace x.toLinearMap (X - 1) = fixedSpace x := by
      rw [orbitSpace, reciprocalPolynomial_X_sub_one, sup_idem, fixedSpace_eq_primaryComponent]
    refine ⟨hW ▸ hx.isCompl_orbit_others hmem, fun w hw r hr => ?_⟩
    exact hx.polar_orbit_others hmem (hW ▸ hw) hr
  · have hbot := fixedSpace_eq_bot_of_not_mem hmem
    have htop : othersSpace x.toLinearMap (X - 1) = ⊤ := by
      rw [eq_top_iff]
      intro v _
      have hsum := congrArg (fun f : Module.End K V => f v)
        (sum_primaryProjection (x := x.toLinearMap) hx.squarefree_minpoly)
      simp only [LinearMap.sum_apply, Module.End.one_apply] at hsum
      rw [← hsum]
      refine Submodule.sum_mem _ fun k hk => ?_
      have hk1 : k ≠ X - 1 := fun e => hmem (e ▸ hk)
      exact Submodule.mem_iSup_of_mem k (Submodule.mem_iSup_of_mem
        ⟨hk, hk1, by rw [reciprocalPolynomial_X_sub_one]; exact hk1⟩
        (primaryProjection_mem hx.squarefree_minpoly hk v))
    rw [hbot, htop]
    exact ⟨isCompl_bot_top, fun w hw => by simp at hw; simp [hw]⟩

omit [FiniteDimensional K V] in
theorem mem_fixedSpace_of_apply {g : V ≃ₗ[K] V}
    (hg : g ∈ Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V))) {w : V} (hw : w ∈ fixedSpace x) :
    g w ∈ fixedSpace x := by
  rw [fixedSpace_eq_primaryComponent] at hw ⊢
  exact apply_mem_primaryComponent_of_mem_centralizer hg hw

@[expose] noncomputable def restrictFixed (Q : QuadraticForm K V) (x : V ≃ₗ[K] V) :
    ↥(supportedBlock Q x (X - 1)) →* (fixedSpace x ≃ₗ[K] fixedSpace x) where
  toFun g := restrictEquiv (fixedSpace x) g.1
    (fun _ hw => mem_fixedSpace_of_apply
      (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp g.2).1).2 hw)
    (fun _ hw => mem_fixedSpace_of_apply (symm_mem_centralizer x
      (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp g.2).1).2) hw)
  map_one' := LinearEquiv.ext fun _ => Subtype.ext rfl
  map_mul' _ _ := LinearEquiv.ext fun _ => Subtype.ext rfl

omit [FiniteDimensional K V] in
theorem coe_restrictFixed (g : ↥(supportedBlock Q x (X - 1))) (w : fixedSpace x) :
    (restrictFixed Q x g w : V) = g.1 w := rfl

omit [FiniteDimensional K V] in
theorem restrictFixed_mem_orthogonalGroup (g : ↥(supportedBlock Q x (X - 1))) :
    restrictFixed Q x g ∈ TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype) := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro w
  have h := (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp
    (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp g.2).1).1) (w : V)
  show Q ((restrictFixed Q x g w : fixedSpace x) : V) = Q (w : V)
  rw [coe_restrictFixed]
  exact h

theorem restrictFixed_injective (hx : OddOrderIsometry Q p x) :
    Function.Injective (restrictFixed Q x) := by
  intro g g' hgg
  apply Subtype.ext
  refine LinearEquiv.ext fun v => ?_
  obtain ⟨w, hw, r, hr, rfl⟩ := exists_add_of_isCompl hx.fixed_others.1 v
  have h1 := congrArg (fun φ : fixedSpace x ≃ₗ[K] fixedSpace x => (φ ⟨w, hw⟩ : V)) hgg
  simp only [coe_restrictFixed] at h1
  rw [map_add, map_add, h1, (mem_supportedBlock.mp g.2).2 r hr, (mem_supportedBlock.mp g'.2).2 r hr]

omit [FiniteDimensional K V] in
theorem mem_othersSpace_of_apply {g : V ≃ₗ[K] V}
    (hg : g ∈ Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V))) {h : K[X]} {r : V}
    (hr : r ∈ othersSpace x.toLinearMap h) : g r ∈ othersSpace x.toLinearMap h := by
  unfold othersSpace at hr ⊢
  refine Submodule.iSup_induction _ (motive := fun r => g r ∈ ⨆ (k : K[X])
    (_ : k ∈ primaryFactors x.toLinearMap ∧ k ≠ h ∧ k ≠ reciprocalPolynomial h),
      primaryComponent x.toLinearMap k) hr (fun k r hr => ?_) (by simp)
    (fun a b ha hb => by rw [map_add]; exact Submodule.add_mem _ ha hb)
  refine Submodule.iSup_induction _ (motive := fun r => g r ∈ ⨆ (k : K[X])
    (_ : k ∈ primaryFactors x.toLinearMap ∧ k ≠ h ∧ k ≠ reciprocalPolynomial h),
      primaryComponent x.toLinearMap k) hr (fun hk r hr => ?_) (by simp)
    (fun a b ha hb => by rw [map_add]; exact Submodule.add_mem _ ha hb)
  exact Submodule.mem_iSup_of_mem k (Submodule.mem_iSup_of_mem hk
    (apply_mem_primaryComponent_of_mem_centralizer hg hr))

theorem restrictFixed_surjective (hx : OddOrderIsometry Q p x)
    (φ : fixedSpace x ≃ₗ[K] fixedSpace x)
    (hφ : φ ∈ TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype)) :
    ∃ g : ↥(supportedBlock Q x (X - 1)), restrictFixed Q x g = φ := by
  obtain ⟨hc, horth⟩ := hx.fixed_others
  set R := othersSpace x.toLinearMap (X - 1) with hR
  let T : V ≃ₗ[K] V := glue hc φ 1
  have hT : ∀ (u : fixedSpace x) (r : R), T ((u : V) + r) = (φ u : V) + r := fun u r => by
    simp only [T]
    rw [glue_apply]
    rfl
  have hxR : ∀ r ∈ R, x r ∈ R := fun r hr =>
    mem_othersSpace_of_apply ((Subgroup.mem_centralizer_singleton_iff).mpr rfl) hr
  have hTfix : ∀ r ∈ R, T r = r := fun r hr => by
    have := hT 0 ⟨r, hr⟩
    simpa using this
  have hTx : ∀ v, T (x v) = x (T v) := by
    intro v
    obtain ⟨u, r, rfl⟩ := exists_coe_add_of_isCompl hc v
    have hxu : x (u : V) = u := mem_fixedSpace.mp u.2
    have hxφ : x (φ u : V) = φ u := mem_fixedSpace.mp (φ u).2
    have hxr : x (r : V) ∈ R := hxR _ r.2
    have h1 : T (x ((u : V) + r)) = (φ u : V) + x r := by
      rw [map_add, hxu]
      exact hT u ⟨x r, hxr⟩
    have h2 : x (T ((u : V) + r)) = (φ u : V) + x r := by
      rw [hT, map_add, hxφ]
    rw [h1, h2]
  have hTQ : ∀ v, Q (T v) = Q v := by
    intro v
    obtain ⟨u, r, rfl⟩ := exists_coe_add_of_isCompl hc v
    have hφQ : Q (φ u : V) = Q (u : V) := by
      have := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hφ u
      simpa [QuadraticMap.comp_apply] using this
    rw [hT, QuadraticMap.map_add (⇑Q) _ _, QuadraticMap.map_add (⇑Q) (u : V) (r : V),
      horth _ (φ u).2 _ r.2, horth _ u.2 _ r.2, hφQ]
  have hTmem : T ∈ supportedBlock Q x (X - 1) :=
    mem_supportedBlock.mpr ⟨mem_isometryCentralizer.mpr ⟨hTQ, hTx⟩, hTfix⟩
  refine ⟨⟨T, hTmem⟩, LinearEquiv.ext fun w => Subtype.ext ?_⟩
  rw [coe_restrictFixed]
  have := hT w 0
  simpa using this

@[expose] noncomputable def fixedBlockEquiv (hx : OddOrderIsometry Q p x) :
    ↥(supportedBlock Q x (X - 1)) ≃*
      ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype)) :=
  MulEquiv.ofBijective ((restrictFixed Q x).codRestrict _ restrictFixed_mem_orthogonalGroup)
    ⟨fun g g' h => restrictFixed_injective hx (congrArg Subtype.val h), fun φ => by
      obtain ⟨g, hg⟩ := restrictFixed_surjective hx φ.1 φ.2
      exact ⟨g, Subtype.ext hg⟩⟩

theorem coe_fixedBlockEquiv (hx : OddOrderIsometry Q p x) (g : ↥(supportedBlock Q x (X - 1)))
    (w : fixedSpace x) : ((fixedBlockEquiv hx g : fixedSpace x ≃ₗ[K] fixedSpace x) w : V) =
      g.1 w := rfl

end Fixed

end CFSG.RankThree.PartOne.KCOrthogonal
