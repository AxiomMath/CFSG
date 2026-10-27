module

public import CFSG.RankThree.PartOne.KC.OrthogonalCentralizerBlocks
public import CFSG.RankThree.PartOne.KC.OrthogonalPrimarySummands

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary

section Supported

variable {K : Type*} {V : Type*} [Field K] [AddCommGroup V] [Module K V]

@[expose] def isometryCentralizer (Q : QuadraticForm K V) (x : V ≃ₗ[K] V) :
    Subgroup (V ≃ₗ[K] V) :=
  TauCeti.QuadraticMap.orthogonalGroup Q ⊓ Subgroup.centralizer {x}

theorem mem_isometryCentralizer {Q : QuadraticForm K V} {x g : V ≃ₗ[K] V} :
    g ∈ isometryCentralizer Q x ↔ (∀ v, Q (g v) = Q v) ∧ ∀ v, g (x v) = x (g v) := by
  rw [isometryCentralizer, Subgroup.mem_inf, TauCeti.QuadraticMap.mem_orthogonalGroup_iff,
    mem_centralizer_iff]

@[expose] def supportedBlock (Q : QuadraticForm K V) (x : V ≃ₗ[K] V) (h : K[X]) :
    Subgroup (V ≃ₗ[K] V) :=
  isometryCentralizer Q x ⊓
    fixingSubgroup (V ≃ₗ[K] V) (othersSpace x.toLinearMap h : Set V)

theorem mem_supportedBlock {Q : QuadraticForm K V} {x g : V ≃ₗ[K] V} {h : K[X]} :
    g ∈ supportedBlock Q x h ↔ g ∈ isometryCentralizer Q x ∧
      ∀ v ∈ othersSpace x.toLinearMap h, g v = v := by
  rw [supportedBlock, Subgroup.mem_inf, mem_fixingSubgroup_iff]
  rfl

theorem fixes_othersSpace_iff {x : V ≃ₗ[K] V} {h : K[X]} {g : V ≃ₗ[K] V} :
    (∀ v ∈ othersSpace x.toLinearMap h, g v = v) ↔
      ∀ k ∈ primaryFactors x.toLinearMap, k ≠ h → k ≠ reciprocalPolynomial h →
        ∀ v ∈ primaryComponent x.toLinearMap k, g v = v := by
  constructor
  · intro hg k hk hkh hkh' v hv
    exact hg v (Submodule.mem_iSup_of_mem k (Submodule.mem_iSup_of_mem ⟨hk, hkh, hkh'⟩ hv))
  · intro hg v hv
    unfold othersSpace at hv
    refine Submodule.iSup_induction _ (motive := fun v => g v = v) hv (fun k v hv => ?_) (by simp)
      (fun a b ha hb => by rw [map_add, ha, hb])
    refine Submodule.iSup_induction _ (motive := fun v => g v = v) hv (fun hk v hv => ?_) (by simp)
      (fun a b ha hb => by rw [map_add, ha, hb])
    exact hg k hk.1 hk.2.1 hk.2.2 v hv

theorem exists_add_of_isCompl {U R : Submodule K V} (hc : IsCompl U R) (v : V) :
    ∃ u ∈ U, ∃ r ∈ R, u + r = v := by
  obtain ⟨⟨u, r⟩, h⟩ := (Submodule.prodEquivOfIsCompl U R hc).surjective v
  exact ⟨u, u.2, r, r.2, by simpa using h⟩

end Supported

section Block

variable {K : Type*} {V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

theorem OddOrderIsometry.mem_supportedBlock_of_block (hx : OddOrderIsometry Q p x) {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) {T : V ≃ₗ[K] V}
    (hT : T ∈ Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V)))
    (hfix : ∀ v ∈ othersSpace x.toLinearMap h, T v = v)
    (hQ : ∀ u ∈ orbitSpace x.toLinearMap h, Q (T u) = Q u) : T ∈ supportedBlock Q x h := by
  refine mem_supportedBlock.mpr ⟨mem_isometryCentralizer.mpr ⟨fun v => ?_,
    (mem_centralizer_iff x).mp hT⟩, hfix⟩
  obtain ⟨u, hu, r, hr, rfl⟩ := exists_add_of_isCompl (hx.isCompl_orbit_others hh) v
  have hTu : T u ∈ orbitSpace x.toLinearMap h := mem_orbitSpace_of_apply hT hu
  rw [map_add, hfix r hr, QuadraticMap.map_add (⇑Q) _ _, QuadraticMap.map_add (⇑Q) u r,
    hx.polar_orbit_others hh hTu hr, hx.polar_orbit_others hh hu hr, hQ u hu]

open scoped _root_.Classical in
@[expose] noncomputable def blockComponent (hx : OddOrderIsometry Q p x)
    (g : (Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V)) : Subgroup (V ≃ₗ[K] V))) (h : K[X]) :
    (Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V)) : Subgroup (V ≃ₗ[K] V)) :=
  (theta x hx.squarefree_minpoly).symm fun a =>
    if (a : K[X]) = h ∨ (a : K[X]) = reciprocalPolynomial h then
      theta x hx.squarefree_minpoly g a else 1

open scoped _root_.Classical in
theorem blockComponent_apply_of_mem (hx : OddOrderIsometry Q p x)
    (g : (Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V)) : Subgroup (V ≃ₗ[K] V))) (h : K[X])
    {a : K[X]} (ha : a ∈ primaryFactors x.toLinearMap) {v : V}
    (hv : v ∈ primaryComponent x.toLinearMap a) :
    (blockComponent hx g h).1 v = if a = h ∨ a = reciprocalPolynomial h then g.1 v else v := by
  classical
  have h1 := coe_theta_apply x hx.squarefree_minpoly (blockComponent hx g h) ⟨a, ha⟩ ⟨v, hv⟩
  have h2 : theta x hx.squarefree_minpoly (blockComponent hx g h) =
      fun a : primaryFactors x.toLinearMap =>
      if (a : K[X]) = h ∨ (a : K[X]) = reciprocalPolynomial h then
        theta x hx.squarefree_minpoly g a else 1 :=
    (theta x hx.squarefree_minpoly).apply_symm_apply _
  rw [← h1, h2]
  by_cases hc : a = h ∨ a = reciprocalPolynomial h
  · simp only [hc, ite_true]
    exact coe_theta_apply x hx.squarefree_minpoly g ⟨a, ha⟩ ⟨v, hv⟩
  · simp only [hc, ite_false]
    rfl

omit [FiniteDimensional K V] in
theorem apply_mem_primaryComponent_of_mem_centralizer {g : V ≃ₗ[K] V}
    (hg : g ∈ Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V))) {a : K[X]} {v : V}
    (hv : v ∈ primaryComponent x.toLinearMap a) : g v ∈ primaryComponent x.toLinearMap a :=
  apply_mem_primaryComponent (commute_toLinearMap_of_mem_centralizer x hg) hv

theorem OddOrderIsometry.blockComponent_mem (hx : OddOrderIsometry Q p x)
    {g : V ≃ₗ[K] V} (hg : g ∈ isometryCentralizer Q x) {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) :
    (blockComponent hx ⟨g, (Subgroup.mem_inf.mp hg).2⟩ h).1 ∈ supportedBlock Q x h := by
  classical
  set g' : (Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V)) : Subgroup (V ≃ₗ[K] V)) :=
    ⟨g, (Subgroup.mem_inf.mp hg).2⟩ with hg'
  have hh' := hx.reciprocalPolynomial_mem hh
  refine hx.mem_supportedBlock_of_block hh (blockComponent hx g' h).2 ?_ ?_
  · exact fun v hv => (fixes_othersSpace_iff.mpr (fun k hk hkh hkh' v hv => by
      rw [blockComponent_apply_of_mem hx g' h hk hv]
      simp [hkh, hkh']) v hv)
  · intro u hu
    obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := Submodule.mem_sup.mp hu
    rw [map_add, blockComponent_apply_of_mem hx g' h hh hu₁,
      blockComponent_apply_of_mem hx g' h hh' hu₂]
    simp only [true_or, or_true, ite_true, ← map_add]
    exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp (Subgroup.mem_inf.mp hg).1 _

theorem OddOrderIsometry.orbit_disjoint (hx : OddOrderIsometry Q p x) {h k : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) (hk : k ∈ primaryFactors x.toLinearMap)
    (hkh : k ≠ h) (hkh' : k ≠ reciprocalPolynomial h) {a : K[X]}
    (ha : a = h ∨ a = reciprocalPolynomial h) : a ≠ k ∧ a ≠ reciprocalPolynomial k := by
  have e1 := hx.reciprocal_reciprocal_eq hh
  have e2 := hx.reciprocal_reciprocal_eq hk
  rcases ha with rfl | rfl
  · exact ⟨fun h1 => hkh h1.symm, fun h1 => hkh' (by rw [h1, e2])⟩
  · exact ⟨fun h1 => hkh' h1.symm, fun h1 => hkh (by rw [← e1, h1, e2])⟩

omit [FiniteDimensional K V] in
theorem apply_eq_of_mem_supportedBlock {g : V ≃ₗ[K] V} {h : K[X]}
    (hg : g ∈ supportedBlock Q x h) {a : K[X]} (ha : a ∈ primaryFactors x.toLinearMap)
    (hah : a ≠ h) (hah' : a ≠ reciprocalPolynomial h) {v : V}
    (hv : v ∈ primaryComponent x.toLinearMap a) : g v = v :=
  (mem_supportedBlock.mp hg).2 v
    (Submodule.mem_iSup_of_mem a (Submodule.mem_iSup_of_mem ⟨ha, hah, hah'⟩ hv))

theorem OddOrderIsometry.commute_supportedBlock (hx : OddOrderIsometry Q p x) {h k : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) (hk : k ∈ primaryFactors x.toLinearMap)
    (hkh : k ≠ h) (hkh' : k ≠ reciprocalPolynomial h) {g g' : V ≃ₗ[K] V}
    (hg : g ∈ supportedBlock Q x h) (hg' : g' ∈ supportedBlock Q x k) : Commute g g' := by
  have hcg := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hg).1).2
  have hcg' := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hg').1).2
  have hh' := hx.reciprocalPolynomial_mem hh
  have hk' := hx.reciprocalPolynomial_mem hk
  have hext : g.toLinearMap * g'.toLinearMap = g'.toLinearMap * g.toLinearMap := by
    refine ext_primaryComponent hx.squarefree_minpoly fun a ha v hv => ?_
    show g (g' v) = g' (g v)
    by_cases hah : a = h ∨ a = reciprocalPolynomial h
    · obtain ⟨h1, h2⟩ := hx.orbit_disjoint hh hk hkh hkh' hah
      rw [apply_eq_of_mem_supportedBlock hg' ha h1 h2 hv,
        apply_eq_of_mem_supportedBlock hg' ha h1 h2
          (apply_mem_primaryComponent_of_mem_centralizer hcg hv)]
    · by_cases hak : a = k ∨ a = reciprocalPolynomial k
      · have h1 : a ≠ h := fun e => hah (Or.inl e)
        have h2 : a ≠ reciprocalPolynomial h := fun e => hah (Or.inr e)
        rw [apply_eq_of_mem_supportedBlock hg ha h1 h2 hv,
          apply_eq_of_mem_supportedBlock hg ha h1 h2
            (apply_mem_primaryComponent_of_mem_centralizer hcg' hv)]
      · have h1 : a ≠ h := fun e => hah (Or.inl e)
        have h2 : a ≠ reciprocalPolynomial h := fun e => hah (Or.inr e)
        have h3 : a ≠ k := fun e => hak (Or.inl e)
        have h4 : a ≠ reciprocalPolynomial k := fun e => hak (Or.inr e)
        rw [apply_eq_of_mem_supportedBlock hg' ha h3 h4 hv,
          apply_eq_of_mem_supportedBlock hg ha h1 h2 hv,
          apply_eq_of_mem_supportedBlock hg' ha h3 h4 hv]
  show g * g' = g' * g
  ext v
  exact congrArg (fun f : Module.End K V => f v) hext

section Product

@[expose] def IsOrbitRepresentatives (x : V ≃ₗ[K] V) (Rep : Finset K[X]) : Prop :=
  Rep ⊆ primaryFactors x.toLinearMap ∧ ∀ k ∈ primaryFactors x.toLinearMap,
    ∃! r, r ∈ Rep ∧ (k = r ∨ k = reciprocalPolynomial r)

open scoped _root_.Classical in
theorem OddOrderIsometry.disjoint_supportedBlock (hx : OddOrderIsometry Q p x) {Rep : Finset K[X]}
    (hRep : IsOrbitRepresentatives x Rep) {r : K[X]} (hr : r ∈ Rep) :
    Disjoint (supportedBlock Q x r) (⨆ s ∈ Rep.erase r, supportedBlock Q x s) := by
  rw [Subgroup.disjoint_def]
  intro g hg hg'
  have hfix : ∀ a ∈ primaryFactors x.toLinearMap, (a = r ∨ a = reciprocalPolynomial r) →
      ∀ v ∈ primaryComponent x.toLinearMap a, g v = v := by
    intro a ha har v hv
    refine Subgroup.iSup_induction (fun s => ⨆ (_ : s ∈ Rep.erase r), supportedBlock Q x s)
      (C := fun g => g v = v) hg' (fun s g hg => ?_) rfl (fun g g' hg hg' => by
        rw [LinearEquiv.mul_apply, hg', hg])
    refine Subgroup.iSup_induction (fun _ : s ∈ Rep.erase r => supportedBlock Q x s)
      (C := fun g => g v = v) hg (fun hs g hg => ?_) rfl (fun g g' hg hg' => by
        rw [LinearEquiv.mul_apply, hg', hg])
    have hs' := Finset.mem_erase.mp hs
    refine apply_eq_of_mem_supportedBlock hg ha (fun e => hs'.1 ?_) (fun e => hs'.1 ?_) hv
    · obtain ⟨r₀, -, hr₀⟩ := hRep.2 a ha
      have h1 := hr₀ r ⟨hr, har⟩
      have h2 := hr₀ s ⟨hs'.2, Or.inl e⟩
      rw [h1, h2]
    · obtain ⟨r₀, -, hr₀⟩ := hRep.2 a ha
      have h1 := hr₀ r ⟨hr, har⟩
      have h2 := hr₀ s ⟨hs'.2, Or.inr e⟩
      rw [h1, h2]
  have hg1 : g = 1 := by
    refine LinearEquiv.ext fun v => ?_
    have := congrArg (fun f : Module.End K V => f v) (ext_primaryComponent
      (f := g.toLinearMap) (g := LinearMap.id) hx.squarefree_minpoly fun a ha v hv => ?_)
    · exact this
    · by_cases har : a = r ∨ a = reciprocalPolynomial r
      · exact hfix a ha har v hv
      · exact apply_eq_of_mem_supportedBlock hg ha (fun e => har (Or.inl e))
          (fun e => har (Or.inr e)) hv
  exact hg1

open scoped _root_.Classical in
theorem OddOrderIsometry.isometryCentralizer_le (hx : OddOrderIsometry Q p x) {Rep : Finset K[X]}
    (hRep : IsOrbitRepresentatives x Rep) :
    isometryCentralizer Q x ≤ ⨆ r ∈ Rep, supportedBlock Q x r := by
  suffices H : ∀ s : Finset K[X], s ⊆ Rep → ∀ g ∈ isometryCentralizer Q x,
      (∀ a ∈ primaryFactors x.toLinearMap, (∀ r ∈ s, a ≠ r ∧ a ≠ reciprocalPolynomial r) →
        ∀ v ∈ primaryComponent x.toLinearMap a, g v = v) → g ∈ ⨆ r ∈ s, supportedBlock Q x r by
    intro g hg
    refine H Rep le_rfl g hg fun a ha hnot => ?_
    obtain ⟨r, ⟨hr, har⟩, -⟩ := hRep.2 a ha
    exfalso
    rcases har with rfl | rfl
    · exact (hnot a hr).1 rfl
    · exact (hnot r hr).2 rfl
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro _ g hg hall
    have hg1 : g = 1 := by
      refine LinearEquiv.ext fun v => ?_
      have := congrArg (fun f : Module.End K V => f v) (ext_primaryComponent
        (f := g.toLinearMap) (g := LinearMap.id) hx.squarefree_minpoly fun a ha v hv =>
          hall a ha (by simp) v hv)
      exact this
    simp [hg1]
  | insert r s hrs ih =>
    intro hsub g hg hall
    have hr : r ∈ Rep := hsub (Finset.mem_insert_self r s)
    have hs : s ⊆ Rep := fun a ha => hsub (Finset.mem_insert_of_mem ha)
    have hrpf : r ∈ primaryFactors x.toLinearMap := hRep.1 hr
    set g0 : (Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V)) : Subgroup (V ≃ₗ[K] V)) :=
      ⟨g, (Subgroup.mem_inf.mp hg).2⟩ with hg0
    have hc : (blockComponent hx g0 r).1 ∈ supportedBlock Q x r :=
      hx.blockComponent_mem hg hrpf
    set g' := (blockComponent hx g0 r).1 with hg'
    have hg'M : g' ∈ isometryCentralizer Q x := (Subgroup.mem_inf.mp hc).1
    have hg''M : g'⁻¹ * g ∈ isometryCentralizer Q x :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ hg'M) hg
    have hg'' : g'⁻¹ * g ∈ ⨆ r ∈ s, supportedBlock Q x r := by
      refine ih hs _ hg''M fun a ha hnot v hv => ?_
      have hga : g v ∈ primaryComponent x.toLinearMap a :=
        apply_mem_primaryComponent_of_mem_centralizer (Subgroup.mem_inf.mp hg).2 hv
      by_cases har : a = r ∨ a = reciprocalPolynomial r
      · have h1 : g' v = g v := by
          rw [hg', blockComponent_apply_of_mem hx g0 r ha hv]
          simp only [har, ite_true]
          rfl
        show g'.symm (g v) = v
        rw [← h1]
        exact g'.symm_apply_apply v
      · have h1 : g' v = v := by
          rw [hg', blockComponent_apply_of_mem hx g0 r ha hv]
          simp [har]
        have h2 : g v = v := by
          refine hall a ha (fun r' hr' => ?_) v hv
          rcases Finset.mem_insert.mp hr' with rfl | hr'
          · exact ⟨fun e => har (Or.inl e), fun e => har (Or.inr e)⟩
          · exact hnot r' hr'
        show g'.symm (g v) = v
        rw [h2]
        exact g'.symm_apply_eq.mpr h1.symm
    rw [Finset.iSup_insert]
    have : g = g' * (g'⁻¹ * g) := by simp
    rw [this]
    exact Subgroup.mul_mem_sup hc hg''

end Product

end Block

end CFSG.RankThree.PartOne.KCOrthogonal
