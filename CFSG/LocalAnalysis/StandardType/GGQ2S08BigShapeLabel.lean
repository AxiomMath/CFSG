module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigDefs
public import CFSG.LocalAnalysis.StandardType.GGQ2S08Cartan
public import CFSG.LocalAnalysis.StandardType.GGQ2LDatumDims

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Matrix TestLin

variable {G : Type} [Group G] {Bs L : Subgroup G} {x : G}

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma ggQ2s08bs1_root_xV (M : GGQ2LDatum 3 Bs L x) (i : M.Λ) :
    M.root i M.xV = 0 := by
  have hxV_fixed : M.xV ∈ ggFixedSubmodule (p := 3) M.model (ggAutomizer L Bs) := by
    rw [M.fixed_x]
    exact Submodule.subset_span (Set.mem_singleton M.xV)
  have hmem : M.simple i ∈ ggAutomizer L Bs := by
    rw [M.automizer_L]
    exact Subgroup.subset_closure (Set.mem_range_self i)
  have hfix : ggLin (p := 3) M.model (M.simple i) M.xV = M.xV :=
    (mem_ggFixedSubmodule_iff.mp hxV_fixed) (M.simple i) hmem
  rw [M.simple_apply i M.xV] at hfix
  have h0 : (M.root i M.xV) • M.coroot i = 0 := sub_eq_self.mp hfix
  have h2 : (M.root i M.xV) * (M.cartan i i : ZMod 3) = 0 := by
    have := congrArg (fun w => M.root i w) h0
    simpa [map_smul, M.pairing i i, smul_eq_mul, RingHom.id_apply] using this
  have hc2 : (M.cartan i i : ZMod 3) = 2 := by
    rw [M.isCartan.1 i]
    norm_num
  rw [hc2] at h2
  exact (mul_eq_zero.mp h2).resolve_right (by decide : (2 : ZMod 3) ≠ 0)

private lemma ggQ2s08bs1_mem_span_xV (M : GGQ2LDatum 3 Bs L x) (v : M.V)
    (h : ∀ i, M.root i v = 0) : v ∈ Submodule.span (ZMod 3) {M.xV} := by
  have hfix : ∀ i, ggLin (p := 3) M.model (M.simple i) v = v := by
    intro i
    rw [M.simple_apply i v, h i, zero_smul, sub_zero]
  let H : Subgroup (MulAut ↥Bs) :=
    { carrier := {φ | ggLin (p := 3) M.model φ v = v}
      one_mem' := by
        simp only [Set.mem_setOf_eq]
        rw [map_one]
        rfl
      mul_mem' := by
        intro φ ψ hφ hψ
        simp only [Set.mem_setOf_eq] at hφ hψ ⊢
        rw [map_mul, LinearEquiv.mul_apply, hψ, hφ]
      inv_mem' := by
        intro φ hφ
        simp only [Set.mem_setOf_eq] at hφ ⊢
        apply (ggLin (p := 3) M.model φ).injective
        rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
        rw [hφ]
        rfl }
  have hle : Subgroup.closure (Set.range M.simple) ≤ H := by
    rw [Subgroup.closure_le]
    rintro φ ⟨i, rfl⟩
    exact hfix i
  have hmem : v ∈ ggFixedSubmodule (p := 3) M.model (ggAutomizer L Bs) := by
    rw [mem_ggFixedSubmodule_iff]
    intro φ hφ
    rw [M.automizer_L] at hφ
    exact hle hφ
  rw [M.fixed_x] at hmem
  exact hmem

private lemma ggQ2s08bs1_root_sum (M : GGQ2LDatum 3 Bs L x) {ℓ : ℕ} (e : Fin ℓ ≃ M.Λ)
    (C₀ : Matrix (Fin ℓ) (Fin ℓ) ℤ) (hC : ∀ i j, M.cartan (e i) (e j) = C₀ i j)
    (y : Fin ℓ → ZMod 3) (i : Fin ℓ) :
    M.root (e i) (∑ j, y j • M.coroot (e j)) = ∑ j, (C₀ i j : ZMod 3) * y j := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, M.pairing, hC, smul_eq_mul, mul_comm]

private lemma ggQ2s08bs1_eq_zero_of_kernel_det_ne_zero {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    (C : Matrix Λ Λ ℤ) (hdet : (C.det : ZMod 3) ≠ 0)
    (c : Λ → ZMod 3) (hc : ∀ i, ∑ j, (C i j : ZMod 3) * c j = 0) : c = 0 := by
  let C3 : Matrix Λ Λ (ZMod 3) := (Int.castRingHom (ZMod 3)).mapMatrix C
  have hdet3 : C3.det ≠ 0 := by
    dsimp only [C3]
    rw [← RingHom.map_det]
    exact hdet
  have hv : C3.mulVec c = 0 := by
    ext i
    dsimp only [C3]
    change ∑ j, (C i j : ZMod 3) * c j = 0
    simpa only [Matrix.mulVec, dotProduct, mul_comm] using hc i
  exact Matrix.eq_zero_of_mulVec_eq_zero hdet3 hv

private lemma ggQ2s08bs1_det_reindex {n : ℕ} {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    (e : Fin n ≃ Λ) (C₀ : Matrix (Fin n) (Fin n) ℤ) (C : Matrix Λ Λ ℤ)
    (hC : ∀ i j, C (e i) (e j) = C₀ i j) : C.det = C₀.det := by
  have hCL_eq : C = Matrix.reindex e e C₀ := by
    ext a b
    rw [Matrix.reindex_apply]
    simpa [Matrix.submatrix_apply] using hC (e.symm a) (e.symm b)
  rw [hCL_eq, Matrix.det_reindex_self]

private lemma ggQ2s08bs1_cartanA_det_ne_zero {n : ℕ} (h : ¬ 3 ∣ n + 1) :
    (((CartanMatrix.A n).det : ℤ) : ZMod 3) ≠ 0 := by
  rw [CartanMatrix.A_det]
  intro h0
  apply h
  have h1 : ((n + 1 : ℕ) : ZMod 3) = 0 := by
    push_cast at h0
    push_cast
    exact h0
  exact (ZMod.natCast_eq_zero_iff _ _).mp h1

private lemma ggQ2s08bs1_cartanA_det_eq_zero_of_dvd {n : ℕ} (h : 3 ∣ n + 1) :
    (((CartanMatrix.A n).det : ℤ) : ZMod 3) = 0 := by
  rw [CartanMatrix.A_det]
  have hnat : ((n + 1 : ℕ) : ZMod 3) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h
  push_cast at hnat
  push_cast
  exact hnat

private lemma ggQ2s08bs1_cartanB_det_ne_zero {n : ℕ} (hn : 0 < n) :
    (((CartanMatrix.B n).det : ℤ) : ZMod 3) ≠ 0 := by
  rw [CartanMatrix.B_det hn]
  decide

private lemma ggQ2s08bs1_cartanC_det_ne_zero {n : ℕ} (hn : 0 < n) :
    (((CartanMatrix.C n).det : ℤ) : ZMod 3) ≠ 0 := by
  rw [CartanMatrix.C_det hn]
  decide

private lemma ggQ2s08bs1_cartanD_det_ne_zero {n : ℕ} (hn : 2 ≤ n) :
    (((CartanMatrix.D n).det : ℤ) : ZMod 3) ≠ 0 := by
  rw [CartanMatrix.D_det hn]
  decide

private lemma ggQ2s08bs1_kernel_of_mem_coSpan (M : GGQ2LDatum 3 Bs L x)
    (hx0 : M.xV ≠ 0) (hxH : M.xV ∈ M.coSpan) :
    ∃ c : M.Λ → ZMod 3, c ≠ 0 ∧
      ∀ i, ∑ j, (M.cartan i j : ZMod 3) * c j = 0 := by
  obtain ⟨c, hc_eq⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 3)).mp hxH
  have hc0 : c ≠ 0 := by
    intro h0
    apply hx0
    have h := hc_eq
    rw [h0] at h
    simpa using h.symm
  refine ⟨c, hc0, ?_⟩
  intro i
  have h := congrArg (M.root i) hc_eq
  rw [ggQ2s08bs1_root_xV M i, map_sum] at h
  rw [Finset.sum_congr rfl (fun j _ => by rw [map_smul, M.pairing, smul_eq_mul])] at h
  rw [Finset.sum_congr rfl (fun j _ => by rw [mul_comm])] at h
  exact h

private lemma ggQ2s08bs1_kernel_of_finrank (M : GGQ2LDatum 3 Bs L x)
    (hfr : Module.finrank (ZMod 3) M.coSpan + 1 = Fintype.card M.Λ) :
    ∃ c : M.Λ → ZMod 3, c ≠ 0 ∧
      ∀ i, ∑ j, (M.cartan i j : ZMod 3) * c j = 0 := by
  have hli_not : ¬ LinearIndependent (ZMod 3) M.coroot := by
    intro hli
    have hcard : Module.finrank (ZMod 3) M.coSpan = Fintype.card M.Λ := by
      rw [GGQ2LDatum.coSpan]
      exact finrank_span_eq_card hli
    omega
  have hnot : ¬ ∀ g : M.Λ → ZMod 3, (∑ j, g j • M.coroot j) = 0 → g = 0 := by
    intro h
    apply hli_not
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    exact congrFun (h g hg) i
  push Not at hnot
  obtain ⟨c, hsum, hc0⟩ := hnot
  refine ⟨c, hc0, ?_⟩
  intro i
  have h := congrArg (M.root i) hsum
  rw [map_sum, map_zero] at h
  rw [Finset.sum_congr rfl (fun j _ => by rw [map_smul, M.pairing, smul_eq_mul])] at h
  rw [Finset.sum_congr rfl (fun j _ => by rw [mul_comm])] at h
  exact h

private lemma ggQ2s08bs1_exists_kernel_of_notFull (M : GGQ2LDatum 3 Bs L x)
    (hx0 : M.xV ≠ 0) (h : M.ShapeA ∨ M.ShapeB ∨ M.ShapeC ∨ M.ShapeD) :
    ∃ c : M.Λ → ZMod 3, c ≠ 0 ∧
      ∀ i, ∑ j, (M.cartan i j : ZMod 3) * c j = 0 := by
  rcases h with hA | hB | hC | hD
  · exact ggQ2s08bs1_kernel_of_mem_coSpan M hx0 hA.2.2.1
  · exact ggQ2s08bs1_kernel_of_finrank M hB.2.1
  · exact ggQ2s08bs1_kernel_of_finrank M hC.2.1
  · exact ggQ2s08bs1_kernel_of_mem_coSpan M hx0 (by rw [hD.2.2]; exact Submodule.mem_top)

private lemma ggQ2s08bs1_not_shapeFull_of_nonFull (M : GGQ2LDatum 3 Bs L x)
    (h : M.ShapeA ∨ M.ShapeB ∨ M.ShapeC ∨ M.ShapeD) : ¬ M.ShapeFull := by
  rintro hF
  rcases h with hA | hB | hC | hD
  · exact hF.2.2.1 hA.2.2.1
  · have hcard : Module.finrank (ZMod 3) M.coSpan = Fintype.card M.Λ := by
      rw [GGQ2LDatum.coSpan]
      exact finrank_span_eq_card hF.2.1
    have hfr : Module.finrank (ZMod 3) M.coSpan + 1 = Fintype.card M.Λ := hB.2.1
    omega
  · have hcard : Module.finrank (ZMod 3) M.coSpan = Fintype.card M.Λ := by
      rw [GGQ2LDatum.coSpan]
      exact finrank_span_eq_card hF.2.1
    have hfr : Module.finrank (ZMod 3) M.coSpan + 1 = Fintype.card M.Λ := hC.2.1
    omega
  · exact hF.2.2.1 (by rw [hD.2.2]; exact Submodule.mem_top)

private lemma ggQ2s08bs1_tag_and_dvd_of_kernel (M : GGQ2LDatum 3 Bs L x)
    {lab : LargeEvenLabel} (hlab : GGQ2S08BigLabel lab)
    (hMW : GGQ2LabelWeyl lab M.coxeter)
    (c : M.Λ → ZMod 3) (hc0 : c ≠ 0)
    (hc : ∀ i, ∑ j, (M.cartan i j : ZMod 3) * c j = 0) :
    lab.tag = .twA ∧ 3 ∣ lab.rank + 1 := by
  obtain ⟨-, htag, hrank⟩ := hlab
  have hrank' : 0 < lab.rank := by omega
  have hrank2 : 2 ≤ lab.rank := by omega
  rcases htag with htwA | hB | hC | hD | htwD
  ·
    obtain ⟨e, he⟩ : ∃ e : Fin lab.rank ≃ M.Λ,
        M.coxeter = (CoxeterMatrix.A lab.rank).reindex e := by
      simpa only [GGQ2LabelWeyl, htwA] using hMW
    have hA' : ∀ i j : Fin lab.rank, M.cartan (e i) (e j) = CartanMatrix.A lab.rank i j :=
      ggQ2_cartan_A e he M.isCartan
    refine ⟨htwA, ?_⟩
    by_contra hnot
    have hdet : (M.cartan.det : ZMod 3) ≠ 0 := by
      rw [ggQ2s08bs1_det_reindex e (CartanMatrix.A lab.rank) M.cartan hA']
      exact ggQ2s08bs1_cartanA_det_ne_zero hnot
    exact hc0 (ggQ2s08bs1_eq_zero_of_kernel_det_ne_zero M.cartan hdet c hc)
  ·
    exfalso
    obtain ⟨e, he⟩ : ∃ e : Fin lab.rank ≃ M.Λ,
        M.coxeter = (CoxeterMatrix.B lab.rank).reindex e := by
      simpa only [GGQ2LabelWeyl, hB] using hMW
    rcases ggQ2_cartan_B e he M.isCartan with hB' | hC'
    · have hdet : (M.cartan.det : ZMod 3) ≠ 0 := by
        rw [ggQ2s08bs1_det_reindex e (CartanMatrix.B lab.rank) M.cartan hB']
        exact ggQ2s08bs1_cartanB_det_ne_zero hrank'
      exact hc0 (ggQ2s08bs1_eq_zero_of_kernel_det_ne_zero M.cartan hdet c hc)
    · have hdet : (M.cartan.det : ZMod 3) ≠ 0 := by
        rw [ggQ2s08bs1_det_reindex e (CartanMatrix.C lab.rank) M.cartan hC']
        exact ggQ2s08bs1_cartanC_det_ne_zero hrank'
      exact hc0 (ggQ2s08bs1_eq_zero_of_kernel_det_ne_zero M.cartan hdet c hc)
  ·
    exfalso
    obtain ⟨e, he⟩ : ∃ e : Fin lab.rank ≃ M.Λ,
        M.coxeter = (CoxeterMatrix.B lab.rank).reindex e := by
      simpa only [GGQ2LabelWeyl, hC] using hMW
    rcases ggQ2_cartan_B e he M.isCartan with hB' | hC'
    · have hdet : (M.cartan.det : ZMod 3) ≠ 0 := by
        rw [ggQ2s08bs1_det_reindex e (CartanMatrix.B lab.rank) M.cartan hB']
        exact ggQ2s08bs1_cartanB_det_ne_zero hrank'
      exact hc0 (ggQ2s08bs1_eq_zero_of_kernel_det_ne_zero M.cartan hdet c hc)
    · have hdet : (M.cartan.det : ZMod 3) ≠ 0 := by
        rw [ggQ2s08bs1_det_reindex e (CartanMatrix.C lab.rank) M.cartan hC']
        exact ggQ2s08bs1_cartanC_det_ne_zero hrank'
      exact hc0 (ggQ2s08bs1_eq_zero_of_kernel_det_ne_zero M.cartan hdet c hc)
  ·
    exfalso
    obtain ⟨e, he⟩ : ∃ e : Fin lab.rank ≃ M.Λ,
        M.coxeter = (ggCoxeterMatrixD lab.rank).reindex e := by
      simpa only [GGQ2LabelWeyl, hD] using hMW
    have hD' : ∀ i j : Fin lab.rank, M.cartan (e i) (e j) = CartanMatrix.D lab.rank i j :=
      ggQ2_cartan_D e he M.isCartan
    have hdet : (M.cartan.det : ZMod 3) ≠ 0 := by
      rw [ggQ2s08bs1_det_reindex e (CartanMatrix.D lab.rank) M.cartan hD']
      exact ggQ2s08bs1_cartanD_det_ne_zero hrank2
    exact hc0 (ggQ2s08bs1_eq_zero_of_kernel_det_ne_zero M.cartan hdet c hc)
  ·
    exfalso
    obtain ⟨e, he⟩ : ∃ e : Fin lab.rank ≃ M.Λ,
        M.coxeter = (ggCoxeterMatrixD lab.rank).reindex e := by
      simpa only [GGQ2LabelWeyl, htwD] using hMW
    have hD' : ∀ i j : Fin lab.rank, M.cartan (e i) (e j) = CartanMatrix.D lab.rank i j :=
      ggQ2_cartan_D e he M.isCartan
    have hdet : (M.cartan.det : ZMod 3) ≠ 0 := by
      rw [ggQ2s08bs1_det_reindex e (CartanMatrix.D lab.rank) M.cartan hD']
      exact ggQ2s08bs1_cartanD_det_ne_zero hrank2
    exact hc0 (ggQ2s08bs1_eq_zero_of_kernel_det_ne_zero M.cartan hdet c hc)

private lemma ggQ2s08bs1_second_alt_of_nonFull (M : GGQ2LDatum 3 Bs L x)
    {lab : LargeEvenLabel} (hlab : GGQ2S08BigLabel lab)
    (hMW : GGQ2LabelWeyl lab M.coxeter) (hx0 : M.xV ≠ 0)
    (h : M.ShapeA ∨ M.ShapeB ∨ M.ShapeC ∨ M.ShapeD) :
    ¬ M.ShapeFull ∧ lab.tag = .twA ∧ 3 ∣ lab.rank + 1 ∧ 12 ≤ lab.rank + 1 := by
  have hnon : ¬ M.ShapeFull := ggQ2s08bs1_not_shapeFull_of_nonFull M h
  obtain ⟨c, hc0, hc⟩ := ggQ2s08bs1_exists_kernel_of_notFull M hx0 h
  obtain ⟨htwA, hdiv⟩ := ggQ2s08bs1_tag_and_dvd_of_kernel M hlab hMW c hc0 hc
  obtain ⟨-, -, hrank⟩ := hlab
  refine ⟨hnon, htwA, hdiv, ?_⟩
  omega

theorem ggQ2s08_big_shape_label (M : GGQ2LDatum 3 Bs L x) {lab : LargeEvenLabel}
    (hlab : GGQ2S08BigLabel lab) (hMW : GGQ2LabelWeyl lab M.coxeter) (hx0 : M.xV ≠ 0)
    (hSh : M.Shape) :
    (M.ShapeFull ∧ ¬ (lab.tag = .twA ∧ 3 ∣ lab.rank + 1)) ∨
      (¬ M.ShapeFull ∧ lab.tag = .twA ∧ 3 ∣ lab.rank + 1 ∧ 12 ≤ lab.rank + 1) := by
  rcases hSh with hFull | hA | hB | hC | hD
  · left
    refine ⟨hFull, ?_⟩
    rintro ⟨htwA, hdiv⟩
    obtain ⟨e, he⟩ : ∃ e : Fin lab.rank ≃ M.Λ,
        M.coxeter = (CoxeterMatrix.A lab.rank).reindex e := by
      simpa only [GGQ2LabelWeyl, htwA] using hMW
    have hA' : ∀ i j : Fin lab.rank, M.cartan (e i) (e j) = CartanMatrix.A lab.rank i j :=
      ggQ2_cartan_A e he M.isCartan
    have hdet0 : (M.cartan.det : ZMod 3) = 0 := by
      rw [ggQ2s08bs1_det_reindex e (CartanMatrix.A lab.rank) M.cartan hA']
      exact ggQ2s08bs1_cartanA_det_eq_zero_of_dvd hdiv
    let C3 : Matrix M.Λ M.Λ (ZMod 3) := (Int.castRingHom (ZMod 3)).mapMatrix M.cartan
    have hC3det : C3.det = 0 := by
      dsimp only [C3]
      rw [← RingHom.map_det]
      exact hdet0
    obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hC3det
    let c' : Fin lab.rank → ZMod 3 := fun i => c (e i)
    have hc'_ker : ∀ i, ∑ j, (CartanMatrix.A lab.rank i j : ZMod 3) * c' j = 0 := by
      intro i
      have h : ∑ j : M.Λ, (M.cartan (e i) j : ZMod 3) * c j = 0 := by
        have hc' := congrFun hc (e i)
        dsimp only [C3] at hc'
        simp only [Matrix.mulVec_apply, dotProduct] at hc'
        change ∑ j : M.Λ, (M.cartan (e i) j : ZMod 3) * c j = 0 at hc'
        exact hc'
      rw [← Equiv.sum_comp e (fun j : M.Λ => (M.cartan (e i) j : ZMod 3) * c j)] at h
      simpa only [hA', c'] using h
    let v' : M.V := ∑ j : Fin lab.rank, c' j • M.coroot (e j)
    have hv'_coSpan : v' ∈ M.coSpan := by
      rw [GGQ2LDatum.coSpan]
      change (∑ j : Fin lab.rank, c' j • M.coroot (e j)) ∈
        Submodule.span (ZMod 3) (Set.range M.coroot)
      exact Submodule.sum_mem _ fun j _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨e j, rfl⟩)
    have hv'_span : v' ∈ Submodule.span (ZMod 3) {M.xV} := by
      apply ggQ2s08bs1_mem_span_xV
      intro i
      obtain ⟨i', rfl⟩ := e.surjective i
      change M.root (e i') (∑ j : Fin lab.rank, c' j • M.coroot (e j)) = 0
      rw [ggQ2s08bs1_root_sum M e (CartanMatrix.A lab.rank) hA' c' i', hc'_ker i']
    have hinf : M.coSpan ⊓ Submodule.span (ZMod 3) {M.xV} = ⊥ :=
      disjoint_iff.mp (Submodule.disjoint_span_singleton_of_notMem hFull.2.2.1)
    have hv'_zero : v' = 0 := by
      have : v' ∈ M.coSpan ⊓ Submodule.span (ZMod 3) {M.xV} := ⟨hv'_coSpan, hv'_span⟩
      rwa [hinf, Submodule.mem_bot] at this
    have hli' : LinearIndependent (ZMod 3) (fun j : Fin lab.rank => M.coroot (e j)) :=
      hFull.2.1.comp e e.injective
    have hc'_zero : c' = 0 := funext fun i => (Fintype.linearIndependent_iff.mp hli') c' hv'_zero i
    exact hc0 (funext fun a => by
      obtain ⟨i, rfl⟩ := e.surjective a
      exact congrFun hc'_zero i)
  · exact Or.inr (ggQ2s08bs1_second_alt_of_nonFull M hlab hMW hx0 (Or.inl hA))
  · exact Or.inr (ggQ2s08bs1_second_alt_of_nonFull M hlab hMW hx0 (Or.inr (Or.inl hB)))
  · exact Or.inr (ggQ2s08bs1_second_alt_of_nonFull M hlab hMW hx0 (Or.inr (Or.inr (Or.inl hC))))
  · exact Or.inr (ggQ2s08bs1_second_alt_of_nonFull M hlab hMW hx0 (Or.inr (Or.inr (Or.inr hD))))

end CFSG.StandardType

end
