module

public import CFSG.LocalAnalysis.StandardType.GGQTwoGammaXGraphLinDefs
import CFSG.LocalAnalysis.StandardType.GGQTwoReflKill
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem ggQ2gc_sub_mem (D : GGQ2WDatum 3) (g : D.V ≃ₗ[ZMod 3] D.V) (hg : g ∈ D.weyl)
    (v : D.V) : g v - v ∈ D.corootSpan := by
  refine Subgroup.closure_induction
    (p := fun g _ => ∀ v : D.V, g v - v ∈ D.corootSpan) ?_ ?_ ?_ ?_ hg v
  · rintro g ⟨k, rfl⟩ v
    rw [D.simpleRefl_apply]
    have hmem : D.coroot k ∈ D.corootSpan := Submodule.subset_span ⟨k, rfl⟩
    have heq : v - D.root k v • D.coroot k - v = -(D.root k v • D.coroot k) := by abel
    rw [heq]
    exact Submodule.neg_mem _ (Submodule.smul_mem _ _ hmem)
  · intro v
    simp
  · intro a b ha hb iha ihb v
    rw [LinearEquiv.mul_apply]
    have heq : a (b v) - v = (a (b v) - b v) + (b v - v) := by abel
    rw [heq]
    exact Submodule.add_mem _ (iha (b v)) (ihb v)
  · intro a ha iha v
    have h := iha (a⁻¹ v)
    have h1 : a (a⁻¹ v) = v := by simp
    rw [h1] at h
    have heq : a⁻¹ v - v = -(v - a⁻¹ v) := by abel
    rw [heq]
    exact Submodule.neg_mem _ h

private theorem ggQ2gc_conj_coroot_mem (D : GGQ2WDatum 3) (S : D.V ≃ₗ[ZMod 3] D.V)
    (hS : ∀ j : D.Λ, S * D.simpleRefl j * S⁻¹ ∈ D.weyl) (j : D.Λ) :
    S (D.coroot j) ∈ D.corootSpan := by
  let v0 : D.V := (2 : ZMod 3) • D.coroot j
  have hv0 : D.root j v0 = 1 := by
    show D.root j ((2 : ZMod 3) • D.coroot j) = 1
    rw [map_smul, D.pairing, D.isCartan.1 j]
    decide
  have hr : D.simpleRefl j v0 = v0 - D.coroot j := by
    rw [D.simpleRefl_apply, hv0, one_smul]
  have hvr : v0 - D.simpleRefl j v0 = D.coroot j := by
    rw [hr]; abel
  have hmem : (S * D.simpleRefl j * S⁻¹) (S v0) - S v0 ∈ D.corootSpan :=
    ggQ2gc_sub_mem D _ (hS j) (S v0)
  have hkey : (S * D.simpleRefl j * S⁻¹) (S v0) = S (D.simpleRefl j v0) := by
    simp [LinearEquiv.mul_apply]
  have heq : S (D.coroot j) = S v0 - (S * D.simpleRefl j * S⁻¹) (S v0) := by
    rw [hkey, ← map_sub, hvr]
  rw [heq]
  simpa only [neg_sub] using Submodule.neg_mem _ hmem

private theorem ggQ2gc_map_le (D : GGQ2WDatum 3) (S : D.V ≃ₗ[ZMod 3] D.V)
    (hS : ∀ j : D.Λ, S * D.simpleRefl j * S⁻¹ ∈ D.weyl) :
    D.corootSpan.map (S : D.V →ₗ[ZMod 3] D.V) ≤ D.corootSpan := by
  rw [Submodule.map_le_iff_le_comap, GGQ2WDatum.corootSpan, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  exact ggQ2gc_conj_coroot_mem D S hS j

private theorem ggQ2gc_map_eq (D : GGQ2WDatum 3) (S : D.V ≃ₗ[ZMod 3] D.V)
    (hS : S ∈ Subgroup.normalizer (D.weyl : Set (D.V ≃ₗ[ZMod 3] D.V))) :
    D.corootSpan.map (S : D.V →ₗ[ZMod 3] D.V) = D.corootSpan := by
  have hconj : ∀ j : D.Λ, S * D.simpleRefl j * S⁻¹ ∈ D.weyl := fun j =>
    (Subgroup.mem_normalizer_iff.mp hS _).mp (D.simpleRefl_mem_weyl j)
  have hconj' : ∀ j : D.Λ, S⁻¹ * D.simpleRefl j * S ∈ D.weyl := fun j =>
    (Subgroup.mem_normalizer_iff''.mp hS _).mp (D.simpleRefl_mem_weyl j)
  refine le_antisymm (ggQ2gc_map_le D S hconj) ?_
  intro u hu
  have hmem : S⁻¹ u ∈ D.corootSpan :=
    ggQ2gc_map_le D S⁻¹ (by simpa using hconj') ⟨u, hu, rfl⟩
  exact ⟨S⁻¹ u, hmem, by simp⟩

private noncomputable def ggQ2gc_res (D : GGQ2WDatum 3) :
    D.weyl →* (D.corootSpan ≃ₗ[ZMod 3] D.corootSpan) where
  toFun g := LinearEquiv.ofSubmodules (g.1 : D.V ≃ₗ[ZMod 3] D.V) D.corootSpan D.corootSpan
    (ggQ2gc_map_eq D g.1 (Subgroup.le_normalizer g.2))
  map_one' := by ext; rfl
  map_mul' g h := by ext; rfl

private theorem ggQ2gc_res_apply (D : GGQ2WDatum 3) (g : D.weyl) (v : D.V)
    (hv : v ∈ D.corootSpan) : ((ggQ2gc_res D g) ⟨v, hv⟩ : D.V) = g.1 v :=
  LinearEquiv.ofSubmodules_apply (g.1 : D.V ≃ₗ[ZMod 3] D.V)
    (ggQ2gc_map_eq D g.1 (Subgroup.le_normalizer g.2)) ⟨v, hv⟩

private def ggQ2gc_h' (D : GGQ2WDatum 3) {n : ℕ} (e : Fin n ≃ D.Λ) : Fin n → D.corootSpan :=
  fun i => ⟨D.coroot (e i), Submodule.subset_span ⟨e i, rfl⟩⟩

private def ggQ2gc_α' (D : GGQ2WDatum 3) {n : ℕ} (e : Fin n ≃ D.Λ) :
    Fin n → Module.Dual (ZMod 3) D.corootSpan :=
  fun i => (D.root (e i)).comp D.corootSpan.subtype

private theorem ggQ2gc_α'_h' (D : GGQ2WDatum 3) {n : ℕ} (e : Fin n ≃ D.Λ)
    (C : Matrix (Fin n) (Fin n) ℤ) (hC : ∀ i j, D.cartan (e i) (e j) = C i j) (i j : Fin n) :
    ggQ2gc_α' D e i (ggQ2gc_h' D e j) = ((C i j : ℤ) : ZMod 3) := by
  show D.root (e i) (D.coroot (e j)) = _
  rw [D.pairing, hC i j]

private theorem ggQ2gc_h'_li (D : GGQ2WDatum 3) {n : ℕ} (e : Fin n ≃ D.Λ)
    (hind : LinearIndependent (ZMod 3) D.coroot) :
    LinearIndependent (ZMod 3) (ggQ2gc_h' D e) := by
  have h0 := linearIndependent_span (R := ZMod 3) (v := D.coroot) hind
  have h := h0.comp e e.injective
  change LinearIndependent (ZMod 3) (fun i => (⟨D.coroot (e i), _⟩ : D.corootSpan))
  exact h

private theorem ggQ2gc_h'_span (D : GGQ2WDatum 3) {n : ℕ} (e : Fin n ≃ D.Λ)
    (hind : LinearIndependent (ZMod 3) D.coroot) :
    Submodule.span (ZMod 3) (Set.range (ggQ2gc_h' D e)) = ⊤ := by
  have : Module.Finite (ZMod 3) D.corootSpan :=
    Module.Finite.span_of_finite (ZMod 3) (Set.finite_range _)
  obtain ⟨j0⟩ := D.nonempty
  have : Nonempty (Fin n) := ⟨e.symm j0⟩
  refine LinearIndependent.span_eq_top_of_card_eq_finrank (ggQ2gc_h'_li D e hind) ?_
  rw [GGQ2WDatum.corootSpan, finrank_span_eq_card hind]
  exact Fintype.card_congr e

private theorem ggQ2gc_range_res (D : GGQ2WDatum 3) {n : ℕ} (e : Fin n ≃ D.Λ) :
    (ggQ2gc_res D).range = ggQ2WeylOf (ggQ2gc_h' D e) (ggQ2gc_α' D e) := by
  refine le_antisymm ?_ ?_
  · intro y hy
    rw [MonoidHom.mem_range] at hy
    obtain ⟨g, rfl⟩ := hy
    refine Subgroup.closure_induction
      (p := fun g hg => ggQ2gc_res D ⟨g, hg⟩ ∈
        ggQ2WeylOf (ggQ2gc_h' D e) (ggQ2gc_α' D e)) ?_ ?_ ?_ ?_ g.2
    · rintro g ⟨k, rfl⟩
      let i : Fin n := e.symm k
      have hki : e i = k := e.apply_symm_apply _
      refine Subgroup.subset_closure ⟨i, ?_⟩
      intro v
      apply Subtype.ext
      rw [ggQ2gc_res_apply D _ (v : D.V) v.2, D.simpleRefl_apply]
      simp [ggQ2gc_α', ggQ2gc_h', hki]
    · change ggQ2gc_res D (1 : D.weyl) ∈ ggQ2WeylOf (ggQ2gc_h' D e) (ggQ2gc_α' D e)
      rw [map_one]
      exact Subgroup.one_mem _
    · intro a b ha hb iha ihb
      have hmul : (⟨a * b, _⟩ : D.weyl) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
      rw [hmul, map_mul]
      exact Subgroup.mul_mem _ iha ihb
    · intro a ha iha
      have hinv : (⟨a⁻¹, _⟩ : D.weyl) = ⟨a, ha⟩⁻¹ := rfl
      rw [hinv, map_inv]
      exact Subgroup.inv_mem _ iha
  · rw [ggQ2WeylOf, Subgroup.closure_le]
    rintro t ⟨i, ht⟩
    refine MonoidHom.mem_range.mpr ⟨⟨D.simpleRefl (e i), D.simpleRefl_mem_weyl (e i)⟩, ?_⟩
    apply LinearEquiv.ext
    intro v
    apply Subtype.ext
    rw [ggQ2gc_res_apply D _ (v : D.V) v.2, D.simpleRefl_apply]
    exact (congrArg Subtype.val (ht v)).symm

private noncomputable def ggQ2gc_T' (D : GGQ2WDatum 3) (T : D.V ≃ₗ[ZMod 3] D.V)
    (hT : T ∈ Subgroup.normalizer (D.weyl : Set (D.V ≃ₗ[ZMod 3] D.V))) :
    D.corootSpan ≃ₗ[ZMod 3] D.corootSpan :=
  LinearEquiv.ofSubmodules T D.corootSpan D.corootSpan (ggQ2gc_map_eq D T hT)

private theorem ggQ2gc_T'_apply (D : GGQ2WDatum 3) (T : D.V ≃ₗ[ZMod 3] D.V)
    (hT : T ∈ Subgroup.normalizer (D.weyl : Set (D.V ≃ₗ[ZMod 3] D.V))) (x : D.corootSpan) :
    ((ggQ2gc_T' D T hT x : D.corootSpan) : D.V) = T x :=
  LinearEquiv.ofSubmodules_apply T (ggQ2gc_map_eq D T hT) x

private theorem ggQ2gc_T'_inv_apply (D : GGQ2WDatum 3) (T : D.V ≃ₗ[ZMod 3] D.V)
    (hT : T ∈ Subgroup.normalizer (D.weyl : Set (D.V ≃ₗ[ZMod 3] D.V))) (x : D.corootSpan) :
    (((ggQ2gc_T' D T hT)⁻¹ x : D.corootSpan) : D.V) = T⁻¹ x :=
  LinearEquiv.ofSubmodules_symm_apply (e := T) (ggQ2gc_map_eq D T hT) x

private theorem ggQ2gc_T'_conj (D : GGQ2WDatum 3) (T : D.V ≃ₗ[ZMod 3] D.V)
    (hT : T ∈ Subgroup.normalizer (D.weyl : Set (D.V ≃ₗ[ZMod 3] D.V))) (g : D.weyl) :
    ggQ2gc_T' D T hT * ggQ2gc_res D g * (ggQ2gc_T' D T hT)⁻¹ =
      ggQ2gc_res D ⟨T * g.1 * T⁻¹, (Subgroup.mem_normalizer_iff.mp hT _).mp g.2⟩ := by
  apply LinearEquiv.ext
  intro v
  apply Subtype.ext
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, ggQ2gc_T'_apply,
    ggQ2gc_res_apply, ggQ2gc_T'_inv_apply]
  rfl

private theorem ggQ2gc_T'_inv_conj (D : GGQ2WDatum 3) (T : D.V ≃ₗ[ZMod 3] D.V)
    (hT : T ∈ Subgroup.normalizer (D.weyl : Set (D.V ≃ₗ[ZMod 3] D.V))) (g : D.weyl) :
    (ggQ2gc_T' D T hT)⁻¹ * ggQ2gc_res D g * ggQ2gc_T' D T hT =
      ggQ2gc_res D ⟨T⁻¹ * g.1 * T, (Subgroup.mem_normalizer_iff''.mp hT _).mp g.2⟩ := by
  apply LinearEquiv.ext
  intro v
  apply Subtype.ext
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, ggQ2gc_T'_inv_apply,
    ggQ2gc_res_apply, ggQ2gc_T'_apply]
  rfl

private theorem ggQ2gc_lift (D : GGQ2WDatum 3) {n : ℕ} (e : Fin n ≃ D.Λ) {xV : D.V}
    (hfix : ∀ v : D.V, (∀ g ∈ D.weyl, g v = v) ↔ v ∈ Submodule.span (ZMod 3) {xV})
    {t' : D.corootSpan ≃ₗ[ZMod 3] D.corootSpan}
    (ht' : t' ∈ ggQ2WeylOf (ggQ2gc_h' D e) (ggQ2gc_α' D e)) :
    ∃ g ∈ D.weyl, g xV = xV ∧ ∀ u : D.corootSpan, g (u : D.V) = (t' u : D.V) := by
  rw [← ggQ2gc_range_res D e] at ht'
  obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp ht'
  refine ⟨g, g.2, ?_, ?_⟩
  · exact (hfix xV).mpr (Submodule.subset_span (Set.mem_singleton xV)) g g.2
  · intro u
    rw [← hg]
    exact (ggQ2gc_res_apply D g (u : D.V) u.2).symm

private theorem ggQ2gc_models_of_reindex {n : ℕ} {Λ : Type} {C₀ : Matrix (Fin n) (Fin n) ℤ}
    (e : Fin n ≃ Λ) {C : Matrix Λ Λ ℤ}
    (h : C = Matrix.reindex e e C₀ ∨ C = (Matrix.reindex e e C₀).transpose) :
    (∀ i j, C (e i) (e j) = C₀ i j) ∨ (∀ i j, C (e i) (e j) = C₀ j i) := by
  rcases h with h | h
  · left
    intro i j
    simp only [h, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  · right
    intro i j
    simp only [h, Matrix.transpose_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.symm_apply_apply]

private theorem ggQ2gc_F4_rev (i j : Fin 4) :
    CartanMatrix.F₄ (Fin.rev j) (Fin.rev i) = CartanMatrix.F₄ i j := by
  fin_cases i <;> fin_cases j <;> decide

theorem ggQ2GraphLinCore_of_abs (D : GGQ2WDatum 3) {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ)
    (e : Fin n ≃ D.Λ) (hC : ∀ i j, D.cartan (e i) (e j) = C i j) (hcore : GGQ2GraphAbsCore n C) :
    GGQ2GraphLinCore D := by
  classical
  intro xV hxV0 hfix hind hxH hsup E hxE hE2 A hAE hTF h4A hI1 hTBC T hT
  let U₀ := D.corootSpan
  let h' : Fin n → U₀ := ggQ2gc_h' D e
  let α' : Fin n → Module.Dual (ZMod 3) U₀ := ggQ2gc_α' D e
  have hP' : ∀ i j, α' i (h' j) = ((C i j : ℤ) : ZMod 3) := fun i j =>
    ggQ2gc_α'_h' D e C hC i j
  have hli' : LinearIndependent (ZMod 3) h' := ggQ2gc_h'_li D e hind
  have hsp' : Submodule.span (ZMod 3) (Set.range h') = ⊤ := ggQ2gc_h'_span D e hind
  have hVfin : Module.Finite (ZMod 3) D.V := by
    have hU0fin : Module.Finite (ZMod 3) D.corootSpan :=
      Module.Finite.span_of_finite (ZMod 3) (Set.finite_range D.coroot)
    have hxfin : Module.Finite (ZMod 3) (Submodule.span (ZMod 3) {xV}) :=
      Module.Finite.span_of_finite (ZMod 3) (Set.finite_singleton xV)
    have hfg : (⊤ : Submodule (ZMod 3) D.V).FG := by
      rw [← hsup]
      exact Submodule.FG.sup (Submodule.FG.of_finite) (Submodule.FG.of_finite)
    exact Module.Finite.of_fg_top hfg
  have hU0finrank : Module.finrank (ZMod 3) U₀ = n := by
    have h := finrank_span_eq_card hli'
    rw [hsp', finrank_top] at h
    simpa using h
  have hxVspan : Module.finrank (ZMod 3) (Submodule.span (ZMod 3) {xV}) = 1 :=
    finrank_span_singleton hxV0
  have hdisj : U₀ ⊓ Submodule.span (ZMod 3) {xV} = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    obtain ⟨hvU, hvx⟩ := Submodule.mem_inf.mp hv
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hvx
    by_cases ha0 : a = 0
    · rw [ha0, zero_smul] at ha
      exact ha.symm
    · exfalso
      apply hxH
      have hx : xV = a⁻¹ • v := by rw [← ha, smul_smul, inv_mul_cancel₀ ha0, one_smul]
      rw [hx]
      exact Submodule.smul_mem _ _ hvU
  have hcompl : IsCompl U₀ (Submodule.span (ZMod 3) {xV}) :=
    isCompl_iff.mpr ⟨disjoint_iff.mpr hdisj, codisjoint_iff.mpr hsup⟩
  let π : D.V →ₗ[ZMod 3] U₀ := Submodule.projectionOnto U₀ (Submodule.span (ZMod 3) {xV}) hcompl
  have hπU : ∀ u : U₀, π (u : D.V) = u := fun u =>
    Submodule.projectionOnto_apply_left hcompl u
  have hπx : π xV = 0 :=
    Submodule.projectionOnto_apply_of_mem_right hcompl (Submodule.subset_span (Set.mem_singleton xV))
  have hπker : ∀ v : D.V, v - π v ∈ Submodule.span (ZMod 3) {xV} := by
    intro v
    rw [← Submodule.ker_projectionOnto hcompl]
    refine LinearMap.mem_ker.mpr ?_
    rw [map_sub, hπU (π v), sub_self]
  have hVdim : Module.finrank (ZMod 3) D.V = n + 1 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (K := ZMod 3) U₀
      (Submodule.span (ZMod 3) {xV})
    rw [hsup, finrank_top, hdisj, finrank_bot, hU0finrank, hxVspan] at h
    omega
  have hsupE : U₀ ⊔ E = ⊤ := by
    rw [eq_top_iff]
    calc ⊤ = U₀ ⊔ Submodule.span (ZMod 3) {xV} := hsup.symm
      _ ≤ U₀ ⊔ E :=
        sup_le_sup le_rfl (Submodule.span_singleton_le_iff_mem xV E |>.mpr hxE)
  have hdim_inf : Module.finrank (ZMod 3) ↥(U₀ ⊓ E) = 1 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (K := ZMod 3) U₀ E
    rw [hsupE, finrank_top, hU0finrank, hE2, hVdim] at h
    omega
  have hne : U₀ ⊓ E ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hdim_inf
    omega
  obtain ⟨d, hdmem, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hdU0 : d ∈ U₀ := hdmem.1
  have hdE : d ∈ E := hdmem.2
  let d' : U₀ := ⟨d, hdU0⟩
  have hd'0 : d' ≠ 0 := fun h => hd0 (congrArg Subtype.val h)
  have hd_notin : d ∉ Submodule.span (ZMod 3) {xV} := by
    intro hdS
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hdS
    by_cases ha0 : a = 0
    · rw [ha0, zero_smul] at ha
      exact hd0 ha.symm
    · apply hxH
      have hx : xV = a⁻¹ • d := by rw [← ha, smul_smul, inv_mul_cancel₀ ha0, one_smul]
      rw [hx]
      exact Submodule.smul_mem _ _ hdU0
  have hfin2 : Module.finrank (ZMod 3) ↥(Submodule.span (ZMod 3) {xV} ⊔
      Submodule.span (ZMod 3) {d}) = 2 := by
    rw [Submodule.finrank_sup_span_singleton (p := Submodule.span (ZMod 3) {xV}) hd_notin,
      hxVspan]
  have hle : Submodule.span (ZMod 3) {xV} ⊔ Submodule.span (ZMod 3) {d} ≤ E := by
    refine sup_le ?_ ?_
    · exact Submodule.span_singleton_le_iff_mem xV E |>.mpr hxE
    · exact Submodule.span_singleton_le_iff_mem d E |>.mpr hdE
  have hE : E = Submodule.span (ZMod 3) {xV} ⊔ Submodule.span (ZMod 3) {d} := by
    refine (Submodule.eq_of_le_of_finrank_eq (S₁ := _) (S₂ := E) hle ?_).symm
    rw [hfin2, hE2]
  rcases hcore h' hli' hsp' α' hP' d' hd'0 with hkill | hline
  ·
    obtain ⟨ι, hneι, c', f', hfc', hrefl', hfd', hconn', hfix', hdim'⟩ := hkill
    have : Nonempty ι := hneι
    let c : ι → D.V := fun i => (c' i : D.V)
    let f : ι → Module.Dual (ZMod 3) D.V := fun i => (f' i).comp π
    have hfc_apply : ∀ i j, f i (c j) = f' i (c' j) := by
      intro i j
      simp [f, c, π]
    have hfc : ∀ i, f i (c i) = 2 := fun i => by
      rw [hfc_apply i i]
      exact hfc' i
    have hfx : ∀ i, f i xV = 0 := by
      intro i
      show f' i (π xV) = 0
      rw [hπx, map_zero]
    have hfd : ∀ i, f i d = 0 := by
      intro i
      have hπd : π d = d' := hπU d'
      show f' i (π d) = 0
      rw [hπd]
      exact hfd' i
    have hspan_c : Submodule.span (ZMod 3) (Set.range c) =
        Submodule.map U₀.subtype (Submodule.span (ZMod 3) (Set.range c')) := by
      rw [Submodule.map_span]
      congr 1
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨c' i, ⟨i, rfl⟩, rfl⟩
      · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
    have hspan_d : Submodule.map U₀.subtype (Submodule.span (ZMod 3) {d'}) =
        Submodule.span (ZMod 3) {d} := by
      rw [Submodule.map_span, Set.image_singleton]
      rfl
    have hfixV : ∀ v : D.V, (∀ i, f i v = 0) → v ∈ E := by
      intro v hv
      have hπv : π v ∈ Submodule.span (ZMod 3) {d'} := hfix' (π v) (fun i => hv i)
      obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp hπv
      have hπv' : (π v : D.V) = μ • d := by
        rw [← hμ]
        simp [d']
      rw [hE, ← sub_add_cancel v (π v : D.V)]
      refine Submodule.add_mem _ ?_ ?_
      · exact Submodule.mem_sup_left (hπker v)
      · rw [hπv']
        exact Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.subset_span rfl))
    have hconnV : ∀ S : Set ι, S.Nonempty →
        (∀ i j, (f i (c j) ≠ 0 ∨ f j (c i) ≠ 0) → (i ∈ S ↔ j ∈ S)) → S = Set.univ := by
      intro S hS h
      refine hconn' S hS ?_
      intro i j hij
      exact h i j (by simpa only [← hfc_apply i j, ← hfc_apply j i] using hij)
    have ht_fix : ∀ i, ∀ v ∈ E, Module.reflection (hfc i) v = v := by
      intro i v hv
      rw [hE] at hv
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
      rw [map_add]
      congr 1
      · obtain ⟨μ, rfl⟩ := Submodule.mem_span_singleton.mp ha
        rw [map_smul, Module.reflection_apply, hfx i, zero_smul, sub_zero]
      · obtain ⟨μ, rfl⟩ := Submodule.mem_span_singleton.mp hb
        rw [map_smul, Module.reflection_apply, hfd i, zero_smul, sub_zero]
    have hlift : ∀ i, ∃ g ∈ D.weyl, g = Module.reflection (hfc i) := by
      intro i
      obtain ⟨g, hgW, hgx, hgu⟩ := ggQ2gc_lift D e hfix (hrefl' i)
      refine ⟨g, hgW, ?_⟩
      have hEqU : Set.EqOn (g : D.V → D.V) (Module.reflection (hfc i) : D.V → D.V)
          (U₀ : Set D.V) := by
        intro u hu
        have h1 : g u = ((Module.reflection (hfc' i)) ⟨u, hu⟩ : D.V) := hgu ⟨u, hu⟩
        have h2 : ((Module.reflection (hfc' i)) ⟨u, hu⟩ : D.V) =
            u - f' i ⟨u, hu⟩ • (c' i : D.V) := by
          have := congrArg Subtype.val
            (Module.reflection_apply (h := hfc' i) (⟨u, hu⟩ : D.corootSpan))
          simpa using this
        have h3 : Module.reflection (hfc i) u = u - f' i ⟨u, hu⟩ • (c' i : D.V) := by
          rw [Module.reflection_apply]
          have hf : f i u = f' i ⟨u, hu⟩ := by
            show f' i (π u) = f' i ⟨u, hu⟩
            rw [hπU ⟨u, hu⟩]
          rw [hf]
        rw [h1, h2, h3]
      have hEqX : Set.EqOn (g : D.V → D.V) (Module.reflection (hfc i) : D.V → D.V)
          (Submodule.span (ZMod 3) {xV} : Set D.V) := by
        intro w hw
        obtain ⟨μ, rfl⟩ := Submodule.mem_span_singleton.mp hw
        rw [map_smul, map_smul, hgx, Module.reflection_apply, hfx i, zero_smul, sub_zero]
      have hEq : (g : D.V →ₗ[ZMod 3] D.V) =
          (Module.reflection (hfc i) : D.V →ₗ[ZMod 3] D.V) :=
        LinearMap.ext_on_codisjoint (codisjoint_iff.mpr hsup) hEqU hEqX
      exact LinearEquiv.ext fun v =>
        congrArg (fun (f : D.V →ₗ[ZMod 3] D.V) => f v) hEq
    have hTBCV : ∀ i, Module.reflection (hfc i) ∈ A ∨
        ∀ a ∈ A, Module.reflection (hfc i) * a = a * Module.reflection (hfc i) := by
      intro i
      obtain ⟨g, hgW, hgeq⟩ := hlift i
      have hIsRefl : IsReflLin g := hgeq ▸ ⟨c i, f i, hfc i, rfl⟩
      have hFixE : ∀ v ∈ E, g v = v := hgeq ▸ ht_fix i
      rcases hTBC g hgW hIsRefl hFixE with hA | hcomm
      · left
        rwa [← hgeq]
      · right
        intro a ha
        rw [← hgeq]
        exact hcomm a ha
    have hdimV : Submodule.span (ZMod 3) (Set.range c) ⊔ E = ⊤ ∨
        (Submodule.span (ZMod 3) (Set.range c) ⊓ E ≠ ⊥ ∧
          Module.finrank (ZMod 3) ↥(Submodule.span (ZMod 3) (Set.range c) ⊔ E) + 1 =
            Module.finrank (ZMod 3) D.V) := by
      rcases hdim' with htop | ⟨hdspan, hfr⟩
      · left
        have hmap : Submodule.span (ZMod 3) (Set.range c) ⊔
            Submodule.span (ZMod 3) {d} = U₀ := by
          have h := congrArg (Submodule.map U₀.subtype) htop
          rw [Submodule.map_sup, Submodule.map_top, Submodule.range_subtype,
            ← hspan_c, hspan_d] at h
          exact h
        rw [hE]
        calc Submodule.span (ZMod 3) (Set.range c) ⊔
              (Submodule.span (ZMod 3) {xV} ⊔ Submodule.span (ZMod 3) {d})
            = (Submodule.span (ZMod 3) (Set.range c) ⊔ Submodule.span (ZMod 3) {d}) ⊔
                Submodule.span (ZMod 3) {xV} := by
              rw [sup_comm (Submodule.span (ZMod 3) {xV}) (Submodule.span (ZMod 3) {d}),
                ← sup_assoc]
          _ = U₀ ⊔ Submodule.span (ZMod 3) {xV} := by rw [hmap]
          _ = ⊤ := hsup
      · right
        have hdspanV : Submodule.span (ZMod 3) {d} ≤ Submodule.span (ZMod 3) (Set.range c) :=
          Submodule.span_singleton_le_iff_mem d _ |>.mpr (by
            have h : d ∈ Submodule.map U₀.subtype (Submodule.span (ZMod 3) (Set.range c')) :=
              Submodule.mem_map.mpr ⟨d', hdspan, rfl⟩
            rwa [← hspan_c] at h)
        have hdinf : Submodule.span (ZMod 3) (Set.range c) ⊓ E ≠ ⊥ := by
          intro hbot
          have hdmem : d ∈ Submodule.span (ZMod 3) (Set.range c) ⊓ E :=
            ⟨hdspanV (Submodule.subset_span rfl), hdE⟩
          rw [hbot] at hdmem
          exact hd0 (by simpa using hdmem)
        have hfin_span : Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range c)) + 1 = n := by
          have hfr' : Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range c)) =
              Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range c')) := by
            rw [hspan_c]
            exact Submodule.finrank_map_subtype_eq U₀ (Submodule.span (ZMod 3) (Set.range c'))
          rw [hfr', ← hU0finrank]
          exact hfr
        have hxV_notin : xV ∉ Submodule.span (ZMod 3) (Set.range c) := by
          intro hx
          apply hxH
          have hle' : Submodule.span (ZMod 3) (Set.range c) ≤ U₀ := by
            rw [hspan_c]
            exact Submodule.map_subtype_le (p := U₀) (Submodule.span (ZMod 3) (Set.range c'))
          exact hle' hx
        have hspan_sup : Submodule.span (ZMod 3) (Set.range c) ⊔ E =
            Submodule.span (ZMod 3) (Set.range c) ⊔ Submodule.span (ZMod 3) {xV} := by
          rw [hE, sup_comm (Submodule.span (ZMod 3) {xV}) (Submodule.span (ZMod 3) {d}),
            ← sup_assoc, sup_eq_left.mpr hdspanV]
        have hfinV : Module.finrank (ZMod 3) ↥(Submodule.span (ZMod 3) (Set.range c) ⊔ E) + 1 =
            Module.finrank (ZMod 3) D.V := by
          rw [hspan_sup, Submodule.finrank_sup_span_singleton (p :=
            Submodule.span (ZMod 3) (Set.range c)) hxV_notin, hfin_span, hVdim]
        exact ⟨hdinf, hfinV⟩
    exact (ggQ2_reflKill_three E A hAE hTF c f hfc hconnV hfixV hdimV hTBCV hI1 h4A).elim
  ·
    let T' : U₀ ≃ₗ[ZMod 3] U₀ := ggQ2gc_T' D T hT
    have hT'apply : ∀ x : U₀, (T' x : D.V) = T x := fun x => ggQ2gc_T'_apply D T hT x
    have hT'norm : T' ∈ Subgroup.normalizer (ggQ2WeylOf h' α' : Set (U₀ ≃ₗ[ZMod 3] U₀)) := by
      rw [← ggQ2gc_range_res D e, Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · intro hy
        rcases MonoidHom.mem_range.mp hy with ⟨g, hg⟩
        refine MonoidHom.mem_range.mpr ⟨⟨T * g.1 * T⁻¹,
          (Subgroup.mem_normalizer_iff.mp hT g.1).mp g.2⟩, ?_⟩
        rw [← hg]
        exact (ggQ2gc_T'_conj D T hT g).symm
      · intro hy
        rcases MonoidHom.mem_range.mp hy with ⟨g, hg⟩
        refine MonoidHom.mem_range.mpr ⟨⟨T⁻¹ * g.1 * T,
          (Subgroup.mem_normalizer_iff''.mp hT g.1).mp g.2⟩, ?_⟩
        have h1 : T'⁻¹ * ggQ2gc_res D g * T' = y := by
          rw [hg]; group
        rw [← h1]
        exact (ggQ2gc_T'_inv_conj D T hT g).symm
    obtain ⟨u', hu'mem, hu'd'⟩ := hline T' hT'norm
    obtain ⟨g, hgW, hgx, hgu⟩ := ggQ2gc_lift D e hfix hu'mem
    refine ⟨g, hgW, ?_⟩
    have hTxV : T xV ∈ Submodule.span (ZMod 3) {xV} := by
      refine (hfix (T xV)).mp ?_
      intro w hw
      have hTw : T⁻¹ * w * T ∈ D.weyl := (Subgroup.mem_normalizer_iff''.mp hT w).mp hw
      have h1 : (T⁻¹ * w * T) xV = xV :=
        (hfix xV).mpr (Submodule.subset_span (Set.mem_singleton xV)) _ hTw
      have h2 : T ((T⁻¹ * w * T) xV) = T xV := by rw [h1]
      simpa [LinearEquiv.mul_apply] using h2
    have hTgd : T (g d) ∈ Submodule.span (ZMod 3) {d} := by
      have hgd : g d = (u' d' : D.V) := hgu d'
      have hmem : (T' (u' d') : D.V) ∈
          Submodule.map U₀.subtype (Submodule.span (ZMod 3) {d'}) :=
        Submodule.mem_map.mpr ⟨T' (u' d'), hu'd', rfl⟩
      have hspan_d : Submodule.map U₀.subtype (Submodule.span (ZMod 3) {d'}) =
          Submodule.span (ZMod 3) {d} := by
        rw [Submodule.map_span, Set.image_singleton]
        rfl
      rw [hgd, ← hT'apply (u' d'), ← hspan_d]
      exact hmem
    intro v hv
    rw [hE] at hv
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
    rw [hE, map_add, map_add]
    refine Submodule.add_mem _ ?_ ?_
    · obtain ⟨μ, rfl⟩ := Submodule.mem_span_singleton.mp ha
      rw [map_smul, map_smul, hgx]
      exact Submodule.mem_sup_left (Submodule.smul_mem _ _ hTxV)
    · obtain ⟨μ, rfl⟩ := Submodule.mem_span_singleton.mp hb
      rw [map_smul, map_smul]
      exact Submodule.mem_sup_right (Submodule.smul_mem _ _ hTgd)

theorem ggQ2GraphCoreAll_of_abs (hD : ∀ n, 5 ≤ n → GGQ2GraphAbsCore n (CartanMatrix.D n))
    (hD4 : GGQ2GraphAbsCore 4 (CartanMatrix.D 4)) (hF4 : GGQ2GraphAbsCore 4 CartanMatrix.F₄) :
    GGQ2GraphCoreAll := by
  intro D lab hlab htag hW
  rcases htag with htag | htag
  ·
    have hDlab : Even lab.rank ∧ 4 ≤ lab.rank := by
      unfold GGQ2TBLabel at hlab
      rcases hlab with ⟨h, h4⟩ | ⟨h, h4⟩ | ⟨h, he, h4⟩ | ⟨h, h4⟩ | h | h | h | h
      · rw [htag] at h; exact absurd h (by decide)
      · rcases h with h | h <;> (rw [htag] at h; exact absurd h (by decide))
      · exact ⟨he, h4⟩
      · rw [htag] at h; exact absurd h (by decide)
      · rw [htag] at h; exact absurd h (by decide)
      · rw [htag] at h; exact absurd h (by decide)
      · rw [htag] at h; exact absurd h (by decide)
      · rw [htag] at h; exact absurd h (by decide)
    simp only [GGQ2LabelWeyl, htag] at hW
    obtain ⟨e, hcox⟩ := hW
    have hcart : ∀ i j, D.cartan (e i) (e j) = CartanMatrix.D lab.rank i j := by
      have hC := D.isCartan
      rw [hcox] at hC
      rcases ggQ2gc_models_of_reindex (C₀ := CartanMatrix.D lab.rank) e
        (hC.eq_or_eq_transpose ((ggIntCartan_D lab.rank).reindex e)
          ((ggAtMostOneMultipleEdge_D lab.rank).reindex e)) with h | h
      · exact h
      · intro i j
        exact (h i j).trans (congrFun (congrFun (CartanMatrix.D_transpose lab.rank) i) j)
    by_cases h4 : lab.rank = 4
    · exact ggQ2GraphLinCore_of_abs D (CartanMatrix.D lab.rank) e hcart (h4.symm ▸ hD4)
    · have h5 : 5 ≤ lab.rank := by omega
      exact ggQ2GraphLinCore_of_abs D (CartanMatrix.D lab.rank) e hcart (hD lab.rank h5)
  ·
    simp only [GGQ2LabelWeyl, htag] at hW
    obtain ⟨e, hcox⟩ := hW
    have hC := D.isCartan
    rw [hcox] at hC
    rcases ggQ2gc_models_of_reindex (C₀ := CartanMatrix.F₄) e
      (hC.eq_or_eq_transpose (ggIntCartan_F₄.reindex e)
        (ggAtMostOneMultipleEdge_F₄.reindex e)) with h | h
    · exact ggQ2GraphLinCore_of_abs D CartanMatrix.F₄ e h hF4
    · refine ggQ2GraphLinCore_of_abs D CartanMatrix.F₄ (Fin.revPerm.trans e) ?_ hF4
      intro i j
      have h1 := h (Fin.rev i) (Fin.rev j)
      simp only [Equiv.trans_apply, Fin.revPerm_apply]
      rw [h1, ggQ2gc_F4_rev]

end CFSG.StandardType

end
