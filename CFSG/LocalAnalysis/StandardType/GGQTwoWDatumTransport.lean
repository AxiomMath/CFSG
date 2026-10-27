module

public import CFSG.LocalAnalysis.StandardType.GGQTwoWDatumK

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGQ2WDatum.corootSpan (D : GGQ2WDatum 3) : Submodule (ZMod 3) D.V :=
  Submodule.span (ZMod 3) (Set.range D.coroot)

private theorem ggQ2wdt_sub_mem (D : GGQ2WDatum 3) (g : D.V ≃ₗ[ZMod 3] D.V) (hg : g ∈ D.weyl)
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

private theorem ggQ2wdt_conj_coroot_mem (D : GGQ2WDatum 3) (S : D.V ≃ₗ[ZMod 3] D.V)
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
    ggQ2wdt_sub_mem D _ (hS j) (S v0)
  have hkey : (S * D.simpleRefl j * S⁻¹) (S v0) = S (D.simpleRefl j v0) := by
    simp [LinearEquiv.mul_apply]
  have heq : S (D.coroot j) = S v0 - (S * D.simpleRefl j * S⁻¹) (S v0) := by
    rw [hkey, ← map_sub, hvr]
  rw [heq]
  simpa only [neg_sub] using Submodule.neg_mem _ hmem

private theorem ggQ2wdt_map_le (D : GGQ2WDatum 3) (S : D.V ≃ₗ[ZMod 3] D.V)
    (hS : ∀ j : D.Λ, S * D.simpleRefl j * S⁻¹ ∈ D.weyl) :
    D.corootSpan.map (S : D.V →ₗ[ZMod 3] D.V) ≤ D.corootSpan := by
  rw [Submodule.map_le_iff_le_comap, GGQ2WDatum.corootSpan, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  exact ggQ2wdt_conj_coroot_mem D S hS j

private theorem ggQ2wdt_map_eq (D : GGQ2WDatum 3) (S : D.V ≃ₗ[ZMod 3] D.V)
    (hS : S ∈ Subgroup.normalizer (D.weyl : Set (D.V ≃ₗ[ZMod 3] D.V))) :
    D.corootSpan.map (S : D.V →ₗ[ZMod 3] D.V) = D.corootSpan := by
  have hconj : ∀ j : D.Λ, S * D.simpleRefl j * S⁻¹ ∈ D.weyl := fun j =>
    (Subgroup.mem_normalizer_iff.mp hS _).mp (D.simpleRefl_mem_weyl j)
  have hconj' : ∀ j : D.Λ, S⁻¹ * D.simpleRefl j * S ∈ D.weyl := fun j =>
    (Subgroup.mem_normalizer_iff''.mp hS _).mp (D.simpleRefl_mem_weyl j)
  refine le_antisymm (ggQ2wdt_map_le D S hconj) ?_
  intro u hu
  have hmem : S⁻¹ u ∈ D.corootSpan :=
    ggQ2wdt_map_le D S⁻¹ (by simpa using hconj') ⟨u, hu, rfl⟩
  exact ⟨S⁻¹ u, hmem, by simp⟩

private noncomputable def ggQ2wdt_res (D : GGQ2WDatum 3) :
    D.weyl →* (D.corootSpan ≃ₗ[ZMod 3] D.corootSpan) where
  toFun g := LinearEquiv.ofSubmodules (g.1 : D.V ≃ₗ[ZMod 3] D.V) D.corootSpan D.corootSpan
    (ggQ2wdt_map_eq D g.1 (Subgroup.le_normalizer g.2))
  map_one' := by ext; rfl
  map_mul' g h := by ext; rfl

private theorem ggQ2wdt_res_apply (D : GGQ2WDatum 3) (g : D.weyl) (v : D.V)
    (hv : v ∈ D.corootSpan) : ((ggQ2wdt_res D g) ⟨v, hv⟩ : D.V) = g.1 v :=
  LinearEquiv.ofSubmodules_apply (g.1 : D.V ≃ₗ[ZMod 3] D.V)
    (ggQ2wdt_map_eq D g.1 (Subgroup.le_normalizer g.2)) ⟨v, hv⟩

private def ggQ2wdt_h' (D : GGQ2WDatum 3) {n : ℕ} (e : Fin n ≃ D.Λ) : Fin n → D.corootSpan :=
  fun i => ⟨D.coroot (e i), Submodule.subset_span ⟨e i, rfl⟩⟩

private def ggQ2wdt_α' (D : GGQ2WDatum 3) {n : ℕ} (e : Fin n ≃ D.Λ) :
    Fin n → Module.Dual (ZMod 3) D.corootSpan :=
  fun i => (D.root (e i)).comp D.corootSpan.subtype

private theorem ggQ2wdt_α'_h' (D : GGQ2WDatum 3) {n : ℕ} (e : Fin n ≃ D.Λ)
    (C : Matrix (Fin n) (Fin n) ℤ) (hC : ∀ i j, D.cartan (e i) (e j) = C i j) (i j : Fin n) :
    ggQ2wdt_α' D e i (ggQ2wdt_h' D e j) = ((C i j : ℤ) : ZMod 3) := by
  show D.root (e i) (D.coroot (e j)) = _
  rw [D.pairing, hC i j]

private theorem ggQ2wdt_h'_li (D : GGQ2WDatum 3) {n : ℕ} (e : Fin n ≃ D.Λ)
    (hind : LinearIndependent (ZMod 3) D.coroot) :
    LinearIndependent (ZMod 3) (ggQ2wdt_h' D e) := by
  have h0 := linearIndependent_span (R := ZMod 3) (v := D.coroot) hind
  have h := h0.comp e e.injective
  change LinearIndependent (ZMod 3) (fun i => (⟨D.coroot (e i), _⟩ : D.corootSpan))
  exact h

private theorem ggQ2wdt_h'_span (D : GGQ2WDatum 3) {n : ℕ} (e : Fin n ≃ D.Λ)
    (hind : LinearIndependent (ZMod 3) D.coroot) :
    Submodule.span (ZMod 3) (Set.range (ggQ2wdt_h' D e)) = ⊤ := by
  have : Module.Finite (ZMod 3) D.corootSpan :=
    Module.Finite.span_of_finite (ZMod 3) (Set.finite_range _)
  obtain ⟨j0⟩ := D.nonempty
  have : Nonempty (Fin n) := ⟨e.symm j0⟩
  refine LinearIndependent.span_eq_top_of_card_eq_finrank (ggQ2wdt_h'_li D e hind) ?_
  rw [GGQ2WDatum.corootSpan, finrank_span_eq_card hind]
  exact Fintype.card_congr e

private theorem ggQ2wdt_intCartan (D : GGQ2WDatum 3) {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℤ) (e : Fin n ≃ D.Λ)
    (M : CoxeterMatrix (Fin n)) (hM : ∀ i j, M i j = D.coxeter (e i) (e j))
    (hC : ∀ i j, D.cartan (e i) (e j) = C i j) :
    GGIntCartan M C := by
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · rw [← hC i i, D.isCartan.1]
  · have hij' : e i ≠ e j := fun h => hij (e.injective h)
    have h := D.isCartan.2 (e i) (e j) hij'
    rw [show C i j = D.cartan (e i) (e j) from (hC i j).symm,
      show C j i = D.cartan (e j) (e i) from (hC j i).symm]
    simpa [hM] using h

private theorem ggQ2wdt_isFiniteType (D : GGQ2WDatum 3) {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℤ) (e : Fin n ≃ D.Λ)
    (hC : ∀ i j, D.cartan (e i) (e j) = C i j) : TauCeti.IsFiniteType C := by
  have hFTV : TauCeti.IsFiniteType D.cartan :=
    isFiniteType_of_ggIsWeylMatrixFixed D.isWeyl D.isCartan
  have heq : C = D.cartan.submatrix e e := by
    ext i j; exact (hC i j).symm
  rw [heq]
  exact hFTV.submatrix (e := e) e.injective

private theorem ggQ2wdt_closure_range_top (D : GGQ2WDatum 3) {n : ℕ} (e : Fin n ≃ D.Λ) :
    Subgroup.closure (Set.range (fun i : Fin n =>
      (⟨D.simpleRefl (e i), D.simpleRefl_mem_weyl (e i)⟩ : D.weyl))) = ⊤ := by
  let W := D.weyl
  let S : Set W := Set.range (fun i : Fin n =>
    (⟨D.simpleRefl (e i), D.simpleRefl_mem_weyl (e i)⟩ : W))
  have himg : W.subtype '' S = Set.range D.simpleRefl := by
    ext x; constructor
    · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
      exact ⟨e i, rfl⟩
    · rintro ⟨k, rfl⟩
      refine ⟨⟨D.simpleRefl (e (e.symm k)), D.simpleRefl_mem_weyl _⟩, ⟨e.symm k, rfl⟩, ?_⟩
      simp
  have hmap : Subgroup.map W.subtype (Subgroup.closure S) = W := by
    rw [MonoidHom.map_closure, himg]
    rfl
  have hmap' : Subgroup.map W.subtype (Subgroup.closure S) =
      Subgroup.map W.subtype (⊤ : Subgroup W) := by
    rw [hmap]
    rw [← Subgroup.subgroupOf_self (H := W), Subgroup.map_subgroupOf_eq_of_le le_rfl]
  exact Subgroup.map_subtype_inj.mp hmap'

private theorem ggQ2wdt_res_injective (D : GGQ2WDatum 3) {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℤ) (e : Fin n ≃ D.Λ)
    (hC : ∀ i j, D.cartan (e i) (e j) = C i j)
    (hind : LinearIndependent (ZMod 3) D.coroot) :
    Function.Injective (ggQ2wdt_res D) := by
  classical
  let M : CoxeterMatrix (Fin n) :=
    CoxeterMatrix.mk (Matrix.of fun i j => D.coxeter (e i) (e j))
      (Matrix.IsSymm.ext fun i j => (D.coxeter.symmetric (e i) (e j)).symm)
      (fun i => D.coxeter.diagonal (e i))
      (fun i j hij h => D.coxeter.off_diagonal (e i) (e j)
        (fun he => hij (e.injective he)) h)
  let h' : Fin n → D.corootSpan := ggQ2wdt_h' D e
  let α' : Fin n → Module.Dual (ZMod 3) D.corootSpan := ggQ2wdt_α' D e
  have hMij : ∀ i j, M i j = D.coxeter (e i) (e j) := fun i j => rfl
  have hC' : GGIntCartan M C := ggQ2wdt_intCartan D C e M hMij hC
  have hFT : TauCeti.IsFiniteType C := ggQ2wdt_isFiniteType D C e hC
  have hind' : LinearIndependent (ZMod 3) h' := ggQ2wdt_h'_li D e hind
  have hP' : ∀ i j, α' i (h' j) = ((C i j : ℤ) : ZMod 3) := fun i j =>
    ggQ2wdt_α'_h' D e C hC i j
  have hCii : ∀ i, C i i = 2 := fun i => by
    rw [← hC i i, D.isCartan.1]
  have hα' : ∀ i, α' i (h' i) = 2 := fun i => by
    rw [hP' i i, hCii i]; norm_num
  have hL' : M.IsLiftable (fun i => Module.reflection (hα' i)) :=
    isLiftable_reflection_of_intCartan hC' h' α' hα' hP'
  let ρ : M.Group →* (D.corootSpan ≃ₗ[ZMod 3] D.corootSpan) :=
    M.toCoxeterSystem.lift ⟨fun i => Module.reflection (hα' i), hL'⟩
  have hinjρ : Function.Injective ρ :=
    ggCartanFaithful_of_isFiniteType (p := 3) (M := M) (C := C) (h := h') (α := α')
      (hα := hα') (hP := hP') (by decide) hFT hC' hind'
  let sV : Fin n → D.V ≃ₗ[ZMod 3] D.V := fun i => Module.reflection
    (show D.root (e i) (D.coroot (e i)) = 2 from D.root_coroot_self (e i))
  have hPV : ∀ i j, D.root (e i) (D.coroot (e j)) = ((C i j : ℤ) : ZMod 3) :=
    fun i j => by rw [D.pairing, hC i j]
  have hαV : ∀ i, D.root (e i) (D.coroot (e i)) = 2 := fun i => D.root_coroot_self (e i)
  have hL : M.IsLiftable sV := by
    simpa [sV, GGQ2WDatum.simpleRefl] using
      isLiftable_reflection_of_intCartan hC' (fun i => D.coroot (e i))
        (fun i => D.root (e i)) hαV hPV
  let sW : Fin n → D.weyl := fun i => ⟨sV i, D.simpleRefl_mem_weyl (e i)⟩
  have hLW : M.IsLiftable sW := by
    intro i j
    apply Subtype.ext
    have h := hL i j
    simpa [sW, sV] using h
  let Ψ : M.Group →* D.weyl := M.toCoxeterSystem.lift ⟨sW, hLW⟩
  have hcomp : (ggQ2wdt_res D).comp Ψ = ρ := by
    refine M.toCoxeterSystem.ext_simple fun i => ?_
    have hΨ : Ψ (M.toCoxeterSystem.simple i) = sW i := by
      simp only [Ψ, CoxeterSystem.lift_apply_simple]
    rw [MonoidHom.comp_apply, hΨ, CoxeterSystem.lift_apply_simple]
    apply LinearEquiv.ext
    intro v
    apply Subtype.ext
    rw [ggQ2wdt_res_apply D (sW i) (v : D.V) v.2]
    show (sV i) (v : D.V) = _
    rw [show sV i = Module.reflection (D.root_coroot_self (e i)) from rfl,
      Module.reflection_apply, Module.reflection_apply]
    rfl
  have hsurj : Function.Surjective Ψ := by
    have hrange : Ψ.range = ⊤ := by
      rw [MonoidHom.range_eq_map, ← M.toCoxeterSystem.subgroup_closure_range_simple,
        MonoidHom.map_closure]
      have himg : Ψ '' Set.range M.toCoxeterSystem.simple = Set.range sW := by
        ext y; constructor
        · rintro ⟨x, ⟨i, rfl⟩, rfl⟩
          exact ⟨i, by rw [CoxeterSystem.lift_apply_simple]⟩
        · rintro ⟨i, rfl⟩
          exact ⟨M.toCoxeterSystem.simple i, ⟨i, rfl⟩, by
            rw [CoxeterSystem.lift_apply_simple]⟩
      rw [himg]
      exact ggQ2wdt_closure_range_top D e
    intro g
    have hg : g ∈ Ψ.range := by rw [hrange]; exact Subgroup.mem_top g
    rwa [MonoidHom.mem_range] at hg
  intro a b hab
  have h1 : ggQ2wdt_res D (a * b⁻¹) = 1 := by
    rw [map_mul, map_inv, hab, mul_inv_cancel]
  obtain ⟨w, hw⟩ := hsurj (a * b⁻¹)
  have hw1 : w = 1 := by
    apply hinjρ
    rw [map_one]
    calc ρ w = (ggQ2wdt_res D).comp Ψ w := by rw [hcomp]
      _ = ggQ2wdt_res D (Ψ w) := rfl
      _ = ggQ2wdt_res D (a * b⁻¹) := by rw [hw]
      _ = 1 := h1
  have h2 : a * b⁻¹ = 1 := by rw [← hw, hw1, map_one]
  have h3 : a * b⁻¹ * b = 1 * b := by rw [h2]
  simpa using h3

private theorem ggQ2wdt_range_res (D : GGQ2WDatum 3) {n : ℕ} (e : Fin n ≃ D.Λ) :
    (ggQ2wdt_res D).range = ggQ2WeylOf (ggQ2wdt_h' D e) (ggQ2wdt_α' D e) := by
  refine le_antisymm ?_ ?_
  · intro y hy
    rw [MonoidHom.mem_range] at hy
    obtain ⟨g, rfl⟩ := hy
    refine Subgroup.closure_induction
      (p := fun g hg => ggQ2wdt_res D ⟨g, hg⟩ ∈
        ggQ2WeylOf (ggQ2wdt_h' D e) (ggQ2wdt_α' D e)) ?_ ?_ ?_ ?_ g.2
    · rintro g ⟨k, rfl⟩
      let i : Fin n := e.symm k
      have hki : e i = k := e.apply_symm_apply _
      refine Subgroup.subset_closure ⟨i, ?_⟩
      intro v
      apply Subtype.ext
      rw [ggQ2wdt_res_apply D _ (v : D.V) v.2, D.simpleRefl_apply]
      simp [ggQ2wdt_α', ggQ2wdt_h', hki]
    · change ggQ2wdt_res D (1 : D.weyl) ∈ ggQ2WeylOf (ggQ2wdt_h' D e) (ggQ2wdt_α' D e)
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
    rw [ggQ2wdt_res_apply D _ (v : D.V) v.2, D.simpleRefl_apply]
    exact (congrArg Subtype.val (ht v)).symm

private noncomputable def ggQ2wdt_T' (D : GGQ2WDatum 3) (T : D.V ≃ₗ[ZMod 3] D.V)
    (hT : T ∈ Subgroup.normalizer (D.weyl : Set (D.V ≃ₗ[ZMod 3] D.V))) :
    D.corootSpan ≃ₗ[ZMod 3] D.corootSpan :=
  LinearEquiv.ofSubmodules T D.corootSpan D.corootSpan (ggQ2wdt_map_eq D T hT)

private theorem ggQ2wdt_T'_apply (D : GGQ2WDatum 3) (T : D.V ≃ₗ[ZMod 3] D.V)
    (hT : T ∈ Subgroup.normalizer (D.weyl : Set (D.V ≃ₗ[ZMod 3] D.V))) (x : D.corootSpan) :
    ((ggQ2wdt_T' D T hT x : D.corootSpan) : D.V) = T x :=
  LinearEquiv.ofSubmodules_apply T (ggQ2wdt_map_eq D T hT) x

private theorem ggQ2wdt_T'_inv_apply (D : GGQ2WDatum 3) (T : D.V ≃ₗ[ZMod 3] D.V)
    (hT : T ∈ Subgroup.normalizer (D.weyl : Set (D.V ≃ₗ[ZMod 3] D.V))) (x : D.corootSpan) :
    (((ggQ2wdt_T' D T hT)⁻¹ x : D.corootSpan) : D.V) = T⁻¹ x :=
  LinearEquiv.ofSubmodules_symm_apply (e := T) (ggQ2wdt_map_eq D T hT) x

private theorem ggQ2wdt_T'_conj (D : GGQ2WDatum 3) (T : D.V ≃ₗ[ZMod 3] D.V)
    (hT : T ∈ Subgroup.normalizer (D.weyl : Set (D.V ≃ₗ[ZMod 3] D.V))) (g : D.weyl) :
    ggQ2wdt_T' D T hT * ggQ2wdt_res D g * (ggQ2wdt_T' D T hT)⁻¹ =
      ggQ2wdt_res D ⟨T * g.1 * T⁻¹, (Subgroup.mem_normalizer_iff.mp hT _).mp g.2⟩ := by
  apply LinearEquiv.ext
  intro v
  apply Subtype.ext
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, ggQ2wdt_T'_apply,
    ggQ2wdt_res_apply, ggQ2wdt_T'_inv_apply]
  rfl

private theorem ggQ2wdt_T'_inv_conj (D : GGQ2WDatum 3) (T : D.V ≃ₗ[ZMod 3] D.V)
    (hT : T ∈ Subgroup.normalizer (D.weyl : Set (D.V ≃ₗ[ZMod 3] D.V))) (g : D.weyl) :
    (ggQ2wdt_T' D T hT)⁻¹ * ggQ2wdt_res D g * ggQ2wdt_T' D T hT =
      ggQ2wdt_res D ⟨T⁻¹ * g.1 * T, (Subgroup.mem_normalizer_iff''.mp hT _).mp g.2⟩ := by
  apply LinearEquiv.ext
  intro v
  apply Subtype.ext
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, ggQ2wdt_T'_inv_apply,
    ggQ2wdt_res_apply, ggQ2wdt_T'_apply]
  rfl

theorem GGQ2WDatum.inner_of_transport (D : GGQ2WDatum 3) {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ)
    (e : Fin n ≃ D.Λ) (hC : ∀ i j, D.cartan (e i) (e j) = C i j)
    (hind : LinearIndependent (ZMod 3) D.coroot) (hW : GGQ2WeylInner n C)
    (T : D.V ≃ₗ[ZMod 3] D.V)
    (hT : T ∈ Subgroup.normalizer (D.weyl : Set (D.V ≃ₗ[ZMod 3] D.V))) :
    ∃ w ∈ D.weyl, ∀ g ∈ D.weyl, T * g * T⁻¹ = w * g * w⁻¹ := by
  classical
  let h' : Fin n → D.corootSpan := ggQ2wdt_h' D e
  let α' : Fin n → Module.Dual (ZMod 3) D.corootSpan := ggQ2wdt_α' D e
  have hP' : ∀ i j, α' i (h' j) = ((C i j : ℤ) : ZMod 3) := fun i j =>
    ggQ2wdt_α'_h' D e C hC i j
  have hli' : LinearIndependent (ZMod 3) h' := ggQ2wdt_h'_li D e hind
  have hsp' : Submodule.span (ZMod 3) (Set.range h') = ⊤ := ggQ2wdt_h'_span D e hind
  have hrange : (ggQ2wdt_res D).range = ggQ2WeylOf h' α' := ggQ2wdt_range_res D e
  let T' : D.corootSpan ≃ₗ[ZMod 3] D.corootSpan := ggQ2wdt_T' D T hT
  have hT'norm : T' ∈ Subgroup.normalizer (ggQ2WeylOf h' α') := by
    rw [← hrange, Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      rcases MonoidHom.mem_range.mp hy with ⟨g, hg⟩
      refine MonoidHom.mem_range.mpr ⟨⟨T * g.1 * T⁻¹,
        (Subgroup.mem_normalizer_iff.mp hT g.1).mp g.2⟩, ?_⟩
      rw [← hg]
      exact (ggQ2wdt_T'_conj D T hT g).symm
    · intro hy
      rcases MonoidHom.mem_range.mp hy with ⟨g, hg⟩
      refine MonoidHom.mem_range.mpr ⟨⟨T⁻¹ * g.1 * T,
        (Subgroup.mem_normalizer_iff''.mp hT g.1).mp g.2⟩, ?_⟩
      have h1 : T'⁻¹ * ggQ2wdt_res D g * T' = y := by
        rw [hg]; group
      rw [← h1]
      exact (ggQ2wdt_T'_inv_conj D T hT g).symm
  obtain ⟨w', hw'mem, hw'conj⟩ := hW h' hli' hsp' α' hP' T' hT'norm
  have hw'range : w' ∈ (ggQ2wdt_res D).range := by rwa [hrange]
  obtain ⟨w, hw_eq⟩ := MonoidHom.mem_range.mp hw'range
  refine ⟨w, w.2, fun g hg => ?_⟩
  set hconjM : T * g * T⁻¹ ∈ D.weyl := (Subgroup.mem_normalizer_iff.mp hT g).mp hg
  set hconjW : w.1 * g * w.1⁻¹ ∈ D.weyl :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ w.2 hg) (Subgroup.inv_mem _ w.2)
  have htarget : (⟨T * g * T⁻¹, hconjM⟩ : D.weyl) = ⟨w.1 * g * w.1⁻¹, hconjW⟩ := by
    apply ggQ2wdt_res_injective D C e hC hind
    have hL : ggQ2wdt_res D ⟨T * g * T⁻¹, hconjM⟩ = T' * ggQ2wdt_res D ⟨g, hg⟩ * T'⁻¹ :=
      ggQ2wdt_T'_conj D T hT ⟨g, hg⟩
    have hR : ggQ2wdt_res D ⟨w.1 * g * w.1⁻¹, hconjW⟩ =
        ggQ2wdt_res D w * ggQ2wdt_res D ⟨g, hg⟩ * (ggQ2wdt_res D w)⁻¹ := by
      have hconv : (⟨w.1 * g * w.1⁻¹, hconjW⟩ : D.weyl) = w * ⟨g, hg⟩ * w⁻¹ := Subtype.ext rfl
      rw [hconv, map_mul, map_mul, map_inv]
    have hresg : ggQ2wdt_res D ⟨g, hg⟩ ∈ ggQ2WeylOf h' α' := by
      rw [← hrange]
      exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
    have hWconj := hw'conj (ggQ2wdt_res D ⟨g, hg⟩) hresg
    calc ggQ2wdt_res D ⟨T * g * T⁻¹, hconjM⟩
        = T' * ggQ2wdt_res D ⟨g, hg⟩ * T'⁻¹ := hL
      _ = w' * ggQ2wdt_res D ⟨g, hg⟩ * w'⁻¹ := hWconj
      _ = ggQ2wdt_res D w * ggQ2wdt_res D ⟨g, hg⟩ * (ggQ2wdt_res D w)⁻¹ := by rw [hw_eq]
      _ = ggQ2wdt_res D ⟨w.1 * g * w.1⁻¹, hconjW⟩ := hR.symm
  simpa using congrArg Subtype.val htarget

end CFSG.StandardType

end
