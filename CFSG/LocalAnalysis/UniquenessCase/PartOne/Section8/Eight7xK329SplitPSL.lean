module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xK329SplitTwist
import CFSG.LieType.SemisimpleCentralizers.HeldLinearComponents
import CFSG.LieType.SemisimpleCentralizers.HeldCompTrivSL
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xK329SplitOrder

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open (StatedLieAdmissible StatedScalars StatedSL)

open CFSG.Open (StatedLieAdmissible StatedScalars StatedSL StatedProj)

section K329Private

open CFSG.Open CFSG.Open.StatedAPI Matrix
open CFSG.LieType.SemisimpleCentralizers.Held CFSG.StandardType.LinNonsplit
open CFSG.StandardType.LayerFacts Representation
open scoped commutatorElement

private theorem k329pf_component_block {F : Type} [Field F] [Finite F] {n : ℕ} (A : GL (Fin n) F)
    (hord : (orderOf A : F) ≠ 0) (M : Subgroup (GL (Fin n) F))
    (hM : CFSG.Open.IsComponentOf M (Subgroup.centralizer ({A} : Set (GL (Fin n) F)) ⊓ StatedSL n F)) :
    ∃ (r : ℕ) (D : Fin r → Type) (d : Fin r → ℕ) (_ : ∀ i, Field (D i)) (_ : ∀ i, Finite (D i))
      (_ : ∀ i, Algebra F (D i))
      (Φ : (∀ i, Matrix (Fin (d i)) (Fin (d i)) (D i)) →ₐ[F] Matrix (Fin n) (Fin n) F)
      (θ : (∀ i, GL (Fin (d i)) (D i)) →* GL (Fin n) F),
      (∀ i, NeZero (d i)) ∧ Function.Injective Φ ∧
      (∀ X : Matrix (Fin n) (Fin n) F, X ∈ Set.range Φ ↔
        ∀ g ∈ Subgroup.zpowers A, X * (g : Matrix (Fin n) (Fin n) F) =
          (g : Matrix (Fin n) (Fin n) F) * X) ∧
      Function.Injective θ ∧ θ.range = Subgroup.centralizer ({A} : Set (GL (Fin n) F)) ∧
      (∀ w, ((θ w : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
        Φ (fun i => ((w i : GL (Fin (d i)) (D i)) : Matrix (Fin (d i)) (Fin (d i)) (D i)))) ∧
      ∃ i : Fin r, 2 ≤ d i ∧
        M = ((StatedSL (d i) (D i)).map
          (MonoidHom.mulSingle (fun j => GL (Fin (d j)) (D j)) i)).map θ := by
  classical
  have hA : (Nat.card (Subgroup.zpowers A) : F) ≠ 0 := by
    rw [Nat.card_zpowers]
    exact hord
  obtain ⟨r, D, d, hFld, hFin, hAlg, Φ, θ, hNZ, hΦinj, hΦrange, hθinj, hθrange, hθapply⟩ :=
    exists_piMat_commutant (Subgroup.zpowers A) hA
  let : ∀ i, Field (D i) := hFld
  have : ∀ i, Finite (D i) := hFin
  have hcent : Subgroup.centralizer ((Subgroup.zpowers A : Subgroup (GL (Fin n) F)) :
      Set (GL (Fin n) F)) = Subgroup.centralizer ({A} : Set (GL (Fin n) F)) := by
    ext g
    rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
    constructor
    · intro hg h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact hg _ (Subgroup.mem_zpowers _)
    · intro hg h hh
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      have hc : Commute A g := hg A (Set.mem_singleton A)
      exact (hc.zpow_left k).eq
  have hSL' : ∀ (d : ℕ) (K : Type) [Field K] [Finite K] (X : Subgroup (StatedSL d K)),
      IsComponentOf X ⊤ → X = ⊤ :=
    CFSG.LieType.SemisimpleCentralizers.Held.SLComponentsTrivial_holds
  have hCeq : Subgroup.centralizer ({A} : Set (GL (Fin n) F)) ⊓ StatedSL n F =
      ((StatedSL n F).comap θ).map θ := by
    ext x
    constructor
    · rintro ⟨hx1, hx2⟩
      have hxr : x ∈ θ.range := by
        rw [hθrange, hcent]
        exact hx1
      obtain ⟨w, rfl⟩ := MonoidHom.mem_range.mp hxr
      exact Subgroup.mem_map.mpr ⟨w, hx2, rfl⟩
    · intro hx
      obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hx
      refine ⟨?_, hw⟩
      rw [← hcent, ← hθrange]
      exact MonoidHom.mem_range.mpr ⟨w, rfl⟩
  have hMle : M ≤ θ.range := by
    intro x hx
    have hx1 := (hM.1 hx).1
    rw [hθrange, hcent]
    exact hx1
  have hMmap : (M.comap θ).map θ = M := by
    rw [Subgroup.map_comap_eq]
    exact inf_eq_right.mpr hMle
  have hM'comp : IsComponentOf (M.comap θ) ((StatedSL n F).comap θ) := by
    refine isComponentOf_of_map_injective θ hθinj ?_
    rw [hMmap, ← hCeq]
    exact hM
  have hM'top : IsComponentOf (M.comap θ) ⊤ :=
    isComponentOf_top_of_normal' hM'comp
  obtain ⟨i, hi⟩ := exists_factor_of_isComponentOf_top (H := fun k => GL (Fin (d k)) (D k)) hM'top
  have hcommS : ∀ a b : GL (Fin (d i)) (D i), ⁅a, b⁆ ∈ StatedSL (d i) (D i) :=
    fun a b => commutatorElement_mem_statedSL a b
  have hms : Function.Injective (MonoidHom.mulSingle (fun k => GL (Fin (d k)) (D k)) i) := by
    intro a b hab
    have := congrFun hab i
    simpa [MonoidHom.mulSingle_apply] using this
  have hM'T : M.comap θ ≤ (StatedSL (d i) (D i)).map
      (MonoidHom.mulSingle (fun k => GL (Fin (d k)) (D k)) i) := by
    have h1 := commutator_eq_self_of_isComponentOf_top hM'top
    have h2 := Subgroup.commutator_mono hi hi
    rw [h1] at h2
    exact h2.trans (commutator_factorSub_le (H := fun k => GL (Fin (d k)) (D k))
      (StatedSL (d i) (D i)) hcommS)
  have hTeq : M.comap θ = (StatedSL (d i) (D i)).map
      (MonoidHom.mulSingle (fun k => GL (Fin (d k)) (D k)) i) := by
    have hX : IsComponentOf ((M.comap θ).subgroupOf _) ⊤ :=
      CFSG.ComponentClassification.LocalComponents.of_overgroup hM'top hM'T
    let e : ↥((StatedSL (d i) (D i)).map
        (MonoidHom.mulSingle (fun k => GL (Fin (d k)) (D k)) i)) ≃*
        ↥(StatedSL (d i) (D i)) :=
      (Subgroup.equivMapOfInjective (StatedSL (d i) (D i))
        (MonoidHom.mulSingle (fun k => GL (Fin (d k)) (D k)) i) hms).symm
    have hXe := (CFSG.ComponentClassification.LocalComponents.equiv_iff e _).2 hX
    have htop := hSL' (d i) (D i) _ hXe
    have hXtop : (M.comap θ).subgroupOf _ = ⊤ := eq_top_of_map_equiv_eq_top e _ htop
    exact le_antisymm hM'T (Subgroup.subgroupOf_eq_top.mp hXtop)
  have hMeq : M = (((StatedSL (d i) (D i)).map
      (MonoidHom.mulSingle (fun k => GL (Fin (d k)) (D k)) i))).map θ := by
    rw [← hTeq, hMmap]
  have hd2 : 2 ≤ d i := by
    by_contra hlt
    have hlt : d i < 2 := by omega
    have hall : ∀ a ∈ M, a = 1 := by
      intro a ha
      rw [hMeq] at ha
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      have hy1 := eq_one_of_mem_statedSL_of_le_one (by omega) hy
      rw [hy1, map_one, map_one]
    exact not_isQuasisimple_of_comm
      (fun a b => Subtype.ext (by simp [hall a a.2, hall b b.2])) hM.2.2
  exact ⟨r, D, d, hFld, hFin, hAlg, Φ, θ, hNZ, hΦinj, hΦrange, hθinj, hθrange.trans hcent, hθapply,
    i, hd2, hMeq⟩

private theorem k329pf_center_endRestrict {K : Type} [Field K] [Finite K] {n : ℕ}
    (s : GL (Fin n) K) (hA : (Nat.card (Subgroup.zpowers s) : K) ≠ 0)
    {z : Module.End K (Fin n → K)}
    (hz : z ∈ Set.range (endRestrict (Subgroup.zpowers s)))
    (hzc : ∀ w ∈ Set.range (endRestrict (Subgroup.zpowers s)), z * w = w * z) :
    z ∈ Set.range ((rhoOf (Subgroup.zpowers s)).asAlgebraHom) := by
  classical
  have : NeZero (Nat.card (Subgroup.zpowers s) : K) := ⟨hA⟩
  have : Finite (Subgroup.zpowers s) := inferInstance
  obtain ⟨f, rfl⟩ := hz
  have hcomm : ∀ g : Module.End (MonoidAlgebra K (Subgroup.zpowers s))
      (rhoOf (Subgroup.zpowers s)).asModule, f * g = g * f := by
    intro g
    apply endRestrict_injective
    have h := hzc (endRestrict (Subgroup.zpowers s) g) ⟨g, rfl⟩
    simpa only [map_mul] using h
  let f₀ : Module.End (Module.End (MonoidAlgebra K (Subgroup.zpowers s))
      (rhoOf (Subgroup.zpowers s)).asModule) (rhoOf (Subgroup.zpowers s)).asModule :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun g m => by
        have h := LinearMap.congr_fun (hcomm g) m
        simpa [Module.End.mul_apply] using h }
  have : Module.Finite (Module.End (MonoidAlgebra K (Subgroup.zpowers s))
      (rhoOf (Subgroup.zpowers s)).asModule) (rhoOf (Subgroup.zpowers s)).asModule :=
    Module.Finite.of_restrictScalars_finite K _ _
  obtain ⟨r, hr⟩ := Module.Finite.toModuleEnd_moduleEnd_surjective (R := MonoidAlgebra K (Subgroup.zpowers s))
    (M := (rhoOf (Subgroup.zpowers s)).asModule) f₀
  refine ⟨r, ?_⟩
  apply LinearMap.ext
  intro m
  show r • (show (rhoOf (Subgroup.zpowers s)).asModule from m) =
    f₀ (show (rhoOf (Subgroup.zpowers s)).asModule from m)
  rw [← hr]
  rfl

private theorem k329pf_zpow_mem_span {K : Type} [Field K] {n : ℕ} (s : GL (Fin n) K) (hs3 : s ^ 3 = 1)
    (k : ℤ) : ((s ^ k : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ∈
      Submodule.span K ({1, (s : Matrix (Fin n) (Fin n) K),
        (s : Matrix (Fin n) (Fin n) K) ^ 2} : Set (Matrix (Fin n) (Fin n) K)) := by
  rw [zpow_eq_zpow_emod' k hs3]
  have h1 : 0 ≤ k % ((3 : ℕ) : ℤ) := Int.emod_nonneg k (by norm_num)
  have h2 : k % ((3 : ℕ) : ℤ) < 3 := Int.emod_lt_of_pos k (by norm_num)
  have h3 : k % ((3 : ℕ) : ℤ) = 0 ∨ k % ((3 : ℕ) : ℤ) = 1 ∨
      k % ((3 : ℕ) : ℤ) = 2 := by omega
  rcases h3 with h | h | h
  · refine Submodule.subset_span ?_
    rw [h]
    simp
  · refine Submodule.subset_span ?_
    rw [h]
    simp
  · refine Submodule.subset_span ?_
    rw [h]
    simp

private theorem k329pf_asAlgebraHom_mem_span {K : Type} [Field K] {n : ℕ} (s : GL (Fin n) K)
    (hs3 : s ^ 3 = 1) {z : Module.End K (Fin n → K)}
    (hz : z ∈ Set.range ((rhoOf (Subgroup.zpowers s)).asAlgebraHom)) :
    LinearMap.toMatrixAlgEquiv' z ∈ Submodule.span K ({1, (s : Matrix (Fin n) (Fin n) K),
      (s : Matrix (Fin n) (Fin n) K) ^ 2} : Set (Matrix (Fin n) (Fin n) K)) := by
  obtain ⟨r, rfl⟩ := hz
  induction r using MonoidAlgebra.induction_on with
  | of g =>
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp g.2
    rw [Representation.asAlgebraHom_of, rhoOf_apply, LinearMap.toMatrixAlgEquiv'_toLinAlgEquiv']
    rw [← hk]
    exact k329pf_zpow_mem_span s hs3 k
  | add a b ha hb =>
    rw [map_add, map_add]
    exact Submodule.add_mem _ ha hb
  | smul c a ha =>
    rw [map_smul, map_smul]
    exact Submodule.smul_mem _ c ha

private theorem k329pf_density_matrix {K : Type} [Field K] [Finite K] {n : ℕ} (s : GL (Fin n) K)
    (hA : (Nat.card (Subgroup.zpowers s) : K) ≠ 0) (hs3 : s ^ 3 = 1)
    {z : Matrix (Fin n) (Fin n) K}
    (hz : ∀ g ∈ Subgroup.zpowers s, z * (g : Matrix (Fin n) (Fin n) K) =
      (g : Matrix (Fin n) (Fin n) K) * z)
    (hzc : ∀ w : Matrix (Fin n) (Fin n) K,
      (∀ g ∈ Subgroup.zpowers s, w * (g : Matrix (Fin n) (Fin n) K) =
        (g : Matrix (Fin n) (Fin n) K) * w) → z * w = w * z) :
    z ∈ Submodule.span K ({1, (s : Matrix (Fin n) (Fin n) K),
      (s : Matrix (Fin n) (Fin n) K) ^ 2} : Set (Matrix (Fin n) (Fin n) K)) := by
  classical
  have hzA : Matrix.toLinAlgEquiv' z ∈ Set.range (endRestrict (Subgroup.zpowers s)) := by
    rw [mem_range_endRestrict]
    intro g
    apply LinearMap.toMatrixAlgEquiv'.injective
    rw [map_mul, map_mul, rhoOf_apply, LinearMap.toMatrixAlgEquiv'_toLinAlgEquiv',
      LinearMap.toMatrixAlgEquiv'_toLinAlgEquiv']
    exact hz g g.2
  have hzcA : ∀ w ∈ Set.range (endRestrict (Subgroup.zpowers s)),
      Matrix.toLinAlgEquiv' z * w = w * Matrix.toLinAlgEquiv' z := by
    intro w hw
    rw [mem_range_endRestrict] at hw
    have hw' : ∀ g ∈ Subgroup.zpowers s,
        LinearMap.toMatrixAlgEquiv' w * (g : Matrix (Fin n) (Fin n) K) =
          (g : Matrix (Fin n) (Fin n) K) * LinearMap.toMatrixAlgEquiv' w := by
      intro g hg
      have h2 := congrArg LinearMap.toMatrixAlgEquiv' (hw ⟨g, hg⟩).eq
      simpa [map_mul, rhoOf_apply] using h2
    have hcomm := hzc (LinearMap.toMatrixAlgEquiv' w) hw'
    apply LinearMap.toMatrixAlgEquiv'.injective
    simpa [map_mul, LinearMap.toMatrixAlgEquiv'_toLinAlgEquiv'] using hcomm
  have hzHom : Matrix.toLinAlgEquiv' z ∈ Set.range ((rhoOf (Subgroup.zpowers s)).asAlgebraHom) :=
    k329pf_center_endRestrict s hA hzA hzcA
  have h := k329pf_asAlgebraHom_mem_span s hs3 hzHom
  rwa [LinearMap.toMatrixAlgEquiv'_toLinAlgEquiv'] at h

private theorem k329pf_f2_block_ne_eight {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK2 : Nat.card K = 2) (s : GL (Fin n) K) (hA : (Nat.card (Subgroup.zpowers s) : K) ≠ 0)
    (hs3 : s ^ 3 = 1) (hs1 : s ≠ 1)
    {r : ℕ} {D : Fin r → Type} {d : Fin r → ℕ} [∀ i, Field (D i)] [∀ i, Finite (D i)]
    [∀ i, Algebra K (D i)]
    {Φ : (∀ i, Matrix (Fin (d i)) (Fin (d i)) (D i)) →ₐ[K] Matrix (Fin n) (Fin n) K}
    (hΦinj : Function.Injective Φ)
    (hΦrange : ∀ X : Matrix (Fin n) (Fin n) K, X ∈ Set.range Φ ↔
      ∀ g ∈ Subgroup.zpowers s, X * (g : Matrix (Fin n) (Fin n) K) =
        (g : Matrix (Fin n) (Fin n) K) * X)
    (i : Fin r) (hd : NeZero (d i)) (hE : Nat.card (D i) = 8) : False := by
  classical
  have : Nonempty (Fin (d i)) := ⟨⟨0, Nat.pos_of_ne_zero hd.out⟩⟩
  let S : Submodule K (Matrix (Fin n) (Fin n) K) :=
    Submodule.span K ({1, (s : Matrix (Fin n) (Fin n) K),
      (s : Matrix (Fin n) (Fin n) K) ^ 2} : Set (Matrix (Fin n) (Fin n) K))
  let ψ : D i →ₗ[K] Matrix (Fin n) (Fin n) K :=
    Φ.toLinearMap.comp ((LinearMap.single K (fun j => Matrix (Fin (d j)) (Fin (d j)) (D j)) i).comp
      (Matrix.scalarAlgHom (Fin (d i)) K).toLinearMap)
  have hψapply : ∀ e : D i, ψ e = Φ (Pi.single i (Matrix.scalar (Fin (d i)) e)) := fun _ => rfl
  have hψinj : Function.Injective ψ := by
    intro a b hab
    have h : Pi.single i (Matrix.scalar (Fin (d i)) a) =
        Pi.single i (Matrix.scalar (Fin (d i)) b) :=
      hΦinj (by simpa [hψapply] using hab)
    have h2 := congrFun h i
    simp only [Pi.single_eq_same] at h2
    exact Matrix.scalar_inj.mp h2
  have hψmul : ∀ e f : D i, ψ (e * f) = ψ e * ψ f := by
    intro e f
    rw [hψapply, hψapply, hψapply, ← map_mul]
    congr 1
    funext j
    by_cases hj : j = i
    · subst hj
      rw [Pi.single_eq_same, Pi.mul_apply, Pi.single_eq_same, Pi.single_eq_same, ← map_mul]
    · simp [Pi.single_eq_of_ne, hj]
  have hcentral : ∀ (e : D i) (y : (∀ j, Matrix (Fin (d j)) (Fin (d j)) (D j))),
      Pi.single i (Matrix.scalar (Fin (d i)) e) * y =
        y * Pi.single i (Matrix.scalar (Fin (d i)) e) := by
    intro e y
    funext j
    by_cases hj : j = i
    · cases hj
      simp only [Pi.mul_apply, Pi.single_eq_same]
      exact (Matrix.scalar_commute e (fun r' => mul_comm e r') (y i)).eq
    · simp [Pi.single_eq_of_ne, hj]
  have hψrange_le : LinearMap.range ψ ≤ S := by
    rintro z ⟨e, rfl⟩
    have hzA : ∀ g ∈ Subgroup.zpowers s, ψ e * (g : Matrix (Fin n) (Fin n) K) =
        (g : Matrix (Fin n) (Fin n) K) * ψ e := by
      intro g hg
      rw [hψapply]
      exact ((hΦrange (Φ (Pi.single i (Matrix.scalar (Fin (d i)) e)))).mp ⟨_, rfl⟩) g hg
    have hzc : ∀ w : Matrix (Fin n) (Fin n) K,
        (∀ g ∈ Subgroup.zpowers s, w * (g : Matrix (Fin n) (Fin n) K) =
          (g : Matrix (Fin n) (Fin n) K) * w) → ψ e * w = w * ψ e := by
      intro w hw
      obtain ⟨y, rfl⟩ := (hΦrange w).mpr hw
      rw [hψapply, ← map_mul, ← map_mul, hcentral e y]
    exact k329pf_density_matrix s hA hs3 hzA hzc
  have hfinE : Module.finrank K (D i) = 3 := by
    have h := Module.natCard_eq_pow_finrank (K := K) (V := D i)
    rw [hK2, hE] at h
    have h' : (2 : ℕ) ^ Module.finrank K (D i) = 2 ^ 3 := h.symm
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) h'
  have hfr : Module.finrank K (LinearMap.range ψ) = 3 := by
    have h := LinearMap.finrank_range_add_finrank_ker ψ
    rw [LinearMap.ker_eq_bot.mpr hψinj, finrank_bot, add_zero] at h
    rw [h, hfinE]
  have hSfin : Module.finrank K S ≤ 3 := by
    have h := finrank_span_le_card (R := K) (M := Matrix (Fin n) (Fin n) K)
      ({1, (s : Matrix (Fin n) (Fin n) K), (s : Matrix (Fin n) (Fin n) K) ^ 2} : Set _)
    have hc : ({1, (s : Matrix (Fin n) (Fin n) K),
        (s : Matrix (Fin n) (Fin n) K) ^ 2} : Set (Matrix (Fin n) (Fin n) K)).toFinset.card ≤ 3 := by
      rw [Set.toFinset_insert, Set.toFinset_insert, Set.toFinset_singleton]
      exact Finset.card_le_three
    exact h.trans hc
  have hrange_eq : LinearMap.range ψ = S :=
    Submodule.eq_of_le_of_finrank_le hψrange_le (by rw [hfr]; exact hSfin)
  have hs_sub : (s : Matrix (Fin n) (Fin n) K) - 1 ∈ S :=
    Submodule.sub_mem _ (Submodule.subset_span (by simp)) (Submodule.subset_span (by simp))
  have hs2_sub : (s : Matrix (Fin n) (Fin n) K) ^ 2 + (s : Matrix (Fin n) (Fin n) K) + 1 ∈ S :=
    Submodule.add_mem _ (Submodule.add_mem _ (Submodule.subset_span (by simp))
      (Submodule.subset_span (by simp))) (Submodule.subset_span (by simp))
  rw [← hrange_eq] at hs_sub hs2_sub
  obtain ⟨a, ha⟩ := hs_sub
  obtain ⟨b, hb⟩ := hs2_sub
  have hab : a * b = 0 := by
    apply hψinj
    rw [map_zero, hψmul, ha, hb]
    have h : ((s : Matrix (Fin n) (Fin n) K) - 1) *
        ((s : Matrix (Fin n) (Fin n) K) ^ 2 + (s : Matrix (Fin n) (Fin n) K) + 1) =
        (s : Matrix (Fin n) (Fin n) K) ^ 3 - 1 := by noncomm_ring
    have hs3m : (s : Matrix (Fin n) (Fin n) K) ^ 3 = 1 := by
      have hh := congrArg (fun u : GL (Fin n) K => (u : Matrix (Fin n) (Fin n) K)) hs3
      simpa [Units.val_pow_eq_pow_val] using hh
    rw [h, hs3m]
    simp
  rcases mul_eq_zero.mp hab with ha0 | hb0
  · apply hs1
    have h := ha
    rw [ha0, map_zero] at h
    exact Units.ext (sub_eq_zero.mp h.symm)
  · have hb0' : (s : Matrix (Fin n) (Fin n) K) ^ 2 + (s : Matrix (Fin n) (Fin n) K) + 1 = 0 := by
      have h := hb
      rw [hb0, map_zero] at h
      exact h.symm
    have hs2eq : (s : Matrix (Fin n) (Fin n) K) ^ 2 = -(s : Matrix (Fin n) (Fin n) K) - 1 := by
      linear_combination (norm := noncomm_ring) hb0'
    have hspan_le : S ≤ Submodule.span K ({1, (s : Matrix (Fin n) (Fin n) K)} : Set _) := by
      dsimp only [S]
      apply Submodule.span_le.mpr
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact Submodule.subset_span (by simp)
      · exact Submodule.subset_span (by simp)
      · rw [hs2eq]
        exact Submodule.sub_mem _ (Submodule.neg_mem _ (Submodule.subset_span (by simp)))
          (Submodule.subset_span (by simp))
    have hspanfin : Module.finrank K (Submodule.span K ({1, (s : Matrix (Fin n) (Fin n) K)} : Set _)) ≤ 2 := by
      have h := finrank_span_le_card (R := K) (M := Matrix (Fin n) (Fin n) K)
        ({1, (s : Matrix (Fin n) (Fin n) K)} : Set _)
      have hc : ({1, (s : Matrix (Fin n) (Fin n) K)} : Set (Matrix (Fin n) (Fin n) K)).toFinset.card ≤ 2 := by
        rw [Set.toFinset_insert, Set.toFinset_singleton]
        exact Finset.card_le_two
      exact h.trans hc
    have : Module.finrank K S ≤ 2 := (Submodule.finrank_mono hspan_le).trans hspanfin
    rw [hrange_eq] at hfr
    omega

end K329Private

open CFSG.LieType.SemisimpleCentralizers.Held

private theorem k329p4_order {n : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ 3) (s : GL (Fin n) K)
    (hs3 : s ^ 3 ∈ StatedScalars (Fin n) K) :
    (Nat.card (Subgroup.zpowers s) : K) ≠ 0 := by
  obtain ⟨c, hc⟩ := hs3
  have h7 : Nat.card Kˣ = 7 := by rw [Nat.card_units, hK]; norm_num
  have hc7 : c ^ 7 = 1 := by rw [← h7]; exact pow_card_eq_one'
  have hs21 : s ^ 21 = 1 := by
    rw [show (21 : ℕ) = 3 * 7 by norm_num, pow_mul, ← hc, ← map_pow, hc7]
    simp
  have hdvd : orderOf s ∣ 21 := orderOf_dvd_of_pow_eq_one hs21
  have hchar : CharP K 2 := CFSG.LieType.BorelTits.charP_of_natCard_eq hK
  have hne : (orderOf s : K) ≠ 0 := by
    intro hzero
    have h2 : 2 ∣ orderOf s := (CharP.cast_eq_zero_iff K 2 (orderOf s)).mp hzero
    have : 2 ∣ 21 := h2.trans hdvd
    norm_num at this
  rwa [Nat.card_zpowers]

private theorem k329p4_scalar_commute {d : ℕ} {E : Type} [Field E]
    (M N : GL (Fin d) E)
    (hM : ∀ p q : Fin d, p ≠ q →
      (M : Matrix (Fin d) (Fin d) E) * Matrix.transvection p q 1 =
        Matrix.transvection p q 1 * (M : Matrix (Fin d) (Fin d) E))
    (hN : ∀ p q : Fin d, p ≠ q →
      (N : Matrix (Fin d) (Fin d) E) * Matrix.transvection p q 1 =
        Matrix.transvection p q 1 * (N : Matrix (Fin d) (Fin d) E)) :
    M * N = N * M := by
  obtain ⟨c, hc⟩ := matrix_eq_scalar_of_commute_transvection (M : Matrix (Fin d) (Fin d) E) hM
  obtain ⟨e, he⟩ := matrix_eq_scalar_of_commute_transvection (N : Matrix (Fin d) (Fin d) E) hN
  refine Units.ext ?_
  simp only [Units.val_mul]
  rw [hc, he, ← map_mul, ← map_mul, mul_comm c e]

theorem k329_Z3_PSL {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ 3) : ∀ ω ∈ K329Zh (StatedSL n K), ω ^ 3 = 1 → ω = 1 := by
  intro ω hω h3
  have hω' : (ω : GL (Fin n) K) ∈ StatedScalars (Fin n) K := hω
  obtain ⟨c, hc⟩ := hω'
  have hc3 : c ^ 3 = 1 := by
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    apply k329_scalar_injective (ι := Fin n)
    rw [map_pow, hc, map_one]
    simpa using congrArg Subtype.val h3
  have h7 : c ^ 7 = 1 := by
    have h : Nat.card Kˣ = 7 := by rw [Nat.card_units, hK]; norm_num
    rw [← h]
    exact pow_card_eq_one'
  have hc1 : c = 1 := by
    have e3 : orderOf c ∣ 3 := orderOf_dvd_of_pow_eq_one hc3
    have e7 : orderOf c ∣ 7 := orderOf_dvd_of_pow_eq_one h7
    have h1 : orderOf c = 1 := by
      have := Nat.dvd_gcd e3 e7
      simpa using this
    exact orderOf_eq_one_iff.mp h1
  apply Subtype.ext
  rw [← hc, hc1, map_one]
  rfl

theorem k329_S3f_PSL (n r e : ℕ) (hadm : StatedLieAdmissible .PSL n r e) (hr : r ≠ 3)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = r ^ e) :
    K329YMatrix (StatedSL n K) (r ^ e) := by
  intro x hx hx3 hQ
  obtain ⟨Q, hQL, hQn, hQq, hQcard⟩ := hQ
  let s : GL (Fin n) K := (x : GL (Fin n) K)
  have hs3mem : s ^ 3 ∈ StatedScalars (Fin n) K := by
    have h := Subgroup.mem_subgroupOf.mp hx3
    rwa [show ((x ^ 3 : ↥(StatedSL n K)) : GL (Fin n) K) = s ^ 3 from
      map_pow (Subgroup.subtype (StatedSL n K)) x 3] at h
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp hs3mem
  have hc' : s ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin n) c := hc.symm
  have hcard_units : Nat.card Kˣ = r ^ e - 1 := by rw [Nat.card_units, hK]
  have hc_pow : c ^ (r ^ e - 1) = 1 := by
    rw [← hcard_units]; exact pow_card_eq_one'
  have hs_pow : s ^ (3 * (r ^ e - 1)) = 1 := by
    calc s ^ (3 * (r ^ e - 1)) = (s ^ 3) ^ (r ^ e - 1) := by rw [pow_mul]
      _ = (Matrix.GeneralLinearGroup.scalar (Fin n) c) ^ (r ^ e - 1) := by rw [hc']
      _ = Matrix.GeneralLinearGroup.scalar (Fin n) (c ^ (r ^ e - 1)) := by rw [map_pow]
      _ = Matrix.GeneralLinearGroup.scalar (Fin n) 1 := by rw [hc_pow]
      _ = 1 := map_one _
  have horder_dvd : orderOf s ∣ 3 * (r ^ e - 1) := orderOf_dvd_of_pow_eq_one hs_pow
  have hrprime : r.Prime := hadm.1
  have he1 : 1 ≤ e := hadm.2.1
  have hn2 : 2 ≤ n := hadm.2.2.1
  have : Fact r.Prime := ⟨hrprime⟩
  have hchar : CharP K r := by
    have : Fintype K := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  have hr_not_dvd : ¬ r ∣ 3 * (r ^ e - 1) := by
    intro h
    rcases (hrprime.dvd_mul).mp h with h3 | hrm1
    · have := (Nat.prime_dvd_prime_iff_eq hrprime Nat.prime_three).mp h3
      exact hr this
    · have hre : r ∣ r ^ e := by
        obtain ⟨k, rfl⟩ := he1.dest
        rw [pow_add, pow_one]
        exact dvd_mul_right r _
      have h1 : r ∣ 1 := by
        have hrpos : 0 < r := hrprime.pos
        have hre1 : 1 ≤ r ^ e := by
          have : 0 < r ^ e := pow_pos hrpos e
          omega
        have := Nat.dvd_sub hre hrm1
        rwa [show r ^ e - (r ^ e - 1) = 1 by omega] at this
      exact hrprime.ne_one (Nat.dvd_one.mp h1)
  have hrn : ¬ r ∣ orderOf s := fun h => hr_not_dvd (h.trans horder_dvd)
  have hord : (orderOf s : K) ≠ 0 :=
    fun h => hrn ((CharP.cast_eq_zero_iff K r (orderOf s)).mp h)
  have hA : (Nat.card (Subgroup.zpowers s) : K) ≠ 0 := by
    rw [Nat.card_zpowers]; exact hord
  let C : Subgroup ↥(StatedSL n K) := Subgroup.centralizer ({x} : Set ↥(StatedSL n K))
  have hLleC : K329Lres x ≤ C := Subgroup.map_subtype_le _
  have hLn : ((K329Lres x).subgroupOf C).Normal := by
    have : ((Subgroup.centralizer ({x} : Set ↥(StatedSL n K))).subgroupOf C).Normal := by
      rw [show Subgroup.centralizer ({x} : Set ↥(StatedSL n K)) = C from rfl,
        Subgroup.subgroupOf_self]
      infer_instance
    have h := k329_res_normal (C := Subgroup.centralizer ({x} : Set ↥(StatedSL n K))) (D := C)
      le_rfl inferInstance
    simpa [K329Lres] using h
  have hQcomp : CFSG.Open.IsComponentOf Q C :=
    ⟨hQL.trans hLleC,
      CFSG.Open.IsSubnormal.step hQL hQn (CFSG.Open.IsSubnormal.step hLleC hLn (CFSG.Open.IsSubnormal.refl C)),
      hQq⟩
  have hQcompGL : CFSG.Open.IsComponentOf (Q.map (StatedSL n K).subtype) (C.map (StatedSL n K).subtype) :=
    CFSG.LieType.SemisimpleCentralizers.Held.isComponentOf_map_of_injective (StatedSL n K).subtype
      (Subgroup.subtype_injective _) hQcomp
  have hCmap : C.map (StatedSL n K).subtype =
      Subgroup.centralizer ({s} : Set (GL (Fin n) K)) ⊓ StatedSL n K := by
    ext g
    constructor
    · intro hg
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hg
      refine ⟨Subgroup.mem_centralizer_iff.mpr ?_, y.2⟩
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      have h := (Subgroup.mem_centralizer_iff.mp hy) x (Set.mem_singleton x)
      exact congrArg Subtype.val h
    · rintro ⟨hg1, hg2⟩
      refine Subgroup.mem_map.mpr ⟨⟨g, hg2⟩, Subgroup.mem_centralizer_iff.mpr ?_, rfl⟩
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp hg1 s (Set.mem_singleton s)
  have hJ : CFSG.Open.IsComponentOf (Q.map (StatedSL n K).subtype)
      (Subgroup.centralizer ({s} : Set (GL (Fin n) K)) ⊓ StatedSL n K) := by
    rwa [← hCmap]
  obtain ⟨r', D, d, hFld, hFin, hAlg, Φ, θ, hNZ, hΦinj, hΦrange, hθinj, hθrange, hθapply, i, hd2, hMeq⟩ :=
    k329pf_component_block s hord (Q.map (StatedSL n K).subtype) hJ
  let : ∀ i, Field (D i) := hFld
  have : ∀ i, Finite (D i) := hFin
  have hms : Function.Injective (MonoidHom.mulSingle (fun j => GL (Fin (d j)) (D j)) i) := by
    intro a b hab
    have := congrFun hab i
    simpa [MonoidHom.mulSingle_apply] using this
  let eJ : ↥(Q.map (StatedSL n K).subtype) ≃* ↥(StatedSL (d i) (D i)) :=
    (MulEquiv.subgroupCongr hMeq).trans
      ((Subgroup.equivMapOfInjective _ θ hθinj).symm.trans
        (Subgroup.equivMapOfInjective (StatedSL (d i) (D i))
          (MonoidHom.mulSingle (fun j => GL (Fin (d j)) (D j)) i) hms).symm)
  let eQ : ↥Q ≃* ↥(StatedSL (d i) (D i)) :=
    (Subgroup.equivMapOfInjective Q (StatedSL n K).subtype (Subgroup.subtype_injective _)).trans eJ
  obtain ⟨eQc⟩ := CFSG.LieType.SemisimpleCentralizers.Held.nonempty_quotientCenter_equiv_statedProj eQ
  have hY : Nat.card (StatedProj (StatedSL (d i) (D i))) = 504 := by
    rw [← Nat.card_congr eQc.toEquiv, hQcard]
  have : Fintype (D i) := Fintype.ofFinite (D i)
  have hcharE : CharP (D i) r :=
    charP_of_injective_algebraMap (FaithfulSMul.algebraMap_injective K (D i)) r
  obtain ⟨f, hfprime, hEcardF⟩ := FiniteField.card (D i) r
  have hEcard : Nat.card (D i) = r ^ (f : ℕ) := by
    rw [Nat.card_eq_fintype_card]; exact hEcardF
  have : Group.IsPerfect ↥Q := Group.isPerfect_def.mpr hQq.1
  have : IsSimpleGroup (↥Q ⧸ Subgroup.center ↥Q) := hQq.2
  have hnot22 : (d i, r ^ (f : ℕ)) ≠ (2, 2) := by
    intro h
    have hd : d i = 2 := congrArg Prod.fst h
    have hr2 : r ^ (f : ℕ) = 2 := congrArg Prod.snd h
    have hcard2 : Nat.card (D i) = 2 := by rw [hEcard, hr2]
    have hs2 : Group.IsSolvable ↥(StatedSL 2 (D i)) := by
      have hc := CFSG.Open.StatedAPI.card_statedSL_two (D i)
      exact CFSG.LieType.SemisimpleCentralizers.Held.hct_isSolvable_of_natCard_eq
        (p := 2) (q := 3) (a := 1) (b := 1) Nat.prime_two Nat.prime_three (by norm_num)
        (by rw [hc, hcard2]; norm_num)
    have hs : Group.IsSolvable ↥(StatedSL (d i) (D i)) :=
      Eq.mpr (congrArg (fun k => Group.IsSolvable ↥(StatedSL k (D i))) hd) hs2
    have : Nontrivial ↥Q := (QuotientGroup.mk_surjective :
      Function.Surjective (QuotientGroup.mk : ↥Q → ↥Q ⧸ Subgroup.center ↥Q)).nontrivial
    have : Nontrivial ↥(StatedSL (d i) (D i)) := eQ.symm.surjective.nontrivial
    have : Group.IsPerfect ↥(StatedSL (d i) (D i)) :=
      Group.IsPerfect.ofSurjective (f := eQ.toMonoidHom) eQ.surjective
    exact Group.IsPerfect.not_isSolvable (G := ↥(StatedSL (d i) (D i))) hs
  have hnot23 : (d i, r ^ (f : ℕ)) ≠ (2, 3) := by
    intro h
    have hd : d i = 2 := congrArg Prod.fst h
    have hr3 : r ^ (f : ℕ) = 3 := congrArg Prod.snd h
    have hcard3 : Nat.card (D i) = 3 := by rw [hEcard, hr3]
    have hs2 : Group.IsSolvable ↥(StatedSL 2 (D i)) := by
      have hc := CFSG.Open.StatedAPI.card_statedSL_two (D i)
      exact CFSG.LieType.SemisimpleCentralizers.Held.hct_isSolvable_of_natCard_eq
        (p := 2) (q := 3) (a := 3) (b := 1) Nat.prime_two Nat.prime_three (by norm_num)
        (by rw [hc, hcard3]; norm_num)
    have hs : Group.IsSolvable ↥(StatedSL (d i) (D i)) :=
      Eq.mpr (congrArg (fun k => Group.IsSolvable ↥(StatedSL k (D i))) hd) hs2
    have : Nontrivial ↥Q := (QuotientGroup.mk_surjective :
      Function.Surjective (QuotientGroup.mk : ↥Q → ↥Q ⧸ Subgroup.center ↥Q)).nontrivial
    have : Nontrivial ↥(StatedSL (d i) (D i)) := eQ.symm.surjective.nontrivial
    have : Group.IsPerfect ↥(StatedSL (d i) (D i)) :=
      Group.IsPerfect.ofSurjective (f := eQ.toMonoidHom) eQ.surjective
    exact Group.IsPerfect.not_isSolvable (G := ↥(StatedSL (d i) (D i))) hs
  have hAdm : StatedLieAdmissible .PSL (d i) r (f : ℕ) :=
    ⟨hrprime, f.pos, hd2, hnot22, hnot23⟩
  have hLie : CFSG.Blueprint.LieModel (StatedProj (StatedSL (d i) (D i))) .PSL (d i) r (f : ℕ) :=
    Or.inl ⟨by simp [CFSG.Blueprint.classicalTags],
      ⟨hAdm, D i, hFld i, hFin i, hEcard, ⟨MulEquiv.refl _⟩⟩⟩
  have hdi : d i ≠ 0 := by omega
  obtain ⟨-, hdi2, hrf8⟩ := k329_S2_order504 hdi hLie hY
  have hD8 : Nat.card (D i) = 8 := by rw [hEcard, hrf8]
  have : Module.Finite K (D i) := Module.Finite.of_finite
  have hcardD : Nat.card (D i) = Nat.card K ^ Module.finrank K (D i) :=
    Module.natCard_eq_pow_finrank
  have hpow : (r ^ e) ^ Module.finrank K (D i) = 8 := by
    rw [← hK, ← hcardD]
    exact hD8
  have hkpos : 0 < Module.finrank K (D i) := Module.finrank_pos
  have hr2 : r = 2 := by
    have hdvd : r ∣ 8 := by
      rw [← hpow]
      exact dvd_trans (dvd_pow_self r (n := e) (by omega : e ≠ 0))
        (dvd_pow_self (r ^ e) (n := Module.finrank K (D i)) hkpos.ne')
    have hdvd2 : r ∣ 2 := by
      rw [show (8 : ℕ) = 2 ^ 3 by norm_num] at hdvd
      exact hrprime.dvd_of_dvd_pow hdvd
    exact (Nat.prime_dvd_prime_iff_eq hrprime Nat.prime_two).mp hdvd2
  have hek : e * Module.finrank K (D i) = 3 := by
    have h : (r ^ e) ^ Module.finrank K (D i) = 2 ^ 3 := by rw [hpow]; norm_num
    rw [← pow_mul] at h
    rw [hr2] at h
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) h
  rcases (Nat.dvd_prime Nat.prime_three).mp ⟨Module.finrank K (D i), hek.symm⟩ with he1' | he3
  · have hK2 : Nat.card K = 2 := by rw [hK, he1', pow_one, hr2]
    have hs3 : s ^ 3 = 1 := by
      have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
      rw [hc', show (1 : GL (Fin n) K) = Matrix.GeneralLinearGroup.scalar (Fin n) 1 from
        (map_one (Matrix.GeneralLinearGroup.scalar (Fin n))).symm]
      exact congrArg (Matrix.GeneralLinearGroup.scalar (Fin n)) (by
        have hcardu : Nat.card Kˣ = 1 := by rw [Nat.card_units, hK2]
        have : Subsingleton Kˣ := (Nat.card_eq_one_iff_unique.mp hcardu).1
        exact Subsingleton.elim c 1)
    have hs1 : s ≠ 1 := by
      intro h
      apply hx
      have hx1 : x = 1 := Subtype.ext h
      rw [hx1]
      exact Subgroup.one_mem _
    exact (k329pf_f2_block_ne_eight hK2 s hA hs3 hs1 hΦinj hΦrange i (hNZ i) hD8).elim
  · rw [he3, hr2]; norm_num

private theorem k329pc_mem_centralizer_subtype {G H : Type} [Group G] [Group H] (f : G →* H)
    (hf : Function.Injective f) (x a : G) :
    a ∈ Subgroup.centralizer ({x} : Set G) ↔
      f a ∈ Subgroup.centralizer ({(f x)} : Set H) := by
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h; rw [← map_mul, ← map_mul, h]
  · intro h; exact hf (by rw [map_mul, map_mul, h])

private theorem k329pc_pi_eq_iSup {ι : Type} [Fintype ι] [DecidableEq ι] {M : ι → Type}
    [∀ i, Group (M i)] (S : (i : ι) → Subgroup (M i)) :
    Subgroup.pi Set.univ S = ⨆ i, (S i).map (MonoidHom.mulSingle M i) := by
  refine le_antisymm ?_ ?_
  · rw [Subgroup.pi_le_iff]
    intro i
    exact le_iSup (fun i => (S i).map (MonoidHom.mulSingle M i)) i
  · refine iSup_le fun i => ?_
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    rw [Subgroup.mem_pi]
    intro j _
    rw [MonoidHom.mulSingle_apply]
    by_cases h : j = i
    · subst h; simpa using ha
    · rw [Pi.mulSingle_eq_of_ne h]; exact Subgroup.one_mem _

private theorem k329pc_statedSL_eq_bot_of_le_one {E : Type} [Field E] {d : ℕ} (hd : d ≤ 1) :
    StatedSL d E = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  exact CFSG.LieType.SemisimpleCentralizers.Held.eq_one_of_mem_statedSL_of_le_one hd hx

private abbrev k329pc_T {r : ℕ} (D : Fin r → Type) [∀ i, Field (D i)] (d : Fin r → ℕ)
    (i : Fin r) : Subgroup (∀ j, GL (Fin (d j)) (D j)) :=
  (StatedSL (d i) (D i)).map (MonoidHom.mulSingle (fun j => GL (Fin (d j)) (D j)) i)

private theorem k329pc_factor_le_SL {K : Type} [Field K] {n r : ℕ}
    {D : Fin r → Type} [∀ i, Field (D i)] {d : Fin r → ℕ}
    (θ : (∀ i, GL (Fin (d i)) (D i)) →* GL (Fin n) K) {i : Fin r}
    (hperf : Group.IsPerfect (StatedSL (d i) (D i))) :
    (k329pc_T D d i).map θ ≤ StatedSL n K := by
  have hTperf : ⁅k329pc_T D d i, k329pc_T D d i⁆ = k329pc_T D d i := by
    rw [← Subgroup.map_commutator, Subgroup.isPerfect_iff.mp hperf]
  have hθperf : ⁅(k329pc_T D d i).map θ, (k329pc_T D d i).map θ⁆ =
      (k329pc_T D d i).map θ := by
    rw [← Subgroup.map_commutator, hTperf]
  rw [← hθperf]
  exact Subgroup.commutator_le.mpr (fun x _ y _ =>
    CFSG.LieType.SemisimpleCentralizers.Held.commutatorElement_mem_statedSL x y)

private theorem k329pc_factor_quasisimple {K : Type} [Field K] {n r : ℕ}
    {D : Fin r → Type} [∀ i, Field (D i)] {d : Fin r → ℕ}
    (θ : (∀ i, GL (Fin (d i)) (D i)) →* GL (Fin n) K) (hθinj : Function.Injective θ)
    {i : Fin r} (hle : (k329pc_T D d i).map θ ≤ StatedSL n K)
    (hq : CFSG.Open.IsQuasisimple ↥(StatedSL (d i) (D i))) :
    CFSG.Open.IsQuasisimple ↥(((k329pc_T D d i).map θ).subgroupOf (StatedSL n K)) := by
  have hms : Function.Injective
      (MonoidHom.mulSingle (fun j => GL (Fin (d j)) (D j)) i) := by
    intro a b hab
    have h : Pi.mulSingle (M := fun j => GL (Fin (d j)) (D j)) i a =
        Pi.mulSingle (M := fun j => GL (Fin (d j)) (D j)) i b := by
      simpa only [MonoidHom.mulSingle_apply] using hab
    exact (Pi.mulSingle_inj (M := fun j => GL (Fin (d j)) (D j)) i).mp h
  have e1 : ↥(((k329pc_T D d i).map θ).subgroupOf (StatedSL n K)) ≃*
      ↥((k329pc_T D d i).map θ) :=
    Subgroup.subgroupOfEquivOfLe hle
  have e2 : ↥((k329pc_T D d i).map θ) ≃* ↥(k329pc_T D d i) :=
    (Subgroup.equivMapOfInjective (k329pc_T D d i) θ hθinj).symm
  have e3 : ↥(k329pc_T D d i) ≃* ↥(StatedSL (d i) (D i)) :=
    (Subgroup.equivMapOfInjective (StatedSL (d i) (D i))
      (MonoidHom.mulSingle (fun j => GL (Fin (d j)) (D j)) i) hms).symm
  exact k329_isQuasisimple_of_mulEquiv ((e1.trans e2).trans e3).symm hq

private theorem k329pc_factors_commute {K : Type} [Field K] {n r : ℕ}
    {D : Fin r → Type} [∀ i, Field (D i)] {d : Fin r → ℕ}
    (θ : (∀ i, GL (Fin (d i)) (D i)) →* GL (Fin n) K)
    {i j : Fin r} (hij : i ≠ j) :
    ⁅((k329pc_T D d i).map θ).subgroupOf (StatedSL n K),
      ((k329pc_T D d j).map θ).subgroupOf (StatedSL n K)⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  have ha' : (a : GL (Fin n) K) ∈ (k329pc_T D d i).map θ := Subgroup.mem_subgroupOf.mp ha
  have hb' : (b : GL (Fin n) K) ∈ (k329pc_T D d j).map θ := Subgroup.mem_subgroupOf.mp hb
  obtain ⟨ta, hta, htaeq⟩ := Subgroup.mem_map.mp ha'
  obtain ⟨tb, htb, htbeq⟩ := Subgroup.mem_map.mp hb'
  obtain ⟨xa, hxa, rfl⟩ := Subgroup.mem_map.mp hta
  obtain ⟨xb, hxb, rfl⟩ := Subgroup.mem_map.mp htb
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, ← htaeq, ← htbeq]
  exact ((Pi.mulSingle_commute hij xa xb).map θ).eq.symm

private theorem k329pc_map_commutator_top_le {K : Type} [Field K] {n r : ℕ}
    {D : Fin r → Type} [∀ i, Field (D i)] {d : Fin r → ℕ}
    (θ : (∀ i, GL (Fin (d i)) (D i)) →* GL (Fin n) K)
    (hSL : ∀ i, ⁅(⊤ : Subgroup (GL (Fin (d i)) (D i))), ⊤⁆ ≤ StatedSL (d i) (D i)) :
    Subgroup.map θ (⁅(⊤ : Subgroup (∀ i, GL (Fin (d i)) (D i))), ⊤⁆) ≤
      ⨆ i, (k329pc_T D d i).map θ := by
  have hpi : (⊤ : Subgroup (∀ i, GL (Fin (d i)) (D i))) =
      Subgroup.pi Set.univ (fun i => (⊤ : Subgroup (GL (Fin (d i)) (D i)))) := by
    ext w; simp [Subgroup.mem_pi]
  rw [hpi, Subgroup.commutator_pi_pi_of_finite, k329pc_pi_eq_iSup, Subgroup.map_iSup]
  refine iSup_le fun i => ?_
  show Subgroup.map θ (Subgroup.map
      (MonoidHom.mulSingle (fun j => GL (Fin (d j)) (D j)) i)
      (⁅(⊤ : Subgroup (GL (Fin (d i)) (D i))), ⊤⁆)) ≤
    ⨆ j, Subgroup.map θ (Subgroup.map
      (MonoidHom.mulSingle (fun k => GL (Fin (d k)) (D k)) j)
      (StatedSL (d j) (D j)))
  rw [Subgroup.map_map]
  refine le_trans (Subgroup.map_mono (hSL i)) ?_
  rw [← Subgroup.map_map]
  exact le_iSup (fun j => Subgroup.map θ (Subgroup.map
    (MonoidHom.mulSingle (fun k => GL (Fin (d k)) (D k)) j)
    (StatedSL (d j) (D j)))) i

private theorem k329pc_centralizer_commutator_le_iSup {K : Type} [Field K] {n r : ℕ}
    {D : Fin r → Type} [∀ i, Field (D i)] {d : Fin r → ℕ}
    (θ : (∀ i, GL (Fin (d i)) (D i)) →* GL (Fin n) K)
    (hSL : ∀ i, ⁅(⊤ : Subgroup (GL (Fin (d i)) (D i))), ⊤⁆ ≤ StatedSL (d i) (D i))
    (hle : ∀ i, (k329pc_T D d i).map θ ≤ StatedSL n K)
    (x : ↥(StatedSL n K))
    (hθrange : θ.range = Subgroup.centralizer ({(x : GL (Fin n) K)} : Set (GL (Fin n) K))) :
    ⁅Subgroup.centralizer ({x} : Set ↥(StatedSL n K)),
        Subgroup.centralizer ({x} : Set ↥(StatedSL n K))⁆ ≤
      ⨆ i, ((k329pc_T D d i).map θ).subgroupOf (StatedSL n K) := by
  have hCmap : (Subgroup.centralizer ({x} : Set ↥(StatedSL n K))).map
      (Subgroup.subtype (StatedSL n K)) = StatedSL n K ⊓ θ.range := by
    ext g
    constructor
    · intro hg
      obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hg
      refine Subgroup.mem_inf.mpr ⟨c.2, ?_⟩
      rw [hθrange]
      exact (k329pc_mem_centralizer_subtype (Subgroup.subtype (StatedSL n K))
        (Subgroup.subtype_injective (StatedSL n K)) x c).mp hc
    · intro hg
      rw [Subgroup.mem_inf] at hg
      obtain ⟨hgH, hgrange⟩ := hg
      refine Subgroup.mem_map.mpr ⟨⟨g, hgH⟩, ?_, rfl⟩
      rw [hθrange] at hgrange
      exact (k329pc_mem_centralizer_subtype (Subgroup.subtype (StatedSL n K))
        (Subgroup.subtype_injective (StatedSL n K)) x ⟨g, hgH⟩).mpr hgrange
  have key : (⁅Subgroup.centralizer ({x} : Set ↥(StatedSL n K)),
      Subgroup.centralizer ({x} : Set ↥(StatedSL n K))⁆).map
        (Subgroup.subtype (StatedSL n K)) ≤
      (⨆ i, ((k329pc_T D d i).map θ).subgroupOf (StatedSL n K)).map
        (Subgroup.subtype (StatedSL n K)) := by
    rw [Subgroup.map_commutator, hCmap]
    calc ⁅StatedSL n K ⊓ θ.range, StatedSL n K ⊓ θ.range⁆ ≤ ⁅θ.range, θ.range⁆ :=
          Subgroup.commutator_mono inf_le_right inf_le_right
      _ = Subgroup.map θ (⁅(⊤ : Subgroup (∀ i, GL (Fin (d i)) (D i))), ⊤⁆) := by
          rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator]
      _ ≤ ⨆ i, (k329pc_T D d i).map θ := k329pc_map_commutator_top_le θ hSL
      _ ≤ (⨆ i, ((k329pc_T D d i).map θ).subgroupOf (StatedSL n K)).map
            (Subgroup.subtype (StatedSL n K)) := by
          rw [Subgroup.map_iSup]
          refine iSup_le fun i => ?_
          refine le_trans ?_
            (le_iSup (fun j => (((k329pc_T D d j).map θ).subgroupOf (StatedSL n K)).map
              (Subgroup.subtype (StatedSL n K))) i)
          rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (hle i)]
  exact (Subgroup.map_le_map_iff_of_injective
    (Subgroup.subtype_injective (StatedSL n K))).mp key

private theorem k329pc_iSup_subtype_eq {M : Type} [Group M] {r : ℕ} (d : Fin r → ℕ)
    (S : Fin r → Subgroup M) (htriv : ∀ i, ¬ 2 ≤ d i → S i = ⊥) :
    (⨆ i : Fin r, S i) = ⨆ i : {i : Fin r // 2 ≤ d i}, S i.val := by
  refine le_antisymm ?_ ?_
  · refine iSup_le fun i => ?_
    by_cases h : 2 ≤ d i
    · exact le_iSup (fun j : {i : Fin r // 2 ≤ d i} => S j.val) ⟨i, h⟩
    · rw [htriv i h]; exact bot_le
  · refine iSup_le fun i => ?_
    exact le_iSup (fun j : Fin r => S j) i.val

theorem k329_S3c_PSL (n : ℕ) (hadm : StatedLieAdmissible .PSL n 2 3) (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = 2 ^ 3) : K329CentralProductMatrix (StatedSL n K) := by
  classical
  have _ : 2 ≤ n := hadm.2.2.1
  intro x hxZ hx3
  let s : GL (Fin n) K := (x : GL (Fin n) K)
  have hx3s : s ^ 3 ∈ StatedScalars (Fin n) K := by
    have h := Subgroup.mem_subgroupOf.mp hx3
    simpa [s, map_pow] using h
  obtain ⟨c, hc⟩ := hx3s
  have hc7 : c ^ 7 = 1 := by
    have h : Nat.card Kˣ = 7 := by rw [Nat.card_units, hK]; norm_num
    rw [← h]; exact pow_card_eq_one'
  have hs21 : s ^ 21 = 1 := by
    have h : s ^ 21 = (s ^ 3) ^ 7 := by group
    rw [h, ← hc, ← map_pow, hc7, map_one]
  have hord21 : orderOf s ∣ 21 := orderOf_dvd_of_pow_eq_one hs21
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : CharP K 2 := CFSG.LieType.BorelTits.charP_of_natCard_eq (p := 2) (f := 3) hK
  have : CharP K 2 := hchar
  have hordK : (orderOf s : K) ≠ 0 := by
    intro h0
    exact (by norm_num : ¬ (2 : ℕ) ∣ 21)
      ((CharP.cast_eq_zero_iff K 2 (orderOf s)).mp h0 |>.trans hord21)
  have hA : (Nat.card (Subgroup.zpowers s) : K) ≠ 0 := by
    rw [Nat.card_zpowers]; exact hordK
  have hcent : Subgroup.centralizer ((Subgroup.zpowers s : Subgroup (GL (Fin n) K)) :
      Set (GL (Fin n) K)) = Subgroup.centralizer ({s} : Set (GL (Fin n) K)) := by
    ext g
    rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
    constructor
    · intro hg h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact hg _ (Subgroup.mem_zpowers _)
    · intro hg h hh
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      have hc : Commute s g := hg s (Set.mem_singleton s)
      exact (hc.zpow_left k).eq
  obtain ⟨r, D, d, hFld, hFin, hAlg, Φ, θ, hNZ, hΦinj, hΦrange, hθinj, hθrange, hθapply⟩ :=
    CFSG.StandardType.LinNonsplit.exists_piMat_commutant (Subgroup.zpowers s) hA
  let : ∀ i, Field (D i) := hFld
  have : ∀ i, Finite (D i) := hFin
  let : ∀ i, Algebra K (D i) := hAlg
  have hθrange' : θ.range = Subgroup.centralizer ({(x : GL (Fin n) K)} : Set (GL (Fin n) K)) :=
    hθrange.trans hcent
  let ι : Type := {i : Fin r // 2 ≤ d i}
  have : Fintype ι := Subtype.fintype _
  let T : ι → Subgroup (∀ j, GL (Fin (d j)) (D j)) := fun i =>
    (StatedSL (d i.val) (D i.val)).map
      (MonoidHom.mulSingle (fun j => GL (Fin (d j)) (D j)) i.val)
  let Lf : ι → Subgroup ↥(StatedSL n K) := fun i =>
    ((T i).map θ).subgroupOf (StatedSL n K)
  have hDcard : ∀ i, Nat.card K ≤ Nat.card (D i) := fun i =>
    Nat.card_le_card_of_injective (algebraMap K (D i)) (algebraMap K (D i)).injective
  have hDne : ∀ i, Nat.card (D i) ≠ 2 ∧ Nat.card (D i) ≠ 3 := by
    intro i
    have h := hDcard i
    rw [hK] at h
    constructor <;> intro hh <;> omega
  have hperf : ∀ i : Fin r, 2 ≤ d i → Group.IsPerfect (StatedSL (d i) (D i)) := fun i h2 =>
    CFSG.LieType.SemisimpleCentralizers.Held.hct_isPerfect_statedSL (D i) h2
      (Or.inr (hDne i).1) (Or.inr (hDne i).2)
  have hqSL : ∀ i : Fin r, 2 ≤ d i → CFSG.Open.IsQuasisimple ↥(StatedSL (d i) (D i)) :=
    fun i h2 => CFSG.LieType.SemisimpleCentralizers.Held.hct_isQuasisimple_statedSL (D i) h2
      (Or.inr (hDne i).1) (Or.inr (hDne i).2)
  have hleT : ∀ i : Fin r, (k329pc_T D d i).map θ ≤ StatedSL n K := by
    intro i
    by_cases h2 : 2 ≤ d i
    · exact k329pc_factor_le_SL θ (hperf i h2)
    · have hbot : k329pc_T D d i = ⊥ := by
        show (StatedSL (d i) (D i)).map
          (MonoidHom.mulSingle (fun j => GL (Fin (d j)) (D j)) i) = ⊥
        rw [k329pc_statedSL_eq_bot_of_le_one (by omega : d i ≤ 1), Subgroup.map_bot]
      rw [hbot, Subgroup.map_bot]
      exact bot_le
  have hLf_q : ∀ i : ι, CFSG.Open.IsQuasisimple ↥(Lf i) := by
    intro i
    exact k329pc_factor_quasisimple θ hθinj (hleT i.val) (hqSL i.val i.2)
  have hLf_c : ∀ i j : ι, i ≠ j → ⁅Lf i, Lf j⁆ = ⊥ := by
    intro i j hij
    exact k329pc_factors_commute θ (fun h => hij (Subtype.ext h))
  have hLf_le : ∀ i : ι, Lf i ≤ K329Lres x := by
    intro i
    refine k329_perfect_le_res ?_ ?_
    · intro a ha
      refine (k329pc_mem_centralizer_subtype (Subgroup.subtype (StatedSL n K))
        (Subgroup.subtype_injective (StatedSL n K)) x a).mpr ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      have ha' : (a : GL (Fin n) K) ∈ (k329pc_T D d i.val).map θ :=
        Subgroup.mem_subgroupOf.mp ha
      have harange : (a : GL (Fin n) K) ∈ θ.range := by
        rw [MonoidHom.range_eq_map]
        exact Subgroup.map_mono le_top ha'
      rw [hθrange'] at harange
      exact Subgroup.mem_centralizer_singleton_iff.mp harange
    · exact Subgroup.isPerfect_iff.mp ⟨(hLf_q i).1⟩
  have hsup_le : ⨆ i : ι, Lf i ≤ K329Lres x := iSup_le hLf_le
  have htriv : ∀ i : Fin r, ¬ 2 ≤ d i →
      ((k329pc_T D d i).map θ).subgroupOf (StatedSL n K) = ⊥ := by
    intro i hi
    have hbot : k329pc_T D d i = ⊥ := by
      show (StatedSL (d i) (D i)).map
        (MonoidHom.mulSingle (fun j => GL (Fin (d j)) (D j)) i) = ⊥
      rw [k329pc_statedSL_eq_bot_of_le_one (by omega : d i ≤ 1), Subgroup.map_bot]
    rw [hbot, Subgroup.map_bot, Subgroup.bot_subgroupOf]
  have hjoin_eq : (⨆ i : Fin r, ((k329pc_T D d i).map θ).subgroupOf (StatedSL n K)) =
      ⨆ i : ι, Lf i := by
    have h := k329pc_iSup_subtype_eq d
      (fun i => ((k329pc_T D d i).map θ).subgroupOf (StatedSL n K)) htriv
    simpa [Lf, T] using h
  have hsup_ge : K329Lres x ≤ ⨆ i : ι, Lf i := by
    calc K329Lres x
        = K329Res (Subgroup.centralizer ({x} : Set ↥(StatedSL n K))) := rfl
      _ ≤ ⁅Subgroup.centralizer ({x} : Set ↥(StatedSL n K)),
            Subgroup.centralizer ({x} : Set ↥(StatedSL n K))⁆ :=
          k329_res_le_commutator _
      _ ≤ ⨆ i : Fin r, ((k329pc_T D d i).map θ).subgroupOf (StatedSL n K) :=
          k329pc_centralizer_commutator_le_iSup θ
            (fun i => Subgroup.commutator_le.mpr (fun a _ b _ =>
              CFSG.LieType.SemisimpleCentralizers.Held.commutatorElement_mem_statedSL a b))
            hleT x hθrange'
      _ = ⨆ i : ι, Lf i := hjoin_eq
  have hsup : ⨆ i : ι, Lf i = K329Lres x := le_antisymm hsup_le hsup_ge
  exact ⟨ι, inferInstance, Lf, hLf_q, hLf_c, hsup⟩

theorem k329_S4_PSL (n : ℕ) (hadm : StatedLieAdmissible .PSL n 2 3) (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = 2 ^ 3) : K329SchurMatrix (StatedSL n K) := by
  intro x _hxZ hx3 R hRC _hR3 hcomm a ha b hb
  have _ := hadm
  let s : GL (Fin n) K := (x : GL (Fin n) K)
  have hs3 : s ^ 3 ∈ StatedScalars (Fin n) K := by
    change (x : GL (Fin n) K) ^ 3 ∈ StatedScalars (Fin n) K
    have h := hx3
    rw [K329Zh, Subgroup.mem_subgroupOf] at h
    simpa using h
  have hA : (Nat.card (Subgroup.zpowers s) : K) ≠ 0 := k329p4_order hK s hs3
  obtain ⟨r, D, d, hFld, hFin, hAlg, _Φ, θ, _hNZ, _hΦinj, _hΦrange, hθinj, hθrange, _hθapply⟩ :=
    CFSG.StandardType.LinNonsplit.exists_piMat_commutant (Subgroup.zpowers s) hA
  let hField : ∀ i, Field (D i) := hFld
  have hFinite : ∀ i, Finite (D i) := hFin
  let hAlgebra : ∀ i, Algebra K (D i) := hAlg
  have hcent : Subgroup.centralizer (Subgroup.zpowers s : Set (GL (Fin n) K)) =
      Subgroup.centralizer ({s} : Set (GL (Fin n) K)) := by
    ext g
    rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
    constructor
    · intro hg h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact hg _ (Subgroup.mem_zpowers _)
    · intro hg h hh
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      have hc : Commute s g := hg s (Set.mem_singleton s)
      exact (hc.zpow_left k).eq
  have hθrange' : θ.range = Subgroup.centralizer ({s} : Set (GL (Fin n) K)) := by
    rw [hθrange, hcent]
  have hmem_cent : ∀ y ∈ R, (y : GL (Fin n) K) ∈
      Subgroup.centralizer ({s} : Set (GL (Fin n) K)) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    have h := Subgroup.mem_centralizer_iff.mp (hRC hy) x (Set.mem_singleton x)
    change (x : GL (Fin n) K) * (y : GL (Fin n) K) = (y : GL (Fin n) K) * (x : GL (Fin n) K)
    exact congrArg (fun g : ↥(StatedSL n K) => (g : GL (Fin n) K)) h
  have hmem_range : ∀ y ∈ R, (y : GL (Fin n) K) ∈ θ.range := by
    intro y hy
    rw [hθrange']
    exact hmem_cent y hy
  have hD8 : ∀ i : Fin r, 8 ≤ Nat.card (D i) := by
    intro i
    have hle : Nat.card K ≤ Nat.card (D i) :=
      Nat.card_le_card_of_injective (algebraMap K (D i)) (algebraMap K (D i)).injective
    rw [hK] at hle
    norm_num at hle
    exact hle
  have hcomm_coord : ∀ (y : ↥(StatedSL n K)) (hy : y ∈ R)
      (wy : ∀ i, GL (Fin (d i)) (D i)) (hwy : θ wy = (y : GL (Fin n) K))
      (i : Fin r), 2 ≤ d i →
      ∀ τ ∈ StatedSL (d i) (D i), wy i * τ = τ * wy i := by
    intro y hy wy hwy i hd2 τ hτ
    let Ti : Subgroup (∀ k, GL (Fin (d k)) (D k)) :=
      (StatedSL (d i) (D i)).map (MonoidHom.mulSingle (fun k => GL (Fin (d k)) (D k)) i)
    have hTi_perf : ⁅Ti, Ti⁆ = Ti := by
      have h22 : d i ≠ 2 ∨ Nat.card (D i) ≠ 2 := by
        right; intro h; have := hD8 i; rw [h] at this; norm_num at this
      have h23 : d i ≠ 2 ∨ Nat.card (D i) ≠ 3 := by
        right; intro h; have := hD8 i; rw [h] at this; norm_num at this
      have hperf := Subgroup.isPerfect_iff.mp (hct_isPerfect_statedSL (D i) hd2 h22 h23)
      rw [← Subgroup.map_commutator, hperf]
    have hTiSL : Ti.map θ ≤ StatedSL n K := by
      rw [← hTi_perf, Subgroup.map_commutator]
      exact Subgroup.commutator_le.mpr fun p _ q _ => commutatorElement_mem_statedSL p q
    let Ti' : Subgroup ↥(StatedSL n K) := (Ti.map θ).subgroupOf (StatedSL n K)
    have hTi'_perf : ⁅Ti', Ti'⁆ = Ti' := by
      apply Subgroup.map_injective (StatedSL n K).subtype_injective
      rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hTiSL,
        ← Subgroup.map_commutator, hTi_perf]
    have hTi'C : Ti' ≤ Subgroup.centralizer ({x} : Set ↥(StatedSL n K)) := by
      intro t ht
      have htGL : (t : GL (Fin n) K) ∈ Ti.map θ := by
        simpa [Ti', Subgroup.mem_subgroupOf] using ht
      have hrange : (t : GL (Fin n) K) ∈ θ.range := Subgroup.map_le_range θ Ti htGL
      rw [hθrange'] at hrange
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp hrange s (Set.mem_singleton s)
    have hTi'L : Ti' ≤ K329Lres x := k329_perfect_le_res hTi'C hTi'_perf
    have hRL : R ≤ Subgroup.centralizer (K329Lres x : Set ↥(StatedSL n K)) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    let u : ∀ k, GL (Fin (d k)) (D k) :=
      MonoidHom.mulSingle (fun k => GL (Fin (d k)) (D k)) i τ
    have hu_mem : u ∈ Ti := Subgroup.mem_map.mpr ⟨τ, hτ, rfl⟩
    have hθu_mem : θ u ∈ Ti.map θ := Subgroup.mem_map.mpr ⟨u, hu_mem, rfl⟩
    have hθu : θ u ∈ StatedSL n K := hTiSL hθu_mem
    have ht'_mem : (⟨θ u, hθu⟩ : ↥(StatedSL n K)) ∈ Ti' := by
      simp only [Ti', Subgroup.mem_subgroupOf]
      exact hθu_mem
    have hca := Subgroup.mem_centralizer_iff.mp (hRL hy) _ (hTi'L ht'_mem)
    have hca' : θ u * θ wy = θ wy * θ u := by
      have := congrArg (fun g : ↥(StatedSL n K) => (g : GL (Fin n) K)) hca
      simpa [hwy] using this
    have hca'' : u * wy = wy * u := by
      apply hθinj
      rw [map_mul, map_mul, hca']
    have := congrFun hca'' i
    simpa [u, Pi.mul_apply] using this.symm
  obtain ⟨wa, hwa⟩ := MonoidHom.mem_range.mp (hmem_range a ha)
  obtain ⟨wb, hwb⟩ := MonoidHom.mem_range.mp (hmem_range b hb)
  have hcoord : ∀ i, wa i * wb i = wb i * wa i := by
    intro i
    by_cases hd2 : 2 ≤ d i
    · have hM : ∀ p q : Fin (d i), p ≠ q →
          (wa i : Matrix (Fin (d i)) (Fin (d i)) (D i)) * Matrix.transvection p q 1 =
            Matrix.transvection p q 1 * (wa i : Matrix (Fin (d i)) (Fin (d i)) (D i)) := by
        intro p q hpq
        have hτ := hcomm_coord a ha wa hwa i hd2
          (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection hpq 1))
          (transvection_toGL_mem_statedSL hpq 1)
        have hτ' := congrArg (fun g : GL (Fin (d i)) (D i) =>
          (g : Matrix (Fin (d i)) (Fin (d i)) (D i))) hτ
        exact hτ'
      have hN : ∀ p q : Fin (d i), p ≠ q →
          (wb i : Matrix (Fin (d i)) (Fin (d i)) (D i)) * Matrix.transvection p q 1 =
            Matrix.transvection p q 1 * (wb i : Matrix (Fin (d i)) (Fin (d i)) (D i)) := by
        intro p q hpq
        have hτ := hcomm_coord b hb wb hwb i hd2
          (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection hpq 1))
          (transvection_toGL_mem_statedSL hpq 1)
        have hτ' := congrArg (fun g : GL (Fin (d i)) (D i) =>
          (g : Matrix (Fin (d i)) (Fin (d i)) (D i))) hτ
        exact hτ'
      exact k329p4_scalar_commute (wa i) (wb i) hM hN
    · have hM : ∀ p q : Fin (d i), p ≠ q →
          (wa i : Matrix (Fin (d i)) (Fin (d i)) (D i)) * Matrix.transvection p q 1 =
            Matrix.transvection p q 1 * (wa i : Matrix (Fin (d i)) (Fin (d i)) (D i)) := by
        intro p q hpq
        exact (hpq (by apply Fin.ext; have hp := p.isLt; have hq := q.isLt; omega)).elim
      have hN : ∀ p q : Fin (d i), p ≠ q →
          (wb i : Matrix (Fin (d i)) (Fin (d i)) (D i)) * Matrix.transvection p q 1 =
            Matrix.transvection p q 1 * (wb i : Matrix (Fin (d i)) (Fin (d i)) (D i)) := by
        intro p q hpq
        exact (hpq (by apply Fin.ext; have hp := p.isLt; have hq := q.isLt; omega)).elim
      exact k329p4_scalar_commute (wa i) (wb i) hM hN
  have hw : wa * wb = wb * wa := funext hcoord
  have hGL : (a : GL (Fin n) K) * (b : GL (Fin n) K) =
      (b : GL (Fin n) K) * (a : GL (Fin n) K) := by
    rw [← hwa, ← hwb, ← map_mul, ← map_mul, hw]
  apply Subtype.ext
  exact hGL

theorem k329_S5_PSL (n : ℕ) (hadm : StatedLieAdmissible .PSL n 2 3) (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = 2 ^ 3) : K329TwistMatrix (StatedSL n K) False := by
  intro x _ hx3 g hg _ hgx
  exact hgx (k329_S5_of_no_order_three (K329Zh _) (k329_Zh_le_center _)
    (k329_Z3_PSL (by have := hadm.2.2.1; omega) hK) hx3 hg)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
