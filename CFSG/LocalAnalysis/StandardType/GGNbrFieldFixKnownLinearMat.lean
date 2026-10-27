module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.FQMat
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FQLin
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeATransport
public import CFSG.LinearAlgebra.LinearGroups.Perfect

public section

namespace CFSG.StandardType.LinearFieldFix

open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.FQ
open scoped commutatorElement

private theorem commutator_mul_central_left {G : Type*} [Group G] {g h c : G}
    (hc : c ∈ Subgroup.center G) : ⁅c * g, h⁆ = ⁅g, h⁆ := by
  have hcg : c * g = g * c := (Subgroup.mem_center_iff.mp hc g).symm
  have h1 : ⁅c, h⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hc h).symm
  rw [hcg, commutatorElement_mul_left_eq_conj_mul, h1, mul_one]
  simp

private theorem commutator_mul_central_right {G : Type*} [Group G] {g h c : G}
    (hc : c ∈ Subgroup.center G) : ⁅g, c * h⁆ = ⁅g, h⁆ := by
  have hch : c * h = h * c := (Subgroup.mem_center_iff.mp hc h).symm
  have h1 : ⁅g, c⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hc g)
  rw [hch, commutatorElement_mul_right_eq_mul_conj, h1, mul_one]
  simp

private theorem coe_glMap {ι : Type} [Fintype ι] [DecidableEq ι] {R S : Type} [CommRing R]
    [CommRing S] (f : R →+* S) (g : GL ι R) :
    ((Matrix.GeneralLinearGroup.map f g : GL ι S) : Matrix ι ι S) =
      (g : Matrix ι ι R).map f :=
  rfl

theorem commute_of_commutator_mem_center {G : Type*} [Group G] {H : Subgroup G}
    (hH : ⁅H, H⁆ = H) {B : G} (hB : ∀ g ∈ H, ⁅B, g⁆ ∈ Subgroup.center G) {g : G} (hg : g ∈ H) :
    Commute B g := by
  have hle : ⁅H, H⁆ ≤ Subgroup.centralizer ({B} : Set G) := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    have hconja : B * a * B⁻¹ = ⁅B, a⁆ * a := by
      simpa only [MulAut.conj_apply] using conj_eq_commutatorElement_mul (g₁ := B) (g₂ := a)
    have hconjb : B * b * B⁻¹ = ⁅B, b⁆ * b := by
      simpa only [MulAut.conj_apply] using conj_eq_commutatorElement_mul (g₁ := B) (g₂ := b)
    have hconj : B * ⁅a, b⁆ * B⁻¹ = ⁅a, b⁆ := by
      rw [conjugate_commutatorElement, hconja, hconjb,
        commutator_mul_central_left (hB a ha), commutator_mul_central_right (hB b hb)]
    exact mul_inv_eq_iff_eq_mul.mp hconj
  rw [← hH] at hg
  exact Subgroup.mem_centralizer_iff.mp (hle hg) B (Set.mem_singleton B)

variable {d : ℕ} {K : Type} [Field K]

theorem commutator_slGroup (hd : 3 ≤ d) :
    ⁅LargeEvenSLGroup (Fin d) K, LargeEvenSLGroup (Fin d) K⁆ = LargeEvenSLGroup (Fin d) K := by
  haveI hP : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin d) K) :=
    CFSG.LinearGroups.special_linear_isPerfect (K := K) (n := d) (by omega) (Or.inl hd)
  have hP' : Group.IsPerfect (↥(LargeEvenSLGroup (Fin d) K)) :=
    Group.IsPerfect.ofSurjective (f := (TypeA.slKerEquiv d K).symm.toMonoidHom)
      (TypeA.slKerEquiv d K).symm.surjective
  exact (Subgroup.isPerfect_iff (H := LargeEvenSLGroup (Fin d) K)).1 hP'

@[expose] noncomputable def elemSL (F : Type) [Field F] {i j : Fin d} (hij : i ≠ j) :
    LargeEvenSLGroup (Fin d) F :=
  (TypeA.slKerEquiv d F).symm (Matrix.SpecialLinearGroup.transvection hij 1)

theorem coe_elemSL (F : Type) [Field F] {i j : Fin d} (hij : i ≠ j) :
    (((elemSL F hij : LargeEvenSLGroup (Fin d) F) : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) =
      1 + Matrix.single i j 1 := by
  unfold elemSL
  rw [← TypeA.coe_slKerEquiv (K := F) (h := (TypeA.slKerEquiv d F).symm
    (Matrix.SpecialLinearGroup.transvection hij 1))]
  rw [MulEquiv.apply_symm_apply]
  exact Matrix.SpecialLinearGroup.transvection_coe hij 1

theorem map_elemSL (k : Subfield K) {i j : Fin d} (hij : i ≠ j) :
    Matrix.GeneralLinearGroup.map k.subtype
        ((elemSL k hij : LargeEvenSLGroup (Fin d) k) : GL (Fin d) k) =
      ((elemSL K hij : LargeEvenSLGroup (Fin d) K) : GL (Fin d) K) := by
  apply Units.ext
  rw [coe_glMap, coe_elemSL, coe_elemSL]
  rw [Matrix.map_add k.subtype (map_add k.subtype),
    Matrix.map_one k.subtype (map_zero k.subtype) (map_one k.subtype),
    Matrix.map_single, map_one]

theorem mem_scalars_of_commute_elemSL (A : GL (Fin d) K)
    (h : ∀ (i j : Fin d) (hij : i ≠ j),
      Commute A ((elemSL K hij : LargeEvenSLGroup (Fin d) K) : GL (Fin d) K)) :
    A ∈ LargeEvenScalars (Fin d) K := by
  rw [largeEvenScalars_def]
  rcases isEmpty_or_nonempty (Fin d) with h_empty | h_nonempty
  · refine ⟨1, ?_⟩
    apply Units.ext
    ext i j
    exact (h_empty.false i).elim
  · haveI : Nonempty (Fin d) := h_nonempty
    have hcomm : Pairwise fun i j : Fin d =>
        Commute (Matrix.single i j (1 : K)) (A : Matrix (Fin d) (Fin d) K) := by
      intro i j hij
      have h1 : Commute A ((elemSL K hij : LargeEvenSLGroup (Fin d) K) : GL (Fin d) K) :=
        h i j hij
      have h2 : (A : Matrix (Fin d) (Fin d) K) * (1 + Matrix.single i j 1) =
          (1 + Matrix.single i j 1) * (A : Matrix (Fin d) (Fin d) K) := by
        have := congrArg (fun g : GL (Fin d) K => (g : Matrix (Fin d) (Fin d) K)) h1.eq
        simpa only [Units.val_mul, coe_elemSL] using this
      have h3 : (A : Matrix (Fin d) (Fin d) K) * Matrix.single i j 1 =
          Matrix.single i j 1 * (A : Matrix (Fin d) (Fin d) K) := by
        rw [mul_add, mul_one, add_mul, one_mul] at h2
        exact add_left_cancel h2
      exact h3.symm
    obtain ⟨r, hr⟩ := Matrix.mem_range_scalar_of_commute_single hcomm
    have hr0 : r ≠ 0 := by
      intro h0
      have hunit : IsUnit (Matrix.scalar (Fin d) r) := by
        rw [hr]
        exact A.isUnit
      rw [h0] at hunit
      have hzero : IsUnit (0 : Matrix (Fin d) (Fin d) K) := by
        simpa using hunit
      exact not_isUnit_zero hzero
    refine ⟨Units.mk0 r hr0, ?_⟩
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0]
    exact hr

end CFSG.StandardType.LinearFieldFix

end
