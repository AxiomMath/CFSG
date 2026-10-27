module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IDefs
public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1ILongNotShortF4
public import CFSG.LocalAnalysis.StandardType.GGRootInvolutionSp
public import CFSG.LieType.Universal.SymplecticExtras.Matrices

public section

namespace CFSG.StandardType.RCKK1I

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.RCKRP
  CFSG.StandardType.LieOddCover
open CFSG.Open (StatedLieTag StatedLieAdmissible)
open CFSG.StandardType.RCKSmall (RCKSmallTag)
open CFSG.LieType.Steinberg
open CFSG.LieType.Universal.Symplectic
open CFSG.LieType.Universal.Symplectic.SpExtras
open TauCeti.GLSymplecticFin
open CFSG.StandardType.GGRootSp

private theorem rckK1Ilns_allEven_stdVec_iff_longIdx {n : ℕ} (r : RootSubgroupIndex n) :
    AllEven (stdVec r) ↔
      (∃ i : Fin n, r = .positiveLong i) ∨ (∃ i : Fin n, r = .negativeLong i) := by
  cases r with
  | positiveLong i =>
    refine ⟨fun _ => Or.inl ⟨i, rfl⟩, fun _ a => ?_⟩
    simp only [stdVec, Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite, mul_one, mul_zero]
    split_ifs <;> simp
  | negativeLong i =>
    refine ⟨fun _ => Or.inr ⟨i, rfl⟩, fun _ a => ?_⟩
    simp only [stdVec, Pi.smul_apply, smul_eq_mul, Pi.single_apply, Pi.neg_apply]
    split_ifs <;> simp
  | difference i j hij =>
    refine ⟨fun h => ?_, fun h => ?_⟩
    · exfalso
      have h1 := h i
      simp only [stdVec, Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne hij,
        sub_zero] at h1
      norm_num at h1
    · rcases h with ⟨k, hk⟩ | ⟨k, hk⟩ <;> simp at hk
  | positiveSum i j hij =>
    refine ⟨fun h => ?_, fun h => ?_⟩
    · exfalso
      have h1 := h i
      simp only [stdVec, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne (ne_of_lt hij),
        add_zero] at h1
      norm_num at h1
    · rcases h with ⟨k, hk⟩ | ⟨k, hk⟩ <;> simp at hk
  | negativeSum i j hij =>
    refine ⟨fun h => ?_, fun h => ?_⟩
    · exfalso
      have h1 := h i
      simp only [stdVec, Pi.neg_apply, Pi.add_apply, Pi.single_eq_same,
        Pi.single_eq_of_ne (ne_of_lt hij), add_zero, neg_one_mul, neg_eq_zero] at h1
      norm_num at h1
    · rcases h with ⟨k, hk⟩ | ⟨k, hk⟩ <;> simp at hk

private theorem rckK1Ilns_ggLongRoot_iff_allEven {n : ℕ} (hn : 2 ≤ n) {F : Type} [Field F]
    {γ : Fin n → ℤ} (hγ : γ ∈ (rootDatum n F).roots) :
    GGLongRoot (rootDatum n F) γ ↔ AllEven (toStd n γ) := by
  set i0 : Fin n := ⟨0, by omega⟩ with hi0
  set i1 : Fin n := ⟨1, by omega⟩ with hi1
  have h01 : i0 < i1 := by rw [Fin.lt_def]; simp [i0, i1]
  obtain ⟨θ, hθ, hθstd⟩ := exists_root_toStd_eq (n := n) (.positiveLong i0)
  obtain ⟨θs, hθs, hθsstd⟩ := exists_root_toStd_eq (n := n) (.positiveSum i0 i1 h01)
  have hθe : AllEven (toStd n θ) := by
    rw [hθstd]
    intro a
    simp only [stdVec, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    split_ifs <;> simp
  have hθso : ¬ AllEven (toStd n θs) := by
    rw [hθsstd]
    intro h
    have h1 := h i0
    simp only [stdVec, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne (ne_of_lt h01),
      add_zero] at h1
    norm_num at h1
  have hhtθ : 2 * ht θ = 2 * (2 * (n : ℤ) - 1) := by
    rw [two_mul_ht, hθstd, stdVec, map_nsmul, lv_single]
    simp only [i0, Fin.val_mk, Fin.val_zero, nsmul_eq_mul, Nat.cast_ofNat]
    ring
  have hmaxθ : ∀ δ ∈ (rootDatum n F).roots, ht δ ≤ ht θ := by
    intro δ hδ
    obtain ⟨r, hr⟩ := exists_stdVec_of_mem_roots (n := n) hδ
    have h1 := two_mul_ht (n := n) δ
    rw [← hr] at h1
    have h2 : lv n (stdVec r) ≤ 2 * ht θ := by
      rw [hhtθ]
      exact lv_stdVec_le r
    have h3 : 2 * ht δ ≤ 2 * ht (θ : Fin n → ℤ) := le_trans (le_of_eq h1) h2
    omega
  constructor
  · intro h
    obtain ⟨w, γ₀, hγ₀, hmax₀, hγeq⟩ := h
    let γ₀' : Fin n → ℤ := γ₀
    have hmax₀' : ∀ δ ∈ (rootDatum n F).roots, ht δ ≤ ht γ₀' := fun δ hδ => hmax₀ δ hδ
    have hγeq' : γ = weylAction (rootDatum n F).isFiniteType w γ₀' := hγeq
    have hAllEvenγ₀ : AllEven (toStd n γ₀') := by
      have hle : ht γ₀' ≤ ht θ := hmaxθ γ₀ hγ₀
      have hge : ht θ ≤ ht γ₀' := hmax₀' θ hθ
      have hht : ht γ₀' = ht θ := le_antisymm hle hge
      obtain ⟨r₀, hr₀⟩ := exists_stdVec_of_mem_roots (n := n) hγ₀
      have h2 : 4 * (n : ℤ) - 4 < lv n (stdVec r₀) := by
        have h1 := two_mul_ht (n := n) γ₀'
        rw [← hr₀] at h1
        rw [← h1, hht, hhtθ]
        omega
      have h4 := stdVec_eq_of_lv_lt hn r₀ h2
      have hγ₀_eq : γ₀' = θ := by
        apply toStd_inj (n := n)
        rw [← hr₀, h4, hθstd]
      rw [hγ₀_eq]
      exact hθe
    rw [hγeq']
    exact (allEven_toStd_weylAction_iff (n := n)
      (show (coxeterMatrix (isFiniteType_cartanC n)).Group from w)
      γ₀').mpr hAllEvenγ₀
  · intro h
    obtain ⟨w, c, hc, hγeq⟩ := exists_weylAction_theta_or_thetaS hθ hθs hθe hθso hγ
    rcases hc with hc | hc
    · rw [hc] at hγeq
      exact ⟨w, θ, hθ, hmaxθ, hγeq⟩
    · rw [hc] at hγeq
      exfalso
      have hγs : AllEven (toStd n (weylAction (rootDatum n F).isFiniteType w θs)) := by
        rw [← hγeq]
        exact h
      have hγs' : AllEven (toStd n θs) :=
        (allEven_toStd_weylAction_iff (n := n)
          (show (coxeterMatrix (isFiniteType_cartanC n)).Group from w) θs).mp hγs
      exact hθso hγs'

private theorem rckK1Ilns_rank_E_long_le_one {F : Type} [Field F] (r : RootSubgroupIndex 2)
    (hr : (∃ i : Fin 2, r = .positiveLong i) ∨ (∃ i : Fin 2, r = .negativeLong i)) :
    (E F r).rank ≤ 1 := by
  rcases hr with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · rw [E, Matrix.single_eq_single_vecMulVec_single]
    exact Matrix.rank_vecMulVec_le _ _
  · rw [E, Matrix.single_eq_single_vecMulVec_single]
    exact Matrix.rank_vecMulVec_le _ _

private theorem rckK1Ilns_rank_ge_two_of_det {F : Type} [Field F]
    {M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F} {r c : Fin 2 → Fin 2 ⊕ Fin 2}
    (h : (M.submatrix r c).det ≠ 0) : 2 ≤ M.rank := by
  have hrank : (M.submatrix r c).rank = 2 := by
    simpa using Matrix.rank_of_det_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero h)
  calc 2 = (M.submatrix r c).rank := hrank.symm
    _ ≤ M.rank := Matrix.rank_submatrix_le M r c

private theorem rckK1Ilns_rank_E_short_ge_two {F : Type} [Field F] (r : RootSubgroupIndex 2)
    (hr : ¬ ((∃ i : Fin 2, r = .positiveLong i) ∨ (∃ i : Fin 2, r = .negativeLong i))) :
    2 ≤ (E F r).rank := by
  cases r with
  | positiveLong i => exact absurd (Or.inl ⟨i, rfl⟩) hr
  | negativeLong i => exact absurd (Or.inr ⟨i, rfl⟩) hr
  | difference i j hij =>
    refine rckK1Ilns_rank_ge_two_of_det (M := E F (.difference i j hij))
      (r := ![Sum.inl i, Sum.inr j]) (c := ![Sum.inl j, Sum.inr i]) ?_
    rw [Matrix.det_fin_two]
    simp [E, Matrix.sub_apply, Matrix.single_apply, hij, hij.symm]
  | positiveSum i j hij =>
    refine rckK1Ilns_rank_ge_two_of_det (M := E F (.positiveSum i j hij))
      (r := ![Sum.inl i, Sum.inl j]) (c := ![Sum.inr j, Sum.inr i]) ?_
    rw [Matrix.det_fin_two]
    simp [E, Matrix.add_apply, Matrix.single_apply, hij.ne, hij.ne']
  | negativeSum i j hij =>
    refine rckK1Ilns_rank_ge_two_of_det (M := E F (.negativeSum i j hij))
      (r := ![Sum.inr i, Sum.inr j]) (c := ![Sum.inl j, Sum.inl i]) ?_
    rw [Matrix.det_fin_two]
    simp [E, Matrix.add_apply, Matrix.single_apply, hij.ne, hij.ne']

private theorem rckK1Ilns_sp4
    {f : ℕ} (hadm : StatedLieAdmissible .PSp 2 2 f)
    {β γ : Fin 2 → ℤ} (hβ : β ∈ (rootDatum 2 (GaloisField 2 f)).roots)
    (hlong : GGLongRoot (rootDatum 2 (GaloisField 2 f)) β)
    (hγ : γ ∈ (rootDatum 2 (GaloisField 2 f)).roots)
    (hshort : ¬ GGLongRoot (rootDatum 2 (GaloisField 2 f)) γ)
    (h2γ : 2 • γ ∉ (rootDatum 2 (GaloisField 2 f)).roots)
    (u : StatedSp 2 (GaloisField 2 f)) :
    (rootDatum 2 (GaloisField 2 f)).rootGroup β ⊓
      ((rootDatum 2 (GaloisField 2 f)).rootGroup γ).map (MulAut.conj u).toMonoidHom = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  obtain ⟨hxβ, hxγ⟩ := Subgroup.mem_inf.1 hx
  obtain ⟨y, hyγ, hyx⟩ := Subgroup.mem_map.1 hxγ
  have hyx' : u * y * u⁻¹ = x := (MulAut.conj_apply u y).symm.trans hyx
  by_contra hx1
  have hy1 : y ≠ 1 := by
    intro hy
    exact hx1 (by rw [← hyx, hy]; exact map_one (MulAut.conj u))
  obtain ⟨rβ, hrβ⟩ := exists_stdVec_of_mem_roots (n := 2) hβ
  obtain ⟨rγ, hrγ⟩ := exists_stdVec_of_mem_roots (n := 2) hγ
  have hlongIdx : (∃ i : Fin 2, rβ = .positiveLong i) ∨
      (∃ i : Fin 2, rβ = .negativeLong i) := by
    have h1 : AllEven (toStd 2 β) := (rckK1Ilns_ggLongRoot_iff_allEven (by norm_num) hβ).1 hlong
    rw [← hrβ] at h1
    exact (rckK1Ilns_allEven_stdVec_iff_longIdx rβ).1 h1
  have hshortIdx : ¬ ((∃ i : Fin 2, rγ = .positiveLong i) ∨
      (∃ i : Fin 2, rγ = .negativeLong i)) := by
    intro h1
    have h2 : AllEven (toStd 2 γ) := by
      rw [← hrγ]
      exact (rckK1Ilns_allEven_stdVec_iff_longIdx rγ).2 h1
    exact hshort ((rckK1Ilns_ggLongRoot_iff_allEven (by norm_num) hγ).2 h2)
  obtain ⟨c, rfl⟩ := (mem_rootGroup_iff hrβ).1 hxβ
  obtain ⟨d, rfl⟩ := (mem_rootGroup_iff hrγ).1 hyγ
  have hc : c ≠ 0 := by
    rintro rfl
    exact hx1 (elt_zero rβ)
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact hy1 (elt_zero rγ)
  have hdet : IsUnit (mat 2 (GaloisField 2 f) u).det :=
    (Matrix.isUnit_iff_isUnit_det (A := mat 2 (GaloisField 2 f) u)).mp
      ((isUnit_iff_exists_inv.mpr ⟨u⁻¹, by simp⟩).map (mat 2 (GaloisField 2 f)))
  have hmat_inv : mat 2 (GaloisField 2 f) u⁻¹ = (mat 2 (GaloisField 2 f) u)⁻¹ :=
    (Matrix.inv_eq_right_inv (by rw [← map_mul, mul_inv_cancel, map_one])).symm
  have hmat : mat 2 (GaloisField 2 f) (elt rβ c) =
      mat 2 (GaloisField 2 f) u * mat 2 (GaloisField 2 f) (elt rγ d) *
        (mat 2 (GaloisField 2 f) u)⁻¹ := by
    rw [← hyx']
    calc mat 2 (GaloisField 2 f) (u * elt rγ d * u⁻¹)
        = mat 2 (GaloisField 2 f) (u * elt rγ d) * mat 2 (GaloisField 2 f) u⁻¹ :=
          map_mul (mat 2 (GaloisField 2 f)) (u * elt rγ d) u⁻¹
      _ = (mat 2 (GaloisField 2 f) u * mat 2 (GaloisField 2 f) (elt rγ d)) *
            mat 2 (GaloisField 2 f) u⁻¹ := by
          rw [map_mul (mat 2 (GaloisField 2 f)) u (elt rγ d)]
      _ = mat 2 (GaloisField 2 f) u * mat 2 (GaloisField 2 f) (elt rγ d) *
            (mat 2 (GaloisField 2 f) u)⁻¹ := by
          rw [hmat_inv]
  have hAu : mat 2 (GaloisField 2 f) u * (mat 2 (GaloisField 2 f) u)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv (A := mat 2 (GaloisField 2 f) u) hdet
  have hxmat : mat 2 (GaloisField 2 f) (elt rβ c) - 1 =
      mat 2 (GaloisField 2 f) u * (mat 2 (GaloisField 2 f) (elt rγ d) - 1) *
        (mat 2 (GaloisField 2 f) u)⁻¹ := by
    rw [hmat, mul_sub, mul_one, sub_mul, hAu]
  have hrank_eq : (mat 2 (GaloisField 2 f) (elt rβ c) - 1).rank =
      (mat 2 (GaloisField 2 f) (elt rγ d) - 1).rank := by
    rw [hxmat,
      Matrix.rank_mul_eq_left_of_isUnit_det (mat 2 (GaloisField 2 f) u)⁻¹
        (mat 2 (GaloisField 2 f) u * (mat 2 (GaloisField 2 f) (elt rγ d) - 1))
        (Matrix.isUnit_nonsing_inv_det (A := mat 2 (GaloisField 2 f) u) hdet),
      Matrix.rank_mul_eq_right_of_isUnit_det (mat 2 (GaloisField 2 f) u)
        (mat 2 (GaloisField 2 f) (elt rγ d) - 1) hdet]
  have hlong_rank : (mat 2 (GaloisField 2 f) (elt rβ c) - 1).rank ≤ 1 := by
    rw [mat_elt, add_sub_cancel_left,
      Matrix.rank_smul_of_mem_nonZeroDivisors _ (mem_nonZeroDivisors_of_ne_zero hc)]
    exact rckK1Ilns_rank_E_long_le_one rβ hlongIdx
  have hshort_rank : 2 ≤ (mat 2 (GaloisField 2 f) (elt rγ d) - 1).rank := by
    rw [mat_elt, add_sub_cancel_left,
      Matrix.rank_smul_of_mem_nonZeroDivisors _ (mem_nonZeroDivisors_of_ne_zero hd0)]
    exact rckK1Ilns_rank_E_short_ge_two rγ hshortIdx
  omega

theorem rckK1I_longNotShort
    {t : StatedLieTag} {n f : ℕ} (ht : (t = .PSp ∧ n = 2) ∨ t = .F4) (hadm : StatedLieAdmissible t n 2 f)
    {β γ : Fin (ggU t n f).D.rank → ℤ} (hβ : β ∈ (ggU t n f).D.roots) (hlong : GGLongRoot (ggU t n f).D β)
    (hγ : γ ∈ (ggU t n f).D.roots) (hshort : ¬ GGLongRoot (ggU t n f).D γ) (h2γ : 2 • γ ∉ (ggU t n f).D.roots)
    (u : (ggU t n f).K) :
    (ggU t n f).D.rootGroup β ⊓ ((ggU t n f).D.rootGroup γ).map (MulAut.conj u).toMonoidHom = ⊥ := by
  rcases ht with ⟨rfl, rfl⟩ | rfl
  · change (rootDatum 2 (GaloisField 2 f)).rootGroup β ⊓
      ((rootDatum 2 (GaloisField 2 f)).rootGroup γ).map
        (MulAut.conj u).toMonoidHom = ⊥
    exact rckK1Ilns_sp4 hadm hβ hlong hγ hshort h2γ u
  · exact rckK1I_longNotShort_F4 hadm hβ hlong hγ hshort h2γ u

end CFSG.StandardType.RCKK1I
