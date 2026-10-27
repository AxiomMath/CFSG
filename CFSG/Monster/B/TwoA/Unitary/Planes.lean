module

public import CFSG.Monster.B.TwoA.Unitary.PlanesPrelude
public import Certificates.Certificate3175

public import CFSG.Monster.B.TwoA.Unitary.PlanesBase
import all CFSG.Monster.B.TwoA.Unitary.PlanesBase

public import CFSG.Monster.B.TwoA.Unitary.Form
public meta import CFSG.Monster.B.TwoA.Unitary.Form
public import CFSG.Monster.B.TwoA.Unitary.PlanesInputs
public import Certificates.Certificate3175Base
import all CFSG.Fischer.F4
public import Certificates.Certificate3080Base

public section

namespace CFSG.Monster.B.TwoA.Unitary

open CFSG.Fischer Matrix
open CFSG.Monster.B.Classical.UnitarySix (bar bar_add bar_mul bar_bar bar_zero bar_one
  bar_eq_zero_iff)

theorem rrefOK_all : ∀ j, rrefOK j :=
  Certificates.certificate3175.1

theorem isotropic_rows :
    ∀ (j : Fin 891) (a b : Fin 3), hU (planeRow j a) (planeRow j b) = 0 :=
  Certificates.certificate3175.2.1

theorem expand_rows (j : Fin 891) (c : Fin 3 → F4) :
    expand j (∑ a, c a • planeRow j a) = ∑ a, c a • planeRow j a := by
  rw [expand]
  refine Finset.sum_congr rfl fun b _ => ?_
  congr 1
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, rrefOK_all j _ b, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem mem_plane_iff (j : Fin 891) (x : V6) :
    x ∈ plane j ↔ expand j x = x := by
  constructor
  · intro hx
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun F4).1 hx
    exact expand_rows j c
  · intro hx
    rw [← hx, expand]
    exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)

theorem linearIndependent_planeRow (j : Fin 891) :
    LinearIndependent F4 (planeRow j) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg b
  have h := congrFun hg (piv (planeRow j b))
  simpa [Finset.sum_apply, rrefOK_all j _ b] using h

theorem finrank_plane (j : Fin 891) :
    Module.finrank F4 (plane j) = 3 := by
  rw [plane, finrank_span_eq_card (linearIndependent_planeRow j), Fintype.card_fin]

theorem isMaxIso_plane (j : Fin 891) : IsMaxIso (plane j) := by
  refine ⟨finrank_plane j, fun s hs t ht => ?_⟩
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun F4).1 hs
  obtain ⟨d, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun F4).1 ht
  rw [hU_sum_sum]
  simp [isotropic_rows]

theorem distinct_check : ∀ i j : Fin 891, i < j → ∃ b : Fin 3,
    expand i (planeRow j b) ≠ planeRow j b :=
  Certificates.certificate3175.2.2.1

theorem rows_mem_plane {i j : Fin 891} (h : plane i = plane j)
    (b : Fin 3) :
    expand i (planeRow j b) = planeRow j b := by
  rw [← mem_plane_iff, h]
  exact Submodule.subset_span ⟨b, rfl⟩

theorem plane_injective : Function.Injective plane := by
  intro i j h
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · obtain ⟨b, hb⟩ := distinct_check i j hlt
    exact hb (rows_mem_plane h b)
  · obtain ⟨b, hb⟩ := distinct_check j i hlt
    exact hb (rows_mem_plane h.symm b)

theorem b6Mat_det : ∀ k : Fin 17, (b6Mat k).det = 1 :=
  Certificates.certificate3175.2.2.2.1

theorem b6Mat_gram :
    ∀ k : Fin 17, b6Mat k * hGram * (barM (b6Mat k))ᵀ = hGram :=
  Certificates.certificate3175.2.2.2.2.1

theorem b6N_det (k : Fin 17) : (b6N k).det = 1 := by
  rw [b6N, barPowM]
  split_ifs
  · exact b6Mat_det k
  · rw [det_barM, b6Mat_det, bar_one]

theorem b6N_gram (k : Fin 17) :
    b6N k * hGram * (barM (b6N k))ᵀ = hGram := by
  rw [b6N, barPowM]
  split_ifs
  · exact b6Mat_gram k
  · have h := congrArg barM (b6Mat_gram k)
    rw [barM_mul, barM_mul] at h
    have hH : barM hGram = hGram := by
      ext i j
      simp only [barM, map_apply, hGram, of_apply]
      split_ifs <;> simp
    have hT : barM ((barM (b6Mat k))ᵀ) = (barM (barM (b6Mat k)))ᵀ := rfl
    rw [hH, hT] at h
    exact h

@[expose] noncomputable def b6SU (k : Fin 17) : SUh :=
  ⟨GeneralLinearGroup.mkOfDetNeZero (b6N k) (by rw [b6N_det]; exact one_ne_zero),
    mem_SUh_iff_gram.2 ⟨b6N_det k, b6N_gram k⟩⟩

theorem coe_b6SU (k : Fin 17) :
    (((b6SU k : SUh) : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) = b6N k := rfl

@[expose] noncomputable def slElt (k : Fin 17) : SigmaU6 :=
  ⟨(b6SU k : SUh ⧸ Zh), Multiplicative.ofAdd (b6Frob k)⟩

theorem sigmaAct_slElt (P : Submodule F4 V6) (k : Fin 17) :
    sigmaAct P (slElt k) = subMul (subBarPow (b6Frob k) P) (b6Mat k) := by
  rw [slElt, sigmaAct_mk, subBarPow_subMul, coe_b6SU, b6N, barPowM]
  congr 1
  by_cases h : b6Frob k = 0
  · rw [ite_eq_left h, ite_eq_left h]
  · rw [ite_eq_right h, ite_eq_right h, barM_barM]

theorem sigmaAct_slElt_span (S : Set V6) (k : Fin 17) :
    sigmaAct (Submodule.span F4 S) (slElt k) = Submodule.span F4 (b6Map k '' S) := by
  rw [sigmaAct_slElt, subBarPow_span, subMul_span, Set.image_image]
  rfl

theorem imgOK : ∀ (k : Fin 17) (j : Fin 891) (a : Fin 3),
    expand (b6Iso (n6perm k j)) (imgRow k j a) = imgRow k j a :=
  Certificates.certificate3175.2.2.2.2.2

theorem linearIndependent_imgRow (k : Fin 17) (j : Fin 891) :
    LinearIndependent F4 (imgRow k j) :=
  linearIndependent_vecMul (linearIndependent_barPowV (linearIndependent_planeRow _) _)
    (by rw [b6Mat_det]; exact one_ne_zero)

theorem sigmaAct_slElt_plane (k : Fin 17) (j : Fin 891) :
    sigmaAct (plane (b6Iso j)) (slElt k) = plane (b6Iso (n6perm k j)) := by
  have hspan : sigmaAct (plane (b6Iso j)) (slElt k) =
      Submodule.span F4 (Set.range (imgRow k j)) := by
    rw [plane, sigmaAct_slElt_span, ← Set.range_comp]
    rfl
  rw [hspan]
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    exact (mem_plane_iff _ _).2 (imgOK k j a)
  · rw [finrank_span_eq_card (linearIndependent_imgRow k j), Fintype.card_fin, finrank_plane]

theorem eq_one_of_sigmaAct_plane (x : SigmaU6)
    (h : ∀ j, sigmaAct (plane j) x = plane j) :
    x = 1 := by
  obtain ⟨xl, xr⟩ := x
  induction xl using QuotientGroup.induction_on with
  | H g =>
  induction xr using Multiplicative.rec with
  | ofAdd ε =>
  set N : Matrix (Fin 6) (Fin 6) F4 :=
    (((g : SUh) : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) with hN
  have hfix : ∀ j, subBarPow ε (subMul (plane j) N) = plane j := fun j => h j
  have hstab : ∀ j, subBar (plane j) = plane j → subMul (plane j) N = plane j := by
    intro j hj
    have e := congrArg (subBarPow ε) (hfix j)
    rw [subBarPow_subBarPow] at e
    rw [e]
    by_cases hε : ε = 0
    · rw [subBarPow, ite_eq_left hε]
    · rw [subBarPow, ite_eq_right hε, hj]
  have hrow : ∀ j, subBar (plane j) = plane j → ∀ x ∈ plane j, x ᵥ* N ∈ plane j := by
    intro j hj x hx
    rw [← hstab j hj]
    exact mem_subMul_of_mem hx N
  have hdiag : ∀ i t : Fin 6, i ≠ t → N i t = 0 := by
    intro i t hit
    obtain ⟨⟨a, ha⟩, hz, hb⟩ := coordPlane_ok i t hit
    have hmem := hrow _ (subBar_plane_of hb) _ (mem_plane_row _ a)
    rw [ha] at hmem
    have := plane_coord_zero hz hmem
    rwa [single_vecMul] at this
  have hrel : ∀ (j : Fin 891) (a : Fin 3) (i₁ i₂ t₁ t₂ : Fin 6),
      subBar (plane j) = plane j → planeRow j a = Pi.single i₁ 1 + Pi.single i₂ 1 →
      (∀ b, planeRow j b t₂ = planeRow j b t₁) → i₁ ≠ i₂ → t₁ = i₁ → t₂ = i₂ →
      N i₂ i₂ = N i₁ i₁ := by
    intro j a i₁ i₂ t₁ t₂ hj hra hcoord hne h1 h2
    have hmem := hrow j hj _ (mem_plane_row j a)
    rw [hra] at hmem
    have := plane_coord_eq hcoord hmem
    subst h1 h2
    rw [add_vecMul, Pi.add_apply, Pi.add_apply, single_vecMul, single_vecMul, single_vecMul,
      single_vecMul, hdiag t₁ t₂ hne, hdiag t₂ t₁ (Ne.symm hne), zero_add, add_zero] at this
    exact this
  have hst := fun j (hj : j ∈ ([0, 6, 5, 54, 4, 50, 49, 304, 97, 98, 110] : List (Fin 891))) =>
    subBar_plane_of (coord_planes_stable j hj)
  have e33 := hrel 97 0 0 3 0 3 (hst 97 (by decide)) planeRow_97.1 rows_97.1 (by decide) rfl rfl
  have e44 := hrel 97 1 1 4 1 4 (hst 97 (by decide)) planeRow_97.2.1 rows_97.2.1 (by decide) rfl
    rfl
  have e55 := hrel 97 2 2 5 2 5 (hst 97 (by decide)) planeRow_97.2.2 rows_97.2.2 (by decide) rfl
    rfl
  have e4 := hrel 98 0 0 4 0 4 (hst 98 (by decide)) planeRow_98 rows_98 (by decide) rfl rfl
  have e5 := hrel 110 0 0 5 0 5 (hst 110 (by decide)) planeRow_110 rows_110 (by decide) rfl rfl
  have hscal : ∀ i, N i i = N 0 0 := by
    intro i
    fin_cases i
    · rfl
    · exact e44.symm.trans e4
    · exact e55.symm.trans e5
    · exact e33
    · exact e4
    · exact e5
  have hN0 : N = Matrix.scalar (Fin 6) (N 0 0) := by
    ext i t
    rw [Matrix.scalar_apply, diagonal_apply]
    by_cases hit : i = t
    · subst hit
      rw [ite_eq_left rfl, hscal]
    · rw [ite_eq_right hit, hdiag i t hit]
  have hdet : N.det = 1 := (g.2).1
  have hc : N 0 0 ≠ 0 := by
    intro h0
    rw [hN0, h0, Matrix.scalar_apply, det_diagonal] at hdet
    simp at hdet
  have hg : g ∈ Zh := ⟨Units.mk0 _ hc, Units.ext (by rw [GeneralLinearGroup.coe_scalar]; exact hN0)⟩
  have hg1 : (g : SUh ⧸ Zh) = 1 := (QuotientGroup.eq_one_iff g).2 hg
  have hε : ε = 0 := by
    by_contra hε
    have hs8 : subMul (plane 8) N = plane 8 := by
      rw [hN0]
      have := subMul_scalar (plane 8) (Units.mk0 _ hc)
      rwa [Units.val_mk0] at this
    have h8 := hfix 8
    rw [hs8, subBarPow, ite_eq_right hε] at h8
    apply frob_moves_8
    rw [← mem_plane_iff]
    have hm : planeRow 8 0 ∈ subBar (plane 8) := by rw [h8]; exact mem_plane_row 8 0
    exact (mem_subBar).1 hm
  subst hε
  rw [hg1]
  rfl

end CFSG.Monster.B.TwoA.Unitary
