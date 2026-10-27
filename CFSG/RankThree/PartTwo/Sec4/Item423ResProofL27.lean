module

public import CFSG.RankThree.PartTwo.Sec4.Item423StepsProofUAlpha
public import CFSG.RankThree.PartTwo.KFacts.KS10L27Aut
import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.RankThree.PartTwo.KFacts
open scoped MatrixGroups Pointwise

namespace Res462L27

theorem toPGL_eq_mk_of_smul {K : Type*} [Field K] (A : SL(2, K)) (M : GL (Fin 2) K) (r : K)
    (hr : r ≠ 0) (hM : (M : Matrix (Fin 2) (Fin 2) K) = r • (A : Matrix (Fin 2) (Fin 2) K)) :
    Matrix.ProjectiveSpecialLinearGroup.toPGL (psl2QuotientMap K A) =
      Matrix.ProjGenLinGroup.mk M := by
  show Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL A) = _
  rw [Matrix.ProjGenLinGroup.mk_eq_mk_iff]
  refine ⟨Units.mk0 r hr, Units.ext ?_⟩
  rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, hM, Matrix.scalar_apply]
  ext i j
  rw [Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul, mul_comm]
  rfl

theorem exists_mem_psl2FourGroup_of_commute {K : Type*} [Field K] [CharP K 3] {g : PGL2 K}
    (hI : g * Matrix.ProjectiveSpecialLinearGroup.toPGL (psl2QI K) =
      Matrix.ProjectiveSpecialLinearGroup.toPGL (psl2QI K) * g)
    (hJ : g * Matrix.ProjectiveSpecialLinearGroup.toPGL (psl2QJ K) =
      Matrix.ProjectiveSpecialLinearGroup.toPGL (psl2QJ K) * g) :
    ∃ w ∈ psl2FourGroup K, Matrix.ProjectiveSpecialLinearGroup.toPGL w = g := by
  induction g using Matrix.ProjGenLinGroup.induction_on with
  | mk M =>
    set NI : GL (Fin 2) K := Matrix.SpecialLinearGroup.toGL (sl2QI K) with hNI
    set NJ : GL (Fin 2) K := Matrix.SpecialLinearGroup.toGL (sl2QJ K) with hNJ
    have hNI' : Matrix.ProjectiveSpecialLinearGroup.toPGL (psl2QI K) =
        Matrix.ProjGenLinGroup.mk NI := rfl
    have hNJ' : Matrix.ProjectiveSpecialLinearGroup.toPGL (psl2QJ K) =
        Matrix.ProjGenLinGroup.mk NJ := rfl
    rw [hNI', ← map_mul, ← map_mul, Matrix.ProjGenLinGroup.mk_eq_mk_iff] at hI
    rw [hNJ', ← map_mul, ← map_mul, Matrix.ProjGenLinGroup.mk_eq_mk_iff] at hJ
    obtain ⟨u, hu⟩ := hI
    obtain ⟨v, hv⟩ := hJ
    have hmI : (M : Matrix (Fin 2) (Fin 2) K) * (NI : Matrix (Fin 2) (Fin 2) K) *
        Matrix.scalar (Fin 2) (u : K) = (NI : Matrix (Fin 2) (Fin 2) K) * M := by
      have := congrArg (fun X : GL (Fin 2) K => (X : Matrix (Fin 2) (Fin 2) K)) hu
      simpa [Matrix.GeneralLinearGroup.coe_scalar] using this
    have hmJ : (M : Matrix (Fin 2) (Fin 2) K) * (NJ : Matrix (Fin 2) (Fin 2) K) *
        Matrix.scalar (Fin 2) (v : K) = (NJ : Matrix (Fin 2) (Fin 2) K) * M := by
      have := congrArg (fun X : GL (Fin 2) K => (X : Matrix (Fin 2) (Fin 2) K)) hv
      simpa [Matrix.GeneralLinearGroup.coe_scalar] using this
    have hNIm : (NI : Matrix (Fin 2) (Fin 2) K) = !![0, 1; -1, 0] := rfl
    have hNJm : (NJ : Matrix (Fin 2) (Fin 2) K) = !![1, 1; 1, -1] := rfl
    set a := (M : Matrix (Fin 2) (Fin 2) K) 0 0
    set b := (M : Matrix (Fin 2) (Fin 2) K) 0 1
    set c := (M : Matrix (Fin 2) (Fin 2) K) 1 0
    set e := (M : Matrix (Fin 2) (Fin 2) K) 1 1
    have hM : (M : Matrix (Fin 2) (Fin 2) K) = !![a, b; c, e] := Matrix.eta_fin_two _
    have hdet : a * e - b * c ≠ 0 := by
      have h := (Matrix.GeneralLinearGroup.det M).ne_zero
      rwa [Matrix.GeneralLinearGroup.val_det_apply, hM, Matrix.det_fin_two_of] at h
    rw [hM, hNIm] at hmI
    rw [hM, hNJm] at hmJ
    have i00 := congrFun (congrFun hmI 0) 0
    have i01 := congrFun (congrFun hmI 0) 1
    have i10 := congrFun (congrFun hmI 1) 0
    have i11 := congrFun (congrFun hmI 1) 1
    have j00 := congrFun (congrFun hmJ 0) 0
    have j01 := congrFun (congrFun hmJ 0) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar_apply] at i00 i01 i10 i11 j00 j01
    have h3 : (3 : K) = 0 := CharP.cast_eq_zero K 3
    have h2 : (2 : K) ≠ 0 := by
      intro h
      exact one_ne_zero (show (1 : K) = 0 by linear_combination h3 - h)
    have huu : (u : K) * u = 1 := by
      by_contra hne
      have hne' : (u : K) * u - 1 ≠ 0 := sub_ne_zero.mpr hne
      have ha : a = 0 := by
        have : a * ((u : K) * u - 1) = 0 := by linear_combination (u : K) * i01 + i10
        exact (mul_eq_zero.mp this).resolve_right hne'
      have hb : b = 0 := by
        have : b * ((u : K) * u - 1) = 0 := by linear_combination (-(u : K)) * i00 - i11
        exact (mul_eq_zero.mp this).resolve_right hne'
      apply hdet
      rw [← i01, ← i00, ha, hb]
      ring
    rcases mul_self_eq_one_iff.mp huu with hu1 | hu1
    ·
      rw [hu1, mul_one] at i00 i01
      have hX : (a + b) * ((v : K) * v - 1) = 0 := by
        linear_combination (v : K) * j00 + j01 - i01 - (v : K) * i00
      have hY : (a + -b) * ((v : K) * v - 1) = 0 := by
        linear_combination (v : K) * j01 + j00 - i00 - (v : K) * i01
      have hvv : (v : K) * v = 1 := by
        by_contra hne
        have hne' : (v : K) * v - 1 ≠ 0 := sub_ne_zero.mpr hne
        have hX0 := (mul_eq_zero.mp hX).resolve_right hne'
        have hY0 := (mul_eq_zero.mp hY).resolve_right hne'
        have ha : a = 0 := by
          have : (2 : K) * a = 0 := by linear_combination hX0 + hY0
          exact (mul_eq_zero.mp this).resolve_left h2
        have hb : b = 0 := by
          have : (2 : K) * b = 0 := by linear_combination hX0 - hY0
          exact (mul_eq_zero.mp this).resolve_left h2
        apply hdet
        rw [← i01, ← i00, ha, hb]
        ring
      rcases mul_self_eq_one_iff.mp hvv with hv1 | hv1
      ·
        rw [hv1, mul_one] at j00
        have hb : b = 0 := by
          have : (2 : K) * b = 0 := by linear_combination j00 - i00
          exact (mul_eq_zero.mp this).resolve_left h2
        have ha : a ≠ 0 := by
          intro ha
          apply hdet
          rw [← i01, ← i00, ha, hb]
          ring
        refine ⟨psl2QuotientMap K 1, by rw [map_one]; exact Subgroup.one_mem _,
          toPGL_eq_mk_of_smul _ M a ha ?_⟩
        rw [hM, ← i01, ← i00, hb]
        ext i j
        fin_cases i <;> fin_cases j <;> simp
      ·
        rw [hv1] at j00
        have ha : a = 0 := by
          have : (2 : K) * a = 0 := by linear_combination -j00 + i00
          exact (mul_eq_zero.mp this).resolve_left h2
        have hb : b ≠ 0 := by
          intro hb
          apply hdet
          rw [← i01, ← i00, ha, hb]
          ring
        refine ⟨psl2QI K, Subgroup.subset_closure (by simp),
          toPGL_eq_mk_of_smul _ M b hb ?_⟩
        rw [hM, ← i01, ← i00, ha]
        ext i j
        fin_cases i <;> fin_cases j <;> simp [sl2QI]
    ·
      rw [hu1] at i00 i01
      have hX : (a + b) * ((v : K) - 1) = 0 := by
        linear_combination j00 - i00
      have hY : (a + -b) * ((v : K) + 1) = 0 := by
        linear_combination j01 - i01
      by_cases hab : a + b = 0
      ·
        have hb : b = -a := by linear_combination hab
        have ha : a ≠ 0 := by
          intro ha
          apply hdet
          rw [← i01, ← i00, hb, ha]
          ring
        refine ⟨psl2QI K * psl2QJ K, Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
          (Subgroup.subset_closure (by simp)), ?_⟩
        rw [← map_mul]
        refine toPGL_eq_mk_of_smul _ M a ha ?_
        rw [hM, ← i01, ← i00, hb, Matrix.SpecialLinearGroup.coe_mul]
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [sl2QI, sl2QJ]
      ·
        have hv1 : (v : K) = 1 := by
          have := (mul_eq_zero.mp hX).resolve_left hab
          linear_combination this
        rw [hv1] at hY
        have hb : b = a := by
          have : (2 : K) * (a - b) = 0 := by linear_combination hY
          have := (mul_eq_zero.mp this).resolve_left h2
          linear_combination -this
        have ha : a ≠ 0 := by
          intro ha
          apply hdet
          rw [← i01, ← i00, hb, ha]
          ring
        refine ⟨psl2QJ K, Subgroup.subset_closure (by simp),
          toPGL_eq_mk_of_smul _ M a ha ?_⟩
        rw [hM, ← i01, ← i00, hb]
        ext i j
        fin_cases i <;> fin_cases j <;> simp [sl2QJ]

theorem exists_conj_eq_of_card_four {V W : Subgroup (PSL2 (GaloisField 3 3))}
    (hV : Nat.card V = 4) (hW : Nat.card W = 4) :
    ∃ c : PSL2 (GaloisField 3 3), ∀ x, x ∈ V ↔ ∃ w ∈ W, c * w * c⁻¹ = x := by
  have key : ∀ {U : Subgroup (PSL2 (GaloisField 3 3))}, Nat.card U = 4 →
      ∃ P : Sylow 2 (PSL2 (GaloisField 3 3)), (P : Subgroup _) = U := by
    intro U hU
    have hUp : IsPGroup 2 U := IsPGroup.of_card (n := 2) (by rw [hU]; norm_num)
    obtain ⟨P, hUP⟩ := hUp.exists_le_sylow
    refine ⟨P, (Subgroup.eq_of_le_of_card_ge hUP ?_).symm⟩
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card (p := 2)).mp P.isPGroup'
    have hdvd : 2 ^ m ∣ 9828 := by
      rw [← hm, ← card_psl2_27]
      exact Subgroup.card_subgroup_dvd_card _
    have hm2 : m ≤ 2 := by
      by_contra h
      have h8 : 2 ^ 3 ∣ 9828 := (Nat.pow_dvd_pow 2 (by omega)).trans hdvd
      norm_num at h8
    rw [hU, hm]
    calc 2 ^ m ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hm2
      _ = 4 := by norm_num
  obtain ⟨P, hP⟩ := key hV
  obtain ⟨Q, hQ⟩ := key hW
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (PSL2 (GaloisField 3 3)) Q P
  refine ⟨c, fun x => ?_⟩
  rw [← hP, ← hQ, ← hc, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
  simp only [MulAut.smul_def, MulAut.conj_apply]

theorem card_psl2FourGroup_27 : Nat.card (psl2FourGroup (GaloisField 3 3)) = 4 := by
  set W := psl2FourGroup (GaloisField 3 3)
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card (p := 2)).mp (isPGroup_psl2FourGroup (K := GaloisField 3 3))
  have hdvd : 2 ^ m ∣ 9828 := by
    rw [← hm, ← card_psl2_27]
    exact Subgroup.card_subgroup_dvd_card _
  have hm2 : m ≤ 2 := by
    by_contra h
    have h8 : 2 ^ 3 ∣ 9828 := (Nat.pow_dvd_pow 2 (by omega)).trans hdvd
    norm_num at h8
  have h3 : 3 ≤ Nat.card W := by
    have hI : psl2QI (GaloisField 3 3) ∈ W := Subgroup.subset_closure (by simp)
    have hJ : psl2QJ (GaloisField 3 3) ∈ W := Subgroup.subset_closure (by simp)
    have hsub : ({1, psl2QI (GaloisField 3 3), psl2QJ (GaloisField 3 3)} :
        Set (PSL2 (GaloisField 3 3))) ⊆ (W : Set (PSL2 (GaloisField 3 3))) := by
      intro x hx
      rcases hx with rfl | rfl | rfl
      · exact W.one_mem
      · exact hI
      · exact hJ
    have hs : ({1, psl2QI (GaloisField 3 3), psl2QJ (GaloisField 3 3)} :
        Set (PSL2 (GaloisField 3 3))).ncard = 3 := by
      rw [Set.ncard_insert_of_notMem, Set.ncard_pair psl2QI_ne_psl2QJ]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨psl2QI_ne_one.symm, psl2QJ_ne_one.symm⟩
    have hc : Nat.card W = (W : Set (PSL2 (GaloisField 3 3))).ncard :=
      (Nat.card_coe_set_eq (W : Set (PSL2 (GaloisField 3 3))))
    have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [hs] at hle
    rw [hc]
    exact hle
  rw [hm] at h3 ⊢
  interval_cases m <;> omega

theorem mem_map_conj_of_fix_psl2_27 {V : Subgroup (PSL2 (GaloisField 3 3))}
    (hV4 : Nat.card V = 4) {τ : MulAut (PSL2 (GaloisField 3 3))} {k : ℕ}
    (hτ : τ ^ 2 ^ k = 1) (hfix : ∀ v ∈ V, τ v = v) :
    τ ∈ V.map (MulAut.conj : PSL2 (GaloisField 3 3) →* MulAut (PSL2 (GaloisField 3 3))) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcop : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left k (by norm_num)
  set ψ : MulAut (PSL2 (GaloisField 3 3)) →* (GaloisField 3 3 ≃+* GaloisField 3 3) :=
    SemidirectProduct.rightHom.comp (semilinearEquivAut (GaloisField 3 3)).symm.toMonoidHom
    with hψ
  have hψ1 : ψ τ = 1 := by
    have h1 : ψ τ ^ 2 ^ k = 1 := by rw [← map_pow, hτ, map_one]
    have : Finite (GaloisField 3 3 ≃+* GaloisField 3 3) :=
      Nat.finite_of_card_ne_zero (by rw [card_ringAut_galoisField_three_three]; norm_num)
    have h2 : ψ τ ^ 3 = 1 := by
      have := pow_card_eq_one' (G := GaloisField 3 3 ≃+* GaloisField 3 3) (x := ψ τ)
      rwa [card_ringAut_galoisField_three_three] at this
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop
      (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h2))
  obtain ⟨g, rfl⟩ := mem_range_pglAction_of_rightHom_eq_one hψ1
  obtain ⟨c, hVc⟩ := exists_conj_eq_of_card_four hV4 card_psl2FourGroup_27
  have hcomm : ∀ v ∈ V, g * Matrix.ProjectiveSpecialLinearGroup.toPGL v =
      Matrix.ProjectiveSpecialLinearGroup.toPGL v * g := by
    intro v hv
    have h1 := congrArg Matrix.ProjectiveSpecialLinearGroup.toPGL (hfix v hv)
    rw [toPGL_pglAction] at h1
    exact mul_inv_eq_iff_eq_mul.mp h1
  set C := Matrix.ProjectiveSpecialLinearGroup.toPGL c with hC
  set g' := C⁻¹ * g * C with hg'
  have hcomm' : ∀ w ∈ psl2FourGroup (GaloisField 3 3),
      g' * Matrix.ProjectiveSpecialLinearGroup.toPGL w =
        Matrix.ProjectiveSpecialLinearGroup.toPGL w * g' := by
    intro w hw
    have h1 := hcomm (c * w * c⁻¹) ((hVc _).mpr ⟨w, hw, rfl⟩)
    rw [map_mul, map_mul, map_inv, ← hC] at h1
    calc g' * Matrix.ProjectiveSpecialLinearGroup.toPGL w
        = C⁻¹ * (g * (C * Matrix.ProjectiveSpecialLinearGroup.toPGL w * C⁻¹)) * C := by
          rw [hg']; group
      _ = C⁻¹ * ((C * Matrix.ProjectiveSpecialLinearGroup.toPGL w * C⁻¹) * g) * C := by
          rw [h1]
      _ = Matrix.ProjectiveSpecialLinearGroup.toPGL w * g' := by rw [hg']; group
  obtain ⟨w₀, hw₀, hw₀g⟩ := exists_mem_psl2FourGroup_of_commute
    (hcomm' _ (Subgroup.subset_closure (Set.mem_insert _ _)))
    (hcomm' _ (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)))
  refine ⟨c * w₀ * c⁻¹, (hVc _).mpr ⟨w₀, hw₀, rfl⟩, ?_⟩
  have hg : Matrix.ProjectiveSpecialLinearGroup.toPGL (c * w₀ * c⁻¹) = g := by
    rw [map_mul, map_mul, map_inv, ← hC, hw₀g, hg']
    group
  change MulAut.conj (c * w₀ * c⁻¹) = pglAction (GaloisField 3 3) g
  rw [← pglAction_toPGL, hg]

end Res462L27

open Res462L27

theorem k462L27 : K462L27 := by
  intro S _ hS V hV4 τ hτ hfix
  obtain ⟨e₀⟩ := hS
  set e : S ≃* PSL2 (GaloisField 3 3) := e₀.trans (projSLEquivPSL _) with he
  obtain ⟨k, hk⟩ := hτ
  have h := mem_map_conj_of_fix_psl2_27 (V := V.map e.toMonoidHom)
    (by rw [Subgroup.card_map_of_injective e.injective]; exact hV4) (τ := MulAut.congr e τ)
    (k := k) (by rw [← map_pow, hk, map_one]) (by
      rintro _ ⟨v, hv, rfl⟩
      show e (τ (e.symm (e v))) = e v
      rw [MulEquiv.symm_apply_apply, hfix v hv])
  obtain ⟨_, ⟨v, hv, rfl⟩, hτv⟩ := h
  refine ⟨v, hv, (MulAut.congr e).injective ?_⟩
  rw [← hτv]
  ext x
  show e (v * e.symm x * v⁻¹) = e v * x * (e v)⁻¹
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

end CFSG.RankThree.PartTwo.Sec4
