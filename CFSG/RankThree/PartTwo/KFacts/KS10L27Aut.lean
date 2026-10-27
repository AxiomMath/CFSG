module

public import CFSG.RankThree.PartTwo.KFacts.KS10L27

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open scoped MatrixGroups

theorem pgl2_pow_three_eq_one_of_commute_upper {K : Type*} [Field K] [CharP K 3] {s : K}
    (hs : s ≠ 0) {g : PGL2 K}
    (hg : g * Matrix.ProjectiveSpecialLinearGroup.toPGL (psl2QuotientMap K (sl2UpperUnipotent s)) =
      Matrix.ProjectiveSpecialLinearGroup.toPGL (psl2QuotientMap K (sl2UpperUnipotent s)) * g) :
    g ^ 3 = 1 := by
  induction g using Matrix.ProjGenLinGroup.induction_on with
  | mk M =>
    set N : GL (Fin 2) K := Matrix.SpecialLinearGroup.toGL (sl2UpperUnipotent s) with hN
    have hN' : Matrix.ProjectiveSpecialLinearGroup.toPGL
        (psl2QuotientMap K (sl2UpperUnipotent s)) = Matrix.ProjGenLinGroup.mk N := rfl
    rw [hN', ← map_mul, ← map_mul, Matrix.ProjGenLinGroup.mk_eq_mk_iff] at hg
    obtain ⟨u, hu⟩ := hg
    have hmat : (M : Matrix (Fin 2) (Fin 2) K) * (N : Matrix (Fin 2) (Fin 2) K) *
        Matrix.scalar (Fin 2) (u : K) = (N : Matrix (Fin 2) (Fin 2) K) * M := by
      have := congrArg (fun X : GL (Fin 2) K => (X : Matrix (Fin 2) (Fin 2) K)) hu
      simpa [Matrix.GeneralLinearGroup.coe_scalar] using this
    have hNm : (N : Matrix (Fin 2) (Fin 2) K) = !![1, s; 0, 1] := rfl
    set a := (M : Matrix (Fin 2) (Fin 2) K) 0 0
    set b := (M : Matrix (Fin 2) (Fin 2) K) 0 1
    set c := (M : Matrix (Fin 2) (Fin 2) K) 1 0
    set e := (M : Matrix (Fin 2) (Fin 2) K) 1 1
    have hM : (M : Matrix (Fin 2) (Fin 2) K) = !![a, b; c, e] := Matrix.eta_fin_two _
    have hdet : a * e - b * c ≠ 0 := by
      have h := (Matrix.GeneralLinearGroup.det M).ne_zero
      rwa [Matrix.GeneralLinearGroup.val_det_apply, hM, Matrix.det_fin_two_of] at h
    rw [hM, hNm] at hmat
    have h00 := congrFun (congrFun hmat 0) 0
    have h01 := congrFun (congrFun hmat 0) 1
    have h10 := congrFun (congrFun hmat 1) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar_apply] at h00 h01 h10
    have hu1 : (u : K) = 1 := by
      by_contra hu1
      have hu1' : (u : K) - 1 ≠ 0 := sub_ne_zero.mpr hu1
      have hc : c = 0 := by
        have : c * ((u : K) - 1) = 0 := by rw [mul_sub, mul_one, h10, sub_self]
        exact (mul_eq_zero.mp this).resolve_right hu1'
      have ha : a = 0 := by
        rw [hc, mul_zero, add_zero] at h00
        have : a * ((u : K) - 1) = 0 := by rw [mul_sub, mul_one, h00, sub_self]
        exact (mul_eq_zero.mp this).resolve_right hu1'
      apply hdet
      rw [ha, hc]
      ring
    rw [hu1, mul_one] at h00 h01
    have hc : c = 0 := by
      have : s * c = 0 := by linear_combination -h00
      exact (mul_eq_zero.mp this).resolve_left hs
    have hae : a = e := by
      have : s * (a - e) = 0 := by linear_combination h01
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hs)
    have ha0 : a ≠ 0 := by
      intro ha
      apply hdet
      rw [← hae, ha, hc]
      ring
    rw [← map_pow, Matrix.ProjGenLinGroup.mk_eq_one,
      Matrix.GeneralLinearGroup.center_eq_range_scalar]
    refine ⟨Units.mk0 (a ^ 3) (pow_ne_zero 3 ha0), Units.ext ?_⟩
    have h3 : (3 : K) = 0 := CharP.cast_eq_zero K 3
    rw [Matrix.GeneralLinearGroup.coe_scalar, Units.val_pow_eq_pow_val, hM, ← hae, hc]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar_apply]
    all_goals first
      | linear_combination (a ^ 2 * b) * h3
      | linear_combination (-(a ^ 2 * b)) * h3

theorem eq_one_of_mulAut_psl2_27_of_fix {τ : MulAut (PSL2 (GaloisField 3 3))} {k : ℕ}
    (hτ : τ ^ 2 ^ k = 1) {x : PSL2 (GaloisField 3 3)} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hfix : τ x = x) : τ = 1 := by
  set K := GaloisField 3 3 with hKdef
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcop : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left k (by norm_num)
  set ψ : MulAut (PSL2 K) →* (K ≃+* K) :=
    SemidirectProduct.rightHom.comp (semilinearEquivAut K).symm.toMonoidHom with hψ
  have hψ1 : ψ τ = 1 := by
    have h1 : ψ τ ^ 2 ^ k = 1 := by rw [← map_pow, hτ, map_one]
    have : Finite (K ≃+* K) :=
      Nat.finite_of_card_ne_zero (by rw [card_ringAut_galoisField_three_three]; norm_num)
    have h2 : ψ τ ^ 3 = 1 := by
      have := pow_card_eq_one' (G := K ≃+* K) (x := ψ τ)
      rwa [card_ringAut_galoisField_three_three] at this
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop
      (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h2))
  obtain ⟨g, rfl⟩ := mem_range_pglAction_of_rightHom_eq_one hψ1
  have hg : g ^ 2 ^ k = 1 := pglAction_injective (by rw [map_pow, hτ, map_one])
  have hcomm : g * Matrix.ProjectiveSpecialLinearGroup.toPGL x =
      Matrix.ProjectiveSpecialLinearGroup.toPGL x * g := by
    have h1 := congrArg Matrix.ProjectiveSpecialLinearGroup.toPGL hfix
    rw [toPGL_pglAction] at h1
    exact mul_inv_eq_iff_eq_mul.mp h1
  have hK : Nat.card K = 3 ^ 3 := GaloisField.card 3 3 (by norm_num)
  have hP : IsPGroup 3 (Subgroup.zpowers x) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, orderOf_eq_prime hx3 hx1, pow_one])
  obtain ⟨c, hc⟩ := exists_map_conj_le_psl2UpperUnipotentSubgroup hK hP
  have hcx : c * x * c⁻¹ ∈ psl2UpperUnipotentSubgroup K := hc ⟨x, Subgroup.mem_zpowers x, rfl⟩
  obtain ⟨s, hs⟩ := (mem_psl2UpperUnipotentSubgroup_iff _).mp hcx
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [sl2UpperUnipotent_zero, map_one] at hs
    apply hx1
    calc x = c⁻¹ * (c * x * c⁻¹) * c := by group
      _ = 1 := by rw [hs]; group
  set C := Matrix.ProjectiveSpecialLinearGroup.toPGL c with hC
  set g' := C * g * C⁻¹ with hg'
  have hg'comm : g' * Matrix.ProjectiveSpecialLinearGroup.toPGL
      (psl2QuotientMap K (sl2UpperUnipotent s)) =
      Matrix.ProjectiveSpecialLinearGroup.toPGL (psl2QuotientMap K (sl2UpperUnipotent s)) *
        g' := by
    rw [← hs, map_mul, map_mul, map_inv, ← hC, hg']
    calc C * g * C⁻¹ * (C * Matrix.ProjectiveSpecialLinearGroup.toPGL x * C⁻¹) =
        C * (g * Matrix.ProjectiveSpecialLinearGroup.toPGL x) * C⁻¹ := by group
      _ = C * (Matrix.ProjectiveSpecialLinearGroup.toPGL x * g) * C⁻¹ := by rw [hcomm]
      _ = C * Matrix.ProjectiveSpecialLinearGroup.toPGL x * C⁻¹ * (C * g * C⁻¹) := by group
  have h3 : g' ^ 3 = 1 := pgl2_pow_three_eq_one_of_commute_upper hs0 hg'comm
  have h2 : g' ^ 2 ^ k = 1 := by rw [hg', conj_pow, hg]; group
  have hg'1 : g' = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop
    (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h3))
  have hg1 : g = 1 := by
    calc g = C⁻¹ * g' * C := by rw [hg']; group
      _ = 1 := by rw [hg'1]; group
  rw [hg1, map_one]

theorem eq_one_of_mulAut_of_mulEquiv_psl2_27 {X : Type*} [Group X]
    (e : X ≃* PSL2 (GaloisField 3 3)) {τ : MulAut X} {k : ℕ} (hτ : τ ^ 2 ^ k = 1) {x : X}
    (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) (hfix : τ x = x) : τ = 1 := by
  have h := eq_one_of_mulAut_psl2_27_of_fix (τ := MulAut.congr e τ) (k := k)
    (by rw [← map_pow, hτ, map_one]) (x := e x) (by rw [← map_pow, hx3, map_one])
    (by rwa [Ne, MulEquiv.map_eq_one_iff])
    (by
      show e (τ (e.symm (e x))) = e x
      rw [MulEquiv.symm_apply_apply, hfix])
  exact (MulAut.congr e).injective (h.trans (map_one _).symm)

section Three

variable {F : Type*} [Field F]

theorem card_psl2_of_card_three [Finite F] (hF : Nat.card F = 3) : Nat.card (PSL2 F) = 12 := by
  rw [psl2_card_formula F ⟨3, 1, Nat.prime_three, by decide, le_rfl, by rw [hF]; norm_num⟩, hF]
  norm_num

theorem card_psl2_27 : Nat.card (PSL2 (GaloisField 3 3)) = 9828 := by
  have hK : Nat.card (GaloisField 3 3) = 27 := by
    rw [GaloisField.card 3 3 (by norm_num)]
    norm_num
  rw [psl2_card_formula _ ⟨3, 3, Nat.prime_three, by decide, by norm_num, by rw [hK]; norm_num⟩,
    hK]
  norm_num

variable [CharP F 3]

theorem isElemAbelian_psl2FourGroup : CFSG.Assembly.IsElemAbelian 2 (psl2FourGroup F) := by
  have hcomm : ({psl2QI F, psl2QJ F} : Set (PSL2 F)).Pairwise Commute := by
    rintro x (rfl | rfl) y (rfl | rfl) hxy
    · exact absurd rfl hxy
    · exact psl2QI_mul_comm
    · exact psl2QI_mul_comm.symm
    · exact absurd rfl hxy
  exact ⟨Subgroup.isMulCommutative_closure hcomm, fun x hx => psl2FourGroup_pow_two hx⟩

theorem psl2QJ_ne_one : psl2QJ F ≠ 1 := by
  intro h
  apply psl2QI_ne_one (K := F)
  have h1 := psl2U1_conj_QI (K := F)
  rw [h] at h1
  calc psl2QI F = (psl2U1 F)⁻¹ * (psl2U1 F * psl2QI F * (psl2U1 F)⁻¹) * psl2U1 F := by group
    _ = 1 := by rw [h1]; group

theorem psl2QI_ne_psl2QJ : psl2QI F ≠ psl2QJ F := by
  intro h
  apply psl2QJ_ne_one (F := F)
  have h1 := psl2U1_conj_QJ (K := F)
  rw [← h, ← pow_two, psl2QI_sq] at h1
  rw [← h]
  calc psl2QI F = (psl2U1 F)⁻¹ * (psl2U1 F * psl2QI F * (psl2U1 F)⁻¹) * psl2U1 F := by group
    _ = 1 := by rw [h1]; group

theorem psl2U1_ne_one : psl2U1 F ≠ 1 := by
  intro h
  apply psl2QI_ne_psl2QJ (F := F)
  have h1 := psl2U1_conj_QI (K := F)
  rw [h] at h1
  simpa using h1

theorem orderOf_psl2U1 : orderOf (psl2U1 F) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime
    (psl2Upper_pow_three ((mem_psl2UpperUnipotentSubgroup_iff _).mpr ⟨1, rfl⟩)) psl2U1_ne_one

theorem psl2U1_conj_psl2QI_ne : psl2U1 F * psl2QI F * (psl2U1 F)⁻¹ ≠ psl2QI F := by
  rw [psl2U1_conj_QI]
  exact fun h => psl2QI_ne_psl2QJ h.symm

theorem card_psl2FourGroup_of_card_three [Finite F] (hF : Nat.card F = 3) :
    Nat.card (psl2FourGroup F) = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := (isPGroup_psl2FourGroup (K := F)).exists_card_eq
  have hdvd : 2 ^ m ∣ 12 := by
    rw [← hm, ← card_psl2_of_card_three hF]
    exact Subgroup.card_subgroup_dvd_card _
  have hm2 : m ≤ 2 := by
    by_contra hm2
    have : 2 ^ 3 ∣ 12 := (Nat.pow_dvd_pow 2 (by omega)).trans hdvd
    norm_num at this
  have hI : psl2QI F ∈ psl2FourGroup F := Subgroup.subset_closure (by simp)
  have hJ : psl2QJ F ∈ psl2FourGroup F := Subgroup.subset_closure (by simp)
  interval_cases m
  · exfalso
    rw [pow_zero] at hm
    have := Subgroup.eq_bot_of_card_eq _ hm
    rw [this, Subgroup.mem_bot] at hI
    exact psl2QI_ne_one hI
  · exfalso
    rw [pow_one] at hm
    have hz : Subgroup.zpowers (psl2QI F) = psl2FourGroup F := by
      apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hI)
      rw [hm, Nat.card_zpowers, orderOf_eq_prime psl2QI_sq psl2QI_ne_one]
    rw [← hz] at hJ
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hJ
    rw [zpow_eq_zpow_emod k (by exact_mod_cast psl2QI_sq : psl2QI F ^ (2 : ℤ) = 1)] at hk
    have : k % 2 = 0 ∨ k % 2 = 1 := by omega
    rcases this with h0 | h1
    · rw [h0, zpow_zero] at hk
      exact psl2QJ_ne_one hk.symm
    · rw [h1, zpow_one] at hk
      exact psl2QI_ne_psl2QJ hk
  · rw [hm]
    norm_num

theorem psl2FourGroup_normal_of_card_three [Finite F] (hF : Nat.card F = 3) :
    (psl2FourGroup F).Normal := by
  rw [← Subgroup.normalizer_eq_top_iff]
  apply Subgroup.eq_top_of_card_eq
  have hdvd4 : 4 ∣ Nat.card (Subgroup.normalizer (psl2FourGroup F : Set (PSL2 F))) := by
    rw [← card_psl2FourGroup_of_card_three hF]
    exact Subgroup.card_dvd_of_le Subgroup.le_normalizer
  have hdvd3 : 3 ∣ Nat.card (Subgroup.normalizer (psl2FourGroup F : Set (PSL2 F))) := by
    rw [← orderOf_psl2U1 (F := F)]
    exact Subgroup.orderOf_dvd_natCard _ psl2U1_mem_normalizer_psl2FourGroup
  have h12 := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 4 3) hdvd4 hdvd3
  rw [card_psl2_of_card_three hF]
  refine Nat.dvd_antisymm ?_ h12
  rw [← card_psl2_of_card_three hF]
  exact Subgroup.card_subgroup_dvd_card _

end Three

end CFSG.RankThree.PartTwo.KFacts
