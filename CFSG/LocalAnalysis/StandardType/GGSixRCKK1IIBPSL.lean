module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IIBPair
public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IIBPSLAux

public section

namespace CFSG.StandardType.RCKK1II

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.Open
open scoped Matrix commutatorElement

theorem rckIIPair_PSL
    (n : ℕ) (hn : 5 ≤ n) (hadm : StatedLieAdmissible .PSL n 2 1) : RCKIIPair .PSL n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  let F := GaloisField 2 1
  have hm : 0 < m := by omega
  have hm4 : 4 ≤ m := by omega
  let β : Fin m → ℤ := fun _ => 1
  have h0last : (0 : Fin (m + 1)) ≠ Fin.last m := by
    intro h; have := congrArg Fin.val h; simp at this; omega
  let k1 : Fin (m + 1) := ⟨1, by omega⟩
  have h01 : (0 : Fin (m + 1)) ≠ k1 := by
    intro h; have := congrArg Fin.val h; simp [k1] at this
  have hlast1 : Fin.last m ≠ k1 := by
    intro h; have := congrArg Fin.val h; simp [k1] at this; omega
  have hk10 : k1 ≠ 0 := h01.symm
  let x : (Matrix.SpecialLinearGroup (Fin (m + 1)) F) :=
    Matrix.SpecialLinearGroup.transvection h0last (1 : F)
  let y : (Matrix.SpecialLinearGroup (Fin (m + 1)) F) :=
    Matrix.SpecialLinearGroup.transvection h01 (1 : F)
  let j2 : (Matrix.SpecialLinearGroup (Fin (m + 1)) F) :=
    Matrix.SpecialLinearGroup.transvection hlast1 (1 : F)
  let σ : Equiv.Perm (Fin (m + 1)) := Equiv.swap k1 (Fin.last m)
  have hx2 : x * x = 1 := by
    show Matrix.SpecialLinearGroup.transvection h0last (1 : F) *
      Matrix.SpecialLinearGroup.transvection h0last (1 : F) = 1
    rw [← Matrix.SpecialLinearGroup.transvection_add]
    rw [show (1 : F) + 1 = 0 by rw [CharTwo.add_self_eq_zero]]
    exact Matrix.SpecialLinearGroup.transvection_coeff_zero h0last
  have hxne : x ≠ 1 := by
    intro h
    have h' : Matrix.SpecialLinearGroup.transvection h0last (1 : F) =
        Matrix.SpecialLinearGroup.transvection h0last (0 : F) := by
      rw [show Matrix.SpecialLinearGroup.transvection h0last (0 : F) = 1 from
        Matrix.SpecialLinearGroup.transvection_coeff_zero h0last]
      exact h
    exact one_ne_zero (Matrix.SpecialLinearGroup.transvection_injective h0last h')
  have hy2 : y * y = 1 := by
    show Matrix.SpecialLinearGroup.transvection h01 (1 : F) *
      Matrix.SpecialLinearGroup.transvection h01 (1 : F) = 1
    rw [← Matrix.SpecialLinearGroup.transvection_add]
    rw [show (1 : F) + 1 = 0 by rw [CharTwo.add_self_eq_zero]]
    exact Matrix.SpecialLinearGroup.transvection_coeff_zero h01
  have hyne : y ≠ 1 := by
    intro h
    have h' : Matrix.SpecialLinearGroup.transvection h01 (1 : F) =
        Matrix.SpecialLinearGroup.transvection h01 (0 : F) := by
      rw [show Matrix.SpecialLinearGroup.transvection h01 (0 : F) = 1 from
        Matrix.SpecialLinearGroup.transvection_coeff_zero h01]
      exact h
    exact one_ne_zero (Matrix.SpecialLinearGroup.transvection_injective h01 h')
  have hxy_comm : Commute x y :=
    Matrix.SpecialLinearGroup.commute_transvection h0last h01 h0last.symm h01.symm (1 : F) (1 : F)
  have hxy : x * y = y * x := hxy_comm.eq
  have hxy_ne : x ≠ y := by
    intro h
    have hx_eq : x = Matrix.SpecialLinearGroup.transvection h0last (1 : F) := rfl
    have hy_eq : y = Matrix.SpecialLinearGroup.transvection h01 (1 : F) := rfl
    rw [hx_eq, hy_eq] at h
    have h1 : (Matrix.SpecialLinearGroup.transvection h0last (1 : F) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) F) 0 (Fin.last m) = 1 := by
      rw [Matrix.SpecialLinearGroup.transvection_coe]
      simp [Matrix.add_apply, Matrix.one_apply_ne h0last, Matrix.single_apply]
    have h2 : (Matrix.SpecialLinearGroup.transvection h01 (1 : F) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) F) 0 (Fin.last m) = 0 := by
      rw [Matrix.SpecialLinearGroup.transvection_coe]
      simp [Matrix.add_apply, Matrix.one_apply_ne h0last, Matrix.single_apply, hlast1.symm]
    rw [h] at h1
    rw [h2] at h1
    exact zero_ne_one h1
  have hxy1 : x * y ≠ 1 := by
    intro h
    exact hxy_ne (by
      calc x = x⁻¹ := (inv_eq_of_mul_eq_one_right hx2).symm
        _ = y := inv_eq_of_mul_eq_one_right h)
  let V : Subgroup (Matrix.SpecialLinearGroup (Fin (m + 1)) F) := rckPSL_four x y hx2 hy2 hxy
  let N : Subgroup (Matrix.SpecialLinearGroup (Fin (m + 1)) F) :=
    Subgroup.normalizer
      (Subgroup.zpowers x : Set (Matrix.SpecialLinearGroup (Fin (m + 1)) F))
  let R : Subgroup (Matrix.SpecialLinearGroup (Fin (m + 1)) F) := rckPSL_rad (F := F) (m := m)
  have hxR : x ∈ R := rckPSL_transvection_mem_rad h0last rfl h0last.symm
  have hyR : y ∈ R := rckPSL_transvection_mem_rad h01 rfl hk10
  have hβ : β ∈ (SpecialLinear.rootDatum m F).roots := rckPSL_one_mem_roots hm
  have hlong : GGLongRoot (SpecialLinear.rootDatum m F) β := by
    refine ⟨1, β, hβ, ?_, ?_⟩
    · intro δ hδ
      change CFSG.LieType.Steinberg.ht δ ≤ CFSG.LieType.Steinberg.ht β
      have hβht : CFSG.LieType.Steinberg.ht β = (m : ℤ) := by
        simp [β, CFSG.LieType.Steinberg.ht]
      rw [hβht]
      exact rckPSL_ht_root_le hδ
    · rfl
  have hroot : (SpecialLinear.rootDatum m F).rootGroup β = Subgroup.zpowers x := by
    have hstd : SpecialLinear.toStd m β =
        Pi.single 0 1 - Pi.single (Fin.last m) 1 := rckPSL_toStd_one hm
    have h1 : (SpecialLinear.rootDatum m F).rootGroup β = SpecialLinear.rootSubgroup m F h0last :=
      SpecialLinear.rootGroup_eq m F h0last hstd
    rw [h1]
    ext g
    rw [SpecialLinear.mem_rootSubgroup, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨c, rfl⟩
      rcases rckPSL_eq_zero_or_one c with hc | hc
      · refine ⟨0, ?_⟩
        rw [hc, Matrix.SpecialLinearGroup.transvection_coeff_zero, zpow_zero]
      · refine ⟨1, ?_⟩
        rw [hc, zpow_one]
    · rintro ⟨n, hn⟩
      have hcases : x ^ n = 1 ∨ x ^ n = x := by
        rcases Int.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
        · left; rw [hk, ← two_mul, zpow_mul, zpow_two, hx2, one_zpow]
        · right; rw [hk, zpow_add, zpow_mul, zpow_two, hx2, one_zpow, one_mul, zpow_one]
      rcases hcases with hc | hc
      · exact ⟨0, by rw [← hn, hc, Matrix.SpecialLinearGroup.transvection_coeff_zero]⟩
      · exact ⟨1, by rw [← hn, hc]⟩
  have hxV : x ∈ V := by simp [V]
  have habel : IsElemAbelian 2 V := rckPSL_four_isElemAbelian hx2 hy2 hxy
  have hcardV : Nat.card V = 4 := by
    have h3 : y ∉ ({x * y} : Set (Matrix.SpecialLinearGroup (Fin (m + 1)) F)) := by
      simp only [Set.mem_singleton_iff]
      intro h
      exact hxne (by
        calc x = x * 1 := (mul_one x).symm
          _ = x * (y * y⁻¹) := by rw [mul_inv_cancel]
          _ = (x * y) * y⁻¹ := by group
          _ = y * y⁻¹ := by rw [← h]
          _ = 1 := mul_inv_cancel y)
    have h2 : x ∉ ({y, x * y} : Set (Matrix.SpecialLinearGroup (Fin (m + 1)) F)) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      refine ⟨hxy_ne, fun h => hyne ?_⟩
      calc y = 1 * y := (one_mul y).symm
        _ = (x⁻¹ * x) * y := by rw [inv_mul_cancel]
        _ = x⁻¹ * (x * y) := by group
        _ = x⁻¹ * x := by rw [← h]
        _ = 1 := inv_mul_cancel x
    have h1 : (1 : (Matrix.SpecialLinearGroup (Fin (m + 1)) F)) ∉
        ({x, y, x * y} : Set (Matrix.SpecialLinearGroup (Fin (m + 1)) F)) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨fun h => hxne h.symm, fun h => hyne h.symm, fun h => hxy1 h.symm⟩
    rw [show Nat.card V =
        (V : Set (Matrix.SpecialLinearGroup (Fin (m + 1)) F)).ncard from
      Nat.card_coe_set_eq (V : Set (Matrix.SpecialLinearGroup (Fin (m + 1)) F))]
    change ({1, x, y, x * y} : Set (Matrix.SpecialLinearGroup (Fin (m + 1)) F)).ncard = 4
    rw [Set.ncard_insert_of_notMem h1, Set.ncard_insert_of_notMem h2,
      Set.ncard_insert_of_notMem h3, Set.ncard_singleton]
  have hR_le_N : R ≤ N := by
    have hRC : R ≤
        Subgroup.centralizer
          (Subgroup.zpowers x : Set (Matrix.SpecialLinearGroup (Fin (m + 1)) F)) := by
      intro r hr
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      change (∃ q : ℤ, x ^ q = s) at hs
      obtain ⟨q, rfl⟩ := hs
      exact ((show Commute r x from rckPSL_rad_comm hr hxR).symm.zpow_left q).eq
    exact hRC.trans (Subgroup.centralizer_le_normalizer _)
  have hR_2 : IsPGroup 2 R := by
    rw [isPGroup_iff_orderOf_dvd_pow]
    intro g
    refine ⟨1, ?_⟩
    rw [pow_one, orderOf_dvd_iff_pow_eq_one]
    apply Subtype.ext
    obtain ⟨a, ha, hga⟩ := g.2
    rw [Subgroup.coe_pow, Subgroup.coe_one, pow_two]
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
    rw [hga, rckPSL_row_sq ha]
  have hR_normal : (R.subgroupOf N).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hR_le_N]
    intro r n hr hn
    obtain ⟨a, ha, hra⟩ := hr
    change r.1 = 1 + rckPSL_row a at hra
    have hnn : n.1 * (n⁻¹).1 = 1 := by
      have h := congrArg Subtype.val (mul_inv_cancel n)
      change n.1 * (n⁻¹).1 = 1 at h
      exact h
    have hnn' : (n⁻¹).1 * n.1 = 1 := by
      have h := congrArg Subtype.val (inv_mul_cancel n)
      change (n⁻¹).1 * n.1 = 1 at h
      exact h
    have hx_conj : n * x * n⁻¹ = x := by
      have hmem : n * x * n⁻¹ ∈ Subgroup.zpowers x :=
        (Subgroup.mem_normalizer_iff.mp hn x).mp (Subgroup.mem_zpowers x)
      obtain ⟨q, hq⟩ := Subgroup.mem_zpowers_iff.mp hmem
      have hcases : x ^ q = 1 ∨ x ^ q = x := by
        rcases Int.even_or_odd q with ⟨k, hk⟩ | ⟨k, hk⟩
        · left; rw [hk, ← two_mul, zpow_mul, zpow_two, hx2, one_zpow]
        · right; rw [hk, zpow_add, zpow_mul, zpow_two, hx2, one_zpow, one_mul, zpow_one]
      rcases hcases with h1 | h1
      · exfalso
        apply hxne
        calc x = n⁻¹ * (n * x * n⁻¹) * n := by group
          _ = n⁻¹ * 1 * n := by rw [← hq, h1]
          _ = 1 := by simp
      · rwa [← hq]
    set E : Matrix (Fin (m + 1)) (Fin (m + 1)) F :=
      Matrix.single 0 (Fin.last m) 1 with hEdef
    set e0 : Fin (m + 1) → F :=
      Pi.single (0 : Fin (m + 1)) (1 : F) with he0def
    set em : Fin (m + 1) → F :=
      Pi.single (Fin.last m) (1 : F) with hemdef
    have hxmat : x.1 = 1 + E := by
      rw [show x = Matrix.SpecialLinearGroup.transvection h0last (1 : GaloisField 2 1) from rfl,
        Matrix.SpecialLinearGroup.transvection_coe]
    have hE_conj : n.1 * E * (n⁻¹).1 = E := by
      have h := congrArg Subtype.val hx_conj
      change n.1 * x.1 * (n⁻¹).1 = x.1 at h
      rw [hxmat] at h
      have h' : 1 + n.1 * E * (n⁻¹).1 = 1 + E := by
        calc 1 + n.1 * E * (n⁻¹).1
            = n.1 * (1 + E) * (n⁻¹).1 := by
              rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, hnn]
          _ = 1 + E := h
      exact add_left_cancel h'
    have h2 : E *ᵥ em = e0 := by
      rw [hEdef, hemdef, he0def, rckPSL_single_mulVec, Pi.single_eq_same, one_smul]
    have hEn : n.1 * E = E * n.1 := by
      have h := congrArg (fun A : Matrix (Fin (m + 1)) (Fin (m + 1)) F =>
        A * n.1) hE_conj
      rw [Matrix.mul_assoc, hnn', Matrix.mul_one] at h
      exact h
    have hn_e0 : n.1 *ᵥ e0 = e0 := by
      have hm : n.1 *ᵥ e0 = ((n.1 *ᵥ em) (Fin.last m)) • e0 := by
        calc n.1 *ᵥ e0 = n.1 *ᵥ (E *ᵥ em) := by rw [h2]
          _ = (n.1 * E) *ᵥ em := by rw [Matrix.mulVec_mulVec]
          _ = (E * n.1) *ᵥ em := by rw [hEn]
          _ = E *ᵥ (n.1 *ᵥ em) := by rw [Matrix.mulVec_mulVec]
          _ = ((n.1 *ᵥ em) (Fin.last m)) • e0 := by rw [hEdef, rckPSL_single_mulVec]
      have hc : (n.1 *ᵥ em) (Fin.last m) = n.1 0 0 := by
        have h0 := congrFun hm 0
        rw [Pi.smul_apply, smul_eq_mul, he0def, Pi.single_eq_same, mul_one,
          Matrix.mulVec_single_one] at h0
        exact h0.symm
      rw [hc] at hm
      have h00 : n.1 0 0 ≠ 0 := by
        intro hz
        have hzero : n.1 *ᵥ e0 = 0 := by rw [hm, hz, zero_smul]
        have he0z : e0 = 0 := by
          calc e0 = (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *ᵥ e0 := by
                rw [Matrix.one_mulVec]
            _ = ((n⁻¹).1 * n.1) *ᵥ e0 := by rw [hnn']
            _ = (n⁻¹).1 *ᵥ (n.1 *ᵥ e0) := by rw [Matrix.mulVec_mulVec]
            _ = (n⁻¹).1 *ᵥ 0 := by rw [hzero]
            _ = 0 := by rw [Matrix.mulVec_zero]
        have h0 := congrFun he0z 0
        rw [he0def, Pi.single_eq_same, Pi.zero_apply] at h0
        exact one_ne_zero h0
      rcases rckPSL_eq_zero_or_one (n.1 0 0) with h0 | h0
      · exact absurd h0 h00
      · rw [hm, h0, one_smul]
    have hn_col : ∀ i, n.1 i 0 = if i = 0 then 1 else 0 := by
      intro i
      have h := congrFun hn_e0 i
      rw [Matrix.mulVec_single_one, he0def, Pi.single_apply] at h
      exact h
    have hnin_e0 : (n⁻¹).1 *ᵥ e0 = e0 := by
      calc (n⁻¹).1 *ᵥ e0
          = (n⁻¹).1 *ᵥ (n.1 *ᵥ e0) := by rw [hn_e0]
        _ = ((n⁻¹).1 * n.1) *ᵥ e0 := by rw [Matrix.mulVec_mulVec]
        _ = (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *ᵥ e0 := by rw [hnn']
        _ = e0 := by rw [Matrix.one_mulVec]
    have hninv_col : ∀ i, (n⁻¹).1 i 0 = if i = 0 then 1 else 0 := by
      intro i
      have h := congrFun hnin_e0 i
      rw [Matrix.mulVec_single_one, he0def, Pi.single_apply] at h
      exact h
    set a' : Fin (m + 1) → F := fun j => ∑ l, a l * (n⁻¹).1 l j with ha'def
    have ha'0 : a' 0 = 0 := by
      rw [ha'def]
      show (∑ l, a l * (n⁻¹).1 l 0) = 0
      rw [Finset.sum_eq_single 0]
      · simp [ha]
      · intro l _ hl
        rw [hninv_col l, if_neg hl, mul_zero]
      · intro h; exact absurd (Finset.mem_univ 0) h
    refine ⟨a', ha'0, ?_⟩
    have hMconj : n.1 * rckPSL_row a * (n⁻¹).1 = rckPSL_row a' := by
      apply Matrix.mulVec_injective
      funext v
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, rckPSL_row_mulVec, rckPSL_row_mulVec,
        Matrix.mulVec_smul, hn_e0]
      congr 1
      rw [ha'def]
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      rw [mul_assoc]
    change n.1 * r.1 * (n⁻¹).1 = 1 + rckPSL_row a'
    rw [hra, Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, hnn, hMconj]

  have hR_pcore : R ≤ pCoreOf 2 N :=
    CFSG.LargeEvenClassification.Helpers.normal_pSubgroup_le_pCoreOf R N hR_le_N hR_normal hR_2
  have hV_le_R : V ≤ R := by
    intro v hv
    have hv' : (v : (Matrix.SpecialLinearGroup (Fin (m + 1)) F)) = 1 ∨
        (v : (Matrix.SpecialLinearGroup (Fin (m + 1)) F)) = x ∨
        (v : (Matrix.SpecialLinearGroup (Fin (m + 1)) F)) = y ∨
        (v : (Matrix.SpecialLinearGroup (Fin (m + 1)) F)) = x * y := by
      have h : (v : (Matrix.SpecialLinearGroup (Fin (m + 1)) F)) ∈
          ({1, x, y, x * y} : Set (Matrix.SpecialLinearGroup (Fin (m + 1)) F)) := hv
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h
    rcases hv' with h | h | h | h
    · rw [h]; exact R.one_mem
    · rw [h]; exact hxR
    · rw [h]; exact hyR
    · rw [h]; exact R.mul_mem hxR hyR
  have hpcore : V ≤ pCoreOf 2 (Subgroup.normalizer
      ((SpecialLinear.rootDatum m F).rootGroup β :
        Set (Matrix.SpecialLinearGroup (Fin (m + 1)) F))) := by
    rw [hroot]
    exact hV_le_R.trans hR_pcore
  have hconj : ∀ v ∈ V, v ≠ 1 →
      ∃ j : (Matrix.SpecialLinearGroup (Fin (m + 1)) F), v = j * x * j⁻¹ := by
    intro v hv hv1
    have hv' : (v : (Matrix.SpecialLinearGroup (Fin (m + 1)) F)) = 1 ∨
        (v : (Matrix.SpecialLinearGroup (Fin (m + 1)) F)) = x ∨
        (v : (Matrix.SpecialLinearGroup (Fin (m + 1)) F)) = y ∨
        (v : (Matrix.SpecialLinearGroup (Fin (m + 1)) F)) = x * y := by
      have h : (v : (Matrix.SpecialLinearGroup (Fin (m + 1)) F)) ∈
          ({1, x, y, x * y} : Set (Matrix.SpecialLinearGroup (Fin (m + 1)) F)) := hv
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h
    rcases hv' with h | h | h | h
    · exact absurd h hv1
    · exact ⟨1, by rw [h]; simp⟩
    · refine ⟨CFSG.SeitzReduction.LinearPilot.permSL σ, ?_⟩
      have hσsymm : σ.symm = σ := Equiv.symm_swap k1 (Fin.last m)
      have hσ0 : σ.symm 0 = 0 := by
        rw [hσsymm]
        exact Equiv.swap_apply_of_ne_of_ne h01 h0last
      have hσlast : σ.symm (Fin.last m) = k1 := by
        rw [hσsymm]
        exact Equiv.swap_apply_right k1 (Fin.last m)
      have htrans : Matrix.SpecialLinearGroup.transvection (σ.symm.injective.ne h0last) (1 : F) =
          Matrix.SpecialLinearGroup.transvection h01 (1 : F) := by
        apply Subtype.ext
        rw [Matrix.SpecialLinearGroup.transvection_coe, Matrix.SpecialLinearGroup.transvection_coe,
          hσ0, hσlast]
      rw [h, show x = Matrix.SpecialLinearGroup.transvection h0last (1 : F) from rfl,
        CFSG.SeitzReduction.LinearPilot.permSL_mul_transvection_mul_inv (K := F) σ h0last (1 : F)]
      exact htrans.symm
    · refine ⟨j2, ?_⟩
      have hcomm : ⁅x, j2⁆ = y := by
        show ⁅Matrix.SpecialLinearGroup.transvection h0last (1 : F),
            Matrix.SpecialLinearGroup.transvection hlast1 (1 : F)⁆ =
          Matrix.SpecialLinearGroup.transvection h01 (1 : F)
        rw [Matrix.SpecialLinearGroup.commutatorElement_transvection h0last hlast1 h01,
          one_mul]
      have hxy_conj : x * y = j2 * x * j2⁻¹ := by
        have h := hcomm
        rw [commutatorElement_def] at h
        calc x * y = x * (x * j2 * x⁻¹ * j2⁻¹) := by rw [← h]
          _ = (x * x) * (j2 * x⁻¹ * j2⁻¹) := by group
          _ = j2 * x⁻¹ * j2⁻¹ := by rw [hx2, one_mul]
          _ = j2 * x * j2⁻¹ := by rw [inv_eq_of_mul_eq_one_right hx2]
      rw [h]
      exact hxy_conj
  exact ⟨β, x, V, hβ, hlong, hroot, hx2, hxne, hxV, habel, hcardV, hpcore, hconj⟩


end CFSG.StandardType.RCKK1II
