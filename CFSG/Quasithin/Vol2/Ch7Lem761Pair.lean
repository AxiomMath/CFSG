module

public import CFSG.Quasithin.Vol2.Ch7Lem761
public import CFSG.Quasithin.Vol2.Ch7QuadPair
public import CFSG.Quasithin.Background.HSL3Inner

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem offender_quad_761 (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hmod : StmtFSUModule) (h734 : Stmt7_3_4) (h771 : Stmt7_7_1) (hyp : Hyp7_0_2 G T L I)
    (h731 : Hyp7_3_1 T L I) [IsMulCommutative ↥(fsuV T I)] (hrow : Row711SL3Pair T L I 1)
    (hV : IsElemAbelian 2 (fsuV T I)) {g : G} (hg : IsWOffenderAt T (fsuV T I) g) :
    mQuot (fsuV T I) (fsuV T I ⊓ Subgroup.normalizer (conjSubgroup (fsuV T I) g : Set G)) = 1 ∧
      (∀ v ∈ fsuV T I, ∀ a ∈ conjSubgroup (fsuV T I) g ⊓ Subgroup.normalizer (fsuV T I : Set G),
        a * v * a⁻¹ * v⁻¹ ∈ Subgroup.centralizer (conjSubgroup (fsuV T I) g : Set G)) ∧
      IsWOffenderAt T (fsuV T I) g⁻¹ ∧
      (gammaCheck 1 (autI hV (conjSubgroup (fsuV T I) g ⊓
        Subgroup.normalizer (fsuV T I : Set G)))).map (E3.valHom hV) =
          fsuV T I ⊓ Subgroup.normalizer (conjSubgroup (fsuV T I) g : Set G) := by
  obtain ⟨-, hN⟩ := hmod G T L I hyp.fsu
  have hNM := normalizer_fsuV_le_fsuM h37 h38 h39 hyp.fsu hV hN
  obtain ⟨hw, hr, hm22, hoff⟩ :=
    offender_le_autL_761 h37 h38 h39 hmod h734 h771 hyp h731 hrow hV
  obtain ⟨hcardA, hAL⟩ := hoff g hg
  obtain ⟨htw, hnat⟩ := hrow
  obtain ⟨φ, hφN, hinf, hsup, hniso⟩ := exists_twist hV hN hNM htw
  have hL3 : BinaryNaturalSL (V := IntMod (fsuV T I) hV) (autI hV (fsuL0 T L)) (intSub hV I) ⊥
      3 1 := hnat
  obtain ⟨hcard, -, hm2, hm3, -, -⟩ := SL3One.H4_SL3One hL3 hφN hinf hsup hniso
    (autI_fsuL0_le hV) (autI_top_le_normalizer hV hNM)
  set A := conjSubgroup (fsuV T I) g ⊓ Subgroup.normalizer (fsuV T I : Set G) with hAdef
  have hVg : IsElemAbelian 2 (conjSubgroup (fsuV T I) g) := isElemAbelian_conjSubgroup hV g
  have hAN : A ≤ Subgroup.normalizer (fsuV T I : Set G) := inf_le_right
  have hA2 : IsElemAbelian2 (autI hV A) :=
    isElemAbelian2_autI hV (B2F.isElemAbelian_mono inf_le_left hVg) hAN
  obtain ⟨hquad, x, hxA, y, hyA, hx1, hy1, h32⟩ :=
    SL3One.H4_SL3One_inner hL3 hφN hinf hsup hniso hAL hA2 hcardA
  have hT := hypE322_of_fsu hyp.fsu hV hN
  have h24 := hypE324_of_hyp702 hyp hV hNM
  have hEq : rParam (fsuV T I) =
      ((CFSG.Open.pRank 2 (autI hV ⊤) : ℕ) : ℕ∞) + wParam T (fsuV T I) := by
    rw [hr, hm22, hw]
    norm_num
  obtain ⟨hrkA, -⟩ := e3_31_one_core hV hT h24 hg hEq
  rw [hm22] at hrkA
  have h21 : rk ↥(autI hV A) - 1 = 1 := by rw [hrkA] <;> norm_num
  have hW1 := rkIdx_gammaCheck_le_one hcard hA2 hcardA hxA hyA hx1 hy1 h32
  have hW2 := e3_31_two_ge hV hT h24 hg hEq
  rw [h21, hw] at hW2
  have hW : rkIdx (gammaCheck 1 (autI hV A)) = 1 := by
    have : 1 ≤ rkIdx (gammaCheck 1 (autI hV A)) := by exact_mod_cast hW2
    omega
  obtain ⟨-, hWeq, -, -⟩ := e3_31_two_eq hV hVg hT h24 hg hEq (by rw [h21, hw, hW] <;> simp)
  rw [h21] at hWeq
  have hm1 : mQuot (fsuV T I)
      (fsuV T I ⊓ Subgroup.normalizer (conjSubgroup (fsuV T I) g : Set G)) = 1 := by
    rw [← hWeq, ← rkIdx_eq_mQuot_map hV, hW]
  have hmA : mQuot (conjSubgroup (fsuV T I) g) A = 1 := by
    have h := hg.2
    rw [hw] at h
    exact_mod_cast h.symm
  have hs : mQuot (conjSubgroup (fsuV T I) g) A < sParam hV := by
    have hsP : sParam hV = mParam (autI hV ⊤) := by
      unfold E3.sParam
      rw [hr, min_eq_right (by exact_mod_cast hm3), ENat.toNat_natCast]
    rw [hmA, hsP]
    omega
  have he37 := e3_7 hV (g := g) (B := A) le_rfl hs
  refine ⟨hm1, fun v hv a ha => ?_, ?_, hWeq⟩
  ·
    obtain ⟨u, hu⟩ := IntMod.exists_eq_mk (hV := hV) ⟨v, hv⟩
    have hxaA : convI hV ⟨a, hAN ha⟩ ∈ autI hV A := convI_mem_autI hV ha (hAN ha)
    have hfix : convI hV ⟨a, hAN ha⟩ u * u⁻¹ ∈ fixV (autI hV A) :=
      mem_fixV.mpr fun z hz => hquad _ hxaA z hz u
    have hval : (convI hV ⟨a, hAN ha⟩ u * u⁻¹).val = a * v * a⁻¹ * v⁻¹ := by
      rw [IntMod.val_mul, IntMod.val_inv, convI_apply_val, hu] <;> rfl
    have hC := (mem_fixV_autI hV hAN _).mp hfix
    rw [hval] at hC
    have hmem : a * v * a⁻¹ * v⁻¹ ∈ fsuV T I ⊓ Subgroup.centralizer (A : Set G) := by
      refine ⟨?_, hC⟩
      exact (fsuV T I).mul_mem ((Subgroup.mem_normalizer_iff.mp (hAN ha) v).mp hv)
        ((fsuV T I).inv_mem hv)
    rw [he37] at hmem
    exact hmem.2
  ·
    refine ⟨fun hbot => hg.1 ?_, ?_⟩
    · have h1 : ⁅fsuV T I, conjSubgroup (fsuV T I) g⁻¹⁆ =
          conjSubgroup ⁅conjSubgroup (fsuV T I) g, fsuV T I⁆ g⁻¹ := by
        rw [conjSubgroup_commutator, conjSubgroup_conj_inv]
      have h2 := congrArg (fun X => conjSubgroup X g) (h1.symm.trans hbot)
      simp only [conjSubgroup_inv_conj, conjSubgroup_bot] at h2
      rw [Subgroup.commutator_comm]
      exact h2
    · have h3 : conjSubgroup (fsuV T I) g⁻¹ ⊓ Subgroup.normalizer (fsuV T I : Set G) =
          conjSubgroup (fsuV T I ⊓ Subgroup.normalizer (conjSubgroup (fsuV T I) g : Set G))
            g⁻¹ := by
        rw [conjSubgroup_inf, conjSubgroup_normalizer, conjSubgroup_conj_inv]
      rw [h3, mQuot_conjSubgroup, hm1, hw] <;> simp

theorem isPGroup_sup_conj_761 (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hmod : StmtFSUModule) (h734 : Stmt7_3_4) (h771 : Stmt7_7_1) (hyp : Hyp7_0_2 G T L I)
    (h731 : Hyp7_3_1 T L I) [IsMulCommutative ↥(fsuV T I)] (hrow : Row711SL3Pair T L I 1)
    (hV : IsElemAbelian 2 (fsuV T I)) {g : G} (hg : IsWOffenderAt T (fsuV T I) g) :
    IsPGroup 2 ↥(fsuV T I ⊔ conjSubgroup (fsuV T I) g) := by
  obtain ⟨hw, hr, -, -⟩ := offender_le_autL_761 h37 h38 h39 hmod h734 h771 hyp h731 hrow hV
  obtain ⟨hm1, hq, hinv, -⟩ :=
    offender_quad_761 h37 h38 h39 hmod h734 h771 hyp h731 hrow hV hg
  obtain ⟨-, hq'', -, -⟩ :=
    offender_quad_761 h37 h38 h39 hmod h734 h771 hyp h731 hrow hV hinv
  have hVg := isElemAbelian_conjSubgroup hV g
  have hpV : IsPGroup 2 (fsuV T I) := B2F.isPGroup_of_isElemAbelian hV
  have hpVg : IsPGroup 2 (conjSubgroup (fsuV T I) g) := B2F.isPGroup_of_isElemAbelian hVg
  have hmA : mQuot (conjSubgroup (fsuV T I) g)
      (conjSubgroup (fsuV T I) g ⊓ Subgroup.normalizer (fsuV T I : Set G)) = 1 := by
    have h := hg.2
    rw [hw] at h
    exact_mod_cast h.symm
  refine isPGroup_sup_of_quadratic hV hVg ?_ ?_ hq ?_ ?_ ?_
  · rw [relIndex_eq_two_pow hpV, hm1, pow_one]
  · rw [relIndex_eq_two_pow hpVg, hmA, pow_one]
  ·
    intro v hv a ha
    have hu : g * v * g⁻¹ ∈ fsuV T I := mem_conjSubgroup_iff.mp hv
    have hb1 : g * a * g⁻¹ ∈ conjSubgroup (fsuV T I) g⁻¹ := by
      rw [mem_conjSubgroup_inv_iff]
      simpa [mul_assoc] using ha.1
    have hb2 : g * a * g⁻¹ ∈ Subgroup.normalizer (fsuV T I : Set G) := by
      have h := conjSubgroup_normalizer (conjSubgroup (fsuV T I) g) g⁻¹
      rw [conjSubgroup_conj_inv] at h
      rw [← h, mem_conjSubgroup_inv_iff]
      simpa [mul_assoc] using ha.2
    have h := hq'' _ hu _ ⟨hb1, hb2⟩
    have e : g * a * g⁻¹ * (g * v * g⁻¹) * (g * a * g⁻¹)⁻¹ * (g * v * g⁻¹)⁻¹ =
        g * (a * v * a⁻¹ * v⁻¹) * g⁻¹ := by group
    rw [e, ← conjSubgroup_centralizer, mem_conjSubgroup_inv_iff] at h
    simpa [mul_assoc] using h
  ·
    intro c hc
    by_contra hcN
    have h := rParam_le_mQuot (inf_le_left : fsuV T I ⊓
      Subgroup.normalizer (conjSubgroup (fsuV T I) g : Set G) ≤ fsuV T I) fun hle => hcN (hle hc)
    rw [hr, hm1] at h
    have h' : (3 : ℕ) ≤ 1 := by exact_mod_cast h
    omega
  ·
    intro c hc
    by_contra hcN
    have h := rParam_le_mQuot (inf_le_left : conjSubgroup (fsuV T I) g ⊓
      Subgroup.normalizer (fsuV T I : Set G) ≤ conjSubgroup (fsuV T I) g) fun hle => hcN (hle hc)
    rw [rParam_conj, hr, hmA] at h
    have h' : (3 : ℕ) ≤ 1 := by exact_mod_cast h
    omega

end CFSG.Quasithin.H13
