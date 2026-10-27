module

public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompPSL2A
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2OuterInvolutionFusion
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2DeterminantSquare
public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompOdd

public section

namespace CFSG.Quasithin.H13.S126C

open CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.RankThree.PartTwo.KFacts

variable {F : Type} [Field F] [Finite F]

theorem psl2_seven_not_commute (hF : Nat.card F = 7) {t c : PSL2 F} (ht : orderOf t = 2)
    (hc : orderOf c = 3) (hcomm : Commute t c) : False := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨U, S, -, hUcard, -, hScard, hpart⟩ :=
    BenderSuzuki.External.huppert_II_8_5_a_psl2_cover (F := F) (p := 7) (f := 1)
      (by rw [hF, pow_one]) (default : Sylow 7 (BenderSuzuki.MatrixGroups.PSL2MatrixGroup F))
  have hz : orderOf (t * c) = 6 := by
    rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [ht, hc]; norm_num), ht, hc]
  have hz1 : t * c ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hz
    omega
  obtain ⟨T, ⟨hzT, hfam⟩, -⟩ := hpart (t * c) hz1
  have hdvd : 6 ∣ Nat.card T := by
    have h0 := orderOf_dvd_natCard (⟨t * c, hzT⟩ : T)
    have ho : orderOf (⟨t * c, hzT⟩ : T) = orderOf (t * c) :=
      (Subgroup.orderOf_coe (⟨t * c, hzT⟩ : T)).symm
    rwa [ho, hz] at h0
  rcases hfam with ⟨g, rfl⟩ | ⟨g, rfl⟩ | ⟨g, rfl⟩
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective] at hdvd
    obtain ⟨n, hn⟩ := (Sylow.isPGroup' (default : Sylow 7
      (BenderSuzuki.MatrixGroups.PSL2MatrixGroup F))).exists_card_eq
    rw [hn] at hdvd
    have h2 : 2 ∣ 7 ^ n := (show 2 ∣ 6 by norm_num).trans hdvd
    have := Nat.prime_two.dvd_of_dvd_pow h2
    omega
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hUcard, hF] at hdvd
    norm_num at hdvd
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hScard, hF] at hdvd
    norm_num at hdvd

omit [Finite F] in
theorem diag_mul_sl2Transv :
    Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal ![-1, 1]) (by simp) *
        Matrix.SpecialLinearGroup.toGL (sl2Transv (1 : F)) =
      Matrix.SpecialLinearGroup.toGL (sl2Transv (-1 : F)) *
        Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal ![-1, 1]) (by simp) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sl2Transv, Matrix.SpecialLinearGroup.transvection_coe, Matrix.mul_apply,
      Matrix.diagonal]

theorem exists_pglAction_inv_unipotent (hF : IsOddPrimePower (Nat.card F)) (h3 : 3 < Nat.card F)
    (hq4 : Nat.card F % 4 = 3) {p : ℕ} [Fact p.Prime] [CharP F p] {g : PGL2 F}
    (hg : BenderSuzuki.PFAppendixIII.IsInvolution g)
    (hgJ : g ∉ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range) :
    ∃ x : PSL2 F, orderOf x = p ∧ pglAction F g x = x⁻¹ := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero fun hc => by
    have := FiniteField.even_card_iff_char_two.mp hc
    rw [← Nat.card_eq_fintype_card] at this
    omega
  have hdet : (Matrix.diagonal ![(-1 : F), 1]).det ≠ 0 := by simp
  set D : GL (Fin 2) F := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet with hD
  set g₀ : PGL2 F := Matrix.ProjGenLinGroup.mk D with hg₀
  have hcomm := pgl2_commutator_eq_psl2_range_of_card_gt_three F hF h3
  have hg₀J : g₀ ∉ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range := by
    rw [hg₀, pgl2_mk_mem_psl2_range_iff_det_isSquare]
    have hd : ((Matrix.GeneralLinearGroup.det D : Fˣ) : F) = -1 := by
      rw [Matrix.GeneralLinearGroup.val_det_apply, hD,
        Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
      simp
    change ¬ IsSquare ((Matrix.GeneralLinearGroup.det D : Fˣ) : F)
    rw [hd, FiniteField.isSquare_neg_one_iff, ← Nat.card_eq_fintype_card, hq4]
    exact fun h => h rfl
  have hDD : D * D = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hD, Matrix.mul_apply, Matrix.diagonal]
  have hg₀I : BenderSuzuki.PFAppendixIII.IsInvolution g₀ := by
    refine ⟨fun h1 => ?_, by rw [pow_two, hg₀, ← map_mul, hDD, map_one]⟩
    rw [hg₀, Matrix.ProjGenLinGroup.mk_eq_one,
      Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar] at h1
    obtain ⟨r, hr⟩ := h1
    have h00 := congrFun (congrFun hr 0) 0
    have h11 := congrFun (congrFun hr 1) 1
    simp [hD, Matrix.diagonal] at h00 h11
    apply h2
    linear_combination h00 - h11
  rw [← hcomm] at hgJ hg₀J
  obtain ⟨h, hh⟩ := isConj_iff.mp (pgl2_outer_involutions_conjugate F hF h3 hg₀I hg hg₀J hgJ)
  set u : PSL2 F := QuotientGroup.mk (sl2Transv (1 : F)) with hu
  have hu1 : pglAction F g₀ u = u⁻¹ := by
    apply Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
    rw [toPGL_pglAction, hu, ← QuotientGroup.mk_inv, sl2Transv_inv,
      Matrix.ProjectiveSpecialLinearGroup.toPGL_mk, Matrix.ProjectiveSpecialLinearGroup.toPGL_mk,
      hg₀, ← map_mul, ← map_inv, ← map_mul, hD, diag_mul_sl2Transv, mul_inv_cancel_right]
  refine ⟨pglAction F h u, ?_, ?_⟩
  · rw [MulEquiv.orderOf_eq, hu]
    exact orderOf_mk_transvection _ one_ne_zero
  · have hgh : g * h = h * g₀ := by rw [← hh]; group
    rw [← MulAut.mul_apply, ← map_mul, hgh, map_mul, MulAut.mul_apply, hu1, map_inv]

omit [Finite F] in
theorem not_autConf_fieldAut_of_ne {p : ℕ} [Fact p.Prime] [CharP F p] (hp2 : p ≠ 2)
    (hp35 : p ≠ 3 ∧ p ≠ 5) {σ : F ≃+* F} (hσ : orderOf σ = 2)
    {Lb Pb : Subgroup (MulAut (PSL2 F))} (h : AutConf (PSL2 F) (psl2FieldAut F σ) Lb Pb) :
    False := by
  have hσ2 : σ ^ 2 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  have hσσ : ∀ y, σ (σ y) = y := fun y => by
    have := DFunLike.congr_fun hσ2 y
    rwa [pow_two] at this
  obtain ⟨y, hy⟩ : ∃ y, σ y ≠ y := by
    by_contra hcon
    push Not at hcon
    have : σ = 1 := RingEquiv.ext hcon
    rw [this, orderOf_one] at hσ
    omega
  set t := y - σ y with ht
  have ht0 : t ≠ 0 := sub_ne_zero.mpr (Ne.symm hy)
  have hσt : σ t = -t := by rw [ht, map_sub, hσσ]; ring
  have hx := orderOf_mk_transvection (F := F) (p := p) (by decide : (0 : Fin 2) ≠ 1) ht0
  have hinv : psl2FieldAut F σ (QuotientGroup.mk (sl2Transv t) : PSL2 F) =
      (QuotientGroup.mk (sl2Transv t))⁻¹ := by
    rw [psl2FieldAut_sl2Transv, hσt, ← sl2Transv_inv, QuotientGroup.mk_inv]
  have hodd : Odd (orderOf (QuotientGroup.mk (sl2Transv t) : PSL2 F)) := by
    rw [sl2Transv, hx]
    exact (Fact.out : p.Prime).odd_of_ne_two hp2
  rcases h.inv _ hodd hinv with h3 | h5
  · have := orderOf_dvd_of_pow_eq_one h3
    rw [sl2Transv, hx] at this
    exact hp35.1 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_three).mp this)
  · have := orderOf_dvd_of_pow_eq_one h5
    rw [sl2Transv, hx] at this
    exact hp35.2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) (by norm_num)).mp this)

theorem exists_conj_mem_zpowers_of_three {G : Type*} [Group G] [Finite G] (h9 : ¬ 9 ∣ Nat.card G)
    {C : Subgroup G} {c c₀ : G} (hc : c ∈ C) (hc₀ : c₀ ∈ C) (hco : orderOf c = 3)
    (hc₀o : orderOf c₀ = 3) : ∃ d ∈ C, d * c * d⁻¹ ∈ Subgroup.zpowers c₀ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set a : C := ⟨c, hc⟩
  set a₀ : C := ⟨c₀, hc₀⟩
  have ha : orderOf a = 3 := by rw [← Subgroup.orderOf_coe]; exact hco
  have ha₀ : orderOf a₀ = 3 := by rw [← Subgroup.orderOf_coe]; exact hc₀o
  have hne : Nat.card C ≠ 0 := Nat.card_pos.ne'
  have h3C : 3 ^ 1 ∣ Nat.card C := by rw [pow_one, ← ha]; exact orderOf_dvd_natCard a
  have h9C : ¬ 3 ^ 2 ∣ Nat.card C := fun h => h9 (h.trans (Subgroup.card_subgroup_dvd_card C))
  have hfact : (Nat.card C).factorization 3 = 1 := by
    have h1 := (Nat.prime_three.pow_dvd_iff_le_factorization hne).mp h3C
    have h2 := mt (Nat.prime_three.pow_dvd_iff_le_factorization hne).mpr h9C
    omega
  let S : Sylow 3 C := Sylow.ofCard (Subgroup.zpowers a)
    (by rw [Nat.card_zpowers, ha, hfact, pow_one])
  let S₀ : Sylow 3 C := Sylow.ofCard (Subgroup.zpowers a₀)
    (by rw [Nat.card_zpowers, ha₀, hfact, pow_one])
  obtain ⟨d, hd⟩ := MulAction.exists_smul_eq C S S₀
  have haS : a ∈ (S : Subgroup C) := by
    rw [Sylow.coe_ofCard]
    exact Subgroup.mem_zpowers a
  have hmem : MulAut.conj d • a ∈ (S₀ : Subgroup C) := by
    rw [← hd, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul a (MulAut.conj d) _ haS
  rw [Sylow.coe_ofCard, MulAut.smul_def, MulAut.conj_apply] at hmem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  refine ⟨d, d.2, Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩⟩
  have := congrArg Subtype.val hk
  simpa [a, a₀] using this

@[expose] noncomputable def sl2Three : Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![0, 1; -1, -1], by simp [Matrix.det_fin_two]⟩

omit [Finite F] in
theorem coe_sl2Three :
    ((sl2Three (F := F) : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![0, 1; -1, -1] :=
  rfl

omit [Finite F] in
theorem coe_sl2Transv (t : F) :
    ((sl2Transv t : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![1, t; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2Transv, Matrix.SpecialLinearGroup.transvection_coe]

omit [Finite F] in
theorem coe_transvection_one_zero (t : F) :
    ((Matrix.SpecialLinearGroup.transvection (by decide : (1 : Fin 2) ≠ 0) t :
      Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![1, 0; t, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.SpecialLinearGroup.transvection_coe]

omit [Finite F] in
theorem sl2Three_pow_three : sl2Three (F := F) ^ 3 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one, coe_sl2Three,
    pow_succ, pow_two, Matrix.mul_fin_two, Matrix.mul_fin_two, Matrix.one_fin_two]
  simp

omit [Finite F] in
theorem orderOf_mk_sl2Three : orderOf (QuotientGroup.mk (sl2Three (F := F)) : PSL2 F) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime ?_ ?_
  · rw [← QuotientGroup.mk_pow, sl2Three_pow_three, QuotientGroup.mk_one]
  · intro h1
    rw [QuotientGroup.eq_one_iff, Matrix.SpecialLinearGroup.mem_center_iff] at h1
    obtain ⟨r, -, hr⟩ := h1
    have h01 := congrFun (congrFun hr 0) 1
    simp [sl2Three] at h01

omit [Finite F] in
theorem sl2Three_mul_mem_center :
    sl2Three (F := F) * (sl2Transv 1 * sl2Three * sl2Transv (-1)) *
        Matrix.SpecialLinearGroup.transvection (by decide : (1 : Fin 2) ≠ 0) 2 ∈
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  refine ⟨-1, by norm_num, ?_⟩
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_sl2Three, coe_sl2Transv,
    coe_transvection_one_zero, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  ring

omit [Finite F] in
theorem psl2FieldAut_sl2Three (σ : F ≃+* F) :
    psl2FieldAut F σ (QuotientGroup.mk (sl2Three (F := F)) : PSL2 F) =
      QuotientGroup.mk sl2Three := by
  show psl2RingEquiv σ (QuotientGroup.mk' _ sl2Three) = QuotientGroup.mk' _ sl2Three
  rw [psl2RingEquiv_mk]
  congr 1
  ext i j
  rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
    coe_sl2Three]
  fin_cases i <;> fin_cases j <;> simp

theorem not_autConf_fieldAut_five (hFc : Nat.card F = 5 ^ 2) {σ : F ≃+* F}
    {Lb Pb : Subgroup (MulAut (PSL2 F))} (h : AutConf (PSL2 F) (psl2FieldAut F σ) Lb Pb) :
    False := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Fintype F := Fintype.ofFinite F
  have : CharP F 5 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hFc])
  have hF : IsOddPrimePower (Nat.card F) := ⟨5, 2, by norm_num, by decide, by norm_num, hFc⟩
  have hZ := psl2_center_eq_bot F
  obtain ⟨c, hc, hc3⟩ := h.exists_innerPart_three hZ fun α hα =>
    mem_range_conj_of_pow_three_eq_one hF (by norm_num) hFc (Or.inr rfl) hα
  set ν := psl2FieldAut F σ with hν
  set C : Subgroup (PSL2 F) := (ν : PSL2 F →* PSL2 F).eqLocus (MonoidHom.id _) with hC
  have hmemC : ∀ x, x ∈ C ↔ ν x = x := fun x => Iff.rfl
  set c₀ : PSL2 F := QuotientGroup.mk sl2Three with hc₀
  set d₁ : PSL2 F := QuotientGroup.mk (sl2Transv 1) with hd₁
  have hc₀C : c₀ ∈ C := (hmemC _).mpr (psl2FieldAut_sl2Three σ)
  have hd₁C : d₁ ∈ C := (hmemC _).mpr (by rw [hd₁, hν, psl2FieldAut_sl2Transv, map_one])
  have hcC : c ∈ C := (hmemC _).mpr (h.fix_of_mem_innerPart hZ hc)
  have h9 : ¬ 9 ∣ Nat.card (PSL2 F) := by
    rw [psl2_card_formula F hF, hFc]
    norm_num
  obtain ⟨d, hdC, hd⟩ := exists_conj_mem_zpowers_of_three h9 hcC hc₀C hc3 orderOf_mk_sl2Three
  have hc' : d * c * d⁻¹ ∈ innerPart Lb := h.conj_mem_innerPart ((hmemC d).mp hdC) hc
  have hc'o : orderOf (d * c * d⁻¹) = 3 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hc3]
  have hc₀in : c₀ ∈ innerPart Lb := by
    have hle : Subgroup.zpowers (d * c * d⁻¹) ≤ Subgroup.zpowers c₀ :=
      (Subgroup.zpowers_le).mpr hd
    have heq : Subgroup.zpowers (d * c * d⁻¹) = Subgroup.zpowers c₀ :=
      Subgroup.eq_of_le_of_card_ge hle (by
        rw [Nat.card_zpowers, Nat.card_zpowers, hc'o, orderOf_mk_sl2Three])
    have : c₀ ∈ Subgroup.zpowers (d * c * d⁻¹) := heq ▸ Subgroup.mem_zpowers c₀
    exact (Subgroup.zpowers_le.mpr hc') this
  set z := c₀ * (d₁ * c₀ * d₁⁻¹) with hz
  have hzin : z ∈ innerPart Lb :=
    (innerPart Lb).mul_mem hc₀in (h.conj_mem_innerPart ((hmemC d₁).mp hd₁C) hc₀in)
  have hzT : z = QuotientGroup.mk
      (Matrix.SpecialLinearGroup.transvection (by decide : (1 : Fin 2) ≠ 0) (-2)) := by
    have key := (QuotientGroup.eq_one_iff _).mpr (sl2Three_mul_mem_center (F := F))
    simp only [QuotientGroup.mk_mul] at key
    rw [hz, hc₀, hd₁, ← QuotientGroup.mk_inv, sl2Transv_inv,
      ← Matrix.SpecialLinearGroup.transvection_inv, QuotientGroup.mk_inv]
    exact eq_inv_of_mul_eq_one_left key
  have h2 : (-2 : F) ≠ 0 := by
    intro h2
    have h5 : (5 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 5
    have : (1 : F) = 0 := by linear_combination (2 : F) * h2 + h5
    exact one_ne_zero this
  have hzo : orderOf z = 5 := by rw [hzT]; exact orderOf_mk_transvection _ h2
  have hz3 := h.pow_three_of_mem_innerPart hZ hzin (by rw [hzo]; decide)
  have := orderOf_dvd_of_pow_eq_one hz3
  rw [hzo] at this
  norm_num at this

end CFSG.Quasithin.H13.S126C
