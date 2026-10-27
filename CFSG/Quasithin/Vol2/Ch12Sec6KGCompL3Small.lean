module

public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompAlt
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115OddL3AutFinal
import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneLinearField
import CFSG.RankThree.SteinbergR3ELinearRegularUnipotent
import CFSG.RankThree.PartTwo.KFacts.AutPSL
import CFSG.RankThree.PartOne.CTP.ExtA
import CFSG.Quasithin.SteinbergBSQTEOddLinearThree
import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115OddL3
public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompOdd
public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompSL3A

public section

namespace CFSG.Quasithin.H13.S126C

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Assembly.LowTwoRank CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

theorem AutConf.exists_sylow_fixed {M : Type} [Group M] {ν : MulAut M}
    {Lb Pb : Subgroup (MulAut M)} (h : AutConf M ν Lb Pb) :
    ∃ P : Sylow 2 M, ∀ t ∈ (P : Subgroup M), ν t = t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS, hSν⟩ := h.sylow
  have hi : ¬ 2 ∣ S.index := by
    have := hS.2.2
    rwa [show (S.subgroupOf ⊤).index = S.index from Subgroup.relIndex_top_right S] at this
  exact ⟨IsPGroup.toSylow hS.2.1 hi, fun t ht => hSν t ht⟩

variable {F : Type} [Field F] [Finite F]

theorem statedClassicalModel_projectiveSL {p : ℕ} (hp : p.Prime) (hFc : Nat.card F = p) :
    StatedClassicalModel (projectiveSL 3 F) .PSL 3 p 1 := by
  refine ⟨⟨hp, le_rfl, by norm_num, by simp, by simp⟩, F, inferInstance, inferInstance,
    by rw [hFc, pow_one], ⟨CFSG.RankThree.PartOne.CTP.projectiveSLEquivStated 3 F⟩⟩

theorem isInner_of_autConf_psl3 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hFc : Nat.card F = p)
    {ν : MulAut (projectiveSL 3 F)} {Lb Pb : Subgroup (MulAut (projectiveSL 3 F))}
    (h : AutConf (projectiveSL 3 F) ν Lb Pb) :
    ∃ l : projectiveSL 3 F, ∀ x, ν x = l⁻¹ * x * l := by
  have hνν : ∀ x, ν (ν x) = x := fun x => by
    have := DFunLike.congr_fun h.sq x
    rwa [pow_two] at this
  exact CFSG.QuasithinUnique.Ch1.oddAutInner_psl3 hp hp2
    (statedClassicalModel_projectiveSL hp hFc) ν hνν h.exists_sylow_fixed

theorem mem_range_conj_of_pow_three_eq_one_psl3 {p : ℕ} (hp : p.Prime) (hFc : Nat.card F = p)
    (hcube : ∀ u : Fˣ, ∃ w : Fˣ, w ^ 3 = u) {α : MulAut (projectiveSL 3 F)} (hα : α ^ 3 = 1) :
    α ∈ (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).range := by
  obtain ⟨-, hform⟩ := automorphism_generation (n := 3) (K := F) (by norm_num)
  obtain ⟨A, σ, ε, hε, rfl⟩ := hform α
  rw [ringAut_eq_one hp hFc σ, map_one, mul_one] at hα ⊢
  interval_cases ε
  · rw [pow_zero, mul_one] at hα ⊢
    obtain ⟨w, hw⟩ := hcube (Matrix.GeneralLinearGroup.det A)
    set B : GL (Fin 3) F := Matrix.GeneralLinearGroup.scalar (Fin 3) w⁻¹ * A with hB
    have hdetB : (B : Matrix (Fin 3) (Fin 3) F).det = 1 := by
      rw [hB, Matrix.GeneralLinearGroup.coe_mul, det_mul, Matrix.GeneralLinearGroup.coe_scalar,
        scalar_apply, det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        ← Matrix.GeneralLinearGroup.val_det_apply, ← hw, Units.val_pow_eq_pow_val,
        ← mul_pow, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_pow]
    refine ⟨proj 3 F ⟨B, hdetB⟩, ?_⟩
    have : Matrix.SpecialLinearGroup.toGL (⟨B, hdetB⟩ : Matrix.SpecialLinearGroup (Fin 3) F) = B :=
      Units.ext rfl
    refine (CFSG.RankThree.PartTwo.KFacts.conj_proj_eq_conjAut 3 F ⟨B, hdetB⟩).trans ?_
    rw [this, hB, map_mul, conjAut_scalar, one_mul]
  · rw [pow_one] at hα
    exfalso
    have hsq := sq_conjAut_fieldAut_dualAut A (1 : F ≃+* F)
    rw [map_one, mul_one, mul_one, map_one, mul_one] at hsq
    apply CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.dualAut_not_mem_semilinearAutGroup
      (n := 3) (K := F) (by norm_num)
    set C := A * Matrix.GeneralLinearGroup.map ((1 : F ≃+* F) : F →+* F)
      (Matrix.GeneralLinearGroup.inverseTranspose A) with hC
    have h3 : conjAut 3 F A * dualAut 3 F * (conjAut 3 F A * dualAut 3 F) ^ 2 = 1 := by
      rw [← pow_succ', hα]
    rw [hsq] at h3
    have hδ : dualAut 3 F = conjAut 3 F (A⁻¹ * C⁻¹) := by
      rw [map_mul, map_inv, map_inv]
      calc dualAut 3 F = (conjAut 3 F A)⁻¹ * (conjAut 3 F A * dualAut 3 F * conjAut 3 F C) *
            (conjAut 3 F C)⁻¹ := by group
        _ = (conjAut 3 F A)⁻¹ * (conjAut 3 F C)⁻¹ := by rw [h3]; group
    rw [hδ]
    exact linearAutGroup_le_semilinearAutGroup (conjAut_mem_linearAutGroup _)

theorem forall_cube_of_card {p : ℕ} (hFc : Nat.card F = p) (hp3 : ¬ 3 ∣ p - 1) :
    ∀ u : Fˣ, ∃ w : Fˣ, w ^ 3 = u := by
  intro u
  have : Fintype F := Fintype.ofFinite F
  have hcard : Nat.card Fˣ = p - 1 := by
    rw [Nat.card_units, hFc]
  have hcop : Nat.Coprime 3 (orderOf u) := by
    have hdvd : orderOf u ∣ p - 1 := hcard ▸ orderOf_dvd_natCard u
    exact (Nat.Coprime.coprime_dvd_right hdvd
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hp3))
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  exact ⟨u ^ m, by rw [← pow_mul, mul_comm, pow_mul, hm]⟩

omit [Finite F] in
theorem scalars_eq_bot {p : ℕ} (hFc : Nat.card F = p) (hp3 : ¬ 3 ∣ p - 1) :
    scalars 3 F = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨c, hc3, hc⟩ := mem_scalars.mp hx
  have hc1 : c = 1 := by
    have hcard : Nat.card Fˣ = p - 1 := by rw [Nat.card_units, hFc]
    have hdvd : orderOf c ∣ p - 1 := hcard ▸ orderOf_dvd_natCard c
    have hcop : Nat.Coprime 3 (p - 1) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hp3
    exact orderOf_eq_one_iff.mp
      (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hc3) hdvd)
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [hc, hc1, Units.val_one, map_one, Matrix.SpecialLinearGroup.coe_one]

omit [Finite F] in
theorem nonempty_sl3_mulEquiv {p : ℕ} (hFc : Nat.card F = p) (hp3 : ¬ 3 ∣ p - 1) :
    Nonempty (SpecialLinearGroup (Fin 3) F ≃* projectiveSL 3 F) :=
  ⟨QuotientGroup.quotientBot.symm.trans
    (QuotientGroup.quotientMulEquivOfEq (scalars_eq_bot hFc hp3).symm)⟩

theorem exists_elemAbelian_nine_psl3 [CharP F 3] :
    ∃ E : Subgroup (projectiveSL 3 F), IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype F := Fintype.ofFinite F
  have h1 : (Pi.single 2 1 : Fin 3 → F) ⬝ᵥ Pi.single 0 1 = 0 := by simp
  have h2 : (Pi.single 2 1 : Fin 3 → F) ⬝ᵥ Pi.single 1 1 = 0 := by simp
  have hv : ∀ i : Fin 3, (Pi.single i 1 : Fin 3 → F) ≠ 0 := fun i h0 => by
    have := congrFun h0 i
    simp at this
  obtain ⟨-, ha⟩ := orderOf_rankOneSL (p := 3) (hv 0) (hv 2) h1
  obtain ⟨-, hb⟩ := orderOf_rankOneSL (p := 3) (hv 1) (hv 2) h2
  have ha3 := pow_orderOf_eq_one (proj 3 F (rankOneSL _ _ h1))
  have hb3 := pow_orderOf_eq_one (proj 3 F (rankOneSL _ _ h2))
  rw [ha] at ha3
  rw [hb] at hb3
  refine exists_elemAbelian_nine (a := proj 3 F (rankOneSL _ _ h1))
    (b := proj 3 F (rankOneSL _ _ h2)) ?_ ha3 hb3 ?_
  · rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_rankOneSL, add_mul, mul_add, one_mul,
      mul_one, vecMulVec_mul_vecMulVec, h1, h2, zero_smul, vecMulVec_zero, add_zero]
    abel
  · intro i j hij
    rw [← map_pow, ← map_pow, ← map_mul, ← MonoidHom.mem_ker, ker_proj, mem_scalars] at hij
    obtain ⟨c, -, hc⟩ := hij
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_rankOneSL_pow, coe_rankOneSL_pow] at hc
    have e02 := congrFun (congrFun hc 0) 2
    have e12 := congrFun (congrFun hc 1) 2
    simp [Matrix.mul_apply, Fin.sum_univ_three, vecMulVec_apply, Matrix.one_apply,
      scalar_apply] at e02 e12
    have hi := (CharP.cast_eq_zero_iff F 3 i).mp e02
    have hj := (CharP.cast_eq_zero_iff F 3 j).mp e12
    have := i.isLt
    have := j.isLt
    exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩

theorem AutConf.involution_of_inner {M : Type} [Group M] {ν : MulAut M}
    {Lb Pb : Subgroup (MulAut M)} (h : AutConf M ν Lb Pb) (hZ : Subgroup.center M = ⊥) {l : M}
    (hl : ∀ x, ν x = l⁻¹ * x * l) :
    orderOf l = 2 ∧ ∀ d, ν d = d ↔ d ∈ Subgroup.centralizer ({l} : Set M) := by
  have hinj := conj_injective_of_center_eq_bot hZ
  have hνl : ν = MulAut.conj l⁻¹ := MulEquiv.ext fun x => by
    rw [hl, MulAut.conj_apply, inv_inv]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨orderOf_eq_prime ?_ fun h1 => h.ne_one (by rw [hνl, h1, inv_one, map_one]),
    fun d => ?_⟩
  · apply hinj
    rw [map_pow, map_one]
    have h1 := h.sq
    rw [hνl, map_inv, inv_pow, inv_eq_one] at h1
    exact h1
  · rw [hl, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h1
      calc d * l = l * (l⁻¹ * d * l) := by group
        _ = l * d := by rw [h1]
    · intro h1
      rw [mul_assoc, h1, inv_mul_cancel_left]

theorem not_autConf_psl3_three (hFc : Nat.card F = 3) {ν : MulAut (projectiveSL 3 F)}
    {Lb Pb : Subgroup (MulAut (projectiveSL 3 F))} (h : AutConf (projectiveSL 3 F) ν Lb Pb)
    (h9 : Nat.card Pb = 9) : False := by
  classical
  have hp : Nat.Prime 3 := Nat.prime_three
  obtain ⟨l, hl⟩ := isInner_of_autConf_psl3 hp (by norm_num) hFc h
  have hZ := CFSG.RankThree.RegularUnipotent.center_projectiveSL_eq_bot (n := 3) (k := F)
    (by norm_num)
  obtain ⟨hl2, hfix⟩ := h.involution_of_inner hZ hl
  have hinj := conj_injective_of_center_eq_bot hZ
  have hcube := forall_cube_of_card hFc (by norm_num)
  have hPin : Pb ≤ (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).range :=
    fun π hπ => mem_range_conj_of_pow_three_eq_one_psl3 hp hFc hcube (h.elem.2 π hπ)
  have hE9 : Nat.card (Pb.comap (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F))) =
      9 := by
    rw [← Subgroup.card_map_of_injective hinj, Subgroup.map_comap_eq, inf_eq_right.mpr hPin, h9]
  have hEC : Pb.comap (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)) ≤
      Subgroup.centralizer ({l} : Set (projectiveSL 3 F)) := fun e he =>
    (hfix e).mp (h.fix_of_mem_innerPart hZ (h.le he))
  have hodd : Odd (Nat.card F) := by rw [hFc]; decide
  obtain ⟨z, hz, hzt, -⟩ :=
    CFSG.Wreathed.OddLinearThreeCentralizerCore.odd_linear_three_involution_centralizer_core F
      hodd (by rw [hFc]) (scalars 3 F) (scalars_eq_center 3 F).le l hl2
  have hC := CFSG.Wreathed.OddLinearThreeCentralizerCore.targetQuotientCentralizer_card F hodd
    (scalars 3 F) (scalars_eq_center 3 F).le z hz l hzt
  have hD : Nat.card (scalars 3 F) = 1 := by
    rw [scalars_eq_bot hFc (by norm_num), Subgroup.card_bot]
  rw [hD, hFc, Nat.div_one] at hC
  have hdvd := Subgroup.card_dvd_of_le hEC
  rw [hE9, hC] at hdvd
  norm_num at hdvd

theorem not_autConf_psl3_five (hFc : Nat.card F = 5) {ν : MulAut (projectiveSL 3 F)}
    {Lb Pb : Subgroup (MulAut (projectiveSL 3 F))} (h : AutConf (projectiveSL 3 F) ν Lb Pb) :
    False := by
  classical
  have hp : Nat.Prime 5 := by norm_num
  obtain ⟨l, hl⟩ := isInner_of_autConf_psl3 hp (by norm_num) hFc h
  have hZ := CFSG.RankThree.RegularUnipotent.center_projectiveSL_eq_bot (n := 3) (k := F)
    (by norm_num)
  obtain ⟨hl2, hfix⟩ := h.involution_of_inner hZ hl
  obtain ⟨c, hcΛ, hc3⟩ := h.exists_innerPart_three hZ fun α hα =>
    mem_range_conj_of_pow_three_eq_one_psl3 hp hFc (forall_cube_of_card hFc (by norm_num)) hα
  have hcC := (hfix c).mp (h.fix_of_mem_innerPart hZ hcΛ)
  have hodd : Odd (Nat.card F) := by rw [hFc]; decide
  have hDs : scalars 3 F ≤ CFSG.LinearGroups.scalarSubgroup 3 F := by
    rw [scalars_eq_center, CFSG.LinearGroups.scalarSubgroup_eq_center]
  obtain ⟨-, hst⟩ := CFSG.Quasithin.SteinbergBS.odd_linear_three_involution_and_Sylow_structure
    hodd (by rw [hFc]) (scalars 3 F) hDs
  obtain ⟨z, ⟨hz, hzl⟩, -, -, -, hJ, -, heJ, -, hJl⟩ := hst l hl2
  set C := Subgroup.centralizer ({l} : Set (projectiveSL 3 F)) with hCdef
  obtain ⟨J, hJ, ⟨eJ⟩, hJl⟩ : ∃ J : Subgroup (projectiveSL 3 F),
      (CFSG.perfectResidual C).map C.subtype = J ∧
        Nonempty (↥J ≃* SpecialLinearGroup (Fin 2) F) ∧ ∀ x ∈ J, x * l = l * x :=
    ⟨_, hJ, heJ, hJl⟩
  have hC := CFSG.Wreathed.OddLinearThreeCentralizerCore.targetQuotientCentralizer_card F hodd
    (scalars 3 F) (scalars_eq_center 3 F).le z hz l hzl
  have hD : Nat.card (scalars 3 F) = 1 := by
    rw [scalars_eq_bot hFc (by norm_num), Subgroup.card_bot]
  rw [hD, hFc, Nat.div_one] at hC
  have hJc : Nat.card J = 120 := by
    rw [Nat.card_congr eJ.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hFc]
    norm_num
  have hRc : Nat.card (CFSG.perfectResidual C) = 120 := by
    rw [← Subgroup.card_map_of_injective C.subtype_injective, hJ, hJc]
  have hidx : (CFSG.perfectResidual C).index = 4 := by
    have := Subgroup.card_mul_index (CFSG.perfectResidual C)
    rw [hRc, hC] at this
    omega
  have hcJ : c ∈ J := by
    have h4 := Subgroup.pow_index_mem (CFSG.perfectResidual C) (⟨c, hcC⟩ : C)
    have hc3' : c ^ 3 = 1 := by
      have := pow_orderOf_eq_one c
      rwa [hc3] at this
    have h3 : (⟨c, hcC⟩ : C) ^ 3 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact hc3')
    rw [hidx, pow_succ, h3, one_mul] at h4
    rw [← hJ]
    exact ⟨_, h4, rfl⟩
  have hJfix : ∀ x ∈ J, ν x = x := fun x hx =>
    (hfix x).mpr (Subgroup.mem_centralizer_singleton_iff.mpr (hJl x hx))
  have hJq : CFSG.IsQuasisimple J :=
    (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr eJ).2
      (CFSG.QuasithinUnique.Ch1.isQuasisimple_sl2 (by rw [hFc]; norm_num))
  have hN : ((innerPart Lb).subgroupOf J).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using h.conj_mem_innerPart (hJfix g g.2) hn⟩
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top
      ⟨Group.isPerfect_def.mp hJq.1, hJq.2.1⟩ ((innerPart Lb).subgroupOf J) with hcen | htop
  · have hc' : (⟨c, hcJ⟩ : J) ∈ Subgroup.center J := hcen hcΛ
    have h1 : eJ ⟨c, hcJ⟩ ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F) := by
      rw [Subgroup.mem_center_iff] at hc' ⊢
      intro g
      rw [← eJ.apply_symm_apply g, ← map_mul, ← map_mul, hc']
    obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp h1
    have h2 : eJ ⟨c, hcJ⟩ ^ 2 = 1 := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_pow, ← hrA, ← map_pow]
      rw [Fintype.card_fin] at hr
      rw [hr, map_one, Matrix.SpecialLinearGroup.coe_one]
    have h3 : (⟨c, hcJ⟩ : J) ^ 2 = 1 := eJ.injective (by rw [map_pow, h2, map_one])
    have h4 : c ^ 2 = 1 := by
      have := congrArg Subtype.val h3
      rwa [Subgroup.coe_pow, Subgroup.coe_one] at this
    have := orderOf_dvd_of_pow_eq_one h4
    rw [hc3] at this
    norm_num at this
  · have : Fact (Nat.Prime 5) := ⟨hp⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := J) 5 (by rw [hJc]; norm_num)
    have hxΛ : (x : projectiveSL 3 F) ∈ innerPart Lb := by
      have : x ∈ (innerPart Lb).subgroupOf J := by rw [htop]; trivial
      exact this
    have hxo : orderOf (x : projectiveSL 3 F) = 5 := by rw [Subgroup.orderOf_coe, hx]
    have h3 := h.pow_three_of_mem_innerPart hZ hxΛ (by rw [hxo]; decide)
    have := orderOf_dvd_of_pow_eq_one h3
    rw [hxo] at this
    norm_num at this

variable {Q : Type} [Group Q] {K L P T : Subgroup Q} {v : Q}

theorem Conf12626.not_psl3_three (hQ : Vol2Native.SQTKHypCat Q) (h : Conf12626 K L P T v)
    (hK : StatedClassicalModel ↥K .PSL 3 3 1) : False := by
  have := hQ.finite
  obtain ⟨-, F, _, _, hFc, ⟨e⟩⟩ := hK
  rw [pow_one] at hFc
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype F := Fintype.ofFinite F
  have : CharP F 3 := charP_of_card_eq_prime_pow (f := 1)
    (by rw [← Nat.card_eq_fintype_card, hFc, pow_one])
  obtain ⟨E, hE, hE9⟩ := exists_elemAbelian_nine_psl3 (F := F)
  have hZ : ∀ z ∈ Subgroup.center (projectiveSL 3 F), z = 1 := fun z hz => by
    rw [CFSG.RankThree.RegularUnipotent.center_projectiveSL_eq_bot (by norm_num)] at hz
    exact hz
  set e' := e.trans (CFSG.RankThree.PartOne.CTP.projectiveSLEquivStated 3 F).symm
  exact not_autConf_psl3_three hFc (h.autConf.map e') (h.card_map_rhoP_eq_nine hQ e' hZ hE hE9)

theorem Conf12626.not_psl3_five (hQ : Vol2Native.SQTKHypCat Q) (h : Conf12626 K L P T v)
    (hK : StatedClassicalModel ↥K .PSL 3 5 1) : False := by
  have := hQ.finite
  obtain ⟨-, F, _, _, hFc, ⟨e⟩⟩ := hK
  rw [pow_one] at hFc
  exact not_autConf_psl3_five hFc
    (h.autConf.map (e.trans (CFSG.RankThree.PartOne.CTP.projectiveSLEquivStated 3 F).symm))

theorem Conf12626.not_sl3_small (hQ : Vol2Native.SQTKHypCat Q) (h : Conf12626 K L P T v)
    {p : ℕ} (hp : p = 3 ∨ p = 5) (hSL : IsSLEps3 true p ↥K) : False := by
  have := hQ.finite
  obtain ⟨F, _, _, hFc, ⟨e⟩⟩ := hSL
  obtain ⟨e₂⟩ := nonempty_sl3_mulEquiv hFc (by rcases hp with rfl | rfl <;> norm_num)
  set e' := (e.trans (specialLinearGroupEquivStatedSL 3 F).symm).trans e₂
  rcases hp with rfl | rfl
  · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have : Fintype F := Fintype.ofFinite F
    have : CharP F 3 := charP_of_card_eq_prime_pow (f := 1)
      (by rw [← Nat.card_eq_fintype_card, hFc, pow_one])
    obtain ⟨E, hE, hE9⟩ := exists_elemAbelian_nine_psl3 (F := F)
    have hZ : ∀ z ∈ Subgroup.center (projectiveSL 3 F), z = 1 := fun z hz => by
      rw [CFSG.RankThree.RegularUnipotent.center_projectiveSL_eq_bot (by norm_num)] at hz
      exact hz
    exact not_autConf_psl3_three hFc (h.autConf.map e')
      (h.card_map_rhoP_eq_nine hQ e' hZ hE hE9)
  · exact not_autConf_psl3_five hFc (h.autConf.map e')

end CFSG.Quasithin.H13.S126C
