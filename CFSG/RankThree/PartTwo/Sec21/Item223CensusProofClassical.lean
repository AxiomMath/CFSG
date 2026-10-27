module

public import CFSG.RankThree.PartTwo.Sec21.Item223CensusProofTools
public import CFSG.RankThree.PartTwo.Sec4.Item413AutL2
public import CFSG.RankThree.PartTwo.Sec4.Item413AutL3
public import CFSG.RankThree.PartTwo.Sec4.Item413AutU3

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo

namespace Item223CensusProof

theorem card_le_nine_inner_PSL2 {K : Type} [Field K] [Finite K] (h3 : (3 : K) ≠ 0)
    (F : Subgroup (MulAut (PSL2 K))) (hF : CFSG.Assembly.IsElemAbelian 3 F)
    (hFi : F ≤ (MulAut.conj : PSL2 K →* MulAut (PSL2 K)).range) : Nat.card F ≤ 9 := by
  have hle : F ≤ (pglAction K).range := hFi.trans (KFacts.innAut_le_range_pglAction K)
  set F' := F.comap (pglAction K)
  have hcard : Nat.card F' = Nat.card F := by
    have h := Subgroup.card_map_of_injective (K := F') (KFacts.pglAction_injective (K := K))
    rw [Subgroup.map_comap_eq_self hle] at h
    exact h.symm
  have hFc : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hF.1.1.comm ⟨x, hx⟩ ⟨y, hy⟩)
  rw [← hcard]
  refine Sec4.card_le_nine_of_pgl2 h3 F' (fun x hx y hy => KFacts.pglAction_injective ?_)
    (fun x hx => KFacts.pglAction_injective ?_)
  · rw [map_mul, map_mul]
    exact hFc _ hx _ hy
  · rw [map_pow, map_one]
    exact hF.2 _ hx

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag in
theorem card_le_nine_inner_projectiveSL3 {K : Type} [Field K] [Finite K] (h3 : (3 : K) ≠ 0)
    (F : Subgroup (MulAut (projectiveSL 3 K))) (hF : CFSG.Assembly.IsElemAbelian 3 F)
    (hFi : F ≤ (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range) :
    Nat.card F ≤ 9 := by
  have h := Sec4.card_inf_linearAutGroup_three_le h3 hF
  rwa [inf_eq_left.mpr (hFi.trans (KFacts.innAut_le_linearAutGroup 3 K))] at h

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial KFacts in
theorem card_le_nine_of_le_psuConj_range {p f : ℕ} {K : Type} [Field K] [Finite K]
    {h : UnitaryFieldData p f K} (h3 : (3 : K) ≠ 0) (F : Subgroup (MulAut (unitaryPSU h 3)))
    (hF : CFSG.Assembly.IsElemAbelian 3 F) (hFN : F ≤ (psuConj h).range) : Nat.card F ≤ 9 := by
  set N := (psuConj h).range
  set ψ : unitaryIsom3 h →* GL (Fin 3) K ⧸ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 3) K :=
    (QuotientGroup.mk' _).comp (unitaryIsom3 h).subtype
  have hk : (psuConj h).ker = ψ.ker := by
    ext A
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, Sec4.psuConj_eq_one_iff]
    change _ ↔ QuotientGroup.mk' _ (A : GL (Fin 3) K) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  set χ : N →* GL (Fin 3) K ⧸ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 3) K :=
    (QuotientGroup.kerLift ψ).comp ((QuotientGroup.quotientMulEquivOfEq hk).toMonoidHom.comp
      (QuotientGroup.quotientKerEquivRange (psuConj h)).symm.toMonoidHom)
  have hχ : Function.Injective χ :=
    (QuotientGroup.kerLift_injective ψ).comp ((QuotientGroup.quotientMulEquivOfEq hk).injective.comp
      (QuotientGroup.quotientKerEquivRange (psuConj h)).symm.injective)
  set E := (F.subgroupOf N).map χ
  have hcardE : Nat.card E = Nat.card F := by
    rw [Subgroup.card_map_of_injective hχ]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFN).toEquiv
  have hFc : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hF.1.1.comm ⟨x, hx⟩ ⟨y, hy⟩)
  rw [← hcardE]
  refine Sec4.card_le_nine_of_pgl3 h3 E ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact hFc _ (Subgroup.mem_subgroupOf.mp hx) _ (Subgroup.mem_subgroupOf.mp hy)
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow]
    have : x ^ 3 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact hF.2 _ (Subgroup.mem_subgroupOf.mp hx))
    rw [this, map_one]

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial KFacts in
theorem card_le_nine_inner_unitaryPSU {p f : ℕ} {K : Type} [Field K] [Finite K]
    {h : UnitaryFieldData p f K} (h3 : (3 : K) ≠ 0) (F : Subgroup (MulAut (unitaryPSU h 3)))
    (hF : CFSG.Assembly.IsElemAbelian 3 F)
    (hFi : F ≤ (MulAut.conj : unitaryPSU h 3 →* MulAut (unitaryPSU h 3)).range) :
    Nat.card F ≤ 9 :=
  card_le_nine_of_le_psuConj_range h3 F hF (hFi.trans (stdPinnedPSU3 h).inn_le)

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial in
theorem centerDescend_injective_unitarySU {p f : ℕ} {K : Type} [Field K]
    (hU : UnitaryFieldData p f K) (hq : 2 < p ^ f) :
    Function.Injective (KFacts.centerDescend (unitarySU p f K 3)) := by
  have := hU.finite
  have : Group.IsPerfect (unitarySU p f K 3) := KFacts.isPerfect_unitarySU_three hU hq
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro σ hσ
  rw [MonoidHom.mem_ker] at hσ
  rw [Subgroup.mem_bot]
  refine KFacts.eq_one_of_forall_mul_inv_mem_center fun s => ?_
  have h1 := congrArg (fun φ : MulAut (unitarySU p f K 3 ⧸ Subgroup.center _) =>
    φ (s : unitarySU p f K 3 ⧸ Subgroup.center _)) hσ
  simp only [KFacts.centerDescend_mk, MulAut.one_apply] at h1
  rw [QuotientGroup.eq] at h1
  have := (Subgroup.center _).inv_mem h1
  simpa using this

end Item223CensusProof

open Item223CensusProof

namespace Config223

variable {Y : Type} [Group Y] {E D : Subgroup (MulAut Y)} {Kb : Subgroup Y} {m : ℕ}

theorem false_of_projSL_two (h : Config223 Y E D Kb m) {p e : ℕ} [Fact p.Prime] (hp3 : p ≠ 3)
    (he : 1 ≤ e) (eY : Y ≃* projSL 2 (GaloisField p e)) : False :=
  h.false_of_mulEquiv (eY.trans (Sec4.projSLEquivPSLn 2 _)) (card_le_nine_inner_PSL2
    (Sec4.three_ne_zero_of_card Fact.out hp3 (GaloisField.card p e (by omega))))

theorem false_of_projSL_three (h : Config223 Y E D Kb m) {p e : ℕ} [Fact p.Prime] (hp3 : p ≠ 3)
    (he : 1 ≤ e) (eY : Y ≃* projSL 3 (GaloisField p e)) : False :=
  h.false_of_mulEquiv (eY.trans (Sec4.projSLEquivProjectiveSL 3 _))
    (card_le_nine_inner_projectiveSL3
      (Sec4.three_ne_zero_of_card Fact.out hp3 (GaloisField.card p e (by omega))))

theorem false_of_projSU_three (h : Config223 Y E D Kb m) {p e : ℕ} [Fact p.Prime] (hp3 : p ≠ 3)
    (he : 1 ≤ e) (eY : Y ≃* projSU 3 p e) : False := by
  have hU := Sec4.unitaryFieldData_galoisField p e he
  have := hU.finite
  exact h.false_of_mulEquiv (eY.trans (Sec4.projSUEquivUnitaryPSU p e hU))
    (card_le_nine_inner_unitaryPSU
      (Sec4.three_ne_zero_of_card Fact.out hp3 (GaloisField.card p (2 * e) (by omega))))

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag in
theorem false_of_statedSL_three (h : Config223 Y E D Kb m) {K : Type} [Field K] [Finite K]
    (h3 : (3 : K) ≠ 0) (eY : Y ≃* CFSG.Assembly.LowTwoRank.StatedSL 3 K) : False := by
  set e := eY.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K).symm
  refine h.false_of_hom ((descendAut 3 K).comp (MulAut.congr e).toMonoidHom)
    (Sec4.descendAut_three_injective.comp (MulAut.congr e).injective) (fun y => ?_)
    (card_le_nine_inner_projectiveSL3 h3)
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, KFacts.congr_mulAutConj,
    KFacts.descendAut_conj]
  exact ⟨_, rfl⟩

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial in
theorem false_of_statedSU_three (h : Config223 Y E D Kb m) {p f : ℕ} {K : Type} [Field K]
    (hU : UnitaryFieldData p f K) (h3 : (3 : K) ≠ 0) (hq : 2 < p ^ f)
    (eY : Y ≃* CFSG.Assembly.LowTwoRank.StatedSU 3 (p ^ f) K) : False := by
  have := hU.finite
  have hinj := centerDescend_injective_unitarySU hU hq
  set φ : MulAut Y →* MulAut (unitaryPSU hU 3) :=
    (MulAut.congr (KFacts.suCenterEquiv hU hq)).toMonoidHom.comp
      ((KFacts.centerDescend (unitarySU p f K 3)).comp (MulAut.congr eY).toMonoidHom)
  refine h.false_of_hom φ ((MulAut.congr (KFacts.suCenterEquiv hU hq)).injective.comp
    (hinj.comp (MulAut.congr eY).injective)) (fun y => ?_) (card_le_nine_inner_unitaryPSU h3)
  simp only [φ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [KFacts.congr_mulAutConj, KFacts.centerDescend_conj, KFacts.congr_mulAutConj]
  exact ⟨_, rfl⟩

end Config223

end CFSG.RankThree.PartTwo.Sec21
