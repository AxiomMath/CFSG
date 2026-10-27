module

public import CFSG.LocalAnalysis.StandardType.GGTorsionDefs
import CFSG.LocalAnalysis.StandardType.GGInndiagNormalOtherUnitary
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.UnitaryInnerExport
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Export
import CFSG.RankThree.PartOne.KC.UnitaryGoodModel
import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.Adapters.SpecialLinearPerfect
import CFSG.LieType.Universal.Unitary.Clause0
import CFSG.Open.StatedAPI
import CFSG.Assembly.Subnormal

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section TorsionPSUComp

private theorem tpu_fixSubgroup_eq {Q : Type*} [Group Q] (α : MulAut Q) :
    CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup α = ggAutFixedSubgroup α :=
  Subgroup.ext fun _ => Iff.rfl

private theorem tpu_fixed_congr {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (f : MulAut X) :
    ggAutFixedSubgroup (MulAut.congr e f) = (ggAutFixedSubgroup f).map e.toMonoidHom := by
  ext y
  rw [Subgroup.mem_map]
  constructor
  · intro hy
    rw [mem_ggAutFixedSubgroup] at hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    rw [mem_ggAutFixedSubgroup]
    have h := congrArg e.symm hy
    simpa [MulAut.congr_apply] using h
  · rintro ⟨x, hx, rfl⟩
    rw [mem_ggAutFixedSubgroup] at hx ⊢
    simp [MulAut.congr_apply, hx]

private theorem tpu_isComponentOf_map {R P : Type*} [Group R] [Group P] (e : R ≃* P)
    {δ : MulAut R} {α : MulAut P} (hα : α = MulAut.congr e δ) {J : Subgroup R}
    (hJ : IsComponentOf J (ggAutFixedSubgroup δ)) :
    CFSG.Open.IsComponentOf (J.map e.toMonoidHom)
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup α) := by
  subst hα
  rw [tpu_fixSubgroup_eq, tpu_fixed_congr e δ]
  refine CFSG.Assembly.isComponentOf_iff_open.mp ⟨Subgroup.map_mono hJ.1, ?_, ?_⟩
  · exact hJ.2.1.map e.toMonoidHom
  · exact (CFSG.Assembly.IsQuasisimple.congr
      (Subgroup.equivMapOfInjective J e.toMonoidHom e.injective)).mp hJ.2.2

private theorem tpu_centerQuot_map {R P : Type*} [Group R] [Group P] (e : R ≃* P)
    (J : Subgroup R) :
    Nonempty (↥J ⧸ Subgroup.center ↥J ≃*
      ↥(J.map e.toMonoidHom) ⧸ Subgroup.center ↥(J.map e.toMonoidHom)) :=
  ⟨QuotientGroup.congr _ _ (Subgroup.equivMapOfInjective J e.toMonoidHom e.injective)
    (Subgroup.map_center_eq _)⟩

private theorem tpu_psl_model {Q : Type} [Group Q] {E : Type} [Field E] [Fintype E]
    {m f : ℕ} (hf : 1 ≤ f) (hm : 2 ≤ m) (h4 : 4 ≤ Fintype.card E)
    (hE : Fintype.card E = 2 ^ f)
    (g : Matrix.SpecialLinearGroup (Fin m) E →* Q) (hg : Function.Surjective g)
    (hker : g.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin m) E)) :
    CFSG.Open.StatedClassicalModel (Q ⧸ Subgroup.center Q) CFSG.Open.StatedLieTag.PSL m 2 f := by
  have hperf : commutator (Matrix.SpecialLinearGroup (Fin m) E) = ⊤ := by
    rcases lt_or_ge m 3 with hm3 | hm3
    · have hm2 : m = 2 := by omega
      subst hm2
      exact (CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card E
        (by rwa [Nat.card_eq_fintype_card])).commutator_eq_top
    · exact CFSG.ClassicalModels.specialLinear_commutator_eq_top_of_three_le hm3
  obtain ⟨e⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.nonempty_centralQuotient_mulEquiv
      hperf g hg hker
  refine ⟨⟨Nat.prime_two, hf, hm, ?_, ?_⟩, E, inferInstance, inferInstance, ?_, ⟨?_⟩⟩
  · intro hc
    have h2 : 2 ^ f = 2 := (Prod.mk.inj hc).2
    have hpow : 4 ≤ 2 ^ f := by rw [← hE]; exact h4
    omega
  · intro hc
    have h3 : 2 ^ f = 3 := (Prod.mk.inj hc).2
    have hpow : 4 ≤ 2 ^ f := by rw [← hE]; exact h4
    omega
  · rw [Nat.card_eq_fintype_card]; exact hE
  · exact e.symm.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj m E)

private theorem tpu_psu_model {Q : Type} [Group Q] {E : Type} [Field E] [Fintype E]
    {m f : ℕ} (hf : 1 ≤ f) (hm : 3 ≤ m) (hne : (m, 2 ^ f) ≠ (3, 2))
    (hE : Fintype.card E = (2 ^ f) ^ 2)
    (g : ↥(CFSG.Open.StatedSU m (2 ^ f) E) →* Q) (hg : Function.Surjective g)
    (hker : g.ker ≤ Subgroup.center ↥(CFSG.Open.StatedSU m (2 ^ f) E)) :
    CFSG.Open.StatedClassicalModel (Q ⧸ Subgroup.center Q) CFSG.Open.StatedLieTag.PSU m 2 f := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF : Nat.card E = (2 ^ f) ^ 2 := by rw [Nat.card_eq_fintype_card]; exact hE
  obtain ⟨hQ, hZ⟩ :=
    CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (p := 2) (f := f) hF hm hne
  obtain ⟨e⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.nonempty_centralQuotient_mulEquiv
      hQ.1.commutator_eq_top g hg hker
  exact ⟨⟨Nat.prime_two, hf, hm, hne⟩, E, inferInstance, inferInstance, hF,
    ⟨e.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ)⟩⟩

private theorem tpu_pow_scalar {m n p : ℕ} {K : Type} [Field K]
    (hm : 2 ≤ m) (hm2 : m = 2 → 2 ≤ n)
    (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 n K)
    (A : ↥(CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormUnitary h
      (CFSG.RankThree.PartOne.KCUnitaryModel.idGram K (m + 1))))
    {α : MulAut (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormP h
      (CFSG.RankThree.PartOne.KCUnitaryModel.idGram K (m + 1)))}
    (hA : CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom h
      (CFSG.RankThree.PartOne.KCUnitaryModel.idGram K (m + 1)) A = α) (hα : α ^ p = 1) :
    ∃ c : Kˣ, (A : Matrix.GeneralLinearGroup (Fin (m + 1)) K) ^ p =
      Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) c := by
  have hne : ¬(m + 1 = 3 ∧ 2 ^ n = 2) := by
    rintro ⟨hm3, hn2⟩
    have hn : 2 ≤ n := hm2 (by omega)
    have hn1 : n = 1 := by
      have hpow : 2 ^ n = 2 ^ 1 := by rw [hn2]; norm_num
      exact Nat.pow_right_injective (a := 2) (by norm_num) hpow
    omega
  have hm3' : 3 ≤ m + 1 := Nat.succ_le_succ hm
  have h1 : CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom h
      (CFSG.RankThree.PartOne.KCUnitaryModel.idGram K (m + 1)) (A ^ p) = 1 := by
    rw [map_pow, hA, hα]
  obtain ⟨c, -, hc⟩ :=
    (CFSG.RankThree.PartOne.KCUnitaryModel.primeFormConjHom_eq_one_iff_of_ne (h := h)
      hm3' hne (A ^ p)).mp h1
  exact ⟨c, by rw [← Subgroup.coe_pow]; exact hc⟩

theorem ggTorsion_psu_components {m n : ℕ} (hn : 1 ≤ n) (hm : 2 ≤ m) (hm2 : m = 2 → 2 ≤ n)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {δ : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin (m + 1)) K (2 ^ n)))} (hδp : δ ^ p = 1)
    (hδ : δ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin (m + 1)) K (2 ^ n)))
      (LargeEvenGUSet (Fin (m + 1)) K (2 ^ n)))
    {J : Subgroup (LargeEvenProj (LargeEvenSUGroup (Fin (m + 1)) K (2 ^ n)))}
    (hJ : IsComponentOf J (ggAutFixedSubgroup δ)) :
    ∃ (t : CFSG.Open.StatedLieTag) (n' f : ℕ),
      CFSG.Open.StatedClassicalModel (↥J ⧸ Subgroup.center ↥J) t n' 2 f := by
  have hd : 1 ≤ m + 1 := by omega
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 n K :=
    ⟨Nat.prime_two, hn, by rw [hK, ← pow_mul, mul_comm]⟩
  have hD := InndiagSU.congr_mem_primeFormD hU hd hK hδ
  rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormD] at hD
  obtain ⟨A, hA⟩ := hD
  have hα : (MulAut.congr (InndiagSU.projEquiv hU hd) δ) ^ p = 1 := by
    rw [← map_pow, hδp, map_one]
  obtain ⟨c, hc⟩ := tpu_pow_scalar hm hm2 hU A hA hα
  have hT := tpu_isComponentOf_map (InndiagSU.projEquiv hU hd) hA hJ
  obtain ⟨d', hd', hcase⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.exists_field_factor_of_component_primeFormConjHom
      hp hp2 A hc (J.map (InndiagSU.projEquiv hU hd).toMonoidHom) hT
  have hnd : 1 ≤ n * d' := Nat.mul_pos hn hd'
  obtain ⟨eJT⟩ := tpu_centerQuot_map (InndiagSU.projEquiv hU hd) J
  rcases hcase with
    ⟨F, hFf, hFt, -, hcF, h4, g, hg, hker⟩ |
    ⟨E, hEf, hEt, m', -, hcE, hm3, hne, g, hg, hker⟩ |
    ⟨E, hEf, hEt, m', -, hcE, hm2', h4, g, hg, hker⟩
  · letI : Field F := hFf
    letI : Fintype F := hFt
    exact ⟨CFSG.Open.StatedLieTag.PSL, 2, n * d',
      CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv eJT.symm
        (tpu_psl_model (m := 2) (f := n * d') hnd le_rfl h4 hcF g hg hker)⟩
  · letI : Field E := hEf
    letI : Fintype E := hEt
    exact ⟨CFSG.Open.StatedLieTag.PSU, m', n * d',
      CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv eJT.symm
        (tpu_psu_model (f := n * d') hnd hm3 hne hcE g hg hker)⟩
  · letI : Field E := hEf
    letI : Fintype E := hEt
    exact ⟨CFSG.Open.StatedLieTag.PSL, m', 2 * (n * d'),
      CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv eJT.symm
        (tpu_psl_model (m := m') (f := 2 * (n * d')) (by omega) hm2' h4 hcE g hg hker)⟩

end TorsionPSUComp

end CFSG.StandardType
