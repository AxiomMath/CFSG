module

public import CFSG.RankThree.PartOne.S11c.Sec66ClassCommon
public import CFSG.RankThree.PartOne.S11d.LieCentralizerPSL
public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible StatedClassicalModel StatedProj
  StatedSL StatedSU StatedScalars)
open CFSG.RankThree.PartOne.Sec66T (lieModel_classical_iff)
open CFSG.Assembly.LowTwoRank (projectiveSpecialLinearGroupEquivStatedProj)
open scoped MatrixGroups

theorem center_SL2_eq_bot' {F : Type} [Field F] [CharP F 2] :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro A hA
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  rw [Fintype.card_fin] at hr
  have h2 : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
  have hr1 : r = 1 := by
    have h0 : (r - 1) ^ 2 = 0 := by linear_combination hr - (r - 1) * h2
    exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h0)
  subst hr1
  ext1
  rw [Matrix.SpecialLinearGroup.coe_one, ← hrA, map_one]

theorem nonempty_SL2_mulEquiv_statedProj' {F : Type} [Field F] [CharP F 2] :
    Nonempty (Matrix.SpecialLinearGroup (Fin 2) F ≃* StatedProj (StatedSL 2 F)) :=
  ⟨((QuotientGroup.quotientMulEquivOfEq center_SL2_eq_bot').trans
    QuotientGroup.quotientBot).symm.trans (projectiveSpecialLinearGroupEquivStatedProj 2 F)⟩

theorem lieModel_of_sesqSU {F : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 F K)
    {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    {Hf : W →ₛₗ[h.bar] W →ₗ[K] K} (hHf : Hf.IsSymm) (hHfl : Hf.SeparatingLeft)
    (hm : 2 ≤ Module.finrank K W) (hq : 4 ≤ 2 ^ F) {G : Type} [Group G]
    (e : G ≃* sesqSpecialUnitaryGroup Hf) :
    ∃ (t' : StatedLieTag) (n' : ℕ), LieModel (G ⧸ Subgroup.center G) t' n' 2 F := by
  have hfin := h.finite
  have : CharP K 2 := h.charP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF1 : 1 ≤ F := h.one_le
  rcases Nat.lt_or_ge (Module.finrank K W) 3 with h2 | h3
  · have hV : Module.finrank K W = 2 := by omega
    obtain ⟨φ⟩ := CFSG.RankThree.Classical.nonempty_sesqSpecialUnitaryGroup_mulEquiv_SL2 h hHf
      hHfl hV
    let e2 : G ≃* Matrix.SpecialLinearGroup (Fin 2) h.fixedField := e.trans φ
    have hcard : Nat.card h.fixedField = 2 ^ F := h.card_fixedField
    have : CharP h.fixedField 2 := charP_two_of_card_eq_pow hcard
    have hZ : Subgroup.center G = ⊥ := by
      have h1 := Subgroup.map_center_eq e2
      rw [center_SL2_eq_bot'] at h1
      exact (Subgroup.map_eq_bot_iff_of_injective _ e2.injective).mp h1
    obtain ⟨ψ⟩ := nonempty_SL2_mulEquiv_statedProj' (F := h.fixedField)
    refine ⟨.PSL, 2, (lieModel_classical_iff (by decide)).mpr ⟨⟨Nat.prime_two, hF1, le_rfl,
      fun hc => by have := (Prod.mk.inj hc).2; omega,
      fun hc => by have := (Prod.mk.inj hc).2; omega⟩, h.fixedField, inferInstance, inferInstance,
      hcard, ⟨?_⟩⟩⟩
    exact ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans
      (e2.trans ψ)
  · have hF : Nat.card K = (2 ^ F) ^ 2 := h.card_eq_sq
    have hnq : (Module.finrank K W, 2 ^ F) ≠ (3, 2) := by
      intro hc
      have h1 := congrArg Prod.snd hc
      simp only at h1
      omega
    obtain ⟨b, hb⟩ := h.exists_orthonormal_basis hHf hHfl
    obtain ⟨φ⟩ := CFSG.RankThree.CentralLift.nonempty_sesqSpecialUnitaryGroup_mulEquiv_gramSU h b
      (G := (1 : Matrix (Fin (Module.finrank K W)) (Fin (Module.finrank K W)) K))
      (fun i j => by rw [hb i j, Matrix.one_apply])
    let e3 : G ≃* StatedSU (Module.finrank K W) (2 ^ F) K :=
      (e.trans φ).trans (MulEquiv.subgroupCongr (unitarySU_eq_gramSU h _).symm)
    obtain ⟨-, hZc⟩ := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hF h3 hnq
    refine ⟨.PSU, Module.finrank K W, (lieModel_classical_iff (by decide)).mpr ⟨⟨Nat.prime_two,
      hF1, h3, hnq⟩, K, inferInstance, inferInstance, hF, ⟨?_⟩⟩⟩
    exact (QuotientGroup.congr _ _ e3 (Subgroup.map_center_eq e3)).trans
      (QuotientGroup.quotientMulEquivOfEq hZc)

end CFSG.RankThree.PartOne
