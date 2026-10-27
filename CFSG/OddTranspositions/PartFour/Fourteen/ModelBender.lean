module

public import CFSG.LocalAnalysis.WeakClosure81.SevenKSymplectic
public import CFSG.LocalAnalysis.WeakClosure81.SevenKUnitary
public import CFSG.Quasithin.Background.A3StructureDefs
import CFSG.LocalAnalysis.WeakClosure81.W16LBShape
import CFSG.OddTranspositions.PartThree.Ten.WreathRigidity
import CFSG.RankThree.SteinbergR3ELargeEvenLinearTwoCover
import CFSG.CGT.PushingUp.BenderBridge
public import CFSG.ClassicalGroups.Unitary.Simple
public import CFSG.Models.BenderSuzuki

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.LocalAnalysis.WeakClosure81 CFSG.LocalAnalysis.WeakClosure81.SevenK

variable {X : Type} [Group X]

theorem isSymplecticTransvection_of_mulEquiv_psl2Model [Finite X] {f : ℕ} (hf : 2 ≤ f)
    (e : X ≃* CFSG.Theory.Comparator.PSL2Model f) {s : X} (hs2 : s * s = 1) (hs1 : s ≠ 1) :
    IsSymplecticTransvection X 2 f s := by
  have hZ : Subgroup.center X = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx' : e x ∈ Subgroup.center (CFSG.Theory.Comparator.PSL2Model f) := by
      rw [Subgroup.mem_center_iff] at hx ⊢
      intro y
      obtain ⟨z, rfl⟩ := e.surjective y
      rw [← map_mul, ← map_mul, hx z]
    rw [PartThree.center_psl2Model_eq_bot hf, Subgroup.mem_bot] at hx'
    exact Subgroup.mem_bot.mpr (e.injective (hx'.trans e.map_one.symm))
  refine w16l_isSymplecticTransvection_of_l2 ?_ ?_ hs2 hs1
  · rw [hZ, Subgroup.card_bot]
    exact odd_one
  · refine ⟨GaloisField 2 f, inferInstance, inferInstance,
      GaloisField.card 2 f (by omega), ⟨?_⟩⟩
    exact (QuotientGroup.quotientMulEquivOfEq hZ).trans (QuotientGroup.quotientBot.trans
      (e.trans (CFSG.RankThree.projectiveSpecialLinearTwoEquivSLOfCharTwo _)))

theorem isUnitaryTransvection_of_mulEquiv_psu3Model {f : ℕ} (hf : 2 ≤ f)
    (e : X ≃* ↥(CFSG.Theory.Comparator.PSU3Model f)) {s : X} (hs2 : s * s = 1) (hs1 : s ≠ 1) :
    IsUnitaryTransvection X 3 f s := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h4 : 4 ≤ 2 ^ f := (Nat.pow_le_pow_right (by norm_num) hf : 2 ^ 2 ≤ 2 ^ f)
  have hF2 : 2 * f ≠ 0 := by omega
  have hK : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := by
    rw [GaloisField.card 2 (2 * f) hF2, ← pow_mul, Nat.mul_comm]
  have hnq : (3, 2 ^ f) ≠ (3, 2) := by
    intro h
    simp only [Prod.mk.injEq, true_and] at h
    omega
  obtain ⟨eP⟩ := CFSG.CGT.PushingUp.benderBridge_psu hf e
  let eG : X ≃* CFSG.Open.StatedProj
      (CFSG.Open.StatedSU 3 (2 ^ f) (GaloisField 2 (2 * f))) :=
    eP.trans (CFSG.PGLModel.projSUEquivStatedProj 3 2 f)
  have hsimpG : IsSimpleGroup (CFSG.Open.StatedProj
      (CFSG.Open.StatedSU 3 (2 ^ f) (GaloisField 2 (2 * f)))) :=
    CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU (GaloisField 2 (2 * f)) 2 f
      hK 3 le_rfl hnq
  have hperfSU : Group.IsPerfect (CFSG.Open.StatedSU 3 (2 ^ f) (GaloisField 2 (2 * f))) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU (p := 2) (f := f) hK le_rfl hnq
  have hperfG : Group.IsPerfect (CFSG.Open.StatedProj
      (CFSG.Open.StatedSU 3 (2 ^ f) (GaloisField 2 (2 * f)))) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  have hsimpX : IsSimpleGroup X := eG.isSimpleGroup
  have hperfX : Group.IsPerfect X :=
    Group.IsPerfect.ofSurjective (f := eG.symm.toMonoidHom) eG.symm.surjective
  have hZ : Subgroup.center X = ⊥ := by
    rcases hsimpX.eq_bot_or_eq_top_of_normal (Subgroup.center X) with hc | hc
    · exact hc
    · exfalso
      have hcomm : ∀ a b : X, a * b = b * a := fun a b =>
        (Subgroup.mem_center_iff.1 (hc ▸ Subgroup.mem_top a) b).symm
      have : IsMulCommutative X := ⟨⟨hcomm⟩⟩
      exact Group.IsPerfect.not_isMulCommutative X this
  let eQ : X ⧸ Subgroup.center X ≃* CFSG.Open.StatedProj
      (CFSG.Open.StatedSU 3 (2 ^ f) (GaloisField 2 (2 * f))) :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans ((QuotientGroup.quotientBot (G := X)).trans eG)
  unfold IsUnitaryTransvection
  refine ⟨GaloisField 2 (2 * f), inferInstance, inferInstance, hK, eQ, ?_⟩
  have hx2 : eQ (QuotientGroup.mk s) * eQ (QuotientGroup.mk s) = 1 := by
    rw [← map_mul, ← QuotientGroup.mk_mul, hs2, QuotientGroup.mk_one, map_one]
  have hx1 : eQ (QuotientGroup.mk s) ≠ 1 := by
    intro h
    apply hs1
    have h1 : (QuotientGroup.mk s : X ⧸ Subgroup.center X) = 1 :=
      eQ.injective (h.trans (map_one eQ).symm)
    rw [QuotientGroup.eq_one_iff, hZ, Subgroup.mem_bot] at h1
    exact h1
  exact CFSG.LocalAnalysis.WeakClosure81.TimTI.isUnitaryTransvectionIn_three_of_mul_self
    (n := f) (by omega) hK hx2 hx1

theorem isSz_of_mulEquiv_szModel {f : ℕ} (hf : 1 ≤ f) (e : X ≃* ↥(CFSG.Theory.Comparator.SzModel f)) :
    CFSG.Quasithin.IsSz (2 * f + 1) X := by
  obtain ⟨E⟩ :=
    CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.nonempty_mulEquiv_sz_suzukiGroup f
  have hK : Nat.card (GaloisField 2 (2 * f + 1)) = 2 ^ (2 * f + 1) :=
    GaloisField.card 2 (2 * f + 1) (by omega)
  exact ⟨rfl, f, hf, GaloisField 2 (2 * f + 1), inferInstance, inferInstance, rfl, hK,
    ⟨e.trans ((MulEquiv.subgroupCongr (CFSG.Models.benderSzModel_eq_sz f)).trans E)⟩⟩

end CFSG.OddTranspositions.PartFour
