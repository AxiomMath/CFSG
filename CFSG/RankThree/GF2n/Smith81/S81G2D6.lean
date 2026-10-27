module

public import CFSG.RankThree.GF2n.Smith81.S81D6Res

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.D6Spin

open CFSG.Blueprint CFSG.SeitzReduction CFSG.RankThree.GF2n.Smith81.E7Model
  CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors CFSG.LieType.Steinberg.Minuscule
open CFSG.Open (StatedProj StatedOmega StatedQuadPlus)
open CFSG.LieType.Universal.Spin (quadPlus spinQuotientCenterEquivQuadPlus)


variable (K : Type) [Field K]

@[expose] def lamWEquivEAut0 : ↥(LamW K) ≃* ↥(EAut0 K) :=
  (LamW K).equivMapOfInjective (vAut0 K).toMonoidHom (vAut0 K).injective

variable [Finite K] [CharP K 2]

theorem range_resV0 : (resV0 K).range = LamW K := by
  ext g
  rw [MonoidHom.mem_range]
  exact mem_LamW_iff.symm

@[expose] def lamEquivLamW : ↥(Lam K) ≃* ↥(LamW K) :=
  (MonoidHom.ofInjective (resV0_injective (K := K))).trans
    (MulEquiv.subgroupCongr (range_resV0 K))

@[expose] def perpLeviEquivLam : ↥(EPilot.perpLevi .E7 K) ≃* ↥(Lam K) :=
  ((EPilot.perpLevi .E7 K).equivMapOfInjective (e7Psi K) (e7Equiv (K := K)).symm.injective).trans
    ((((EPilot.perpLevi .E7 K).map (e7Psi K)).equivMapOfInjective _
      (e7Data_valid.minGroup K).subtype_injective).trans
      (MulEquiv.subgroupCongr (Lam_eq_map (K := K)).symm))

@[expose] def statedProjEquivSpinD6 :
    StatedProj (StatedOmega (StatedQuadPlus 6 K)) ≃* spinGroup (quadPlus 6 K) :=
  (spinQuotientCenterEquivQuadPlus (n := 6) (K := K) (by norm_num)).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq (E7Pilot.center_spinGroup_quadPlus_eq_bot K)).trans
      QuotientGroup.quotientBot)

@[expose] def omega12EquivLamW : StatedProj (StatedOmega (StatedQuadPlus 6 K)) ≃* ↥(LamW K) :=
  (statedProjEquivSpinD6 K).trans ((E7Pilot.spinEquivPerpLevi K).trans
    ((perpLeviEquivLam K).trans (lamEquivLamW K)))

theorem exists_equiv_LamW_of_lieModel {G : Type} [Group G] {f : ℕ}
    (h : LieModel G .POmegaPlus 6 2 f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = 2 ^ f ∧
      Nonempty (G ≃* ↥(LamW K)) := by
  obtain ⟨-, L, _, _, hL, ⟨e⟩⟩ := LieModel.statedClassicalModel h (by decide)
  have : CharP L 2 := by
    have := Fintype.ofFinite L
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hL])
  exact ⟨L, inferInstance, inferInstance, this, hL, ⟨e.trans (omega12EquivLamW L)⟩⟩

end CFSG.RankThree.GF2n.Smith81.D6Spin
