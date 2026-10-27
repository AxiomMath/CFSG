module

public import CFSG.LocalAnalysis.StandardType.GGNbrCenterPCyclicHolds
public import CFSG.LocalAnalysis.StandardType.GGNbrLangKGInputs
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.KGTorsBoundReg
public import CFSG.LocalAnalysis.StandardType.GGOddCenterPrimeLabel
import CFSG.LocalAnalysis.StandardType.GGReverseMarking
import CFSG.LocalAnalysis.StandardType.Marking
import CFSG.RankThree.PerfectCover.HopfCentralCoversSetup

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank

@[expose] def KGCenterCoprimeInput : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (lab : LargeEvenLabel), LargeEvenInLambda2 lab →
    GGNbrLangRegLabel p lab → ∀ (K : Type) [Group K] [Finite K], commutator K = ⊤ →
      GGHasLabel lab (K ⧸ Subgroup.center K) → Nat.Coprime (Nat.card (Subgroup.center K)) p

section Certs

theorem not_dvd_card_center_of_torsBound_eq_one
    {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    {K : Type} [Group K] [Finite K] (hK : commutator K = ⊤)
    (hl : GGHasLabel lab (K ⧸ Subgroup.center K))
    (hbound : CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.torsBound p
      (markTag lab) (markRank lab) (markChar lab) (markDeg lab) = 1) :
    ¬ p ∣ Nat.card (Subgroup.center K) := by
  by_cases hn : Nontrivial (K ⧸ Subgroup.center K)
  · obtain ⟨a, b, hab⟩ := exists_mul_ne_mul_centerQuot_of_perfect hK hn
    obtain ⟨R, _, I, F, ⟨e⟩, hm⟩ := largeEvenRawDatum_exists
      (largeEvenRawDatum_markedModel hlab
        (Q := fun R' _ _ _ => Nonempty (K ⧸ Subgroup.center K ≃* R'))
        (by
          rintro R _ I F ⟨e⟩
          exact nonabelian_of_mulEquiv e ⟨a, b, hab⟩)
        hl)
    have hM : MarkedModel lab (K ⧸ Subgroup.center K) := MarkedModel.of_mulEquiv e.symm hm
    obtain ⟨-, hT⟩ := CFSG.Milestones.cl_lit_griess_schur_multipliers_all_native_models _ _ _ _ _ hM
    have hle := center_torsion_le_native hK (MulEquiv.refl _) hM hT hp
    rw [hbound] at hle
    intro hdvd
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨z, hzo⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center K) p hdvd
    obtain ⟨hzpow, hzne⟩ := orderOf_eq_prime_iff.mp hzo
    have hnt : Nontrivial {z : Subgroup.center K // z ^ p = 1} :=
      ⟨⟨z, hzpow⟩, ⟨1, by simp⟩, fun h => hzne (Subtype.ext_iff.mp h)⟩
    have h2 : 1 < Nat.card {z : Subgroup.center K // z ^ p = 1} :=
      Finite.one_lt_card_iff_nontrivial.mpr hnt
    omega
  · have hZ : Subgroup.center K = ⊤ := by
      rw [Subgroup.eq_top_iff']
      intro g
      have : Subsingleton (K ⧸ Subgroup.center K) := not_nontrivial_iff_subsingleton.mp hn
      exact (QuotientGroup.eq_one_iff g).mp (Subsingleton.elim _ _)
    have : Group.IsPerfect K := ⟨hK⟩
    have : IsMulCommutative K := Subgroup.center_eq_top_iff.mp hZ
    have : Subsingleton K := inferInstance
    have hcard : Nat.card (Subgroup.center K) = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨1⟩⟩
    rw [hcard]
    exact hp.not_dvd_one

theorem kgCenterCoprimeInput_holds : KGCenterCoprimeInput := by
  intro p hp hp2 lab hlab hreg K _ _ hK hl
  exact Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr
    (not_dvd_card_center_of_torsBound_eq_one hp hlab hK hl
      (CFSG.StandardType.KGUniv.torsBound_mark_eq_one_of_regLabel hp hp2 hreg)))

end Certs

end CFSG.StandardType
