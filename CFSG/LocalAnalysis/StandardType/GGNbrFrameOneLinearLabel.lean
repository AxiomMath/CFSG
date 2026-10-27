module

public import CFSG.LocalAnalysis.StandardType.GGNbrFrameOneLinear
public import CFSG.LocalAnalysis.StandardType.GGNbrFrameOneTransfer
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerLinearNonsplit
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeATorus

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem ggTorusFrameEltSC_projectiveSL {d p : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hpK0 : (p : K) ≠ 0) (hpK : p ∣ Nat.card K + 1)
    (hd : 0 < d) : GGTorusFrameEltSC p (projectiveSL d K) := by
  haveI : Nonempty K := ⟨0⟩
  have hpK' : ¬ p ∣ Nat.card K - 1 := by
    intro hK1
    have hdvd : p ∣ 2 := by
      have hsub : Nat.card K + 1 - (Nat.card K - 1) = 2 := by
        have hpos : 1 ≤ Nat.card K := Nat.card_pos
        omega
      rw [← hsub]
      exact Nat.dvd_sub hpK hK1
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdvd)
  refine ggTorusFrameEltSC_of_centralQuotient hp (proj d K) (proj_surjective d K) ?_ ?_
    (ggTorusFrameEltSC_specialLinear hp hp2 hpK0 hpK)
  · intro g hg
    rw [← scalars_eq_center]
    exact proj_eq_one_iff.mp hg
  · intro h
    exact hpK' (h.trans (card_center_specialLinear_dvd hd))

theorem largeEvenLabelAll_frame_linear {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : lab.tag = .A ∧ 5 ≤ lab.rank ∧ p ∣ 2 ^ lab.n + 1) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧
      ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
        GGTorusTBGroup p r R I L' ψ A → GGTorusFrame p A := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨ht, hl, hq⟩ := h
  dsimp only at ht hl hq
  subst ht
  have hn : 1 ≤ n := hlab.1
  intro Q hQ
  obtain ⟨K, _, _, hK, hQ'⟩ := hQ
  haveI : CharP K 2 := NbrInnerMore.charP_two_of_card_pow hn hK
  haveI : Nonempty K := ⟨0⟩
  have hpK0 : (p : K) ≠ 0 := fun hzero =>
    hp2 (((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp
      ((CharP.cast_eq_zero_iff K 2 p).mp hzero)).symm)
  have hpK : p ∣ Nat.card K + 1 := by rwa [hK]
  have hpK' : ¬ p ∣ Nat.card K - 1 := by
    intro hK1
    have hdvd : p ∣ 2 := by
      have hsub : Nat.card K + 1 - (Nat.card K - 1) = 2 := by
        have hpos : 1 ≤ Nat.card K := by rw [hK]; exact Nat.one_le_two_pow
        omega
      rw [← hsub]
      exact Nat.dvd_sub hpK hK1
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdvd)
  let e := TypeA.recipeEquiv (l + 1) K
  have hZ : Subgroup.center (LargeEvenProj (LargeEvenSLGroup (Fin (l + 1)) K)) = ⊥ := by
    have h1 := Subgroup.map_center_eq e
    rw [CFSG.RankThree.RegularUnipotent.center_projectiveSL_eq_bot (n := l + 1) (k := K)
      (by omega)] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _
      (f := (e : LargeEvenProj (LargeEvenSLGroup (Fin (l + 1)) K) →*
        projectiveSL (l + 1) K)) e.injective).mp h1
  refine ⟨K, inferInstance, inferInstance, hK, hQ', 0, ?_, ?_⟩
  · exact TypeA.ggTorusLift_of_mulEquiv e
      (TypeA.ggTorusLift_zero (TypeA.two_dvd_card_projectiveSL (d := l + 1) (by omega)))
  · exact ggTorusFrame_of_frameEltSC (r := 0) hp hp2 hZ
      (fun φ hφ hφp => NbrInnerMore.ggOutdiagPrime_linear hp hpK' (by omega) φ hφ hφp)
      (ggCenterPrime_of_mulEquiv e (ggCenterPrime_projectiveSL hp hpK' (by omega)))
      (ggTorusFrameEltSC_of_mulEquiv e
        (ggTorusFrameEltSC_projectiveSL hp hp2 hpK0 hpK (by omega)))

end CFSG.StandardType

end
