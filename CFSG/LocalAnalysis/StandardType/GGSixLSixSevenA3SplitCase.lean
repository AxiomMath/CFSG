module

public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenA3TypeDet
public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenAltProof
public import CFSG.LocalAnalysis.StandardType.GGLinearTorusCompBasic
public import CFSG.LocalAnalysis.StandardType.GGSixBstarUniqueToralA

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Inputs

theorem false_of_a3Case_of_dvd {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {m f : ℕ}
    {ψ : (ggU .PSL (m + 1) f).K →* G}
    (hctx : GGSixCtxV2 p B Bs x L D J (ggU .PSL (m + 1) f).D .PSL (m + 1) f ψ)
    (hpf : p ∣ 2 ^ f - 1) (hA : GGSixLSevenA3Case J) : False := by
  have hp : p.Prime := hctx.prime
  have hp2 : p ≠ 2 := hctx.ne_two
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hm : 2 ≤ m := hctx.2.2.2.1.2
  have hf : 1 ≤ f := hctx.2.2.2.1.1.2.1
  obtain ⟨hrange, hker⟩ := hctx.2.2.2.2.1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcardF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hpF : p ∣ Nat.card (GaloisField 2 f) - 1 := by rw [hcardF]; exact hpf
  have hBsE : IsElemAbelian p Bs := hctx.bstar.2.1
  have hcen : ¬ p ∣ Nat.card (Subgroup.centralizer (ψ.range : Set G)) := by
    rw [hrange]
    exact not_dvd_card_centralizer_ggG0_of_stdSub hp hctx.sstar hctx.stdType hctx.stdSub
  have hEC : Bs ⊓ Subgroup.centralizer (ψ.range : Set G) = ⊥ := by
    refine Subgroup.eq_bot_iff_forall _ |>.mpr fun e he => ?_
    obtain ⟨heB, heC⟩ := he
    have hep : e ^ p = 1 := hBsE.2 e heB
    have hord : orderOf e = 1 := by
      rcases hp.eq_one_or_self_of_dvd _ (orderOf_dvd_of_pow_eq_one hep) with h | h
      · exact h
      · exfalso
        apply hcen
        have h4 := orderOf_dvd_natCard
          (⟨e, heC⟩ : Subgroup.centralizer (ψ.range : Set G))
        rwa [Subgroup.orderOf_mk, h] at h4
    exact orderOf_eq_one_iff.mp hord
  have hBsA : ∀ b ∈ Bs, ∃ A, (b, A) ∈ LinFusion.ggInducedPairs ψ := fun b hb =>
    LinFusion.exists_mem_ggInducedPairs hm ψ hker
      (hctx.2.2.2.2.2.2.1.2 b⁻¹ (Bs.inv_mem hb))
  have hBcard : Nat.card B = p ^ LargeEvenTwoLocalRank p G := hctx.sstar.1.2.1
  have hBBs : Nat.card B ≤ Nat.card Bs := Subgroup.card_le_of_le hctx.bstar.1
  have hr4 : 4 ≤ LargeEvenTwoLocalRank p G := hctx.beta.2.2.2
  have hrm : m - 1 ≤ LargeEvenTwoLocalRank p G :=
    RootPlaneA.sub_one_le_twoLocalRank (F := GaloisField 2 f) hp hpF (by omega) hker
  have hdiv : (m + 1) / p ≤ (m + 1) / 3 := Nat.div_le_div_left hp3 (by norm_num)
  have hbig : p ^ ((m + 1) / p + 1) < Nat.card Bs := by
    have h1 : (m + 1) / p + 1 < LargeEvenTwoLocalRank p G := by omega
    calc p ^ ((m + 1) / p + 1) < p ^ LargeEvenTwoLocalRank p G :=
          Nat.pow_lt_pow_right hp.one_lt h1
      _ = Nat.card B := hBcard.symm
      _ ≤ Nat.card Bs := hBBs
  obtain ⟨P, hP⟩ := LinTorus.exists_le_ggFrameTorus hp hp2 hpF hker hBsE hbig hBsA hEC
  have hJ : IsComponentOf J (ψ.range ⊓ Subgroup.centralizer (D : Set G)) := by
    rw [hctx.range_eq]
    exact hctx.j_isComponentOf_inf
  obtain ⟨I, hJI, -⟩ := LinSemisimple.exists_eq_ggFrameBlock_of_le_ggFrameTorus hker P
    (hctx.d_le_bstar.trans hP) hJ
  have hrangeJ : ((ψ.comp (InnerDiagA.conjSL P⁻¹)).comp
      (CFSG.SeitzReduction.LinearPilot.blockEmbed I)).range = J := by
    exact (LinSemisimple.map_blockSpecialLinear_eq_range
      (ψ.comp (InnerDiagA.conjSL P⁻¹)) I).symm.trans hJI.symm
  obtain ⟨-, hF2⟩ := card_eq_four_of_range_eq _ hrangeJ hJ.2.2 hA
  rw [hcardF] at hF2
  have h1 : 2 ^ f - 1 = 1 := by omega
  rw [h1] at hpf
  exact hp.ne_one (Nat.dvd_one.mp hpf)

end Inputs

end CFSG.StandardType
