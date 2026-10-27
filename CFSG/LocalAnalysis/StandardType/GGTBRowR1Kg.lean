module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosHolds
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwenty
import CFSG.LocalAnalysis.StandardType.GGStdPosRankBase
import CFSG.LocalAnalysis.StandardType.GGStdPosRankHolds
import CFSG.LocalAnalysis.StandardType.GGStdPosRankLift
import CFSG.LocalAnalysis.StandardType.GGStdPosLocalConj
import CFSG.LocalAnalysis.StandardType.GGStdPosTableBPos
import CFSG.LocalAnalysis.StandardType.GGTableBRank
import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpRest

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal

private theorem ggR1Kg_prime_rank_ge_four {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (h : GGConfig p B Bs x L D J) :
    p.Prime ∧ p ≠ 2 ∧ 4 ≤ LargeEvenTwoLocalRank p G := by
  obtain ⟨hp, hp2, -, h4⟩ := h.1.2.2.2.2.2.1
  exact ⟨hp, hp2, h4⟩

private theorem ggR1Kg_exists_central_elt {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (h : GGConfig p B Bs x L D J) :
    ∃ y : G, y ∈ B ∧ y ≠ 1 ∧ y ^ p = 1 ∧ L ≤ Subgroup.centralizer ({y} : Set G) ∧
      B ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers y := by
  obtain ⟨hp, -, -⟩ := ggR1Kg_prime_rank_ge_four h
  have hS : LargeEvenSStar p B x L := h.1.2.2.2.2.2.2.1
  exact ⟨x, hS.2.1, hS.2.2.1, hS.1.1.2 x hS.2.1, hS.2.2.2.1.1,
    inf_centralizer_eq_zpowers_of_sstar hp hS⟩

private theorem ggR1Kg_pow_mul_card_le {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (h : GGConfig p B Bs x L D J) :
    p ^ (LargeEvenTwoLocalRank p G - 1) * Nat.card ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) ≤
      Nat.card ↥Bs := by
  obtain ⟨hp, -, h4⟩ := ggR1Kg_prime_rank_ge_four h
  obtain ⟨y, -, hy1, hyp, -, hBC⟩ := ggR1Kg_exists_central_elt h
  have := Fact.mk hp
  have hBBs : B ≤ Bs := h.2.1.1
  have hBcard : Nat.card B = p ^ LargeEvenTwoLocalRank p G := h.1.2.2.2.2.2.2.1.1.2.1
  set C : Subgroup G := Bs ⊓ Subgroup.centralizer (L : Set G) with hC
  have hBC' : B ⊓ C = Subgroup.zpowers y := by
    rw [hC, ← inf_assoc, inf_eq_left.mpr hBBs, hBC]
  have h1 : B.relIndex C * p = Nat.card C := by
    have := Subgroup.relIndex_mul_card B C
    rwa [hBC', Nat.card_zpowers, orderOf_eq_prime hyp hy1] at this
  have h2 : B.relIndex Bs * p ^ LargeEvenTwoLocalRank p G = Nat.card Bs := by
    have := Subgroup.relIndex_mul_card B Bs
    rwa [inf_eq_left.mpr hBBs, hBcard] at this
  have hne : B.relIndex Bs ≠ 0 := fun h0 =>
    (Nat.card_pos (α := Bs)).ne' (by rw [← h2, h0, zero_mul])
  have h3 : B.relIndex C ≤ B.relIndex Bs :=
    Subgroup.relIndex_le_of_le_right inf_le_left hne
  have hpm : p ^ (LargeEvenTwoLocalRank p G - 1) * p = p ^ LargeEvenTwoLocalRank p G := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega)]
  calc p ^ (LargeEvenTwoLocalRank p G - 1) * Nat.card C
      = B.relIndex C * (p ^ (LargeEvenTwoLocalRank p G - 1) * p) := by rw [← h1]; ring
    _ ≤ B.relIndex Bs * p ^ LargeEvenTwoLocalRank p G := by
        rw [hpm]; exact Nat.mul_le_mul_right _ h3
    _ = Nat.card Bs := h2

theorem ggR1_kgPos_of_witness
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hHyp : GGCorFiveTwentyHyp p B Bs x L D J) {t : StatedLieTag} {n f : ℕ}
    {ψ : (ggU t n f).K →* G} (hadm : StatedLieAdmissible t n 2 f)
    (hker : ψ.ker ≤ Subgroup.center (ggU t n f).K) (hrange : ψ.range = L)
    (ht : t = .PSL ∨ t = .POmegaPlus ∨ t = .E6 ∨ t = .E7 ∨ t = .E8) (hpf : p ∣ 2 ^ f - 1) :
    3 ≤ bnRank t n ∧ ∃ ψ' : (ggU t n f).K →* G, ψ'.ker ≤ Subgroup.center (ggU t n f).K ∧
      ψ'.range = L ∧ GGTableBPos p Bs L t n f ψ' := by
  classical
  obtain ⟨hp, hp2, h4⟩ := ggR1Kg_prime_rank_ge_four hHyp.1
  have hInn : GGInnerDiagOn Bs L := hHyp.2.2.1.1
  have hBsG : GGBstar p B Bs := hHyp.1.2.1
  have hcard : p ^ 3 * Nat.card ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) ≤ Nat.card ↥Bs :=
    (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hp.pos (by omega))).trans
      (ggR1Kg_pow_mul_card_le hHyp.1)
  have hrk : 3 ≤ bnRank t n :=
    ggKGPos_three_le_bnRank ggLabelRigidInput_holds hp hadm hker hrange ht hpf hBsG.2.1 hInn hcard
  have hrk2 : 2 ≤ (ggU t n f).D.rank := two_le_lieUniversal_rank t n 2 f Nat.prime_two hadm hrk
  obtain ⟨-, lab, -, hraw⟩ := ggInnerDiagMpInput_holds G t n f ψ hadm hrk2 hker L hrange _ hInn
  obtain ⟨R, _, I, _, -, -, θ, ⟨hBsN, hI⟩, himp⟩ := largeEvenRawDatum_exists hraw
  have hbase : GGKGPosBaseHyp p Bs L t n f ψ :=
    ⟨⟨hp, hp2, hadm, hrk⟩, ⟨hker, hrange, ht, hpf⟩, ⟨hBsG.2.1, hBsN, hBsG.2.2.2⟩,
      fun b hb => himp b (hBsN hb) (hI b hb)⟩
  have hbounds : GGKGPosBoundsHyp p Bs L t n := by
    obtain ⟨y, -, hy1, hyp, hXy, -⟩ := ggR1Kg_exists_central_elt hHyp.1
    have hcardm := ggR1Kg_pow_mul_card_le hHyp.1
    have : Group.IsPerfect (ggU t n f).K := ⟨(ggU_perfect_lieModel hadm hrk2).1⟩
    have hmodel := lieModel_range_centerQuot hadm hrk2 ψ hker
    subst hrange
    have hcomm : commutator ψ.range = ⊤ := by
      have := Group.IsPerfect.range ψ
      exact Group.IsPerfect.commutator_eq_top
    obtain ⟨R', _, r, ⟨θ'⟩, hlift, h1, h2⟩ := ggKGPos_lieLift ht hp hp2 hadm.2.1 hrk hpf hmodel
    exact ggKGPosBoundsHyp_of_rank hp hcardm
      (succ_le_twoLocalRank_of_torusLift hp hXy hyp hy1 hcomm θ' hlift) h1 h2
  have hloc : GGKGPosLocalHyp p Bs L t n f ψ := ggKGPosLocalHyp_iff.mpr ⟨hbase, hbounds⟩
  obtain ⟨k, hstd⟩ := ggKGPos_exists_stdPos hloc
  have hloc' := ggKGPosLocalHyp_comp_conj hloc k
  exact ⟨hloc'.1.2.2.2, ψ.comp (MulAut.conj k).toMonoidHom, hloc'.2.1.1, hloc'.2.1.2.1,
    ggKGPos_tableBPos_of_stdPos G p Bs L t n f _ hloc' hstd⟩

end CFSG.StandardType

end
