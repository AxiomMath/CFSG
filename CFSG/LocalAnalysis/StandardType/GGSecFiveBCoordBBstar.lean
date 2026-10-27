module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBLabelDefs
public import CFSG.LocalAnalysis.StandardType.GGTBTorLiftRowsHolds
import CFSG.LocalAnalysis.StandardType.GGTableBRank
import CFSG.LocalAnalysis.StandardType.GGTableBTwoThreeTorus
import CFSG.LocalAnalysis.StandardType.GGTableBTypeATransport
import CFSG.LocalAnalysis.StandardType.GGFieldCaseTableBIrred
import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1OfPrim
import CFSG.LocalAnalysis.StandardType.GGSecFiveBFourPermExcCoord

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly


private theorem labelAll_torusLift_coordB {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 5 ≤ n)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) (hS : GGSecFiveBCoordBLabel n p lab)
    (hnot : ¬ (5 ≤ n ∧ (lab.tag = .B ∨ lab.tag = .C) ∧ lab.n = 1 ∧ p = 3)) :
    LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift p (n - 1) R := by
  rcases hS with ⟨htag, hr, hq | ⟨hq1, hp3⟩⟩ | ⟨htag, hr, hq⟩ | ⟨htag, hr, hodd, hq1, hp3⟩ |
      ⟨htag, hr, hq1, hp3⟩
  · have h := ggTBTorLiftRows_holds p lab _ _ _ _ _ hp hp2 hlab
      (GGTBTorRowAt.c htag (Dvd.dvd.mul_right hq _))
    rwa [ggTorEnn_eq_zero_of_dvd_sub_one hp hp2 hq, hr, Nat.sub_zero] at h
  · exact absurd ⟨hn, htag, hq1, hp3⟩ hnot
  · have h := ggTBTorLiftRows_holds p lab _ _ _ _ _ hp hp2 hlab
      (GGTBTorRowAt.relD (Or.inr ⟨htag, hq.imp id fun h => ⟨h.2, hr ▸ h.1⟩⟩))
    rwa [hr] at h
  · subst hp3
    have h := ggTBTorLiftRows_holds 3 lab _ _ _ _ _ hp hp2 hlab
      (GGTBTorRowAt.relD (Or.inl ⟨htag, by rw [hq1]; norm_num, by rwa [hr]⟩))
    rwa [hr] at h
  · subst hp3
    obtain ⟨t, l, f⟩ := lab
    dsimp only at htag hr hq1 ⊢
    subst htag hq1
    have hl : (l + 1) / 2 = n - 1 := by omega
    intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, hKf, hKfin, hKn, hQ'⟩ := hQ
    have hK2 : Nat.card K = 2 := by simpa using hKn
    have : CharP K 2 :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
        Nat.prime_two (le_refl 1) (by rw [hK2, pow_one])
    refine ⟨K, hKf, hKfin, hKn, hQ', ?_⟩
    rw [← hl]
    exact TypeA.ggTorusLift_of_mulEquiv (TypeA.recipeEquiv (l + 1) K)
      (TwoThree.ggTorusLift_two hK2 (by omega))

variable {G : Type} [Group G] [Finite G]

theorem ggSecFiveBCoordB_eq_bstar {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {n : ℕ} (hn : 4 ≤ n)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (hM : GGInnerDiagOnLabel (fun p lab => GGSecFiveBCoordBLabel n p lab ∧
      ¬ (5 ≤ n ∧ (lab.tag = .B ∨ lab.tag = .C) ∧ lab.n = 1 ∧ p = 3)) p Bs L) :
    B = Bs := by
  have hcfg : GGConfig p B Bs x L D J := hR.1.1
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hR
  have hBc : Nat.card B = p ^ LargeEvenTwoLocalRank p G := hcfg.1.2.2.2.2.2.2.1.1.2.1
  suffices hm : n ≤ LargeEvenTwoLocalRank p G by
    refine Subgroup.eq_of_le_of_card_ge hcfg.2.1.1 ?_
    rw [hBc, natCard_eq_pow_of_mulEquiv eta]
    exact Nat.pow_le_pow_right hp.pos hm
  rcases (show n = 4 ∨ 5 ≤ n by omega) with rfl | h5
  · exact hcfg.1.2.2.2.2.2.1.2.2.2
  have hS : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
  obtain ⟨-, -, -, hLx, -⟩ := hcfg.tableB_facts
  obtain ⟨hperf, lab, hlab, hraw⟩ := hM
  obtain ⟨R₀, _, I₀, F₀, -, -, θ₀, ⟨hSl, hnot⟩, -⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨R, _, I, F, ⟨-, -, θ, -⟩, hlift⟩ := largeEvenRawDatum_exists
    (labelAll_torusLift_coordB hp hp2 h5 hlab hSl hnot _ hraw)
  have := succ_le_twoLocalRank_of_torusLift hp hLx (hS.1.1.2 x hS.2.1) hS.2.2.1 hperf θ hlift
  omega

theorem ggSecFiveBCoordB_eq_bstar_or {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {n : ℕ} (hn : 4 ≤ n)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (hM : GGInnerDiagOnLabel (fun p lab => GGSecFiveBCoordBLabel n p lab) p Bs L) :
    B = Bs ∨ GGInnerDiagOnLabel (fun p lab => GGSecFiveBCoordBLabel n p lab ∧ 5 ≤ n ∧
      (lab.tag = .B ∨ lab.tag = .C) ∧ lab.n = 1 ∧ p = 3) p Bs L := by
  have h : GGInnerDiagOnLabel (fun p lab => (GGSecFiveBCoordBLabel n p lab ∧
      ¬ (5 ≤ n ∧ (lab.tag = .B ∨ lab.tag = .C) ∧ lab.n = 1 ∧ p = 3)) ∨
      (GGSecFiveBCoordBLabel n p lab ∧ 5 ≤ n ∧ (lab.tag = .B ∨ lab.tag = .C) ∧ lab.n = 1 ∧
        p = 3)) p Bs L :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ ⟨hS, hP⟩ =>
      ⟨(em _).symm.imp (fun h => ⟨hS, h⟩) (fun h => ⟨hS, h⟩), hP⟩) hM
  exact h.elim_or.imp_left (ggSecFiveBCoordB_eq_bstar hR hn eta)

end CFSG.StandardType

end
