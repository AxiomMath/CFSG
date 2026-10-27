module

public import CFSG.RankThree.PartTwo.Sec13.Item13ResProofA7Z3
public import CFSG.RankThree.PartTwo.Sec13.Steps
import CFSG.RankThree.PartTwo.Sec13.Item136E
import CFSG.RankThree.PartTwo.Sec13.Item131Facts
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

@[expose] def Item135A7Z3HypTK : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec13Data G A c L → HypT A → c ∈ L → ¬ IsQuasisimple (L ⧸ CFSG.pCore 2 L) →
    CFSG.pCore 2 L = ⊥ → CFSG.Open.pRank 2 (⊤ : Subgroup L) ≤ 2 →
    IsQuasisimple (L ⧸ CFSG.oddCore L) →
    Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 7)) →
    Sec4.IsHeisCentral (lBarA c L A) (L ⧸ aschbacherSolvableCore 3 L) →
    ∀ K ∈ thetaComponentsAt 3 c, A ≤ L ⊔ K →
      Sec4.IsTripleCover (K ⧸ aschbacherSolvableCore 3 K) (alternatingGroup (Fin 6)) → False

theorem item135A7Z3HypT_of_K
    (h131 : Item131) (hK : Item135A7Z3HypTK) :
    Item135A7Z3HypT := by
  intro G _ _ A c L hD hT hcL hnq hO2 hm hO hA7
  obtain ⟨⟨hM22p, hM22z⟩, ⟨hM12p, hM12z⟩, ⟨hJ2p, hJ2z⟩⟩ := sporadicModels131
  rcases h131 G A c L hD with ⟨hL3, -⟩ | ⟨hPGL, -, -⟩ | ⟨⟨φ⟩, -⟩ | ⟨⟨φ⟩, -⟩ |
      ⟨⟨φ⟩, -⟩ | ⟨⟨φ⟩, -⟩ | ⟨h7, -, hE⟩
  ·
    exfalso
    obtain ⟨p, e, hp, he, hcase⟩ := hL3
    rcases hcase with ⟨hq, ⟨φ⟩⟩ | ⟨hq, ⟨φ⟩⟩
    · obtain ⟨hS, hZ⟩ := isPerfect_center_projSL p e he hq
      exact (facts_of_prod hD hS hZ φ).1 hcL
    · by_cases hq2 : 2 < p ^ e
      · obtain ⟨hS, hZ⟩ := isPerfect_center_projSU p e he hq hq2
        exact (facts_of_prod hD hS hZ φ).1 hcL
      · have h2 : p ^ e = 2 := by
          have : 2 ≤ p ^ e := le_trans hp.out.two_le (Nat.le_self_pow (by omega) _)
          omega
        obtain ⟨rfl, rfl⟩ := eq_two_one_of_pow_eq_two hp.out h2
        exact false_of_isSolvable hD isSolvable_projSU_two φ
  ·
    exfalso
    obtain ⟨π, p, f, K, _, hK', hq, ⟨φ⟩⟩ := hPGL
    by_cases hq2 : 2 < p ^ f
    · exact not_mem_of_center_inf_commutator hD φ
        (by rw [center_projImage_glPi hK' hq hq2, bot_inf_eq]) hcL
    · have h2 : p ^ f = 2 := by
        have hf : f ≠ 0 := by have := hK'.one_le; omega
        have : 2 ≤ p ^ f := le_trans hK'.prime.two_le (Nat.le_self_pow hf _)
        omega
      cases π
      · exact false_of_isSolvable hD (isSolvable_projImage_glPi_two hK' h2) φ
      · change p ^ f % 3 = 1 at hq
        omega
  ·
    exact absurd hcL (facts_of_prod hD isPerfect_center_alt7.1 isPerfect_center_alt7.2 φ).1
  · exact absurd hcL (facts_of_prod hD hM22p hM22z φ).1
  · exact absurd hcL (facts_of_prod hD hM12p hM12z φ).1
  · exact absurd hcL (facts_of_prod hD hJ2p hJ2z φ).1
  ·
    have hZ3 : Nat.card (Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) = 3 := hA7.1
    obtain ⟨U, hzU, hU9, hU3, hUΛ, hUΛz, hAbU⟩ :
        ∃ U : Subgroup (lBarA c L A), mkC (L := L) hD.mem_A ∈ U ∧ 9 ≤ Nat.card U ∧
          (∀ x ∈ U, x ^ 3 = 1) ∧
          (∀ u ∈ U, ∀ l ∈ (Sec12.lBar c L).subgroupOf (lBarA c L A), u * l = l * u) ∧
          (∀ u ∈ U, u ∈ (Sec12.lBar c L).subgroupOf (lBarA c L A) →
            u ∈ Subgroup.zpowers (mkC (L := L) hD.mem_A)) ∧
          (∀ a ∈ (aBarHom hD).range, ∀ u ∈ U,
            a * u * a⁻¹ * u⁻¹ ∈ Subgroup.zpowers (mkC (L := L) hD.mem_A)) := by
      rcases h7 with hSL | ⟨hHeis, -⟩
      · exact exists_U_of_isSLThreePiTwo hD hcL hSL
      · exact exists_U_of_isHeisCentral hD hcL hHeis hZ3
    obtain ⟨E, hEle, hEe, hE27, hEC, hEL, -⟩ :=
      exists_E_of_U hD hcL hzU hU9 hU3 hUΛ hUΛz hAbU
    have hET : E ∉ partTwoT G := by
      intro hET
      have hEc : E ≤ Subgroup.centralizer ({c} : Set G) :=
        hEle.trans (inf_le_left.trans (sup_le hD.le_centralizer hD.A_le_centralizer))
      have hemp := hT.2.2 c hD.zpowers_mem_omegaA
      have hmem : E ∈ collectionIn (partTwoT G) (Subgroup.centralizer ({c} : Set G)) :=
        ⟨hET, hEc⟩
      rw [hemp] at hmem
      exact hmem
    obtain ⟨-, hrest⟩ := hE E hEle hEe hE27 hEC hEL
    obtain ⟨hHeis, ⟨K, hKc, hAK, hK6⟩, -⟩ := hrest hET
    exact hK G A c L hD hT hcL hnq hO2 hm hO hA7 hHeis K hKc hAK hK6

end CFSG.RankThree.PartTwo.Sec13
