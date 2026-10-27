module

public import CFSG.RankThree.PartOne.S15K.Defs
public import CFSG.RankThree.PartOne.S12.Sec158
import CFSG.RankThree.PartOne.S12.Sec12A

public section

namespace CFSG.RankThree.PartOne.S15K

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

theorem node158_of_inputs_c (h155 : Node155) (hS : SchreierFor InCatalog)
    (h82 : LocalThetaComponentEmbeddingFrontier) (hA : KF158A) (hL0 : KF158L0c)
    (hComm : KF158Commc) (h157 : KF157c) (hCov : KF158CovAt) (h156 : KF156') : Node158 := by
  classical
  intro G _ _ p A c L E h15 hF hout B hBA hBcyc
  have h := h15.h12
  have hp := h.prime
  have hE : IsElementaryAbelian p ↥E := h.E_elem
  have hEab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have : Fact p.Prime := ⟨hp⟩
  have hJ : ∀ Q : Subgroup G, E ≤ Q → Q ≤ Subgroup.normalizer (E : Set G) → IsPGroup p ↥Q →
      thompsonElem p Q = E := fun Q hEQ hQW hQ =>
    Sec15FA.thompson_eq_of_node155 h155 h15 hF hout hEQ hQW hQ
  have hI : ∀ Y ∈ thetaCompZeroE p E, Y ≤ lieGenerated p E := fun Y hY =>
    h156 G p A c L E h15 hF hout Y hY
  have hc : Sec158.Ctx158 p E :=
    { prime := hp
      elem := hE
      hJ := hJ
      layer_le := fun b => Sec158.zeroLayer_le_lieGenerated h156 h15 hF hout b
      L0 := fun b hbE hb1 z hz Y hY0 hYb =>
        hL0 G p A c L E h15 hF hout b hbE hb1 z hz Y hY0 hYb (hI Y hY0)
      B2 := fun b hbE hb1 => Sec158.E_le_layer_mul_centralizer hbE hEab
        (fun Y hY e he => (h157 G p A c L E h15 hF hout Y hY (hI Y hY)).1 e he)
        (fun Y₁ hY₁0 hY₁b Y₂ hY₂0 hY₂b hne =>
          hComm G p A c L E h15 hF hout b hbE hb1 Y₁ hY₁0 hY₁b (hI Y₁ hY₁0) Y₂ hY₂0 hY₂b
            (hI Y₂ hY₂0) hne) }
  obtain ⟨t, ht, K, J, hKt, hKJ, hmov, hcardD, hJθ, hS2⟩ := hA G p A c L E h15 hF hout
  have hcardM : Nat.card ↥(autMovedInG E t) = p := by
    unfold autMovedInG
    rw [Subgroup.card_map_of_injective E.subtype_injective]
    exact ht.1.2
  have hcycM : IsCyclic ↥(autMovedInG E t) := isCyclic_of_prime_card hcardM
  obtain ⟨a, haz⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top (autMovedInG E t)).1 hcycM
  have haM : a ∈ autMovedInG E t := haz ▸ Subgroup.mem_zpowers a
  have haE : a ∈ E := (Subgroup.map_subtype_le _) haM
  have ha1 : a ≠ 1 := by
    intro h1
    have : Nat.card ↥(Subgroup.zpowers a) = 1 := by rw [h1]; simp
    rw [haz, hcardM] at this
    exact hp.one_lt.ne' this
  have hcov := hCov G p A c L E h15 hF hout t ht K J hKt hKJ hmov hcardD hJθ hS2 a haz
  have hcov' : (E ≤ zeroLayer p E a ⊔ Subgroup.zpowers a) ∨
      (∃ d ∈ E, d ≠ 1 ∧ d ∈ zeroLayer p E a ⊔ Subgroup.zpowers a ∧
        E ≤ zeroLayer p E d ⊔ Subgroup.zpowers d) ∨
      (∃ w ∈ torusNormalizer E, w * a * w⁻¹ ∈ zeroLayer p E a ∧
        zeroLayer p E a ⊔ conjBy w (zeroLayer p E a) = lieGenerated p E) :=
    hcov.imp id (Or.imp (fun h => h.2) (fun h => h.2))
  have hCa := Sec158.root_centralizer_le hc haE ha1 hcov'
  obtain ⟨b, hbBD, hb1⟩ := Sec158.exists_ne_one_mem_inf hp h.A_elem hBA inf_le_left hBcyc hcardD
  have hbB : b ∈ B := hbBD.1
  have hbD : b ∈ A ⊓ Subgroup.centralizer (J : Set G) := hbBD.2
  have hbE : b ∈ E := h.A_le_E (hBA hbB)
  have hJX := Sec158.layer_ge_of_KF158A hS h82 h15 hcardD hJθ hS2 hbD hb1
  have haJ : a ∈ J := hKJ (hmov haM)
  have hCb := Sec158.hyperplane_centralizer_le hc hbE hb1 haJ hJX hCa
  have hCB : Subgroup.centralizer (B : Set G) ≤ lieNormalizer p E :=
    (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hbB)).trans hCb
  exact Sec15FA.normalizer_le_of_centralizer_le hp hE hJ (hBA.trans h.A_le_E)
    (torusNormalizer_le_lieNormalizer hp E) hCB

end CFSG.RankThree.PartOne.S15K
