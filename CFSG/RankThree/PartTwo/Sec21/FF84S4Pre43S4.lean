module

public import CFSG.RankThree.PartTwo.Sec21.FF84S4Pre43ct
public import CFSG.RankThree.PartTwo.Sec21.FF84S4KF43S4
public import CFSG.RankThree.PartTwo.Sec21.FF84S4SecFour
public import CFSG.RankThree.PartTwo.Sec21.FF84S4Pre43i

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84
open CFSG.Assembly (InCatalog)
open CFSG.RankThree.LocalRank (aschbacherSolvableCore)

variable {G : Type} [Group G] [Finite G] {b b₁ b₂ : G} {L B K : Subgroup G}

theorem commTheta_of_kfactS4 (hKF : S43_KFactS4)
    (hS4 : ∀ D : Subgroup G, D ≠ ⊤ → PartTwo.SectionFourHyp ↥D)
    (hA : A8Model L) (h : FF84Sec4 b L B K b₁ b₂) : CommTheta b b₁ b₂ := by
  obtain ⟨D, hD⟩ : ∃ D : Subgroup G, D = Cen (b * b₁) := ⟨_, rfl⟩
  unfold CommTheta
  rw [← hD]
  have hKD : K ≤ D := hD ▸ K_le_cen_bb₁ h
  have hDne : D ≠ ⊤ := hD ▸ cen_bb₁_ne_top h
  have hKG := S3.B_kgroup h.hyp.iii D hDne
  have hKt := isTypeLnq_subgroupOf hKD h.hK.2.1
  have hmain := hKF ↥D hKG (hS4 D hDne) ⁅K.subgroupOf D, K.subgroupOf D⁆
    (commutator_perfect hKt) (commutator_typeLnq hKt)
  intro t ht
  obtain ⟨t', ht', rfl⟩ := Subgroup.mem_map.1 ht
  have hb₂ : b₂ ∈ ⁅K, K⁆ := b₂_mem_commutator hA h
  have hmapK : (K.subgroupOf D).map D.subtype = K := Subgroup.map_subgroupOf_eq_of_le hKD
  have hcomm : ⁅K.subgroupOf D, K.subgroupOf D⁆.map D.subtype = ⁅K, K⁆ := by
    rw [Subgroup.map_commutator, hmapK]
  rw [← hcomm] at hb₂
  obtain ⟨y, hy, hyb⟩ := Subgroup.mem_map.1 hb₂
  have hmem := hmain (Subgroup.commutator_mem_commutator hy ht')
  refine Subgroup.mem_map.2 ⟨y * t' * y⁻¹ * t'⁻¹, hmem, ?_⟩
  have hy' : D.subtype y = b₂ := hyb
  simp only [map_mul, map_inv, hy']
  first | done | rfl

theorem s43_commThetaAll :
    S43_CommThetaAll := fun _ _ _ _ _ _ _ _ _ h =>
  commTheta_of_kfactS4 s43_kfactS4 (sectionFourHyp_of_ff84Hyp h.hyp) (a8Model_of_hyp h.hyp) h

end CFSG.RankThree.PartTwo.Sec21.FF84.S4
