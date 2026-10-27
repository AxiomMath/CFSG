module

public import CFSG.RankThree.PartOne.S10.ThetaContract
import CFSG.RankThree.PartOne.S10.ThetaFreeNormalizedLayerEmbedding
import CFSG.RankThree.PartOne.S10.EmbeddingTransport
import CFSG.RankThree.PartOne.S10.AmbientTheta
import CFSG.RankThree.LocalRank.ThetaCoreQuotients

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank

theorem local_theta_component_quotient_normalization_embedding :
    LocalThetaComponentQuotientNormalizationEmbedding := by
  intro hS H _ _ hK p hp x hx Y hY hnorm
  obtain ⟨hNs, -, hNp, -⟩ := solvable_prime_complement_core_characterization (H := H) hp
  have hQ := solvable_prime_complement_core_quotient_centralizers (G := H) hp
    (aschbacherSolvableCore p H) hNs hNp
  have hx' : ∃ k : ℕ, orderOf (QuotientGroup.mk' (aschbacherSolvableCore p H) x) = p ^ k := by
    obtain ⟨k, hk⟩ := hx
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp
      (hk ▸ orderOf_map_dvd (QuotientGroup.mk' (aschbacherSolvableCore p H)) x)
    exact ⟨j, hj⟩
  obtain ⟨J, hJ, hYJ⟩ := theta_free_normalized_layer_local_component_embedding hS
    (H ⧸ aschbacherSolvableCore p H) (EmbeddingTransport.isKGroup_quotient hK _) p hp
    hQ.2.2.1 _ hx' _ (EmbeddingTransport.map_mem_thetaComponentsAt_quotient hp _ hNs hNp hx hY)
    (fun L hL => (hnorm L hL).1) (fun L hL => (hnorm L hL).2)
  obtain ⟨hL, -⟩ := perfectResidual_comap_mem_thetaComponents hp hJ
  exact ⟨_, hL, EmbeddingTransport.le_inSubgroup_perfectResidual_of_isPerfect
    (Subgroup.map_le_iff_le_comap.mp hYJ)
    (isPerfect_of_mem_thetaComponentsAt hY)⟩

end CFSG.RankThree.PartOne
