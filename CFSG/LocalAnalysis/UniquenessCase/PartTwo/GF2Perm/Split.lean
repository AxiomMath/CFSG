module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.GF2Perm.BorelQuotient
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GOrbConn
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.CoverOneNodes
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.CoverOneParab
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanBlockCycNodes

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.GF2Perm

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.Steinberg
  CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar
  CFSG.AGLEmbeddingD2.Tits.GN516.Nodes CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank

variable {K G : Type} [Group K] [Finite K] [Group G] [Finite G] {D : UniversalRootDatum K}
  {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {π : K →* G} {M : ℕ}

omit [Finite G] in
theorem diagram_connected_of_card_six (h : BorelQuotient D n H π M) [IsSimpleGroup G]
    {j : Fin D.rank} (h6 : Nat.card (rankOne D.rootGroup j) = 6 ∧
      ∃ a ∈ rankOne D.rootGroup j, ∃ b ∈ rankOne D.rootGroup j, a * b ≠ b * a) :
    (TauCeti.diagramGraph D.cartan).Connected := by
  obtain ⟨a, ha, b, hb, hab⟩ := h6.2
  refine CFSG.AGLEmbeddingD2.Tits.GN516.Conn.diagram_connected h ⟨π a, π b, fun hcomm => hab ?_⟩
  have hz : a * b * a⁻¹ * b⁻¹ ∈ π.ker := by
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    rw [hcomm]
    group
  have hzL : a * b * a⁻¹ * b⁻¹ ∈ rankOne D.rootGroup j :=
    (rankOne D.rootGroup j).mul_mem
      ((rankOne D.rootGroup j).mul_mem
        ((rankOne D.rootGroup j).mul_mem ha hb) ((rankOne D.rootGroup j).inv_mem ha))
      ((rankOne D.rootGroup j).inv_mem hb)
  have hz1 := CFSG.AGLEmbeddingD2.McLaughlin.Lie.eq_one_of_central_of_card_six h6.1 h6.2 hzL
    (fun l _ => (Subgroup.mem_center_iff.1 (h.ker_central _ hz) l).symm)
  calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
    _ = b * a := by rw [hz1, one_mul]

theorem permWitness_of_borelQuotient_split (h : BorelQuotient D n H π M) (hM : M ∣ 3)
    (hconn : (TauCeti.diagramGraph D.cartan).Connected) (hr : 3 ≤ D.rank)
    (h6 : ∀ j, Nat.card (rankOne D.rootGroup j) = 6 ∧
      ∃ a ∈ rankOne D.rootGroup j, ∃ b ∈ rankOne D.rootGroup j, a * b ≠ b * a)
    (h3 : ∀ j, HasOrderThree D j) (h3nc : ∀ j, CFSG.AGLEmbedding.BlockCyc.HasOrderThreeNC D j) :
    PermWitness G := by
  have : Nontrivial (Fin D.rank) :=
    ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp [Fin.ext_iff]⟩
  have hT := D.isFiniteType.isTree_diagramGraph hconn
  obtain ⟨i, j, hij, hi1, hj1⟩ := hT.exists_ne_and_degree_eq_one
  have hmem : ∀ k, (TauCeti.diagramGraph D.cartan).degree k = 1 → k ∈ endNodesThree D H :=
    fun k hk => ⟨hk, by
      have hpar : parJ D H {k} = borel D H ⊔ rankOne D.rootGroup k := by simp [parJ]
      rw [hpar, card_borel_sup_rankOne_of_torus h k (h6 k).1 (h6 k).2]⟩
  have hiJ := hmem i hi1
  have hjJ := hmem j hj1
  have horth : ∀ j ∈ endNodesThree D H, ∀ k ∈ endNodesThree D H, j ≠ k → D.cartan j k = 0 :=
    fun j hj k hk hjk => cartan_eq_zero_of_degree_eq_one hconn hr hj.1 hk.1 hjk
  obtain ⟨E, hE, hEel, hE9⟩ :=
    exists_E9_of_nodes h (horth i hiJ j hjJ hij) hij (h3 i) (h3nc j)
  refine permWitness_of_borelQuotient (J := endNodesThree D H) h hM
    (nodePerm_image_endNodesThree h) (fun k _ => h6 k) horth ?_ hEel hE9
  exact hE.trans (sup_le (Subgroup.map_mono (rankOne_le_parJ hiJ))
    (Subgroup.map_mono (rankOne_le_parJ hjJ)))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.GF2Perm
