module

public import CFSG.LocalAnalysis.StandardType.GGQTwoChartDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoChartHubBlk
import CFSG.LocalAnalysis.StandardType.GGQTwoNativeGen

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.ClassicalInvolution.Phan
open CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary
open scoped Pointwise Matrix
variable {G : Type} [Group G] [Finite G]
variable {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} {m n : ℕ}
variable {F0 : Type} [Field F0] [Finite F0] [CharP F0 2]

theorem qTwoChartHub_chart (S : QTwoChartSetting B Bs x L D J 𝒦 m n)
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {ψ : Su F0 2 1 m →* G} (hψ : QTwoOrdModel Bs L ψ) {ε0 : Fin m ↪ Fin (n + 1)}
    (hlifts : ∀ π : Equiv.Perm (Fin (n + 1)), ∃ g : G, QTwoLiftsPerm Bs (QTwoH L 𝒦) S.ρA g π)
    {blk : Finset (Fin (n + 1)) → Subgroup G} (hblk : qTwoChartHub_spec S ψ ε0 blk)
    (e : Su F0 2 1 m ≃* Su K 2 1 m)
    (he : ∀ T : Finset (Fin m),
      (coordBlockSU F0 2 1 T).map e.toMonoidHom = coordBlockSU K 2 1 T)
    (ε : Fin m ↪ Fin (n + 1)) :
    ∃ φ : Su K 2 1 m →* G, φ.ker ≤ Subgroup.center (Su K 2 1 m) ∧
      ∀ T : Finset (Fin m), 2 ≤ T.card → T.card ≤ 4 →
        blk (T.map ε) = (coordBlockSU K 2 1 T).map φ := by
  obtain ⟨π, hπ⟩ := qTwoChartHub_exists_perm_of_embedding ε0 ε
  obtain ⟨g, hg⟩ := hlifts π
  refine ⟨((MulAut.conj g).toMonoidHom.comp ψ).comp e.symm.toMonoidHom, ?_, ?_⟩
  · intro u hu
    rw [MonoidHom.mem_ker] at hu
    rw [Subgroup.mem_center_iff]
    intro v
    have hψu : ψ (e.symm u) = 1 := by
      have hconj : (MulAut.conj g) (ψ (e.symm u)) = 1 := by
        simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] using hu
      exact (MulEquiv.map_eq_one_iff (MulAut.conj g)).mp hconj
    have hcomm : e.symm v * e.symm u = e.symm u * e.symm v :=
      (Subgroup.mem_center_iff.mp (hψ.2.1 (MonoidHom.mem_ker.mpr hψu))) (e.symm v)
    refine e.symm.injective ?_
    rw [map_mul, map_mul, hcomm]
  · intro T h2 h4
    have hframe : qTwoFrameSet ε0 π T = T.map ε := by
      rw [qTwoFrameSet, Finset.map_map,
        show ε0.trans π.toEmbedding = ε from Function.Embedding.ext fun i => hπ i]
    have hsymm : (coordBlockSU K 2 1 T).map e.symm.toMonoidHom =
        coordBlockSU F0 2 1 T := by
      rw [← he T, Subgroup.map_map]
      have hcomp : e.symm.toMonoidHom.comp e.toMonoidHom =
          MonoidHom.id (Su F0 2 1 m) := by
        ext x
        simp
      rw [hcomp, Subgroup.map_id]
    rw [← hframe, hblk hg h2 h4, qTwoBlockOf]
    conv_rhs => rw [← Subgroup.map_map]
    rw [hsymm]

theorem qTwoChartHub_gen (S : QTwoChartSetting B Bs x L D J 𝒦 m n) (hF0 : Nat.card F0 = 4)
    {ψ : Su F0 2 1 m →* G} (hψ : QTwoOrdModel Bs L ψ) {ε0 : Fin m ↪ Fin (n + 1)}
    (hlifts : ∀ π : Equiv.Perm (Fin (n + 1)), ∃ g : G, QTwoLiftsPerm Bs (QTwoH L 𝒦) S.ρA g π)
    {blk : Finset (Fin (n + 1)) → Subgroup G} (hblk : qTwoChartHub_spec S ψ ε0 blk)
    (hgen : QTwoH L 𝒦 =
      ⨆ (π : Equiv.Perm (Fin (n + 1))) (g : G) (_ : QTwoLiftsPerm Bs (QTwoH L 𝒦) S.ρA g π),
        L.map (MulAut.conj g).toMonoidHom) :
    (⨆ (I : Finset (Fin (n + 1))) (_ : I.card = 4), blk I) = QTwoH L 𝒦 := by
  refine le_antisymm ?_ ?_
  · refine iSup₂_le fun I hI => qTwoChartHub_blk_le S hψ hlifts hblk ?_ ?_
    · omega
    · omega
  · rw [hgen]
    refine iSup_le fun π => ?_
    refine iSup_le fun g => ?_
    refine iSup_le fun hg => ?_
    have hmap : L.map (MulAut.conj g).toMonoidHom
        = ⨆ (Q : Finset (Fin m)) (_ : Q.card = 4), qTwoBlockOf ψ g Q := by
      rw [← hψ.1, MonoidHom.range_eq_map,
        ← fourBlockSup_eq_top (N := m) hF0 (by have := S.hm; omega), fourBlockSup,
        Subgroup.map_map]
      simp only [Subgroup.map_iSup, qTwoBlockOf]
    rw [hmap]
    refine iSup₂_le fun Q hQ => ?_
    have h2 : 2 ≤ Q.card := by omega
    have h4 : Q.card ≤ 4 := by omega
    have hcard : (qTwoFrameSet ε0 π Q).card = 4 := by
      rw [qTwoChartHub_card_frameSet, hQ]
    calc qTwoBlockOf ψ g Q = blk (qTwoFrameSet ε0 π Q) := (hblk hg h2 h4).symm
      _ ≤ ⨆ (I : Finset (Fin (n + 1))) (_ : I.card = 4), blk I :=
          le_iSup₂_of_le (qTwoFrameSet ε0 π Q) hcard le_rfl

end CFSG.StandardType.QTwo

end
