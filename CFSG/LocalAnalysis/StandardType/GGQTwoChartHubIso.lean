module

public import CFSG.LocalAnalysis.StandardType.GGQTwoChartDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoChartHubBlk
import CFSG.LocalAnalysis.StandardType.GGQTwoChartTwoThreeBlk
import CFSG.LocalAnalysis.StandardType.GGQTwoChartField

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.ClassicalInvolution.Phan
open CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary
open scoped Pointwise Matrix
variable {G : Type} [Group G] [Finite G]
variable {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} {m n : ℕ}
variable {F0 : Type} [Field F0] [Finite F0] [CharP F0 2]

theorem qTwoChartHub_inj_block (S : QTwoChartSetting B Bs x L D J 𝒦 m n)
    {ψ : Su F0 2 1 m →* G} (hψ : QTwoOrdModel Bs L ψ) {ε0 : Fin m ↪ Fin (n + 1)}
    (hε0 : QTwoFrameMatch S ψ ε0) {T : Finset (Fin m)} (hT : T.card ≤ 4)
    {u : Su F0 2 1 m} (hu : u ∈ coordBlockSU F0 2 1 T) (h : ψ u = 1) : u = 1 := by
  have hm : 5 ≤ m := S.hm
  have hψ' := hψ
  unfold QTwoOrdModel at hψ'
  have hz : u ∈ Subgroup.center (Su F0 2 1 m) := hψ'.2.1 (MonoidHom.mem_ker.mpr h)
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := T) (t := Finset.univ) (by rw [Finset.card_univ, Fintype.card_fin]; omega)
  have hvec : ((u : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *ᵥ Pi.single i 1 =
      Pi.single i 1 := by
    ext j
    rw [Matrix.mulVec_single_one, Matrix.col_apply,
      (mem_coordBlockSU_iff.mp hu) j i (Or.inr hi)]
    by_cases hji : j = i
    · rw [hji, if_pos rfl, Pi.single_eq_same]
    · rw [if_neg hji, Pi.single_eq_of_ne hji]
  have hε0' := hε0
  unfold QTwoFrameMatch at hε0'
  exact qTwoChartTwoThree_central_eq_one (fun σ => (hε0' σ).imp fun v hv => hv.1) hz hvec

theorem qTwoChartHub_blk_iso (S : QTwoChartSetting B Bs x L D J 𝒦 m n)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hF0 : Nat.card F0 = 4) (hK : Nat.card K = 4)
    {ψ : Su F0 2 1 m →* G} (hψ : QTwoOrdModel Bs L ψ) {ε0 : Fin m ↪ Fin (n + 1)}
    (hε0 : QTwoFrameMatch S ψ ε0)
    (hlifts : ∀ π : Equiv.Perm (Fin (n + 1)), ∃ g : G, QTwoLiftsPerm Bs (QTwoH L 𝒦) S.ρA g π)
    {blk : Finset (Fin (n + 1)) → Subgroup G} (hblk : qTwoChartHub_spec S ψ ε0 blk)
    {I : Finset (Fin (n + 1))} (h2 : 2 ≤ I.card) (h4 : I.card ≤ 4) :
    Nonempty (Su K 2 1 I.card ≃* ↥(blk I)) := by
  have hm : 5 ≤ m := S.hm
  have h4m : 4 ≤ m := by omega
  have hIle : I.card ≤ m := le_trans h4 h4m
  obtain ⟨π, T, hIT, hcard⟩ := qTwoChartHub_exists_frameSet ε0 hIle
  obtain ⟨g, hg⟩ := hlifts π
  have h2T : 2 ≤ T.card := by rw [hcard]; exact h2
  have h4T : T.card ≤ 4 := by rw [hcard]; exact h4
  have hblkI : blk I = qTwoBlockOf ψ g T := by
    rw [← hIT]
    exact hblk hg h2T h4T
  have hinj : Function.Injective
      (((MulAut.conj g).toMonoidHom.comp ψ).domRestrict (coordBlockSU F0 2 1 T)) := by
    intro u v huv
    simp only [MonoidHom.domRestrict_apply] at huv
    have hψeq : ψ (u : Su F0 2 1 m) = ψ (v : Su F0 2 1 m) := by
      apply (MulAut.conj g).injective
      simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] using huv
    have hmem : (u : Su F0 2 1 m) * (v : Su F0 2 1 m)⁻¹ ∈ coordBlockSU F0 2 1 T :=
      mul_mem u.2 (inv_mem v.2)
    have hone : (u : Su F0 2 1 m) * (v : Su F0 2 1 m)⁻¹ = 1 :=
      qTwoChartHub_inj_block S hψ hε0 h4T hmem
        (by rw [map_mul, map_inv, hψeq, mul_inv_cancel])
    exact Subtype.ext (mul_inv_eq_one.mp hone)
  have hrange : (((MulAut.conj g).toMonoidHom.comp ψ).domRestrict
      (coordBlockSU F0 2 1 T)).range = qTwoBlockOf ψ g T := by
    rw [MonoidHom.domRestrict_range]
    simp only [qTwoBlockOf]
  have e12 : Su K 2 1 T.card ≃* Su F0 2 1 T.card :=
    (qTwoChart_fieldTransport hF0 hK T.card).choose.symm
  have e23 : Su F0 2 1 T.card ≃* ↥(coordBlockSU F0 2 1 T) :=
    MonoidHom.ofInjective (f := blockSUOn F0 2 1 T)
      (blockSUOn_injective (K := F0) (p := 2) (f := 1) (n := m) T)
  have e34 : ↥(coordBlockSU F0 2 1 T) ≃* ↥(qTwoBlockOf ψ g T) :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  have e45 : ↥(qTwoBlockOf ψ g T) ≃* ↥(blk I) :=
    (MulEquiv.subgroupCongr hblkI).symm
  rw [← hcard]
  exact ⟨e12.trans (e23.trans (e34.trans e45))⟩

end CFSG.StandardType.QTwo

end
