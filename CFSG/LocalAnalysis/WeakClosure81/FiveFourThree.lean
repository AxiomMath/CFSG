module

public import CFSG.LocalAnalysis.WeakClosure81.FiveFour
public import CFSG.LocalAnalysis.WeakClosure81.FiveFourNil
public import CFSG.Quasithin.Background.E1Defs
public import CFSG.LocalAnalysis.WeakClosure81.FiveSylow

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem five_four_three {H M A X : Subgroup G} (h : Sec5Hyp H M A) (hM : maxOver H A = {M})
    (hX : IsMinNormalOver H (kerMOf M H) X) :
    E1.IsTwoClosed (kerMOf M H) ∧
      Group.IsNilpotent (↥(kerMOf M H) ⧸ pCore 2 ↥(kerMOf M H)) := by
  classical
  have hYH : kerMOf M H ≤ H := kerMOf_le_group M H
  have hYn : ((kerMOf M H).subgroupOf H).Normal := normal_subgroupOf_kerMOf M H
  have h2 : ∀ K : Subgroup G, K ≤ H → A ≤ K → X ≤ K ⊔ kerMOf M H → K = H :=
    fun K hKH hAK hXK => five_four_two hM hX hKH hAK hXK
  have hApg : IsPGroup 2 A := fun y => ⟨1, by
    apply Subtype.ext
    simpa using h.isElemAbelian.2 y y.2⟩
  obtain ⟨T, hT, hAT⟩ := exists_isSylowIn_ge 2 h.le_group hApg
  have hPY : IsSylowIn 2 (T ⊓ kerMOf M H) (kerMOf M H) := hT.inf_normal hYH hYn
  have hTnorm : T ≤ normalizer ((T ⊓ kerMOf M H : Subgroup G) : Set G) := by
    intro t ht
    rw [mem_normalizer_iff]
    intro g
    constructor
    · intro hg
      obtain ⟨hgT, hgY⟩ := Subgroup.mem_inf.mp hg
      exact Subgroup.mem_inf.mpr
        ⟨T.mul_mem (T.mul_mem ht hgT) (T.inv_mem ht),
          conj_mem_kerMOf (hT.le ht) hgY⟩
    · intro hg
      obtain ⟨hgT, hgY⟩ := Subgroup.mem_inf.mp hg
      have hmem : t⁻¹ * (t * g * t⁻¹) * (t⁻¹)⁻¹ ∈ T ⊓ kerMOf M H :=
        Subgroup.mem_inf.mpr
          ⟨T.mul_mem (T.mul_mem (T.inv_mem ht) hgT) (T.inv_mem (T.inv_mem ht)),
            conj_mem_kerMOf (H.inv_mem (hT.le ht)) hgY⟩
      have hge : g = t⁻¹ * (t * g * t⁻¹) * (t⁻¹)⁻¹ := by group
      rw [hge]
      exact hmem
  let L : Subgroup G := H ⊓ normalizer ((T ⊓ kerMOf M H : Subgroup G) : Set G)
  have hAL : A ≤ L := le_inf h.le_group (hAT.trans hTnorm)
  have hXL : X ≤ L ⊔ kerMOf M H := by
    intro x hxX
    have hxH : x ∈ H := hX.2.1 hxX
    obtain ⟨y, hyY, n, hnH, hnN, hyn⟩ := frattini_isSylowIn hYH hYn hPY x hxH
    have hnL : n ∈ L := Subgroup.mem_inf.mpr ⟨hnH, hnN⟩
    have hx' : y * n ∈ kerMOf M H ⊔ L := Subgroup.mul_mem_sup hyY hnL
    rw [hyn] at hx'
    rwa [sup_comm] at hx'
  have hLeq : L = H := h2 L inf_le_left hAL hXL
  have hHnorm : H ≤ normalizer ((T ⊓ kerMOf M H : Subgroup G) : Set G) :=
    (le_of_eq hLeq.symm).trans inf_le_right
  have hPleH : (T ⊓ kerMOf M H : Subgroup G) ≤ H := inf_le_left.trans hT.le
  have hPH : ((T ⊓ kerMOf M H).subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPleH).2 hHnorm
  have hPYnorm : ((T ⊓ kerMOf M H).subgroupOf (kerMOf M H)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).2 (hYH.trans hHnorm)
  have hTwoClosed : E1.IsTwoClosed (kerMOf M H) :=
    ⟨T ⊓ kerMOf M H, hPY, hPYnorm⟩
  haveI : ((T ⊓ kerMOf M H).subgroupOf (kerMOf M H)).Normal := hPYnorm
  have hsupp : ∀ K : Subgroup G, K ≤ H → T ≤ K → kerMOf M H ⊔ K = H → K = H := by
    intro K hKH hTK hYK
    refine h2 K hKH (hAT.trans hTK) ?_
    calc X ≤ H := hX.2.1
      _ = kerMOf M H ⊔ K := hYK.symm
      _ = K ⊔ kerMOf M H := by rw [sup_comm]
  have hNilYP : Group.IsNilpotent
      (↥(kerMOf M H) ⧸ (T ⊓ kerMOf M H).subgroupOf (kerMOf M H)) :=
    isNilpotent_quotient_of_supplement hYH hYn inf_le_right hPH hPY hT.isPGroup hT.le hsupp
  have hPsubP : IsPGroup 2 ((T ⊓ kerMOf M H).subgroupOf (kerMOf M H)) :=
    hPY.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
  have hle : (T ⊓ kerMOf M H).subgroupOf (kerMOf M H) ≤ pCore 2 ↥(kerMOf M H) := by
    show (T ⊓ kerMOf M H).subgroupOf (kerMOf M H)
      ≤ sSup {K : Subgroup ↥(kerMOf M H) | K.Normal ∧ IsPGroup 2 K}
    exact le_sSup ⟨hPYnorm, hPsubP⟩
  refine ⟨hTwoClosed, ?_⟩
  have hle' : (T ⊓ kerMOf M H).subgroupOf (kerMOf M H)
      ≤ (pCore 2 ↥(kerMOf M H)).comap (MonoidHom.id ↥(kerMOf M H)) := by
    simpa using hle
  haveI : Group.IsNilpotent
      (↥(kerMOf M H) ⧸ (T ⊓ kerMOf M H).subgroupOf (kerMOf M H)) := hNilYP
  refine Group.nilpotent_of_surjective
    (QuotientGroup.map ((T ⊓ kerMOf M H).subgroupOf (kerMOf M H))
      (pCore 2 ↥(kerMOf M H)) (MonoidHom.id ↥(kerMOf M H)) hle') ?_
  intro z
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (N := pCore 2 ↥(kerMOf M H)) z
  exact ⟨QuotientGroup.mk y, by simp⟩

end CFSG.LocalAnalysis.WeakClosure81
