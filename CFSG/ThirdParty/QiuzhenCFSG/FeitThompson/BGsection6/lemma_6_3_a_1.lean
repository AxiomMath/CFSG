module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection6.theorem_6_2

namespace CFSG
end CFSG
open CFSG

open scoped MatrixGroups Pointwise TensorProduct

/-! # lemma_6_3_a_1 from BG Section 6 -/

public theorem CFSG.lemma_6_3_a_1
    {G : Type*} [Group G] [Finite G] [Group.IsSolvable G]
    {H : Subgroup G} [H.Normal] (hHall : ∃ π : Set Nat.Primes, IsHallSubgroup π H)
    {K : Subgroup G} (hCompl : IsCompl H K) (hld : H ≤ derivedSubgroup G) :
    H = ⁅H, K⁆ := by
  let _ := hHall
  let N : Subgroup G := ⁅H, H⁆ ⊔ ⁅H, K⁆
  have hHK' : H.IsComplement' K := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hCompl.disjoint ?_
    ext g
    constructor
    · rintro ⟨h, hh, k, hk, rfl⟩
      simp
    · intro _
      have hg_top : g ∈ (⊤ : Subgroup G) := by simp
      rw [← hCompl.sup_eq_top] at hg_top
      rcases (Subgroup.mem_sup_of_normal_left (s := H) (t := K) (x := g)).mp hg_top with
        ⟨h, hh, k, hk, rfl⟩
      exact ⟨h, hh, k, hk, rfl⟩
  have hHH_le_H : ⁅H, H⁆ ≤ H := Subgroup.commutator_le_left (H₁ := H) (H₂ := H)
  have hHK_le_H : ⁅H, K⁆ ≤ H := Subgroup.commutator_le_left (H₁ := H) (H₂ := K)
  have hN_le_H : N ≤ H := sup_le hHH_le_H hHK_le_H
  have hHK_normal : (⁅H, K⁆).Normal := by
    have hcomm_le_sup : ⁅H, K⁆ ≤ H ⊔ K := commutator_le_sup H K
    have hsup_le_norm : H ⊔ K ≤ Subgroup.normalizer (((⁅H, K⁆ : Subgroup G) : Set G)) := by
      exact (Subgroup.normal_subgroupOf_iff_le_normalizer hcomm_le_sup).mp
        (commutator_normal_in_sup H K)
    have hnorm_top : Subgroup.normalizer (((⁅H, K⁆ : Subgroup G) : Set G)) = ⊤ := by
      apply top_le_iff.mp
      rw [← hHK'.sup_eq_top]
      exact hsup_le_norm
    exact (Subgroup.normalizer_eq_top_iff).mp hnorm_top
  have hN_normal : N.Normal := by
    dsimp [N]
    infer_instance
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  let Hq : Subgroup (G ⧸ N) := H.map q
  let Kq : Subgroup (G ⧸ N) := K.map q
  have hCompq : Hq.IsComplement' Kq := by
    simpa [Hq, Kq, q] using
      isComplement'_map_mk'_of_le_isComplement' H K N hN_le_H hHK'
  have hHH_map_bot : (⁅H, H⁆).map q = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact le_sup_left
  have hHK_map_bot : (⁅H, K⁆).map q = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact le_sup_right
  have hHq_comm_bot : ⁅Hq, Hq⁆ = ⊥ := by
    calc
      ⁅Hq, Hq⁆ = (⁅H, H⁆).map q := by
        simpa [Hq] using (Subgroup.map_commutator (H₁ := H) (H₂ := H) q).symm
      _ = ⊥ := hHH_map_bot
  have hHq_cent : Hq ≤ Subgroup.centralizer (Hq : Set (G ⧸ N)) := by
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer).1 hHq_comm_bot
  let : IsMulCommutative ↥Hq := by
    refine ⟨⟨?_⟩⟩
    intro x y
    apply Subtype.ext
    exact ((Subgroup.mem_centralizer_iff.mp (hHq_cent x.2)) y y.2).symm
  have hHqKq_comm_bot : ⁅Hq, Kq⁆ = ⊥ := by
    calc
      ⁅Hq, Kq⁆ = (⁅H, K⁆).map q := by
        simpa [Hq, Kq] using (Subgroup.map_commutator (H₁ := H) (H₂ := K) q).symm
      _ = ⊥ := hHK_map_bot
  have hHq_centKq : Hq ≤ Subgroup.centralizer (Kq : Set (G ⧸ N)) := by
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer).1 hHqKq_comm_bot
  have hHq_le_normKq : Hq ≤ Subgroup.normalizer (Kq : Set (G ⧸ N)) := by
    exact hHq_centKq.trans (centralizer_le_normalizer (R := Kq))
  have htop_le_normKq : (⊤ : Subgroup (G ⧸ N)) ≤ Subgroup.normalizer (Kq : Set (G ⧸ N)) := by
    rw [← hCompq.sup_eq_top]
    exact sup_le hHq_le_normKq Subgroup.le_normalizer
  have hnormKq_eq_top : Subgroup.normalizer (Kq : Set (G ⧸ N)) = ⊤ := top_le_iff.mp htop_le_normKq
  have hKq_normal : Kq.Normal := (Subgroup.normalizer_eq_top_iff).mp hnormKq_eq_top
  let : Kq.Normal := hKq_normal
  have hderivedQ_le_Kq : derivedSubgroup (G ⧸ N) ≤ Kq := by
    simpa [derivedSubgroup] using
      (Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top
        (N := Kq) (H := Hq) (by simpa [sup_comm] using hCompq.sup_eq_top) inferInstance)
  have hmap_derived : (derivedSubgroup G).map q = derivedSubgroup (G ⧸ N) := by
    exact map_derivedSeries_eq (f := q) (QuotientGroup.mk'_surjective N) 1
  have hHq_le_derivedQ : Hq ≤ derivedSubgroup (G ⧸ N) := by
    rw [← hmap_derived]
    exact Subgroup.map_mono hld
  have hHq_le_Kq : Hq ≤ Kq := hHq_le_derivedQ.trans hderivedQ_le_Kq
  have hHq_bot : Hq = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    exact (Subgroup.disjoint_def.mp hCompq.disjoint) hx (hHq_le_Kq hx)
  have hH_le_N : H ≤ N := by
    simpa [Hq, q, QuotientGroup.ker_mk'] using
      (Subgroup.map_eq_bot_iff (f := q) (H := H)).mp hHq_bot
  let C : Subgroup H := (⁅H, H⁆).subgroupOf H
  let Nsub : Subgroup H := (⁅H, K⁆).subgroupOf H
  have : Nsub.Normal := by
    dsimp [Nsub]
    infer_instance
  have hC_eq_comm : C = _root_.commutator H := by
    apply (Subgroup.map_injective H.subtype_injective)
    calc
      C.map H.subtype = ⁅H, H⁆ := by
        simpa [C] using (Subgroup.map_subgroupOf_eq_of_le (G := G) (H := ⁅H, H⁆) (K := H) hHH_le_H)
      _ = (_root_.commutator H).map H.subtype := by
        simpa using (Subgroup.map_subtype_commutator (H := H)).symm
  have htopH_le : (⊤ : Subgroup H) ≤ C ⊔ Nsub := by
    rw [← Subgroup.map_le_map_iff_of_injective H.subtype_injective]
    have htop_map : (⊤ : Subgroup H).map H.subtype = H := by
      ext x
      constructor
      · rintro ⟨y, -, rfl⟩
        exact y.2
      · intro hx
        exact ⟨⟨x, hx⟩, by simp, rfl⟩
    rw [htop_map]
    calc
      H ≤ N := hH_le_N
      _ = ⁅H, H⁆ ⊔ ⁅H, K⁆ := rfl
      _ = C.map H.subtype ⊔ Nsub.map H.subtype := by
        rw [show C.map H.subtype = ⁅H, H⁆ by
              simpa [C] using
                (Subgroup.map_subgroupOf_eq_of_le (G := G) (H := ⁅H, H⁆) (K := H) hHH_le_H)]
        rw [show Nsub.map H.subtype = ⁅H, K⁆ by
              simpa [Nsub] using
                (Subgroup.map_subgroupOf_eq_of_le (G := G) (H := ⁅H, K⁆) (K := H) hHK_le_H)]
      _ = (C ⊔ Nsub).map H.subtype := by
        symm
        simpa using (Subgroup.map_sup C Nsub H.subtype)
  let qH : H →* H ⧸ Nsub := QuotientGroup.mk' Nsub
  have hNsub_map_bot : Nsub.map qH = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  have hqH_top : (⊤ : Subgroup H).map qH = ⊤ := by
    exact Subgroup.map_top_of_surjective (f := qH) (QuotientGroup.mk'_surjective Nsub)
  have hcommH_map_top : (_root_.commutator H).map qH = ⊤ := by
    have htop_le :
        (⊤ : Subgroup (H ⧸ Nsub)) ≤ C.map qH := by
      simpa [hqH_top, Subgroup.map_sup, hNsub_map_bot] using
        (Subgroup.map_mono htopH_le : (⊤ : Subgroup H).map qH ≤ (C ⊔ Nsub).map qH)
    have hC_map_top : C.map qH = ⊤ := top_le_iff.mp htop_le
    simpa [hC_eq_comm] using hC_map_top
  have hcommQ_top : _root_.commutator (H ⧸ Nsub) = ⊤ := by
    calc
      _root_.commutator (H ⧸ Nsub) = (_root_.commutator H).map qH := by
        exact (map_derivedSeries_eq (f := qH) (QuotientGroup.mk'_surjective Nsub) 1).symm
      _ = ⊤ := hcommH_map_top
  have hNsub_top : Nsub = ⊤ := by
    by_contra hNsub_ne_top
    have : Nontrivial (H ⧸ Nsub) := (QuotientGroup.nontrivial_iff (N := Nsub)).2 hNsub_ne_top
    have hsolvQ : Group.IsSolvable (H ⧸ Nsub) := by
      have hsolvH : Group.IsSolvable H := inferInstance
      infer_instance
    have : Group.IsPerfect (H ⧸ Nsub) := (Group.isPerfect_def).2 hcommQ_top
    exact Group.IsPerfect.not_isSolvable (H ⧸ Nsub) hsolvQ
  apply le_antisymm
  · intro x hx
    have hx_top : (⟨x, hx⟩ : H) ∈ (⊤ : Subgroup H) := by simp
    have hx_nsub : (⟨x, hx⟩ : H) ∈ Nsub := by
      simp [hNsub_top]
    simpa [Nsub, Subgroup.mem_subgroupOf] using hx_nsub
  · exact hHK_le_H
