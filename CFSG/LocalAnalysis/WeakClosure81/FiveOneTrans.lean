module

public import CFSG.LocalAnalysis.WeakClosure81.FiveOneEnd
public import CFSG.LocalAnalysis.WeakClosure81.FiveCoatom

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem b5_FiveOneTrans_card_map_mk'_eq_relIndex {A : Type*} [Group A] [Finite A]
    (S' : Subgroup A) [S'.Normal] (V : Subgroup A) (hSV : S' ≤ V) :
    Nat.card (V.map (QuotientGroup.mk' S')) = S'.relIndex V := by
  have hcomap : (V.map (QuotientGroup.mk' S')).comap (QuotientGroup.mk' S') = V :=
    Subgroup.comap_map_eq_self (by rw [QuotientGroup.ker_mk']; exact hSV)
  have hindex : (V.map (QuotientGroup.mk' S')).index = V.index := by
    rw [← Subgroup.index_comap_of_surjective
      (H := V.map (QuotientGroup.mk' S')) (QuotientGroup.mk'_surjective S'), hcomap]
  have h1 : Nat.card (V.map (QuotientGroup.mk' S')) * (V.map (QuotientGroup.mk' S')).index
      = S'.relIndex V * V.index := by
    rw [Subgroup.card_mul_index (V.map (QuotientGroup.mk' S')),
      Subgroup.relIndex_mul_index hSV]
    exact (Subgroup.index_eq_card (H := S')).symm
  rw [hindex] at h1
  exact Nat.eq_of_mul_eq_mul_right
    (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := V))) h1

theorem five_one_end {H M S : Subgroup G} (hM : IsMaxSubgroupIn H M)
    (hodd : Odd (M.relIndex H)) (hS : IsPGroup 2 S) (hSM : S ≤ M) (hSn : (S.subgroupOf H).Normal)
    (hSw : 2 ∣ S.relIndex M) (hnn : ¬ (M.subgroupOf H).Normal)
    (hu : ∀ X L : Subgroup G, S < X → X ≤ M → IsPGroup 2 X → IsMaxSubgroupIn H L → X ≤ L →
      L = M) :
    ∃ N₀ : Subgroup G, IsMaxSubgroupIn H N₀ ∧ S ≤ N₀ ∧ ¬ N₀ ≤ M ∧ Odd (M.relIndex N₀) := by
  have hMH : M ≤ H := hM.le
  have hSH : S ≤ H := hSM.trans hMH
  let M' : Subgroup ↥H := M.subgroupOf H
  let S' : Subgroup ↥H := S.subgroupOf H
  have hS'M' : S' ≤ M' := Subgroup.subgroupOf_mono H hSM
  haveI hS'normal : S'.Normal := hSn
  let q : ↥H →* (↥H ⧸ S') := QuotientGroup.mk' S'
  have hq_surj : Function.Surjective q := QuotientGroup.mk'_surjective S'
  have hq_ker : q.ker = S' := QuotientGroup.ker_mk' S'
  let Mbar : Subgroup (↥H ⧸ S') := M'.map q
  have hMbar_comap : Mbar.comap q = M' :=
    Subgroup.comap_map_eq_self (by rw [hq_ker]; exact hS'M')
  have hM'coat : IsCoatom M' := isCoatom_subgroupOf hM
  have hMbar_ne_top : Mbar ≠ ⊤ := by
    intro htop
    apply hM'coat.1
    calc M' = Mbar.comap q := hMbar_comap.symm
      _ = (⊤ : Subgroup (↥H ⧸ S')).comap q := by rw [htop]
      _ = ⊤ := Subgroup.comap_top q
  have hMbar_coatom : IsCoatom Mbar := by
    refine ⟨hMbar_ne_top, fun V hV => ?_⟩
    have hlt : M' < V.comap q := by
      have h := (Subgroup.comap_lt_comap_of_surjective hq_surj).mpr hV
      rwa [hMbar_comap] at h
    have htop : V.comap q = ⊤ := hM'coat.2 _ hlt
    calc V = (V.comap q).map q :=
          (Subgroup.map_comap_eq_self_of_surjective hq_surj V).symm
      _ = (⊤ : Subgroup ↥H).map q := by rw [htop]
      _ = ⊤ := Subgroup.map_top_of_surjective q hq_surj
  have hMbar_index : Mbar.index = M.relIndex H := by
    rw [← Subgroup.index_comap_of_surjective (H := Mbar) hq_surj, hMbar_comap]
    rfl
  have hMbar_odd : Odd Mbar.index := by rw [hMbar_index]; exact hodd
  have hcardMbar : Nat.card Mbar = S.relIndex M := by
    have h := b5_FiveOneTrans_card_map_mk'_eq_relIndex S' M' hS'M'
    rw [Subgroup.relIndex_subgroupOf hMH] at h
    exact h
  have hevMbar : Even (Nat.card Mbar) := by rw [hcardMbar, even_iff_two_dvd]; exact hSw
  have hMbar_nn : ¬ Mbar.Normal := by
    intro hnorm
    apply hnn
    change M'.Normal
    rw [← hMbar_comap]
    exact hnorm.comap q
  have hu_bar : ∀ X L : Subgroup (↥H ⧸ S'), X ≤ Mbar → X ≠ ⊥ → IsPGroup 2 X →
      IsCoatom L → X ≤ L → L = Mbar := by
    intro Xbar Lbar hXbarM hXbar_ne hXbar_p hLbar_coat hXbarLbar
    let X' : Subgroup ↥H := Xbar.comap q
    let L' : Subgroup ↥H := Lbar.comap q
    have hS'X' : S' ≤ X' := by
      rw [hq_ker.symm]
      exact Subgroup.ker_le_comap (f := q) Xbar
    have hS'neX' : S' ≠ X' := by
      intro heq
      have hbot : S'.map q = ⊥ := by
        rw [Subgroup.map_eq_bot_iff (H := S') (f := q)]
        exact le_of_eq hq_ker.symm
      have hX'map : X'.map q = Xbar :=
        Subgroup.map_comap_eq_self_of_surjective hq_surj Xbar
      have : Xbar = ⊥ := by rw [← hX'map, ← heq, hbot]
      exact hXbar_ne this
    have hX'M' : X' ≤ M' := by
      have h := Subgroup.comap_mono (f := q) hXbarM
      rwa [hMbar_comap] at h
    have hX'_p : IsPGroup 2 X' := by
      refine IsPGroup.comap_of_ker_isPGroup hXbar_p q ?_
      rw [hq_ker]
      exact IsPGroup.comap_subtype hS
    have hL'_coat : IsCoatom L' :=
      Subgroup.isCoatom_comap_of_surjective hq_surj hLbar_coat
    have hX'L' : X' ≤ L' := Subgroup.comap_mono (f := q) hXbarLbar
    have hSX : S < X'.map H.subtype := by
      have h := (Subgroup.map_lt_map_iff_of_injective H.subtype_injective).mpr
        (lt_of_le_of_ne hS'X' hS'neX')
      rwa [Subgroup.map_subgroupOf_eq_of_le hSH] at h
    have hXM : X'.map H.subtype ≤ M := by
      have h := Subgroup.map_mono (f := H.subtype) hX'M'
      rwa [Subgroup.map_subgroupOf_eq_of_le hMH] at h
    have hX_p : IsPGroup 2 (X'.map H.subtype) := hX'_p.map H.subtype
    have hLmax : IsMaxSubgroupIn H (L'.map H.subtype) := isMaxSubgroupIn_map_subtype hL'_coat
    have hXL : X'.map H.subtype ≤ L'.map H.subtype :=
      Subgroup.map_mono (f := H.subtype) hX'L'
    have hLM : L'.map H.subtype = M :=
      hu (X'.map H.subtype) (L'.map H.subtype) hSX hXM hX_p hLmax hXL
    have hL'M' : L' = M' := by
      apply Subgroup.map_injective H.subtype_injective
      rw [Subgroup.map_subgroupOf_eq_of_le hMH]
      exact hLM
    calc Lbar = L'.map q :=
          (Subgroup.map_comap_eq_self_of_surjective hq_surj Lbar).symm
      _ = M'.map q := by rw [hL'M']
      _ = Mbar := rfl
  obtain ⟨Nbar, hNbar_coat, hNbar_odd⟩ :=
    exists_odd_coatom_of_unique_max hMbar_coatom hMbar_odd hevMbar hMbar_nn hu_bar
  let N' : Subgroup ↥H := Nbar.comap q
  let N₀ : Subgroup G := N'.map H.subtype
  have hN'_coat : IsCoatom N' :=
    Subgroup.isCoatom_comap_of_surjective hq_surj hNbar_coat
  have hS'N' : S' ≤ N' := by
    rw [hq_ker.symm]
    exact Subgroup.ker_le_comap (f := q) Nbar
  refine ⟨N₀, isMaxSubgroupIn_map_subtype hN'_coat, ?_, ?_, ?_⟩
  · have h := Subgroup.map_mono (f := H.subtype) hS'N'
    rwa [Subgroup.map_subgroupOf_eq_of_le hSH] at h
  · intro hN₀M
    have hN₀M' : N'.map H.subtype ≤ M'.map H.subtype := by
      rw [Subgroup.map_subgroupOf_eq_of_le hMH]
      exact hN₀M
    have hN'M' : N' ≤ M' :=
      (Subgroup.map_le_map_iff_of_injective H.subtype_injective).mp hN₀M'
    have hNbar_le : Nbar ≤ Mbar := by
      have h := Subgroup.map_mono (f := q) hN'M'
      rwa [Subgroup.map_comap_eq_self_of_surjective hq_surj Nbar] at h
    have hMbar_eq : Mbar = Nbar := by
      rcases hNbar_coat.le_iff.mp hNbar_le with h | h
      · exact absurd h hMbar_ne_top
      · exact h
    exact (Nat.not_even_iff_odd.mpr hNbar_odd) (hMbar_eq ▸ hevMbar)
  · have hdiv : M.relIndex N₀ ∣ S.relIndex N₀ :=
      Subgroup.relIndex_dvd_of_le_left (H := S) (K := M) (L := N₀) hSM
    have hSrel : S.relIndex N₀ = S'.relIndex N' := by
      have h := Subgroup.relIndex_map_map_of_injective S' N' H.subtype_injective
      rwa [Subgroup.map_subgroupOf_eq_of_le hSH] at h
    have hcardNbar : Nat.card Nbar = S'.relIndex N' := by
      have h := b5_FiveOneTrans_card_map_mk'_eq_relIndex S' N' hS'N'
      rwa [Subgroup.map_comap_eq_self_of_surjective hq_surj Nbar] at h
    have hodd_Srel : Odd (S'.relIndex N') := by rw [← hcardNbar]; exact hNbar_odd
    have hodd_Srel' : Odd (S.relIndex N₀) := by rw [hSrel]; exact hodd_Srel
    exact Odd.of_dvd_nat hodd_Srel' hdiv

end CFSG.LocalAnalysis.WeakClosure81
