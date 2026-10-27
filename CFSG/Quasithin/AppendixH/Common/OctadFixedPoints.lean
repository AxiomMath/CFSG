module

public import CFSG.Quasithin.AppendixH.Common.OctadActionRange
public import CFSG.Quasithin.AppendixH.Common.OctadCentralizer
public import CFSG.Quasithin.AppendixH.Common.OctadAltFix

public section

open scoped Pointwise

namespace CFSG.ASVolI.AppH

open CFSG.ASVolI.ChH CFSG.Monster.Code

theorem eq_of_five_subset {c c' : Finset (Fin 24)} (hc : IsOctad c) (hc' : IsOctad c')
    {T : Finset (Fin 24)} (hT : T.card = 5) (h : T ⊆ c) (h' : T ⊆ c') : c = c' := by
  rw [isOctad_iff_mem_octads] at hc hc'
  obtain ⟨O, ⟨hO, hTO⟩, huniq⟩ := existsUnique_octad T hT
  exact (huniq c ⟨hc, h⟩).trans (huniq c' ⟨hc', h'⟩).symm

theorem smul_octad_eq_of_fix_five {g : S24} (hg : g ∈ M24g) {c : Finset (Fin 24)}
    (hc : IsOctad c) {T : Finset (Fin 24)} (hT : T.card = 5) (hTc : T ⊆ c)
    (hfix : ∀ i ∈ T, g i = i) : g • c = c := by
  apply eq_of_five_subset (isOctad_smul hg hc) hc hT
  · intro i hi
    rw [smul_finset_eq_map, Finset.mem_map_equiv, ← hfix i hi, Equiv.symm_apply_apply]
    exact hTc hi
  · exact hTc

theorem card_inter_le_five_of_fix {g : S24} (hg : g ∈ M24g)
    (hg1 : g ≠ 1) {F : Finset (Fin 24)} (hF : 9 ≤ F.card) (hfix : ∀ i ∈ F, g i = i)
    {c : Finset (Fin 24)} (hc : IsOctad c) : (c ∩ F).card ≤ 5 := by
  by_contra hle
  rw [not_le] at hle
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq (show 5 ≤ (c ∩ F).card by omega)
  have hTc : T ⊆ c := fun i hi => (Finset.mem_inter.1 (hTsub hi)).1
  have hTF : T ⊆ F := fun i hi => (Finset.mem_inter.1 (hTsub hi)).2
  have hgstab : g ∈ octStab c := by
    rw [mem_octStab_iff]
    exact ⟨hg, smul_octad_eq_of_fix_five hg hc hTcard hTc (fun i hi => hfix i (hTF hi))⟩
  have hσalt : octAct c ⟨g, hgstab⟩ ∈ alternatingGroup ↥c := by
    rw [← range_octAct hc]
    exact MonoidHom.mem_range.2 ⟨⟨g, hgstab⟩, rfl⟩
  let W : Finset ↥c := Finset.univ.filter fun x => (x : Fin 24) ∈ F
  let Z : Finset ↥c := Finset.univ.filter fun x => (x : Fin 24) ∉ F
  have hW : W.image (Subtype.val : ↥c → Fin 24) = c ∩ F := by
    ext y
    simp only [W, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_inter]
    constructor
    · rintro ⟨x, hxF, rfl⟩
      exact ⟨x.2, hxF⟩
    · rintro ⟨hyc, hyF⟩
      exact ⟨⟨y, hyc⟩, hyF, rfl⟩
  have hWcard : W.card = (c ∩ F).card := by
    rw [← Finset.card_image_of_injective W Subtype.val_injective, hW]
  have hZeq : Z = (Finset.univ : Finset ↥c) \ W := by
    ext x
    simp only [Z, W, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and]
  have hZcard : Z.card ≤ 2 := by
    rw [hZeq, Finset.card_sdiff_of_subset (Finset.subset_univ W), Finset.card_univ,
      Fintype.card_coe, hc.1, hWcard]
    omega
  have hfixZ : ∀ x, x ∉ Z → octAct c ⟨g, hgstab⟩ x = x := by
    intro x hx
    apply Subtype.ext
    rw [octAct_apply]
    exact hfix x.1 (by
      by_contra hxF
      exact hx (by simp [Z, hxF]))
  have hσ1 : octAct c ⟨g, hgstab⟩ = 1 := eq_one_of_even_of_fix_compl Z hZcard hσalt hfixZ
  have hfixc : ∀ i ∈ c, g i = i := by
    intro i hi
    have h1 : octAct c ⟨g, hgstab⟩ ⟨i, hi⟩ = ⟨i, hi⟩ := by rw [hσ1]; rfl
    have h2 := congrArg (fun x : ↥c => (x : Fin 24)) h1
    simpa only [octAct_apply, Subtype.coe_mk] using h2
  have hlt : c.card < F.card := by rw [hc.1]; omega
  obtain ⟨p, hpF, hpc⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  exact hg1 (eq_one_of_fix_octad_of_fix_outside hc hg hfixc hpc (hfix p hpF))

theorem sum_choose_card_inter_octads (F : Finset (Fin 24)) {j : ℕ} (hj : j ≤ 5) :
    (∑ c ∈ octads, (c ∩ F).card.choose j) * (8 - j).choose (5 - j) =
      F.card.choose j * (24 - j).choose (5 - j) := by
  have hpow : ∀ c : Finset (Fin 24),
      ((F.powersetCard j).filter (fun T => T ⊆ c)) = (c ∩ F).powersetCard j := by
    intro c
    ext T
    rw [Finset.mem_filter, Finset.mem_powersetCard, Finset.mem_powersetCard]
    constructor
    · rintro ⟨⟨hTF, hTcard⟩, hTc⟩
      exact ⟨fun x hx => Finset.mem_inter.2 ⟨hTc hx, hTF hx⟩, hTcard⟩
    · rintro ⟨hTsub, hTcard⟩
      exact ⟨⟨fun x hx => (Finset.mem_inter.1 (hTsub hx)).2, hTcard⟩,
        fun x hx => (Finset.mem_inter.1 (hTsub hx)).1⟩
  have hsum : (∑ c ∈ octads, (c ∩ F).card.choose j)
      = ∑ T ∈ F.powersetCard j, (octads.filter (fun c => T ⊆ c)).card := by
    have h1 : (∑ c ∈ octads, (c ∩ F).card.choose j)
        = ∑ c ∈ octads, ((F.powersetCard j).filter (fun T => T ⊆ c)).card := by
      refine Finset.sum_congr rfl ?_
      intro c _
      rw [hpow c, Finset.card_powersetCard]
    rw [h1]
    calc ∑ c ∈ octads, ((F.powersetCard j).filter (fun T => T ⊆ c)).card
        = ∑ c ∈ octads, ∑ T ∈ F.powersetCard j, (if T ⊆ c then 1 else 0) := by
          refine Finset.sum_congr rfl ?_
          intro c _
          rw [Finset.card_filter]
      _ = ∑ T ∈ F.powersetCard j, ∑ c ∈ octads, (if T ⊆ c then 1 else 0) := by
          rw [Finset.sum_comm]
      _ = ∑ T ∈ F.powersetCard j, (octads.filter (fun c => T ⊆ c)).card := by
          refine Finset.sum_congr rfl ?_
          intro T _
          rw [Finset.card_filter]
  calc (∑ c ∈ octads, (c ∩ F).card.choose j) * (8 - j).choose (5 - j)
      = (∑ T ∈ F.powersetCard j, (octads.filter (fun c => T ⊆ c)).card) *
          (8 - j).choose (5 - j) := by rw [hsum]
    _ = ∑ T ∈ F.powersetCard j,
          ((octads.filter (fun c => T ⊆ c)).card * (8 - j).choose (5 - j)) := by
          rw [Finset.sum_mul]
    _ = ∑ T ∈ F.powersetCard j, (24 - j).choose (5 - j) := by
          refine Finset.sum_congr rfl ?_
          intro T hT
          rw [Finset.mem_powersetCard] at hT
          rw [← hT.2]
          exact card_octads_superset T (by omega)
    _ = F.card.choose j * (24 - j).choose (5 - j) := by
          rw [Finset.sum_const, Finset.card_powersetCard, smul_eq_mul]

theorem exists_octad_card_inter_ge_six (F : Finset (Fin 24)) (hF : F.card = 9) :
    ∃ c ∈ octads, 6 ≤ (c ∩ F).card := by
  by_contra h
  rw [not_exists] at h
  simp only [not_and, not_le] at h
  have hfib : ∀ j ≤ 5, (∑ c ∈ octads, (c ∩ F).card.choose j) * (8 - j).choose (5 - j)
      = ∑ i ∈ Finset.range 6,
          ((octads.filter fun c => (c ∩ F).card = i).card * i.choose j) *
            (8 - j).choose (5 - j) := by
    intro j hj
    rw [← Finset.sum_fiberwise_of_maps_to (s := octads) (t := Finset.range 6)
      (g := fun c => (c ∩ F).card) (f := fun c => (c ∩ F).card.choose j) (fun c hc => by
        rw [Finset.mem_range]
        exact h c hc)]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro i _
    congr 1
    have h1 : (∑ c ∈ octads.filter (fun c => (c ∩ F).card = i), (c ∩ F).card.choose j)
        = ∑ c ∈ octads.filter (fun c => (c ∩ F).card = i), i.choose j :=
      Finset.sum_congr rfl (fun c hc => by
        rw [Finset.mem_filter] at hc
        rw [hc.2])
    rw [h1, Finset.sum_const, smul_eq_mul]
  have hE : ∀ j ≤ 5, (∑ i ∈ Finset.range 6,
        ((octads.filter fun c => (c ∩ F).card = i).card * i.choose j) *
          (8 - j).choose (5 - j)) = Nat.choose 9 j * (24 - j).choose (5 - j) := by
    intro j hj
    rw [← hfib j hj]
    have := sum_choose_card_inter_octads F (j := j) hj
    rwa [hF] at this
  have e0 := hE 0 (by norm_num)
  have e1 := hE 1 (by norm_num)
  have e2 := hE 2 (by norm_num)
  have e3 := hE 3 (by norm_num)
  have e4 := hE 4 (by norm_num)
  have e5 := hE 5 (by norm_num)
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose] at e0 e1 e2 e3 e4 e5
  omega

theorem eq_one_of_fix_nine {g : S24} (hg : g ∈ M24g)
    {F : Finset (Fin 24)} (hF : 9 ≤ F.card) (hfix : ∀ i ∈ F, g i = i) : g = 1 := by
  by_contra hg1
  obtain ⟨F', hF'sub, hF'card⟩ := Finset.exists_subset_card_eq hF
  obtain ⟨c, hc, hci⟩ := exists_octad_card_inter_ge_six F' hF'card
  have h5 := card_inter_le_five_of_fix hg hg1 (F := F') (by omega)
    (fun i hi => hfix i (hF'sub hi)) (isOctad_iff_mem_octads.2 hc)
  omega

end CFSG.ASVolI.AppH
