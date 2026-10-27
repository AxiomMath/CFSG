
module

public import CFSG.Monster.B.TwoA.Base.GeomObjBase

public import CFSG.Monster.B.TwoA.Base.Incidence
public import CFSG.Monster.B.TwoA.Base.RankThree

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA

open CFSG.Monster CFSG.Monster.B.Short CFSG.Monster.B Module

open scoped IsMulCommutative

attribute [local instance] parAction

theorem Kchain_le_Shat :
    ∀ i : ℕ, 1 ≤ i → i ≤ 5 → Kchain i ≤ Shat := by
  intro i h1 h5
  interval_cases i
  · rw [Kchain_one]
    exact Jhat_le_Shat
  · exact Ntwo_le_Shat
  · exact K3_le_Shat
  · exact K4_le_Shat
  · exact K5_le_Shat

theorem echain_data :
    ∀ i : ℕ, 2 ≤ i → i ≤ 5 →
    ∃ _ : CFSG.IsElementaryAbelian 2 (Echain i), Function.Surjective (conjE (Echain i)) := by
  intro i h2 h5
  interval_cases i
  · exact ⟨isElementaryAbelian_Vhat, conjE_Vhat_surjective⟩
  · exact ⟨isElementaryAbelian_E3, conjE_E3_surjective⟩
  · exact ⟨isElementaryAbelian_E4, conjE_E4_surjective⟩
  · exact ⟨isElementaryAbelian_E5, conjE_E5_surjective⟩

theorem isObj_of_le
    {i j : ℕ} {A B : Subgroup Dfull} (hA : IsObj i A) (hBA : B ≤ A)
    (hB : Nat.card B = 2 ^ j) (hj : 1 ≤ j) (hji : j ≤ i) : IsObj j B := by
  obtain ⟨hi1, hi5, g, hg, hAg⟩ := hA
  change A = conjSub g (Echain i) at hAg
  subst hAg
  refine ⟨hj, hji.trans hi5, ?_⟩
  rcases Nat.lt_or_ge i 2 with hi | hi
  · obtain rfl : i = 1 := by omega
    obtain rfl : j = 1 := by omega
    refine ⟨g, hg, Subgroup.eq_of_le_of_card_ge hBA ?_⟩
    rw [hB, natCard_conjSub, natCard_Echain 1 le_rfl (by norm_num)]
  obtain ⟨hinst, hsurj⟩ := echain_data i hi hi5
  have hB0 : conjSub g⁻¹ B ≤ Echain i := by
    have h1 := conjSub_mono (g := g⁻¹) hBA
    rwa [conjSub_inv_conjSub] at h1
  obtain ⟨k, hk, hkB⟩ := exists_conj_of_natCard_eq hsurj (Echain_mono hj hji hi5) hB0
    (by rw [natCard_conjSub, hB, natCard_Echain j hj (hji.trans hi5)])
  have hkS : k ∈ Shat := Kchain_le_Shat i hi1 hi5 hk
  refine ⟨g * k, Shat.mul_mem hg hkS, ?_⟩
  have h1 : conjSub k (Echain j) = conjSub g⁻¹ B := by
    refine Subgroup.eq_of_le_of_card_ge (fun x hx => ?_) ?_
    · obtain ⟨f, hf, rfl⟩ := hx
      exact hkB f hf
    · rw [natCard_conjSub, natCard_conjSub, hB, natCard_Echain j hj (hji.trans hi5)]
  rw [conjSub_mul, h1, conjSub_conjSub_inv]

theorem exists_conj_std_of_flag
    {F : Set ParGeom} (hF : IsParFlag F) :
    ∃ g ∈ Shat, ∀ x ∈ F, x.1.2 = conjSub g (Echain (parType x)) := by
  classical
  by_cases hne : F.Nonempty
  swap
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    exact ⟨1, Shat.one_mem, fun x hx => by rw [hne] at hx; exact absurd hx (Set.notMem_empty x)⟩
  set I : Finset ℕ := (Finset.Icc 1 5).filter (fun s => ∃ x ∈ F, parType x = s) with hI
  have hmemI : ∀ x ∈ F, parType x ∈ I := fun x hx =>
    Finset.mem_filter.2 ⟨parType_mem_Icc x, x, hx, rfl⟩
  have hIne : I.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨_, hmemI x hx⟩
  have hex : ∀ s ∈ I, ∃ x ∈ F, parType x = s := fun s hs => (Finset.mem_filter.1 hs).2
  let mem : ℕ → ParGeom := fun s =>
    if h : ∃ x ∈ F, parType x = s then Classical.choose h else (stdObj 1 le_rfl (by norm_num))
  have hmem : ∀ s ∈ I, mem s ∈ F ∧ parType (mem s) = s := by
    intro s hs
    have h := hex s hs
    have hm : mem s = Classical.choose h := dite_eq_left h
    rw [hm]
    exact Classical.choose_spec h
  have huniq : ∀ x ∈ F, mem (parType x) = x := fun x hx =>
    eq_of_parInc (hF _ (hmem _ (hmemI x hx)).1 x hx) (hmem _ (hmemI x hx)).2
  set t := I.max' hIne
  have htI : t ∈ I := I.max'_mem hIne
  set A := (mem t).1.2
  obtain ⟨-, -, g, hg, hAg⟩ := (mem t).2
  change A = conjSub g (Echain (parType (mem t))) at hAg
  rw [(hmem t htI).2] at hAg
  have hle : ∀ s ∈ I, (mem s).1.2 ≤ A := fun s hs =>
    le_of_parInc (hF _ (hmem s hs).1 _ (hmem t htI).1)
      (by rw [(hmem s hs).2, (hmem t htI).2]; exact I.le_max' s hs)
  have ht5 : t ≤ 5 := (Finset.mem_Icc.1 (Finset.mem_filter.1 htI).1).2
  have ht1 : 1 ≤ t := (Finset.mem_Icc.1 (Finset.mem_filter.1 htI).1).1
  have hs1 : ∀ s ∈ I, 1 ≤ s := fun s hs => (Finset.mem_Icc.1 (Finset.mem_filter.1 hs).1).1
  have hst : ∀ s ∈ I, s ≤ t := fun s hs => I.le_max' s hs
  rcases Nat.lt_or_ge t 2 with ht | ht
  ·
    refine ⟨g, hg, fun x hx => ?_⟩
    have hxt : parType x = t := le_antisymm (hst _ (hmemI x hx)) (by
      have := hs1 _ (hmemI x hx); omega)
    rw [← huniq x hx, hxt, (hmem t htI).2]
    exact hAg
  obtain ⟨hinst, hsurj⟩ := echain_data t ht ht5
  obtain ⟨k, hk, hkC⟩ := exists_normalizer_map_chain hsurj I Echain
    (fun s => conjSub g⁻¹ (mem s).1.2)
    (fun s hs => Echain_mono (hs1 s hs) (hst s hs) ht5)
    (fun s hs => by
      have h1 := conjSub_mono (g := g⁻¹) (hle s hs)
      rwa [show A = conjSub g (Echain t) from hAg, conjSub_inv_conjSub] at h1)
    (fun s hs u hu hsu => Echain_mono (hs1 s hs) hsu ((hst u hu).trans ht5))
    (fun s hs u hu hsu => conjSub_mono (le_of_parInc (hF _ (hmem s hs).1 _ (hmem u hu).1)
      (by rw [(hmem s hs).2, (hmem u hu).2]; exact hsu)))
    (fun s hs => natCard_Echain s (hs1 s hs) ((hst s hs).trans ht5))
    (fun s hs => by rw [natCard_conjSub, natCard_obj, (hmem s hs).2])
  refine ⟨g * k, Shat.mul_mem hg (Kchain_le_Shat t ht1 ht5 hk), fun x hx => ?_⟩
  have hs := hmemI x hx
  rw [conjSub_mul, hkC _ hs, conjSub_conjSub_inv, huniq x hx]

theorem flag_transitive
    {F F' : Set ParGeom} (hF : IsParFlag F) (hF' : IsParFlag F')
    (ht : parType '' F = parType '' F') : ∃ g : Shat, (g • ·) '' F = F' := by
  obtain ⟨a, ha, hFa⟩ := exists_conj_std_of_flag hF
  obtain ⟨b, hb, hFb⟩ := exists_conj_std_of_flag hF'
  let g : Shat := ⟨b, hb⟩ * (⟨a, ha⟩ : Shat)⁻¹
  have hg : ∀ x ∈ F, (g • x).1.2 = conjSub b (Echain (parType x)) := by
    intro x hx
    rw [smul_obj_eq g (hFa x hx)]
    congr 1
    change b * a⁻¹ * a = b
    group
  refine ⟨g, Set.eq_of_subset_of_subset ?_ ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    show g • x ∈ F'
    obtain ⟨y, hy, hyx⟩ : ∃ y ∈ F', parType y = parType x := by
      have : parType x ∈ parType '' F' := ht ▸ ⟨x, hx, rfl⟩
      exact this
    have e : g • x = y := obj_ext (by rw [parType_smul, hyx]) (by rw [hg x hx, hFb y hy, hyx])
    rw [e]
    exact hy
  · intro y hy
    obtain ⟨x, hx, hxy⟩ : ∃ x ∈ F, parType x = parType y := by
      have : parType y ∈ parType '' F := ht.symm ▸ ⟨y, hy, rfl⟩
      exact this
    exact ⟨x, hx, obj_ext (by rw [parType_smul, hxy]) (by rw [hg x hx, hFb y hy, hxy])⟩

theorem exists_chamber_of_flag
    {F : Set ParGeom} (hF : IsParFlag F) :
    ∃ C : Set ParGeom, F ⊆ C ∧ IsParFlag C ∧ parType '' C = Set.Icc 1 5 := by
  obtain ⟨g, hg, hFg⟩ := exists_conj_std_of_flag hF
  refine ⟨stdChamber ⟨g, hg⟩, fun x hx => ?_, isParFlag_smul stdParFlag_isParFlag.1 _,
    (parType_image_smul _ _).trans stdParFlag_isParFlag.2⟩
  refine ⟨stdObj (parType x) (parType_bounds x).1 (parType_bounds x).2, rfl, ?_⟩
  refine obj_ext rfl ?_
  rw [hFg x hx]
  change conjSub g (Echain (parType x)) = _
  rfl

end CFSG.Monster.B.TwoA
