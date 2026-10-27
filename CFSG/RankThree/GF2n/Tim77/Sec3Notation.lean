module

import all CFSG.Timmesfeld.RootInvolutions.RootInvolutionSetting
public import CFSG.RankThree.GF2n.Tim77.Cor2Hyp
public import CFSG.RankThree.GF2n.Tim77.Defs

public section

namespace CFSG.RankThree.GF2n.Tim77

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.RootInvolutions Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem notation_isPGroup_two_of_le {E H : Subgroup G} (hE : IsElemAbelian 2 E) (hH : H ≤ E) :
    IsPGroup 2 H := by
  rintro ⟨w, hw⟩
  refine ⟨1, Subtype.ext ?_⟩
  simpa using hE.2 w (hH hw)

theorem notation_centralizer_le_normalizer {A : Subgroup G} :
    centralizer (A : Set G) ≤ normalizer (A : Set G) :=
  le_normalizer_of_comm fun x hx y hy => (Subgroup.mem_centralizer_iff.mp hx y hy).symm

theorem notation_exists_noncomm_conj {A : Subgroup G} (hA : IsElemAbelian 2 A) (hTI : IsTI A)
    (hnr : ¬ IsRootType 2 A) :
    ∃ h : G, normalizerIn A (conjSubgroup h A) ≠ ⊥ ∧
      ¬ ∀ a ∈ A, ∀ b ∈ conjSubgroup h A, a * b = b * a := by
  by_contra hcon
  apply hnr
  unfold IsRootType IsRootTypeIn
  refine ⟨le_top, hA, fun h _ => (hTI h).symm, fun h _ hN a ha b hb => ?_⟩
  by_contra hab
  exact hcon ⟨h, hN, fun hall => hab (hall a ha b hb)⟩

theorem notation_setup_of_noncomm {A : Subgroup G} (hA : IsElemAbelian 2 A) (hTI : IsTI A)
    {h : G} (hN : normalizerIn A (conjSubgroup h A) ≠ ⊥)
    (hnc : ¬ ∀ a ∈ A, ∀ b ∈ conjSubgroup h A, a * b = b * a) :
    Prop24Setup A (conjSubgroup h A) (normalizerIn A (conjSubgroup h A))
      (normalizerIn (conjSubgroup h A) A)
      (normalizerIn A (conjSubgroup h A) ⊔ normalizerIn (conjSubgroup h A) A) where
  elem := hA
  ti := hTI
  conj := ⟨h, rfl⟩
  hL := rfl
  hLb := rfl
  hM := rfl
  ne_bot := hN
  ne := by
    intro hL
    apply hnc
    have hC : IsElemAbelian 2 (conjSubgroup h A) := isElemAbelian_conj hA h
    have hCTI : IsTI (conjSubgroup h A) := isTI_conjSubgroup hTI h
    have hAN : A ≤ normalizer (conjSubgroup h A : Set G) := by
      intro x hx
      have hx' : x ∈ normalizerIn A (conjSubgroup h A) := by
        rw [hL]
        exact hx
      exact (Subgroup.mem_inf.mp hx').2
    have hback : conjSubgroup h⁻¹ (conjSubgroup h A) = A := by
      rw [← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]
    have hle : conjSubgroup h⁻¹ (conjSubgroup h A) ≤ normalizer (conjSubgroup h A : Set G) := by
      rw [hback]
      exact hAN
    have hel := tim77_2_3 hC hCTI hle
    rw [hback] at hel
    intro a ha b hb
    exact (congrArg Subtype.val
      (hel.1.is_comm.comm ⟨b, Subgroup.mem_sup_left hb⟩ ⟨a, Subgroup.mem_sup_right ha⟩)).symm

theorem notation_exists_sylow_le {A T : Subgroup G} (hT : IsPGroup 2 T)
    (hTN : T ≤ normalizer (A : Set G)) :
    ∃ Q : Sylow 2 ↥(normalizer (A : Set G)),
      T ≤ (Q : Subgroup ↥(normalizer (A : Set G))).map (normalizer (A : Set G)).subtype := by
  have hT' : IsPGroup 2 (T.subgroupOf (normalizer (A : Set G))) := hT.comap_subtype
  obtain ⟨Q, hQ⟩ := hT'.exists_le_sylow
  refine ⟨Q, fun x hx => ?_⟩
  have hy : (⟨x, hTN hx⟩ : ↥(normalizer (A : Set G))) ∈
      T.subgroupOf (normalizer (A : Set G)) :=
    Subgroup.mem_subgroupOf.mpr hx
  exact Subgroup.mem_map.mpr ⟨⟨x, hTN hx⟩, hQ hy, rfl⟩

theorem notation_sylow_map_max {A : Subgroup G} (Q : Sylow 2 ↥(normalizer (A : Set G))) :
    IsPGroup 2 ((Q : Subgroup ↥(normalizer (A : Set G))).map (normalizer (A : Set G)).subtype) ∧
      (Q : Subgroup ↥(normalizer (A : Set G))).map (normalizer (A : Set G)).subtype ≤
        normalizer (A : Set G) ∧
      ∀ T : Subgroup G, IsPGroup 2 T → T ≤ normalizer (A : Set G) →
        (Q : Subgroup ↥(normalizer (A : Set G))).map (normalizer (A : Set G)).subtype ≤ T →
          T = (Q : Subgroup ↥(normalizer (A : Set G))).map (normalizer (A : Set G)).subtype := by
  refine ⟨Q.isPGroup'.map _, Subgroup.map_subtype_le _, fun T hT hTN hle => ?_⟩
  have hT' : IsPGroup 2 (T.subgroupOf (normalizer (A : Set G))) := hT.comap_subtype
  have hQle : (Q : Subgroup ↥(normalizer (A : Set G))) ≤
      T.subgroupOf (normalizer (A : Set G)) := by
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr (hle (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩))
  have heq := Q.is_maximal' hT' hQle
  calc T = (T.subgroupOf (normalizer (A : Set G))).map (normalizer (A : Set G)).subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hTN).symm
    _ = _ := by rw [heq]

theorem notation_exists_conj_le_sylow {A B₀ : Subgroup G} (hB : IsPGroup 2 B₀)
    (hBN : B₀ ≤ normalizer (A : Set G)) (Q₀ : Sylow 2 ↥(normalizer (A : Set G))) :
    ∃ n ∈ normalizer (A : Set G), ∀ b ∈ B₀, n * b * n⁻¹ ∈
      (Q₀ : Subgroup ↥(normalizer (A : Set G))).map (normalizer (A : Set G)).subtype := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (Sylow 2 ↥(normalizer (A : Set G))) := inferInstance
  have hB' : IsPGroup 2 (B₀.subgroupOf (normalizer (A : Set G))) := hB.comap_subtype
  obtain ⟨Q₁, hQ₁⟩ := hB'.exists_le_sylow
  obtain ⟨n, hn⟩ := MulAction.exists_smul_eq (↥(normalizer (A : Set G))) Q₁ Q₀
  have hsub : MulAut.conj n • (Q₁ : Subgroup ↥(normalizer (A : Set G))) =
      (Q₀ : Subgroup ↥(normalizer (A : Set G))) := by
    rw [← hn]
    rfl
  refine ⟨(n : G), n.2, fun b hb => ?_⟩
  have hbY : (⟨b, hBN hb⟩ : ↥(normalizer (A : Set G))) ∈
      B₀.subgroupOf (normalizer (A : Set G)) :=
    Subgroup.mem_subgroupOf.mpr hb
  have hb1 : (⟨b, hBN hb⟩ : ↥(normalizer (A : Set G))) ∈
      (Q₁ : Subgroup ↥(normalizer (A : Set G))) := hQ₁ hbY
  have hb2 := Subgroup.smul_mem_pointwise_smul _ (MulAut.conj n) _ hb1
  rw [hsub] at hb2
  exact Subgroup.mem_map.mpr
    ⟨MulAut.conj n • (⟨b, hBN hb⟩ : ↥(normalizer (A : Set G))), hb2, rfl⟩

theorem notation_exists_sylow_choice {A Abar : Subgroup G} (hA : IsElemAbelian 2 A)
    (hAbar : IsElemAbelian 2 Abar) :
    ∃ Q : Sylow 2 ↥(normalizer (A : Set G)),
      A ⊔ normalizerIn Abar A ≤
        (Q : Subgroup ↥(normalizer (A : Set G))).map (normalizer (A : Set G)).subtype := by
  have hHK : normalizerIn Abar A ≤ normalizer (A : Set G) :=
    fun x hx => (Subgroup.mem_inf.mp hx).2
  have hT : IsPGroup 2 (A ⊔ normalizerIn Abar A : Subgroup G) :=
    IsPGroup.to_sup_of_normal_left' (notation_isPGroup_two_of_le hA le_rfl)
      (notation_isPGroup_two_of_le hAbar (fun x hx => (Subgroup.mem_inf.mp hx).1)) hHK
  have hTN : A ⊔ normalizerIn Abar A ≤ normalizer (A : Set G) :=
    sup_le Subgroup.le_normalizer hHK
  exact notation_exists_sylow_le hT hTN

theorem notation_exists_B {A : Subgroup G} (hA : IsElemAbelian 2 A)
    (hnwc : ¬ ∀ g : G, conjSubgroup g A ≤ centralizer (A : Set G) → conjSubgroup g A = A)
    (Q₀ : Sylow 2 ↥(normalizer (A : Set G))) :
    ∃ B : Subgroup G, (∃ g : G, B = conjSubgroup g A) ∧ B ≠ A ∧
      B ≤ (Q₀ : Subgroup ↥(normalizer (A : Set G))).map (normalizer (A : Set G)).subtype ⊓
        centralizer (A : Set G) := by
  obtain ⟨g₁, hg₁C, hg₁ne⟩ : ∃ g : G, conjSubgroup g A ≤ centralizer (A : Set G) ∧
      conjSubgroup g A ≠ A := by
    by_contra hcon
    apply hnwc
    intro g hg
    by_contra hne
    exact hcon ⟨g, hg, hne⟩
  have hB₀N : conjSubgroup g₁ A ≤ normalizer (A : Set G) :=
    hg₁C.trans notation_centralizer_le_normalizer
  have hB₀2 : IsPGroup 2 (conjSubgroup g₁ A) :=
    notation_isPGroup_two_of_le (isElemAbelian_conj hA g₁) le_rfl
  obtain ⟨n, hnN, hn⟩ := notation_exists_conj_le_sylow hB₀2 hB₀N Q₀
  refine ⟨conjSubgroup (n * g₁) A, ⟨n * g₁, rfl⟩, ?_, ?_⟩
  · intro hBA
    apply hg₁ne
    have h1 : conjSubgroup n (conjSubgroup g₁ A) = A := by
      rw [← conjSubgroup_mul]
      exact hBA
    have h2 : conjSubgroup n⁻¹ A = A := conjSubgroup_eq_self_iff.mpr (inv_mem hnN)
    calc conjSubgroup g₁ A = conjSubgroup n⁻¹ (conjSubgroup n (conjSubgroup g₁ A)) := by
          rw [← conjSubgroup_mul n⁻¹ n, inv_mul_cancel, conjSubgroup_one]
      _ = conjSubgroup n⁻¹ A := by rw [h1]
      _ = A := h2
  · intro x hx
    have hx' : x ∈ conjSubgroup n (conjSubgroup g₁ A) := by
      rw [← conjSubgroup_mul]
      exact hx
    have hb : n⁻¹ * x * n ∈ conjSubgroup g₁ A := mem_conjSubgroup.mp hx'
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have hS := hn _ hb
      have hxe : n * (n⁻¹ * x * n) * n⁻¹ = x := by group
      rw [hxe] at hS
      exact hS
    · have hC := Subgroup.mem_centralizer_iff.mp (hg₁C hb)
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have ha' : n⁻¹ * a * n ∈ A := by
        have h := (Subgroup.mem_normalizer_iff.mp (inv_mem hnN) a).mp ha
        rwa [inv_inv] at h
      have key := hC (n⁻¹ * a * n) ha'
      calc a * x = n * ((n⁻¹ * a * n) * (n⁻¹ * x * n)) * n⁻¹ := by group
        _ = n * ((n⁻¹ * x * n) * (n⁻¹ * a * n)) * n⁻¹ := by rw [key]
        _ = x * a := by group

theorem tim77ExistsNotation_holds : Tim77ExistsNotationStatement := by
  intro G _ _ A hyp hnr hnwc
  obtain ⟨h₁, hN₁, hnc₁⟩ := notation_exists_noncomm_conj hyp.elemAbelian hyp.ti hnr
  have hS₁ := notation_setup_of_noncomm hyp.elemAbelian hyp.ti hN₁ hnc₁
  obtain ⟨g₀, hg₀, hmax⟩ := Set.exists_max_image
    {g : G | normalizerIn (conjSubgroup g A) A ≠ ⊥ ∧
      normalizerIn (conjSubgroup g A) A ≠ conjSubgroup g A}
    (fun g => Nat.card (normalizerIn (conjSubgroup g A) A)) (Set.toFinite _)
    ⟨h₁, hS₁.Lb_ne_bot, hS₁.Lb_ne⟩
  have hAbar : IsElemAbelian 2 (conjSubgroup g₀ A) := isElemAbelian_conj hyp.elemAbelian g₀
  obtain ⟨Q₀, hQ₀⟩ := notation_exists_sylow_choice hyp.elemAbelian hAbar
  obtain ⟨B, hBconj, hBne, hBle⟩ := notation_exists_B hyp.elemAbelian hnwc Q₀
  exact ⟨conjSubgroup g₀ A,
    (Q₀ : Subgroup ↥(normalizer (A : Set G))).map (normalizer (A : Set G)).subtype, B,
    { choice := ⟨⟨g₀, rfl⟩, hg₀, fun g hg => hmax g hg⟩
      sylow := notation_sylow_map_max Q₀
      contains := hQ₀
      conj := hBconj
      ne := hBne
      le := hBle }⟩

end CFSG.RankThree.GF2n.Tim77
