module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.OuterRSplitBar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Sp4G2OuterRSplit
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.U4OuterRSplit
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.OuterRSplitCube
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.RankTwoOuterRank
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214c
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1511A
public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Cong
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenTen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22 (calC conjClosure conjSetOf Opp Bar2 barImage)

variable {G : Type} [Group G] [Finite G]

theorem k_RankTwoOuterRank_of
    (hZfam : ∀ (X : Type) [Group X] [Finite X] (n : ℕ),
      (CFSG.Blueprint.LieModel X .PSU 4 2 n ∨ CFSG.Blueprint.LieModel X .PSp 2 2 n ∨
        CFSG.Blueprint.LieModel X .G2 0 2 n) → CFSG.Open.IsQuasisimple X → Subgroup.center X = ⊥)
    (hfam : ∀ (X : Type) [Group X] [Finite X] (n r : ℕ),
      (CFSG.Blueprint.LieModel X .PSU 4 2 n ∨ CFSG.Blueprint.LieModel X .PSp 2 2 n ∨
        CFSG.Blueprint.LieModel X .G2 0 2 n) →
        r.Prime → 5 < r → r ∣ 2 ^ n - 1 → OuterRSplit X r 2) :
    S17.K_RankTwoOuterRank := by
  intro H _ _ M L n r hL hshape hr hr5 hrdvd hne
  have hr2 : r ≠ 2 := by omega
  have hsplit := hfam (Bar2 L) n r hshape hr hr5 hrdvd
  have hZ : Subgroup.center (Bar2 L) = ⊥ := hZfam (Bar2 L) n hshape hL.2.2
  have hs : IsSimpleGroup (Bar2 L) := by
    have : IsSimpleGroup (Bar2 L ⧸ Subgroup.center (Bar2 L)) := hL.2.2.2
    exact
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.isSimpleGroup
  obtain ⟨E, -, hEcard⟩ := hsplit.exists_elemAbelian
  have hdvd : r ∣ Nat.card (Bar2 L) := by
    have h1 := Subgroup.card_subgroup_dvd_card E
    rw [hEcard] at h1
    exact (dvd_pow_self r two_ne_zero).trans h1
  have hle : L ≤ Opp r M :=
    (TwelveTwentyThree.le_conjClosure M L).trans (conjClosure_le_opp hL hs hr hr2 hdvd)
  obtain ⟨x, hxM, hxL, k, hk⟩ := CFSG.LocalAnalysis.RankThreeUC.S15.exists_pElement_not_mem r M L
    fun h => hne (le_antisymm hle h)
  obtain ⟨e⟩ := s13_bar_equiv hL
  have hZ' := center_barImage_eq_bot hL hZ
  have hsplit' : OuterRSplit (barImage M L) r 2 := hsplit.of_mulEquiv e
  by_cases hxN : x ∈ Subgroup.normalizer (L : Set H)
  ·
    obtain ⟨j, hj1, hj2⟩ := exists_pow_pow_not_mem hxL (k := k)
      (by rw [← hk, pow_orderOf_eq_one]; exact L.one_mem)
    have hij : orderOf (x ^ r ^ j) ∣ r ^ k := hk ▸ orderOf_pow_dvd _
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hr).1 hij
    have hyM : x ^ r ^ j ∈ M := M.pow_mem hxM _
    have hyN : x ^ r ^ j ∈ Subgroup.normalizer (L : Set H) := Subgroup.pow_mem _ hxN _
    have h1 := UC22.uc22ine229_mk_mem_normalizer (x := ⟨x ^ r ^ j, hyM⟩) hyN
    have h2 := mk_not_mem_barImage (UC22.uc22p22u_pCore_normalizes_calC hL) hr2 hr hyM hi hj1
    have h3 : (QuotientGroup.mk' (CFSG.pCore 2 ↥M) (⟨x ^ r ^ j, hyM⟩ : ↥M)) ^ r ∈
        barImage M L := by
      rw [← map_pow]
      have : ((⟨x ^ r ^ j, hyM⟩ : ↥M) ^ r) = ⟨(x ^ r ^ j) ^ r, M.pow_mem hyM r⟩ := rfl
      rw [this]
      exact UC22.uc22p21c_mem_barImage.2 ⟨⟨(x ^ r ^ j) ^ r, M.pow_mem hyM r⟩, hj2, rfl⟩
    obtain ⟨E₃, hE₃, hE₃card⟩ := exists_elemAbelian_cube_of_normalizer hr hZ' hsplit' h1
      (exists_orderOf_mk_eq hyM hr hi) h2 h3
    exact le_pRank_of_bar2 hr hr2 hE₃ hE₃card
  ·
    set L₂ : Subgroup H := L.map (MulAut.conj x).toMonoidHom with hL₂def
    have hL₂ : L₂ ∈ calC M := UC22.uc22p2214_calC_of_mem_conjSetOf hL ⟨x, hxM, rfl⟩
    have hne₂ : L ≠ L₂ := by
      intro h
      apply hxN
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      exact h.symm
    obtain ⟨e₂⟩ := UC22.uc22p20d_bar2_conj x L
    obtain ⟨e₂'⟩ := s13_bar_equiv hL₂
    have hsplit₂ : OuterRSplit (barImage M L₂) r 2 := (hsplit.of_mulEquiv e₂).of_mulEquiv e₂'
    obtain ⟨E₁, hE₁, hE₁card⟩ := hsplit'.exists_elemAbelian
    obtain ⟨E₂, hE₂, hE₂card⟩ := hsplit₂.exists_elemAbelian
    have hc := UC22.uc22p22l_barImage_commute hL hL₂ hne₂
    set F₁ : Subgroup (Bar2 M) := E₁.map (barImage M L).subtype with hF₁
    set F₂ : Subgroup (Bar2 M) := E₂.map (barImage M L₂).subtype with hF₂
    have hF₁X : F₁ ≤ barImage M L := by rintro _ ⟨a, -, rfl⟩; exact a.2
    have hF₂X : F₂ ≤ barImage M L₂ := by rintro _ ⟨a, -, rfl⟩; exact a.2
    have hFc : ∀ a ∈ F₁, ∀ b ∈ F₂, a * b = b * a := fun a ha b hb => hc a (hF₁X ha) b (hF₂X hb)
    have hF : IsElemAbelian r (F₁ ⊔ F₂) :=
      (hE₁.map (barImage M L).subtype).sup_of_commute (hE₂.map (barImage M L₂).subtype) hFc
    have hFinf : F₁ ⊓ F₂ = ⊥ := by
      rw [eq_bot_iff, ← CFSG.Quasithin.S143.InspW2.inf_eq_bot_of_commute hZ' hc]
      exact inf_le_inf hF₁X hF₂X
    have hFcard : Nat.card (F₁ ⊔ F₂ : Subgroup (Bar2 M)) = r ^ 4 := by
      rw [CFSG.card_sup_eq_mul_of_commute F₁ F₂ (fun a ha b hb => hFc a ha b hb) hFinf,
        hF₁, hF₂, Subgroup.card_map_of_injective (barImage M L).subtype_injective,
        Subgroup.card_map_of_injective (barImage M L₂).subtype_injective, hE₁card, hE₂card]
      ring
    have h4 := le_pRank_of_bar2 hr hr2 hF hFcard
    omega

section Holds


theorem k_RankTwoOuterRank_holds : S17.K_RankTwoOuterRank :=
  k_RankTwoOuterRank_of
    (fun X _ _ n h hq => by
      rcases h with h | h | h
      · have := CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h
        exact UC22.uc22p21k_center_eq_bot hq
      · have := CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h
        exact UC22.uc22p21k_center_eq_bot hq
      · exact S17.center_eq_bot_of_lieModel_g2 h)
    (fun X _ _ n r h hr hr5 hrn => by
      rcases h with h | h | h
      · exact outerRSplit_two_of_u4 h hr hr5 hrn
      · exact outerRSplit_two_of_sp4 h hr (by omega) hrn
      · exact outerRSplit_two_of_g2 h hr (by omega) hrn)

end Holds

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
