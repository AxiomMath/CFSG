module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.RankOneSz
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.RankOneGen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.RankOneFamTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.RankOneFamOdd
public import CFSG.LocalAnalysis.UniquenessCase.UC1K46Cover
import CFSG.Adapters.LieModelSimple
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFactNineteenTwentySix

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsSpor)
open scoped MatrixGroups

private theorem r1asm_pRank_top_eq_one {Y : Type} [Group Y] [Finite Y] {K : Subgroup Y} {e : Y}
    (heK : e ∈ K) (he : orderOf e = 3) (hrank : CFSG.Open.pRank 3 K ≤ 1) :
    CFSG.Open.pRank 3 (⊤ : Subgroup ↥K) = 1 := by
  have hE : CFSG.Open.IsElemAbelian 3 (zpowers e) :=
    ⟨inferInstance, fun x hx => orderOf_dvd_iff_pow_eq_one.1 (he ▸ orderOf_dvd_of_mem_zpowers hx)⟩
  have h1 : 1 ≤ CFSG.Open.pRank 3 K := CFSG.SectionRank.le_pRank (by norm_num)
    (zpowers_le.2 heK) hE (by rw [Nat.card_zpowers, he, pow_one])
  rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
  omega

private theorem r1asm_center_eq_bot {G : Type} [Group G] (hq : CFSG.Open.IsQuasisimple G)
    (hs : IsSimpleGroup G) : center G = ⊥ := by
  refine (hs.eq_bot_or_eq_top_of_normal (center G)).resolve_right fun h => ?_
  have := hq.2
  obtain ⟨x, hx⟩ := exists_ne (1 : G ⧸ center G)
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  exact hx ((QuotientGroup.eq_one_iff g).2 (h ▸ mem_top g))

private theorem r1asm_isSimpleGroup_of_isSpor {G : Type} [Group G]
    (h : IsSpor G .J1) : IsSimpleGroup G := by
  obtain ⟨φ⟩ := h
  have := CFSG.Walter.J1Props.isSimpleGroup_walterJ1
  exact (φ.trans CFSG.Walter.walterJ1EquivNative.symm).isSimpleGroup

private theorem r1asm_false_of_sl2 {G : Type} [Group G] (hZ : Odd (Nat.card (center G)))
    (h : ∃ (F : Type) (_ : Field F) (_ : Finite F), Odd (Nat.card F) ∧ Nonempty (G ≃* SL(2, F))) :
    False := by
  obtain ⟨F, _, _, hF, ⟨φ⟩⟩ := h
  rw [Nat.card_congr (centerCongr φ).toEquiv, CFSG.ClassicalInvolution.sl2_natCard_center hF] at hZ
  exact Nat.not_odd_iff_even.2 even_two hZ

section Main


theorem k_19_26_rankOne_of_families
    (hL2 : ∀ (K : Type) [Group K] [Finite K] (f : ℕ), LieModel K .PSL 2 2 f →
      (∀ x : K, orderOf x = 3 → Odd (Nat.card (centralizer ({x} : Set K)))) ∧
      ∀ W : Subgroup (MulAut K), IsPGroup 2 W → W ⊓ (MulAut.conj : K →* MulAut K).range = ⊥ →
        IsCyclic W)
    (hL3 : ∀ (K : Type) [Group K] [Finite K] (f : ℕ), 2 ^ f % 3 = 2 → LieModel K .PSL 3 2 f →
      (∀ x : K, orderOf x = 3 → Odd (Nat.card (centralizer ({x} : Set K)))) ∧
      ∀ W : Subgroup (MulAut K), IsPGroup 2 W → W ⊓ (MulAut.conj : K →* MulAut K).range = ⊥ →
        IsCyclic W)
    (hU3 : ∀ (K : Type) [Group K] [Finite K] (f : ℕ), 2 ^ f % 3 = 1 → LieModel K .PSU 3 2 f →
      (∀ x : K, orderOf x = 3 → Odd (Nat.card (centralizer ({x} : Set K)))) ∧
      ∀ W : Subgroup (MulAut K), IsPGroup 2 W → W ⊓ (MulAut.conj : K →* MulAut K).range = ⊥ →
        IsCyclic W)
    (hJ1 : ∀ (K : Type) [Group K] [Finite K], IsSpor K .J1 →
      (∀ α : MulAut K, α ∈ (MulAut.conj : K →* MulAut K).range) ∧
      ∀ x : K, orderOf x = 3 → ∀ P : Subgroup K, P ≤ centralizer ({x} : Set K) → IsPGroup 2 P →
        IsCyclic P)
    (hOdd : ∀ {Y : Type} [Group Y] [Finite Y] (K V : Subgroup Y) (e : Y), IsSimpleGroup ↥K →
      ((∃ p f : ℕ, p ≠ 2 ∧ LieModel ↥K .PSL 2 p f) ∨
        (∃ p f : ℕ, p ≠ 2 ∧ p ^ f % 3 = 2 ∧ LieModel ↥K .PSL 3 p f) ∨
        (∃ p f : ℕ, p ≠ 2 ∧ p ^ f % 3 = 1 ∧ LieModel ↥K .PSU 3 p f)) →
      CFSG.Open.pRank 3 K ≤ 1 → CFSG.Open.IsElemAbelian 2 V → 4 ≤ Nat.card V →
      V ≤ normalizer (K : Set Y) → V ⊓ centralizer (K : Set Y) = ⊥ →
      CFSG.CGT.Timmesfeld75.IsTI V → orderOf e = 3 → e ∈ K → V ≤ centralizer ({e} : Set Y) →
      False) :
    K_19_26_rankOne := by
  intro Y _ _ K V e hKq hKK hZ hrank hV2 hV4 hVN hVf hVTI _ he heN hVe h3K
  have hSz := k_19_26_rankOne_of_not_three_dvd K V e hKq hKK hZ hV2 hVN he heN
  rcases h3K with heK | h3
  swap
  · exact hSz h3
  exfalso
  have hord : orderOf (⟨e, heK⟩ : ↥K) = 3 := by rwa [orderOf_mk]
  have hchar2 : IsSimpleGroup ↥K →
      ((∀ x : ↥K, orderOf x = 3 → Odd (Nat.card (centralizer ({x} : Set ↥K)))) ∧
        ∀ W : Subgroup (MulAut ↥K), IsPGroup 2 W →
          W ⊓ (MulAut.conj : ↥K →* MulAut ↥K).range = ⊥ → IsCyclic W) →
      Nat.card V ≤ 2 := fun hs h =>
    card_le_two_of_odd_centralizer (r1asm_center_eq_bot hKq hs) heK hV2 hVN hVf hVe (h.1 _ hord) h.2
  have hodd := fun hs : IsSimpleGroup ↥K => fun hsh =>
    hOdd K V e hs hsh hrank hV2 hV4 hVN hVf hVTI he heK hVe
  have hle : Nat.card V ≤ 2 := by
    rcases UCK.k46Quasisimple_holds ↥K hKK hKq (r1asm_pRank_top_eq_one heK he hrank) with
      ⟨p, f, hL⟩ | ⟨p, f, hq, hL⟩ | ⟨p, f, hq, hL⟩ | hJ | hSL
    · have hs := LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL
      rcases eq_or_ne p 2 with rfl | hp
      · exact hchar2 hs (hL2 ↥K f hL)
      · exact (hodd hs (Or.inl ⟨p, f, hp, hL⟩)).elim
    · have hs := LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL
      rcases eq_or_ne p 2 with rfl | hp
      · exact hchar2 hs (hL3 ↥K f hq hL)
      · exact (hodd hs (Or.inr (Or.inl ⟨p, f, hp, hq, hL⟩))).elim
    · have hs := LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL
      rcases eq_or_ne p 2 with rfl | hp
      · exact hchar2 hs (hU3 ↥K f hq hL)
      · exact (hodd hs (Or.inr (Or.inr ⟨p, f, hp, hq, hL⟩))).elim
    · obtain ⟨hinn, hcyc⟩ := hJ1 ↥K hJ
      exact card_le_two_of_isCyclic_sylow_centralizer
        (r1asm_center_eq_bot hKq (r1asm_isSimpleGroup_of_isSpor hJ)) heK hV2 hVN hVf hVe
        (fun α _ => hinn α) (hcyc _ hord)
    · exact (r1asm_false_of_sl2 hZ hSL).elim
  omega

end Main

section Final


theorem k_19_26_rankOne_holds : K_19_26_rankOne :=
  k_19_26_rankOne_of_families
    (fun _ _ _ _ hK => ⟨fun _ hx => odd_card_centralizer_of_psl_two_two hK hx,
      fun W hW hWi => isCyclic_of_inf_inner_eq_bot_of_psl_two_two hK W hW hWi⟩)
    (fun _ _ _ _ hq hK => ⟨fun _ hx => odd_card_centralizer_of_psl_three_two hq hK hx,
      fun W hW hWi => isCyclic_of_inf_inner_eq_bot_of_psl_three_two hq hK W hW hWi⟩)
    (fun _ _ _ _ hq hK => ⟨fun _ hx => odd_card_centralizer_of_psu_three_two hq hK hx,
      fun W hW hWi => isCyclic_of_inf_inner_eq_bot_of_psu_three_two hq hK W hW hWi⟩)
    (fun _ _ _ hK => ⟨mem_range_conj_of_isSpor_J1 hK,
      fun _ hx P hP h2 => isCyclic_of_le_centralizer_of_isSpor_J1 hK hx P hP h2⟩)
    (fun K V e hKs hshape h3 hV2 hV4 hVN hVf hTI he heK hVe =>
      false_of_odd_char_of_rankOne K V e hKs hshape h3 hV2 hV4 hVN hVf hTI he heK hVe)

end Final

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
