module

public import CFSG.Quasithin.Background.RonanE114Pair
public import CFSG.Quasithin.Background.RonanE114A7
public import CFSG.Quasithin.EmptyFaithful.S151S9TM24Inputs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatM24
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatIncl
import CFSG.Blueprint.NativeSporadic
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporJ4Quot
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.Open.SplitBNPair
public import CFSG.Quasithin.Background.B1More13A
public import CFSG.Quasithin.Background.B1More13Defs
public import CFSG.Quasithin.Background.B1MoreEleven
public import CFSG.Quasithin.Background.B5CompA
public import CFSG.Quasithin.Background.B5CompB
public import CFSG.Quasithin.Background.D2
public import CFSG.Quasithin.Background.D2Dihedral
public import CFSG.Quasithin.Background.E1ElevenIso
public import CFSG.Quasithin.Background.E3OffenderB
public import CFSG.Quasithin.EmptyFaithful.E22NParam
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
public import CFSG.Quasithin.EmptyFaithful.S152N11
public import CFSG.Quasithin.H13.A5S1326
public import CFSG.Quasithin.H13.A5Top
public import CFSG.Quasithin.Vol2.Ch10StatementsE
public import CFSG.Quasithin.Vol2.Ch10StatementsInputs
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS2
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS3
public import CFSG.Quasithin.Vol2.Ch11SecBNPCaseS
public import CFSG.Quasithin.Vol2.Ch11SecBTCIso
public import CFSG.Quasithin.Vol2.Ch11SecU1Crit
public import CFSG.Quasithin.Vol2.Ch11SecU1Defs
public import CFSG.Quasithin.Vol2.Ch11StatementsE
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS2
public import CFSG.RankThree.GroupTheory.SteinbergCEMutualSupplementResidual
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import CFSG.StronglyEmbedded.ParityCriterion

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.Ch1.SporLat.M24
open CFSG.Open CFSG.Quasithin.E2P.SporB CFSG.Quasithin.S151S9T CFSG.Quasithin.RonanE114

namespace RonanE114

theorem map_le_iff_of_fix {Γ : Type} [Group Γ] {α : MulAut Γ} {A B : Subgroup Γ}
    (hB : B.map α.toMonoidHom = B) : A.map α.toMonoidHom ≤ B ↔ A ≤ B := by
  conv_lhs => rw [← hB]
  exact Subgroup.map_le_map_iff_of_injective α.injective

section M24

@[expose] def m24Idx : Array ℕ := #[1, 315, 63, 135, 21, 9, 21, 3, 3, 3, 9, 3, 9]


theorem m24_hL : m24Ctx.D.Om.map (fun o => o.lbl.size) = m24Idx := m24_Om_map

theorem m24_all : ∀ Z : Subgroup ↥CFSG.Blueprint.NativeSporadic.M24, m24Ctx.S ≤ Z →
    ∃ j ≤ m24Idx.size, Z = memberOrTop m24Idx.size m24Ctx.Y j := lat_all m24Ctx m24_hL

theorem m24_card_Y : ∀ j < m24Idx.size, Nat.card (m24Ctx.Y j) = m24Idx[j]! * 2 ^ 10 :=
  lat_card m24Ctx m24_hL

theorem m24_card_top : Nat.card ↥CFSG.Blueprint.NativeSporadic.M24 = 239085 * 2 ^ 10 := by
  rw [m24_card]
  ring

theorem m24_list_card (j : ℕ) :
    Nat.card (memberOrTop m24Idx.size m24Ctx.Y j) = latSz m24Idx 239085 j * 2 ^ 10 :=
  list_card m24_card_Y m24_card_top j

theorem m24_idx9 {Z : Subgroup ↥CFSG.Blueprint.NativeSporadic.M24} (hZ : m24Ctx.S ≤ Z)
    (hc : Nat.card Z = 9 * 2 ^ 10) :
    Z = m24Ctx.Y 5 ∨ Z = m24Ctx.Y 10 ∨ Z = m24Ctx.Y 12 := by
  obtain ⟨j, hj, rfl⟩ := m24_all Z hZ
  rw [m24_list_card] at hc
  have h9 : latSz m24Idx 239085 j = 9 := Nat.eq_of_mul_eq_mul_right (by positivity) hc
  have hcl : ∀ j < m24Idx.size + 1, latSz m24Idx 239085 j = 9 → j = 5 ∨ j = 10 ∨ j = 12 := by
    decide
  rcases hcl j (Nat.lt_succ_of_le hj) h9 with rfl | rfl | rfl
  · exact Or.inl (list_member (by decide))
  · exact Or.inr (Or.inl (list_member (by decide)))
  · exact Or.inr (Or.inr (list_member (by decide)))

theorem hasSolvInvPair_M24 : HasSolvInvPair ↥CFSG.Blueprint.NativeSporadic.M24 := by
  have hsz : m24Idx.size = 13 := rfl
  have hle : ∀ {j jj : ℕ}, j < 13 → jj < 13 →
      (m24Ctx.Y j ≤ m24Ctx.Y jj ↔ jj ∈ m24Incl[j]!) := fun {j jj} hj hjj => m24_Y_le_iff hj hjj
  have hfix : ∀ a, (∀ j < m24Idx.size + 1, latSz m24Idx 239085 j = latSz m24Idx 239085 a →
      j = a) → a < 13 → ∀ α : MulAut ↥CFSG.Blueprint.NativeSporadic.M24,
      m24Ctx.S.map α.toMonoidHom = m24Ctx.S →
      (m24Ctx.Y a).map α.toMonoidHom = m24Ctx.Y a := by
    intro a hua ha α hα
    refine map_eq_of_unique_card (m24Ctx.S_le_Y a) (fun Z hZ hZc => ?_) α hα
    have hmem : memberOrTop m24Idx.size m24Ctx.Y a = m24Ctx.Y a := list_member (by rw [hsz]; exact ha)
    rw [← hmem]
    exact list_unique m24_all m24_card_Y m24_card_top hua Z hZ (by rw [hmem]; exact hZc)
  have hc9 : ∀ j, j = 5 ∨ j = 10 ∨ j = 12 → Nat.card (m24Ctx.Y j) = 9 * 2 ^ 10 := by
    intro j hj
    have hj13 : j < m24Idx.size := by rw [hsz]; omega
    rw [m24_card_Y j hj13]
    rcases hj with rfl | rfl | rfl <;> rfl
  have hsolv : ∀ j, (j = 5 ∨ j = 10 ∨ j = 12) → Group.IsSolvable ↥(m24Ctx.Y j) := by
    intro j hj
    exact CFSG.QuasithinUnique.Vol2Native.A312L.isSolvable_of_card_two_three (a := 10) (b := 2)
      (by rw [hc9 j hj]; norm_num)
  refine ⟨m24Ctx.S, m24Ctx.Y 5, m24Ctx.Y 12, m24_S_sylow, m24Ctx.S_le_Y 5, m24Ctx.S_le_Y 12,
    hsolv 5 (Or.inl rfl), hsolv 12 (Or.inr (Or.inr rfl)), ?_, ?_⟩
  ·
    obtain ⟨j, hj, hjZ⟩ := m24_all (m24Ctx.Y 5 ⊔ m24Ctx.Y 12)
      (le_sup_of_le_left (m24Ctx.S_le_Y 5))
    by_cases hjL : j < m24Idx.size
    · exfalso
      have h13 : j < 13 := by rw [← hsz]; exact hjL
      rw [list_member hjL] at hjZ
      have h5 := (hle (by norm_num) h13).mp (le_sup_left.trans hjZ.le)
      have h12 := (hle (by norm_num) h13).mp (le_sup_right.trans hjZ.le)
      have hno : ∀ j < 13, j ∈ m24Incl[5]! → j ∈ m24Incl[12]! → False := by decide
      exact hno j h13 h5 h12
    · rw [hjZ]
      unfold memberOrTop
      rw [if_neg hjL]
  ·
    intro α hα
    have hY1 := hfix 1 (by decide) (by norm_num) α hα
    have hY2 := hfix 2 (by decide) (by norm_num) α hα
    have hY3 := hfix 3 (by decide) (by norm_num) α hα
    have hSmap : ∀ j, m24Ctx.S ≤ (m24Ctx.Y j).map α.toMonoidHom := fun j => by
      rw [← hα]
      exact Subgroup.map_mono (m24Ctx.S_le_Y j)
    have hcmap : ∀ j, Nat.card ((m24Ctx.Y j).map α.toMonoidHom) = Nat.card (m24Ctx.Y j) :=
      fun j => Subgroup.card_map_of_injective α.injective
    constructor
    ·
      rcases m24_idx9 (hSmap 5) ((hcmap 5).trans (hc9 5 (Or.inl rfl))) with h5 | h10 | h12
      · exact h5
      · exfalso
        have h51 : m24Ctx.Y 5 ≤ m24Ctx.Y 1 := (hle (by norm_num) (by norm_num)).mpr (by decide)
        have hm := (map_le_iff_of_fix hY1).mpr h51
        rw [h10] at hm
        have := (hle (by norm_num) (by norm_num)).mp hm
        revert this
        decide
      · exfalso
        have h51 : m24Ctx.Y 5 ≤ m24Ctx.Y 1 := (hle (by norm_num) (by norm_num)).mpr (by decide)
        have hm := (map_le_iff_of_fix hY1).mpr h51
        rw [h12] at hm
        have := (hle (by norm_num) (by norm_num)).mp hm
        revert this
        decide
    ·
      rcases m24_idx9 (hSmap 12) ((hcmap 12).trans (hc9 12 (Or.inr (Or.inr rfl)))) with
        h5 | h10 | h12
      · exfalso
        have h122 : m24Ctx.Y 12 ≤ m24Ctx.Y 2 := (hle (by norm_num) (by norm_num)).mpr (by decide)
        have hm := (map_le_iff_of_fix hY2).mpr h122
        rw [h5] at hm
        have := (hle (by norm_num) (by norm_num)).mp hm
        revert this
        decide
      · exfalso
        have h103 : m24Ctx.Y 10 ≤ m24Ctx.Y 3 := (hle (by norm_num) (by norm_num)).mpr (by decide)
        have hm : (m24Ctx.Y 12).map α.toMonoidHom ≤ m24Ctx.Y 3 := by
          rw [h10]
          exact h103
        have := (hle (by norm_num) (by norm_num)).mp ((map_le_iff_of_fix hY3).mp hm)
        revert this
        decide
      · exact h12

theorem nParam_eq_one_of_isM24 {G : Type} [Group G] [Finite G] {T : Subgroup G}
    (hM : IsSporadic .M24 (ASInputs.FStar G)) (hT : quasithinIsSylowTwo T)
    (hFT : CFSG.generalizedFitting G ⊔ T = ⊤) : E1.nParam (⊤ : Subgroup G) = 1 := by
  have hTs : IsSylowTwoOf T ⊤ := ⟨le_top, hT.1, by
    show ¬ 2 ∣ T.relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    exact hT.2⟩
  have hLn : (CFSG.generalizedFitting G).Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := G)).2
  obtain ⟨e₀⟩ := hM
  refine le_antisymm (nParam_le_one_of_hasSolvInvPair hasSolvInvPair_M24 hLn e₀ hTs hFT) ?_
  refine Vol2.Ch11.SecE3.one_le_nParam_of_not_odd
    (not_odd_of_two_dvd_card (H := CFSG.generalizedFitting G) ?_)
  have h1 : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .M24) = 2 ^ 10 * 239085 := m24_card
  rw [Nat.card_congr e₀.toEquiv, h1]
  exact dvd_mul_of_dvd_left (dvd_pow_self 2 (by norm_num)) _

end M24

end RonanE114

end CFSG.Quasithin
