module

public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma42NHyp
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisGL3
public import CFSG.RankThree.Classical.SteinbergBJBinaryThreeSpaceFrobenius

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79.LemmaN

open CFSG
open CFSG.ComponentClassification.GHarris (isSimpleGroup_GL32_gh card_GL32_gh)

variable {G : Type} [Group G] {Q L : Subgroup G} {b : G}

theorem NHyp.isSimple (h : NHyp Q L b) : IsSimpleGroup L := by
  obtain ⟨φ⟩ := h.iso
  haveI := isSimpleGroup_GL32_gh
  exact φ.isSimpleGroup

theorem NHyp.card_L (h : NHyp Q L b) : Nat.card L = 168 := by
  obtain ⟨φ⟩ := h.iso
  rw [Nat.card_congr φ.toEquiv, card_GL32_gh]

theorem NHyp.nonab_L (h : NHyp Q L b) : ∃ x y : L, x * y ≠ y * x := by
  obtain ⟨φ⟩ := h.iso
  by_contra hc
  push Not at hc
  have h1 := hc (φ.symm CFSG.RankThree.Classical.GL3.frobS)
    (φ.symm CFSG.RankThree.Classical.GL3.frobX)
  have h2 := congrArg φ h1
  rw [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h2
  have h3 := CFSG.RankThree.Classical.GL3.frobX_conj_frobS
  have h4 : CFSG.RankThree.Classical.GL3.frobS ^ 2 = CFSG.RankThree.Classical.GL3.frobS := by
    rw [← h3, ← h2]
    group
  have h5 : CFSG.RankThree.Classical.GL3.frobS = 1 := by
    have : CFSG.RankThree.Classical.GL3.frobS * CFSG.RankThree.Classical.GL3.frobS =
        CFSG.RankThree.Classical.GL3.frobS * 1 := by rw [← sq, h4, mul_one]
    exact mul_left_cancel this
  exact CFSG.RankThree.Classical.GL3.frobS_ne_one h5

theorem NHyp.centralizes_of_ne_one (h : NHyp Q L b) {l : G} (hl : l ∈ L) (hl1 : l ≠ 1)
    (hc : ∀ x ∈ Q, l * x = x * l) : Q ≤ Subgroup.centralizer (L : Set G) := by
  haveI := h.isSimple
  set K : Subgroup L := (L ⊓ Subgroup.centralizer (Q : Set G)).subgroupOf L with hK
  have hKn : K.Normal := ⟨fun k hk g => by
    rw [hK, Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hk ⊢
    obtain ⟨hk1, hk2⟩ := hk
    refine ⟨L.mul_mem (L.mul_mem g.2 hk1) (L.inv_mem g.2), ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hgx : (g : G)⁻¹ * x * (g : G) ∈ Q := by
      have := (Subgroup.mem_normalizer_iff.mp (h.normalizes (L.inv_mem g.2)) x).mp hx
      simpa using this
    have e := Subgroup.mem_centralizer_iff.mp hk2 _ hgx
    show x * ((g : G) * (k : G) * (g : G)⁻¹) = ((g : G) * (k : G) * (g : G)⁻¹) * x
    calc x * ((g : G) * (k : G) * (g : G)⁻¹)
        = (g : G) * (((g : G)⁻¹ * x * (g : G)) * (k : G)) * (g : G)⁻¹ := by group
      _ = (g : G) * ((k : G) * ((g : G)⁻¹ * x * (g : G))) * (g : G)⁻¹ := by rw [e]
      _ = ((g : G) * (k : G) * (g : G)⁻¹) * x := by group⟩
  rcases hKn.eq_bot_or_eq_top with hb | ht
  · exfalso
    have : (⟨l, hl⟩ : L) ∈ K := by
      rw [hK, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨hl, Subgroup.mem_centralizer_iff.mpr fun x hx => (hc x hx).symm⟩
    rw [hb, Subgroup.mem_bot] at this
    exact hl1 (congrArg Subtype.val this)
  · intro x hx l' hl'
    have : (⟨l', hl'⟩ : L) ∈ K := ht ▸ Subgroup.mem_top _
    rw [hK, Subgroup.mem_subgroupOf, Subgroup.mem_inf] at this
    exact (Subgroup.mem_centralizer_iff.mp this.2 x hx).symm

theorem NHyp.eq_top_of_index_le_three (h : NHyp Q L b) (H : Subgroup L) (hi : H.index ≤ 3) :
    H = ⊤ := by
  haveI := h.isSimple
  haveI : Finite L := Nat.finite_of_card_ne_zero (by rw [h.card_L]; norm_num)
  rcases (Subgroup.normalCore_normal H).eq_bot_or_eq_top with hb | ht
  · exfalso
    have hinj : Function.Injective (MulAction.toPermHom L (L ⧸ H)) := by
      rw [← MonoidHom.ker_eq_bot_iff, ← Subgroup.normalCore_eq_ker, hb]
    have h1 := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_perm, ← Subgroup.index, h.card_L] at h1
    have h2 : Nat.factorial H.index ≤ Nat.factorial 3 := Nat.factorial_le hi
    have : Nat.factorial 3 = 6 := rfl
    omega
  · exact top_le_iff.mp (ht ▸ Subgroup.normalCore_le H)

end CFSG.RankThree.PartTwo.Sec21.FF79.LemmaN
