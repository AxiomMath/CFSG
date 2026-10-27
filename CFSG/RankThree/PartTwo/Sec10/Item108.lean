module

public import CFSG.RankThree.PartTwo.Sec10.Steps
public import CFSG.RankThree.PartTwo.KFacts.K74Normal
public import CFSG.RankThree.PartTwo.Sec12.Item123

public section

namespace CFSG.RankThree.PartTwo.Sec10

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

section Core

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_zpowers_of_conj_mem {g x : G} (h : g * x * g⁻¹ ∈ Subgroup.zpowers x) :
    g ∈ Subgroup.normalizer (Subgroup.zpowers x : Set G) := by
  have hle : (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom ≤ Subgroup.zpowers x := by
    rw [MonoidHom.map_zpowers, Subgroup.zpowers_le]
    exact h
  have heq : (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers x :=
    Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [← heq]
    exact ⟨y, hy, rfl⟩
  · intro hy
    rw [← heq] at hy
    obtain ⟨z, hz, hzy⟩ := hy
    have hzy' : z = y := by
      have h1 : g * z * g⁻¹ = g * y * g⁻¹ := hzy
      exact mul_left_cancel (mul_right_cancel h1)
    rw [← hzy']
    exact hz

theorem rank3II_10_8_of {A : Subgroup G} (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (h27 : Nat.card A = 27) {c d : G} (hcA : c ∈ A) (hdA : d ∈ A) (hd : d ≠ 1) {L : Subgroup G}
    (hdL : A ⊓ L = Subgroup.zpowers d)
    (h107 : Sec12.transvectionGroup A ⟨d, hdA⟩ ≤ Sec4.autIn ⊤ A)
    (h103 : ∀ g : G, g * c * g⁻¹ ∉ L)
    (hHW : Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓ Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers d : Set G)) :
    Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G) := by
  have hd' : (⟨d, hdA⟩ : A) ≠ 1 := fun h => hd (congrArg Subtype.val h)
  have hdL' : Subgroup.zpowers d ≤ L := by
    rw [← hdL]
    exact inf_le_right
  have hc : ∀ σ ∈ Sec4.autIn ⊤ A, σ ⟨c, hcA⟩ ∉ Subgroup.zpowers ⟨d, hdA⟩ := by
    intro σ hσ hσc
    obtain ⟨g, hg, -, rfl⟩ := Sec4.mem_autIn_iff.mp hσ
    rw [Sec12.mem_zpowers_subtype_iff, Sec4.normalizerMonoidHom_apply_coe] at hσc
    exact h103 g (hdL' hσc)
  have hH : ∀ σ ∈ Sec4.autIn ⊤ A, σ ⟨c, hcA⟩ ∈ Subgroup.zpowers ⟨c, hcA⟩ →
      σ ⟨d, hdA⟩ ∈ Subgroup.zpowers ⟨d, hdA⟩ := by
    intro σ hσ hσc
    obtain ⟨g, hg, -, rfl⟩ := Sec4.mem_autIn_iff.mp hσ
    rw [Sec12.mem_zpowers_subtype_iff, Sec4.normalizerMonoidHom_apply_coe] at hσc ⊢
    have hgd := hHW ⟨mem_normalizer_zpowers_of_conj_mem hσc, hg⟩
    exact (Subgroup.mem_normalizer_iff.mp hgd d).mp (Subgroup.mem_zpowers d)
  have key := KFacts.mem_zpowers_of_transvectionGroup_le hA h27 hd' h107 hc hH
  intro g hg
  have h1 := key _ (Sec4.mem_autIn_iff.mpr ⟨g, hg, Subgroup.mem_top g, rfl⟩)
  rw [Sec12.mem_zpowers_subtype_iff, Sec4.normalizerMonoidHom_apply_coe] at h1
  exact mem_normalizer_zpowers_of_conj_mem h1

end Core

@[expose] def HWNormalizesL : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R : Subgroup G), Sec9.Hyp91 G A c L a R →
      Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓ Subgroup.normalizer (A : Set G) ≤
        Subgroup.normalizer (L : Set G)

theorem item108_of (h107 : Item107) (h103 : Item103) (hL : HWNormalizesL) : Item108 := by
  intro G _ _ A c L a R h d hdL
  by_cases hd : d = 1
  · intro g _
    rw [hd, Subgroup.zpowers_one_eq_bot, Subgroup.mem_normalizer_iff]
    intro y
    simp only [Subgroup.mem_bot]
    constructor
    · rintro rfl
      group
    · intro hy
      have h1 : y = g⁻¹ * (g * y * g⁻¹) * g := by group
      rw [h1, hy]
      group
  · have hdAL : d ∈ A ⊓ L := by
      rw [hdL]
      exact Subgroup.mem_zpowers d
    have hHW : Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓
        Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G) := by
      intro g hg
      have hgL := hL G A c L a R h.toHyp91 hg
      have hgA := (Subgroup.mem_inf.mp hg).2
      rw [← hdL, Subgroup.mem_normalizer_iff]
      intro y
      rw [Subgroup.mem_inf, Subgroup.mem_inf]
      exact and_congr (Subgroup.mem_normalizer_iff.mp hgA y) (Subgroup.mem_normalizer_iff.mp hgL y)
    exact rank3II_10_8_of h.mem_partTwoF.1 h.card_eq h.mem_A hdAL.1 hd hdL
      (h107 G A c L a R h d hdAL.1 hdL) (h103 G A c L a R h) hHW

end CFSG.RankThree.PartTwo.Sec10
