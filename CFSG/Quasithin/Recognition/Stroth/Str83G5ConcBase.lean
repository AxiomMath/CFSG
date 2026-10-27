module

public import CFSG.Quasithin.Recognition.Stroth.Str83G5ChiConj
public import CFSG.Quasithin.Recognition.Stroth.Str83G5ArithBasic

public section

namespace CFSG.Quasithin.Stroth.G5

open Subgroup CFSG.Quasithin.OperatorJH

variable {G : Type} [Group G] [Finite G] {n : ℕ}

private theorem le_normalizer_inf' {K A B : Subgroup G} (hA : K ≤ normalizer (A : Set G))
    (hB : K ≤ normalizer (B : Set G)) : K ≤ normalizer ((A ⊓ B : Subgroup G) : Set G) :=
  (le_inf hA hB).trans inf_normalizer_le_normalizer_inf

theorem baseS_of_emb (hn : Odd n) {ζ : GaloisField 2 n} (hζ : orderOf ζ = 2 ^ n - 1)
    {d₁ d₂ : G} {Q X₀ S : Subgroup G} {β β' : G → GaloisField 2 n} {k₀ m₀ : ZMod (2 ^ n - 1)}
    (hQX : Q ≤ X₀) (hXS : X₀ ≤ S) (hsq : ∀ s ∈ S, s ∉ X₀ → s ^ 2 ∈ X₀ ∧ s ^ 2 ∉ Q)
    (hβ : IsChiEmb ζ d₁ d₂ X₀ S ((-1 : ZMod (2 ^ n - 1)) • psi m₀) β)
    (hβ' : IsChiEmb ζ d₁ d₂ Q X₀ (cen n • (-1 : ZMod (2 ^ n - 1)) • psi m₀) β')
    (hSQ : S ≤ normalizer (Q : Set G)) (hSX : S ≤ normalizer (X₀ : Set G))
    (hHQ : zpowers d₁ ⊔ zpowers d₂ ≤ normalizer (Q : Set G))
    (hHX : zpowers d₁ ⊔ zpowers d₂ ≤ normalizer (X₀ : Set G))
    {Y : Subgroup G} (hYS : Y ≤ S) (hHY : zpowers d₁ ⊔ zpowers d₂ ≤ normalizer (Y : Set G)) :
    ∃ d ≤ 2, Q.relIndex Y = (2 ^ n) ^ d ∧
      ∃ l, IsYSeries (zpowers d₁ ⊔ zpowers d₂) (Q ⊓ Y) l Y ∧
        facMultiset (chiLab ζ d₁ d₂) l Y = clsSets (Pattern.contrib k₀ m₀ (-1) 0 d) := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact Nat.not_odd_zero hn
  have hd₁H : d₁ ∈ zpowers d₁ ⊔ zpowers d₂ := mem_sup_left (mem_zpowers d₁)
  have hd₂H : d₂ ∈ zpowers d₁ ⊔ zpowers d₂ := mem_sup_right (mem_zpowers d₂)
  have hYN : Y ≤ normalizer (Y : Set G) := le_normalizer
  have hYX : Y ≤ normalizer ((Y ⊓ X₀ : Subgroup G) : Set G) :=
    le_normalizer_inf' hYN (hYS.trans hSX)
  have hHYX : zpowers d₁ ⊔ zpowers d₂ ≤ normalizer ((Y ⊓ X₀ : Subgroup G) : Set G) :=
    le_normalizer_inf' hHY hHX
  have hYXQ : Y ⊓ X₀ ≤ normalizer ((Q ⊓ Y : Subgroup G) : Set G) :=
    le_normalizer_inf' ((inf_le_right.trans hXS).trans hSQ) (inf_le_left.trans hYN)
  have hHQY : zpowers d₁ ⊔ zpowers d₂ ≤ normalizer ((Q ⊓ Y : Subgroup G) : Set G) :=
    le_normalizer_inf' hHQ hHY
  have eTop := hβ.restrict hYS
  have eBot : IsChiEmb ζ d₁ d₂ (Q ⊓ Y) (Y ⊓ X₀) (cen n • (-1 : ZMod (2 ^ n - 1)) • psi m₀) β' := by
    have h := hβ'.restrict (inf_le_right : Y ⊓ X₀ ≤ X₀)
    rwa [inf_assoc, inf_eq_right.mpr hQX, inf_comm] at h
  have hu₁ : IsUnit ((-1 : ZMod (2 ^ n - 1)) • psi m₀).1 := by
    simpa [psi] using isUnit_one.neg
  have hu₂ : IsUnit (cen n • (-1 : ZMod (2 ^ n - 1)) • psi m₀).1 := by
    simpa [psi] using (isUnit_cen hn).neg
  by_cases hYX₀ : Y ≤ X₀
  · have hT : Y ⊓ X₀ = Y := inf_eq_left.mpr hYX₀
    by_cases hYQ : Y ≤ Q
    · refine ⟨0, by norm_num, ?_, [], inf_eq_right.mpr hYQ, ?_⟩
      · rw [pow_zero]
        exact relIndex_eq_one.mpr hYQ
      · simp [facMultiset, clsSets, Pattern.contrib]
    · have hlt : Q ⊓ Y < Y := lt_of_le_of_ne inf_le_right fun h => hYQ (by
        rw [← h]
        exact inf_le_left)
      rw [hT] at eBot hYXQ
      have hs := eBot.isYSimple hn0 hζ hu₂ hd₁H hlt hYXQ hHQY hHY
      refine ⟨1, by norm_num, ?_, [Q ⊓ Y], ⟨hs, rfl⟩, ?_⟩
      · rw [← inf_relIndex_right, eBot.relIndex_eq hn0 hζ hs, card_cls_of_isUnit hn0 hu₂, pow_one]
      · simp only [facMultiset]
        rw [eBot.chiLab_eq_cls hn0 hζ (hHY hd₁H) (hHY hd₂H) (not_le_of_gt hlt)]
        simp [clsSets, Pattern.contrib]
  · obtain ⟨s, hsY, hsX⟩ := SetLike.not_le_iff_exists.mp hYX₀
    obtain ⟨hs₁, hs₂⟩ := hsq s (hYS hsY) hsX
    have hlt₁ : Y ⊓ X₀ < Y := lt_of_le_of_ne inf_le_left fun h => hYX₀ (by
      rw [← h]
      exact inf_le_right)
    have hlt₂ : Q ⊓ Y < Y ⊓ X₀ := by
      refine lt_of_le_of_ne (le_inf inf_le_right (inf_le_left.trans hQX)) fun h => hs₂ ?_
      have : s ^ 2 ∈ Y ⊓ X₀ := mem_inf.mpr ⟨pow_mem hsY 2, hs₁⟩
      rw [← h] at this
      exact (mem_inf.mp this).1
    have hsT := eTop.isYSimple hn0 hζ hu₁ hd₁H hlt₁ hYX hHYX hHY
    have hsB := eBot.isYSimple hn0 hζ hu₂ hd₁H hlt₂ hYXQ hHQY hHYX
    refine ⟨2, le_rfl, ?_, [Y ⊓ X₀, Q ⊓ Y], ⟨hsT, hsB, rfl⟩, ?_⟩
    · rw [← inf_relIndex_right, ← relIndex_mul_relIndex (Q ⊓ Y) (Y ⊓ X₀) Y hlt₂.le hlt₁.le,
        eBot.relIndex_eq hn0 hζ hsB, eTop.relIndex_eq hn0 hζ hsT, card_cls_of_isUnit hn0 hu₂,
        card_cls_of_isUnit hn0 hu₁, sq]
    · simp only [facMultiset]
      rw [eTop.chiLab_eq_cls hn0 hζ (hHY hd₁H) (hHY hd₂H) (not_le_of_gt hlt₁),
        eBot.chiLab_eq_cls hn0 hζ (hHYX hd₁H) (hHYX hd₂H) (not_le_of_gt hlt₂)]
      simp [clsSets, Pattern.contrib]

theorem baseL_of_emb {ζ : GaloisField 2 n} (hn : n ≠ 0) (hζ : orderOf ζ = 2 ^ n - 1)
    {d₁ d₂ : G} {Q S : Subgroup G} {β : G → GaloisField 2 n} {k₀ m₀ : ZMod (2 ^ n - 1)}
    (hk₀ : IsUnit k₀) (hβ : IsChiEmb ζ d₁ d₂ Q S (chi k₀) β)
    (hSQ : S ≤ normalizer (Q : Set G)) (hHQ : zpowers d₁ ⊔ zpowers d₂ ≤ normalizer (Q : Set G))
    {Y : Subgroup G} (hYS : Y ≤ S) (hHY : zpowers d₁ ⊔ zpowers d₂ ≤ normalizer (Y : Set G)) :
    ∃ d ≤ 1, Q.relIndex Y = (2 ^ n) ^ d ∧
      ∃ l, IsYSeries (zpowers d₁ ⊔ zpowers d₂) (Y ⊓ Q) l Y ∧
        facMultiset (chiLab ζ d₁ d₂) l Y = clsSets (Pattern.contrib k₀ m₀ 1 1 d) := by
  have hd₁H : d₁ ∈ zpowers d₁ ⊔ zpowers d₂ := mem_sup_left (mem_zpowers d₁)
  have hd₂H : d₂ ∈ zpowers d₁ ⊔ zpowers d₂ := mem_sup_right (mem_zpowers d₂)
  have hYQ' : Y ≤ normalizer ((Y ⊓ Q : Subgroup G) : Set G) :=
    le_normalizer_inf' le_normalizer (hYS.trans hSQ)
  have hHYQ : zpowers d₁ ⊔ zpowers d₂ ≤ normalizer ((Y ⊓ Q : Subgroup G) : Set G) :=
    le_normalizer_inf' hHY hHQ
  have e := hβ.restrict hYS
  have hu : IsUnit (chi k₀ : Coord n).1 := hk₀
  by_cases hYQ : Y ≤ Q
  · refine ⟨0, by norm_num, ?_, [], inf_eq_left.mpr hYQ, ?_⟩
    · rw [pow_zero]
      exact relIndex_eq_one.mpr hYQ
    · simp [facMultiset, clsSets, Pattern.contrib]
  · have hlt : Y ⊓ Q < Y := lt_of_le_of_ne inf_le_left fun h => hYQ (by
      rw [← h]
      exact inf_le_right)
    have hs := e.isYSimple hn hζ hu hd₁H hlt hYQ' hHYQ hHY
    refine ⟨1, le_rfl, ?_, [Y ⊓ Q], ⟨hs, rfl⟩, ?_⟩
    · rw [← inf_relIndex_right, inf_comm Q Y, e.relIndex_eq hn hζ hs, card_cls_of_isUnit hn hu,
        pow_one]
    · simp only [facMultiset]
      rw [e.chiLab_eq_cls hn hζ (hHY hd₁H) (hHY hd₂H) (not_le_of_gt hlt)]
      simp [clsSets, Pattern.contrib]

end CFSG.Quasithin.Stroth.G5

end
