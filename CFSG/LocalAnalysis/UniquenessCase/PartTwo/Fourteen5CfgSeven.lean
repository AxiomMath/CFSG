module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen5Inputs
public import CFSG.RankThree.PartOne.CTP.StrongPGlue
public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

namespace Cfg145

variable {K : Type} [Group K] [Finite K] {M X₁ X₂ P : Subgroup K}

theorem isSylowOf_seven_top (c : Cfg145 M X₁ X₂ P) : CFSG.ABGLocalTools.IsSylowOf 7 P ⊤ := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨Q, hQtop, hQM⟩ := c.strong.exists_isSylowOf_le
  have hQtop' : CFSG.ABGLocalTools.IsSylowOf 7 Q ⊤ :=
    CFSG.ABGLocalTools.isSylowOf_iff.mpr hQtop
  have hQM' : CFSG.ABGLocalTools.IsSylowOf 7 Q M := hQtop'.of_le hQM le_top
  have hcardPQ : Nat.card P = Nat.card Q := by
    rw [c.isSylowOf_seven.card_eq, hQM'.card_eq]
  refine CFSG.ABGLocalTools.isSylowOf_of_card le_top ?_
  rw [hcardPQ, hQtop'.card_eq]

theorem ne_bot_seven (c : Cfg145 M X₁ X₂ P) : P ≠ ⊥ := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  intro hbot
  haveI : Nonempty M := ⟨⟨1, M.one_mem⟩⟩
  have hpos : 0 < (Nat.card M).factorization 7 :=
    (by norm_num : Nat.Prime 7).factorization_pos_of_dvd (Nat.card_pos (α := M)).ne'
      c.strong.2.1
  have hcard := c.isSylowOf_seven.card_eq
  rw [hbot, Subgroup.card_bot] at hcard
  exact (one_lt_pow' (by norm_num : 1 < 7) hpos.ne').ne' hcard.symm

theorem normalizer_seven_le (c : Cfg145 M X₁ X₂ P) : normalizer (P : Set K) ≤ M := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact c.strong.normalizer_le c.ne_bot_seven c.isSylowOf_seven.isPGroup c.isSylowOf_seven.le

lemma inv_mul_mul_eq_of_mem_centralizer {s : Set K} {k z : K}
    (hk : k ∈ centralizer s) (hz : z ∈ s) : k⁻¹ * z * k = z := by
  have h := Subgroup.mem_centralizer_iff.mp hk z hz
  calc k⁻¹ * z * k = k⁻¹ * (z * k) := by group
    _ = k⁻¹ * (k * z) := by rw [h]
    _ = z := by group

lemma map_conj_le_centralizer {X P : Subgroup K} {d : K}
    (hd : d ∈ normalizer (X : Set K)) (hP : P ≤ centralizer (X : Set K)) :
    P.map (MulAut.conj d).toMonoidHom ≤ centralizer (X : Set K) := by
  have hmap : X.map (MulAut.conj d).toMonoidHom = X := by
    simpa using (Subgroup.mem_normalizer_iff_map_conj_eq (H := X) (g := d)).mp hd
  have hfX : (MulAut.conj d).toMonoidHom '' (X : Set K) = (X : Set K) := by
    rw [← Subgroup.coe_map, hmap]
  calc P.map (MulAut.conj d).toMonoidHom
      ≤ (centralizer (X : Set K)).map (MulAut.conj d).toMonoidHom := Subgroup.map_mono hP
    _ ≤ centralizer ((MulAut.conj d).toMonoidHom '' (X : Set K)) :=
        Subgroup.map_centralizer_le_centralizer_image (X : Set K) _
    _ = centralizer (X : Set K) := by rw [hfX]

theorem exists_mem_normalizer_inf (c : Cfg145 M X₁ X₂ P) (s₁ s₂ : Bool) :
    ∃ e ∈ normalizer ((X₁ ⊔ X₂ : Subgroup K) : Set K) ⊓ normalizer (P : Set K),
      (∀ x ∈ X₁, e * x * e⁻¹ = if s₁ then x⁻¹ else x) ∧
        (∀ x ∈ X₂, e * x * e⁻¹ = if s₂ then x⁻¹ else x) := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  let Xs : Set K := ((X₁ ⊔ X₂ : Subgroup K) : Set K)
  let C : Subgroup K := centralizer Xs
  have hPC : P ≤ C := c.le_centralizer
  have hCn : C ≤ normalizer Xs := Subgroup.centralizer_le_normalizer Xs
  have hCM : C ≤ M := hCn.trans c.normalizer_le
  have hPCsyl : CFSG.ABGLocalTools.IsSylowOf 7 P C := c.isSylowOf_seven.of_le hPC hCM
  obtain ⟨d, hdX, hd₁, hd₂⟩ := c.inversion s₁ s₂
  have hP'C : P.map (MulAut.conj d).toMonoidHom ≤ C := map_conj_le_centralizer hdX hPC
  have hcard' : Nat.card (P.map (MulAut.conj d).toMonoidHom) =
      7 ^ (Nat.card C).factorization 7 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj d).injective, hPCsyl.card_eq]
  have hP'syl : CFSG.ABGLocalTools.IsSylowOf 7 (P.map (MulAut.conj d).toMonoidHom) C :=
    CFSG.ABGLocalTools.isSylowOf_of_card hP'C hcard'
  obtain ⟨k, hkC, hconj⟩ := hPCsyl.exists_mem_conj hP'syl
  have heval : ∀ h : K, (k⁻¹ * d) * h * (k⁻¹ * d)⁻¹ = k⁻¹ * (d * h * d⁻¹) * k := by
    intro h; group
  have hmem : ∀ h : K, d * h * d⁻¹ ∈ P.map (MulAut.conj d).toMonoidHom ↔ h ∈ P := by
    intro h
    rw [← MulAut.conj_apply]
    exact Subgroup.mem_map_iff_mem (MulAut.conj d).injective
  refine ⟨k⁻¹ * d, ⟨?_, ?_⟩, ?_, ?_⟩
  · exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hCn hkC)) hdX
  · exact Subgroup.mem_normalizer_iff.mpr fun h => by
      rw [heval h, ← hconj (d * h * d⁻¹), hmem h]
  · intro x hx
    have hz : (if s₁ then x⁻¹ else x) ∈ Xs := by
      by_cases hs : s₁
      · rw [if_pos hs]; exact Subgroup.mem_sup_left (X₁.inv_mem hx)
      · rw [if_neg hs]; exact Subgroup.mem_sup_left hx
    rw [heval x, hd₁ x hx]
    exact inv_mul_mul_eq_of_mem_centralizer hkC hz
  · intro x hx
    have hz : (if s₂ then x⁻¹ else x) ∈ Xs := by
      by_cases hs : s₂
      · rw [if_pos hs]; exact Subgroup.mem_sup_right (X₂.inv_mem hx)
      · rw [if_neg hs]; exact Subgroup.mem_sup_right hx
    rw [heval x, hd₂ x hx]
    exact inv_mul_mul_eq_of_mem_centralizer hkC hz

end Cfg145

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
