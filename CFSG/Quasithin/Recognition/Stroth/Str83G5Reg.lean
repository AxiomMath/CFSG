module

public import CFSG.Quasithin.Recognition.F112Crit.BenderLocalOf
public import CFSG.Quasithin.Recognition.Stroth.Str83G5Track

import CFSG.Quasithin.Recognition.F112Crit.BenderCartanElt
import CFSG.Quasithin.Background.GoldschmidtRankOneFacts

public section

namespace CFSG.Quasithin.Stroth.G5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.GH74.Uniqueness.Bender

theorem mem_bigB_or_of_mem_normalizer {G : Type} [Group G]
    [Finite G] {L M S : Subgroup G} (hF : Hyp111 L M S) {n i e : ℕ}
    (hL : BenderType (oTwoQuot ↥L) n i e) (hi : i ≠ 3) {H : Subgroup G} (hH : H ≤ bigB L M S)
    {d x : G} (hdH : d ∈ H) (hdL : d ∈ L) (hdO : d ∉ pCoreOf 2 L) (hx : x ∈ L ⊔ bigB L M S)
    (hxB : x ∉ bigB L M S) (hxH : x ∈ Subgroup.normalizer (H : Set G)) {y : G}
    (hy : y ∈ L ⊔ bigB L M S) (hyH : y ∈ Subgroup.normalizer (H : Set G)) :
    y ∈ bigB L M S ∨ x⁻¹ * y ∈ bigB L M S := by
  let B := bigB L M S
  have hR : Hyp111R L M S := Hyp111R.of_hyp111 rankOneListedFacts hF
  have hBL : B ≤ Subgroup.normalizer (L : Set G) := (F1.bigB_le_normalizer_left hR).1
  have hBS : B ≤ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) :=
    (F1.bigB_le_normalizer_sylow hR).1
  have hB1B : borelOf L S ≤ B := le_sup_left.trans le_sup_left
  have hdB : d ∈ B := hH hdH
  have hdN : d ∈ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) := hBS hdB
  obtain ⟨l', hl'L, b', hb'B, rfl⟩ :=
    (F1.mem_sup_iff_exists_mul_of_normalizes hBL).mp hx
  have hxdBH : (l' * b')⁻¹ * d * (l' * b') ∈ H :=
    (Subgroup.mem_normalizer_iff''.mp hxH d).mp hdH
  have hxdB : (l' * b')⁻¹ * d * (l' * b') ∈ B := hH hxdBH
  have hld'B : l'⁻¹ * d * l' ∈ B := by
    have e : l'⁻¹ * d * l' = b' * ((l' * b')⁻¹ * d * (l' * b')) * b'⁻¹ := by group
    rw [e]
    exact B.mul_mem (B.mul_mem hb'B hxdB) (B.inv_mem hb'B)
  have hld'N : l'⁻¹ * d * l' ∈ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) :=
    hBS hld'B
  have hl'N : l' ∉ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) := by
    intro hl'N
    exact hxB (B.mul_mem (hB1B (by exact ⟨hl'L, hl'N⟩ : l' ∈ borelOf L S)) hb'B)
  obtain ⟨l, hlL, b, hbB, rfl⟩ :=
    (F1.mem_sup_iff_exists_mul_of_normalizes hBL).mp hy
  have hydH : (l * b)⁻¹ * d * (l * b) ∈ H :=
    (Subgroup.mem_normalizer_iff''.mp hyH d).mp hdH
  have hldB : l⁻¹ * d * l ∈ B := by
    have h1 : (l * b)⁻¹ * d * (l * b) ∈ B := hH hydH
    have e : l⁻¹ * d * l = b * ((l * b)⁻¹ * d * (l * b)) * b⁻¹ := by group
    rw [e]
    exact B.mul_mem (B.mul_mem hbB h1) (B.inv_mem hbB)
  have hldN : l⁻¹ * d * l ∈ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) := hBS hldB
  rcases CFSG.Quasithin.F112Crit.BenderLocalOf.lift_fix_two_elt hL hi hF.h1.sylow
    hdL hdO hdN hl'L hl'N hld'N hlL hldN with hlN | hl'lN
  · left
    exact B.mul_mem (hB1B (by exact ⟨hlL, hlN⟩ : l ∈ borelOf L S)) hbB
  · right
    have hl'lL : l'⁻¹ * l ∈ L := L.mul_mem (L.inv_mem hl'L) hlL
    have hl'lB : l'⁻¹ * l ∈ B :=
      hB1B (by exact ⟨hl'lL, hl'lN⟩ : l'⁻¹ * l ∈ borelOf L S)
    have e : (l' * b')⁻¹ * (l * b) = b'⁻¹ * (l'⁻¹ * l * b) := by group
    rw [e]
    exact B.mul_mem (B.inv_mem hb'B) (B.mul_mem hl'lB hbB)

theorem trackData_bigB {G : Type} [Group G] [Finite G]
    {L1 L2 S : Subgroup G} (hF : Hyp111 L1 L2 S) {a f : ℕ} (ha : 1 ≤ a)
    (hSz : Nonempty (oTwoQuot ↥L1 ≃* Sz a)) (hf : 2 ≤ f) (hL2 : IsL2Quot f (oTwoQuot ↥L2))
    {H : Subgroup G} (hH : H ≤ bigB L1 L2 S) {d₁ d₂ x₁ x₂ : G}
    (hd₁H : d₁ ∈ H) (hd₁L : d₁ ∈ L1) (hd₁O : d₁ ∉ pCoreOf 2 L1)
    (hd₂H : d₂ ∈ H) (hd₂L : d₂ ∈ L2) (hd₂O : d₂ ∉ pCoreOf 2 L2)
    (hx₁ : x₁ ∈ L1 ⊔ bigB L1 L2 S) (hx₁B : x₁ ∉ bigB L1 L2 S)
    (hx₁H : x₁ ∈ Subgroup.normalizer (H : Set G))
    (hx₂ : x₂ ∈ L2 ⊔ bigB L1 L2 S) (hx₂B : x₂ ∉ bigB L1 L2 S)
    (hx₂H : x₂ ∈ Subgroup.normalizer (H : Set G)) :
    TrackData (L1 ⊔ bigB L1 L2 S) (L2 ⊔ bigB L1 L2 S) H x₁ x₂ := by
  have hBt₁ : BenderType (oTwoQuot ↥L1) (2 * a + 1) 2 1 :=
    BenderType.suzuki a ha (Classical.choice hSz |>.trans
      (MulEquiv.subgroupCongr (szModel_eq_open_sz a).symm))
  have hBt₂ : BenderType (oTwoQuot ↥L2) f 1 1 := BenderType.linear f hf (Classical.choice hL2)
  have hInt : (L1 ⊔ bigB L1 L2 S) ⊓ (L2 ⊔ bigB L1 L2 S) = bigB L1 L2 S :=
    (prop_F19_of_listed rankOneListedFacts hF).1
  refine ⟨hx₁, ?_, hx₂, ?_, hx₁H, hx₂H, ?_, ?_⟩
  · intro hmem
    exact hx₁B (hInt ▸ ⟨hx₁, hmem⟩)
  · intro hmem
    exact hx₂B (hInt ▸ ⟨hmem, hx₂⟩)
  · intro y hy hyH
    rcases mem_bigB_or_of_mem_normalizer hF hBt₁ (by norm_num) hH hd₁H hd₁L hd₁O hx₁ hx₁B hx₁H
      hy hyH with h | h
    · exact Or.inl (Subgroup.mem_sup_right h)
    · exact Or.inr (Subgroup.mem_sup_right h)
  · intro y hy hyH
    have hH' : H ≤ bigB L2 L1 S := by rwa [bigB_comm L1 L2 S]
    have hy' : y ∈ L2 ⊔ bigB L2 L1 S := by rwa [bigB_comm L1 L2 S]
    have hx₂B' : x₂ ∉ bigB L2 L1 S := by rwa [bigB_comm L1 L2 S]
    have hx₂' : x₂ ∈ L2 ⊔ bigB L2 L1 S := by rwa [bigB_comm L1 L2 S]
    rcases mem_bigB_or_of_mem_normalizer (M := L1) hF.symm hBt₂ (by norm_num) hH'
      hd₂H hd₂L hd₂O hx₂' hx₂B' hx₂H hy' hyH with h | h
    · exact Or.inl (Subgroup.mem_sup_right (by rwa [bigB_comm L1 L2 S] at h))
    · exact Or.inr (Subgroup.mem_sup_right (by rwa [bigB_comm L1 L2 S] at h))

end CFSG.Quasithin.Stroth.G5

