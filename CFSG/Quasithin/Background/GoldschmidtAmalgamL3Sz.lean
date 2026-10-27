module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3Ord

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {z : D} {V : Subgroup D}

namespace GoldHyp3

variable (h : GoldHyp3 A B z V)

include h

theorem not_mem_normalizer_conjClosure {y : D} (hyA : y ∈ A) (hy3 : orderOf y = 3) :
    y ∉ Subgroup.normalizer (conjClosure V B : Set D) := by
  intro hyN
  have hyT := h.gold.vertex_left.not_mem_of_orderOf hy3
  have hy2T := h.gold.vertex_left.sq_not_mem_of_orderOf hy3
  have hAN : A ≤ Subgroup.normalizer (conjClosure V B : Set D) := by
    intro a ha
    rcases coset_decomp h.gold.relIndex_left hyA hyT hy2T ha with haT | ⟨t, htT, rfl⟩ |
        ⟨t, htT, rfl⟩
    · exact le_normalizer_conjClosure V B haT.2
    · exact Subgroup.mul_mem _ hyN (le_normalizer_conjClosure V B htT.2)
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hyN hyN) (le_normalizer_conjClosure V B htT.2)
  have hUT : conjClosure V B ≤ A ⊓ B :=
    h.conjClosure_le_pCoreOf_right.trans h.gold.pCoreOf_right_le
  have hbot := h.gold.eq_bot_of_normalizes hAN (le_normalizer_conjClosure V B) hUT
  have hV : V ≤ (⊥ : Subgroup D) := hbot ▸ le_conjClosure V B
  have h4 := Subgroup.card_le_of_le hV
  rw [h.natural.card_eq] at h4
  simp at h4

theorem inf_conjSub_conjClosure_le (hU : Nat.card (conjClosure V B) = 8) {y : D} (hyA : y ∈ A)
    (hy3 : orderOf y = 3) :
    conjClosure V B ⊓ conjSub y (conjClosure V B) ≤ V := by
  intro x hx
  by_contra hxV
  have hVy : V ≤ conjSub y (conjClosure V B) := by
    have h1 : conjSub y V = V := conjSub_eq_of_mem_normalizer (h.natural.reduced.2.1 hyA)
    have h2 : conjSub y V ≤ conjSub y (conjClosure V B) :=
      conjSub_mono y (le_conjClosure V B)
    rwa [h1] at h2
  have hUle : conjClosure V B ≤ conjSub y (conjClosure V B) := by
    intro u hu
    by_cases huV : u ∈ V
    · exact hVy huV
    · have hv : u * x⁻¹ ∈ V := h.mul_inv_mem_V_of_not_mem hU hu hx.1 huV hxV
      have e : u = (u * x⁻¹) * x := by group
      rw [e]
      exact Subgroup.mul_mem _ (hVy hv) hx.2
  have hEq : conjSub y (conjClosure V B) = conjClosure V B :=
    (Subgroup.eq_of_le_of_card_ge hUle (by rw [card_conjSub])).symm
  exact h.not_mem_normalizer_conjClosure hyA hy3 (mem_normalizer_of_conjSub_eq hEq)

theorem thirty_two_le_card_coreIn_of_four_le (hU : Nat.card (conjClosure V B) = 8)
    (h4 : 4 ≤ critDist (A ⊔ B) A B V) :
    32 ≤ Nat.card ↥(coreIn (pCoreOf 2 A ⊓ pCoreOf 2 B) B) := by
  obtain ⟨y, hyA, hy3⟩ := h.gold.vertex_left.exists_order_three
  set U : Subgroup D := conjClosure V B with hUdef
  set W : Subgroup D := conjClosure U A with hWdef
  have hWK : W ≤ coreIn (pCoreOf 2 A ⊓ pCoreOf 2 B) B := h.four_le_critDist_iff_le_coreIn.mp h4
  have hUyW : conjSub y U ≤ W := HypF91.conjSub_le_conjClosure hyA
  have hUW : U ≤ W := le_conjClosure U A
  have hsup : U ⊔ conjSub y U ≤ W := sup_le hUW hUyW
  have h16 : 16 ≤ Nat.card ↥(U ⊔ conjSub y U) := by
    obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le (le_sup_left : U ≤ U ⊔ conjSub y U)
    rw [hU] at hm
    have hm1 : m ≠ 1 := by
      rintro rfl
      have heq : U = U ⊔ conjSub y U :=
        Subgroup.eq_of_le_of_card_ge (le_sup_left : U ≤ U ⊔ conjSub y U) (by omega)
      have hle : conjSub y U ≤ U := le_sup_right.trans heq.symm.le
      have hEq : conjSub y U = U :=
        Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjSub])
      exact h.not_mem_normalizer_conjClosure hyA hy3 (mem_normalizer_of_conjSub_eq hEq)
    have hm0 : m ≠ 0 := by
      rintro rfl
      have : 0 < Nat.card ↥(U ⊔ conjSub y U) := Nat.card_pos
      omega
    have : 2 ≤ m := by omega
    omega
  have hW16 : 16 ≤ Nat.card ↥W := h16.trans (Subgroup.card_le_of_le hsup)
  have hWne : W ≠ coreIn (pCoreOf 2 A ⊓ pCoreOf 2 B) B := by
    intro heq
    have hAN : A ≤ Subgroup.normalizer (W : Set D) := le_normalizer_conjClosure U A
    have hBN : B ≤ Subgroup.normalizer (W : Set D) := heq ▸ le_normalizer_coreIn _ _
    have hWT : W ≤ A ⊓ B :=
      hWK.trans ((coreIn_le_right _ _).trans (inf_le_left.trans h.gold.pCoreOf_left_le))
    have hbot := h.gold.eq_bot_of_normalizes hAN hBN hWT
    have h1 : Nat.card ↥W = 1 := by rw [hbot]; simp
    omega
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hWK
  have hm1 : m ≠ 1 := by
    rintro rfl
    exact hWne (Subgroup.eq_of_le_of_card_ge hWK (by omega))
  have hm0 : m ≠ 0 := by
    rintro rfl
    have : 0 < Nat.card ↥(coreIn (pCoreOf 2 A ⊓ pCoreOf 2 B) B) := Nat.card_pos
    omega
  have : 2 ≤ m := by omega
  nlinarith

theorem critDist_eq_three_and_card_inf_eq_of_card_coreIn_le
    (hU : Nat.card (conjClosure V B) = 8)
    (hK : Nat.card ↥(coreIn (pCoreOf 2 A ⊓ pCoreOf 2 B) B) ≤ 16) :
    critDist (A ⊔ B) A B V = 3 ∧ (Nat.card ↥(A ⊓ B) = 64 ∨ Nat.card ↥(A ⊓ B) = 128) := by
  refine ⟨?_, ?_⟩
  · have h3 := h.three_le_critDist
    by_contra hne
    have h4 : 4 ≤ critDist (A ⊔ B) A B V := by omega
    have := h.thirty_two_le_card_coreIn_of_four_le hU h4
    omega
  · have h3 := h.eight_le_card_coreIn
    have h4 := h.card_inf_eq_eight_mul hU
    have hpg : IsPGroup 2 ↥(coreIn (pCoreOf 2 A ⊓ pCoreOf 2 B) B) :=
      (pCoreOf_isPGroup 2 B).to_le ((coreIn_le_right _ _).trans inf_le_right)
    obtain ⟨n, hn⟩ := hpg.exists_card_eq
    rw [hn] at h3 hK h4
    have hn3 : 3 ≤ n := by
      by_contra hlt
      push Not at hlt
      interval_cases n <;> simp at h3
    have hn4 : n ≤ 4 := by
      by_contra hlt
      push Not at hlt
      have : 2 ^ 5 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hlt
      omega
    interval_cases n
    · left; omega
    · right; omega

end GoldHyp3

end GoldAmL3

end F6

end CFSG.Quasithin
