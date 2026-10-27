
module

public import CFSG.Monster.B.TwoA.Base.Space34ABase
import all CFSG.Monster.B.TwoA.Base.Space34ABase

public import Certificates.Certificate16035

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Lifts CFSG.Monster.Visible
  CFSG.Monster.VisQuot CFSG.Monster.ScalarKernel CFSG.Monster.SpinLattice
  CFSG.Monster.B.Short CFSG.Monster.B.Co2 CFSG.Monster.VisCert CFSG.Sporadic.Mathieu

theorem dec_v0 :
    dec 12288 = v0 := by
  rw [v0_eq_pairCls]
  exact (cls_pairN_eq (by decide) (pairN_eq 0 1 (by decide)) (r := 12288)
    (by exact Certificates.certificate16035.1)).symm

theorem rCoord_check :
    ∀ i : Fin 7, rowCheck (pairN (pa7 i) (pb7 i)) (rCoord i) = true :=
  Certificates.certificate16035.2.1

theorem sCoord_act : ∀ i : Fin 7,
    Native.actD 22 Native.quotientBasis (sCoord i) = rCoord i ∨
      Native.actD 22 Native.quotientBasis (sCoord i) = rCoord i ^^^ 12288 :=
  Certificates.certificate16035.2.2.1

theorem sP_eq
    (i : Fin 7) : sP i = decW (sCoord i) := by
  obtain ⟨hm, he⟩ := decW_eq_mk (sCoord i)
  rw [he, sP, pairW]
  have hr := cls_pairN_eq (offPair7 i).ne (pairN_eq _ _ (offPair7 i).ne) (rCoord_check i)
  rcases sCoord_act i with h | h
  · congr 1
    apply Subtype.ext
    change pairCls (pa7 i) (pb7 i) 0 = dec (Native.actD 22 Native.quotientBasis (sCoord i))
    rw [h, hr]
  · rw [Submodule.Quotient.eq]
    change pairCls (pa7 i) (pb7 i) 0 - dec (Native.actD 22 Native.quotientBasis (sCoord i)) ∈
      vLineL v0
    rw [h, dec_xor, dec_v0, hr, sub_add_cancel_left]
    exact Submodule.neg_mem _ (Submodule.mem_span_singleton_self _)

theorem sP_one
    (i : Fin 7) : pairW (pa7 i) (pb7 i) (offPair7 i) 1 = decW (sCoord i ^^^ 31) := by
  rw [pairW_one, decW_xor, ← sP_eq, wFr_eq_decW]
  rfl

theorem sP_b
    (i : Fin 7) (b : ZMod 2) :
    pairW (pa7 i) (pb7 i) (offPair7 i) b = decW (sCoord i ^^^ sel b 31) := by
  rcases zmod2_cases b with rfl | rfl
  · rw [sel, ite_eq_right (by decide), Nat.xor_zero]
    exact sP_eq i
  · rw [sel, ite_eq_left rfl]
    exact sP_one i

theorem xsel4_cases :
    ∀ c : Fin 4 → ZMod 2, xsel4 c = 0 ∨ xsel4 c = 31 ∨
    ∃ i : Fin 7, ∃ b : ZMod 2, xsel4 c = sCoord i ^^^ sel b 31 :=
  Certificates.certificate16035.2.2.2.1

theorem xsel4_exists :
    ∀ (i : Fin 7) (b : ZMod 2), ∃ c : Fin 4 → ZMod 2,
    xsel4 c = sCoord i ^^^ sel b 31 :=
  Certificates.certificate16035.2.2.2.2.1

theorem xsel3_cases : ∀ c : Fin 3 → ZMod 2,
    xsel3 c = 0 ∨
      xsel3 c = 31 ∨
      ∃ i : Fin 7, (i : ℕ) < 3 ∧ ∃ b : ZMod 2,
        xsel3 c = sCoord i ^^^ sel b 31 :=
  Certificates.certificate16035.2.2.2.2.2.1

theorem xsel3_exists :
    ∀ (i : Fin 7), (i : ℕ) < 3 → ∀ b : ZMod 2, ∃ c : Fin 3 → ZMod 2,
    xsel3 c = sCoord i ^^^ sel b 31 :=
  Certificates.certificate16035.2.2.2.2.2.2.1

theorem pairSpace_U4 :
    PairSpace U4 A3 where
  pairs D hD := by
    obtain ⟨i, rfl⟩ := A3_eq_duad7 D hD
    exact ⟨_, _, offPair7 i, rfl⟩
  mem_iff z := by
    rw [mem_U4_iff_exists]
    constructor
    · rintro ⟨c, rfl⟩
      rcases xsel4_cases c with h | h | ⟨i, b, h⟩
      · left; rw [h, decW_zero]
      · right; left; rw [h, wFr_eq_decW]
      · right; right
        exact ⟨_, _, offPair7 i, duad7_mem_A3 i, b, by rw [h, sP_b]⟩
    · rintro (rfl | rfl | ⟨x, y, h, hD, b, rfl⟩)
      · exact ⟨0, by rw [show xsel4 0 = 0 by decide, decW_zero]⟩
      · exact ⟨Pi.single 0 1, by rw [show xsel4 (Pi.single 0 1) = 31 by decide,
          wFr_eq_decW]⟩
      · obtain ⟨i, hi⟩ := A3_eq_duad7 _ hD
        obtain ⟨c, hc⟩ := xsel4_exists i b
        exact ⟨c, by rw [pairW_of_duad_eq h hi, sP_b, hc]⟩

theorem pairSpace_U3 :
    PairSpace U3 A2 where
  pairs D hD := by
    obtain ⟨i, -, rfl⟩ := A2_eq_duad7 D hD
    exact ⟨_, _, offPair7 i, rfl⟩
  mem_iff z := by
    rw [mem_U3_iff_exists]
    constructor
    · rintro ⟨c, rfl⟩
      rcases xsel3_cases c with h | h | ⟨i, hi, b, h⟩
      · left; rw [h, decW_zero]
      · right; left; rw [h, wFr_eq_decW]
      · right; right
        exact ⟨_, _, offPair7 i, duad7_mem_A2 i hi, b, by rw [h, sP_b]⟩
    · rintro (rfl | rfl | ⟨x, y, h, hD, b, rfl⟩)
      · exact ⟨0, by rw [show xsel3 0 = 0 by decide,
          decW_zero]⟩
      · exact ⟨Pi.single 0 1, by
          rw [show xsel3 (Pi.single 0 1) = 31 by decide,
            wFr_eq_decW]⟩
      · obtain ⟨i, hi3, hi⟩ := A2_eq_duad7 _ hD
        obtain ⟨c, hc⟩ := xsel3_exists i hi3 b
        exact ⟨c, by rw [pairW_of_duad_eq h hi, sP_b, hc]⟩

theorem linearIndependent_gen4 :
    LinearIndependent (ZMod 2) gen4 := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  rw [sum_gen4, ← decW_zero] at hc
  have h1 : ∀ c : Fin 4 → ZMod 2, xsel4 c < 2 ^ 22 :=
    Certificates.certificate16035.2.2.2.2.2.2.2.1
  have h2 := decW_injective (h1 c) (by norm_num) hc
  have h3 : ∀ c : Fin 4 → ZMod 2, xsel4 c = 0 → c = 0 :=
    Certificates.certificate16035.2.2.2.2.2.2.2.2.1
  exact congrFun (h3 c h2)

theorem linearIndependent_gen3 :
    LinearIndependent (ZMod 2) gen3 := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  rw [sum_gen3, ← decW_zero] at hc
  have h1 : ∀ c : Fin 3 → ZMod 2, xsel3 c < 2 ^ 22 :=
    Certificates.certificate16035.2.2.2.2.2.2.2.2.2.1
  have h2 := decW_injective (h1 c) (by norm_num) hc
  have h3 : ∀ c : Fin 3 → ZMod 2, xsel3 c = 0 → c = 0 :=
    Certificates.certificate16035.2.2.2.2.2.2.2.2.2.2
  exact congrFun (h3 c h2)

theorem finrank_U4 :
    Module.finrank (ZMod 2) U4 = 4 := by
  rw [U4, finrank_span_eq_card linearIndependent_gen4, Fintype.card_fin]

theorem finrank_U3 :
    Module.finrank (ZMod 2) U3 = 3 := by
  rw [U3, finrank_span_eq_card linearIndependent_gen3, Fintype.card_fin]

end CFSG.Monster.B.TwoA
