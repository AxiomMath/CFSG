module

public import CFSG.Monster.B.Rep4371.PacketData
public import CFSG.Monster.B.Cbar.LocalE

public section

namespace CFSG.Monster.B

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice CFSG.Monster.Lifts
  CFSG.Monster.Visible CFSG.Monster.Griess CFSG.Monster.ScalarKernel CFSG.Monster.B.Rep4371
  CFSG.Monster.VisQuot CFSG.Monster.VisCert

theorem bC_eq_basisC (j : Fin 12) : bC j = basisC j := Subtype.ext (basisC_apply j).symm

theorem frameQ_eq_of_lt {j : ℕ} (hj : j < 15) :
    Co2.frameQ j = QuotientGroup.mk (frameGen ⟨j, hj⟩) := by
  rw [Co2.frameQ, dite_eq_left hj]

theorem frameGen_zero : frameGen ⟨0, by norm_num⟩ = xiO := by
  rw [frameGen, ite_eq_left rfl]

theorem frameGen_one : frameGen ⟨1, by norm_num⟩ = PO pAAut := by
  rw [frameGen, ite_eq_right (by norm_num), ite_eq_left rfl]

theorem frameGen_two : frameGen ⟨2, by norm_num⟩ = PO pBAut := by
  rw [frameGen, ite_eq_right (by norm_num), ite_eq_right (by norm_num), ite_eq_left rfl]

theorem frameGen_of_ge {j : ℕ} (h3 : 3 ≤ j) (h15 : j < 15) :
    frameGen ⟨j, h15⟩ = gO (basisC ⟨j - 3, by omega⟩) := by
  rw [frameGen, ite_eq_right (by simp; omega), ite_eq_right (by simp; omega), ite_eq_right (by simp; omega),
    bC_eq_basisC]

theorem mk_PO_letterPerm {l : ℤ} (h0 : l ≠ 0) (h2 : l.natAbs ≤ 2) :
    (QuotientGroup.mk (PO (letterPerm l)) : OLq) = Co2.pairLetterQ l := by
  have hl : l.natAbs = 1 ∨ l.natAbs = 2 := by omega
  unfold letterPerm Co2.pairLetterQ
  by_cases hpos : 0 < l
  · rw [ite_eq_left hpos, ite_eq_left hpos]
    rcases hl with h | h
    · rw [ite_eq_left h, h, frameQ_eq_of_lt (by norm_num), frameGen_one]
    · rw [ite_eq_right (by omega), ite_eq_left h, h, frameQ_eq_of_lt (by norm_num), frameGen_two]
  · rw [ite_eq_right hpos, ite_eq_right hpos, PO_inv, QuotientGroup.mk_inv]
    rcases hl with h | h
    · rw [ite_eq_left h, h, frameQ_eq_of_lt (by norm_num), frameGen_one]
    · rw [ite_eq_right (by omega), ite_eq_left h, h, frameQ_eq_of_lt (by norm_num), frameGen_two]

theorem mk_PO_wordPerm : ∀ w : List ℤ, (∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ 2) →
    (QuotientGroup.mk (PO (wordPerm w)) : OLq) = Co2.pairWordQ w
  | [], _ => by rw [wordPerm, PO_one, QuotientGroup.mk_one, Co2.pairWordQ]
  | l :: w, hw => by
    rw [PO_wordPerm_cons, QuotientGroup.mk_mul,
      mk_PO_letterPerm (hw l List.mem_cons_self).1 (hw l List.mem_cons_self).2,
      mk_PO_wordPerm w fun l' hl' => hw l' (List.mem_cons_of_mem _ hl'), Co2.pairWordQ]

theorem mk_gO_frameSum : ∀ w : List ℤ, (∀ k ∈ w, 3 ≤ k.toNat ∧ k.toNat < 15) →
    (QuotientGroup.mk (gO (frameSum w)) : OLq) = Co2.frameWordQ w
  | [], _ => by
    rw [frameSum, List.map_nil, List.sum_nil, gO_zero, QuotientGroup.mk_one, Co2.frameWordQ]
  | k :: w, hw => by
    have hk := hw k List.mem_cons_self
    have hk' : k.toNat - 3 < 12 := by omega
    have hfs : frameSum (k :: w) = basisC ⟨k.toNat - 3, hk'⟩ + frameSum w := by
      rw [frameSum, List.map_cons, List.sum_cons, dite_eq_left hk']
      rfl
    rw [hfs, gO_add, QuotientGroup.mk_mul,
      mk_gO_frameSum w fun k' hk'' => hw k' (List.mem_cons_of_mem _ hk''), Co2.frameWordQ,
      frameQ_eq_of_lt hk.2, frameGen_of_ge hk.1 hk.2]

theorem pair_word_letters : ∀ i : Fin 24, (i : ℕ) < 12 →
    ∀ l ∈ (Co2.genRecord i).word, l ≠ 0 ∧ l.natAbs ≤ 2 := by
  decide +kernel

theorem codeSign_word_letters : ∀ i : Fin 24, 12 ≤ (i : ℕ) → (i : ℕ) < 23 →
    ∀ k ∈ (Co2.genRecord i).word, 3 ≤ k.toNat ∧ k.toNat < 15 := by
  decide +kernel

theorem alpha_of_pairStabilizer {i : Fin 24} (h : (Co2.genRecord i).kind = .pairStabilizer) :
    Co2.alpha i = Co2.pairWordQ (Co2.genRecord i).word := by
  rw [Co2.alpha, h]

theorem alpha_of_codeSign {i : Fin 24} (h : (Co2.genRecord i).kind = .codeSign) :
    Co2.alpha i = Co2.frameWordQ (Co2.genRecord i).word := by
  rw [Co2.alpha, h]

theorem alpha_of_xiSign {i : Fin 24} (h : (Co2.genRecord i).kind = .xiSign) :
    Co2.alpha i = Co2.frameWordQ (Co2.genRecord i).word := by
  rw [Co2.alpha, h]

theorem mk_hPair_snd (i : Fin 24) :
    (QuotientGroup.mk (hPair i : GL SpinIdx ℚ × latticeO).2 : OLq) = Co2.alpha i := by
  by_cases h1 : (i : ℕ) < 12
  · have hk : (Co2.genRecord i).kind = .pairStabilizer := by rw [genRecord_kind, ite_eq_left h1]
    rw [hPair_of_lt_twelve h1, alpha_of_pairStabilizer hk]
    exact mk_PO_wordPerm _ (pair_word_letters i h1)
  · by_cases h2 : (i : ℕ) < 23
    · have hk : (Co2.genRecord i).kind = .codeSign := by
        rw [genRecord_kind, ite_eq_right h1, ite_eq_left h2]
      rw [hPair_of_codeSign (by omega) h2, alpha_of_codeSign hk]
      exact mk_gO_frameSum _ (codeSign_word_letters i (by omega) h2)
    · have hi : i = 23 := Fin.ext (by omega)
      subst hi
      have hk : (Co2.genRecord 23).kind = .xiSign := by
        rw [genRecord_kind, ite_eq_right (by norm_num), ite_eq_right (by norm_num)]
      rw [hPair_xi, alpha_of_xiSign hk, genRecord_word_xi]
      show (QuotientGroup.mk (xiO * gO (toC 1)) : OLq) = Co2.frameWordQ [0, 3]
      rw [QuotientGroup.mk_mul, Co2.frameWordQ, Co2.frameWordQ, Co2.frameWordQ, mul_one,
        toC_one_eq, show (0 : ℤ).toNat = 0 from rfl, show (3 : ℤ).toNat = 3 from rfl,
        frameQ_eq_of_lt (by norm_num), frameQ_eq_of_lt (by norm_num), frameGen_zero,
        frameGen_of_ge (by norm_num) (by norm_num)]
      rfl

theorem jbarToKv_kappa_hElt (i : Fin 24) (hC : hElt i ∈ Cgen) (hJ : hElt i ∈ Jstar) :
    ((jbarToKv ⟨kappa ⟨hElt i, hC⟩, kappa_mem_Jbar hJ⟩ : Short.Kstab (phi0 (coordOf Short.rStar))) :
      OLq) = (Co2.alpha i)⁻¹ := by
  rw [coe_jbarToKv_kappa hJ (p := hPair i) rfl, mk_hPair_snd]

end CFSG.Monster.B
