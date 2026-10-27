module

public import CFSG.Quasithin.Recognition.GoldschmidtF112FA5Alt
public import CFSG.Quasithin.Recognition.F112WSetup

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.QuasithinUnique.A5.Delta5

namespace FA5

variable {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G}

structure Pair (L1 L2 S : Subgroup G) : Prop where
  hyp : Hyp111R L1 L2 S
  card1 : ∃ k : ℕ, 1 ≤ k ∧ Nat.card (OTwoQuot L1) = 2 ^ k * 5
  alt2 : Nonempty (OTwoQuot L2 ≃* Alt5)

namespace Pair

variable (h : Pair L1 L2 S)
include h

theorem borelOf_left_eq : borelOf L1 S = S ⊓ L1 := by
  obtain ⟨k, hk, hcard⟩ := h.card1
  have := inf_normalizer_eq_of_card_quot h.hyp.hyp.h1.sylow hk (r := 5) (by norm_num)
    (by decide) hcard
  simpa [borelOf] using this

theorem borelOf_left_le : borelOf L1 S ≤ S := h.borelOf_left_eq ▸ inf_le_left

theorem relIndex_borelOf_left : (borelOf L1 S).relIndex L1 = 5 := by
  obtain ⟨k, hk, hcard⟩ := h.card1
  rw [h.borelOf_left_eq]
  exact index_sylow_eq_of_card_quot h.hyp.hyp.h1.sylow (r := 5) (by decide) hcard

theorem relIndex_borelOf_right : (borelOf L2 S).relIndex L2 = 5 := by
  obtain ⟨e⟩ := h.alt2
  exact index_borelOf_of_alt5 h.hyp.hyp.h2.sylow e

theorem relIndex_sylow_right : (S ⊓ L2).relIndex L2 = 15 := by
  obtain ⟨e⟩ := h.alt2
  exact index_sylow_of_alt5 h.hyp.hyp.h2.sylow e

theorem relIndex_bigB_left :
    (bigB L1 L2 S).relIndex (L1 ⊔ bigB L1 L2 S) = 5 := by
  rw [F112W.relIndex_sup_eq_relIndex_inf (F1.bigB_le_normalizer_left h.hyp).1,
    F1.inf_bigB_eq_borelOf h.hyp]
  exact h.relIndex_borelOf_left

theorem relIndex_bigB_right :
    (bigB L1 L2 S).relIndex (L2 ⊔ bigB L1 L2 S) = 5 := by
  rw [F112W.relIndex_sup_eq_relIndex_inf (F1.bigB_le_normalizer_left h.hyp).2]
  have := F1.inf_bigB_eq_borelOf h.hyp.symm
  rw [bigB_comm] at this
  rw [this]
  exact h.relIndex_borelOf_right

theorem parabolic_right_eq : L2 ⊔ bigB L1 L2 S = L2 ⊔ S := by
  apply le_antisymm
  · refine sup_le le_sup_left (sup_le (sup_le (h.borelOf_left_le.trans le_sup_right) ?_)
      le_sup_right)
    exact (F1.borelOf_le L2 S).trans le_sup_left
  · exact sup_le_sup_left le_sup_right _

theorem relIndex_S_bigB : S.relIndex (bigB L1 L2 S) = 3 := by
  have hSB : S ≤ bigB L1 L2 S := le_sup_right
  have hBP : bigB L1 L2 S ≤ L2 ⊔ bigB L1 L2 S := le_sup_right
  have hmul := Subgroup.relIndex_mul_relIndex S (bigB L1 L2 S) (L2 ⊔ bigB L1 L2 S) hSB hBP
  rw [h.relIndex_bigB_right, h.parabolic_right_eq] at hmul
  have hP : S.relIndex (L2 ⊔ S) = 15 := by
    rw [F112W.relIndex_sup_eq_relIndex_inf h.hyp.hyp.h2.normalizes, inf_comm]
    exact h.relIndex_sylow_right
  rw [hP] at hmul
  omega

theorem exists_cartan :
    ∃ D : Subgroup G, D ≤ L2 ∧ Nat.card D = 3 ∧ D ⊓ S = ⊥ ∧ D ≤ Subgroup.normalizer (L1 : Set G) ∧
      (S ⊓ L2) ⊔ D = borelOf L2 S ∧ bigB L1 L2 S = S ⊔ D := by
  obtain ⟨e⟩ := h.alt2
  obtain ⟨D, hDB, hD3, hDS, hsup⟩ := exists_cartan_three h.hyp.hyp.h2.sylow e
  have hDL : D ≤ L2 := hDB.trans (F1.borelOf_le L2 S)
  have hDN : D ≤ Subgroup.normalizer (L1 : Set G) := hDB.trans h.hyp.hyp.h1.borel_le
  have hodd : D ⊓ S = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨k, hk⟩ := h.hyp.hyp.h1.pgroup ⟨x, hx.2⟩
    have hx2 : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hx3 : x ^ 3 = 1 := by
      have := pow_card_eq_one' (G := ↥D) (x := ⟨x, hx.1⟩)
      rw [hD3] at this
      simpa using congrArg Subtype.val this
    have hcop : Nat.gcd (2 ^ k) 3 = 1 := Nat.Coprime.pow_left k (by norm_num)
    have := pow_gcd_eq_one.mpr ⟨hx2, hx3⟩
    rw [hcop, pow_one] at this
    exact this
  refine ⟨D, hDL, hD3, hodd, hDN, hsup, ?_⟩
  have hB1 := h.borelOf_left_le
  apply le_antisymm
  · refine sup_le (sup_le (hB1.trans le_sup_left) ?_) le_sup_left
    rw [← hsup]
    exact sup_le (inf_le_left.trans le_sup_left) le_sup_right
  · refine sup_le le_sup_right ?_
    exact hDB.trans (le_sup_right.trans le_sup_left)

end Pair

end FA5

end CFSG.Quasithin
