module

public import CFSG.RankThree.GF2n.Stroth80.Sec12Defs
public import CFSG.RankThree.GF2n.Stroth80.Sec39

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem card_V_of_naturalRep {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [Finite K]
    {X : Subgroup (GL ι K)} {R V Z N : Subgroup G} (hZV : Z ≤ V) (hK : Nat.card K = Nat.card Z)
    (h : NaturalRep K X R V Z N) : Nat.card V = Nat.card Z ^ (Fintype.card ι + 1) := by
  obtain ⟨φ, -, -, -, hN, ψ, -⟩ := h
  haveI : Fintype K := Fintype.ofFinite K
  have h1 : Nat.card (↥V ⧸ Z.subgroupOf V) = Nat.card K ^ Fintype.card ι := by
    rw [Nat.card_congr ψ.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_eq_fintype_card,
      Fintype.card_fun, ← Nat.card_eq_fintype_card (α := K)]
  have h2 : Nat.card (Z.subgroupOf V) = Nat.card Z :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZV).toEquiv
  have h3 := (Z.subgroupOf V).index_mul_card
  rw [Subgroup.index_eq_card, h1, h2, hK] at h3
  rw [← h3, pow_succ]

theorem card_Vt_of_plus {hc : Ctx M Q Z B} {t : G} {m : ℕ} (h : OmegaPlusNat hc t m) :
    Nat.card (Vt M (LB M Q B) B Z t) = Nat.card Z ^ (2 * m + 1) := by
  obtain ⟨K, fK, finK, hK, hrep⟩ := h
  have := card_V_of_naturalRep (sec39_Z_le_Vt (M := M) (L := LB M Q B) (B := B) (t := t)) hK hrep
  simpa [Fintype.card_sum, Fintype.card_fin, two_mul] using this

theorem card_Vt_of_minus {hc : Ctx M Q Z B} {t : G} {m : ℕ} (hm : 1 ≤ m)
    (h : OmegaMinusNat hc t m) :
    Nat.card (Vt M (LB M Q B) B Z t) = Nat.card Z ^ (2 * m + 1) := by
  obtain ⟨K, fK, finK, hK, b, c, -, hrep⟩ := h
  have := card_V_of_naturalRep (sec39_Z_le_Vt (M := M) (L := LB M Q B) (B := B) (t := t)) hK hrep
  rw [this]
  congr 1
  simp only [Fintype.card_sum, Fintype.card_fin]
  omega

theorem two_le_card_Z_of_ctx (hc : Ctx M Q Z B) : 2 ≤ Nat.card Z := by
  have := hc.hyp.q4
  omega

theorem eq_of_pow_card_Z (hc : Ctx M Q Z B) {a b : ℕ} (h : Nat.card Z ^ a = Nat.card Z ^ b) :
    a = b :=
  Nat.pow_right_injective (two_le_card_Z_of_ctx hc) h

theorem OmegaPlusNat.eq_of_plus {hc : Ctx M Q Z B} {t : G} {m m' : ℕ} (h : OmegaPlusNat hc t m)
    (h' : OmegaPlusNat hc t m') : m = m' := by
  have := eq_of_pow_card_Z hc ((card_Vt_of_plus h).symm.trans (card_Vt_of_plus h'))
  omega

theorem OmegaMinusNat.eq_of_minus {hc : Ctx M Q Z B} {t : G} {m m' : ℕ} (hm : 1 ≤ m)
    (hm' : 1 ≤ m') (h : OmegaMinusNat hc t m) (h' : OmegaMinusNat hc t m') : m = m' := by
  have := eq_of_pow_card_Z hc ((card_Vt_of_minus hm h).symm.trans (card_Vt_of_minus hm' h'))
  omega

theorem omegaPlusNat_eq_omegaMinusNat {hc : Ctx M Q Z B} {t : G} {m m' : ℕ} (hm' : 1 ≤ m')
    (h : OmegaPlusNat hc t m) (h' : OmegaMinusNat hc t m') : m = m' := by
  have := eq_of_pow_card_Z hc ((card_Vt_of_plus h).symm.trans (card_Vt_of_minus hm' h'))
  omega

end CFSG.RankThree.GF2n.Stroth80
