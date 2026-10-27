module

public import CFSG.Quasithin.Vol2.Ch3B513NC1Setup
public import CFSG.Quasithin.Background.FFC4Five
public import CFSG.Quasithin.Background.FFC5Two
public import CFSG.Quasithin.Background.B5FinWedge

public section

namespace CFSG.Quasithin.B513N

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

variable {W : Type} [CommGroup W] [Finite W]

theorem hasGood_of_realizes_small (hW : ∀ w : W, w ^ 2 = 1) {G L : Subgroup (MulAut W)}
    (hne : G ≠ ⊥) (hJ : G = ffJ G) (hGL : G ≤ L) {M : FFModel} (hM : M.Faithful)
    {Z : Subgroup W} {π : M.Gam →* ↥L} (hr : M.RealizesVia L (commV L) Z π)
    (hcard : Nat.card (commV L) ≤ 2 ^ 7) : HasGood G := by
  obtain ⟨D, hD⟩ := exists_isFFStarMin hne hJ
  have hDL : D ≤ L := hD.1.1.trans hGL
  obtain ⟨d, hd, hd1⟩ : ∃ d ∈ D, d ≠ 1 := by
    by_contra h
    push Not at h
    exact hD.1.2.1 (eq_bot_iff.2 fun x hx => Subgroup.mem_bot.2 (h x hx))
  have hmove : ∃ u ∈ commV L, ∃ d ∈ D, d u ≠ u := by
    by_contra hcon
    push Not at hcon
    exact hd1 (FFC.faithful_on_of_realizes hM hr d (hDL hd) fun u hu => hcon u hu d hd)
  exact hasGood_of_le_small hW hD hDL hmove hcard

omit [Finite W] in
theorem card_commV_of_nat {d : ℕ} {K : Type} [Field K] [Finite K]
    {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin d) K)} {L : Subgroup (MulAut W)}
    {U Z : Subgroup W}
    {π : (FFModel.nat Γ).Gam →* ↥L} (hr : (FFModel.nat Γ).RealizesVia L U Z π) :
    Nat.card U = Nat.card Z * Nat.card K ^ d := by
  rw [FFC.card_eq_of_realizes rfl hr]
  congr 1
  show Nat.card ↥(⊤ : Subgroup (Multiplicative (Fin d → K))) = _
  rw [Subgroup.card_top, Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_fin]

section Wedge

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

theorem card_wedge4 : Nat.card (Multiplicative (⋀[ZMod 2]^2 (Fin 4 → ZMod 2))) = 2 ^ 6 := by
  rw [Nat.card_congr (Multiplicative.toAdd.trans (Equiv.ofBijective _
    (B5FinWedge.wedgeCoord4_bijective (K := ZMod 2)))), Nat.card_fun, Nat.card_fin, Nat.card_zmod]

omit [Finite W] in
theorem card_commV_of_wedge4 {L : Subgroup (MulAut W)} {U Z : Subgroup W}
    {π : (FFModel.extSq (ZMod 2) 4).Gam →* ↥L}
    (hr : (FFModel.extSq (ZMod 2) 4).RealizesVia L U Z π) :
    Nat.card U = Nat.card Z * 2 ^ 6 := by
  rw [FFC.card_eq_of_realizes rfl hr]
  congr 1
  show Nat.card ↥(⊤ : Subgroup (Multiplicative (⋀[ZMod 2]^2 (Fin 4 → ZMod 2)))) = _
  rw [Subgroup.card_top, card_wedge4]

end Wedge

omit [Finite W] in
theorem card_commV_of_a7Four
    {α : ↥(alternatingGroup (Fin 8)) ≃* Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)}
    {L : Subgroup (MulAut W)} {U Z : Subgroup W} {π : (FFModel.a7Four α).Gam →* ↥L}
    (hr : (FFModel.a7Four α).RealizesVia L U Z π) : Nat.card U = Nat.card Z * 2 ^ 4 := by
  rw [FFC.card_eq_of_realizes rfl hr]
  congr 1
  show Nat.card ↥(⊤ : Subgroup (Multiplicative (Fin 4 → ZMod 2))) = _
  rw [Subgroup.card_top, Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_fin,
    Nat.card_zmod]

end CFSG.Quasithin.B513N
