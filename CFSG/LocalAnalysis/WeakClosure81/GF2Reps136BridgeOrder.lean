module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136Sec
import CFSG.Quasithin.Background.SmithB42HatA6Model
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSumConv

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps136

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix

variable {W : Type} [CommGroup W] [Finite W]

private theorem w1369_mQuot_eq_of_card {U Z : Subgroup W} {k : ℕ}
    (hcard : Nat.card (Sect U Z) = 2 ^ E3.mQuot U Z)
    (hk : Nat.card (Sect U Z) = 2 ^ k) : E3.mQuot U Z = k :=
  Nat.pow_right_injective (le_refl 2) (hcard.symm.trans hk)

private theorem w1369_isSpn_congr {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {n a : ℕ}
    (h : IsSpn X n a) : IsSpn Y n a := by
  obtain ⟨hn, K, hKf, hKfin, hKcard, ⟨e'⟩⟩ := h
  exact ⟨hn, K, hKf, hKfin, hKcard, ⟨e.symm.trans e'⟩⟩

private theorem w1369_isSpor_congr {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    {s : TauCeti.SporadicName} (h : IsSpor X s) : IsSpor Y s := by
  obtain ⟨f⟩ := h
  exact ⟨e.symm.trans f⟩

private theorem w1369_tripleA6Six_transfer (hw2 : ∀ w : W, w ^ 2 = 1) {U Z : Subgroup W}
    {L : Subgroup (MulAut W)} (hZU : Z ≤ U) (hL : StabPair L U Z) (hf : FaithOn L U Z)
    (hhat : IsHat ↥(secSub U Z L) ↥(alternatingGroup (Fin 6)))
    (hcard : Nat.card (Sect U Z) = 2 ^ 6) : TripleA6Six L U Z := by
  have hperf : Group.IsPerfect ↥(secSub U Z L) := hhat.1.1
  have hZ : Nat.card (Subgroup.center ↥(secSub U Z L)) = 3 := hhat.2.1
  obtain ⟨K, hKf, hKfin, Γ₀, hKcard, hdet, hhatΓ, hcen, hreal⟩ :=
    HatA6.hatA6SixModel (Sect U Z) (sect_exp_two hw2 U Z) hcard (secSub U Z L) hperf hZ
      hhat.2.2
  exact ⟨K, hKf, hKfin, Γ₀, hKcard, hdet, hhatΓ, hcen,
    (realizes_secSub_iff (FFModel.nat Γ₀) hL hZU hf).mp hreal⟩

theorem bridge_rows_order (hw2 : ∀ w : W, w ^ 2 = 1) {U Z : Subgroup W}
    {L : Subgroup (MulAut W)} {m : ℕ} (hZU : Z ≤ U) (hL : StabPair L U Z)
    (hf : FaithOn L U Z) (hirr : IsIrrOn L U Z)
    (h : (IsHat ↥(secSub U Z L) ↥(alternatingGroup (Fin 6)) ∧ Nat.card (Sect U Z) = 2 ^ 6) ∨
      (∃ (S : Type) (_ : Group S), LieModel S .PSU 4 3 1 ∧ IsHat ↥(secSub U Z L) S ∧
        Nat.card (Sect U Z) = 2 ^ 12) ∨
      (IsSpn ↥(secSub U Z L) 6 1 ∧ Nat.card (Sect U Z) = 2 ^ 8) ∨
      (IsSLn ↥(secSub U Z L) 5 1 ∧ Nat.card (Sect U Z) = 2 ^ 10) ∨
      (IsSpor ↥(secSub U Z L) .M22 ∧ Nat.card (Sect U Z) = 2 ^ 10) ∨
      (LieModel ↥(secSub U Z L) .PSL 3 2 2 ∧ Nat.card (Sect U Z) = 2 ^ 9) ∨
      (IsL3 ↥(secSub U Z L) 1 ∧ Nat.card (Sect U Z) = 2 ^ 8)) :
    Conc4_135 L U Z m := by
  have hU2 : IsPGroup 2 ↥U := fun x => ⟨1, by
    apply Subtype.ext
    simpa using hw2 (x : W)⟩
  have hcard : Nat.card (Sect U Z) = 2 ^ E3.mQuot U Z := E3.relIndex_eq_two_pow hU2 Z
  obtain ⟨e⟩ := mulEquiv_secSub hL hf
  unfold Conc4_135
  rcases h with hA6 | hU43 | hSp6 | hSL5 | hM22 | hL34 | hL32
  · obtain ⟨hhat, hc6⟩ := hA6
    iterate 3 right
    exact Or.inl (w1369_tripleA6Six_transfer hw2 hZU hL hf hhat hc6)
  · obtain ⟨S, hSgrp, hLie, hHat, hc12⟩ := hU43
    iterate 4 right
    exact Or.inl ⟨⟨S, hSgrp, hLie, IsHat.of_mulEquiv e.symm hHat⟩,
      w1369_mQuot_eq_of_card hcard hc12⟩
  · obtain ⟨hSp, hc8⟩ := hSp6
    iterate 7 right
    exact Or.inl ⟨w1369_isSpn_congr e.symm hSp, w1369_mQuot_eq_of_card hcard hc8⟩
  · obtain ⟨hSL, hc10⟩ := hSL5
    iterate 8 right
    refine Or.inl ⟨?_, w1369_mQuot_eq_of_card hcard hc10⟩
    obtain ⟨K, hKf, hKfin, hKcard, ⟨eSL⟩⟩ := hSL
    exact s16k_isLn_of_isSLn (by norm_num) ⟨K, hKf, hKfin, hKcard, ⟨e.trans eSL⟩⟩
  · obtain ⟨hSpor, hc10⟩ := hM22
    iterate 9 right
    exact Or.inl ⟨w1369_isSpor_congr e.symm hSpor, w1369_mQuot_eq_of_card hcard hc10⟩
  · obtain ⟨hLie, hc9⟩ := hL34
    iterate 10 right
    exact Or.inl ⟨LieModel.of_mulEquiv e.symm hLie, w1369_mQuot_eq_of_card hcard hc9⟩
  · obtain ⟨hL3, hc8⟩ := hL32
    iterate 11 right
    exact ⟨LieModel.of_mulEquiv e.symm hL3, w1369_mQuot_eq_of_card hcard hc8⟩

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps136
