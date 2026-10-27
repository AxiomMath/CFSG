module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Fix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFixHalfSum
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFixHalfSL
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFixHalfGen
public import CFSG.Adapters.StatedSLPerfect
public import CFSG.Quasithin.Background.JonesParshallBasic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG CFSG.Quasithin CFSG.Open Subgroup CFSG.Quasithin.JonesParshall Matrix

variable {W : Type} [CommGroup W]

private theorem s16h_e3_l3_rk_le_of_card_le {Z : Subgroup W} {m : ℕ}
    (h : Nat.card ↥Z ≤ 2 ^ m) : rk ↥Z ≤ m := by
  change padicValNat 2 (Nat.card ↥Z) ≤ m
  calc padicValNat 2 (Nat.card ↥Z) ≤ Nat.log 2 (Nat.card ↥Z) := padicValNat_le_nat_log _
    _ ≤ Nat.log 2 (2 ^ m) := Nat.log_mono_right h
    _ = m := Nat.log_pow (by norm_num) m

theorem s16h_e3_l3_sumOfNat_fix_le [Finite W] (hW2 : ∀ w : W, w ^ 2 = 1)
    {L : Subgroup (MulAut W)} {k : ℕ}
    (hL3 : s16h_H5L3Sum L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) k) :
    rk ↥(commSub ⊤ L ⊓ fixV L) ≤ k := by
  obtain ⟨hsl, hsum⟩ := hL3
  obtain ⟨K, hKf, -, hKcard, ⟨e⟩⟩ := hsl
  letI := hKf
  haveI : Group.IsPerfect ↥(StatedSL 3 K) :=
    CFSG.Open.StatedAPI.isPerfect_statedSL_of_three_le (by norm_num) K
  have hperf : Group.IsPerfect ↥L :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hmem : ∀ l ∈ L, ∀ y ∈ (⊤ : Subgroup W), l y ∈ (⊤ : Subgroup W) :=
    fun l _ y _ => Subgroup.mem_top (l y)
  have hUinv : ∀ l ∈ L, ∀ u ∈ commSub ⊤ L, l u ∈ commSub ⊤ L :=
    s16jp_commSub_stable (L := L) (Y := ⊤) hmem
  have hUc : commSub (commSub ⊤ L) L = commSub ⊤ L :=
    s16jp_commSub_commSub hperf (Y := ⊤) hmem
  have hcard : Nat.card ↥(commSub ⊤ L ⊓ fixV L) ≤ 2 ^ (1 * k) :=
    s16fh_sum_cover hW2 hperf hUinv hUc inf_le_right
      (N := fun H U Z => BinaryNaturalSL H U Z 3 1) (k := k) (c := 1)
      (fun I hI => by
        obtain ⟨K', hK'f, hK'fin, hK'card, hreal⟩ := hI
        letI := hK'f
        letI := hK'fin
        exact ⟨FFModel.nat (StatedSL 3 K'), s16fh_cover_sl_three (by simpa using hK'card),
          hreal, s16fh_commSub_sup_nat (by norm_num) hreal⟩) hsum
  exact s16h_e3_l3_rk_le_of_card_le (by simpa using hcard)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
