module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFixHalfAlt
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFixHalfSL
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFixHalfGen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFixHalfSum
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFixHalfDim
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5Cfg
import CFSG.Adapters.StatedSLPerfect

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W]

private theorem s16fh_rk_le_of_card_le {Z : Subgroup W} {m : ℕ} (h : Nat.card ↥Z ≤ 2 ^ m) :
    rk ↥Z ≤ m := by
  change padicValNat 2 (Nat.card ↥Z) ≤ m
  calc padicValNat 2 (Nat.card ↥Z) ≤ Nat.log 2 (Nat.card ↥Z) := padicValNat_le_nat_log _
    _ ≤ Nat.log 2 (2 ^ m) := Nat.log_mono_right h
    _ = m := Nat.log_pow (by norm_num) m

private theorem s16fh_isPerfect_of_alt {G : Type*} [Group G] {n : ℕ} (hn : 5 ≤ n)
    (e : G ≃* ↥(alternatingGroup (Fin n))) : Group.IsPerfect G := by
  have h : Group.IsPerfect ↥(alternatingGroup (Fin n)) :=
    Group.isPerfect_def.2 (commutator_alternatingGroup_eq_top (α := Fin n)
      (by simpa [Nat.card_fin] using hn))
  exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective

theorem s16fh_row_L3 [Finite W] (hW2 : ∀ w : W, w ^ 2 = 1)
    {L : Subgroup (MulAut W)}
    (h : s16h_H5RowL3 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L)) :
    3 * rk ↥(commSub ⊤ L ⊓ fixV L) ≤ rk ↥(commSub ⊤ L) := by
  obtain ⟨k, -, hsl, hsum⟩ := h
  obtain ⟨K₀, hK₀f, -, -, ⟨e⟩⟩ := hsl
  letI := hK₀f
  haveI : Group.IsPerfect ↥(StatedSL 3 K₀) :=
    CFSG.Open.StatedAPI.isPerfect_statedSL_of_three_le (by norm_num) K₀
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
        obtain ⟨K, hKf, hKfin, hKcard, hreal⟩ := hI
        letI := hKf
        letI := hKfin
        exact ⟨FFModel.nat (StatedSL 3 K), s16fh_cover_sl_three (by simpa using hKcard),
          hreal, s16fh_commSub_sup_nat (by norm_num) hreal⟩) hsum
  have hZk : rk ↥(commSub ⊤ L ⊓ fixV L) ≤ k := s16fh_rk_le_of_card_le (by simpa using hcard)
  have hdim : rk ↥(commSub ⊤ L ⊓ fixV L) + k * 3 ≤ rk ↥(commSub ⊤ L) :=
    s16fh_rk_sumOfNat_ge (N := fun H U Z => BinaryNaturalSL H U Z 3 1) hsum
      (fun I hI => by
        obtain ⟨K, hKf, hKfin, hKcard, hreal⟩ := hI
        letI := hKf
        letI := hKfin
        simpa using s16fh_rk_of_realizes_nat (d := 3) (a := 1) hKcard hreal)
  omega

theorem s16fh_row_SL2_three [Finite W] (hW2 : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)}
    (h : s16h_H5RowSL2 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 3) :
    3 * rk ↥(commSub ⊤ L ⊓ fixV L) ≤ rk ↥(commSub ⊤ L) := by
  obtain ⟨-, hBN⟩ := h
  obtain ⟨K, hKf, hKfin, hKcard, hreal⟩ := hBN
  letI := hKf
  letI := hKfin
  obtain ⟨π, hπ⟩ := hreal
  have hK4 : 4 ≤ Nat.card K := by rw [hKcard]; norm_num
  haveI : Group.IsPerfect (FFModel.nat (StatedSL 2 K)).Gam :=
    CFSG.Open.StatedAPI.isPerfect_statedSL_two_of_four_le_card hK4
  have hperf : Group.IsPerfect ↥L := Group.IsPerfect.ofSurjective (f := π) hπ.1
  have hmem : ∀ l ∈ L, ∀ y ∈ (⊤ : Subgroup W), l y ∈ (⊤ : Subgroup W) :=
    fun l _ y _ => Subgroup.mem_top (l y)
  have hUinv : ∀ l ∈ L, ∀ u ∈ commSub ⊤ L, l u ∈ commSub ⊤ L :=
    s16jp_commSub_stable (L := L) (Y := ⊤) hmem
  have hUc : commSub (commSub ⊤ L) L = commSub ⊤ L :=
    s16jp_commSub_commSub hperf (Y := ⊤) hmem
  have hcard : Nat.card ↥(commSub ⊤ L ⊓ fixV L) ≤ 2 ^ 3 :=
    s16fh_cover_restrict (s16fh_cover_sl_two (n := 3) (by norm_num) hKcard)
      hW2 hUinv hUc inf_le_right ⟨π, hπ⟩
  have hZk : rk ↥(commSub ⊤ L ⊓ fixV L) ≤ 3 := s16fh_rk_le_of_card_le hcard
  have hdim : rk ↥(commSub ⊤ L) = rk ↥(commSub ⊤ L ⊓ fixV L) + 2 * 3 :=
    s16fh_rk_of_realizes_nat (d := 2) (a := 3) hKcard ⟨π, hπ⟩
  omega

theorem s16fh_row_SL2_two [Finite W] {L : Subgroup (MulAut W)}
    (h : s16h_H5RowSL2 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 2)
    (hZ : rk ↥(commSub ⊤ L ⊓ fixV L) ≤ 2) :
    3 * rk ↥(commSub ⊤ L ⊓ fixV L) ≤ rk ↥(commSub ⊤ L) := by
  obtain ⟨-, hBN⟩ := h
  obtain ⟨K, hKf, hKfin, hKcard, hreal⟩ := hBN
  letI := hKf
  letI := hKfin
  have hdim : rk ↥(commSub ⊤ L) = rk ↥(commSub ⊤ L ⊓ fixV L) + 2 * 2 :=
    s16fh_rk_of_realizes_nat (d := 2) (a := 2) hKcard hreal
  omega

theorem s16fh_row_alt [Finite W] (hW2 : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)}
    {U Z : Subgroup W} {n : ℕ} (hn6 : 6 ≤ n) (hn8 : n ≤ 8) (hAlt : IsAlt ↥L n)
    (hUinv : ∀ l ∈ L, ∀ u ∈ U, l u ∈ U) (hUc : commSub U L = U) (hZ : Z ≤ fixV L)
    (hsum : SumOfNat (fun H U Z => AlternatingNatural H U Z n) L U Z 2) : rk ↥Z ≤ 2 := by
  interval_cases n
  · have hperf : Group.IsPerfect ↥L := by
      obtain ⟨e⟩ := hAlt
      exact s16fh_isPerfect_of_alt (by norm_num) e
    have hcard : Nat.card ↥Z ≤ 2 ^ (1 * 2) :=
      s16fh_sum_cover hW2 hperf hUinv hUc hZ
        (N := fun H U Z => AlternatingNatural H U Z 6) (k := 2) (c := 1)
        (fun I hI => ⟨FFModel.altDn 6, s16fh_cover_alt_six, hI,
          s16fh_commSub_sup_alt (by norm_num) hI⟩) hsum
    exact s16fh_rk_le_of_card_le (by simpa using hcard)
  · have hperf : Group.IsPerfect ↥L := by
      obtain ⟨e⟩ := hAlt
      exact s16fh_isPerfect_of_alt (by norm_num) e
    have hcard : Nat.card ↥Z ≤ 2 ^ (0 * 2) :=
      s16fh_sum_cover hW2 hperf hUinv hUc hZ
        (N := fun H U Z => AlternatingNatural H U Z 7) (k := 2) (c := 0)
        (fun I hI => ⟨FFModel.altDn 7, s16fh_cover_alt_seven, hI,
          s16fh_commSub_sup_alt (by norm_num) hI⟩) hsum
    refine s16fh_rk_le_of_card_le ?_
    calc Nat.card ↥Z ≤ 2 ^ (0 * 2) := hcard
      _ = 1 := by norm_num
      _ ≤ 2 ^ 2 := by norm_num
  · have hperf : Group.IsPerfect ↥L := by
      obtain ⟨e⟩ := hAlt
      exact s16fh_isPerfect_of_alt (by norm_num) e
    have hcard : Nat.card ↥Z ≤ 2 ^ (1 * 2) :=
      s16fh_sum_cover hW2 hperf hUinv hUc hZ
        (N := fun H U Z => AlternatingNatural H U Z 8) (k := 2) (c := 1)
        (fun I hI => ⟨FFModel.altDn 8, s16fh_cover_alt_eight, hI,
          s16fh_commSub_sup_alt (by norm_num) hI⟩) hsum
    exact s16fh_rk_le_of_card_le (by simpa using hcard)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
