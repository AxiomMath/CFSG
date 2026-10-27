module

public import CFSG.Quasithin.H13.VolIAltCoverChain
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFixHalfSum
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFixHalfDim
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFixHalfGen
public import CFSG.Quasithin.Background.H47WBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {X : Type} [CommGroup X]

theorem s16nt_cover_altDn_two {n : ℕ} (hn : 3 ≤ n) : S16BoundCover (FFModel.altDn n) 2 := by
  intro W _ _ hW2 H Z hZ hcomm hreal
  calc Nat.card ↥Z ≤ 4 :=
        CFSG.Quasithin.H13.VolI.card_le_four_of_altNaturalCover hn W hW2 H Z hZ hcomm hreal
    _ = 2 ^ 2 := by norm_num

theorem s16nt_rk_of_realizes_altDn [Finite X] {n : ℕ} (hn : 1 ≤ n) {L : Subgroup (MulAut X)}
    {I Z : Subgroup X} (h : (FFModel.altDn n).Realizes L I Z) :
    rk ↥I = rk ↥Z + if Even n then n - 2 else n - 1 := by
  obtain ⟨π, hπ⟩ := h
  have h1 : Nat.card ↥I = Nat.card (FFModel.altDn n).Mod * Nat.card ↥Z :=
    CFSG.Quasithin.G64.RealizesVia.card_eq hπ
  have h2 : Nat.card (FFModel.altDn n).Mod = 2 ^ (if Even n then n - 2 else n - 1) := by
    have h : Nat.card (FFModel.altDn n).Mod = if Even n then 2 ^ (n - 2) else 2 ^ (n - 1) :=
      Explicit.card_dn_sec hn .alternating
    rw [h]
    split_ifs <;> rfl
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpow : (2 : ℕ) ^ (if Even n then n - 2 else n - 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hZ : Nat.card ↥Z ≠ 0 := Nat.card_pos.ne'
  calc rk ↥I = padicValNat 2 (Nat.card ↥I) := rfl
    _ = padicValNat 2 (2 ^ (if Even n then n - 2 else n - 1) * Nat.card ↥Z) := by rw [h1, h2]
    _ = (if Even n then n - 2 else n - 1) + padicValNat 2 (Nat.card ↥Z) := by
        rw [padicValNat.mul hpow hZ, padicValNat.prime_pow]
    _ = rk ↥Z + if Even n then n - 2 else n - 1 := by unfold rk; omega

private theorem s16nt_five_le_of_isAlt {G : Type} [Group G] {n : ℕ} (hAlt : IsAlt G n)
    (hq : CFSG.Open.IsQuasisimple G) : 5 ≤ n := by
  by_contra hn
  obtain ⟨e⟩ := hAlt
  have : Group.IsPerfect G := ⟨hq.1⟩
  have : Nontrivial G := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    have : Subsingleton (G ⧸ center G) := by
      constructor
      intro a b
      induction a using QuotientGroup.induction_on
      induction b using QuotientGroup.induction_on
      congr 1
      exact Subsingleton.elim _ _
    exact (not_nontrivial_iff_subsingleton.2 this) hq.2.toNontrivial
  have hsolv : Group.IsSolvable ↥(alternatingGroup (Fin n)) :=
    alternatingGroup.isSolvable (by rw [Nat.card_fin]; omega)
  have : Group.IsSolvable G := solvable_of_solvable_injective (f := e.toMonoidHom) e.injective
  exact Group.IsPerfect.not_isSolvable G this

private theorem s16nt_four_le_dim {n : ℕ} (hn : 5 ≤ n) :
    4 ≤ if Even n then n - 2 else n - 1 := by
  split_ifs with he
  · obtain ⟨r, rfl⟩ := he
    omega
  · omega

theorem s16nt_row_alt_sum [Finite X] (hX : ∀ x : X, x ^ 2 = 1) {L : Subgroup (MulAut X)}
    (hL : CFSG.Open.IsQuasisimple ↥L) {n k : ℕ} (hAlt : IsAlt ↥L n)
    (hsum : SumOfNat (fun H U Z => AlternatingNatural H U Z n) L (commSub ⊤ L)
      (commSub ⊤ L ⊓ fixV L) k) :
    3 * rk ↥(commSub ⊤ L ⊓ fixV L) ≤ rk ↥(commSub ⊤ L) := by
  have hn5 : 5 ≤ n := s16nt_five_le_of_isAlt hAlt hL
  have hperf : Group.IsPerfect ↥L := ⟨hL.1⟩
  have hX' : ∀ l ∈ L, ∀ y ∈ (⊤ : Subgroup X), l y ∈ (⊤ : Subgroup X) := fun _ _ y _ => mem_top _
  have hcard : Nat.card ↥(commSub ⊤ L ⊓ fixV L) ≤ 2 ^ (2 * k) :=
    s16fh_sum_cover hX hperf (s16jp_commSub_stable hX') (s16jp_commSub_commSub hperf hX')
      inf_le_right (N := fun H U Z => AlternatingNatural H U Z n) (k := k) (c := 2)
      (fun I hI => ⟨FFModel.altDn n, s16nt_cover_altDn_two (by omega), hI,
        s16fh_commSub_sup_alt (by omega) hI⟩) hsum
  set d := if Even n then n - 2 else n - 1 with hd_def
  have hrk := s16fh_rk_sumOfNat_ge hsum (m := d)
    (fun I hI => s16nt_rk_of_realizes_altDn (by omega) hI)
  have hZ := CFSG.Quasithin.H47W.rk_le_of_card_le hX _ hcard
  have hd : 4 ≤ d := s16nt_four_le_dim hn5
  nlinarith

theorem s16nt_row_alt_irr [Finite X] (hX : ∀ x : X, x ^ 2 = 1) {L : Subgroup (MulAut X)}
    (hL : CFSG.Open.IsQuasisimple ↥L) (hirr : commSub ⊤ L ∈ irrSet L) {n : ℕ}
    (hAlt : IsAlt ↥L n)
    (hnat : AlternatingNatural L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) n) :
    3 * rk ↥(commSub ⊤ L ⊓ fixV L) ≤ rk ↥(commSub ⊤ L) := by
  have hn5 : 5 ≤ n := s16nt_five_le_of_isAlt hAlt hL
  obtain ⟨hUc, -, hUst, -, -⟩ := hirr
  have hcard : Nat.card ↥(commSub ⊤ L ⊓ fixV L) ≤ 2 ^ 2 :=
    s16fh_cover_restrict (s16nt_cover_altDn_two (by omega)) hX hUst hUc inf_le_right hnat
  set d := if Even n then n - 2 else n - 1 with hd_def
  have hrk : rk ↥(commSub ⊤ L) = rk ↥(commSub ⊤ L ⊓ fixV L) + d :=
    s16nt_rk_of_realizes_altDn (by omega) hnat
  have hZ := CFSG.Quasithin.H47W.rk_le_of_card_le hX _ hcard
  have hd : 4 ≤ d := s16nt_four_le_dim hn5
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
