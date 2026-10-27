module

public import CFSG.Quasithin.Vol2.Ch3B513NOff
public import CFSG.Quasithin.Vol2.Ch3B513NCase245
public import CFSG.Quasithin.Background.FFC5Case1

public section

namespace CFSG.Quasithin.B513N

open CFSG.Open CFSG.QuasithinUnique

variable {W : Type} [CommGroup W] [Finite W]

theorem b51Hyp_of_case1 (hA21 : AsA21SQTKSection) {G : Subgroup (MulAut W)} (hB53 : B53Hyp G)
    (h1 : B56Case1 G) : B51Hyp G (quasithinGenFitting G) := by
  have hLG : quasithinGenFitting G ≤ G := quasithinGenFitting_le G
  have hq := FFC.isQuotientOfSQTKTauCeti_of_b53 hB53
  have hSQ := FFC.sqtk_of_le hA21 hq hLG h1.1
  exact ⟨by rw [sup_eq_left.2 (FFC.centerOf_le_genFitting G)], h1.1, hSQ, hLG, hB53.1, hB53.2.1⟩

theorem hasGood_of_le_small (hW : ∀ w : W, w ^ 2 = 1) {G L D : Subgroup (MulAut W)}
    (hD : IsFFStarMin G D) (hDL : D ≤ L) (hmove : ∃ u ∈ commV L, ∃ d ∈ D, d u ≠ u)
    (hcard : Nat.card (commV L) ≤ 2 ^ 7) : HasGood G := by
  refine hasGood_of_offender_small hW hD (commV_mono hDL) ?_
  obtain ⟨u, hu, d, hd, hdu⟩ := hmove
  have hlt : fixV D ⊓ commV L < commV L := by
    refine lt_of_le_of_ne inf_le_right fun heq => hdu ?_
    have : u ∈ fixV D ⊓ commV L := by rw [heq]; exact hu
    exact this.1 d hd
  have hdvd : Nat.card ↥(fixV D ⊓ commV L) ∣ Nat.card (commV L) :=
    Subgroup.card_dvd_of_le inf_le_right
  have hlt' : Nat.card ↥(fixV D ⊓ commV L) < Nat.card (commV L) := Subgroup.card_lt_of_lt hlt
  obtain ⟨j, hj⟩ := card_subgroup_two_pow hW (commV L)
  rw [hj] at hdvd hlt' hcard
  obtain ⟨i, hi, hi'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  rw [hi'] at hlt' ⊢
  have hij : i < j := (Nat.pow_lt_pow_iff_right (by norm_num)).1 hlt'
  have hj7 : j ≤ 7 := (Nat.pow_le_pow_iff_right (by norm_num)).1 hcard
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

end CFSG.Quasithin.B513N
