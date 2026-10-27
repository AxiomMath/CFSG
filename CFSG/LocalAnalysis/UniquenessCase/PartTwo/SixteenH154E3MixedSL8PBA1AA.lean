module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Table
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8PBA1AAA
public import CFSG.CGT.PushingUpLit.BHS.TwoSixteenAlt
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8PBA1AAA1

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W]

theorem s16h_H5_row_SL2_eight_seven_rank {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t)
    (h : s16h_H5RowSL2 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 3)
    (hZ : commSub ⊤ L ⊓ fixV L ≠ ⊥)
    (hrk : rk ↥(commSub ⊤ L ⊓ fixV L) ≤ 2) :
    ∀ E : Subgroup (MulAut W), E ≤ A ⊓ normalizer (L : Set (MulAut W)) →
      IsElemAbelian 7 E → Nat.card ↥(autSub E (commSub ⊤ L)) ≤ 7 := by
  intro E hE hEab
  have hEAN : autSub E (commSub ⊤ L) ≤
      autSub (A ⊓ normalizer (L : Set (MulAut W))) (commSub ⊤ L) :=
    autSub_mono hE (commSub ⊤ L)
  have hEN : E ≤ normalizer (L : Set (MulAut W)) := fun e he => (mem_inf.mp (hE he)).2
  have hN : autSub E (commSub ⊤ L) ≤
      Subgroup.normalizer (autSub L (commSub ⊤ L) : Set (MulAut ↥(commSub ⊤ L))) :=
    CFSG.CGT.PushingUpLit.BHS.autSub_le_normalizer (E := L) (A := E)
      (U := commSub ⊤ L) hEN
  let φ : autSub E (commSub ⊤ L) →* MulAut ↥(autSub L (commSub ⊤ L)) :=
    (Subgroup.normalizerMonoidHom (autSub L (commSub ⊤ L))).comp
      (Subgroup.inclusion hN)
  have hEab' : IsElemAbelian 7 (autSub E (commSub ⊤ L)) := by
    have h1 := IsElemAbelian.map (hEab.subgroupOf (stabSub (commSub ⊤ L)))
      (resHom (commSub ⊤ L))
    simpa [autSub] using h1
  have hker : φ.ker = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have hxker : (Subgroup.inclusion hN x) ∈
        (Subgroup.normalizerMonoidHom (autSub L (commSub ⊤ L))).ker := by
      rw [MonoidHom.mem_ker]
      simpa [φ] using MonoidHom.mem_ker.mp hx
    rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at hxker
    have hxc : (x : MulAut ↥(commSub ⊤ L)) ∈
        Subgroup.centralizer (autSub L (commSub ⊤ L) : Set (MulAut ↥(commSub ⊤ L))) := by
      simpa using hxker
    have hx7 : (x : MulAut ↥(commSub ⊤ L)) ^ 7 = 1 := hEab'.2 x x.2
    exact Subtype.ext (by
      simpa using s16h_H5_row_SL2_eight_central_seven_triv hc h hZ hrk
        (x : MulAut ↥(commSub ⊤ L)) (hEAN x.2) hxc hx7)
  have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hker
  have hcardEq : Nat.card ↥(autSub E (commSub ⊤ L)) = Nat.card ↥(φ.range) :=
    Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
  have hM : Nat.card (MulAut ↥(autSub L (commSub ⊤ L))) = 1512 :=
    s16h_H5_row_SL2_eight_mulAut_card hc h
  have hdvd : Nat.card ↥(autSub E (commSub ⊤ L)) ∣ 1512 := by
    rw [hcardEq]
    exact (Subgroup.card_subgroup_dvd_card φ.range).trans (by rw [hM])
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card (p := 7)).mp hEab'.isPGroup
  have hm1 : m ≤ 1 := by
    have h7m : 7 ^ m ∣ 1512 := by rw [← hm]; exact hdvd
    by_contra hlt
    have h2 : 2 ≤ m := by omega
    have h49 : (7 : ℕ) ^ 2 ∣ 1512 := dvd_trans (pow_dvd_pow 7 h2) h7m
    norm_num at h49
  rw [hm]
  calc (7 : ℕ) ^ m ≤ 7 ^ 1 := Nat.pow_le_pow_right (by norm_num) hm1
    _ = 7 := pow_one 7

theorem s16h_H5_row_SL2_eight_seven_block {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t)
    (h : s16h_H5RowSL2 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 3)
    (hZ : commSub ⊤ L ⊓ fixV L ≠ ⊥)
    (hrk : rk ↥(commSub ⊤ L ⊓ fixV L) ≤ 2) :
    s16h_BlockBound A L 7 1 := by
  intro E hE hEab
  have hU : E ≤ stabSub (commSub ⊤ L) := by
    intro g hg
    exact CFSG.Quasithin.StabLat.mem_stabSub_commSub
      (mem_stabSub.2 fun _ => by simp) (Subgroup.mem_inf.mp (hE hg)).2
  have hcard := card_autSub_mul (A := E) (U := commSub ⊤ L) hU
  have hb := s16h_H5_row_SL2_eight_seven_rank hc h hZ hrk E hE hEab
  rw [← hcard, pow_one]
  exact Nat.mul_le_mul_right _ hb

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
