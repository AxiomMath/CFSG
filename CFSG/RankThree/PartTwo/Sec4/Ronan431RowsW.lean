module

public import CFSG.RankThree.PartTwo.Sec4.Ronan431Open
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowVU43
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.Sec4.RonanK432L2Outer

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan431

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.GorensteinWalter
open CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly.RankThreeEven (projSL projSU)

theorem noCfgS431_of_inner_dvd {S : Type} [Group S] [Finite S] (hZ : Subgroup.center S = ⊥)
    (hin : ∀ τ : MulAut S, τ ^ 3 = 1 → τ ∈ (MulAut.conj : S →* MulAut S).range) {N : ℕ}
    (hC : ∀ x : S, orderOf x = 3 → Nat.card (Subgroup.centralizer ({x} : Set S)) ∣ N)
    (hN : ¬ 360 ∣ N) : NoCfgS431 S := by
  intro A σ K hc
  have h3 : σ ^ 3 = 1 := hc.isE27.1.2 σ hc.mem
  obtain ⟨s, rfl⟩ := hin σ h3
  have hs3 : s ^ 3 = 1 := by
    have h3' : MulAut.conj (s ^ 3) = 1 := by rw [map_pow]; exact h3
    have hmem : s ^ 3 ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h := congrArg (fun τ : MulAut S => τ g) h3'
      simp only [MulAut.conj_apply, MulAut.one_apply] at h
      calc g * s ^ 3 = s ^ 3 * g * (s ^ 3)⁻¹ * s ^ 3 := by rw [h]
        _ = s ^ 3 * g := by group
    rw [hZ, Subgroup.mem_bot] at hmem
    exact hmem
  have hs1 : s ≠ 1 := fun h => hc.ne_one (by rw [h, map_one])
  have hso : orderOf s = 3 := orderOf_eq_prime hs3 hs1
  have hle : K ≤ Subgroup.centralizer ({s} : Set S) := by
    rw [← RonanK429.RowV.autFix_conj_eq_centralizer]
    exact hc.le_autFix
  have hK : Nat.card K ∣ N := (Subgroup.card_dvd_of_le hle).trans (hC s hso)
  apply hN
  rw [card_eq_of_isType431 hc.isType] at hK
  exact (Dvd.intro _ rfl).trans hK

theorem rowSOf431_one_27 : RowSOf431 (projSL 2 (GaloisField 3 3)) := by
  refine rowSOf431_of_noCfg fun S _ _ _ _ ⟨eS⟩ => ?_
  have e' : S ≃* PSL2 (GaloisField 3 3) := eS.trans (projSLEquivPSL _)
  apply noCfgS431_of_not_five_dvd
  have hc := RonanK432.card_psl2_mul_gcd (GaloisField 3 3)
  rw [← Nat.card_congr e'.toEquiv, GaloisField.card 3 3 (by norm_num)] at hc
  norm_num at hc
  omega

theorem rowSOf431_nine_SU4 : RowSOf431 (projSU 4 3 1) := by
  refine rowSOf431_of_noCfg fun S _ _ hs hna ⟨φ⟩ => ?_
  refine noCfgS431_of_inner_dvd (N := 653184) (RonanK429.RowV.center_eq_bot_of_simple hs hna) ?_
    ?_ (by norm_num)
  · intro τ h3
    have h3' : MulAut.congr φ τ ^ 3 = 1 := by rw [← map_pow, h3, map_one]
    exact (isInnerAut_congr φ τ).mp (cubeInner_of_not_three_dvd_card_outer outU43_holds _ h3')
  · intro x hx
    rw [RonanK429.RowV.card_centralizer_congr φ x]
    exact RonanK429.RowV.card_centralizer_u43_dvd (φ x) (by rw [MulEquiv.orderOf_eq]; exact hx)

theorem k431OpenW : K431OpenW where
  one_27 := rowSOf431_one_27
  nine_SU4 := rowSOf431_nine_SU4

end CFSG.RankThree.PartTwo.Sec4.Ronan431
