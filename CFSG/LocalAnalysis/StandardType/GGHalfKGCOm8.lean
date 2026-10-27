module

public import CFSG.LocalAnalysis.StandardType.GGHalfKGCOm8Cent

public section

namespace CFSG.StandardType

open CFSG.RankThree.PartTwo.Sec4.RonanK429F

private theorem ggHalfKGCOm8_zpowers_conj {G : Type*} [Group G] [Finite G]
    {r : ℕ} (hr : r.Prime) {y z : G} (hy : orderOf y = r) (hz : orderOf z = r)
    (hr2 : ¬ r ^ 2 ∣ Nat.card G) :
    ∃ c : G, Subgroup.zpowers y = (Subgroup.zpowers z).map (MulAut.conj c).toMonoidHom := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hsyl : ∀ w : G, orderOf w = r →
      IsPGroup r (Subgroup.zpowers w) ∧ ¬ r ∣ (Subgroup.zpowers w).index := by
    intro w hw
    refine ⟨IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hw, pow_one]), fun hi => ?_⟩
    have hmul := Subgroup.card_mul_index (Subgroup.zpowers w)
    rw [Nat.card_zpowers, hw] at hmul
    apply hr2
    rw [← hmul, pow_two]
    exact Nat.mul_dvd_mul_left r hi
  obtain ⟨hPy, hPyi⟩ := hsyl y hy
  obtain ⟨hPz, hPzi⟩ := hsyl z hz
  let SY : Sylow r G := hPy.toSylow hPyi
  let SZ : Sylow r G := hPz.toSylow hPzi
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq G SZ SY
  refine ⟨c, ?_⟩
  have h1 : ((c • SZ : Sylow r G) : Subgroup G) = (SY : Subgroup G) := by rw [hc]
  rw [Sylow.coe_subgroup_smul] at h1
  exact h1.symm

private theorem ggHalfKGCOm8_centralizer_solvable_of_orderOf_seven
    {y : Om8} (hy : orderOf y = 7) :
    Group.IsSolvable ↥(Subgroup.centralizer ({y} : Set Om8)) := by
  have hbc : ∀ s : GaloisField 2 1, s ^ 2 + (1 : GaloisField 2 1) * s + 1 ≠ 0 := by
    intro s
    rcases gf2_eq_zero_or_one s with rfl | rfl
    · simp
    · rw [one_pow, mul_one]
      intro h
      rw [gf2_one_add_one, zero_add] at h
      exact one_ne_zero h
  have hcard7 : ¬ 7 ^ 2 ∣ Nat.card Om8 := Om8.not_sq_seven_dvd (b := 1) (c := 1) hbc
  obtain ⟨c, hc⟩ := ggHalfKGCOm8_zpowers_conj (G := Om8) (r := 7) (by norm_num)
    (y := y) (z := Om8.y7) hy Om8.orderOf_y7 hcard7
  have hy_mem : y ∈ (Subgroup.zpowers Om8.y7).map (MulAut.conj c).toMonoidHom := by
    rw [← hc]; exact Subgroup.mem_zpowers y
  obtain ⟨w, hw, hwc⟩ := hy_mem
  have hwc' : c * w * c⁻¹ = y := by
    change (MulAut.conj c) w = y
    exact hwc
  have hw7 : orderOf w = 7 := by
    rw [← orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective w, hwc, hy]
  have hzw : Subgroup.zpowers w = Subgroup.zpowers Om8.y7 := by
    apply Subgroup.eq_of_le_of_card_ge
    · exact Subgroup.zpowers_le.mpr hw
    · rw [Nat.card_zpowers, Nat.card_zpowers, hw7, Om8.orderOf_y7]
  have hcent_w : Subgroup.centralizer ({w} : Set Om8) =
      Subgroup.centralizer ({Om8.y7} : Set Om8) := by
    rw [← Subgroup.centralizer_closure ({w} : Set Om8),
        ← Subgroup.centralizer_closure ({Om8.y7} : Set Om8),
        ← Subgroup.zpowers_eq_closure w, ← Subgroup.zpowers_eq_closure Om8.y7, hzw]
  have hmem : ∀ x : ↥(Subgroup.centralizer ({y} : Set Om8)),
      c⁻¹ * (x : Om8) * c ∈ Subgroup.centralizer ({w} : Set Om8) := by
    intro x
    have hx : (x : Om8) * y = y * (x : Om8) :=
      Subgroup.mem_centralizer_singleton_iff.mp x.2
    have hx' : (x : Om8) * (c * w * c⁻¹) = (c * w * c⁻¹) * (x : Om8) := by
      rw [hwc']; exact hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (c⁻¹ * (x : Om8) * c) * w
        = c⁻¹ * ((x : Om8) * (c * w * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * w * c⁻¹) * (x : Om8)) * c := by rw [hx']
      _ = w * (c⁻¹ * (x : Om8) * c) := by group
  let f : ↥(Subgroup.centralizer ({y} : Set Om8)) →*
      ↥(Subgroup.centralizer ({w} : Set Om8)) :=
    { toFun := fun x => ⟨c⁻¹ * (x : Om8) * c, hmem x⟩
      map_one' := by ext; simp
      map_mul' := by
        intro a b
        apply Subtype.ext
        show c⁻¹ * ((a : Om8) * (b : Om8)) * c =
          (c⁻¹ * (a : Om8) * c) * (c⁻¹ * (b : Om8) * c)
        group }
  haveI : Group.IsSolvable ↥(Subgroup.centralizer ({w} : Set Om8)) := by
    rw [hcent_w]
    exact ggKGCOm8_cent_y7_solvable
  refine Group.isSolvable_of_isSolvable_injective (f := f) ?_
  intro a b hab
  apply Subtype.ext
  have h2 : c⁻¹ * (a : Om8) * c = c⁻¹ * (b : Om8) * c := congrArg Subtype.val hab
  calc (a : Om8) = c * (c⁻¹ * (a : Om8) * c) * c⁻¹ := by group
    _ = c * (c⁻¹ * (b : Om8) * c) * c⁻¹ := by rw [h2]
    _ = (b : Om8) := by group

theorem ggKGCCentSolv_Om8 : GGKGCCentSolv CFSG.RankThree.PartTwo.Sec4.RonanK429F.Om8 5 := by
  intro J k hJ _hk3 _hk1 _hkcent
  obtain ⟨e⟩ := hJ
  have hcard : Nat.card (Matrix.SpecialLinearGroup (Fin 4) (GaloisField 2 1)) = 20160 := by
    rw [CFSG.OrderReductions.LinearOrders.card_specialLinear (GaloisField 2 1) 4 (by norm_num),
      GaloisField.card 2 1 (by norm_num)]
    decide +kernel
  have hcardJ : Nat.card ↥J = 20160 := by
    rw [Nat.card_congr e.toEquiv]
    change Nat.card (Matrix.SpecialLinearGroup (Fin 4) (GaloisField 2 1)) = 20160
    exact hcard
  have hdvd7 : 7 ∣ Nat.card ↥J := by rw [hcardJ]; norm_num
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨yJ, hyJ⟩ := exists_prime_orderOf_dvd_card' (G := ↥J) 7 hdvd7
  let y : Om8 := (yJ : Om8)
  have hy : orderOf y = 7 := by
    change orderOf ((yJ : Om8)) = 7
    rw [Subgroup.orderOf_coe, hyJ]
  have hy_mem : y ∈ J := yJ.2
  have hle : Subgroup.centralizer (J : Set Om8) ≤ Subgroup.centralizer ({y} : Set Om8) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp hx y hy_mem).symm
  haveI : Group.IsSolvable ↥(Subgroup.centralizer ({y} : Set Om8)) :=
    ggHalfKGCOm8_centralizer_solvable_of_orderOf_seven hy
  exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
    (Subgroup.inclusion_injective hle)

end CFSG.StandardType

end
