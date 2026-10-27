module

public import CFSG.LocalAnalysis.StandardType.GGHalfKGCFiveCent
public import CFSG.Assembly.OrderReductions.LinearOrders

public section

namespace CFSG.StandardType

private abbrev ggKGCFiveMain_K : Type := GaloisField 2 1

private abbrev ggKGCFiveMain_V : Type := Fin 6 → ggKGCFiveMain_K

private abbrev ggKGCFiveMain_P : Type := Matrix.SpecialLinearGroup (Fin 6) ggKGCFiveMain_K

private abbrev ggKGCFiveMain_SL4 : Type := Matrix.SpecialLinearGroup (Fin 4) ggKGCFiveMain_K

private abbrev ggKGCFiveMain_Q : Type := ggKGCFiveMain_V ≃ₗ[ggKGCFiveMain_K] ggKGCFiveMain_V

private theorem ggKGCFiveMain_card_SL4 : Nat.card ggKGCFiveMain_SL4 = 20160 := by
  have hprod : (∏ x ∈ Finset.Icc 2 4, ((2 : ℕ) ^ x - 1)) = 315 := by decide
  rw [CFSG.OrderReductions.LinearOrders.card_specialLinear ggKGCFiveMain_K 4 (by norm_num),
    GaloisField.card 2 1 (by norm_num)]
  simp only [pow_one]
  rw [hprod]
  norm_num

theorem ggKGCCentSolv_A_five :
    GGKGCCentSolv (Matrix.SpecialLinearGroup (Fin 6) (GaloisField 2 1)) 5 := by
  change GGKGCCentSolv ggKGCFiveMain_P 5
  unfold GGKGCCentSolv
  intro J k hJ hk3 hk1 hkJ
  let e : Matrix.GeneralLinearGroup (Fin 6) ggKGCFiveMain_K ≃* ggKGCFiveMain_Q :=
    (Matrix.GeneralLinearGroup.toLin (n := Fin 6) (R := ggKGCFiveMain_K)).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv ggKGCFiveMain_K ggKGCFiveMain_V)
  let φ : ggKGCFiveMain_P →* ggKGCFiveMain_Q :=
    e.toMonoidHom.comp Matrix.SpecialLinearGroup.toGL
  have hφinj : Function.Injective φ := by
    intro a b hab
    exact Matrix.SpecialLinearGroup.toGL_injective (e.injective hab)
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨eJ⟩ := hJ
  have hcardJ : Nat.card ↥J = 20160 := by
    rw [Nat.card_congr eJ.toEquiv, ggKGCFiveMain_card_SL4]
  have h5dvd : 5 ∣ Nat.card ↥J := by rw [hcardJ]; norm_num
  obtain ⟨y0, hy0⟩ := exists_prime_orderOf_dvd_card' 5 h5dvd
  let y0P : ggKGCFiveMain_P := (y0 : ↥J)
  have hy0P : orderOf y0P = 5 := by
    rw [Subgroup.orderOf_coe, hy0]
  let y : ggKGCFiveMain_Q := φ y0P
  have hy5 : y ^ 5 = 1 := by
    have hy0P5 : y0P ^ 5 = 1 := by rw [← hy0P]; exact pow_orderOf_eq_one y0P
    calc (φ y0P) ^ 5 = φ (y0P ^ 5) := (map_pow φ y0P 5).symm
      _ = φ 1 := by rw [hy0P5]
      _ = 1 := map_one φ
  have hy1 : y ≠ 1 := by
    intro h
    have h1 : y0P = 1 := hφinj (by rw [show φ y0P = y from rfl, h, map_one])
    have hord : orderOf y0P = 1 := by rw [h1]; exact orderOf_one
    rw [hy0P] at hord
    exact absurd hord (by norm_num)
  have hsol : Group.IsSolvable ↥(Subgroup.centralizer ({y} : Set ggKGCFiveMain_Q)) :=
    ggKGCFive_cent_solvable (V := ggKGCFiveMain_V)
      (by rw [Module.finrank_fin_fun]) y hy5 hy1
  let C : Subgroup ggKGCFiveMain_Q := Subgroup.centralizer ({y} : Set ggKGCFiveMain_Q)
  let f : ↥(Subgroup.centralizer (J : Set ggKGCFiveMain_P)) →* ↥C :=
    (φ.comp (Subgroup.subtype _)).codRestrict C (fun g => by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hgy : ((g : ↥(Subgroup.centralizer (J : Set ggKGCFiveMain_P))) : ggKGCFiveMain_P) * y0P =
          y0P * ((g : ↥(Subgroup.centralizer (J : Set ggKGCFiveMain_P))) : ggKGCFiveMain_P) :=
        ((Subgroup.mem_centralizer_iff.mp g.property) y0P (by exact y0.property)).symm
      calc φ ↑g * y = φ ↑g * φ y0P := rfl
        _ = φ (↑g * y0P) := (map_mul φ _ _).symm
        _ = φ (y0P * ↑g) := by rw [hgy]
        _ = φ y0P * φ ↑g := map_mul φ _ _
        _ = y * φ ↑g := rfl)
  have hfinj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply hφinj
    exact congrArg Subtype.val hab
  haveI : Group.IsSolvable ↥C := hsol
  exact Group.isSolvable_of_isSolvable_injective (f := f) hfinj

end CFSG.StandardType

end
