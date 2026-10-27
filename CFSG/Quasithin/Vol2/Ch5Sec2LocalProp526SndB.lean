module

public import CFSG.Quasithin.Vol2.Ch5Sec2LocalProp526SndA
public import CFSG.Quasithin.Recognition.CertTits
public import CFSG.Quasithin.Recognition.CertU33AutBound
public import CFSG.Quasithin.Recognition.CertU33Simple
public import CFSG.Quasithin.Vol2.Ch5Sec1L34J2Aut
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAut
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13

open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf

namespace Sec526

theorem factorization_two_of_eq {n k m : ℕ} (h : n = 2 ^ k * m) (hm : ¬ 2 ∣ m) :
    n.factorization 2 = k := by
  have hm0 : m ≠ 0 := fun h0 => hm (h0 ▸ dvd_zero 2)
  rw [h, Nat.factorization_mul (pow_ne_zero _ two_ne_zero) hm0, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hm, add_zero, Nat.Prime.factorization_pow Nat.prime_two]
  simp

theorem fac_l32
    (Y : Type) [Group Y] (hY : IsLieOverTwo .PSL 3 1 Y) : (Nat.card Y).factorization 2 = 3 := by
  rw [(factorization_of_lieModel (adm_psl3 le_rfl) hY).2]
  rfl

theorem fac_sp42 (Y : Type) [Group Y] (hY : IsSp4Over 1 Y) : (Nat.card Y).factorization 2 = 4 := by
  rcases hY with ⟨-, ⟨e⟩⟩ | ⟨h, -⟩
  · have h720 : Nat.card ↥(StatedSp 2 (ZMod 2)) = 720 := by
      rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, Nat.card_zmod,
        show Finset.Icc 1 2 = {1, 2} by decide, Finset.prod_pair (by norm_num)]
      norm_num
    rw [Nat.card_congr e.toEquiv, h720]
    exact factorization_two_of_eq (m := 45) (by norm_num) (by norm_num)
  · omega

theorem fac_tits (Y : Type) [Group Y]
    (hY : Nonempty (Y ≃* CFSG.Open.quasithinTits)) : (Nat.card Y).factorization 2 = 11 := by
  obtain ⟨e⟩ := hY
  rw [Nat.card_congr e.toEquiv, card_quasithinTits]
  exact factorization_two_of_eq (m := 8775) (by norm_num) (by norm_num)

theorem card_psu3_three_one :
    Nat.card (CFSG.Open.PSU3 3 1) = 6048 := by
  obtain ⟨e⟩ := u33Pres_mulEquiv_PSU3
  rw [← Nat.card_congr e.toEquiv, card_u33Pres]

theorem fac_u33 (Y : Type) [Group Y]
    (hY : Nonempty (Y ≃* CFSG.Open.PSU3 3 1)) : (Nat.card Y).factorization 2 = 5 := by
  obtain ⟨e⟩ := hY
  rw [Nat.card_congr e.toEquiv, card_psu3_three_one]
  exact factorization_two_of_eq (m := 189) (by norm_num) (by norm_num)

theorem fac_j2 (Y : Type) [Group Y]
    (hY : Nonempty (Y ≃* CFSG.Open.quasithinJ2)) : (Nat.card Y).factorization 2 = 7 := by
  obtain ⟨e⟩ := hY
  rw [Nat.card_congr (e.trans quasithinJ2MulEquivNative).toEquiv, CFSG.Sporadic.J2.card_J2]
  exact factorization_two_of_eq (m := 4725) (by norm_num) (by norm_num)

theorem fac_autj2 (Y : Type)
    [Group Y] (hY : Nonempty (Y ≃* MulAut CFSG.Open.quasithinJ2)) :
    (Nat.card Y).factorization 2 = 8 := by
  obtain ⟨e⟩ := hY
  rw [Nat.card_congr e.toEquiv, card_mulAut_quasithinJ2]
  exact factorization_two_of_eq (m := 4725) (by norm_num) (by norm_num)

theorem fac_m12 (Y : Type) [Group Y]
    (hY : Nonempty (Y ≃* CFSG.Open.quasithinM12)) : (Nat.card Y).factorization 2 = 6 := by
  obtain ⟨e⟩ := hY
  have h : Nat.card ↥CFSG.Open.quasithinM12 = 95040 := CFSG.Sporadic.Mathieu.card_M12
  rw [Nat.card_congr e.toEquiv, h]
  exact factorization_two_of_eq (m := 1485) (by norm_num) (by norm_num)

theorem fac_autm12
    (Y : Type) [Group Y] (hY : Nonempty (Y ≃* MulAut CFSG.Open.quasithinM12)) :
    (Nat.card Y).factorization 2 = 7 := by
  obtain ⟨e⟩ := hY
  have h : Nat.card (MulAut ↥CFSG.Open.quasithinM12) = 190080 := by
    rw [← CFSG.ComponentClassification.M12Cover.card_autModel]
    exact (Nat.card_congr CFSG.ComponentClassification.M12Cover.autModelEquiv.toEquiv).symm
  rw [Nat.card_congr e.toEquiv, h]
  exact factorization_two_of_eq (m := 1485) (by norm_num) (by norm_num)

theorem card_g22
    (Y : Type) [Group Y] (hY : IsG2Over 1 Y) :
    Nat.card Y = 6048 ∨ Nat.card Y = 12096 := by
  rcases hY with ⟨-, ⟨e⟩⟩ | ⟨h, -⟩
  swap
  · omega
  rw [Nat.card_congr e.toEquiv]
  have hX : Nat.card (CFSG.Open.PSU3 3 1) = 6048 := card_psu3_three_one
  obtain ⟨e'⟩ := u33Pres_mulEquiv_PSU3
  have : IsSimpleGroup (CFSG.Open.PSU3 3 1) := e'.isSimpleGroup_congr.mp isSimpleGroup_u33Pres
  have : Finite (CFSG.Open.PSU3 3 1) := Nat.finite_of_card_ne_zero (by rw [hX]; norm_num)
  have hZ : Subgroup.center (CFSG.Open.PSU3 3 1) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (CFSG.Open.PSU3 3 1)) with
      h | h
    · exact h
    · exfalso
      obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := CFSG.Open.PSU3 3 1) 2
        (by rw [hX]; norm_num)
      have hN : (Subgroup.zpowers g).Normal := ⟨fun n hn x => by
        have hx : x ∈ Subgroup.center (CFSG.Open.PSU3 3 1) := h ▸ Subgroup.mem_top x
        have h1 : x * n * x⁻¹ = n := by
          rw [← Subgroup.mem_center_iff.mp hx n, mul_assoc, mul_inv_cancel]
          exact mul_one n
        rw [h1]
        exact hn⟩
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.zpowers g) with h1 | h1
      · have hg1 : g = 1 := Subgroup.zpowers_eq_bot.mp h1
        rw [hg1, orderOf_one] at hg
        omega
      · have h2 := Nat.card_zpowers g
        rw [h1, Subgroup.card_top, hg, hX] at h2
        omega
  have hinj : Function.Injective (MulAut.conj : CFSG.Open.PSU3 3 1 →* MulAut _) := by
    intro x y hxy
    have hc : x⁻¹ * y ∈ Subgroup.center (CFSG.Open.PSU3 3 1) := by
      rw [Subgroup.mem_center_iff]
      intro z
      have h1 := congrArg (fun φ : MulAut (CFSG.Open.PSU3 3 1) => φ z) hxy
      simp only [MulAut.conj_apply] at h1
      calc z * (x⁻¹ * y) = x⁻¹ * (x * z * x⁻¹) * y := by group
        _ = x⁻¹ * (y * z * y⁻¹) * y := by rw [h1]
        _ = x⁻¹ * y * z := by group
    rw [hZ, Subgroup.mem_bot] at hc
    calc x = x * (x⁻¹ * y) := by rw [hc]; exact (mul_one x).symm
      _ = y := by group
  have : Finite (MulAut (CFSG.Open.PSU3 3 1)) :=
    Finite.of_injective (fun φ : MulAut (CFSG.Open.PSU3 3 1) => (φ : _ → _))
      (fun φ ψ h => MulEquiv.ext (congrFun h))
  have hdvd : 6048 ∣ Nat.card (MulAut (CFSG.Open.PSU3 3 1)) := by
    rw [← hX, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
    exact Subgroup.card_subgroup_dvd_card _
  have hle := card_mulAut_psu3_le
  have hpos : 0 < Nat.card (MulAut (CFSG.Open.PSU3 3 1)) := Nat.card_pos
  obtain ⟨k, hk⟩ := hdvd
  rw [hk] at hle hpos ⊢
  have hk2 : k ≤ 2 := by omega
  interval_cases k <;> simp_all

end Sec526

end CFSG.Quasithin.H13
