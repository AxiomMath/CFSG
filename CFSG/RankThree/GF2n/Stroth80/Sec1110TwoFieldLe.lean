module

public import CFSG.RankThree.GF2n.Stroth80.Sec1110TwoBound
import CFSG.RankThree.GF2n.Stroth80.Sec1110TwoCenter
import CFSG.RankThree.GF2n.Stroth80.Sec116
import CFSG.LocalAnalysis.SeitzReduction.F4PilotNonsplitSL2
import CFSG.CGT.Timmesfeld75.L2Real
import CFSG.Walter.PSL2Facts.Even
public import CFSG.RankThree.GF2n.Stroth80.Sec112Basic

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] {M Q Z B : Subgroup G}

theorem exists_inv_conj_of_orderOf_two_pow_add_one {X : Type*} [Group X] {x : ℕ} (hx : 1 ≤ x)
    (e : X ≃* CFSG.AGLEmbedding.PSL2GF 2 x) :
    ∃ τ t : X, orderOf τ = 2 ^ x + 1 ∧ orderOf t = 2 ∧ t⁻¹ * τ * t = τ⁻¹ := by
  let ε : X ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 x) :=
    e.trans (CFSG.Timmesfeld.RankOne.psl2EquivSL2 (GaloisField 2 x))
  obtain ⟨A, hA⟩ :=
    CFSG.SeitzReduction.F4Pilot.exists_orderOf_eq_natCard_add_one (K := GaloisField 2 x)
  rw [GaloisField.card 2 x (by omega)] at hA
  obtain ⟨a, ha, haA⟩ := CFSG.CGT.Timmesfeld75.exists_mul_self_eq_one_conj_eq_inv A
  have ha1 : a ≠ 1 := by
    rintro rfl
    rw [one_mul, mul_one] at haA
    have h2 : A ^ 2 = 1 := by
      rw [sq]
      nth_rewrite 2 [haA]
      exact mul_inv_cancel A
    have hdvd := orderOf_dvd_of_pow_eq_one h2
    rw [hA] at hdvd
    have hle : 2 ^ x + 1 ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    have h2x : 2 ≤ 2 ^ x := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ x := Nat.pow_le_pow_right (by norm_num) hx
    omega
  have hao : orderOf a = 2 := orderOf_eq_prime (by rw [sq]; exact ha) ha1
  have hinv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  refine ⟨ε.symm A, ε.symm a, ?_, ?_, ?_⟩
  · rw [MulEquiv.orderOf_eq, hA]
  · rw [MulEquiv.orderOf_eq, hao]
  · rw [← map_inv, hinv, ← map_mul, ← map_mul, haA, map_inv]

theorem Ctx.exists_mem_Ebar_inv_conj_of_lieModel [Finite G]
    [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {x : ℕ}
    (hLm2 : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSL 2 2 x)
    (hcenter : Subgroup.center ↥(Xbar M Q Z B) = ⊥) :
    ∃ d ∈ Ebar M Q Z B, ∃ τ : Mbar M Q, orderOf τ = 2 ^ x + 1 ∧ d⁻¹ * τ * d = τ⁻¹ := by
  obtain ⟨e⟩ := nonempty_xbar_mulEquiv_psl2GF hLm2 hcenter
  have hx2 := two_le_exponent_of_lieModel_psl_two hLm2
  have hx : 1 ≤ x := by omega
  obtain ⟨τ₀, t₀, hτo, hto, hτt⟩ := exists_inv_conj_of_orderOf_two_pow_add_one hx e
  obtain ⟨e₀, he₀⟩ := hc.Ebar_nonempty (exists_isA2_of_lieModel hc hx hLm2 hcenter)
  have he₀X : e₀ ∈ Xbar M Q Z B := Subgroup.subset_closure he₀
  have he₀o : orderOf (⟨e₀, he₀X⟩ : ↥(Xbar M Q Z B)) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact Ctx.orderOf_eq_two_of_mem_Ebar he₀
  have hconj : IsConj (⟨e₀, he₀X⟩ : ↥(Xbar M Q Z B)) t₀ := by
    have h := CFSG.Walter.psl2_even_isConj_of_orderOf_eq_two hx2
      (x := e ⟨e₀, he₀X⟩) (y := e t₀) (by rw [MulEquiv.orderOf_eq]; exact he₀o)
      (by rw [MulEquiv.orderOf_eq]; exact hto)
    simpa using e.symm.toMonoidHom.map_isConj h
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj
  have htE : (t₀ : Mbar M Q) ∈ Ebar M Q Z B := by
    rw [← hg]
    simpa using hc.Ebar_conj he₀ (g : Mbar M Q)
  refine ⟨t₀, htE, τ₀, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe]
    exact hτo
  · simpa using congrArg (fun y : ↥(Xbar M Q Z B) => (y : Mbar M Q)) hτt

theorem dvd_of_two_pow_add_one_dvd_sq_sub_one {x a : ℕ} (hx : 1 ≤ x)
    (h : 2 ^ x + 1 ∣ (2 ^ a) ^ 2 - 1) : x ∣ a := by
  have h1 : 2 ^ x + 1 ∣ 2 ^ (2 * x) - 1 := by
    refine ⟨2 ^ x - 1, ?_⟩
    have e1 : 1 ≤ 2 ^ x := Nat.one_le_two_pow
    have e2 : 1 ≤ 2 ^ (2 * x) := Nat.one_le_two_pow
    zify [e1, e2]
    ring
  have h2 : 2 ^ x + 1 ∣ 2 ^ (2 * a) - 1 := by
    rwa [mul_comm, pow_mul]
  have hg := Nat.dvd_gcd h1 h2
  rw [Nat.pow_sub_one_gcd_pow_sub_one, Nat.gcd_mul_left] at hg
  have hgx : Nat.gcd x a ∣ x := Nat.gcd_dvd_left x a
  have hga : Nat.gcd x a ∣ a := Nat.gcd_dvd_right x a
  have hg0 : 0 < Nat.gcd x a := Nat.gcd_pos_of_pos_left a (by omega)
  set g := Nat.gcd x a
  by_contra hxa
  have hgne : g ≠ x := fun h => hxa (h ▸ hga)
  have h2g : 2 * g ≤ x := by
    obtain ⟨m, hm⟩ := hgx
    have hm2 : 2 ≤ m := by
      rcases m with _ | _ | m
      · omega
      · exact absurd (by omega) hgne
      · omega
    calc 2 * g ≤ m * g := Nat.mul_le_mul_right _ hm2
      _ = x := by rw [mul_comm]; exact hm.symm
  have hpos : 0 < 2 ^ (2 * g) - 1 := by
    have : 2 ≤ 2 ^ (2 * g) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (2 * g) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hle := Nat.le_of_dvd hpos hg
  have : 2 ^ (2 * g) ≤ 2 ^ x := Nat.pow_le_pow_right (by norm_num) h2g
  omega

theorem dvd_of_card_Z_eq_two_pow_of_lieModel [Finite G]
    [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {n x a : ℕ} (hw : Width Q Z n)
    (hLm2 : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSL 2 2 x)
    (hcenter : Subgroup.center ↥(Xbar M Q Z B) = ⊥) (ha : Nat.card Z = 2 ^ a) : x ∣ a := by
  obtain ⟨d, hd, τ, hτo, hτ⟩ := hc.exists_mem_Ebar_inv_conj_of_lieModel hLm2 hcenter
  have hx : 1 ≤ x := (hLm2.admissible).2.1
  have hodd : Odd (orderOf τ) := by
    rw [hτo]
    exact Even.add_one ((Nat.even_pow' (by omega)).mpr even_two)
  have h := stroth_11_6 hc hw hd hτ hodd
  rw [hτo, ha] at h
  exact dvd_of_two_pow_add_one_dvd_sq_sub_one hx h

theorem two_pow_le_card_Z_of_lieModel [Finite G]
    [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {n x : ℕ} (hw : Width Q Z n)
    (hLm2 : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSL 2 2 x)
    (hcenter : Subgroup.center ↥(Xbar M Q Z B) = ⊥) : 2 ^ x ≤ Nat.card Z := by
  obtain ⟨a, -, ha, -⟩ := hc.hyp.cp
  have hdvd := dvd_of_card_Z_eq_two_pow_of_lieModel hc hw hLm2 hcenter ha
  have ha0 : a ≠ 0 := by
    rintro rfl
    have h4 := hc.hyp.q4
    rw [ha] at h4
    norm_num at h4
  rw [ha]
  exact Nat.pow_le_pow_right (by norm_num) (Nat.le_of_dvd (Nat.pos_of_ne_zero ha0) hdvd)

end CFSG.RankThree.GF2n.Stroth80
