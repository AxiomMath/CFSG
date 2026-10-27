module

import Mathlib.Data.Nat.Choose.Dvd
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_2_a
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_2_b

namespace CFSG
end CFSG
open CFSG

/-! # Infrastructure for BG Section 4 -/

open scoped commutatorElement

section Main

public theorem CFSG.commutator_pow_left_of_mem_center {G : Type*} [Group G] {x y : G}
    (n : ℕ) (hcomm : ⁅x, y⁆ ∈ Subgroup.center G) :
    ⁅x ^ n, y⁆ = ⁅x, y⁆ ^ n := by
  rcases n with _ | n
  · simp [commutatorElement_def]
  rcases n with _ | n
  · simp
  exact (lemma_4_2_a (G := G) (x := x) (y := y) (n := n + 2) (by omega) hcomm).1

public theorem CFSG.commutator_pow_right_of_mem_center {G : Type*} [Group G] {x y : G}
    (n : ℕ) (hcomm : ⁅x, y⁆ ∈ Subgroup.center G) :
    ⁅x, y ^ n⁆ = ⁅x, y⁆ ^ n := by
  rcases n with _ | n
  · simp [commutatorElement_def]
  rcases n with _ | n
  · simp
  exact (lemma_4_2_a (G := G) (x := x) (y := y) (n := n + 2) (by omega) hcomm).2

public theorem CFSG.commutator_pow_pow_of_mem_center {G : Type*} [Group G] {x y : G}
    (m n : ℕ) (hcomm : ⁅x, y⁆ ∈ Subgroup.center G) :
    ⁅x ^ m, y ^ n⁆ = ⁅x, y⁆ ^ (m * n) := by
  have hleft : ⁅x ^ m, y⁆ = ⁅x, y⁆ ^ m :=
    commutator_pow_left_of_mem_center (G := G) (x := x) (y := y) m hcomm
  have hleft_center : ⁅x ^ m, y⁆ ∈ Subgroup.center G := by
    rw [hleft]
    exact (Subgroup.center G).pow_mem hcomm m
  calc
    ⁅x ^ m, y ^ n⁆ = ⁅x ^ m, y⁆ ^ n :=
      commutator_pow_right_of_mem_center (G := G) (x := x ^ m) (y := y) n hleft_center
    _ = ⁅x, y⁆ ^ (m * n) := by rw [hleft, pow_mul]

public theorem CFSG.zmod_natCast_eq_of_pow_eq_of_orderOf
    {G : Type*} [LeftCancelMonoid G] {g : G} {p a b : ℕ}
    (horder : orderOf g = p) (hpow : g ^ a = g ^ b) :
    (a : ZMod p) = (b : ZMod p) := by
  have hmod : a ≡ b [MOD orderOf g] := by
    exact (pow_eq_pow_iff_modEq (x := g) (m := b) (n := a)).1 hpow
  rw [horder] at hmod
  exact (ZMod.natCast_eq_natCast_iff a b p).2 hmod

public theorem CFSG.commutator_mul_factors_eq_of_commute
    {G : Type*} [Group G] {a b t d : G}
    (htb : Commute t b) (htd : Commute t d) (had : Commute a d) :
    ⁅a * t, b * d⁆ = ⁅a, b⁆ := by
  rw [commutator_mul_right, commutator_mul_left]
  rw [htb.commutator_eq, (had.mul_left htd).commutator_eq]
  simp [mul_assoc]

public theorem CFSG.conjugate_eq_commutator_mul {G : Type*} [Group G] (a b : G) :
    a * b * a⁻¹ = ⁅a, b⁆ * b := by
  rw [commutatorElement_def]
  group

public theorem CFSG.lowerCentralSeries_two_le_center_of_class3
    {R : Type*} [Group R] (hclass : NilpotencyClassLe 3 R) :
    (⊤ : Subgroup R).lowerCentralSeries 2 ≤ Subgroup.center R := by
  letI : Group.IsNilpotent R :=
    (Subgroup.nilpotent_iff_finite_ascending_central_series (G := R)).2
      ⟨3, Subgroup.upperCentralSeries R,
        Subgroup.upperCentralSeries_isAscendingCentralSeries R, hclass⟩
  have hclass' : Group.nilpotencyClass R ≤ 3 :=
    (Subgroup.upperCentralSeries_eq_top_iff_nilpotencyClass_le (G := R)).1 hclass
  have hL3_bot : (⊤ : Subgroup R).lowerCentralSeries 3 = ⊥ :=
    (Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le (G := R)).2 hclass'
  have hcomm_bot : ⁅(⊤ : Subgroup R).lowerCentralSeries 2, (⊤ : Subgroup R)⁆ = ⊥ := by
    simpa [Subgroup.lowerCentralSeries, Nat.succ_eq_add_one] using hL3_bot
  have hcent :
      (⊤ : Subgroup R).lowerCentralSeries 2 ≤
        Subgroup.centralizer ((⊤ : Subgroup R) : Set R) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).1 hcomm_bot
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro y
  exact (Subgroup.mem_centralizer_iff.mp (hcent hx)) y (by simp)

public theorem CFSG.commutator_pow_formula
    {G : Type*} [Group G] {u w : G}
    (htr : ⁅⁅u, w⁆, u⁆ ∈ Subgroup.center G) :
    ∀ n : ℕ, ⁅u ^ n, w⁆ = (⁅⁅u, w⁆, u⁆ ^ Nat.choose n 2)⁻¹ * ⁅u, w⁆ ^ n
  | 0 => by simp
  | n + 1 => by
      let a : G := ⁅u, w⁆
      let c : G := ⁅a, u⁆
      have huc : ⁅u, a⁆ ∈ Subgroup.center G := by
        simpa [a, c, commutatorElement_inv] using (Subgroup.center G).inv_mem htr
      have hca : c ∈ Subgroup.center G := by simpa [a, c] using htr
      have huconj : u ^ n * a * (u ^ n)⁻¹ = (c ^ n)⁻¹ * a := by
        calc
          u ^ n * a * (u ^ n)⁻¹ = a * ⁅u, a⁆ ^ n := by
            rw [pow_mul_eq_mul_pow_commutator_pow_of_mem_center (x := a) (y := u) huc n]
            have hcent : u ^ n * ⁅u, a⁆ ^ n = ⁅u, a⁆ ^ n * u ^ n := by
              exact (Subgroup.mem_center_iff.mp ((Subgroup.center G).pow_mem huc n)) (u ^ n)
            calc
              a * u ^ n * ⁅u, a⁆ ^ n * (u ^ n)⁻¹
                  = a * (u ^ n * ⁅u, a⁆ ^ n) * (u ^ n)⁻¹ := by simp [mul_assoc]
              _ = a * (⁅u, a⁆ ^ n * u ^ n) * (u ^ n)⁻¹ := by rw [hcent]
              _ = a * ⁅u, a⁆ ^ n := by simp [mul_assoc]
          _ = (c ^ n)⁻¹ * a := by
            have hcainv : (c ^ n)⁻¹ ∈ Subgroup.center G := by
              exact (Subgroup.center G).inv_mem ((Subgroup.center G).pow_mem hca n)
            have hua : ⁅u, a⁆ = c⁻¹ := by simp [a, c, commutatorElement_inv]
            calc
              a * ⁅u, a⁆ ^ n = a * (c ^ n)⁻¹ := by rw [hua, inv_pow]
              _ = (c ^ n)⁻¹ * a := by
                exact (Subgroup.mem_center_iff.mp hcainv) a
      calc
        ⁅u ^ (n + 1), w⁆ = u ^ n * ⁅u, w⁆ * (u ^ n)⁻¹ * ⁅u ^ n, w⁆ := by
          rw [pow_succ, commutator_mul_left]
        _ = ((c ^ n)⁻¹ * a) * ((c ^ Nat.choose n 2)⁻¹ * a ^ n) := by
          rw [huconj, commutator_pow_formula htr n]
        _ = (c ^ n)⁻¹ * (c ^ Nat.choose n 2)⁻¹ * (a * a ^ n) := by
          have hkcent : (c ^ Nat.choose n 2)⁻¹ ∈ Subgroup.center G := by
            exact (Subgroup.center G).inv_mem ((Subgroup.center G).pow_mem hca _)
          have hka : a * (c ^ Nat.choose n 2)⁻¹ = (c ^ Nat.choose n 2)⁻¹ * a := by
            exact (Subgroup.mem_center_iff.mp hkcent) a
          calc
            ((c ^ n)⁻¹ * a) * ((c ^ Nat.choose n 2)⁻¹ * a ^ n)
                = (c ^ n)⁻¹ * (a * ((c ^ Nat.choose n 2)⁻¹ * a ^ n)) := by
                    simp [mul_assoc]
            _ = (c ^ n)⁻¹ * ((c ^ Nat.choose n 2)⁻¹ * (a * a ^ n)) := by
                  calc
                    (c ^ n)⁻¹ * (a * ((c ^ Nat.choose n 2)⁻¹ * a ^ n))
                        = (c ^ n)⁻¹ * ((a * (c ^ Nat.choose n 2)⁻¹) * a ^ n) := by
                            simp [mul_assoc]
                    _ = (c ^ n)⁻¹ * (((c ^ Nat.choose n 2)⁻¹ * a) * a ^ n) := by
                            rw [hka]
                    _ = (c ^ n)⁻¹ * ((c ^ Nat.choose n 2)⁻¹ * (a * a ^ n)) := by
                            simp [mul_assoc]
            _ = (c ^ n)⁻¹ * (c ^ Nat.choose n 2)⁻¹ * (a * a ^ n) := by
                  simp [mul_assoc]
        _ = (c ^ (n + Nat.choose n 2))⁻¹ * a ^ (n + 1) := by
          have hcc : (c ^ n)⁻¹ * (c ^ Nat.choose n 2)⁻¹ = (c ^ Nat.choose n 2)⁻¹ * (c ^ n)⁻¹ := by
            exact (Commute.pow_pow_self c n (Nat.choose n 2)).inv_left.inv_right.eq
          rw [hcc]
          simp [pow_succ', pow_add, mul_assoc]
        _ = (c ^ Nat.choose (n + 1) 2)⁻¹ * ⁅u, w⁆ ^ (n + 1) := by
          have hchoose : Nat.choose (n + 1) 2 = n + Nat.choose n 2 := by
            simpa [Nat.add_comm] using Nat.choose_succ_right (n := n + 1) (k := 1) (Nat.succ_pos n)
          simp [a, c, hchoose, pow_succ', pow_add, mul_assoc]

public theorem CFSG.lowerCentralSeries_three_eq_bot_of_class3
    {R : Type*} [Group R] (hclass : NilpotencyClassLe 3 R) :
    (⊤ : Subgroup R).lowerCentralSeries 3 = ⊥ := by
  letI : Group.IsNilpotent R :=
    (Subgroup.nilpotent_iff_finite_ascending_central_series (G := R)).2
      ⟨3, Subgroup.upperCentralSeries R,
        Subgroup.upperCentralSeries_isAscendingCentralSeries R, hclass⟩
  have hclass' : Group.nilpotencyClass R ≤ 3 :=
    (Subgroup.upperCentralSeries_eq_top_iff_nilpotencyClass_le (G := R)).1 hclass
  exact (Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le (G := R)).2 hclass'

public theorem CFSG.commutator_mem_lowerCentralSeries_one
    {R : Type*} [Group R] (x y : R) :
    ⁅x, y⁆ ∈ (⊤ : Subgroup R).lowerCentralSeries 1 := by
  simpa [Subgroup.top_lowerCentralSeries_one] using
    (Subgroup.commutator_mem_commutator (H₁ := (⊤ : Subgroup R)) (H₂ := (⊤ : Subgroup R))
      (by simp : x ∈ (⊤ : Subgroup R)) (by simp : y ∈ (⊤ : Subgroup R)))

public theorem CFSG.triple_commutator_mem_lowerCentralSeries_two
    {R : Type*} [Group R] (x y z : R) :
    ⁅⁅x, y⁆, z⁆ ∈ (⊤ : Subgroup R).lowerCentralSeries 2 := by
  have hxy : ⁅x, y⁆ ∈ (⊤ : Subgroup R).lowerCentralSeries 1 :=
    commutator_mem_lowerCentralSeries_one (R := R) x y
  simpa [Subgroup.lowerCentralSeries, Nat.succ_eq_add_one] using
    (Subgroup.commutator_mem_commutator
      (H₁ := (⊤ : Subgroup R).lowerCentralSeries 1) (H₂ := (⊤ : Subgroup R))
      hxy (by simp : z ∈ (⊤ : Subgroup R)))

public theorem CFSG.commutator_eq_one_of_mem_lowerCentralSeries_two
    {R : Type*} [Group R] (hclass : NilpotencyClassLe 3 R)
    {a b : R} (ha : a ∈ (⊤ : Subgroup R).lowerCentralSeries 2) :
    ⁅a, b⁆ = 1 := by
  have hL3_bot : (⊤ : Subgroup R).lowerCentralSeries 3 = ⊥ :=
    lowerCentralSeries_three_eq_bot_of_class3 (R := R) hclass
  have hab : ⁅a, b⁆ ∈ (⊤ : Subgroup R).lowerCentralSeries 3 := by
    simpa [Subgroup.lowerCentralSeries, Nat.succ_eq_add_one] using
      (Subgroup.commutator_mem_commutator
        (H₁ := (⊤ : Subgroup R).lowerCentralSeries 2) (H₂ := (⊤ : Subgroup R))
        ha (by simp : b ∈ (⊤ : Subgroup R)))
  have hab_bot : ⁅a, b⁆ ∈ (⊥ : Subgroup R) := by
    rw [hL3_bot] at hab
    exact hab
  simpa using hab_bot

public theorem CFSG.mul_pow_formula_front {G : Type*} [Group G] {u v : G}
    (hcu : ⁅⁅v, u⁆, u⁆ ∈ Subgroup.center G)
    (hcv : ⁅⁅v, u⁆, v⁆ ∈ Subgroup.center G) :
    ∀ n : ℕ,
      (u * v) ^ n =
        ⁅⁅v, u⁆, u⁆ ^ Nat.choose (n + 1) 3 *
          (⁅⁅v, u⁆, v⁆ ^ Nat.choose n 3)⁻¹ *
          u ^ n * ⁅v, u⁆ ^ Nat.choose n 2 * v ^ n
  | 0 => by
      norm_num [Nat.choose]
  | n + 1 => by
      let c : G := ⁅v, u⁆
      let d : G := ⁅c, u⁆
      let e : G := ⁅c, v⁆
      let A : ℕ := Nat.choose n 2
      let B : ℕ := Nat.choose (n + 1) 3
      let C : ℕ := Nat.choose n 3
      have hdcent : d ∈ Subgroup.center G := by simpa [c, d] using hcu
      have hecent : e ∈ Subgroup.center G := by simpa [c, e] using hcv
      have hepow_inv_cent : (e ^ A)⁻¹ ∈ Subgroup.center G := by
        exact (Subgroup.center G).inv_mem ((Subgroup.center G).pow_mem hecent _)
      have hdpow_cent : d ^ (A + n) ∈ Subgroup.center G := by
        exact (Subgroup.center G).pow_mem hdcent _
      have h_e_cp : c ^ A * (e ^ A)⁻¹ = (e ^ A)⁻¹ * c ^ A := by
        exact (Subgroup.mem_center_iff.mp hepow_inv_cent) (c ^ A)
      have h_e_un : u ^ n * (e ^ A)⁻¹ = (e ^ A)⁻¹ * u ^ n := by
        exact (Subgroup.mem_center_iff.mp hepow_inv_cent) (u ^ n)
      have hcvu : v ^ n * u = (e ^ Nat.choose n 2)⁻¹ * c ^ n * u * v ^ n := by
        calc
          v ^ n * u = (v ^ n * u * (v ^ n)⁻¹) * v ^ n := by simp [mul_assoc]
          _ = ⁅v ^ n, u⁆ * u * v ^ n := by
            rw [conjugate_eq_commutator_mul]
          _ = ((e ^ Nat.choose n 2)⁻¹ * c ^ n) * u * v ^ n := by
            rw [commutator_pow_formula hcv n]
      have hcu_pow :
          c ^ (A + n) * u = u * c ^ (A + n) * d ^ (A + n) := by
        simpa [c, d] using
          (pow_mul_eq_mul_pow_commutator_pow_of_mem_center (x := u) (y := c) hcu (A + n))
      have hcu_pow' : c ^ (A + n) * u = d ^ (A + n) * u * c ^ (A + n) := by
        have hcd :
            c ^ (A + n) * d ^ (A + n) = d ^ (A + n) * c ^ (A + n) := by
          exact (Subgroup.mem_center_iff.mp hdpow_cent) (c ^ (A + n))
        have hud : u * d ^ (A + n) = d ^ (A + n) * u := by
          exact (Subgroup.mem_center_iff.mp hdpow_cent) u
        calc
          c ^ (A + n) * u = u * c ^ (A + n) * d ^ (A + n) := hcu_pow
          _ = u * (d ^ (A + n) * c ^ (A + n)) := by
                simpa [mul_assoc] using congrArg (fun t => u * t) hcd
          _ = d ^ (A + n) * (u * c ^ (A + n)) := by
                simpa [mul_assoc] using congrArg (fun t => t * c ^ (A + n)) hud
          _ = d ^ (A + n) * u * c ^ (A + n) := by
                simp [mul_assoc]
      have h_eA_cA_cn :
          c ^ A * ((e ^ A)⁻¹ * c ^ n) = (e ^ A)⁻¹ * c ^ A * c ^ n := by
        calc
          c ^ A * ((e ^ A)⁻¹ * c ^ n) = (c ^ A * (e ^ A)⁻¹) * c ^ n := by simp [mul_assoc]
          _ = ((e ^ A)⁻¹ * c ^ A) * c ^ n := by rw [h_e_cp]
          _ = (e ^ A)⁻¹ * c ^ A * c ^ n := by simp [mul_assoc]
      have h_un_eA_cA_cn :
          u ^ n * ((e ^ A)⁻¹ * c ^ A * c ^ n) = ((e ^ A)⁻¹ * u ^ n) * (c ^ A * c ^ n) := by
        calc
          u ^ n * ((e ^ A)⁻¹ * c ^ A * c ^ n) = (u ^ n * (e ^ A)⁻¹) * (c ^ A * c ^ n) := by
            simp [mul_assoc]
          _ = ((e ^ A)⁻¹ * u ^ n) * (c ^ A * c ^ n) := by rw [h_e_un]
      have h_u_d_block :
          ((e ^ C)⁻¹ * (e ^ A)⁻¹) * u ^ n * (d ^ (A + n) * u * c ^ (A + n)) =
            d ^ (A + n) * ((e ^ C)⁻¹ * (e ^ A)⁻¹) * u ^ (n + 1) * c ^ (A + n) := by
        have hudn : u ^ n * d ^ (A + n) = d ^ (A + n) * u ^ n := by
          exact (Subgroup.mem_center_iff.mp hdpow_cent) (u ^ n)
        have hprefixd :
            ((e ^ C)⁻¹ * (e ^ A)⁻¹) * d ^ (A + n) =
              d ^ (A + n) * ((e ^ C)⁻¹ * (e ^ A)⁻¹) := by
          exact (Subgroup.mem_center_iff.mp hdpow_cent) ((e ^ C)⁻¹ * (e ^ A)⁻¹)
        have hu_block :
            u ^ n * (d ^ (A + n) * u * c ^ (A + n)) =
              d ^ (A + n) * u ^ (n + 1) * c ^ (A + n) := by
          calc
            u ^ n * (d ^ (A + n) * u * c ^ (A + n))
                = (u ^ n * d ^ (A + n)) * u * c ^ (A + n) := by simp [mul_assoc]
            _ = (d ^ (A + n) * u ^ n) * u * c ^ (A + n) := by rw [hudn]
            _ = d ^ (A + n) * (u ^ n * u) * c ^ (A + n) := by simp [mul_assoc]
            _ = d ^ (A + n) * u ^ (n + 1) * c ^ (A + n) := by simp [pow_succ, mul_assoc]
        calc
          ((e ^ C)⁻¹ * (e ^ A)⁻¹) * u ^ n * (d ^ (A + n) * u * c ^ (A + n))
              = ((e ^ C)⁻¹ * (e ^ A)⁻¹) * (u ^ n * (d ^ (A + n) * u * c ^ (A + n))) := by
                  simp [mul_assoc]
          _ = ((e ^ C)⁻¹ * (e ^ A)⁻¹) * (d ^ (A + n) * u ^ (n + 1) * c ^ (A + n)) := by
                rw [hu_block]
          _ = d ^ (A + n) * (((e ^ C)⁻¹ * (e ^ A)⁻¹) * (u ^ (n + 1) * c ^ (A + n))) := by
                simpa [mul_assoc] using congrArg
                  (fun t => t * (u ^ (n + 1) * c ^ (A + n))) hprefixd
          _ = d ^ (A + n) * ((e ^ C)⁻¹ * (e ^ A)⁻¹) * u ^ (n + 1) * c ^ (A + n) := by
                simp [pow_succ', mul_assoc]
      calc
        (u * v) ^ (n + 1) = (u * v) ^ n * (u * v) := by simp [pow_succ]
        _ = (⁅⁅v, u⁆, u⁆ ^ Nat.choose (n + 1) 3 *
              (⁅⁅v, u⁆, v⁆ ^ Nat.choose n 3)⁻¹ *
              u ^ n * ⁅v, u⁆ ^ Nat.choose n 2 * v ^ n) * (u * v) := by
                rw [mul_pow_formula_front hcu hcv n]
        _ = d ^ Nat.choose (n + 1) 3 * (e ^ Nat.choose n 3)⁻¹ *
              u ^ n * c ^ Nat.choose n 2 * (v ^ n * u) * v := by
                simp [c, d, e, mul_assoc]
        _ = d ^ Nat.choose (n + 1) 3 * (e ^ Nat.choose n 3)⁻¹ *
              u ^ n * c ^ Nat.choose n 2 * (((e ^ Nat.choose n 2)⁻¹ * c ^ n) * u * v ^ n) * v := by
                rw [hcvu]
        _ = d ^ Nat.choose (n + 1) 3 * ((e ^ Nat.choose n 3)⁻¹ * (e ^ Nat.choose n 2)⁻¹) *
              u ^ n * c ^ (Nat.choose n 2 + n) * u * v ^ (n + 1) := by
                have h_expand :
                    d ^ Nat.choose (n + 1) 3 * (e ^ Nat.choose n 3)⁻¹ *
                        u ^ n * c ^ Nat.choose n 2 *
                        (((e ^ Nat.choose n 2)⁻¹ * c ^ n) * u * v ^ n) * v
                      =
                    d ^ B * (e ^ C)⁻¹ *
                        u ^ n * (c ^ A * ((e ^ A)⁻¹ * c ^ n)) *
                        u * v ^ n * v := by
                  simp [A, B, C, mul_assoc]
                have h_mid :
                    d ^ B * (e ^ C)⁻¹ *
                        u ^ n * ((e ^ A)⁻¹ * c ^ A * c ^ n) *
                        u * v ^ n * v
                      =
                    d ^ B * ((e ^ C)⁻¹ * (e ^ A)⁻¹) *
                        u ^ n * (c ^ A * c ^ n) * u * v ^ n * v := by
                  simpa [mul_assoc] using congrArg
                    (fun t => d ^ B * (e ^ C)⁻¹ * u ^ n * t * u * v ^ n * v) h_un_eA_cA_cn
                have h_tail :
                    d ^ B * ((e ^ C)⁻¹ * (e ^ A)⁻¹) *
                        u ^ n * (c ^ A * c ^ n) * u * v ^ n * v
                      =
                    d ^ B * ((e ^ C)⁻¹ * (e ^ A)⁻¹) *
                        u ^ n * c ^ (A + n) * u * v ^ (n + 1) := by
                  have htail :
                      (c ^ A * c ^ n) * u * v ^ n * v = c ^ (A + n) * u * v ^ (n + 1) := by
                    simp [A, pow_add, pow_succ, mul_assoc]
                  simpa [mul_assoc] using congrArg
                    (fun t => d ^ B * ((e ^ C)⁻¹ * (e ^ A)⁻¹) * u ^ n * t) htail
                calc
                  d ^ Nat.choose (n + 1) 3 * (e ^ Nat.choose n 3)⁻¹ *
                      u ^ n * c ^ Nat.choose n 2 * (((e ^ Nat.choose n 2)⁻¹ * c ^ n) * u * v ^ n) * v
                      =
                    d ^ B * (e ^ C)⁻¹ *
                      u ^ n * (c ^ A * ((e ^ A)⁻¹ * c ^ n)) *
                      u * v ^ n * v := h_expand
                  _ =
                    d ^ B * (e ^ C)⁻¹ *
                      u ^ n * ((e ^ A)⁻¹ * c ^ A * c ^ n) *
                      u * v ^ n * v := by
                        simpa [mul_assoc] using congrArg
                          (fun t => d ^ B * (e ^ C)⁻¹ * u ^ n * t * u * v ^ n * v) h_eA_cA_cn
                  _ =
                    d ^ B * ((e ^ C)⁻¹ * (e ^ A)⁻¹) *
                      u ^ n * (c ^ A * c ^ n) * u * v ^ n * v := h_mid
                  _ =
                    d ^ B * ((e ^ C)⁻¹ * (e ^ A)⁻¹) *
                      u ^ n * c ^ (A + n) * u * v ^ (n + 1) := h_tail
        _ = d ^ B * ((e ^ C)⁻¹ * (e ^ A)⁻¹) *
              d ^ (A + n) * u ^ (n + 1) * c ^ (A + n) * v ^ (n + 1) := by
                have hfront :
                    d ^ B * (d ^ (A + n) * ((e ^ C)⁻¹ * (e ^ A)⁻¹) * u ^ (n + 1) * c ^ (A + n)) *
                        v ^ (n + 1)
                      =
                    d ^ B * ((e ^ C)⁻¹ * (e ^ A)⁻¹) *
                        d ^ (A + n) * u ^ (n + 1) * c ^ (A + n) * v ^ (n + 1) := by
                  have hswap :
                      d ^ (A + n) * ((e ^ C)⁻¹ * (e ^ A)⁻¹) =
                        ((e ^ C)⁻¹ * (e ^ A)⁻¹) * d ^ (A + n) := by
                    symm
                    exact (Subgroup.mem_center_iff.mp hdpow_cent) ((e ^ C)⁻¹ * (e ^ A)⁻¹)
                  simpa [mul_assoc] using congrArg
                    (fun t => d ^ B * t * u ^ (n + 1) * c ^ (A + n) * v ^ (n + 1)) hswap
                calc
                  d ^ B * ((e ^ C)⁻¹ * (e ^ A)⁻¹) *
                      u ^ n * c ^ (A + n) * u * v ^ (n + 1)
                      = d ^ B * ((e ^ C)⁻¹ * (e ^ A)⁻¹) *
                      u ^ n * (c ^ (A + n) * u) * v ^ (n + 1) := by
                        simp [mul_assoc]
                  _ =
                    d ^ B * ((e ^ C)⁻¹ * (e ^ A)⁻¹) *
                      u ^ n * (d ^ (A + n) * u * c ^ (A + n)) * v ^ (n + 1) := by
                        rw [hcu_pow']
                  _ =
                    d ^ B * (d ^ (A + n) * ((e ^ C)⁻¹ * (e ^ A)⁻¹) * u ^ (n + 1) * c ^ (A + n)) *
                      v ^ (n + 1) := by
                        simpa [mul_assoc] using congrArg
                          (fun t => d ^ B * t * v ^ (n + 1)) h_u_d_block
                  _ =
                    d ^ B * ((e ^ C)⁻¹ * (e ^ A)⁻¹) *
                      d ^ (A + n) * u ^ (n + 1) * c ^ (A + n) * v ^ (n + 1) := hfront
        _ = d ^ (B + (A + n)) * ((e ^ C)⁻¹ * (e ^ A)⁻¹) *
              u ^ (n + 1) * c ^ (A + n) * v ^ (n + 1) := by
                have hswap :
                    ((e ^ C)⁻¹ * (e ^ A)⁻¹) * d ^ (A + n) =
                      d ^ (A + n) * ((e ^ C)⁻¹ * (e ^ A)⁻¹) := by
                  exact (Subgroup.mem_center_iff.mp hdpow_cent) ((e ^ C)⁻¹ * (e ^ A)⁻¹)
                calc
                  d ^ B * ((e ^ C)⁻¹ * (e ^ A)⁻¹) *
                      d ^ (A + n) * u ^ (n + 1) * c ^ (A + n) * v ^ (n + 1)
                      =
                    d ^ B * (d ^ (A + n) * ((e ^ C)⁻¹ * (e ^ A)⁻¹)) *
                      u ^ (n + 1) * c ^ (A + n) * v ^ (n + 1) := by
                        rw [← hswap]
                        simp [mul_assoc]
                  _ =
                    d ^ B * d ^ (A + n) * ((e ^ C)⁻¹ * (e ^ A)⁻¹) *
                      u ^ (n + 1) * c ^ (A + n) * v ^ (n + 1) := by
                        simp [mul_assoc]
                  _ =
                    d ^ (B + (A + n)) * ((e ^ C)⁻¹ * (e ^ A)⁻¹) *
                      u ^ (n + 1) * c ^ (A + n) * v ^ (n + 1) := by
                        simp [pow_add, mul_assoc]
        _ = d ^ Nat.choose (n + 2) 3 * (e ^ Nat.choose (n + 1) 3)⁻¹ *
              u ^ (n + 1) * c ^ Nat.choose (n + 1) 2 * v ^ (n + 1) := by
                have hchoose2 : Nat.choose (n + 1) 2 = Nat.choose n 2 + n := by
                  simpa [Nat.add_comm] using
                    Nat.choose_succ_right (n := n + 1) (k := 1) (Nat.succ_pos n)
                have hchoose3a : Nat.choose (n + 2) 3 = Nat.choose (n + 1) 3 + (Nat.choose n 2 + n) := by
                  calc
                    Nat.choose (n + 2) 3 = Nat.choose (n + 1) 2 + Nat.choose (n + 1) 3 := by
                      simpa using Nat.choose_succ_right (n := n + 2) (k := 2) (by omega)
                    _ = Nat.choose (n + 1) 3 + (Nat.choose n 2 + n) := by
                      rw [hchoose2]
                      omega
                have hchoose3b : Nat.choose (n + 1) 3 = Nat.choose n 3 + Nat.choose n 2 := by
                  simpa [Nat.add_comm] using Nat.choose_succ_succ n 2
                have hecombine :
                    (e ^ C)⁻¹ * (e ^ A)⁻¹ = (e ^ (C + A))⁻¹ := by
                  calc
                    (e ^ C)⁻¹ * (e ^ A)⁻¹ = (e ^ A * e ^ C)⁻¹ := by simp [mul_inv_rev]
                    _ = (e ^ (A + C))⁻¹ := by rw [pow_add]
                    _ = (e ^ (C + A))⁻¹ := by simp [Nat.add_comm]
                rw [hchoose2, hchoose3a, hecombine, hchoose3b]
                have hmain := congrArg
                  (fun m : ℕ =>
                    d ^ (m + (Nat.choose n 2 + n)) *
                      (e ^ (Nat.choose n 3 + Nat.choose n 2))⁻¹ *
                      u ^ (n + 1) * c ^ (Nat.choose n 2 + n) * v ^ (n + 1))
                  hchoose3b
                simpa [A, B, C, mul_assoc] using hmain

public theorem CFSG.prime_dvd_choose_two {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2) :
    p ∣ Nat.choose p 2 := by
  have hpprime : Nat.Prime p := Fact.out
  have hlt : 2 < p := lt_of_le_of_ne hpprime.two_le (Ne.symm hpodd)
  exact Nat.Prime.dvd_choose_self hpprime (k := 2) (by decide) hlt

public theorem CFSG.choose_two_pow_eq_one
    {M : Type*} [Group M] {p : ℕ} [Fact p.Prime] {c : M}
    (hpodd : p ≠ 2) (hc : c ^ p = 1) : c ^ Nat.choose p 2 = 1 := by
  rcases prime_dvd_choose_two (p := p) hpodd with ⟨k, hk⟩
  calc
    c ^ Nat.choose p 2 = c ^ (p * k) := by simp [hk]
    _ = (c ^ p) ^ k := by rw [pow_mul]
    _ = 1 := by simp [hc]

public theorem CFSG.pth_mul_eq_one_of_class3
    {R : Type*} [Group R] {p : ℕ} [Fact p.Prime]
    (hpodd : p ≠ 2) (hpgt : 3 < p) (hclass : NilpotencyClassLe 3 R)
    {u v : R} (hu : u ^ p = 1) (hv : v ^ p = 1) :
    (u * v) ^ p = 1 := by
  let c : R := ⁅v, u⁆
  let du : R := ⁅c, u⁆
  let dv : R := ⁅c, v⁆
  have hL2 : (⊤ : Subgroup R).lowerCentralSeries 2 ≤ Subgroup.center R :=
    lowerCentralSeries_two_le_center_of_class3 (R := R) hclass
  have hdu_mem_l2 : du ∈ (⊤ : Subgroup R).lowerCentralSeries 2 := by
    simpa [c, du] using
      (triple_commutator_mem_lowerCentralSeries_two (R := R) v u u)
  have hdv_mem_l2 : dv ∈ (⊤ : Subgroup R).lowerCentralSeries 2 := by
    simpa [c, dv] using
      (triple_commutator_mem_lowerCentralSeries_two (R := R) v u v)
  have hdu_cent : du ∈ Subgroup.center R := hL2 hdu_mem_l2
  have hdv_cent : dv ∈ Subgroup.center R := hL2 hdv_mem_l2
  have hc_pow_eq : c ^ p = dv ^ Nat.choose p 2 := by
    have htmp : 1 = (dv ^ Nat.choose p 2)⁻¹ * c ^ p := by
      simpa [c, dv, hv] using (commutator_pow_formula (u := v) (w := u) hdv_cent p)
    have hmul := congrArg (fun t : R => dv ^ Nat.choose p 2 * t) htmp
    simpa [mul_assoc] using hmul.symm
  have hc_pow_cent : c ^ p ∈ Subgroup.center R := by
    rw [hc_pow_eq]
    exact (Subgroup.center R).pow_mem hdv_cent (Nat.choose p 2)
  have hdu_four_eq : ⁅du, c⁆ = 1 :=
    commutator_eq_one_of_mem_lowerCentralSeries_two (R := R) hclass hdu_mem_l2
  have hdv_four_eq : ⁅dv, c⁆ = 1 :=
    commutator_eq_one_of_mem_lowerCentralSeries_two (R := R) hclass hdv_mem_l2
  have hdv_four_cent : ⁅⁅c, v⁆, c⁆ ∈ Subgroup.center R := by
    simp [dv, hdv_four_eq]
  have hdu_four_cent : ⁅⁅c, u⁆, c⁆ ∈ Subgroup.center R := by
    simp [du, hdu_four_eq]
  have hc_pow_comm_v : ⁅c ^ p, v⁆ = 1 := by
    have hcomm : c ^ p * v = v * c ^ p := ((Subgroup.mem_center_iff.mp hc_pow_cent) v).symm
    rw [commutatorElement_def, hcomm]
    simp [mul_assoc]
  have hc_pow_comm_u : ⁅c ^ p, u⁆ = 1 := by
    have hcomm : c ^ p * u = u * c ^ p := ((Subgroup.mem_center_iff.mp hc_pow_cent) u).symm
    rw [commutatorElement_def, hcomm]
    simp [mul_assoc]
  have hdv_pow : dv ^ p = 1 := by
    have htmp : 1 = dv ^ p := by
      simpa [c, dv, hc_pow_comm_v, hdv_four_eq] using
        (commutator_pow_formula (u := c) (w := v) hdv_four_cent p)
    exact htmp.symm
  have hdu_pow : du ^ p = 1 := by
    have htmp : 1 = du ^ p := by
      simpa [c, du, hc_pow_comm_u, hdu_four_eq] using
        (commutator_pow_formula (u := c) (w := u) hdu_four_cent p)
    exact htmp.symm
  have hc_pow : c ^ p = 1 := by
    calc
      c ^ p = dv ^ Nat.choose p 2 := hc_pow_eq
      _ = 1 := choose_two_pow_eq_one (p := p) hpodd hdv_pow
  have hpdvd_choose3 : p ∣ Nat.choose p 3 := by
    have hpprime : Nat.Prime p := Fact.out
    exact Nat.Prime.dvd_choose_self hpprime (k := 3) (by decide) hpgt
  have hpdvd_chooseSucc3 : p ∣ Nat.choose (p + 1) 3 := by
    have hpascal : Nat.choose (p + 1) 3 = Nat.choose p 2 + Nat.choose p 3 := by
      simpa [Nat.add_comm] using Nat.choose_succ_succ p 2
    rw [hpascal]
    exact dvd_add (prime_dvd_choose_two (p := p) hpodd) hpdvd_choose3
  have hdu_choose : du ^ Nat.choose (p + 1) 3 = 1 := by
    rcases hpdvd_chooseSucc3 with ⟨k, hk⟩
    calc
      du ^ Nat.choose (p + 1) 3 = du ^ (p * k) := by simp [hk]
      _ = (du ^ p) ^ k := by rw [pow_mul]
      _ = 1 := by simp [hdu_pow]
  have hdv_choose : dv ^ Nat.choose p 3 = 1 := by
    rcases hpdvd_choose3 with ⟨k, hk⟩
    calc
      dv ^ Nat.choose p 3 = dv ^ (p * k) := by simp [hk]
      _ = (dv ^ p) ^ k := by rw [pow_mul]
      _ = 1 := by simp [hdv_pow]
  have hc_choose : c ^ Nat.choose p 2 = 1 := choose_two_pow_eq_one (p := p) hpodd hc_pow
  calc
    (u * v) ^ p
        = du ^ Nat.choose (p + 1) 3 * (dv ^ Nat.choose p 3)⁻¹ * u ^ p * c ^ Nat.choose p 2 * v ^ p := by
            simpa [c, du, dv] using (mul_pow_formula_front (u := u) (v := v) hdu_cent hdv_cent p)
    _ = du ^ Nat.choose (p + 1) 3 * (dv ^ Nat.choose p 3)⁻¹ * c ^ Nat.choose p 2 := by
          simp [hu, hv]
    _ = 1 := by simp [hdu_choose, hdv_choose, hc_choose]


end Main
