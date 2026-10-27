module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.proposition_1_10

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise IsMulCommutative commutatorElement

universe uG uA
public section

public theorem CFSG.commutator_mem_omega₁_center_of_mem_upperCentralSeries_two_of_pow_eq_one
    {G : Type*} [Group G] {p : ℕ} [Fact p.Prime] {x g : G}
    (hx₂ : x ∈ Subgroup.upperCentralSeries G 2) (hxpow : x ^ p = 1) :
    ⁅x, g⁆ ∈ (omega₁ (G := Subgroup.center G) (p := p)).map (Subgroup.center G).subtype := by
  let _ := (inferInstance : Fact p.Prime)
  have hcomm_center : ⁅x, g⁆ ∈ Subgroup.center G := by
    rw [show 2 = 1 + 1 by decide] at hx₂
    simpa [Subgroup.upperCentralSeries_one, commutatorElement_def, mul_assoc] using
      (Subgroup.mem_upperCentralSeries_succ_iff.mp hx₂) g
  have hxpow_center : x ^ p ∈ Subgroup.center G := by
    simp [hxpow]
  have hcomm_center' : ⁅g, x⁆ ∈ Subgroup.center G := by
    simpa [commutatorElement_inv] using (Subgroup.center G).inv_mem hcomm_center
  let c : G := ⁅g, x⁆
  have hc : IsMulCentral c := by
    rw [isMulCentral_iff]
    refine ⟨?_, ?_, ?_⟩
    · intro a
      exact (Subgroup.mem_center_iff.mp hcomm_center' a).symm
    · intro a b
      simp [mul_assoc]
    · intro a b
      simp [mul_assoc]
  have hrel : g * x = c * x * g := by
    simpa [c, mul_assoc] using (by
      rw [commutatorElement_def]
      group)
  have move_left :
      ∀ n : ℕ, g * x ^ n = c ^ n * x ^ n * g := by
    intro n
    induction n with
    | zero =>
        simp
    | succ n ihn =>
        calc
          g * x ^ (n + 1) = (g * x ^ n) * x := by simp [pow_succ, mul_assoc]
          _ = (c ^ n * x ^ n * g) * x := by rw [ihn]
          _ = c ^ n * x ^ n * (g * x) := by simp [mul_assoc]
          _ = c ^ n * x ^ n * (c * x * g) := by rw [hrel]
          _ = c ^ (n + 1) * x ^ (n + 1) * g := by
            have hcx : c * x ^ n = x ^ n * c := (hc.comm (x ^ n)).eq
            have hcc : c ^ n * c = c * c ^ n := (Commute.self_pow c n).symm.eq
            calc
              c ^ n * x ^ n * (c * x * g)
                  = c ^ n * (x ^ n * c) * x * g := by simp [mul_assoc]
              _ = c ^ n * (c * x ^ n) * x * g := by rw [← hcx]
              _ = c ^ n * c * x ^ n * x * g := by simp [mul_assoc]
              _ = c ^ (n + 1) * x ^ (n + 1) * g := by simp [hcc, pow_succ, mul_assoc]
  have hc_pow : c ^ p = 1 := by
    have hmove := move_left p
    rw [hxpow] at hmove
    have h1 := congrArg (fun t : G => t * g⁻¹) hmove
    simpa [mul_assoc] using h1.symm
  have hcomm_pow : ⁅x, g⁆ ^ p = 1 := by
    have hcomm_inv : ⁅g, x⁆ = ⁅x, g⁆⁻¹ := by
      simp
    have hpow_inv : (⁅x, g⁆⁻¹) ^ p = 1 := by
      rw [← hcomm_inv]
      simpa [c] using hc_pow
    have htmp : (⁅x, g⁆ ^ p)⁻¹ = 1 := by
      rw [inv_pow] at hpow_inv
      exact hpow_inv
    exact inv_eq_one.mp htmp
  have homega :
      (⟨⁅x, g⁆, hcomm_center⟩ : Subgroup.center G) ∈ omega₁ (G := Subgroup.center G) (p := p) := by
    change (⟨⁅x, g⁆, hcomm_center⟩ : Subgroup.center G) ∈
      Subgroup.closure {y : Subgroup.center G | y ^ (p ^ 1) = 1}
    refine Subgroup.subset_closure ?_
    simpa [pow_one] using hcomm_pow
  exact Subgroup.mem_map_of_mem (Subgroup.center G).subtype homega

public theorem CFSG.classTwo_pthPower_hom {G : Type*} [Group G] {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    (hcomm : commutator G ≤ Subgroup.center G) (hpowcent : ∀ x : G, x ^ p ∈ Subgroup.center G)
    (x y : G) : (x * y) ^ p = x ^ p * y ^ p := by
  have commutator_central (u v : G) : IsMulCentral ⁅u, v⁆ := by
    rw [isMulCentral_iff]
    refine ⟨?_, ?_, ?_⟩
    · intro a
      have hmem : ⁅u, v⁆ ∈ Subgroup.center G := hcomm <|
        Subgroup.commutator_mem_commutator (H₁ := ⊤) (H₂ := ⊤)
          (show u ∈ (⊤ : Subgroup G) by trivial) (show v ∈ (⊤ : Subgroup G) by trivial)
      exact (Subgroup.mem_center_iff.mp hmem a).symm
    · intro a b
      simp [mul_assoc]
    · intro a b
      simp [mul_assoc]
  have commutator_factor (u v : G) : v * u = ⁅v, u⁆ * u * v := by
    rw [commutatorElement_def]
    simp [mul_assoc]
  have move_right (u v c : G) (hc : IsMulCentral c) (hvu : v * u = c * u * v) :
      ∀ n : ℕ, v ^ n * u = c ^ n * u * v ^ n := by
    intro n
    induction n with
    | zero =>
        simp
    | succ n ihn =>
        calc
          v ^ (n + 1) * u = v ^ n * (v * u) := by simp [pow_succ, mul_assoc]
          _ = v ^ n * (c * u * v) := by rw [hvu]
          _ = (v ^ n * c) * u * v := by simp [mul_assoc]
          _ = (c * v ^ n) * u * v := by rw [(hc.comm (v ^ n)).eq]
          _ = c * (v ^ n * u) * v := by simp [mul_assoc]
          _ = c * (c ^ n * u * v ^ n) * v := by rw [ihn]
          _ = c ^ (n + 1) * u * v ^ (n + 1) := by
            have hcc : c * c ^ n = c ^ n * c := (Commute.self_pow c n).eq
            have hcc' := congrArg (fun t : G => t * (u * (v ^ n * v))) hcc
            simpa [pow_succ, mul_assoc] using hcc'
  have move_left (u v c : G) (hc : IsMulCentral c) (hvu : v * u = c * u * v) :
      ∀ n : ℕ, v * u ^ n = c ^ n * u ^ n * v := by
    intro n
    induction n with
    | zero =>
        simp
    | succ n ihn =>
        calc
          v * u ^ (n + 1) = (v * u ^ n) * u := by simp [pow_succ, mul_assoc]
          _ = (c ^ n * u ^ n * v) * u := by rw [ihn]
          _ = c ^ n * u ^ n * (v * u) := by simp [mul_assoc]
          _ = c ^ n * u ^ n * (c * u * v) := by rw [hvu]
          _ = c ^ (n + 1) * u ^ (n + 1) * v := by
            have hcu : c * u ^ n = u ^ n * c := (hc.comm (u ^ n)).eq
            have hcc : c ^ n * c = c * c ^ n := (Commute.self_pow c n).symm.eq
            calc
              c ^ n * u ^ n * (c * u * v)
                  = c ^ n * (u ^ n * c) * u * v := by simp [mul_assoc]
              _ = c ^ n * (c * u ^ n) * u * v := by rw [← hcu]
              _ = c ^ n * c * u ^ n * u * v := by simp [mul_assoc]
              _ = c ^ (n + 1) * u ^ (n + 1) * v := by simp [hcc, pow_succ, mul_assoc]
  have commutator_pow_eq_one (u v : G) : ⁅v, u⁆ ^ p = 1 := by
    let c := ⁅v, u⁆
    have hc : IsMulCentral c := commutator_central v u
    have hmove : v * u ^ p = c ^ p * u ^ p * v := by
      simpa [c] using
        move_left u v c hc (by simpa [c, mul_assoc] using commutator_factor u v) p
    have hcent : v * u ^ p = u ^ p * v := (Subgroup.mem_center_iff.mp (hpowcent u)) v
    rw [hcent] at hmove
    have h1 := congrArg (fun t : G => t * v⁻¹) hmove
    simp [mul_assoc] at h1
    have h2 := congrArg (fun t : G => t * (u ^ p)⁻¹) h1
    simpa [mul_assoc] using h2
  let c : G := ⁅y, x⁆
  have hc : IsMulCentral c := commutator_central y x
  have hyx : y * x = c * x * y := by
    simpa [c, mul_assoc] using commutator_factor x y
  have hmul :
      ∀ n : ℕ, (x * y) ^ n = c ^ (Nat.choose n 2) * x ^ n * y ^ n := by
    intro n
    induction n with
    | zero =>
        simp [c]
    | succ n ih =>
        calc
          (x * y) ^ (n + 1) = (x * y) ^ n * (x * y) := by simp [pow_succ]
          _ = (c ^ Nat.choose n 2 * x ^ n * y ^ n) * (x * y) := by rw [ih]
          _ = c ^ Nat.choose n 2 * x ^ n * (y ^ n * x) * y := by simp [mul_assoc]
          _ = c ^ Nat.choose n 2 * x ^ n * (c ^ n * x * y ^ n) * y := by
            rw [move_right x y c hc hyx n]
          _ = c ^ (Nat.choose n 2 + n) * x ^ (n + 1) * y ^ (n + 1) := by
            have hcxn : c ^ n * x ^ n = x ^ n * c ^ n := (Commute.pow_pow (hc.comm x) n n).eq
            calc
              c ^ Nat.choose n 2 * x ^ n * (c ^ n * x * y ^ n) * y
                  = c ^ Nat.choose n 2 * (c ^ n * x ^ n) * x * y ^ n * y := by
                      rw [hcxn]
                      simp [mul_assoc]
              _ = (c ^ Nat.choose n 2 * c ^ n) * x ^ n * x * y ^ n * y := by
                    simp [mul_assoc]
              _ = c ^ (Nat.choose n 2 + n) * x ^ (n + 1) * y ^ (n + 1) := by
                    simp [← pow_add, pow_succ, mul_assoc]
          _ = c ^ Nat.choose (n + 1) 2 * x ^ (n + 1) * y ^ (n + 1) := by
            rw [Nat.choose_succ_succ, Nat.choose_one_right]
            simp [Nat.add_comm]
  have hchoose : p ∣ Nat.choose p 2 := by
    rcases (Nat.Prime.even_sub_one (Fact.out : p.Prime) hpodd) with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [Nat.choose_two_right, hk, ← Nat.two_mul k, Nat.mul_comm 2 k]
    apply Nat.div_eq_of_eq_mul_left (by decide : 0 < 2)
    simp [Nat.mul_assoc]
  have hcomm_pow : c ^ p = 1 := by
    simpa [c] using commutator_pow_eq_one x y
  rcases hchoose with ⟨k, hk⟩
  calc
    (x * y) ^ p = c ^ (Nat.choose p 2) * x ^ p * y ^ p := hmul p
    _ = x ^ p * y ^ p := by
      rw [hk, pow_mul, hcomm_pow, one_pow, one_mul]


lemma CFSG.swap_mul_commutator_of_mem_center {G : Type*} [Group G] {x y : G}
    (hcomm : ⁅y, x⁆ ∈ Subgroup.center G) :
    y * x = x * y * ⁅y, x⁆ := by
  have hx : x * ⁅y, x⁆ = ⁅y, x⁆ * x := (Subgroup.mem_center_iff.mp hcomm) x
  have hy : y * ⁅y, x⁆ = ⁅y, x⁆ * y := (Subgroup.mem_center_iff.mp hcomm) y
  calc
    y * x = ⁅y, x⁆ * x * y := by
      simp [commutatorElement_def, mul_assoc]
    _ = x * ⁅y, x⁆ * y := by
      rw [← hx, mul_assoc]
    _ = x * (⁅y, x⁆ * y) := by
      simp [mul_assoc]
    _ = x * (y * ⁅y, x⁆) := by
      rw [← hy]
    _ = x * y * ⁅y, x⁆ := by
      simp [mul_assoc]

public lemma CFSG.pow_mul_eq_mul_pow_commutator_pow_of_mem_center {G : Type*} [Group G] {x y : G}
    (hcomm : ⁅y, x⁆ ∈ Subgroup.center G) :
    ∀ n : ℕ, y ^ n * x = x * y ^ n * ⁅y, x⁆ ^ n
  | 0 => by simp
  | n + 1 => by
      have hyc : y ^ n * ⁅y, x⁆ = ⁅y, x⁆ * y ^ n := (Subgroup.mem_center_iff.mp hcomm) (y ^ n)
      calc
        y ^ (n + 1) * x = y * (y ^ n * x) := by
          simp [pow_succ', mul_assoc]
        _ = y * (x * y ^ n * ⁅y, x⁆ ^ n) := by
          rw [pow_mul_eq_mul_pow_commutator_pow_of_mem_center hcomm n]
        _ = (y * x) * y ^ n * ⁅y, x⁆ ^ n := by
          simp [mul_assoc]
        _ = (x * y * ⁅y, x⁆) * y ^ n * ⁅y, x⁆ ^ n := by
          rw [swap_mul_commutator_of_mem_center hcomm]
        _ = x * y * (⁅y, x⁆ * y ^ n) * ⁅y, x⁆ ^ n := by
          simp [mul_assoc]
        _ = x * y * (y ^ n * ⁅y, x⁆) * ⁅y, x⁆ ^ n := by
          rw [← hyc]
        _ = x * (y * y ^ n) * ⁅y, x⁆ * ⁅y, x⁆ ^ n := by
          simp [mul_assoc]
        _ = x * y ^ (n + 1) * ⁅y, x⁆ ^ (n + 1) := by
          simp [pow_succ', mul_assoc]

public lemma CFSG.mul_pow_eq_pow_mul_commutator_choose_of_mem_center {G : Type*} [Group G] {x y : G}
    (hcomm : ⁅y, x⁆ ∈ Subgroup.center G) :
    ∀ n : ℕ, (x * y) ^ n = x ^ n * y ^ n * ⁅y, x⁆ ^ Nat.choose n 2
  | 0 => by simp
  | n + 1 => by
      have hcxn : x * ⁅y, x⁆ ^ Nat.choose n 2 = ⁅y, x⁆ ^ Nat.choose n 2 * x := by
        exact (Subgroup.mem_center_iff.mp ((Subgroup.center G).pow_mem hcomm _)) x
      have hycPow : y * ⁅y, x⁆ ^ (n + Nat.choose n 2) = ⁅y, x⁆ ^ (n + Nat.choose n 2) * y := by
        exact (Subgroup.mem_center_iff.mp ((Subgroup.center G).pow_mem hcomm _)) y
      calc
        (x * y) ^ (n + 1) = (x * y) ^ n * (x * y) := by
          simp [pow_succ]
        _ = x ^ n * y ^ n * ⁅y, x⁆ ^ Nat.choose n 2 * (x * y) := by
          rw [mul_pow_eq_pow_mul_commutator_choose_of_mem_center hcomm n]
        _ = x ^ n * y ^ n * (⁅y, x⁆ ^ Nat.choose n 2 * x) * y := by
          simp [mul_assoc]
        _ = x ^ n * y ^ n * (x * ⁅y, x⁆ ^ Nat.choose n 2) * y := by
          rw [← hcxn]
        _ = x ^ n * (y ^ n * x) * ⁅y, x⁆ ^ Nat.choose n 2 * y := by
          simp [mul_assoc]
        _ = x ^ n * (x * y ^ n * ⁅y, x⁆ ^ n) * ⁅y, x⁆ ^ Nat.choose n 2 * y := by
          rw [pow_mul_eq_mul_pow_commutator_pow_of_mem_center hcomm n]
        _ = x ^ (n + 1) * y ^ n * (⁅y, x⁆ ^ n * ⁅y, x⁆ ^ Nat.choose n 2) * y := by
          simp [pow_succ, mul_assoc]
        _ = x ^ (n + 1) * y ^ n * ⁅y, x⁆ ^ (n + Nat.choose n 2) * y := by
          rw [← pow_add]
        _ = x ^ (n + 1) * (y ^ n * (⁅y, x⁆ ^ (n + Nat.choose n 2) * y)) := by
          simp [mul_assoc]
        _ = x ^ (n + 1) * (y ^ n * (y * ⁅y, x⁆ ^ (n + Nat.choose n 2))) := by
          rw [hycPow]
        _ = x ^ (n + 1) * (y ^ (n + 1) * ⁅y, x⁆ ^ (n + Nat.choose n 2)) := by
          simp [pow_succ, mul_assoc]
        _ = x ^ (n + 1) * y ^ (n + 1) * ⁅y, x⁆ ^ Nat.choose (n + 1) 2 := by
          simp [Nat.choose_succ_succ, Nat.choose_one_right, mul_assoc]

lemma CFSG.commutator_pow_eq_one_of_pow_mem_center {G : Type*} [Group G] {x y : G} {p : ℕ}
    (hcomm : ⁅y, x⁆ ∈ Subgroup.center G) (hypow : y ^ p ∈ Subgroup.center G) :
    ⁅y, x⁆ ^ p = 1 := by
  have hmain := pow_mul_eq_mul_pow_commutator_pow_of_mem_center (x := x) (y := y) hcomm p
  have hcentral : x * y ^ p = y ^ p * x := (Subgroup.mem_center_iff.mp hypow) x
  rw [← hcentral] at hmain
  have h1 : y ^ p = y ^ p * ⁅y, x⁆ ^ p := by
    exact mul_left_cancel (a := x) (by simpa [mul_assoc] using hmain)
  have h2 : 1 = ⁅y, x⁆ ^ p := by
    exact mul_left_cancel (a := y ^ p) (by simpa [mul_assoc] using h1)
  simpa using h2.symm

lemma CFSG.commutator_pow_eq_one_of_pow_eq_one_of_commute {G : Type*} [Group G] {x g : G} {p : ℕ}
    (hcomm : Commute ⁅x, g⁆ x) (hxpow : x ^ p = 1) :
    ⁅x, g⁆ ^ p = 1 := by
  let c : G := ⁅x, g⁆
  have hfactor : x * g = c * g * x := by
    simpa [c, mul_assoc] using (show x * g = ⁅x, g⁆ * g * x by
      rw [commutatorElement_def]
      simp [mul_assoc])
  have hmove : ∀ n : ℕ, x ^ n * g = c ^ n * g * x ^ n := by
    intro n
    induction n with
    | zero =>
        simp
    | succ n ihn =>
        calc
          x ^ (n + 1) * g = x * (x ^ n * g) := by
            simp [pow_succ', mul_assoc]
          _ = x * (c ^ n * g * x ^ n) := by rw [ihn]
          _ = (x * c ^ n) * g * x ^ n := by simp [mul_assoc]
          _ = (c ^ n * x) * g * x ^ n := by
            rw [(Commute.pow_left hcomm n).eq.symm]
          _ = c ^ n * (x * g) * x ^ n := by simp [mul_assoc]
          _ = c ^ n * (c * g * x) * x ^ n := by rw [hfactor]
          _ = c ^ (n + 1) * g * x ^ (n + 1) := by
            have hcc : c ^ n * c = c * c ^ n := (Commute.self_pow c n).symm.eq
            calc
              c ^ n * (c * g * x) * x ^ n = c ^ n * c * g * x * x ^ n := by
                simp [mul_assoc]
              _ = c * c ^ n * g * x * x ^ n := by rw [hcc]
              _ = c ^ (n + 1) * g * x ^ (n + 1) := by
                simp [pow_succ', mul_assoc]
  have hmain : x ^ p * g = c ^ p * g * x ^ p := hmove p
  rw [hxpow] at hmain
  have h1 : g = c ^ p * g := by simpa [c] using hmain
  exact mul_right_cancel (b := g) (by simpa [mul_assoc] using h1)

lemma CFSG.diff_pow_eq_one_of_commutator_mem_center_of_pow_fixed
    {G A : Type*} [Group G] [Group A] [MulDistribMulAction A G] {p : ℕ} [Fact p.Prime]
    (hpodd : p ≠ 2) {x : G} {a : A}
    (hcomm : ⁅a • x, x⁻¹⁆ ∈ Subgroup.center G)
    (hxpow_center : x ^ p ∈ Subgroup.center G)
    (hpowfix : a • (x ^ p) = x ^ p) :
    (x⁻¹ * a • x) ^ p = 1 := by
  have hpprime : Nat.Prime p := Fact.out
  have hsmul_pow : (a • x) ^ p = x ^ p := by
    simpa [smul_pow] using hpowfix
  have hypow_center : (a • x) ^ p ∈ Subgroup.center G := by
    simpa [hsmul_pow] using hxpow_center
  have hc_pow_p : ⁅a • x, x⁻¹⁆ ^ p = 1 :=
    commutator_pow_eq_one_of_pow_mem_center (x := x⁻¹) (y := a • x) hcomm hypow_center
  have h2lt : 2 < p := lt_of_le_of_ne hpprime.two_le (by simpa [eq_comm] using hpodd)
  have hchoose_dvd : p ∣ Nat.choose p 2 := by
    rcases (Nat.Prime.even_sub_one hpprime hpodd) with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [Nat.choose_two_right, hk, ← Nat.two_mul k, Nat.mul_comm 2 k]
    apply Nat.div_eq_of_eq_mul_left (by decide : 0 < 2)
    simp [Nat.mul_assoc]
  obtain ⟨k, hk⟩ := hchoose_dvd
  calc
    (x⁻¹ * a • x) ^ p = (x⁻¹) ^ p * (a • x) ^ p * ⁅a • x, x⁻¹⁆ ^ Nat.choose p 2 :=
      mul_pow_eq_pow_mul_commutator_choose_of_mem_center (x := x⁻¹) (y := a • x) hcomm p
    _ = (x ^ p)⁻¹ * x ^ p * ⁅a • x, x⁻¹⁆ ^ (p * k) := by
      rw [hsmul_pow, hk]
      simp
    _ = 1 * (⁅a • x, x⁻¹⁆ ^ p) ^ k := by
      rw [pow_mul]
      simp
    _ = 1 := by
      simp [hc_pow_p]

theorem CFSG.actsTriviallyOnSubgroup_omega₁_subgroup
    {G A : Type*} [Group G] [Finite G] [Group A] [Finite A] {p : ℕ} [Fact p.Prime]
    [Fact (IsPGroup p G)] [MulDistribMulAction A G]
    (H : Subgroup G) [IsInvariant A G H]
    (hΩ : ActsTriviallyOnSubgroup (A := A) (G := G) (omega₁ (G := G) (p := p))) :
    ActsTriviallyOnSubgroup (A := A) (G := H) (omega₁ (G := H) (p := p)) := by
  have hmap :
      (omega₁ (G := H) (p := p)).map H.subtype ≤ omega₁ (G := G) (p := p) := by
    rw [omega₁, omega₁, omega, omega, MonoidHom.map_closure]
    refine (Subgroup.closure_le (K := omega₁ (G := G) (p := p))).2 ?_
    rintro _ ⟨x, hx, rfl⟩
    refine Subgroup.subset_closure ?_
    simpa [pow_one] using congrArg H.subtype hx
  intro a x hx
  apply Subtype.ext
  exact hΩ a x (hmap (Subgroup.mem_map_of_mem H.subtype hx))

theorem CFSG.theorem_1_11_direct {G : Type uG} {A : Type uA} [Group G] [Finite G] [Group A]
    [Finite A] {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2) [Fact (IsPGroup p G)]
    [MulDistribMulAction A G] (hcoprime : Nat.Coprime (Nat.card A) (Nat.card G))
    (hΩ : ActsTriviallyOnSubgroup (A := A) (G := G) (omega₁ (G := G) (p := p))) :
    ActsTrivially (A := A) (G := G) := by
  let P : ℕ → Prop := fun n =>
    ∀ {H : Type uG} [Group H] [Finite H] [Fact (IsPGroup p H)] [MulDistribMulAction A H],
      Nat.card H = n →
      Nat.Coprime (Nat.card A) (Nat.card H) →
      ActsTriviallyOnSubgroup (A := A) (G := H) (omega₁ (G := H) (p := p)) →
      ActsTrivially (A := A) (G := H)
  have hP : ∀ n, P n := by
    intro n
    exact Nat.strong_induction_on (p := P) n <| fun n ih {H} _ _ _ _ hcard hHcop hΩH => by
      by_cases htriv : Subsingleton H
      · let : Subsingleton H := htriv
        intro a x
        exact Subsingleton.elim _ _
      · let : Nontrivial H := not_subsingleton_iff_nontrivial.mp htriv
        let C : Subgroup H := fixedPointSubgroup A H
        let D : Subgroup H := Subgroup.centralizer (C : Set H)
        have hΩH' : ∀ a : A, ∀ x : H, x ∈ omega₁ (G := H) (p := p) → a • x = x := by
          simpa [ActsTriviallyOnSubgroup] using hΩH
        have hDsmul {a : A} {x : H} (hx : x ∈ D) : a • x ∈ D := by
          have hx' : ∀ c : H, c ∈ C → c * x = x * c := by
            simpa [D, Subgroup.mem_centralizer_iff] using hx
          change a • x ∈ Subgroup.centralizer (C : Set H)
          rw [Subgroup.mem_centralizer_iff]
          intro c hc
          have hcfix : a • c = c := by
            change c ∈ fixedPointSubgroup A H at hc
            rw [FixedPoints.mem_subgroup] at hc
            exact hc a
          calc
            c * (a • x) = a • (c * x) := by simp [hcfix]
            _ = a • (x * c) := by rw [hx' c hc]
            _ = (a • x) * c := by simp [hcfix]
        have hDinv : IsInvariant A H D := by
          refine ⟨?_⟩
          intro a x
          constructor
          · exact hDsmul
          · intro hx
            simpa [smul_smul] using (hDsmul (a := a⁻¹) (x := a • x) hx)
        let : IsInvariant A H D := hDinv
        by_cases hDtop : D = ⊤
        · have hC_le_center : C ≤ Subgroup.center H := by
            intro c hc
            rw [Subgroup.mem_center_iff]
            intro x
            have hxD : x ∈ D := by simp [D, hDtop]
            have hxD' : ∀ y : H, y ∈ C → y * x = x * y := by
              simpa [D, Subgroup.mem_centralizer_iff] using hxD
            exact (hxD' c hc).symm
          let Φ : Subgroup H := frattini H
          have hΦinv : IsInvariant A H Φ :=
            isInvariant_of_characteristic (A := A) (G := H) Φ
          let : IsInvariant A H Φ := hΦinv
          by_cases hΦtop : Φ = ⊤
          · exact theorem_1_8 (R := H) (A := A) (p := p) hHcop <| by
              let hΦinv' : IsInvariant A H (frattini H) :=
                isInvariant_of_characteristic (A := A) (G := H) (frattini H)
              let : MulAction.QuotientAction A (frattini H) :=
                quotientAction_of_isInvariant (A := A) (frattini H) hΦinv'
              let : MulDistribMulAction A (H ⧸ frattini H) :=
                quotientMulDistribMulAction (A := A) (G := H) (frattini H) hΦinv'
              have : Subsingleton (H ⧸ frattini H) := by
                simp [Φ, hΦtop]
              simpa [ActsTrivially] using fun a x => Subsingleton.elim (a • x) x
          · have hΦ_card_lt : Nat.card Φ < Nat.card H := by
              have hle : Nat.card Φ ≤ Nat.card H := Subgroup.card_le_card_group (H := Φ)
              have hne : Nat.card Φ ≠ Nat.card H := by
                intro hEq
                exact hΦtop ((Subgroup.card_eq_iff_eq_top (H := Φ)).1 hEq)
              exact lt_of_le_of_ne hle hne
            have hΦ_card_lt' : Nat.card Φ < n := by
              simpa [hcard] using hΦ_card_lt
            have hΦcop : Nat.Coprime (Nat.card A) (Nat.card Φ) :=
              hHcop.of_dvd_right (Subgroup.card_subgroup_dvd_card Φ)
            have hΩΦ :
                ActsTriviallyOnSubgroup (A := A) (G := Φ) (omega₁ (G := Φ) (p := p)) :=
              actsTriviallyOnSubgroup_omega₁_subgroup (A := A) (G := H) (p := p) Φ hΩH
            have : Fact (IsPGroup p Φ) := ⟨(Fact.out : IsPGroup p H).to_subgroup Φ⟩
            have htrivΦ : ActsTrivially (A := A) (G := Φ) :=
              ih (Nat.card Φ) hΦ_card_lt' (H := Φ) rfl hΦcop hΩΦ
            have hΦ_le_C : Φ ≤ C := by
              intro x hx
              change x ∈ fixedPointSubgroup A H
              rw [FixedPoints.mem_subgroup]
              intro a
              exact congrArg Subtype.val (htrivΦ a ⟨x, hx⟩)
            have hcomm_le_frattini : _root_.commutator H ≤ frattini H := by
              intro x hx
              rw [lemma_1_7_d (R := H) (p := p)]
              exact Subgroup.subset_closure (Or.inl (by simpa [derivedSubgroup] using hx))
            have hcomm_center : _root_.commutator H ≤ Subgroup.center H :=
              le_trans hcomm_le_frattini (le_trans hΦ_le_C hC_le_center)
            have hpow_frattini : ∀ x : H, x ^ p ∈ frattini H := by
              intro x
              rw [lemma_1_7_d (R := H) (p := p)]
              exact Subgroup.subset_closure (Or.inr ⟨x, rfl⟩)
            have hcomm_le_C : commutatorAction (A := A) (G := H) ≤ C := by
              change
                Subgroup.closure {x : H | ∃ a : A, ∃ g : H, g ∈ (⊤ : Subgroup H) ∧
                  x = g⁻¹ * (a • g)} ≤ C
              refine (Subgroup.closure_le (K := C)).2 ?_
              intro x hx
              rcases hx with ⟨a, g, -, rfl⟩
              have hcomm :
                  ⁅a • g, g⁻¹⁆ ∈ Subgroup.center H :=
                hcomm_center <|
                  Subgroup.commutator_mem_commutator (H₁ := ⊤) (H₂ := ⊤)
                    (show a • g ∈ (⊤ : Subgroup H) by trivial)
                    (show g⁻¹ ∈ (⊤ : Subgroup H) by trivial)
              have hgpow_frattini : g ^ p ∈ frattini H := hpow_frattini g
              have hgpow_center : g ^ p ∈ Subgroup.center H :=
                (le_trans hΦ_le_C hC_le_center) hgpow_frattini
              have hgpow_fix : a • (g ^ p) = g ^ p := by
                have hgpow_C : g ^ p ∈ fixedPointSubgroup A H := hΦ_le_C hgpow_frattini
                rw [FixedPoints.mem_subgroup] at hgpow_C
                exact hgpow_C a
              have hxpow : (g⁻¹ * a • g) ^ p = 1 :=
                diff_pow_eq_one_of_commutator_mem_center_of_pow_fixed
                  (A := A) (G := H) (p := p) hpodd hcomm hgpow_center hgpow_fix
              have hxomega : g⁻¹ * a • g ∈ omega₁ (G := H) (p := p) := by
                change g⁻¹ * a • g ∈ Subgroup.closure {y : H | y ^ (p ^ 1) = 1}
                refine Subgroup.subset_closure ?_
                simpa [pow_one] using hxpow
              change g⁻¹ * a • g ∈ fixedPointSubgroup A H
              rw [FixedPoints.mem_subgroup]
              intro b
              exact hΩH' b _ hxomega
            have hcomm2 : commutatorAction₂ (A := A) (G := H) = ⊥ := by
              apply bot_unique
              change
                Subgroup.closure
                    {x : H | ∃ a : A, ∃ g : H, g ∈ commutatorAction (A := A) (G := H) ∧
                      x = g⁻¹ * (a • g)} ≤
                  (⊥ : Subgroup H)
              refine (Subgroup.closure_le (K := (⊥ : Subgroup H))).2 ?_
              intro x hx
              rcases hx with ⟨a, g, hg, rfl⟩
              have hgC : g ∈ C := hcomm_le_C hg
              have hgfix : ∀ b : A, b • g = g := by
                simpa [C, FixedPoints.mem_subgroup] using hgC
              simp [hgfix a]
            let : Group.IsNilpotent H := (Fact.out : IsPGroup p H).isNilpotent
            have hsolv : Group.IsSolvable H := by infer_instance
            exact proposition_1_6_c (G := H) (A := A) hsolv hHcop hcomm2
        · have hD_card_lt : Nat.card D < Nat.card H := by
            have hle : Nat.card D ≤ Nat.card H := Subgroup.card_le_card_group (H := D)
            have hne : Nat.card D ≠ Nat.card H := by
              intro hEq
              exact hDtop ((Subgroup.card_eq_iff_eq_top (H := D)).1 hEq)
            exact lt_of_le_of_ne hle hne
          have hD_card_lt' : Nat.card D < n := by
            simpa [hcard] using hD_card_lt
          have hDcop : Nat.Coprime (Nat.card A) (Nat.card D) :=
            hHcop.of_dvd_right (Subgroup.card_subgroup_dvd_card D)
          have hΩD :
              ActsTriviallyOnSubgroup (A := A) (G := D) (omega₁ (G := D) (p := p)) :=
            actsTriviallyOnSubgroup_omega₁_subgroup (A := A) (G := H) (p := p) D hΩH
          have : Fact (IsPGroup p D) := ⟨(Fact.out : IsPGroup p H).to_subgroup D⟩
          have htrivD : ActsTrivially (A := A) (G := D) :=
            ih (Nat.card D) hD_card_lt' (H := D) rfl hDcop hΩD
          have hD_le_C : D ≤ C := by
            intro x hx
            change x ∈ fixedPointSubgroup A H
            rw [FixedPoints.mem_subgroup]
            intro a
            exact congrArg Subtype.val (htrivD a ⟨x, hx⟩)
          let : Group.IsNilpotent H := (Fact.out : IsPGroup p H).isNilpotent
          exact proposition_1_10 (G := H) (A := A) inferInstance hHcop (by simpa [C, D] using hD_le_C)
  exact hP (Nat.card G) (H := G) rfl hcoprime hΩ


/-
**Kind**: Theorem
**Note**: Theorem 1.11
**Stmt**:
Let $p$ be an odd prime.
Let $G$ be a $p$-group.
Let $A$ be a $p'$-group of operators on $G$ that acts trivially on $\Omega_1(G)$.
Then $A$ acts trivially on $G$.
-/

public theorem CFSG.theorem_1_11 {G A : Type*} [Group G] [Finite G] [Group A] [Finite A]
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2) [Fact (IsPGroup p G)]
    [MulDistribMulAction A G] (hcoprime : Nat.Coprime (Nat.card A) (Nat.card G))
    (hΩ : ActsTriviallyOnSubgroup (A := A) (G := G) (omega₁ (G := G) (p := p))) :
    ActsTrivially (A := A) (G := G) := by
  simpa using theorem_1_11_direct (G := G) (A := A) (p := p) hpodd hcoprime hΩ


end
