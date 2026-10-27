module

public import CFSG.Quasithin.Background.F918Z8Su0
public import CFSG.Quasithin.Background.F918Z8Su3
public import CFSG.Quasithin.Background.F918Z8Loc3
public import CFSG.Quasithin.Background.F918Z8Su1

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.QuasithinUnique.Bridge
open scoped Pointwise

theorem suz_arith {n m : ℕ} (hn3 : 3 ≤ n) (hn : Odd n)
    (hdvd : (2 ^ n) ^ 2 * (2 ^ n - 1) * ((2 ^ n) ^ 2 + 1) ∣
      ∏ i : Fin 4, ((2 ^ m) ^ 4 - (2 ^ m) ^ (i : ℕ))) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∣ (2 ^ n - 1) * ((2 ^ n) ^ 2 + 1) ∧
      p ∣ ((2 ^ m) ^ 3 - 1) * ((2 ^ m) ^ 2 - 1) := by
  by_contra hcon
  push Not at hcon
  have h8 : 8 ≤ 2 ^ n := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
  have hne1 : 2 ^ n - 1 ≠ 1 := by omega
  obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd hne1
  have h2n : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
  have hr2 : r ≠ 2 := by
    rintro rfl
    omega
  have hrO : r ∣ (2 ^ n - 1) * ((2 ^ n) ^ 2 + 1) := hrd.mul_right _
  have hnot : ¬ r ∣ ((2 ^ m) ^ 3 - 1) * ((2 ^ m) ^ 2 - 1) := hcon r hr hr2 hrO
  have hnot3 : ¬ r ∣ (2 ^ m) ^ 3 - 1 := fun h => hnot (h.mul_right _)
  have hnot2 : ¬ r ∣ (2 ^ m) ^ 2 - 1 := fun h => hnot (h.mul_left _)
  have hnot1 : ¬ r ∣ 2 ^ m - 1 := fun h =>
    hnot2 (h.trans (by simpa using Nat.sub_dvd_pow_sub_pow (2 ^ m) 1 2))
  have hnotQ : ¬ r ∣ 2 ^ m := fun h =>
    hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h))
  have hrGL : r ∣ ∏ i : Fin 4, ((2 ^ m) ^ 4 - (2 ^ m) ^ (i : ℕ)) := by
    refine (Dvd.dvd.trans ?_ hdvd)
    exact (hrd.mul_left _).trans (Dvd.intro _ rfl)
  have hrQ : r ∣ (2 ^ m) ^ 2 + 1 := by
    obtain ⟨i, -, hi⟩ := (Prime.dvd_finsetProd_iff hr.prime _).1 hrGL
    have hi4 : (i : ℕ) < 4 := i.2
    generalize (i : ℕ) = j at hi hi4
    interval_cases j
    · have e : (2 ^ m) ^ 4 - (2 ^ m) ^ 0 = ((2 ^ m) ^ 2 + 1) * ((2 ^ m) ^ 2 - 1) := by
        have e1 : (2 ^ m) ^ 4 = ((2 ^ m) ^ 2) ^ 2 := by ring
        have := Nat.sq_sub_sq ((2 ^ m) ^ 2) 1
        rw [one_pow] at this
        rw [e1, pow_zero]
        exact this
      rw [e] at hi
      rcases (Nat.Prime.dvd_mul hr).1 hi with h | h
      · exact h
      · exact absurd h hnot2
    · have e : (2 ^ m) ^ 4 - (2 ^ m) ^ 1 = 2 ^ m * ((2 ^ m) ^ 3 - 1) := by
        rw [Nat.mul_sub_one, pow_one, ← pow_succ']
      rw [e] at hi
      rcases (Nat.Prime.dvd_mul hr).1 hi with h | h
      · exact absurd h hnotQ
      · exact absurd h hnot3
    · have e : (2 ^ m) ^ 4 - (2 ^ m) ^ 2 = (2 ^ m) ^ 2 * ((2 ^ m) ^ 2 - 1) := by
        rw [Nat.mul_sub_one, ← pow_add]
      rw [e] at hi
      rcases (Nat.Prime.dvd_mul hr).1 hi with h | h
      · exact absurd (hr.dvd_of_dvd_pow h) hnotQ
      · exact absurd h hnot2
    · have e : (2 ^ m) ^ 4 - (2 ^ m) ^ 3 = (2 ^ m) ^ 3 * (2 ^ m - 1) := by
        rw [Nat.mul_sub_one, ← pow_succ]
      rw [e] at hi
      rcases (Nat.Prime.dvd_mul hr).1 hi with h | h
      · exact absurd (hr.dvd_of_dvd_pow h) hnotQ
      · exact absurd h hnot1
  have := Fact.mk hr
  have h1 : (2 : ZMod r) ^ n = 1 := by
    have : ((2 ^ n - 1 : ℕ) : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hrd
    rw [Nat.cast_sub (by omega), Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] at this
    exact sub_eq_zero.1 this
  have h2 : ((2 : ZMod r) ^ m) ^ 2 = -1 := by
    have : (((2 ^ m) ^ 2 + 1 : ℕ) : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hrQ
    push_cast at this
    exact eq_neg_of_add_eq_zero_left this
  have h4 : (2 : ZMod r) ^ (4 * m) = 1 := by
    have e : (2 : ZMod r) ^ (4 * m) = (((2 : ZMod r) ^ m) ^ 2) ^ 2 := by ring
    rw [e, h2]
    exact neg_one_sq
  have hg : (2 : ZMod r) ^ (Nat.gcd n (4 * m)) = 1 := pow_gcd_eq_one.2 ⟨h1, h4⟩
  have hgm : Nat.gcd n (4 * m) ∣ m := by
    have hodd : Odd (Nat.gcd n (4 * m)) := hn.of_dvd_nat (Nat.gcd_dvd_left n (4 * m))
    have hcop : Nat.Coprime (Nat.gcd n (4 * m)) (2 ^ 2) :=
      (Odd.coprime_two_right hodd).pow_right 2
    exact hcop.dvd_of_dvd_mul_left (by simpa using Nat.gcd_dvd_right n (4 * m))
  have h5 : (2 : ZMod r) ^ m = 1 := by
    obtain ⟨c, hc⟩ := hgm
    rw [hc, pow_mul, hg, one_pow]
  rw [h5] at h2
  have h' : (1 : ZMod r) = -1 := by
    rw [one_pow] at h2
    exact h2
  have h6 : (2 : ZMod r) = 0 := by
    have h6' : (1 : ZMod r) + 1 = 0 := by
      calc (1 : ZMod r) + 1 = 1 + -1 := by rw [← h']
        _ = 0 := add_neg_cancel _
    rw [← one_add_one_eq_two]
    exact h6'
  have h7 : r ∣ 2 := by
    have : ((2 : ℕ) : ZMod r) = 0 := by simpa using h6
    exact (ZMod.natCast_eq_zero_iff _ _).1 this
  exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 h7)

section Suz

variable {Y : Type} [CommGroup Y] [Finite Y] {Γ Λ S : Subgroup (MulAut Y)} {V : Subgroup Y}

theorem suz_component_prime
    (hSuz : SuzFFClass) (h : LocCfg Γ Λ S V) (hsz : ∃ n, IsSz n ↥Λ)
    {A : Subgroup (MulAut Y)} (hA : A ∈ QhatStar Γ) (hAS : A ≤ S)
    (hAc : ∀ a ∈ A, ∀ x ∈ Λ, a * x = x * a) {X : Subgroup (MulAut Y)} (hXΓ : X ≤ Γ)
    (hXc : ∀ x ∈ X, ∀ y ∈ Λ, x * y = y * x) (hAX : A ≤ Subgroup.normalizer (X : Set (MulAut Y)))
    (hXA : ⁅X, A⁆ = X) (hX1 : X ≠ ⊥)
    (hcomp : ∃ K : Subgroup (MulAut Y), IsComponentOf K Γ ∧ ¬ IsSuzukiComponent K ∧
      X = ⨆ a ∈ A, conjAutSub a K) (h3 : 3 ∣ Nat.card ↥X) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∣ Nat.card ↥Λ ∧ p ∣ Nat.card ↥X := by
  obtain ⟨W, hW0, hWΛ, hWA, hWX, hBW, hXnt, hUA, hAU, hA3, hrAU⟩ :=
    suz_AxB_data h hA hAc hXc hAX hXA h3
  have hFF := hSuz Y Γ Λ S V h hsz A hA hAS hAc X hXΓ hXc hAX hXA hX1 hcomp h3 W hW0 hWΛ hWA hWX
    hBW hXnt hUA hAU hA3 hrAU
  obtain ⟨n, -, a, ha, K, _, _, hn, hK, ⟨e⟩⟩ := hsz
  subst hn
  have hcard : Nat.card ↥Λ = (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) *
      ((2 ^ (2 * a + 1)) ^ 2 + 1) :=
    (Nat.card_congr e.toEquiv).trans (CFSG.LieType.Ree.suzuki_order hK)
  have h5Λ : 5 ∣ Nat.card ↥Λ := by
    rw [hcard]
    have h5 : 5 ∣ (2 ^ (2 * a + 1)) ^ 2 + 1 := by
      have := Odd.nat_add_dvd_pow_add_pow 4 1 (⟨a, rfl⟩ : Odd (2 * a + 1))
      have e : (2 ^ (2 * a + 1)) ^ 2 = 4 ^ (2 * a + 1) := by
        rw [← pow_mul, mul_comm, pow_mul]; norm_num
      rw [e]
      simpa using this
    exact h5.mul_left _
  rcases hFF with h5 | ⟨m, hm, hdvd, hprimes⟩
  · exact ⟨5, by norm_num, by norm_num, h5Λ, h5⟩
  · rw [hcard] at hdvd
    obtain ⟨p, hp, hp2, hpO, hpD⟩ := suz_arith (n := 2 * a + 1) (by omega) ⟨a, rfl⟩ hdvd
    refine ⟨p, hp, hp2, ?_, hprimes p hp hpD⟩
    rw [hcard]
    exact hpO.trans ⟨(2 ^ (2 * a + 1)) ^ 2, by ring⟩

end Suz

theorem d321LocSuz_of_inputs
    (hD392 : D392) (hB45 : AsB45) (hA21 : AsA21SQTKSection) (hF : Vol2.Ch10.SecA.Facts10_1)
    (hX : Insp5aNonShape) (hSuz : SuzFFClass) : D321LocSuz := by
  intro Y _ _ Γ Λ S V h hsz A hA hAS hunf
  have hAc := suz_central hB45 hA21 hF hX h hsz hA hAS
  have hAcent : A ⊓ Subgroup.centralizer (Λ : Set (MulAut Y)) = A := by
    refine inf_eq_left.2 fun a ha => Subgroup.mem_centralizer_iff.2 fun x hx => ?_
    exact (hAc a ha x hx).symm
  obtain ⟨X, hX1, hXM, hXc, hAX, hXA, hcase, -, -, h3X⟩ :=
    hD392 Y Γ Λ S Λ V h.std rfl h.hq (Or.inl h.VS) A hA hAS hunf
  rw [hAcent] at hXA
  rcases hcase with ⟨K, hKc, hKns, hXK⟩ | ⟨-, hX3⟩
  · obtain ⟨p, hp, hp2, hpΛ, hpX⟩ :=
      suz_component_prime hSuz h hsz hA hAS hAc hXM hXc hAX hXA hX1 ⟨K, hKc, hKns, hXK⟩ h3X
    have := Fact.mk hp
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥X) p hpX
    have hxp : (x : MulAut Y) ^ (p ^ 1) = 1 := by
      have : x ^ p = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
      simpa using congrArg Subtype.val this
    have h1 : (x : MulAut Y) = 1 :=
      h.hK x (hXM x.2) (fun y hy => hXc x x.2 y hy) p hp hp2 hpΛ ⟨1, hxp⟩
    have : x = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hx
    exact hp.one_lt.ne hx
  · exact suz_order_three h hsz hA hAc hXc hAX hXA hX3

end CFSG.Quasithin
