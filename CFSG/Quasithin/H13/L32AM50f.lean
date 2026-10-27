module

public import CFSG.Quasithin.H13.L32AM50b

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open Equiv Equiv.Perm
open scoped IsMulCommutative

theorem Mod16.eq_one_of_stab {M : Type} [CommGroup M] [Finite M] (h16 : Nat.card M = 16)
    {g : MulAut M} {p : ℕ} (hp : p = 5 ∨ p = 7) (hg : g ^ p = 1) {X : Subgroup M}
    (hX : Nat.card X = 4) (hgX : ∀ x ∈ X, g x ∈ X) : g = 1 := by
  classical
  have hpp : p.Prime := by rcases hp with rfl | rfl <;> norm_num
  have : Fact p.Prime := ⟨hpp⟩
  have hXfin : Finite X := Nat.finite_of_card_ne_zero (by rw [hX]; norm_num)
  have hinj : Function.Injective (fun x : X => (⟨g x, hgX x x.2⟩ : X)) := fun a b hab =>
    Subtype.ext (g.injective (congrArg Subtype.val hab))
  set gX : Perm X := Equiv.ofBijective _ hinj.bijective_of_finite with hgXdef
  have hpow : ∀ (n : ℕ) (x : X), ((gX ^ n) x : M) = (g ^ n) x := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ n ih =>
      intro x
      rw [pow_succ, Perm.mul_apply, ih, pow_succ, MulAut.mul_apply]
      rfl
  have hgXp : gX ^ p = 1 := by
    ext x
    rw [hpow, hg]
    rfl
  have hord : orderOf gX ∣ Nat.gcd p 24 := by
    refine Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hgXp) ?_
    have h24 : Nat.card (Perm X) = 24 := by
      rw [Nat.card_perm, hX]
      rfl
    have := orderOf_dvd_natCard (G := Perm X) gX
    rwa [h24] at this
  have hgX1 : gX = 1 := by
    have h1 : Nat.gcd p 24 = 1 := by rcases hp with rfl | rfl <;> norm_num
    rw [h1, Nat.dvd_one, orderOf_eq_one_iff] at hord
    exact hord
  have hXC : ∀ x ∈ X, g x = x := by
    intro x hx
    have := hpow 1 ⟨x, hx⟩
    rw [hgX1, one_pow, pow_one] at this
    exact this.symm
  set Cg : Subgroup M :=
    { carrier := {m | g m = m}
      one_mem' := map_one g
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq] at ha hb ⊢
        rw [map_mul, ha, hb]
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_ofPred_eq] at ha ⊢
        rw [map_inv, ha] } with hCg
  have hXCg : X ≤ Cg := fun x hx => hXC x hx
  have h4 : 4 ∣ Nat.card Cg := by
    rw [← hX]
    exact Subgroup.card_dvd_of_le hXCg
  have h16d : Nat.card Cg ∣ 16 := by
    rw [← h16]
    exact Subgroup.card_subgroup_dvd_card Cg
  have hP : IsPGroup p (Subgroup.zpowers g) := by
    rintro ⟨_, k, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hg, one_zpow]
  have hmod := hP.card_modEq_card_fixedPoints M
  have hfix : Nat.card (MulAction.fixedPoints (Subgroup.zpowers g) M) = Nat.card Cg := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun m => ?_)
    constructor
    · intro hm
      exact hm ⟨g, Subgroup.mem_zpowers g⟩
    · rintro hm ⟨_, k, rfl⟩
      show (g ^ k) m = m
      have hm' : g m = m := hm
      induction k using Int.induction_on with
      | zero => rfl
      | succ n ih => rw [zpow_add_one, MulAut.mul_apply, hm', ih]
      | pred n ih =>
        rw [zpow_sub_one, MulAut.mul_apply]
        have : g⁻¹ m = m := by
          conv_lhs => rw [← hm']
          exact MulAut.inv_apply_self M g m
        rw [this, ih]
  rw [hfix, h16] at hmod
  have hC16 : Nat.card Cg = 16 := by
    have hle : Nat.card Cg ≤ 16 := Nat.le_of_dvd (by norm_num) h16d
    obtain ⟨c, hc⟩ := h4
    have hc4 : c ≤ 4 := by omega
    interval_cases c <;> rcases hp with rfl | rfl <;> simp_all [Nat.ModEq]
  have htop : Cg = ⊤ := Subgroup.eq_top_of_card_eq Cg (hC16.trans h16.symm)
  refine MulEquiv.ext fun m => ?_
  have : m ∈ Cg := by rw [htop]; trivial
  exact this

theorem Alt7.card_dvd_72 {N : Subgroup (Perm (Fin 7))} (hNA : N ≤ alternatingGroup (Fin 7))
    (h5 : ∀ x ∈ N, x ^ 5 = 1 → x = 1) (h7 : ∀ x ∈ N, x ^ 7 = 1 → x = 1) :
    Nat.card N ∣ 72 := by
  have hdvd : Nat.card N ∣ 2520 := by
    rw [← Alt7.card_alt7]
    exact Subgroup.card_dvd_of_le hNA
  have hp : ∀ p : ℕ, p.Prime → (∀ x ∈ N, x ^ p = 1 → x = 1) → ¬ p ∣ Nat.card N := by
    intro p hp hN hpd
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥N) p hpd
    have h1 : (x : Perm (Fin 7)) ^ p = 1 := by
      rw [← hx, ← Subgroup.orderOf_coe]
      exact pow_orderOf_eq_one _
    have h2 := hN x x.2 h1
    have h3 : x = 1 := Subtype.ext h2
    rw [h3, orderOf_one] at hx
    exact hp.one_lt.ne hx
  have h5' := hp 5 (by norm_num) h5
  have h7' := hp 7 (by norm_num) h7
  obtain ⟨k, hk⟩ := hdvd
  have hc5 : Nat.Coprime (Nat.card N) 5 :=
    (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr h5'))
  have hc7 : Nat.Coprime (Nat.card N) 7 :=
    (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr h7'))
  have hc : Nat.Coprime (Nat.card N) 35 := by
    rw [show (35 : ℕ) = 5 * 7 by norm_num]
    exact Nat.Coprime.mul_right hc5 hc7
  have : Nat.card N ∣ 72 * 35 := by rw [show 72 * 35 = 2520 by norm_num]; exact ⟨k, hk⟩
  exact hc.dvd_of_dvd_mul_right this

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

namespace Top50

variable {W K : Subgroup G} {π : ↥H →* Perm (Fin 7)} (C : Top50 T L V H W K π)
  [IsMulCommutative ↥(conjClosure V H)]
include C

@[expose] def stabHat (X : Subgroup (Hat V H W)) : Subgroup (Perm (Fin 7)) where
  carrier := {γ | ∃ hγ : γ ∈ alternatingGroup (Fin 7),
    ∀ x ∈ X, ((C.iota.symm ⟨γ, hγ⟩ : ↥C.autK) : MulAut (Hat V H W)) x ∈ X ∧
      ((C.iota.symm ⟨γ, hγ⟩ : ↥C.autK) : MulAut (Hat V H W))⁻¹ x ∈ X}
  one_mem' := ⟨(alternatingGroup (Fin 7)).one_mem, fun x hx => by
    have : C.iota.symm ⟨1, (alternatingGroup (Fin 7)).one_mem⟩ = 1 := map_one C.iota.symm
    rw [this]
    exact ⟨hx, hx⟩⟩
  mul_mem' := by
    rintro a b ⟨ha, hha⟩ ⟨hb, hhb⟩
    refine ⟨(alternatingGroup (Fin 7)).mul_mem ha hb, fun x hx => ?_⟩
    have e : C.iota.symm ⟨a * b, (alternatingGroup (Fin 7)).mul_mem ha hb⟩ =
        C.iota.symm ⟨a, ha⟩ * C.iota.symm ⟨b, hb⟩ := by
      rw [← map_mul]
      rfl
    rw [e, Subgroup.coe_mul, mul_inv_rev, MulAut.mul_apply, MulAut.mul_apply]
    exact ⟨(hha _ (hhb x hx).1).1, (hhb _ (hha x hx).2).2⟩
  inv_mem' := by
    rintro a ⟨ha, hha⟩
    refine ⟨(alternatingGroup (Fin 7)).inv_mem ha, fun x hx => ?_⟩
    have e : C.iota.symm ⟨a⁻¹, (alternatingGroup (Fin 7)).inv_mem ha⟩ =
        (C.iota.symm ⟨a, ha⟩)⁻¹ := by
      rw [← map_inv]
      rfl
    rw [e, Subgroup.coe_inv, inv_inv]
    exact ⟨(hha x hx).2, (hha x hx).1⟩

theorem card_stabHat_dvd (h16 : Nat.card (Hat V H W) = 16) {X : Subgroup (Hat V H W)}
    (hX : Nat.card X = 4) : Nat.card (C.stabHat X) ∣ 72 := by
  have key : ∀ x ∈ C.stabHat X, ∀ p : ℕ, (p = 5 ∨ p = 7) → x ^ p = 1 → x = 1 := by
    rintro x ⟨hx, hxX⟩ p hp hxp
    have h1 : ((C.iota.symm ⟨x, hx⟩ : ↥C.autK) : MulAut (Hat V H W)) ^ p = 1 := by
      have : (⟨x, hx⟩ : ↥(alternatingGroup (Fin 7))) ^ p = 1 := Subtype.ext hxp
      rw [← Subgroup.coe_pow, ← map_pow, this, map_one, Subgroup.coe_one]
    have h2 := Mod16.eq_one_of_stab h16 hp h1 hX fun y hy => (hxX y hy).1
    have h3 : C.iota.symm ⟨x, hx⟩ = 1 := Subtype.ext h2
    have h4 : (⟨x, hx⟩ : ↥(alternatingGroup (Fin 7))) = 1 := by
      have := congrArg C.iota h3
      rwa [MulEquiv.apply_symm_apply, map_one] at this
    exact congrArg Subtype.val h4
  exact Alt7.card_dvd_72 (fun x hx => hx.1) (fun x hx h => key x hx 5 (Or.inl rfl) h)
    (fun x hx h => key x hx 7 (Or.inr rfl) h)

end Top50

end CFSG.Quasithin.H13.L32A.C
