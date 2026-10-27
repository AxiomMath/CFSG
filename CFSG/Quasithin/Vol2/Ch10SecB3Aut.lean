module

public import CFSG.LieType.SteinbergBRAltFiveGL3TwoRank
public import CFSG.Quasithin.Vol2.Ch10SecBCoord

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

@[expose] noncomputable def autQuot2 (K : Type*) [Group K] :
    MulAut K →* MulAut (K ⧸ CFSG.pCore 2 K) where
  toFun φ := quotO2Equiv φ
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl
  map_mul' φ ψ := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl

theorem autQuot2_mk (K : Type*) [Group K] (φ : MulAut K) (k : K) :
    autQuot2 K φ (k : K ⧸ CFSG.pCore 2 K) = ((φ k : K) : K ⧸ CFSG.pCore 2 K) := rfl

theorem card_mulAut_of_equiv_SL32 {Q : Type*} [Group Q]
    (e : Q ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) : Nat.card (MulAut Q) = 336 := by
  rw [Nat.card_congr
    (MulAut.congr (e.trans (CFSG.QuasithinUnique.Setup.Family.slEquivGL 3))).toEquiv]
  exact CFSG.LieType.SteinbergBR.AutGL32.card_mulAut_GL32

theorem card_mulAut_of_equiv_A5 {Q : Type*} [Group Q] (e : Q ≃* alternatingGroup (Fin 5)) :
    Nat.card (MulAut Q) = 120 := by
  rw [Nat.card_congr (CFSG.LieType.SteinbergBR.AltFiveGL3.autEquivPerm e).toEquiv,
    Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

theorem eq_one_of_pow_prime_eq_one {X : Type*} [Group X] [Finite X] {α : X} {p : ℕ}
    (hp : p.Prime) (hα : α ^ p = 1) (hpX : ¬ p ∣ Nat.card X) : α = 1 := by
  rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one hα) with h | h
  · exact orderOf_eq_one_iff.mp h
  · exact absurd (h ▸ orderOf_dvd_natCard α) hpX

theorem mem_of_forall_primePow {G : Type*} [Group G] {X : Subgroup G} {b : G}
    (hb : IsOfFinOrder b) (h : ∀ k : ℕ, IsPrimePow (orderOf (b ^ k)) → b ^ k ∈ X) : b ∈ X := by
  suffices key : ∀ n : ℕ, ∀ c : G, 0 < orderOf c → orderOf c = n →
      (∀ k : ℕ, IsPrimePow (orderOf (c ^ k)) → c ^ k ∈ X) → c ∈ X from
    key _ b hb.orderOf_pos rfl h
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro c hc0 hcn hc
    by_cases hpp : IsPrimePow (orderOf c)
    · simpa using hc 1 (by simpa using hpp)
    by_cases hc1 : orderOf c = 1
    · rw [orderOf_eq_one_iff.mp hc1]
      exact X.one_mem
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hc1
    obtain ⟨a, m, hpm, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hc0.ne' p hp.ne_one
    have ha : a ≠ 0 := by
      rintro rfl
      rw [pow_zero, one_mul] at hnm
      exact hpm (hnm ▸ hpd)
    have hm1 : m ≠ 1 := by
      rintro rfl
      rw [mul_one] at hnm
      exact hpp (hnm ▸ hp.isPrimePow.pow ha)
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hnm
      exact hc0.ne' hnm
    have hpa : 1 < p ^ a := Nat.one_lt_pow ha hp.one_lt
    have hcm : orderOf (c ^ m) = p ^ a := by
      rw [orderOf_pow_of_dvd hm0 (hnm ▸ dvd_mul_left m _), hnm, Nat.mul_div_cancel _ (by omega)]
    have hcp : orderOf (c ^ p ^ a) = m := by
      rw [orderOf_pow_of_dvd (by positivity) (hnm ▸ dvd_mul_right _ m), hnm,
        Nat.mul_div_cancel_left _ (by omega)]
    have h1 : c ^ m ∈ X := hc m (by rw [hcm]; exact hp.isPrimePow.pow ha)
    have h2 : c ^ p ^ a ∈ X := by
      refine ih m ?_ _ (by rw [hcp]; omega) hcp fun k hk => ?_
      · rw [← hcn, hnm]
        exact lt_mul_left (by omega) hpa
      · rw [← pow_mul] at hk ⊢
        exact hc _ hk
    have hcop : Nat.Coprime (p ^ a) m :=
      Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpm)
    have hbez := Nat.gcd_eq_gcd_ab (p ^ a) m
    rw [hcop.gcd_eq_one, Nat.cast_one] at hbez
    have e : c = (c ^ p ^ a) ^ (Nat.gcdA (p ^ a) m) * (c ^ m) ^ (Nat.gcdB (p ^ a) m) := by
      rw [← zpow_natCast, ← zpow_natCast c m, ← zpow_mul, ← zpow_mul, ← zpow_add, ← hbez,
        zpow_one]
    rw [e]
    exact X.mul_mem (X.zpow_mem h2 _) (X.zpow_mem h1 _)

end CFSG.Quasithin.Vol2.Ch10.SecB
