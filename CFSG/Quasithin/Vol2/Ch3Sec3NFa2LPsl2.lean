module

public import CFSG.Quasithin.Vol2.Ch3Sec3L2qFacts
public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2L2Gen

public section

namespace CFSG.Quasithin.H13.NFa2

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Quasithin

theorem psl_two_elt_sq {X : Type} [Group X] (q : ℕ) (hq : q.Prime)
    (h24 : q % 24 = 11 ∨ q % 24 = 13) (hX : StatedClassicalModel X .PSL 2 q 1)
    {s : X} {k : ℕ} (hs : s ^ 2 ^ k = 1) : s * s = 1 := by
  have hq5 : 5 ≤ q := by omega
  have h3 : q % 8 = 3 ∨ q % 8 = 5 := by omega
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hFq : Nat.card (ZMod q) = q := Nat.card_zmod q
  obtain ⟨e⟩ := nonempty_mulEquiv_psl_zmod hq hX
  haveI : Finite X := Finite.of_equiv _ e.symm.toEquiv
  have hA : IsPGroup 2 (Subgroup.zpowers s) := by
    apply IsPGroup.of_card_dvd_pow (n := k)
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one hs
  obtain ⟨P, hAP⟩ := IsPGroup.exists_le_sylow hA
  have hPcard : Nat.card (P : Subgroup X) = 4 :=
    CFSG.Quasithin.H13.L2q.card_sylow_four e hFq hq hq5 h3 P.isPGroup' P.not_dvd_index
  have hPnc : ¬ IsCyclic (P : Subgroup X) := fun h =>
    CFSG.Quasithin.H13.L2q.not_isCyclic_sylow hFq hq hq5
      (CFSG.Quasithin.H13.L2q.isPGroup_map e P.isPGroup')
      (by rw [CFSG.Quasithin.H13.L2q.index_map]; exact P.not_dvd_index)
      ((MulEquiv.isCyclic ((P : Subgroup X).equivMapOfInjective e.toMonoidHom e.injective)).mp h)
  have hdvd : orderOf s ∣ 2 ^ 2 := by
    have h4 := Subgroup.card_dvd_of_le hAP
    rw [hPcard, Nat.card_zpowers] at h4
    exact h4
  obtain ⟨m, hm, hm'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hsq : orderOf s ∣ 2 := by
    interval_cases m
    · simp [hm']
    · simp [hm']
    · exfalso
      have hz : Nat.card (Subgroup.zpowers s) = 4 := by simp [Nat.card_zpowers, hm']
      have hPeq : Subgroup.zpowers s = (P : Subgroup X) :=
        Subgroup.eq_of_le_of_card_ge hAP (by omega)
      have hcyc : IsCyclic (P : Subgroup X) := by
        rw [← hPeq]
        exact Subgroup.isCyclic_zpowers s
      exact hPnc hcyc
  have hs2 : s ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp hsq
  exact (pow_two s).symm.trans hs2

end CFSG.Quasithin.H13.NFa2
