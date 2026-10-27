module

public import CFSG.Quasithin.Vol2.F134L2
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieBridge

public section

namespace CFSG.Quasithin.H13.NQCore

open CFSG.Quasithin CFSG.Quasithin.F134 CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

theorem isCyclic_of_card_eq_one' {G : Type*} [Group G] (h : Nat.card G = 1) : IsCyclic G :=
  @isCyclic_of_subsingleton G _ (Nat.card_eq_one_iff_unique.mp h).1

theorem isCyclic_of_isPGroup_psl2 {r f p : ℕ} [hr : Fact r.Prime]
    [hp : Fact p.Prime] (hpr : p ≠ r) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    {Q : Subgroup PSL(2, GaloisField r f)} (hQ : IsPGroup p Q) : IsCyclic Q := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hQ
  have hodd : ¬ 2 ∣ Nat.card Q := fun h => hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two
    hp.out).1 (Nat.prime_two.dvd_of_dvd_pow (hk ▸ h))).symm
  have hrm : ∀ m : ℕ, r ^ m ∣ p ^ k → m = 0 := by
    intro m hm
    by_contra hm0
    have h1 : r ∣ p ^ k := (dvd_pow_self r hm0).trans hm
    exact hpr ((Nat.prime_dvd_prime_iff_eq hr.out hp.out).1 (hr.out.dvd_of_dvd_pow h1)).symm
  have hcentre : ∀ {Y : Type} [Group Y], (Q ≃* Y) → Subgroup.center Y = ⊥ → IsCyclic Q := by
    intro Y _ e hY
    have hc : Subgroup.center Q = ⊥ := CFSG.Quasithin.F420.center_eq_bot_of_mulEquiv' e hY
    by_cases h1 : Nat.card Q = 1
    · exact isCyclic_of_card_eq_one' h1
    · exfalso
      have : Nontrivial Q := Finite.one_lt_card_iff_nontrivial.mp (by
        have := Nat.card_pos (α := Q)
        omega)
      have hn := hQ.center_nontrivial
      rw [hc] at hn
      exact (not_nontrivial_iff_subsingleton.mpr (inferInstance : Subsingleton (⊥ : Subgroup Q)))
        hn
  rcases F6.dicksonPSL2_holds r f hf Q with
      ⟨-, m, -, hm⟩ | ⟨hc, -⟩ | ⟨z, -, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ |
      ⟨m, t, P, hPn, -, hPc, hQc, hQt, -, -⟩ | ⟨m, -, ⟨e⟩⟩ | ⟨m, -, ⟨e⟩⟩
  · have hm0 : m = 0 := hrm m (by rw [← hm, hk])
    exact isCyclic_of_card_eq_one' (by rw [hm, hm0, pow_zero])
  · exact hc
  · have := Nat.card_congr e.toEquiv
    rw [DihedralGroup.nat_card] at this
    exact absurd (this ▸ dvd_mul_right 2 z) hodd
  · have := Nat.card_congr e.toEquiv
    rw [card_alternating_four] at this
    exact absurd (by rw [this]; norm_num) hodd
  · have := Nat.card_congr e.toEquiv
    rw [card_perm_four] at this
    exact absurd (by rw [this]; norm_num) hodd
  · have := Nat.card_congr e.toEquiv
    rw [card_alternating_five] at this
    exact absurd (by rw [this]; norm_num) hodd
  · have hPQ : Nat.card P ∣ Nat.card Q := Subgroup.card_subgroup_dvd_card P
    have hm0 : m = 0 := hrm m (by rw [← hPc, ← hk]; exact hPQ)
    have hPbot : P = ⊥ := Subgroup.card_eq_one.mp (by rw [hPc, hm0, pow_zero])
    subst hPbot
    exact isCyclic_of_surjective (QuotientGroup.quotientBot.toMonoidHom)
      QuotientGroup.quotientBot.surjective
  · exact hcentre e (CFSG.GorensteinWalter.psl2_center_eq_bot (GaloisField r m))
  · exact hcentre e (CFSG.GorensteinWalter.pgl2_center_eq_bot (GaloisField r m))

theorem psl2Even_simple (n : ℕ) :
    NoOddCfg fun (X : Type) [Group X] => StatedClassicalModel X .PSL 2 2 n := by
  intro A _ _ p hp L P T hp5 hL hcfg
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := nonempty_mulEquiv_psl2 hL
  set Q' : Subgroup PSL(2, GaloisField 2 n) := (P.subgroupOf L).map e.toMonoidHom with hQ'
  have hPQ : ↥P ≃* ↥Q' :=
    (Subgroup.subgroupOfEquivOfLe hcfg.le).symm.trans
      ((P.subgroupOf L).equivMapOfInjective e.toMonoidHom e.injective)
  have hQp : IsPGroup p Q' := hcfg.isPGroup.of_equiv hPQ
  have hcyc := isCyclic_of_isPGroup_psl2 (r := 2) (p := p) (by omega) (by omega) hL.1.2.1 hQp
  exact hcfg.not_isCyclic (isCyclic_of_surjective hPQ.symm.toMonoidHom hPQ.symm.surjective)

theorem liePsl2Even : LiePsl2Even := fun n =>
  noOddConfigQ_of_noOddCfg (isoInvariant_stated .PSL 2 2 n) (psl2Even_simple n)

end CFSG.Quasithin.H13.NQCore
