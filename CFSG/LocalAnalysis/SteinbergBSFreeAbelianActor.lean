module

public import CFSG.GroupTheory.HyperplaneGeneration

public section

namespace CFSG.LocalAnalysis.SteinbergBS

open Subgroup

theorem card_ker_powMonoidHom_le {A : Type*} [CommGroup A] [Finite A]
    (h : ∀ p : ℕ, p.Prime → Nat.card (powMonoidHom p : A →* A).ker ≤ p) :
    ∀ n : ℕ, 0 < n → Nat.card (powMonoidHom n : A →* A).ker ≤ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases Nat.lt_or_ge n 2 with hlt | hge
    · obtain rfl : n = 1 := by omega
      have h1 : (powMonoidHom 1 : A →* A).ker = ⊥ := by
        ext x
        simp
      rw [h1, card_bot]
    · have hp : n.minFac.Prime := Nat.minFac_prime (by omega)
      obtain ⟨m, hm⟩ := Nat.minFac_dvd n
      have hm0 : 0 < m := by
        rcases Nat.eq_zero_or_pos m with h0 | h0
        · rw [h0, mul_zero] at hm
          omega
        · exact h0
      have hmn : m < n := by
        calc m = 1 * m := (one_mul m).symm
          _ < n.minFac * m := Nat.mul_lt_mul_of_pos_right hp.one_lt hm0
          _ = n := hm.symm
      let f : (powMonoidHom n : A →* A).ker →* (powMonoidHom m : A →* A).ker :=
        { toFun := fun x => ⟨(x : A) ^ n.minFac, by
            rw [MonoidHom.mem_ker, powMonoidHom_apply, ← pow_mul, ← hm]
            exact x.2⟩
          map_one' := by
            ext
            simp
          map_mul' := fun x y => by
            ext
            simp [mul_pow] }
      have h1 : Nat.card f.ker ≤ n.minFac := by
        refine le_trans (Nat.card_le_card_of_injective
          (fun x => (⟨((x : (powMonoidHom n : A →* A).ker) : A), ?_⟩ :
            (powMonoidHom n.minFac : A →* A).ker)) ?_) (h _ hp)
        · have hx := x.2
          rw [MonoidHom.mem_ker] at hx
          rw [MonoidHom.mem_ker, powMonoidHom_apply]
          exact congrArg Subtype.val hx
        · intro x y hxy
          have hval : ((x : (powMonoidHom n : A →* A).ker) : A) =
              (y : (powMonoidHom n : A →* A).ker) :=
            congrArg (fun z : (powMonoidHom n.minFac : A →* A).ker => (z : A)) hxy
          exact Subtype.ext (Subtype.ext hval)
      have h2 : Nat.card f.range ≤ m :=
        (card_le_card_group f.range).trans (ih m hmn hm0)
      calc Nat.card (powMonoidHom n : A →* A).ker = Nat.card f.ker * Nat.card f.range :=
            (card_ker_mul_card_range f).symm
        _ ≤ n.minFac * m := Nat.mul_le_mul h1 h2
        _ = n := hm.symm

theorem isCyclic_of_card_ker_pow_prime_le {A : Type*} [CommGroup A] [Finite A]
    (h : ∀ p : ℕ, p.Prime → Nat.card (powMonoidHom p : A →* A).ker ≤ p) : IsCyclic A := by
  classical
  let := Fintype.ofFinite A
  refine isCyclic_of_card_pow_eq_one_le fun n hn => ?_
  have hle := card_ker_powMonoidHom_le h n hn
  rwa [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]

theorem abelian_free_nilpotent_actor_cyclic {A N : Type*} [CommGroup A] [Finite A] [Group N]
    [Finite N] [Nontrivial N] [MulDistribMulAction A N]
    (hfree : ∀ a : A, a ≠ 1 → ∀ x : N, a • x = x → x = 1) :
    Nat.Coprime (Nat.card A) (Nat.card N) ∧ IsCyclic A := by
  classical
  have hcop : Nat.Coprime (Nat.card A) (Nat.card N) := by
    by_contra hnc
    obtain ⟨p, hp, hpA, hpN⟩ := Nat.Prime.not_coprime_iff_dvd.1 hnc
    have := Fact.mk hp
    obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' p hpA
    have ha1 : a ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at ha
      exact hp.one_lt.ne ha
    have hZ : IsPGroup p (zpowers a) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha, pow_one])
    have hmod := hZ.card_modEq_card_fixedPoints N
    have hfix : Nat.card (MulAction.fixedPoints (zpowers a) N) = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      refine ⟨⟨fun x y => Subtype.ext ?_⟩, ⟨⟨1, fun g => smul_one _⟩⟩⟩
      rw [hfree a ha1 x (x.2 ⟨a, mem_zpowers a⟩), hfree a ha1 y (y.2 ⟨a, mem_zpowers a⟩)]
    rw [hfix] at hmod
    have h0 : Nat.card N % p = 0 := Nat.mod_eq_zero_of_dvd hpN
    have h1 : 1 % p = 1 := Nat.mod_eq_of_lt hp.one_lt
    unfold Nat.ModEq at hmod
    omega
  refine ⟨hcop, isCyclic_of_card_ker_pow_prime_le fun p hp => ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  have := Fact.mk hp
  set E := (powMonoidHom p : A →* A).ker with hE
  have hEab : IsElementaryAbelian p E :=
    { toIsMulCommutative := ⟨⟨fun x y => mul_comm x y⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext x.2 }
  obtain ⟨k, hk⟩ := (IsElementaryAbelian.isPGroup p E).exists_card_eq
  have hk2 : 2 ≤ k := by
    by_contra hk2
    have hle : p ^ k ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos (by omega)
    rw [← hk, pow_one] at hle
    omega
  have hcard : p ^ 2 ≤ Nat.card E := hk ▸ Nat.pow_le_pow_right hp.pos hk2
  have hpE : p ∣ Nat.card E := hk ▸ dvd_pow_self p (by omega)
  have hpN : ¬ p ∣ Nat.card N := (Nat.Prime.coprime_iff_not_dvd hp).1
    (Nat.Coprime.coprime_dvd_left (hpE.trans (card_subgroup_dvd_card E)) hcop)
  let : MulDistribMulAction E N := MulDistribMulAction.compHom N E.subtype
  have hgen := CFSG.SolvableHall.coprime_centralizer_generation (A := E) (H := N) hcard hpN
  have hbot : (⨆ (a : E) (_ : a ≠ 1), CFSG.fixedPointSubgroup (zpowers a) N) = ⊥ := by
    refine le_bot_iff.1 (iSup₂_le fun a ha x hx => ?_)
    have hax := (CFSG.SolvableHall.mem_fixedPointSubgroup_zpowers_iff a x).1 hx
    exact mem_bot.2 (hfree (a : A) (fun h => ha (Subtype.ext h)) x hax)
  rw [hbot] at hgen
  obtain ⟨x, hx⟩ := exists_ne (1 : N)
  have hxtop : x ∈ (⊤ : Subgroup N) := mem_top x
  rw [← hgen] at hxtop
  exact hx (mem_bot.1 hxtop)

end CFSG.LocalAnalysis.SteinbergBS
