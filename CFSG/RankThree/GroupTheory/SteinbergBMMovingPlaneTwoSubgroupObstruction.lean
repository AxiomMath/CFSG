module

public import CFSG.RankThree.GroupTheory.SteinbergBYMinimalCoprimeAction
public import CFSG.GroupTheory.HyperplaneGeneration
public import CFSG.CharacterTheory.Semidihedral.ElementaryActionTransport
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ActionTransport

public section

namespace CFSG.RankThree.GroupTheory.SteinbergBM

open Subgroup CFSG
open scoped IsMulCommutative

theorem exists_dvd_two_pow_sub_one_of_dvd_card_GL_two {p d : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : p ∣ Nat.card (Matrix.GeneralLinearGroup (Fin d) (ZMod 2))) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ d ∧ p ∣ 2 ^ k - 1 := by
  rw [Matrix.card_GL_field, ZMod.card] at h
  obtain ⟨i, -, hi⟩ := (Prime.dvd_finsetProd_iff hp.prime _).mp h
  have hid : (i : ℕ) < d := i.2
  have hsplit : 2 ^ d - 2 ^ (i : ℕ) = 2 ^ (i : ℕ) * (2 ^ (d - i) - 1) := by
    rw [Nat.mul_sub_one, ← pow_add, Nat.add_sub_cancel' hid.le]
  rw [hsplit] at hi
  have hcop : Nat.Coprime p (2 ^ (i : ℕ)) :=
    Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  exact ⟨d - i, by omega, by omega, hcop.dvd_of_dvd_mul_left hi⟩

theorem four_le_of_five_dvd_card_GL_two {d : ℕ}
    (h : 5 ∣ Nat.card (Matrix.GeneralLinearGroup (Fin d) (ZMod 2))) : 4 ≤ d := by
  obtain ⟨k, hk1, hkd, hdvd⟩ :=
    exists_dvd_two_pow_sub_one_of_dvd_card_GL_two (by norm_num) (by norm_num) h
  by_contra hd
  have hk : k < 4 := by omega
  interval_cases k <;> norm_num at hdvd

theorem three_le_of_seven_dvd_card_GL_two {d : ℕ}
    (h : 7 ∣ Nat.card (Matrix.GeneralLinearGroup (Fin d) (ZMod 2))) : 3 ≤ d := by
  obtain ⟨k, hk1, hkd, hdvd⟩ :=
    exists_dvd_two_pow_sub_one_of_dvd_card_GL_two (by norm_num) (by norm_num) h
  by_contra hd
  have hk : k < 3 := by omega
  interval_cases k <;> norm_num at hdvd

theorem ten_le_of_eleven_dvd_card_GL_two {d : ℕ}
    (h : 11 ∣ Nat.card (Matrix.GeneralLinearGroup (Fin d) (ZMod 2))) : 10 ≤ d := by
  obtain ⟨k, hk1, hkd, hdvd⟩ :=
    exists_dvd_two_pow_sub_one_of_dvd_card_GL_two (by norm_num) (by norm_num) h
  by_contra hd
  have hk : k < 10 := by omega
  interval_cases k <;> norm_num at hdvd

theorem moving_large_prime_plane_two_subgroup_fixed_line_and_small_order_obstruction
    {E U : Type*} [Group E] [Group U] [Finite E] [Finite U] [MulDistribMulAction E U]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) [IsElementaryAbelian p E] (hE : Nat.card E = p ^ 2)
    (hU : IsPGroup 2 U) (hUE : commutatorAction E U ≠ ⊥) :
    ∃ (R : Subgroup U) (hR : ∀ e : E, ∀ r ∈ R, e • r ∈ R) (D : Subgroup E),
      Nat.card D = p ∧ commutatorSubgroup E U R = R ∧ R ≠ ⊥ ∧
      D = fixingSubgroup E (R : Set U) ∧
      (letI := RankThreeEvenClassification.Helpers.invariantSubgroupAction R hR;
        letI := SteinbergBY.frattiniQuotientAction E R;
        Nontrivial (R ⧸ frattini R) ∧ IsElementaryAbelian 2 (R ⧸ frattini R) ∧
          (∀ e : E, e ∈ D ↔ ∀ v : R ⧸ frattini R, e • v = v) ∧
          (∃ ψ : E ⧸ D →* MulAut (R ⧸ frattini R), Function.Injective ψ ∧
            ∀ (e : E) (v : R ⧸ frattini R), ψ (e : E ⧸ D) v = e • v) ∧
          (∃ (e : E) (v : R ⧸ frattini R), e • v ≠ v) ∧
          ∀ S : Subgroup (R ⧸ frattini R), (∀ e : E, ∀ s ∈ S, e • s ∈ S) → S = ⊥ ∨ S = ⊤) ∧
      (∃ d : ℕ, Nat.card (R ⧸ frattini R) = 2 ^ d) ∧
      (∀ d : ℕ, Nat.card (R ⧸ frattini R) = 2 ^ d →
        p ∣ Nat.card (Matrix.GeneralLinearGroup (Fin d) (ZMod 2))) ∧
      (p = 5 → 16 ≤ Nat.card R) ∧ (p = 7 → 8 ≤ Nat.card R) ∧ (p = 11 → 1024 ≤ Nat.card R) ∧
      (p = 5 → Nat.card R = 16 → IsElementaryAbelian 2 R) ∧
      (∀ β ∈ D, β ≠ 1 → ∀ r ∈ R, β • r = r) ∧ ∀ γ : E, γ ∉ D → ∃ r ∈ R, γ • r ≠ r := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hEpow : ∀ e : E, e ^ p = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p p E)
  have hE2 : ¬ 2 ∣ Nat.card E := by
    rw [hE]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp
      (Nat.prime_two.dvd_of_dvd_pow h)).symm
  let Good : Subgroup U → Prop := fun R =>
    (∀ e : E, ∀ r ∈ R, e • r ∈ R) ∧ ∃ e : E, ∃ r ∈ R, e • r ≠ r
  have hgood : Good ⊤ := by
    refine ⟨fun _ _ _ => mem_top _, ?_⟩
    by_contra h
    push Not at h
    apply hUE
    rw [commutatorAction_eq_closure, eq_bot_iff, closure_le]
    rintro _ ⟨e, u, rfl⟩
    rw [SetLike.mem_coe, mem_bot, h e u (mem_top u), inv_mul_cancel]
  have hex : ∃ n : ℕ, ∃ R : Subgroup U, Good R ∧ Nat.card R = n := ⟨_, ⊤, hgood, rfl⟩
  obtain ⟨R, ⟨hR, e₀, r₀, hr₀, hmove₀⟩, hRn⟩ := Nat.find_spec hex
  have hRmin : ∀ S : Subgroup U, Good S → Nat.card R ≤ Nat.card S := fun S hS =>
    hRn ▸ Nat.find_min' hex ⟨S, hS, rfl⟩
  let _ : MulDistribMulAction E R :=
    RankThreeEvenClassification.Helpers.invariantSubgroupAction R hR
  have hP : IsPGroup 2 R := hU.to_subgroup R
  have hnt : ∃ (e : E) (q : R), e • q ≠ q :=
    ⟨e₀, ⟨r₀, hr₀⟩, fun h => hmove₀ (congrArg Subtype.val h)⟩
  have hmin : ∀ S : Subgroup R, S ≠ ⊤ → (∀ (e : E), ∀ s ∈ S, e • s ∈ S) →
      ∀ (e : E), ∀ s ∈ S, e • s = s := by
    intro S hS hSinv
    by_contra hcon
    push Not at hcon
    obtain ⟨e, s, hs, hes⟩ := hcon
    have hgoodS : Good (S.map R.subtype) := by
      refine ⟨?_, e, s, mem_map_of_mem _ hs, fun h => hes (Subtype.ext h)⟩
      rintro a _ ⟨t, ht, rfl⟩
      exact mem_map_of_mem _ (hSinv a t ht)
    have hle := hRmin _ hgoodS
    rw [card_map_of_injective R.subtype_injective] at hle
    exact hS ((card_eq_iff_eq_top S).mp (le_antisymm (card_le_card_group S) hle))
  obtain ⟨htop, -, ⟨hVnt, hVel, hVmove, hVirr⟩, -, -⟩ :=
    SteinbergBY.minimal_coprime_action_elementary_or_special (l := 2) hP hE2 hnt hmin
  have hcomm : commutatorSubgroup E U R = R := by
    have h1 : commutatorSubgroup E U R = (commutatorAction E R).map R.subtype := by
      rw [commutatorAction_eq_closure, MonoidHom.map_closure, commutatorSubgroup]
      congr 1
      ext x
      constructor
      · rintro ⟨a, h, hh, rfl⟩
        exact ⟨⟨h, hh⟩⁻¹ * (a • ⟨h, hh⟩), ⟨a, ⟨h, hh⟩, rfl⟩, rfl⟩
      · rintro ⟨y, ⟨a, g, rfl⟩, rfl⟩
        exact ⟨a, g, g.2, rfl⟩
    rw [h1, htop, ← MonoidHom.range_eq_map, range_subtype]
  have hR1 : R ≠ ⊥ := by
    intro h
    rw [h, mem_bot] at hr₀
    rw [hr₀, smul_one] at hmove₀
    exact hmove₀ rfl
  let _ : MulDistribMulAction E (R ⧸ frattini R) := SteinbergBY.frattiniQuotientAction E R
  have : IsElementaryAbelian 2 (R ⧸ frattini R) := hVel
  have : Nontrivial (R ⧸ frattini R) := hVnt
  set ρ := Semidihedral.ElementaryActionTransport.primeFieldAction (p := 2)
    (MulDistribMulAction.toMulAut E (R ⧸ frattini R)) with hρ
  set D : Subgroup E := (MulDistribMulAction.toMulAut E (R ⧸ frattini R)).ker with hD
  have hDmem : ∀ e : E, e ∈ D ↔ ∀ v : R ⧸ frattini R, e • v = v := by
    intro e
    rw [hD, MonoidHom.mem_ker]
    constructor
    · intro h v
      exact congrArg (fun σ : MulAut (R ⧸ frattini R) => σ v) h
    · intro h
      ext v
      exact h v
  have hcyc : IsCyclic ρ.range := by
    refine SolvableHall.abelian_irreducible_action_cyclic_image ρ fun W hW => ?_
    set S := (Semidihedral.ElementaryActionTransport.subgroupEquivSubmodule (p := 2)
      (R := R ⧸ frattini R)).symm W with hS
    have hSinv : ∀ e : E, ∀ s ∈ S, e • s ∈ S := fun e s hs => hW e (Additive.ofMul s) hs
    have hW' : W = Semidihedral.ElementaryActionTransport.subgroupEquivSubmodule (p := 2) S :=
      (OrderIso.apply_symm_apply _ W).symm
    rcases hVirr S hSinv with h | h
    · left
      rw [hW', h, OrderIso.map_bot]
    · right
      rw [hW', h, OrderIso.map_top]
  have hker : ρ.ker = D := Semidihedral.ElementaryActionTransport.primeFieldAction_kernel _
  have hrangep : Nat.card ρ.range ∣ p := by
    rw [← IsCyclic.exponent_eq_card]
    refine Monoid.exponent_dvd_of_forall_pow_eq_one fun x => ?_
    obtain ⟨_, e, rfl⟩ := x
    exact Subtype.ext (by simp [← map_pow, hEpow])
  have hrange1 : Nat.card ρ.range ≠ 1 := by
    intro h1
    obtain ⟨e, v, hev⟩ := hVmove
    apply hev
    have he : e ∈ D := by
      rw [← hker, MonoidHom.mem_ker]
      have hmem : ρ e ∈ ρ.range := ⟨e, rfl⟩
      rw [card_eq_one.mp h1] at hmem
      exact mem_bot.mp hmem
    exact (hDmem e).mp he v
  have hrange : Nat.card ρ.range = p :=
    ((Nat.dvd_prime hp).mp hrangep).resolve_left hrange1
  have hDcard : Nat.card D = p := by
    have h := card_ker_mul_card_range ρ
    rw [hker, hrange, hE, pow_two] at h
    exact Nat.eq_of_mul_eq_mul_right hp.pos h
  obtain ⟨hquot, hker2⟩ := GroupTheory.frattini_automorphism_kernel hP
  have hDR : ∀ e : E, e ∈ D ↔ ∀ r ∈ R, e • r = r := by
    intro e
    constructor
    · intro he r hr
      set σ := MulDistribMulAction.toMulAut E R e with hσ
      have hσker : σ ∈ (OrderReductions.FrattiniAutomorphisms.quotientAutomorphism
          (frattini R)).ker := by
        rw [MonoidHom.mem_ker]
        ext v
        obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective v
        rw [hquot, MulAut.one_apply]
        exact (hDmem e).mp he q
      have hσp : σ ^ p = 1 := by rw [hσ, ← map_pow, hEpow, map_one]
      obtain ⟨i, hi⟩ := hker2 ⟨σ, hσker⟩
      have hσi : σ ^ 2 ^ i = 1 := congrArg Subtype.val hi
      have hcop : Nat.Coprime (2 ^ i) p :=
        Nat.Coprime.pow_left i ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
      have hord : orderOf σ = 1 := Nat.eq_one_of_dvd_coprimes hcop
        (orderOf_dvd_of_pow_eq_one hσi) (orderOf_dvd_of_pow_eq_one hσp)
      exact congrArg (fun τ : MulAut R => ((τ ⟨r, hr⟩ : R) : U)) (orderOf_eq_one_iff.mp hord)
    · intro h
      rw [hDmem]
      intro v
      obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective v
      change ((e • q : R) : R ⧸ frattini R) = q
      rw [show e • q = q from Subtype.ext (h q q.2)]
  have hDfix : D = fixingSubgroup E (R : Set U) := by
    ext e
    rw [mem_fixingSubgroup_iff, hDR]
    rfl
  have hψ : ∃ ψ : E ⧸ D →* MulAut (R ⧸ frattini R), Function.Injective ψ ∧
      ∀ (e : E) (v : R ⧸ frattini R), ψ (e : E ⧸ D) v = e • v :=
    ⟨QuotientGroup.kerLift _, QuotientGroup.kerLift_injective _, fun _ _ => rfl⟩
  have hGL : ∀ d : ℕ, Nat.card (R ⧸ frattini R) = 2 ^ d →
      p ∣ Nat.card (Matrix.GeneralLinearGroup (Fin d) (ZMod 2)) := by
    intro d hd
    have hfin : Module.finrank (ZMod 2) (Additive (R ⧸ frattini R)) = d := by
      have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive (R ⧸ frattini R))
      rw [Nat.card_zmod] at h
      have h' : Nat.card (Additive (R ⧸ frattini R)) = Nat.card (R ⧸ frattini R) := rfl
      rw [h', hd] at h
      exact (Nat.pow_right_injective le_rfl h).symm
    let b := Module.finBasisOfFinrankEq (ZMod 2) (Additive (R ⧸ frattini R)) hfin
    have hcard : Nat.card (Matrix.GeneralLinearGroup (Fin d) (ZMod 2)) =
        Nat.card (LinearMap.GeneralLinearGroup (ZMod 2) (Additive (R ⧸ frattini R))) :=
      Nat.card_congr (Matrix.GeneralLinearGroup.toLin' b).toEquiv
    rw [hcard, ← hrange]
    exact card_subgroup_dvd_card ρ.range
  have hcardR : ∀ d : ℕ, Nat.card (R ⧸ frattini R) = 2 ^ d → 2 ^ d ≤ Nat.card R := by
    intro d hd
    rw [← hd]
    exact Nat.le_of_dvd Nat.card_pos (card_quotient_dvd_card _)
  obtain ⟨d, hd⟩ := (hP.to_quotient (frattini R)).exists_card_eq
  have hdvdGL := hGL d hd
  refine ⟨R, hR, D, hDcard, hcomm, hR1, hDfix, ⟨hVnt, hVel, hDmem, hψ, hVmove, hVirr⟩, ⟨d, hd⟩,
    hGL, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro rfl
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) (four_le_of_five_dvd_card_GL_two hdvdGL)
      _ ≤ Nat.card R := hcardR d hd
  · rintro rfl
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) (three_le_of_seven_dvd_card_GL_two hdvdGL)
      _ ≤ Nat.card R := hcardR d hd
  · rintro rfl
    calc 1024 = 2 ^ 10 := by norm_num
      _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) (ten_le_of_eleven_dvd_card_GL_two hdvdGL)
      _ ≤ Nat.card R := hcardR d hd
  · rintro rfl h16
    have h4 := four_le_of_five_dvd_card_GL_two hdvdGL
    have hdle : 2 ^ d ≤ 2 ^ 4 := (hcardR d hd).trans h16.le
    have hd4 : d = 4 := le_antisymm ((Nat.pow_le_pow_iff_right (by norm_num)).mp hdle) h4
    have hF : frattini R = ⊥ := by
      have h := card_eq_card_quotient_mul_card_subgroup (frattini R)
      rw [h16, hd, hd4] at h
      exact card_eq_one.mp (by omega)
    have hcommR : ∀ x y : R, x * y = y * x := by
      intro x y
      have h := hVel.toIsMulCommutative.is_comm.comm (x : R ⧸ frattini R) y
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, hF, mem_bot] at h
      exact inv_mul_eq_one.mp h
    have hsq : ∀ x : R, x ^ 2 = 1 := by
      intro x
      have h := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 (R ⧸ frattini R)) (x : R ⧸ frattini R)
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, hF, mem_bot] at h
      exact h
    exact { toIsMulCommutative := ⟨⟨hcommR⟩⟩
            exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hsq }
  · intro β hβ _ r hr
    exact (hDR β).mp hβ r hr
  · intro γ hγ
    by_contra h
    push Not at h
    exact hγ ((hDR γ).mpr h)

end CFSG.RankThree.GroupTheory.SteinbergBM
