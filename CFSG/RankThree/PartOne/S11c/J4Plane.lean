module

public import CFSG.RankThree.PartOne.S11.CatalogLeaves
public import CFSG.RankThree.PartOne.S11c.J4Rank
public import CFSG.Sporadic.Schreier.J4SSylow11

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Blueprint
open CFSG.Blueprint.NativeSporadic (IsSporadic)
open CFSG.Sporadic.J4Schreier CFSG.LinearAlgebra Module Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open scoped commutatorElement

attribute [local instance high] cleanAddCommGroupFin

section MatrixGroup

theorem J4_eq_bot_of_normalized_by_plane (E : Subgroup CFSG.Sporadic.J4.J)
    (hEel : IsElementaryAbelian 11 E) (hEcard : Nat.card E = 11 ^ 2)
    (U : Subgroup CFSG.Sporadic.J4.J) (hU : IsPGroup 2 U)
    (hEU : E ≤ Subgroup.normalizer (U : Set CFSG.Sporadic.J4.J)) : U = ⊥ := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hM := CFSG.Sporadic.J4.j4Facts.mat
  have hS0idx : ¬ 2 ∣ S0.index := by
    have := S0Sylow.not_dvd_index
    rwa [S0Sylow_coe] at this
  have hS0p : IsPGroup 2 S0 := by
    have := S0Sylow.isPGroup'
    rwa [S0Sylow_coe] at this
  have hCN : ∀ h ∈ H, (∀ n ∈ N, h * n = n * h) → h ∈ N := by
    intro h hh hc
    have h1 : h ∈ Subgroup.centralizer (N : Set CFSG.Sporadic.J4.J) ⊓ H :=
      ⟨Subgroup.mem_centralizer_iff.mpr fun n hn => (hc n hn).symm, hh⟩
    rwa [QT_unique_J4_local_normal_module_irreducible.2.2.2.2.2.2.2.2.2] at h1
  have hcov : ∀ n ∈ N, n ≠ 1 → ∃ h ∈ H, n = h * η 1 * h⁻¹ ∨ n = h * η 14 * h⁻¹ := by
    intro n hn hn1
    rcases QT_unique_J4_local_normal_module_irreducible.1 n hn with h | ⟨k, hk, e⟩ | ⟨k, hk, e⟩
    · exact absurd h hn1
    · exact ⟨k, K_le_H hk, Or.inl e⟩
    · exact ⟨k, K_le_H hk, Or.inr e⟩
  have h11 : ¬ 11 ^ 4 ∣ Nat.card CFSG.Sporadic.J4.J := by
    rw [card_J4J]
    norm_num
  exact eq_bot_of_normalized_by_plane rowRep (Module.finrank_fin_fun (ZMod 2))
    formB_nondegenerate (formB_invariant hM) Q11 isExtraspecial_Q11 exponent_Q11
    (x := ⟨qx, qx_mem⟩) (y := ⟨qy, qy_mem⟩) (z := ⟨qz, qz_mem⟩) qz_eq_commutator card_Q11
    closure_Q11_gens h11 (rowRep_ne_one qz_ne_one)
    (fun g hg hpg => hrank_of_local rowRep (Module.finrank_fin_fun (ZMod 2)) H N
      conj_mem_N_of_mem_H hCN (η 1) (η 14) hcov finrank_centralFixed_eta_one
      finrank_centralFixed_eta_fourteen S0 hS0p hS0idx S0_le_H g hg hpg) E hEel hEcard U hU hEU

end MatrixGroup

section Transport

theorem eq_eleven_of_sq_dvd_card_J4 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (h : p ^ 2 ∣ 86775571046077562880) : p = 11 := by
  have e : (86775571046077562880 : ℕ) =
      2 ^ 21 * 3 ^ 3 * 5 * 7 * 11 ^ 3 * 23 * 29 * 31 * 37 * 43 := by norm_num
  rw [e] at h
  have h1 : p ∣ 2 ^ 21 * 3 ^ 3 * 5 * 7 * 11 ^ 3 * 23 * 29 * 31 * 37 * 43 :=
    (dvd_pow_self p two_ne_zero).trans h
  have hq : ∀ q : ℕ, q.Prime → p ∣ q → p = q := fun q hq hpq =>
    (Nat.prime_dvd_prime_iff_eq hp hq).1 hpq
  have key : ∀ a b : ℕ, p ∣ a * b → p ∣ a ∨ p ∣ b := fun a b hab => (Nat.Prime.dvd_mul hp).1 hab
  rcases key _ _ h1 with h1 | h1
  · rcases key _ _ h1 with h1 | h1
    · rcases key _ _ h1 with h1 | h1
      · rcases key _ _ h1 with h1 | h1
        · rcases key _ _ h1 with h1 | h1
          · rcases key _ _ h1 with h1 | h1
            · rcases key _ _ h1 with h1 | h1
              · rcases key _ _ h1 with h1 | h1
                · rcases key _ _ h1 with h1 | h1
                  · have := hq 2 Nat.prime_two (hp.dvd_of_dvd_pow h1)
                    omega
                  · have := hq 3 Nat.prime_three (hp.dvd_of_dvd_pow h1)
                    omega
                · have := hq 5 (by norm_num) h1
                  subst this
                  exact absurd h (by norm_num)
              · have := hq 7 (by norm_num) h1
                subst this
                exact absurd h (by norm_num)
            · exact hq 11 (by norm_num) (hp.dvd_of_dvd_pow h1)
          · have := hq 23 (by norm_num) h1
            subst this
            exact absurd h (by norm_num)
        · have := hq 29 (by norm_num) h1
          subst this
          exact absurd h (by norm_num)
      · have := hq 31 (by norm_num) h1
        subst this
        exact absurd h (by norm_num)
    · have := hq 37 (by norm_num) h1
      subst this
      exact absurd h (by norm_num)
  · have := hq 43 (by norm_num) h1
    subst this
    exact absurd h (by norm_num)

theorem conj_injective_of_simple {T : Type*} [Group T] (hs : IsSimpleGroup T)
    (hnab : ∃ a b : T, a * b ≠ b * a) : Function.Injective (MulAut.conj : T →* MulAut T) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hgc : g ∈ Subgroup.center T := by
    rw [Subgroup.mem_center_iff]
    intro h
    have h1 : g * h * g⁻¹ = h := by
      have := congrArg (fun φ : MulAut T => φ h) hg
      simpa [MulAut.conj_apply] using this
    calc h * g = (g * h * g⁻¹) * g := by rw [h1]
      _ = g * h := by group
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center T) with h | h
  · rw [h] at hgc
    exact Subgroup.mem_bot.mp hgc
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    apply hab
    have ha : a ∈ Subgroup.center T := by rw [h]; exact Subgroup.mem_top a
    exact (Subgroup.mem_center_iff.mp ha b).symm

theorem eq_bot_of_planeOn_J4 {T : Type} [Group T] [Finite T] (hs : IsSimpleGroup T)
    (hnab : ∃ a b : T, a * b ≠ b * a) (hT : IsSporadic T .J4) {p : ℕ} {E : Subgroup (MulAut T)}
    {U : Subgroup T} (hplane : PlaneOn p E U) : U = ⊥ := by
  have hT' : Nonempty (T ≃* NativeSporadic.J4) := hT
  obtain ⟨e⟩ := hT'
  have hp := hplane.prime
  have hp5 : 5 ≤ p := by
    have h3 := hplane.three_lt
    by_contra hlt
    have : p = 4 := by omega
    subst this
    exact absurd hp (by norm_num)
  have := hplane.elementary
  have hEin : E ≤ inner T :=
    (R3E_J4_outer_automorphism_group_no_large_primes ⟨e⟩).2 p hp hp5 E
      (IsElementaryAbelian.isPGroup p E)
  have hinj : Function.Injective (MulAut.conj : T →* MulAut T) := conj_injective_of_simple hs hnab
  set E' : Subgroup T := E.comap (MulAut.conj : T →* MulAut T) with hE'
  have hmap : E'.map (MulAut.conj : T →* MulAut T) = E := Subgroup.map_comap_eq_self hEin
  have hE'card : Nat.card E' = p ^ 2 := by
    rw [← Subgroup.card_map_of_injective hinj, hmap]
    exact hplane.card
  have hnorm : ∀ t ∈ E', ∀ u ∈ U, t * u * t⁻¹ ∈ U := fun t ht u hu => by
    have := hplane.normalized (MulAut.conj t) ht u hu
    simpa [MulAut.conj_apply] using this
  have hcardT : Nat.card T = 86775571046077562880 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.J4.card_J4
  have hp11 : p = 11 := eq_eleven_of_sq_dvd_card_J4 hp hp5 (by
    rw [← hE'card, ← hcardT]
    exact Subgroup.card_subgroup_dvd_card E')
  subst hp11
  have hE'el : IsElementaryAbelian 11 E' := by
    refine
      { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext (hinj ?_)⟩⟩
        exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x => Subtype.ext ?_ }
    · have hE : IsMulCommutative E := hplane.elementary.toIsMulCommutative
      have := hE.is_comm.comm ⟨MulAut.conj (a : T), a.2⟩ ⟨MulAut.conj (b : T), b.2⟩
      simpa [map_mul] using congrArg Subtype.val this
    · apply hinj
      have := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 11 E) ⟨MulAut.conj (x : T), x.2⟩
      simpa [map_pow] using congrArg Subtype.val this
  set eJ : T ≃* CFSG.Sporadic.J4.J :=
    e.trans (CFSG.Sporadic.J4.seedEquiv CFSG.Sporadic.J4.j4Facts.mat) with heJ
  set φ : T →* CFSG.Sporadic.J4.J := (eJ : T →* CFSG.Sporadic.J4.J) with hφ
  have hφinj : Function.Injective φ := eJ.injective
  have hφsurj : Function.Surjective φ := eJ.surjective
  have hU := J4_eq_bot_of_normalized_by_plane (E'.map φ) (IsElementaryAbelian.map φ)
    (by rw [Subgroup.card_map_of_injective hφinj, hE'card]) (U.map φ)
    (hplane.two_group.map _) (by
      intro g hg
      obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hg
      rw [Subgroup.mem_normalizer_iff]
      intro h
      obtain ⟨v, rfl⟩ := hφsurj h
      have e1 : φ t * φ v * (φ t)⁻¹ = φ (t * v * t⁻¹) := by simp
      rw [e1, Subgroup.mem_map_iff_mem hφinj, Subgroup.mem_map_iff_mem hφinj]
      refine ⟨fun hv => hnorm t ht v hv, fun hv => ?_⟩
      have := hnorm t⁻¹ (inv_mem ht) _ hv
      simpa [mul_assoc] using this)
  exact (Subgroup.map_eq_bot_iff_of_injective U hφinj).1 hU

theorem j4LargePrimePlaneCentralization : J4LargePrimePlaneCentralization := by
  intro T _ _ hs hnab hT p E U hplane e _ u hu
  have hU : U = ⊥ := eq_bot_of_planeOn_J4 hs hnab hT hplane
  rw [hU, Subgroup.mem_bot] at hu
  rw [hu, map_one]

end Transport

end CFSG.RankThree.PartOne
