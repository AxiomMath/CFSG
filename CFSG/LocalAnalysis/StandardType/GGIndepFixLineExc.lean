module

public import CFSG.LocalAnalysis.StandardType.GGIndepFixLineStep4
public import CFSG.LocalAnalysis.StandardType.GGIndepFixLineStep5

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggFixLine_not_orth {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {ι : Type} {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {s : ι → (V ≃ₗ[ZMod p] V)} {x : V}
    (S : GGFixLineHyp p N h α r s x)
    (hF2 : Module.finrank (ZMod p) ↥(ggLinFix (Set.range r)) = 2)
    (Q0 : QuadraticForm (ZMod p) ↥(ggFixLineT r s))
    (hnd : (QuadraticMap.polarBilin Q0).Nondegenerate)
    (hQ : ∀ g ∈ ggFixLineQ S, ZS.IsIsom p Q0 g) : False := by
  classical
  have hB : ∀ g ∈ ggFixLineQ S, ∀ u v,
      (QuadraticMap.polarBilin Q0) (g u) (g v) = (QuadraticMap.polarBilin Q0) u v := by
    intro g hg u v
    have hgQ : ∀ w, Q0 (g w) = Q0 w := hQ g hg
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polarBilin_apply_apply]
    have h1 := QuadraticMap.map_add Q0 (g u) (g v)
    have h2 := QuadraticMap.map_add Q0 u v
    rw [← map_add g u v, hgQ (u + v), hgQ u, hgQ v] at h1
    rw [h1] at h2
    exact add_left_cancel (a := Q0 u + Q0 v) h2
  obtain ⟨w, hw_ne, hw_rad⟩ :=
    ggFixLine_form_degenerate S hF2 (QuadraticMap.polarBilin Q0) hB
  exact hw_ne (hnd.1 w hw_rad)

private lemma l6ke_prime_eq_of_dvd {p q : ℕ} (hq : Nat.Prime q) (hp : Nat.Prime p)
    (h : p ∣ q) : p = q := by
  rcases (Nat.dvd_prime hq).mp h with h1 | hq'
  · exact absurd h1 hp.ne_one
  · exact hq'

private lemma l6ke_prime_eq_three {p : ℕ} (hp : Nat.Prime p) (hp2 : p ≠ 2) (h : p ∣ 6) :
    p = 3 := by
  have h' : p ∣ 2 * 3 := by simpa using h
  rcases hp.dvd_mul.mp h' with h2 | h3
  · rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp h2 with h1 | h2'
    · exact absurd h1 hp.ne_one
    · exact absurd h2' hp2
  · rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp h3 with h1 | h3'
    · exact absurd h1 hp.ne_one
    · exact h3'

private lemma l6ke_center_element {G : Type*} [Group G] (H : Subgroup G)
    {n : ℕ} (hcard : Nat.card ↥(Subgroup.center H) = n) (hn : 1 < n) :
    ∃ c : ↥H, c ∈ Subgroup.center H ∧ c ≠ 1 ∧ orderOf c ∣ n := by
  have hpos : 0 < Nat.card ↥(Subgroup.center H) := by rw [hcard]; omega
  have hfin : Finite ↥(Subgroup.center H) := (Nat.card_pos_iff.mp hpos).2
  haveI : Finite ↥(Subgroup.center H) := hfin
  have h2 : 1 < Nat.card ↥(Subgroup.center H) := by rw [hcard]; exact hn
  haveI : Nontrivial ↥(Subgroup.center H) := (Finite.one_lt_card_iff_nontrivial).mp h2
  obtain ⟨z, hz⟩ := exists_ne (1 : ↥(Subgroup.center H))
  refine ⟨z.1, z.2, ?_, ?_⟩
  · intro h
    exact hz (Subtype.ext h)
  · have h1 := Subgroup.orderOf_dvd_natCard (Subgroup.center H) z.2
    rw [hcard] at h1
    exact h1

private lemma l6ke_gl5_not_dvd {p : ℕ} [Fact p.Prime] (hp : p = 5) :
    ¬ (2 ^ 7 * 3 ^ 4 * 5 ∣ Nat.card (GL (Fin 5) (ZMod p))) := by
  subst hp
  rw [Matrix.card_GL_field 5, ZMod.card 5]
  decide

theorem ggFixLine_not_exc {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {ι : Type} {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {s : ι → (V ≃ₗ[ZMod p] V)} {x : V}
    (S : GGFixLineHyp p N h α r s x)
    (hF2 : Module.finrank (ZMod p) ↥(ggLinFix (Set.range r)) = 2)
    (k : ZS.ExcRow) (hadm : k.admissible p)
    (hdim : Module.finrank (ZMod p) ↥(ggFixLineT r s) = k.deg)
    (hcard : Nat.card ↥(ggFixLineQ S) = k.ord)
    (hcen : Nat.card ↥(Subgroup.center ↥(ggFixLineQ S)) = k.cen) : False := by
  classical
  haveI hι : Finite ι := S.finite_family
  haveI hfinV : Module.Finite (ZMod p) V := ggFixLine_finite (p := p) s S.s_refl S.fix_H
  obtain ⟨_, _, hle_low, hle_high⟩ := ggFixLine_T_props S
  have hN5 : 5 ≤ N := S.five_le
  have hpN : p ∣ N := S.dvd
  have hp_odd : p ≠ 2 := S.odd
  have hp_prime : Nat.Prime p := Fact.out
  haveI hfinT : Module.Finite (ZMod p) ↥(ggFixLineT r s) :=
    FiniteDimensional.finiteDimensional_submodule (ggFixLineT r s)
  cases k <;>
    simp only [ZS.ExcRow.deg, ZS.ExcRow.ord, ZS.ExcRow.cen, ZS.ExcRow.admissible] at hdim hcard hcen hadm
  ·
    have hN : N = 5 := by omega
    have hT : Module.finrank (ZMod p) ↥(ggFixLineT r s) = N - 1 := by omega
    obtain ⟨c, hc, hc1, hord⟩ := l6ke_center_element (ggFixLineQ S) hcen (by norm_num)
    have hcop : Nat.Coprime (orderOf c) p := by
      rw [Nat.coprime_comm]
      refine hp_prime.coprime_iff_not_dvd.mpr ?_
      intro hdiv
      have hp4 : p ∣ 4 := hdiv.trans hord
      have hp4' : p ∣ 2 ^ 2 := by simpa using hp4
      have hp2 : p ∣ 2 := hp_prime.dvd_of_dvd_pow hp4'
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp hp2 with h1 | h2
      · exact hp_prime.ne_one h1
      · exact hp_odd h2
    exact ggFixLine_central_complement S hF2 hT hc hc1 hcop
  ·
    have hN : N = 5 := by omega
    have hT : Module.finrank (ZMod p) ↥(ggFixLineT r s) = N - 1 := by omega
    obtain ⟨c, hc, hc1, hord⟩ := l6ke_center_element (ggFixLineQ S) hcen (by norm_num)
    have hcop : Nat.Coprime (orderOf c) p := by
      rw [Nat.coprime_comm]
      refine hp_prime.coprime_iff_not_dvd.mpr ?_
      intro hdiv
      have hp4 : p ∣ 4 := hdiv.trans hord
      have hp4' : p ∣ 2 ^ 2 := by simpa using hp4
      have hp2 : p ∣ 2 := hp_prime.dvd_of_dvd_pow hp4'
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp hp2 with h1 | h2
      · exact hp_prime.ne_one h1
      · exact hp_odd h2
    exact ggFixLine_central_complement S hF2 hT hc hc1 hcop
  ·
    have hN : N = 5 := by
      rcases (by omega : N = 5 ∨ N = 6) with hN | hN
      · exact hN
      · exfalso
        have hp3 : p = 3 := l6ke_prime_eq_three hp_prime hp_odd (by simpa [hN] using hpN)
        exact hadm hp3
    have hp5 : p = 5 := l6ke_prime_eq_of_dvd (by norm_num : Nat.Prime 5) hp_prime
      (by simpa [hN] using hpN)
    have hdimT : Module.finrank (ZMod p) ↥(ggFixLineT r s) = 5 := by omega
    have hdiv : 2 ^ 7 * 3 ^ 4 * 5 ∣
        Nat.card (↥(ggFixLineT r s) ≃ₗ[ZMod p] ↥(ggFixLineT r s)) := by
      rw [← hcard]
      exact Subgroup.card_subgroup_dvd_card (ggFixLineQ S)
    have hcard_eq :
        Nat.card (↥(ggFixLineT r s) ≃ₗ[ZMod p] ↥(ggFixLineT r s)) =
          Nat.card (GL (Fin 5) (ZMod p)) := by
      let b : Module.Basis (Fin 5) (ZMod p) ↥(ggFixLineT r s) :=
        Module.finBasisOfFinrankEq (ZMod p) ↥(ggFixLineT r s) (n := 5) hdimT
      have h := Nat.card_congr
        ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod p) ↥(ggFixLineT r s)).symm.trans
          (Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toMulEquiv)).toEquiv
      simpa using h
    have hnot : ¬ (2 ^ 7 * 3 ^ 4 * 5 ∣ Nat.card (GL (Fin 5) (ZMod p))) :=
      l6ke_gl5_not_dvd (p := p) hp5
    exact hnot (hcard_eq ▸ hdiv)
  ·
    have hN : N = 7 := by
      rcases (by omega : N = 6 ∨ N = 7) with hN | hN
      · exfalso
        have hp3 : p = 3 := l6ke_prime_eq_three hp_prime hp_odd (by simpa [hN] using hpN)
        exact hadm hp3
      · exact hN
    have hp7 : p = 7 := l6ke_prime_eq_of_dvd (by norm_num : Nat.Prime 7) hp_prime
      (by simpa [hN] using hpN)
    have hT : Module.finrank (ZMod p) ↥(ggFixLineT r s) = N - 1 := by omega
    obtain ⟨c, hc, hc1, hord⟩ := l6ke_center_element (ggFixLineQ S) hcen (by norm_num)
    have hcop : Nat.Coprime (orderOf c) p := by
      rw [Nat.coprime_comm]
      refine hp_prime.coprime_iff_not_dvd.mpr ?_
      intro hdiv
      have hp6 : p ∣ 6 := hdiv.trans hord
      have hp3 : p = 3 := l6ke_prime_eq_three hp_prime hp_odd (by simpa using hp6)
      omega
    exact ggFixLine_central_complement S hF2 hT hc hc1 hcop
  ·
    have hN : N = 5 := by omega
    have hp5 : p = 5 := l6ke_prime_eq_of_dvd (by norm_num : Nat.Prime 5) hp_prime
      (by simpa [hN] using hpN)
    exact hadm hp5
  ·
    omega
  ·
    omega
  ·
    omega
  ·
    omega
  ·
    have hN : N = 5 := by omega
    have hp5 : p = 5 := l6ke_prime_eq_of_dvd (by norm_num : Nat.Prime 5) hp_prime
      (by simpa [hN] using hpN)
    omega

end CFSG.StandardType

end
