module

public import CFSG.ClassicalGroups.Orthogonal.RootGroupSwap
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.ClassicalGroups.Orthogonal QuadraticMap

theorem omegaA2_isRefl {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) : (polarBilin Q).IsRefl := fun x y h => by
  rw [polarBilin_apply_apply] at h ⊢
  rwa [polar_comm Q]

theorem omegaA2_map_add_smul {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) (x y : V) (t : K) :
    Q (x + t • y) = Q x + t * polar Q x y + t ^ 2 * Q y := by
  rw [QuadraticMap.map_add Q x (t • y), map_smul_eq_sq, polar_smul_right_eq]
  ring

theorem omegaA2_exists_perp {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Q : QuadraticForm K V} (hQ : (polarBilin Q).Nondegenerate)
    (h6 : 6 ≤ Module.finrank K V) {u w e : V} (hu0 : u ≠ 0) (hw : Q w = 0) (he : Q e = 0)
    (huw : polar Q u w = 0) (hue : polar Q u e = 0) (hwe : polar Q w e = 1) :
    ∃ d : V, polar Q u d = 0 ∧ polar Q w d = 0 ∧ polar Q e d = 0 ∧ Q d ≠ 0 := by
  classical
  obtain ⟨S, hS⟩ : ∃ S : Submodule K V, S = Submodule.span K ({u, w, e} : Set V) := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : Submodule K V, D = LinearMap.BilinForm.orthogonal (polarBilin Q) S :=
    ⟨_, rfl⟩
  have hmemD : ∀ x, x ∈ D ↔ ∀ m ∈ S, polar Q m x = 0 := fun x => by
    rw [hD]
    exact LinearMap.BilinForm.mem_orthogonal_iff
  have huS : u ∈ S := by
    rw [hS]
    exact Submodule.subset_span (by simp)
  have hwS : w ∈ S := by
    rw [hS]
    exact Submodule.subset_span (by simp)
  have heS : e ∈ S := by
    rw [hS]
    exact Submodule.subset_span (by simp)
  have hfinS : Module.finrank K S ≤ 3 := by
    have h := finrank_span_finset_le_card (R := K) ({u, w, e} : Finset V)
    have h3 : ({u, w, e} : Finset V).card ≤ 3 := Finset.card_le_three
    rw [hS]
    simp only [Finset.coe_insert, Finset.coe_singleton] at h
    exact le_trans h h3
  have hfinD : Module.finrank K D = Module.finrank K V - Module.finrank K S := by
    rw [hD]
    exact LinearMap.BilinForm.finrank_orthogonal hQ S
  have hfinD3 : 3 ≤ Module.finrank K D := by omega
  have hwu : polar Q w u = 0 := by
    rw [polar_comm]
    exact huw
  have hew : polar Q e w = 1 := by
    rw [polar_comm]
    exact hwe
  have heu : polar Q e u = 0 := by
    rw [polar_comm]
    exact hue
  have hww : polar Q w w = 0 := polar_self_eq_zero hw
  have hee : polar Q e e = 0 := polar_self_eq_zero he
  have hdiv : ∃ d ∈ D, Q d ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hpol : ∀ x ∈ D, ∀ y ∈ D, polar Q x y = 0 := by
      intro x hx y hy
      have h1 := hcon (x + y) (D.add_mem hx hy)
      have h2 := hcon x hx
      have h3 := hcon y hy
      show Q (x + y) - Q x - Q y = 0
      linear_combination h1 - h2 - h3
    have hDle : D ≤ LinearMap.BilinForm.orthogonal (polarBilin Q) D := by
      intro x hx
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro m hm
      exact hpol m hm x hx
    have hOO : LinearMap.BilinForm.orthogonal (polarBilin Q) D = S := by
      rw [hD]
      exact LinearMap.BilinForm.orthogonal_orthogonal hQ (omegaA2_isRefl Q) S
    have hDS : D ≤ S := by
      rw [← hOO]
      exact hDle
    have hDu : D ≤ Submodule.span K {u} := by
      intro d hd
      have hdS : d ∈ S := hDS hd
      rw [hS] at hdS
      obtain ⟨a, b, c, habc⟩ := Submodule.mem_span_triple.1 hdS
      have hc : c = 0 := by
        have h := (hmemD d).1 hd w hwS
        rw [← habc, polar_add_right, polar_add_right, polar_smul_right_eq,
          polar_smul_right_eq, polar_smul_right_eq, hwu, hww, hwe] at h
        linear_combination h
      have hb : b = 0 := by
        have h := (hmemD d).1 hd e heS
        rw [← habc, polar_add_right, polar_add_right, polar_smul_right_eq,
          polar_smul_right_eq, polar_smul_right_eq, heu, hew, hee] at h
        linear_combination h
      rw [Submodule.mem_span_singleton]
      exact ⟨a, by rw [← habc, hb, hc]; simp⟩
    have h1 := Submodule.finrank_mono hDu
    rw [finrank_span_singleton hu0] at h1
    omega
  obtain ⟨d, hdD, hQd⟩ := hdiv
  have hmem := (hmemD d).1 hdD
  exact ⟨d, hmem u huS, hmem w hwS, hmem e heS, hQd⟩

theorem omegaA2Conj_holds :
    ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (V : Type) [AddCommGroup V] [Module K V]
      [FiniteDimensional K V] (Q : QuadraticForm K V), (polarBilin Q).Nondegenerate →
      6 ≤ Module.finrank K V →
      ∀ u w : V, Q u = 0 → polar Q u w = 0 → Q w = 0 → LinearIndependent K ![u, w] →
        ∃ h : Gom Q, h.app u = u ∧ Q (w + h.app w) ≠ 0 := by
  intro K _ _ _ V _ _ _ Q hQ hdim u w _hu huw hw hli
  have hu0 : u ≠ 0 := by simpa using hli.ne_zero 0
  obtain ⟨g, hg⟩ := exists_dual_family hQ hli
  have hue₀ : polar Q u (g 1) = 0 := by simpa using hg 0 1
  have hwe₀ : polar Q w (g 1) = 1 := by simpa using hg 1 1
  have hwe₁ : polar Q (g 1) w = 1 := by
    rw [polar_comm]
    exact hwe₀
  obtain ⟨e, he⟩ : ∃ e : V, e = g 1 + Q (g 1) • w := ⟨_, rfl⟩
  have hQe : Q e = 0 := by
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    rw [he, omegaA2_map_add_smul, hwe₁, hw]
    linear_combination (Q (g 1)) * h2
  have hwe : polar Q w e = 1 := by
    rw [he, polar_add_right, polar_smul_right_eq, hwe₀, polar_self_eq_zero hw, mul_zero,
      add_zero]
  have hue : polar Q u e = 0 := by
    rw [he, polar_add_right, polar_smul_right_eq, hue₀, huw, mul_zero, add_zero]
  obtain ⟨d, hud, hwd, hed, hQd⟩ := omegaA2_exists_perp hQ hdim hu0 hw hQe huw hue hwe
  have hde : polar Q d e = 0 := by
    rw [polar_comm]
    exact hed
  refine ⟨eichlerG Q e d, ?_, ?_⟩
  · rw [eichlerG_app hQe hed u, hue, hud]
    simp
  · rw [eichlerG_app hQe hed w, hwe, hwd, one_smul, zero_add, mul_one]
    have hww2 : w + w = 0 := by
      rw [← two_smul K w, CharTwo.two_eq_zero, zero_smul]
    have hy : w + (w + d - Q d • e) = d - Q d • e := by
      rw [show w + (w + d - Q d • e) = (w + w) + d - Q d • e by abel, hww2, zero_add]
    rw [hy, sub_eq_add_neg, ← neg_smul, omegaA2_map_add_smul, hde, hQe]
    simpa using hQd

end CFSG.RankThree.GF2n.Stroth80
