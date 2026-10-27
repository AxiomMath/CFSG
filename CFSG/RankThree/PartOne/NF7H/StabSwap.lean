module

public import CFSG.RankThree.PartOne.N1322.CaseBasic
public import CFSG.RankThree.PartOne.N1322.CoreHyp

public section

namespace CFSG.RankThree.PartOne.NF7H

open CFSG.RankThree.PartOne.N1322
open scoped Matrix

theorem neg_one_ne_one_GL {p : ℕ} [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0) :
    (-1 : GL (Fin 3) (ZMod p)) ≠ 1 := by
  intro h
  have h1 := congrArg (fun g : GL (Fin 3) (ZMod p) => ((g : Matrix (Fin 3) (Fin 3) (ZMod p)) 0 0)) h
  simp only [Units.val_neg, Units.val_one, Matrix.neg_apply, Matrix.one_apply_eq] at h1
  apply h2
  linear_combination -h1

theorem neg_one_not_mem {p : ℕ} [Fact p.Prime] {H : Subgroup (GL (Fin 3) (ZMod p))}
    (h2 : (2 : ZMod p) ≠ 0)
    (hZ3 : ∀ z ∈ H, (∀ g : GL (Fin 3) (ZMod p), g * z = z * g) → z ^ 3 = 1) :
    (-1 : GL (Fin 3) (ZMod p)) ∉ H := by
  intro hmem
  have h3 := hZ3 (-1) hmem (fun g => (neg_one_comm g).symm)
  have h4 : (-1 : GL (Fin 3) (ZMod p)) ^ 3 = -1 := Odd.neg_one_pow ⟨1, rfl⟩
  rw [h4] at h3
  exact neg_one_ne_one_GL h2 h3

theorem exists_fin4_zpow {G : Type*} [Group G] {g : G} (hg : orderOf g = 4) (z : ℤ) :
    ∃ r : Fin 4, g ^ z = g ^ (r : ℕ) := by
  have h0 : 0 ≤ z % (4 : ℤ) := Int.emod_nonneg z (by norm_num)
  have h4 : z % (4 : ℤ) < 4 := Int.emod_lt_of_pos z (by norm_num)
  refine ⟨⟨(z % 4).toNat, by omega⟩, ?_⟩
  have h1 : g ^ (z % (orderOf g : ℤ)) = g ^ z := zpow_mod_orderOf g z
  rw [hg] at h1
  push_cast at h1
  show g ^ z = g ^ ((z % 4).toNat)
  rw [← h1, ← zpow_natCast, Int.toNat_of_nonneg h0]

theorem stab_swap_form {p : ℕ} [Fact p.Prime] {d : CoreData (ZMod p)} (h : CoreHyp d)
    (hn4 : d.n = 4) {ρ t₀ : d.Lm} (hg : DihGens d.Lm d.n ρ t₀)
    {H : Subgroup (GL (Fin 3) (ZMod p))} (hneg : (-1 : GL (Fin 3) (ZMod p)) ∉ H)
    {a₁ a₂ k : GL (Fin 3) (ZMod p)} (ha₁ : a₁ ∈ H) (ha₂ : a₂ ∈ H) (hkH : k ∈ H) (hkX : k ∈ d.X)
    (ht₁ : (t₀ : GL (Fin 3) (ZMod p)) = (-1 : GL (Fin 3) (ZMod p)) * a₁)
    (ht₂ : ((t₀ * ρ : d.Lm) : GL (Fin 3) (ZMod p)) = (-1 : GL (Fin 3) (ZMod p)) * a₂)
    (hmul : a₁ * a₂ = (ρ : GL (Fin 3) (ZMod p)))
    (hstab : ∃ μ : ZMod p, (k : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ d.c = μ • d.c) :
    ∃ j : Fin 4, k * a₂ * k⁻¹ = a₁ * (a₁ * a₂) ^ (j : ℕ) := by
  have hord : orderOf ρ = 4 := by rw [hg.ord, hn4]
  have hs : k * ((t₀ * ρ : d.Lm) : GL (Fin 3) (ZMod p)) * k⁻¹ ∈ d.Lm :=
    h.N k hkX hstab _ (t₀ * ρ).2
  obtain ⟨m, hm⟩ := hg.all ⟨_, hs⟩
  obtain ⟨r, hr⟩ := exists_fin4_zpow hord m
  have hconj : k * ((t₀ * ρ : d.Lm) : GL (Fin 3) (ZMod p)) * k⁻¹ =
      (-1 : GL (Fin 3) (ZMod p)) * (k * a₂ * k⁻¹) := by
    rw [ht₂]
    calc k * ((-1) * a₂) * k⁻¹ = (k * (-1)) * a₂ * k⁻¹ := by simp only [mul_assoc]
      _ = ((-1) * k) * a₂ * k⁻¹ := by rw [← neg_one_comm k]
      _ = (-1) * (k * a₂ * k⁻¹) := by simp only [mul_assoc]
  have hbH : k * a₂ * k⁻¹ ∈ H := H.mul_mem (H.mul_mem hkH ha₂) (H.inv_mem hkH)
  have hρH : (ρ : GL (Fin 3) (ZMod p)) ∈ H := by rw [← hmul]; exact H.mul_mem ha₁ ha₂
  rcases hm with hm | hm
  · exfalso
    have h1 : k * ((t₀ * ρ : d.Lm) : GL (Fin 3) (ZMod p)) * k⁻¹ =
        (ρ : GL (Fin 3) (ZMod p)) ^ (r : ℕ) := by
      have := congrArg Subtype.val hm
      rw [hr] at this
      simpa using this
    rw [hconj] at h1
    apply hneg
    have h2 : (-1 : GL (Fin 3) (ZMod p)) =
        (ρ : GL (Fin 3) (ZMod p)) ^ (r : ℕ) * (k * a₂ * k⁻¹)⁻¹ := by
      rw [← h1]
      group
    rw [h2]
    exact H.mul_mem (H.pow_mem hρH _) (H.inv_mem hbH)
  · refine ⟨r, ?_⟩
    have h1 : k * ((t₀ * ρ : d.Lm) : GL (Fin 3) (ZMod p)) * k⁻¹ =
        (t₀ : GL (Fin 3) (ZMod p)) * (ρ : GL (Fin 3) (ZMod p)) ^ (r : ℕ) := by
      have := congrArg Subtype.val hm
      rw [hr] at this
      simpa using this
    rw [hconj, ht₁, ← hmul] at h1
    have h2 : (-1 : GL (Fin 3) (ZMod p)) * (k * a₂ * k⁻¹) =
        (-1 : GL (Fin 3) (ZMod p)) * (a₁ * (a₁ * a₂) ^ (r : ℕ)) := by
      rw [h1]
      group
    exact mul_left_cancel h2

end CFSG.RankThree.PartOne.NF7H
