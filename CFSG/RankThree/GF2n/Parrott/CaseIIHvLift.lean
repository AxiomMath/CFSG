module

public import CFSG.RankThree.GF2n.Parrott.CaseIIF1Data

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open Subgroup
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open scoped Matrix commutatorElement

set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
local notation "GL8" => Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)
local notation "Mat8" => Matrix (Fin 8) (Fin 8) (ZMod 2)

variable {G : Type} [Group G] {z : G}

namespace IsSpinCoord

private lemma mem_H_of_mem_J {k : G} (hk : k ∈ J z) : k ∈ H z :=
  Subgroup.map_subtype_le (pCore 2 (H z)) hk

private lemma z_commute_J {k : G} (hk : k ∈ J z) : z * k = k * z :=
  (mem_centralizer_singleton_iff.mp (mem_H_of_mem_J hk)).symm

private lemma z_commute_inv_J {k : G} (hk : k ∈ J z) (hzz : z * z = 1) :
    z * k⁻¹ = k⁻¹ * z := by
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  calc z * k⁻¹ = (k * z)⁻¹ := by rw [mul_inv_rev, hzi]
    _ = (z * k)⁻¹ := by rw [z_commute_J hk]
    _ = k⁻¹ * z := by rw [mul_inv_rev, hzi]

private lemma z_commute_H {x : G} (hx : x ∈ H z) : z * x = x * z :=
  (mem_centralizer_singleton_iff.mp hx).symm

private lemma mul_inv_eq_one_or_z {a b : G} (hzz : z * z = 1)
    (ha : a = 1 ∨ a = z) (hb : b = 1 ∨ b = z) : a * b⁻¹ = 1 ∨ a * b⁻¹ = z := by
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact Or.inl (by simp)
  · exact Or.inr (by rw [hzi]; simp)
  · exact Or.inr (by simp)
  · exact Or.inl (by rw [hzi, hzz])

private lemma conj_mul_inv_eq_inv {x k : G} (hzz : z * z = 1)
    (hxx : x * x = 1 ∨ x * x = z) (hzk : z * k = k * z) (hzx : z * x = x * z) :
    x * (x * k * x⁻¹ * k⁻¹) * x⁻¹ = (x * k * x⁻¹ * k⁻¹)⁻¹ := by
  rcases hxx with h1 | h1
  · have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right h1
    apply eq_inv_of_mul_eq_one_left
    calc (x * (x * k * x⁻¹ * k⁻¹) * x⁻¹) * (x * k * x⁻¹ * k⁻¹)
        = (x * x) * k * x⁻¹ * x⁻¹ * k⁻¹ := by group
      _ = (x * x) * k * (x * x) * k⁻¹ := by rw [hxi]; group
      _ = 1 := by rw [h1]; group
  · have hxi : x⁻¹ = z * x := by
      apply inv_eq_of_mul_eq_one_right
      calc x * (z * x) = x * (x * z) := by rw [hzx]
        _ = (x * x) * z := by group
        _ = z * z := by rw [h1]
        _ = 1 := hzz
    apply eq_inv_of_mul_eq_one_left
    calc (x * (x * k * x⁻¹ * k⁻¹) * x⁻¹) * (x * k * x⁻¹ * k⁻¹)
        = (x * x) * k * x⁻¹ * x⁻¹ * k⁻¹ := by group
      _ = (x * x) * k * (z * x) * (z * x) * k⁻¹ := by rw [hxi]
      _ = z * k * (z * x) * (z * x) * k⁻¹ := by rw [h1]
      _ = z * k * ((z * x) * (z * x)) * k⁻¹ := by group
      _ = k * (z * (z * x)) * (z * x) * k⁻¹ := by rw [hzk]; group
      _ = k * x * (z * x) * k⁻¹ := by
          rw [show z * (z * x) = x from by rw [← mul_assoc, hzz, one_mul]]
      _ = k * x * (x * z) * k⁻¹ := by rw [hzx]
      _ = k * (x * x) * z * k⁻¹ := by group
      _ = k * z * z * k⁻¹ := by rw [h1]
      _ = 1 := by
          rw [show k * z * z * k⁻¹ = k * (z * z) * k⁻¹ from by group]
          rw [hzz, mul_one, mul_inv_cancel]

private lemma mul_sq_no_z {x k : G} (hxx : x * x = z) (hzk : z * k = k * z) :
    (k * x * k⁻¹) * (k * x * k⁻¹) = z := by
  calc (k * x * k⁻¹) * (k * x * k⁻¹) = k * (x * x) * k⁻¹ := by group
    _ = k * z * k⁻¹ := by rw [hxx]
    _ = (k * z) * k⁻¹ := rfl
    _ = (z * k) * k⁻¹ := by rw [← hzk]
    _ = z := by rw [mul_assoc, mul_inv_cancel, mul_one]

private lemma mul_z_sq {x k : G} (hzz : z * z = 1) (hxx : x * x = z)
    (hzk : z * k = k * z) (hzx : z * x = x * z) :
    (k * x * k⁻¹ * z) * (k * x * k⁻¹ * z) = z := by
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  have hzk_inv : z * k⁻¹ = k⁻¹ * z := by
    calc z * k⁻¹ = (k * z)⁻¹ := by rw [mul_inv_rev, hzi]
      _ = (z * k)⁻¹ := by rw [hzk]
      _ = k⁻¹ * z := by rw [mul_inv_rev, hzi]
  have hzy : z * (k * x * k⁻¹) = (k * x * k⁻¹) * z := by
    calc z * (k * x * k⁻¹) = (z * k * x) * k⁻¹ := by group
      _ = (k * z * x) * k⁻¹ := by rw [hzk]
      _ = (k * (z * x)) * k⁻¹ := by group
      _ = (k * (x * z)) * k⁻¹ := by rw [hzx]
      _ = k * x * (z * k⁻¹) := by group
      _ = k * x * (k⁻¹ * z) := by rw [hzk_inv]
      _ = (k * x * k⁻¹) * z := by group
  calc (k * x * k⁻¹ * z) * (k * x * k⁻¹ * z)
      = (k * x * k⁻¹) * ((z * (k * x * k⁻¹)) * z) := by group
    _ = (k * x * k⁻¹) * (((k * x * k⁻¹) * z) * z) := by rw [hzy]
    _ = ((k * x * k⁻¹) * (k * x * k⁻¹)) * (z * z) := by group
    _ = (k * (x * x) * k⁻¹) * (z * z) := by group
    _ = k * z * k⁻¹ := by rw [hxx, hzz, mul_one]
    _ = (k * z) * k⁻¹ := rfl
    _ = (z * k) * k⁻¹ := by rw [← hzk]
    _ = z := by rw [mul_assoc, mul_inv_cancel, mul_one]

private lemma conj_z_eq {n : G} (hn : n ∈ H z) : n * z * n⁻¹ = z := by
  have hzn : z * n = n * z := z_commute_H hn
  calc n * z * n⁻¹ = (z * n) * n⁻¹ := by rw [← hzn]
    _ = z := by rw [mul_assoc, mul_inv_cancel, mul_one]

private def SpinSign (z : G) (x₀ n ε : G) : Prop :=
  ∃ k ∈ J z, n * x₀ * n⁻¹ = k * x₀ * k⁻¹ * ε

private lemma spinSign_of_mem_J {x₀ j : G} (hj : j ∈ J z) : SpinSign z x₀ j 1 :=
  ⟨j, hj, by rw [mul_one]⟩

private lemma spinSign_self {x₀ : G} : SpinSign z x₀ x₀ 1 :=
  ⟨1, (J z).one_mem, by group⟩

variable {ψ : ↥(H z) →* A45} {κ : G → V}

private lemma conj_mem_J (hκ : IsSpinCoord ψ κ) {x k : G} (hx : x ∈ H z) (hk : k ∈ J z) :
    x * k * x⁻¹ ∈ J z := by
  have hψk : ψ ⟨k, mem_H_of_mem_J hk⟩ = 1 := (hκ.eq_one_iff _).mpr hk
  have hxH : x * k * x⁻¹ ∈ H z := mul_mem (mul_mem hx (mem_H_of_mem_J hk)) (inv_mem hx)
  have hψ : ψ ⟨x * k * x⁻¹, hxH⟩ = 1 := by
    have e : (⟨x * k * x⁻¹, hxH⟩ : ↥(H z)) =
        ⟨x, hx⟩ * ⟨k, mem_H_of_mem_J hk⟩ * ⟨x, hx⟩⁻¹ := by
      apply Subtype.ext
      rfl
    rw [e, map_mul, map_mul, map_inv, hψk, mul_one, mul_inv_cancel]
  exact (hκ.eq_one_iff ⟨_, hxH⟩).mp hψ

theorem exists_isConj_mul_of_fixed (hκ : IsSpinCoord ψ κ) {s : A45}
    (hs : ∀ w : V, ((rhoA s : GL8) : Mat8) *ᵥ w = w →
      ∃ u : V, ((rhoA s : GL8) : Mat8) *ᵥ u + u = w)
    {x : G} (hx : x ∈ H z) (hψx : ψ ⟨x, hx⟩ = s) {j : G} (hj : j ∈ J z)
    (hjs : ((rhoA s : GL8) : Mat8) *ᵥ κ j = κ j) :
    ∃ k ∈ J z, j * x = k * x * k⁻¹ ∨ j * x = k * x * k⁻¹ * z := by
  obtain ⟨u, hu⟩ := hs (κ j) hjs
  obtain ⟨k, hk, hκk⟩ := hκ.surj u
  have hmem : x * k⁻¹ * x⁻¹ ∈ J z := conj_mem_J hκ hx (inv_mem hk)
  have hcJ : k * x * k⁻¹ * x⁻¹ ∈ J z := by
    have h := (J z).mul_mem hk hmem
    simpa [mul_assoc] using h
  have hcκ : κ (k * x * k⁻¹ * x⁻¹) = κ j := by
    have hc_eq : k * x * k⁻¹ * x⁻¹ = k * (x * k⁻¹ * x⁻¹) := by group
    rw [hc_eq, hκ.add k hk (x * k⁻¹ * x⁻¹) hmem]
    have hact : κ (x * k⁻¹ * x⁻¹) = ((rhoA s : GL8) : Mat8) *ᵥ u := by
      rw [hκ.act x hx k⁻¹ (inv_mem hk), hψx, hκ.kappa_inv hk, hκk]
    rw [hact, hκk, add_comm]
    exact hu
  rcases (hκ.kappa_eq_iff hcJ hj).mp hcκ.symm with h | h
  · refine ⟨k, hk, Or.inl ?_⟩
    rw [h]
    group
  · refine ⟨k, hk, Or.inr ?_⟩
    have hxz : z * x = x * z := z_commute_H hx
    rw [h]
    calc (k * x * k⁻¹ * x⁻¹) * z * x = k * x * k⁻¹ * (x⁻¹ * (z * x)) := by group
      _ = k * x * k⁻¹ * (x⁻¹ * (x * z)) := by rw [hxz]
      _ = k * x * k⁻¹ * z := by group

theorem fixed_of_mul_self (hκ : IsSpinCoord ψ κ) (hzz : z * z = 1) {x w : G} (hx : x ∈ H z)
    (hw : w ∈ H z) (hψ : ψ ⟨w, hw⟩ = ψ ⟨x, hx⟩) (hxx : x * x = 1 ∨ x * x = z)
    (hww : w * w = 1 ∨ w * w = z) :
    w * x⁻¹ ∈ J z ∧ ((rhoA (ψ ⟨x, hx⟩) : GL8) : Mat8) *ᵥ κ (w * x⁻¹) = κ (w * x⁻¹) := by
  set j : G := w * x⁻¹ with hjdef
  have hjH : j ∈ H z := by
    rw [hjdef]
    exact mul_mem hw (inv_mem hx)
  have hψj : ψ ⟨j, hjH⟩ = 1 := by
    have e : (⟨j, hjH⟩ : ↥(H z)) = ⟨w, hw⟩ * ⟨x, hx⟩⁻¹ := by
      apply Subtype.ext
      simpa using hjdef
    rw [e, map_mul, map_inv, hψ, mul_inv_cancel]
  have hj : j ∈ J z := (hκ.eq_one_iff ⟨j, hjH⟩).mp hψj
  have hxjJ : x * j * x⁻¹ ∈ J z := conj_mem_J hκ hx hj
  have ht_eq : j * (x * j * x⁻¹) = (w * w) * (x * x)⁻¹ := by
    rw [hjdef]
    group
  have htz : j * (x * j * x⁻¹) = 1 ∨ j * (x * j * x⁻¹) = z := by
    rw [ht_eq]
    exact mul_inv_eq_one_or_z hzz hww hxx
  have htJ : j * (x * j * x⁻¹) ∈ J z := (J z).mul_mem hj hxjJ
  have htκ0 : κ (j * (x * j * x⁻¹)) = 0 := (hκ.eq_zero_iff _ htJ).mpr htz
  have hfix : ((rhoA (ψ ⟨x, hx⟩) : GL8) : Mat8) *ᵥ κ j = κ j := by
    have hsum : κ (j * (x * j * x⁻¹)) = κ j +
        ((rhoA (ψ ⟨x, hx⟩) : GL8) : Mat8) *ᵥ κ j := by
      rw [hκ.add j hj (x * j * x⁻¹) hxjJ, hκ.act x hx j hj]
    have h0 : κ j + ((rhoA (ψ ⟨x, hx⟩) : GL8) : Mat8) *ᵥ κ j = 0 := by
      rw [← hsum]
      exact htκ0
    have h1 : κ j + κ j = 0 := spinV_add_self (κ j)
    exact (add_left_cancel (h1.trans h0.symm)).symm
  exact ⟨hj, hfix⟩

theorem conj_eq_inv_of_fixed (hκ : IsSpinCoord ψ κ) (hzz : z * z = 1) {s : A45}
    (hs : ∀ w : V, ((rhoA s : GL8) : Mat8) *ᵥ w = w →
      ∃ u : V, ((rhoA s : GL8) : Mat8) *ᵥ u + u = w)
    {x : G} (hx : x ∈ H z) (hψx : ψ ⟨x, hx⟩ = s) (hxx : x * x = 1 ∨ x * x = z)
    {p : G} (hp : p ∈ J z) (hps : ((rhoA s : GL8) : Mat8) *ᵥ κ p = κ p) :
    x * p * x⁻¹ = p⁻¹ := by
  obtain ⟨u, hu⟩ := hs (κ p) hps
  obtain ⟨k, hk, hκk⟩ := hκ.surj u
  set c : G := x * k * x⁻¹ * k⁻¹ with hcdef
  have hck : x * k * x⁻¹ ∈ J z := conj_mem_J hκ hx hk
  have hcJ : c ∈ J z := by
    rw [hcdef]
    exact (J z).mul_mem hck (inv_mem hk)
  have hcκ : κ c = κ p := by
    have h1 : c = (x * k * x⁻¹) * k⁻¹ := by rw [hcdef]
    rw [h1, hκ.add _ hck k⁻¹ (inv_mem hk), hκ.act x hx k hk, hψx,
      hκ.kappa_inv hk, hκk]
    exact hu
  have hconj : x * c * x⁻¹ = c⁻¹ :=
    conj_mul_inv_eq_inv hzz hxx (z_commute_J hk) (z_commute_H hx)
  rcases (hκ.kappa_eq_iff hcJ hp).mp hcκ.symm with h | h
  · rw [h]
    exact hconj
  · have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
    have hzc_inv : z * c⁻¹ = c⁻¹ * z := z_commute_inv_J hcJ hzz
    have hxz : z * x = x * z := z_commute_H hx
    rw [h]
    calc x * (c * z) * x⁻¹ = (x * c * x⁻¹) * (x * z * x⁻¹) := by group
      _ = c⁻¹ * z := by
          rw [hconj]
          rw [show x * z * x⁻¹ = z from by
            rw [← hxz, mul_assoc, mul_inv_cancel, mul_one]]
      _ = z * c⁻¹ := hzc_inv.symm
      _ = (c * z)⁻¹ := by
          have hcz : (c * z)⁻¹ = z * c⁻¹ := by
            calc (c * z)⁻¹ = z⁻¹ * c⁻¹ := by rw [mul_inv_rev]
              _ = z * c⁻¹ := by rw [hzi]
          exact hcz.symm

theorem exists_lift_mul_self (hκ : IsSpinCoord ψ κ) {s : A45}
    (hss : s * s = 1)
    (hs : ∀ w : V, ((rhoA s : GL8) : Mat8) *ᵥ w = w →
      ∃ u : V, ((rhoA s : GL8) : Mat8) *ᵥ u + u = w) :
    ∃ (x : G) (hx : x ∈ H z), ψ ⟨x, hx⟩ = s ∧ (x * x = 1 ∨ x * x = z) := by
  obtain ⟨⟨x₁, hx₁⟩, hψ₁⟩ := hκ.surjective s
  have hj₀H : x₁ * x₁ ∈ H z := mul_mem hx₁ hx₁
  have hψj₀ : ψ ⟨x₁ * x₁, hj₀H⟩ = 1 := by
    have e : (⟨x₁ * x₁, hj₀H⟩ : ↥(H z)) = ⟨x₁, hx₁⟩ * ⟨x₁, hx₁⟩ := by
      apply Subtype.ext
      rfl
    rw [e, map_mul, hψ₁, hss]
  have hj₀ : x₁ * x₁ ∈ J z := (hκ.eq_one_iff _).mp hψj₀
  have hfix : ((rhoA s : GL8) : Mat8) *ᵥ κ (x₁ * x₁) = κ (x₁ * x₁) := by
    have h := hκ.act x₁ hx₁ (x₁ * x₁) hj₀
    have e : x₁ * (x₁ * x₁) * x₁⁻¹ = x₁ * x₁ := by group
    rw [e, hψ₁] at h
    exact h.symm
  obtain ⟨u, hu⟩ := hs (κ (x₁ * x₁)) hfix
  obtain ⟨k, hk, hκk⟩ := hκ.surj u
  have hψk : ψ ⟨k, mem_H_of_mem_J hk⟩ = 1 := (hκ.eq_one_iff _).mpr hk
  let x : G := x₁ * k
  have hxH : x ∈ H z := mul_mem hx₁ (mem_H_of_mem_J hk)
  have hψx : ψ ⟨x, hxH⟩ = s := by
    have e : (⟨x, hxH⟩ : ↥(H z)) = ⟨x₁, hx₁⟩ * ⟨k, mem_H_of_mem_J hk⟩ := by
      apply Subtype.ext
      rfl
    rw [e, map_mul, hψ₁, hψk, mul_one]
  have hmem1 : x₁ * k * x₁⁻¹ ∈ J z := conj_mem_J hκ hx₁ hk
  have hxx_eq : x * x = (x₁ * k * x₁⁻¹) * (x₁ * x₁) * k := by
    dsimp only [x]
    group
  have hxxJ : x * x ∈ J z := by
    rw [hxx_eq]
    exact (J z).mul_mem ((J z).mul_mem hmem1 hj₀) hk
  have hκxx : κ (x * x) = 0 := by
    rw [hxx_eq, hκ.add _ ((J z).mul_mem hmem1 hj₀) k hk,
      hκ.add _ hmem1 (x₁ * x₁) hj₀, hκ.act x₁ hx₁ k hk, hψ₁, hκk, ← hu]
    calc ((rhoA s : GL8) : Mat8) *ᵥ u +
          (((rhoA s : GL8) : Mat8) *ᵥ u + u) + u
        = (((rhoA s : GL8) : Mat8) *ᵥ u + ((rhoA s : GL8) : Mat8) *ᵥ u) +
            (u + u) := by abel
      _ = 0 := by rw [spinV_add_self, spinV_add_self, add_zero]
  exact ⟨x, hxH, hψx, (hκ.eq_zero_iff _ hxxJ).mp hκxx⟩

private lemma commute_of_mem_CV (hκ : IsSpinCoord ψ κ) (hzz : z * z = 1) {x₀ : G} {b₀ : A45}
    (hx₀ : x₀ ∈ H z) (hψx₀ : ψ ⟨x₀, hx₀⟩ = b₀)
    (hx₀x₀ : x₀ * x₀ = 1 ∨ x₀ * x₀ = z)
    (hFb1 : ∀ w : V, ((rhoA b₀ : GL8) : Mat8) *ᵥ w = w →
      ∃ u : V, ((rhoA b₀ : GL8) : Mat8) *ᵥ u + u = w)
    (hFb2 : ∀ w : V, ((rhoA b₀ : GL8) : Mat8) *ᵥ w = w → q w = 0)
    {p : G} (hp : p ∈ J z) (hfix : ((rhoA b₀ : GL8) : Mat8) *ᵥ κ p = κ p) :
    x₀ * p = p * x₀ := by
  have hinv := hκ.conj_eq_inv_of_fixed hzz hFb1 hx₀ hψx₀ hx₀x₀ hp hfix
  have hpp : p * p = 1 := by
    have h := hκ.sq p hp
    rw [if_pos (hFb2 (κ p) hfix)] at h
    exact h
  have hpi : p⁻¹ = p := inv_eq_of_mul_eq_one_right hpp
  calc x₀ * p = (x₀ * p * x₀⁻¹) * x₀ := by group
    _ = p⁻¹ * x₀ := by rw [hinv]
    _ = p * x₀ := by rw [hpi]

private lemma fixed_of_commute_CV (hκ : IsSpinCoord ψ κ) {x₀ : G} {b₀ : A45}
    (hx₀ : x₀ ∈ H z) (hψx₀ : ψ ⟨x₀, hx₀⟩ = b₀) {p : G} (hp : p ∈ J z)
    (hcomm : p * x₀ = x₀ * p) : ((rhoA b₀ : GL8) : Mat8) *ᵥ κ p = κ p := by
  have h := hκ.act x₀ hx₀ p hp
  have e : x₀ * p * x₀⁻¹ = p := by
    calc x₀ * p * x₀⁻¹ = (p * x₀) * x₀⁻¹ := by rw [hcomm]
      _ = p := by group
  rw [e, hψx₀] at h
  exact h.symm

private lemma spinSign_of_commute (hκ : IsSpinCoord ψ κ) (hzz : z * z = 1) {x₀ n : G}
    {b₀ : A45} (hx₀ : x₀ ∈ H z) (hn : n ∈ H z)
    (hψx₀ : ψ ⟨x₀, hx₀⟩ = b₀) (hx₀x₀ : x₀ * x₀ = 1 ∨ x₀ * x₀ = z)
    (hFb1 : ∀ w : V, ((rhoA b₀ : GL8) : Mat8) *ᵥ w = w →
      ∃ u : V, ((rhoA b₀ : GL8) : Mat8) *ᵥ u + u = w)
    (hψn : ψ ⟨n, hn⟩ * b₀ = b₀ * ψ ⟨n, hn⟩) :
    SpinSign z x₀ n 1 ∨ SpinSign z x₀ n z := by
  set w : G := n * x₀ * n⁻¹ with hwdef
  have hwH : w ∈ H z := mul_mem (mul_mem hn hx₀) (inv_mem hn)
  have hψw : ψ ⟨w, hwH⟩ = b₀ := by
    have e : (⟨w, hwH⟩ : ↥(H z)) = ⟨n, hn⟩ * ⟨x₀, hx₀⟩ * ⟨n, hn⟩⁻¹ := by
      apply Subtype.ext
      simpa using hwdef
    rw [e, map_mul, map_mul, map_inv, hψx₀, hψn]
    group
  have hww : w * w = 1 ∨ w * w = z := by
    have e : w * w = n * (x₀ * x₀) * n⁻¹ := by
      rw [hwdef]
      group
    rw [e]
    rcases hx₀x₀ with h1 | h1
    · left
      rw [h1]
      group
    · right
      rw [h1]
      exact conj_z_eq hn
  obtain ⟨hjJ, hfix⟩ := hκ.fixed_of_mul_self hzz hx₀ hwH (hψw.trans hψx₀.symm) hx₀x₀ hww
  have hfix' : ((rhoA b₀ : GL8) : Mat8) *ᵥ κ (w * x₀⁻¹) = κ (w * x₀⁻¹) := by
    simpa [hψx₀] using hfix
  obtain ⟨k, hk, hcase⟩ := hκ.exists_isConj_mul_of_fixed hFb1 hx₀ hψx₀ hjJ hfix'
  have hcancel : w * x₀⁻¹ * x₀ = w := by group
  rw [hcancel] at hcase
  rcases hcase with h | h
  · exact Or.inl ⟨k, hk, by rw [← hwdef, h, mul_one]⟩
  · exact Or.inr ⟨k, hk, by rw [← hwdef, h]⟩

private lemma spinSign_mul (hκ : IsSpinCoord ψ κ) (hzz : z * z = 1) {x₀ n n' ε ε' : G}
    (hn : n ∈ H z) (hε : ε = 1 ∨ ε = z) (hε' : ε' = 1 ∨ ε' = z)
    (h1 : SpinSign z x₀ n ε) (h2 : SpinSign z x₀ n' ε') :
    SpinSign z x₀ (n * n') (ε * ε') := by
  obtain ⟨k, hk, h1eq⟩ := h1
  obtain ⟨k', hk', h2eq⟩ := h2
  have hA : n * k' * n⁻¹ ∈ J z := conj_mem_J hκ hn hk'
  have hAk : n * k' * n⁻¹ * k ∈ J z := (J z).mul_mem hA hk
  have hnz : n * z * n⁻¹ = z := conj_z_eq hn
  have hAni : z * (n * k' * n⁻¹)⁻¹ = (n * k' * n⁻¹)⁻¹ * z := z_commute_inv_J hA hzz
  have hstep : (n * n') * x₀ * (n * n')⁻¹ =
      (n * k' * n⁻¹) * (n * x₀ * n⁻¹) * (n * k' * n⁻¹)⁻¹ * (n * ε' * n⁻¹) := by
    calc (n * n') * x₀ * (n * n')⁻¹ = n * (n' * x₀ * n'⁻¹) * n⁻¹ := by group
      _ = n * (k' * x₀ * k'⁻¹ * ε') * n⁻¹ := by rw [h2eq]
      _ = (n * k' * n⁻¹) * (n * x₀ * n⁻¹) * (n * k' * n⁻¹)⁻¹ *
            (n * ε' * n⁻¹) := by group
  have hstep2 : (n * n') * x₀ * (n * n')⁻¹ =
      (n * k' * n⁻¹) * (k * x₀ * k⁻¹ * ε) * (n * k' * n⁻¹)⁻¹ *
        (n * ε' * n⁻¹) := by
    rw [hstep, h1eq]
  refine ⟨n * k' * n⁻¹ * k, hAk, ?_⟩
  rcases hε with hε | hε <;> rcases hε' with hε' | hε'
  · subst ε
    subst ε'
    have hmain : (n * n') * x₀ * (n * n')⁻¹ =
        (n * k' * n⁻¹ * k) * x₀ * (n * k' * n⁻¹ * k)⁻¹ := by
      rw [hstep2]
      group
    simpa using hmain
  · subst ε
    subst ε'
    have hmain : (n * n') * x₀ * (n * n')⁻¹ =
        (n * k' * n⁻¹ * k) * x₀ * (n * k' * n⁻¹ * k)⁻¹ * z := by
      rw [hstep2, hnz]
      group
    simpa using hmain
  · subst ε
    subst ε'
    have hmain : (n * n') * x₀ * (n * n')⁻¹ =
        (n * k' * n⁻¹ * k) * x₀ * (n * k' * n⁻¹ * k)⁻¹ * z := by
      calc (n * n') * x₀ * (n * n')⁻¹
          = (n * k' * n⁻¹) * (k * x₀ * k⁻¹ * z) * (n * k' * n⁻¹)⁻¹ *
              (n * 1 * n⁻¹) := hstep2
        _ = (n * k' * n⁻¹) * (k * x₀ * k⁻¹) * (z * (n * k' * n⁻¹)⁻¹) *
              (n * 1 * n⁻¹) := by group
        _ = (n * k' * n⁻¹) * (k * x₀ * k⁻¹) * ((n * k' * n⁻¹)⁻¹ * z) *
              (n * 1 * n⁻¹) := by rw [hAni]
        _ = (n * k' * n⁻¹ * k) * x₀ * (n * k' * n⁻¹ * k)⁻¹ * z := by group
    simpa using hmain
  · subst ε
    subst ε'
    have hmain : (n * n') * x₀ * (n * n')⁻¹ =
        (n * k' * n⁻¹ * k) * x₀ * (n * k' * n⁻¹ * k)⁻¹ * (z * z) := by
      calc (n * n') * x₀ * (n * n')⁻¹
          = (n * k' * n⁻¹) * (k * x₀ * k⁻¹ * z) * (n * k' * n⁻¹)⁻¹ *
              (n * z * n⁻¹) := hstep2
        _ = (n * k' * n⁻¹) * (k * x₀ * k⁻¹) * (z * (n * k' * n⁻¹)⁻¹) *
              (n * z * n⁻¹) := by group
        _ = (n * k' * n⁻¹) * (k * x₀ * k⁻¹) * ((n * k' * n⁻¹)⁻¹ * z) *
              (n * z * n⁻¹) := by rw [hAni]
        _ = (n * k' * n⁻¹ * k) * x₀ * (n * k' * n⁻¹ * k)⁻¹ * (z * z) := by
            rw [hnz]; group
    simpa using hmain

private lemma spinSign_inv (hκ : IsSpinCoord ψ κ) (hzz : z * z = 1) {x₀ n ε : G}
    (hn : n ∈ H z) (hε : ε = 1 ∨ ε = z) (h : SpinSign z x₀ n ε) :
    SpinSign z x₀ n⁻¹ ε := by
  obtain ⟨k, hk, hk_eq⟩ := h
  set k₁ : G := n⁻¹ * k * n with hk₁def
  have hk₁H : k₁ ∈ H z := by
    rw [hk₁def]
    exact mul_mem (mul_mem (inv_mem hn) (mem_H_of_mem_J hk)) hn
  have hεk₁ : ε * k₁ = k₁ * ε := by
    rcases hε with hε | hε
    · subst ε
      group
    · subst ε
      exact z_commute_H hk₁H
  have hεε : ε * ε = 1 := by
    rcases hε with hε | hε
    · subst ε
      group
    · subst ε
      exact hzz
  have hεconj : n⁻¹ * ε * n = ε := by
    rcases hε with hε | hε
    · subst ε
      group
    · subst ε
      have hnz := conj_z_eq hn
      calc n⁻¹ * z * n = n⁻¹ * (n * z * n⁻¹) * n := by rw [hnz]
        _ = z := by group
  have hk₁_eq : x₀ = k₁ * (n⁻¹ * x₀ * n) * k₁⁻¹ * ε := by
    calc x₀ = n⁻¹ * (n * x₀ * n⁻¹) * n := by group
      _ = n⁻¹ * (k * x₀ * k⁻¹ * ε) * n := by rw [hk_eq]
      _ = k₁ * (n⁻¹ * x₀ * n) * k₁⁻¹ * (n⁻¹ * ε * n) := by rw [hk₁def]; group
      _ = k₁ * (n⁻¹ * x₀ * n) * k₁⁻¹ * ε := by rw [hεconj]
  have hsol : n⁻¹ * x₀ * n = k₁⁻¹ * x₀ * k₁ * ε := by
    calc n⁻¹ * x₀ * n
        = k₁⁻¹ * (k₁ * (n⁻¹ * x₀ * n) * k₁⁻¹ * ε) * k₁ * ε := by
          rw [show k₁⁻¹ * (k₁ * (n⁻¹ * x₀ * n) * k₁⁻¹ * ε) * k₁ * ε =
              n⁻¹ * x₀ * n from by
            calc k₁⁻¹ * (k₁ * (n⁻¹ * x₀ * n) * k₁⁻¹ * ε) * k₁ * ε
                = k₁⁻¹ * k₁ * (n⁻¹ * x₀ * n) * k₁⁻¹ * (ε * k₁) * ε := by group
              _ = k₁⁻¹ * k₁ * (n⁻¹ * x₀ * n) * k₁⁻¹ * (k₁ * ε) * ε := by
                  rw [hεk₁]
              _ = (n⁻¹ * x₀ * n) * (ε * ε) := by group
              _ = n⁻¹ * x₀ * n := by rw [hεε, mul_one]]
      _ = k₁⁻¹ * x₀ * k₁ * ε := by rw [← hk₁_eq]
  have hk₁inv : k₁⁻¹ = n⁻¹ * k⁻¹ * n := by
    rw [hk₁def]
    group
  have hk₁ : k₁ = (n⁻¹ * k⁻¹ * n)⁻¹ := by rw [← hk₁inv, inv_inv]
  refine ⟨n⁻¹ * k⁻¹ * n, ?_, ?_⟩
  · simpa using conj_mem_J hκ (inv_mem hn) (inv_mem hk)
  · rw [hk₁inv, hk₁] at hsol
    simpa using hsol

theorem mul_self_ne_one_of_isConj (hκ : IsSpinCoord ψ κ) (hzz : z * z = 1) (hz1 : z ≠ 1)
    {s : A45}
    (hs : ∀ w : V, ((rhoA s : GL8) : Mat8) *ᵥ w = w →
      ∃ u : V, ((rhoA s : GL8) : Mat8) *ᵥ u + u = w)
    {x : G} (hx : x ∈ H z) (hψx : ψ ⟨x, hx⟩ = s) (hxx : x * x = z)
    {y : G} (hy : y ∈ H z) (hys : IsConj (ψ ⟨y, hy⟩) s) : y * y ≠ 1 := by
  intro hyy
  obtain ⟨c, hc⟩ := isConj_iff.mp hys
  obtain ⟨⟨h, hhH⟩, hψh⟩ := hκ.surjective c
  set y' : G := h * y * h⁻¹ with hy'def
  have hy'H : y' ∈ H z := by
    rw [hy'def]
    exact mul_mem (mul_mem hhH hy) (inv_mem hhH)
  have hψy' : ψ ⟨y', hy'H⟩ = s := by
    have e : (⟨y', hy'H⟩ : ↥(H z)) = ⟨h, hhH⟩ * ⟨y, hy⟩ * ⟨h, hhH⟩⁻¹ := by
      apply Subtype.ext
      simpa using hy'def
    rw [e, map_mul, map_mul, map_inv, hψh, hc]
  have hy'y' : y' * y' = 1 := by
    have e : y' * y' = h * (y * y) * h⁻¹ := by
      rw [hy'def]
      group
    rw [e, hyy]
    group
  obtain ⟨hjJ, hfix⟩ := hκ.fixed_of_mul_self hzz hx hy'H
    (hψy'.trans hψx.symm) (Or.inr hxx) (Or.inl hy'y')
  have hfix' : ((rhoA s : GL8) : Mat8) *ᵥ κ (y' * x⁻¹) = κ (y' * x⁻¹) := by
    simpa [hψx] using hfix
  obtain ⟨k, hk, hcase⟩ := hκ.exists_isConj_mul_of_fixed hs hx hψx hjJ hfix'
  have hy'eq : y' = k * x * k⁻¹ ∨ y' = k * x * k⁻¹ * z := by
    have hcancel : y' * x⁻¹ * x = y' := by group
    rw [hcancel] at hcase
    exact hcase
  have hsq : y' * y' = z := by
    rcases hy'eq with h | h
    · rw [h]
      exact mul_sq_no_z hxx (z_commute_J hk)
    · rw [h]
      exact mul_z_sq hzz hxx (z_commute_J hk) (z_commute_H hx)
  exact hz1 (hsq.symm.trans hy'y')

theorem exists_commuting_lift (hκ : IsSpinCoord ψ κ) (hzz : z * z = 1)
    {v₀ b₀ g₁ g₂ : A45} (hbb : b₀ * b₀ = 1) (hg₁ : g₁ * b₀ = b₀ * g₁)
    (hg₂ : g₂ * b₀ = b₀ * g₂) (hg : ⁅g₁, g₂⁆ * b₀ = v₀)
    (hFv1 : ∀ w : V, ((rhoA v₀ : GL8) : Mat8) *ᵥ w = w →
      ∃ u : V, ((rhoA v₀ : GL8) : Mat8) *ᵥ u + u = w)
    (hFv2 : ∃ w : V, ((rhoA v₀ : GL8) : Mat8) *ᵥ w = w ∧ q w = 1)
    (hFb1 : ∀ w : V, ((rhoA b₀ : GL8) : Mat8) *ᵥ w = w →
      ∃ u : V, ((rhoA b₀ : GL8) : Mat8) *ᵥ u + u = w)
    (hFb2 : ∀ w : V, ((rhoA b₀ : GL8) : Mat8) *ᵥ w = w → q w = 0)
    (hFvb : ∀ w : V, ((rhoA v₀ : GL8) : Mat8) *ᵥ w = w → ((rhoA b₀ : GL8) : Mat8) *ᵥ w = w →
      ∃ u : V, ((rhoA b₀ : GL8) : Mat8) *ᵥ u = u ∧ ((rhoA v₀ : GL8) : Mat8) *ᵥ u + u = w)
    {a : G} (ha : a ∈ H z) (haa : a * a = 1) (hψa : ψ ⟨a, ha⟩ = v₀) :
    ∃ (x : G) (hx : x ∈ H z), ψ ⟨x, hx⟩ = b₀ ∧ x * a = a * x ∧ (x * x = 1 ∨ x * x = z) := by
  obtain ⟨x₀, hx₀, hψx₀, hx₀x₀⟩ := hκ.exists_lift_mul_self hbb hFb1
  obtain ⟨⟨n₁, hn₁⟩, hψn₁⟩ := hκ.surjective g₁
  obtain ⟨⟨n₂, hn₂⟩, hψn₂⟩ := hκ.surjective g₂
  obtain ⟨ε₁, hε₁, hS₁⟩ : ∃ ε : G, (ε = 1 ∨ ε = z) ∧ SpinSign z x₀ n₁ ε :=
    (spinSign_of_commute hκ hzz hx₀ hn₁ hψx₀ hx₀x₀ hFb1 (by rw [hψn₁]; exact hg₁)).elim
      (fun h => ⟨1, Or.inl rfl, h⟩) (fun h => ⟨z, Or.inr rfl, h⟩)
  obtain ⟨ε₂, hε₂, hS₂⟩ : ∃ ε : G, (ε = 1 ∨ ε = z) ∧ SpinSign z x₀ n₂ ε :=
    (spinSign_of_commute hκ hzz hx₀ hn₂ hψx₀ hx₀x₀ hFb1 (by rw [hψn₂]; exact hg₂)).elim
      (fun h => ⟨1, Or.inl rfl, h⟩) (fun h => ⟨z, Or.inr rfl, h⟩)
  have hεmul : ∀ {ε ε' : G}, (ε = 1 ∨ ε = z) → (ε' = 1 ∨ ε' = z) →
      (ε * ε' = 1 ∨ ε * ε' = z) := by
    intro ε ε' hε hε'
    rcases hε with h | h <;> rcases hε' with h' | h' <;> rw [h, h']
    · exact Or.inl (mul_one 1)
    · exact Or.inr (one_mul z)
    · exact Or.inr (mul_one z)
    · exact Or.inl hzz
  have h12 := spinSign_mul hκ hzz hn₁ hε₁ hε₂ hS₁ hS₂
  have h121 := spinSign_mul hκ hzz (mul_mem hn₁ hn₂) (hεmul hε₁ hε₂) hε₁ h12
    (spinSign_inv hκ hzz hn₁ hε₁ hS₁)
  have hcH : n₁ * n₂ * n₁⁻¹ * n₂⁻¹ ∈ H z :=
    mul_mem (mul_mem (mul_mem hn₁ hn₂) (inv_mem hn₁)) (inv_mem hn₂)
  have hSc := spinSign_mul hκ hzz (mul_mem (mul_mem hn₁ hn₂) (inv_mem hn₁))
    (hεmul (hεmul hε₁ hε₂) hε₁) hε₂ h121 (spinSign_inv hκ hzz hn₂ hε₂ hS₂)
  have hε : ε₁ * ε₂ * ε₁ * ε₂ = 1 := by
    rcases hε₁ with h | h <;> rcases hε₂ with h' | h' <;> rw [h, h'] <;>
      simp only [one_mul, mul_one, hzz]
  rw [hε] at hSc
  have hj'H : (n₁ * n₂ * n₁⁻¹ * n₂⁻¹ * x₀)⁻¹ * a ∈ H z :=
    mul_mem (inv_mem (mul_mem hcH hx₀)) ha
  have hj'J : (n₁ * n₂ * n₁⁻¹ * n₂⁻¹ * x₀)⁻¹ * a ∈ J z := by
    refine (hκ.eq_one_iff ⟨_, hj'H⟩).mp ?_
    show ψ ((⟨n₁, hn₁⟩ * ⟨n₂, hn₂⟩ * ⟨n₁, hn₁⟩⁻¹ * ⟨n₂, hn₂⟩⁻¹ * ⟨x₀, hx₀⟩)⁻¹ * ⟨a, ha⟩) = 1
    simp only [map_mul, map_inv, hψn₁, hψn₂, hψx₀, hψa]
    rw [← hg, commutatorElement_def]
    group
  have hSa := spinSign_mul hκ hzz (mul_mem hcH hx₀) (Or.inl (mul_one 1)) (Or.inl rfl)
    (spinSign_mul hκ hzz hcH (Or.inl rfl) (Or.inl rfl) hSc spinSign_self)
    (spinSign_of_mem_J hj'J)
  rw [show n₁ * n₂ * n₁⁻¹ * n₂⁻¹ * x₀ * ((n₁ * n₂ * n₁⁻¹ * n₂⁻¹ * x₀)⁻¹ * a) = a by group]
    at hSa
  obtain ⟨m, hm, hmeq⟩ := hSa
  have hmeq' : a * x₀ * a⁻¹ = m * x₀ * m⁻¹ := by
    rw [hmeq, mul_one, mul_one, mul_one]
  have hrJ : a * m * a⁻¹ * m ∈ J z := (J z).mul_mem (conj_mem_J hκ ha hm) hm
  have hrx : (a * m * a⁻¹ * m) * x₀ = x₀ * (a * m * a⁻¹ * m) := by
    have h1 : (a * m * a⁻¹ * m) * x₀ * (a * m * a⁻¹ * m)⁻¹ = x₀ := by
      calc (a * m * a⁻¹ * m) * x₀ * (a * m * a⁻¹ * m)⁻¹
          = a * m * a⁻¹ * (m * x₀ * m⁻¹) * a * m⁻¹ * a⁻¹ := by group
        _ = a * m * a⁻¹ * (a * x₀ * a⁻¹) * a * m⁻¹ * a⁻¹ := by rw [hmeq']
        _ = a * (m * x₀ * m⁻¹) * a⁻¹ := by group
        _ = a * (a * x₀ * a⁻¹) * a⁻¹ := by rw [hmeq']
        _ = (a * a) * x₀ * (a * a)⁻¹ := by group
        _ = x₀ := by rw [haa]; group
    calc (a * m * a⁻¹ * m) * x₀
        = ((a * m * a⁻¹ * m) * x₀ * (a * m * a⁻¹ * m)⁻¹) * (a * m * a⁻¹ * m) := by group
      _ = x₀ * (a * m * a⁻¹ * m) := by rw [h1]
  have hvv : v₀ * v₀ = 1 := by
    have e : (⟨a, ha⟩ : ↥(H z)) * ⟨a, ha⟩ = 1 := Subtype.ext haa
    rw [← hψa, ← map_mul, e, map_one]
  have hvinv : ∀ e : V, ((rhoA v₀ : GL8) : Mat8) *ᵥ (((rhoA v₀ : GL8) : Mat8) *ᵥ e) = e := by
    intro e
    rw [← rhoA_mulVec_mul, hvv, rhoA_mulVec_one]
  have hκr : κ (a * m * a⁻¹ * m) = ((rhoA v₀ : GL8) : Mat8) *ᵥ κ m + κ m := by
    rw [hκ.add _ (conj_mem_J hκ ha hm) m hm, hκ.act a ha m hm, hψa]
  have hrb : ((rhoA b₀ : GL8) : Mat8) *ᵥ κ (a * m * a⁻¹ * m) = κ (a * m * a⁻¹ * m) :=
    fixed_of_commute_CV hκ hx₀ hψx₀ hrJ hrx
  have hrv : ((rhoA v₀ : GL8) : Mat8) *ᵥ κ (a * m * a⁻¹ * m) = κ (a * m * a⁻¹ * m) := by
    rw [hκr, Matrix.mulVec_add, hvinv, add_comm]
  obtain ⟨u, hub, huv⟩ := hFvb _ hrv hrb
  obtain ⟨p, hp, hκp⟩ := hκ.surj u
  have hpx : x₀ * p = p * x₀ :=
    commute_of_mem_CV hκ hzz hx₀ hψx₀ hx₀x₀ hFb1 hFb2 hp (by rw [hκp]; exact hub)
  have hm'J : m * p ∈ J z := (J z).mul_mem hm hp
  have hm'eq : a * x₀ * a⁻¹ = (m * p) * x₀ * (m * p)⁻¹ := by
    rw [hmeq']
    calc m * x₀ * m⁻¹ = m * ((x₀ * p) * p⁻¹) * m⁻¹ := by group
      _ = m * ((p * x₀) * p⁻¹) * m⁻¹ := by rw [hpx]
      _ = (m * p) * x₀ * (m * p)⁻¹ := by group
  have hm'v : ((rhoA v₀ : GL8) : Mat8) *ᵥ κ (m * p) = κ (m * p) := by
    have h2 : ((rhoA v₀ : GL8) : Mat8) *ᵥ u + u = ((rhoA v₀ : GL8) : Mat8) *ᵥ κ m + κ m :=
      huv.trans hκr
    rw [hκ.add m hm p hp, Matrix.mulVec_add, hκp]
    calc ((rhoA v₀ : GL8) : Mat8) *ᵥ κ m + ((rhoA v₀ : GL8) : Mat8) *ᵥ u
        = (((rhoA v₀ : GL8) : Mat8) *ᵥ κ m + κ m) + (κ m + ((rhoA v₀ : GL8) : Mat8) *ᵥ u) := by
          rw [show (((rhoA v₀ : GL8) : Mat8) *ᵥ κ m + κ m) +
              (κ m + ((rhoA v₀ : GL8) : Mat8) *ᵥ u) =
              (((rhoA v₀ : GL8) : Mat8) *ᵥ κ m + ((rhoA v₀ : GL8) : Mat8) *ᵥ u) +
              (κ m + κ m) by abel, spinV_add_self, add_zero]
      _ = (((rhoA v₀ : GL8) : Mat8) *ᵥ u + u) + (κ m + ((rhoA v₀ : GL8) : Mat8) *ᵥ u) := by
          rw [h2]
      _ = (((rhoA v₀ : GL8) : Mat8) *ᵥ u + ((rhoA v₀ : GL8) : Mat8) *ᵥ u) + (κ m + u) := by
          abel
      _ = κ m + u := by rw [spinV_add_self, zero_add]
  have hK : ∃ K ∈ J z, (m * p)⁻¹ * a = K * a * K⁻¹ := by
    have hfix : ((rhoA v₀ : GL8) : Mat8) *ᵥ κ (m * p)⁻¹ = κ (m * p)⁻¹ := by
      rw [hκ.kappa_inv hm'J]
      exact hm'v
    obtain ⟨k, hk, hcase⟩ := hκ.exists_isConj_mul_of_fixed hFv1 ha hψa (inv_mem hm'J) hfix
    rcases hcase with h | h
    · exact ⟨k, hk, h⟩
    ·
      obtain ⟨w₁, hw₁, hqw₁⟩ := hFv2
      obtain ⟨n, hn, hκn⟩ := hκ.surj w₁
      have hnn : n * n = z := by
        have h' := hκ.sq n hn
        rw [hκn, if_neg (by rw [hqw₁]; decide)] at h'
        exact h'
      have hinv : a * n * a⁻¹ = n⁻¹ :=
        hκ.conj_eq_inv_of_fixed hzz hFv1 ha hψa (Or.inl haa) hn (by rw [hκn]; exact hw₁)
      have h1 : a * n⁻¹ * a⁻¹ = n := by
        calc a * n⁻¹ * a⁻¹ = (a * n * a⁻¹)⁻¹ := by group
          _ = n := by rw [hinv, inv_inv]
      have hna : n * a * n⁻¹ = a * z := by
        calc n * a * n⁻¹ = n * (a * n⁻¹ * a⁻¹) * a := by group
          _ = n * n * a := by rw [h1]
          _ = z * a := by rw [hnn]
          _ = a * z := z_commute_H ha
      refine ⟨k * n, (J z).mul_mem hk hn, ?_⟩
      rw [h]
      calc k * a * k⁻¹ * z = k * a * (k⁻¹ * z) := by group
        _ = k * a * (z * k⁻¹) := by rw [z_commute_inv_J hk hzz]
        _ = k * (a * z) * k⁻¹ := by group
        _ = k * (n * a * n⁻¹) * k⁻¹ := by rw [hna]
        _ = (k * n) * a * (k * n)⁻¹ := by group
  obtain ⟨K, hKJ, hKeq⟩ := hK
  have hKH : K ∈ H z := mem_H_of_mem_J hKJ
  have hcomm : (K * a * K⁻¹) * x₀ = x₀ * (K * a * K⁻¹) := by
    rw [← hKeq]
    have h1 : ((m * p)⁻¹ * a) * x₀ * ((m * p)⁻¹ * a)⁻¹ = x₀ := by
      calc ((m * p)⁻¹ * a) * x₀ * ((m * p)⁻¹ * a)⁻¹
          = (m * p)⁻¹ * (a * x₀ * a⁻¹) * (m * p) := by group
        _ = (m * p)⁻¹ * ((m * p) * x₀ * (m * p)⁻¹) * (m * p) := by rw [hm'eq]
        _ = x₀ := by group
    calc ((m * p)⁻¹ * a) * x₀
        = (((m * p)⁻¹ * a) * x₀ * ((m * p)⁻¹ * a)⁻¹) * ((m * p)⁻¹ * a) := by group
      _ = x₀ * ((m * p)⁻¹ * a) := by rw [h1]
  refine ⟨K⁻¹ * x₀ * K, mul_mem (mul_mem (inv_mem hKH) hx₀) hKH, ?_, ?_, ?_⟩
  · have hψK : ψ ⟨K, hKH⟩ = 1 := (hκ.eq_one_iff _).mpr hKJ
    show ψ (⟨K, hKH⟩⁻¹ * ⟨x₀, hx₀⟩ * ⟨K, hKH⟩) = b₀
    rw [map_mul, map_mul, map_inv, hψK, hψx₀, inv_one, one_mul, mul_one]
  · calc K⁻¹ * x₀ * K * a = K⁻¹ * (x₀ * (K * a * K⁻¹)) * K := by group
      _ = K⁻¹ * ((K * a * K⁻¹) * x₀) * K := by rw [← hcomm]
      _ = a * (K⁻¹ * x₀ * K) := by group
  · have hsq : (K⁻¹ * x₀ * K) * (K⁻¹ * x₀ * K) = K⁻¹ * (x₀ * x₀) * K := by group
    rcases hx₀x₀ with h | h
    · left
      rw [hsq, h]
      group
    · right
      rw [hsq, h, mul_assoc, z_commute_J hKJ, ← mul_assoc, inv_mul_cancel, one_mul]

end IsSpinCoord

end CFSG.RankThree.GF2n.Parrott
