module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4CentGeo
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4SubOrb

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V} {T : Track Γ G}
  {a b : ℤ} {H : Subgroup G}

theorem claim_five_a (hS : SubgraphProp T a b H) (F : FanTree Γ G) {m : ℤ} (hm : b - a = 2 * m)
    (h3 : 3 ≤ m) {p : G} (hpH : p ∈ H) (hpα : p • T.line.vert a = T.line.vert a)
    (hp3 : orderOf p = 3) :
    ∃ k ∈ H ⊓ nbrStab Γ G (T.line.vert a),
      p * k * p⁻¹ * k⁻¹ ∉ fixSet G (MulAction.orbit ↥H (T.line.vert a)) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨γ₁, w₁, γ₂, hγ₁, hadj, hpart, hsub⟩ := hS.long_data F hm h3
  have hγ₂ : γ₂ ∈ MulAction.orbit ↥H (T.line.vert a) := by
    have := hpart.1
    rwa [MulAction.orbit_eq_iff.2 hγ₁] at this
  have key : ∀ u ∈ MulAction.orbit ↥H (T.line.vert a), ∃ q ∈ H, q • u = u ∧ orderOf q = 3 ∧
      ∀ k ∈ H ⊓ nbrStab Γ G u,
        q * k * q⁻¹ * k⁻¹ ∈ fixSet G (MulAction.orbit ↥H (T.line.vert a)) := by
    intro u hu
    obtain ⟨h, hh, rfl⟩ := mem_orbit_subgroup.1 hu
    refine ⟨h * p * h⁻¹, H.mul_mem (H.mul_mem hh hpH) (H.inv_mem hh),
      by rw [mul_smul, mul_smul, inv_smul_smul, hpα], ?_, ?_⟩
    · rw [← hp3]
      exact (MulAut.conj h).orderOf_eq p
    · intro k hk
      have hk' : h⁻¹ * k * h ∈ H ⊓ nbrStab Γ G (T.line.vert a) := by
        refine ⟨H.mul_mem (H.mul_mem (H.inv_mem hh) hk.1) hh, fun w hw => ?_⟩
        have hw' : Γ.Adj (h • T.line.vert a) (h • w) := (F.adj_smul h _ _).2 hw
        rw [mul_smul, mul_smul, hk.2 _ hw', inv_smul_smul]
      have e : h * p * h⁻¹ * k * (h * p * h⁻¹)⁻¹ * k⁻¹ =
          h * (p * (h⁻¹ * k * h) * p⁻¹ * (h⁻¹ * k * h)⁻¹) * h⁻¹ := by group
      rw [e]
      exact fixSet_orbit_conj hh (hcon _ hk')
  obtain ⟨q₁, hq₁H, hq₁u, hq₁o, hq₁c⟩ := key γ₁ hγ₁
  obtain ⟨q₂, hq₂H, hq₂u, hq₂o, hq₂c⟩ := key γ₂ hγ₂
  set N := fixSet G (MulAction.orbit ↥H (T.line.vert a)) with hN
  set U : Subgroup G := H ⊓ nbrStab Γ G γ₁ ⊓ nbrStab Γ G γ₂ with hU
  set W : Subgroup G := Subgroup.closure ((N : Set G) ∪ (U : Set G)) with hW
  have hNW : ∀ x ∈ N, x ∈ W := fun x hx => Subgroup.subset_closure (Or.inl hx)
  have hUW : ∀ x ∈ U, x ∈ W := fun x hx => Subgroup.subset_closure (Or.inr hx)
  have hconj : ∀ q ∈ H, (∀ g ∈ U, q * g * q⁻¹ * g⁻¹ ∈ N) → ∀ x ∈ W, q * x * q⁻¹ ∈ W := by
    intro q hq hqU x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with hy | hy
      · exact hNW _ (fixSet_orbit_conj hq hy)
      · have h1 : q * y * q⁻¹ = (q * y * q⁻¹ * y⁻¹) * y := by group
        rw [h1]
        exact W.mul_mem (hNW _ (hqU y hy)) (hUW y hy)
    | one => simp
    | mul y z _ _ hy hz =>
      have : q * (y * z) * q⁻¹ = (q * y * q⁻¹) * (q * z * q⁻¹) := by group
      rw [this]
      exact W.mul_mem hy hz
    | inv y _ hy =>
      have : q * y⁻¹ * q⁻¹ = (q * y * q⁻¹)⁻¹ := by group
      rw [this]
      exact W.inv_mem hy
  have hnorm : ∀ q ∈ H, orderOf q = 3 → (∀ g ∈ U, q * g * q⁻¹ * g⁻¹ ∈ N) →
      q ∈ Subgroup.normalizer (W : Set G) := by
    intro q hq ho hqU
    have hq3 : q ^ 3 = 1 := by rw [← ho]; exact pow_orderOf_eq_one q
    have e3 : q * q * q = 1 := by
      calc q * q * q = q ^ 3 := by rw [pow_succ, pow_two]
        _ = 1 := hq3
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨hconj q hq hqU x, fun hx => ?_⟩
    have h2 := hconj q hq hqU _ (hconj q hq hqU _ hx)
    have e : q * (q * (q * x * q⁻¹) * q⁻¹) * q⁻¹ = (q * q * q) * x * (q * q * q)⁻¹ := by group
    rwa [e, e3, one_mul, inv_one, mul_one] at h2
  set M : Subgroup G := Subgroup.closure ({q₁, q₂} : Set G) with hMdef
  have hM1 : q₁ ∈ M := Subgroup.subset_closure (by simp)
  have hM2 : q₂ ∈ M := Subgroup.subset_closure (by simp)
  have hMH : M ≤ H := by
    rw [hMdef, Subgroup.closure_le]
    rintro g (rfl | rfl)
    · exact hq₁H
    · exact hq₂H
  have hMW : M ≤ Subgroup.normalizer (W : Set G) := by
    rw [hMdef, Subgroup.closure_le]
    rintro g (rfl | rfl)
    · exact hnorm _ hq₁H hq₁o (fun g hg => hq₁c g ⟨hg.1.1, hg.1.2⟩)
    · exact hnorm _ hq₂H hq₂o (fun g hg => hq₂c g ⟨hg.1.1, hg.2⟩)
  have hWst : ∀ γ ∈ MulAction.orbit ↥H (T.line.vert a), (∀ g ∈ U, g • γ = γ) →
      ∀ g ∈ W, g • γ = γ := by
    intro γ hγ hUγ g hg
    have : W ≤ MulAction.stabilizer G γ := by
      rw [hW, Subgroup.closure_le]
      rintro x (hx | hx)
      · exact MulAction.mem_stabilizer_iff.2 (hx γ hγ)
      · exact MulAction.mem_stabilizer_iff.2 (hUγ x hx)
    exact MulAction.mem_stabilizer_iff.1 (this hg)
  have hfix := fan46_fix hS F hm hMH hγ₁ hadj hpart
    (fun x y hx hy => by
      obtain ⟨k, hk, hku, hkx⟩ := zpowers_transitive F γ₁
        (MulAction.mem_stabilizer_iff.2 hq₁u) Nat.prime_three (by norm_num) hq₁o x y hx hy
      exact ⟨k, (Subgroup.zpowers_le.2 hM1) hk, hku, hkx⟩)
    (fun x y hx hy => by
      obtain ⟨k, hk, hku, hkx⟩ := zpowers_transitive F γ₂
        (MulAction.mem_stabilizer_iff.2 hq₂u) Nat.prime_three (by norm_num) hq₂o x y hx hy
      exact ⟨k, (Subgroup.zpowers_le.2 hM2) hk, hku, hkx⟩)
    (U := W)
    (hWst γ₁ hγ₁ fun g hg => MulAction.mem_stabilizer_iff.1 (F.nbrStab_le_stabilizer γ₁ hg.1.2))
    (hWst γ₂ hγ₂ fun g hg => MulAction.mem_stabilizer_iff.1 (F.nbrStab_le_stabilizer γ₂ hg.2))
    hMW
  exact hS.not_subFixer_le_fixSet F (fun g hg => hfix (hUW g (hsub hg)))

end CFSG.Quasithin.Fan86
