module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4SubFive
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4SubLong
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4SubOrb

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V} {T : Track Γ G}
  {a b : ℤ} {H : Subgroup G}

theorem exists_five_elt (hS : SubgraphProp T a b H) (F : FanTree Γ G) {m : ℤ} (hm : b - a = 2 * m)
    (h5 : valence Γ (T.line.vert a) = 5) {u : V}
    (hu : u ∈ MulAction.orbit ↥H (T.line.vert a)) :
    ∃ y ∈ H, y • u = u ∧
      (∀ v w, Γ.Adj u v → Γ.Adj u w → ∃ k ∈ Subgroup.zpowers y, k • u = u ∧ k • v = w) ∧
      ∀ k ∈ H ⊓ nbrStab Γ G u, y * k = k * y := by
  obtain ⟨L, hL, hHL⟩ := hS.lam
  have hMα : H ⊓ MulAction.stabilizer G (T.line.vert a) ≤
      L ⊓ MulAction.stabilizer G (T.line.vert a) := fun g hg => ⟨hHL hg.1, hg.2⟩
  obtain ⟨x₅, hx₅M, hx₅o, hx₅n⟩ := fan41_2_sub F (T.line.adj a) (T.line.nb a) hL h5 hMα
    (fun v w hv hw => by
      obtain ⟨k, hk, hka, hkv⟩ := hS.loc_alpha F hm v w hv hw
      exact ⟨k, ⟨hk, MulAction.mem_stabilizer_iff.2 hka⟩, hkv⟩)
  obtain ⟨htr, hcomm⟩ := five_props F (T.line.vert a) (K := H ⊓ MulAction.stabilizer G
    (T.line.vert a)) hx₅M.2 hx₅o fun g hg => hx₅n g (hMα hg)
  obtain ⟨h, hh, rfl⟩ := mem_orbit_subgroup.1 hu
  have hxa := MulAction.mem_stabilizer_iff.1 hx₅M.2
  refine ⟨h * x₅ * h⁻¹, H.mul_mem (H.mul_mem hh hx₅M.1) (H.inv_mem hh), ?_, ?_, ?_⟩
  · rw [mul_smul, mul_smul, inv_smul_smul, hxa]
  · intro v w hv hw
    have hv' : Γ.Adj (T.line.vert a) (h⁻¹ • v) := by
      have := (F.adj_smul h⁻¹ _ _).2 hv
      rwa [inv_smul_smul] at this
    have hw' : Γ.Adj (T.line.vert a) (h⁻¹ • w) := by
      have := (F.adj_smul h⁻¹ _ _).2 hw
      rwa [inv_smul_smul] at this
    obtain ⟨k, hk, hka, hkv⟩ := htr _ _ hv' hw'
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
    refine ⟨h * x₅ ^ j * h⁻¹, ?_, ?_, ?_⟩
    · rw [← conj_zpow]
      exact Subgroup.mem_zpowers_iff.2 ⟨j, rfl⟩
    · rw [mul_smul, mul_smul, inv_smul_smul, hka]
    · rw [mul_smul, mul_smul, hkv, smul_inv_smul]
  · intro k hk
    have hk' : h⁻¹ * k * h ∈ H ⊓ MulAction.stabilizer G (T.line.vert a) ⊓
        nbrStab Γ G (T.line.vert a) := by
      refine ⟨⟨H.mul_mem (H.mul_mem (H.inv_mem hh) hk.1) hh, ?_⟩, ?_⟩
      · have : h⁻¹ * k * h ∈ nbrStab Γ G (T.line.vert a) := by
          intro w hw
          have hw' : Γ.Adj (h • T.line.vert a) (h • w) := (F.adj_smul h _ _).2 hw
          rw [mul_smul, mul_smul, hk.2 _ hw', inv_smul_smul]
        exact F.nbrStab_le_stabilizer _ this
      · intro w hw
        have hw' : Γ.Adj (h • T.line.vert a) (h • w) := (F.adj_smul h _ _).2 hw
        rw [mul_smul, mul_smul, hk.2 _ hw', inv_smul_smul]
    have := hcomm _ hk'
    calc h * x₅ * h⁻¹ * k = h * (x₅ * (h⁻¹ * k * h)) * h⁻¹ := by group
      _ = h * ((h⁻¹ * k * h) * x₅) * h⁻¹ := by rw [this]
      _ = k * (h * x₅ * h⁻¹) := by group

theorem fan46_five (hS : SubgraphProp T a b H) (F : FanTree Γ G) (hPi : TrackInPi T)
    (h5 : valence Γ (T.line.vert a) = 5) : b - a ≤ 4 := by
  by_contra hcon
  push Not at hcon
  have hev := fan_4_3_2 T F hPi hS.tarc
  obtain ⟨m, hm⟩ : ∃ m : ℤ, b - a = 2 * m := ⟨(b - a) / 2, by omega⟩
  obtain ⟨γ₁, w₁, γ₂, hγ₁, hadj, hp, hsub⟩ := hS.long_data F hm (by omega)
  have hγ₂ : γ₂ ∈ MulAction.orbit ↥H (T.line.vert a) := by
    have := hp.1
    rwa [MulAction.orbit_eq_iff.2 hγ₁] at this
  obtain ⟨y₁, hy₁H, hy₁u, hy₁tr, hy₁c⟩ := exists_five_elt hS F hm h5 hγ₁
  obtain ⟨y₂, hy₂H, hy₂u, hy₂tr, hy₂c⟩ := exists_five_elt hS F hm h5 hγ₂
  set M : Subgroup G := Subgroup.closure ({y₁, y₂} : Set G) with hMdef
  have hM1 : y₁ ∈ M := Subgroup.subset_closure (by simp)
  have hM2 : y₂ ∈ M := Subgroup.subset_closure (by simp)
  have hMH : M ≤ H := by
    rw [hMdef, Subgroup.closure_le]
    rintro g (rfl | rfl)
    · exact hy₁H
    · exact hy₂H
  set U : Subgroup G := H ⊓ nbrStab Γ G γ₁ ⊓ nbrStab Γ G γ₂ with hU
  have hcomm : ∀ g ∈ U, ∀ n ∈ M, n * g = g * n := by
    intro g hg n hn
    induction hn using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact hy₁c g ⟨hg.1.1, hg.1.2⟩
      · exact hy₂c g ⟨hg.1.1, hg.2⟩
    | one => simp
    | mul x y _ _ hx hy => rw [mul_assoc, hy, ← mul_assoc, hx, mul_assoc]
    | inv x _ hx =>
      have : x⁻¹ * g * x = g := by rw [mul_assoc, ← hx, ← mul_assoc, inv_mul_cancel, one_mul]
      calc x⁻¹ * g = x⁻¹ * g * x * x⁻¹ := by group
        _ = g * x⁻¹ := by rw [this]
  have hMU : M ≤ Subgroup.normalizer (U : Set G) := by
    intro n hn
    apply Subgroup.centralizer_le_normalizer (U : Set G)
    rw [Subgroup.mem_centralizer_iff]
    exact fun g hg => (hcomm g hg n hn).symm
  have hfix := fan46_fix hS F hm hMH hγ₁ hadj hp
    (fun x y hx hy => by
      obtain ⟨k, hk, hku, hkx⟩ := hy₁tr x y hx hy
      exact ⟨k, (Subgroup.zpowers_le.2 hM1) hk, hku, hkx⟩)
    (fun x y hx hy => by
      obtain ⟨k, hk, hku, hkx⟩ := hy₂tr x y hx hy
      exact ⟨k, (Subgroup.zpowers_le.2 hM2) hk, hku, hkx⟩)
    (U := U) (fun g hg => MulAction.mem_stabilizer_iff.1 (F.nbrStab_le_stabilizer γ₁ hg.1.2))
    (fun g hg => MulAction.mem_stabilizer_iff.1 (F.nbrStab_le_stabilizer γ₂ hg.2)) hMU
  exact hS.not_subFixer_le_fixSet F (hsub.trans hfix)

end CFSG.Quasithin.Fan86
