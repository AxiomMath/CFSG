module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4SubDefs
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4Norm

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V} (T : Track Γ G)

theorem Track.exists_moves_pred {a b : ℤ} (h : IsQuasiTArc T a b) :
    ∃ g ∈ T.subFixer a b, g • T.line.vert (a - 1) ≠ T.line.vert (a - 1) := by
  obtain ⟨-, hL, -, -⟩ := h
  obtain ⟨g, hg, hg'⟩ := IsConcreteLE.not_le_iff_exists.1 hL
  refine ⟨g, hg, fun hfix => hg' ((T.mem_subFixer).2 fun i h1 h2 => ?_)⟩
  by_cases hi : i = a - 1
  · subst hi
    exact hfix
  · exact (T.mem_subFixer).1 hg i (by omega) h2

theorem Track.exists_moves_succ {a b : ℤ} (h : IsQuasiTArc T a b) :
    ∃ g ∈ T.subFixer a b, g • T.line.vert (b + 1) ≠ T.line.vert (b + 1) := by
  obtain ⟨-, -, hR, -⟩ := h
  obtain ⟨g, hg, hg'⟩ := IsConcreteLE.not_le_iff_exists.1 hR
  refine ⟨g, hg, fun hfix => hg' ((T.mem_subFixer).2 fun i h1 h2 => ?_)⟩
  by_cases hi : i = b + 1
  · subst hi
    exact hfix
  · exact (T.mem_subFixer).1 hg i h1 (by omega)

theorem Track.conj_smul_vert (k : ℤ) (g : G) (j : ℤ) :
    (T.τ ^ k * g * (T.τ ^ k)⁻¹) • T.line.vert (j + 2 * k) = T.τ ^ k • (g • T.line.vert j) := by
  rw [mul_smul, mul_smul]
  congr 2
  rw [inv_smul_eq_iff, T.zpow_smul_vert]

theorem locTrans_conj (F : FanTree Γ G) {H : Subgroup G} {v : V}
    (hv : ∀ x y, Γ.Adj v x → Γ.Adj v y → ∃ k ∈ H, k • v = v ∧ k • x = y) {h : G} (hh : h ∈ H) :
    ∀ x y, Γ.Adj (h • v) x → Γ.Adj (h • v) y → ∃ k ∈ H, k • (h • v) = h • v ∧ k • x = y := by
  intro x y hx hy
  have hx' : Γ.Adj v (h⁻¹ • x) := by
    have := (F.adj_smul h⁻¹ _ _).2 hx
    rwa [inv_smul_smul] at this
  have hy' : Γ.Adj v (h⁻¹ • y) := by
    have := (F.adj_smul h⁻¹ _ _).2 hy
    rwa [inv_smul_smul] at this
  obtain ⟨k, hk, hkv, hkx⟩ := hv _ _ hx' hy'
  refine ⟨h * k * h⁻¹, H.mul_mem (H.mul_mem hh hk) (H.inv_mem hh), ?_, ?_⟩
  · rw [mul_smul, mul_smul, inv_smul_smul, hkv]
  · rw [mul_smul, mul_smul, hkx, smul_inv_smul]

namespace SubgraphProp

variable {T} {a b : ℤ} {H : Subgroup G}

theorem exists_g₁ (hS : SubgraphProp T a b H) :
    ∃ g ∈ H, g • T.line.vert a = T.line.vert a ∧ g • T.line.vert (a + 1) = T.line.vert (a + 1) ∧
      g • T.line.vert (a - 1) ≠ T.line.vert (a - 1) := by
  obtain ⟨g, hg, hmove⟩ := T.exists_moves_pred (hS.tarc.isQuasi T)
  have hab := hS.tarc.1
  exact ⟨g, hS.sub hg, (T.mem_subFixer).1 hg a le_rfl hab.le,
    (T.mem_subFixer).1 hg (a + 1) (by omega) (by omega), hmove⟩

theorem exists_g₂ (hS : SubgraphProp T a b H) {m : ℤ} (hm : b - a = 2 * m) :
    ∃ g ∈ H, g • T.line.vert a = T.line.vert a ∧ g • T.line.vert (a - 1) = T.line.vert (a - 1) ∧
      g • T.line.vert (a + 1) ≠ T.line.vert (a + 1) := by
  obtain ⟨g, hg, hmove⟩ := T.exists_moves_succ (hS.tarc.isQuasi T)
  have hab := hS.tarc.1
  have hτ : T.τ ^ (-m) ∈ H := H.zpow_mem hS.tau _
  have hmem : T.τ ^ (-m) * g * (T.τ ^ (-m))⁻¹ ∈ T.subFixer (a - 2 * m) a := by
    have := (T.conj_mem_subFixer (-m) (a := a) (b := b) (h := g)).2 hg
    rwa [show a + 2 * -m = a - 2 * m by omega, show b + 2 * -m = a by omega] at this
  have hm1 : 1 ≤ m := by omega
  refine ⟨_, H.mul_mem (H.mul_mem hτ (hS.sub hg)) (H.inv_mem hτ), ?_, ?_, ?_⟩
  · exact (T.mem_subFixer).1 hmem a (by omega) le_rfl
  · exact (T.mem_subFixer).1 hmem (a - 1) (by omega) (by omega)
  · intro hfix
    have h1 := T.conj_smul_vert (-m) g (b + 1)
    rw [show b + 1 + 2 * -m = a + 1 by omega, hfix] at h1
    have h2 : T.τ ^ (-m) • T.line.vert (b + 1) = T.line.vert (a + 1) := by
      rw [T.zpow_smul_vert]
      congr 1
      omega
    rw [← h2] at h1
    exact hmove (MulAction.injective (T.τ ^ (-m)) h1).symm

theorem loc_alpha (hS : SubgraphProp T a b H) (F : FanTree Γ G) {m : ℤ} (hm : b - a = 2 * m) :
    ∀ x y, Γ.Adj (T.line.vert a) x → Γ.Adj (T.line.vert a) y →
      ∃ k ∈ H, k • T.line.vert a = T.line.vert a ∧ k • x = y := by
  intro x y hx hy
  obtain ⟨g₁, hg₁, h1a, h1b, h1c⟩ := hS.exists_g₁
  obtain ⟨g₂, hg₂, h2a, h2c, h2b⟩ := hS.exists_g₂ hm
  obtain ⟨k, hk, hka, hkx⟩ := F.transitive_of_two_fixers (T.line.adj a) (T.adj_pred a)
    (T.ne_pred_succ a).symm (MulAction.mem_stabilizer_iff.2 h1a)
    (MulAction.mem_stabilizer_iff.2 h2a) h1b h1c h2c h2b hx hy
  refine ⟨k, ?_, hka, hkx⟩
  have : Subgroup.closure ({g₁, g₂} : Set G) ≤ H := by
    rw [Subgroup.closure_le]
    rintro g (rfl | rfl)
    · exact hg₁
    · exact hg₂
  exact this hk

theorem exists_swap (hS : SubgraphProp T a b H) (F : FanTree Γ G) {m : ℤ} (hm : b - a = 2 * m) :
    ∃ w ∈ H, w • T.line.vert (a + 1) = T.line.vert (a + 1) ∧
      w • T.line.vert a = T.line.vert (a + 2) := by
  have hloc := locTrans_translate_of_zpow_mem T F (L := H) 1 (by simpa using hS.tau)
    (i := a) (fun x y hx hy => by
      obtain ⟨k, hk, hka, hkx⟩ := hS.loc_alpha F hm x y hx hy
      exact ⟨k, ⟨hk, MulAction.mem_stabilizer_iff.2 hka⟩, hkx⟩)
  rw [show a + 2 * 1 = a + 2 by omega] at hloc
  obtain ⟨y, ⟨hyH, hyS⟩, hyx⟩ := hloc (T.line.vert (a + 2 + 1)) (T.line.vert (a + 2 - 1))
    (T.line.adj (a + 2)) (T.adj_pred (a + 2))
  rw [show a + 2 - 1 = a + 1 by omega] at hyx
  have hyS' := MulAction.mem_stabilizer_iff.1 hyS
  refine ⟨y * T.τ, H.mul_mem hyH hS.tau, ?_, ?_⟩
  · rw [mul_smul, T.trans (a + 1), show a + 1 + 2 = a + 2 + 1 by omega, hyx]
  · rw [mul_smul, T.trans a, hyS']

end SubgraphProp

theorem fan46_loc {a b : ℤ} {H : Subgroup G} (hS : SubgraphProp T a b H) (F : FanTree Γ G)
    {m : ℤ} (hm : b - a = 2 * m) :
    ∀ u ∈ MulAction.orbit ↥H (T.line.vert a), ∀ v w, Γ.Adj u v → Γ.Adj u w →
      ∃ h ∈ H, h • u = u ∧ h • v = w := by
  rintro _ ⟨⟨h, hh⟩, rfl⟩ v w hv hw
  exact locTrans_conj F (hS.loc_alpha F hm) hh v w hv hw

end CFSG.Quasithin.Fan86
