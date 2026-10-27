module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4Fin
public import CFSG.Quasithin.Recognition.GoldschmidtFan86TArcEven

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V} (T : Track Γ G)

theorem locTrans_translate_of_zpow_mem (F : FanTree Γ G) {L : Subgroup G} (k : ℤ)
    (hk : T.τ ^ k ∈ L) {i : ℤ}
    (h : ∀ x y, Γ.Adj (T.line.vert i) x → Γ.Adj (T.line.vert i) y →
      ∃ g ∈ L ⊓ MulAction.stabilizer G (T.line.vert i), g • x = y) :
    ∀ x y, Γ.Adj (T.line.vert (i + 2 * k)) x → Γ.Adj (T.line.vert (i + 2 * k)) y →
      ∃ g ∈ L ⊓ MulAction.stabilizer G (T.line.vert (i + 2 * k)), g • x = y := by
  intro x y hx hy
  have hg : (T.τ ^ k)⁻¹ • T.line.vert (i + 2 * k) = T.line.vert i := by
    rw [inv_smul_eq_iff, T.zpow_smul_vert]
  have hx' : Γ.Adj (T.line.vert i) ((T.τ ^ k)⁻¹ • x) := by
    have := (F.adj_smul (T.τ ^ k)⁻¹ _ _).2 hx
    rwa [hg] at this
  have hy' : Γ.Adj (T.line.vert i) ((T.τ ^ k)⁻¹ • y) := by
    have := (F.adj_smul (T.τ ^ k)⁻¹ _ _).2 hy
    rwa [hg] at this
  obtain ⟨m, ⟨hmL, hmS⟩, hmx⟩ := h _ _ hx' hy'
  refine ⟨T.τ ^ k * m * (T.τ ^ k)⁻¹, ⟨L.mul_mem (L.mul_mem hk hmL) (L.inv_mem hk),
    MulAction.mem_stabilizer_iff.2 ?_⟩, ?_⟩
  · rw [mul_smul, mul_smul, hg, MulAction.mem_stabilizer_iff.1 hmS, T.zpow_smul_vert]
  · rw [mul_smul, mul_smul, hmx, smul_inv_smul]

theorem fan45_1a (F : FanTree Γ G) {Q : Subgroup G} (hQ0 : Q ≠ ⊥) {c : ℤ}
    (hQ : Q ≤ MulAction.stabilizer G (T.line.vert c) ⊓
      MulAction.stabilizer G (T.line.vert (c + 1)))
    (hloc : ∀ u v, Γ.Adj (T.line.vert c) u → Γ.Adj (T.line.vert c) v →
      ∃ g ∈ Subgroup.normalizer (Q : Set G) ⊓ MulAction.stabilizer G (T.line.vert c), g • u = v)
    (hτ : T.τ ∈ Subgroup.normalizer (Q : Set G)) :
    Subgroup.normalizer (Q : Set G) ∈
      LamSet Γ G (T.line.vert c) (T.line.vert (c + 1)) (T.line.vert (c + 2)) := by
  refine ⟨Q, hQ0, hQ, rfl, hloc, ?_⟩
  have h1 := locTrans_translate_of_zpow_mem T F (L := Subgroup.normalizer (Q : Set G)) 1
    (by simpa using hτ) hloc
  rw [show c + 2 * 1 = c + 2 by omega] at h1
  have hn1 : Γ.Adj (T.line.vert (c + 2)) (T.line.vert (c + 2 + 1)) := T.line.adj (c + 2)
  have hn2 : Γ.Adj (T.line.vert (c + 2)) (T.line.vert (c + 2 - 1)) := T.adj_pred (c + 2)
  obtain ⟨y, ⟨hyL, hyS⟩, hyx⟩ := h1 _ _ hn1 hn2
  rw [show c + 2 - 1 = c + 1 by omega] at hyx
  have hyS' := MulAction.mem_stabilizer_iff.1 hyS
  refine ⟨y * T.τ, ⟨(Subgroup.normalizer (Q : Set G)).mul_mem hyL hτ,
    MulAction.mem_stabilizer_iff.2 ?_⟩, ?_⟩
  · rw [mul_smul, T.trans (c + 1), show c + 1 + 2 = c + 2 + 1 by omega, hyx]
  · rw [mul_smul, T.trans c, hyS']

theorem Track.rev_line_vert_neg (c : ℤ) : T.rev.line.vert (-c) = T.line.vert c := by
  rw [Track.rev_line_vert, neg_neg]

theorem fan45_1b (F : FanTree Γ G) {Q : Subgroup G} (hQ0 : Q ≠ ⊥) {c : ℤ}
    (hQ : Q ≤ MulAction.stabilizer G (T.line.vert c) ⊓
      MulAction.stabilizer G (T.line.vert (c - 1)))
    (hloc : ∀ u v, Γ.Adj (T.line.vert c) u → Γ.Adj (T.line.vert c) v →
      ∃ g ∈ Subgroup.normalizer (Q : Set G) ⊓ MulAction.stabilizer G (T.line.vert c), g • u = v)
    (hτ : T.τ ∈ Subgroup.normalizer (Q : Set G)) :
    Subgroup.normalizer (Q : Set G) ∈
      LamSet Γ G (T.line.vert c) (T.line.vert (c - 1)) (T.line.vert (c - 2)) := by
  have e0 : T.rev.line.vert (-c) = T.line.vert c := T.rev_line_vert_neg c
  have e1 : T.rev.line.vert (-c + 1) = T.line.vert (c - 1) := by
    rw [Track.rev_line_vert, show -(-c + 1) = c - 1 by omega]
  have e2 : T.rev.line.vert (-c + 2) = T.line.vert (c - 2) := by
    rw [Track.rev_line_vert, show -(-c + 2) = c - 2 by omega]
  have := fan45_1a T.rev F hQ0 (c := -c) (by rwa [e0, e1]) (by rwa [e0])
    (by simpa [Track.rev] using Subgroup.inv_mem _ hτ)
  rwa [e0, e1, e2] at this

theorem locTrans_endpoint (F : FanTree Γ G) (hne : T.fixer ≠ ⊥) (hrc : ReflClosed T) {a b : ℤ}
    (hθ : IsTArc T a b) {c : ℤ} (hc : c = a ∨ c = b) :
    ∀ u v, Γ.Adj (T.line.vert c) u → Γ.Adj (T.line.vert c) v →
      ∃ g ∈ Subgroup.normalizer (omega1 T.fixer : Set G) ⊓
        MulAction.stabilizer G (T.line.vert c), g • u = v := by
  have hev := fan_4_3_2 T F ⟨hne, hrc⟩ hθ
  have hab := hθ.1
  intro u v hu hv
  rcases hc with rfl | rfl
  · obtain ⟨k, hk⟩ : ∃ k : ℤ, b + 2 * k = c := ⟨(c - b) / 2, by omega⟩
    have h₁ := (hθ.translate T k).isQuasi T
    rw [hk] at h₁
    obtain ⟨m, hm, hmα, hmx⟩ := locTrans_of_quasiTArcs T F h₁ (hθ.isQuasi T) u v hu hv
    exact ⟨m, ⟨hm, MulAction.mem_stabilizer_iff.2 hmα⟩, hmx⟩
  · obtain ⟨k, hk⟩ : ∃ k : ℤ, a + 2 * k = c := ⟨(c - a) / 2, by omega⟩
    have h₂ := (hθ.translate T k).isQuasi T
    rw [hk] at h₂
    obtain ⟨m, hm, hmα, hmx⟩ := locTrans_of_quasiTArcs T F (hθ.isQuasi T) h₂ u v hu hv
    exact ⟨m, ⟨hm, MulAction.mem_stabilizer_iff.2 hmα⟩, hmx⟩

theorem fan45_2_lam (F : FanTree Γ G) (hne : T.fixer ≠ ⊥) (hrc : ReflClosed T) {a b : ℤ}
    (hθ : IsTArc T a b) {c : ℤ} (hc : c = a ∨ c = b) :
    Subgroup.normalizer (omega1 T.fixer : Set G) ∈
      LamSet Γ G (T.line.vert c) (T.line.vert (c + 1)) (T.line.vert (c + 2)) ∧
    Subgroup.normalizer (omega1 T.fixer : Set G) ∈
      LamSet Γ G (T.line.vert c) (T.line.vert (c - 1)) (T.line.vert (c - 2)) := by
  obtain ⟨y, hy, hy1, hy2⟩ := T.exists_involution_of_fixer_ne_bot F hne
  have hY0 : omega1 T.fixer ≠ ⊥ := fun h =>
    hy1 (Subgroup.mem_bot.1 (h ▸ Subgroup.subset_closure ⟨hy, hy2⟩))
  have hloc := locTrans_endpoint T F hne hrc hθ hc
  have hτ : T.τ ∈ Subgroup.normalizer (omega1 T.fixer : Set G) := by
    simpa using T.zpow_mem_normalizer 1
  have hY : ∀ i : ℤ, omega1 T.fixer ≤ MulAction.stabilizer G (T.line.vert i) := fun i g hg =>
    MulAction.mem_stabilizer_iff.2 ((T.mem_fixer).1 (omega1_le _ hg) i)
  exact ⟨fan45_1a T F hY0 (fun g hg => ⟨hY c hg, hY (c + 1) hg⟩) hloc hτ,
    fan45_1b T F hY0 (fun g hg => ⟨hY c hg, hY (c - 1) hg⟩) hloc hτ⟩

end CFSG.Quasithin.Fan86
