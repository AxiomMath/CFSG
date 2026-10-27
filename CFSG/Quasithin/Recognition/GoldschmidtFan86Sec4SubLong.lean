module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4SubDefs
public import CFSG.Quasithin.Recognition.GoldschmidtFan86TArcEven

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V} {T : Track Γ G}
  {a b : ℤ} {H : Subgroup G}

theorem Track.subFixer_le_nbrStab (T : Track Γ G) (F : FanTree Γ G) {a b i : ℤ} (h1 : a < i)
    (h2 : i < b) : T.subFixer a b ≤ nbrStab Γ G (T.line.vert i) := by
  intro g hg w hw
  have hf := (T.mem_subFixer).1 hg
  exact F.frobenius_two (T.line.vert i) (T.line.vert (i - 1)) (T.line.vert (i + 1))
    (T.adj_pred i) (T.line.adj i) (T.ne_pred_succ i) g
    (MulAction.mem_stabilizer_iff.2 (hf i (by omega) (by omega)))
    (hf (i - 1) (by omega) (by omega)) (hf (i + 1) (by omega) (by omega)) w hw

namespace SubgraphProp

theorem vert_mem_orbit (hS : SubgraphProp T a b H) (j : ℤ) :
    T.line.vert (a + 2 * j) ∈ MulAction.orbit ↥H (T.line.vert a) :=
  mem_orbit_subgroup.2 ⟨T.τ ^ j, H.zpow_mem hS.tau _, T.zpow_smul_vert j a⟩

theorem fixSet_orbit_le_fixer (hS : SubgraphProp T a b H) (F : FanTree Γ G) :
    fixSet G (MulAction.orbit ↥H (T.line.vert a)) ≤ T.fixer := by
  intro g hg
  rw [T.mem_fixer]
  intro i
  have hj : ∀ j : ℤ, g • T.line.vert (a + 2 * j) = T.line.vert (a + 2 * j) := fun j =>
    hg _ (hS.vert_mem_orbit j)
  exact Line.fixes_between F.isTree F.adj_smul T.line (i := a - 2 * max (i - a) (a - i))
    (j := a + 2 * max (i - a) (a - i)) (by omega) (by omega)
    (by simpa [sub_eq_add_neg, mul_neg] using hj (-max (i - a) (a - i)))
    (hj (max (i - a) (a - i)))

theorem not_subFixer_le_fixSet (hS : SubgraphProp T a b H) (F : FanTree Γ G) :
    ¬ T.subFixer a b ≤ fixSet G (MulAction.orbit ↥H (T.line.vert a)) := by
  intro hle
  refine (hS.tarc.isQuasi T).2.2.1 fun g hg => ?_
  exact T.fixer_le_subFixer a (b + 1) (hS.fixSet_orbit_le_fixer F (hle hg))

theorem long_data (hS : SubgraphProp T a b H) (F : FanTree Γ G) {m : ℤ} (hm : b - a = 2 * m)
    (h3 : 3 ≤ m) :
    ∃ (γ₁ w₁ γ₂ : V), γ₁ ∈ MulAction.orbit ↥H (T.line.vert a) ∧ Γ.Adj γ₁ w₁ ∧
      IsPartner Γ H γ₁ w₁ γ₂ ∧ T.subFixer a b ≤ H ⊓ nbrStab Γ G γ₁ ⊓ nbrStab Γ G γ₂ := by
  have e1 : T.line.vert (a + 2 * (m - 2)) ∈ MulAction.orbit ↥H (T.line.vert a) :=
    hS.vert_mem_orbit _
  have e2 : T.line.vert (a + 2 * (m - 1)) ∈ MulAction.orbit ↥H (T.line.vert a) :=
    hS.vert_mem_orbit _
  have hb4 : a + 2 * (m - 2) = b - 4 := by omega
  have hb2 : a + 2 * (m - 1) = b - 2 := by omega
  rw [hb4] at e1
  rw [hb2] at e2
  have hadj1 : Γ.Adj (T.line.vert (b - 4)) (T.line.vert (b - 3)) := by
    have := T.line.adj (b - 4)
    rwa [show b - 4 + 1 = b - 3 by omega] at this
  have hadj2 : Γ.Adj (T.line.vert (b - 2)) (T.line.vert (b - 3)) := by
    have := (T.line.adj (b - 3)).symm
    rwa [show b - 3 + 1 = b - 2 by omega] at this
  have hne : T.line.vert (b - 2) ≠ T.line.vert (b - 4) := fun h => by
    have := Line.vert_injective F.isTree T.line h
    omega
  refine ⟨T.line.vert (b - 4), T.line.vert (b - 3), T.line.vert (b - 2), e1, hadj1,
    ⟨?_, hne, hadj2⟩, fun g hg => ⟨⟨hS.sub hg, ?_⟩, ?_⟩⟩
  · rw [MulAction.orbit_eq_iff.2 e1]
    exact e2
  · exact T.subFixer_le_nbrStab F (i := b - 4) (by omega) (by omega) hg
  · exact T.subFixer_le_nbrStab F (i := b - 2) (by omega) (by omega) hg

end SubgraphProp

end CFSG.Quasithin.Fan86
