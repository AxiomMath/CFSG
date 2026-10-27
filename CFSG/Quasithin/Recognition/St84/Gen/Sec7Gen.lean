module

public import CFSG.Quasithin.Recognition.St84.Sec7S3

import CFSG.Quasithin.Recognition.St84.Sec7Even
import CFSG.Quasithin.Recognition.St84.Gen.OddTransGen
import CFSG.Quasithin.Recognition.St84.Gen.PushZL2
import CFSG.Quasithin.Recognition.St84.Gen.Sec7S3Gen

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86

namespace Setup

theorem rightTransAt_three_gen {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V}
    (X : Setup Γ G) (hc : CharTwoStab (V := V) (G := G)) : X.RightTransAt 0 3 := by
  by_contra hsing
  have hR3 : X.R72 ≤ X.Q 3 := X.R72_le_Q_three hsing
  have hαβ : Γ.Adj (X.vert 1) (X.vert 2) := by
    have h := X.adj 1
    rw [show (1 : ℤ) + 1 = 2 by norm_num] at h
    exact h
  obtain ⟨x, hxα, hxo, hxtr⟩ := X.hyp.exists_odd_transitive_gen (X.vert 1)
  have hinf : X.H72 ⊓ X.Q 2 = X.R72 := X.H72_inf_Q_two_gen hc hR3
  exact lemmaR_L2 (h := X.hyp) (hαβ := hαβ) (W := X.H72) (T := X.Q 1) (n := X.n 0)
    (X.hyp.valency (X.vert 0)).1 X.H72_le_Gi (X.H72_transitive hc)
    (X.charTwo_H72_of_inf hc hR3 hinf) (X.isL2Quot_H72 hc)
    (X.isSylowTwoOf_Q_one_H72_of_inf hc hinf) (X.Q_le_Gi 1) (X.noCharNormal_H72 hc) hxα
    ((CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 1)) hxα) hxo hxtr

theorem rightTransitive_arc_three_gen {V G : Type} [Group G] [MulAction G V]
    {Γ : SimpleGraph V} (X : Setup Γ G) (hc : CharTwoStab (V := V) (G := G)) :
    RightTransitive Γ G (X.line.arc 0 3).vert 0 3 :=
  (X.rightTransitive_arc_iff 0 (k := 3) (by norm_num)).mpr (X.rightTransAt_three_gen hc)

end Setup

theorem singularity_ne_three_gen {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V}
    {s : ℕ} (h : Hyp30 Γ G) (hc : CharTwoStab (V := V) (G := G)) (hs : IsSingularity Γ G s) :
    s ≠ 3 := by
  intro hs3
  obtain ⟨X, hX⟩ := h.exists_setup_not_rightTransitive hs
  subst hs3
  exact hX (X.rightTransitive_arc_three_gen hc)

theorem sec7_mixed {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V}
    (h : Hyp30 Γ G) (hc : CharTwoStab (V := V) (G := G))
    (hmix : ∀ v w, Γ.Adj v w → nOf Γ v ≠ nOf Γ w) :
    ∃ (s : ℕ) (X : Setup Γ G), IsSingularity Γ G s ∧
      ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s ∧ Odd s ∧ 5 ≤ s := by
  obtain ⟨s, X, hs, hX⟩ := h.exists_singular_setup
  have hne : X.n 0 ≠ X.n 1 := fun h01 => hmix (X.vert 0) (X.vert 1) (X.adj 0) h01
  have hodd : Odd s := Nat.not_even_iff_odd.mp (X.not_even_of_n_ne hs hne)
  have h3 : 3 ≤ s := three_le_of_isSingularity h hc hs
  have hne3 : s ≠ 3 := singularity_ne_three_gen h hc hs
  obtain ⟨k, hk⟩ := hodd
  exact ⟨s, X, hs, hX, ⟨k, hk⟩, by omega⟩

end CFSG.Quasithin.St84

end
