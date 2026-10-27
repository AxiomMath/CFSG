module

public import CFSG.Quasithin.Recognition.St84.Sec7S3
public import CFSG.Quasithin.Recognition.St84.Sec7Even
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86
  CFSG.Quasithin.F6.GoldAmL3T

theorem sec7_A5A5 {V G : Type} [Group G] [MulAction G V]
    {Γ : SimpleGraph V} (h : Hyp30 Γ G) (hc : CharTwoStab (V := V) (G := G))
    (hn : ∀ v, nOf Γ v = 2) :
    ∃ (s : ℕ) (X : Setup Γ G), IsSingularity Γ G s ∧
      ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s ∧
      ((Odd s ∧ 5 ≤ s) ∨ (s = 4 ∧ X.TreeL34Data)) := by
  obtain ⟨s, X, hs, hX⟩ := h.exists_singular_setup
  refine ⟨s, X, hs, hX, ?_⟩
  have h3 : 3 ≤ s := three_le_of_isSingularity h hc hs
  by_cases hev : Even s
  · obtain ⟨rfl, hd⟩ := X.even_singularity_A5A5 hc hs hev hn
    exact Or.inr ⟨rfl, hd⟩
  · have hodd : Odd s := Nat.not_even_iff_odd.mp hev
    have hne3 : s ≠ 3 := singularity_ne_three h hc (fun v => Or.inr (hn v)) hs
    obtain ⟨k, hk⟩ := hodd
    exact Or.inl ⟨⟨k, hk⟩, by omega⟩

theorem sec7_S3A5 {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V}
    (h : Hyp30 Γ G) (hc : CharTwoStab (V := V) (G := G))
    (hn : ∀ v, nOf Γ v = 1 ∨ nOf Γ v = 2) (hmix : ∀ v w, Γ.Adj v w → nOf Γ v ≠ nOf Γ w) :
    ∃ (s : ℕ) (X : Setup Γ G), IsSingularity Γ G s ∧
      ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s ∧ Odd s ∧ 5 ≤ s := by
  obtain ⟨s, X, hs, hX⟩ := h.exists_singular_setup
  have hne : X.n 0 ≠ X.n 1 := by
    intro h01
    exact hmix (X.vert 0) (X.vert 1) (X.adj 0) h01
  have hodd : Odd s := Nat.not_even_iff_odd.mp (X.not_even_of_n_ne hs hne)
  have h3 : 3 ≤ s := three_le_of_isSingularity h hc hs
  have hne3 : s ≠ 3 := singularity_ne_three h hc hn hs
  obtain ⟨k, hk⟩ := hodd
  exact ⟨s, X, hs, hX, ⟨k, hk⟩, by omega⟩

theorem sec7_A5A5_even {V G : Type} [Group G]
    [MulAction G V] {Γ : SimpleGraph V} (h : Hyp30 Γ G) (hc : CharTwoStab (V := V) (G := G))
    (hn : ∀ v, nOf Γ v = 2) {s : ℕ} (hs : IsSingularity Γ G s) (hev : Even s) (X : Setup Γ G) :
    s = 4 ∧ X.TreeL34Data :=
  X.even_singularity_A5A5 hc hs hev hn

end CFSG.Quasithin.St84

end
