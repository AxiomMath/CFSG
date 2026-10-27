module

public import CFSG.Quasithin.Recognition.Stroth.WeissMoufang

public section

namespace CFSG.Quasithin.Stroth

universe u v w

variable {V : Type*}

@[expose] def WeissFree (H : Type*) [Group H] [MulAction H V] (Γ : SimpleGraph V)
    [GraphAction H Γ] (n : ℕ) : Prop :=
  ∀ p : GPath Γ n, p.NoBack → ∀ h : H, (∀ i, i ≤ n → h • p i = p i) →
    (∀ w, Γ.Adj (p 0) w → h • w = w) → (∀ w, Γ.Adj (p 1) w → h • w = w) → h = 1

theorem weissFreeHat_iff (α : RankTwoAmalgam.{u}) (n : ℕ) :
    WeissFreeHat α n ↔ WeissFree ↥(α.Ghat1 ⊔ α.Ghat2) α.graphHat n :=
  Iff.rfl

section Covering

variable {Vh : Type*} {Γh : SimpleGraph Vh} {Γ : SimpleGraph V} {θ : Vh → V}
  {Gh : Type*} {G : Type*} [Group Gh] [Group G] [MulAction Gh Vh] [MulAction G V]
  [GraphAction Gh Γh] [GraphAction G Γ] {θG : Gh →* G}

theorem moufangCondition_of_covering (hθ : GraphCovering Γh Γ θ)
    (hs : ∀ (gh : Gh) (v : Vh), θ (gh • v) = θG gh • θ v) {n : ℕ}
    (hM : MoufangCondition Gh Γh n) : MoufangCondition G Γ n := by
  intro p hp y y' hy hy' hne hne'
  obtain ⟨vh₀, hv₀⟩ := hθ.surj (p 0)
  obtain ⟨q, ⟨-, hqmap⟩, -⟩ := hθ.lift_path vh₀ n p hv₀.symm
  have hqi : ∀ i, θ (q i) = p i := fun i => congrArg (fun r : GPath Γ n => r i) hqmap
  have hqnb : q.NoBack := (hθ.noBack_pathMap_iff q).mp (by rw [hqmap]; exact hp)
  obtain ⟨ŷ, hŷ, hŷy⟩ := hθ.loc_surj (q n) y (by rw [hqi n]; exact hy)
  obtain ⟨ŷ', hŷ', hŷy'⟩ := hθ.loc_surj (q n) y' (by rw [hqi n]; exact hy')
  have hne1 : ŷ ≠ q (n - 1) := fun h => hne (by rw [← hŷy, h, hqi (n - 1)])
  have hne2 : ŷ' ≠ q (n - 1) := fun h => hne' (by rw [← hŷy', h, hqi (n - 1)])
  obtain ⟨h, hfix, hhy⟩ := hM q hqnb ŷ ŷ' hŷ hŷ' hne1 hne2
  refine ⟨θG h, fun i hi1 hin w hw => ?_, ?_⟩
  · obtain ⟨ŵ, hŵ, hŵw⟩ := hθ.loc_surj (q i) w (by rw [hqi i]; exact hw)
    calc θG h • w = θG h • θ ŵ := by rw [← hŵw]
      _ = θ (h • ŵ) := (hs h ŵ).symm
      _ = θ ŵ := by rw [hfix i hi1 hin ŵ hŵ]
      _ = w := hŵw
  · calc θG h • y = θG h • θ ŷ := by rw [← hŷy]
      _ = θ (h • ŷ) := (hs h ŷ).symm
      _ = θ ŷ' := by rw [hhy]
      _ = y' := hŷy'

theorem weissFree_of_covering (hθ : GraphCovering Γh Γ θ)
    (hs : ∀ uh : Vh, GraphCovering.StabIso (θ := θ) (θG := θG) uh) {n : ℕ} (hn : 1 ≤ n)
    (hW : WeissFree Gh Γh n) : WeissFree G Γ n := by
  intro p hp h hfix h0 h1
  obtain ⟨vh₀, hv₀⟩ := hθ.surj (p 0)
  obtain ⟨q, ⟨-, hqmap⟩, -⟩ := hθ.lift_path vh₀ n p hv₀.symm
  have hqi : ∀ i, θ (q i) = p i := fun i => congrArg (fun r : GPath Γ n => r i) hqmap
  have hqnb : q.NoBack := (hθ.noBack_pathMap_iff q).mp (by rw [hqmap]; exact hp)
  have hq0' : h • θ (q 0) = θ (q 0) := by
    rw [hqi 0]
    exact hfix 0 (Nat.zero_le n)
  obtain ⟨hh, hhq0, hhh⟩ := (hs (q 0)).surj h hq0'
  have hfixN0 : ∀ x, Γh.Adj (q 0) x → hh • x = x := by
    intro x hx
    have hadj : Γ.Adj (p 0) (θ x) := by
      rw [← hqi 0]
      exact hθ.adj _ _ hx
    have hfx : h • θ x = θ x := h0 (θ x) hadj
    have h1' : Γh.Adj (q 0) (hh • x) := by
      have h2 := (GraphAction.adj_smul hh (q 0) x).mpr hx
      rwa [hhq0] at h2
    refine hθ.loc_inj (q 0) (hh • x) x h1' hx ?_
    calc θ (hh • x) = θG hh • θ x := (hs (q 0)).equivariant hh x
      _ = h • θ x := by rw [hhh]
      _ = θ x := hfx
  have hq1 : hh • q 1 = q 1 := by
    have h01 : Γh.Adj (q 0) (q 1) := q.adj 0 hn
    have h2 : Γh.Adj (q 0) (hh • q 1) := by
      have h := (GraphAction.adj_smul hh (q 0) (q 1)).mpr h01
      rwa [hhq0] at h
    refine hθ.loc_inj (q 0) (hh • q 1) (q 1) h2 h01 ?_
    calc θ (hh • q 1) = θG hh • θ (q 1) := (hs (q 0)).equivariant hh (q 1)
      _ = h • θ (q 1) := by rw [hhh]
      _ = θ (q 1) := by rw [hqi 1]; exact hfix 1 hn
  have hfixN1 : ∀ x, Γh.Adj (q 1) x → hh • x = x := by
    intro x hx
    have hadj : Γ.Adj (p 1) (θ x) := by
      rw [← hqi 1]
      exact hθ.adj _ _ hx
    have hfx : h • θ x = θ x := h1 (θ x) hadj
    have h1' : Γh.Adj (q 1) (hh • x) := by
      have h2 := (GraphAction.adj_smul hh (q 1) x).mpr hx
      rwa [hq1] at h2
    refine hθ.loc_inj (q 1) (hh • x) x h1' hx ?_
    calc θ (hh • x) = θG hh • θ x := (hs (q 1)).equivariant hh x
      _ = h • θ x := by rw [hhh]
      _ = θ x := hfx
  have hfixPath : ∀ i, i ≤ n → hh • q i = q i := by
    intro i
    induction i with
    | zero => intro _; exact hhq0
    | succ i ih =>
      intro hi
      have hprev : hh • q i = q i := ih (by omega)
      have hinter : Γh.Adj (q i) (q (i + 1)) := q.adj i (by omega)
      have h2 : Γh.Adj (q i) (hh • q (i + 1)) := by
        have h := (GraphAction.adj_smul hh (q i) (q (i + 1))).mpr hinter
        rwa [hprev] at h
      refine hθ.loc_inj (q i) (hh • q (i + 1)) (q (i + 1)) h2 hinter ?_
      calc θ (hh • q (i + 1)) = θG hh • θ (q (i + 1)) :=
            (hs (q i)).equivariant hh (q (i + 1))
        _ = h • θ (q (i + 1)) := by rw [hhh]
        _ = θ (q (i + 1)) := by rw [hqi (i + 1)]; exact hfix (i + 1) hi
  have hh1 : hh = 1 := hW q hqnb hh hfixPath hfixN0 hfixN1
  calc h = θG hh := hhh.symm
    _ = θG 1 := by rw [hh1]
    _ = 1 := map_one θG

end Covering

section Completion

variable {α : RankTwoAmalgam.{u}} {Y : Type w} [Group Y]

theorem completion_moufangCondition_of_hat {n : ℕ} (c : α.Completion Y) (hc : c.IsFaithful)
    (hM : MoufangHat α n) :
    MoufangCondition ↥(c.φ1.range ⊔ c.φ2.range) c.graph n :=
  moufangCondition_of_covering (c.graphCovering hc) (c.Θ_smul hc) hM

theorem completion_weissFree_of_hat {n : ℕ} (c : α.Completion Y) (hc : c.IsFaithful)
    (hn : 1 ≤ n) (hW : WeissFreeHat α n) :
    WeissFree ↥(c.φ1.range ⊔ c.φ2.range) c.graph n :=
  weissFree_of_covering (c.graphCovering hc) (fun uh => c.stabIso hc uh) hn
    ((weissFreeHat_iff α n).mp hW)

end Completion

end CFSG.Quasithin.Stroth
