module

public import CFSG.Milestones.ASVolI.F411.Ident

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.ASVolI.ChF

@[expose] def burnsideF411_AutCentSylow (X : Type) [Group X] (p : ℕ) : Prop :=
  ∀ (α : MulAut X) (S : Sylow p X), (∀ s ∈ (S : Subgroup X), α s = s) →
    ∃ g : X, α = MulAut.conj g

theorem burnsideF411_autCentSylow_of_mulEquiv {X Y : Type} [Group X] [Group Y] [Finite Y] {p : ℕ}
    [Fact p.Prime]
    (e : X ≃* Y) (h : burnsideF411_AutCentSylow X p) : burnsideF411_AutCentSylow Y p := by
  intro α S hα
  let α' : MulAut X := (e.trans α).trans e.symm
  let S' : Sylow p X := Sylow.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective S
  have hα' : ∀ s ∈ (S' : Subgroup X), α' s = s := by
    intro s hs
    have hs' : s ∈ (S : Subgroup Y).map e.symm.toMonoidHom := hs
    obtain ⟨t, ht, rfl⟩ := hs'
    show e.symm (α (e (e.symm t))) = e.symm t
    rw [MulEquiv.apply_symm_apply, hα t ht]
  obtain ⟨g, hg⟩ := h α' S' hα'
  refine ⟨e g, MulEquiv.ext fun y => ?_⟩
  have := congrArg (fun β : MulAut X => e (β (e.symm y))) hg
  simp only [α', MulEquiv.trans_apply, MulEquiv.apply_symm_apply, MulAut.conj_apply] at this
  rw [MulAut.conj_apply, this, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

theorem burnsideF411_centSylow_of_aut {E : Type} [Group E] [Finite E] {p : ℕ} [Fact p.Prime]
    {Gp : Subgroup E}
    (hN : Gp.Normal) (hC : Subgroup.centralizer (Gp : Set E) = ⊥)
    (h : burnsideF411_AutCentSylow ↥Gp p) : burnsideF411_CentSylow p Gp := by
  intro S hS W _ hW w hw
  obtain ⟨hSGp, hSp, hSi⟩ := hS
  have hAp : IsPGroup p (S.subgroupOf Gp) :=
    hSp.of_equiv (Subgroup.subgroupOfEquivOfLe hSGp).symm
  let S' : Sylow p ↥Gp := hAp.toSylow hSi
  let α : MulAut ↥Gp := MulAut.conjNormal w
  have hα : ∀ s ∈ (S' : Subgroup ↥Gp), α s = s := by
    intro s hs
    apply Subtype.ext
    rw [MulAut.conjNormal_apply]
    have hsS : (s : E) ∈ S := (hs : s ∈ S.subgroupOf Gp)
    have hc := Subgroup.mem_centralizer_iff.mp (hW hw) (s : E) hsS
    calc w * (s : E) * w⁻¹ = (s : E) * w * w⁻¹ := by rw [← hc]
      _ = (s : E) := by group
  obtain ⟨g, hg⟩ := h α S' hα
  have hgw : (g : E)⁻¹ * w ∈ Subgroup.centralizer (Gp : Set E) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 := congrArg Subtype.val (congrArg (fun β : MulAut ↥Gp => β ⟨x, hx⟩) hg)
    simp only [α, MulAut.conjNormal_apply, MulAut.conj_apply, Subgroup.coe_mul,
      Subgroup.coe_inv] at h1
    calc x * ((g : E)⁻¹ * w) = (g : E)⁻¹ * ((g : E) * x * (g : E)⁻¹) * w := by group
      _ = (g : E)⁻¹ * (w * x * w⁻¹) * w := by rw [h1]
      _ = (g : E)⁻¹ * w * x := by group
  rw [hC, Subgroup.mem_bot] at hgw
  have : w = (g : E) := by
    have := congrArg (fun z => (g : E) * z) hgw
    simpa using this
  rw [this]
  exact g.2

end CFSG.ASVolI
