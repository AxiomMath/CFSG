module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42F48Rig
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42F45Main

public section

namespace CFSG.Quasithin.H13.F431.U42

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
  CFSG.Quasithin.H13.F431.U42.F48

section Generic

variable {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y]

theorem f48_f1_sup_f2 (c : α.Completion Y) : (f1 (c := c)).range ⊔ (f2 (c := c)).range = ⊤ := by
  have h1 : (f1 (c := c)).range.map (c.φ1.range ⊔ c.φ2.range).subtype = c.φ1.range := by
    ext y
    constructor
    · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
      exact ⟨a, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨_, ⟨a, rfl⟩, rfl⟩
  have h2 : (f2 (c := c)).range.map (c.φ1.range ⊔ c.φ2.range).subtype = c.φ2.range := by
    ext y
    constructor
    · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
      exact ⟨a, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨_, ⟨a, rfl⟩, rfl⟩
  refine Subgroup.map_injective (f := (c.φ1.range ⊔ c.φ2.range).subtype)
    (Subgroup.subtype_injective _) ?_
  rw [Subgroup.map_sup, h1, h2, Subgroup.map_top, Subgroup.range_subtype]

@[expose] def f48MapEquivComp {Y' : Type} [Group Y'] (c : α.Completion Y) (e : Y ≃* Y') :
    α.Completion Y' where
  φ1 := e.toMonoidHom.comp c.φ1
  φ12 := e.toMonoidHom.comp c.φ12
  φ2 := e.toMonoidHom.comp c.φ2
  comm1 g := by simp [c.comm1]
  comm2 g := by simp [c.comm2]
  inter := by
    simp only [MonoidHom.range_comp]
    rw [← Subgroup.map_inf _ _ _ e.injective, c.inter]
  gen := by
    simp only [MonoidHom.range_comp]
    rw [← Subgroup.map_sup, c.gen, Subgroup.map_top, MonoidHom.range_eq_top.2 e.surjective]

theorem f48MapEquivComp_faithful {Y' : Type} [Group Y'] {c : α.Completion Y} (hc : c.IsFaithful)
    (e : Y ≃* Y') : (f48MapEquivComp c e).IsFaithful :=
  ⟨e.injective.comp hc.1, e.injective.comp hc.2.1, e.injective.comp hc.2.2⟩

theorem f48MapEquivComp_equiv {Y' : Type} [Group Y'] (c : α.Completion Y) (e : Y ≃* Y') :
    Amalgam.Completion.IsEquivalent c.toCompletion (f48MapEquivComp c e).toCompletion :=
  ⟨e, fun d x => by cases d <;> rfl⟩

end Generic

section Assembly

theorem u42_f1_eq_f2 {Y : Type}
    [Group Y] (c : u42Setting.α.Completion Y) (x : u42Setting.α.G12) :
    f1 (c := c) (u42Setting.α.α1 x) = f2 (c := c) (u42Setting.α.α2 x) :=
  Subtype.ext ((c.comm1 x).trans (c.comm2 x).symm)

theorem u42_toPerm_injective :
    Function.Injective (MulAction.toPermHom u42Setting.ι.G0 (Pt u42Setting.ι)) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  apply stdG0_injective
  rw [map_one]
  ext m
  obtain ⟨z, rfl⟩ := u42Kappa.surjective m
  rw [← u42Kappa_smul]
  have := congrArg (fun σ : Equiv.Perm (Pt u42Setting.ι) => σ z) hg
  simp only [MulAction.toPermHom_apply, MulAction.toPerm_apply, Equiv.Perm.one_apply] at this
  rw [this]
  rfl

theorem u42_equiv_small
    {Y₀ : Type} [Group Y₀] [Finite Y₀]
    (β : u42Setting.α.Completion Y₀) (hβ : β.IsFaithful) (hs : β.IsSmall (polyNumber .PSU)) :
    ∃ θ : β.G0 ≃* u42Setting.ι.G0, (∀ p, θ (f1 (c := β) p) = f1 (c := u42Setting.ι) p) ∧
      ∀ q, θ (f2 (c := β) q) = f2 (c := u42Setting.ι) q := by
  have hF := facts45L_u42
  have Fβ : β.Facts46 4 := hF.facts46 β hβ
  have Fι : u42Setting.ι.Facts46 4 := hF.facts46 u42Setting.ι u42Setting.hι
  have Dβ : ∀ u v : β.Γ, β.graph.dist u v ≤ 4 := Fβ.diam_le hs
  have Dι : ∀ u v : u42Setting.ι.Γ, u42Setting.ι.graph.dist u v ≤ 4 := hF.poly.diam_le
  have hE2 := ptEquiv_f2 β u42Setting.ι hβ u42Setting.hι Fβ Fι Dβ Dι
  have hE1 := ptEquiv_f1 β u42Setting.ι hβ u42Setting.hι Fβ Fι Dβ Dι
  have hNear := ptEquiv_near β u42Setting.ι hβ u42Setting.hι Fβ Fι Dβ Dι
  set f := ptEquiv β u42Setting.ι hβ u42Setting.hι Fβ Fι Dβ Dι with hf
  let π : u42Setting.α.G1 →* Equiv.Perm (Pt u42Setting.ι) :=
    (f48PermConj f).comp ((MulAction.toPermHom β.G0 (Pt β)).comp f1)
  have hπ : ∀ p z, π p z = f (f1 (c := β) p • f.symm z) := fun p z => rfl
  have hall1 : ∀ p w, f (f1 (c := β) p • w) = f1 (c := u42Setting.ι) p • f w := by
    intro p w
    have := u42_rigid π (fun x z => by
        rw [hπ, u42_f1_eq_f2 β x, hE2, Equiv.apply_symm_apply, u42_f1_eq_f2 u42Setting.ι x])
      (fun p z hz => by
        have hw : Near β (f.symm z) := (hNear _).1 (by rw [Equiv.apply_symm_apply]; exact hz)
        rw [hπ, hE1 p _ hw, Equiv.apply_symm_apply]) p (f w)
    rw [hπ, Equiv.symm_apply_apply] at this
    exact this
  let Tι : u42Setting.ι.G0 →* Equiv.Perm (Pt u42Setting.ι) :=
    MulAction.toPermHom u42Setting.ι.G0 (Pt u42Setting.ι)
  have hTι : Function.Injective Tι := u42_toPerm_injective
  let Ψ : β.G0 →* Equiv.Perm (Pt u42Setting.ι) :=
    (f48PermConj f).comp (MulAction.toPermHom β.G0 (Pt β))
  have hΨ1 : ∀ p, Ψ (f1 (c := β) p) = Tι (f1 (c := u42Setting.ι) p) := by
    intro p
    refine Equiv.ext fun z => ?_
    show f (f1 (c := β) p • f.symm z) = f1 (c := u42Setting.ι) p • z
    rw [hall1, Equiv.apply_symm_apply]
  have hΨ2 : ∀ q, Ψ (f2 (c := β) q) = Tι (f2 (c := u42Setting.ι) q) := by
    intro q
    refine Equiv.ext fun z => ?_
    show f (f2 (c := β) q • f.symm z) = f2 (c := u42Setting.ι) q • z
    rw [hE2, Equiv.apply_symm_apply]
  have hrange : ∀ g : β.G0, Ψ g ∈ Tι.range := by
    have h : Tι.range.comap Ψ = ⊤ := by
      rw [eq_top_iff, ← f48_f1_sup_f2 β]
      refine sup_le ?_ ?_
      · rintro _ ⟨p, rfl⟩
        exact ⟨f1 p, (hΨ1 p).symm⟩
      · rintro _ ⟨q, rfl⟩
        exact ⟨f2 q, (hΨ2 q).symm⟩
    intro g
    have hg : g ∈ Tι.range.comap Ψ := by rw [h]; trivial
    exact hg
  let θ : β.G0 →* u42Setting.ι.G0 :=
    (MonoidHom.ofInjective hTι).symm.toMonoidHom.comp (Ψ.codRestrict Tι.range hrange)
  have hθ : ∀ g, Tι (θ g) = Ψ g := fun g =>
    congrArg Subtype.val ((MonoidHom.ofInjective hTι).apply_symm_apply ⟨Ψ g, hrange g⟩)
  have hθ1 : ∀ p, θ (f1 (c := β) p) = f1 (c := u42Setting.ι) p := fun p =>
    hTι (by rw [hθ, hΨ1])
  have hθ2 : ∀ q, θ (f2 (c := β) q) = f2 (c := u42Setting.ι) q := fun q =>
    hTι (by rw [hθ, hΨ2])
  have hsurj : Function.Surjective θ := by
    have h : θ.range = ⊤ := by
      rw [eq_top_iff, ← f48_f1_sup_f2 u42Setting.ι]
      refine sup_le ?_ ?_
      · rintro _ ⟨p, rfl⟩
        exact ⟨f1 p, hθ1 p⟩
      · rintro _ ⟨q, rfl⟩
        exact ⟨f2 q, hθ2 q⟩
    exact MonoidHom.range_eq_top.1 h
  have hcard : Nat.card β.G0 ≤ Nat.card u42Setting.ι.G0 := by
    rw [card_G0 β, card_G0 u42Setting.ι, hF.lemma_F413_2 β hβ hs]
  exact ⟨MulEquiv.ofBijective θ (hsurj.bijective_of_nat_card_le hcard), hθ1, hθ2⟩

end Assembly

end CFSG.Quasithin.H13.F431.U42
