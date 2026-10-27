module

public import CFSG.Quasithin.Vol2.GoldschmidtF48RigRig

public section

namespace CFSG.Quasithin.H13.F48Rig

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

universe u

theorem f1_sup_f2 {α : RankTwoAmalgam.{u}} {Y : Type} [Group Y] (c : α.Completion Y) :
    (f1 (c := c)).range ⊔ (f2 (c := c)).range = ⊤ := by
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

variable {S : LieSetting.{u, 0}} {Y : Type} [Group Y] [Finite Y] (hS : S.Facts45L)
  (β : S.α.Completion Y) (hβ : β.IsFaithful) (hs : β.IsSmall S.m)

include hS hβ hs in
theorem exists_equiv_small (hT : S.CartanFPF) (hF : S.FaithfulOnType (decide (Odd S.m))) :
    ∃ θ : β.G0 ≃* S.ι.G0, (∀ p, θ (f1 (c := β) p) = f1 (c := S.ι) p) ∧
      ∀ q, θ (f2 (c := β) q) = f2 (c := S.ι) q := by
  set f := vEq hS β hβ hs with hf
  let Ψ : β.G0 →* Equiv.Perm (Vs S.ι (decide (Odd S.m))) :=
    (Equiv.permCongrHom f).toMonoidHom.comp
      (MulAction.toPermHom β.G0 (Vs β (decide (Odd S.m))))
  let Tι : S.ι.G0 →* Equiv.Perm (Vs S.ι (decide (Odd S.m))) :=
    MulAction.toPermHom S.ι.G0 (Vs S.ι (decide (Odd S.m)))
  have hTι : Function.Injective Tι := by
    rw [injective_iff_map_eq_one]
    intro k hk
    refine hF k fun v hv => ?_
    exact congrArg Subtype.val (congrArg (fun σ => σ ⟨v, hv⟩) hk)
  have hΨ1 : ∀ p, Ψ (f1 (c := β) p) = Tι (f1 (c := S.ι) p) := by
    intro p
    refine Equiv.ext fun z => ?_
    show f (f1 (c := β) p • f.symm z) = f1 (c := S.ι) p • z
    rw [vEq_f1 hS β hβ hs hT, Equiv.apply_symm_apply]
  have hΨ2 : ∀ q, Ψ (f2 (c := β) q) = Tι (f2 (c := S.ι) q) := by
    intro q
    refine Equiv.ext fun z => ?_
    show f (f2 (c := β) q • f.symm z) = f2 (c := S.ι) q • z
    rw [vEq_f2 hS β hβ hs, Equiv.apply_symm_apply]
  have hrange : ∀ g : β.G0, Ψ g ∈ Tι.range := by
    have hh : Tι.range.comap Ψ = ⊤ := by
      rw [eq_top_iff, ← f1_sup_f2 β]
      refine sup_le ?_ ?_
      · rintro _ ⟨p, rfl⟩
        exact ⟨f1 p, (hΨ1 p).symm⟩
      · rintro _ ⟨q, rfl⟩
        exact ⟨f2 q, (hΨ2 q).symm⟩
    intro g
    have hg : g ∈ Tι.range.comap Ψ := by rw [hh]; trivial
    exact hg
  let θ : β.G0 →* S.ι.G0 :=
    (MonoidHom.ofInjective hTι).symm.toMonoidHom.comp (Ψ.codRestrict Tι.range hrange)
  have hθ : ∀ g, Tι (θ g) = Ψ g := fun g =>
    congrArg Subtype.val ((MonoidHom.ofInjective hTι).apply_symm_apply ⟨Ψ g, hrange g⟩)
  have hθ1 : ∀ p, θ (f1 (c := β) p) = f1 (c := S.ι) p := fun p =>
    hTι (by rw [hθ, hΨ1])
  have hθ2 : ∀ q, θ (f2 (c := β) q) = f2 (c := S.ι) q := fun q =>
    hTι (by rw [hθ, hΨ2])
  have hsurj : Function.Surjective θ := by
    have hh : θ.range = ⊤ := by
      rw [eq_top_iff, ← f1_sup_f2 S.ι]
      refine sup_le ?_ ?_
      · rintro _ ⟨p, rfl⟩
        exact ⟨f1 p, hθ1 p⟩
      · rintro _ ⟨q, rfl⟩
        exact ⟨f2 q, hθ2 q⟩
    exact MonoidHom.range_eq_top.1 hh
  have hcard : Nat.card β.G0 ≤ Nat.card S.ι.G0 := by
    rw [card_G0 β, card_G0 S.ι, hS.lemma_F413_2 β hβ hs]
  exact ⟨MulEquiv.ofBijective θ (hsurj.bijective_of_nat_card_le hcard), hθ1, hθ2⟩

end CFSG.Quasithin.H13.F48Rig
