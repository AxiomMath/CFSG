module

public import CFSG.Quasithin.Vol2.TwoF4F48Rig
public import CFSG.Quasithin.Vol2.GoldschmidtF45RuCert
public import CFSG.Quasithin.Recognition.F4Thirteen

public section

namespace CFSG.Quasithin.H13.TwoF4F48

open CFSG.Quasithin CFSG.Sporadic.Schreier.Tits CFSG.RuF45 CFSG.Quasithin.RuType
  CFSG.Quasithin.H13.F45Ru CFSG.Quasithin.H13.F48Gen CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.TwoF4F48 CFSG.Quasithin.RankTwoAmalgam
  CFSG.Quasithin.RankTwoAmalgam.Completion

local notation "TA" => CFSG.Sporadic.Schreier.Tits.titsA

section Generic

variable {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y]

theorem f1_sup_f2 (c : α.Completion Y) : (f1 (c := c)).range ⊔ (f2 (c := c)).range = ⊤ := by
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

theorem f1_eq_f2 (c : α.Completion Y) (x : α.G12) :
    f1 (c := c) (α.α1 x) = f2 (c := c) (α.α2 x) :=
  Subtype.ext ((c.comm1 x).trans (c.comm2 x).symm)

@[expose] def mapEquivComp {Y' : Type} [Group Y'] (c : α.Completion Y) (e : Y ≃* Y') :
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

theorem mapEquivComp_faithful {Y' : Type} [Group Y'] {c : α.Completion Y} (hc : c.IsFaithful)
    (e : Y ≃* Y') : (mapEquivComp c e).IsFaithful :=
  ⟨e.injective.comp hc.1, e.injective.comp hc.2.1, e.injective.comp hc.2.2⟩

theorem mapEquivComp_equiv {Y' : Type} [Group Y'] (c : α.Completion Y) (e : Y ≃* Y') :
    Amalgam.Completion.IsEquivalent c.toCompletion (mapEquivComp c e).toCompletion :=
  ⟨e, fun d x => by cases d <;> rfl⟩

end Generic

section Assembly


theorem card_Yb : Nat.card twoF4Setting.Yb = gOrder := by
  show Nat.card ↥(twoF4H ⊔ twoF4N) = 35942400
  rw [sup_eq_TA, card_titsA]

theorem card_G0_small {Y₀ : Type} [Group Y₀] [Finite Y₀] (β : twoF4Setting.α.Completion Y₀)
    (hβ : β.IsFaithful) (hs : β.IsSmall twoF4Setting.m) : Nat.card β.G0 = gOrder := by
  rw [card_G0 β, (f45TwoF4 : twoF4Setting.Facts45L).lemma_F413_2 β hβ hs, card_Yb]

theorem twoF4_equiv_small {Y₀ : Type} [Group Y₀] [Finite Y₀] (β : twoF4Setting.α.Completion Y₀)
    (hβ : β.IsFaithful) (hs : β.IsSmall twoF4Setting.m) :
    ∃ θ : β.G0 ≃* twoF4Setting.ι.G0, (∀ p, θ (f1 (c := β) p) = f1 (c := twoF4Setting.ι) p) ∧
      ∀ q, θ (f2 (c := β) q) = f2 (c := twoF4Setting.ι) q := by
  have hF : twoF4Setting.Facts45L := f45TwoF4
  have hm : Even 8 := by decide
  have Fβ : β.Facts46 8 := hF.facts46 β hβ
  have Fι : twoF4Setting.ι.Facts46 8 := hF.facts46 twoF4Setting.ι twoF4Setting.hι
  have Dβ : ∀ u v : β.Γ, β.graph.dist u v ≤ 8 := Fβ.diam_le hs
  have Dι : ∀ u v : twoF4Setting.ι.Γ, twoF4Setting.ι.graph.dist u v ≤ 8 := hF.poly.diam_le
  have hE2 := ptEquiv_f2 β twoF4Setting.ι hβ twoF4Setting.hι hm Fβ Fι Dβ Dι
  have hE1 := ptEquiv_f1 β twoF4Setting.ι hβ twoF4Setting.hι hm Fβ Fι Dβ Dι
  have hNear := ptEquiv_near β twoF4Setting.ι hβ twoF4Setting.hι hm Fβ Fι Dβ Dι
  set f := ptEquiv β twoF4Setting.ι hβ twoF4Setting.hι hm Fβ Fι Dβ Dι with hf
  let Ψ : β.G0 →* Equiv.Perm (Pt twoF4Setting.ι) :=
    (permConj f).comp (MulAction.toPermHom β.G0 (Pt β))
  let π : twoF4Setting.α.G1 →* Equiv.Perm (Pt twoF4Setting.ι) := Ψ.comp f1
  have hπ : ∀ p z, π p z = f (f1 (c := β) p • f.symm z) := fun p z => rfl
  have hΨ2 : ∀ q, Ψ (f2 (c := β) q) = MulAction.toPerm (f2 (c := twoF4Setting.ι) q) := by
    intro q
    refine Equiv.ext fun z => ?_
    show f (f2 (c := β) q • f.symm z) = f2 (c := twoF4Setting.ι) q • z
    rw [hE2, Equiv.apply_symm_apply]
  have hX : (π ⟨titsGen 3, n1_mem⟩ *
      MulAction.toPerm (f2 (c := twoF4Setting.ι) ⟨titsGen 2, q_mem_N⟩)) ^ gOrder = 1 := by
    have e : π ⟨titsGen 3, n1_mem⟩ *
        MulAction.toPerm (f2 (c := twoF4Setting.ι) ⟨titsGen 2, q_mem_N⟩) =
        Ψ (f1 (c := β) ⟨titsGen 3, n1_mem⟩ * f2 (c := β) ⟨titsGen 2, q_mem_N⟩) :=
      (congrArg (π ⟨titsGen 3, n1_mem⟩ * ·) (hΨ2 ⟨titsGen 2, q_mem_N⟩).symm).trans
        (map_mul Ψ _ _).symm
    calc (π ⟨titsGen 3, n1_mem⟩ *
          MulAction.toPerm (f2 (c := twoF4Setting.ι) ⟨titsGen 2, q_mem_N⟩)) ^ gOrder
        = Ψ (f1 (c := β) ⟨titsGen 3, n1_mem⟩ * f2 (c := β) ⟨titsGen 2, q_mem_N⟩) ^
            gOrder := by rw [e]
      _ = Ψ ((f1 (c := β) ⟨titsGen 3, n1_mem⟩ * f2 (c := β) ⟨titsGen 2, q_mem_N⟩) ^
            gOrder) := (map_pow Ψ _ _).symm
      _ = Ψ ((f1 (c := β) ⟨titsGen 3, n1_mem⟩ * f2 (c := β) ⟨titsGen 2, q_mem_N⟩) ^
            Nat.card β.G0) := by rw [card_G0_small β hβ hs]
      _ = 1 := by rw [pow_card_eq_one', map_one]
  have hall1 : ∀ p w, f (f1 (c := β) p • w) = f1 (c := twoF4Setting.ι) p • f w := by
    intro p w
    have := twoF4_rigid_pt π (fun x z => by
        rw [hπ, f1_eq_f2 β x, hE2, Equiv.apply_symm_apply, f1_eq_f2 twoF4Setting.ι x])
      (fun p z hz => by
        have hw : Near 8 β (f.symm z) := (hNear _).1 (by rw [Equiv.apply_symm_apply]; exact hz)
        rw [hπ, hE1 p _ hw, Equiv.apply_symm_apply]) hX p (f w)
    rw [hπ, Equiv.symm_apply_apply] at this
    exact this
  let Tι : twoF4Setting.ι.G0 →* Equiv.Perm (Pt twoF4Setting.ι) :=
    MulAction.toPermHom twoF4Setting.ι.G0 (Pt twoF4Setting.ι)
  have hTι : Function.Injective Tι := toPerm_injective
  have hΨ1 : ∀ p, Ψ (f1 (c := β) p) = Tι (f1 (c := twoF4Setting.ι) p) := by
    intro p
    refine Equiv.ext fun z => ?_
    show f (f1 (c := β) p • f.symm z) = f1 (c := twoF4Setting.ι) p • z
    rw [hall1, Equiv.apply_symm_apply]
  have hΨ2' : ∀ q, Ψ (f2 (c := β) q) = Tι (f2 (c := twoF4Setting.ι) q) := hΨ2
  have hrange : ∀ g : β.G0, Ψ g ∈ Tι.range := by
    have h : Tι.range.comap Ψ = ⊤ := by
      rw [eq_top_iff, ← f1_sup_f2 β]
      refine sup_le ?_ ?_
      · rintro _ ⟨p, rfl⟩
        exact ⟨f1 p, (hΨ1 p).symm⟩
      · rintro _ ⟨q, rfl⟩
        exact ⟨f2 q, (hΨ2' q).symm⟩
    intro g
    have hg : g ∈ Tι.range.comap Ψ := by rw [h]; trivial
    exact hg
  let θ : β.G0 →* twoF4Setting.ι.G0 :=
    (MonoidHom.ofInjective hTι).symm.toMonoidHom.comp (Ψ.codRestrict Tι.range hrange)
  have hθ : ∀ g, Tι (θ g) = Ψ g := fun g =>
    congrArg Subtype.val ((MonoidHom.ofInjective hTι).apply_symm_apply ⟨Ψ g, hrange g⟩)
  have hθ1 : ∀ p, θ (f1 (c := β) p) = f1 (c := twoF4Setting.ι) p := fun p =>
    hTι (by rw [hθ, hΨ1])
  have hθ2 : ∀ q, θ (f2 (c := β) q) = f2 (c := twoF4Setting.ι) q := fun q =>
    hTι (by rw [hθ, hΨ2'])
  have hsurj : Function.Surjective θ := by
    have h : θ.range = ⊤ := by
      rw [eq_top_iff, ← f1_sup_f2 twoF4Setting.ι]
      refine sup_le ?_ ?_
      · rintro _ ⟨p, rfl⟩
        exact ⟨f1 p, hθ1 p⟩
      · rintro _ ⟨q, rfl⟩
        exact ⟨f2 q, hθ2 q⟩
    exact MonoidHom.range_eq_top.1 h
  have hcard : Nat.card β.G0 ≤ Nat.card twoF4Setting.ι.G0 := by
    rw [card_G0 β, card_G0 twoF4Setting.ι, hF.lemma_F413_2 β hβ hs]
  exact ⟨MulEquiv.ofBijective θ (hsurj.bijective_of_nat_card_le hcard), hθ1, hθ2⟩

end Assembly

end CFSG.Quasithin.H13.TwoF4F48
