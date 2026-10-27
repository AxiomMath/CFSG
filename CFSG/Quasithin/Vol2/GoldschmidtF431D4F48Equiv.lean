module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsGeoF48Eqv

public noncomputable section

namespace CFSG.Quasithin.D4Hex

open CFSG.Quasithin CFSG.Quasithin.TitsGeo CFSG.Quasithin.H13.F48Gen
  CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

@[expose] def PtRigid (S : LieSetting.{0, 0}) (n : S.α.G1) (q : S.α.G2) (M : ℕ) : Prop :=
  ∀ π : S.α.G1 →* Equiv.Perm (Pt S.ι),
    (∀ (x : S.α.G12) (z : Pt S.ι), π (S.α.α1 x) z = f1 (c := S.ι) (S.α.α1 x) • z) →
    (∀ (p : S.α.G1) (z : Pt S.ι), Near S.m S.ι z → π p z = f1 (c := S.ι) p • z) →
    (π n * MulAction.toPerm (f2 (c := S.ι) q)) ^ M = 1 →
    ∀ (p : S.α.G1) (z : Pt S.ι), π p z = f1 (c := S.ι) p • z

section Equiv

variable (S : LieSetting.{0, 0}) {k : ℕ} (hm : S.m = k + 2) (M : TitsModel S.ι k)
  (hpoly : IsGenPolygon S.ι.graph S.m) {n : S.α.G1} {q : S.α.G2} {Mord : ℕ}
  (hcard : Nat.card S.Yb ∣ Mord) (hrig : PtRigid S n q Mord)
  (hTι : Function.Injective (MulAction.toPermHom S.ι.G0 (Pt S.ι)))

include hm M hpoly hcard hrig hTι in
theorem f48_equiv_small {Y₀ : Type} [Group Y₀] [Finite Y₀] (β : S.α.Completion Y₀)
    (hβ : β.IsFaithful) (hs : β.IsSmall S.m) :
    ∃ θ : β.G0 ≃* S.ι.G0, (∀ p, θ (f1 (c := β) p) = f1 (c := S.ι) p) ∧
      ∀ q, θ (f2 (c := β) q) = f2 (c := S.ι) q := by
  have hev : Even S.m := by
    rw [hm]
    exact M.even.add (by decide)
  have Fβ : β.Facts46 S.m := by
    rw [hm]
    exact M.facts46 hβ
  have Fι : S.ι.Facts46 S.m := by
    rw [hm]
    exact M.facts46 S.hι
  have hSι : S.ι.IsSmall S.m := by
    obtain ⟨T, hT⟩ := hpoly.polygon
    exact Fι.isSmall_of_polygon hT
  have Dβ : ∀ u v : β.Γ, β.graph.dist u v ≤ S.m := Fβ.diam_le hs
  have Dι : ∀ u v : S.ι.Γ, S.ι.graph.dist u v ≤ S.m := hpoly.diam_le
  have hcardβ : Nat.card β.G0 ∣ Mord := by
    rw [card_G0 β, card_Y_eq_of_small Fβ Fι hs hSι]
    exact hcard
  have hE2 := ptEquiv_f2 β S.ι hβ S.hι hev Fβ Fι Dβ Dι
  have hE1 := ptEquiv_f1 β S.ι hβ S.hι hev Fβ Fι Dβ Dι
  have hNear := ptEquiv_near β S.ι hβ S.hι hev Fβ Fι Dβ Dι
  set f := ptEquiv β S.ι hβ S.hι hev Fβ Fι Dβ Dι with hf
  let Ψ : β.G0 →* Equiv.Perm (Pt S.ι) :=
    (titsPermConj f).comp (MulAction.toPermHom β.G0 (Pt β))
  let π : S.α.G1 →* Equiv.Perm (Pt S.ι) := Ψ.comp f1
  have hπ : ∀ p z, π p z = f (f1 (c := β) p • f.symm z) := fun p z => rfl
  have hΨ2 : ∀ q, Ψ (f2 (c := β) q) = MulAction.toPerm (f2 (c := S.ι) q) := by
    intro q
    refine Equiv.ext fun z => ?_
    show f (f2 (c := β) q • f.symm z) = f2 (c := S.ι) q • z
    rw [hE2, Equiv.apply_symm_apply]
  have hX : (π n * MulAction.toPerm (f2 (c := S.ι) q)) ^ Mord = 1 := by
    have e : π n * MulAction.toPerm (f2 (c := S.ι) q) =
        Ψ (f1 (c := β) n * f2 (c := β) q) :=
      (congrArg (π n * ·) (hΨ2 q).symm).trans (map_mul Ψ _ _).symm
    calc (π n * MulAction.toPerm (f2 (c := S.ι) q)) ^ Mord
        = Ψ (f1 (c := β) n * f2 (c := β) q) ^ Mord := by rw [e]
      _ = Ψ ((f1 (c := β) n * f2 (c := β) q) ^ Mord) := (map_pow Ψ _ _).symm
      _ = 1 := by
        rw [orderOf_dvd_iff_pow_eq_one.1 ((orderOf_dvd_natCard _).trans hcardβ), map_one]
  have hall1 : ∀ p w, f (f1 (c := β) p • w) = f1 (c := S.ι) p • f w := by
    intro p w
    have := hrig π (fun x z => by
        rw [hπ, f1_eq_f2 β x, hE2, Equiv.apply_symm_apply, f1_eq_f2 S.ι x])
      (fun p z hz => by
        have hw : Near S.m β (f.symm z) := (hNear _).1 (by rw [Equiv.apply_symm_apply]; exact hz)
        rw [hπ, hE1 p _ hw, Equiv.apply_symm_apply]) hX p (f w)
    rw [hπ, Equiv.symm_apply_apply] at this
    exact this
  let Tι : S.ι.G0 →* Equiv.Perm (Pt S.ι) := MulAction.toPermHom S.ι.G0 (Pt S.ι)
  have hΨ1 : ∀ p, Ψ (f1 (c := β) p) = Tι (f1 (c := S.ι) p) := by
    intro p
    refine Equiv.ext fun z => ?_
    show f (f1 (c := β) p • f.symm z) = f1 (c := S.ι) p • z
    rw [hall1, Equiv.apply_symm_apply]
  have hΨ2' : ∀ q, Ψ (f2 (c := β) q) = Tι (f2 (c := S.ι) q) := hΨ2
  have hrange : ∀ g : β.G0, Ψ g ∈ Tι.range := by
    have hh : Tι.range.comap Ψ = ⊤ := by
      rw [eq_top_iff, ← f1_sup_f2 β]
      refine sup_le ?_ ?_
      · rintro _ ⟨p, rfl⟩
        exact ⟨f1 p, (hΨ1 p).symm⟩
      · rintro _ ⟨q, rfl⟩
        exact ⟨f2 q, (hΨ2' q).symm⟩
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
    hTι (by rw [hθ, hΨ2'])
  have hsurj : Function.Surjective θ := by
    have hh : θ.range = ⊤ := by
      rw [eq_top_iff, ← f1_sup_f2 S.ι]
      refine sup_le ?_ ?_
      · rintro _ ⟨p, rfl⟩
        exact ⟨f1 p, hθ1 p⟩
      · rintro _ ⟨q, rfl⟩
        exact ⟨f2 q, hθ2 q⟩
    exact MonoidHom.range_eq_top.1 hh
  have hle : Nat.card β.G0 ≤ Nat.card S.ι.G0 := by
    rw [card_G0 β, card_G0 S.ι, card_Y_eq_of_small Fβ Fι hs hSι]
  exact ⟨MulEquiv.ofBijective θ (hsurj.bijective_of_nat_card_le hle), hθ1, hθ2⟩

end Equiv

end CFSG.Quasithin.D4Hex
