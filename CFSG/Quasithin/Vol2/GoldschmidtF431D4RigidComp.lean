module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4OverB
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4Setting
public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsGeoAbs

public noncomputable section

namespace CFSG.Quasithin.D4Hex

open CFSG.LargeExtraspecial.S63 CFSG.Quasithin CFSG.D4Hex CFSG.Quasithin.RankTwoAmalgam
  CFSG.Quasithin.RankTwoAmalgam.Completion
open CFSG.Quasithin.TitsGeo (TitsModel)

section Small

theorem isSmall_of_card_le (S : LieSetting.{0, 0}) {k : ℕ} (hm : S.m = k + 2)
    (M : TitsModel S.ι k) (hpoly : IsGenPolygon S.ι.graph S.m) {Y : Type} [Group Y] [Finite Y]
    (β : S.α.Completion Y) (hβ : β.IsFaithful) (hle : Nat.card Y ≤ Nat.card S.Yb) :
    β.IsSmall S.m := by
  have hev : Even S.m := by
    rw [hm]
    exact M.even.add (by decide)
  have Fι : S.ι.Facts46 S.m := by
    rw [hm]
    exact M.facts46 S.hι
  have Fβ : β.Facts46 S.m := by
    rw [hm]
    exact M.facts46 hβ
  have hsι : S.ι.IsSmall S.m := by
    obtain ⟨T, hT⟩ := hpoly.polygon
    exact Fι.isSmall_of_polygon hT
  by_contra h
  have hl : β.IsLarge S.m := not_not.mp h
  have hlt := Facts46.ptsCard_lt_of_large_even Fβ Fι hev hl hsι
  have e1 := card_Y_eq β Fβ.faithful
  have e2 := card_Y_eq S.ι Fι.faithful
  have hp := LieSetting.card_G1_pos β Fβ.faithful
  have : S.ι.ptsCard * Nat.card S.α.G1 < β.ptsCard * Nat.card S.α.G1 :=
    Nat.mul_lt_mul_of_pos_right hlt hp
  omega

end Small

section Completion


theorem exists_d4_completion (a₁ : MulAut ↥d4H) (a₂ : MulAut ↥d4N)
    (hag : ∀ (x : D) (h₁ : x ∈ d4H) (h₂ : x ∈ d4N),
      ((a₁ ⟨x, h₁⟩ : ↥d4H) : D) = ((a₂ ⟨x, h₂⟩ : ↥d4N) : D)) :
    ∃ β : d4Setting.α.Completion D, (∀ x : ↥d4H, β.φ1 x = ((a₁ x : ↥d4H) : D)) ∧
      (∀ x : ↥d4N, β.φ2 x = ((a₂ x : ↥d4N) : D)) ∧ β.IsFaithful := by
  have : Finite D := finite_D'
  let φ1 : ↥d4H →* D := d4H.subtype.comp a₁.toMonoidHom
  let φ2 : ↥d4N →* D := d4N.subtype.comp a₂.toMonoidHom
  let φ12 : ↥(d4H ⊓ d4N) →* D := φ1.comp (Subgroup.inclusion inf_le_left)
  have hr1 : φ1.range = d4H := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 a₁.surjective, Subgroup.map_top]
    exact Subgroup.range_subtype _
  have hr2 : φ2.range = d4N := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 a₂.surjective, Subgroup.map_top]
    exact Subgroup.range_subtype _
  have h12 : ∀ g : ↥(d4H ⊓ d4N), φ12 g = ((a₁ ⟨g.1, g.2.1⟩ : ↥d4H) : D) := fun g => rfl
  have h12' : ∀ g : ↥(d4H ⊓ d4N), φ12 g = ((a₂ ⟨g.1, g.2.2⟩ : ↥d4N) : D) := fun g =>
    hag g.1 g.2.1 g.2.2
  have hmem : ∀ g : ↥(d4H ⊓ d4N), ((a₁ ⟨g.1, g.2.1⟩ : ↥d4H) : D) ∈ d4H ⊓ d4N := fun g =>
    ⟨(a₁ ⟨g.1, g.2.1⟩).2, by rw [← h12 g, h12' g]; exact (a₂ ⟨g.1, g.2.2⟩).2⟩
  have hr12 : φ12.range = d4H ⊓ d4N := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      rw [h12 g]
      exact hmem g
    · intro hx
      let g₀ : ↥(d4H ⊓ d4N) → ↥(d4H ⊓ d4N) := fun g => ⟨_, hmem g⟩
      have hinj : Function.Injective g₀ := fun g g' h => by
        have h2 : ((a₁ ⟨g.1, g.2.1⟩ : ↥d4H) : D) = ((a₁ ⟨g'.1, g'.2.1⟩ : ↥d4H) : D) :=
          congrArg (fun z : ↥(d4H ⊓ d4N) => (z : D)) h
        have h3 := a₁.injective (Subtype.ext h2)
        exact Subtype.ext (Subtype.mk.inj h3)
      obtain ⟨g, hg⟩ := Finite.surjective_of_injective hinj ⟨x, hx⟩
      exact ⟨g, (h12 g).trans (congrArg Subtype.val hg)⟩
  let β : d4Setting.α.Completion D :=
    { φ1 := φ1
      φ12 := φ12
      φ2 := φ2
      comm1 := fun g => rfl
      comm2 := fun g => (hag g.1 g.2.1 g.2.2).symm
      inter := (congrArg₂ (fun A B : Subgroup D => A ⊓ B) hr1 hr2).trans hr12.symm
      gen := (congrArg₂ (fun A B : Subgroup D => A ⊔ B) hr1 hr2).trans d4H_sup_d4N }
  refine ⟨β, fun x => rfl, fun x => rfl, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · exact fun x y h => a₁.injective (Subtype.ext h)
  · exact fun x y h => Subgroup.inclusion_injective _ (a₁.injective (Subtype.ext h))
  · exact fun x y h => a₂.injective (Subtype.ext h)

end Completion

end CFSG.Quasithin.D4Hex
