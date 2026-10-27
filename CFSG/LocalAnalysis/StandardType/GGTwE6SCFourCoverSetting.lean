module

public import CFSG.LocalAnalysis.StandardType.GGTwE6SCFourCoverMark
import CFSG.LocalAnalysis.StandardType.GGTableB

public section

namespace CFSG.StandardType.SCFourCover

open CFSG CFSG.Assembly CFSG.Blueprint TableB

@[expose] def GGTwE6SCFourSettingAd {R : Type} [Group R] (I : Set (MulAut R))
    (A : Subgroup (MulAut R)) (a₀ : MulAut R) (J₁ : Subgroup R) : Prop :=
  IsElemAbelian 3 A ∧ (∀ a ∈ A, a ∈ I) ∧ Nat.card A = 3 ^ 4 ∧ a₀ ∈ A ∧ a₀ ≠ 1 ∧
    IsComponentOf J₁ (ggFix a₀) ∧ (∀ a ∈ A, ∀ m ∈ J₁, a m ∈ J₁) ∧
    (∀ a ∈ A, (∀ m ∈ J₁, a m = m) → a ∈ Subgroup.zpowers a₀)

@[expose] def GGTwE6OfOutsideKnownAd : Prop :=
  ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
    LargeEvenLabelAll lab fun R _ I _ => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
      Finite R →
      ∀ (s t : MulAut R) (n : ℕ), s ^ 3 = 1 → t ^ 3 = 1 → s * t = t * s → s ∈ I → t ∈ I →
        3 ∣ 2 ^ n + 1 →
        ∀ J₁ : Subgroup R, IsComponentOf J₁ (ggFix s) →
          LargeEvenMarking ↥J₁ (fun lab' _ _ _ _ _ =>
            lab' = ⟨.D, 4, n⟩ ∨ lab' = ⟨.triD4, 0, n⟩ ∨ lab' = ⟨.A, 2, 3 * n⟩ ∨
              lab' = ⟨.twA, 2, 3 * n⟩) →
          GGOutsideInndiag J₁ t →
          (lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1) ∨ GGTorusLift 3 5 R

@[expose] def GGTwE6A5LKnownAd : Prop :=
  ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
    LargeEvenLabelAll lab fun R _ I _ => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
      Finite R →
      ∀ (B' : Subgroup (MulAut R)) (s : MulAut R) (n : ℕ), IsElemAbelian 3 B' →
        (∀ a ∈ B', a ∈ I) → s ∈ B' → s ≠ 1 → 3 ^ 4 ≤ Nat.card B' → 3 ∣ 2 ^ n + 1 →
        ∀ J₁ : Subgroup R, IsComponentOf J₁ (ggFix s) → (∀ a ∈ B', ∀ m ∈ J₁, a m ∈ J₁) →
          LargeEvenMarking ↥J₁ (fun lab' _ _ _ _ _ => lab' = ⟨.twA, 5, n⟩) →
          GGUnitaryCommLifts J₁ n 6 (B' : Set (MulAut R)) ∨
            (lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1) ∨ GGTorusLift 3 5 R

variable {L' R : Type} [Group L'] [Group R] {ψ : L' →* R}

theorem ggTwE6SCFourSetting_descend (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hL : commutator L' = ⊤) {I : Set (MulAut R)}
    {A : Subgroup (MulAut L')} {a₀ : MulAut L'} {J₁ : Subgroup L'}
    (h : GGTwE6SCFourSetting I ψ A a₀ J₁) {φ₀ : MulAut R} (hφ₀ : ∀ l, φ₀ (ψ l) = ψ (a₀ l)) :
    GGTwE6SCFourSettingAd I (TypeA.inducedSub ψ A) φ₀ (J₁.map ψ) := by
  obtain ⟨hE, hI, hcard, -, ha₀, hne, hcomp, hnorm, hcent⟩ := h
  have hJ := commutator_eq_self_of_isComponentOf hcomp
  refine ⟨TypeA.isElemAbelian_inducedSub hψ hE, inducedSub_subset hψ hI, ?_,
    TypeA.mem_inducedSub.2 ⟨a₀, ha₀, hφ₀⟩, fun h1 => hne ((induced_eq_one_iff hψ hker hL hφ₀).1 h1),
    (isComponentOf_map_iff hψ hker hφ₀ hJ).1 hcomp, fun φ hφ => ?_, fun φ hφ hfix => ?_⟩
  · rw [TypeA.card_inducedSub hψ hker hL fun a ha => (hI a ha).imp fun _ hφ => hφ.2]
    exact hcard
  · obtain ⟨a, ha, hc⟩ := TypeA.mem_inducedSub.1 hφ
    exact (mapsTo_map_iff hker hc hJ).1 (hnorm a ha)
  · obtain ⟨a, ha, hc⟩ := TypeA.mem_inducedSub.1 hφ
    exact (induced_mem_zpowers_iff hψ hker hL hc hφ₀).2
      (hcent a ha ((fixes_map_iff hker hc hJ).2 hfix))

theorem ggTwE6A5LKnown_of_ad (h : GGTwE6A5LKnownAd) : GGTwE6A5LKnown := by
  intro lab hlab
  refine LargeEvenLabelAll.mono ?_ (h lab hlab)
  rintro R _ _ _ hR hs hna L' _ _ ψ hψ hker hL B s n hB hBI hsB hs1 hcard hn J₁ hJ₁ hBJ hmark
  have hfin : Finite R := Finite.of_surjective ψ hψ
  have hJ := commutator_eq_self_of_isComponentOf hJ₁
  have hA : ∀ a ∈ B, ∃ φ : MulAut R, ∀ l, φ (ψ l) = ψ (a l) := fun a ha =>
    (hBI a ha).imp fun _ hφ => hφ.2
  obtain ⟨φs, -, hφs⟩ := hBI s hsB
  rcases hR hs hna hfin (TypeA.inducedSub ψ B) φs n (TypeA.isElemAbelian_inducedSub hψ hB)
      (inducedSub_subset hψ hBI) (TypeA.mem_inducedSub.2 ⟨s, hsB, hφs⟩)
      (fun h1 => hs1 ((induced_eq_one_iff hψ hker hL hφs).1 h1))
      (by rw [TypeA.card_inducedSub hψ hker hL hA]; exact hcard) hn (J₁.map ψ)
      ((isComponentOf_map_iff hψ hker hφs hJ).1 hJ₁)
      (fun φ hφ => by
        obtain ⟨a, ha, hc⟩ := TypeA.mem_inducedSub.1 hφ
        exact (mapsTo_map_iff hker hc hJ).1 (hBJ a ha))
      ((largeEvenMarking_map_iff hker hJ _).1 hmark) with hc | hc
  · exact Or.inl ((ggUnitaryCommLifts_map_iff hker hJ n 6 hA).2 hc)
  · exact Or.inr hc

end CFSG.StandardType.SCFourCover

end
