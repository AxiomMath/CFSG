module

public import CFSG.RankThree.PartTwo.Sec13.Item138
public import CFSG.RankThree.PartTwo.Sec13.Steps

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

@[expose] def Item138N : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec13Data G A c L → IsLThreePi (L ⧸ aschbacherSolvableCore 3 L) →
      ∀ E : Subgroup G, c ∈ E → CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 27 →
        E ≤ Subgroup.normalizer (L : Set G) →
        Late.sectionCentralizer E L ((aschbacherSolvableCore 3 L).map L.subtype) =
          (Subgroup.zpowers c : Set G) →
        HypS E ∨ HypT E → Sec4.IsTypeCOn E L →
          Sec8.IsZ3PGLThreePi (lBarA c L E) ∧
          (∀ (p e : ℕ) [Fact p.Prime], 1 ≤ e →
            Sec4.IsoLThreePi (L ⧸ aschbacherSolvableCore 3 L) p e →
              ¬ (p ^ e % 9 = 1 ∨ p ^ e % 9 = 8)) ∧
          ∀ F : Subgroup G, F ≤ E ⊔ L → CFSG.Assembly.IsElemAbelian 3 F → Nat.card F = 27 →
            Nat.card (F ⊓ L : Subgroup G) = 9 →
            (∀ y ∈ F ⊓ L, y ≠ 1 → ∀ z ∈ F ⊓ L, z ≠ 1 → ∃ l ∈ L, l * y * l⁻¹ = z) →
            F ≤ Subgroup.normalizer (E : Set G) →
              CFSG.ABGLocalTools.IsSylowOf 3 (E ⊔ F)
                (Subgroup.normalizer (Subgroup.zpowers c : Set G)) ∧
              (HypS F ∨ HypT F →
                omegaA F = orbitIn (Subgroup.normalizer (F : Set G)) (Subgroup.zpowers c) ∧
                  (omegaA F).ncard = 9)

@[expose] def IsF138N {G : Type} [Group G] (L E F : Subgroup G) : Prop :=
  IsF138 L E F ∧ Nat.card (F ⊓ L : Subgroup G) = 9

@[expose] def Item138ExistsN : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E : Subgroup G),
    Hyp138 A c L E → ∃ F : Subgroup G, IsF138N L E F

@[expose] def Item138MainN : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E : Subgroup G),
    Hyp138 A c L E → ∀ F : Subgroup G, IsF138N L E F →
      Sec8.IsZ3PGLThreePi (lBarA c L E) ∧
        CFSG.ABGLocalTools.IsSylowOf 3 (E ⊔ F)
          (Subgroup.normalizer (Subgroup.zpowers c : Set G))

@[expose] def Item138Mod9N : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E : Subgroup G),
    Hyp138 A c L E → Sec8.IsZ3PGLThreePi (lBarA c L E) →
    (∃ F : Subgroup G, IsF138N L E F ∧ CFSG.ABGLocalTools.IsSylowOf 3 (E ⊔ F)
      (Subgroup.normalizer (Subgroup.zpowers c : Set G))) →
      ∀ (p e : ℕ) [Fact p.Prime], 1 ≤ e →
        Sec4.IsoLThreePi (L ⧸ aschbacherSolvableCore 3 L) p e →
          ¬ (p ^ e % 9 = 1 ∨ p ^ e % 9 = 8)

@[expose] def Item138OmegaN : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E : Subgroup G),
    Hyp138 A c L E → ∀ F : Subgroup G, IsF138N L E F →
      Sec8.IsZ3PGLThreePi (lBarA c L E) →
      CFSG.ABGLocalTools.IsSylowOf 3 (E ⊔ F) (Subgroup.normalizer (Subgroup.zpowers c : Set G)) →
      HypS F ∨ HypT F →
        omegaA F = orbitIn (Subgroup.normalizer (F : Set G)) (Subgroup.zpowers c) ∧
          (omegaA F).ncard = 9

theorem rank3II_13_8N_of_steps (hEx : Item138ExistsN) (hMain : Item138MainN)
    (hMod9 : Item138Mod9N) (hΩ : Item138OmegaN) : Item138N := by
  intro G _ _ A c L h hL3 E hcE hE3 hE27 hEN hEC hST hC
  have hH : Hyp138 A c L E := ⟨h, hL3, hcE, hE3, hE27, hEN, hEC, hST, hC⟩
  obtain ⟨F₀, hF₀⟩ := hEx G A c L E hH
  obtain ⟨hPGL, hSyl₀⟩ := hMain G A c L E hH F₀ hF₀
  refine ⟨hPGL, hMod9 G A c L E hH hPGL ⟨F₀, hF₀, hSyl₀⟩, ?_⟩
  intro F hFEL hF3 hF27 hFL hFfus hFN
  have hF : IsF138N L E F := ⟨⟨hFEL, hF3, hF27, hFfus, hFN⟩, hFL⟩
  have hSyl := (hMain G A c L E hH F hF).2
  exact ⟨hSyl, hΩ G A c L E hH F hF hPGL hSyl⟩

end CFSG.RankThree.PartTwo.Sec13
