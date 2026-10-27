module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineNReduction
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNine

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup

variable {B : Type} [Group B] [Finite B]

structure MovWit914 (L D E H Xh : Subgroup B) (p : ℕ) : Prop where
  le : H ≤ L
  inf_centralizer : H ⊓ centralizer (L : Set B) = ⊥
  normalizes : E ≤ normalizer (H : Set B)
  irr : TwoPTwoIrred H (H ⊓ D) Xh p
  elem : IsElemAbelian p Xh
  nontriv : ∃ y ∈ H ⊓ D ⊓ normalizer (Xh : Set B), ∃ x ∈ Xh, y * x * y⁻¹ ≠ x
  three : p = 3 ∨ ∃ y ∈ closure {z | ∃ d ∈ D, ∃ x ∈ Xh, z = d * x * d⁻¹}, orderOf y = 3

@[expose] def MovStar914 (L D Es E : Subgroup B) : Prop :=
  ∃ H Xh : Subgroup B, MovWit914 L D E H Xh 3 ∧ Es ≤ normalizer (H : Set B) ∧
    ∀ e ∈ Es, ∀ x ∈ Xh, e * x * e⁻¹ * x⁻¹ ∈ pCoreOf 2 H

structure FixWit914 (D E K Xh : Subgroup B) (p : ℕ) : Prop where
  le : E ≤ K
  not_le : ¬ E ≤ pCoreOf 2 K
  irr : TwoPTwoIrred K (K ⊓ D) Xh p
  three : p = 3 ∨ ∃ y ∈ closure {z | ∃ d ∈ D, ∃ x ∈ Xh, z = d * x * d⁻¹}, orderOf y = 3

@[expose] def Fix914 (D E : Subgroup B) : Prop :=
  ∃ (K Xh : Subgroup B) (p : ℕ), FixWit914 D E K Xh p

@[expose] def PairProp914 (L : Subgroup B) (x : B) : Prop :=
  ∃ l ∈ L, IsPGroup 2 (closure {x, l * x * l⁻¹}) ∧ x * (l * x * l⁻¹) ≠ l * x * l⁻¹ * x

@[expose] def CloseFamily914 (D Es : Subgroup B) (Ks : Finset (Subgroup B)) : Prop :=
  (∀ K ∈ Ks, ∃ Y : Subgroup B, TwoPTwoIrred K (K ⊓ D) Y 3 ∧ Es ≤ pCoreOf 2 K ∧
      D ⊓ centralizer (Es : Set B) ≤ K) ∧
    (⨆ K ∈ Ks, K) ⊔ D = ⊤

structure CoordFacts914 (L D Es : Subgroup B) : Prop where
  three_dvd : 3 ∣ Nat.card L
  sq : ∃ d ∈ D ⊓ L, d ^ 2 ≠ 1
  mov : ∀ E : Subgroup B, E ≤ D → IsElemAbelian 2 E →
    ∃ (H Xh : Subgroup B) (p : ℕ), MovWit914 L D E H Xh p
  fix : ∀ E : Subgroup B, E ≤ D → IsElemAbelian 2 E → E ≠ ⊥ → Fix914 D E ∨ E = Es
  normal : ∀ F : Subgroup B, F ≤ D → D ≤ normalizer (F : Set B) → IsElemAbelian 2 F →
    F = ⊥ ∨ F = Es ∨ (Nat.card F = 2 ∧ ∀ x ∈ F, x ≠ 1 → PairProp914 L x)
  star : Es ≠ ⊥ → Es ≤ D ∧ D ≤ normalizer (Es : Set B) ∧ IsElemAbelian 2 Es ∧
    (∀ E : Subgroup B, E ≤ D ⊓ centralizer (Es : Set B) → IsElemAbelian 2 E →
      MovStar914 L D Es E) ∧
    ∃ Ks : Finset (Subgroup B), CloseFamily914 D Es Ks

@[expose] def IsCoordGroup914 (B : Type) [Group B] (L D : Subgroup B) : Prop :=
  IsSylowIn 2 D ⊤ ∧ L.Normal ∧
    ((L ≠ ⊥ ∧ ⁅L, L⁆ = L ∧
        (CFSG.Quasithin.F6.IsPGL2 7 B ∨ CFSG.Quasithin.F6.IsPGL2 9 B ∨
          CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.IsM10 B ∨
          CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.IsAutOf B
            (alternatingGroup (Fin 6)))) ∨
      (CFSG.IsQuasisimple ↥L ∧ Nat.card (center ↥L) = 3 ∧ centralizer (L : Set B) ≤ L ∧
        ∃ (A : Type) (_ : Group A) (ρ : B →* A), Function.Surjective ρ ∧
          ρ.ker = centralizer (L : Set B) ∧
          (CFSG.Quasithin.F6.IsPGL2 9 A ∨
            CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.IsAutOf A
              (alternatingGroup (Fin 6)) ∨
            CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.IsM10 A)))

@[expose] def TCCoord : Prop :=
  ∀ (B : Type) [Group B] [Finite B] (L D : Subgroup B), IsCoordGroup914 B L D →
    ∃ Es : Subgroup B, CoordFacts914 L D Es

@[expose] def TCCoord7 : Prop :=
  ∀ (B : Type) [Group B] [Finite B] (L D : Subgroup B), IsSylowIn 2 D ⊤ → L.Normal → L ≠ ⊥ →
    ⁅L, L⁆ = L → CFSG.Quasithin.F6.IsPGL2 7 B → ∃ Es : Subgroup B, CoordFacts914 L D Es

@[expose] def TCCoord9 : Prop :=
  ∀ (B : Type) [Group B] [Finite B] (L D : Subgroup B), IsSylowIn 2 D ⊤ → L.Normal → L ≠ ⊥ →
    ⁅L, L⁆ = L → CFSG.Quasithin.F6.IsPGL2 9 B → ∃ Es : Subgroup B, CoordFacts914 L D Es

@[expose] def TCCoordM10 : Prop :=
  ∀ (B : Type) [Group B] [Finite B] (L D : Subgroup B), IsSylowIn 2 D ⊤ → L.Normal → L ≠ ⊥ →
    ⁅L, L⁆ = L → CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.IsM10 B →
    ∃ Es : Subgroup B, CoordFacts914 L D Es

@[expose] def TCCoordAut : Prop :=
  ∀ (B : Type) [Group B] [Finite B] (L D : Subgroup B), IsSylowIn 2 D ⊤ → L.Normal → L ≠ ⊥ →
    ⁅L, L⁆ = L →
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.IsAutOf B (alternatingGroup (Fin 6)) →
    ∃ Es : Subgroup B, CoordFacts914 L D Es

@[expose] def TCCoord3 : Prop :=
  ∀ (B : Type) [Group B] [Finite B] (L D : Subgroup B), IsSylowIn 2 D ⊤ → L.Normal →
    CFSG.IsQuasisimple ↥L → Nat.card (center ↥L) = 3 → centralizer (L : Set B) ≤ L →
    (∃ (A : Type) (_ : Group A) (ρ : B →* A), Function.Surjective ρ ∧
      ρ.ker = centralizer (L : Set B) ∧
      (CFSG.Quasithin.F6.IsPGL2 9 A ∨
        CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.IsAutOf A
          (alternatingGroup (Fin 6)) ∨
        CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.IsM10 A)) →
    ∃ Es : Subgroup B, CoordFacts914 L D Es

theorem tcCoord_of (h7 : TCCoord7) (h9 : TCCoord9) (hM : TCCoordM10) (hA : TCCoordAut)
    (h3 : TCCoord3) : TCCoord := by
  intro B _ _ L D ⟨hD, hL, h⟩
  rcases h with ⟨hne, hperf, h7' | h9' | hM' | hA'⟩ | ⟨hq, hz, hc, hρ⟩
  · exact h7 B L D hD hL hne hperf h7'
  · exact h9 B L D hD hL hne hperf h9'
  · exact hM B L D hD hL hne hperf hM'
  · exact hA B L D hD hL hne hperf hA'
  · exact h3 B L D hD hL hq hz hc hρ

end CFSG.LocalAnalysis.WeakClosure81

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81

@[expose] def W3Lem914C (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (V T N L : Subgroup G), Hyp9 V T → T ≤ N → N ≤ normalizer (V : Set G) → N = T ⊔ L →
    L = CFSG.Quasithin.perfectCore (L ⊔ pCoreOf 2 N) →
    (∃ (Z : Type) (_ : Group Z) (ψ : ↥N →* Z), Function.Surjective ψ ∧
      (∀ x : ↥N, ψ x = 1 ↔ (x : G) ∈ pCoreOf 2 N) ∧
      CFSG.IsComponent ((L.subgroupOf N).map ψ)) →
    (∃ (A : Type) (_ : Group A) (φ : ↥(N ⊓ normalizer (L : Set G)) →* A),
      Function.Surjective φ ∧
      (∀ x : ↥(N ⊓ normalizer (L : Set G)),
        φ x = 1 ↔ (x : G) ∈ S17.centSection N L (oTwoThreeIn L)) ∧
      (CFSG.Quasithin.F6.IsPGL2 7 A ∨
        Inputs1719.IsAutOf A (alternatingGroup (Fin 6)) ∨ Inputs1719.IsM10 A ∨
        CFSG.Quasithin.F6.IsPGL2 9 A)) →
    Star914 V N →
    normalizer (E3.wClos V 1 T : Set G) ≤ normalizer (V : Set G) ∨
      N ≤ normalizer (E3.wClos V 0 T : Set G)

theorem w3Lem914_of_C (h : ∀ (G : Type) [Group G] [Finite G], W3Lem914C G)
    (G : Type) [Group G] [Finite G] : W3Lem914 G := by
  intro V T N L hyp hTN hNM hN hL hψ hφ hP
  exact h G V T N L hyp hTN hNM hN hL hψ hφ (starOfSylThree_holds G V N hP)

@[expose] def TCReduction : Prop :=
  TCCoord → ∀ (G : Type) [Group G] [Finite G], W3Lem914C G

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
