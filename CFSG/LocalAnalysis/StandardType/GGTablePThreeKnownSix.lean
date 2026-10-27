module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeKnownOn

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly

@[expose] def KnownOverSix (D : DatumPred) : Prop :=
  (∀ (X : Type) [Group X] [Finite X], commutator X = ⊤ →
    ∀ (A : Subgroup (MulAut X)) (δ : MulAut X) (J : Subgroup X), D X A δ J →
      ¬ LargeEvenMarking J (fun lab _ _ _ _ _ => GGLabelG2 lab)) ∧
  (∀ (X : Type) [Group X] [Finite X], commutator X = ⊤ →
    ∀ (A : Subgroup (MulAut X)) (δ : MulAut X) (J : Subgroup X), D X A δ J →
      LargeEvenMarking J (fun lab _ _ _ _ _ => GGLabelA2 lab) → Subgroup.center J = ⊥ →
        GGMarkingAll (K := X) fun lab _ _ _ _ _ => LargeEvenSplit 3 lab →
          (lab.tag = .E6 ∧ 3 ∣ 2 ^ lab.n - 1) ∨ (lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1) ∨
            (lab.tag = .A ∧ lab.rank = 8 ∧ 3 ∣ 2 ^ lab.n - 1) ∨
            (lab.tag = .twA ∧ lab.rank = 8 ∧ 3 ∣ 2 ^ lab.n + 1)) ∧
  (∀ (X : Type) [Group X] [Finite X], commutator X = ⊤ →
    ∀ (A : Subgroup (MulAut X)) (δ : MulAut X) (J : Subgroup X), D X A δ J →
      LargeEvenMarking J (fun lab _ _ _ _ _ => GGLabelA2 lab ∧ lab.tag = .twA) →
      Subgroup.center J ≠ ⊥ →
        GGMarkingAll (K := X) fun lab _ _ _ _ _ => LargeEvenSplit 3 lab →
          (lab.tag = .twA ∧ lab.rank = 3) ∨ (lab.tag = .twD ∧ (lab.rank = 3 ∨ lab.rank = 4)) ∨
            (lab.tag = .twA ∧ lab.rank = 4 ∧ 3 ∣ 2 ^ lab.n + 1 ∧ Nat.card A = 3 ^ 3) ∨
            (lab.tag = .twA ∧ lab.rank = 8 ∧ 3 ∣ 2 ^ lab.n + 1)) ∧
  (∀ (X : Type) [Group X] [Finite X], commutator X = ⊤ →
    ∀ (A : Subgroup (MulAut X)) (δ : MulAut X) (J : Subgroup X), D X A δ J →
      LargeEvenMarking J (fun lab _ _ _ _ _ => lab.tag = .triD4) →
        GGMarkingAll (K := X) fun lab _ _ _ _ _ => LargeEvenSplit 3 lab →
          (lab.tag = .E6 ∧ 3 ∣ 2 ^ lab.n - 1) ∨ (lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1)) ∧
  (∀ (X : Type) [Group X] [Finite X], commutator X = ⊤ →
    ∀ (A : Subgroup (MulAut X)) (δ : MulAut X) (J : Subgroup X), D X A δ J →
      LargeEvenMarking J (fun lab _ _ _ _ _ => lab.tag = .D ∧ lab.rank = 4 ∧ Odd lab.n) →
        GGMarkingAll (K := X) fun lab _ _ _ _ _ => LargeEvenSplit 3 lab →
          (lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1) ∨ (lab.tag = .twD ∧ lab.rank = 5) ∨
            (lab.tag = .D ∧ lab.rank = 6 ∧ lab.n = 1) ∨
            (lab.tag = .twD ∧ lab.rank = 7 ∧ lab.n = 1)) ∧
  (∀ (X : Type) [Group X] [Finite X], commutator X = ⊤ →
    ∀ (A : Subgroup (MulAut X)) (δ : MulAut X) (J : Subgroup X), D X A δ J →
      LargeEvenMarking J (fun lab _ _ _ _ _ => lab.tag = .A ∧ lab.rank = 1) →
        Nat.card A = 3 ^ 3 ∧
          GGMarkingAll (K := X) fun lab _ _ _ _ _ => LargeEvenSplit 3 lab →
            (lab.tag = .A ∧ lab.rank = 5 ∧ 3 ∣ 2 ^ lab.n - 1) ∨
              (lab.tag = .twA ∧ lab.rank = 5 ∧ 3 ∣ 2 ^ lab.n + 1))

@[expose] def KG7U6Over (D : DatumPred) : Prop :=
  (∀ (X : Type) [Group X] [Finite X], commutator X = ⊤ →
    ∀ (A : Subgroup (MulAut X)) (δ : MulAut X) (J : Subgroup X), D X A δ J →
      Nat.card A = 3 ^ 3 →
      LargeEvenMarking X (fun lab _ _ _ _ _ => lab.tag = .twA ∧ lab.rank = 5 ∧ 3 ∣ 2 ^ lab.n + 1) →
      LargeEvenMarking J (fun lab _ _ _ _ _ => lab.tag = .A ∧ lab.rank = 1) →
        ¬ ∃ U : Subgroup (MulAut X), U ≠ ⊥ ∧ IsPGroup 2 U ∧ ∀ a ∈ A, ∀ u ∈ U, a * u * a⁻¹ ∈ U)

@[expose] def KG7U5Over (D : DatumPred) : Prop :=
  (∀ (X : Type) [Group X] [Finite X], commutator X = ⊤ →
    ∀ (A : Subgroup (MulAut X)) (δ : MulAut X) (J : Subgroup X), D X A δ J →
      Nat.card A = 3 ^ 3 →
      LargeEvenMarking X (fun lab _ _ _ _ _ => lab.tag = .twA ∧ lab.rank = 4 ∧ 3 ∣ 2 ^ lab.n + 1) →
      LargeEvenMarking J (fun lab _ _ _ _ _ => GGLabelA2 lab ∧ lab.tag = .twA) →
      Subgroup.center J ≠ ⊥ →
        ¬ ∃ U : Subgroup (MulAut X), U ≠ ⊥ ∧ IsPGroup 2 U ∧ ∀ a ∈ A, ∀ u ∈ U, a * u * a⁻¹ ∈ U)

theorem knownOver_iff_six (D : DatumPred) :
    KnownOver D ↔ KnownOverSix D ∧ KG7U6Over D ∧ KG7U5Over D :=
  ⟨fun h => ⟨⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩, h.2.2.2.2.2.2.1,
      h.2.2.2.2.2.2.2⟩,
    fun h => ⟨h.1.1, h.1.2.1, h.1.2.2.1, h.1.2.2.2.1, h.1.2.2.2.2.1, h.1.2.2.2.2.2, h.2.1, h.2.2⟩⟩

theorem kg7U6Over_of_known {D : DatumPred}
    (hD : ∀ (X : Type) [Group X] (A : Subgroup (MulAut X)) (δ : MulAut X) (J : Subgroup X),
      D X A δ J → GGTablePThreeDatum A δ J)
    (h : GGTablePThreeU6NoTwoGroupKnown) : KG7U6Over D :=
  fun X _ _ hX A δ J hd => h X hX A δ J (hD X A δ J hd)

theorem kg7U5Over_of_known {D : DatumPred}
    (hD : ∀ (X : Type) [Group X] (A : Subgroup (MulAut X)) (δ : MulAut X) (J : Subgroup X),
      D X A δ J → GGTablePThreeDatum A δ J)
    (h : GGTablePThreeU5NoTwoGroupKnown) : KG7U5Over D :=
  fun X _ _ hX A δ J hd => h X hX A δ J (hD X A δ J hd)

theorem knownOver_datumOn_of_six {F : LargeEvenLieTag → Prop} (h6 : KnownOverSix (DatumOn F))
    (hU6 : GGTablePThreeU6NoTwoGroupKnown) (hU5 : GGTablePThreeU5NoTwoGroupKnown) :
    KnownOver (DatumOn F) :=
  (knownOver_iff_six _).mpr ⟨h6,
    kg7U6Over_of_known (fun _ _ _ _ _ hd => datumOn_to_datum hd) hU6,
    kg7U5Over_of_known (fun _ _ _ _ _ hd => datumOn_to_datum hd) hU5⟩

@[expose] def KnownSixOn (S : Fin 11 → Prop) : Prop :=
  ∀ i : Fin 11, S i → KnownOverSix (DatumOn (fam i))

theorem knownOn_of_six {S : Fin 11 → Prop} (h : KnownSixOn S)
    (hU6 : GGTablePThreeU6NoTwoGroupKnown) (hU5 : GGTablePThreeU5NoTwoGroupKnown) : KnownOn S :=
  fun i hi => knownOver_datumOn_of_six (h i hi) hU6 hU5

end CFSG.StandardType.TablePThreeKG

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGTablePThreeKnownRestSix : Prop :=
  TablePThreeKG.KnownSixOn fun i => i ≠ 0 ∧ i ≠ 10

theorem ggTablePThreeKnownRest_of_six (h : GGTablePThreeKnownRestSix)
    (hU6 : GGTablePThreeU6NoTwoGroupKnown) (hU5 : GGTablePThreeU5NoTwoGroupKnown) :
    GGTablePThreeKnownRest :=
  TablePThreeKG.knownOn_of_six h hU6 hU5

end CFSG.StandardType

end
