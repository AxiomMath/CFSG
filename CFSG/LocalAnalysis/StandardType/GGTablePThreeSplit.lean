module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeDefs

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly

abbrev DatumPred : Type 1 :=
  (X : Type) → [Group X] → Subgroup (MulAut X) → MulAut X → Subgroup X → Prop

@[expose] def KnownOver (D : DatumPred) : Prop :=
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
              (lab.tag = .twA ∧ lab.rank = 5 ∧ 3 ∣ 2 ^ lab.n + 1)) ∧
  (∀ (X : Type) [Group X] [Finite X], commutator X = ⊤ →
    ∀ (A : Subgroup (MulAut X)) (δ : MulAut X) (J : Subgroup X), D X A δ J →
      Nat.card A = 3 ^ 3 →
      LargeEvenMarking X (fun lab _ _ _ _ _ => lab.tag = .twA ∧ lab.rank = 5 ∧ 3 ∣ 2 ^ lab.n + 1) →
      LargeEvenMarking J (fun lab _ _ _ _ _ => lab.tag = .A ∧ lab.rank = 1) →
        ¬ ∃ U : Subgroup (MulAut X), U ≠ ⊥ ∧ IsPGroup 2 U ∧ ∀ a ∈ A, ∀ u ∈ U, a * u * a⁻¹ ∈ U) ∧
  (∀ (X : Type) [Group X] [Finite X], commutator X = ⊤ →
    ∀ (A : Subgroup (MulAut X)) (δ : MulAut X) (J : Subgroup X), D X A δ J →
      Nat.card A = 3 ^ 3 →
      LargeEvenMarking X (fun lab _ _ _ _ _ => lab.tag = .twA ∧ lab.rank = 4 ∧ 3 ∣ 2 ^ lab.n + 1) →
      LargeEvenMarking J (fun lab _ _ _ _ _ => GGLabelA2 lab ∧ lab.tag = .twA) →
      Subgroup.center J ≠ ⊥ →
        ¬ ∃ U : Subgroup (MulAut X), U ≠ ⊥ ∧ IsPGroup 2 U ∧ ∀ a ∈ A, ∀ u ∈ U, a * u * a⁻¹ ∈ U)

theorem known_iff :
    GGTablePThreeKnown ↔ KnownOver fun X _ A δ J => GGTablePThreeDatum A δ J :=
  Iff.rfl

@[expose] def fam : Fin 11 → LargeEvenLieTag → Prop
  | 0 => fun t => t = .A
  | 1 => fun t => t = .twA
  | 2 => fun t => t = .B ∨ t = .C ∨ t = .B2der
  | 3 => fun t => t = .D
  | 4 => fun t => t = .twD
  | 5 => fun t => t = .E6
  | 6 => fun t => t = .twE6
  | 7 => fun t => t = .F4
  | 8 => fun t => t = .E7
  | 9 => fun t => t = .E8
  | 10 => fun t => t = .G2 ∨ t = .G2der ∨ t = .triD4 ∨ t = .twB2 ∨ t = .twF4 ∨ t = .twF4der

@[expose] def DatumOn (F : LargeEvenLieTag → Prop) : DatumPred := fun X [inst : Group X] A δ J =>
  GGKLocal A δ J ∧
    (∀ Q : Subgroup X, IsComponentOf Q (ggAutFixedSubgroup δ) → Q = J) ∧
    3 ^ 3 ≤ Nat.card A ∧
    LargeEvenMarking X
      (fun lab _ _ I _ θ => F lab.tag ∧ (LargeEvenSplit 3 lab ∧ GGInducedInn A θ I))

theorem datum_cover {X : Type} [Group X] {A : Subgroup (MulAut X)} {δ : MulAut X}
    {J : Subgroup X} (hd : GGTablePThreeDatum A δ J) : ∃ i : Fin 11, DatumOn (fam i) X A δ J := by
  obtain ⟨h1, h2, h3, hX, lab, hlab, hraw⟩ := hd
  have key : ∀ (F : LargeEvenLieTag → Prop), F lab.tag → DatumOn F X A δ J := fun F hF =>
    ⟨h1, h2, h3, hX, lab, hlab, largeEvenRawDatum_mono
      (fun R _ I F' ⟨hs, hna, θ, hs3, hin⟩ => ⟨hs, hna, θ, hF, hs3, hin⟩) hraw⟩
  obtain ⟨tag, rank, n⟩ := lab
  cases tag
  · exact ⟨0, key _ rfl⟩
  · exact ⟨1, key _ rfl⟩
  · exact ⟨2, key _ (Or.inl rfl)⟩
  · exact ⟨2, key _ (Or.inr (Or.inl rfl))⟩
  · exact ⟨3, key _ rfl⟩
  · exact ⟨4, key _ rfl⟩
  · exact ⟨5, key _ rfl⟩
  · exact ⟨8, key _ rfl⟩
  · exact ⟨9, key _ rfl⟩
  · exact ⟨7, key _ rfl⟩
  · exact ⟨6, key _ rfl⟩
  · exact ⟨10, key _ (Or.inr (Or.inr (Or.inl rfl)))⟩
  · exact ⟨10, key _ (Or.inl rfl)⟩
  · exact ⟨10, key _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))⟩
  · exact ⟨10, key _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))⟩
  · exact ⟨2, key _ (Or.inr (Or.inr rfl))⟩
  · exact ⟨10, key _ (Or.inr (Or.inl rfl))⟩
  · exact ⟨10, key _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))⟩

theorem knownOver_of_cover {Dall : DatumPred} {ι : Type} {D : ι → DatumPred}
    (hcover : ∀ (X : Type) [Group X] (A : Subgroup (MulAut X)) (δ : MulAut X) (J : Subgroup X),
      Dall X A δ J → ∃ i, D i X A δ J)
    (h : ∀ i, KnownOver (D i)) : KnownOver Dall := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro X _ _ hX A δ J hd
    obtain ⟨i, hi⟩ := hcover X A δ J hd
    exact (h i).1 X hX A δ J hi
  · intro X _ _ hX A δ J hd
    obtain ⟨i, hi⟩ := hcover X A δ J hd
    exact (h i).2.1 X hX A δ J hi
  · intro X _ _ hX A δ J hd
    obtain ⟨i, hi⟩ := hcover X A δ J hd
    exact (h i).2.2.1 X hX A δ J hi
  · intro X _ _ hX A δ J hd
    obtain ⟨i, hi⟩ := hcover X A δ J hd
    exact (h i).2.2.2.1 X hX A δ J hi
  · intro X _ _ hX A δ J hd
    obtain ⟨i, hi⟩ := hcover X A δ J hd
    exact (h i).2.2.2.2.1 X hX A δ J hi
  · intro X _ _ hX A δ J hd
    obtain ⟨i, hi⟩ := hcover X A δ J hd
    exact (h i).2.2.2.2.2.1 X hX A δ J hi
  · intro X _ _ hX A δ J hd
    obtain ⟨i, hi⟩ := hcover X A δ J hd
    exact (h i).2.2.2.2.2.2.1 X hX A δ J hi
  · intro X _ _ hX A δ J hd
    obtain ⟨i, hi⟩ := hcover X A δ J hd
    exact (h i).2.2.2.2.2.2.2 X hX A δ J hi

theorem ggTablePThreeKnown_of_families (h : ∀ i : Fin 11, KnownOver (DatumOn (fam i))) :
    GGTablePThreeKnown :=
  known_iff.mpr (knownOver_of_cover (fun _ _ _ _ _ hd => datum_cover hd) h)

theorem datumOn_to_datum {F : LargeEvenLieTag → Prop} {X : Type} [Group X]
    {A : Subgroup (MulAut X)} {δ : MulAut X} {J : Subgroup X} (h : DatumOn F X A δ J) :
    GGTablePThreeDatum A δ J :=
  ⟨h.1, h.2.1, h.2.2.1, largeEvenMarking_mono (fun _ _ _ _ _ _ h' => h'.2) h.2.2.2⟩

theorem KnownOver.mono {D D' : DatumPred}
    (hDD : ∀ (X : Type) [Group X] (A : Subgroup (MulAut X)) (δ : MulAut X) (J : Subgroup X),
      D' X A δ J → D X A δ J) (h : KnownOver D) : KnownOver D' := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun X _ _ hX A δ J hd => h.1 X hX A δ J (hDD X A δ J hd)
  · exact fun X _ _ hX A δ J hd => h.2.1 X hX A δ J (hDD X A δ J hd)
  · exact fun X _ _ hX A δ J hd => h.2.2.1 X hX A δ J (hDD X A δ J hd)
  · exact fun X _ _ hX A δ J hd => h.2.2.2.1 X hX A δ J (hDD X A δ J hd)
  · exact fun X _ _ hX A δ J hd => h.2.2.2.2.1 X hX A δ J (hDD X A δ J hd)
  · exact fun X _ _ hX A δ J hd => h.2.2.2.2.2.1 X hX A δ J (hDD X A δ J hd)
  · exact fun X _ _ hX A δ J hd => h.2.2.2.2.2.2.1 X hX A δ J (hDD X A δ J hd)
  · exact fun X _ _ hX A δ J hd => h.2.2.2.2.2.2.2 X hX A δ J (hDD X A δ J hd)

theorem known_iff_families :
    GGTablePThreeKnown ↔ ∀ i : Fin 11, KnownOver (DatumOn (fam i)) :=
  ⟨fun h i => KnownOver.mono (fun _ _ _ _ _ hd => datumOn_to_datum hd) (known_iff.mp h),
    ggTablePThreeKnown_of_families⟩

@[expose] def LeafSmallVac : Prop :=
  ∀ (X : Type) [Group X] [Finite X], commutator X = ⊤ →
    ∀ (A : Subgroup (MulAut X)) (δ : MulAut X) (J : Subgroup X), ¬ DatumOn (fam 10) X A δ J

theorem knownOn_small (h : LeafSmallVac) : KnownOver (DatumOn (fam 10)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro X _ _ hX A δ J hd <;>
    exact absurd hd (h X hX A δ J)

@[expose] abbrev LeafLin : Prop := KnownOver (DatumOn (fam 0))

end CFSG.StandardType.TablePThreeKG

end
