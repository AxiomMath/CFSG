module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcCoreDefs

public section

namespace CFSG.StandardType.GGQ2Frame.ExcPlacement

open CFSG CFSG.Assembly CFSG.StandardType CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.StandardType.QTwoCav
open CFSG.Open (IsElemAbelian)

noncomputable section


@[expose] def E6SplitLangTwo {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    (S : LangSetup .E6 L p) : Prop :=
  S.D.q = 2 ∧ S.IsAlgebraic ∧ ∀ γ, IsRoot .E6 γ → S.ρ γ = -permLattice TwistTag.E6.perm γ

@[expose] def e6RelCorootPair (β v : Fin Tag.E6.rank → ℤ) : ℤ :=
  if permLattice (τ := .E6) TwistTag.E6.perm β = β then corootPair β v
  else corootPair β v + corootPair (permLattice TwistTag.E6.perm β) v

@[expose] def e6SplitRootTable : List (List ℤ) :=
  [[0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 0, 0], [0, 1, 0, 1, 1, 0], [0, -1, 0, -1, 0, 0],
    [0, 1, 0, 1, 1, 1], [0, 0, 0, 0, 1, 1], [0, 0, 0, 1, 1, 1], [0, 1, 1, 1, 1, 1],
    [0, 0, 0, 0, 1, 0], [0, 0, 0, 1, 1, 0], [0, 1, 1, 1, 1, 0], [0, 1, 1, 2, 1, 0],
    [0, -1, 0, 0, 0, 0], [0, 1, 1, 2, 1, 1], [0, 0, 1, 1, 1, 1], [1, 1, 1, 2, 1, 1],
    [1, 1, 1, 1, 1, 1], [1, 0, 1, 1, 1, 1], [1, 1, 1, 2, 2, 1], [0, 1, 1, 2, 2, 1],
    [1, 2, 2, 3, 2, 1], [1, 1, 2, 2, 2, 1], [1, 1, 2, 3, 2, 1], [0, 0, 1, 1, 1, 0]]

@[expose] def e6SplitRoot (i : ExcRaw.Root 1) : Fin Tag.E6.rank → ℤ :=
  fun k => (e6SplitRootTable.getD i.val []).getD k.val 0

@[expose] def e6SplitCodeRoots (c : Finset (ExcRaw.Root 1)) : Set (Fin Tag.E6.rank → ℤ) :=
  {δ | ∃ i ∈ c, δ = e6SplitRoot i ∨ δ = -e6SplitRoot i ∨
    δ = permLattice TwistTag.E6.perm (e6SplitRoot i) ∨
    δ = -permLattice TwistTag.E6.perm (e6SplitRoot i)}

@[expose] def e6SplitComponent {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    (S : LangSetup .E6 L p) (c : Finset (ExcRaw.Root 1)) : Subgroup (ModGL .E6 L) :=
  ⁅rootSpan .E6 L (e6SplitCodeRoots c) ⊓ S.Γ, rootSpan .E6 L (e6SplitCodeRoots c) ⊓ S.Γ⁆

theorem e6SplitComponent_le_Γ {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    (S : LangSetup .E6 L p) (c : Finset (ExcRaw.Root 1)) : e6SplitComponent S c ≤ S.Γ :=
  (Subgroup.commutator_le_self _).trans inf_le_right

structure E6SplitDatum {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    (S : LangSetup .E6 L p) (T₀ : Subgroup (ModGL .E6 L)) : Type where
  ζ : Lˣ
  coord : Additive ↥T₀ ≃+ ExcRaw.V 1
  le_fullThreeTorus : T₀ ≤ fullThreeTorus S
  ζ_pow_three : ζ ^ 3 = 1
  ζ_ne_one : ζ ≠ 1
  rootChar_eq : ∀ (t : ↥T₀) (b : Fin Tag.E6.rank → Lˣ), (t : ModGL .E6 L) = rootDiagUnit .E6 b →
    ∀ i, rootChar b (e6SplitRoot i) = ζ ^ (ExcRaw.root 1 i (coord (Additive.ofMul t))).val
  coroot_mem : ∀ i,
    rootDiagUnit .E6 (fun j => ζ ^ e6RelCorootPair (e6SplitRoot i) (Pi.single j 1)) ∈ T₀
  coord_coroot : ∀ i, coord (Additive.ofMul ⟨_, coroot_mem i⟩) = ExcRaw.coroot 1 i

@[expose] def E6SplitCoreDatum : Prop :=
  ∀ {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup .E6 L p), E6SplitLangTwo S →
    Nonempty (E6SplitDatum S (fullThreeTorus S))

@[expose] def E6SplitCoreOccurs : Prop :=
  ∀ {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup .E6 L p), E6SplitLangTwo S →
    ∀ {T₀ : Subgroup (ModGL .E6 L)} (d : E6SplitDatum S T₀) (A : Subgroup (ModGL .E6 L)),
      A ≤ T₀ → ∀ X : Subgroup (ModGL .E6 L),
        IsComponentOf X (S.Γ ⊓ Subgroup.centralizer (A : Set (ModGL .E6 L))) ↔
          ∃ c : Finset (ExcRaw.Root 1), ExcRaw.admissible 1 c ∧
            ExcRaw.occurs 1 (ggLinImage (p := 3) d.coord A) c ∧ X = e6SplitComponent S c

@[expose] def E6SplitCoreMarked : Prop :=
  ∀ {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup .E6 L p), E6SplitLangTwo S →
    ∀ c : Finset (ExcRaw.Root 1), ExcRaw.admissible 1 c →
      LargeEvenMarking ↥(e6SplitComponent S c) (fun lab _ _ _ _ _ => lab = ExcRaw.label 1 c)

@[expose] def E6SplitCoreCent : Prop :=
  ∀ {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup .E6 L p), E6SplitLangTwo S →
    ∀ {T₀ : Subgroup (ModGL .E6 L)} (d : E6SplitDatum S T₀) (c : Finset (ExcRaw.Root 1)),
      ExcRaw.admissible 1 c →
        ggLinImage (p := 3) d.coord
          (Subgroup.centralizer (e6SplitComponent S c : Set (ModGL .E6 L))) = ExcRaw.cent 1 c

@[expose] def E6SplitCoreInside : Prop :=
  ∀ {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup .E6 L p), E6SplitLangTwo S →
    ∀ {T₀ : Subgroup (ModGL .E6 L)} (d : E6SplitDatum S T₀) (c : Finset (ExcRaw.Root 1)),
      ExcRaw.admissible 1 c →
        ggLinImage (p := 3) d.coord (e6SplitComponent S c) = ExcRaw.inside 1 c

@[expose] def E6SplitCoreNormalizer : Prop :=
  ∀ {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup .E6 L p), E6SplitLangTwo S →
    ∀ {T₀ : Subgroup (ModGL .E6 L)} (d : E6SplitDatum S T₀) (c : Finset (ExcRaw.Root 1)),
      ExcRaw.admissible 1 c →
        (ggAutomizer (e6SplitComponent S c) T₀).map (ggLin (p := 3) d.coord) =
          ExcRaw.normalizerGroup 1 c

@[expose] def E6SplitCoreAmbient : Prop :=
  ∀ {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup .E6 L p), E6SplitLangTwo S →
    ∀ {T₀ : Subgroup (ModGL .E6 L)} (d : E6SplitDatum S T₀),
      (ggAutomizer S.Γ T₀).map (ggLin (p := 3) d.coord) = ExcRaw.ambientNormalizer 1

@[expose] def E6SplitLangModelFrame : Prop :=
  ∀ {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup .E6 L p), E6SplitLangTwo S →
    Nonempty (ModelFrame S.Γ (fullThreeTorus S) (excRaw 1))

@[expose] def E6SplitLangSetup : Prop :=
  ∀ {K : Type} [Field K] [Finite K], Nat.card K = 2 →
    ∀ {E : Subgroup (adjointGroup .E6 K)}, IsElemAbelian 3 E → 3 ^ 4 ≤ Nat.card E →
      ∃ (S : LangSetup .E6 (AlgebraicClosure K) 5)
        (ι : adjointGroup .E6 K →* ModGL .E6 (AlgebraicClosure K)),
        E6SplitLangTwo S ∧ Function.Injective ι ∧ ι.range = S.Γ ∧ fullThreeTorus S = E.map ι

theorem nonempty_modelFrame_of_e6SplitCore (hO : E6SplitCoreOccurs) (hM : E6SplitCoreMarked)
    (hC : E6SplitCoreCent) (hI : E6SplitCoreInside) (hN : E6SplitCoreNormalizer)
    (hA : E6SplitCoreAmbient) {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    (S : LangSetup .E6 L p) (hS : E6SplitLangTwo S) {T₀ : Subgroup (ModGL .E6 L)}
    (d : E6SplitDatum S T₀) :
    Nonempty (ModelFrame S.Γ T₀ (excRaw 1)) :=
  ⟨{ coord := d.coord
     component := e6SplitComponent S
     component_le := fun c _ => e6SplitComponent_le_Γ S c
     marked := hM S hS
     occurs_iff := hO S hS d
     cent_eq := hC S hS d
     inside_eq := hI S hS d
     normalizer_eq := hN S hS d
     ambientNormalizer_eq := hA S hS d }⟩

theorem e6SplitLangModelFrame_of_core (hD : E6SplitCoreDatum) (hO : E6SplitCoreOccurs)
    (hM : E6SplitCoreMarked) (hC : E6SplitCoreCent) (hI : E6SplitCoreInside)
    (hN : E6SplitCoreNormalizer) (hA : E6SplitCoreAmbient) : E6SplitLangModelFrame := by
  intro L _ _ p S hS
  obtain ⟨d⟩ := hD S hS
  exact nonempty_modelFrame_of_e6SplitCore hO hM hC hI hN hA S hS d

theorem excUntwModelFrame_E6_of_lang (hS : E6SplitLangSetup) (h : E6SplitLangModelFrame) :
    ExcUntwModelFrame 1 .E6 := by
  intro K _ _ hK E hE hcard _
  obtain ⟨S, ι, hS2, hιinj, hιrange, hfull⟩ := hS hK hE (by rw [hcard]; decide)
  obtain ⟨mf⟩ := h S hS2
  have hΓtop : S.Γ = (⊤ : Subgroup (adjointGroup .E6 K)).map ι := by
    rw [← hιrange, MonoidHom.range_eq_map]
  rw [hΓtop, hfull] at mf
  exact nonempty_modelFrame_of_map hιinj mf

end

end CFSG.StandardType.GGQ2Frame.ExcPlacement

end
