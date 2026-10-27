module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcLangFrame

public section

namespace CFSG.StandardType.GGQ2Frame.ExcPlacement

open CFSG CFSG.Assembly CFSG.StandardType CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.StandardType.QTwoCav

noncomputable section


@[expose] def NegLangTwo {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    (S : LangSetup τ L p) : Prop :=
  S.D.q = 2 ∧ S.IsAlgebraic ∧ ∀ γ, IsRoot τ γ → S.ρ γ = -γ

@[expose] def codeRoots {τ : Tag} {m : Fin 6} (γ : ExcRaw.Root m → Fin τ.rank → ℤ)
    (c : Finset (ExcRaw.Root m)) : Set (Fin τ.rank → ℤ) :=
  {δ | ∃ i ∈ c, δ = γ i ∨ δ = -γ i}

@[expose] def codeComponent {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    (S : LangSetup τ L p) {m : Fin 6} (γ : ExcRaw.Root m → Fin τ.rank → ℤ)
    (c : Finset (ExcRaw.Root m)) : Subgroup (ModGL τ L) :=
  ⁅rootSpan τ L (codeRoots γ c) ⊓ S.Γ, rootSpan τ L (codeRoots γ c) ⊓ S.Γ⁆

theorem codeComponent_le_Γ {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    (S : LangSetup τ L p) {m : Fin 6} (γ : ExcRaw.Root m → Fin τ.rank → ℤ)
    (c : Finset (ExcRaw.Root m)) : codeComponent S γ c ≤ S.Γ :=
  (Subgroup.commutator_le_self _).trans inf_le_right

structure ExcCoordDatum {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    (S : LangSetup τ L p) (T₀ : Subgroup (ModGL τ L)) (m : Fin 6) : Type where
  γ : ExcRaw.Root m → Fin τ.rank → ℤ
  ζ : Lˣ
  coord : Additive ↥T₀ ≃+ ExcRaw.V m
  le_fullThreeTorus : T₀ ≤ fullThreeTorus S
  ζ_pow_three : ζ ^ 3 = 1
  ζ_ne_one : ζ ≠ 1
  isRoot : ∀ i, IsRoot τ (γ i)
  exists_eq : ∀ δ, IsRoot τ δ → ∃ i, δ = γ i ∨ δ = -γ i
  eq_of_eq : ∀ i j, (γ i = γ j ∨ γ i = -γ j) → i = j
  pairing_eq : ∀ i j, ExcRaw.pairing m i j = corootPair (γ j) (γ i)
  rootChar_eq : ∀ (t : ↥T₀) (b : Fin τ.rank → Lˣ), (t : ModGL τ L) = rootDiagUnit τ b →
    ∀ i, rootChar b (γ i) = ζ ^ (ExcRaw.root m i (coord (Additive.ofMul t))).val
  coroot_mem : ∀ i, rootDiagUnit τ (fun j => ζ ^ corootPair (γ i) (Pi.single j 1)) ∈ T₀
  coord_coroot : ∀ i, coord (Additive.ofMul ⟨_, coroot_mem i⟩) = ExcRaw.coroot m i

@[expose] def ExcCoreDatum (m : Fin 6) (τ : Tag) : Prop :=
  ∀ {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p), NegLangTwo S →
    Nonempty (ExcCoordDatum S (fullThreeTorus S) m)

@[expose] def ExcCoreOccurs (m : Fin 6) (τ : Tag) : Prop :=
  ∀ {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p), NegLangTwo S →
    ∀ {T₀ : Subgroup (ModGL τ L)} (d : ExcCoordDatum S T₀ m) (A : Subgroup (ModGL τ L)), A ≤ T₀ →
      ∀ X : Subgroup (ModGL τ L),
        IsComponentOf X (S.Γ ⊓ Subgroup.centralizer (A : Set (ModGL τ L))) ↔
          ∃ c : Finset (ExcRaw.Root m), ExcRaw.admissible m c ∧
            ExcRaw.occurs m (ggLinImage (p := 3) d.coord A) c ∧ X = codeComponent S d.γ c

@[expose] def ExcCoreMarked (m : Fin 6) (τ : Tag) : Prop :=
  ∀ {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p), NegLangTwo S →
    ∀ {T₀ : Subgroup (ModGL τ L)} (d : ExcCoordDatum S T₀ m) (c : Finset (ExcRaw.Root m)),
      ExcRaw.admissible m c →
        LargeEvenMarking ↥(codeComponent S d.γ c) (fun lab _ _ _ _ _ => lab = ExcRaw.label m c)

@[expose] def ExcCoreCent (m : Fin 6) (τ : Tag) : Prop :=
  ∀ {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p), NegLangTwo S →
    ∀ {T₀ : Subgroup (ModGL τ L)} (d : ExcCoordDatum S T₀ m) (c : Finset (ExcRaw.Root m)),
      ExcRaw.admissible m c →
        ggLinImage (p := 3) d.coord
          (Subgroup.centralizer (codeComponent S d.γ c : Set (ModGL τ L))) = ExcRaw.cent m c

@[expose] def ExcCoreInside (m : Fin 6) (τ : Tag) : Prop :=
  ∀ {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p), NegLangTwo S →
    ∀ {T₀ : Subgroup (ModGL τ L)} (d : ExcCoordDatum S T₀ m) (c : Finset (ExcRaw.Root m)),
      ExcRaw.admissible m c →
        ggLinImage (p := 3) d.coord (codeComponent S d.γ c) = ExcRaw.inside m c

@[expose] def ExcCoreNormalizer (m : Fin 6) (τ : Tag) : Prop :=
  ∀ {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p), NegLangTwo S →
    ∀ {T₀ : Subgroup (ModGL τ L)} (d : ExcCoordDatum S T₀ m) (c : Finset (ExcRaw.Root m)),
      ExcRaw.admissible m c →
        (ggAutomizer (codeComponent S d.γ c) T₀).map (ggLin (p := 3) d.coord) =
          ExcRaw.normalizerGroup m c

@[expose] def ExcCoreAmbient (m : Fin 6) (τ : Tag) : Prop :=
  ∀ {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p), NegLangTwo S →
    ∀ {T₀ : Subgroup (ModGL τ L)} (d : ExcCoordDatum S T₀ m),
      (ggAutomizer S.Γ T₀).map (ggLin (p := 3) d.coord) = ExcRaw.ambientNormalizer m

theorem nonempty_modelFrame_of_core {m : Fin 6} {τ : Tag} (hO : ExcCoreOccurs m τ)
    (hM : ExcCoreMarked m τ) (hC : ExcCoreCent m τ) (hI : ExcCoreInside m τ)
    (hN : ExcCoreNormalizer m τ) (hA : ExcCoreAmbient m τ)
    {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p) (hS : NegLangTwo S)
    {T₀ : Subgroup (ModGL τ L)} (d : ExcCoordDatum S T₀ m) :
    Nonempty (ModelFrame S.Γ T₀ (excRaw m)) :=
  ⟨{ coord := d.coord
     component := codeComponent S d.γ
     component_le := fun c _ => codeComponent_le_Γ S d.γ c
     marked := hM S hS d
     occurs_iff := hO S hS d
     cent_eq := hC S hS d
     inside_eq := hI S hS d
     normalizer_eq := hN S hS d
     ambientNormalizer_eq := hA S hS d }⟩

theorem excLangModelFrame_of_core {m : Fin 6} {τ : Tag} (hD : ExcCoreDatum m τ)
    (hO : ExcCoreOccurs m τ) (hM : ExcCoreMarked m τ) (hC : ExcCoreCent m τ)
    (hI : ExcCoreInside m τ) (hN : ExcCoreNormalizer m τ) (hA : ExcCoreAmbient m τ) :
    ExcLangModelFrame m τ := by
  intro L _ _ p S hq hAlg hρ
  obtain ⟨d⟩ := hD S ⟨hq, hAlg, hρ⟩
  exact nonempty_modelFrame_of_core hO hM hC hI hN hA S ⟨hq, hAlg, hρ⟩ d

end

end CFSG.StandardType.GGQ2Frame.ExcPlacement

end
