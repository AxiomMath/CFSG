module

public import CFSG.LocalAnalysis.StandardType.GGE0Frame
public import CFSG.LocalAnalysis.StandardType.GGTwE6LangRetype
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin

public noncomputable section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

@[expose] def WeylGood {τ : Tag} {L : Type} [Field L] {ι : Type}
    (a : ι → Fin τ.rank → Lˣ) : Prop :=
  ∀ w ∈ familyStabilizer a,
    w ∈ Subgroup.closure {s | ∃ α ∈ familyKernel a, s = rootReflection α}

@[expose] def PairWeylGood {L : Type} [Field L]
    (a : Fin 2 → Fin Tag.E6.rank → Lˣ) : Prop :=
  ∀ w ∈ familyStabilizer a, ∀ i,
    w ∈ Subgroup.closure {s | ∃ α ∈ familyKernel (fun _ : Unit => a i),
      s = rootReflection α}

@[expose] def RigidToralPlane {L : Type} [Field L] (E : Subgroup (ModGL .E6 L)) : Prop :=
  ∃ (a : Fin 2 → Fin Tag.E6.rank → Lˣ) (g : ModGL .E6 L),
    g ∈ adjointGroup .E6 L ∧
    (∀ i j, a i j ^ 3 = 1) ∧
    E.map (MulAut.conj g).toMonoidHom =
      Subgroup.closure (Set.range fun i => rootDiagUnit .E6 (a i)) ∧
    Nat.card E = 9 ∧ PairWeylGood a

@[expose] def RigidPair {L : Type} [Field L] (β : ModGL .E6 L)
    (E : Subgroup (ModGL .E6 L)) : Prop :=
  β ≠ 1 ∧ β ^ 3 = 1 ∧ E ≤ Subgroup.centralizer {β} ∧ RigidToralPlane E

structure ShapeRealization (C : Type) [Group C] (I : Subgroup (MulAut C))
    (L : Type) [Field L] [IsAlgClosed L]
    where
  setup : LangSetup .E6 L 5
  groupEquiv : C ≃* setup.Γ
  action : I →* ModGL .E6 L
  action_injective : Function.Injective action
  action_mem : ∀ φ, action φ ∈ setup.D.model
  inner_le : (MulAut.conj : C →* MulAut C).range ≤ I
  inner_compatible : ∀ c : C,
    action ⟨MulAut.conj c, inner_le ⟨c, rfl⟩⟩ = (groupEquiv c : ModGL .E6 L)
  compatible : ∀ (φ : I) (x : C),
    (groupEquiv (φ.1 x) : ModGL .E6 L) =
      action φ * (groupEquiv x : ModGL .E6 L) * (action φ)⁻¹

@[expose] def realizedSubgroup {C : Type} [Group C] {I : Subgroup (MulAut C)}
    {L : Type} [Field L] [IsAlgClosed L]
    (R : ShapeRealization C I L) (E : Subgroup (MulAut C)) : Subgroup (ModGL .E6 L) :=
  (E.comap I.subtype).map R.action

@[expose] def planeGroup {L : Type} [Field L] (a : Fin 2 → Fin Tag.E6.rank → Lˣ) :
    Subgroup (ModGL .E6 L) :=
  Subgroup.closure (Set.range fun i => rootDiagUnit .E6 (a i))

@[expose] def a2roots (α β : Fin Tag.E6.rank → ℤ) : Set (Fin Tag.E6.rank → ℤ) :=
  {α, -α, β, -β, α + β, -(α + β)}

@[expose] def contextImage {G : Type} [Group G] (G0 H : Subgroup G) :
    Subgroup (MulAut G0) :=
  (H.comap (Subgroup.normalizer (G0 : Set G)).subtype).map
    (Subgroup.normalizerMonoidHom G0)

structure ToralKernelContext {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    (S : LangSetup .E6 Ω 5) (B J : Subgroup (ModGL .E6 Ω))
    (a : Fin 2 → Fin Tag.E6.rank → Ωˣ) : Prop where
  B_model : B ≤ S.D.model
  B_torus : B ≤ torusGroup .E6 Ω
  B_exp : ∀ b ∈ B, b ^ 3 = 1
  B_card : 3 ^ 4 ≤ Nat.card B
  pair_exp : ∀ i j, a i j ^ 3 = 1
  D_le : planeGroup a ≤ B
  D_card : Nat.card (planeGroup a) = 9
  J_component : IsComponentOf J (S.Γ ⊓ Subgroup.centralizer (planeGroup a : Set _))
  D_eq : B ⊓ Subgroup.centralizer (J : Set _) = planeGroup a
  sign : (∀ α, S.ρ α = α) ∨ (∀ α, S.ρ α = -α)

structure KernelContext {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    (S : LangSetup .E6 Ω 5) (B J : Subgroup (ModGL .E6 Ω))
    (a : Fin 2 → Fin Tag.E6.rank → Ωˣ) : Prop extends ToralKernelContext S B J a where
  local_rank : 3 ^ 5 ≤ Nat.card B ∨ ∃ α, IsRoot .E6 α ∧
    ∀ t : Fin Tag.E6.rank → Ωˣ, rootDiagUnit .E6 t ∈ B → rootChar t α = 1

@[expose] def Shape (t : StatedLieTag) (f : ℕ) : Prop :=
  (t = .E6 ∧ 3 ∣ 2 ^ f - 1) ∨ (t = .twistedE6 ∧ 3 ∣ 2 ^ f + 1)

end CFSG.StandardType
