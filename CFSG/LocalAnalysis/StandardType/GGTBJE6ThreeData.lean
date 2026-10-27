module

public import CFSG.LocalAnalysis.StandardType.GGTBTorDatum
public import CFSG.LocalAnalysis.StandardType.GGTBJE6Three

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TableBExc
  TableBExc.E6Three CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Solomon.Coordinator

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGE6ThreeFrameA {L' : Type} [Group L'] (A : Subgroup (MulAut L'))
    (κ : ↥A →* Multiplicative (Fin Tag.E6.rank → ZMod 3)) : Prop :=
  Function.Injective κ ∧
  (κ.range = ⊤ ∨ ∀ x, Multiplicative.ofAdd x ∈ κ.range ↔ x ∈ NoOffRest.hypE6) ∧
  (∀ γ : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 γ →
    ∃ (n : L') (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
      GGTorusWeylElt 3 A n ∧ GGIsReflection 3 (ggConjAut A hn) ∧
      ∀ a : ↥A, Multiplicative.toAdd (κ (ggConjAut A hn a)) =
        ExcSplitRootGen.excRefl (p := 3) γ (Multiplicative.toAdd (κ a))) ∧
  (∀ m : L', MulAut.conj m ∈ Subgroup.normalizer (A : Set (MulAut L')) →
    ∃ u : WeylGroup Tag.E6, ∀ a b : ↥A,
      (b : MulAut L') = MulAut.conj m * (a : MulAut L') * (MulAut.conj m)⁻¹ →
        Multiplicative.toAdd (κ b) = adAct Tag.E6 3 u (Multiplicative.toAdd (κ a)))

@[expose] def GGE6ThreeClassA {L' : Type} [Group L'] (A : Subgroup (MulAut L'))
    (κ : ↥A →* Multiplicative (Fin Tag.E6.rank → ZMod 3)) (y : ↥A) (J : Subgroup L') (P : Prop) :
    Prop :=
  ∃ (F : Type) (_ : Field F) (ζ : Fˣ) (hζ : ζ ^ 3 = 1), orderOf ζ = 3 ∧
    ∃ i : KernelComponent (rootCharHom (zetaVec ζ hζ (Multiplicative.toAdd (κ y)))),
      (∀ a : ↥A, (∀ γ ∈ componentRoots
          (rootCharHom (zetaVec ζ hζ (Multiplicative.toAdd (κ y)))) i,
          ∑ j, (γ j : ZMod 3) * Multiplicative.toAdd (κ a) j = 0) →
        ∀ j ∈ J, (a : MulAut L') j = j) ∧
      (∀ c ∈ componentRoots (rootCharHom (zetaVec ζ hζ (Multiplicative.toAdd (κ y)))) i,
        ∃ (n : L') (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))), n ∈ J ∧
          GGTorusWeylElt 3 A n ∧ ∀ a : ↥A, Multiplicative.toAdd (κ (ggConjAut A hn a)) =
            adAct Tag.E6 3 (rootReflection c) (Multiplicative.toAdd (κ a))) ∧
      ((∃ v : WeylGroup Tag.E6, componentRoots
          (rootCharHom (zetaVec ζ hζ (Multiplicative.toAdd (κ y)))) i =
          (fun α => v • α) '' parabolicRoots Tag.E6 {j | j ∉ ({0, 5} : Finset (Fin 6))}) → P)

@[expose] def GGE6ThreeCoordData {G : Type} [Group G] [Finite G]
    (Bs X J : Subgroup G) (g : G) (hgBs : g ∈ Bs) (P : Prop) : Prop :=
  ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod 3) V) (ι : Additive ↥Bs ≃+ V)
    (φ : Fin 6 → MulAut ↥Bs) (h : Fin 6 → V) (α : Fin 6 → Module.Dual (ZMod 3) V)
    (f : CoxeterMatrix.E₆.Group ≃* ↥(ggAutomizer X Bs))
    (κW : WeylGroup .E6 ≃* CoxeterMatrix.E₆.Group)
    (cd : ↥Bs →* Multiplicative (Fin Tag.E6.rank → ZMod 3))
    (F : Type) (_ : Field F) (ζ : Fˣ) (hζ : ζ ^ 3 = 1),
    orderOf ζ = 3 ∧
    (∀ i w, ggLin (p := 3) ι (φ i) w = w - α i w • h i) ∧
    (∀ i, GGIsReflection 3 (φ i)) ∧
    (∀ i j, α i (h j) = (Tag.cartan .E6 i j : ZMod 3)) ∧
    (∀ i, (f (CoxeterMatrix.E₆.simple i) : MulAut ↥Bs) = φ i) ∧
    ggAutomizer X Bs = Subgroup.closure (Set.range φ) ∧
    (∀ j, κW (simple .E6 j) = CoxeterMatrix.E₆.simple j) ∧
    (∀ (b : ↥Bs) j, α j (ι (Additive.ofMul b)) = Multiplicative.toAdd (cd b) j) ∧
    (cd.range = ⊤ ∨ ∀ x, Multiplicative.ofAdd x ∈ cd.range ↔ x ∈ NoOffRest.hypE6) ∧
    (∀ (u : WeylGroup .E6) (b : ↥Bs),
      cd ((f (κW u) : MulAut ↥Bs) b) =
        Multiplicative.ofAdd (adAct .E6 3 u (Multiplicative.toAdd (cd b)))) ∧
    (∀ (n : ↥(X ⊓ Subgroup.normalizer (Bs : Set G))) (u : WeylGroup .E6),
      (∀ b : ↥Bs, cd (ggTDρB X Bs n b) =
        Multiplicative.ofAdd (adAct .E6 3 u (Multiplicative.toAdd (cd b)))) →
      ggTDρB X Bs n = (f (κW u) : MulAut ↥Bs)) ∧
    (∀ b : ↥Bs, (b : G) ∈ Subgroup.centralizer (X : Set G) → cd b = 1) ∧
    cd ⟨g, hgBs⟩ ≠ 1 ∧
    ∃ i : KernelComponent (rootCharHom (zetaVec ζ hζ (Multiplicative.toAdd (cd ⟨g, hgBs⟩)))),
      (∀ b : ↥Bs, (∀ γ ∈ componentRoots
          (rootCharHom (zetaVec ζ hζ (Multiplicative.toAdd (cd ⟨g, hgBs⟩)))) i,
          ∑ j, (γ j : ZMod 3) * Multiplicative.toAdd (cd b) j = 0) →
        (b : G) ∈ Subgroup.centralizer (J : Set G)) ∧
      (∀ c ∈ componentRoots
          (rootCharHom (zetaVec ζ hζ (Multiplicative.toAdd (cd ⟨g, hgBs⟩)))) i,
        ∃ n : ↥(J ⊓ Subgroup.normalizer (Bs : Set G)), ∀ b : ↥Bs,
          cd (ggTDρB J Bs n b) =
            Multiplicative.ofAdd (adAct .E6 3 (rootReflection c) (Multiplicative.toAdd (cd b)))) ∧
      ((∃ v : WeylGroup .E6, componentRoots
          (rootCharHom (zetaVec ζ hζ (Multiplicative.toAdd (cd ⟨g, hgBs⟩)))) i =
          (fun α => v • α) '' parabolicRoots .E6 {j | j ∉ ({0, 5} : Finset (Fin 6))}) → P)

end CFSG.StandardType

end
