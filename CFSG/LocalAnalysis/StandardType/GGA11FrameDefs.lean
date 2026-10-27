module

public import CFSG.LocalAnalysis.StandardType.GGA11Defs
public import CFSG.LocalAnalysis.StandardType.GGA8NbrKFrameDefs
public import CFSG.LocalAnalysis.StandardType.GGAssemblyTwoHypSix
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance
public import CFSG.LocalAnalysis.StandardType.GGA8NbrCoordDefs

public section

open CFSG CFSG.Assembly CFSG.StandardType CFSG.StandardType.A8Coord Matrix

namespace CFSG.StandardType.A11

abbrev GLV : Type := GGSL9V ≃ₗ[ZMod 2] GGSL9V

noncomputable abbrev tC (c : Fin 3 → ZMod 7) : GLV := ggSL9TorusCoord (Multiplicative.ofAdd c)

@[expose] def fBasis (a : ZMod 7) : Certificates.A8Nbr476.M4 :=
  !![0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1; a, 0, 0, 0]

@[expose] def fBasisInv (a : ZMod 7) : Certificates.A8Nbr476.M4 :=
  !![0, 0, 0, a⁻¹; 1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0]

@[expose] def fPerm (a : ZMod 7) (σ : Equiv.Perm (Fin 4)) : Certificates.A8Nbr476.M4 :=
  fBasisInv a * a8PermMat σ * fBasis a

@[expose] def A11TorusModelInput : Prop :=
  ∃ Θ : SL 9 ≃* GLV, ∀ i : Fin 3, Θ (T9 i) = tC (Pi.single i 1)

@[expose] def A11GlueExtInput : Prop :=
  ∀ {G : Type} [Group G] {Bs L K J : Subgroup G}, GGNoTransvection 7 Bs → J ≤ K →
    ∀ (xb : ↥Bs) (y : G) (hy : y ∈ Bs), (∀ ψ ∈ ggAutomizer J Bs, ψ xb = xb) →
      ∀ (ρ : ↥K ≃* GLV) (ιK ιL : Additive ↥Bs ≃+ (Fin 4 → ZMod 7)),
        GGA8KFrame Bs K y hy ρ ιK →
        (∀ φ : MulAut ↥Bs, φ ∈ ggAutomizer K Bs ↔
          ∃ (π : Equiv.Perm (Fin 3)) (k : Fin 3 → ZMod 3), ∀ b : ↥Bs,
            ιK (Additive.ofMul (φ b)) = Matrix.vecMul (ιK (Additive.ofMul b)) (a8MonK π k)) →
        (∀ i : Fin 3, ιK (Additive.ofMul xb) i.succ ≠ 0) →
        ιL (Additive.ofMul xb) = (fun _ => 1) →
        (∀ σ : Equiv.Perm (Fin 4), ∃ ψ ∈ ggAutomizer L Bs, ∀ b : ↥Bs,
          ιL (Additive.ofMul (ψ b)) = Matrix.vecMul (ιL (Additive.ofMul b)) (a8PermMat σ)) →
        (∀ σ : Equiv.Perm (Fin 4), σ 0 = 0 → ∃ ψ ∈ ggAutomizer J Bs, ∀ b : ↥Bs,
          ιL (Additive.ofMul (ψ b)) = Matrix.vecMul (ιL (Additive.ofMul b)) (a8PermMat σ)) →
        ∃ (ρ' : ↥K ≃* GLV) (ι : Additive ↥Bs ≃+ (Fin 4 → ZMod 7)) (a : ZMod 7), a ≠ 0 ∧
          GGA8KFrame Bs K y hy ρ' ι ∧ ι (Additive.ofMul xb) = ![a, 1, 1, 1] ∧
          (∀ σ : Equiv.Perm (Fin 4), ∃ ψ ∈ ggAutomizer L Bs, ∀ b : ↥Bs,
            ι (Additive.ofMul (ψ b)) = Matrix.vecMul (ι (Additive.ofMul b)) (fPerm a σ)) ∧
          (∀ σ : Equiv.Perm (Fin 4), σ 3 = 3 → ∃ ψ ∈ ggAutomizer J Bs, ∀ b : ↥Bs,
            ι (Additive.ofMul (ψ b)) = Matrix.vecMul (ι (Additive.ofMul b)) (fPerm a σ))

@[expose] def A11CoordInput :
    Prop :=
  GGInnerDiagMpInput → GGLBalanceInput →
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGSecFiveRestHyp 7 B Bs x L D J → GGSecFiveA11Config 7 B Bs x L D J →
      ∃ (y : G) (K : Subgroup G) (hy : y ∈ Bs) (hx : x ∈ Bs) (ρ : ↥K ≃* GLV)
        (ι : Additive ↥Bs ≃+ (Fin 4 → ZMod 7)) (a : ZMod 7),
        GGNbr 7 B x D J y K ∧ J ≤ K ∧ 7 ∣ Nat.card J ∧ a ≠ 0 ∧ GGA8KFrame Bs K y hy ρ ι ∧
          ι (Additive.ofMul ⟨x, hx⟩) = ![a, 1, 1, 1] ∧
          (∀ σ : Equiv.Perm (Fin 4), ∃ ψ ∈ ggAutomizer L Bs, ∀ b : ↥Bs,
            ι (Additive.ofMul (ψ b)) = Matrix.vecMul (ι (Additive.ofMul b)) (fPerm a σ)) ∧
          (∀ σ : Equiv.Perm (Fin 4), σ 3 = 3 → ∃ ψ ∈ ggAutomizer J Bs, ∀ b : ↥Bs,
            ι (Additive.ofMul (ψ b)) = Matrix.vecMul (ι (Additive.ofMul b)) (fPerm a σ))

@[expose] def A11FrameCore {G : Type} [Group G] [Finite G] (B Bs : Subgroup G) (x : G)
    (L D J : Subgroup G) (y : G) (K : Subgroup G) (φ₃ : SL 9 →* G) (f n : Fin 4 → G) : Prop :=
  A11GlueHyp φ₃ f n ∧ φ₃.range = K ∧ GGNbr 7 B x D J y K ∧ Subgroup.closure (Set.range f) = Bs ∧
    x = f 0 * f 1 * f 2 * f 3 ∧ y ∈ Subgroup.zpowers (f 3) ∧ D = Subgroup.closure {x, f 3} ∧
    (∀ l, n l ∈ L) ∧ J ≤ K ∧ J ≤ J9.map φ₃

@[expose] def A11FrameExtra {G : Type} [Group G] (Bs J : Subgroup G) (f : Fin 4 → G) : Prop :=
  7 ∣ Nat.card J ∧ ∀ σ : Equiv.Perm (Fin 4), σ 3 = 3 →
    ∃ g ∈ J, g ∈ Subgroup.normalizer (Bs : Set G) ∧ ∀ i, g * f i * g⁻¹ = f (σ i)

@[expose] def A11LGenInput :
    Prop :=
  GGInnerDiagMpInput → GGLBalanceInput →
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGSecFiveRestHyp 7 B Bs x L D J → GGSecFiveA11Config 7 B Bs x L D J →
      ∀ (y : G) (K : Subgroup G) (f n : Fin 4 → G), GGNbr 7 B x D J y K →
        Subgroup.closure (Set.range f) = Bs → (∀ i j, f i * f j = f j * f i) →
        (∀ i, orderOf (f i) = 7) → Nat.card (Subgroup.closure (Set.range f)) = 7 ^ 4 →
        x = f 0 * f 1 * f 2 * f 3 → y ∈ Subgroup.zpowers (f 3) → D = Subgroup.closure {x, f 3} →
        (∀ l, n l ∈ L) → (∀ l i, n l * f i * (n l)⁻¹ = f (Equiv.swap l 3 i)) →
          L ≤ Subgroup.closure
            ((J : Set G) ∪ (J.map (MulAut.conj (n 2)).toMonoidHom : Set G))

@[expose] def A11FrameAssembleInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGSecFiveRestHyp 7 B Bs x L D J → GGSecFiveA11Config 7 B Bs x L D J →
    ∀ (y : G) (K : Subgroup G) (hy : y ∈ Bs) (hx : x ∈ Bs) (ρ : ↥K ≃* GLV)
      (ι : Additive ↥Bs ≃+ (Fin 4 → ZMod 7)) (a : ZMod 7) (Θ : SL 9 ≃* GLV),
      GGNbr 7 B x D J y K → J ≤ K → 7 ∣ Nat.card J → a ≠ 0 → GGA8KFrame Bs K y hy ρ ι →
      ι (Additive.ofMul ⟨x, hx⟩) = ![a, 1, 1, 1] →
      (∀ σ : Equiv.Perm (Fin 4), ∃ ψ ∈ ggAutomizer L Bs, ∀ b : ↥Bs,
        ι (Additive.ofMul (ψ b)) = Matrix.vecMul (ι (Additive.ofMul b)) (fPerm a σ)) →
      (∀ σ : Equiv.Perm (Fin 4), σ 3 = 3 → ∃ ψ ∈ ggAutomizer J Bs, ∀ b : ↥Bs,
        ι (Additive.ofMul (ψ b)) = Matrix.vecMul (ι (Additive.ofMul b)) (fPerm a σ)) →
      (∀ i : Fin 3, Θ (T9 i) = tC (Pi.single i 1)) →
        ∃ (φ₃ : SL 9 →* G) (f n : Fin 4 → G),
          A11FrameCore B Bs x L D J y K φ₃ f n ∧ A11FrameExtra Bs J f

@[expose] def A11FrameInput' :
    Prop :=
  GGInnerDiagMpInput → GGLBalanceInput →
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGSecFiveRestHyp 7 B Bs x L D J → GGSecFiveA11Config 7 B Bs x L D J →
    ∃ (y : G) (K : Subgroup G) (φ₃ : SL 9 →* G) (f n : Fin 4 → G),
      A11FrameCore B Bs x L D J y K φ₃ f n ∧ A11FrameExtra Bs J f ∧
        L ≤ Subgroup.closure ((J : Set G) ∪ (J.map (MulAut.conj (n 2)).toMonoidHom : Set G))

theorem a11FrameInput'_of_pieces
    (hA2 : A11CoordInput) (hB : A11TorusModelInput)
    (hD : A11LGenInput) (hE : A11FrameAssembleInput) : A11FrameInput' := by
  intro hMp hLB G _ _ B Bs x L D J hR hA
  obtain ⟨y, K, hy, hx, ρ, ι, a, hnb, hJK, h7, ha, hF, hxι, hL, hJ⟩ := hA2 hMp hLB G B Bs x L D J hR hA
  obtain ⟨Θ, hΘ⟩ := hB
  obtain ⟨φ₃, f, n, hcore, hext⟩ := hE G B Bs x L D J hR hA y K hy hx ρ ι a Θ hnb hJK h7 ha hF hxι hL hJ hΘ
  obtain ⟨hGlue, hrange, hnb', hBs, hx', hy', hD', hnL, hJK', hJ9⟩ := hcore
  have hf1 : ∀ i j, f i * f j = f j * f i := hGlue.2.2.1
  have hf2 : ∀ i, orderOf (f i) = 7 := hGlue.2.2.2.1
  have hf3 : Nat.card (Subgroup.closure (Set.range f)) = 7 ^ 4 := hGlue.2.2.2.2.1
  have hn3 : ∀ l i, n l * f i * (n l)⁻¹ = f (Equiv.swap l 3 i) := hGlue.2.2.2.2.2.2.1
  exact ⟨y, K, φ₃, f, n, ⟨hGlue, hrange, hnb', hBs, hx', hy', hD', hnL, hJK', hJ9⟩, hext,
    hD hMp hLB G B Bs x L D J hR hA y K f n hnb hBs hf1 hf2 hf3 hx' hy' hD' hnL hn3⟩

end CFSG.StandardType.A11

end
