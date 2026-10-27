module

public import CFSG.LocalAnalysis.StandardType.GGK0ExcB3
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwReduction
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwTorus
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcVacuous
public import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterE
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
public import CFSG.LieType.Chevalley.C2E6SubsystemBruhat
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LieType.Simplicity.Finiteness
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBasic
public import CFSG.Quasithin.Background.A3Structure36BPrime
public import CFSG.RankThree.Lattice.SteinbergBIOrbitQuotFull
public import CFSG.RankThree.PartOne.KE.A1SL2
public import CFSG.RankThree.PartOne.KE.A1Torus
public import CFSG.RankThree.PartOne.KE.A2Family
public import CFSG.RankThree.PartOne.KE.A2Shape
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted
public import CFSG.RankThree.PartOne.KLR.Master
public import CFSG.RankThree.PartOne.KLR.SectorAssembly
public import CFSG.RankThree.PartOne.S8.Statements
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7

public section

namespace CFSG.StandardType.GGK0MarkedKacIface1587

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley
open CFSG.LieType.AlgebraicGroups
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

@[expose] def absTag : GGKacType → Tag
  | .E6 => .E6
  | .E7 => .E7
  | .E8 => .E8
  | .F4 => .F4

@[expose] def rawOrbitsOf (D : K0Diag) (s rho : List ℕ) : List (List (List ℕ)) :=
  let nNodes := D.marks.length
  let zero := (List.range nNodes).filter (fun i => decide (s.getD i 0 = 0))
  let comps := k0Comps D zero
  let img : List ℕ → List ℕ := fun c => k0SortNat (c.map (fun i => rho.getD i 0))
  k0CompOrbits img (nNodes + 1) comps []

@[expose]
def orbitDescriptorOf (D : K0Diag) (rho : List ℕ) (d n : ℕ) (orb : List (List ℕ)) : GGKacOrbit :=
  let k := orb.length
  let c := orb.headD []
  let ct := k0CompType D c
  let rk := k0pPow rho k
  let o := k0AutOrder c rk
  let tw := if d = 2 ∧ k % 2 = 1 ∧ k0Tau0Of ct.1 ct.2 then
              (if o = 1 then 2 else if o = 2 then 1 else o) else o
  k0LabelOf ct.1 ct.2 tw (k * n)

structure KacRow (lab : LargeEvenLabel) (p : ℕ) where
  T : GGKacType
  tw : Bool
  type_eq : ggKacTypeOfLabel lab = some (T, tw)
  d : ℕ
  d_eq : d = (if p ∣ 2 ^ lab.n - 1 then 1 else 2)
  s : List ℕ
  s_length : s.length = (k0DiagOf T).marks.length
  s_mem : s ∈ k0VecsAux (k0DiagOf T).marks p
  s_min : k0OrbMin (k0DiagOf T) s = s
  base : List ℕ
  base_eq : k0KacBase (k0DiagOf T) (k0Rho0 (k0DiagOf T) tw d) s = some base
  rho : List ℕ
  rho_length : rho.length = (k0DiagOf T).marks.length
  rho_mem : rho ∈ k0Reps (((k0DiagOf T).omega).filter (fun w => decide (k0pAct w s = s))) base
  nodePerm : Equiv.Perm (Fin (k0DiagOf T).marks.length)
  rho_apply : ∀ i, rho.getD i.val 0 = (nodePerm i).val
  D : GGKacDatum
  D_eq : D = k0Datum (k0DiagOf T) s rho d lab.n
      (((k0DiagOf T).omega.filter (fun w => decide (k0pAct w s = s))).length)
  valid : GGKacValid lab p D

namespace KacRow

variable {lab : LargeEvenLabel} {p : ℕ}

abbrev diagram (row : KacRow lab p) : K0Diag := k0DiagOf row.T

@[expose] def rawComponentOrbits (row : KacRow lab p) : List (List (List ℕ)) :=
  rawOrbitsOf (k0DiagOf row.T) row.s row.rho

@[expose] def orbitDescriptor (row : KacRow lab p) (orb : List (List ℕ)) : GGKacOrbit :=
  orbitDescriptorOf (k0DiagOf row.T) row.rho row.d lab.n orb

end KacRow

@[expose] noncomputable def fullFactor
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] {tau : Tag}
    (setup : LangSetup tau Omega 5) {R : Type} [Group R]
    (iota : R →* ModGL tau Omega) (a : Fin tau.rank → Omegaˣ)
    (c : KernelComponent (rootCharHom a)) : Subgroup R :=
  (rationalSpan setup.ρ setup.Γ (rootCharHom a) c).comap iota

@[expose] noncomputable def coreFactor
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] {tau : Tag}
    (setup : LangSetup tau Omega 5) {R : Type} [Group R]
    (iota : R →* ModGL tau Omega) (a : Fin tau.rank → Omegaˣ)
    (c : KernelComponent (rootCharHom a)) : Subgroup R :=
  (rationalComponent setup.ρ setup.Γ (rootCharHom a) c).comap iota

structure MarkedRationalKacRealization (Omega : Type) [Field Omega] [IsAlgClosed Omega]
    [CharP Omega 2]
    (lab : LargeEvenLabel) (p : ℕ) (R : Type) [Group R] (I : Set (MulAut R))
    (phi : MulAut R) where
  row : KacRow lab p
  tau : Tag
  tau_eq : absTag row.T = tau
  setup : LangSetup tau Omega 5
  q_eq : setup.D.q = 2 ^ lab.n
  fr : Omega →+* Omega
  fr_eq : ∀ x, fr x = x ^ (2 ^ lab.n)
  phi_split : row.tw = false → ∀ g : ModGL tau Omega,
    setup.D.Φ g = Units.map (entrywiseHom fr) g
  phi_twisted : row.tw = true → ∃ ht : TwistTag.E6.tag = tau,
    ∀ g : ModGL tau Omega, setup.D.Φ g =
      diagramAt tau Omega TwistTag.E6 ht * Units.map (entrywiseHom fr) g *
        (diagramAt tau Omega TwistTag.E6 ht)⁻¹
  iota : R →* ModGL tau Omega
  iota_inj : Function.Injective iota
  iota_range : iota.range = setup.Γ
  modelAction : (setup.D.model : Type) →* MulAut R
  modelAction_inj : Function.Injective modelAction
  modelAction_range : Set.range (fun x => modelAction x) = I
  modelAction_compat : ∀ g r, iota (modelAction g r) =
    (g : ModGL tau Omega) * iota r * (g : ModGL tau Omega)⁻¹
  a : Fin tau.rank → Omegaˣ
  a_pow : ∀ i, a i ^ p = 1
  a_torus : rootDiagUnit tau a ∈ setup.D.torus
  a_model : rootDiagUnit tau a ∈ setup.D.model
  a_ne : rootDiagUnit tau a ≠ 1
  action_eq : modelAction ⟨rootDiagUnit tau a, a_model⟩ = phi
  zeta : Omegaˣ
  zeta_order : orderOf zeta = p
  nodeMap : (Fin row.diagram.marks.length → ℤ) →ₗ[ℤ] (Fin tau.rank → ℤ)
  nodeMap_surj : Function.Surjective nodeMap
  nodeMap_ker : nodeMap.ker = Submodule.span ℤ
    ({fun i : Fin row.diagram.marks.length => (row.diagram.marks.getD i.val 0 : ℤ)} :
      Set (Fin row.diagram.marks.length → ℤ))
  node_isRoot : ∀ i : Fin row.diagram.marks.length, IsRoot tau (nodeMap (Pi.single i 1))
  node_eval : ∀ i : Fin row.diagram.marks.length,
    rootChar a (nodeMap (Pi.single i 1)) = zeta ^ (row.s.getD i.val 0)
  kernel_span_eq : Submodule.span ℤ (kernelRoots (rootCharHom a)) =
    Submodule.span ℤ {v | ∃ i : Fin row.diagram.marks.length,
      row.s.getD i.val 0 = 0 ∧ v = nodeMap (Pi.single i 1)}
  epsilon : ℤ
  epsilon_eq : epsilon = (if row.d = 1 then 1 else -1)
  frobLinear : (Fin tau.rank → ℤ) ≃ₗ[ℤ] (Fin tau.rank → ℤ)
  frob_roots : ∀ v, IsRoot tau v → frobLinear v = setup.ρ v
  frob_nodes : ∀ i : Fin row.diagram.marks.length,
    frobLinear (nodeMap (Pi.single i 1)) = epsilon • nodeMap (Pi.single (row.nodePerm i) 1)
  repr : Fin row.D.orbits.length → KernelComponent (rootCharHom a)
  orbitNodes : Fin row.D.orbits.length → List (List ℕ)
  orbitNodes_perm : List.Perm (List.ofFn orbitNodes) row.rawComponentOrbits
  orbit_descriptor : ∀ j, row.D.orbits[j] = row.orbitDescriptor (orbitNodes j)
  repr_roots : ∀ j, componentRoots (rootCharHom a) (repr j) =
    {v | IsRoot tau v ∧ v ∈ Submodule.span ℤ {w | ∃ i : Fin row.diagram.marks.length,
      i.val ∈ (orbitNodes j).headD [] ∧ w = nodeMap (Pi.single i 1)}}
  orbit_cover : ∀ c : KernelComponent (rootCharHom a), ∃ j,
    rationalRoots setup.ρ (rootCharHom a) c =
      rationalRoots setup.ρ (rootCharHom a) (repr j)
  orbit_distinct : ∀ j k, j ≠ k →
    Disjoint (rationalRoots setup.ρ (rootCharHom a) (repr j))
      (rationalRoots setup.ρ (rootCharHom a) (repr k))
  orbit_length : ∀ j,
    componentOrbitLength setup.ρ (componentRoots (rootCharHom a) (repr j)) =
      (orbitNodes j).length
  field_exp : ∀ j, row.D.orbits[j].lab.n = (orbitNodes j).length * lab.n
  qs : ∀ j, row.D.orbits[j].qs = true →
    CFSG.IsQuasisimple (rationalComponent setup.ρ setup.Γ (rootCharHom a) (repr j))
  label : ∀ j, row.D.orbits[j].qs = true → LargeEvenInLambda2 row.D.orbits[j].lab ∧
    GGHasLabel row.D.orbits[j].lab
      ((coreFactor setup iota a (repr j)) ⧸ Subgroup.center (coreFactor setup iota a (repr j)))
  solvable : ∀ j, row.D.orbits[j].qs = false →
    Group.IsSolvable (rationalSpan setup.ρ setup.Γ (rootCharHom a) (repr j))
  a12_model : ∀ j, row.D.orbits[j].lab = ⟨.A, 1, 1⟩ → row.D.orbits[j].qs = false →
    Nonempty ((fullFactor setup iota a (repr j)) ≃* Equiv.Perm (Fin 3))
  model_equivariance : ∀ g : setup.D.model, Commute (modelAction g) phi →
    ∃ sigma : Equiv.Perm (Fin row.D.orbits.length),
      ∀ j, (fullFactor setup iota a (repr j)).map (modelAction g).toMonoidHom =
        fullFactor setup iota a (repr (sigma j))
  a12_invariant : ∀ j, row.D.orbits[j].lab = ⟨.A, 1, 1⟩ → row.D.orbits[j].qs = false →
    ∀ u : MulAut R, Commute u phi →
      (fullFactor setup iota a (repr j)).map u.toMonoidHom = fullFactor setup iota a (repr j)
  saturated : Submodule ℤ (Fin tau.rank → ℤ)
  saturated_mem : ∀ v, v ∈ saturated ↔ ∃ m : ℕ, 0 < m ∧
    (m : ℤ) • v ∈ Submodule.span ℤ (kernelRoots (rootCharHom a))
  saturated_frob : ∀ v, v ∈ saturated ↔ frobLinear v ∈ saturated
  centralTorus : Subgroup (ModGL tau Omega)
  centralTorus_mem : ∀ g, g ∈ centralTorus ↔ ∃ b : Fin tau.rank → Omegaˣ,
    rootDiagUnit tau b = g ∧ ∀ v ∈ saturated, rootChar b v = 1
  torusStep : (Fin tau.rank → Omegaˣ) →* (Fin tau.rank → Omegaˣ)
  torusStep_diag : ∀ b, rootDiagUnit tau (torusStep b) =
    setup.D.step (rootDiagUnit tau b)
  torusStep_char : ∀ b v, rootChar (torusStep b) (frobLinear v) =
    (rootChar b v) ^ setup.D.q
  centred_centralizer_generated : GGKacCentred lab p →
    adjointGroup tau Omega ⊓ Subgroup.centralizer {rootDiagUnit tau a} ≤
      Subgroup.closure (Set.range (fun b : Fin tau.rank → Omegaˣ =>
        rootDiagUnit tau b)) ⊔
        rootSpan tau Omega (kernelRoots (rootCharHom a))

@[expose] def RationalProducerOn (Omega : Type) [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    (tag : LargeEvenLieTag) : Prop :=
  ∀ p : ℕ, ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → GGKacExcPair lab p →
    lab.tag = tag →
    LargeEvenLabelAll lab (fun R _ I _ => ∀ phi : MulAut R, phi ∈ I → orderOf phi = p →
      Nonempty (MarkedRationalKacRealization Omega lab p R I phi))

@[expose] def CoverProducerOn (Omega : Type) [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    (tag : LargeEvenLieTag) : Prop :=
  ∀ p : ℕ, ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → GGKacExcPair lab p →
    lab.tag = tag →
    LargeEvenLabelAll lab (fun R _ I _ =>
      ∀ (L : Type) [Group L] [Finite L] (psi : L →* R), Function.Surjective psi →
        psi.ker ≤ Subgroup.center L → commutator L = ⊤ →
        ∀ e : MulAut L, orderOf e = p →
          (∃ phi ∈ I, ∀ l : L, phi (psi l) = psi (e l)) →
          ∃ phi ∈ I, (∀ l : L, phi (psi l) = psi (e l)) ∧
            Nonempty (MarkedRationalKacRealization Omega lab p R I phi))

end CFSG.StandardType.GGK0MarkedKacIface1587

end
