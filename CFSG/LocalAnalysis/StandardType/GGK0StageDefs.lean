module

public import CFSG.LocalAnalysis.StandardType.GGK0MarkedKacIface1587

public section

namespace CFSG.StandardType.GGK0MarkedKacIface1587

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley
open CFSG.LieType.AlgebraicGroups
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable (Omega : Type) [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]

structure K0LangMark (lab : LargeEvenLabel) (p : ℕ) (R : Type) [Group R] (I : Set (MulAut R))
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
  node_std : ∀ (i : Fin row.diagram.marks.length) (j : Fin tau.rank), i.val = j.val + 1 →
    nodeMap (Pi.single i 1) = Pi.single j 1

variable {Omega} {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
  {phi : MulAut R}

structure K0Positions (A : K0LangMark Omega lab p R I phi) where
  repr : Fin A.row.D.orbits.length → KernelComponent (rootCharHom A.a)
  orbitNodes : Fin A.row.D.orbits.length → List (List ℕ)
  orbitNodes_perm : List.Perm (List.ofFn orbitNodes) A.row.rawComponentOrbits
  orbit_descriptor : ∀ j, A.row.D.orbits[j] = A.row.orbitDescriptor (orbitNodes j)
  repr_roots : ∀ j, componentRoots (rootCharHom A.a) (repr j) =
    {v | IsRoot A.tau v ∧ v ∈ Submodule.span ℤ {w | ∃ i : Fin A.row.diagram.marks.length,
      i.val ∈ (orbitNodes j).headD [] ∧ w = A.nodeMap (Pi.single i 1)}}
  orbit_cover : ∀ c : KernelComponent (rootCharHom A.a), ∃ j,
    rationalRoots A.setup.ρ (rootCharHom A.a) c =
      rationalRoots A.setup.ρ (rootCharHom A.a) (repr j)
  orbit_distinct : ∀ j k, j ≠ k →
    Disjoint (rationalRoots A.setup.ρ (rootCharHom A.a) (repr j))
      (rationalRoots A.setup.ρ (rootCharHom A.a) (repr k))
  orbit_length : ∀ j,
    componentOrbitLength A.setup.ρ (componentRoots (rootCharHom A.a) (repr j)) =
      (orbitNodes j).length
  field_exp : ∀ j, A.row.D.orbits[j].lab.n = (orbitNodes j).length * lab.n

structure K0CentralTorus (A : K0LangMark Omega lab p R I phi) where
  saturated : Submodule ℤ (Fin A.tau.rank → ℤ)
  saturated_mem : ∀ v, v ∈ saturated ↔ ∃ m : ℕ, 0 < m ∧
    (m : ℤ) • v ∈ Submodule.span ℤ (kernelRoots (rootCharHom A.a))
  saturated_frob : ∀ v, v ∈ saturated ↔ A.frobLinear v ∈ saturated
  centralTorus : Subgroup (ModGL A.tau Omega)
  centralTorus_mem : ∀ g, g ∈ centralTorus ↔ ∃ b : Fin A.tau.rank → Omegaˣ,
    rootDiagUnit A.tau b = g ∧ ∀ v ∈ saturated, rootChar b v = 1
  torusStep : (Fin A.tau.rank → Omegaˣ) →* (Fin A.tau.rank → Omegaˣ)
  torusStep_diag : ∀ b, rootDiagUnit A.tau (torusStep b) =
    A.setup.D.step (rootDiagUnit A.tau b)
  torusStep_char : ∀ b v, rootChar (torusStep b) (A.frobLinear v) =
    (rootChar b v) ^ A.setup.D.q

@[expose] def K0LangMark.toRealization (A : K0LangMark Omega lab p R I phi)
    (P : K0Positions A) (T : K0CentralTorus A)
    (hqs : ∀ j, A.row.D.orbits[j].qs = true →
      CFSG.IsQuasisimple (rationalComponent A.setup.ρ A.setup.Γ (rootCharHom A.a) (P.repr j)))
    (hlabel : ∀ j, A.row.D.orbits[j].qs = true → LargeEvenInLambda2 A.row.D.orbits[j].lab ∧
      GGHasLabel A.row.D.orbits[j].lab
        ((coreFactor A.setup A.iota A.a (P.repr j)) ⧸
          Subgroup.center (coreFactor A.setup A.iota A.a (P.repr j))))
    (hsolv : ∀ j, A.row.D.orbits[j].qs = false →
      Group.IsSolvable (rationalSpan A.setup.ρ A.setup.Γ (rootCharHom A.a) (P.repr j)))
    (ha12 : ∀ j, A.row.D.orbits[j].lab = ⟨.A, 1, 1⟩ → A.row.D.orbits[j].qs = false →
      Nonempty ((fullFactor A.setup A.iota A.a (P.repr j)) ≃* Equiv.Perm (Fin 3)))
    (hmodel : ∀ g : A.setup.D.model, Commute (A.modelAction g) phi →
      ∃ sigma : Equiv.Perm (Fin A.row.D.orbits.length),
        ∀ j, (fullFactor A.setup A.iota A.a (P.repr j)).map (A.modelAction g).toMonoidHom =
          fullFactor A.setup A.iota A.a (P.repr (sigma j)))
    (hinv : ∀ j, A.row.D.orbits[j].lab = ⟨.A, 1, 1⟩ → A.row.D.orbits[j].qs = false →
      ∀ u : MulAut R, Commute u phi →
        (fullFactor A.setup A.iota A.a (P.repr j)).map u.toMonoidHom =
          fullFactor A.setup A.iota A.a (P.repr j))
    (hcentred : GGKacCentred lab p →
      adjointGroup A.tau Omega ⊓ Subgroup.centralizer {rootDiagUnit A.tau A.a} ≤
        Subgroup.closure (Set.range (fun b : Fin A.tau.rank → Omegaˣ =>
          rootDiagUnit A.tau b)) ⊔
          rootSpan A.tau Omega (kernelRoots (rootCharHom A.a))) :
    MarkedRationalKacRealization Omega lab p R I phi where
  row := A.row
  tau := A.tau
  tau_eq := A.tau_eq
  setup := A.setup
  q_eq := A.q_eq
  fr := A.fr
  fr_eq := A.fr_eq
  phi_split := A.phi_split
  phi_twisted := A.phi_twisted
  iota := A.iota
  iota_inj := A.iota_inj
  iota_range := A.iota_range
  modelAction := A.modelAction
  modelAction_inj := A.modelAction_inj
  modelAction_range := A.modelAction_range
  modelAction_compat := A.modelAction_compat
  a := A.a
  a_pow := A.a_pow
  a_torus := A.a_torus
  a_model := A.a_model
  a_ne := A.a_ne
  action_eq := A.action_eq
  zeta := A.zeta
  zeta_order := A.zeta_order
  nodeMap := A.nodeMap
  nodeMap_surj := A.nodeMap_surj
  nodeMap_ker := A.nodeMap_ker
  node_isRoot := A.node_isRoot
  node_eval := A.node_eval
  kernel_span_eq := A.kernel_span_eq
  epsilon := A.epsilon
  epsilon_eq := A.epsilon_eq
  frobLinear := A.frobLinear
  frob_roots := A.frob_roots
  frob_nodes := A.frob_nodes
  repr := P.repr
  orbitNodes := P.orbitNodes
  orbitNodes_perm := P.orbitNodes_perm
  orbit_descriptor := P.orbit_descriptor
  repr_roots := P.repr_roots
  orbit_cover := P.orbit_cover
  orbit_distinct := P.orbit_distinct
  orbit_length := P.orbit_length
  field_exp := P.field_exp
  qs := hqs
  label := hlabel
  solvable := hsolv
  a12_model := ha12
  model_equivariance := hmodel
  a12_invariant := hinv
  saturated := T.saturated
  saturated_mem := T.saturated_mem
  saturated_frob := T.saturated_frob
  centralTorus := T.centralTorus
  centralTorus_mem := T.centralTorus_mem
  torusStep := T.torusStep
  torusStep_diag := T.torusStep_diag
  torusStep_char := T.torusStep_char
  centred_centralizer_generated := hcentred

end CFSG.StandardType.GGK0MarkedKacIface1587

end
