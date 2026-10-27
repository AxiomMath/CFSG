module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.OrbitSpanPerm
public import CFSG.LocalAnalysis.StandardType.GGK0StageDefs
public import CFSG.LocalAnalysis.StandardType.GGKacA12Rows
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.NormalForm
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.Quasi
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyBruhat
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LieType.Chevalley.EvenOddCentralizerRadicalPairing
public import CFSG.LieType.Chevalley.OrdinaryRootHyperplaneGeneration
public import CFSG.LieType.Chevalley.ParabolicRadicalNormalizer
public import CFSG.LieType.Chevalley.ParabolicRadicalsOpposite
public import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
public import CFSG.RankThree.PartOne.KE.A1Action
public import CFSG.RankThree.PartOne.KE.A1Levi
public import CFSG.RankThree.PartOne.KE.D4LayerAlgebraic
public import CFSG.RankThree.PartOne.KE.E8D4Family
public import CFSG.RankThree.PartOne.KE.ThreeA1Group
public import Certificates.Certificate1953
public import Certificates.Certificate1954

public section

namespace CFSG.StandardType.GGK0MarkedKacIface1587

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley
open CFSG.LieType.AlgebraicGroups
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem fullFactor_map_modelAction_of
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] {tau : Tag} {R : Type} [Group R]
    {phi : MulAut R} {setup : LangSetup tau Omega 5} {iota : R →* ModGL tau Omega}
    (iota_range : iota.range = setup.Γ) {modelAction : (setup.D.model : Type) →* MulAut R}
    (modelAction_inj : Function.Injective modelAction)
    (modelAction_compat : ∀ g r, iota (modelAction g r) =
      (g : ModGL tau Omega) * iota r * (g : ModGL tau Omega)⁻¹)
    {a : Fin tau.rank → Omegaˣ} (a_torus : rootDiagUnit tau a ∈ setup.D.torus)
    (a_model : rootDiagUnit tau a ∈ setup.D.model)
    (action_eq : modelAction ⟨rootDiagUnit tau a, a_model⟩ = phi)
    {n : ℕ} {repr : Fin n → KernelComponent (rootCharHom a)}
    (orbit_cover : ∀ c : KernelComponent (rootCharHom a), ∃ j,
      rationalRoots setup.ρ (rootCharHom a) c = rationalRoots setup.ρ (rootCharHom a) (repr j))
    (orbit_distinct : ∀ j k, j ≠ k →
      Disjoint (rationalRoots setup.ρ (rootCharHom a) (repr j))
        (rationalRoots setup.ρ (rootCharHom a) (repr k)))
    (g : setup.D.model) (hg : Commute (modelAction g) phi) :
    ∃ sigma : Equiv.Perm (Fin n), ∀ j,
      (fullFactor setup iota a (repr j)).map (modelAction g).toMonoidHom =
        fullFactor setup iota a (repr (sigma j)) := by
  have hgd : g * ⟨rootDiagUnit tau a, a_model⟩ = ⟨rootDiagUnit tau a, a_model⟩ * g := by
    apply modelAction_inj
    rw [map_mul, map_mul, action_eq]
    exact hg.eq
  have hya : (g : ModGL tau Omega) * rootDiagUnit tau a * (g : ModGL tau Omega)⁻¹ =
      rootDiagUnit tau a := by
    have h2 : (g : ModGL tau Omega) * rootDiagUnit tau a = rootDiagUnit tau a * g :=
      congrArg Subtype.val hgd
    rw [h2, mul_assoc, mul_inv_cancel, mul_one]
  have hex : ∀ j, ∃ j', (rootSpan tau Omega (rationalRoots setup.ρ (rootCharHom a)
      (repr j))).map (MulAut.conj (g : ModGL tau Omega)).toMonoidHom =
      rootSpan tau Omega (rationalRoots setup.ρ (rootCharHom a) (repr j')) := by
    intro j
    obtain ⟨i', hi'⟩ := exists_map_conj_rootSpan_rationalRoots setup g.2 hya (repr j)
    obtain ⟨j', hj'⟩ := orbit_cover i'
    exact ⟨j', by rw [hi', hj']⟩
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro j₁ j₂ h12
    have hmap : (rootSpan tau Omega (rationalRoots setup.ρ (rootCharHom a)
          (repr j₁))).map (MulAut.conj (g : ModGL tau Omega)).toMonoidHom =
        (rootSpan tau Omega (rationalRoots setup.ρ (rootCharHom a)
          (repr j₂))).map (MulAut.conj (g : ModGL tau Omega)).toMonoidHom := by
      rw [hf j₁, h12, hf j₂]
    have hspan := Subgroup.map_injective (f := (MulAut.conj (g : ModGL tau Omega)).toMonoidHom)
      (MulAut.conj (g : ModGL tau Omega)).injective hmap
    by_contra hne
    exact not_disjoint_rationalRoots_of_rootSpan_eq setup a_torus hspan
      (orbit_distinct j₁ j₂ hne)
  have hff : ∀ c, fullFactor setup iota a c =
      (rootSpan tau Omega (rationalRoots setup.ρ (rootCharHom a) c)).comap iota := by
    intro c
    ext r
    simp only [fullFactor, rationalSpan, Subgroup.mem_comap, Subgroup.mem_inf,
      and_iff_left_iff_imp]
    intro _
    rw [← iota_range]
    exact MonoidHom.mem_range.2 ⟨r, rfl⟩
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.1 hinj), fun j => ?_⟩
  rw [Equiv.ofBijective_apply, hff, hff, ← hf j]
  ext s
  constructor
  · rintro ⟨r, hr, rfl⟩
    refine Subgroup.mem_comap.2 (Subgroup.mem_map.2 ⟨iota r, Subgroup.mem_comap.1 hr, ?_⟩)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, modelAction_compat]
  · rintro ⟨x, hx, hxs⟩
    refine Subgroup.mem_map.2 ⟨(modelAction g).symm s, Subgroup.mem_comap.2 ?_,
      (modelAction g).apply_symm_apply s⟩
    have hc := modelAction_compat g ((modelAction g).symm s)
    rw [MulEquiv.apply_symm_apply] at hc
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hxs
    have h3 : iota ((modelAction g).symm s) = x :=
      (mul_left_cancel (mul_right_cancel (hxs.trans hc))).symm
    rw [h3]
    exact hx

theorem k0_fullFactor_map_modelAction
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (A : K0LangMark Omega lab p R I phi) (P : K0Positions A)
    (g : A.setup.D.model) (hg : Commute (A.modelAction g) phi) :
    ∃ sigma : Equiv.Perm (Fin A.row.D.orbits.length),
      ∀ j, (fullFactor A.setup A.iota A.a (P.repr j)).map (A.modelAction g).toMonoidHom =
        fullFactor A.setup A.iota A.a (P.repr (sigma j)) :=
  fullFactor_map_modelAction_of A.iota_range A.modelAction_inj A.modelAction_compat A.a_torus
    A.a_model A.action_eq P.orbit_cover P.orbit_distinct g hg

theorem eq_of_map_fullFactor_a12
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] {tau : Tag} {R : Type} [Group R]
    {setup : LangSetup tau Omega 5} {iota : R →* ModGL tau Omega}
    (iota_inj : Function.Injective iota) (iota_range : iota.range = setup.Γ)
    {a : Fin tau.rank → Omegaˣ} {lab : LargeEvenLabel} {p : ℕ} {D : GGKacDatum}
    (hD : GGKacValid lab p D) {repr : Fin D.orbits.length → KernelComponent (rootCharHom a)}
    (hqs : ∀ j, D.orbits[j].qs = true →
      CFSG.IsQuasisimple (rationalComponent setup.ρ setup.Γ (rootCharHom a) (repr j)))
    (hsolv : ∀ j, D.orbits[j].qs = false →
      Group.IsSolvable (rationalSpan setup.ρ setup.Γ (rootCharHom a) (repr j)))
    (hn : 1 ≤ lab.n) (hp : p.Prime) (hd : p ∣ 2 ^ lab.n - 1 ∨ p ∣ 2 ^ lab.n + 1)
    {j k : Fin D.orbits.length} (hj : D.orbits[j].lab = ⟨.A, 1, 1⟩)
    (hjqs : D.orbits[j].qs = false) (u : MulAut R)
    (hk : (fullFactor setup iota a (repr j)).map u.toMonoidHom = fullFactor setup iota a (repr k)) :
    k = j := by
  have hFj : Group.IsSolvable (fullFactor setup iota a (repr j)) := by
    have := hsolv j hjqs
    exact Group.isSolvable_of_isSolvable_injective
      (f := iota.subgroupComap (rationalSpan setup.ρ setup.Γ (rootCharHom a) (repr j)))
      fun x y h => Subtype.ext (iota_inj (congrArg Subtype.val h))
  have hFk : Group.IsSolvable (fullFactor setup iota a (repr k)) := by
    rw [← hk]
    exact Group.isSolvable_of_surjective (MonoidHom.subgroupMap_surjective u.toMonoidHom _)
  have hmap : (fullFactor setup iota a (repr k)).map iota =
      rationalSpan setup.ρ setup.Γ (rootCharHom a) (repr k) :=
    Subgroup.map_comap_eq_self (iota_range ▸ inf_le_right)
  have hSk : Group.IsSolvable (rationalSpan setup.ρ setup.Γ (rootCharHom a) (repr k)) := by
    rw [← hmap]
    exact Group.isSolvable_of_surjective (MonoidHom.subgroupMap_surjective iota _)
  have hkqs : D.orbits[k].qs = false := by
    cases hq : D.orbits[k].qs
    · rfl
    · exfalso
      have hq' := hqs k hq
      have hle : rationalComponent setup.ρ setup.Γ (rootCharHom a) (repr k) ≤
          rationalSpan setup.ρ setup.Γ (rootCharHom a) (repr k) :=
        Subgroup.commutator_le.2 fun x hx y hy =>
          Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hy)
            (Subgroup.inv_mem _ hx)) (Subgroup.inv_mem _ hy)
      have hsol : Group.IsSolvable (rationalComponent setup.ρ setup.Γ (rootCharHom a) (repr k)) :=
        Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
      have := hq'.1
      have : Nontrivial (rationalComponent setup.ρ setup.Γ (rootCharHom a) (repr k)) :=
        have := hq'.2.1.toNontrivial
        (QuotientGroup.mk_surjective (s := Subgroup.center _)).nontrivial
      exact Group.IsPerfect.not_isSolvable _ hsol
  exact ggKacValid_a12_nonqs_unique hn hp hd hD j k ⟨hj, hjqs⟩ hkqs |>.symm

theorem k0_fullFactor_a12_map_modelAction
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (A : K0LangMark Omega lab p R I phi) (P : K0Positions A)
    (hqs : ∀ j, A.row.D.orbits[j].qs = true →
      CFSG.IsQuasisimple (rationalComponent A.setup.ρ A.setup.Γ (rootCharHom A.a) (P.repr j)))
    (hsolv : ∀ j, A.row.D.orbits[j].qs = false →
      Group.IsSolvable (rationalSpan A.setup.ρ A.setup.Γ (rootCharHom A.a) (P.repr j)))
    (hn : 1 ≤ lab.n) (hp : p.Prime) (hd : p ∣ 2 ^ lab.n - 1 ∨ p ∣ 2 ^ lab.n + 1)
    (j : Fin A.row.D.orbits.length) (hj : A.row.D.orbits[j].lab = ⟨.A, 1, 1⟩)
    (hjqs : A.row.D.orbits[j].qs = false)
    (g : A.setup.D.model) (hg : Commute (A.modelAction g) phi) :
    (fullFactor A.setup A.iota A.a (P.repr j)).map (A.modelAction g).toMonoidHom =
      fullFactor A.setup A.iota A.a (P.repr j) := by
  obtain ⟨sigma, hsigma⟩ := k0_fullFactor_map_modelAction A P g hg
  rw [hsigma j, eq_of_map_fullFactor_a12 A.iota_inj A.iota_range A.row.valid hqs hsolv
    hn hp hd hj hjqs _ (hsigma j)]

end CFSG.StandardType.GGK0MarkedKacIface1587
