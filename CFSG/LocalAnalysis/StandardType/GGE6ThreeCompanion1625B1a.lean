module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeCompanion1625Pieces

public section

namespace CFSG.StandardType.S2MathAs1E6Companion1625

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.StandardType.GGK0MarkedKacIface1587
open CFSG.StandardType.E6Centralizer1585
open CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley
open CFSG.LieType.AlgebraicGroups
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private lemma ltrv3j1_geomCentralizer_eq
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (ρ : MarkedRationalKacRealization Omega lab p R I phi) :
    geomCentralizer ρ =
      (CFSG.StandardType.LayerSixE.famCentralizer
        ({ρ.a} : Set (Fin ρ.tau.rank → Omegaˣ))).map
        (CFSG.Blueprint.Chevalley.adjointGroup ρ.tau Omega).subtype := by
  ext x
  constructor
  · intro hx
    unfold geomCentralizer at hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxadj, hxcen⟩ := hx
    refine Subgroup.mem_map.mpr ⟨⟨x, hxadj⟩, ?_, rfl⟩
    rw [CFSG.StandardType.LayerSixE.mem_famCentralizer]
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    subst ha
    rw [Subgroup.mem_centralizer_iff] at hxcen
    exact mul_inv_eq_iff_eq_mul.mpr (hxcen _ (Set.mem_singleton _))
  · rintro ⟨g, hg, rfl⟩
    unfold geomCentralizer
    rw [Subgroup.mem_inf]
    refine ⟨g.2, ?_⟩
    change g ∈ CFSG.StandardType.LayerSixE.famCentralizer
        ({ρ.a} : Set (Fin ρ.tau.rank → Omegaˣ)) at hg
    rw [CFSG.StandardType.LayerSixE.mem_famCentralizer] at hg
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact mul_inv_eq_iff_eq_mul.mp (hg _ (Set.mem_singleton _))

private lemma ltrv3j1_centralizerGroup_eq
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (ρ : MarkedRationalKacRealization Omega lab p R I phi) :
    centralizerGroup ρ =
      ((geomCentralizer ρ ⊓ ρ.setup.D.model).subgroupOf ρ.setup.D.model).map ρ.modelAction := by
  ext u
  constructor
  · intro hu
    unfold centralizerGroup at hu
    unfold innDiag at hu
    rw [Subgroup.mem_inf] at hu
    obtain ⟨hu_range, hu_cen⟩ := hu
    rw [MonoidHom.range_eq_map, Subgroup.mem_map] at hu_range
    obtain ⟨g, -, rfl⟩ := hu_range
    refine Subgroup.mem_map.mpr ⟨g, ?_, rfl⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    refine ⟨?_, g.2⟩
    unfold geomCentralizer
    rw [Subgroup.mem_inf]
    refine ⟨(ρ.setup.D.mem_model.mp g.2).1, ?_⟩
    rw [Subgroup.mem_centralizer_iff] at hu_cen ⊢
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    have hc : ρ.modelAction (⟨rootDiagUnit ρ.tau ρ.a, ρ.a_model⟩ * g) =
        ρ.modelAction (g * ⟨rootDiagUnit ρ.tau ρ.a, ρ.a_model⟩) := by
      rw [map_mul, map_mul, ρ.action_eq]
      exact hu_cen phi (Set.mem_singleton _)
    have hcg : (⟨rootDiagUnit ρ.tau ρ.a, ρ.a_model⟩ : ρ.setup.D.model) * g =
        g * ⟨rootDiagUnit ρ.tau ρ.a, ρ.a_model⟩ := ρ.modelAction_inj hc
    have hval := congrArg Subtype.val hcg
    simpa using hval
  · rintro ⟨g, hg, rfl⟩
    unfold centralizerGroup
    unfold innDiag
    rw [Subgroup.mem_inf]
    refine ⟨⟨g, rfl⟩, ?_⟩
    change g ∈ (geomCentralizer ρ ⊓ ρ.setup.D.model).subgroupOf ρ.setup.D.model at hg
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hg
    obtain ⟨hg_geom, -⟩ := hg
    unfold geomCentralizer at hg_geom
    rw [Subgroup.mem_inf] at hg_geom
    obtain ⟨-, hg_cen⟩ := hg_geom
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    rw [Subgroup.mem_centralizer_iff] at hg_cen
    have hc := hg_cen _ (Set.mem_singleton _)
    have hge : (⟨rootDiagUnit ρ.tau ρ.a, ρ.a_model⟩ : ρ.setup.D.model) * g =
        g * ⟨rootDiagUnit ρ.tau ρ.a, ρ.a_model⟩ := Subtype.ext (by simpa using hc)
    have hc2 : ρ.modelAction (⟨rootDiagUnit ρ.tau ρ.a, ρ.a_model⟩ : ρ.setup.D.model) *
        ρ.modelAction g = ρ.modelAction g *
        ρ.modelAction (⟨rootDiagUnit ρ.tau ρ.a, ρ.a_model⟩ : ρ.setup.D.model) := by
      rw [← map_mul, ← map_mul, hge]
    simpa [ρ.action_eq] using hc2

private lemma ltrv3j1_b1BruhatAt_of_certs
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (ρ : MarkedRationalKacRealization Omega lab p R I phi)
    (j : Fin ρ.row.D.orbits.length) : B1BruhatAt ρ j := by
  refine ⟨ltrv3j1_geomCentralizer_eq ρ, ?_⟩
  intro g hg
  rw [ltrv3j1_geomCentralizer_eq ρ, Subgroup.mem_map] at hg
  obtain ⟨x, hx, rfl⟩ := hg
  have hx' : (x : ModGL ρ.tau Omega) ∈
      CFSG.HardMathSupport.Timmesfeld.Torality.familyCentralizer ρ.tau Omega
        (fun a : ({ρ.a} : Set (Fin ρ.tau.rank → Omegaˣ)) => (a : Fin ρ.tau.rank → Omegaˣ)) := by
    rw [CFSG.HardMathSupport.Timmesfeld.Torality.mem_familyCentralizer]
    refine ⟨x.2, fun i => ?_⟩
    exact (CFSG.StandardType.LayerSixE.mem_famCentralizer.mp hx) i i.2
  obtain ⟨w, hw, h, hh, u, hu, v, hv, heq⟩ :=
    CFSG.HardMathSupport.Timmesfeld.Torality.familyCentralizer_factors ρ.tau Omega
      (fun a : ({ρ.a} : Set (Fin ρ.tau.rank → Omegaˣ)) => (a : Fin ρ.tau.rank → Omegaˣ))
      (x : ModGL ρ.tau Omega) hx'
  refine ⟨w, ?_, h, hh, u, ?_, v, ?_, heq⟩
  · simpa [CFSG.StandardType.LayerSixE.famStabilizer_eq_familyStabilizer] using hw
  · simpa [CFSG.StandardType.LayerSixE.famKernel_eq_familyKernel] using hu
  · simpa [CFSG.StandardType.LayerSixE.famKernel_eq_familyKernel] using hv

theorem b1aOn_holds (Omega : Type) [Field Omega] [IsAlgClosed Omega] [CharP Omega 2] :
    B1aOn Omega := by
  unfold B1aOn
  intro lab R _ I phi ρ j _ _ _
  exact ⟨ltrv3j1_centralizerGroup_eq ρ, ltrv3j1_b1BruhatAt_of_certs ρ j⟩

end CFSG.StandardType.S2MathAs1E6Companion1625

end
