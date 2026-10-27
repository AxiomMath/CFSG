module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeCompanion1625Pieces

public section

namespace CFSG.StandardType.S2MathAs1E6Companion1625

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.StandardType.GGK0MarkedKacIface1587
open CFSG.StandardType.E6Centralizer1585
open CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.LieType.AlgebraicGroups
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private lemma ltrv3j2_geom {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (ρ : MarkedRationalKacRealization Omega lab 3 R I phi) :
    connectedCentralizer ρ ≤ geomCentralizer ρ ∧
      ((connectedCentralizer ρ).subgroupOf (geomCentralizer ρ)).Normal := by
  set F : Set (Fin ρ.tau.rank → Omegaˣ) := {ρ.a} with hF
  have hfamK : CFSG.RankThree.PartOne.KE8F.famKernel F =
      kernelRoots (rootCharHom ρ.a) := by
    ext α
    simp [CFSG.RankThree.PartOne.KE8F.famKernel, kernelRoots_rootCharHom, hF]
  have hgeom : geomCentralizer ρ =
      (LayerSixE.famCentralizer F).map (adjointGroup ρ.tau Omega).subtype := by
    ext x
    constructor
    · intro hx
      refine Subgroup.mem_map.mpr ⟨⟨x, hx.1⟩, ?_, rfl⟩
      rw [LayerSixE.mem_famCentralizer]
      intro b hb
      rw [hF, Set.mem_singleton_iff] at hb
      subst hb
      have hcomm := Subgroup.mem_centralizer_singleton_iff.mp hx.2
      rw [← hcomm]
      group
    · rintro ⟨y, hy, rfl⟩
      rw [geomCentralizer, Subgroup.mem_inf]
      refine ⟨y.2, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      change (y : ModGL ρ.tau Omega) * rootDiagUnit ρ.tau ρ.a =
        rootDiagUnit ρ.tau ρ.a * (y : ModGL ρ.tau Omega)
      have hy' : rootDiagUnit ρ.tau ρ.a * (y : ModGL ρ.tau Omega) *
          (rootDiagUnit ρ.tau ρ.a)⁻¹ = (y : ModGL ρ.tau Omega) :=
        (LayerSixE.mem_famCentralizer.mp hy) ρ.a
          (by rw [hF]; exact Set.mem_singleton ρ.a)
      exact (mul_inv_eq_iff_eq_mul.mp hy').symm
  have htor : Subgroup.closure (Set.range (fun b : Fin ρ.tau.rank → Omegaˣ =>
        rootDiagUnit ρ.tau b)) = torusGroup ρ.tau Omega := by
    refine le_antisymm ?_ ?_
    · refine (Subgroup.closure_le (torusGroup ρ.tau Omega)).mpr ?_
      rintro x ⟨b, rfl⟩
      exact rootDiagUnit_mem_torusGroup b
    · refine (CFSG.HardMathSupport.Timmesfeld.CrossChar.torusGroup_le_range_rootDiagUnitHom
        (τ := ρ.tau) (K := Omega)).trans ?_
      rintro x ⟨b, rfl⟩
      exact Subgroup.subset_closure ⟨b, rfl⟩
  have hle : connectedCentralizer ρ ≤ geomCentralizer ρ := by
    rw [connectedCentralizer, hgeom, htor, ← hfamK]
    exact LayerSixE.torus_sup_rootSpan_le_map_famCentralizer (τ := ρ.tau) (K := Omega) F
  refine ⟨hle, ?_⟩
  have hnorm : (LayerSixE.famCentralizer F).map (adjointGroup ρ.tau Omega).subtype ≤
      Subgroup.normalizer (connectedCentralizer ρ) := by
    simpa only [connectedCentralizer, ← htor, ← hfamK] using
      (LayerSixE.map_famCentralizer_le_normalizer (τ := ρ.tau) (K := Omega) F)
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hle, hgeom]
  exact hnorm

private lemma ltrv3j2_kernel_stable {Omega : Type} [Field Omega] [IsAlgClosed Omega]
    [CharP Omega 2]
    {lab : LargeEvenLabel} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (ρ : MarkedRationalKacRealization Omega lab 3 R I phi) :
    ∀ γ ∈ kernelRoots (rootCharHom ρ.a), ρ.setup.ρ γ ∈ kernelRoots (rootCharHom ρ.a) := by
  intro γ hγ
  rw [kernelRoots_rootCharHom] at hγ ⊢
  exact ⟨(ρ.setup.frob.isRoot_iff γ).2 hγ.1,
    by rw [ρ.setup.frob.rootChar_eq ρ.a ρ.a_torus γ hγ.1, hγ.2, one_pow]⟩

private lemma ltrv3j2_rationalRoots_subset {Omega : Type} [Field Omega] [IsAlgClosed Omega]
    [CharP Omega 2]
    {lab : LargeEvenLabel} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (ρ : MarkedRationalKacRealization Omega lab 3 R I phi)
    (j : Fin ρ.row.D.orbits.length) :
    rationalRoots ρ.setup.ρ (rootCharHom ρ.a) (ρ.repr j) ⊆
      kernelRoots (rootCharHom ρ.a) := by
  intro γ hγ
  rw [rationalRoots] at hγ
  obtain ⟨k, δ, hδ, rfl⟩ := hγ
  obtain ⟨hδker, -⟩ := hδ
  induction k with
  | zero => simpa using hδker
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact ltrv3j2_kernel_stable ρ _ ih

private lemma ltrv3j2_component_eq_commutator {Omega : Type} [Field Omega] [IsAlgClosed Omega]
    [CharP Omega 2]
    {lab : LargeEvenLabel} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (ρ : MarkedRationalKacRealization Omega lab 3 R I phi)
    (j : Fin ρ.row.D.orbits.length) :
    component ρ j = ⁅fullFactor ρ.setup ρ.iota ρ.a (ρ.repr j),
      fullFactor ρ.setup ρ.iota ρ.a (ρ.repr j)⁆ := by
  rw [component, coreFactor, rationalComponent, fullFactor]
  have hle : rationalSpan ρ.setup.ρ ρ.setup.Γ (rootCharHom ρ.a) (ρ.repr j) ≤ ρ.iota.range := by
    rw [ρ.iota_range]
    exact inf_le_right
  have hmapself : (Subgroup.comap ρ.iota
        (rationalSpan ρ.setup.ρ ρ.setup.Γ (rootCharHom ρ.a) (ρ.repr j))).map ρ.iota =
      rationalSpan ρ.setup.ρ ρ.setup.Γ (rootCharHom ρ.a) (ρ.repr j) := by
    rw [Subgroup.map_comap_eq, inf_eq_right.mpr hle]
  have hmapcomm : (⁅Subgroup.comap ρ.iota
          (rationalSpan ρ.setup.ρ ρ.setup.Γ (rootCharHom ρ.a) (ρ.repr j)),
        Subgroup.comap ρ.iota
          (rationalSpan ρ.setup.ρ ρ.setup.Γ (rootCharHom ρ.a) (ρ.repr j))⁆).map ρ.iota =
      ⁅rationalSpan ρ.setup.ρ ρ.setup.Γ (rootCharHom ρ.a) (ρ.repr j),
        rationalSpan ρ.setup.ρ ρ.setup.Γ (rootCharHom ρ.a) (ρ.repr j)⁆ := by
    rw [Subgroup.map_commutator, hmapself]
  have hkerbot : ρ.iota.ker = ⊥ := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_bot]
    exact ⟨fun h => ρ.iota_inj (by rw [h, map_one]), fun h => by rw [h, map_one]⟩
  have hcme : ∀ H : Subgroup R, (H.map ρ.iota).comap ρ.iota = H := by
    intro H
    rw [Subgroup.comap_map_eq, hkerbot, sup_bot_eq]
  rw [← hmapcomm, hcme]

theorem b1bOn_holds (Omega : Type) [Field Omega] [IsAlgClosed Omega] [CharP Omega 2] :
    B1bOn Omega := by
  intro lab R _ I phi ρ j hΛ hj hqs
  have hgeo := ltrv3j2_geom ρ
  have hconn_le : conn ρ ≤ centralizerGroup ρ := by
    intro u hu
    rw [conn, Subgroup.mem_map] at hu
    obtain ⟨⟨m, hm⟩, hmm, hmv⟩ := hu
    have hmm' : (m : ModGL ρ.tau Omega) ∈ connectedCentralizer ρ ⊓ ρ.setup.D.model :=
      Subgroup.mem_subgroupOf.mp hmm
    rw [centralizerGroup, Subgroup.mem_inf]
    refine ⟨?_, ?_⟩
    · rw [innDiag]
      exact ⟨⟨m, hm⟩, hmv⟩
    · rw [Subgroup.mem_centralizer_singleton_iff, ← hmv]
      have hcomm_amb : m * rootDiagUnit ρ.tau ρ.a = rootDiagUnit ρ.tau ρ.a * m :=
        Subgroup.mem_centralizer_singleton_iff.mp (hgeo.1 hmm'.1).2
      have hcomm : (⟨m, hm⟩ : ρ.setup.D.model) *
          ⟨rootDiagUnit ρ.tau ρ.a, ρ.a_model⟩ =
          ⟨rootDiagUnit ρ.tau ρ.a, ρ.a_model⟩ * ⟨m, hm⟩ := Subtype.ext hcomm_amb
      have h := congrArg ρ.modelAction hcomm
      have h' : ρ.modelAction ⟨m, hm⟩ *
          ρ.modelAction ⟨rootDiagUnit ρ.tau ρ.a, ρ.a_model⟩ =
          ρ.modelAction ⟨rootDiagUnit ρ.tau ρ.a, ρ.a_model⟩ * ρ.modelAction ⟨m, hm⟩ := by
        rw [← map_mul, ← map_mul]
        exact h
      rwa [ρ.action_eq] at h'
  refine ⟨hgeo.1, hgeo.2, hconn_le, ?_, ?_, ?_⟩
  ·
    intro v hv
    rw [innerComponent, Subgroup.mem_map] at hv
    obtain ⟨d, hd, rfl⟩ := hv
    have hdRC : ρ.iota d ∈
        rationalComponent ρ.setup.ρ ρ.setup.Γ (rootCharHom ρ.a) (ρ.repr j) := by
      have h := hd
      rw [component, coreFactor] at h
      exact h
    have hRCleRS : rationalComponent ρ.setup.ρ ρ.setup.Γ (rootCharHom ρ.a) (ρ.repr j) ≤
        rationalSpan ρ.setup.ρ ρ.setup.Γ (rootCharHom ρ.a) (ρ.repr j) := by
      rw [rationalComponent]
      refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
      rw [commutatorElement_def]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb)
        (Subgroup.inv_mem _ ha)) (Subgroup.inv_mem _ hb)
    have hsub := ltrv3j2_rationalRoots_subset ρ j
    have hmemRS : ρ.iota d ∈ rationalSpan ρ.setup.ρ ρ.setup.Γ (rootCharHom ρ.a) (ρ.repr j) :=
      hRCleRS hdRC
    have hmemH : ρ.iota d ∈ connectedCentralizer ρ := by
      rw [connectedCentralizer]
      refine Subgroup.mem_sup_right ?_
      exact rootSpan_mono hsub hmemRS.1
    have hmemM : ρ.iota d ∈ ρ.setup.D.model := by
      have hΓ : rationalComponent ρ.setup.ρ ρ.setup.Γ (rootCharHom ρ.a) (ρ.repr j) ≤
          ρ.setup.D.model := by
        refine (hRCleRS.trans inf_le_right).trans ?_
        rw [LangSetup.Γ, LangDatum.Γ]
        refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
        rw [commutatorElement_def]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb)
          (Subgroup.inv_mem _ ha)) (Subgroup.inv_mem _ hb)
      exact hΓ hdRC
    refine Subgroup.mem_map.mpr ⟨⟨ρ.iota d, hmemM⟩, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf]
      exact ⟨hmemH, hmemM⟩
    · ext r
      apply ρ.iota_inj
      rw [ρ.modelAction_compat, MulAut.conj_apply]
      simp [map_mul]
  ·
    rw [Subgroup.normal_subgroupOf_iff hconn_le]
    intro h k hk hkK
    have hk'' : h ∈ ((connectedCentralizer ρ ⊓ ρ.setup.D.model).subgroupOf
        ρ.setup.D.model).map ρ.modelAction := hk
    rw [Subgroup.mem_map] at hk''
    obtain ⟨⟨mv, hmvM⟩, hmvH, hmvv⟩ := hk''
    rw [centralizerGroup, Subgroup.mem_inf] at hkK
    obtain ⟨mu, hmu⟩ := hkK.1
    have hmuc : (mu : ModGL ρ.tau Omega) * rootDiagUnit ρ.tau ρ.a =
        rootDiagUnit ρ.tau ρ.a * (mu : ModGL ρ.tau Omega) := by
      have hh : ρ.modelAction mu * phi = phi * ρ.modelAction mu := by
        rw [hmu]
        exact Subgroup.mem_centralizer_singleton_iff.mp hkK.2
      have hsub : (mu : ↥ρ.setup.D.model) * ⟨rootDiagUnit ρ.tau ρ.a, ρ.a_model⟩ =
          ⟨rootDiagUnit ρ.tau ρ.a, ρ.a_model⟩ * mu := by
        apply ρ.modelAction_inj
        rw [map_mul, map_mul, ρ.action_eq]
        exact hh
      exact congrArg Subtype.val hsub
    have hmuG : (mu : ModGL ρ.tau Omega) ∈ geomCentralizer ρ :=
      ⟨(LangDatum.mem_model (D := ρ.setup.D)).1 mu.2 |>.1,
        Subgroup.mem_centralizer_singleton_iff.mpr hmuc⟩
    have hmvH' : (mv : ModGL ρ.tau Omega) ∈ connectedCentralizer ρ :=
      (Subgroup.mem_subgroupOf.mp hmvH).1
    have hmvG : (mv : ModGL ρ.tau Omega) ∈ geomCentralizer ρ := hgeo.1 hmvH'
    have hconj_sub : (⟨(mu : ModGL ρ.tau Omega), hmuG⟩ : ↥(geomCentralizer ρ)) *
        ⟨(mv : ModGL ρ.tau Omega), hmvG⟩ *
        (⟨(mu : ModGL ρ.tau Omega), hmuG⟩ : ↥(geomCentralizer ρ))⁻¹ ∈
        (connectedCentralizer ρ).subgroupOf (geomCentralizer ρ) :=
      hgeo.2.conj_mem ⟨(mv : ModGL ρ.tau Omega), hmvG⟩
        (Subgroup.mem_subgroupOf.mpr hmvH') ⟨(mu : ModGL ρ.tau Omega), hmuG⟩
    have hconj : (mu : ModGL ρ.tau Omega) * (mv : ModGL ρ.tau Omega) *
        (mu : ModGL ρ.tau Omega)⁻¹ ∈ connectedCentralizer ρ :=
      Subgroup.mem_subgroupOf.mp hconj_sub
    have hconjM : (mu : ModGL ρ.tau Omega) * (mv : ModGL ρ.tau Omega) *
        (mu : ModGL ρ.tau Omega)⁻¹ ∈ ρ.setup.D.model := by
      have h1 : (mu : ModGL ρ.tau Omega) * (mv : ModGL ρ.tau Omega) ∈
          ρ.setup.D.model :=
        ρ.setup.D.model.mul_mem mu.2 hmvM
      exact ρ.setup.D.model.mul_mem h1 (ρ.setup.D.model.inv_mem mu.2)
    rw [← hmu, ← hmvv]
    refine Subgroup.mem_map.mpr
      ⟨⟨_, hconjM⟩, Subgroup.mem_subgroupOf.mpr ⟨hconj, hconjM⟩, ?_⟩
    change ρ.modelAction (⟨(mu : ModGL ρ.tau Omega), mu.2⟩ * ⟨mv, hmvM⟩ *
        ⟨(mu : ModGL ρ.tau Omega), mu.2⟩⁻¹) =
      ρ.modelAction mu * ρ.modelAction ⟨mv, hmvM⟩ * (ρ.modelAction mu)⁻¹
    rw [map_mul, map_mul, map_inv]
  ·
    intro u hu x
    rw [centralizerGroup, Subgroup.mem_inf] at hu
    have hcomm : Commute u phi := Subgroup.mem_centralizer_singleton_iff.mp hu.2
    obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp hu.1
    obtain ⟨sigma, hmap⟩ := ρ.model_equivariance g (hg ▸ hcomm)
    rw [hg] at hmap
    have hsig : sigma j = j := hj (sigma j)
    have hmapj : (fullFactor ρ.setup ρ.iota ρ.a (ρ.repr j)).map u.toMonoidHom =
        fullFactor ρ.setup ρ.iota ρ.a (ρ.repr j) := by
      rw [hmap j, hsig]
    have hFF : ⁅fullFactor ρ.setup ρ.iota ρ.a (ρ.repr j),
        fullFactor ρ.setup ρ.iota ρ.a (ρ.repr j)⁆ = component ρ j :=
      (ltrv3j2_component_eq_commutator ρ j).symm
    rw [← hFF]
    have hFFmap : (⁅fullFactor ρ.setup ρ.iota ρ.a (ρ.repr j),
        fullFactor ρ.setup ρ.iota ρ.a (ρ.repr j)⁆).map u.toMonoidHom =
        ⁅fullFactor ρ.setup ρ.iota ρ.a (ρ.repr j),
          fullFactor ρ.setup ρ.iota ρ.a (ρ.repr j)⁆ := by
      rw [Subgroup.map_commutator, hmapj]
    have hmem : u x ∈ (⁅fullFactor ρ.setup ρ.iota ρ.a (ρ.repr j),
        fullFactor ρ.setup ρ.iota ρ.a (ρ.repr j)⁆).map u.toMonoidHom ↔
        x ∈ ⁅fullFactor ρ.setup ρ.iota ρ.a (ρ.repr j),
          fullFactor ρ.setup ρ.iota ρ.a (ρ.repr j)⁆ := by
      rw [Subgroup.mem_map]
      constructor
      · rintro ⟨y, hy, hyx⟩
        have hyx' : y = x := u.injective hyx
        simpa [hyx'] using hy
      · intro hx
        exact ⟨x, hx, rfl⟩
    rw [hFFmap] at hmem
    exact hmem.symm

end CFSG.StandardType.S2MathAs1E6Companion1625

end
