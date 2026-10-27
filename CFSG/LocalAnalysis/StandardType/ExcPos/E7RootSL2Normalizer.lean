module

public import CFSG.LinearAlgebra.LinearGroups.SL2InvolutionPairs
public import CFSG.LocalAnalysis.StandardType.GGOrdinaryMemberE7RootCentralizer
public import CFSG.LocalAnalysis.StandardType.GGLieM6cDescent
public import CFSG.RankThree.Chevalley.EvenPinnedRootSL2
public import CFSG.LocalAnalysis.StandardType.ExcPos.E6RootPairStabilizer
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.AmbientPairDescentPart1

public noncomputable section

namespace CFSG.StandardType.LieKnownR2.ExcPos

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KE6 CFSG.SeitzReduction.E8Pilot
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley WithConv

open scoped CFSG.ConvolutionPoints




private theorem domainImage_of_connected
    {k : Type} [Field k] [IsAlgClosed k] {A : Type} [CommRing A]
    [HopfAlgebra k A] [Algebra.FiniteType k A]
    {H : Subgroup (WithConv (A →ₐ[k] k))}
    (h : IsConnectedAlgebraicSubgroup k H) :
    SeminaireExp3.IsDomainImage k (subgroupPoints H) := by
  letI := h.finiteType
  letI := h.isDomain
  refine ⟨A ⧸ subgroupIdeal H, inferInstance, inferInstance, inferInstance,
    inferInstance, Ideal.Quotient.mkₐ k (subgroupIdeal H), ?_⟩
  rw [SeminaireExp3.range_comp_mkₐ, h.pointsZero_eq]

private theorem connected_sup
    {tau : Tag} {k : Type} [Field k] [IsAlgClosed k]
    (H K : Subgroup (ModGL tau k))
    (hH : IsConnectedAlgebraicSubgroup k (H.map (modGLPoint tau k).toMonoidHom))
    (hK : IsConnectedAlgebraicSubgroup k (K.map (modGLPoint tau k).toMonoidHom)) :
    IsConnectedAlgebraicSubgroup k ((H ⊔ K).map (modGLPoint tau k).toMonoidHom) := by
  let C : Bool → Set (ModGL tau k) := Bool.rec (H : Set _) (K : Set _)
  have hC : ∀ b, SeminaireExp3.IsDomainImage k
      (SeminaireExp3.ZariskiGL.pt '' (modGLZariski tau k '' C b)) := by
    intro b
    cases b
    · change SeminaireExp3.IsDomainImage k
        (SeminaireExp3.ZariskiGL.pt '' (modGLZariski tau k '' (H : Set _)))
      rw [← transportPoints_eq_image_modGLZariski, ← subgroupPoints_map]
      exact domainImage_of_connected hH
    · change SeminaireExp3.IsDomainImage k
        (SeminaireExp3.ZariskiGL.pt '' (modGLZariski tau k '' (K : Set _)))
      rw [← transportPoints_eq_image_modGLZariski, ← subgroupPoints_map]
      exact domainImage_of_connected hK
  have h1 : ∀ b, (1 : ModGL tau k) ∈ C b := by intro b; cases b <;> exact Subgroup.one_mem _
  have hUnion : (⋃ b, C b) = (H : Set _) ∪ (K : Set _) := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_union]
    constructor
    · rintro ⟨b, hb⟩
      cases b
      · exact Or.inl hb
      · exact Or.inr hb
    · rintro (h | h)
      · exact ⟨false, h⟩
      · exact ⟨true, h⟩
  have h := isConnectedAlgebraicSubgroup_closure_iUnion C hC h1
  simpa only [hUnion, Subgroup.closure_union, Subgroup.closure_eq] using h

theorem e7_commute_pinnedX_of_commute_one
    {Omega : Type} [Field Omega] [CharP Omega 2] [Algebra (ZMod 2) Omega]
    [Algebra.IsAlgebraic (ZMod 2) Omega]
    {g : ModGL .E7 Omega} (hg : g ∈ adjointGroup .E7 Omega)
    {gamma : Fin Tag.E7.rank → ℤ} (hgamma : IsRoot .E7 gamma)
    (hOne : Commute g (pinnedX .E7 Omega gamma 1)) (c : Omega) :
    Commute g (pinnedX .E7 Omega gamma c) := by
  classical
  obtain ⟨F, hF, hFfin, kappa, iota, -, hLift⟩ :=
    CFSG.StandardType.LieCore.M6c.exists_finite_subfield_lift_adjoint
      ({g} : Finset (ModGL .E7 Omega)) (by simpa using hg)
      (ZMod 2) (algebraMap (ZMod 2) Omega)
  letI := hF
  letI := hFfin
  haveI : CharP F 2 := RingHom.charP iota iota.injective 2
  letI : Algebra F Omega := iota.toAlgebra
  letI : Algebra (ZMod 2) F := ZMod.algebra F 2
  haveI : IsScalarTower (ZMod 2) F Omega :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_zmod _ _)
  haveI : Algebra.IsAlgebraic F Omega :=
    Algebra.IsAlgebraic.tower_top (K := ZMod 2) (L := F)
  obtain ⟨gF, hgF, hfg⟩ := hLift g (by simp)
  let theta := e7MinEquivAdjoint F
  let y : e7Data_valid.minGroup F := theta.symm ⟨gF, hgF⟩
  have hy : ((e7Isogeny F y : adjointGroup .E7 F) : ModGL .E7 F) = gF := by
    change ((theta (theta.symm ⟨gF, hgF⟩) : adjointGroup .E7 F) : ModGL .E7 F) = gF
    simp
  have hNative : Commute y (e7Data_valid.xm F gamma 1) := by
    change y * e7Data_valid.xm F gamma 1 = e7Data_valid.xm F gamma 1 * y
    apply theta.injective
    rw [map_mul, map_mul]
    apply Subtype.ext
    change ((e7Isogeny F y : adjointGroup .E7 F) : ModGL .E7 F) *
      ((e7Isogeny F (e7Data_valid.xm F gamma 1) : adjointGroup .E7 F) : ModGL .E7 F) =
      ((e7Isogeny F (e7Data_valid.xm F gamma 1) : adjointGroup .E7 F) : ModGL .E7 F) *
      ((e7Isogeny F y : adjointGroup .E7 F) : ModGL .E7 F)
    rw [hy, coe_e7Isogeny_xm hgamma]
    apply baseChangeGL_injective (f := iota)
    have hh := hOne.eq
    rw [← hfg] at hh
    simpa only [map_mul, baseChangeGL_pinnedX, map_one] using hh
  have hc := e7_commute_pinnedX_baseChange_of_commute_xm_one hgamma hNative c
  change Commute (baseChangeGL iota
    ((e7Isogeny F y : adjointGroup .E7 F) : ModGL .E7 F)) (pinnedX .E7 Omega gamma c) at hc
  rwa [hy, hfg] at hc

variable {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
  [Algebra (ZMod 2) Omega] [Algebra.IsAlgebraic (ZMod 2) Omega]

theorem normalizer_rootSL2_inf_eq_sup_pair_stabilizer
    (H : Subgroup (ModGL .E7 Omega)) (hH : H ≤ adjointGroup .E7 Omega)
    {gamma : Fin Tag.E7.rank → ℤ} (hgamma : IsRoot .E7 gamma)
    (hAH : (rootSL2 .E7 Omega gamma).range ≤ H) :
    H ⊓ Subgroup.normalizer ((rootSL2 .E7 Omega gamma).range : Set _) =
      (rootSL2 .E7 Omega gamma).range ⊔
        (H ⊓ Subgroup.normalizer (rootSubgroup .E7 Omega gamma : Set _) ⊓
          Subgroup.normalizer (rootSubgroup .E7 Omega (-gamma) : Set _)) := by
  classical
  let phi := rootSL2 .E7 Omega gamma
  let Z := H ⊓ Subgroup.normalizer (rootSubgroup .E7 Omega gamma : Set _) ⊓
    Subgroup.normalizer (rootSubgroup .E7 Omega (-gamma) : Set _)
  have hRange : phi.range = rootSubgroup .E7 Omega gamma ⊔
      rootSubgroup .E7 Omega (-gamma) := range_rootSL2_of_isRoot hgamma
  have hZnormal : Z ≤ Subgroup.normalizer (phi.range : Set _) := by
    intro n hn
    have hp : (rootSubgroup .E7 Omega gamma).map (MulAut.conj n).toMonoidHom =
        rootSubgroup .E7 Omega gamma := by
      have h := Subgroup.mem_normalizer_iff_map_conj_eq.mp hn.1.2
      rwa [← MulEquiv.toMonoidHom_eq_coe] at h
    have hm : (rootSubgroup .E7 Omega (-gamma)).map (MulAut.conj n).toMonoidHom =
        rootSubgroup .E7 Omega (-gamma) := by
      have h := Subgroup.mem_normalizer_iff_map_conj_eq.mp hn.2
      rwa [← MulEquiv.toMonoidHom_eq_coe] at h
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    rw [← MulEquiv.toMonoidHom_eq_coe, hRange, Subgroup.map_sup, hp, hm]
  apply le_antisymm
  · intro n hn
    have hsq : ∀ a : Omega, ∃ b : Omega, b * b = a := by
      intro a
      obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq a (n := 2) (by decide)
      exact ⟨b, by simpa only [pow_two] using hb⟩
    obtain ⟨g, hgU, hgV⟩ := CFSG.LinearGroups.SL2.exists_corrector_of_normalizes_range
      phi (rootSL2_injective_of_field gamma) hsq hn.2
    let k : ModGL .E7 Omega := (phi g)⁻¹ * n
    have hgH : phi g ∈ H := hAH ⟨g, rfl⟩
    have hkH : k ∈ H := H.mul_mem (H.inv_mem hgH) hn.1
    have hkA : k ∈ adjointGroup .E7 Omega := hH hkH
    have hU : sl2Upper (1 : Omega) = uSL 1 := by apply Subtype.ext; rfl
    have hV : sl2Lower (1 : Omega) = vSL 1 := by apply Subtype.ext; rfl
    have hUimage : phi (sl2Upper 1) = pinnedX .E7 Omega gamma 1 := by
      rw [hU]
      exact rootSL2_uSL_of_charTwo hgamma _
    have hVimage : phi (sl2Lower 1) = pinnedX .E7 Omega (-gamma) 1 := by
      rw [hV]
      exact rootSL2_vSL_of_charTwo hgamma _
    have hkU : Commute k (pinnedX .E7 Omega gamma 1) := by
      simpa only [k, hUimage] using hgU
    have hkV : Commute k (pinnedX .E7 Omega (-gamma) 1) := by
      simpa only [k, hVimage] using hgV
    have hrootNorm (delta : Fin Tag.E7.rank → ℤ)
        (hc : ∀ c, Commute k (pinnedX .E7 Omega delta c)) :
        k ∈ Subgroup.normalizer (rootSubgroup .E7 Omega delta : Set _) := by
      have hle : rootSubgroup .E7 Omega delta ≤ Subgroup.centralizer ({k} : Set _) := by
        apply (Subgroup.closure_le (Subgroup.centralizer ({k} : Set _))).mpr
        rintro _ ⟨c, rfl⟩
        apply Subgroup.mem_centralizer_iff.mpr
        intro z hz
        obtain rfl := Set.mem_singleton_iff.mp hz
        exact (hc c).eq
      apply Subgroup.centralizer_le_normalizer _
      apply Subgroup.mem_centralizer_iff.mpr
      intro z hz
      exact (Subgroup.mem_centralizer_iff.mp (hle hz) k (by simp)).symm
    have hkNplus := hrootNorm gamma fun c =>
      e7_commute_pinnedX_of_commute_one hkA hgamma hkU c
    have hkNminus := hrootNorm (-gamma) fun c =>
      e7_commute_pinnedX_of_commute_one hkA (IsRoot.neg hgamma) hkV c
    have hkZ : k ∈ Z := ⟨⟨hkH, hkNplus⟩, hkNminus⟩
    have hgJoin : phi g ∈ phi.range ⊔ Z :=
      (show phi.range ≤ phi.range ⊔ Z from le_sup_left) ⟨g, rfl⟩
    have hkJoin : k ∈ phi.range ⊔ Z :=
      (show Z ≤ phi.range ⊔ Z from le_sup_right) hkZ
    have hjoin : phi g * k ∈ phi.range ⊔ Z := Subgroup.mul_mem _ hgJoin hkJoin
    have hnk : phi g * k = n := by dsimp [k]; group
    rwa [hnk] at hjoin
  · apply sup_le
    · exact le_inf hAH Subgroup.le_normalizer
    · exact le_inf (fun _ hn => hn.1.1) hZnormal

theorem isConnectedAlgebraicSubgroup_e6_rootSL2_normalizer
    (w : WeylGroup .E7) (Psi : Set (Fin Tag.E7.rank → ℤ))
    (hPsi : Psi = (fun alpha => w • alpha) '' parabolicRoots .E7 (e6Nodes .E7))
    {gamma : Fin Tag.E7.rank → ℤ} (hgamma : IsRoot .E7 gamma)
    (hgPsi : gamma ∈ Psi) (hngPsi : -gamma ∈ Psi) :
    IsConnectedAlgebraicSubgroup Omega
      ((rootSpan .E7 Omega Psi ⊓
        Subgroup.normalizer ((rootSL2 .E7 Omega gamma).range : Set _)).map
          (modGLPoint .E7 Omega).toMonoidHom) := by
  let H := rootSpan .E7 Omega Psi
  have hHA : H ≤ adjointGroup .E7 Omega :=
    le_trans le_sup_right (torus_sup_rootSpan_le_adjointGroup Psi)
  have hAH : (rootSL2 .E7 Omega gamma).range ≤ H := by
    rw [range_rootSL2_of_isRoot hgamma]
    apply sup_le
    · exact le_iSup_of_le gamma (le_iSup_of_le hgPsi le_rfl)
    · exact le_iSup_of_le (-gamma) (le_iSup_of_le hngPsi le_rfl)
  have hAspan : (rootSL2 .E7 Omega gamma).range =
      rootSpan .E7 Omega {gamma, -gamma} := by
    rw [range_rootSL2_of_isRoot hgamma, rootSpan, iSup_insert, iSup_singleton]
  have hAconn : IsConnectedAlgebraicSubgroup Omega
      (((rootSL2 .E7 Omega gamma).range).map (modGLPoint .E7 Omega).toMonoidHom) := by
    rw [hAspan]
    exact isConnectedAlgebraicSubgroup_rootSpan _
  have hZconn := LieKnownR2.ExcPos.isConnectedAlgebraicSubgroup_e6_root_pair_stabilizer
    (Omega := Omega) w Psi hPsi gamma hgamma hgPsi
  rw [normalizer_rootSL2_inf_eq_sup_pair_stabilizer H hHA hgamma hAH]
  exact connected_sup _ _ hAconn hZconn


theorem exists_fixed_conj_of_connected_normalizer
    {tau : Tag} {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    (q : ℕ) (hq : 1 ≤ q) (Q : ModGL tau Omega)
    (H A B : Subgroup (ModGL tau Omega))
    (hFH : ∀ x ∈ H, frobTwistGL tau Omega 2 q Q x ∈ H)
    (hFA : A.map (frobTwistGL tau Omega 2 q Q) = A)
    (hFB : B.map (frobTwistGL tau Omega 2 q Q) = B)
    (hN : IsConnectedAlgebraicSubgroup Omega
      ((H ⊓ Subgroup.normalizer (A : Set _)).map (modGLPoint tau Omega).toMonoidHom))
    {g : ModGL tau Omega} (hg : g ∈ H)
    (hConj : A.map (MulAut.conj g).toMonoidHom = B) :
    ∃ u ∈ H, frobTwistGL tau Omega 2 q Q u = u ∧
      A.map (MulAut.conj u).toMonoidHom = B := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let F := frobTwistGL tau Omega 2 q Q
  have hFN : ∀ x ∈ H ⊓ Subgroup.normalizer (A : Set _), F x ∈
      H ⊓ Subgroup.normalizer (A : Set _) := by
    intro x hx
    refine ⟨hFH x hx.1, ?_⟩
    have h := Subgroup.le_normalizer_map F ⟨x, hx.2, rfl⟩
    rwa [hFA] at h
  obtain ⟨_, _, _, hLang⟩ := exists_frobTwist_restriction (τ := tau) 2 hN hq Q hFN
  have hLangPair : ∀ c ∈ H ⊓ Subgroup.normalizer (A : Set _) ⊓
      Subgroup.normalizer (A : Set _), ∃ z ∈ H ⊓ Subgroup.normalizer (A : Set _) ⊓
      Subgroup.normalizer (A : Set _), z⁻¹ * F z = c := by
    simpa only [inf_assoc, inf_idem] using hLang
  have hSame : A.map (MulAut.conj (F g)).toMonoidHom =
      A.map (MulAut.conj g).toMonoidHom := by
    calc
      A.map (MulAut.conj (F g)).toMonoidHom =
          (A.map F).map (MulAut.conj (F g)).toMonoidHom := by rw [hFA]
      _ = (A.map (MulAut.conj g).toMonoidHom).map F := (Subgroup.map_map_conj A F g).symm
      _ = B.map F := by rw [hConj]
      _ = B := hFB
      _ = A.map (MulAut.conj g).toMonoidHom := hConj.symm
  obtain ⟨u, hu, hFu, hAu, _⟩ :=
    F4ExplicitPos.AmbientPairDescent.exists_fixed_conj_eq_of_lang_pair F H A A hFH
      hLangPair hg hSame hSame
  exact ⟨u, hu, hFu, hAu.trans hConj⟩


end CFSG.StandardType.LieKnownR2.ExcPos
