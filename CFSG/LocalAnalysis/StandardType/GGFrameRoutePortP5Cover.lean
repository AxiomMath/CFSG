module

public import CFSG.Assembly.LargeEvenDefs
public import CFSG.GroupTheory.CommutatorLeSubgroupOf
public import CFSG.GroupTheory.InnerCentralizerProjection
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.Lift
public import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates
public import CFSG.RankThree.GroupTheory.SteinbergCESolvableLayerQuasisimple
public import CFSG.RankThree.PartOne.S11d.LieComponentLift
public import TauCeti.GroupTheory.FixedSubgroup
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.RankThree.GroupTheory.ThetaComponents
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Lemma83
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Cardinalities

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Assembly CFSG.RankThree.PartOne

open scoped commutatorElement

variable {G : Type} [Group G] {L : Subgroup G} {R : Type} [Group R]

@[expose] def coverMap (θ : ↥L ⧸ Subgroup.center ↥L ≃* R) : ↥L →* R :=
  θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))

@[expose] def coverComponent (θ : ↥L ⧸ Subgroup.center ↥L ≃* R) (J : Subgroup R) : Subgroup G :=
  (derivedPreimage (coverMap θ) J).map L.subtype

theorem coverMap_surjective (θ : ↥L ⧸ Subgroup.center ↥L ≃* R) :
    Function.Surjective (coverMap θ) :=
  θ.surjective.comp (QuotientGroup.mk'_surjective _)

theorem coverMap_ker (θ : ↥L ⧸ Subgroup.center ↥L ≃* R) :
    (coverMap θ).ker = Subgroup.center ↥L := by
  rw [coverMap, MonoidHom.ker_comp_of_injective _ _ θ.injective, QuotientGroup.ker_mk']

private def coverCentralizer (L : Subgroup G) (x z : G) : Subgroup G :=
  L ⊓ Subgroup.centralizer ((Subgroup.closure {x, z} : Subgroup G) : Set G)

private theorem coverMap_mem_fixedSubgroup (θ : ↥L ⧸ Subgroup.center ↥L ≃* R) {z : G}
    {φ : MulAut R} (hφ : LargeEvenInduces θ (fun l l' => (l' : G) = z⁻¹ * l * z) φ)
    {c : G} (hc : c ∈ L) (hcz : c ∈ Subgroup.centralizer ({z} : Set G)) :
    coverMap θ ⟨c, hc⟩ ∈ TauCeti.fixedSubgroup φ.toMonoidHom := by
  rw [TauCeti.mem_fixedSubgroup]
  have hzc : z * c = c * z := Subgroup.mem_centralizer_iff.mp hcz z (by simp)
  have hrel : ((⟨c, hc⟩ : ↥L) : G) = z⁻¹ * ((⟨c, hc⟩ : ↥L) : G) * z := by
    show c = z⁻¹ * c * z
    have h2 : z⁻¹ * c * z = c := by
      calc z⁻¹ * c * z = z⁻¹ * (c * z) := by group
        _ = z⁻¹ * (z * c) := by rw [← hzc]
        _ = c := by group
    exact h2.symm
  simpa [coverMap] using hφ ⟨c, hc⟩ ⟨c, hc⟩ hrel

private theorem commutator_subgroupOf_le_coverComponent (θ : ↥L ⧸ Subgroup.center ↥L ≃* R)
    {J : Subgroup R} {C : Subgroup G} :
    ⁅(C ⊓ (J.comap (coverMap θ)).map L.subtype).subgroupOf C,
        (C ⊓ (J.comap (coverMap θ)).map L.subtype).subgroupOf C⁆ ≤
      ((derivedPreimage (coverMap θ) J).map L.subtype).subgroupOf C := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [Subgroup.mem_subgroupOf]
  have haH : (a : G) ∈ (J.comap (coverMap θ)).map L.subtype :=
    (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp ha)).2
  have hbH : (b : G) ∈ (J.comap (coverMap θ)).map L.subtype :=
    (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hb)).2
  obtain ⟨aL, haL, haeq⟩ := Subgroup.mem_map.mp haH
  obtain ⟨bL, hbL, hbeq⟩ := Subgroup.mem_map.mp hbH
  refine Subgroup.mem_map.mpr ⟨⁅aL, bL⁆, Subgroup.commutator_mem_commutator haL hbL, ?_⟩
  rw [map_commutatorElement, haeq, hbeq]
  exact (map_commutatorElement C.subtype a b).symm

private theorem isSolvable_quotient_of_isSolvable_of_commutator_ker_le
    {X Y : Type*} [Group X] [Group Y] (φ : X →* Y) (hY : Group.IsSolvable Y)
    {N : Subgroup X} (hNn : N.Normal) (hN : N ≤ φ.ker)
    (hcomm : ⁅φ.ker, φ.ker⁆ ≤ N) :
    Group.IsSolvable (X ⧸ N) := by
  let M : Subgroup X := φ.ker
  have hNM : (N.subgroupOf M).Normal := hNn.subgroupOf M
  let f : ↥M ⧸ N.subgroupOf M →* X ⧸ N :=
    QuotientGroup.map (N.subgroupOf M) N M.subtype (by rw [Subgroup.subgroupOf])
  let g : X ⧸ N →* Y := QuotientGroup.lift N φ hN
  have hfr : f.range = M.map (QuotientGroup.mk' N) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (N.subgroupOf M) x
      change (QuotientGroup.map (N.subgroupOf M) N M.subtype _)
        (QuotientGroup.mk' (N.subgroupOf M) m) ∈ M.map (QuotientGroup.mk' N)
      rw [QuotientGroup.map_mk']
      exact Subgroup.mem_map.mpr ⟨m, m.2, rfl⟩
    · rintro ⟨m, hm, rfl⟩
      refine ⟨QuotientGroup.mk' (N.subgroupOf M) ⟨m, hm⟩, ?_⟩
      change (QuotientGroup.map (N.subgroupOf M) N M.subtype _)
        (QuotientGroup.mk' (N.subgroupOf M) _) = _
      rw [QuotientGroup.map_mk']
      rfl
  have hker : g.ker = M.map (QuotientGroup.mk' N) := QuotientGroup.ker_lift N φ hN
  have hsolM : Group.IsSolvable (↥M ⧸ N.subgroupOf M) :=
    @Group.instIsSolvableOfIsMulCommutative _ _
      (CFSG.GroupTheory.isMulCommutative_quotient_subgroupOf_of_commutator_le hcomm)
  exact Group.isSolvable_of_ker_le_range (G := X ⧸ N) f g (by rw [hker, hfr])

section Centralizer

variable (θ : ↥L ⧸ Subgroup.center ↥L ≃* R) {J : Subgroup R}

private theorem mem_centralizer_coverComponent_of_forall_fixes {b : G}
    (hb : b ∈ Subgroup.normalizer (L : Set G)) {ψ : MulAut R}
    (hψ : LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) ψ)
    (hfix : ∀ j ∈ J, ψ j = j) :
    b ∈ Subgroup.centralizer (coverComponent θ J : Set G) := by
  let π := coverMap θ
  let H : Subgroup ↥L := J.comap π
  let D : Subgroup ↥L := derivedPreimage π J
  let σ : MulAut ↥L := L.normalizerMonoidHom ⟨b⁻¹, (Subgroup.normalizer (L : Set G)).inv_mem hb⟩
  have hσ : ∀ h : ↥L, π (σ h) = ψ (π h) := by
    intro h
    refine (hψ h (σ h) ?_).symm
    change ((σ h : ↥L) : G) = b⁻¹ * (h : G) * b
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    simp
  have hcent : ∀ h ∈ H, σ h * h⁻¹ ∈ Subgroup.center ↥L := by
    intro h hh
    have hk : π (σ h * h⁻¹) = 1 := by
      rw [map_mul, map_inv, hσ, hfix (π h) hh]
      exact mul_inv_cancel _
    rw [← coverMap_ker θ, MonoidHom.mem_ker]
    exact hk
  have hDfix : ∀ d ∈ D, σ d = d :=
    CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.fixed_of_mem_commutator σ H hcent
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hy' : y ∈ (derivedPreimage π J).map L.subtype := by
    simpa [coverComponent, D, π] using hy
  obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hy'
  have hd' : σ d = d := hDfix d hd
  have hval : ((σ d : ↥L) : G) = b⁻¹ * (d : G) * b := by
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    simp
  rw [hd'] at hval
  have h1 : b * (d : G) = (d : G) * b := by
    calc b * (d : G) = b * (b⁻¹ * (d : G) * b) :=
          congrArg (fun x => b * x) hval
      _ = (d : G) * b := by group
  exact h1.symm

theorem mem_centralizer_coverComponent_iff (hJ : Group.IsPerfect ↥J) {b : G}
    (hb : b ∈ Subgroup.normalizer (L : Set G)) {ψ : MulAut R}
    (hψ : LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) ψ) :
    b ∈ Subgroup.centralizer (coverComponent θ J : Set G) ↔ ∀ j ∈ J, ψ j = j := by
  let π := coverMap θ
  let D : Subgroup ↥L := derivedPreimage π J
  have hπ : Function.Surjective π := coverMap_surjective θ
  constructor
  · intro hbc j hj
    have hmap : D.map π = J := map_derivedPreimage_of_perfect hπ hJ
    have hj' : j ∈ D.map π := by rw [hmap]; exact hj
    obtain ⟨d, hd, hdπ⟩ := Subgroup.mem_map.mp hj'
    have hbd : (d : G) * b = b * (d : G) :=
      Subgroup.mem_centralizer_iff.mp hbc (d : G) (Subgroup.mem_map.mpr ⟨d, hd, rfl⟩)
    have hrel : ((d : ↥L) : G) = b⁻¹ * ((d : ↥L) : G) * b := by
      have hconv : b⁻¹ * (d : G) * b = (d : G) := by
        calc b⁻¹ * (d : G) * b = b⁻¹ * ((d : G) * b) := by group
          _ = b⁻¹ * (b * (d : G)) := by rw [hbd]
          _ = (d : G) := by group
      exact hconv.symm
    rw [← hdπ]
    exact hψ d d hrel
  · intro hfix
    exact mem_centralizer_coverComponent_of_forall_fixes θ hb hψ hfix

end Centralizer

theorem isQuasisimple_coverComponent (θ : ↥L ⧸ Subgroup.center ↥L ≃* R) {J : Subgroup R}
    (hJ : CFSG.IsQuasisimple ↥J) : CFSG.IsQuasisimple ↥(coverComponent θ J) := by
  have hπ : Function.Surjective (coverMap θ) := coverMap_surjective θ
  have hker : (coverMap θ).ker ≤ Subgroup.center ↥L := (coverMap_ker θ).le
  have hq := isQuasisimple_derivedPreimage hπ hker hJ
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (Subgroup.equivMapOfInjective (derivedPreimage (coverMap θ) J) L.subtype
      L.subtype_injective) hq

section Component

variable (θ : ↥L ⧸ Subgroup.center ↥L ≃* R) {x z : G} {φ : MulAut R} {J : Subgroup R}

theorem coverComponent_le (hx : x ∈ Subgroup.centralizer (L : Set G))
    (hz : z ∈ Subgroup.normalizer (L : Set G))
    (hφ : LargeEvenInduces θ (fun l l' => (l' : G) = z⁻¹ * l * z) φ)
    (hJ : Group.IsPerfect ↥J) (hfix : J ≤ TauCeti.fixedSubgroup φ.toMonoidHom) :
    coverComponent θ J ≤
      L ⊓ Subgroup.centralizer ((Subgroup.closure {x, z} : Subgroup G) : Set G) := by
  refine le_inf (Subgroup.map_subtype_le _) ?_
  rw [Subgroup.le_centralizer_iff, Subgroup.closure_le]
  intro g hg
  rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl
  · exact Subgroup.centralizer_le (Subgroup.map_subtype_le _) hx
  · exact (mem_centralizer_coverComponent_iff θ hJ hz hφ).mpr fun j hj =>
      TauCeti.mem_fixedSubgroup.mp (hfix hj)

private theorem coverComponent_normal_subgroupOf (θ : ↥L ⧸ Subgroup.center ↥L ≃* R) {x z : G}
    {φ : MulAut R} {J : Subgroup R} (hx : x ∈ Subgroup.centralizer (L : Set G))
    (hz : z ∈ Subgroup.normalizer (L : Set G))
    (hφ : LargeEvenInduces θ (fun l l' => (l' : G) = z⁻¹ * l * z) φ)
    (hJ : Group.IsPerfect ↥J) (hfix : J ≤ TauCeti.fixedSubgroup φ.toMonoidHom)
    [(J.subgroupOf (TauCeti.fixedSubgroup φ.toMonoidHom)).Normal] :
    ((coverComponent θ J).subgroupOf (coverCentralizer L x z)).Normal := by
  let C := coverCentralizer L x z
  let H : Subgroup ↥L := J.comap (coverMap θ)
  let D : Subgroup ↥L := derivedPreimage (coverMap θ) J
  let J₁ : Subgroup G := coverComponent θ J
  have hJ₁C : J₁ ≤ C := coverComponent_le θ hx hz hφ hJ hfix
  rw [Subgroup.normal_subgroupOf_iff hJ₁C]
  intro y c hy hc
  have hcL : c ∈ L := hc.1
  have hcz : c ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    rw [hg]
    exact Subgroup.mem_centralizer_iff.mp hc.2 z (Subgroup.subset_closure (by simp))
  have hcK : coverMap θ ⟨c, hcL⟩ ∈ TauCeti.fixedSubgroup φ.toMonoidHom :=
    coverMap_mem_fixedSubgroup θ hφ hcL hcz
  let τ : MulAut ↥L := L.normalizerMonoidHom ⟨c, Subgroup.le_normalizer hcL⟩
  have hHmap : H.map τ.toMonoidHom ≤ H := by
    intro h' hh'
    obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.mp hh'
    change coverMap θ (τ h) ∈ J
    have hπh : coverMap θ h ∈ J := hh
    have hnorm := (Subgroup.normal_subgroupOf_iff hfix).mp
      (inferInstance : (J.subgroupOf (TauCeti.fixedSubgroup φ.toMonoidHom)).Normal)
      (coverMap θ h) (coverMap θ ⟨c, hcL⟩) hπh hcK
    have hτ : coverMap θ (τ h) =
        coverMap θ ⟨c, hcL⟩ * coverMap θ h * (coverMap θ ⟨c, hcL⟩)⁻¹ := by
      have hval : τ h = ⟨c, hcL⟩ * h * ⟨c, hcL⟩⁻¹ :=
        Subtype.ext (by rw [Subgroup.normalizerMonoidHom_apply_apply_coe]; rfl)
      rw [hval, map_mul, map_mul, map_inv]
    rw [hτ]
    exact hnorm
  have hDmap : D.map τ.toMonoidHom ≤ D := by
    rw [show D = ⁅H, H⁆ from rfl, Subgroup.map_commutator]
    exact Subgroup.commutator_mono hHmap hHmap
  have hy' : y ∈ (derivedPreimage (coverMap θ) J).map L.subtype := hy
  obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hy'
  refine Subgroup.mem_map.mpr ⟨τ d, hDmap (Subgroup.mem_map.mpr ⟨d, hd, rfl⟩), ?_⟩
  simp [τ, Subgroup.normalizerMonoidHom_apply_apply_coe]

private theorem coverComponent_subgroupOf_le_ker (θ : ↥L ⧸ Subgroup.center ↥L ≃* R)
    {J : Subgroup R} {C : Subgroup G} {K : Subgroup R} [(J.subgroupOf K).Normal]
    (φc : ↥C →* ↥K ⧸ J.subgroupOf K)
    (hker : φc.ker = (C ⊓ (J.comap (coverMap θ)).map L.subtype).subgroupOf C) :
    ((coverComponent θ J).subgroupOf C) ≤ φc.ker := by
  rw [hker]
  intro c hc
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  have hc' : (c : G) ∈ (derivedPreimage (coverMap θ) J).map L.subtype := by
    simpa [coverComponent] using Subgroup.mem_subgroupOf.mp hc
  obtain ⟨d, hd, hdc⟩ := Subgroup.mem_map.mp hc'
  exact ⟨c.2, Subgroup.mem_map.mpr
    ⟨d, derivedPreimage_le_comap (coverMap θ) J hd, hdc⟩⟩

private theorem commutator_ker_le_coverComponent (θ : ↥L ⧸ Subgroup.center ↥L ≃* R)
    {J : Subgroup R} {C : Subgroup G} {K : Subgroup R} [(J.subgroupOf K).Normal]
    (φc : ↥C →* ↥K ⧸ J.subgroupOf K)
    (hker : φc.ker = (C ⊓ (J.comap (coverMap θ)).map L.subtype).subgroupOf C) :
    ⁅φc.ker, φc.ker⁆ ≤ (coverComponent θ J).subgroupOf C := by
  rw [hker]
  exact commutator_subgroupOf_le_coverComponent θ

private theorem isSolvable_coverCentralizer_quotient (θ : ↥L ⧸ Subgroup.center ↥L ≃* R)
    {x z : G} {φ : MulAut R} {J : Subgroup R}
    (hφ : LargeEvenInduces θ (fun l l' => (l' : G) = z⁻¹ * l * z) φ)
    [(J.subgroupOf (TauCeti.fixedSubgroup φ.toMonoidHom)).Normal]
    (hnorm : ((coverComponent θ J).subgroupOf (coverCentralizer L x z)).Normal)
    (hsolv : IsSolvable (↥(TauCeti.fixedSubgroup φ.toMonoidHom) ⧸
      J.subgroupOf (TauCeti.fixedSubgroup φ.toMonoidHom))) :
    IsSolvable (↥(coverCentralizer L x z) ⧸
      (coverComponent θ J).subgroupOf (coverCentralizer L x z)) := by
  let C := coverCentralizer L x z
  let J₁ := coverComponent θ J
  let K := TauCeti.fixedSubgroup φ.toMonoidHom
  have hCL : C ≤ L := inf_le_left
  let fK : ↥C →* ↥K := ((coverMap θ).comp (Subgroup.inclusion hCL)).codRestrict K fun c => by
    have hcL : (c : G) ∈ L := c.2.1
    have hcz : (c : G) ∈ Subgroup.centralizer ({z} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      rw [hg]
      exact Subgroup.mem_centralizer_iff.mp c.2.2 z (Subgroup.subset_closure (by simp))
    have hsub : (⟨↑c, hcL⟩ : ↥L) = Subgroup.inclusion hCL c :=
      Subtype.ext (by rw [Subgroup.coe_inclusion])
    change coverMap θ (Subgroup.inclusion hCL c) ∈ K
    rw [← hsub]
    exact coverMap_mem_fixedSubgroup θ hφ hcL hcz
  let φc : ↥C →* ↥K ⧸ J.subgroupOf K := (QuotientGroup.mk' (J.subgroupOf K)).comp fK
  have hker : φc.ker = (C ⊓ (J.comap (coverMap θ)).map L.subtype).subgroupOf C := by
    ext c
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro hc
      have hc1 : fK c ∈ J.subgroupOf K := (QuotientGroup.eq_one_iff (fK c)).mp hc
      have hcJ : coverMap θ (Subgroup.inclusion hCL c) ∈ J := Subgroup.mem_subgroupOf.mp hc1
      refine ⟨c.2, Subgroup.mem_map.mpr ⟨⟨c, c.2.1⟩, hcJ, rfl⟩⟩
    · rintro ⟨-, hcH⟩
      obtain ⟨d, hd, hdc⟩ := Subgroup.mem_map.mp hcH
      have hcJ : coverMap θ (Subgroup.inclusion hCL c) ∈ J := by
        rw [show Subgroup.inclusion hCL c = d from Subtype.ext (by
          rw [Subgroup.coe_inclusion]; exact hdc.symm)]
        exact hd
      exact (QuotientGroup.eq_one_iff (fK c)).mpr
        (by simpa using (Subgroup.mem_subgroupOf.mpr hcJ))
  have hN : J₁.subgroupOf C ≤ φc.ker := coverComponent_subgroupOf_le_ker θ φc hker
  have hcomm : ⁅φc.ker, φc.ker⁆ ≤ J₁.subgroupOf C :=
    commutator_ker_le_coverComponent θ φc hker
  exact isSolvable_quotient_of_isSolvable_of_commutator_ker_le φc hsolv hnorm hN hcomm

theorem coverComponent_eq_layer (hx : x ∈ Subgroup.centralizer (L : Set G))
    (hz : z ∈ Subgroup.normalizer (L : Set G))
    (hφ : LargeEvenInduces θ (fun l l' => (l' : G) = z⁻¹ * l * z) φ)
    (hJ : CFSG.IsQuasisimple ↥J) (hfix : J ≤ TauCeti.fixedSubgroup φ.toMonoidHom)
    [(J.subgroupOf (TauCeti.fixedSubgroup φ.toMonoidHom)).Normal]
    (hsolv : IsSolvable (↥(TauCeti.fixedSubgroup φ.toMonoidHom) ⧸
      J.subgroupOf (TauCeti.fixedSubgroup φ.toMonoidHom))) :
    let C := L ⊓ Subgroup.centralizer ((Subgroup.closure {x, z} : Subgroup G) : Set G)
    coverComponent θ J = LargeEvenLayer C ∧ IsComponentOf (coverComponent θ J) C ∧
      ((coverComponent θ J).subgroupOf C).Normal ∧
      ∀ _ : ((coverComponent θ J).subgroupOf C).Normal,
        IsSolvable (↥C ⧸ (coverComponent θ J).subgroupOf C) := by
  let C : Subgroup G := coverCentralizer L x z
  let J₁ : Subgroup G := coverComponent θ J
  change J₁ = LargeEvenLayer C ∧ IsComponentOf J₁ C ∧
    (J₁.subgroupOf C).Normal ∧
    ∀ _ : (J₁.subgroupOf C).Normal, IsSolvable (↥C ⧸ J₁.subgroupOf C)
  have hJ₁C : J₁ ≤ C := coverComponent_le θ hx hz hφ hJ.1 hfix
  have hnorm : (J₁.subgroupOf C).Normal :=
    coverComponent_normal_subgroupOf θ hx hz hφ hJ.1 hfix
  have hsolvC : IsSolvable (↥C ⧸ J₁.subgroupOf C) :=
    isSolvable_coverCentralizer_quotient θ hφ hnorm hsolv
  have hJcmp : IsComponentOf J₁ C :=
    ⟨hJ₁C, IsSubnormal.step hJ₁C hnorm (IsSubnormal.refl C),
      (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native ↥J₁).mpr
        (isQuasisimple_coverComponent θ hJ)⟩
  have hlayer_le : LargeEvenLayer C ≤ J₁ := by
    refine sSup_le fun K hK => ?_
    have hKperf : Group.IsPerfect ↥K := ⟨hK.2.2.1⟩
    have hKCperf : Group.IsPerfect ↥(K.subgroupOf C) :=
      Group.IsPerfect.ofSurjective (G := ↥K)
        (f := (Subgroup.subgroupOfEquivOfLe hK.1).symm.toMonoidHom) (MulEquiv.surjective _)
    exact CFSG.LocalCores.le_of_subgroupOf_le hK.1
      (CFSG.RankThree.GroupTheory.le_of_isPerfect_of_isSolvable_quotient hsolvC hKCperf)
  have hle_layer : J₁ ≤ LargeEvenLayer C := le_sSup hJcmp
  exact ⟨le_antisymm hle_layer hlayer_le, hJcmp, hnorm, fun _ => hsolvC⟩

end Component

end CFSG.StandardType.FrameRoute
