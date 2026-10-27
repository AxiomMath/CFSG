module

public import CFSG.Quasithin.Background.VolII31Orbit

public section

namespace CFSG.Quasithin.VolI.I31

open CFSG.ComponentClassification CFSG.QuasithinUnique CFSG.QuasithinUnique.I32

theorem twoComponent_le_layer_of_isPGroup {G : Type} [Group G] [Finite G]
    (hcore : CFSG.Open.componentClassificationOddCore G = ⊥) {A : Subgroup G} (hA : IsPGroup 2 A)
    {C : Subgroup G} (hC : C = Subgroup.centralizer (A : Set G)) {Lc : Subgroup C}
    (hLc : TwoComponents.IsTwoComponent Lc) : Lc.map C.subtype ≤ Layer.subgroup G := by
  subst hC
  have h1 := (Subgroup.map_mono (le_sSup
    ((CatalogueBAlternating.pComponent_two_iff Lc).mpr hLc))).trans
    (CFSG.ClassicalInvolution.l2PrimeBalance G _ hA)
  rw [LocalBFailure.pLayer_two_eq_twoLayer,
    TwoLayerTransport.eq_layer_of_corefree hcore] at h1
  exact h1

section Main

local notation "𝒪(" X ")" => CFSG.Open.componentClassificationOddCore X

variable {X : Type} [Group X] [Finite X]

theorem abstract_I31 {P : Subgroup X} (hP : IsPGroup 2 P) {C : Subgroup X}
    (hC : C = Subgroup.centralizer (P : Set X)) {L : Subgroup X} (hLC : L ≤ C)
    (hL : TwoComponents.IsTwoComponent (L.subgroupOf C)) :
    ∃ J : Subgroup X, TwoComponents.IsTwoComponent J ∧ normalClosureLayer L = orbitSubP P J := by
  classical
  let π : X →* X ⧸ 𝒪(X) := QuotientGroup.mk' 𝒪(X)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective 𝒪(X)
  have hker : Odd (Nat.card π.ker) := by
    rw [show π.ker = 𝒪(X) from QuotientGroup.ker_mk' 𝒪(X)]
    exact OddCore.odd_card X
  have hcore : CFSG.Open.componentClassificationOddCore (X ⧸ 𝒪(X)) = ⊥ :=
    OddCore.quotient_corefree X
  let Pb : Subgroup (X ⧸ 𝒪(X)) := P.map π
  have hPb : IsPGroup 2 Pb := hP.map π
  let Cb : Subgroup (X ⧸ 𝒪(X)) := Subgroup.centralizer (Pb : Set (X ⧸ 𝒪(X)))
  have hCmap : C.map π = Cb := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : Fact (IsPGroup 2 P) := ⟨hP⟩
    rw [hC]
    exact Eq.symm (CFSG.centralizer_map_quotient_eq_map_centralizer 2 P 𝒪(X) inferInstance
      (Nat.coprime_two_left.mpr (OddCore.odd_card X)))
  let φ : ↥C →* ↥Cb := (π.comp C.subtype).codRestrict Cb (fun c => by
    rw [← hCmap]
    exact Subgroup.mem_map_of_mem π c.2)
  have hφsurj : Function.Surjective φ := by
    intro y
    have hy : (y : X ⧸ 𝒪(X)) ∈ C.map π := by rw [hCmap]; exact y.2
    obtain ⟨c, hc, hcy⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨c, hc⟩, Subtype.ext hcy⟩
  have hφker : Odd (Nat.card φ.ker) := by
    have hkerEq : φ.ker = (π.domRestrict C).ker := by
      ext element
      change φ element = 1 ↔ π element.val = 1
      exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    rw [hkerEq]
    exact OddKernel.odd_card_restriction_kernel π hker C
  let L' : Subgroup ↥C := L.subgroupOf C
  let Lc : Subgroup ↥Cb := L'.map φ
  have hLc : TwoComponents.IsTwoComponent Lc :=
    OddKernelTwoComponents.image φ hφsurj hφker L' hL
  let Lb : Subgroup (X ⧸ 𝒪(X)) := Lc.map Cb.subtype
  have hLbπ : Lb = L.map π := by
    ext y
    constructor
    · rintro ⟨_, ⟨l, hl, rfl⟩, rfl⟩
      exact ⟨l.1, hl, rfl⟩
    · rintro ⟨l, hl, rfl⟩
      exact ⟨φ ⟨l, hLC hl⟩, ⟨⟨l, hLC hl⟩, hl, rfl⟩, rfl⟩
  have hlayer : Lb ≤ Layer.subgroup (X ⧸ 𝒪(X)) :=
    twoComponent_le_layer_of_isPGroup hcore hPb rfl hLc
  obtain ⟨Kb, hKb, hLbA⟩ := exists_component_orbitP_le (P := Pb) rfl hLc hlayer
  have hLbperf : ⁅Lb, Lb⁆ = Lb := by
    have : Group.IsPerfect ↥Lc := ⟨TwoComponents.perfect hLc⟩
    have : Group.IsPerfect ↥Lb := Group.IsPerfect.map Cb.subtype
    exact Subgroup.isPerfect_iff.mp this
  have hLbne : Lb ≠ ⊥ := by
    intro hbot
    have hLcbot : Lc = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective Lc Cb.subtype_injective).mp hbot
    have : Nontrivial ↥Lc := TwoComponents.nontrivial hLc
    exact (Subgroup.nontrivial_iff_ne_bot Lc).mp this hLcbot
  have hLbfix : Lb ≤ Subgroup.centralizer (Pb : Set (X ⧸ 𝒪(X))) := Subgroup.map_subtype_le Lc
  have hnc : (⨆ y ∈ Layer.subgroup (X ⧸ 𝒪(X)), CFSG.conjugate Lb y) = orbitSubP Pb Kb :=
    normalClosure_layer_eqP hKb hLbperf hLbne hLbfix hLbA
  have hKmap : (normalClosureLayer L).map π = orbitSubP Pb Kb := by
    rw [← hnc]
    apply le_antisymm
    · refine Subgroup.map_le_iff_le_comap.mpr (iSup₂_le fun g hg => ?_)
      rw [← Subgroup.map_le_iff_le_comap, map_conjugate, ← hLbπ]
      exact le_iSup₂_of_le (π g) hg le_rfl
    · refine iSup₂_le fun y hy => ?_
      obtain ⟨g, rfl⟩ := hπ y
      rw [hLbπ, ← map_conjugate]
      exact Subgroup.map_mono (le_iSup₂_of_le g hy le_rfl)
  have hKb2 : TwoComponents.IsTwoComponent Kb :=
    TwoLayerTransport.ordinary_isTwoComponent_of_corefree hcore Kb hKb
  obtain ⟨J, hJ, hJmap⟩ := OddKernelTwoComponents.exists_lift π hπ hker Kb hKb2
  have hconjTwo : ∀ (J₀ : Subgroup X) (g : X), TwoComponents.IsTwoComponent J₀ →
      TwoComponents.IsTwoComponent (CFSG.conjugate J₀ g) := fun J₀ g h =>
    (TwoComponentTransport.equiv_iff (MulAut.conj g⁻¹) J₀).mpr h
  have hJpmap : ∀ g : X, (CFSG.conjugate J g).map π = CFSG.conjugate Kb (π g) := fun g => by
    rw [map_conjugate, hJmap]
  have hNJ : ∀ p : X, ∀ g ∈ oddLayerOf X,
      g ∈ Subgroup.normalizer (CFSG.conjugate J p : Set X) := by
    intro p g hg
    rw [← BenderBranch.conjugate_eq_iff_mem_normalizer]
    refine OddKernelTwoComponents.lift_unique π hπ hker _ _
      (hconjTwo _ g (hconjTwo J p hJ)) (hconjTwo J p hJ) ?_
    rw [map_conjugate π (CFSG.conjugate J p) g, hJpmap]
    exact BenderBranch.conjugate_eq_iff_mem_normalizer.mpr
      (layer_le_normalizer (isComponentOf_conjugate hKb (π p)) hg)
  have hNA : ∀ g ∈ oddLayerOf X, g ∈ Subgroup.normalizer (orbitSubP P J : Set X) :=
    fun g hg => mem_normalizer_iSup fun p => mem_normalizer_iSup fun _ => hNJ p g hg
  have hAN : orbitSubP P J ≤ oddLayerOf X := by
    refine iSup₂_le fun p _ => Subgroup.map_le_iff_le_comap.mp ?_
    rw [hJpmap]
    exact Layer.component_le (isComponentOf_conjugate hKb (π p))
  have hAsub : CFSG.Open.IsSubnormal (orbitSubP P J) ⊤ := isSubnormal_of_le_normal hAN hNA
  have hAmap : (orbitSubP P J).map π = orbitSubP Pb Kb := by
    unfold orbitSubP
    rw [Subgroup.map_iSup]
    apply le_antisymm
    · refine iSup_le fun p => ?_
      rw [Subgroup.map_iSup]
      refine iSup_le fun hp => ?_
      rw [hJpmap]
      exact le_iSup₂_of_le (f := fun q (_ : q ∈ Pb) => CFSG.conjugate Kb q) (π p)
        (Subgroup.mem_map_of_mem π hp) le_rfl
    · refine iSup₂_le fun q hq => ?_
      obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hq
      refine le_iSup_of_le p ?_
      rw [Subgroup.map_iSup]
      exact le_iSup_of_le hp (hJpmap p).ge
  have hres : TwoResidual.subgroup ↥L = ⊤ :=
    ((TwoComponentTransport.subgroupOf_iff L C hLC).mp hL).2.1
  have hLA : L ≤ orbitSubP P J :=
    le_of_residual_eq_top_of_map_le π hπ hker L _ hres hAsub (by rw [hAmap, ← hLbπ]; exact hLbA)
  have hKA : normalClosureLayer L ≤ orbitSubP P J :=
    iSup₂_le fun g hg => conjugate_le_of_mem_normalizer hLA (hNA g hg)
  have hKconj : ∀ z ∈ oddLayerOf X,
      CFSG.conjugate (normalClosureLayer L) z ≤ normalClosureLayer L := by
    intro z hz
    unfold normalClosureLayer
    rw [conjugate_iSup]
    refine iSup_le fun g => ?_
    rw [conjugate_iSup]
    refine iSup_le fun hg => ?_
    rw [BenderBranch.conjugate_conjugate]
    exact le_iSup₂_of_le (g * z) (Subgroup.mul_mem _ hg hz) le_rfl
  have hKsub : CFSG.Open.IsSubnormal (normalClosureLayer L) ⊤ :=
    isSubnormal_of_le_normal (hKA.trans hAN) (le_normalizer_of_conjugate_le hKconj)
  have hAK : orbitSubP P J ≤ normalClosureLayer L := by
    refine iSup₂_le fun p hp => ?_
    refine TwoComponentSubnormal.le_of_odd_kernel_map_le π hπ hker _ _ (hconjTwo J p hJ) hKsub ?_
    rw [hJpmap, hKmap]
    exact conjugate_le_orbitSubP (Subgroup.mem_map_of_mem π hp)
  exact ⟨J, hJ, le_antisymm hKA hAK⟩

theorem isComponentOf_of_isTwoComponent {J : Subgroup X} (hJ : TwoComponents.IsTwoComponent J)
    (hJO : J ≤ Subgroup.centralizer (𝒪(X) : Set X)) : CFSG.Open.IsComponentOf J ⊤ := by
  refine ⟨le_top, hJ.1, ?_⟩
  have hperf : Group.IsPerfect ↥J := ⟨TwoComponents.perfect hJ⟩
  have hq : CFSG.IsQuasisimple (↥J ⧸ CFSG.Open.componentClassificationOddCore ↥J) :=
    CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr (TwoComponents.quasisimple_quotient hJ)
  have hker : (QuotientGroup.mk' (CFSG.Open.componentClassificationOddCore ↥J)).ker ≤
      Subgroup.center ↥J := by
    rw [QuotientGroup.ker_mk', OddCore.subnormal_intersection J hJ.1]
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp (hJO y.2) _ hx).symm
  exact CFSG.Quasithin.A3.isQuasisimple_iff_open.mp
    ((CFSG.LocalCores.isQuasisimple_iff_of_surjective hperf _
      (QuotientGroup.mk'_surjective _) hker).mpr hq)

theorem abstract_I31_component {P : Subgroup X} (hP : IsPGroup 2 P) {C : Subgroup X}
    (hC : C = Subgroup.centralizer (P : Set X)) {L : Subgroup X} (hLC : L ≤ C)
    (hL : TwoComponents.IsTwoComponent (L.subgroupOf C))
    (hLO : L ≤ Subgroup.centralizer (𝒪(X) : Set X)) :
    ∃ J : Subgroup X, CFSG.Open.IsComponentOf J ⊤ ∧ L ≤ orbitSubP P J := by
  obtain ⟨J, hJ, hKJ⟩ := abstract_I31 hP hC hLC hL
  have hLK : L ≤ normalClosureLayer L := by
    unfold normalClosureLayer
    exact le_iSup₂_of_le (1 : X) (Subgroup.one_mem _) (BenderBranch.conjugate_one L).ge
  have hKO : normalClosureLayer L ≤ Subgroup.centralizer (𝒪(X) : Set X) :=
    iSup₂_le fun g _ => conjugate_le_of_mem_normalizer hLO
      (Subgroup.le_normalizer_of_normal (K := ⊤) (Subgroup.mem_top g))
  have hJO : J ≤ Subgroup.centralizer (𝒪(X) : Set X) :=
    ((le_orbitSubP P J).trans hKJ.ge).trans hKO
  exact ⟨J, isComponentOf_of_isTwoComponent hJ hJO, hLK.trans hKJ.le⟩

end Main

section Ambient

variable {G : Type} [Group G] [Finite G]

theorem as_I_3_1_one_two {H P L : Subgroup G} (hPH : P ≤ H) (hP : IsPGroup 2 P)
    (hL : Id2519.IsTwoComponentIn L (H ⊓ Subgroup.centralizer (P : Set G)))
    (hLO : L ≤ Subgroup.centralizer (QuasithinUnique.oddCoreIn H : Set G)) :
    ∃ K : Subgroup G, QuasithinUnique.IsComponentIn K H ∧
      L ≤ ⨆ (p : G) (_ : p ∈ P), CFSG.conjugate K p := by
  have hLZ : L ≤ H ⊓ Subgroup.centralizer (P : Set G) := CFSG.Quasithin.le_of_mem_cComp hL.1
  have hLH : L ≤ H := hLZ.trans inf_le_left
  let P' : Subgroup ↥H := P.subgroupOf H
  have hP' : IsPGroup 2 P' := hP.comap_of_injective H.subtype H.subtype_injective
  let C : Subgroup ↥H := (H ⊓ Subgroup.centralizer (P : Set G)).subgroupOf H
  have hC : C = Subgroup.centralizer (P' : Set ↥H) := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
      Subgroup.mem_centralizer_iff]
    constructor
    · rintro ⟨-, hx⟩ p hp
      exact Subtype.ext (hx p hp)
    · intro hx
      refine ⟨x.2, fun p hp => ?_⟩
      exact congrArg Subtype.val (hx ⟨p, hPH hp⟩ hp)
  let LX : Subgroup ↥H := L.subgroupOf H
  have hLX : LX.map H.subtype = L := Subgroup.map_subgroupOf_eq_of_le hLH
  have hLXC : LX ≤ C := fun x hx => hLZ hx
  have hLtwo : TwoComponents.IsTwoComponent (LX.subgroupOf C) := by
    let e : ↥C ≃* ↥(H ⊓ Subgroup.centralizer (P : Set G)) :=
      Subgroup.subgroupOfEquivOfLe inf_le_left
    have h1 := (I32.isTwoComponentIn_iff hLZ).mp hL
    have hmap : (LX.subgroupOf C).map e.toMonoidHom =
        L.subgroupOf (H ⊓ Subgroup.centralizer (P : Set G)) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        exact ⟨⟨⟨x.1, x.2.1⟩, x.2⟩, hx, rfl⟩
    exact (TwoComponentTransport.equiv_iff e _).mp (by rw [hmap]; exact h1)
  have hLXO : LX ≤ Subgroup.centralizer
      (CFSG.Open.componentClassificationOddCore ↥H : Set ↥H) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro o ho
    apply Subtype.ext
    have ho' : (o : G) ∈ QuasithinUnique.oddCoreIn H := Subgroup.mem_map.mpr ⟨o, ho, rfl⟩
    exact Subgroup.mem_centralizer_iff.mp (hLO hx) _ ho'
  obtain ⟨J, hJ, hLJ⟩ := abstract_I31_component hP' hC hLXC hLtwo hLXO
  refine ⟨J.map H.subtype, ⟨Subgroup.map_subtype_le J, ?_⟩, ?_⟩
  · have hJH : (J.map H.subtype).subgroupOf H = J :=
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective J
    rw [hJH]
    exact CFSG.Quasithin.A3.isComponentOf_top_iff.mp hJ
  · rw [← hLX]
    refine (Subgroup.map_mono hLJ).trans ?_
    unfold orbitSubP
    rw [Subgroup.map_iSup]
    refine iSup_le fun p => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hp => ?_
    rw [map_conjugate]
    exact le_iSup₂_of_le (f := fun (p : G) (_ : p ∈ P) => CFSG.conjugate (J.map H.subtype) p)
      (H.subtype p) hp le_rfl

end Ambient

end CFSG.Quasithin.VolI.I31
