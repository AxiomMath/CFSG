module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.CharTwoTorusOn
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.CartanQuotientTools
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ConjClosureSimple
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846g
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22v
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21k
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20d
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.OrthBlocksComp
public import CFSG.GroupTheory.TPermutingTorus
public import CFSG.GroupTheory.ConjClosureCentralProduct
public import CFSG.GroupTheory.SylowCentralProduct
public import CFSG.GroupTheory.PermSylowTwo.Sym
public import CFSG.GroupTheory.HuppertProduct.Quotient
public import CFSG.Quasithin.Vol2.Ch12Sec6P31LieG
public import CFSG.LocalAnalysis.SteinbergCCSQTKTwoCoreQuotient
public import CFSG.HardMathSupport.Malle.OvergroupTransport.Transport
public import TauCeti.GroupTheory.PGroup
public import CFSG.Blueprint.LieModelAPI
public import CFSG.GroupTheory.ElemAbelianRank
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1517B

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.QuasithinUnique (IsSylowTwoOf)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem bar2_conj_equiv (L : Subgroup G) (g : G) :
    Nonempty (Bar2 L ≃* Bar2 (L.map (MulAut.conj g).toMonoidHom)) :=
  ⟨CFSG.LocalAnalysis.UniquenessCase.UC6S846.bar2Equiv
    (L.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective)⟩

theorem mem_calC_of_mem_conjSetOf_of_calC {D : Data G} {L X : Subgroup G}
    (hL : L ∈ calC D.M) (hX : X = conjClosure D.M L)
    {K : Subgroup G} (hK : K ∈ UC22.conjSetOf D.M L) : K ∈ calC X := by
  subst hX
  exact (conjSetOf_subset_calC_conjClosure hL).2.2 K hK

theorem iSup_conjSubgroup_eq_of_calC {D : Data G} {L X : Subgroup G}
    (hX : X = conjClosure D.M L) :
    (⨆ g : ↥D.M, L.map (MulAut.conj (g : G)).toMonoidHom) = X := by
  rw [hX, UC22.uc22br4_conjClosure_eq]

theorem iSup_barImage_conj_eq_top_of_calC {D : Data G} {L X : Subgroup G}
    (hX : X = conjClosure D.M L) :
    (⨆ g : ↥D.M, barImage X (L.map (MulAut.conj (g : G)).toMonoidHom)) = ⊤ := by
  have hsub : (⨆ g : ↥D.M,
      (L.map (MulAut.conj (g : G)).toMonoidHom).subgroupOf X) = ⊤ := by
    have h1 : ∀ g : ↥D.M, Subgroup.map X.subtype
          ((L.map (MulAut.conj (g : G)).toMonoidHom).subgroupOf X) =
          L.map (MulAut.conj (g : G)).toMonoidHom :=
      fun g => Subgroup.map_subgroupOf_eq_of_le
        ((le_iSup _ g).trans (iSup_conjSubgroup_eq_of_calC hX).le)
    refine Subgroup.map_injective X.subtype_injective ?_
    rw [Subgroup.map_iSup, Subgroup.map_top, Subgroup.range_subtype]
    rw [show (⨆ g : ↥D.M, Subgroup.map X.subtype
          ((L.map (MulAut.conj (g : G)).toMonoidHom).subgroupOf X))
        = ⨆ g : ↥D.M, L.map (MulAut.conj (g : G)).toMonoidHom from iSup_congr h1]
    exact iSup_conjSubgroup_eq_of_calC hX
  calc (⨆ g : ↥D.M, barImage X (L.map (MulAut.conj (g : G)).toMonoidHom))
      = (⨆ g : ↥D.M, (L.map (MulAut.conj (g : G)).toMonoidHom).subgroupOf X).map
          (QuotientGroup.mk' (CFSG.pCore 2 ↥X)) := by
        rw [Subgroup.map_iSup]
        rfl
    _ = ⊤ := by
        rw [hsub, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]

theorem layer_bar2_eq_top_of_calC {D : Data G} {L X : Subgroup G}
    (hL : L ∈ calC D.M) (hX : X = conjClosure D.M L) :
    CFSG.layer (Bar2 X) = ⊤ := by
  have hcomp : ∀ g : ↥D.M,
      CFSG.IsComponent (barImage X (L.map (MulAut.conj (g : G)).toMonoidHom)) :=
    fun g => CFSG.LocalAnalysis.UniquenessCase.PartTwo.s13_barImage_isComponent
      (mem_calC_of_mem_conjSetOf_of_calC hL hX ⟨g, g.2, rfl⟩)
  have hgen := iSup_barImage_conj_eq_top_of_calC hX
  rw [eq_top_iff]
  calc ⊤ = ⨆ g : ↥D.M, barImage X (L.map (MulAut.conj (g : G)).toMonoidHom) := hgen.symm
    _ ≤ CFSG.layer (Bar2 X) := iSup_le fun g => CFSG.LocalCores.component_le_layer (hcomp g)

theorem exists_barImage_eq_of_isComponent_of_calC {D : Data G} {L X : Subgroup G}
    (hL : L ∈ calC D.M) (hX : X = conjClosure D.M L)
    {K : Subgroup (Bar2 X)} (hK : CFSG.IsComponent K) :
    ∃ g : ↥D.M, barImage X (L.map (MulAut.conj (g : G)).toMonoidHom) = K := by
  have htop := iSup_barImage_conj_eq_top_of_calC hX
  have hcomp : ∀ g : ↥D.M,
      CFSG.Open.IsComponentOf (barImage X (L.map (MulAut.conj (g : G)).toMonoidHom)) ⊤ :=
    fun g => (CFSG.isComponent_iff_open _).1
      (s13_barImage_isComponent (mem_calC_of_mem_conjSetOf_of_calC hL hX ⟨g, g.2, rfl⟩))
  have hle : K ≤ ⨆ g : ↥D.M, barImage X (L.map (MulAut.conj (g : G)).toMonoidHom) := by
    rw [htop]
    exact le_top
  exact CFSG.HardMathSupport.Dickson.Sec6.OrthBlocks.exists_eq_of_isComponentOf_le_iSup
    (N := ⊤) (fun g : ↥D.M => barImage X (L.map (MulAut.conj (g : G)).toMonoidHom))
    hcomp ((CFSG.isComponent_iff_open K).1 hK) hle

theorem barImage_injOn_cComp {D : Data G} {L X : Subgroup G}
    (hL : L ∈ calC D.M) (hX : X = conjClosure D.M L) :
    Set.InjOn (fun K => barImage X K) (CFSG.Quasithin.cComp X) := by
  classical
  intro K₁ hK₁ K₂ hK₂ heq
  have hsub₁ : K₁.subgroupOf X ∈ CFSG.Quasithin.cComp (⊤ : Subgroup ↥X) :=
    CFSG.Quasithin.subgroupOf_mem_cComp hK₁
  have hsub₂ : K₂.subgroupOf X ∈ CFSG.Quasithin.cComp (⊤ : Subgroup ↥X) :=
    CFSG.Quasithin.subgroupOf_mem_cComp hK₂
  have hbij := CFSG.Quasithin.cComp_quotient_bijOn (CFSG.pCore 2 ↥X)
    (uc22p20d_pCore_solvable X)
  have h1 : K₁.subgroupOf X = K₂.subgroupOf X := hbij.injOn hsub₁ hsub₂ heq
  have h2 : K₁ ⊓ X = K₂ ⊓ X := Subgroup.subgroupOf_inj.mp h1
  rwa [inf_eq_left.mpr (CFSG.Quasithin.le_of_mem_cComp hK₁),
    inf_eq_left.mpr (CFSG.Quasithin.le_of_mem_cComp hK₂)] at h2

theorem isMulCommutative_normalizerQuotient_bar2_of_calC_of_borel {D : Data G}
    {L X : Subgroup G} {n : ℕ} (hL : L ∈ calC D.M) (hX : X = conjClosure D.M L)
    (hB : Inputs1719.BorelChevOver (BarInf L) n)
    (S : Subgroup (Bar2 X)) (hS : IsSylowTwoOf S ⊤) :
    IsMulCommutative (TauCeti.Subgroup.normalizerQuotient S) := by
  classical
  obtain ⟨t, m, hLM, hKt⟩ := hB
  refine CFSG.GroupTheory.isMulCommutative_normalizerQuotient_of_layer_eq_top
    (layer_bar2_eq_top_of_calC hL hX) S ?_
  intro K
  obtain ⟨g, hg⟩ := exists_barImage_eq_of_isComponent_of_calC hL hX K.2
  obtain ⟨e1⟩ := s13_bar_equiv (M := X) (mem_calC_of_mem_conjSetOf_of_calC hL hX ⟨g, g.2, rfl⟩)
  obtain ⟨e2⟩ := bar2_conj_equiv L (g : G)
  let eK : ↥K.1 ≃* Bar2 L := (hg ▸ e1.symm).trans e2.symm
  obtain ⟨eBI⟩ := uc22p21k_barInf_equiv_of_calC (M := D.M) hL
  have hLM1 : CFSG.Blueprint.LieModel (Bar2 L ⧸ Subgroup.center (Bar2 L)) t m 2 n :=
    CFSG.Blueprint.LieModel.of_mulEquiv eBI hLM
  have hLM' : CFSG.Blueprint.LieModel (↥(K.1) ⧸ Subgroup.center ↥(K.1)) t m 2 n :=
    CFSG.Blueprint.LieModel.quotient_center_of_mulEquiv eK.symm hLM1
  have hsinf : IsSylowTwoOf (S ⊓ K.1) K.1 :=
    CFSG.QuasithinUnique.RankOneRecog.isSylowTwoOf_inf_of_subnormal hS le_top
      K.2.2.subgroupOf
  have hsyl : IsSylowTwoOf ((S ⊓ K.1).subgroupOf K.1) ⊤ :=
    CFSG.Quasithin.isSylowTwoOf_top_subgroupOf hsinf
  exact hKt ↥(K.1) hLM'
    (CFSG.Quasithin.A3.isQuasisimple_iff_open.mp K.2.1) ((S ⊓ K.1).subgroupOf K.1) hsyl

theorem isMulCommutative_normalizer_inf_quotient_of_calC_of_borel {D : Data G}
    {L X : Subgroup G} {n : ℕ} (hL : L ∈ calC D.M) (hX : X = conjClosure D.M L)
    (hB : Inputs1719.BorelChevOver (BarInf L) n) :
    IsMulCommutative (TauCeti.Subgroup.normalizerQuotient
      ((D.T ⊓ X).subgroupOf (X ⊓ normalizer ((D.T ⊓ X : Subgroup G) : Set G)))) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let H : Subgroup G := X ⊓ normalizer ((D.T ⊓ X : Subgroup G) : Set G)
  let SH : Subgroup ↥H := (D.T ⊓ X).subgroupOf H
  change IsMulCommutative (TauCeti.Subgroup.normalizerQuotient SH)
  have hXM : X ≤ D.M := by
    rw [hX]
    exact uc22p22v_conjClosure_le (Subgroup.le_normalizer (H := D.M)) hL.1.le
  have hMX : D.M ≤ normalizer (X : Set G) := by
    rw [hX]
    exact uc22p22v_le_normalizer_conjClosure D.M L
  have hSX : CFSG.ABGLocalTools.IsSylowOf 2 (D.T ⊓ X) X :=
    D.sylowM.inf_of_le_normalizer hXM hMX
  have hSylX : IsSylowTwoOf (D.T ⊓ X) X :=
    CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.mpr hSX
  let Sbar : Subgroup (Bar2 X) := barImage X (D.T ⊓ X)
  have hSbar_eq : Sbar = Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 ↥X))
      ((D.T ⊓ X).subgroupOf X) := rfl
  have hSylBar : IsSylowTwoOf Sbar ⊤ :=
    CFSG.Quasithin.H13.S126P31.isSylowTwoOf_map_mk' (Z := CFSG.pCore 2 ↥X)
      (CFSG.Quasithin.isSylowTwoOf_top_subgroupOf hSylX)
  have hbar : IsMulCommutative (TauCeti.Subgroup.normalizerQuotient Sbar) :=
    isMulCommutative_normalizerQuotient_bar2_of_calC_of_borel hL hX hB Sbar hSylBar
  have hHX : H ≤ X := inf_le_left
  have hHN : H ≤ normalizer ((D.T ⊓ X : Subgroup G) : Set G) := inf_le_right
  have hQleS : CFSG.pCore 2 ↥X ≤ (D.T ⊓ X).subgroupOf X :=
    CFSG.Quasithin.pCore_two_le_subgroupOf hSylX
  have hfwd : ∀ u : ↥H, ∀ x ∈ Sbar,
      (QuotientGroup.mk (Subgroup.inclusion hHX u) : Bar2 X) * x *
        (QuotientGroup.mk (Subgroup.inclusion hHX u) : Bar2 X)⁻¹ ∈ Sbar := by
    intro u x hx
    rw [hSbar_eq] at hx ⊢
    obtain ⟨s, hs, hsm⟩ := Subgroup.mem_map.mp hx
    have hsS : (s : G) ∈ D.T ⊓ X := Subgroup.mem_subgroupOf.mp hs
    have hconj : ((u : G) * (s : G) * (u : G)⁻¹) ∈ D.T ⊓ X :=
      (Subgroup.mem_normalizer_iff.mp (hHN u.2) (s : G)).mp hsS
    have hmemK : (Subgroup.inclusion hHX u * s * (Subgroup.inclusion hHX u)⁻¹) ∈
        (D.T ⊓ X).subgroupOf X := by
      rw [Subgroup.mem_subgroupOf]
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion] using hconj
    refine Subgroup.mem_map.mpr ⟨_, hmemK, ?_⟩
    rw [← hsm]
    change QuotientGroup.mk' (CFSG.pCore 2 ↥X)
        (Subgroup.inclusion hHX u * s * (Subgroup.inclusion hHX u)⁻¹) =
      QuotientGroup.mk' (CFSG.pCore 2 ↥X) (Subgroup.inclusion hHX u) *
        QuotientGroup.mk' (CFSG.pCore 2 ↥X) s *
        (QuotientGroup.mk' (CFSG.pCore 2 ↥X) (Subgroup.inclusion hHX u))⁻¹
    simp only [map_mul, map_inv]
  have hnorm : ∀ u : ↥H,
      (QuotientGroup.mk (Subgroup.inclusion hHX u) : Bar2 X) ∈
        Subgroup.normalizer (Sbar : Set (Bar2 X)) := by
    intro u
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact hfwd u x
    · intro hx
      have hinv : (QuotientGroup.mk
          (Subgroup.inclusion hHX (⟨(u : G)⁻¹, H.inv_mem u.2⟩ : ↥H)) : Bar2 X) =
          (QuotientGroup.mk (Subgroup.inclusion hHX u) : Bar2 X)⁻¹ := by
        rw [show (⟨(u : G)⁻¹, H.inv_mem u.2⟩ : ↥H) = u⁻¹ from rfl]
        exact map_inv (QuotientGroup.mk' (CFSG.pCore 2 ↥X)) (Subgroup.inclusion hHX u)
      have h := hfwd (⟨(u : G)⁻¹, H.inv_mem u.2⟩ : ↥H)
        ((QuotientGroup.mk (Subgroup.inclusion hHX u) : Bar2 X) * x *
          (QuotientGroup.mk (Subgroup.inclusion hHX u) : Bar2 X)⁻¹) hx
      rw [hinv] at h
      have e : (QuotientGroup.mk (Subgroup.inclusion hHX u) : Bar2 X)⁻¹ *
          ((QuotientGroup.mk (Subgroup.inclusion hHX u) : Bar2 X) * x *
            (QuotientGroup.mk (Subgroup.inclusion hHX u) : Bar2 X)⁻¹) *
          ((QuotientGroup.mk (Subgroup.inclusion hHX u) : Bar2 X)⁻¹)⁻¹ = x := by group
      rwa [e] at h
  have hcommBar : ∀ u v : ↥H,
      ⁅(QuotientGroup.mk (Subgroup.inclusion hHX u) : Bar2 X),
        (QuotientGroup.mk (Subgroup.inclusion hHX v) : Bar2 X)⁆ ∈ Sbar :=
    fun u v => CFSG.GroupTheory.commutatorElement_mem_of_isMulCommutative_normalizerQuotient
      (P := Sbar) hbar (hnorm u) (hnorm v)
  have hcommS : ∀ u v : ↥H, ((⁅u, v⁆ : ↥H) : G) ∈ (D.T ⊓ X : Subgroup G) := by
    intro u v
    have h1 : (QuotientGroup.mk (Subgroup.inclusion hHX ⁅u, v⁆) : Bar2 X) ∈ Sbar := by
      have h2 := hcommBar u v
      have hφ : (QuotientGroup.mk (Subgroup.inclusion hHX ⁅u, v⁆) : Bar2 X) =
          ⁅(QuotientGroup.mk (Subgroup.inclusion hHX u) : Bar2 X),
            (QuotientGroup.mk (Subgroup.inclusion hHX v) : Bar2 X)⁆ := by
        rw [map_commutatorElement (Subgroup.inclusion hHX) u v]
        exact map_commutatorElement (QuotientGroup.mk' (CFSG.pCore 2 ↥X)) _ _
      rwa [hφ]
    rw [hSbar_eq] at h1
    obtain ⟨s, hs, hsm⟩ := Subgroup.mem_map.mp h1
    have hsS : (s : G) ∈ D.T ⊓ X := Subgroup.mem_subgroupOf.mp hs
    let cX : ↥X := ⟨((⁅u, v⁆ : ↥H) : G), hHX (⁅u, v⁆).2⟩
    have hsm' : (QuotientGroup.mk s : Bar2 X) = QuotientGroup.mk cX := hsm
    have hmem : s⁻¹ * cX ∈ CFSG.pCore 2 ↥X := (QuotientGroup.eq).mp hsm'
    have hmemS : ((s : G)⁻¹ * ((⁅u, v⁆ : ↥H) : G)) ∈ (D.T ⊓ X : Subgroup G) :=
      Subgroup.mem_subgroupOf.mp (hQleS hmem)
    have e : ((⁅u, v⁆ : ↥H) : G) =
        (s : G) * ((s : G)⁻¹ * ((⁅u, v⁆ : ↥H) : G)) := by group
    rw [e]
    exact (D.T ⊓ X).mul_mem hsS hmemS
  refine IsMulCommutative.of_comm fun x y => ?_
  obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective x
  obtain ⟨b, hb⟩ := QuotientGroup.mk_surjective y
  rw [← ha, ← hb, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
    Subgroup.mem_subgroupOf]
  have hdiv : ((a * b)⁻¹ * (b * a) : ↥(Subgroup.normalizer (SH : Set ↥H))) =
      ⁅(b : ↥(Subgroup.normalizer (SH : Set ↥H)))⁻¹,
        (a : ↥(Subgroup.normalizer (SH : Set ↥H)))⁻¹⁆ := by
    rw [commutatorElement_def]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev]
    group
  rw [hdiv]
  exact hcommS _ _

theorem odd_card_center_of_isComponent_of_layer_eq_top {Y : Type} [Group Y] [Finite Y]
    (hY : CFSG.layer Y = ⊤) (hO2 : CFSG.pCore 2 Y = ⊥)
    {K : Subgroup Y} (hK : CFSG.IsComponent K) :
    Odd (Nat.card ↥(Subgroup.center ↥K)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← Nat.not_even_iff_odd]
  intro heven
  have hdvd : 2 ∣ Nat.card ↥(Subgroup.center ↥K) := even_iff_two_dvd.mp heven
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  let zK : ↥K := (z : ↥(Subgroup.center ↥K))
  let zY : Y := (zK : Y)
  have hz1 : z ≠ 1 := by
    intro h
    rw [h] at hz
    simp at hz
  have hcen : ∀ w ∈ K, w * zY = zY * w := by
    intro w hw
    simpa using congrArg Subtype.val (Subgroup.mem_center_iff.mp z.2 (⟨w, hw⟩ : ↥K))
  have hcent := CFSG.WholeGroup.mem_centralizer_layer_of_mem_component hK zK.2 hcen
  rw [hY] at hcent
  have hcent' : zY ∈ Subgroup.center Y := by
    rw [← Subgroup.centralizer_univ]
    simpa using hcent
  have hle_center : Subgroup.zpowers zY ≤ Subgroup.center Y :=
    Subgroup.zpowers_le.mpr hcent'
  have hnorm : (Subgroup.zpowers zY).Normal := Subgroup.normal_of_le_center hle_center
  have hzY : orderOf zY = 2 := by
    have h1 : orderOf zY = orderOf zK := Subgroup.orderOf_coe (H := K) zK
    have h2 : orderOf zK = orderOf z := Subgroup.orderOf_coe (H := Subgroup.center ↥K) z
    rw [h1, h2, hz]
  have hp2 : IsPGroup 2 (Subgroup.zpowers zY) := by
    refine IsPGroup.iff_card.mpr ⟨1, ?_⟩
    rw [Nat.card_zpowers, hzY, pow_one]
  have hle : Subgroup.zpowers zY ≤ CFSG.pCore 2 Y :=
    le_sSup ⟨hnorm, hp2⟩
  rw [hO2] at hle
  have h1 : zY = 1 := by
    have := hle (Subgroup.mem_zpowers zY)
    simpa using this
  apply hz1
  exact Subtype.ext (Subtype.ext h1)

theorem odd_card_center_of_isComponent_bar2_of_calC {D : Data G} {L X : Subgroup G}
    (hL : L ∈ calC D.M) (hX : X = conjClosure D.M L)
    {K : Subgroup (Bar2 X)} (hK : CFSG.IsComponent K) :
    Odd (Nat.card ↥(Subgroup.center ↥K)) :=
  odd_card_center_of_isComponent_of_layer_eq_top (layer_bar2_eq_top_of_calC hL hX)
    (s13_pCore_bar_eq_bot X) hK

theorem barImage_inf_barImage_eq_of_calC {D : Data G} {L X : Subgroup G}
    (hL : L ∈ calC D.M) (hX : X = conjClosure D.M L) :
    barImage X (D.T ⊓ X) ⊓ barImage X L = barImage X (D.T ⊓ L) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXM : X ≤ D.M := by
    rw [hX]
    exact uc22p22v_conjClosure_le (Subgroup.le_normalizer (H := D.M)) hL.1.le
  have hMX : D.M ≤ normalizer (X : Set G) := by
    rw [hX]
    exact uc22p22v_le_normalizer_conjClosure D.M L
  have hSylX : IsSylowTwoOf (D.T ⊓ X) X :=
    CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.mpr
      (D.sylowM.inf_of_le_normalizer hXM hMX)
  have hQleS : CFSG.pCore 2 ↥X ≤ (D.T ⊓ X).subgroupOf X :=
    CFSG.Quasithin.pCore_two_le_subgroupOf hSylX
  apply le_antisymm
  · rintro z ⟨hzS, hzL⟩
    rw [barImage] at hzS hzL ⊢
    obtain ⟨s, hs, hsm⟩ := Subgroup.mem_map.mp hzS
    obtain ⟨l, hl, hlm⟩ := Subgroup.mem_map.mp hzL
    have hsT : (s : G) ∈ D.T := (Subgroup.mem_subgroupOf.mp hs).1
    have hlL : (l : G) ∈ L := Subgroup.mem_subgroupOf.mp hl
    have hq : (QuotientGroup.mk' (CFSG.pCore 2 ↥X)) (s * l⁻¹) = 1 := by
      rw [map_mul, map_inv, hsm, ← hlm, mul_inv_cancel]
    have hk : s * l⁻¹ ∈ CFSG.pCore 2 ↥X := (QuotientGroup.eq_one_iff _).mp hq
    have hkT : ((s * l⁻¹ : ↥X) : G) ∈ D.T :=
      (Subgroup.mem_subgroupOf.mp (hQleS hk)).1
    have hlT : (l : G) ∈ D.T := by
      have h1 : (l : G) = ((s * l⁻¹ : ↥X) : G)⁻¹ * (s : G) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [h1]
      exact D.T.mul_mem (D.T.inv_mem hkT) hsT
    exact Subgroup.mem_map.mpr ⟨l, Subgroup.mem_subgroupOf.mpr ⟨hlT, hlL⟩, hlm⟩
  · rintro z hz
    rw [barImage] at hz ⊢
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hz
    have hu' : (u : G) ∈ D.T ⊓ L := Subgroup.mem_subgroupOf.mp hu
    exact ⟨Subgroup.mem_map.mpr ⟨u, Subgroup.mem_subgroupOf.mpr ⟨hu'.1, u.2⟩, rfl⟩,
      Subgroup.mem_map.mpr ⟨u, Subgroup.mem_subgroupOf.mpr hu'.2, rfl⟩⟩

theorem cartan_le_normalizer_inf_T_of_calC {D : Data G} {L X C : Subgroup G}
    (hL : L ∈ calC D.M) (hX : X = conjClosure D.M L) (hC : CIsCartanOf D.T L C) :
    C ≤ Subgroup.normalizer ((D.T ⊓ X : Subgroup G) : Set G) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXM : X ≤ D.M := by
    rw [hX]
    exact uc22p22v_conjClosure_le (Subgroup.le_normalizer (H := D.M)) hL.1.le
  have hMX : D.M ≤ normalizer (X : Set G) := by
    rw [hX]
    exact uc22p22v_le_normalizer_conjClosure D.M L
  have hSylX : IsSylowTwoOf (D.T ⊓ X) X :=
    CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.mpr
      (D.sylowM.inf_of_le_normalizer hXM hMX)
  have hQleS : CFSG.pCore 2 ↥X ≤ (D.T ⊓ X).subgroupOf X :=
    CFSG.Quasithin.pCore_two_le_subgroupOf hSylX
  have hLX : L ≤ X := by
    rw [hX]
    exact uc22p22v_le_conjClosure D.M L
  have hCX : C ≤ X := hC.1.trans hLX
  have hSylBar : IsSylowTwoOf (barImage X (D.T ⊓ X)) ⊤ :=
    CFSG.Quasithin.H13.S126P31.isSylowTwoOf_map_mk' (Z := CFSG.pCore 2 ↥X)
      (CFSG.Quasithin.isSylowTwoOf_top_subgroupOf hSylX)
  have hjoin : (⨆ K : CFSG.LocalCores.ComponentIndex (Bar2 X), K.1) = ⊤ := by
    rw [← layer_bar2_eq_top_of_calC hL hX, CFSG.layer.eq_sSup]
    apply le_antisymm
    · exact iSup_le fun K => le_sSup K.2
    · refine sSup_le fun K hK => ?_
      exact le_iSup (fun K : CFSG.LocalCores.ComponentIndex (Bar2 X) => K.1) ⟨K, hK⟩
  have hLcalX : L ∈ calC X :=
    mem_calC_of_mem_conjSetOf_of_calC hL hX ⟨1, D.M.one_mem, by
      rw [map_one MulAut.conj]
      exact (Subgroup.map_id L).symm⟩
  let Lbar : Subgroup (Bar2 X) := barImage X L
  have hLcomp : CFSG.IsComponent Lbar := s13_barImage_isComponent hLcalX
  let R : Subgroup (Bar2 X) :=
    ⨆ (K : CFSG.LocalCores.ComponentIndex (Bar2 X)) (_ : K.1 ≠ Lbar), K.1
  have hRcomm : R ≤ Subgroup.centralizer (Lbar : Set (Bar2 X)) := by
    refine iSup₂_le fun K hK => ?_
    have hbot : ⁅K.1, Lbar⁆ = ⊥ := by
      rcases CFSG.LocalCores.distinct_components_commute hLcomp K.2 with h | h
      · exact absurd h.symm hK
      · rwa [Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
  have hjoinL : Lbar ⊔ R = ⨆ K : CFSG.LocalCores.ComponentIndex (Bar2 X), K.1 := by
    apply le_antisymm
    · refine sup_le (le_iSup (fun K : CFSG.LocalCores.ComponentIndex (Bar2 X) => K.1)
        ⟨Lbar, hLcomp⟩) ?_
      exact iSup₂_le fun K _ => le_iSup (fun K : CFSG.LocalCores.ComponentIndex (Bar2 X) => K.1) K
    · refine iSup_le fun K => ?_
      by_cases hK : K.1 = Lbar
      · rw [hK]
        exact le_sup_left
      · exact le_sup_of_le_right (le_iSup₂_of_le K hK le_rfl)
  have hoddInf : Odd (Nat.card ↥(Lbar ⊓ R)) := by
    have hZcenter : Odd (Nat.card ↥((Subgroup.center ↥Lbar).map Lbar.subtype)) := by
      rw [Subgroup.card_map_of_injective Lbar.subtype_injective]
      exact odd_card_center_of_isComponent_bar2_of_calC hL hX hLcomp
    have hle : Lbar ⊓ R ≤ (Subgroup.center ↥Lbar).map Lbar.subtype := by
      rintro x ⟨hxL, hxR⟩
      have hc : x ∈ Subgroup.centralizer (Lbar : Set (Bar2 X)) := hRcomm hxR
      exact ⟨⟨x, hxL⟩, Subgroup.mem_center_iff.mpr fun y =>
        Subtype.ext (Subgroup.mem_centralizer_iff.mp hc (y : Bar2 X) y.2), rfl⟩
    exact Odd.of_dvd_nat hZcenter (Subgroup.card_dvd_of_le hle)
  have hcomm : ∀ x ∈ Lbar, ∀ y ∈ R, x * y = y * x :=
    fun x hx y hy => Subgroup.mem_centralizer_iff.mp (hRcomm hy) x hx
  have hP : IsSylowTwoOf (barImage X (D.T ⊓ X)) (Lbar ⊔ R) := by
    rw [hjoinL, hjoin]
    exact hSylBar
  obtain ⟨hsplit, -, hP'⟩ := CFSG.GroupTheory.isSylowTwoOf_sup_inf_of_odd_inf hcomm hoddInf hP
  let π : ↥X →* Bar2 X := QuotientGroup.mk' (CFSG.pCore 2 ↥X)
  have hnormL : ∀ (c : G) (hc : c ∈ C), π ⟨c, hCX hc⟩ ∈
      Subgroup.normalizer ((barImage X (D.T ⊓ X) ⊓ Lbar : Subgroup (Bar2 X)) :
        Set (Bar2 X)) := by
    intro c hc
    have hKL : barImage X (D.T ⊓ X) ⊓ Lbar = barImage X (D.T ⊓ L) :=
      barImage_inf_barImage_eq_of_calC hL hX
    rw [hKL, Subgroup.mem_normalizer_iff_map_conj_eq]
    have hcomp : (MulAut.conj (π ⟨c, hCX hc⟩)).toMonoidHom.comp π =
        π.comp (MulAut.conj (⟨c, hCX hc⟩ : ↥X)).toMonoidHom := by
      ext x
      change MulAut.conj (π ⟨c, hCX hc⟩) (π x) = π (MulAut.conj (⟨c, hCX hc⟩ : ↥X) x)
      rw [MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]
    have hcN : (⟨c, hCX hc⟩ : ↥X) ∈ Subgroup.normalizer
        (((D.T ⊓ L).subgroupOf X : Subgroup ↥X) : Set ↥X) := by
      rw [Subgroup.mem_normalizer_iff]
      intro u
      constructor
      · intro hu
        rw [Subgroup.mem_subgroupOf] at hu ⊢
        exact (Subgroup.mem_normalizer_iff.mp (hC.2.2.1 hc) (u : G)).mp hu
      · intro hu
        rw [Subgroup.mem_subgroupOf] at hu ⊢
        exact (Subgroup.mem_normalizer_iff.mp (hC.2.2.1 hc) (u : G)).mpr hu
    have hnormU : (((D.T ⊓ L).subgroupOf X).map
        (MulAut.conj (⟨c, hCX hc⟩ : ↥X)).toMonoidHom) = (D.T ⊓ L).subgroupOf X :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hcN
    calc (barImage X (D.T ⊓ L)).map (MulAut.conj (π ⟨c, hCX hc⟩)).toMonoidHom
        = (((D.T ⊓ L).subgroupOf X).map
            ((MulAut.conj (π ⟨c, hCX hc⟩)).toMonoidHom.comp π)) := by
          rw [barImage, Subgroup.map_map]
      _ = (((D.T ⊓ L).subgroupOf X).map
            (π.comp (MulAut.conj (⟨c, hCX hc⟩ : ↥X)).toMonoidHom)) := by rw [hcomp]
      _ = ((((D.T ⊓ L).subgroupOf X).map
            (MulAut.conj (⟨c, hCX hc⟩ : ↥X)).toMonoidHom).map π) := by rw [Subgroup.map_map]
      _ = (((D.T ⊓ L).subgroupOf X).map π) := by rw [hnormU]
      _ = barImage X (D.T ⊓ L) := by rw [barImage]
  have hnormR : ∀ (c : G) (hc : c ∈ C), π ⟨c, hCX hc⟩ ∈
      Subgroup.normalizer ((barImage X (D.T ⊓ X) ⊓ R : Subgroup (Bar2 X)) :
        Set (Bar2 X)) := by
    intro c hc
    have hcbar : π ⟨c, hCX hc⟩ ∈ Lbar := by
      show π ⟨c, hCX hc⟩ ∈ barImage X L
      exact Subgroup.mem_map.mpr
        ⟨⟨c, hCX hc⟩, Subgroup.mem_subgroupOf.mpr (hC.1 hc), rfl⟩
    have hcl : π ⟨c, hCX hc⟩ ∈ Subgroup.centralizer (R : Set (Bar2 X)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (Subgroup.mem_centralizer_iff.mp (hRcomm hy) _ hcbar).symm
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact Subgroup.mem_centralizer_iff.mp hcl t ht.2
  have hnorm : ∀ (c : G) (hc : c ∈ C), π ⟨c, hCX hc⟩ ∈
      Subgroup.normalizer (barImage X (D.T ⊓ X) : Set (Bar2 X)) := by
    intro c hc
    rw [hsplit, Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hnormL c hc),
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hnormR c hc)]
  have hfwd : ∀ c ∈ C, ∀ s ∈ (D.T ⊓ X : Subgroup G),
      c * s * c⁻¹ ∈ (D.T ⊓ X : Subgroup G) := by
    intro c hc s hs
    have hsX : s ∈ X := hs.2
    have hcX : c ∈ X := hCX hc
    have hXc : (c * s * c⁻¹) ∈ X := X.mul_mem (X.mul_mem hcX hsX) (X.inv_mem hcX)
    let csX : ↥X := ⟨c * s * c⁻¹, hXc⟩
    have hmemS : π csX ∈ barImage X (D.T ⊓ X) := by
      have hsbar : π ⟨s, hsX⟩ ∈ barImage X (D.T ⊓ X) := by
        rw [barImage]
        exact Subgroup.mem_map.mpr ⟨⟨s, hsX⟩, Subgroup.mem_subgroupOf.mpr hs, rfl⟩
      have hconj := (Subgroup.mem_normalizer_iff.mp (hnorm c hc) (π ⟨s, hsX⟩)).mp hsbar
      have e : π csX = π ⟨c, hCX hc⟩ * π ⟨s, hsX⟩ * (π ⟨c, hCX hc⟩)⁻¹ := by
        rw [show csX = (⟨c, hCX hc⟩ : ↥X) * ⟨s, hsX⟩ * (⟨c, hCX hc⟩ : ↥X)⁻¹ from rfl]
        rw [map_mul, map_mul, map_inv]
      rwa [e]
    rw [barImage] at hmemS
    obtain ⟨w, hw, hwm⟩ := Subgroup.mem_map.mp hmemS
    have hwS : (w : G) ∈ D.T ⊓ X := Subgroup.mem_subgroupOf.mp hw
    have hq2 : π csX = π w := hwm.symm
    have hker : csX * w⁻¹ ∈ CFSG.pCore 2 ↥X := by
      have h1 : (QuotientGroup.mk' (CFSG.pCore 2 ↥X)) (csX * w⁻¹) = 1 := by
        rw [map_mul, map_inv, hq2]
        exact mul_inv_cancel _
      exact (QuotientGroup.eq_one_iff _).mp h1
    have hmem : ((csX * w⁻¹ : ↥X) : G) ∈ D.T ⊓ X :=
      Subgroup.mem_subgroupOf.mp (hQleS hker)
    have h2 : (c * s * c⁻¹ : G) = ((csX * w⁻¹ : ↥X) : G) * (w : G) := by
      simp only [csX, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [h2]
    exact (D.T ⊓ X).mul_mem hmem hwS
  intro c hc
  rw [Subgroup.mem_normalizer_iff]
  intro s
  constructor
  · exact fun hs => hfwd c hc s hs
  · intro hs
    have h := hfwd c⁻¹ (C.inv_mem hc) (c * s * c⁻¹) hs
    have e : (c : G)⁻¹ * (c * s * c⁻¹) * ((c : G)⁻¹)⁻¹ = s := by group
    rwa [e] at h

theorem exists_permuting_elemAbelian_of_calC_of_borel {D : Data G} {L X : Subgroup G} {n : ℕ}
    (hL : L ∈ calC D.M) (hX : X = conjClosure D.M L)
    (hB : Inputs1719.BorelChevOver (BarInf L) n)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) :
    ∃ E : Subgroup G, E ≤ X ⊓ normalizer ((D.T ⊓ X : Subgroup G) : Set G) ∧
      CFSG.Open.IsElemAbelian r E ∧ Permutes E D.T ∧
        CFSG.Open.pRank r (X ⊓ normalizer ((D.T ⊓ X : Subgroup G) : Set G)) ≤
          CFSG.Open.pRank r E := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S : Subgroup G := D.T ⊓ X
  let B : Subgroup G := X ⊓ normalizer (S : Set G)
  have hXM : X ≤ D.M := by
    rw [hX]
    exact uc22p22v_conjClosure_le (Subgroup.le_normalizer (H := D.M)) hL.1.le
  have hMX : D.M ≤ normalizer (X : Set G) := by
    rw [hX]
    exact uc22p22v_le_normalizer_conjClosure D.M L
  have hTM : D.T ≤ D.M := (CFSG.ABGLocalTools.isSylowOf_iff.mp D.sylowM).1
  have hTX : D.T ≤ Subgroup.normalizer (X : Set G) := hTM.trans hMX
  have hSylX : IsSylowTwoOf S X :=
    CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.mpr
      (D.sylowM.inf_of_le_normalizer hXM hMX)
  have hTS : D.T ≤ Subgroup.normalizer (S : Set G) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨hyT, hyX⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer (H := D.T) ht) y).mp hyT,
        (Subgroup.mem_normalizer_iff.mp (hTX ht) y).mp hyX⟩
    · rintro ⟨hyT, hyX⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer (H := D.T) ht) y).mpr hyT,
        (Subgroup.mem_normalizer_iff.mp (hTX ht) y).mpr hyX⟩
  have hTNN : D.T ≤ Subgroup.normalizer
      ((Subgroup.normalizer (S : Set G) : Subgroup G) : Set G) :=
    fun t ht => CFSG.ABGLocalTools.mem_normalizer_normalizer (hTS ht)
  have hTB : D.T ≤ Subgroup.normalizer (B : Set G) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨hyX, hyN⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp (hTX ht) y).mp hyX,
        (Subgroup.mem_normalizer_iff.mp (hTNN ht) y).mp hyN⟩
    · rintro ⟨hyX, hyN⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp (hTX ht) y).mpr hyX,
        (Subgroup.mem_normalizer_iff.mp (hTNN ht) y).mpr hyN⟩
  have hSB : S ≤ B := le_inf inf_le_right Subgroup.le_normalizer
  have hST : S ≤ D.T := inf_le_left
  have hnormSB : (S.subgroupOf B).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hSB).mpr inf_le_right
  have hcomm2 : IsMulCommutative
      (TauCeti.Subgroup.normalizerQuotient (S.subgroupOf B)) :=
    isMulCommutative_normalizer_inf_quotient_of_calC_of_borel hL hX hB
  haveI : (S.subgroupOf B).Normal := hnormSB
  have hab : ∀ a b : B ⧸ S.subgroupOf B, a * b = b * a := by
    intro a b
    let e : (B ⧸ S.subgroupOf B) ≃*
        TauCeti.Subgroup.normalizerQuotient (S.subgroupOf B) :=
      (TauCeti.Subgroup.normalizerQuotientEquivQuotientOfNormal (S.subgroupOf B)).symm
    refine e.injective ?_
    rw [map_mul, map_mul]
    exact hcomm2.is_comm.comm _ _
  obtain ⟨E, hEB, hEel, hEcard, hperm⟩ :=
    CFSG.GroupTheory.exists_elemAbelian_permutes_of_abelian_quotient (B := B) (S := S) (T := D.T)
      hab hSB hST hTB hTS hr hr2 hSylX.2.1
  refine ⟨E, hEB, hEel, hperm, ?_⟩
  have hcardE : Nat.card E = r ^ CFSG.Open.pRank r E :=
    CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian hr hEel
  have hpk : CFSG.Open.pRank r B = CFSG.Open.pRank r E := by
    refine Nat.pow_right_injective hr.two_le ?_
    show r ^ CFSG.Open.pRank r B = r ^ CFSG.Open.pRank r E
    rw [← hEcard, hcardE]
  exact hpk.le

theorem exists_permuting_elemAbelian_of_calC {D : Data G} {L X : Subgroup G} {n : ℕ}
    (hL : L ∈ calC D.M) (hX : X = conjClosure D.M L)
    (hchev : CIsChevOver (BarInf L) n)
    (hK3 : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.K_BorelTorusAbelian)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) :
    ∃ E : Subgroup G, E ≤ X ⊓ normalizer ((D.T ⊓ X : Subgroup G) : Set G) ∧
      CFSG.Open.IsElemAbelian r E ∧ Permutes E D.T ∧
        CFSG.Open.pRank r (X ⊓ normalizer ((D.T ⊓ X : Subgroup G) : Set G)) ≤
          CFSG.Open.pRank r E :=
  exists_permuting_elemAbelian_of_calC_of_borel hL hX
    (Inputs1719.BorelChevOver.of_chev hK3 hchev) hr hr2

theorem exists_permuting_elemAbelian_le_of_calC_of_borel {D : Data G} {L X C : Subgroup G}
    {n : ℕ} (hL : L ∈ calC D.M) (hX : X = conjClosure D.M L)
    (hB : Inputs1719.BorelChevOver (BarInf L) n)
    (hC : CIsCartanOf D.T L C)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) :
    ∃ E : Subgroup G, E ≤ X ⊓ normalizer ((D.T ⊓ X : Subgroup G) : Set G) ∧
      CFSG.Open.IsElemAbelian r E ∧ Permutes E D.T ∧
        CFSG.Open.pRank r C ≤ CFSG.Open.pRank r E := by
  have hLX : L ≤ X := by
    rw [hX]
    exact uc22p22v_le_conjClosure D.M L
  have hCB : C ≤ X ⊓ normalizer ((D.T ⊓ X : Subgroup G) : Set G) :=
    le_inf (hC.1.trans hLX) (cartan_le_normalizer_inf_T_of_calC hL hX hC)
  obtain ⟨E, hEB, hEel, hperm, hrank⟩ :=
    exists_permuting_elemAbelian_of_calC_of_borel hL hX hB hr hr2
  exact ⟨E, hEB, hEel, hperm,
    (CFSG.SectionRank.pRank_mono hr.one_lt hCB).trans hrank⟩

theorem conjSubgroup_cartan_le_borel {D : Data G} {L X C : Subgroup G}
    (hL : L ∈ calC D.M) (hX : X = conjClosure D.M L) (hC : CIsCartanOf D.T L C)
    {γ : G} (hγM : γ ∈ D.M)
    (hγN : γ ∈ Subgroup.normalizer ((D.T ⊓ X : Subgroup G) : Set G)) :
    CFSG.Quasithin.conjSubgroup C γ ≤
      X ⊓ normalizer ((D.T ⊓ X : Subgroup G) : Set G) := by
  classical
  have hXM : X ≤ D.M := by
    rw [hX]
    exact uc22p22v_conjClosure_le (Subgroup.le_normalizer (H := D.M)) hL.1.le
  have hMX : D.M ≤ normalizer (X : Set G) := by
    rw [hX]
    exact uc22p22v_le_normalizer_conjClosure D.M L
  have hLX : L ≤ X := by
    rw [hX]
    exact uc22p22v_le_conjClosure D.M L
  have hCX : C ≤ X := hC.1.trans hLX
  have hnormC : C ≤ Subgroup.normalizer ((D.T ⊓ X : Subgroup G) : Set G) :=
    cartan_le_normalizer_inf_T_of_calC hL hX hC
  refine le_inf ?_ ?_
  ·
    have hconjL : CFSG.Quasithin.conjSubgroup L γ ≤ X := by
      rw [hX, UC22.uc22br4_conjClosure_eq]
      exact le_iSup (fun g : ↥D.M => L.map (MulAut.conj (g : G)).toMonoidHom)
        ⟨γ⁻¹, D.M.inv_mem hγM⟩
    exact (Subgroup.map_mono (f := (MulAut.conj γ⁻¹).toMonoidHom) hC.1).trans hconjL
  ·
    rintro _ ⟨c, hc, rfl⟩
    have hγinvNN : γ⁻¹ ∈ Subgroup.normalizer
        ((Subgroup.normalizer ((D.T ⊓ X : Subgroup G) : Set G) : Subgroup G) : Set G) :=
      (Subgroup.normalizer ((Subgroup.normalizer ((D.T ⊓ X : Subgroup G) : Set G) :
        Subgroup G) : Set G)).inv_mem
        (CFSG.ABGLocalTools.mem_normalizer_normalizer hγN)
    have hcN : (MulAut.conj γ⁻¹) c ∈ Subgroup.normalizer
        ((D.T ⊓ X : Subgroup G) : Set G) :=
      (Subgroup.mem_normalizer_iff.mp hγinvNN c).mp (hnormC hc)
    simpa [MulAut.conj_apply] using hcN

theorem normalizer_inf_component_le_normalizer_sylow {Y : Type} [Group Y] [Finite Y]
    {P : Subgroup Y} (hP : IsSylowTwoOf P ⊤)
    (hY : CFSG.layer Y = ⊤) (hO2 : CFSG.pCore 2 Y = ⊥)
    {K : Subgroup Y} (hK : CFSG.IsComponent K) :
    K ⊓ Subgroup.normalizer ((P ⊓ K : Subgroup Y) : Set Y) ≤
      Subgroup.normalizer (P : Set Y) := by
  classical
  let R : Subgroup Y :=
    ⨆ (K' : CFSG.LocalCores.ComponentIndex Y) (_ : K'.1 ≠ K), K'.1
  have hjoin : K ⊔ R = ⊤ := by
    rw [← hY, CFSG.layer.eq_sSup]
    apply le_antisymm
    · refine sup_le (le_sSup hK) ?_
      refine iSup₂_le fun K' _ => le_sSup K'.2
    · refine sSup_le fun K' hK' => ?_
      by_cases h : K' = K
      · rw [h]
        exact le_sup_left
      · exact le_sup_of_le_right (le_iSup₂_of_le ⟨K', hK'⟩ h le_rfl)
  have hRcomm : R ≤ Subgroup.centralizer (K : Set Y) := by
    refine iSup₂_le fun K' hK' => ?_
    rcases CFSG.LocalCores.distinct_components_commute K'.2 hK with h | h
    · exact absurd h hK'
    · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
  have hcomm : ∀ x ∈ K, ∀ y ∈ R, x * y = y * x := by
    intro x hx y hy
    exact Subgroup.mem_centralizer_iff.mp (hRcomm hy) x hx
  have hodd : Odd (Nat.card ↥(K ⊓ R)) := by
    have hZcenter : Odd (Nat.card ↥((Subgroup.center ↥K).map K.subtype)) := by
      rw [Subgroup.card_map_of_injective K.subtype_injective]
      exact odd_card_center_of_isComponent_of_layer_eq_top hY hO2 hK
    have hle : K ⊓ R ≤ (Subgroup.center ↥K).map K.subtype := by
      rintro x ⟨hxK, hxR⟩
      have hc : x ∈ Subgroup.centralizer (K : Set Y) := hRcomm hxR
      exact ⟨⟨x, hxK⟩, Subgroup.mem_center_iff.mpr fun y =>
        Subtype.ext (Subgroup.mem_centralizer_iff.mp hc (y : Y) y.2), rfl⟩
    exact Odd.of_dvd_nat hZcenter (Subgroup.card_dvd_of_le hle)
  have hP' : IsSylowTwoOf P (K ⊔ R) := by
    rw [hjoin]
    exact hP
  obtain ⟨hsplit, -, -⟩ := CFSG.GroupTheory.isSylowTwoOf_sup_inf_of_odd_inf hcomm hodd hP'
  have hcentR : K ≤ Subgroup.centralizer (R : Set Y) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.mem_centralizer_iff.mp (hRcomm hy) x hx).symm
  have hcentPR : Subgroup.centralizer (R : Set Y) ≤
      Subgroup.centralizer (P ⊓ R : Set Y) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro y hy
    exact hx y hy.2
  have hRN : K ⊓ Subgroup.normalizer ((P ⊓ K : Subgroup Y) : Set Y) ≤
      Subgroup.normalizer (P ⊓ R : Set Y) :=
    (inf_le_left.trans hcentR).trans
      (hcentPR.trans (Subgroup.centralizer_le_normalizer (P ⊓ R : Set Y)))
  have hKN : K ⊓ Subgroup.normalizer ((P ⊓ K : Subgroup Y) : Set Y) ≤
      Subgroup.normalizer (P ⊓ K : Set Y) := inf_le_right
  have h' : K ⊓ Subgroup.normalizer ((P ⊓ K : Subgroup Y) : Set Y) ≤
      Subgroup.normalizer (((P ⊓ K) ⊔ (P ⊓ R) : Subgroup Y) : Set Y) :=
    CFSG.GroupTheory.HuppertProduct.le_normalizer_sup hKN hRN
  rwa [← hsplit] at h'

theorem exists_elemAbelian_normalizer_of_isComponent {Y : Type} [Group Y] [Finite Y]
    {P : Subgroup Y} (hP : IsSylowTwoOf P ⊤)
    (hY : CFSG.layer Y = ⊤) (hO2 : CFSG.pCore 2 Y = ⊥)
    {K : Subgroup Y} (hK : CFSG.IsComponent K) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) :
    ∃ A : Subgroup Y, A ≤ K ⊓ Subgroup.normalizer (P : Set Y) ∧
      CFSG.Open.IsElemAbelian r A ∧
        CFSG.Open.pRank r (⊤ : Subgroup (TauCeti.Subgroup.normalizerQuotient
          ((P ⊓ K).subgroupOf K))) ≤ CFSG.Open.pRank r A := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsinf : IsSylowTwoOf (P ⊓ K) K :=
    CFSG.QuasithinUnique.RankOneRecog.isSylowTwoOf_inf_of_subnormal hP le_top
      hK.2.subgroupOf
  have hQ : IsSylowTwoOf ((P ⊓ K).subgroupOf K) ⊤ :=
    CFSG.Quasithin.isSylowTwoOf_top_subgroupOf hsinf
  let Q : Subgroup ↥K := (P ⊓ K).subgroupOf K
  let Nrm : Subgroup ↥K := Subgroup.normalizer (Q : Set ↥K)
  have hQ2 : IsPGroup 2 Q := hQ.2.1
  have hcopQ : ¬ r ∣ Nat.card Q := by
    obtain ⟨m, hm⟩ := hQ2.exists_card_eq
    rw [hm]
    intro hd
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow hd))
  have hq_eq : CFSG.Open.pRank r (⊤ : Subgroup (TauCeti.Subgroup.normalizerQuotient Q)) =
      CFSG.Open.pRank r (⊤ : Subgroup Nrm) :=
    CFSG.SectionRank.pRank_quotient_eq (Q.subgroupOf Nrm) (by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (show Q ≤ Nrm from Subgroup.le_normalizer)).toEquiv]
      exact hcopQ)
  obtain ⟨A₀, hA₀Nrm, hA₀el, hA₀card⟩ :=
    CFSG.SectionRank.exists_pRank hr.one_lt Nrm
  let A : Subgroup Y := A₀.map K.subtype
  have hAleK : A ≤ K := by
    rintro _ ⟨a, ha, rfl⟩
    exact a.2
  have hAleNrm : A ≤ Subgroup.normalizer ((P ⊓ K : Subgroup Y) : Set Y) := by
    refine (Subgroup.map_mono hA₀Nrm).trans ?_
    have h := Subgroup.le_normalizer_map (H := Q) K.subtype
    rwa [show Q.map K.subtype = P ⊓ K from
      Subgroup.map_subgroupOf_eq_of_le inf_le_right] at h
  have hAleN : A ≤ Subgroup.normalizer (P : Set Y) :=
    (le_inf hAleK hAleNrm).trans (normalizer_inf_component_le_normalizer_sylow hP hY hO2 hK)
  refine ⟨A, le_inf hAleK hAleN, CFSG.SectionRank.isElemAbelian_map hA₀el K.subtype, ?_⟩
  have hA₀rank : CFSG.Open.pRank r A₀ = CFSG.Open.pRank r Nrm := by
    refine Nat.pow_right_injective hr.two_le ?_
    show r ^ CFSG.Open.pRank r A₀ = r ^ CFSG.Open.pRank r Nrm
    rw [← CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian hr hA₀el, hA₀card]
  calc CFSG.Open.pRank r (⊤ : Subgroup (TauCeti.Subgroup.normalizerQuotient Q))
      = CFSG.Open.pRank r (⊤ : Subgroup Nrm) := hq_eq
    _ = CFSG.Open.pRank r Nrm := (CFSG.SectionRank.pRank_eq_pRank_top_subgroup Nrm).symm
    _ = CFSG.Open.pRank r A₀ := hA₀rank.symm
    _ ≤ CFSG.Open.pRank r A :=
        CFSG.SectionRank.pRank_le_map hr.one_lt K.subtype K.subtype_injective A₀

theorem exists_permuting_elemAbelian_noncyclic_of_calC_of_borel {D : Data G}
    {L X : Subgroup G} {n r : ℕ}
    (hL : L ∈ calC D.M) (hX : X = conjClosure D.M L)
    (hB : Inputs1719.BorelChevOver (BarInf L) n)
    (hnn : ¬ (L.subgroupOf D.M).Normal)
    (hZ : ¬ r ∣ Nat.card (Subgroup.center (Bar2 L)))
    (S : Subgroup (Bar2 L)) (hS : IsSylowTwoOf S ⊤)
    (hrank : 1 ≤ CFSG.Open.pRank r
      (⊤ : Subgroup (TauCeti.Subgroup.normalizerQuotient S)))
    (hr : r.Prime) (hr2 : r ≠ 2) :
    ∃ E : Subgroup G, E ≤ X ⊓ normalizer ((D.T ⊓ X : Subgroup G) : Set G) ∧
      CFSG.Open.IsElemAbelian r E ∧ Permutes E D.T ∧ 2 ≤ CFSG.Open.pRank r E := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnn' : ¬ D.M ≤ Subgroup.normalizer (L : Set G) := by
    intro h
    exact hnn ((Subgroup.normal_subgroupOf_iff_le_normalizer hL.1.le).2 h)
  have hex : ∃ g ∈ D.M, g ∉ Subgroup.normalizer (L : Set G) := by
    by_contra h
    exact hnn' (fun x hx => by
      by_contra hxN
      exact h ⟨x, hx, hxN⟩)
  obtain ⟨g, hgM, hgN⟩ := hex
  let Lg : Subgroup G := L.map (MulAut.conj g).toMonoidHom
  have hLg_ne : Lg ≠ L := by
    intro h
    exact hgN (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h)
  have hLcalX : L ∈ calC X :=
    mem_calC_of_mem_conjSetOf_of_calC hL hX ⟨1, D.M.one_mem, by
      rw [map_one MulAut.conj]
      exact (Subgroup.map_id L).symm⟩
  have hLgcalX : Lg ∈ calC X :=
    mem_calC_of_mem_conjSetOf_of_calC hL hX ⟨g, hgM, rfl⟩
  let K1 : Subgroup (Bar2 X) := barImage X L
  let K2 : Subgroup (Bar2 X) := barImage X Lg
  have hK1 : CFSG.IsComponent K1 := s13_barImage_isComponent hLcalX
  have hK2 : CFSG.IsComponent K2 := s13_barImage_isComponent hLgcalX
  have hKne : K1 ≠ K2 := by
    intro heq
    have hc1 : L ∈ CFSG.Quasithin.cComp X := uc22p20e_cComp_of_calC hLcalX
    have hc2 : Lg ∈ CFSG.Quasithin.cComp X := uc22p20e_cComp_of_calC hLgcalX
    exact hLg_ne ((barImage_injOn_cComp hL hX hc1 hc2 heq).symm)
  obtain ⟨e1⟩ : Nonempty (Bar2 L ≃* ↥K1) := s13_bar_equiv hLcalX
  obtain ⟨e2c⟩ := bar2_conj_equiv L g
  obtain ⟨e2b⟩ := s13_bar_equiv hLgcalX
  let e2 : Bar2 L ≃* ↥K2 := e2c.trans e2b
  have hZ1 : ¬ r ∣ Nat.card (Subgroup.center ↥K1) := by
    rw [← Nat.card_congr (Subgroup.centerCongr e1).toEquiv]
    exact hZ
  have hZ2 : ¬ r ∣ Nat.card (Subgroup.center ↥K2) := by
    rw [← Nat.card_congr (Subgroup.centerCongr e2).toEquiv]
    exact hZ
  have hXM : X ≤ D.M := by
    rw [hX]
    exact uc22p22v_conjClosure_le (Subgroup.le_normalizer (H := D.M)) hL.1.le
  have hMX : D.M ≤ normalizer (X : Set G) := by
    rw [hX]
    exact uc22p22v_le_normalizer_conjClosure D.M L
  let Sx : Subgroup G := D.T ⊓ X
  let Sbar : Subgroup (Bar2 X) := barImage X Sx
  have hSylX : IsSylowTwoOf Sx X :=
    CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.mpr
      (D.sylowM.inf_of_le_normalizer hXM hMX)
  have hSbar : IsSylowTwoOf Sbar ⊤ :=
    CFSG.Quasithin.H13.S126P31.isSylowTwoOf_map_mk' (Z := CFSG.pCore 2 ↥X)
      (CFSG.Quasithin.isSylowTwoOf_top_subgroupOf hSylX)
  have hlayer : CFSG.layer (Bar2 X) = ⊤ := layer_bar2_eq_top_of_calC hL hX
  have hO2 : CFSG.pCore 2 (Bar2 X) = ⊥ := s13_pCore_bar_eq_bot X
  obtain ⟨A1, hA1, hA1el, hA1rank⟩ :=
    exists_elemAbelian_normalizer_of_isComponent hSbar hlayer hO2 hK1 hr hr2
  obtain ⟨A2, hA2, hA2el, hA2rank⟩ :=
    exists_elemAbelian_normalizer_of_isComponent hSbar hlayer hO2 hK2 hr hr2
  let Q1 : Subgroup ↥K1 := (Sbar ⊓ K1).subgroupOf K1
  let Q2 : Subgroup ↥K2 := (Sbar ⊓ K2).subgroupOf K2
  have hQ1syl : IsSylowTwoOf Q1 ⊤ :=
    CFSG.Quasithin.isSylowTwoOf_top_subgroupOf
      (CFSG.QuasithinUnique.RankOneRecog.isSylowTwoOf_inf_of_subnormal hSbar le_top
        hK1.2.subgroupOf)
  have hQ2syl : IsSylowTwoOf Q2 ⊤ :=
    CFSG.Quasithin.isSylowTwoOf_top_subgroupOf
      (CFSG.QuasithinUnique.RankOneRecog.isSylowTwoOf_inf_of_subnormal hSbar le_top
        hK2.2.subgroupOf)
  have hq1 : 1 ≤ CFSG.Open.pRank r
      (⊤ : Subgroup (TauCeti.Subgroup.normalizerQuotient Q1)) := by
    have hmap1 : IsSylowTwoOf (Q1.map (e1.symm : ↥K1 →* Bar2 L)) ⊤ := by
      simpa using CFSG.GroupTheory.PermSylowTwo.isSylowTwoOf_map_mulEquiv e1.symm hQ1syl
    obtain ⟨i1⟩ := Inputs1719.normalizerQuotient_equiv_of_isSylowTwoOf e1.symm hQ1syl hmap1
    obtain ⟨i2⟩ := Inputs1719.normalizerQuotient_equiv_of_isSylowTwoOf
      (MulEquiv.refl (Bar2 L)) hmap1 hS
    calc 1 ≤ CFSG.Open.pRank r
          (⊤ : Subgroup (TauCeti.Subgroup.normalizerQuotient S)) := hrank
      _ = CFSG.Open.pRank r (⊤ : Subgroup (TauCeti.Subgroup.normalizerQuotient
            (Q1.map (e1.symm : ↥K1 →* Bar2 L)))) :=
          (CFSG.SectionRank.pRank_top_eq_of_mulEquiv hr.one_lt i2).symm
      _ = CFSG.Open.pRank r
            (⊤ : Subgroup (TauCeti.Subgroup.normalizerQuotient Q1)) :=
          (CFSG.SectionRank.pRank_top_eq_of_mulEquiv hr.one_lt i1).symm
  have hq2 : 1 ≤ CFSG.Open.pRank r
      (⊤ : Subgroup (TauCeti.Subgroup.normalizerQuotient Q2)) := by
    have hmap2 : IsSylowTwoOf (Q2.map (e2.symm : ↥K2 →* Bar2 L)) ⊤ := by
      simpa using CFSG.GroupTheory.PermSylowTwo.isSylowTwoOf_map_mulEquiv e2.symm hQ2syl
    obtain ⟨i1⟩ := Inputs1719.normalizerQuotient_equiv_of_isSylowTwoOf e2.symm hQ2syl hmap2
    obtain ⟨i2⟩ := Inputs1719.normalizerQuotient_equiv_of_isSylowTwoOf
      (MulEquiv.refl (Bar2 L)) hmap2 hS
    calc 1 ≤ CFSG.Open.pRank r
          (⊤ : Subgroup (TauCeti.Subgroup.normalizerQuotient S)) := hrank
      _ = CFSG.Open.pRank r (⊤ : Subgroup (TauCeti.Subgroup.normalizerQuotient
            (Q2.map (e2.symm : ↥K2 →* Bar2 L)))) :=
          (CFSG.SectionRank.pRank_top_eq_of_mulEquiv hr.one_lt i2).symm
      _ = CFSG.Open.pRank r
            (⊤ : Subgroup (TauCeti.Subgroup.normalizerQuotient Q2)) :=
          (CFSG.SectionRank.pRank_top_eq_of_mulEquiv hr.one_lt i1).symm
  have hA1rank_ge : 1 ≤ CFSG.Open.pRank r A1 := hq1.trans hA1rank
  have hA2rank_ge : 1 ≤ CFSG.Open.pRank r A2 := hq2.trans hA2rank
  have hcommIdx : (⟨K1, hK1⟩ : CFSG.LocalCores.ComponentIndex (Bar2 X)) ≠ ⟨K2, hK2⟩ := by
    intro h
    exact hKne (congrArg Subtype.val h)
  have hAcomm : ∀ a ∈ A1, ∀ b ∈ A2, a * b = b * a := by
    intro a ha b hb
    have haK1 : a ∈ K1 := (Subgroup.mem_inf.mp (hA1 ha)).1
    have hbK2 : b ∈ K2 := (Subgroup.mem_inf.mp (hA2 hb)).1
    exact (CFSG.LocalCores.componentIndex_commute hcommIdx a b haK1 hbK2).eq
  have hAdisj : A1 ⊓ A2 = ⊥ := by
    have hleCenter : A1 ⊓ A2 ≤ (Subgroup.center ↥K1).map K1.subtype := by
      rintro x ⟨hx1, hx2⟩
      have hxK1 : x ∈ K1 := (Subgroup.mem_inf.mp (hA1 hx1)).1
      have hxK2 : x ∈ K2 := (Subgroup.mem_inf.mp (hA2 hx2)).1
      refine Subgroup.mem_map.mpr ⟨⟨x, hxK1⟩, ?_, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro y
      have hyK1 : (y : Bar2 X) ∈ K1 := y.2
      exact Subtype.ext (by
        simpa using
          (CFSG.LocalCores.componentIndex_commute (Ne.symm hcommIdx) x y hxK2 hyK1).eq.symm)
    have hZcard : ¬ r ∣ Nat.card ((Subgroup.center ↥K1).map K1.subtype) := by
      rw [Subgroup.card_map_of_injective K1.subtype_injective]
      exact hZ1
    have hEA : IsPGroup r ↥(A1 ⊓ A2) := hA1el.isPGroup.to_inf_left
    have hdisj := TauCeti.disjoint_of_not_dvd_natCard_of_isPGroup hZcard hEA
    have hle' : A1 ⊓ A2 ≤ (A1 ⊓ A2) ⊓ (Subgroup.center ↥K1).map K1.subtype :=
      le_inf le_rfl hleCenter
    exact le_bot_iff.mp (hle'.trans (le_of_eq (disjoint_iff.mp hdisj.symm)))
  have hsum := CFSG.LocalAnalysis.RankThreeUC.S15.pRank_add_le_pRank_sup_of_commute
    hr hAcomm hAdisj
  have h2N : 2 ≤ CFSG.Open.pRank r
      (Subgroup.normalizer (Sbar : Set (Bar2 X))) := by
    have hmono : CFSG.Open.pRank r (A1 ⊔ A2) ≤
        CFSG.Open.pRank r (Subgroup.normalizer (Sbar : Set (Bar2 X))) :=
      CFSG.SectionRank.pRank_mono hr.one_lt
        (sup_le (hA1.trans inf_le_right) (hA2.trans inf_le_right))
    omega
  let B : Subgroup G := X ⊓ normalizer ((D.T ⊓ X : Subgroup G) : Set G)
  have hBrank : 2 ≤ CFSG.Open.pRank r B := by
    let π : ↥X →* Bar2 X := QuotientGroup.mk' (CFSG.pCore 2 ↥X)
    let SX : Subgroup ↥X := Sx.subgroupOf X
    have hSXbar : SX.map π = Sbar := rfl
    have hQleS : CFSG.pCore 2 ↥X ≤ SX :=
      CFSG.Quasithin.pCore_two_le_subgroupOf hSylX
    have hcomap : Sbar.comap π = SX := by
      rw [show Sbar = SX.map π from rfl]
      exact Subgroup.comap_map_eq_self (by
        rw [show π.ker = CFSG.pCore 2 ↥X from QuotientGroup.ker_mk' _]
        exact hQleS)
    have hBsub : B.subgroupOf X = Subgroup.normalizer (SX : Set ↥X) := by
      ext x
      constructor
      · intro hx
        have hxB : (x : G) ∈ B := Subgroup.mem_subgroupOf.mp hx
        have hxN : (x : G) ∈ Subgroup.normalizer (Sx : Set G) :=
          (Subgroup.mem_inf.mp hxB).2
        rw [Subgroup.mem_normalizer_iff]
        intro y
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
        exact Subgroup.mem_normalizer_iff.mp hxN (y : G)
      · intro hxN
        rw [Subgroup.mem_subgroupOf]
        refine Subgroup.mem_inf.mpr ⟨x.2, ?_⟩
        rw [Subgroup.mem_normalizer_iff]
        intro y
        constructor
        · intro hy
          have hyX : y ∈ X := hy.2
          have h := (Subgroup.mem_normalizer_iff.mp hxN ⟨y, hyX⟩).mp
            (Subgroup.mem_subgroupOf.mpr hy)
          rwa [Subgroup.mem_subgroupOf] at h
        · intro hy
          have hyX : y ∈ X := by
            have h1 : y = (x : G)⁻¹ * (x * y * (x : G)⁻¹) * x := by group
            rw [h1]
            exact X.mul_mem (X.mul_mem (X.inv_mem x.2) hy.2) x.2
          have h := (Subgroup.mem_normalizer_iff.mp hxN ⟨y, hyX⟩).mpr
            (Subgroup.mem_subgroupOf.mpr hy)
          rwa [Subgroup.mem_subgroupOf] at h
    have hmapnorm : (Subgroup.normalizer (SX : Set ↥X)).map π =
        Subgroup.normalizer (Sbar : Set (Bar2 X)) := by
      have h1 : (Subgroup.normalizer Sbar).comap π = Subgroup.normalizer (SX : Set ↥X) := by
        rw [← hcomap]
        exact Subgroup.comap_normalizer_eq_of_surjective Sbar
          (QuotientGroup.mk'_surjective _)
      rw [← h1]
      exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _
    have hBmap : (B.subgroupOf X).map π = Subgroup.normalizer (Sbar : Set (Bar2 X)) := by
      rw [hBsub, hmapnorm]
    have hcop : ¬ r ∣ Nat.card (CFSG.pCore 2 ↥X) :=
      CFSG.LocalAnalysis.SQTKTwoCoreQuotient.not_dvd_card_pCore_two hr hr2
    calc 2 ≤ CFSG.Open.pRank r (Subgroup.normalizer (Sbar : Set (Bar2 X))) := h2N
      _ = CFSG.Open.pRank r ((B.subgroupOf X).map π) := by rw [hBmap]
      _ = CFSG.Open.pRank r (B.subgroupOf X) :=
          CFSG.PreuniquenessRankFour.Helpers.pRank_quotient_map_of_coprime_normal
            (source := ↥X) r hr (CFSG.pCore 2 ↥X) hcop (B.subgroupOf X)
      _ = CFSG.Open.pRank r B :=
          CFSG.HardMathSupport.Malle.OvergroupTransport.pRank_subgroupOf r
            (show B ≤ X from inf_le_left)
  obtain ⟨E, hEB, hEel, hperm, hrankB⟩ :=
    exists_permuting_elemAbelian_of_calC_of_borel hL hX hB hr hr2
  exact ⟨E, hEB, hEel, hperm, hBrank.trans hrankB⟩

theorem exists_permuting_elemAbelian_noncyclic_of_calC {D : Data G} {L X : Subgroup G} {n r : ℕ}
    (hL : L ∈ calC D.M) (hX : X = conjClosure D.M L)
    (hchev : CIsChevOver (BarInf L) n)
    (hK3 : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.K_BorelTorusAbelian)
    (hnn : ¬ (L.subgroupOf D.M).Normal)
    (hZ : ¬ r ∣ Nat.card (Subgroup.center (Bar2 L)))
    (S : Subgroup (Bar2 L)) (hS : IsSylowTwoOf S ⊤)
    (hrank : 1 ≤ CFSG.Open.pRank r
      (⊤ : Subgroup (TauCeti.Subgroup.normalizerQuotient S)))
    (hr : r.Prime) (hr2 : r ≠ 2) :
    ∃ E : Subgroup G, E ≤ X ⊓ normalizer ((D.T ⊓ X : Subgroup G) : Set G) ∧
      CFSG.Open.IsElemAbelian r E ∧ Permutes E D.T ∧ 2 ≤ CFSG.Open.pRank r E :=
  exists_permuting_elemAbelian_noncyclic_of_calC_of_borel hL hX
    (Inputs1719.BorelChevOver.of_chev hK3 hchev) hnn hZ S hS hrank hr hr2

theorem iSup_conj_cartan_le_borel {D : Data G} {L X C : Subgroup G}
    (hL : L ∈ calC D.M) (hX : X = conjClosure D.M L) (hC : CIsCartanOf D.T L C)
    {Gamma : Set G}
    (hGamma : Gamma ⊆ D.M ⊓
      Subgroup.normalizer ((D.T ⊓ X : Subgroup G) : Set G)) :
    (⨆ γ ∈ Gamma, CFSG.Quasithin.conjSubgroup C γ) ≤
      X ⊓ Subgroup.normalizer ((D.T ⊓ X : Subgroup G) : Set G) := by
  refine iSup₂_le fun γ hγ => ?_
  exact conjSubgroup_cartan_le_borel hL hX hC (hGamma hγ).1 (hGamma hγ).2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
