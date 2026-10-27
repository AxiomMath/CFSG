module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8Bar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1FbSyl
public import CFSG.LargeExtraspecial.S5Two
public import CFSG.ClassicalGroups.PCoreSection
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.BarSubComponent
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22a
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod
public import CFSG.RankThree.PartTwo.Sec3.TwoThreeStructure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin (IsSylowIn)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LargeExtraspecial.S5 (IsSylowTwoIn)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace EighteenElevenTransport

variable {D : Data G} {V₀ V : Subgroup G} {L : Subgroup G}

theorem barSub_inf_isSylow (hV : IsElemAbelian 2 V) (hM : D.M ≤ stabTil V₀ V)
    (hT : IsSylowIn 2 D.T D.M) (hX : conjClosure D.M L ≤ D.M)
    (hXn : ((conjClosure D.M L).subgroupOf D.M).Normal) :
    IsSylowIn 2 (barSub V₀ V hV D.T ⊓ barSub V₀ V hV (conjClosure D.M L))
      (barSub V₀ V hV (conjClosure D.M L)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTsyl : IsSylowIn 2 (barSub V₀ V hV D.T) (barSub V₀ V hV D.M) :=
    s16c1_barSub_sylow hM hT
  have hXsub : CFSG.Open.IsSubnormal (conjClosure D.M L) D.M :=
    CFSG.Open.IsSubnormal.step hX hXn (CFSG.Open.IsSubnormal.refl D.M)
  have hXbarsub : CFSG.Open.IsSubnormal (barSub V₀ V hV (conjClosure D.M L))
      (barSub V₀ V hV D.M) :=
    TwelveTwentyThree.isSubnormal_barSub hV hXsub
  exact (show IsSylowTwoIn (barSub V₀ V hV D.T) (barSub V₀ V hV D.M) from hTsyl)
    |>.inf_of_isSubnormal hXbarsub

theorem barSub_inf_eq (hV : IsElemAbelian 2 V) (hM : D.M ≤ stabTil V₀ V)
    (hT : IsSylowIn 2 D.T D.M) (hX : conjClosure D.M L ≤ D.M)
    (hXn : ((conjClosure D.M L).subgroupOf D.M).Normal) :
    barSub V₀ V hV D.T ⊓ barSub V₀ V hV (conjClosure D.M L) =
      barSub V₀ V hV (D.T ⊓ conjClosure D.M L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXstab : conjClosure D.M L ≤ stabTil V₀ V := hX.trans hM
  have hSsyl : IsSylowIn 2 (D.T ⊓ conjClosure D.M L) (conjClosure D.M L) :=
    (CFSG.ABGLocalTools.isSylowOf_iff (p := 2)
      (P := D.T ⊓ conjClosure D.M L) (K := conjClosure D.M L)).mp
      (CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer D.sylowM hX
        (TwelveTwentyThree.le_normalizer_conjClosure D.M L))
  have hS0syl : IsSylowTwoIn (barSub V₀ V hV (D.T ⊓ conjClosure D.M L))
      (barSub V₀ V hV (conjClosure D.M L)) := by
    have hSsyl' : IsSylowTwoIn (D.T ⊓ conjClosure D.M L) (conjClosure D.M L) :=
      ⟨hSsyl.1, hSsyl.2.1, hSsyl.2.2⟩
    have hsub : IsSylowTwoIn ((D.T ⊓ conjClosure D.M L).subgroupOf (stabTil V₀ V))
        ((conjClosure D.M L).subgroupOf (stabTil V₀ V)) :=
      IsSylowTwoIn.subgroupOf hSsyl' hXstab
    have hmap := hsub.map (actTil V₀ V hV)
    simpa only [barSub] using hmap
  have hTsyl : IsSylowIn 2 (barSub V₀ V hV D.T) (barSub V₀ V hV D.M) :=
    s16c1_barSub_sylow hM hT
  have hXsub : CFSG.Open.IsSubnormal (conjClosure D.M L) D.M :=
    CFSG.Open.IsSubnormal.step hX hXn (CFSG.Open.IsSubnormal.refl D.M)
  have hXbarsub : CFSG.Open.IsSubnormal (barSub V₀ V hV (conjClosure D.M L))
      (barSub V₀ V hV D.M) :=
    TwelveTwentyThree.isSubnormal_barSub hV hXsub
  have hS1syl : IsSylowIn 2
      (barSub V₀ V hV D.T ⊓ barSub V₀ V hV (conjClosure D.M L))
      (barSub V₀ V hV (conjClosure D.M L)) :=
    barSub_inf_isSylow hV hM hT hX hXn
  have hle : barSub V₀ V hV (D.T ⊓ conjClosure D.M L) ≤
      barSub V₀ V hV D.T ⊓ barSub V₀ V hV (conjClosure D.M L) :=
    le_inf (barSub_mono V₀ V hV inf_le_left) (barSub_mono V₀ V hV inf_le_right)
  exact hS0syl.eq_of_le hle inf_le_right (show IsPGroup 2 _ from hS1syl.2.1)

theorem barSub_le_normalizer_barSub (D : Data G) {V₀ V : Subgroup G} {p : ℕ}
    {L : Subgroup G} (h : Hyp18 D V₀ V p L) :
    barSub V₀ V h.hyp125.isElemAbelian D.T ≤
      Subgroup.normalizer
        (barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L) : Set _) := by
  obtain ⟨hV, -, -, -, -, -, -⟩ := h.hyp125.pairFacts
  have hYX : ∀ y ∈ D.T, ∀ x ∈ conjClosure D.M L, y * x * y⁻¹ ∈ conjClosure D.M L :=
    fun y hy x hx =>
      (Subgroup.mem_normalizer_iff.1
        (TwelveTwentyThree.le_normalizer_conjClosure D.M L (D.sylowM.le hy)) x).1 hx
  intro g hg
  rw [Subgroup.mem_normalizer_iff'']
  intro y
  constructor
  · intro hy
    have h1 := c8_conj_mem_barSub V₀ V hV hYX (g⁻¹) (Subgroup.inv_mem _ hg) y hy
    simpa using h1
  · intro hy
    have h1 := c8_conj_mem_barSub V₀ V hV hYX g hg (g⁻¹ * y * g) hy
    have hEq : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
    rwa [hEq] at h1

end EighteenElevenTransport

theorem swapsParabolics_barSub_of_hyp18 (D : Data G) {V₀ V : Subgroup G} {p : ℕ}
    {L : Subgroup G} (h : Hyp18 D V₀ V p L) {n : ℕ}
    (hSp : IsSp4 ↥(barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) n)
    (hBar2 : IsSimpleGroup (Bar2 (conjClosure D.M L)))
    (hswap : S17.SwapsParabolics D.T (conjClosure D.M L)) :
    S17.SwapsParabolics (barSub V₀ V h.hyp125.isElemAbelian D.T)
      (barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hV, hV₀, hVle, hVM, hMnorm, hMnorm₀, hVne⟩ := h.hyp125.pairFacts
  set M := D.M with hMdef
  set T := D.T with hTdef
  set X := conjClosure D.M L with hXdef
  have hMstab : M ≤ stabTil V₀ V := le_stabTil hMnorm hMnorm₀
  have hXM : X ≤ M := TwelveTwentyThree.conjClosure_le h.hL.1.1.le
  have hTM : T ≤ M := D.sylowM.le
  have hXstab : X ≤ stabTil V₀ V := hXM.trans hMstab
  have hTstab : T ≤ stabTil V₀ V := hTM.trans hMstab
  have hXn : (X.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXM).mpr
      (TwelveTwentyThree.le_normalizer_conjClosure M L)
  have hTsyl : IsSylowIn 2 T M := CFSG.ABGLocalTools.isSylowOf_iff.mp D.sylowM
  have : IsSimpleGroup (Bar2 X) := hBar2
  have hXbarSimple : IsSimpleGroup ↥(barSub V₀ V hV X) :=
    (uc22p22a_sp4_simple _ n hSp).1
  have hXbar_ne : barSub V₀ V hV X ≠ ⊥ :=
    (Subgroup.nontrivial_iff_ne_bot _).mp hXbarSimple.toNontrivial
  let ψ : ↥X →* MulAut (Vtil V₀ V hV) :=
    (actTil V₀ V hV).comp (Subgroup.inclusion hXstab)
  have hψrange : ψ.range = barSub V₀ V hV X := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range, barSub]
  have hψmem : ∀ y ∈ barSub V₀ V hV X, ∃ x : ↥X, ψ x = y := by
    intro y hy
    rw [← hψrange] at hy
    exact MonoidHom.mem_range.mp hy
  have hO2Xbot : barSub V₀ V hV (pCoreOf 2 X) = ⊥ := by
    have hXsub : CFSG.Open.IsSubnormal X M := CFSG.Open.IsSubnormal.step hXM hXn
      (CFSG.Open.IsSubnormal.refl M)
    exact TwelveTwentyThree.barSub_pCoreOf_eq_bot_of_isSubnormal hV hXsub
      (barSub_pCoreOf_eq_bot_of_hyp125 h.hyp125)
  have hO2leKer : CFSG.pCore 2 ↥X ≤ ψ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    have hxP : (x : G) ∈ pCoreOf 2 X := by
      rw [← CFSG.openPCoreOf_subgroupOf 2 X] at hx
      exact Subgroup.mem_subgroupOf.mp hx
    have h1 : actTil V₀ V hV ⟨(x : G), hXstab x.2⟩ ∈ barSub V₀ V hV (pCoreOf 2 X) :=
      actTil_mem_barSub V₀ V hV hxP (hXstab x.2)
    rw [hO2Xbot, Subgroup.mem_bot] at h1
    exact h1
  let φ : Bar2 X →* MulAut (Vtil V₀ V hV) :=
    QuotientGroup.lift (CFSG.pCore 2 ↥X) ψ hO2leKer
  have hφq : ∀ x : ↥X, φ (QuotientGroup.mk x) = ψ x := fun x =>
    QuotientGroup.lift_mk (N := CFSG.pCore 2 ↥X) hO2leKer x
  have hφrange : φ.range = barSub V₀ V hV X := by
    rw [← hψrange]
    ext y
    constructor
    · rintro ⟨q, rfl⟩
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      exact ⟨x, hφq x⟩
    · rintro ⟨x, rfl⟩
      exact ⟨QuotientGroup.mk x, hφq x⟩
  have hφker : φ.ker = ⊥ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top φ.ker with h1 | h1
    · exact h1
    · exfalso
      have hbot : barSub V₀ V hV X = ⊥ := by
        rw [eq_bot_iff]
        intro y hy
        rw [← hφrange] at hy
        obtain ⟨q, rfl⟩ := hy
        have hq : q ∈ φ.ker := h1 ▸ Subgroup.mem_top q
        rw [MonoidHom.mem_ker] at hq
        rw [hq]
        exact Subgroup.one_mem _
      exact hXbar_ne hbot
  have hker : ψ.ker = (pCoreOf 2 X).subgroupOf X := by
    refine le_antisymm ?_ ?_
    · intro x hx
      have hφx : φ (QuotientGroup.mk x) = 1 := by
        rw [hφq x]
        exact hx
      have hq : QuotientGroup.mk x ∈ φ.ker := hφx
      rw [hφker] at hq
      have hxO2 : x ∈ CFSG.pCore 2 ↥X := (QuotientGroup.eq_one_iff _).mp hq
      rw [CFSG.openPCoreOf_subgroupOf 2 X]
      exact hxO2
    · intro x hx
      rw [MonoidHom.mem_ker]
      have hxO2 : x ∈ CFSG.pCore 2 ↥X := by
        rw [CFSG.openPCoreOf_subgroupOf 2 X] at hx
        exact hx
      have hxP : (x : G) ∈ pCoreOf 2 X := by
        rw [← CFSG.openPCoreOf_subgroupOf 2 X] at hxO2
        exact Subgroup.mem_subgroupOf.mp hxO2
      have h1 : actTil V₀ V hV ⟨(x : G), hXstab x.2⟩ ∈ barSub V₀ V hV (pCoreOf 2 X) :=
        actTil_mem_barSub V₀ V hV hxP (hXstab x.2)
      rw [hO2Xbot, Subgroup.mem_bot] at h1
      exact h1
  have hO2_le : pCoreOf 2 X ≤ T ⊓ X := by
    have hO2normal : ((pCoreOf 2 X).subgroupOf X).Normal := by
      rw [Subgroup.normal_subgroupOf_iff (CFSG.LieType.BorelTits.pCoreOf_le 2 X)]
      intro a b ha hb
      exact CFSG.ClassicalGroups.PCoreSection.conj_mem_pCoreOf hb ha
    have hSylIn : IsSylowIn 2 (T ⊓ X) X :=
      (CFSG.ABGLocalTools.isSylowOf_iff (p := 2) (P := T ⊓ X) (K := X)).mp
        (CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer D.sylowM hXM
          (TwelveTwentyThree.le_normalizer_conjClosure M L))
    exact hSylIn.le_of_normal (CFSG.LieType.BorelTits.pCoreOf_le 2 X) hO2normal
      (CFSG.ClassicalGroups.PCoreSection.isPGroup_pCoreOf 2 X)
  have hkerS : ψ.ker ≤ (T ⊓ X).subgroupOf X := by
    rw [hker]
    exact Subgroup.subgroupOf_mono X hO2_le
  have hinf : barSub V₀ V hV T ⊓ barSub V₀ V hV X =
      barSub V₀ V hV (T ⊓ X) :=
    EighteenElevenTransport.barSub_inf_eq hV hMstab hTsyl hXM hXn
  have hbase : ∀ H : Subgroup G, H ≤ X → (H.subgroupOf X).map ψ = barSub V₀ V hV H := by
    intro H hHX
    rw [barSub]
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact actTil_mem_barSub V₀ V hV hz (hXstab (hHX hz))
    · intro hy
      obtain ⟨a, haH, hay⟩ := (mem_barSub V₀ V hV H y).1 hy
      exact ⟨⟨a, hHX haH⟩, Subgroup.mem_subgroupOf.mpr haH, hay⟩
  have hbaseS : ((T ⊓ X).subgroupOf X).map ψ = barSub V₀ V hV (T ⊓ X) :=
    hbase _ inf_le_right
  have hcomapS : (barSub V₀ V hV (T ⊓ X)).comap ψ = (T ⊓ X).subgroupOf X := by
    rw [← hbaseS]
    exact Subgroup.comap_map_eq_self hkerS
  let ψT : ↥T →* MulAut (Vtil V₀ V hV) :=
    (actTil V₀ V hV).comp (Subgroup.inclusion hTstab)
  obtain ⟨t, htT, P, hP, hPt⟩ := hswap
  have htstab : t ∈ stabTil V₀ V := hTstab htT
  have htM : t ∈ M := hTM htT
  have htX : t ∈ Subgroup.normalizer (X : Set G) :=
    TwelveTwentyThree.le_normalizer_conjClosure M L htM
  have hXconj : X.map (MulAut.conj t).toMonoidHom = X :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp htX
  have hTconj : T.map (MulAut.conj t).toMonoidHom = T :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer htT)
  have hSP : T ⊓ X ≤ P :=
    (le_inf inf_le_right (fun x hx => Subgroup.le_normalizer hx)).trans hP.2.1
  have hkerP : ψ.ker ≤ P.subgroupOf X := hkerS.trans (Subgroup.subgroupOf_mono X hSP)
  let Q : Subgroup (MulAut (Vtil V₀ V hV)) := (P.subgroupOf X).map ψ
  have hQmap : Q = barSub V₀ V hV P := hbase P hP.1
  have hSconj : (T ⊓ X).map (MulAut.conj t).toMonoidHom = T ⊓ X := by
    rw [Subgroup.map_inf T X _ (MulAut.conj t).injective, hTconj, hXconj]
  have hSPt : T ⊓ X ≤ P.map (MulAut.conj t).toMonoidHom := by
    rw [← hSconj]
    exact Subgroup.map_mono hSP
  have hkerPt : ψ.ker ≤ ((P.map (MulAut.conj t).toMonoidHom)).subgroupOf X := by
    rw [hker]
    exact (Subgroup.subgroupOf_mono X hO2_le).trans (Subgroup.subgroupOf_mono X hSPt)
  have hPtX : P.map (MulAut.conj t).toMonoidHom ≤ X := by
    rw [← hXconj]
    exact Subgroup.map_mono hP.1
  have hQmax : S17.IsMaxParabolicOver (barSub V₀ V hV X)
      (barSub V₀ V hV T ⊓ barSub V₀ V hV X) Q := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hQmap]
      exact barSub_mono V₀ V hV hP.1
    · rw [hinf]
      rintro c ⟨hcX, hcN⟩
      obtain ⟨x, hx⟩ := hψmem c hcX
      have key : ∀ z : ↥X, ψ z ∈ Subgroup.normalizer
          (barSub V₀ V hV (T ⊓ X) : Set (MulAut (Vtil V₀ V hV))) →
          ∀ s ∈ T ⊓ X, (z : G) * s * (z : G)⁻¹ ∈ T ⊓ X := by
        intro z hz s hs
        have hsX : s ∈ X := hs.2
        have hψs : ψ ⟨s, hsX⟩ ∈ barSub V₀ V hV (T ⊓ X) := by
          rw [← hbaseS]
          exact Subgroup.mem_map.mpr
            ⟨⟨s, hsX⟩, Subgroup.mem_subgroupOf.mpr hs, rfl⟩
        have hconj : ψ z * ψ ⟨s, hsX⟩ * (ψ z)⁻¹ ∈ barSub V₀ V hV (T ⊓ X) :=
          (Subgroup.mem_normalizer_iff.1 hz (ψ ⟨s, hsX⟩)).1 hψs
        have hψconj : ψ (z * ⟨s, hsX⟩ * z⁻¹) ∈ barSub V₀ V hV (T ⊓ X) := by
          rwa [map_mul, map_mul, map_inv]
        have hmem : z * ⟨s, hsX⟩ * z⁻¹ ∈ (barSub V₀ V hV (T ⊓ X)).comap ψ := hψconj
        rw [hcomapS] at hmem
        have := Subgroup.mem_subgroupOf.mp hmem
        simpa using this
      have hxN : (x : G) ∈ Subgroup.normalizer ((T ⊓ X : Subgroup G) : Set G) := by
        rw [Subgroup.mem_normalizer_iff]
        intro s
        constructor
        · intro hs
          exact key x (hx ▸ hcN) s hs
        · intro hs
          have hxinv : ψ x⁻¹ ∈ Subgroup.normalizer
              (barSub V₀ V hV (T ⊓ X) : Set (MulAut (Vtil V₀ V hV))) := by
            have := Subgroup.inv_mem _ (hx ▸ hcN)
            rwa [map_inv]
          have hEq : ((x⁻¹ : ↥X) : G) * ((x : G) * s * (x : G)⁻¹) *
              (((x⁻¹ : ↥X) : G))⁻¹ = s := by
            simp only [Subgroup.coe_inv]
            group
          have hmem' : ((x⁻¹ : ↥X) : G) * ((x : G) * s * (x : G)⁻¹) *
              (((x⁻¹ : ↥X) : G))⁻¹ ∈ T ⊓ X := key x⁻¹ hxinv (x * s * x⁻¹) hs
          rwa [hEq] at hmem' 
      refine Subgroup.mem_map.mpr ⟨x, Subgroup.mem_subgroupOf.mpr (hP.2.1 ⟨x.2, hxN⟩), ?_⟩
      exact hx
    · intro htop
      have hPtop : P.subgroupOf X = ⊤ := by
        have h1 : (P.subgroupOf X).map ψ = ψ.range := by
          have hQeq : (P.subgroupOf X).map ψ = barSub V₀ V hV X := by
            rw [hbase P hP.1, ← hQmap, htop]
          rw [hQeq, hψrange]
        have h2 := congrArg (fun H => H.comap ψ) h1
        rw [Subgroup.comap_map_eq_self hkerP] at h2
        have hrange : ψ.range.comap ψ = ⊤ := by
          rw [← Subgroup.map_top (f := ψ)]
          exact Subgroup.comap_map_eq_self (le_top : ψ.ker ≤ ⊤)
        rw [hrange] at h2
        exact h2
      have hPX : P = X := by
        have h1 : P.subgroupOf X = X.subgroupOf X := by
          rw [hPtop, Subgroup.subgroupOf_self]
        rw [Subgroup.subgroupOf_inj, inf_eq_left.mpr hP.1, inf_idem] at h1
        exact h1
      exact hP.2.2.1 hPX
    · intro Q' hQQ' hQ'X
      have hP' : P.subgroupOf X ≤ Q'.comap ψ := fun x hx =>
        hQQ' (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
      have hP'X : (Q'.comap ψ).map X.subtype ≤ X := by
        rintro _ ⟨x, -, rfl⟩
        exact x.2
      have hPle : P ≤ (Q'.comap ψ).map X.subtype := by
        rintro p hp
        exact Subgroup.mem_map.mpr ⟨⟨p, hP.1 hp⟩, hP' hp, rfl⟩
      have hQ'eq : (Q'.comap ψ).map ψ = Q' :=
        Subgroup.map_comap_eq_self (hψrange ▸ hQ'X)
      rcases hP.2.2.2 ((Q'.comap ψ).map X.subtype) hPle hP'X with hmax | hmax
      · left
        have hP'map : Q'.comap ψ = P.subgroupOf X := by
          calc Q'.comap ψ = ((Q'.comap ψ).map X.subtype).comap X.subtype :=
                (Subgroup.comap_map_eq_self_of_injective X.subtype_injective (Q'.comap ψ)).symm
            _ = P.comap X.subtype := by rw [hmax]
            _ = P.subgroupOf X := rfl
        rw [← hQ'eq, hP'map]
      · right
        have hP'map : Q'.comap ψ = ⊤ := by
          calc Q'.comap ψ = ((Q'.comap ψ).map X.subtype).comap X.subtype :=
                (Subgroup.comap_map_eq_self_of_injective X.subtype_injective (Q'.comap ψ)).symm
            _ = X.comap X.subtype := by rw [hmax]
            _ = ⊤ := by ext x; simp
        rw [← hQ'eq, hP'map, Subgroup.map_top, hψrange]
  refine ⟨ψT ⟨t, htT⟩, ?_, Q, hQmax, ?_⟩
  · exact actTil_mem_barSub V₀ V hV htT (hTstab htT)
  · intro heq
    apply hPt
    have htbar : (ψT ⟨t, htT⟩ : MulAut (Vtil V₀ V hV)) =
        actTil V₀ V hV ⟨t, htstab⟩ := rfl
    have h1 : barSub V₀ V hV (P.map (MulAut.conj t).toMonoidHom) = barSub V₀ V hV P := by
      rw [TwelveTwentyThree.barSub_map_conj hV (hP.1.trans hXstab) htstab, ← hQmap]
      exact heq
    have h2 : (P.map (MulAut.conj t).toMonoidHom).subgroupOf X = P.subgroupOf X := by
      have hPtbase : ((P.map (MulAut.conj t).toMonoidHom).subgroupOf X).map ψ =
          barSub V₀ V hV (P.map (MulAut.conj t).toMonoidHom) := hbase _ hPtX
      have hPbase : (P.subgroupOf X).map ψ = barSub V₀ V hV P := hbase _ hP.1
      calc (P.map (MulAut.conj t).toMonoidHom).subgroupOf X
          = (((P.map (MulAut.conj t).toMonoidHom).subgroupOf X).map ψ).comap ψ :=
              (Subgroup.comap_map_eq_self hkerPt).symm
        _ = (barSub V₀ V hV (P.map (MulAut.conj t).toMonoidHom)).comap ψ := by rw [hPtbase]
        _ = (barSub V₀ V hV P).comap ψ := by rw [h1]
        _ = ((P.subgroupOf X).map ψ).comap ψ := by rw [hPbase]
        _ = P.subgroupOf X := Subgroup.comap_map_eq_self hkerP
    have h3 := Subgroup.subgroupOf_inj.mp h2
    rw [inf_eq_left.mpr hPtX, inf_eq_left.mpr hP.1] at h3
    exact h3

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
