module

public import CFSG.LocalAnalysis.StandardType.GGSporKPSubquot
public import CFSG.LocalAnalysis.StandardType.GGSporKLamOrders
public import CFSG.LocalAnalysis.StandardType.GGSporKBMTransportB
public import CFSG.HardMathSupport.Dickson.BMRows.CensusB3
public import CFSG.HardMathSupport.Dickson.BMRows.CensusB5
public import CFSG.HardMathSupport.Dickson.BMRows.CensusM3
public import CFSG.HardMathSupport.Dickson.BMRows.CensusM5
public import CFSG.HardMathSupport.Dickson.BMRows.CensusM7
public import CFSG.HardMathSupport.Dickson.BMRows.M13Rows
public import CFSG.Sporadic.Bridge.BBound
public import CFSG.Sporadic.Bridge.MonsterModels
public import CFSG.Sporadic.Bridge.Fi22Surj
public import CFSG.Sporadic.Bridge.Fi24Surj
public import CFSG.Sporadic.Bridge.HSSurj
public import CFSG.Sporadic.Bridge.HNSurj
public import CFSG.Sporadic.Bridge.HeSurj
public import CFSG.Sporadic.Bridge.ThSurj
public import CFSG.Sporadic.Fi22.Simple
public import CFSG.Sporadic.Fi24.Simple
public import CFSG.Sporadic.HS
public import CFSG.Sporadic.HN
public import CFSG.Sporadic.He.Simple
public import CFSG.RankThree.OddKernel.SporadicKernelTh
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabBThreeALocalBase
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabBThreeL1Orb
public import CFSG.HardMathSupport.Dickson.Sec6.Up34SporAux.BMDownMGmat
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporAut168
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS10I1416Pass
public import Certificates.Certificate17632Base
public import Certificates.Data.TabCo1ThreeE

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Dickson.BMRows

theorem bmNoLiePComp_of_pSimpleCard
    {p : ℕ} (hp : p.Prime) {Q : Type} [Group Q] [Finite Q]
    (hcard : ∀ x : Q, orderOf x = p → ∀ J : Subgroup Q,
      GLAPComponent p (Subgroup.centralizer ({x} : Set Q)) J →
        Nat.card (PSimple p J) ∈ bmCompOrders) :
    BMNoLiePComp p Q := by
  intro x hx C hC hmark
  obtain ⟨ψ⟩ := bmPSubquot_centerQuot_equiv_pSimple hp hC
  have h1 : Nat.card (BMPSubquot p x C ⧸ Subgroup.center (BMPSubquot p x C)) ∈ bmCompOrders := by
    rw [Nat.card_congr ψ.toEquiv]
    exact hcard x hx C ((CFSG.Assembly.LargeEven.largeEvenPComponent_iff_glaPComponent p _ C).1 hC)
  exact largeEvenMarking_not_card_of_mem_bmCompOrders h1 rfl hmark

theorem bmNoLiePComp_of_pCompCensus
    {p : ℕ} (hp : p.Prime) {Q : Type} [Group Q] [Finite Q] {P : TauCeti.CFSGIndex → Prop}
    (hP : ∀ i, P i → Nat.card i.Group ∈ bmCompOrders) (hcen : PCompCensus p Q P) :
    BMNoLiePComp p Q :=
  bmNoLiePComp_of_pSimpleCard hp fun x hx J hJ => by
    obtain ⟨i, hi, ⟨e⟩⟩ := hcen x hx J hJ
    rw [Nat.card_congr e.toEquiv]
    exact hP i hi

private theorem gkn_card_Fi22
    : Nat.card (TauCeti.CFSGIndex.sporadic .Fi22).Group = 64561751654400 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Fi22.nonempty_mulEquiv
  rw [← Nat.card_congr b.toEquiv]
  exact CFSG.Sporadic.Fi22.card_Fi22

private theorem gkn_card_HS
    : Nat.card (TauCeti.CFSGIndex.sporadic .HS).Group = 44352000 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.HS.nonempty_mulEquiv
  rw [← Nat.card_congr b.toEquiv]
  exact CFSG.Sporadic.HS.card_HS

private theorem gkn_card_Fi24Prime
    : Nat.card (TauCeti.CFSGIndex.sporadic .Fi24Prime).Group = 1255205709190661721292800 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Fi24.nonempty_mulEquiv
  rw [← Nat.card_congr b.toEquiv]
  exact CFSG.Sporadic.Fi24.card_Fi24prime

private theorem gkn_card_Th
    : Nat.card (TauCeti.CFSGIndex.sporadic .Th).Group = 90745943887872000 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Th.nonempty_mulEquiv
  rw [← Nat.card_congr b.toEquiv]
  exact CFSG.RankThree.OddKernel.card_Th_eq

private theorem gkn_card_HN
    : Nat.card (TauCeti.CFSGIndex.sporadic .HN).Group = 273030912000000 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.HN.nonempty_mulEquiv
  rw [← Nat.card_congr b.toEquiv]
  exact CFSG.Sporadic.HN.card_HN

private theorem gkn_card_He
    : Nat.card (TauCeti.CFSGIndex.sporadic .He).Group = 4030387200 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.He.nonempty_mulEquiv
  rw [← Nat.card_congr b.toEquiv]
  exact CFSG.Sporadic.He.card_He

theorem ggSporK_bmNoLiePComp_B_three [Finite (TauCeti.CFSGIndex.sporadic .B).Group]
    (hK : CFSG.Open.IsKGroup (TauCeti.CFSGIndex.sporadic .B).Group) :
    BMNoLiePComp 3 (TauCeti.CFSGIndex.sporadic .B).Group := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.B.nonempty_mulEquiv
  let e' : CFSG.Blueprint.NativeSporadic.Carrier .B ≃* (TauCeti.CFSGIndex.sporadic .B).Group :=
    e.trans (MulEquiv.refl _)
  haveI : Finite (CFSG.Blueprint.NativeSporadic.Carrier .B) := CFSG.Monster.B.Pinned.finite_B
  have hKB : CFSG.Open.IsKGroup (CFSG.Blueprint.NativeSporadic.Carrier .B) :=
    hK.of_injective e'.toMonoidHom e'.injective
  exact bmNoLiePComp_of_mulEquiv 3 e'
    (bmNoLiePComp_of_pCompCensus Nat.prime_three
      (fun i hi => by subst hi; rw [gkn_card_Fi22]; simp [bmCompOrders])
      (census_B_three hKB))

theorem ggSporK_bmNoLiePComp_B_five [Finite (TauCeti.CFSGIndex.sporadic .B).Group]
    (hK : CFSG.Open.IsKGroup (TauCeti.CFSGIndex.sporadic .B).Group) :
    BMNoLiePComp 5 (TauCeti.CFSGIndex.sporadic .B).Group := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.B.nonempty_mulEquiv
  let e' : CFSG.Blueprint.NativeSporadic.Carrier .B ≃* (TauCeti.CFSGIndex.sporadic .B).Group :=
    e.trans (MulEquiv.refl _)
  haveI : Finite (CFSG.Blueprint.NativeSporadic.Carrier .B) := CFSG.Monster.B.Pinned.finite_B
  have hKB : CFSG.Open.IsKGroup (CFSG.Blueprint.NativeSporadic.Carrier .B) :=
    hK.of_injective e'.toMonoidHom e'.injective
  exact bmNoLiePComp_of_mulEquiv 5 e'
    (bmNoLiePComp_of_pCompCensus Nat.prime_five
      (fun i hi => by subst hi; rw [gkn_card_HS]; simp [bmCompOrders])
      (census_B_five hKB))

theorem ggSporK_bmNoLiePComp_M_three [Finite (TauCeti.CFSGIndex.sporadic .M).Group]
    (hK : CFSG.Open.IsKGroup (TauCeti.CFSGIndex.sporadic .M).Group) :
    BMNoLiePComp 3 (TauCeti.CFSGIndex.sporadic .M).Group := by
  obtain ⟨e⟩ := CFSG.Blueprint.NativeSporadic.MonsterModel.iso_y443Derived_tauCeti
  let e' : CFSG.Blueprint.NativeSporadic.Carrier .M ≃* (TauCeti.CFSGIndex.sporadic .M).Group :=
    e.trans (MulEquiv.refl _)
  haveI : Finite (CFSG.Blueprint.NativeSporadic.Carrier .M) := Finite.of_equiv _ e'.symm.toEquiv
  have hKM : CFSG.Open.IsKGroup (CFSG.Blueprint.NativeSporadic.Carrier .M) :=
    hK.of_injective e'.toMonoidHom e'.injective
  exact bmNoLiePComp_of_mulEquiv 3 e'
    (bmNoLiePComp_of_pCompCensus Nat.prime_three
      (fun i hi => by
        rcases hi with rfl | rfl
        · rw [gkn_card_Fi24Prime]; simp [bmCompOrders]
        · rw [gkn_card_Th]; simp [bmCompOrders])
      (census_M_three hKM))

theorem ggSporK_bmNoLiePComp_M_five [Finite (TauCeti.CFSGIndex.sporadic .M).Group]
    (hK : CFSG.Open.IsKGroup (TauCeti.CFSGIndex.sporadic .M).Group) :
    BMNoLiePComp 5 (TauCeti.CFSGIndex.sporadic .M).Group := by
  obtain ⟨e⟩ := CFSG.Blueprint.NativeSporadic.MonsterModel.iso_y443Derived_tauCeti
  let e' : CFSG.Blueprint.NativeSporadic.Carrier .M ≃* (TauCeti.CFSGIndex.sporadic .M).Group :=
    e.trans (MulEquiv.refl _)
  haveI : Finite (CFSG.Blueprint.NativeSporadic.Carrier .M) := Finite.of_equiv _ e'.symm.toEquiv
  have hKM : CFSG.Open.IsKGroup (CFSG.Blueprint.NativeSporadic.Carrier .M) :=
    hK.of_injective e'.toMonoidHom e'.injective
  exact bmNoLiePComp_of_mulEquiv 5 e'
    (bmNoLiePComp_of_pCompCensus Nat.prime_five
      (fun i hi => by subst hi; rw [gkn_card_HN]; simp [bmCompOrders])
      (census_M_five hKM))

theorem ggSporK_bmNoLiePComp_M_seven [Finite (TauCeti.CFSGIndex.sporadic .M).Group]
    : BMNoLiePComp 7 (TauCeti.CFSGIndex.sporadic .M).Group := by
  obtain ⟨e⟩ := CFSG.Blueprint.NativeSporadic.MonsterModel.iso_y443Derived_tauCeti
  let e' : CFSG.Blueprint.NativeSporadic.Carrier .M ≃* (TauCeti.CFSGIndex.sporadic .M).Group :=
    e.trans (MulEquiv.refl _)
  haveI : Finite (CFSG.Blueprint.NativeSporadic.Carrier .M) := Finite.of_equiv _ e'.symm.toEquiv
  exact bmNoLiePComp_of_mulEquiv 7 e'
    (bmNoLiePComp_of_pCompCensus (by norm_num)
      (fun i hi => by subst hi; rw [gkn_card_He]; simp [bmCompOrders])
      census_M_seven)

private theorem gkn_card_pSimple_gmat_thirteen
    (φ : CFSG.Monster.Generated.Gmat ≃* CFSG.Monster.Existence.MGriess)
    {s : CFSG.Monster.Generated.Gmat} (hs : orderOf s = 13)
    {J : Subgroup CFSG.Monster.Generated.Gmat}
    (hJ : GLAPComponent 13 (Subgroup.centralizer ({s} : Set CFSG.Monster.Generated.Gmat)) J) :
    Nat.card (PSimple 13 J) = 5616 := by
  haveI : Finite CFSG.Monster.Generated.Gmat :=
    CFSG.Monster.Generated.generated_rational_group_finite_simple.2.2
  obtain ⟨m, k, hk, h | h⟩ :=
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteen.census_thirteen s hs
  · exact absurd hJ (noComp_conj_c13 hk h J)
  · rcases CFSG.HardMathSupport.Dickson.I271.ShapeRkAt.toWeak (by norm_num)
      (shapeRkAt_conj_xE φ hk h) with hno | ⟨J₀, -, hu, ⟨e⟩, -⟩
    · exact absurd hJ (hno J)
    · rw [hu J hJ]
      exact M13L33.card_of_equiv_sl e

theorem ggSporK_bmNoLiePComp_M_thirteen [Finite (TauCeti.CFSGIndex.sporadic .M).Group]
    : BMNoLiePComp 13 (TauCeti.CFSGIndex.sporadic .M).Group := by
  obtain ⟨e⟩ := CFSG.Blueprint.NativeSporadic.MonsterModel.iso_y443Derived_tauCeti
  obtain ⟨⟨φ, ψ⟩⟩ := exists_M_equivs
  let e' : CFSG.Blueprint.NativeSporadic.Carrier .M ≃* (TauCeti.CFSGIndex.sporadic .M).Group :=
    e.trans (MulEquiv.refl _)
  haveI : Finite CFSG.Monster.Generated.Gmat :=
    CFSG.Monster.Generated.generated_rational_group_finite_simple.2.2
  exact bmNoLiePComp_of_mulEquiv 13 (ψ.trans e')
    (bmNoLiePComp_of_pSimpleCard (by norm_num) fun x hx J hJ => by
      rw [gkn_card_pSimple_gmat_thirteen φ hx hJ]
      simp [bmCompOrders])

end CFSG.StandardType.SporadicShape
