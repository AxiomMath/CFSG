module

public import CFSG.Quasithin.Background.AutOnPerfect
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem12Inputs
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem5
public import CFSG.Quasithin.Vol2.Ch12Sec2Inputs
public import CFSG.Quasithin.Vol2.Ch1Prop121
public import CFSG.Quasithin.Vol2.Ch1Faithful
public import CFSG.Quasithin.Vol2.Ch12Sec2Action
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem12Stmt

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped IsMulCommutative

namespace Lem12

section General

variable {G : Type*} [Group G]

theorem oTwoUpper_oTwoUpper (X : Subgroup G) : oTwoUpper (oTwoUpper X) = oTwoUpper X := by
  refine le_antisymm (oTwoUpper_le _) ((Subgroup.closure_le _).mpr fun x hx => ?_)
  exact mem_oTwoUpper_of_odd (mem_oTwoUpper_of_odd hx.1 hx.2) hx.2

theorem centralizerSection_inf_normalizer_eq (K X Z : Subgroup G) :
    centralizerSection (K ⊓ Subgroup.normalizer (X : Set G)) X Z = centralizerSection K X Z := by
  ext m
  simp only [mem_centralizerSection, Subgroup.mem_inf]
  exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, h.2.1⟩, h.2⟩⟩

variable [Finite G]

theorem isMaxSignalizer_of_inf_normalizer_le {X M K R : Subgroup G}
    (hR : IsMaxSignalizer M X R) (hMK : M ≤ K)
    (hN : K ⊓ Subgroup.normalizer (R : Set G) ≤ M) : IsMaxSignalizer K X R := by
  refine ⟨⟨hR.1.1.trans hMK, hR.1.2.1, hR.1.2.2⟩, fun S hS hRS => ?_⟩
  have hsig : IsSignalizer M X (S ⊓ Subgroup.normalizer (R : Set G)) := by
    refine ⟨fun x hx => hN ⟨hS.1 hx.1, hx.2⟩, hS.2.1.to_inf_left, ?_⟩
    intro x hx
    exact A4.mem_normalizer_inf (hS.2.2 hx) (Subgroup.le_normalizer (hR.1.2.2 hx))
  have hRle : R ≤ S ⊓ Subgroup.normalizer (R : Set G) := le_inf hRS Subgroup.le_normalizer
  have heq := hR.eq_of_le hsig hRle
  by_contra hSR
  have hlt : R < S := lt_of_le_of_ne hRS (fun h => hSR (h ▸ le_rfl))
  obtain ⟨s, hsS, hsN, hsR⟩ := A4.exists_mem_normalizer_not_mem hS.2.1 hlt
  exact hsR (heq ▸ (⟨hsS, hsN⟩ : s ∈ S ⊓ Subgroup.normalizer (R : Set G)))

theorem a4_2_7_rel {X M K : Subgroup G} (hX : X = oTwoUpper X) (hXM : X ≤ M)
    (hXN : (X.subgroupOf M).Normal) (hMK : M ≤ K) {T R : Subgroup G} (hT : IsSylowTwoOf T M)
    (hR : R = pCoreOf 2 (X ⊔ T)) (hNR : K ⊓ Subgroup.normalizer (R : Set G) ≤ M) :
    IsSylowTwoOf R (centralizerSection K X (pCoreOf 2 X)) ∧
      R = pCoreOf 2 (K ⊓ Subgroup.normalizer (R : Set G)) ∧
      IsSylowTwoOf R (centralizerSection M X (pCoreOf 2 X)) ∧
      IsSylowTwoOf R (conjClosure R M) := by
  have hMN : M ≤ Subgroup.normalizer (X : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXM).mp hXN
  have hsub : IsSubnormal X M := A4.subnormal_of_normal hXM hXN
  have hT' : IsSylowTwoOf T (M ⊓ Subgroup.normalizer (X : Set G)) := by
    rwa [inf_eq_left.mpr hMN]
  have hRmax : IsMaxSignalizer M X R := hR ▸ a4_2_5 hX hsub hT'
  have hRsylM : IsSylowTwoOf R (centralizerSection M X (pCoreOf 2 X)) :=
    (a4_2_4 hX hsub R).mp hRmax
  have hO2 : R = pCoreOf 2 (K ⊓ Subgroup.normalizer (R : Set G)) := by
    have hsig : IsSignalizer M X (pCoreOf 2 (K ⊓ Subgroup.normalizer (R : Set G))) := by
      refine ⟨(pCoreOf_le 2 _).trans hNR, pCoreOf_isPGroup 2 _, ?_⟩
      exact (le_inf (hXM.trans hMK) hRmax.1.2.2).trans (le_normalizer_pCoreOf 2 _)
    have hRP : R ≤ pCoreOf 2 (K ⊓ Subgroup.normalizer (R : Set G)) :=
      le_pCoreOf_of_le_normalizer 2 (le_inf (hRmax.1.1.trans hMK) Subgroup.le_normalizer)
        inf_le_right hRmax.1.2.1
    exact (hRmax.eq_of_le hsig hRP).symm
  have hRK : IsMaxSignalizer K X R := isMaxSignalizer_of_inf_normalizer_le hRmax hMK hNR
  have hsubKX : IsSubnormal X (K ⊓ Subgroup.normalizer (X : Set G)) :=
    A4.subnormal_of_normal (le_inf (hXM.trans hMK) Subgroup.le_normalizer)
      (Subgroup.normal_subgroupOf_of_le_normalizer inf_le_right)
  have hRKX : IsMaxSignalizer (K ⊓ Subgroup.normalizer (X : Set G)) X R := by
    refine ⟨⟨le_inf hRK.1.1 (hRmax.1.1.trans hMN), hRK.1.2.1, hRK.1.2.2⟩, fun S hS hRS => ?_⟩
    exact hRK.2 ⟨hS.1.trans inf_le_left, hS.2.1, hS.2.2⟩ hRS
  have hRsylK : IsSylowTwoOf R (centralizerSection K X (pCoreOf 2 X)) := by
    have := (a4_2_4 hX hsubKX R).mp hRKX
    rwa [centralizerSection_inf_normalizer_eq] at this
  refine ⟨hRsylK, hO2, hRsylM, ?_⟩
  have hle : conjClosure R M ≤ centralizerSection M X (pCoreOf 2 X) := by
    refine conjClosure_le fun m hm r hr => ?_
    have hmX := hMN hm
    exact conj_mem_centralizerSection (Subgroup.le_normalizer hm) hmX
      (normalizer_le_normalizer_pCoreOf 2 X hmX) (hRsylM.1 hr)
  exact A4.isSylowTwoOf_mono hRsylM (le_conjClosure R M) hle

end General

section AutOn

variable {G : Type} [Group G] [Finite G]

theorem autOn_pCoreOf_le {X V : Subgroup G} (hX : X ≤ Subgroup.normalizer (V : Set G)) :
    autOn (pCoreOf 2 X) V ≤ pCoreOf 2 (autOn X V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPX := pCoreOf_le 2 X
  refine le_pCoreOf_of_le_normalizer 2 (A4.autOn_mono hPX)
    (autOn_le_normalizer_autOn (hPX.trans hX) hX (le_normalizer_pCoreOf 2 X)) ?_
  exact ((pCoreOf_isPGroup 2 X).comap_of_injective _
    (Subgroup.normalizer (V : Set G)).subtype_injective).map (conjAct V)

theorem pCoreOf_le_centralizer_of_autOn {X V : Subgroup G}
    (hX : X ≤ Subgroup.normalizer (V : Set G)) (hO2 : pCoreOf 2 (autOn X V) = ⊥) :
    pCoreOf 2 X ≤ Subgroup.centralizer (V : Set G) := by
  have hPV : pCoreOf 2 X ≤ Subgroup.normalizer (V : Set G) := (pCoreOf_le 2 X).trans hX
  intro x hx
  have h1 : A4.actionOn V (pCoreOf 2 X) hPV ⟨x, hx⟩ ∈ autOn (pCoreOf 2 X) V :=
    (A4.mem_autOn_iff hPV).2 ⟨⟨x, hx⟩, rfl⟩
  have h2 := autOn_pCoreOf_le hX h1
  rw [hO2, Subgroup.mem_bot] at h2
  exact (A4.actionOn_eq_one_iff hPV ⟨x, hx⟩).1 h2

end AutOn

section AutOn2

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem autOn_perfectCore_eq {X V : Subgroup G} (hX : X ≤ Subgroup.normalizer (V : Set G)) :
    autOn (perfectCore X) V = perfectCore (autOn X V) :=
  CFSG.Quasithin.AutOn.autOn_perfectCore_eq hX

omit [Finite G] in
theorem commutator_eq_of_autOn_eq {X Y V : Subgroup G} (hX : X ≤ Subgroup.normalizer (V : Set G))
    (hY : Y ≤ Subgroup.normalizer (V : Set G)) (h : autOn X V = autOn Y V) :
    ⁅V, X⁆ = ⁅V, Y⁆ := by
  have key : ∀ {X Y : Subgroup G} (hX : X ≤ Subgroup.normalizer (V : Set G))
      (hY : Y ≤ Subgroup.normalizer (V : Set G)), autOn X V ≤ autOn Y V → ⁅V, X⁆ ≤ ⁅V, Y⁆ := by
    intro X Y hX hY hle
    rw [Subgroup.commutator_le]
    intro w hw x hx
    have hmem : A4.actionOn V X hX ⟨x, hx⟩ ∈ autOn Y V :=
      hle ((A4.mem_autOn_iff hX).mpr ⟨⟨x, hx⟩, rfl⟩)
    obtain ⟨y, hy⟩ := (A4.mem_autOn_iff hY).mp hmem
    have h1 := congrArg (fun a : MulAut ↥V => ((a ⟨w, hw⟩⁻¹ : ↥V) : G)) hy
    simp only [A4.actionOn_apply_coe, Subgroup.coe_inv] at h1
    have e : ⁅w, x⁆ = w * (x * w⁻¹ * x⁻¹) := by rw [commutatorElement_def]; group
    rw [e, ← h1]
    have e2 : w * ((y : G) * w⁻¹ * (y : G)⁻¹) = ⁅w, (y : G)⁆ := by
      rw [commutatorElement_def]; group
    rw [e2]
    exact Subgroup.commutator_mem_commutator hw y.2
  exact le_antisymm (key hX hY h.le) (key hY hX h.ge)

omit [Finite G] in
theorem commutator_le_of_le_normalizer {H K : Subgroup G}
    (h : H ≤ Subgroup.normalizer (K : Set G)) : ⁅H, K⁆ ≤ K := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  exact K.mul_mem ((Subgroup.mem_normalizer_iff.mp (h ha) b).mp hb) (K.inv_mem hb)

omit [Finite G] in
theorem autOn_eq_bot_of_le_centralizer {X V : Subgroup G}
    (h : X ≤ Subgroup.centralizer (V : Set G)) : autOn X V = ⊥ :=
  CFSG.Quasithin.AutOn.autOn_eq_bot_of_le_centralizer h

theorem pCoreOf_le_pCoreOf_of_normal {N Y : Subgroup G} (hNY : N ≤ Y)
    (hYN : Y ≤ Subgroup.normalizer (N : Set G)) : pCoreOf 2 N ≤ pCoreOf 2 Y :=
  le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 N).trans hNY)
    (hYN.trans (normalizer_le_normalizer_pCoreOf 2 N)) (pCoreOf_isPGroup 2 N)

omit [Finite G] in
theorem pCoreOf_centralizer_ne_bot {T : Subgroup G} (hT : IsPGroup 2 T) {v : G} (hvT : v ∈ T)
    (hv1 : v ≠ 1) (hN : Subgroup.centralizer ({v} : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers v : Subgroup G) : Set G)) :
    pCoreOf 2 (Subgroup.centralizer ({v} : Set G)) ≠ ⊥ := by
  have hzp : Subgroup.zpowers v ≤ pCoreOf 2 (Subgroup.centralizer ({v} : Set G)) := by
    refine le_pCoreOf_of_le_normalizer 2
      ((Subgroup.zpowers_le).mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl)) hN ?_
    exact hT.to_le ((Subgroup.zpowers_le).mpr hvT)
  intro h
  rw [h, le_bot_iff] at hzp
  apply hv1
  have : v ∈ Subgroup.zpowers v := Subgroup.mem_zpowers v
  rw [hzp, Subgroup.mem_bot] at this
  exact this

end AutOn2

end Lem12

open Lem12

theorem stmt12_2_12_one (h1222 : Stmt12_2_2) (h323 : Stmt3_2_3) (h3228 : Stmt3_2_2_eight)
    {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (hH : Hyp1223 G T L V) {v : G}
    (hv : v ∈ V) (hv1 : v ≠ 1) (hTv : IsSylowTwoOf (hH.Tv v) (hH.Mv v))
    (hO2 : pCoreOf 2 (autOn (hH.Lv v ⊔ hH.Tv v) V) = ⊥) :
    hH.Q = pCoreOf 2 (hH.Lv v ⊔ hH.Tv v) ∧
      IsSylowTwoOf hH.Q (centralizerSection (hH.Gv v) (hH.Lv v) (pCoreOf 2 (hH.Lv v))) ∧
      HypC23 (hH.Gv v) hH.Q (hH.Mv v) := by
  obtain ⟨hLvMv, hMvN, -, hcgs, hMvMV⟩ := stmt12_2_5_of h1222 h323 G T L V hH v hv hv1
  obtain ⟨-, -, hall⟩ := ((h1222 G T hH.simple hH.nonabelian hH.qtke hH.sylow).resolve_left
    hH.notAlt) L hH.maximal hH.faithful hH.quasisimple
  obtain ⟨⟨hVT, hTV, -, -⟩, -, -, -, -⟩ := hall V hH.irrPlus
  have hQ : hH.Q = T ⊓ Subgroup.centralizer (V : Set G) := by
    have := (h3228 G T L V hH.fsu).2.2
    rwa [hH.conjClosure_eq, conjClosure_eq_self_of_normalizes hTV] at this
  have hQ2 : IsPGroup 2 ↥hH.Q := pCoreOf_isPGroup 2 _
  have hQ1 : hH.Q ≠ ⊥ := hH.maximal.1.2.2.2
  have hQTv : hH.Q ≤ hH.Tv v := by
    rw [hQ]
    exact inf_le_inf_left _
      (Subgroup.centralizer_le (t := (V : Set G)) (Set.singleton_subset_iff.mpr hv))
  have hLTv : hH.Lv v ⊔ hH.Tv v ≤ L ⊔ T :=
    sup_le_sup ((oTwoUpper_le _).trans inf_le_left) inf_le_left
  have hVN : hH.Lv v ⊔ hH.Tv v ≤ Subgroup.normalizer (V : Set G) :=
    (sup_le hLvMv hTv.1).trans (hMvMV.trans inf_le_right)
  have hR : hH.Q = pCoreOf 2 (hH.Lv v ⊔ hH.Tv v) := by
    refine le_antisymm ?_ ?_
    · exact le_pCoreOf_of_le_normalizer 2 (hQTv.trans le_sup_right)
        (hLTv.trans (le_normalizer_pCoreOf 2 (L ⊔ T))) hQ2
    · rw [hQ]
      refine le_inf ?_ (pCoreOf_le_centralizer_of_autOn hVN hO2)
      have hsyl : IsSylowTwoOf (hH.Tv v) (hH.Lv v ⊔ hH.Tv v) :=
        A4.isSylowTwoOf_mono hTv le_sup_right (sup_le hLvMv hTv.1)
      exact (B6.pCoreOf_two_le_of_isSylowTwoOf hsyl).trans inf_le_left
  have hNR : hH.Gv v ⊓ Subgroup.normalizer (hH.Q : Set G) ≤ hH.Mv v :=
    (inf_normalizer_le_cgsIn hQ1).trans hcgs
  have hXN : ((hH.Lv v).subgroupOf (hH.Mv v)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLvMv).mpr hMvN
  obtain ⟨hsylK, hO2Q, -, hsylcc⟩ := a4_2_7_rel (oTwoUpper_oTwoUpper _).symm hLvMv hXN
    inf_le_right hTv hR hNR
  have hGv1 : pCoreOf 2 (hH.Gv v) ≠ ⊥ := pCoreOf_centralizer_ne_bot hH.sylow.1 (hVT hv) hv1
    (Lem5.centralizer_le_normalizer_zpowers v)
  refine ⟨hR, hsylK, ?_⟩
  exact { sqtk := sqtkGroup_of_pCoreOf_ne_bot hH.qtke hH.simple hH.nonabelian hGv1
          radical := ⟨hQTv.trans inf_le_right, hQ1, hO2Q⟩
          le := inf_le_right
          cgs := hcgs
          sylow := hsylcc }

theorem stmt12_2_12_two (h1222 : Stmt12_2_2) (h323 : Stmt3_2_3) (h3228 : Stmt3_2_2_eight)
    (hcomp : Lem12212Comp) {G : Type} [Group G] [Finite G] {T L V : Subgroup G}
    (hH : Hyp1223 G T L V) {v : G} (hv : v ∈ V) (hv1 : v ≠ 1)
    (hTv : IsSylowTwoOf (hH.Tv v) (hH.Mv v))
    (hO2 : pCoreOf 2 (autOn (hH.Lv v ⊔ hH.Tv v) V) = ⊥)
    (hperf : autOn (hH.Lv v) V = perfectCore (autOn (hH.Lv v) V)) (hVL : V = ⁅V, hH.Lv v⁆) :
    HypC28 (hH.Gv v) hH.Q (hH.Mv v) (perfectCore (hH.Lv v)) V := by
  obtain ⟨hLvMv, hMvN, hMvC2, hcgs, hMvMV⟩ := stmt12_2_5_of h1222 h323 G T L V hH v hv hv1
  obtain ⟨-, -, hall⟩ := ((h1222 G T hH.simple hH.nonabelian hH.qtke hH.sylow).resolve_left
    hH.notAlt) L hH.maximal hH.faithful hH.quasisimple
  obtain ⟨⟨hVT, hTV, -, -⟩, -, -, hab, -⟩ := hall V hH.irrPlus
  obtain ⟨-, -, hC23⟩ := stmt12_2_12_one h1222 h323 h3228 hH hv hv1 hTv hO2
  have hQ : hH.Q = T ⊓ Subgroup.centralizer (V : Set G) := by
    have := (h3228 G T L V hH.fsu).2.2
    rwa [hH.conjClosure_eq, conjClosure_eq_self_of_normalizes hTV] at this
  have hQV : hH.Q ≤ Subgroup.centralizer (V : Set G) := by rw [hQ]; exact inf_le_right
  have hQTv : hH.Q ≤ hH.Tv v := by
    rw [hQ]
    exact inf_le_inf_left _
      (Subgroup.centralizer_le (t := (V : Set G)) (Set.singleton_subset_iff.mpr hv))
  have hc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (mul_comm (⟨x, hx⟩ : ↥V) ⟨y, hy⟩)
  have hV2 : ∀ x ∈ V, x ^ 2 = 1 := fun x hx => by
    obtain ⟨⟨-, -, hred, -⟩, -⟩ := hall V hH.irrPlus
    have := hred.2.1
    have h2 := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := V.subgroupOf (L ⊔ T))
      (⟨x, (hVT.trans le_sup_right) hx⟩ : ↥(L ⊔ T)) (Subgroup.mem_subgroupOf.mpr hx)
    simpa using congrArg Subtype.val h2
  have hVTv : V ≤ hH.Tv v :=
    le_inf hVT fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr (hc x hx v hv)
  have hMvNV : hH.Mv v ≤ Subgroup.normalizer (V : Set G) := hMvMV.trans inf_le_right
  have hLvNV : hH.Lv v ≤ Subgroup.normalizer (V : Set G) := hLvMv.trans hMvNV
  have hTvNV : hH.Tv v ≤ Subgroup.normalizer (V : Set G) := hTv.1.trans hMvNV
  have hL'Lv : perfectCore (hH.Lv v) ≤ hH.Lv v := perfectCore_le _
  have hL'NV : perfectCore (hH.Lv v) ≤ Subgroup.normalizer (V : Set G) := hL'Lv.trans hLvNV
  have hMvL' : hH.Mv v ≤ Subgroup.normalizer (perfectCore (hH.Lv v) : Set G) :=
    hMvN.trans (normalizer_le_normalizer_perfectCore _)
  have hL'Mv : perfectCore (hH.Lv v) ≤ hH.Mv v := hL'Lv.trans hLvMv
  have hcc : conjClosure (perfectCore (hH.Lv v)) (hH.Mv v) = perfectCore (hH.Lv v) :=
    conjClosure_eq_self_of_normalizes hMvL'
  have haut : autOn (perfectCore (hH.Lv v)) V = autOn (hH.Lv v) V := by
    rw [autOn_perfectCore_eq hLvNV]
    exact hperf.symm
  have hcomm' : ⁅V, perfectCore (hH.Lv v)⁆ = V := by
    rw [commutator_eq_of_autOn_eq hL'NV hLvNV haut]
    exact hVL.symm
  have hVL' : V ≤ perfectCore (hH.Lv v) := by
    calc V = ⁅V, perfectCore (hH.Lv v)⁆ := hcomm'.symm
      _ ≤ perfectCore (hH.Lv v) :=
        commutator_le_of_le_normalizer ((hVTv.trans hTv.1).trans hMvL')
  have hR' : hH.Q = pCoreOf 2 (perfectCore (hH.Lv v) ⊔ hH.Tv v) := by
    refine le_antisymm ?_ ?_
    · refine le_pCoreOf_of_le_normalizer 2 (hQTv.trans le_sup_right) ?_ (pCoreOf_isPGroup 2 _)
      exact (sup_le_sup (hL'Lv.trans ((oTwoUpper_le _).trans inf_le_left)) inf_le_left).trans
        (le_normalizer_pCoreOf 2 (L ⊔ T))
    · rw [hQ]
      have hNV' : perfectCore (hH.Lv v) ⊔ hH.Tv v ≤ Subgroup.normalizer (V : Set G) :=
        sup_le hL'NV hTvNV
      have hO2' : pCoreOf 2 (autOn (perfectCore (hH.Lv v) ⊔ hH.Tv v) V) = ⊥ := by
        rw [autOn_sup_eq_sup_autOn hL'NV hTvNV, haut, ← autOn_sup_eq_sup_autOn hLvNV hTvNV]
        exact hO2
      refine le_inf ?_ (pCoreOf_le_centralizer_of_autOn hNV' hO2')
      have hsyl : IsSylowTwoOf (hH.Tv v) (perfectCore (hH.Lv v) ⊔ hH.Tv v) :=
        A4.isSylowTwoOf_mono hTv le_sup_right (sup_le hL'Mv hTv.1)
      exact (B6.pCoreOf_two_le_of_isSylowTwoOf hsyl).trans inf_le_left
  have hXN : ((perfectCore (hH.Lv v)).subgroupOf (hH.Mv v)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hL'Mv).mpr hMvL'
  obtain ⟨-, -, hsylM, -⟩ := a4_2_7_rel (eq_oTwoUpper_of_perfect (perfectCore_perfect _)) hL'Mv
    hXN le_rfl hTv hR' inf_le_left
  have hQNV : hH.Q ≤ Subgroup.normalizer (V : Set G) := hQTv.trans hTvNV
  have hLQ : perfectCore (hH.Lv v) ⊔ hH.Q ≤ Subgroup.normalizer (V : Set G) := sup_le hL'NV hQNV
  have hautLQ : autOn (perfectCore (hH.Lv v) ⊔ hH.Q) V = autOn (hH.Lv v) V := by
    rw [autOn_sup_eq_sup_autOn hL'NV hQNV, haut, autOn_eq_bot_of_le_centralizer hQV, sup_bot_eq]
  have hO2Lv : pCoreOf 2 (autOn (hH.Lv v) V) = ⊥ := by
    rw [eq_bot_iff, ← hO2]
    refine pCoreOf_le_pCoreOf_of_normal (A4.autOn_mono le_sup_left) ?_
    rw [autOn_sup_eq_sup_autOn hLvNV hTvNV]
    exact sup_le Subgroup.le_normalizer
      (autOn_le_normalizer_autOn hLvNV hTvNV (hTv.1.trans hMvN))
  have hPV : pCoreOf 2 (perfectCore (hH.Lv v) ⊔ hH.Q) ≤ Subgroup.centralizer (V : Set G) :=
    pCoreOf_le_centralizer_of_autOn hLQ (by rw [hautLQ]; exact hO2Lv)
  have hVP : V ≤ pCoreOf 2 (perfectCore (hH.Lv v) ⊔ hH.Q) :=
    le_pCoreOf_of_le_normalizer 2 (hVL'.trans le_sup_left) hLQ (hH.sylow.1.to_le hVT)
  have hNVM : Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (L : Set G) := by
    have h := (stmt12_2_6_of h1222 h323 G T L V hH).2 V (Subgroup.normalizer (V : Set G))
      hH.irrPlus.2.1 le_rfl le_rfl
    intro x hx
    have hx' : x ∈ Subgroup.normalizer (V : Set G) ⊓ Subgroup.normalizer (V : Set G) := ⟨hx, hx⟩
    rw [← h] at hx'
    exact hx'.2
  exact { sqtk := hC23.sqtk
          pgroup := pCoreOf_isPGroup 2 _
          le_M := hQTv.trans hTv.1
          le_H := inf_le_right
          charTwo := hMvC2
          pCore_ne := pCoreOf_centralizer_ne_bot hH.sylow.1 (hVT hv) hv1
            (Lem5.centralizer_le_normalizer_zpowers v)
          comp := hcomp G T L V hH v hv hv1 hTv hO2 hperf hVL
          sylow := by rw [hcc]; exact hsylM
          cgs := hcgs
          V_le := by rw [hcc]; exact hVL'
          V_ne := hH.irrPlus.2.1
          V_elem := ⟨hab, hV2⟩
          V_comm := by rw [hcc]; exact hcomm'
          V_center := by
            rw [hcc]
            exact le_inf hVP (Subgroup.le_centralizer_iff.mp hPV)
          V_norm := fun x hx => ⟨hNVM hx.2, hx.1⟩ }

theorem stmt12_2_12_of_inputs (h1222 : Stmt12_2_2) (h323 : Stmt3_2_3)
    (h3228 : Stmt3_2_2_eight) (hcomp : Lem12212Comp) : Stmt12_2_12 := by
  intro G _ _ T L V hH v hv hv1 hTv hO2
  exact ⟨stmt12_2_12_one h1222 h323 h3228 hH hv hv1 hTv hO2,
    fun hperf hVL => stmt12_2_12_two h1222 h323 h3228 hcomp hH hv hv1 hTv hO2 hperf hVL⟩

end CFSG.Quasithin.H13
