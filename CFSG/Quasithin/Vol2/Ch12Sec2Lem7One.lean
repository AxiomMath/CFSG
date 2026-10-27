module

public import CFSG.Quasithin.Vol2.Ch3Sec1Thm311
public import CFSG.Quasithin.Background.B6Basic
public import CFSG.Quasithin.Background.BlueprintB2Bridge
public import CFSG.Quasithin.Vol2.Ch12Sec2Statements

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

namespace Lem7

theorem omegaOneCenter_inf_ne_bot {T V : Subgroup G} (hT : IsPGroup 2 T) (hVT : V ≤ T)
    (hTV : T ≤ Subgroup.normalizer (V : Set G)) (hV : V ≠ ⊥) (hV2 : ∀ v ∈ V, v ^ 2 = 1) :
    quasithinOmegaOneCenter T ⊓ V ≠ ⊥ := by
  have hnil : Group.IsNilpotent ↥T := hT.isNilpotent
  have hN : (V.subgroupOf T).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVT).mpr hTV
  have hne : V.subgroupOf T ≠ ⊥ := by
    intro h
    apply hV
    rw [eq_bot_iff]
    intro v hv
    have hv' : (⟨v, hVT hv⟩ : ↥T) ∈ V.subgroupOf T := hv
    rw [h, Subgroup.mem_bot] at hv'
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hv')
  obtain ⟨⟨x, hxV, hxZ⟩, hx1⟩ :=
    (Subgroup.ne_bot_iff_exists_ne_one).mp (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  have hx1' : (x : G) ≠ 1 := fun h => hx1 (Subtype.ext (Subtype.ext h))
  have hxV' : (x : G) ∈ V := hxV
  intro hbot
  apply hx1'
  have hmem : (x : G) ∈ quasithinOmegaOneCenter T ⊓ V := by
    refine ⟨Subgroup.subset_closure ⟨⟨x.2, ?_⟩, hV2 _ hxV'⟩, hxV'⟩
    show (x : G) ∈ Subgroup.centralizer (T : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have := Subgroup.mem_center_iff.mp hxZ ⟨t, ht⟩
    exact congrArg Subtype.val this
  rw [hbot] at hmem
  exact Subgroup.mem_bot.mp hmem

theorem centralizer_le_normalizer (h1226 : Stmt12_2_6) {T L V : Subgroup G}
    (hH : Hyp1223 G T L V)
    (hCZ : Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤
      Subgroup.normalizer (L : Set G))
    (hZV : quasithinOmegaOneCenter T ⊓ V ≠ ⊥) :
    Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤
      Subgroup.normalizer (V : Set G) := by
  have hCU : Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤
      Subgroup.normalizer ((quasithinOmegaOneCenter T ⊓ V : Subgroup G) : Set G) :=
    (Subgroup.centralizer_le fun _ hx => hx.1).trans (Subgroup.centralizer_le_normalizer _)
  have h := (h1226 G T L V hH).2 _ _ hZV inf_le_right hCU
  intro x hx
  have hx' : x ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ⊓
      Subgroup.normalizer (L : Set G) := ⟨hx, hCZ hx⟩
  rw [h] at hx'
  exact hx'.2

theorem minParabolic (h331 : Stmt3_3_1) {T L V H : Subgroup G} (hH : Hyp1223 G T L V)
    (hHs : IsHStar T (Subgroup.normalizer (L : Set G)) H) :
    MinParabolic H T (H ⊓ Subgroup.normalizer (L : Set G)) := by
  obtain ⟨S, hS⟩ := exists_sylow_coe_eq hH.sylow
  have hNT : Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (L : Set G) := by
    obtain ⟨-, -, -, hNT, -⟩ :=
      (h331 G T hH.simple hH.nonabelian hH.qtke hH.sylow).2 L hH.maximal hH.quasisimple
    rwa [hH.conjClosure_eq] at hNT
  refine ⟨isSylowTwoOf_of_isSylowTwo hH.sylow hHs.1.1, fun h => hHs.2.1 (h.trans hNT), ?_⟩
  subst hS
  exact IsHStar.isUniqueMaxOver S hHs hH.normalizes

theorem isTwoReducedIn_VZ {T L V H : Subgroup G} (hH : Hyp1223 G T L V)
    (hHs : IsHStar T (Subgroup.normalizer (L : Set G)) H) : IsTwoReducedIn H (VZ T H) :=
  isTwoReducedIn_conjClosure_of_sylowIn hHs.1.1 hH.sylow.1
    (isSylowTwoOf_of_isSylowTwo hH.sylow hHs.1.1).2.2 (charTwo_of_inH' hH.qtke hH.sylow hHs.1)
    le_rfl

omit [Finite G] in
theorem centralizer_VZ_le (T H : Subgroup G) :
    Subgroup.centralizer (VZ T H : Set G) ≤
      Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
  Subgroup.centralizer_le (le_conjClosure _ _)

omit [Finite G] in
theorem not_le_centralizer_VZ {T L H : Subgroup G}
    (hCZ : Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤
      Subgroup.normalizer (L : Set G))
    (hHs : IsHStar T (Subgroup.normalizer (L : Set G)) H) :
    ¬ H ≤ Subgroup.centralizer (VZ T H : Set G) := fun h =>
  hHs.2.1 (h.trans ((centralizer_VZ_le T H).trans hCZ))

end Lem7

open Lem7

theorem stmt12_2_7_one (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h1226 : Stmt12_2_6)
    {T L V H : Subgroup G} (hH : Hyp1223 G T L V)
    (hCZ : Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤
      Subgroup.normalizer (L : Set G))
    (hHs : IsHStar T (Subgroup.normalizer (L : Set G)) H) :
    IsPrimeReduced 2 ((VZ T H).subgroupOf H) ∧
      T ⊓ Subgroup.centralizer (VZ T H : Set G) = pCoreOf 2 H ∧
      pCoreOf 2 H ≤ H ⊓ Subgroup.centralizer (VZ T H : Set G) ∧
      H ⊓ Subgroup.centralizer (VZ T H : Set G) ≤
        kerIn (H ⊓ Subgroup.normalizer (V : Set G)) H := by
  have hU := isTwoReducedIn_VZ hH hHs
  have hmin := minParabolic h331 hH hHs
  obtain ⟨-, -, hall⟩ := ((h1222 G T hH.simple hH.nonabelian hH.qtke hH.sylow).resolve_left
    hH.notAlt) L hH.maximal hH.faithful hH.quasisimple
  obtain ⟨⟨hVT, hTV, hred, -⟩, -, -, -, -⟩ := hall V hH.irrPlus
  have hVLT : V ≤ L ⊔ T := hVT.trans le_sup_right
  have hV2 : ∀ v ∈ V, v ^ 2 = 1 := fun v hv => by
    have := hred.2.1
    have h2 := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := V.subgroupOf (L ⊔ T))
      (⟨v, hVLT hv⟩ : ↥(L ⊔ T)) (Subgroup.mem_subgroupOf.mpr hv)
    simpa using congrArg Subtype.val h2
  have hZV := omegaOneCenter_inf_ne_bot hH.sylow.1 hVT hTV hH.irrPlus.2.1 hV2
  have hCN := Lem7.centralizer_le_normalizer h1226 hH hCZ hZV
  refine ⟨(isTwoReducedIn_iff_isPrimeReduced_subgroupOf.mp hU).2,
    hmin.inf_centralizer_eq_pCoreOf hU (not_le_centralizer_VZ hCZ hHs),
    le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 H) (MinParabolic.pCoreOf_le_centralizer hU), ?_⟩
  intro x hx
  rw [mem_kerIn]
  intro b hb
  have hbx : b * x * b⁻¹ ∈ Subgroup.centralizer (VZ T H : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : b⁻¹ * y * b ∈ VZ T H := by
      have := (Subgroup.mem_normalizer_iff.mp (hU.2.1 (H.inv_mem hb)) y).mp hy
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.mp hx.2 _ hy'
    calc y * (b * x * b⁻¹) = b * ((b⁻¹ * y * b) * x) * b⁻¹ := by group
      _ = b * (x * (b⁻¹ * y * b)) * b⁻¹ := by rw [h1]
      _ = b * x * b⁻¹ * y := by group
  exact ⟨H.mul_mem (H.mul_mem hb hx.1) (H.inv_mem hb), hCN (centralizer_VZ_le T H hbx)⟩

end CFSG.Quasithin.H13
