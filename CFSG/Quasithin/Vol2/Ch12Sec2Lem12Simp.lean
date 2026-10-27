module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem12
public import CFSG.Quasithin.EmptyFaithful.S151S9UPerf
public import CFSG.Quasithin.Vol2.Ch7Faith
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem21Post
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped IsMulCommutative

@[expose] def StabSimple12_2_12 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V : Subgroup G) [IsMulCommutative ↥V],
    (∀ x ∈ V, x ^ 2 = 1) → L ≤ Subgroup.normalizer (V : Set G) →
    CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) →
    pCoreOf 2 L ≤ Subgroup.centralizer (V : Set G) →
    (∀ J : Subgroup G, V ⊓ Subgroup.centralizer (L : Set G) ≤ J → J ≤ V →
      L ≤ Subgroup.normalizer (J : Set G) →
        J = V ⊓ Subgroup.centralizer (L : Set G) ∨ J = V) →
    Modules12_2_2 L V →
    ∀ v ∈ V, v ≠ 1 →
      autOn (oTwoUpper (L ⊓ Subgroup.centralizer ({v} : Set G))) V =
        perfectCore (autOn (oTwoUpper (L ⊓ Subgroup.centralizer ({v} : Set G))) V) →
      pCoreOf 2 (autOn (oTwoUpper (L ⊓ Subgroup.centralizer ({v} : Set G))) V) = ⊥ →
      V = ⁅V, oTwoUpper (L ⊓ Subgroup.centralizer ({v} : Set G))⁆ →
        IsSimpleGroup ↥(autOn (oTwoUpper (L ⊓ Subgroup.centralizer ({v} : Set G))) V)

namespace Lem12Simp

variable {G : Type} [Group G] [Finite G]

theorem isSolvable_inf_centralizer {L V : Subgroup G}
    (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)) (hLN : L ≤ Subgroup.normalizer (V : Set G))
    (hO2 : pCoreOf 2 L ≤ Subgroup.centralizer (V : Set G))
    (hLC : ¬ L ≤ Subgroup.centralizer (V : Set G)) :
    Group.IsSolvable ↥(L ⊓ Subgroup.centralizer (V : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := L ⊓ Subgroup.centralizer (V : Set G) with hK
  have hcomm := commutatorElement_mem_pCoreOf hq hLN hO2 hLC
  have hKK : ⁅K, K⁆ ≤ pCoreOf 2 L :=
    Subgroup.commutator_le.mpr fun x hx y hy => hcomm x hx y hy.1
  have h2 : IsPGroup 2 ↥(commutator ↥K) := by
    have h1 : IsPGroup 2 ↥(pCoreOf 2 L) := pCoreOf_isPGroup 2 L
    intro x
    have hx : ((x : ↥K) : G) ∈ ⁅K, K⁆ := by
      have hmap : (commutator ↥K).map K.subtype = ⁅K, K⁆ := by
        rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
          Subgroup.range_subtype]
      rw [← hmap]
      exact ⟨x, x.2, rfl⟩
    obtain ⟨n, hn⟩ := h1 ⟨_, hKK hx⟩
    refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg Subtype.val hn
    simpa using this
  have : Group.IsSolvable ↥(commutator ↥K) := by
    have := h2.isNilpotent
    infer_instance
  exact Group.isSolvable_of_ker_le_range (commutator ↥K).subtype Abelianization.of
    (by rw [Abelianization.ker_of, Subgroup.range_subtype])

end Lem12Simp

open Lem12 Lem12Simp

theorem lem12212Comp_of (h1222 : Stmt12_2_2) (h323 : Stmt3_2_3) (hS : StabSimple12_2_12) :
    Lem12212Comp := by
  intro G _ _ T L V hH v hv hv1 hTv hO2 hperf hVL
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hLvMv, hMvN, -, -, hMvMV⟩ := stmt12_2_5_of h1222 h323 G T L V hH v hv hv1
  obtain ⟨-, -, hall⟩ := ((h1222 G T hH.simple hH.nonabelian hH.qtke hH.sylow).resolve_left
    hH.notAlt) L hH.maximal hH.faithful hH.quasisimple
  obtain ⟨⟨hVT, -, hred, -⟩, -, -, hab, hmod⟩ := hall V hH.irrPlus
  have hV2 : ∀ x ∈ V, x ^ 2 = 1 := fun x hx => by
    have := hred.2.1
    have h2 := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := V.subgroupOf (L ⊔ T))
      (⟨x, (hVT.trans le_sup_right) hx⟩ : ↥(L ⊔ T)) (Subgroup.mem_subgroupOf.mpr hx)
    simpa using congrArg Subtype.val h2
  have hLNV : L ≤ Subgroup.normalizer (V : Set G) := hH.irrPlus.2.2.1
  have hMvNV : hH.Mv v ≤ Subgroup.normalizer (V : Set G) := hMvMV.trans inf_le_right
  have hLvNV : hH.Lv v ≤ Subgroup.normalizer (V : Set G) := hLvMv.trans hMvNV
  have hTvNV : hH.Tv v ≤ Subgroup.normalizer (V : Set G) := hTv.1.trans hMvNV
  have hO2Lv : pCoreOf 2 (autOn (hH.Lv v) V) = ⊥ := by
    rw [eq_bot_iff, ← hO2]
    refine pCoreOf_le_pCoreOf_of_normal (A4.autOn_mono le_sup_left) ?_
    rw [autOn_sup_eq_sup_autOn hLvNV hTvNV]
    exact sup_le Subgroup.le_normalizer
      (autOn_le_normalizer_autOn hLvNV hTvNV (hTv.1.trans hMvN))
  have hO2L : pCoreOf 2 L ≤ Subgroup.centralizer (V : Set G) :=
    (pCoreOf_le_pCoreOf_of_normal (le_sup_left : L ≤ L ⊔ T)
      (sup_le Subgroup.le_normalizer hH.normalizes)).trans
      (Lem21Post.pCoreOf_sup_le_centralizer (hVT.trans le_sup_right) hred)
  have hsimple : IsSimpleGroup ↥(autOn (hH.Lv v) V) :=
    hS G L V hV2 hLNV hH.quasisimple hO2L hH.irrPlus.2.2.2.2.2.1 hmod v hv hv1 hperf hO2Lv hVL
  have hLC : ¬ L ≤ Subgroup.centralizer (V : Set G) := by
    intro hle
    apply hH.irrPlus.2.1
    rw [← hH.irrPlus.2.2.2.1, Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact Subgroup.le_centralizer_iff.mp hle
  have hCL := isSolvable_inf_centralizer hH.quasisimple hLNV hO2L hLC
  set Y := perfectCore (hH.Lv v) with hY
  have hYLv : Y ≤ hH.Lv v := perfectCore_le _
  have hYL : Y ≤ L := hYLv.trans ((oTwoUpper_le _).trans inf_le_left)
  have hYNV : Y ≤ Subgroup.normalizer (V : Set G) := hYLv.trans hLvNV
  have haut : autOn Y V = autOn (hH.Lv v) V := by
    rw [hY, autOn_perfectCore_eq hLvNV]
    exact hperf.symm
  have hmemY : ∀ y : ↥Y, A4.actionOn V Y hYNV y ∈ autOn (hH.Lv v) V := fun y => by
    rw [← haut]
    exact (A4.mem_autOn_iff hYNV).mpr ⟨y, rfl⟩
  let ψ : ↥Y →* ↥(autOn (hH.Lv v) V) := (A4.actionOn V Y hYNV).codRestrict _ hmemY
  have hψ : Function.Surjective ψ := by
    rintro ⟨a, ha⟩
    rw [← haut] at ha
    obtain ⟨y, rfl⟩ := (A4.mem_autOn_iff hYNV).mp ha
    exact ⟨y, rfl⟩
  have hker : Group.IsSolvable ↥ψ.ker := by
    have hmap : ∀ y : ↥ψ.ker, ((y : ↥Y) : G) ∈ L ⊓ Subgroup.centralizer (V : Set G) := by
      intro y
      have h1 : ψ (y : ↥Y) = 1 := y.2
      have h2 : A4.actionOn V Y hYNV (y : ↥Y) = 1 := congrArg Subtype.val h1
      exact ⟨hYL (y : ↥Y).2, (A4.actionOn_eq_one_iff hYNV _).mp h2⟩
    let ι : ↥ψ.ker →* ↥(L ⊓ Subgroup.centralizer (V : Set G)) :=
      (Y.subtype.comp ψ.ker.subtype).codRestrict _ hmap
    refine Group.isSolvable_of_isSolvable_injective (f := ι) fun a b hab => ?_
    have := congrArg Subtype.val hab
    exact Subtype.ext (Subtype.ext this)
  have hYne : Y ≠ ⊥ := by
    intro h0
    have h1 : autOn (hH.Lv v) V = ⊥ := by
      rw [← haut, h0, eq_bot_iff]
      intro a ha
      obtain ⟨y, rfl⟩ := (A4.mem_autOn_iff (h0 ▸ hYNV)).mp ha
      have hy : (y : G) = 1 := y.2
      rw [Subgroup.mem_bot]
      refine (A4.actionOn_eq_one_iff _ y).mpr ?_
      rw [hy]
      exact Subgroup.one_mem _
    have := hsimple.toNontrivial
    rw [h1] at this
    exact (Subgroup.nontrivial_iff_ne_bot ⊥).mp this rfl
  have hYY : Y ∈ cComp Y :=
    S151S9U.mem_cComp_self_of_simple_quotient ψ hψ hYne (perfectCore_perfect _) hker
  have hYMv : Y ≤ hH.Mv v := hYLv.trans hLvMv
  have hMvY : hH.Mv v ≤ Subgroup.normalizer (Y : Set G) :=
    hMvN.trans (normalizer_le_normalizer_perfectCore _)
  have hsub : IsSubnormal Y (hH.Mv v) :=
    A3.subnormal_of_normal hYMv ((Subgroup.normal_subgroupOf_iff_le_normalizer hYMv).mpr hMvY)
  exact cComp_mem_of_subnormal hsub hYY

theorem stmt12_2_12_of_stab (h1222 : Stmt12_2_2) (h323 : Stmt3_2_3)
    (h3228 : Stmt3_2_2_eight) (hS : StabSimple12_2_12) : Stmt12_2_12 :=
  stmt12_2_12_of_inputs h1222 h323 h3228 (lem12212Comp_of h1222 h323 hS)

end CFSG.Quasithin.H13
