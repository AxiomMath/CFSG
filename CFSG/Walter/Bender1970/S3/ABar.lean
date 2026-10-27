module

public import CFSG.Walter.Bender1970.S3.Tools
public import CFSG.Walter.Bender1970.S3.Coprime
public import CFSG.Assembly.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.SubnormalPSubgroupLeQCore
public import CFSG.Walter.Bender1970.S1.EqualityOfMaximal
public import CFSG.Walter.Bender1970.S1.EqualityOfMaximalFitting
public import CFSG.Walter.Bender1970.S3.Basic

public section

namespace CFSG.Walter

open CFSG.GorensteinWalter

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_normalizer_inf {A B : Subgroup G} {g : G} (hA : g ∈ Subgroup.normalizer (A : Set G))
    (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro x
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hA, hB]

theorem subnormal_of_commutator_eq
    {B H V U : Subgroup G} (hB : IsAStar B) {t : G}
    (htB : t ∈ B) (ht : orderOf t = 2) (hCH : Subgroup.centralizer ({t} : Set G) ≤ H)
    (hVF : V ≤ generalizedFittingSubgroupOf H)
    (hV : (V.subgroupOf (generalizedFittingSubgroupOf H)).IsSubnormal)
    (hVB : V ⊔ Subgroup.centralizer (V : Set G) ≤ B)
    (hUF : U ≤ generalizedFittingSubgroupOf H)
    (hU : (U.subgroupOf (generalizedFittingSubgroupOf H)).IsSubnormal)
    (hUV : U ≤ Subgroup.centralizer (V : Set G)) (hUt : ⁅U, Subgroup.zpowers t⁆ = U) :
    U ≤ generalizedFittingSubgroupOf B ∧
      (U.subgroupOf (generalizedFittingSubgroupOf B)).IsSubnormal := by
  set F := generalizedFittingSubgroupOf H
  set Y := B ⊓ F with hYdef
  have hFH : F ≤ H := generalizedFittingSubgroupOf_le H
  have hEY : componentLayerOf H ≤ Y :=
    le_inf ((componentLayerOf_le_sup_centralizer (hVF.trans hFH)
      (isSubnormal_subgroupOf_of_isSubnormal_generalizedFitting hVF hV)).trans hVB) le_sup_right
  have hYF : Y ≤ F := inf_le_right
  have hYeq : generalizedFittingSubgroupOf Y = Y :=
    generalizedFittingSubgroupOf_eq_self_of_componentLayerOf_le hEY hYF
  have hCY : B ⊓ Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (Y : Set G) := by
    rintro c ⟨hcB, hcC⟩
    exact mem_normalizer_inf (Subgroup.le_normalizer hcB)
      (le_normalizer_of_isNormalIn (generalizedFittingSubgroupOf_isNormalIn H) (hCH hcC))
  obtain ⟨h1, h2⟩ := bender1970_2_4_subgroup hB htB ht inf_le_left hCY hYeq
  have htY : t ∈ Subgroup.normalizer (Y : Set G) :=
    hCY ⟨htB, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hUY : U ≤ Y := le_inf (hUV.trans (le_sup_right.trans hVB)) hUF
  have hUW : U ≤ ⁅Y, Subgroup.zpowers t⁆ := hUt ▸ Subgroup.commutator_mono hUY le_rfl
  have hWF : ⁅Y, Subgroup.zpowers t⁆ ≤ F := (commutator_zpowers_le_of_mem_normalizer htY).trans hYF
  exact ⟨hUW.trans h1,
    isSubnormal_subgroupOf_trans hUW (isSubnormal_subgroupOf_of_le hUW hWF hU) h2⟩

theorem centralizer_ne_bot_of_isPGroup {V : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hVp : IsPGroup p V) (hV1 : V ≠ ⊥) : Subgroup.centralizer (V : Set G) ≠ ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  have : Nontrivial V := (Subgroup.nontrivial_iff_ne_bot V).mpr hV1
  have := hVp.center_nontrivial
  obtain ⟨z, hz⟩ := exists_ne (1 : Subgroup.center V)
  intro h
  have hzC : ((z : V) : G) ∈ Subgroup.centralizer (V : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp z.2) ⟨v, hv⟩)
  rw [h, Subgroup.mem_bot] at hzC
  exact hz (Subtype.ext (Subtype.ext hzC))

theorem isPGroup_generalizedFitting_of_qCoreOf_eq_bot {B : Subgroup G} {p : ℕ}
    (hq : ∀ q : ℕ, q.Prime → q ≠ p → qCoreOf B q = ⊥) (hE : componentLayerOf B = ⊥) :
    IsPGroup p (generalizedFittingSubgroupOf B) := by
  have hle : generalizedFittingSubgroupOf B ≤ qCoreOf B p := by
    refine sup_le ?_ (hE ▸ bot_le)
    rw [fittingSubgroupOf_eq_iSup_qCoreOf B]
    refine iSup_le fun q => ?_
    have hqp : q.1.1.Prime := Nat.prime_of_mem_primeFactors q.1.2
    by_cases h : q.1.1 = p
    · rw [h]
    · rw [hq _ hqp h]
      exact bot_le
  exact (qCoreOf_isPGroup B p).to_le hle

theorem BenderCounterexample.isPGroup_generalizedFitting_centralizer_of_commutator_eq
    (hG : BenderCounterexample G) {t : G} (ht : orderOf t = 2) {H : Subgroup G}
    (hH : IsCoatom H) (hCH : Subgroup.centralizer ({t} : Set G) ≤ H) {p : ℕ} (hp : p.Prime)
    (hFp : IsPGroup p (generalizedFittingSubgroupOf H)) {V : Subgroup G} (hV1 : V ≠ ⊥)
    (hVF : V ≤ generalizedFittingSubgroupOf H)
    (hV : (V.subgroupOf (generalizedFittingSubgroupOf H)).IsSubnormal)
    (hVt : t ∈ Subgroup.normalizer (V : Set G)) {U : Subgroup G}
    (hUF : U ≤ generalizedFittingSubgroupOf H)
    (hU : (U.subgroupOf (generalizedFittingSubgroupOf H)).IsSubnormal)
    (hUC : IsPGroup p (generalizedFittingSubgroupOf (Subgroup.centralizer (U : Set G))))
    (hUV : U ≤ Subgroup.centralizer (V : Set G)) (hUt : ⁅U, Subgroup.zpowers t⁆ = U) :
    IsPGroup p (generalizedFittingSubgroupOf (Subgroup.centralizer (V : Set G))) := by
  have : Fact p.Prime := ⟨hp⟩
  have hFH := generalizedFittingSubgroupOf_le H
  set B := (V ⊔ Subgroup.centralizer (V : Set G)) ⊔ Subgroup.zpowers t with hBdef
  have hBN : B ≤ Subgroup.normalizer (V : Set G) :=
    sup_le (sup_centralizer_le_normalizer V) (Subgroup.zpowers_le.mpr hVt)
  have hBtop : B ≠ ⊤ := fun h => hG.normalizer_ne_top hV1
    (fun h' => hH.1 (top_le_iff.mp (h' ▸ hVF.trans hFH))) (top_le_iff.mp (h ▸ hBN))
  have hBA : IsAStar B := hG.isAStar B hBtop
  have htB : t ∈ B := (le_sup_right : Subgroup.zpowers t ≤ B) (Subgroup.mem_zpowers t)
  have hVCB : V ⊔ Subgroup.centralizer (V : Set G) ≤ B := le_sup_left
  obtain ⟨hUFB, hUB⟩ := subnormal_of_commutator_eq hBA htB ht hCH hVF hV hVCB hUF hU hUV hUt
  have hUp : IsPGroup p U := hFp.to_le hUF
  have hVp : IsPGroup p V := hFp.to_le hVF
  have hUOp : U ≤ qCoreOf B p :=
    le_qCoreOf_of_isSubnormal_isPGroup B U p (hUFB.trans (generalizedFittingSubgroupOf_le B))
      (isSubnormal_subgroupOf_of_isSubnormal_generalizedFitting hUFB hUB) hUp
  have hVn : IsNormalIn V B := ⟨le_sup_left.trans hVCB, fun b hb v hv =>
    (Subgroup.mem_normalizer_iff.mp (hBN hb) v).mp hv⟩
  have hVOp : V ≤ qCoreOf B p :=
    le_qCoreOf_of_isSubnormal_isPGroup B V p hVn.1 (isSubnormal_subgroupOf_of_isNormalIn hVn) hVp
  set Y := Subgroup.centralizer (U : Set G) ⊓ Subgroup.centralizer (V : Set G) with hYdef
  have hYp : IsPGroup p (generalizedFittingSubgroupOf Y) :=
    isPGroup_generalizedFitting_inf_centralizer hp hUC (Subgroup.le_centralizer_iff.mp hUV) hVp
  have hYB : Y ≤ B := inf_le_right.trans (le_sup_right.trans hVCB)
  have hCOp : Subgroup.centralizer (qCoreOf B p : Set G) ≤ Y :=
    le_inf (Subgroup.centralizer_le hUOp) (Subgroup.centralizer_le hVOp)
  have hq : ∀ q : ℕ, q.Prime → q ≠ p → qCoreOf B q = ⊥ := by
    intro q hq hqp
    by_contra hne
    have hOY : qCoreOf B q ≤ Y := (qCoreOf_centralizer_of_ne B hp hq (Ne.symm hqp)).trans hCOp
    have hOn : IsNormalIn (qCoreOf B q) Y :=
      ⟨hOY, fun y hy x hx => (qCoreOf_normal_in B q).2 y (hYB hy) x hx⟩
    have : Fact q.Prime := ⟨hq⟩
    have hOF : qCoreOf B q ≤ generalizedFittingSubgroupOf Y :=
      (le_fittingSubgroupOf_of_isNormalIn_nilpotent hOY hOn
        (qCoreOf_isPGroup B q).isNilpotent).trans le_sup_left
    exact hqp (eq_of_isPGroup_of_isPGroup hq hp (qCoreOf_isPGroup B q) (hYp.to_le hOF) hne)
  have hE : componentLayerOf B = ⊥ := by
    refine eq_bot_iff.mpr (sSup_le fun K hK => ?_)
    exfalso
    have hKY : K ≤ Y := (Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (component_centralizes_fittingSubgroupOf hK)).trans
        (Subgroup.centralizer_le (qCoreOf_le_fittingSubgroupOf B p hp)) |>.trans hCOp
    have hKc : IsComponentOf K Y := ⟨hKY, isSubnormal_subgroupOf_of_le hKY hYB hK.2.1, hK.2.2⟩
    have hKF : K ≤ generalizedFittingSubgroupOf Y :=
      (le_sSup (s := {E : Subgroup G | IsComponentOf E Y}) hKc).trans le_sup_right
    exact not_isNilpotent_of_isQuasisimple K hK.2.2 (hYp.to_le hKF).isNilpotent
  have hBp := isPGroup_generalizedFitting_of_qCoreOf_eq_bot hq hE
  have hCn : IsNormalIn (Subgroup.centralizer (V : Set G)) B :=
    isNormalIn_centralizer hVn (le_sup_right.trans hVCB)
  exact hBp.to_le (generalizedFittingSubgroupOf_le_of_isNormalIn hCn)

theorem BenderCounterexample.mem_benderABar_of_commutator_eq
    (hG : BenderCounterexample G)
    {t : G} (ht : orderOf t = 2) {H : Subgroup G} (hH : IsCoatom H)
    (hCH : Subgroup.centralizer ({t} : Set G) ≤ H) {V : Subgroup G} (hV1 : V ≠ ⊥)
    (hVF : V ≤ generalizedFittingSubgroupOf H)
    (hV : (V.subgroupOf (generalizedFittingSubgroupOf H)).IsSubnormal)
    (hVt : t ∈ Subgroup.normalizer (V : Set G)) {U : Subgroup G} (hUA : U ∈ benderABar H)
    (hUV : U ≤ Subgroup.centralizer (V : Set G)) (hUt : ⁅U, Subgroup.zpowers t⁆ = U) :
    V ∈ benderABar H := by
  have hsimple := hG.isSimpleGroup
  have hFH := generalizedFittingSubgroupOf_le H
  have hVH : V ≤ H := hVF.trans hFH
  refine ⟨hVF, hV, fun hπ => ?_, fun hπ => ?_⟩
  · obtain ⟨B, hB, hNB⟩ := hG.exists_isCoatom_normalizer_le hH hVH hV1
    have hBA := hG.isAStar_of_isCoatom hB
    have htB : t ∈ B := hNB hVt
    have hVCB : V ⊔ Subgroup.centralizer (V : Set G) ≤ B :=
      (sup_centralizer_le_normalizer V).trans hNB
    obtain ⟨hUFB, hUB⟩ :=
      subnormal_of_commutator_eq hBA htB ht hCH hVF hV hVCB hUA.1 hUA.2.1 hUV hUt
    have hSbarH : subnormalHull B U ≤ H :=
      (subnormalHull_le_sup_centralizer hUFB hUB).trans
        ((sup_centralizer_le_normalizer U).trans (hUA.2.2.1 hπ))
    have hHB : H = B := bender1970_1_7_iii_equalityOfMaximal hsimple H hH (subnormalHull H V)
      (subnormalHull_le_generalizedFitting hVF) (isSubnormal_subnormalHull hVF hV)
      (generalizedFitting_inf_centralizer_subnormalHull_le H V)
      ((subnormalHull_le_sup_centralizer hVF hV).trans hVCB) hB (Or.inl hπ)
      ⟨subnormalHull B U, hSbarH, subnormalHull_le_generalizedFitting hUFB,
        isSubnormal_subnormalHull hUFB hUB, generalizedFitting_inf_centralizer_subnormalHull_le B U⟩
    exact hHB ▸ hNB
  · obtain ⟨p, hp, hFp, -, hπp⟩ := exists_isPGroup_of_card_primesOfOrder_eq_one hπ
    have hUC : IsPGroup p (generalizedFittingSubgroupOf (Subgroup.centralizer (U : Set G))) := by
      have h := hUA.2.2.2 hπ
      rw [hπp] at h
      exact isPGroup_of_primesOfOrder_subset hp h.le
    have h := hG.isPGroup_generalizedFitting_centralizer_of_commutator_eq ht hH hCH hp hFp hV1
      hVF hV hVt hUA.1 hUA.2.1 hUC hUV hUt
    rw [hπp]
    exact primesOfOrder_generalizedFitting_eq_singleton hp h
      (centralizer_ne_bot_of_isPGroup hp (hFp.to_le hVF) hV1)

theorem BenderCounterexample.mem_benderABar_of_centralizer_le_normalizer
    (hG : BenderCounterexample G) {t : G} (ht : orderOf t = 2) {H : Subgroup G}
    (hH : H ∈ benderM t) {V : Subgroup G} (hV1 : V ≠ ⊥)
    (hVF : V ≤ generalizedFittingSubgroupOf H)
    (hV : (V.subgroupOf (generalizedFittingSubgroupOf H)).IsSubnormal)
    (hVC : Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (V : Set G)) :
    V ∈ benderABar H := by
  have hsimple := hG.isSimpleGroup
  obtain ⟨hHco, hCH, hcase⟩ := hH
  have htC : t ∈ Subgroup.centralizer ({t} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have htH : t ∈ H := hCH htC
  have hVt : t ∈ Subgroup.normalizer (V : Set G) := hVC htC
  have hFH := generalizedFittingSubgroupOf_le H
  have hVH : V ≤ H := hVF.trans hFH
  rcases hcase with ⟨p, hp, hne, hfix⟩ | ⟨hnone, hmax⟩
  ·
    obtain ⟨-, -, -, hUt, hUcent⟩ := qCoreOf_props_of_fixedPointFree htH ht hp hfix
    exact hG.mem_benderABar_of_commutator_eq ht hHco hCH hV1 hVF hV hVt
      (hG.qCoreOf_mem_benderABar hHco htH ht hp hne hfix)
      (Subgroup.le_centralizer_iff.mp (hVF.trans hUcent)) hUt
  obtain ⟨B, hB, hNB⟩ := hG.exists_isCoatom_normalizer_le hHco hVH hV1
  have hCB : Subgroup.centralizer ({t} : Set G) ≤ B := hVC.trans hNB
  have hVCB : V ⊔ Subgroup.centralizer (V : Set G) ≤ B :=
    (sup_centralizer_le_normalizer V).trans hNB
  have hO : ∀ q : ℕ, q.Prime → q ∉ primesOfOrder (CFSG.fittingSubgroupOf H) →
      qCoreOf B q = ⊥ := by
    intro q hq hqπ
    by_contra hne
    have h1 := qCoreOf_inf_eq_bot_of_sup_centralizer_le hsimple hHco hVF hV hVCB hq hqπ
    refine hnone B hB hCB ⟨q, hq, hne, eq_bot_iff.mpr fun x hx => ?_⟩
    rw [← h1]
    exact ⟨hx.1, hCH hx.2⟩
  have hE := hmax B hB hCB
  have hBA := hG.isAStar_of_isCoatom hB
  have hSF := subnormalHull_le_generalizedFitting hVF
  have hSsn := isSubnormal_subnormalHull hVF hV
  have hSC := generalizedFitting_inf_centralizer_subnormalHull_le H V
  have hSB := (subnormalHull_le_sup_centralizer hVF hV).trans hVCB
  refine ⟨hVF, hV, fun hπ => ?_, fun hπ => ?_⟩
  · have hHB := bender1970_1_7_iv_equalityOfMaximal hsimple H hHco (subnormalHull H V) hSF hSsn
      hSC hSB hB (Or.inl hπ) hBA hE hO
    exact hHB ▸ hNB
  · obtain ⟨p, hp, hFp, -, hπp⟩ := exists_isPGroup_of_card_primesOfOrder_eq_one hπ
    have hπB : ¬ 2 ≤ Nat.card (primesOfOrder (generalizedFittingSubgroupOf B)) := by
      intro h2
      have hHB := bender1970_1_7_iv_equalityOfMaximal hsimple H hHco (subnormalHull H V) hSF hSsn
        hSC hSB hB (Or.inr h2) hBA hE hO
      rw [← hHB] at h2
      omega
    have hB1 : B ≠ ⊥ := fun h => hG.bot_not_isCoatom (h ▸ hB)
    have hπB1 : Nat.card (primesOfOrder (generalizedFittingSubgroupOf B)) = 1 :=
      le_antisymm (by omega) (one_le_card_primesOfOrder (generalizedFittingSubgroupOf_ne_bot hB1))
    obtain ⟨r, hr, hFBr, hFB1, -⟩ := exists_isPGroup_of_card_primesOfOrder_eq_one hπB1
    have hEB : componentLayerOf B = ⊥ := componentLayerOf_eq_bot_of_isPGroup B hr hFBr
    have hOr : qCoreOf B r = CFSG.fittingSubgroupOf B :=
      qCoreOf_eq_fittingSubgroupOf_of_isPGroup B hr hFBr
    have hOr1 : qCoreOf B r ≠ ⊥ := by
      rw [hOr]
      intro h
      apply hFB1
      rw [generalizedFittingSubgroupOf, hEB,
        show CFSG.GorensteinWalter.fittingSubgroupOf B = ⊥ from h, sup_bot_eq]
    have hrπ : r ∈ primesOfOrder (CFSG.fittingSubgroupOf H) := by
      by_contra h
      exact hOr1 (hO r hr h)
    have hrp : r = p :=
      primesOfOrder_subset_of_isPGroup hp (hFp.to_le le_sup_left) hrπ
    subst hrp
    have h := isPGroup_generalizedFitting_inf_centralizer hr hFBr (le_sup_left.trans hVCB)
      (hFp.to_le hVF)
    rw [inf_eq_right.mpr (le_sup_right.trans hVCB)] at h
    rw [hπp]
    exact primesOfOrder_generalizedFitting_eq_singleton hr h
      (centralizer_ne_bot_of_isPGroup hr (hFp.to_le hVF) hV1)

theorem mem_fittingSubgroupOf_of_zpowers_mem_benderABar {H : Subgroup G} {u : G}
    (hu : Subgroup.zpowers u ∈ benderABar H) : u ∈ CFSG.fittingSubgroupOf H := by
  have hnil : Group.IsNilpotent (Subgroup.zpowers u) := by
    have : IsMulCommutative (Subgroup.zpowers u) := inferInstance
    exact CommGroup.isNilpotent
  exact le_fittingSubgroupOf_of_isSubnormal (hu.1.trans (generalizedFittingSubgroupOf_le H))
    (isSubnormal_subgroupOf_of_isSubnormal_generalizedFitting hu.1 hu.2.1) hnil
    (Subgroup.mem_zpowers u)

omit [Finite G] in
theorem centralizer_singleton_le_normalizer_zpowers (u : G) :
    Subgroup.centralizer ({u} : Set G) ≤ Subgroup.normalizer ((Subgroup.zpowers u : Subgroup G) :
      Set G) := by
  rw [← centralizer_zpowers_eq']
  exact Subgroup.centralizer_le_normalizer _

theorem BenderCounterexample.mem_benderABar_of_noncyclic
    (hG : BenderCounterexample G)
    {t : G} (ht : orderOf t = 2) {H : Subgroup G} (hH : IsCoatom H)
    (hCH : Subgroup.centralizer ({t} : Set G) ≤ H) {V : Subgroup G} (hV1 : V ≠ ⊥)
    (hVF : V ≤ generalizedFittingSubgroupOf H)
    (hV : (V.subgroupOf (generalizedFittingSubgroupOf H)).IsSubnormal)
    (hVt : t ∈ Subgroup.normalizer (V : Set G)) {U : Subgroup G}
    (hUC : U ≤ Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer (V : Set G))
    (hUcomm : IsMulCommutative U) (hUcyc : ¬ IsCyclic U) (hUodd : Odd (Nat.card U))
    (hUA : ∀ u ∈ U, u ≠ 1 → Subgroup.zpowers u ∈ benderABar H) :
    V ∈ benderABar H := by
  have hsimple := hG.isSimpleGroup
  have hFH := generalizedFittingSubgroupOf_le H
  have hVH : V ≤ H := hVF.trans hFH
  have hUF : U ≤ CFSG.fittingSubgroupOf H := by
    intro u hu
    by_cases hu1 : u = 1
    · rw [hu1]
      exact one_mem _
    · exact mem_fittingSubgroupOf_of_zpowers_mem_benderABar (hUA u hu hu1)
  have hUO : U ≤ oddCoreOf (CFSG.fittingSubgroupOf H) :=
    le_oddCoreOf_of_odd (CFSG.fittingSubgroupOf_isNilpotent H) hUF hUodd
  have hUt : U ≤ Subgroup.centralizer ({t} : Set G) := hUC.trans inf_le_left
  have hUV : U ≤ Subgroup.centralizer (V : Set G) := hUC.trans inf_le_right
  have hUOX : ∀ X : Subgroup G, U ≤ X →
      U ≤ oddCoreOf (CFSG.fittingSubgroupOf (X ⊓ Subgroup.centralizer ({t} : Set G))) :=
    fun X hUX => (le_inf hUO (le_inf hUX hUt)).trans
      (oddCoreOf_fitting_inf_le (inf_le_right.trans hCH))
  refine ⟨hVF, hV, fun hπ => ?_, fun hπ => ?_⟩
  ·
    have hCu : ∀ u ∈ U, u ≠ 1 → Subgroup.centralizer ({u} : Set G) ≤ H := fun u hu hu1 =>
      (centralizer_singleton_le_normalizer_zpowers u).trans ((hUA u hu hu1).2.2.1 hπ)
    obtain ⟨B, hB, hNB⟩ := hG.exists_isCoatom_normalizer_le hH hVH hV1
    have hBA := hG.isAStar_of_isCoatom hB
    have htB : t ∈ B := hNB hVt
    have hVCB : V ⊔ Subgroup.centralizer (V : Set G) ≤ B :=
      (sup_centralizer_le_normalizer V).trans hNB
    have hUB : U ≤ B := hUV.trans (le_sup_right.trans hVCB)
    have hSF := subnormalHull_le_generalizedFitting hVF
    have hSsn := isSubnormal_subnormalHull hVF hV
    have hSC := generalizedFitting_inf_centralizer_subnormalHull_le H V
    have hSB := (subnormalHull_le_sup_centralizer hVF hV).trans hVCB
    have hO : ∀ q : ℕ, q.Prime → q ∉ primesOfOrder (CFSG.fittingSubgroupOf H) →
        qCoreOf B q = ⊥ := by
      intro q hq hqπ
      have h1 := qCoreOf_inf_eq_bot_of_sup_centralizer_le hsimple hH hVF hV hVCB hq hqπ
      refine eq_bot_of_forall_inf_centralizer_eq_bot hUcomm hUcyc
        (hUB.trans (le_normalizer_of_isNormalIn (qCoreOf_normal_in B q))) ?_
        fun u hu hu1 => eq_bot_iff.mpr fun x hx => h1 ▸ ⟨hx.1, hCu u hu hu1 hx.2⟩
      have : Fact q.Prime := ⟨hq⟩
      obtain ⟨k, hk⟩ := (qCoreOf_isPGroup B q).exists_card_eq
      rw [hk]
      refine Nat.Coprime.pow_right k ((Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hq).mpr
        fun hqU => hqπ ?_)))
      exact Nat.mem_primeFactors.mpr ⟨hq, hqU.trans (Subgroup.card_dvd_of_le hUF), Nat.card_pos.ne'⟩
    have hres : ∀ p : ℕ, p.Prime → p ∈ primesOfOrder (CFSG.fittingSubgroupOf H) →
        pResidualOf (generalizedFittingSubgroupOf H) p ≠ ⊥ := by
      intro p hp _ hres
      have := card_primesOfOrder_le_one_of_isPGroup hp
        (isPGroup_of_pResidualOf_eq_bot _ p hp hres)
      omega
    have hFB : CFSG.fittingSubgroupOf B ≤ H :=
      fittingSubgroupOf_le_of_pResidualOf_ne_bot hsimple H hH (subnormalHull H V) hSF hSsn hSC hSB
        hres hO
    have hEB : componentLayerOf B ≤ H := by
      refine sSup_le fun K hK => ?_
      obtain ⟨u, hu, hu1, hKu⟩ :=
        exists_ne_one_mem_centralizer_of_isComponentOf hBA htB ht (hUOX B hUB) hUcyc hK
      exact hKu.trans (hCu u hu hu1)
    have hHB : H = B := bender1970_1_7_iii_equalityOfMaximal hsimple H hH (subnormalHull H V) hSF
      hSsn hSC hSB hB (Or.inl hπ)
      ⟨generalizedFittingSubgroupOf B, sup_le hFB hEB, le_rfl, by
        rw [Subgroup.subgroupOf_self]; exact Subgroup.IsSubnormal.top, inf_le_left⟩
    exact hHB ▸ hNB
  ·
    obtain ⟨p, hp, hFp, -, hπp⟩ := exists_isPGroup_of_card_primesOfOrder_eq_one hπ
    have : Fact p.Prime := ⟨hp⟩
    have hUp : IsPGroup p U := hFp.to_le (hUF.trans le_sup_left)
    have hVp : IsPGroup p V := hFp.to_le hVF
    set Y := Subgroup.centralizer (V : Set G) with hYdef
    have hUY : U ≤ Y := hUV
    have hYu : ∀ u ∈ U, u ≠ 1 → IsPGroup p (generalizedFittingSubgroupOf
        (Subgroup.centralizer ({u} : Set G) ⊓ Subgroup.centralizer (V : Set G))) := by
      intro u hu hu1
      have h1 := (hUA u hu hu1).2.2.2 hπ
      rw [hπp, centralizer_zpowers_eq'] at h1
      have hVu : V ≤ Subgroup.centralizer ({u} : Set G) := by
        intro v hv
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_iff.mp (hUV hu)) v hv
      exact isPGroup_generalizedFitting_inf_centralizer hp (isPGroup_of_primesOfOrder_subset hp
        h1.le) hVu hVp
    have hq : ∀ q : ℕ, q.Prime → q ≠ p → qCoreOf Y q = ⊥ := by
      intro q hq hqp
      have : Fact q.Prime := ⟨hq⟩
      refine eq_bot_of_forall_inf_centralizer_eq_bot hUcomm hUcyc
        (hUY.trans (le_normalizer_of_isNormalIn (qCoreOf_normal_in Y q))) ?_ fun u hu hu1 => ?_
      · obtain ⟨k, hk⟩ := hUp.exists_card_eq
        obtain ⟨l, hl⟩ := (qCoreOf_isPGroup Y q).exists_card_eq
        rw [hk, hl]
        exact Nat.Coprime.pow k l ((Nat.coprime_primes hp hq).mpr (Ne.symm hqp))
      · by_contra hne
        set Z := Subgroup.centralizer ({u} : Set G) ⊓ Subgroup.centralizer (V : Set G)
        have hNZ : qCoreOf Y q ⊓ Subgroup.centralizer ({u} : Set G) ≤ Z := fun x hx =>
          ⟨hx.2, (qCoreOf_normal_in Y q).1 hx.1⟩
        have hNn : IsNormalIn (qCoreOf Y q ⊓ Subgroup.centralizer ({u} : Set G)) Z :=
          ⟨hNZ, fun z hz x hx => ⟨(qCoreOf_normal_in Y q).2 z hz.2 x hx.1,
            (Subgroup.centralizer ({u} : Set G)).mul_mem
              ((Subgroup.centralizer ({u} : Set G)).mul_mem hz.1 hx.2)
              ((Subgroup.centralizer ({u} : Set G)).inv_mem hz.1)⟩⟩
        have hNq : IsPGroup q (qCoreOf Y q ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G) :=
          (qCoreOf_isPGroup Y q).to_le inf_le_left
        have hNF : qCoreOf Y q ⊓ Subgroup.centralizer ({u} : Set G) ≤
            generalizedFittingSubgroupOf Z :=
          (le_fittingSubgroupOf_of_isNormalIn_nilpotent hNZ hNn hNq.isNilpotent).trans le_sup_left
        exact hqp (eq_of_isPGroup_of_isPGroup hq hp hNq ((hYu u hu hu1).to_le hNF) hne)
    have hE : componentLayerOf Y = ⊥ := by
      refine eq_bot_iff.mpr (sSup_le fun K hK => ?_)
      exfalso
      set X := Y ⊔ Subgroup.zpowers t with hXdef
      have hYN : Y ≤ Subgroup.normalizer (V : Set G) := Subgroup.centralizer_le_normalizer _
      have hXN : X ≤ Subgroup.normalizer (V : Set G) := sup_le hYN (Subgroup.zpowers_le.mpr hVt)
      have hXtop : X ≠ ⊤ := fun h => hG.normalizer_ne_top hV1
        (fun h' => hH.1 (top_le_iff.mp (h' ▸ hVH))) (top_le_iff.mp (h ▸ hXN))
      have hXA := hG.isAStar X hXtop
      have htX : t ∈ X := (le_sup_right : Subgroup.zpowers t ≤ X) (Subgroup.mem_zpowers t)
      have hYn : IsNormalIn Y X := by
        refine ⟨le_sup_left, fun x hx y hy => ?_⟩
        have hxN := hXN hx
        rw [Subgroup.mem_centralizer_iff] at hy ⊢
        intro v hv
        have hv' : x⁻¹ * v * x ∈ V := by
          have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxN) v).mp hv
          simpa using this
        have := hy _ hv'
        calc v * (x * y * x⁻¹) = x * ((x⁻¹ * v * x) * y) * x⁻¹ := by group
          _ = x * (y * (x⁻¹ * v * x)) * x⁻¹ := by rw [this]
          _ = x * y * x⁻¹ * v := by group
      have hKX : IsComponentOf K X :=
        isComponentOf_of_isSubnormal le_sup_left (isSubnormal_subgroupOf_of_isNormalIn hYn) hK
      obtain ⟨u, hu, hu1, hKu⟩ := exists_ne_one_mem_centralizer_of_isComponentOf hXA htX ht
        (hUOX X (hUY.trans le_sup_left)) hUcyc hKX
      set Z := Subgroup.centralizer ({u} : Set G) ⊓ Subgroup.centralizer (V : Set G)
      have hKZ : K ≤ Z := le_inf hKu hK.1
      have hKc : IsComponentOf K Z :=
        ⟨hKZ, isSubnormal_subgroupOf_of_le hKZ inf_le_right hK.2.1, hK.2.2⟩
      have hKF : K ≤ generalizedFittingSubgroupOf Z :=
        (le_sSup (s := {E : Subgroup G | IsComponentOf E Z}) hKc).trans le_sup_right
      exact not_isNilpotent_of_isQuasisimple K hK.2.2 ((hYu u hu hu1).to_le hKF).isNilpotent
    rw [hπp]
    exact primesOfOrder_generalizedFitting_eq_singleton hp
      (isPGroup_generalizedFitting_of_qCoreOf_eq_bot hq hE)
      (centralizer_ne_bot_of_isPGroup hp hVp hV1)

theorem bender1970_3_1_i
    (hG : BenderCounterexample G) {t : G} (ht : orderOf t = 2)
    {H : Subgroup G} (hH : H ∈ benderM t) {V : Subgroup G} (hV1 : V ≠ ⊥)
    (hVF : V ≤ generalizedFittingSubgroupOf H)
    (hV : (V.subgroupOf (generalizedFittingSubgroupOf H)).IsSubnormal)
    (hVC : Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (V : Set G)) :
    V ∈ benderABar H :=
  hG.mem_benderABar_of_centralizer_le_normalizer ht hH hV1 hVF hV hVC

theorem bender1970_3_1_ii
    (hG : BenderCounterexample G) {t : G} (ht : orderOf t = 2)
    {H : Subgroup G} (hH : H ∈ benderM t) {V : Subgroup G} (hV1 : V ≠ ⊥)
    (hVF : V ≤ generalizedFittingSubgroupOf H)
    (hV : (V.subgroupOf (generalizedFittingSubgroupOf H)).IsSubnormal)
    (hVt : t ∈ Subgroup.normalizer (V : Set G)) {U : Subgroup G} (hUA : U ∈ benderABar H)
    (hUV : U ≤ Subgroup.centralizer (V : Set G)) (hUt : ⁅U, Subgroup.zpowers t⁆ = U) :
    V ∈ benderABar H :=
  hG.mem_benderABar_of_commutator_eq ht (isCoatom_of_mem_benderM hH)
    (centralizer_le_of_mem_benderM hH) hV1 hVF hV hVt hUA hUV hUt

theorem bender1970_3_1_iii
    (hG : BenderCounterexample G) {t : G} (ht : orderOf t = 2)
    {H : Subgroup G} (hH : H ∈ benderM t) {V : Subgroup G} (hV1 : V ≠ ⊥)
    (hVF : V ≤ generalizedFittingSubgroupOf H)
    (hV : (V.subgroupOf (generalizedFittingSubgroupOf H)).IsSubnormal)
    (hVt : t ∈ Subgroup.normalizer (V : Set G)) {U : Subgroup G}
    (hUC : U ≤ Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer (V : Set G))
    (hUcomm : IsMulCommutative U) (hUcyc : ¬ IsCyclic U) (hUodd : Odd (Nat.card U))
    (hUA : ∀ u ∈ U, u ≠ 1 → Subgroup.zpowers u ∈ benderABar H) :
    V ∈ benderABar H :=
  hG.mem_benderABar_of_noncyclic ht (isCoatom_of_mem_benderM hH)
    (centralizer_le_of_mem_benderM hH) hV1 hVF hV hVt hUC hUcomm hUcyc hUodd hUA

theorem bender1970_3_1
    (hG : BenderCounterexample G) {t : G} (ht : orderOf t = 2)
    {H : Subgroup G} (hH : H ∈ benderM t) {V : Subgroup G} (hV1 : V ≠ ⊥)
    (hVF : V ≤ generalizedFittingSubgroupOf H)
    (hV : (V.subgroupOf (generalizedFittingSubgroupOf H)).IsSubnormal)
    (hVt : t ∈ Subgroup.normalizer (V : Set G)) :
    (Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (V : Set G) →
        V ∈ benderABar H) ∧
      (∀ U ∈ benderABar H, U ≤ Subgroup.centralizer (V : Set G) →
        ⁅U, Subgroup.zpowers t⁆ = U → V ∈ benderABar H) ∧
      (∀ U : Subgroup G,
        U ≤ Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer (V : Set G) →
        IsMulCommutative U → ¬ IsCyclic U → Odd (Nat.card U) →
        (∀ u ∈ U, u ≠ 1 → Subgroup.zpowers u ∈ benderABar H) → V ∈ benderABar H) :=
  ⟨bender1970_3_1_i hG ht hH hV1 hVF hV,
    fun _ hUA hUV hUt => bender1970_3_1_ii hG ht hH hV1 hVF hV hVt hUA hUV hUt,
    fun _ hUC hUcomm hUcyc hUodd hUA =>
      bender1970_3_1_iii hG ht hH hV1 hVF hV hVt hUC hUcomm hUcyc hUodd hUA⟩

end CFSG.Walter
