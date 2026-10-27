module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsNineA3
public import CFSG.GroupTheory.FixVConj
public import CFSG.GroupTheory.OrderThreeFixedPoints
public import CFSG.GroupTheory.BarImageConj
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsNineAdjRoot
public import CFSG.GroupTheory.PerfectTwoQuotient
public import TauCeti.GroupTheory.Sylow
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22ua

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC PartTwo Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem barImage_zpowers_eq {M : Subgroup G} {x : G} (hx : x ∈ M) :
    barImage M (Subgroup.zpowers x) =
      Subgroup.zpowers (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨x, hx⟩) := by
  have hsub : (Subgroup.zpowers x).subgroupOf M = Subgroup.zpowers (⟨x, hx⟩ : ↥M) := by
    apply Subgroup.map_injective M.subtype_injective
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (Subgroup.zpowers_le.mpr hx),
      MonoidHom.map_zpowers]
    rfl
  rw [barImage, hsub, MonoidHom.map_zpowers]

namespace S23_9_AdjData

variable {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch} {hV : IsElemAbelian 2 c.V}
  {d : S23_9_A0Data D Ch c} {b : G} {hb : b ∈ c.B0} {r : ℕ}

def ctilde (a : S23_9_AdjData D Ch c hV d b hb r) : G := b * a.dRoot⁻¹

theorem ctilde_eq (a : S23_9_AdjData D Ch c hV d b hb r) : ctilde a = b * a.dRoot⁻¹ := by
  rw [ctilde]

theorem ctilde_pow_three (a : S23_9_AdjData D Ch c hV d b hb r)
    (hbr : orderOf b = r) (hr3 : r = 3) : ctilde a ^ 3 = 1 := by
  have hb_order : orderOf b = 3 := hbr.trans hr3
  have hd_order : orderOf a.dRoot = 3 := a.hdorder.trans hr3
  have hb3 : b ^ 3 = 1 := by rw [← hb_order]; exact pow_orderOf_eq_one b
  have hd3 : a.dRoot ^ 3 = 1 := by rw [← hd_order]; exact pow_orderOf_eq_one a.dRoot
  have hcomm : Commute b a.dRoot := a.hdb.symm
  have hcomm' : Commute b a.dRoot⁻¹ := hcomm.inv_right
  rw [ctilde, hcomm'.mul_pow, hb3, inv_pow, hd3]
  simp

theorem ctilde_comm_dRoot (a : S23_9_AdjData D Ch c hV d b hb r) :
    ctilde a * a.dRoot = a.dRoot * ctilde a := by
  rw [ctilde]
  have hcomm : Commute a.dRoot⁻¹ b := (show Commute a.dRoot b from a.hdb).inv_left
  calc b * a.dRoot⁻¹ * a.dRoot = b := by group
    _ = a.dRoot * (a.dRoot⁻¹ * b) := by group
    _ = a.dRoot * (b * a.dRoot⁻¹) := by rw [hcomm.eq]

theorem ctilde_mem_normalizer (a : S23_9_AdjData D Ch c hV d b hb r) :
    ctilde a ∈ Subgroup.normalizer (a.X : Set G) := by
  have hb' : b ∈ Subgroup.normalizer (a.X : Set G) := a.hbX
  have hd' : a.dRoot⁻¹ ∈ Subgroup.normalizer (a.X : Set G) :=
    (Subgroup.normalizer (a.X : Set G)).inv_mem (Subgroup.le_normalizer a.hdX)
  exact (Subgroup.normalizer (a.X : Set G)).mul_mem hb' hd'

theorem ctilde_centralizes_mod_O (a : S23_9_AdjData D Ch c hV d b hb r)
    {x : G} (hx : x ∈ a.X) :
    ctilde a * x * (ctilde a)⁻¹ * x⁻¹ ∈ (CFSG.pCore 2 ↥a.X).map a.X.subtype := by
  set y : G := a.dRoot⁻¹ * x * a.dRoot with hy
  have hyX : y ∈ a.X := a.X.mul_mem (a.X.mul_mem (a.X.inv_mem a.hdX) hx) a.hdX
  have h := a.hinner y hyX
  have hdy : a.dRoot * y * a.dRoot⁻¹ = x := by
    rw [hy]
    group
  rw [hdy] at h
  have heq : ctilde a * x * (ctilde a)⁻¹ * x⁻¹ =
      b * y * b⁻¹ * x⁻¹ := by
    rw [ctilde, hy]
    group
  rwa [heq]

private theorem exists_conj_inv_of_odd_order_dvd {F : Type*} [Field F] [Finite F] [CharP F 2]
    {y : Matrix.SpecialLinearGroup (Fin 2) F} (hy_odd : Odd (orderOf y))
    (hy_dvd : orderOf y ∣ Nat.card F - 1) (hy_ne_one : y ≠ 1) :
    ∃ w : Matrix.SpecialLinearGroup (Fin 2) F, w * y * w⁻¹ = y⁻¹ := by
  obtain ⟨P, hP⟩ :=
    CFSG.GroupTheory.exists_conj_mem_diagSub_of_odd_order_dvd_card_sub_one
      (F := F) hy_odd hy_dvd hy_ne_one
  set d : Matrix.SpecialLinearGroup (Fin 2) F := P⁻¹ * y * P with hd
  have hd_diag : d ∈ CFSG.GH74.GLS.IVK.L2Torus.diagSub F := hP
  refine ⟨P * CFSG.GH74.GLS.IVK.L2Torus.w0 F * P⁻¹, ?_⟩
  calc (P * CFSG.GH74.GLS.IVK.L2Torus.w0 F * P⁻¹) * y *
        (P * CFSG.GH74.GLS.IVK.L2Torus.w0 F * P⁻¹)⁻¹
      = P * (CFSG.GH74.GLS.IVK.L2Torus.w0 F * d *
          (CFSG.GH74.GLS.IVK.L2Torus.w0 F)⁻¹) * P⁻¹ := by
        rw [hd]
        group
    _ = P * d⁻¹ * P⁻¹ := by
        rw [CFSG.GH74.GLS.IVK.L2Torus.w0_inv_diag (F := F) hd_diag]
    _ = y⁻¹ := by
        rw [hd]
        group

private theorem exists_wBar_inverts_dhat (a : S23_9_AdjData D Ch c hV d b hb r)
    (hr : r.Prime) (hr2 : r ≠ 2) (hbr : orderOf b = r) :
    ∃ wbar : Bar2 a.X, wbar * a.dhat * wbar⁻¹ = a.dhat⁻¹ := by
  obtain ⟨K, hKfield, hKfinite, hKcard, ⟨eK⟩⟩ := a.hXsl
  letI : Field K := hKfield
  letI : Finite K := hKfinite
  letI : Fintype K := Fintype.ofFinite K
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : CharP K 2 :=
    charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  let e : Bar2 a.X ≃* Matrix.SpecialLinearGroup (Fin 2) K :=
    eK.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K).symm
  have hdhat_order : orderOf a.dhat = r := a.orderOf_dhat hr hr2
  let y : Matrix.SpecialLinearGroup (Fin 2) K := e a.dhat
  have hy_order : orderOf y = r := by
    simpa [y] using (MulEquiv.orderOf_eq e a.dhat).trans hdhat_order
  have hy_odd : Odd (orderOf y) := by
    rw [hy_order]
    exact hr.odd_of_ne_two hr2
  have hy_dvd : orderOf y ∣ Nat.card K - 1 := by
    rw [hy_order, hKcard]
    exact a.hrm
  have hy_ne_one : y ≠ 1 := by
    intro hy1
    have h1 : orderOf y = 1 := by rw [hy1, orderOf_one]
    rw [hy_order] at h1
    exact hr.ne_one h1
  obtain ⟨wMat, hwMat⟩ := exists_conj_inv_of_odd_order_dvd hy_odd hy_dvd hy_ne_one
  let wbar : Bar2 a.X := e.symm wMat
  refine ⟨wbar, ?_⟩
  apply e.injective
  calc e (wbar * a.dhat * wbar⁻¹)
      = e wbar * e a.dhat * (e wbar)⁻¹ := by simp
    _ = wMat * y * wMat⁻¹ := by simp [wbar, y]
    _ = y⁻¹ := hwMat
    _ = e (a.dhat⁻¹) := by rw [map_inv]

private theorem exists_w_inverts_dhat (a : S23_9_AdjData D Ch c hV d b hb r)
    (hr : r.Prime) (hr2 : r ≠ 2) (hbr : orderOf b = r) :
    ∃ (w : G) (hw : w ∈ a.X),
      a.qX ⟨w, hw⟩ * a.dhat * (a.qX ⟨w, hw⟩)⁻¹ = a.dhat⁻¹ := by
  obtain ⟨wbar, hwbar⟩ := a.exists_wBar_inverts_dhat hr hr2 hbr
  obtain ⟨wX, hwX⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥a.X) wbar
  refine ⟨(wX : G), wX.2, ?_⟩
  have hq : a.qX ⟨(wX : G), wX.2⟩ = wbar := hwX
  rw [hq]
  exact hwbar

private theorem center_eq_bot_of_isSLn_two {X : Type} [Group X] [Finite X] {m : ℕ}
    (hm : 2 ≤ m) (h : IsSLn X 2 m) : Subgroup.center X = ⊥ := by
  haveI : IsSimpleGroup X := CFSG.GroupTheory.isSimpleGroup_of_isSLn_two hm h
  haveI : Group.IsPerfect X := CFSG.GroupTheory.isPerfect_of_isSLn_two hm h
  rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center X) with hbot | htop
  · exact hbot
  · exfalso
    have hcomm : ∀ a b : X, a * b = b * a := by
      intro a b
      have ha : a ∈ Subgroup.center X := htop ▸ Subgroup.mem_top a
      exact (Subgroup.mem_center_iff.mp ha b).symm
    haveI : IsMulCommutative X := ⟨⟨hcomm⟩⟩
    exact (Group.IsPerfect.not_isMulCommutative X) inferInstance

private theorem b_ne_dRoot_sq (a : S23_9_AdjData D Ch c hV d b hb r) (hr3 : r = 3) :
    b ≠ a.dRoot ^ 2 := by
  intro hb
  have hr : r.Prime := hr3 ▸ Nat.prime_three
  have hr2 : r ≠ 2 := hr3 ▸ (by norm_num)
  have hdhat3 : a.dhat ^ 3 = 1 := by
    have horder : orderOf a.dhat = 3 := by
      rw [a.orderOf_dhat hr hr2]
      exact hr3
    have h := pow_orderOf_eq_one a.dhat
    rwa [horder] at h
  have hcenter : a.dhat ∈ Subgroup.center (Bar2 a.X) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥a.X) y
    have hmem : b * (x : G) * b⁻¹ ∈ a.X :=
      (Subgroup.mem_normalizer_iff.mp a.hbX (x : G)).mp x.2
    have h1 := a.inner_bar (x : G) x.2
    have h2 : a.qX ⟨b * (x : G) * b⁻¹, hmem⟩ =
        a.dhat ^ 2 * a.qX x * (a.dhat ^ 2)⁻¹ := by
      have hsub : (⟨b * (x : G) * b⁻¹, hmem⟩ : ↥a.X) =
          (⟨a.dRoot, a.hdX⟩ : ↥a.X) ^ 2 * x *
            ((⟨a.dRoot, a.hdX⟩ : ↥a.X) ^ 2)⁻¹ := by
        apply Subtype.ext
        simp [hb, mul_assoc]
      rw [hsub, map_mul, map_mul, map_pow, map_inv]
      rfl
    rw [h2] at h1
    have h3 : a.dhat ^ 2 * a.qX x = a.dhat * a.qX x * a.dhat := by
      have := congrArg (fun z => z * a.dhat ^ 2) h1
      simpa [pow_two, mul_assoc] using this
    have h4 : a.dhat * (a.dhat * a.qX x) = a.dhat * (a.qX x * a.dhat) := by
      simpa [pow_two, mul_assoc] using h3
    exact (mul_left_cancel h4).symm
  have hbot : Subgroup.center (Bar2 a.X) = ⊥ :=
    center_eq_bot_of_isSLn_two a.hm2 a.hXsl
  rw [hbot, Subgroup.mem_bot] at hcenter
  have horder : orderOf a.dhat = 3 := by
    rw [a.orderOf_dhat hr hr2]
    exact hr3
  rw [hcenter, orderOf_one] at horder
  norm_num at horder

def bd (a : S23_9_AdjData D Ch c hV d b hb r) : G := b * a.dRoot

theorem bd_eq (a : S23_9_AdjData D Ch c hV d b hb r) : bd a = b * a.dRoot := by
  rw [bd]

theorem bd_mem_normalizer (a : S23_9_AdjData D Ch c hV d b hb r) :
    bd a ∈ Subgroup.normalizer (a.X : Set G) :=
  (Subgroup.normalizer (a.X : Set G)).mul_mem a.hbX (Subgroup.le_normalizer a.hdX)

private theorem dhat_pow_three (a : S23_9_AdjData D Ch c hV d b hb r) (hr3 : r = 3) :
    a.dhat ^ 3 = 1 := by
  have hd3 : a.dRoot ^ 3 = 1 := by
    have hd : orderOf a.dRoot = 3 := a.hdorder.trans hr3
    exact hd ▸ pow_orderOf_eq_one a.dRoot
  have hsub : (⟨a.dRoot, a.hdX⟩ : ↥a.X) ^ 3 = 1 := by
    apply Subtype.ext
    simpa using hd3
  calc a.dhat ^ 3 = a.qX ((⟨a.dRoot, a.hdX⟩ : ↥a.X) ^ 3) := by
        rw [S23_9_AdjData.dhat, map_pow]
    _ = 1 := by rw [hsub, map_one]

private theorem bd_pow_three (a : S23_9_AdjData D Ch c hV d b hb r)
    (hbr : orderOf b = r) (hr3 : r = 3) : (bd a) ^ 3 = 1 := by
  have hb3 : b ^ 3 = 1 := by
    have horder : orderOf b = 3 := by rw [hbr]; exact hr3
    have h := pow_orderOf_eq_one b
    rwa [horder] at h
  have hd3 : a.dRoot ^ 3 = 1 := by
    have horder : orderOf a.dRoot = 3 := by rw [a.hdorder]; exact hr3
    have h := pow_orderOf_eq_one a.dRoot
    rwa [horder] at h
  have hcomm : Commute b a.dRoot := a.hdb.symm
  rw [bd, Commute.mul_pow hcomm 3, hb3, hd3, mul_one]

private theorem bd_ne_one (a : S23_9_AdjData D Ch c hV d b hb r) (hr3 : r = 3) :
    bd a ≠ 1 := by
  intro h
  have h1 : b * a.dRoot = 1 := h
  have h2 : b = a.dRoot⁻¹ := eq_inv_of_mul_eq_one_left h1
  have hd3 : a.dRoot ^ 3 = 1 := by
    have horder : orderOf a.dRoot = 3 := by rw [a.hdorder]; exact hr3
    have h := pow_orderOf_eq_one a.dRoot
    rwa [horder] at h
  have hmul : a.dRoot * a.dRoot ^ 2 = 1 := by
    simpa [pow_succ, mul_assoc] using hd3
  have h3 : a.dRoot⁻¹ = a.dRoot ^ 2 := (eq_inv_of_mul_eq_one_right hmul).symm
  exact a.b_ne_dRoot_sq hr3 (h2.trans h3)

private theorem orderOf_bd (a : S23_9_AdjData D Ch c hV d b hb r)
    (hbr : orderOf b = r) (hr3 : r = 3) : orderOf (bd a) = 3 :=
  orderOf_eq_prime (a.bd_pow_three hbr hr3) (a.bd_ne_one hr3)

private theorem bd_conj_mem_pCore (a : S23_9_AdjData D Ch c hV d b hb r)
    (hr3 : r = 3) {w : G} (hw : w ∈ a.X)
    (hwinv : a.qX ⟨w, hw⟩ * a.dhat * (a.qX ⟨w, hw⟩)⁻¹ = a.dhat⁻¹) :
    (w * b * w⁻¹) * (bd a)⁻¹ ∈ CFSG.Open.pCoreOf 2 a.X := by
  have hdhat3 : a.dhat ^ 3 = 1 := a.dhat_pow_three hr3
  have hbwb : b * w⁻¹ * b⁻¹ ∈ a.X :=
    (Subgroup.mem_normalizer_iff.mp a.hbX w⁻¹).mp (a.X.inv_mem hw)
  have hbdinv : (bd a)⁻¹ = a.dRoot⁻¹ * b⁻¹ := by rw [bd, mul_inv_rev]
  have hcomm : a.dRoot⁻¹ * b⁻¹ = b⁻¹ * a.dRoot⁻¹ := by
    have h : Commute b a.dRoot := a.hdb.symm
    exact h.inv_left.inv_right.eq.symm
  have hxX : (w * b * w⁻¹) * (bd a)⁻¹ ∈ a.X := by
    rw [hbdinv, hcomm]
    simpa [mul_assoc] using
      a.X.mul_mem (a.X.mul_mem hw hbwb) (a.X.inv_mem a.hdX)
  have hq1 : a.qX ⟨(w * b * w⁻¹) * (bd a)⁻¹, hxX⟩ = 1 := by
    have hxeq : (⟨(w * b * w⁻¹) * (bd a)⁻¹, hxX⟩ : ↥a.X) =
        ⟨w, hw⟩ * ⟨b * w⁻¹ * b⁻¹, hbwb⟩ * ⟨a.dRoot⁻¹, a.X.inv_mem a.hdX⟩ := by
      apply Subtype.ext
      change w * b * w⁻¹ * (bd a)⁻¹ =
        w * (b * w⁻¹ * b⁻¹) * a.dRoot⁻¹
      rw [hbdinv, hcomm]
      group
    have hwinv_sub : (⟨w⁻¹, a.X.inv_mem hw⟩ : ↥a.X) = (⟨w, hw⟩ : ↥a.X)⁻¹ := by
      ext
      simp
    have hdinv_sub : (⟨a.dRoot⁻¹, a.X.inv_mem a.hdX⟩ : ↥a.X) =
        (⟨a.dRoot, a.hdX⟩ : ↥a.X)⁻¹ := by
      ext
      simp
    rw [hxeq, map_mul, map_mul, a.inner_bar w⁻¹ (a.X.inv_mem hw), hwinv_sub, map_inv,
      hdinv_sub, map_inv]
    have hgoal : a.qX ⟨w, hw⟩ * a.dhat * (a.qX ⟨w, hw⟩)⁻¹ = a.dhat⁻¹ := hwinv
    calc a.qX ⟨w, hw⟩ * (a.dhat * (a.qX ⟨w, hw⟩)⁻¹ * a.dhat⁻¹) * a.dhat⁻¹
        = (a.qX ⟨w, hw⟩ * a.dhat * (a.qX ⟨w, hw⟩)⁻¹) * a.dhat⁻¹ * a.dhat⁻¹ := by
          group
      _ = a.dhat⁻¹ * a.dhat⁻¹ * a.dhat⁻¹ := by rw [hgoal]
      _ = (a.dhat⁻¹) ^ 3 := by group
      _ = 1 := by rw [inv_pow, hdhat3, inv_one]
  have hmem : (⟨(w * b * w⁻¹) * (bd a)⁻¹, hxX⟩ : ↥a.X) ∈
      CFSG.pCore 2 ↥a.X := (QuotientGroup.eq_one_iff _).mp hq1
  exact (CFSG.Quasithin.C1Pack.coe_mem_pCoreOf_iff a.X ⟨_, hxX⟩).mpr hmem

private theorem card_sup_pCore_zpowers_bd (a : S23_9_AdjData D Ch c hV d b hb r)
    (hbr : orderOf b = r) (hr3 : r = 3) :
    Nat.card ↥(CFSG.Open.pCoreOf 2 a.X ⊔ Subgroup.zpowers (bd a)) =
        Nat.card (CFSG.Open.pCoreOf 2 a.X) * 3 ∧
      ¬ 9 ∣ Nat.card ↥(CFSG.Open.pCoreOf 2 a.X ⊔ Subgroup.zpowers (bd a)) := by
  let O : Subgroup G := CFSG.Open.pCoreOf 2 a.X
  let P : Subgroup G := Subgroup.zpowers (bd a)
  have hPnormO : P ≤ Subgroup.normalizer (O : Set G) := by
    refine Subgroup.zpowers_le.mpr ?_
    exact (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf (r := 2) a.X)
      a.bd_mem_normalizer
  have hO2 : IsPGroup 2 O := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 a.X
  have hP3 : IsPGroup 3 P :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, a.orderOf_bd hbr hr3, pow_one])
  have hPcard : Nat.card P = 3 := by rw [Nat.card_zpowers, a.orderOf_bd hbr hr3]
  have hHcard : Nat.card ↥(O ⊔ P) = Nat.card O * 3 := by
    have h := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer O P hPnormO
      (IsPGroup.disjoint_of_coprime hO2 hP3 (by decide : Nat.Coprime 2 3))
    rw [h, hPcard]
  have hHnot9 : ¬ 9 ∣ Nat.card ↥(O ⊔ P) := by
    obtain ⟨k, hk⟩ := hO2.exists_card_eq
    rw [hHcard, hk, mul_comm]
    intro hdvd
    have h3dvd : 3 ∣ 2 ^ k := Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 3) hdvd
    exact absurd (Nat.prime_three.dvd_of_dvd_pow h3dvd) (by norm_num)
  exact ⟨by simpa [O, P] using hHcard, by simpa [O, P] using hHnot9⟩

private theorem exists_conj_mem_zpowers_bd (a : S23_9_AdjData D Ch c hV d b hb r)
    (hbr : orderOf b = r) (hr3 : r = 3) {x : G}
    (hxH : x ∈ CFSG.Open.pCoreOf 2 a.X ⊔ Subgroup.zpowers (bd a))
    (hxord : orderOf x = 3)
    (hnot9 : ¬ 9 ∣ Nat.card ↥(CFSG.Open.pCoreOf 2 a.X ⊔ Subgroup.zpowers (bd a))) :
    ∃ y : G, y ∈ CFSG.Open.pCoreOf 2 a.X ⊔ Subgroup.zpowers (bd a) ∧
      y * x * y⁻¹ ∈ Subgroup.zpowers (bd a) := by
  let H : Subgroup G := CFSG.Open.pCoreOf 2 a.X ⊔ Subgroup.zpowers (bd a)
  let P : Subgroup G := Subgroup.zpowers (bd a)
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPleH : P ≤ H := le_sup_right
  have hqHord : orderOf (⟨bd a, hPleH (Subgroup.mem_zpowers (bd a))⟩ : ↥H) = 3 := by
    rw [Subgroup.orderOf_mk]
    exact a.orderOf_bd hbr hr3
  have hxHord : orderOf (⟨x, hxH⟩ : ↥H) = 3 := by
    rw [Subgroup.orderOf_mk]
    exact hxord
  obtain ⟨y, hy⟩ := TauCeti.exists_mul_mul_inv_mem_zpowers_of_not_sq_dvd (G := ↥H) (p := 3)
    (by simpa [H] using hnot9)
    (g := ⟨bd a, hPleH (Subgroup.mem_zpowers (bd a))⟩) (h := ⟨x, hxH⟩) hqHord hxHord
  refine ⟨(y : G), y.2, ?_⟩
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hval := congrArg Subtype.val hn
  rw [Subgroup.mem_zpowers_iff]
  exact ⟨n, by simpa using hval⟩

private theorem exists_mem_pCore_conj_of_mem_mul {O P : Subgroup G}
    (hPnormO : P ≤ Subgroup.normalizer (O : Set G)) {x y : G}
    (hy : y ∈ (O : Set G) * (P : Set G)) (hyP : y * x * y⁻¹ ∈ P) :
    ∃ o ∈ O, o * x * o⁻¹ ∈ P := by
  obtain ⟨o, hoO, p, hpP, hop⟩ := hy
  have hop' : y = p * (p⁻¹ * o * p) := by rw [← hop]; group
  have ho'O : p⁻¹ * o * p ∈ O := by
    simpa using (Subgroup.mem_normalizer_iff.mp (hPnormO (P.inv_mem hpP)) o).mp hoO
  refine ⟨p⁻¹ * o * p, ho'O, ?_⟩
  have heq : p * ((p⁻¹ * o * p) * x * (p⁻¹ * o * p)⁻¹) * p⁻¹ = y * x * y⁻¹ := by
    rw [hop']
    group
  have hmem : p * ((p⁻¹ * o * p) * x * (p⁻¹ * o * p)⁻¹) * p⁻¹ ∈ P := by
    rw [heq]
    exact hyP
  have h := P.mul_mem (P.mul_mem (P.inv_mem hpP) hmem) hpP
  simpa [mul_assoc] using h

private theorem exists_pCore_conj_of_inverting
    (a : S23_9_AdjData D Ch c hV d b hb r) (hbr : orderOf b = r) (hr3 : r = 3)
    {w : G} (hw : w ∈ a.X)
    (hwinv : a.qX ⟨w, hw⟩ * a.dhat * (a.qX ⟨w, hw⟩)⁻¹ = a.dhat⁻¹) :
    ∃ o ∈ CFSG.Open.pCoreOf 2 a.X,
      o * (w * b * w⁻¹) * o⁻¹ ∈ Subgroup.zpowers (bd a) := by
  let O : Subgroup G := CFSG.Open.pCoreOf 2 a.X
  let P : Subgroup G := Subgroup.zpowers (bd a)
  let H : Subgroup G := O ⊔ P
  let x : G := w * b * w⁻¹
  have hPnormO : P ≤ Subgroup.normalizer (O : Set G) := by
    refine Subgroup.zpowers_le.mpr ?_
    exact (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf (r := 2) a.X)
      a.bd_mem_normalizer
  have hxO : x * (bd a)⁻¹ ∈ O := a.bd_conj_mem_pCore hr3 hw hwinv
  have hxH : x ∈ H := by
    rw [show x = (x * (bd a)⁻¹) * bd a by group]
    exact Subgroup.mul_mem_sup hxO (Subgroup.mem_zpowers (bd a))
  have hb3ord : orderOf b = 3 := by rw [hbr, hr3]
  have hxord : orderOf x = 3 := by
    have hxeq : x = (MulAut.conj w) b := by simp [x, MulAut.conj_apply]
    rw [hxeq, MulEquiv.orderOf_eq (MulAut.conj w) b, hb3ord]
  obtain ⟨-, hHnot9⟩ := a.card_sup_pCore_zpowers_bd hbr hr3
  obtain ⟨y, hyH, hyP⟩ :=
    a.exists_conj_mem_zpowers_bd hbr hr3 (by simpa [H, O, P] using hxH)
      (by simpa [H, P] using hxord) (by simpa [H, O, P] using hHnot9)
  have hHset : (↑H : Set G) = (↑O : Set G) * (↑P : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left O P hPnormO
  have hyMul : y ∈ (↑O : Set G) * (↑P : Set G) := by
    rw [← hHset]
    exact hyH
  exact exists_mem_pCore_conj_of_mem_mul hPnormO hyMul hyP

theorem exists_conj_zpowers_bd (a : S23_9_AdjData D Ch c hV d b hb r)
    (hbr : orderOf b = r) (hr3 : r = 3) :
    ∃ g ∈ a.X, Subgroup.zpowers (bd a) =
      (Subgroup.zpowers b).map (MulAut.conj g).toMonoidHom := by
  have hr : r.Prime := by rw [hr3]; exact Nat.prime_three
  have hr2 : r ≠ 2 := by rw [hr3]; norm_num
  obtain ⟨w, hw, hwinv⟩ := a.exists_w_inverts_dhat hr hr2 hbr
  obtain ⟨o, hoO, hconjP⟩ := a.exists_pCore_conj_of_inverting hbr hr3 hw hwinv
  have hoX : o ∈ a.X := by
    obtain ⟨u, -, rfl⟩ := Subgroup.mem_map.mp hoO
    exact u.2
  have hxord : orderOf ((o * w) * b * (o * w)⁻¹) = 3 := by
    have heq : (o * w) * b * (o * w)⁻¹ = o * (w * b * w⁻¹) * o⁻¹ := by group
    rw [heq]
    exact (MulEquiv.orderOf_eq (MulAut.conj o) (w * b * w⁻¹)).trans
      (by
        have hxeq : w * b * w⁻¹ = (MulAut.conj w) b := by simp [MulAut.conj_apply]
        rw [hxeq, MulEquiv.orderOf_eq (MulAut.conj w) b, hbr, hr3])
  refine ⟨o * w, a.X.mul_mem hoX hw, ?_⟩
  rw [MonoidHom.map_zpowers]
  have hconj : (MulEquiv.toMonoidHom (MulAut.conj (o * w))) b =
      (o * w) * b * (o * w)⁻¹ := rfl
  rw [hconj]
  have hgen : (o * w) * b * (o * w)⁻¹ = o * (w * b * w⁻¹) * o⁻¹ := by group
  rw [hgen]
  have hle : Subgroup.zpowers (o * (w * b * w⁻¹) * o⁻¹) ≤ Subgroup.zpowers (bd a) :=
    Subgroup.zpowers_le.mpr hconjP
  have hcard : Nat.card (Subgroup.zpowers (o * (w * b * w⁻¹) * o⁻¹)) = 3 := by
    rw [Nat.card_zpowers, ← hgen]
    exact hxord
  exact (Subgroup.eq_of_le_of_card_ge hle
    (by rw [hcard, Nat.card_zpowers, a.orderOf_bd hbr hr3])).symm

theorem fixV_zpowers_bd_eq_bot (a : S23_9_AdjData D Ch c hV d b hb r)
    (hbr : orderOf b = r) (hr3 : r = 3)
    (hfixb : d.fixV (barImage D.M (Subgroup.zpowers b)) = ⊥) :
    d.fixV (barImage D.M (Subgroup.zpowers (bd a))) = ⊥ := by
  obtain ⟨g, hgX, hconj⟩ := a.exists_conj_zpowers_bd hbr hr3
  letI : Fact d.q.Prime := ⟨d.hq⟩
  letI : d.E.Normal := d.hEnorm
  letI : IsPGroup d.q ↥d.E := d.hEp
  letI : IsElementaryAbelian d.q (↥d.E ⧸ frattini ↥d.E) := d.hEel
  letI : CommGroup (↥d.E ⧸ frattini ↥d.E) := IsMulCommutative.instCommGroup
  have hXM : a.X ≤ D.M :=
    a.hXK.trans ((CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p21c_Hinf_le _).trans inf_le_left)
  have hgM : g ∈ D.M := hXM hgX
  have hbM : b ∈ D.M := c.hBM hb
  have hbar : barImage D.M (Subgroup.zpowers (bd a)) =
      (barImage D.M (Subgroup.zpowers b)).map
        (MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨g, hgM⟩)).toMonoidHom := by
    rw [hconj]
    exact CFSG.GroupTheory.barImage_map_conj D.M (Subgroup.zpowers b)
      (Subgroup.zpowers_le.mpr hbM) hgM
  rw [hbar]
  exact CFSG.GroupTheory.fixV_map_conj_eq_bot d.rep (barImage D.M (Subgroup.zpowers b))
    (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨g, hgM⟩) hfixb

private theorem X_le_M (a : S23_9_AdjData D Ch c hV d b hb r) : a.X ≤ D.M :=
  a.hXK.trans ((CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p21c_Hinf_le _).trans inf_le_left)

private theorem mk_bar_pow_three_commute (a : S23_9_AdjData D Ch c hV d b hb r)
    (hbr : orderOf b = r) (hr3 : r = 3) (hbM : b ∈ D.M) (hdM : a.dRoot ∈ D.M) :
    let x : Bar2 D.M := QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨b, hbM⟩
    let y : Bar2 D.M := QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨a.dRoot, hdM⟩
    x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ Commute x y := by
  have hb3 : b ^ 3 = 1 := by
    have h : orderOf b = 3 := hbr.trans hr3
    simpa [h] using pow_orderOf_eq_one b
  have hd3 : a.dRoot ^ 3 = 1 := by
    have h : orderOf a.dRoot = 3 := a.hdorder.trans hr3
    simpa [h] using pow_orderOf_eq_one a.dRoot
  have hx3 : (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨b, hbM⟩ : Bar2 D.M) ^ 3 = 1 := by
    rw [← map_pow]
    rw [show (⟨b, hbM⟩ : ↥D.M) ^ 3 = 1 by ext; simpa using hb3, map_one]
  have hy3 : (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨a.dRoot, hdM⟩ : Bar2 D.M) ^ 3 = 1 := by
    rw [← map_pow]
    rw [show (⟨a.dRoot, hdM⟩ : ↥D.M) ^ 3 = 1 by ext; simpa using hd3, map_one]
  refine ⟨hx3, hy3, ?_⟩
  have hb' : Commute (⟨b, hbM⟩ : ↥D.M) ⟨a.dRoot, hdM⟩ := by
    apply Subtype.ext
    exact a.hdb.symm
  simpa using hb'.map (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M))

private theorem fixV_zpowers_bar_mul_eq_bot (a : S23_9_AdjData D Ch c hV d b hb r)
    (hbr : orderOf b = r) (hr3 : r = 3)
    (hfixb : d.fixV (barImage D.M (Subgroup.zpowers b)) = ⊥)
    (hbM : b ∈ D.M) (hdM : a.dRoot ∈ D.M) :
    d.fixV (Subgroup.zpowers
      ((QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨b, hbM⟩) *
        (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨a.dRoot, hdM⟩))) = ⊥ := by
  have hbdM : bd a ∈ D.M := D.M.mul_mem hbM hdM
  have himg : (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨bd a, hbdM⟩) =
      (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨b, hbM⟩) *
        (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨a.dRoot, hdM⟩) := by
    have hsub : (⟨bd a, hbdM⟩ : ↥D.M) = ⟨b, hbM⟩ * ⟨a.dRoot, hdM⟩ := by
      apply Subtype.ext
      change bd a = b * a.dRoot
      rw [bd_eq a]
    rw [hsub, map_mul]
  rw [← himg, ← barImage_zpowers_eq hbdM]
  exact fixV_zpowers_bd_eq_bot a hbr hr3 hfixb

private theorem fixV_zpowers_bar_mul_inv_eq_bot (a : S23_9_AdjData D Ch c hV d b hb r)
    (hc : d.fixV (barImage D.M (Subgroup.zpowers (ctilde a))) = ⊥)
    (hbM : b ∈ D.M) (hdM : a.dRoot ∈ D.M) :
    d.fixV (Subgroup.zpowers
      ((QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨b, hbM⟩) *
        (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨a.dRoot, hdM⟩)⁻¹)) = ⊥ := by
  have hcM : ctilde a ∈ D.M := D.M.mul_mem hbM (D.M.inv_mem hdM)
  have himg : (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨ctilde a, hcM⟩) =
      (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨b, hbM⟩) *
        (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨a.dRoot, hdM⟩)⁻¹ := by
    have hsub : (⟨ctilde a, hcM⟩ : ↥D.M) = ⟨b, hbM⟩ * ⟨a.dRoot, hdM⟩⁻¹ := by
      apply Subtype.ext
      change ctilde a = b * a.dRoot⁻¹
      rw [ctilde_eq a]
    rw [hsub, map_mul, map_inv]
  rw [← himg, ← barImage_zpowers_eq hcM]
  exact hc

theorem le_ker_of_fixV_ctilde_eq_bot (a : S23_9_AdjData D Ch c hV d b hb r)
    (hbr : orderOf b = r) (hr3 : r = 3) (hq3 : r ≠ d.q)
    (hfixb : d.fixV (barImage D.M (Subgroup.zpowers b)) = ⊥)
    (hc : d.fixV (barImage D.M (Subgroup.zpowers (ctilde a))) = ⊥) :
    barImage D.M (Subgroup.zpowers a.dRoot) ≤ d.rep.ker := by
  letI : Fact d.q.Prime := ⟨d.hq⟩
  letI : d.E.Normal := d.hEnorm
  letI : IsPGroup d.q ↥d.E := d.hEp
  letI : IsElementaryAbelian d.q (↥d.E ⧸ frattini ↥d.E) := d.hEel
  letI : CommGroup (↥d.E ⧸ frattini ↥d.E) := IsMulCommutative.instCommGroup
  have hbM : b ∈ D.M := c.hBM hb
  have hdM : a.dRoot ∈ D.M := a.X_le_M a.hdX
  let x : Bar2 D.M := QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨b, hbM⟩
  let y : Bar2 D.M := QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨a.dRoot, hdM⟩
  obtain ⟨hx3, hy3, hcomm⟩ := a.mk_bar_pow_three_commute hbr hr3 hbM hdM
  have hxfix : d.fixV (Subgroup.zpowers x) = ⊥ := by
    rw [← barImage_zpowers_eq hbM]
    exact hfixb
  have hxyfix : d.fixV (Subgroup.zpowers (x * y)) = ⊥ :=
    a.fixV_zpowers_bar_mul_eq_bot hbr hr3 hfixb hbM hdM
  have hxyifix : d.fixV (Subgroup.zpowers (x * y⁻¹)) = ⊥ :=
    a.fixV_zpowers_bar_mul_inv_eq_bot hc hbM hdM
  have hq3' : d.q ≠ 3 := fun h => hq3 (hr3.trans h.symm)
  have htop : d.fixV (Subgroup.zpowers y) = ⊤ :=
    CFSG.GroupTheory.fixV_zpowers_eq_top_of_commute_of_pow_three
      (ρ := d.rep) d.hq hq3' hcomm hx3 hy3 hxfix hxyfix hxyifix
  have hle : Subgroup.zpowers y ≤ d.rep.ker :=
    (CFSG.GroupTheory.fixV_eq_top_iff_le_ker d.rep (Subgroup.zpowers y)).mp htop
  rw [barImage_zpowers_eq hdM]
  exact hle

private theorem dRoot_mem_barPreimage (a : S23_9_AdjData D Ch c hV d b hb r)
    (hbr : orderOf b = r) (hr3 : r = 3) (hq3 : r ≠ d.q)
    (hfixb : d.fixV (barImage D.M (Subgroup.zpowers b)) = ⊥)
    (hc : d.fixV (barImage D.M (Subgroup.zpowers (ctilde a))) = ⊥) :
    a.dRoot ∈ barPreimage D.M d.rep.ker := by
  have hdM : a.dRoot ∈ D.M := a.X_le_M a.hdX
  refine uc22p21c_mem_barPreimage.2 ⟨hdM, ?_⟩
  have hle := a.le_ker_of_fixV_ctilde_eq_bot hbr hr3 hq3 hfixb hc
  rw [barImage_zpowers_eq hdM] at hle
  have hleker := hle (Subgroup.mem_zpowers
    ((QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)) ⟨a.dRoot, hdM⟩))
  simpa [uc22p21cPi] using hleker

private theorem map_subgroupOf_eq_top_of_mem (a : S23_9_AdjData D Ch c hV d b hb r)
    {N : Subgroup G}
    (hNnormX : a.X ≤ Subgroup.normalizer (N : Set G)) (hdN : a.dRoot ∈ N) (hr3 : r = 3) :
    (N.subgroupOf a.X).map a.qX = ⊤ := by
  haveI : (N.subgroupOf a.X).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hNnormX
  have hxmem : (⟨a.dRoot, a.hdX⟩ : ↥a.X) ∈ N.subgroupOf a.X :=
    Subgroup.mem_subgroupOf.mpr hdN
  have hdhat_mem : a.dhat ∈ (N.subgroupOf a.X).map a.qX :=
    Subgroup.mem_map.mpr ⟨⟨a.dRoot, a.hdX⟩, hxmem, rfl⟩
  have hdhat_ne : a.dhat ≠ 1 := by
    have hord : orderOf a.dhat = 3 := by
      rw [a.orderOf_dhat (hr3 ▸ Nat.prime_three) (hr3 ▸ (by norm_num : (3 : ℕ) ≠ 2))]
      exact hr3
    intro h
    rw [h, orderOf_one] at hord
    omega
  have hnt : (N.subgroupOf a.X).map a.qX ≠ ⊥ := by
    intro h
    rw [h] at hdhat_mem
    exact hdhat_ne (Subgroup.mem_bot.mp hdhat_mem)
  haveI : IsSimpleGroup (Bar2 a.X) :=
    CFSG.GroupTheory.isSimpleGroup_of_isSLn_two a.hm2 a.hXsl
  rcases (inferInstance : IsSimpleGroup (Bar2 a.X)).eq_bot_or_eq_top_of_normal
    ((N.subgroupOf a.X).map a.qX) with h | h
  · exact absurd h hnt
  · exact h

private theorem sup_pCore_eq_top_of_map_eq_top (a : S23_9_AdjData D Ch c hV d b hb r)
    {N : Subgroup G}
    (htop : (N.subgroupOf a.X).map a.qX = ⊤) :
    N.subgroupOf a.X ⊔ CFSG.pCore 2 ↥a.X = ⊤ := by
  have hsup : N.subgroupOf a.X ⊔ a.qX.ker = ⊤ := by
    rw [← codisjoint_iff]
    refine (Subgroup.map_eq_range_iff).mp ?_
    rw [htop]
    exact (MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)).symm
  simpa [S23_9_AdjData.qX] using hsup

private theorem le_of_sup_pCore_eq_top (a : S23_9_AdjData D Ch c hV d b hb r)
    {N : Subgroup G}
    (hNnormX : a.X ≤ Subgroup.normalizer (N : Set G))
    (hsup : N.subgroupOf a.X ⊔ CFSG.pCore 2 ↥a.X = ⊤) : a.X ≤ N := by
  haveI : (N.subgroupOf a.X).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hNnormX
  have hP : IsPGroup 2 (CFSG.pCore 2 ↥a.X) := CFSG.pCore_isPGroup (p := 2) (G := ↥a.X)
  have htopPerf : (⁅(⊤ : Subgroup ↥a.X), (⊤ : Subgroup ↥a.X)⁆ : Subgroup ↥a.X) = ⊤ := by
    haveI : Group.IsPerfect ↥a.X := Subgroup.isPerfect_iff.mpr a.hXperf
    rw [← _root_.commutator_def]
    exact Group.IsPerfect.commutator_eq_top
  have htopN : (⊤ : Subgroup ↥a.X) ≤ N.subgroupOf a.X :=
    CFSG.GroupTheory.le_of_commutator_eq_self_of_le_sup_of_isPGroup
      (X := ↥a.X) (K := ⊤) (N := N.subgroupOf a.X)
      (P := CFSG.pCore 2 ↥a.X) hP htopPerf (le_of_eq hsup.symm)
  intro x hx
  exact Subgroup.mem_subgroupOf.mp (htopN (Subgroup.mem_top ⟨x, hx⟩))

theorem fixV_ctilde_ne_bot (a : S23_9_AdjData D Ch c hV d b hb r)
    (hbr : orderOf b = r) (hr3 : r = 3) (hq3 : r ≠ d.q)
    (hfixb : d.fixV (barImage D.M (Subgroup.zpowers b)) = ⊥) :
    d.fixV (barImage D.M (Subgroup.zpowers (ctilde a))) ≠ ⊥ := by
  intro hbot
  let N : Subgroup G := barPreimage D.M d.rep.ker
  have hNnormM : D.M ≤ Subgroup.normalizer (N : Set G) := by
    haveI : d.rep.ker.Normal := MonoidHom.normal_ker d.rep
    exact uc22p22u_barPreimage_normalizes (D := d.rep.ker)
  have hNnormX : a.X ≤ Subgroup.normalizer (N : Set G) := a.X_le_M.trans hNnormM
  have hdN : a.dRoot ∈ N := a.dRoot_mem_barPreimage hbr hr3 hq3 hfixb hbot
  have htop : (N.subgroupOf a.X).map a.qX = ⊤ :=
    a.map_subgroupOf_eq_top_of_mem hNnormX hdN hr3
  have hsup : N.subgroupOf a.X ⊔ CFSG.pCore 2 ↥a.X = ⊤ :=
    a.sup_pCore_eq_top_of_map_eq_top htop
  have hXleN : a.X ≤ N := a.le_of_sup_pCore_eq_top hNnormX hsup
  have hNcomap : N.subgroupOf D.M =
      (d.rep.ker).comap (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)) := by
    ext x
    constructor
    · intro hx
      exact (uc22p21c_mem_barPreimage.mp (Subgroup.mem_subgroupOf.mp hx)).2
    · intro hx
      exact Subgroup.mem_subgroupOf.mpr
        (uc22p21c_mem_barPreimage.mpr ⟨x.2, hx⟩)
  have hbar_le : barImage D.M a.X ≤ d.rep.ker := by
    rw [show barImage D.M a.X =
      (a.X.subgroupOf D.M).map (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)) from rfl,
      Subgroup.map_le_iff_le_comap]
    intro u hu
    rw [← hNcomap]
    exact Subgroup.subgroupOf_mono D.M hXleN hu
  exact a.hnotker hbar_le

end S23_9_AdjData

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
