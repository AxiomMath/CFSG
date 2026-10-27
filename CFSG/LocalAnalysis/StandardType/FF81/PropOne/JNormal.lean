module

public import CFSG.LocalAnalysis.StandardType.FF81.PropOne.CenbStruct
public import CFSG.LocalAnalysis.StandardType.FF81.PropOne.JStruct
import CFSG.Adapters.LieModelSimple
import CFSG.Adapters.StatedClassicalOrders
import CFSG.CGT.Timmesfeld75.L2Pair
import CFSG.CGT.Timmesfeld75.ListWCBasic
import CFSG.ClassicalGroups

@[expose] public section

namespace CFSG.StandardType.FF81.PropOne

open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open scoped Pointwise

private theorem exists_zpow_mul_of_mem_sup {G : Type} [Group G] {a : G} {J : Subgroup G}
    (hcomm : ∀ y ∈ J, y * a = a * y) {x : G} (hx : x ∈ Subgroup.zpowers a ⊔ J) :
    ∃ k : ℤ, ∃ y ∈ J, x = a ^ k * y := by
  have hLE : Subgroup.zpowers a ≤ Subgroup.normalizer (J : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      rw [← hcomm h hh]
      simpa using hh
    · intro hh
      have hk : h = a * h * a⁻¹ := by
        calc h = a⁻¹ * (a * h * a⁻¹) * a := by group
          _ = a⁻¹ * ((a * h * a⁻¹) * a) := by group
          _ = a⁻¹ * (a * (a * h * a⁻¹)) := by rw [hcomm (a * h * a⁻¹) hh]
          _ = a * h * a⁻¹ := by group
      rwa [hk]
  have hcoe : (↑(Subgroup.zpowers a ⊔ J) : Set G) =
      (Subgroup.zpowers a : Set G) * (J : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right _ _ hLE
  have hx' : x ∈ (Subgroup.zpowers a : Set G) * (J : Set G) := hcoe ▸ hx
  obtain ⟨c, hc, y, hy, hcy⟩ := hx'
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
  exact ⟨k, y, hy, hcy.symm⟩

private theorem two_dvd_card_of_statedClassicalModel_psl {X : Type} [Group X] {n : ℕ}
    (h : StatedClassicalModel X .PSL (n - 1) 2 1) (hn : n = 5 ∨ n = 6) :
    2 ∣ Nat.card X := by
  rcases hn with rfl | rfl
  · rw [CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl (by norm_num) h]
    norm_num [Finset.prod_Icc_succ_top]
  · rw [CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl (by norm_num) h]
    norm_num [Finset.prod_Icc_succ_top]

private theorem exists_decomp_of_mem_X {G : Type} [Group G] [Finite G] {n : ℕ} {b : G}
    {L : Subgroup G} {z : Fin 3 → ↥L} (h : Counterexample G n b L z)
    (hodd : Odd (Nat.card ↥(cB b z))) {J : Subgroup G} (hJ : JData n L z J) {x : G}
    (hx : x ∈ Subgroup.centralizer ({b} : Set G) ⊓
      Subgroup.centralizer ({GGFF.zs z 0} : Set G)) :
    ∃ (O : Subgroup G) (i : ℕ) (o : G) (k : ℤ) (y : G),
      O ≤ Subgroup.centralizer ({b} : Set G) ∧ O ≤ Subgroup.centralizer (L : Set G) ∧
      Odd (Nat.card O) ∧ o ∈ O ∧ y ∈ J ∧
      x = (b ^ i * o * GGFF.zs z 0 ^ k) * y ∧
      (∀ j ∈ J, (b ^ i * o * GGFF.zs z 0 ^ k) * j = j * (b ^ i * o * GGFF.zs z 0 ^ k)) := by
  obtain ⟨O, hO_le_b, hO_le_L, hOodd, -, hOdec⟩ := exists_cen_decomp h hodd
  have hxCb : x ∈ Subgroup.centralizer ({b} : Set G) := hx.1
  have hxCb1 : x ∈ Subgroup.centralizer ({GGFF.zs z 0} : Set G) := hx.2
  obtain ⟨i, o, hoO, l, hlL, hxdec⟩ := hOdec x hxCb
  have hb_Cb1 : b ∈ Subgroup.centralizer ({GGFF.zs z 0} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    rw [Set.mem_singleton_iff] at hc
    subst hc
    exact Subgroup.mem_centralizer_singleton_iff.mp (h.hypA.le (z 0).2)
  have ho_Cb1 : o ∈ Subgroup.centralizer ({GGFF.zs z 0} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    rw [Set.mem_singleton_iff] at hc
    subst hc
    exact Subgroup.mem_centralizer_iff.mp (hO_le_L hoO) (z 0) (z 0).2
  have hl_Cb1 : l ∈ Subgroup.centralizer ({GGFF.zs z 0} : Set G) := by
    have hbo : b ^ i * o ∈ Subgroup.centralizer ({GGFF.zs z 0} : Set G) :=
      (Subgroup.centralizer _).mul_mem ((Subgroup.centralizer _).pow_mem hb_Cb1 i) ho_Cb1
    have hl_eq : l = (b ^ i * o)⁻¹ * x := by rw [hxdec]; group
    rw [hl_eq]
    exact (Subgroup.centralizer _).mul_mem ((Subgroup.centralizer _).inv_mem hbo) hxCb1
  have hl_sup : l ∈ Subgroup.zpowers (GGFF.zs z 0) ⊔ J := by
    rw [← hJ.cen]
    exact ⟨hlL, hl_Cb1⟩
  obtain ⟨k, y, hyJ, hly⟩ := exists_zpow_mul_of_mem_sup hJ.comm hl_sup
  refine ⟨O, i, o, k, y, hO_le_b, hO_le_L, hOodd, hoO, hyJ, ?_, ?_⟩
  · rw [hxdec, hly]; group
  · intro j hj
    have hbj : Commute (b ^ i) j :=
      Commute.pow_left (Subgroup.mem_centralizer_singleton_iff.mp (h.hypA.le (hJ.le hj))).symm i
    have hoj : Commute o j :=
      Commute.symm (Subgroup.mem_centralizer_iff.mp (hO_le_L hoO) j (hJ.le hj))
    have hzj : Commute (GGFF.zs z 0 ^ k) j :=
      Commute.zpow_left (hJ.comm j hj).symm k
    exact ((hbj.mul_left hoj).mul_left hzj).eq

private theorem conj_mem_J_of_mem_X {G : Type} [Group G] [Finite G] {n : ℕ} {b : G}
    {L : Subgroup G} {z : Fin 3 → ↥L} (h : Counterexample G n b L z)
    (hodd : Odd (Nat.card ↥(cB b z))) {J : Subgroup G} (hJ : JData n L z J) {x : G}
    (hx : x ∈ Subgroup.centralizer ({b} : Set G) ⊓
      Subgroup.centralizer ({GGFF.zs z 0} : Set G)) :
    ∀ j ∈ J, x * j * x⁻¹ ∈ J := by
  obtain ⟨O, i, o, k, y, -, -, -, -, hyJ, hxuy, hu_comm⟩ :=
    exists_decomp_of_mem_X h hodd hJ hx
  intro j hj
  rw [hxuy]
  have hyj : y * j * y⁻¹ ∈ J := J.mul_mem (J.mul_mem hyJ hj) (J.inv_mem hyJ)
  have hcalc : (b ^ i * o * GGFF.zs z 0 ^ k) * y * j *
      ((b ^ i * o * GGFF.zs z 0 ^ k) * y)⁻¹ = y * j * y⁻¹ := by
    calc (b ^ i * o * GGFF.zs z 0 ^ k) * y * j *
          ((b ^ i * o * GGFF.zs z 0 ^ k) * y)⁻¹
        = (b ^ i * o * GGFF.zs z 0 ^ k) * (y * j * y⁻¹) *
          (b ^ i * o * GGFF.zs z 0 ^ k)⁻¹ := by group
      _ = y * j * y⁻¹ := by rw [hu_comm (y * j * y⁻¹) hyj]; group
  rw [hcalc]
  exact hyj

private theorem mem_J_of_involution {G : Type} [Group G] [Finite G] {n : ℕ} {b : G}
    {L : Subgroup G} {z : Fin 3 → ↥L} (h : Counterexample G n b L z)
    (hodd : Odd (Nat.card ↥(cB b z))) {J : Subgroup G} (hJ : JData n L z J) {s : G}
    (hsX : s ∈ Subgroup.centralizer ({b} : Set G) ⊓
      Subgroup.centralizer ({GGFF.zs z 0} : Set G))
    (hs2 : s * s = 1) : s ∈ J := by
  obtain ⟨O, i, o, k, y, hO_le_b, hO_le_L, hOodd, hoO, hyJ, hsuy, hu_comm⟩ :=
    exists_decomp_of_mem_X h hodd hJ hsX
  have hsuy' : s = (b ^ i * o * GGFF.zs z 0 ^ k) * y := hsuy
  have huy : Commute (b ^ i * o * GGFF.zs z 0 ^ k) y := hu_comm y hyJ
  have hu2y2 : (b ^ i * o * GGFF.zs z 0 ^ k) ^ 2 * y ^ 2 = 1 := by
    rw [← huy.mul_pow 2, show ((b ^ i * o * GGFF.zs z 0 ^ k) * y) ^ 2 = 1 from by
      rw [sq, ← hsuy', hs2]]
  have hu2J : (b ^ i * o * GGFF.zs z 0 ^ k) ^ 2 ∈ J := by
    rw [eq_inv_of_mul_eq_one_left hu2y2]
    exact J.inv_mem (J.pow_mem hyJ 2)
  have hbo : Commute b o := (Subgroup.mem_centralizer_singleton_iff.mp (hO_le_b hoO)).symm
  have hbz : Commute b (GGFF.zs z 0) :=
    (Subgroup.mem_centralizer_singleton_iff.mp (h.hypA.le (z 0).2)).symm
  have hoz : Commute o (GGFF.zs z 0) :=
    (Subgroup.mem_centralizer_iff.mp (hO_le_L hoO) (z 0) (z 0).2).symm
  have hz3 : GGFF.zs z 0 ^ 3 = 1 := by
    change (z 0 : G) ^ 3 = 1
    rw [← Subgroup.coe_pow, h.model.pow_z, Subgroup.coe_one]
  have hu2_exp : (b ^ i * o * GGFF.zs z 0 ^ k) ^ 2 =
      b ^ (2 * i) * o ^ 2 * GGFF.zs z 0 ^ (2 * k) := by
    have h1 : (b ^ i * o) ^ 2 = b ^ (2 * i) * o ^ 2 := by
      rw [(hbo.pow_left i).mul_pow, ← pow_mul b i 2, Nat.mul_comm i 2]
    have hzk : (GGFF.zs z 0 ^ k) ^ 2 = GGFF.zs z 0 ^ (2 * k) := by
      rw [pow_two, ← zpow_add]
      congr 1
      ring
    have h2 : Commute (b ^ i * o) (GGFF.zs z 0 ^ k) :=
      ((hbz.pow_left i).zpow_right k).mul_left (hoz.zpow_right k)
    rw [show b ^ i * o * GGFF.zs z 0 ^ k = (b ^ i * o) * GGFF.zs z 0 ^ k from by group]
    rw [h2.mul_pow 2, h1, hzk]
  have hw_eq : b ^ (2 * i) * o ^ 2 =
      (b ^ i * o * GGFF.zs z 0 ^ k) ^ 2 * (GGFF.zs z 0 ^ (2 * k))⁻¹ := by
    rw [hu2_exp]; group
  have hwL : b ^ (2 * i) * o ^ 2 ∈ L := by
    rw [hw_eq]
    exact L.mul_mem (hJ.le hu2J) (L.inv_mem (L.zpow_mem (z 0).2 (2 * k)))
  have hw_cen : ∀ c ∈ L, (b ^ (2 * i) * o ^ 2) * c = c * (b ^ (2 * i) * o ^ 2) := by
    intro c hc
    have h1 : Commute (b ^ (2 * i)) c :=
      Commute.pow_left
        (Commute.symm (Subgroup.mem_centralizer_singleton_iff.mp (h.hypA.le hc))) (2 * i)
    have h2 : Commute (o ^ 2) c :=
      Commute.pow_left
        (Commute.symm (Subgroup.mem_centralizer_iff.mp (hO_le_L hoO) c hc)) 2
    exact (h1.mul_left h2).eq
  have hw1 : b ^ (2 * i) * o ^ 2 = 1 := by
    have := h.model.eq_one_of_forall_comm (x := ⟨b ^ (2 * i) * o ^ 2, hwL⟩)
      (fun c => Subtype.ext (hw_cen c c.2))
    exact congrArg Subtype.val this
  have hu2_zpow : (b ^ i * o * GGFF.zs z 0 ^ k) ^ 2 = GGFF.zs z 0 ^ (2 * k) := by
    rw [hu2_exp, hw1, one_mul]
  have hu2_one : (b ^ i * o * GGFF.zs z 0 ^ k) ^ 2 = 1 := by
    have hmem : (b ^ i * o * GGFF.zs z 0 ^ k) ^ 2 ∈
        Subgroup.zpowers (GGFF.zs z 0) ⊓ J := by
      refine ⟨?_, hu2J⟩
      rw [hu2_zpow]
      exact Subgroup.zpow_mem_zpowers _ _
    rw [hJ.inf, Subgroup.mem_bot] at hmem
    exact hmem
  have hb3 : b ^ 3 = 1 := by rw [← h.hypA.ord]; exact pow_orderOf_eq_one b
  have hcomm_bo : Commute (b ^ i) o := hbo.pow_left i
  have hcomm_boz : Commute (b ^ i * o) (GGFF.zs z 0 ^ k) :=
    ((hbz.pow_left i).zpow_right k).mul_left (hoz.zpow_right k)
  have hb_i_pow : (b ^ i) ^ (3 * Nat.card O) = 1 := by
    rw [← pow_mul, show i * (3 * Nat.card O) = 3 * (i * Nat.card O) by ring, pow_mul, hb3,
      one_pow]
  have ho_card : o ^ Nat.card O = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (by
      rw [← Nat.card_zpowers]
      exact Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hoO))
  have ho_pow : o ^ (3 * Nat.card O) = 1 := by
    rw [show 3 * Nat.card O = Nat.card O * 3 by ring, pow_mul, ho_card, one_pow]
  have hzk_pow : (GGFF.zs z 0 ^ k) ^ (3 * Nat.card O) = 1 := by
    have hzk3 : (GGFF.zs z 0 ^ k) ^ 3 = 1 := by
      rw [← zpow_natCast (GGFF.zs z 0 ^ k) 3, ← zpow_mul, zpow_mul', zpow_natCast, hz3,
        one_zpow]
    rw [pow_mul, hzk3, one_pow]
  have hbo_pow : (b ^ i * o) ^ (3 * Nat.card O) = 1 := by
    rw [hcomm_bo.mul_pow, hb_i_pow, ho_pow, one_mul]
  have hu_pow_odd : (b ^ i * o * GGFF.zs z 0 ^ k) ^ (3 * Nat.card O) = 1 := by
    rw [show b ^ i * o * GGFF.zs z 0 ^ k = (b ^ i * o) * GGFF.zs z 0 ^ k from by group,
      hcomm_boz.mul_pow, hbo_pow, hzk_pow, one_mul]
  have hodd_m : Odd (3 * Nat.card O) := (by decide : Odd 3).mul hOodd
  have hu_dvd2 : orderOf (b ^ i * o * GGFF.zs z 0 ^ k) ∣ 2 :=
    orderOf_dvd_iff_pow_eq_one.mpr hu2_one
  have hu_dvd_m : orderOf (b ^ i * o * GGFF.zs z 0 ^ k) ∣ 3 * Nat.card O :=
    orderOf_dvd_iff_pow_eq_one.mpr hu_pow_odd
  have hodd_ord : Odd (orderOf (b ^ i * o * GGFF.zs z 0 ^ k)) := hodd_m.of_dvd_nat hu_dvd_m
  have hu_eq1 : b ^ i * o * GGFF.zs z 0 ^ k = 1 := by
    rw [← orderOf_eq_one_iff]
    have hle : orderOf (b ^ i * o * GGFF.zs z 0 ^ k) ≤ 2 :=
      Nat.le_of_dvd (by norm_num) hu_dvd2
    have hpos : 0 < orderOf (b ^ i * o * GGFF.zs z 0 ^ k) :=
      Nat.pos_of_dvd_of_pos hu_dvd2 (by norm_num)
    have : orderOf (b ^ i * o * GGFF.zs z 0 ^ k) = 1 ∨
        orderOf (b ^ i * o * GGFF.zs z 0 ^ k) = 2 := by omega
    rcases this with h1 | h1
    · exact h1
    · exact absurd (h1 ▸ hodd_ord) (by decide)
  rw [show s = y from by rw [hsuy', hu_eq1, one_mul]]
  exact hyJ

theorem conj_mem_J {G : Type} [Group G] [Finite G] {n : ℕ} {b : G} {L : Subgroup G}
    {z : Fin 3 → ↥L} (h : Counterexample G n b L z) (hodd : Odd (Nat.card ↥(cB b z)))
    {J : Subgroup G} (hJ : JData n L z J) {t : G}
    (ht₀ : t * GGFF.zs z 0 = GGFF.zs z 0 * t)
    (htb : ∃ k : ℤ, t * b * t⁻¹ = GGFF.zs z 0 ^ k * b) :
    ∀ x ∈ J, t * x * t⁻¹ ∈ J := by
  let X : Subgroup G := Subgroup.centralizer ({b} : Set G) ⊓
    Subgroup.centralizer ({GGFF.zs z 0} : Set G)
  have hJX : J ≤ X := by
    intro j hj
    refine ⟨h.hypA.le (hJ.le hj), ?_⟩
    exact Subgroup.mem_centralizer_iff.mpr fun c hc => by
      rw [Set.mem_singleton_iff] at hc
      subst hc
      exact (hJ.comm j hj).symm
  have htX_le : X.map (MulAut.conj t).toMonoidHom ≤ X := by
    rintro y ⟨x, hxX, rfl⟩
    have hxCb : x ∈ Subgroup.centralizer ({b} : Set G) := hxX.1
    have hxCb1 : x ∈ Subgroup.centralizer ({GGFF.zs z 0} : Set G) := hxX.2
    have htc : Commute t (GGFF.zs z 0) := ht₀
    have hxb : Commute x b :=
      Commute.symm (Subgroup.mem_centralizer_iff.mp hxCb b (by simp))
    have hxt : Commute x (GGFF.zs z 0) :=
      Commute.symm (Subgroup.mem_centralizer_iff.mp hxCb1 (GGFF.zs z 0) (by simp))
    have htxz : Commute (t * x * t⁻¹) (GGFF.zs z 0) := by
      calc t * x * t⁻¹ * GGFF.zs z 0 = t * x * (t⁻¹ * GGFF.zs z 0) := by group
        _ = t * x * (GGFF.zs z 0 * t⁻¹) := by rw [htc.inv_left.eq]
        _ = t * (x * GGFF.zs z 0) * t⁻¹ := by group
        _ = t * (GGFF.zs z 0 * x) * t⁻¹ := by rw [hxt.eq]
        _ = (t * GGFF.zs z 0) * x * t⁻¹ := by group
        _ = (GGFF.zs z 0 * t) * x * t⁻¹ := by rw [ht₀]
        _ = GGFF.zs z 0 * (t * x * t⁻¹) := by group
    have h1 : Commute (t * x * t⁻¹) (t * b * t⁻¹) := by
      calc (t * x * t⁻¹) * (t * b * t⁻¹) = t * (x * b) * t⁻¹ := by group
        _ = t * (b * x) * t⁻¹ := by rw [hxb.eq]
        _ = (t * b * t⁻¹) * (t * x * t⁻¹) := by group
    have htxb : Commute (t * x * t⁻¹) b := by
      obtain ⟨k, hk⟩ := htb
      have hzkinv : Commute (t * x * t⁻¹) ((GGFF.zs z 0 ^ k)⁻¹) := by
        rw [← zpow_neg]
        exact htxz.zpow_right (-k)
      have hbeq : b = (GGFF.zs z 0 ^ k)⁻¹ * (t * b * t⁻¹) := by rw [hk]; group
      rw [hbeq]
      exact hzkinv.mul_right h1
    exact ⟨Subgroup.mem_centralizer_iff.mpr (fun c hc => by
        rw [Set.mem_singleton_iff] at hc
        subst hc
        exact htxb.symm),
      Subgroup.mem_centralizer_iff.mpr (fun c hc => by
        rw [Set.mem_singleton_iff] at hc
        subst hc
        exact htxz.symm)⟩
  have htXeq : X.map (MulAut.conj t).toMonoidHom = X :=
    Subgroup.eq_of_le_of_card_ge htX_le
      (le_of_eq (Subgroup.card_map_of_injective (MulAut.conj t).injective).symm)
  have htinvX : ∀ x ∈ X, t⁻¹ * x * t ∈ X := by
    intro x hxX
    have hx' : x ∈ X.map (MulAut.conj t).toMonoidHom := by rw [htXeq]; exact hxX
    obtain ⟨y, hyX, hyx⟩ := Subgroup.mem_map.mp hx'
    have hy_eq : y = t⁻¹ * x * t := by
      have := hyx
      simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply] at this
      rw [← this]; group
    rw [← hy_eq]
    exact hyX
  let K : Subgroup G := J.map (MulAut.conj t).toMonoidHom
  have hKX : K ≤ X := by
    rintro y ⟨j, hj, rfl⟩
    have hmem : (MulAut.conj t) j ∈ X.map (MulAut.conj t).toMonoidHom :=
      Subgroup.mem_map_of_mem _ (hJX hj)
    rwa [htXeq] at hmem
  have hKle : ∀ x ∈ X, K.map (MulAut.conj x).toMonoidHom ≤ K := by
    intro x hxX
    rintro y ⟨k, hkK, rfl⟩
    obtain ⟨j, hjJ, hjk⟩ := Subgroup.mem_map.mp hkK
    refine Subgroup.mem_map.mpr ⟨(t⁻¹ * x * t) * j * (t⁻¹ * x * t)⁻¹, ?_, ?_⟩
    · exact conj_mem_J_of_mem_X h hodd hJ (htinvX x hxX) j hjJ
    · rw [← hjk]
      simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply]
      group
  let D : Subgroup G := K ⊓ J
  have hD_le_J : D ≤ J := inf_le_right
  have hDnorm : (D.subgroupOf J).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hD_le_J]
    intro h k hhD hkJ
    have hhK : h ∈ K := hhD.1
    have hhJ : h ∈ J := hhD.2
    refine ⟨?_, ?_⟩
    · exact hKle k (hJX hkJ) (Subgroup.mem_map_of_mem (MulAut.conj k).toMonoidHom hhK)
    · exact J.mul_mem (J.mul_mem hkJ hhJ) (J.inv_mem hkJ)
  have hJsimple : IsSimpleGroup ↥J :=
    CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel hJ.model
  have h2dvd : 2 ∣ Nat.card ↥J :=
    two_dvd_card_of_statedClassicalModel_psl hJ.model h.hypA.n_cases
  obtain ⟨s₀, hs₀ord⟩ := exists_prime_orderOf_dvd_card' 2 h2dvd
  have hs₀_sq : s₀ * s₀ = 1 := by
    have hpow := pow_orderOf_eq_one s₀
    rw [hs₀ord] at hpow
    simpa [pow_two] using hpow
  have hs₀_ne : s₀ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hs₀ord
    omega
  let s : G := t * (s₀ : G) * t⁻¹
  have hsK : s ∈ K := Subgroup.mem_map_of_mem (MulAut.conj t).toMonoidHom s₀.2
  have hsX : s ∈ X := hKX hsK
  have hs_sq : s * s = 1 := by
    change t * (s₀ : G) * t⁻¹ * (t * (s₀ : G) * t⁻¹) = 1
    rw [show t * (s₀ : G) * t⁻¹ * (t * (s₀ : G) * t⁻¹) =
        t * ((s₀ : G) * (s₀ : G)) * t⁻¹ by group]
    rw [← Subgroup.coe_mul, hs₀_sq, Subgroup.coe_one]
    group
  have hs_ne : s ≠ 1 := by
    intro h1
    apply hs₀_ne
    apply Subtype.ext
    have h1' : t * (s₀ : G) * t⁻¹ = 1 := h1
    calc (s₀ : G) = t⁻¹ * (t * (s₀ : G) * t⁻¹) * t := by group
      _ = t⁻¹ * 1 * t := by rw [h1']
      _ = 1 := by group
  have hsJ : s ∈ J := mem_J_of_involution h hodd hJ hsX hs_sq
  have hsD : s ∈ D := ⟨hsK, hsJ⟩
  have hD_ne_bot : D ≠ ⊥ := by
    intro hbot
    have hs1 : s = 1 := by
      have := hsD
      rw [hbot, Subgroup.mem_bot] at this
      exact this
    exact hs_ne hs1
  have hDtop : D.subgroupOf J = ⊤ := by
    rcases hJsimple.eq_bot_or_eq_top_of_normal (D.subgroupOf J) with h | h
    · exfalso
      exact hD_ne_bot ((Subgroup.subgroupOf_eq_bot.mp h).eq_bot_of_le hD_le_J)
    · exact h
  have hJK : J ≤ K := (Subgroup.subgroupOf_eq_top.mp hDtop).trans inf_le_left
  have hKJ : K = J := by
    refine (Subgroup.eq_of_le_of_card_ge hJK ?_).symm
    show Nat.card (J.map (MulAut.conj t).toMonoidHom) ≤ Nat.card J
    rw [Subgroup.card_map_of_injective (MulAut.conj t).injective]
  intro x hx
  have hxK : t * x * t⁻¹ ∈ K := Subgroup.mem_map_of_mem (MulAut.conj t).toMonoidHom hx
  rw [hKJ] at hxK
  exact hxK

end CFSG.StandardType.FF81.PropOne

end
