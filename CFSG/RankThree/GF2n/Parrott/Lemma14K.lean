module

public import CFSG.RankThree.GF2n.Parrott.Lemma14Assembly
public import CFSG.RankThree.GF2n.Parrott.Lemma14NoQ8
public import CFSG.RankThree.GF2n.Parrott.Lemma14KR
public import CFSG.RankThree.GF2n.Parrott.Lemma16
public import CFSG.RankThree.GF2n.Parrott.Section2CJSigmaQ8
import all CFSG.RankThree.GF2n.Parrott.Section2Products
public import CFSG.RankThree.GF2n.Parrott.A1Section2Lemma14U

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open scoped commutatorElement

private theorem commutator_mul_right_left {M : Type*} [Group M] {a b w : M}
    (hwb : w * b = b * w) : a * w * b * (a * w)⁻¹ * b⁻¹ = a * b * a⁻¹ * b⁻¹ := by
  calc a * w * b * (a * w)⁻¹ * b⁻¹ = a * (w * b) * w⁻¹ * a⁻¹ * b⁻¹ := by group
    _ = a * b * a⁻¹ * b⁻¹ := by rw [hwb]; group

private theorem commutator_mul_right_right {M : Type*} [Group M] {a b w : M}
    (hwa : w * a = a * w) : a * (b * w) * a⁻¹ * (b * w)⁻¹ = a * b * a⁻¹ * b⁻¹ := by
  have hwa' : w * a⁻¹ = a⁻¹ * w := (show Commute w a from hwa).inv_right.eq
  calc a * (b * w) * a⁻¹ * (b * w)⁻¹ = a * b * (w * a⁻¹) * w⁻¹ * b⁻¹ := by group
    _ = a * b * a⁻¹ * b⁻¹ := by rw [hwa']; group

private theorem commutator_eq_of_mul {M : Type*} [Group M] {a b a' b' w : M}
    (hwa : w * a = a * w) (hwb : w * b = b * w) (ha : a' = a ∨ a' = a * w)
    (hb : b' = b ∨ b' = b * w) : a' * b' * a'⁻¹ * b'⁻¹ = a * b * a⁻¹ * b⁻¹ := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · rfl
  · exact commutator_mul_right_right hwa
  · exact commutator_mul_right_left hwb
  · have hwbw : w * (b * w) = b * w * w := by rw [← mul_assoc, hwb]
    rw [commutator_mul_right_left hwbw, commutator_mul_right_right hwa]

variable {G : Type} [Group G] [Finite G] {z : G}

theorem exists_mem_triple_conj_eq_and_sq (h : Tim79a.ParrottHyp z) {x : G} (_hxH : x ∈ H z)
    {p p' : G} (hp : p ∈ J z) (hp' : p' ∈ J z) (hpp' : p * p' * p⁻¹ * p'⁻¹ = z)
    (hxp : x * p * x⁻¹ * p⁻¹ ∈ Subgroup.zpowers z)
    (hxp' : x * p' * x⁻¹ * p'⁻¹ ∈ Subgroup.zpowers z) :
    ∃ c ∈ ({p, p', p * p'} : Set G),
      (x * c * x⁻¹ = c ∧ c * c = z) ∨ (x * c * x⁻¹ = c * z ∧ c * c = 1) := by
  have hz2 : z * z = 1 := by rw [← sq, ← h.1]; exact pow_orderOf_eq_one z
  have hzc : ∀ g ∈ H z, g * z = z * g := fun g hg =>
    Subgroup.mem_centralizer_singleton_iff.mp hg
  have hpH : p ∈ H z := J_le_H hp
  have hp'H : p' ∈ H z := J_le_H hp'
  have hz_or : ∀ {c : G}, c ∈ Subgroup.zpowers z → c = 1 ∨ c = z :=
    fun hc => (Subgroup.mem_zpowers_iff_of_orderOf_eq_two h.1).mp hc
  have hmul : x * (p * p') * x⁻¹ * (p * p')⁻¹ =
      (x * p * x⁻¹ * p⁻¹) * (x * p' * x⁻¹ * p'⁻¹) := by
    have hc : (x * p' * x⁻¹ * p'⁻¹) * p⁻¹ = p⁻¹ * (x * p' * x⁻¹ * p'⁻¹) := by
      rcases hz_or hxp' with h1 | h1 <;> rw [h1]
      · rw [one_mul, mul_one]
      · exact (hzc _ ((H z).inv_mem hpH)).symm
    calc x * (p * p') * x⁻¹ * (p * p')⁻¹
        = (x * p * x⁻¹ * p⁻¹) * p * ((x * p' * x⁻¹ * p'⁻¹) * p⁻¹) := by group
      _ = (x * p * x⁻¹ * p⁻¹) * p * (p⁻¹ * (x * p' * x⁻¹ * p'⁻¹)) := by rw [hc]
      _ = (x * p * x⁻¹ * p⁻¹) * (x * p' * x⁻¹ * p'⁻¹) := by group
  have hsq : p * p' * (p * p') = z * (p * p) * (p' * p') := by
    have hcomm : p' * p = z * (p * p') := by
      calc p' * p = (p * p' * p⁻¹ * p'⁻¹)⁻¹ * (p * p') := by group
        _ = z * (p * p') := by rw [hpp', inv_eq_of_mul_eq_one_left hz2]
    calc p * p' * (p * p') = p * (p' * p) * p' := by group
      _ = p * (z * (p * p')) * p' := by rw [hcomm]
      _ = p * z * (p * p') * p' := by group
      _ = z * p * (p * p') * p' := by rw [hzc p hpH]
      _ = z * (p * p) * (p' * p') := by group
  have key : ∀ c : G, c ∈ H z →
      (x * c * x⁻¹ * c⁻¹ = 1 ∧ c * c = z) ∨ (x * c * x⁻¹ * c⁻¹ = z ∧ c * c = 1) →
      (x * c * x⁻¹ = c ∧ c * c = z) ∨ (x * c * x⁻¹ = c * z ∧ c * c = 1) := by
    intro c hcH hc
    rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨mul_inv_eq_one.mp h1, h2⟩
    · refine Or.inr ⟨?_, h2⟩
      rw [mul_inv_eq_iff_eq_mul.mp h1]
      exact (hzc c hcH).symm
  have hpp'H : p * p' ∈ H z := (H z).mul_mem hpH hp'H
  have m1 : p ∈ ({p, p', p * p'} : Set G) := by simp
  have m2 : p' ∈ ({p, p', p * p'} : Set G) := by simp
  have m3 : p * p' ∈ ({p, p', p * p'} : Set G) := by simp
  rcases hz_or hxp with ha | ha <;> rcases hz_or hxp' with ha' | ha' <;>
    rcases hz_or (sq_mem_zpowers_z h hp) with hs | hs <;>
    rcases hz_or (sq_mem_zpowers_z h hp') with hs' | hs'
  all_goals
    have hα := hmul
    rw [ha, ha'] at hα
    have hβ := hsq
    rw [hs, hs'] at hβ
    simp only [one_mul, mul_one, hz2] at hα hβ
    first
      | exact ⟨p, m1, key p hpH (Or.inl ⟨ha, hs⟩)⟩
      | exact ⟨p, m1, key p hpH (Or.inr ⟨ha, hs⟩)⟩
      | exact ⟨p', m2, key p' hp'H (Or.inl ⟨ha', hs'⟩)⟩
      | exact ⟨p', m2, key p' hp'H (Or.inr ⟨ha', hs'⟩)⟩
      | exact ⟨p * p', m3, key _ hpp'H (Or.inl ⟨hα, hβ⟩)⟩
      | exact ⟨p * p', m3, key _ hpp'H (Or.inr ⟨hα, hβ⟩)⟩

private theorem commutator_eq_z (h : Tim79a.ParrottHyp z) {a b : G} (ha : a ∈ J z)
    (hb : b ∈ J z) (hab : a * b ≠ b * a) : a * b * a⁻¹ * b⁻¹ = z := by
  have hc := commutator_mem_zpowers_z h ha hb
  rw [commutatorElement_def] at hc
  rcases (Subgroup.mem_zpowers_iff_of_orderOf_eq_two h.1).mp hc with h1 | h1
  · exact absurd (by
      calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
        _ = b * a := by rw [h1, one_mul]) hab
  · exact h1

private theorem mul_inv_mem_centerIn_of_pi_eq {a b : J z}
    (hab : QuotientV.pi z a = QuotientV.pi z b) : (a : G) * (b : G)⁻¹ ∈ centerIn (J z) := by
  have hker : a * b⁻¹ ∈ (QuotientV.pi z).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hab, mul_inv_cancel]
  rw [QuotientV.pi_ker] at hker
  exact Subgroup.mem_subgroupOf.mp hker

omit [Finite G] in
private theorem exists_K_of_pauli (h : Tim79a.ParrottHyp z) {x i X Y : G} (hiJ : i ∈ J z)
    (hXJ : X ∈ J z) (hYJ : Y ∈ J z) (hix : i * x = x * i) (hXx : X * x = x * X)
    (hYx : Y * x = x * Y) (hii : i * i = z) (hXX : X * X = 1) (hYY : Y * Y = 1)
    (hiX : i * X = X * i) (hiY : i * Y = Y * i) (hXY : X * Y * X⁻¹ * Y⁻¹ = z) :
    ∃ K : Subgroup (J z), K.map (J z).subtype ≤ Subgroup.centralizer ({x} : Set G) ∧
      Nonempty (↥K ≃* CFSG.Quasithin.Z4StarQ8Model) := by
  have hz2 : z * z = 1 := by rw [← sq, ← h.1]; exact pow_orderOf_eq_one z
  have hz1 : z ≠ 1 := by
    intro h1
    have := h.1
    rw [h1, orderOf_one] at this
    omega
  have hi4 : (⟨i, hiJ⟩ : ↥(J z)) ^ 4 = 1 := Subtype.ext (by
    have e : i ^ 4 = (i * i) * (i * i) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    simpa [e, hii] using hz2)
  have hX2 : (⟨X, hXJ⟩ : ↥(J z)) ^ 2 = 1 := Subtype.ext (by simpa [sq] using hXX)
  have hY2 : (⟨Y, hYJ⟩ : ↥(J z)) ^ 2 = 1 := Subtype.ext (by simpa [sq] using hYY)
  have hiX' : (⟨i, hiJ⟩ : ↥(J z)) * ⟨X, hXJ⟩ = ⟨X, hXJ⟩ * ⟨i, hiJ⟩ := Subtype.ext hiX
  have hiY' : (⟨i, hiJ⟩ : ↥(J z)) * ⟨Y, hYJ⟩ = ⟨Y, hYJ⟩ * ⟨i, hiJ⟩ := Subtype.ext hiY
  have hYX : Y * X = i ^ 2 * X * Y := by
    rw [sq, hii]
    calc Y * X = (X * Y * X⁻¹ * Y⁻¹)⁻¹ * (X * Y) := by group
      _ = z * X * Y := by rw [hXY, inv_eq_of_mul_eq_one_left hz2, mul_assoc]
  have hYX' : (⟨Y, hYJ⟩ : ↥(J z)) * ⟨X, hXJ⟩ = ⟨i, hiJ⟩ ^ 2 * ⟨X, hXJ⟩ * ⟨Y, hYJ⟩ :=
    Subtype.ext (by simpa using hYX)
  have hi2 : (⟨i, hiJ⟩ : ↥(J z)) ^ 2 ≠ 1 := by
    intro e
    apply hz1
    have e' := congrArg Subtype.val e
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at e'
    rw [← hii, ← sq]
    exact e'
  have hS : (A1Section2Local.pauliHom hi4 hX2 hY2 hiX' hiY' hYX').range ≤
      (Subgroup.centralizer ({x} : Set G)).subgroupOf (J z) :=
    A1Section2Local.range_pauliHom_le hi4 hX2 hY2 hiX' hiY' hYX'
      (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hix))
      (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hXx))
      (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hYx))
  refine ⟨(A1Section2Local.pauliHom hi4 hX2 hY2 hiX' hiY' hYX').range, ?_,
    ⟨(MonoidHom.ofInjective
      (A1Section2Local.pauliHom_injective hi4 hX2 hY2 hiX' hiY' hYX' hi2)).symm⟩⟩
  rintro _ ⟨k, hk, rfl⟩
  exact Subgroup.mem_subgroupOf.mp (hS hk)

private theorem mem_H_of_cosetJ {t : ↥(H z)} {x : G} (hx : cosetJ (z := z) t x) : x ∈ H z := by
  obtain ⟨j, hj, rfl⟩ := hx
  exact (H z).mul_mem t.2 (J_le_H hj)

variable [hN : ((J z).subgroupOf (H z)).Normal]
variable (D : QuotientData (z := z) hN)

private theorem sigma1Commutator_le_J (h : Tim79a.ParrottHyp z) :
    sigma1Commutator (z := z) D ≤ J z :=
  (commutator_le_J1sub (z := z) (D := D) h).trans (J1sub_le_J (z := z) (D := D) h)

private theorem mem_CJcomm_of {y : ↥(H z)} {a : G} (haJ : a ∈ J z)
    (haW : a ∈ sigma1Commutator (z := z) D)
    (hay : a ∈ Subgroup.centralizer ({(y : G)} : Set G)) :
    (⟨a, haJ⟩ : ↥(J z)) ∈ CJcomm (z := z) (D := D) y := by
  rw [CJcomm, Subgroup.mem_inf, mem_centralizerJ_iff, Subgroup.mem_subgroupOf]
  exact ⟨Subgroup.mem_centralizer_singleton_iff.mp hay, haW⟩

theorem conj_mul_inv_mem_zpowers_of_mem_CJ_sigma (h : Tim79a.ParrottHyp z)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hcomm : Commute (sigma1Nine (z := z) D) σ₂)
    (hEq : centralizerJ (sigma1Nine (z := z) D) = centralizerJ σ₂)
    {x : G} (hx : cosetJ (z := z) (tH D * uH D) x) (hx2 : orderOf x = 2)
    {e : G} (heW : e ∈ sigma1Commutator (z := z) D)
    (heσ : e ∈ Subgroup.centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G)) :
    x * e * x⁻¹ * e⁻¹ ∈ Subgroup.zpowers z := by
  have hxH : x ∈ H z := mem_H_of_cosetJ hx
  have heJ : e ∈ J z := sigma1Commutator_le_J D h heW
  set g : ↥(H z) := ⟨x, hxH⟩ with hg
  have hX : conjV h g = conjV h (tH D) * conjV h (uH D) := conjV_eq_tH_mul_uH D h hxH hx
  set T := conjV h (tH D) with hT
  set U := conjV h (uH D) with hU
  set A := conjV h (sigma1Nine (z := z) D) with hA
  set B := conjV h σ₂ with hB
  have hTA : T * A = A * T := conjV_tH_commute_sigma1Nine D h
  have hTB : T * B = B * T := conjV_tH_commute_sigma2 D h hq₂
  have hUA : U * A * U⁻¹ = B := conjV_uH_conj_sigma1Nine D h hq₂
  have hUB : U * B * U⁻¹ = A := conjV_uH_conj_sigma2 D h hq₂
  have hAB : A * B = B * A := by rw [hA, hB, ← map_mul, ← map_mul, hcomm.eq]
  have hτ : conjV h (sigma1Nine (z := z) D * σ₂) = A * B := map_mul _ _ _
  have hσ : conjV h (sigma1Nine (z := z) D * σ₂⁻¹) = A * B⁻¹ := by rw [map_mul, map_inv]
  have hg2 : conjV h g * conjV h g = 1 := by
    have hgg : g * g = 1 := Subtype.ext (by
      change x * x = 1
      rw [← sq, ← hx2]
      exact pow_orderOf_eq_one x)
    rw [← map_mul, hgg, map_one]
  have hgτ : conjV h g * conjV h (sigma1Nine (z := z) D * σ₂) =
      conjV h (sigma1Nine (z := z) D * σ₂) * conjV h g := by
    rw [hX, hτ]
    calc T * U * (A * B) = T * (U * A * U⁻¹) * (U * B * U⁻¹) * U := by group
      _ = T * B * A * U := by rw [hUA, hUB]
      _ = T * A * B * U := by rw [mul_assoc T B A, ← hAB, ← mul_assoc]
      _ = A * (T * B) * U := by rw [hTA]; group
      _ = A * B * (T * U) := by rw [hTB]; group
  have hS_T : A * B⁻¹ * T = T * (A * B⁻¹) := by
    have hTB' : T * B⁻¹ = B⁻¹ * T := (show Commute T B from hTB).inv_right.eq
    calc A * B⁻¹ * T = A * (B⁻¹ * T) := mul_assoc _ _ _
      _ = A * (T * B⁻¹) := by rw [hTB']
      _ = A * T * B⁻¹ := (mul_assoc _ _ _).symm
      _ = T * A * B⁻¹ := by rw [hTA]
      _ = T * (A * B⁻¹) := mul_assoc _ _ _
  have hUS : U * (A * B⁻¹) = (A * B⁻¹)⁻¹ * U := by
    calc U * (A * B⁻¹) = (U * A * U⁻¹) * (U * B * U⁻¹)⁻¹ * U := by group
      _ = B * A⁻¹ * U := by rw [hUA, hUB]
      _ = (A * B⁻¹)⁻¹ * U := by group
  have hSXS : A * B⁻¹ * (T * U) * (A * B⁻¹) = T * U := by
    calc A * B⁻¹ * (T * U) * (A * B⁻¹) = (A * B⁻¹ * T) * (U * (A * B⁻¹)) := by group
      _ = (T * (A * B⁻¹)) * ((A * B⁻¹)⁻¹ * U) := by rw [hS_T, hUS]
      _ = T * U := by group
  have hgQ : ∀ v ∈ QbarW D h σ₂, conjV h g v ∈ QbarW D h σ₂ := by
    intro v hv
    rw [QbarW, Subgroup.mem_inf, mem_autFixedSubgroup] at hv ⊢
    refine ⟨conjV_mem_Wsub D h hσ₂ hq₂ hcomm hEq g hv.1, ?_⟩
    have hv2 : (A * B⁻¹) v = v := by rw [← hσ]; exact hv.2
    rw [hσ, hX]
    calc (A * B⁻¹) ((T * U) v) = (A * B⁻¹) ((T * U) ((A * B⁻¹) v)) := by rw [hv2]
      _ = (A * B⁻¹ * (T * U) * (A * B⁻¹)) v := by simp only [MulAut.mul_apply]
      _ = (T * U) v := by rw [hSXS]
  have hvQ : QuotientV.pi z ⟨e, heJ⟩ ∈ QbarW D h σ₂ :=
    (mem_QbarW_iff D h hσ₂ hcomm _).mpr ⟨⟨e, heJ⟩, mem_CJcomm_of D heJ heW heσ, rfl⟩
  have hfix := conjV_eq_self_of_mem_QbarW D h hσ₂ hq₂ hcomm hEq hg2 hgτ hgQ hvQ
  rw [conjV_mk] at hfix
  have hZ := mul_inv_mem_centerIn_of_pi_eq hfix
  rw [conjJ'_apply_coe] at hZ
  have hW : x * e * x⁻¹ * e⁻¹ ∈ sigma1Commutator (z := z) D :=
    (sigma1Commutator (z := z) D).mul_mem
      (commutator_sigma1Nine_conj_mem D h hEq hσ₂ hq₂ hcomm.eq.symm g e heW)
      ((sigma1Commutator (z := z) D).inv_mem heW)
  rw [← sigma1Commutator_inf_centerIn D h]
  exact ⟨hW, hZ⟩

theorem conj_mul_inv_mem_zpowers_of_mem_J0 (h : Tim79a.ParrottHyp z)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hEq : centralizerJ (sigma1Nine (z := z) D) = centralizerJ σ₂)
    {x : G} (hx : cosetJ (z := z) (tH D * uH D) x)
    {c : G} (hc : c ∈ CJ z (sigma1Nine (z := z) D : G)) :
    x * c * x⁻¹ * c⁻¹ ∈ Subgroup.zpowers z := by
  have hcJ : c ∈ J z := (mem_CJ.mp hc).2
  have hδZ : ∀ g ∈ P_H D, ⁅(g : G), c⁆ ∈ centerIn (J z) := by
    intro g hg
    have hv : QuotientV.pi z ⟨c, hcJ⟩ ∈ Fsub (z := z) (sigma1Nine (z := z) D) :=
      Subgroup.mem_map.mpr ⟨⟨c, hcJ⟩, mem_centralizerJ_iff.mpr
        (Subgroup.mem_centralizer_singleton_iff.mp (mem_CJ.mp hc).1), rfl⟩
    have h1 := conjV_eq_self_of_mem_Fsub D h hσ₂ hq₂ hEq hg hv
    rw [conjV_mk] at h1
    have h2 := mul_inv_mem_centerIn_of_pi_eq h1
    rw [conjJ'_apply_coe] at h2
    rw [commutatorElement_def]
    exact h2
  have hZ : ∀ g ∈ P_H D, ∀ a ∈ centerIn (J z), (g : G) * a * (g : G)⁻¹ = a := by
    intro g hg a ha
    have h1 := conjZ_apply_coe g ⟨a, ha⟩
    rw [conjZ_eq_one_of_mem_Q D h g ((mem_P_H_iff D g).mp hg), MulAut.one_apply] at h1
    exact h1.symm
  have hcommZ : ∀ a ∈ centerIn (J z), ∀ b ∈ centerIn (J z), a * b = b * a := fun a ha b hb =>
    Subgroup.mem_centralizer_iff.mp hb.2 a ha.1
  have hδmul : ∀ g₁ ∈ P_H D, ∀ g₂ ∈ P_H D,
      ⁅((g₁ * g₂ : ↥(H z)) : G), c⁆ = ⁅(g₂ : G), c⁆ * ⁅(g₁ : G), c⁆ := by
    intro g₁ hg₁ g₂ hg₂
    have h1 := hZ g₁ hg₁ _ (hδZ g₂ hg₂)
    calc ⁅((g₁ * g₂ : ↥(H z)) : G), c⁆
        = (g₁ : G) * ⁅(g₂ : G), c⁆ * (g₁ : G)⁻¹ * ⁅(g₁ : G), c⁆ := by
          simp only [commutatorElement_def, Subgroup.coe_mul]
          group
      _ = ⁅(g₂ : G), c⁆ * ⁅(g₁ : G), c⁆ := by rw [h1]
  have hδinv : ∀ g ∈ P_H D, ⁅((g⁻¹ : ↥(H z)) : G), c⁆ * ⁅(g : G), c⁆ = 1 := by
    intro g hg
    have h1 := hδmul g hg g⁻¹ ((P_H D).inv_mem hg)
    rw [mul_inv_cancel] at h1
    rw [← h1]
    simp [commutatorElement_def]
  have hu := uH_mem_P_H D
  have hb := betaH_mem_P_H D
  have hub : uH D * betaH D ∈ P_H D := (P_H D).mul_mem hu hb
  have hubu : uH D * betaH D * (uH D)⁻¹ ∈ P_H D := (P_H D).mul_mem hub ((P_H D).inv_mem hu)
  have hcom : uH D * betaH D * (uH D)⁻¹ * (betaH D)⁻¹ ∈ P_H D :=
    (P_H D).mul_mem hubu ((P_H D).inv_mem hb)
  have hδcom : ⁅((uH D * betaH D * (uH D)⁻¹ * (betaH D)⁻¹ : ↥(H z)) : G), c⁆ = 1 := by
    rw [hδmul _ hubu _ ((P_H D).inv_mem hb), hδmul _ hub _ ((P_H D).inv_mem hu),
      hδmul _ hu _ hb]
    have h23 := hcommZ _ (hδZ _ ((P_H D).inv_mem hu)) _ (hδZ _ hb)
    calc ⁅(((betaH D)⁻¹ : ↥(H z)) : G), c⁆ * (⁅(((uH D)⁻¹ : ↥(H z)) : G), c⁆ *
          (⁅((betaH D : ↥(H z)) : G), c⁆ * ⁅((uH D : ↥(H z)) : G), c⁆))
        = ⁅(((betaH D)⁻¹ : ↥(H z)) : G), c⁆ * ((⁅(((uH D)⁻¹ : ↥(H z)) : G), c⁆ *
          ⁅((betaH D : ↥(H z)) : G), c⁆) * ⁅((uH D : ↥(H z)) : G), c⁆) := by
          rw [mul_assoc (⁅(((uH D)⁻¹ : ↥(H z)) : G), c⁆)]
      _ = ⁅(((betaH D)⁻¹ : ↥(H z)) : G), c⁆ * ((⁅((betaH D : ↥(H z)) : G), c⁆ *
          ⁅(((uH D)⁻¹ : ↥(H z)) : G), c⁆) * ⁅((uH D : ↥(H z)) : G), c⁆) := by rw [h23]
      _ = (⁅(((betaH D)⁻¹ : ↥(H z)) : G), c⁆ * ⁅((betaH D : ↥(H z)) : G), c⁆) *
          (⁅(((uH D)⁻¹ : ↥(H z)) : G), c⁆ * ⁅((uH D : ↥(H z)) : G), c⁆) := by group
      _ = 1 := by rw [hδinv _ hb, hδinv _ hu, one_mul]
  obtain ⟨j, hj, hxj⟩ := hx
  have hxH : x ∈ H z := by
    rw [hxj]
    exact (H z).mul_mem (tH D * uH D).2 (J_le_H hj)
  set com : ↥(H z) := uH D * betaH D * (uH D)⁻¹ * (betaH D)⁻¹ with hcom_def
  set gx : ↥(H z) := ⟨x, hxH⟩ with hgx
  have hmodel : u * beta * u⁻¹ * beta⁻¹ = t * u := by
    have hu' : u⁻¹ = u := inv_eq_of_mul_eq_one_left u_sq
    have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_left t_sq
    have h1 : u * beta * u⁻¹ = beta⁻¹ := by
      rw [hu']
      apply eq_inv_of_mul_eq_one_left
      calc u * beta * u * beta = u * (beta * u * beta) := by group
        _ = u * u := by rw [beta_mul_u_mul_beta]
        _ = 1 := u_sq
    calc u * beta * u⁻¹ * beta⁻¹ = beta⁻¹ * beta⁻¹ := by rw [h1]
      _ = (beta * beta)⁻¹ := by group
      _ = (u * t)⁻¹ := by rw [beta_sq]
      _ = t⁻¹ * u⁻¹ := mul_inv_rev u t
      _ = t * u := by rw [hu', ht']
  have hk : com⁻¹ * gx ∈ (J z).subgroupOf (H z) := by
    rw [J_mem_iff D]
    have hjq : qH D (⟨j, J_le_H hj⟩ : ↥(H z)) = 1 :=
      (J_mem_iff D _).mp (Subgroup.mem_subgroupOf.mpr hj)
    have hgx' : gx = (tH D * uH D) * ⟨j, J_le_H hj⟩ := Subtype.ext hxj
    have hq : qH D com = qH D (tH D * uH D) := by
      rw [hcom_def, map_mul, map_mul, map_mul, map_inv, map_inv, qH_uH, qH_betaH, map_mul, qH_tH,
        qH_uH]
      exact Subtype.ext hmodel
    rw [map_mul, map_inv, hq, hgx', map_mul (qH D) (tH D * uH D) ⟨j, J_le_H hj⟩, hjq, mul_one,
      inv_mul_cancel]
  have hkJ : ((com⁻¹ * gx : ↥(H z)) : G) ∈ J z := Subgroup.mem_subgroupOf.mp hk
  have hkP : com⁻¹ * gx ∈ P_H D := J_le_P_H D hk
  have e : gx = com * (com⁻¹ * gx) := by group
  have hxc : ⁅x, c⁆ = ⁅((com⁻¹ * gx : ↥(H z)) : G), c⁆ := by
    calc ⁅x, c⁆ = ⁅((com * (com⁻¹ * gx) : ↥(H z)) : G), c⁆ :=
          congrArg (fun g : ↥(H z) => ⁅(g : G), c⁆) e
      _ = ⁅((com⁻¹ * gx : ↥(H z)) : G), c⁆ * ⁅(com : G), c⁆ := hδmul _ hcom _ hkP
      _ = ⁅((com⁻¹ * gx : ↥(H z)) : G), c⁆ := by rw [hδcom, mul_one]
  rw [← commutatorElement_def, hxc]
  exact commutator_mem_zpowers_z h hkJ hcJ

theorem exists_z4StarQ8_le_centralizer_of_mem_tuJ
    (h : Tim79a.ParrottHyp z)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hcomm : Commute (sigma1Nine (z := z) D) σ₂)
    (hEq : centralizerJ (sigma1Nine (z := z) D) = centralizerJ σ₂)
    {x : G} (hx : cosetJ (z := z) (tH D * uH D) x) (hx2 : orderOf x = 2) :
    ∃ K : Subgroup (J z), K.map (J z).subtype ≤ Subgroup.centralizer ({x} : Set G) ∧
      Nonempty (↥K ≃* CFSG.Quasithin.Z4StarQ8Model) := by
  have hz2 : z * z = 1 := by rw [← sq, ← h.1]; exact pow_orderOf_eq_one z
  have hzc : ∀ g ∈ H z, g * z = z * g := fun g hg =>
    Subgroup.mem_centralizer_singleton_iff.mp hg
  have hxH : x ∈ H z := mem_H_of_cosetJ hx
  have hWJ := sigma1Commutator_le_J D h
  obtain ⟨r, hrW, hrτ, hrr, hxr⟩ :=
    exists_mem_R_sq_eq_z_conj_eq_mul_z D h hσ₂ hq₂ hcomm hEq hx hx2
  have hrJ : r ∈ J z := hWJ hrW
  obtain ⟨e, he, f, hf, hef⟩ :=
    exists_not_commute_of_mem_CJ_mul_inv_inf_commutator D h hσ₂ hq₂ hcomm hEq
  obtain ⟨heσ, heJ⟩ := mem_CJ.mp he.1
  obtain ⟨hfσ, hfJ⟩ := mem_CJ.mp hf.1
  have heW : e ∈ sigma1Commutator (z := z) D := he.2
  have hfW : f ∈ sigma1Commutator (z := z) D := hf.2
  obtain ⟨p, hp, p', hp', hpp'⟩ := exists_not_commute_CJ_sigma1Nine D h
  have hpJ := (mem_CJ.mp hp).2
  have hp'J := (mem_CJ.mp hp').2
  obtain ⟨c, hcmem, hcx⟩ := exists_mem_triple_conj_eq_and_sq h hxH hpJ hp'J
    (commutator_eq_z h hpJ hp'J hpp') (conj_mul_inv_mem_zpowers_of_mem_J0 D h hσ₂ hq₂ hEq hx hp)
    (conj_mul_inv_mem_zpowers_of_mem_J0 D h hσ₂ hq₂ hEq hx hp')
  have hc : c ∈ CJ z (sigma1Nine (z := z) D : G) := by
    rcases hcmem with rfl | rfl | rfl
    · exact hp
    · exact hp'
    · exact (CJ z _).mul_mem hp hp'
  have hcJ := (mem_CJ.mp hc).2
  have hπr : QuotientV.pi z ⟨r, hrJ⟩ ∈ RbarW D h σ₂ :=
    (mem_RbarW_iff D h hσ₂ hcomm _).mpr ⟨⟨r, hrJ⟩, mem_CJcomm_of D hrJ hrW hrτ, rfl⟩
  have hQR : ∀ a, a ∈ J z → a ∈ sigma1Commutator (z := z) D →
      a ∈ Subgroup.centralizer
        ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G) → r * a = a * r := by
    intro a haJ haW haσ
    have hπa : QuotientV.pi z ⟨a, haJ⟩ ∈ QbarW D h σ₂ :=
      (mem_QbarW_iff D h hσ₂ hcomm _).mpr ⟨⟨a, haJ⟩, mem_CJcomm_of D haJ haW haσ, rfl⟩
    exact ((polarVZMod_pi_eq_zero_iff h _ _).mp
      (polarVZMod_eq_zero_of_mem_QbarW_of_mem_RbarW D h hσ₂ hcomm hπa hπr)).eq.symm
  have hre : r * e = e * r := hQR e heJ heW heσ
  have hrf : r * f = f * r := hQR f hfJ hfW hfσ
  have hce : c * e = e * c := commute_of_mem_CJ_sigma1Nine_of_mem_commutator D h hc heW
  have hcf : c * f = f * c := commute_of_mem_CJ_sigma1Nine_of_mem_commutator D h hc hfW
  have hcr : c * r = r * c := commute_of_mem_CJ_sigma1Nine_of_mem_commutator D h hc hrW
  obtain ⟨i, hiJ, hix, hii, hie, hif, hir⟩ : ∃ i ∈ J z, x * i * x⁻¹ = i ∧ i * i = z ∧
      i * e = e * i ∧ i * f = f * i ∧ i * r = r * i := by
    rcases hcx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨c, hcJ, h1, h2, hce, hcf, hcr⟩
    · refine ⟨c * r, (J z).mul_mem hcJ hrJ, ?_, ?_, ?_, ?_, ?_⟩
      · calc x * (c * r) * x⁻¹ = (x * c * x⁻¹) * (x * r * x⁻¹) := by group
          _ = c * (z * r) * z := by rw [h1, hxr]; group
          _ = c * (r * z) * z := by rw [← hzc r (J_le_H hrJ)]
          _ = c * r * (z * z) := by group
          _ = c * r := by rw [hz2, mul_one]
      · calc c * r * (c * r) = c * (r * c) * r := by group
          _ = c * (c * r) * r := by rw [hcr]
          _ = (c * c) * (r * r) := by group
          _ = z := by rw [h2, hrr, one_mul]
      · exact ((show Commute c e from hce).mul_left (show Commute r e from hre)).eq
      · exact ((show Commute c f from hcf).mul_left (show Commute r f from hrf)).eq
      · exact ((show Commute c r from hcr).mul_left (Commute.refl r)).eq
  have hfixr : ∀ a : G, a ∈ J z → x * a * x⁻¹ * a⁻¹ ∈ Subgroup.zpowers z →
      ∃ a' : G, (a' = a ∨ a' = a * r) ∧ x * a' * x⁻¹ = a' := by
    intro a haJ hxa
    rcases (Subgroup.mem_zpowers_iff_of_orderOf_eq_two h.1).mp hxa with h1 | h1
    · exact ⟨a, Or.inl rfl, mul_inv_eq_one.mp h1⟩
    · refine ⟨a * r, Or.inr rfl, ?_⟩
      calc x * (a * r) * x⁻¹ = (x * a * x⁻¹) * (x * r * x⁻¹) := by group
        _ = z * a * (r * z) := by rw [mul_inv_eq_iff_eq_mul.mp h1, hxr]
        _ = a * z * (r * z) := by rw [← hzc a (J_le_H haJ)]
        _ = a * (z * r) * z := by group
        _ = a * (r * z) * z := by rw [← hzc r (J_le_H hrJ)]
        _ = a * r * (z * z) := by group
        _ = a * r := by rw [hz2, mul_one]
  obtain ⟨e₁, he₁, he₁x⟩ := hfixr e heJ
    (conj_mul_inv_mem_zpowers_of_mem_CJ_sigma D h hσ₂ hq₂ hcomm hEq hx hx2 heW heσ)
  obtain ⟨f₁, hf₁, hf₁x⟩ := hfixr f hfJ
    (conj_mul_inv_mem_zpowers_of_mem_CJ_sigma D h hσ₂ hq₂ hcomm hEq hx hx2 hfW hfσ)
  have hJr : ∀ a : G, a ∈ J z → ∀ a' : G, (a' = a ∨ a' = a * r) → a' ∈ J z := by
    rintro a haJ a' (rfl | rfl)
    · exact haJ
    · exact (J z).mul_mem haJ hrJ
  have hir' : ∀ a : G, i * a = a * i → ∀ a' : G, (a' = a ∨ a' = a * r) → i * a' = a' * i := by
    rintro a hia a' (rfl | rfl)
    · exact hia
    · exact ((show Commute i a from hia).mul_right (show Commute i r from hir)).eq
  have he₁J := hJr e heJ e₁ he₁
  have hf₁J := hJr f hfJ f₁ hf₁
  have hie₁ := hir' e hie e₁ he₁
  have hif₁ := hir' f hif f₁ hf₁
  have hef₁ : e₁ * f₁ * e₁⁻¹ * f₁⁻¹ = z :=
    (commutator_eq_of_mul hre hrf he₁ hf₁).trans (commutator_eq_z h heJ hfJ hef)
  have hinvol : ∀ a : G, a ∈ J z → i * a = a * i →
      ∃ a' : G, (a' = a ∨ a' = a * i) ∧ a' * a' = 1 := by
    intro a haJ hia
    rcases (Subgroup.mem_zpowers_iff_of_orderOf_eq_two h.1).mp (sq_mem_zpowers_z h haJ) with
      h1 | h1
    · exact ⟨a, Or.inl rfl, h1⟩
    · refine ⟨a * i, Or.inr rfl, ?_⟩
      calc a * i * (a * i) = a * (i * a) * i := by group
        _ = a * (a * i) * i := by rw [hia]
        _ = (a * a) * (i * i) := by group
        _ = 1 := by rw [h1, hii, hz2]
  obtain ⟨X, hX, hXX⟩ := hinvol e₁ he₁J hie₁
  obtain ⟨Y, hY, hYY⟩ := hinvol f₁ hf₁J hif₁
  have hfixmul : ∀ a b : G, x * a * x⁻¹ = a → x * b * x⁻¹ = b → x * (a * b) * x⁻¹ = a * b :=
    fun a b ha hb => by
      rw [show x * (a * b) * x⁻¹ = (x * a * x⁻¹) * (x * b * x⁻¹) by group, ha, hb]
  have hcomx : ∀ a : G, x * a * x⁻¹ = a → a * x = x * a := fun a ha =>
    (mul_inv_eq_iff_eq_mul.mp ha).symm
  have hiP : ∀ a : G, a ∈ J z → x * a * x⁻¹ = a → i * a = a * i →
      ∀ a' : G, (a' = a ∨ a' = a * i) →
        a' ∈ J z ∧ x * a' * x⁻¹ = a' ∧ i * a' = a' * i := by
    rintro a haJ hxa hia a' (rfl | rfl)
    · exact ⟨haJ, hxa, hia⟩
    · exact ⟨(J z).mul_mem haJ hiJ, hfixmul a i hxa hix,
        ((show Commute i a from hia).mul_right (Commute.refl i)).eq⟩
  obtain ⟨hXJ, hXx, hiX⟩ := hiP e₁ he₁J he₁x hie₁ X hX
  obtain ⟨hYJ, hYx, hiY⟩ := hiP f₁ hf₁J hf₁x hif₁ Y hY
  exact exists_K_of_pauli h hiJ hXJ hYJ (hcomx i hix) (hcomx X hXx) (hcomx Y hYx) hii hXX hYY hiX
    hiY ((commutator_eq_of_mul hie₁ hif₁ hX hY).trans hef₁)

theorem no_conj_z_eq_of_mem_tuJ (h : Tim79a.ParrottHyp z)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hcomm : Commute (sigma1Nine (z := z) D) σ₂)
    (hEq : centralizerJ (sigma1Nine (z := z) D) = centralizerJ σ₂)
    (hJ : ∀ j : G, j ∈ J z → orderOf j = 2 → j ≠ z → ∀ g : G, g * z * g⁻¹ ≠ j) :
    ∀ x : G, cosetJ (z := z) (tH D * uH D) x → orderOf x = 2 → ∀ g : G, g * z * g⁻¹ ≠ x :=
  no_conj_z_eq_of_mem_tuJ_of_inputs D h hJ
    (fun _ hx hx2 => exists_z4StarQ8_le_centralizer_of_mem_tuJ D h hσ₂ hq₂ hcomm hEq hx hx2)
    (noZ4Q8InCHutQuot D)

end CFSG.RankThree.GF2n.Parrott
