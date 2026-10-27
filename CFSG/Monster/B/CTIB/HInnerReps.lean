module

public import CFSG.Monster.B.CTIB.HInnerCensus
public import CFSG.Monster.B.CTIB.Rank2158
public import Certificates.Certificate3011
public import Certificates.Certificate3013
public import Certificates.Certificate3014
public import Certificates.Certificate3017
public import Certificates.Certificate3019
public import Certificates.Certificate3025
public import Certificates.Certificate3026
public import Certificates.Certificate3028
public import Certificates.Certificate3045
public import Certificates.Certificate3048
public import Certificates.Certificate3049
public import Certificates.Certificate3050
public import Certificates.Certificate3051
public import Certificates.Certificate3057
public import Certificates.Certificate3058
public import Certificates.Certificate3060
public import Certificates.Certificate3061
public import Certificates.Certificate3098
public import Certificates.Certificate3099
public import Certificates.Certificate3101
public import Certificates.Certificate3102
public import Certificates.Certificate3103
public import Certificates.Certificate3106
public import Certificates.Certificate3107
public import Certificates.Certificate3108
public import Certificates.Certificate3109
public import Certificates.Certificate16022
public import Certificates.Certificate3027
public import Certificates.Certificate16951

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.CTIB

open MulOpposite CFSG.Blueprint CFSG.Monster.B CFSG.Monster.B.Bin
  CFSG.Monster.B.Short CFSG.Monster.SpinLattice CFSG.Monster.Griess CFSG.Monster.B.TwoA
  CFSG.Monster.B.TwoA.Sp8
open CFSG.Monster.B.CTIB.Native (qmul gArr)

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)
local notation "βr" s => ((betaRow Dyadic.betaS s : MatBˣ) : MatB)

@[expose] def InnerType
    (c : Sbp) (a b : ℕ) (y : Sbp) : Prop :=
  y ∈ Qs ∧ y * c = c * y ∧ y * y = 1 ∧ ((βr y) - 1).rank = a ∧ ((βr (c * y)) - 1).rank = b

theorem InnerType.conj
    {c y : Sbp} {a b : ℕ} (h : InnerType c a b y) {g : Sbp}
    (hg : g ∈ Jbar.op) : InnerType (g⁻¹ * c * g) a b (g⁻¹ * y * g) := by
  obtain ⟨hy, hc, hsq, ha, hb⟩ := h
  exact ⟨(conj_mem_Qs_iff hg).2 hy, (conj_comm_iff g y c).2 hc, (conj_sq_eq_one_iff g y).2 hsq,
    by rw [rank_conj, ha], by rw [conj_mul_conj, rank_conj, hb]⟩

theorem innerRepsOK_parts :
    (∀ f ∈ [2, 4, 32, 16384, 802816], qmul gArr f 1 = qmul gArr 1 f ∧
      innerTy innerTab f = 1 ∧ innerTy innerTab (qmul gArr 1 f) = 2) ∧
    qmul gArr 2 4 = 6 ∧ qmul gArr 4 2 = 6 ∧
    qmul gArr 32 16384 = 16416 ∧ qmul gArr 16384 32 = 16416 ∧
    qmul gArr 32 802816 = 802848 ∧ qmul gArr 802816 32 = 802848 ∧
    qmul gArr 16384 802816 = 786432 ∧ qmul gArr 802816 16384 = 786432 ∧
    qmul gArr 16416 802816 = 786464 ∧
    (∀ p ∈ [6, 16416, 802848, 786432],
      innerTy innerTab p = 2 ∧ innerTy innerTab (qmul gArr 1 p) = 3) ∧
    innerTy innerTab 786464 = 3 ∧ innerTy innerTab (qmul gArr 1 786464) = 3 ∧
    innerTy innerTab (2 ^ 22) = 6 ∧ innerTy innerTab (qmul gArr 1 (2 ^ 22)) = 1 := by
  have h := innerRepsOK_eq_true
  simp only [innerRepsOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, and_assoc] at h
  exact h

theorem innerType_of_codes
    {n : ℕ} (hn : n < 2 ^ 23) (hc : qmul gArr n 1 = qmul gArr 1 n)
    {k l : ℕ} (hk : innerTy innerTab n = k) (hl : innerTy innerTab (qmul gArr 1 n) = l)
    (hk1 : innerTyRank k ≠ 1) (hl1 : innerTyRank l ≠ 1) :
    InnerType (qS 1) (innerTyRank k) (innerTyRank l) (qS n) := by
  obtain ⟨-, -, h2⟩ := innerRank_spec hn
  obtain ⟨-, -, h2'⟩ := innerRank_spec (qmul_lt 1 n)
  rw [hk] at h2
  rw [hl] at h2'
  obtain ⟨hsq, hr⟩ := h2 hk1
  obtain ⟨-, hr'⟩ := h2' hl1
  exact ⟨qS_mem n, by rw [qS_mul, qS_mul, hc], hsq, hr, by rw [qS_mul]; exact hr'⟩

theorem qS_commute
    {a b : ℕ} (h : qmul gArr a b = qmul gArr b a) : Commute (qS a) (qS b) := by
  show qS a * qS b = qS b * qS a
  rw [qS_mul, qS_mul, h]

theorem rootType_q1 :
    ∀ f ∈ [qS 2, qS 4, qS 32, qS 16384, qS 802816],
    InnerType (qS 1) 1860 2048 f := by
  obtain ⟨hf, -⟩ := innerRepsOK_parts
  have key : ∀ n ∈ [2, 4, 32, 16384, 802816], InnerType (qS 1) 1860 2048 (qS n) := by
    intro n hn
    obtain ⟨hc, h1, h2⟩ := hf n hn
    have hlt : n < 2 ^ 23 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
      rcases hn with rfl | rfl | rfl | rfl | rfl <;> norm_num
    exact innerType_of_codes hlt hc h1 h2 (by decide) (by decide)
  intro f hf'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf'
  rcases hf' with rfl | rfl | rfl | rfl | rfl
  · exact key 2 (by simp)
  · exact key 4 (by simp)
  · exact key 32 (by simp)
  · exact key 16384 (by simp)
  · exact key 802816 (by simp)

theorem comm_code_of
    {n : ℕ} (h : qS n * qS 1 = qS 1 * qS n) :
    qmul gArr n 1 = qmul gArr 1 n :=
  qS_injOn (qmul_lt _ _) (qmul_lt _ _) (by rw [← qS_mul, ← qS_mul]; exact h)

theorem comm_mul_of {a b c : Sbp} (ha : a * c = c * a) (hb : b * c = c * b) :
    a * b * c = c * (a * b) := by
  rw [mul_assoc, hb, ← mul_assoc, ha, mul_assoc]

theorem orthType_q1 :
    ∀ p ∈ [qS 2 * qS 4, qS 32 * qS 16384, qS 32 * qS 802816,
    qS 16384 * qS 802816], InnerType (qS 1) 2048 2168 p := by
  obtain ⟨-, h1, -, h3, -, h5, -, h7, -, -, hp, -⟩ := innerRepsOK_parts
  have hr := rootType_q1
  have key : ∀ a ∈ [qS 2, qS 4, qS 32, qS 16384, qS 802816],
      ∀ b ∈ [qS 2, qS 4, qS 32, qS 16384, qS 802816], ∀ n ∈ [6, 16416, 802848, 786432],
      a * b = qS n → InnerType (qS 1) 2048 2168 (a * b) := by
    intro a ha b hb n hn hab
    obtain ⟨h1', h2'⟩ := hp n hn
    have hlt : n < 2 ^ 23 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
      rcases hn with rfl | rfl | rfl | rfl <;> norm_num
    have hc : qS n * qS 1 = qS 1 * qS n := by
      rw [← hab]
      exact comm_mul_of (hr a ha).2.1 (hr b hb).2.1
    rw [hab]
    exact innerType_of_codes hlt (comm_code_of hc) h1' h2' (by decide) (by decide)
  intro p hp'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
  rcases hp' with rfl | rfl | rfl | rfl
  · exact key _ (by simp) _ (by simp) 6 (by simp) (by rw [qS_mul, h1])
  · exact key _ (by simp) _ (by simp) 16416 (by simp) (by rw [qS_mul, h3])
  · exact key _ (by simp) _ (by simp) 802848 (by simp) (by rw [qS_mul, h5])
  · exact key _ (by simp) _ (by simp) 786432 (by simp) (by rw [qS_mul, h7])

theorem xType_q1 :
    InnerType (qS 1) 2048 1860 xs := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, h12, h13⟩ := innerRepsOK_parts
  have hc : qmul gArr (2 ^ 22) 1 = qmul gArr 1 (2 ^ 22) := by
    refine comm_code_of ?_
    rw [qS_two_pow_22]
    exact xs_comm (qS_mem 1)
  have h := innerType_of_codes (by norm_num) hc h12 h13 (by decide) (by decide)
  rwa [qS_two_pow_22] at h

theorem y3_eq :
    qS 32 * qS 16384 * qS 802816 = qS 786464 := by
  obtain ⟨-, -, -, h3, -, -, -, -, -, h9, -⟩ := innerRepsOK_parts
  rw [qS_mul, h3, qS_mul, h9]

theorem y3Type_q1 :
    InnerType (qS 1) 2168 2168 (qS 786464) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h10, h11, -⟩ := innerRepsOK_parts
  have hr := rootType_q1
  have hc : qmul gArr 786464 1 = qmul gArr 1 786464 := by
    refine comm_code_of ?_
    rw [← y3_eq]
    exact comm_mul_of (comm_mul_of (hr _ (by simp)).2.1 (hr _ (by simp)).2.1)
      (hr _ (by simp)).2.1
  exact innerType_of_codes (by norm_num) hc h10 h11 (by decide) (by decide)

theorem commute_reps :
    Commute (qS 2) (qS 4) ∧ Commute (qS 32) (qS 16384) ∧ Commute (qS 32) (qS 802816) ∧
      Commute (qS 16384) (qS 802816) := by
  obtain ⟨-, h1, h2, h3, h4, h5, h6, h7, h8, -⟩ := innerRepsOK_parts
  exact ⟨qS_commute (h1.trans h2.symm), qS_commute (h3.trans h4.symm),
    qS_commute (h5.trans h6.symm), qS_commute (h7.trans h8.symm)⟩

theorem coe_sEquiv (u : Sbp) : ((sEquiv u : Shat) : Dfull) = (iotaD u.unop)⁻¹ := rfl

theorem commute_iff_sEquiv (u a : Sbp) :
    u * a = a * u ↔ ((sEquiv u : Shat) : Dfull) * (sEquiv a : Shat) =
      ((sEquiv a : Shat) : Dfull) * (sEquiv u : Shat) := by
  rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, SetLike.coe_eq_coe, ← map_mul, ← map_mul,
    sEquiv.injective.eq_iff]

theorem map_centralizer_labelS_xs :
    (Subgroup.centralizer {labelS} ⊓ Subgroup.centralizer {xs}).map
      (Shat.subtype.comp sEquiv.toMonoidHom) = P1 := by
  have hl : ((sEquiv labelS : Shat) : Dfull) = cQ := by rw [sEquiv_labelS, cS_inv]; rfl
  have hx : ((sEquiv xs : Shat) : Dfull) = xhat := by rw [sEquiv_xs]; rfl
  ext d
  constructor
  · rintro ⟨u, ⟨h1, h2⟩, rfl⟩
    have h1' := Subgroup.mem_centralizer_singleton_iff.1 h1
    have h2' := Subgroup.mem_centralizer_singleton_iff.1 h2
    rw [commute_iff_sEquiv, hl] at h1'
    rw [commute_iff_sEquiv, hx] at h2'
    refine ⟨?_, Subgroup.mem_centralizer_singleton_iff.2 h1'⟩
    rw [← centralizer_xhat]
    exact Subgroup.mem_centralizer_singleton_iff.2 h2'
  · rintro ⟨hJ, hc⟩
    have hJ' : d ∈ Jhat := hJ
    have hc' := Subgroup.mem_centralizer_singleton_iff.1 hc
    refine ⟨sEquiv.symm ⟨d, Jhat_le_Shat hJ'⟩, ⟨?_, ?_⟩, ?_⟩
    · refine Subgroup.mem_centralizer_singleton_iff.2 ?_
      rw [commute_iff_sEquiv, hl, MulEquiv.apply_symm_apply]
      exact hc'
    · refine Subgroup.mem_centralizer_singleton_iff.2 ?_
      rw [commute_iff_sEquiv, hx, MulEquiv.apply_symm_apply]
      rw [← centralizer_xhat] at hJ'
      exact Subgroup.mem_centralizer_singleton_iff.1 hJ'
    · show ((sEquiv (sEquiv.symm ⟨d, Jhat_le_Shat hJ'⟩) : Shat) : Dfull) = d
      rw [MulEquiv.apply_symm_apply]

theorem natCard_centralizer_labelS_xs :
    Nat.card ↥(Subgroup.centralizer {labelS} ⊓ Subgroup.centralizer {xs}) =
      77148607752437760 := by
  rw [← natCard_P1, ← map_centralizer_labelS_xs, Subgroup.card_map_of_injective]
  exact Shat.subtype_injective.comp sEquiv.injective

theorem map_conj_centralizer_xs
    {g : Sbp} (hg : g ∈ Jbar.op) (a : Sbp) :
    (Subgroup.centralizer {a} ⊓ Subgroup.centralizer {xs}).map (MulAut.conj g⁻¹).toMonoidHom =
      Subgroup.centralizer {g⁻¹ * a * g} ⊓ Subgroup.centralizer {xs} := by
  have hconj : ∀ s : Sbp, (MulAut.conj g⁻¹).toMonoidHom s = g⁻¹ * s * g := fun s => by
    simp
  have hx := conj_xs hg
  ext z
  simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff, hconj]
  constructor
  · rintro ⟨s, ⟨h1, h2⟩, rfl⟩
    refine ⟨(conj_comm_iff g s a).2 h1, ?_⟩
    rw [← hx, conj_comm_iff]
    exact h2
  · rintro ⟨h1, h2⟩
    have hz : z = g⁻¹ * (g * z * g⁻¹) * g := by group
    rw [hz] at h1 h2
    rw [← hx, conj_comm_iff] at h2
    exact ⟨g * z * g⁻¹, ⟨(conj_comm_iff g _ a).1 h1, h2⟩, hz.symm⟩

theorem native_inner_involution_representatives :
    (∀ f ∈ [qS 2, qS 4, qS 32, qS 16384, qS 802816], InnerType (qS 1) 1860 2048 f) ∧
    Commute (qS 2) (qS 4) ∧ Commute (qS 32) (qS 16384) ∧ Commute (qS 32) (qS 802816) ∧
    Commute (qS 16384) (qS 802816) ∧
    (∀ p ∈ [qS 2 * qS 4, qS 32 * qS 16384, qS 32 * qS 802816, qS 16384 * qS 802816],
      InnerType (qS 1) 2048 2168 p) ∧
    InnerType (qS 1) 2048 1860 xs ∧
    qS 2 * qS 4 = qS 6 ∧ InnerType (qS 1) 2048 2168 (qS 6) ∧
    qS 32 * qS 16384 * qS 802816 = qS 786464 ∧ InnerType (qS 1) 2168 2168 (qS 786464) ∧
    (Subgroup.centralizer {labelS} ⊓ Subgroup.centralizer {xs}).map
      (Shat.subtype.comp sEquiv.toMonoidHom) = P1 ∧
    Nat.card ↥(Subgroup.centralizer {labelS} ⊓ Subgroup.centralizer {xs}) =
      77148607752437760 ∧
    Nat.card ↥(Subgroup.centralizer {qS 1} ⊓ Subgroup.centralizer {xs}) = 77148607752437760 ∧
    ∃ g ∈ Jbar.op, g⁻¹ * qS 1 * g = labelS ∧ g⁻¹ * xs * g = xs ∧
      (∀ f ∈ [qS 2, qS 4, qS 32, qS 16384, qS 802816],
        InnerType labelS 1860 2048 (g⁻¹ * f * g)) ∧
      Commute (g⁻¹ * qS 2 * g) (g⁻¹ * qS 4 * g) ∧
      Commute (g⁻¹ * qS 32 * g) (g⁻¹ * qS 16384 * g) ∧
      Commute (g⁻¹ * qS 32 * g) (g⁻¹ * qS 802816 * g) ∧
      Commute (g⁻¹ * qS 16384 * g) (g⁻¹ * qS 802816 * g) ∧
      (∀ p ∈ [qS 2 * qS 4, qS 32 * qS 16384, qS 32 * qS 802816, qS 16384 * qS 802816],
        InnerType labelS 2048 2168 (g⁻¹ * p * g)) ∧
      InnerType labelS 2048 1860 xs ∧ InnerType labelS 2168 2168 (g⁻¹ * qS 786464 * g) := by
  obtain ⟨g, hg, hgl⟩ := labelS_mem_jClass
  have hcomm := commute_reps
  have h6 : qS 2 * qS 4 = qS 6 := by
    obtain ⟨-, h1, -⟩ := innerRepsOK_parts
    rw [qS_mul, h1]
  have hconjC : ∀ a b : Sbp, Commute a b → Commute (g⁻¹ * a * g) (g⁻¹ * b * g) :=
    fun a b h => (conj_comm_iff g a b).2 h.eq
  have hcard : Nat.card ↥(Subgroup.centralizer {qS 1} ⊓ Subgroup.centralizer {xs}) =
      77148607752437760 := by
    rw [← natCard_centralizer_labelS_xs, hgl, ← map_conj_centralizer_xs hg,
      Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]
  refine ⟨rootType_q1, hcomm.1, hcomm.2.1, hcomm.2.2.1, hcomm.2.2.2, orthType_q1, xType_q1, h6,
    h6 ▸ orthType_q1 _ (by simp), y3_eq, y3Type_q1, map_centralizer_labelS_xs,
    natCard_centralizer_labelS_xs, hcard, g, hg, hgl.symm, conj_xs hg, ?_, hconjC _ _ hcomm.1,
    hconjC _ _ hcomm.2.1, hconjC _ _ hcomm.2.2.1, hconjC _ _ hcomm.2.2.2, ?_, ?_, ?_⟩
  · intro f hf
    rw [hgl]
    exact (rootType_q1 f hf).conj hg
  · intro p hp
    rw [hgl]
    exact (orthType_q1 p hp).conj hg
  · have h := xType_q1.conj hg
    rwa [← hgl, conj_xs hg] at h
  · rw [hgl]
    exact y3Type_q1.conj hg

end CFSG.Monster.B.CTIB
