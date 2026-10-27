module

public import CFSG.RankThree.GF2n.BenderStrongWC
public import CFSG.RankThree.GF2n.Tim77Prop24Core
public import CFSG.CGT.Timmesfeld75.Inputs214
public import CFSG.CGT.Timmesfeld75.Cfg214Gen
import CFSG.CGT.Timmesfeld75.Core214Proof
import CFSG.CGT.Timmesfeld75.AschbacherNoPolarDischarge
public import CFSG.CGT.Timmesfeld75.NormalClosure

public section

namespace CFSG.RankThree.GF2n

open CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.GH74.Uniqueness.Bender
open scoped MatrixGroups

variable {X : Type} [Group X]

@[expose] def pairConj (T T₁ : Subgroup X) : Set (Subgroup X) :=
  {U | ∃ g : X, U = conjSubgroup g T ∨ U = conjSubgroup g T₁}

structure QuotPair (T T₁ : Subgroup X) : Prop where
  elem : IsElemAbelian 2 T
  elem₁ : IsElemAbelian 2 T₁
  ne_bot : T ≠ ⊥
  ne_bot₁ : T₁ ≠ ⊥
  ne : T ≠ T₁
  sup : T ⊔ T₁ = ⊤
  closed : ∀ U ∈ pairConj T T₁, ∀ V ∈ pairConj T T₁, ∀ u ∈ U, u ≠ 1 → ∀ v ∈ V, v ≠ 1 →
    u * v = v * u → U = V

namespace QuotPair

variable {T T₁ : Subgroup X} (P : QuotPair T T₁)
include P

omit P in
theorem mem_pairConj_left : T ∈ pairConj T T₁ := ⟨1, Or.inl (conjSubgroup_one T).symm⟩

omit P in
theorem mem_pairConj_right : T₁ ∈ pairConj T T₁ := ⟨1, Or.inr (conjSubgroup_one T₁).symm⟩

omit P in
theorem conj_mem_pairConj {U : Subgroup X} (hU : U ∈ pairConj T T₁) (h : X) :
    conjSubgroup h U ∈ pairConj T T₁ := by
  obtain ⟨g, rfl | rfl⟩ := hU
  · exact ⟨h * g, Or.inl (conjSubgroup_mul h g T).symm⟩
  · exact ⟨h * g, Or.inr (conjSubgroup_mul h g T₁).symm⟩

theorem sq_eq_one {U : Subgroup X} (hU : U ∈ pairConj T T₁) {u : X} (hu : u ∈ U) :
    u * u = 1 := by
  obtain ⟨g, rfl | rfl⟩ := hU
  · have h := P.elem.2 _ (mem_conjSubgroup.mp hu)
    rw [sq] at h
    calc u * u = g * ((g⁻¹ * u * g) * (g⁻¹ * u * g)) * g⁻¹ := by group
      _ = 1 := by rw [h, mul_one, mul_inv_cancel]
  · have h := P.elem₁.2 _ (mem_conjSubgroup.mp hu)
    rw [sq] at h
    calc u * u = g * ((g⁻¹ * u * g) * (g⁻¹ * u * g)) * g⁻¹ := by group
      _ = 1 := by rw [h, mul_one, mul_inv_cancel]

theorem strongWC : StrongWC T := by
  refine ⟨P.elem, fun t ht ht1 a ha g hg => ?_⟩
  by_cases ha1 : g⁻¹ * a * g = 1
  · rw [ha1]
    exact T.one_mem
  have hmem : g⁻¹ * a * g ∈ conjSubgroup g⁻¹ T := by
    rw [mem_conjSubgroup, inv_inv, show g * (g⁻¹ * a * g) * g⁻¹ = a by group]
    exact ha
  rw [Subgroup.mem_centralizer_singleton_iff] at hg
  have := P.closed _ (conj_mem_pairConj mem_pairConj_left g⁻¹) _ mem_pairConj_left _ hmem ha1 t ht
    ht1 hg
  rw [← this]
  exact hmem

variable [Finite X]

theorem eq_one_of_mem_normalizer {s : X} (hs : s ∈ T₁) (hsN : s ∈ Subgroup.normalizer (T : Set X)) :
    s = 1 := by
  by_contra hs1
  obtain ⟨t, ht, ht1, hts⟩ := Tim77.exists_ne_one_commute (U := T) ⟨P.elem.1, P.elem.2⟩ P.ne_bot hsN
    (P.sq_eq_one mem_pairConj_right hs)
  exact P.ne (P.closed _ mem_pairConj_left _ mem_pairConj_right t ht ht1 s hs hs1 hts.symm)

omit [Finite X] in
theorem not_le : ¬ T₁ ≤ T := by
  intro hle
  obtain ⟨⟨s, hs⟩, hs1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp P.ne_bot₁
  have hs1 : s ≠ 1 := fun h => hs1' (Subtype.ext h)
  exact P.ne (P.closed _ mem_pairConj_left _ mem_pairConj_right s (hle hs) hs1 s hs hs1 rfl)

omit [Finite X] in
theorem conj_of_even {t s : X} (ht : t ∈ T) (ht1 : t ≠ 1) (hs : s ∈ T₁) (hs1 : s ≠ 1)
    {m : ℕ} (hm0 : 0 < m) (hm : orderOf (s * t) = 2 * m) :
    ∃ g : X, conjSubgroup g T₁ = T := by
  obtain ⟨z, hzz, hz1, hsz, htz, hconj⟩ := dihedral_central_of_even_order_mem
    (P.sq_eq_one mem_pairConj_right hs) (P.sq_eq_one mem_pairConj_left ht) hm0 hm
  have htz1 : t * z ≠ 1 := fun h => hz1 (by
    have : z = t⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [this, inv_eq_of_mul_eq_one_right (P.sq_eq_one mem_pairConj_left ht)] at hsz
    exact absurd (P.closed _ mem_pairConj_left _ mem_pairConj_right t ht ht1 s hs hs1 hsz.symm)
      P.ne)
  have hcomm : t * (t * z) = (t * z) * t := by
    rw [← mul_assoc, mul_assoc t z t, ← htz, mul_assoc]
  rcases hconj with ⟨g, -, hg⟩ | ⟨g, -, hg⟩
  ·
    refine ⟨g⁻¹, ?_⟩
    have hmem : t * z ∈ conjSubgroup g⁻¹ T₁ := by
      rw [hg, mem_conjSubgroup, inv_inv, show g * (g⁻¹ * s * g) * g⁻¹ = s by group]
      exact hs
    exact (P.closed _ mem_pairConj_left _ (conj_mem_pairConj mem_pairConj_right g⁻¹) t ht ht1
      (t * z) hmem htz1 hcomm).symm
  ·
    exfalso
    have hmem : t * z ∈ conjSubgroup g⁻¹ T := by
      rw [hg, mem_conjSubgroup, inv_inv, show g * (g⁻¹ * t * g) * g⁻¹ = t by group]
      exact ht
    have hT := P.closed _ mem_pairConj_left _ (conj_mem_pairConj mem_pairConj_left g⁻¹) t ht ht1
      (t * z) hmem htz1 hcomm
    have hzT : z ∈ T := by
      have h1 : t * z ∈ T := hT ▸ hmem
      have := T.mul_mem (T.inv_mem ht) h1
      rwa [inv_mul_cancel_left] at this
    exact P.ne (P.closed _ mem_pairConj_left _ mem_pairConj_right z hzT hz1 s hs hs1 hsz.symm)

theorem exists_conj_eq : ∃ x : X, T₁ = conjSubgroup x T := by
  obtain ⟨⟨t, ht⟩, ht1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp P.ne_bot
  have ht1 : t ≠ 1 := fun h => ht1' (Subtype.ext h)
  obtain ⟨⟨s, hs⟩, hs1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp P.ne_bot₁
  have hs1 : s ≠ 1 := fun h => hs1' (Subtype.ext h)
  have htt := P.sq_eq_one mem_pairConj_left ht
  have hss := P.sq_eq_one mem_pairConj_right hs
  rcases Nat.even_or_odd (orderOf (s * t)) with ⟨m, hm⟩ | ⟨k, hk⟩
  · have hm0 : 0 < m := by
      have := orderOf_pos (s * t)
      omega
    obtain ⟨g, hg⟩ := P.conj_of_even ht ht1 hs hs1 hm0 (by omega)
    refine ⟨g⁻¹, ?_⟩
    rw [← hg, ← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]
  ·
    have h1 := inv_pow_mul_mul_pow_of_inverts (left_invol_inverts hss htt) (k + 1)
    have hpow : (s * t) ^ (2 * (k + 1)) = s * t := by
      rw [show 2 * (k + 1) = orderOf (s * t) + 1 by omega, pow_succ, pow_orderOf_eq_one,
        one_mul]
    rw [hpow] at h1
    obtain ⟨d, hd⟩ : ∃ d, d = (s * t) ^ (k + 1) := ⟨_, rfl⟩
    have hconj : d⁻¹ * s * d = t := by
      rw [hd, h1]
      exact (invol_eq_inv_mul_mul htt).symm
    have hmem : t ∈ conjSubgroup d⁻¹ T₁ := by
      rw [mem_conjSubgroup, inv_inv, show d * t * d⁻¹ = s by rw [← hconj]; group]
      exact hs
    have hT := P.closed _ mem_pairConj_left _ (conj_mem_pairConj mem_pairConj_right _) t ht ht1 t
      hmem ht1 rfl
    refine ⟨d, ?_⟩
    rw [hT, ← conjSubgroup_mul, mul_inv_cancel, conjSubgroup_one]

theorem odd_orderOf_mul {t s : X} (ht : t ∈ T) (ht1 : t ≠ 1) (hs : s ∈ T₁) (hs1 : s ≠ 1) :
    Odd (orderOf (t * s)) := by
  have htt := P.sq_eq_one mem_pairConj_left ht
  have hss := P.sq_eq_one mem_pairConj_right hs
  have e : orderOf (t * s) = orderOf (s * t) := by
    rw [show s * t = (t * s)⁻¹ by
      rw [mul_inv_rev, inv_eq_of_mul_eq_one_right htt, inv_eq_of_mul_eq_one_right hss], orderOf_inv]
  rw [e]
  rcases Nat.even_or_odd (orderOf (s * t)) with ⟨m, hm⟩ | hodd
  swap
  · exact hodd
  exfalso
  have hm0 : 0 < m := by
    have := orderOf_pos (s * t)
    omega
  obtain ⟨z, hzz, hz1, hsz, htz, hconj⟩ := dihedral_central_of_even_order_mem hss htt hm0
    (by omega)
  have htz1 : t * z ≠ 1 := fun h => hz1 (by
    have : z = t⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [this, inv_eq_of_mul_eq_one_right htt] at hsz
    exact absurd (P.closed _ mem_pairConj_left _ mem_pairConj_right t ht ht1 s hs hs1 hsz.symm)
      P.ne)
  have hcomm : t * (t * z) = (t * z) * t := by
    rw [← mul_assoc, mul_assoc t z t, ← htz, mul_assoc]
  have hT : t * z ∈ T := by
    rcases hconj with ⟨g, -, hg⟩ | ⟨g, -, hg⟩
    · have hmem : t * z ∈ conjSubgroup g⁻¹ T₁ := by
        rw [hg, mem_conjSubgroup, inv_inv, show g * (g⁻¹ * s * g) * g⁻¹ = s by group]
        exact hs
      have := P.closed _ mem_pairConj_left _ (conj_mem_pairConj mem_pairConj_right g⁻¹) t ht ht1
        (t * z) hmem htz1 hcomm
      exact this ▸ hmem
    · have hmem : t * z ∈ conjSubgroup g⁻¹ T := by
        rw [hg, mem_conjSubgroup, inv_inv, show g * (g⁻¹ * t * g) * g⁻¹ = t by group]
        exact ht
      have := P.closed _ mem_pairConj_left _ (conj_mem_pairConj mem_pairConj_left g⁻¹) t ht ht1
        (t * z) hmem htz1 hcomm
      exact this ▸ hmem
  have hzT : z ∈ T := by
    have := T.mul_mem (T.inv_mem ht) hT
    rwa [inv_mul_cancel_left] at this
  exact P.ne (P.closed _ mem_pairConj_left _ mem_pairConj_right z hzT hz1 s hs hs1 hsz.symm)

theorem models (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput) :
    (∀ K : Subgroup X, K.Normal → IsPGroup 2 K → K = ⊥) ∧
      ((∃ f : ℕ, 2 ≤ f ∧ Nat.card T = 2 ^ f ∧ Nonempty (X ≃* PSL(2, GaloisField 2 f))) ∨
        (∃ a : ℕ, 1 ≤ a ∧ Nat.card T = 2 ^ (2 * a + 1) ∧ Nonempty (X ≃* Sz a)) ∨
        (∃ m : ℕ, Odd m ∧ 3 ≤ m ∧ Nat.card T = 2 ∧ Nonempty (X ≃* DihedralGroup m))) := by
  have hS := P.strongWC
  obtain ⟨x, hx⟩ := P.exists_conj_eq
  have hsup : T ⊔ conjSubgroup x T = ⊤ := hx ▸ P.sup
  have hK : Subgroup.normalClosure (T : Set X) = ⊤ := by
    rw [eq_top_iff, ← hsup]
    exact sup_le Subgroup.le_normalClosure (conjSubgroup_le_normalClosure _ _)
  have hnT : ¬ ∀ g : X, conjSubgroup g T = T := fun h => P.ne (by rw [hx, h])
  rcases lemma25_top aschbacherNoPolarInput_of_repo hS hK with hZ | hB
  · obtain ⟨n, hn, h3, ⟨e⟩⟩ := exists_dihedral_of_zStar P.elem P.elem₁ P.sup hZ P.ne_bot P.not_le
      fun a ha ha1 b hb hb1 => P.odd_orderOf_mul ha ha1 hb hb1
    exact ⟨fun K _ hK2 => eq_bot_of_dihedral hn h3 e K hK2, Or.inr (Or.inr ⟨n, hn, h3,
      card_eq_two_of_dihedral hn e.symm (isPGroup_of_strongWC hS) P.ne_bot, ⟨e.symm⟩⟩)⟩
  · obtain ⟨hO2, hmod⟩ := models_of_isBenderGroup hCen hU hS P.ne_bot hnT hK ⟨x, hsup⟩ hB
    refine ⟨hO2, ?_⟩
    rcases hmod with ⟨f, hf, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩
    · exact Or.inl ⟨f, hf, card_eq_of_strongWC (.linear f hf e) hS P.ne_bot, ⟨e⟩⟩
    · exact Or.inr (Or.inl ⟨a, ha, card_eq_of_strongWC (.suzuki a ha
        (e.trans (MulEquiv.subgroupCongr (szModel_eq_open_sz a).symm))) hS P.ne_bot, ⟨e⟩⟩)

theorem isConj_of_involution (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
    {u v : X} (hu : u * u = 1) (hu1 : u ≠ 1) (hv : v * v = 1) (hv1 : v ≠ 1) : IsConj u v := by
  obtain ⟨-, hmod⟩ := P.models hCen hU
  rcases hmod with ⟨f, hf, -, ⟨e⟩⟩ | ⟨a, ha, -, ⟨e⟩⟩ | ⟨m, hm, -, -, ⟨e⟩⟩
  · exact (BenderType.linear f hf e).lemma_3_4_a hu hu1 hv hv1
  · exact (BenderType.suzuki a ha (e.trans (MulEquiv.subgroupCongr
      (szModel_eq_open_sz a).symm))).lemma_3_4_a hu hu1 hv hv1
  · have h2 : ∀ z, z * z = 1 → z ≠ 1 → orderOf (e z) = 2 := fun z hz hz1 => by
      rw [MulEquiv.orderOf_eq]
      exact orderOf_eq_prime (by rw [sq]; exact hz) hz1
    obtain ⟨c, hc⟩ :=
      isConj_iff.mp (isConj_of_orderOf_eq_two_dihedral hm (h2 u hu hu1) (h2 v hv hv1))
    refine isConj_iff.mpr ⟨e.symm c, e.injective ?_⟩
    simpa [map_mul, map_inv] using hc

theorem exists_normalizer_conj (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
    {t t' : X} (ht : t ∈ T) (ht1 : t ≠ 1) (ht' : t' ∈ T) (ht'1 : t' ≠ 1) :
    ∃ n ∈ Subgroup.normalizer (T : Set X), n * t * n⁻¹ = t' := by
  obtain ⟨c, hc⟩ := isConj_iff.mp (P.isConj_of_involution hCen hU
    (P.sq_eq_one mem_pairConj_left ht) ht1 (P.sq_eq_one mem_pairConj_left ht') ht'1)
  refine ⟨c, ?_, hc⟩
  rw [← conjSubgroup_eq_self_iff]
  refine (P.closed _ (conj_mem_pairConj mem_pairConj_left c) _ mem_pairConj_left t' ?_ ht'1 t'
    ht' ht'1 rfl)
  rw [mem_conjSubgroup, ← hc, show c⁻¹ * (c * t * c⁻¹) * c = t by group]
  exact ht

end QuotPair

end CFSG.RankThree.GF2n
