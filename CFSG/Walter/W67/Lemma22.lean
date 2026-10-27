module

public import CFSG.Walter.W67.Lemma21

public section

namespace CFSG.Walter.W67

open scoped MatrixGroups Pointwise

variable {G : Type} [Group G] [Finite G]

namespace Frame

variable {h : Hyp G} (fr : Frame h)

theorem exists_not_commute (hidx : ∀ N : Subgroup G, N.Normal → N.index ≠ 2) {z : G}
    (hzS : z ∈ (fr.S : Subgroup G)) (hz1 : z ≠ 1) :
    ∃ n ∈ Subgroup.normalizer ((fr.S : Subgroup G) : Set G), n * z ≠ z * n := by
  by_contra hcon
  push Not at hcon
  obtain ⟨H, hHn, hH⟩ := JT.exists_normal_index_eq_of_commute_normalizer fr.S
    (h.abelian_sylow fr.S) hzS hz1 hcon
  exact hidx H hHn hH

theorem exists_conj_of_mem_S (hidx : ∀ N : Subgroup G, N.Normal → N.index ≠ 2) {x y : G}
    (hx : x ∈ (fr.S : Subgroup G)) (hx1 : x ≠ 1) (hy : y ∈ (fr.S : Subgroup G)) (hy1 : y ≠ 1) :
    ∃ n ∈ Subgroup.normalizer ((fr.S : Subgroup G) : Set G), n * x * n⁻¹ = y := by
  classical
  have hab := h.abelian_sylow fr.S
  set S := fr.S
  set N := Subgroup.normalizer ((S : Subgroup G) : Set G)
  let := JT.conjAct N S le_rfl
  set T : Set (S : Subgroup G) := {z | z ≠ 1}
  have hTcard : T.ncard = 7 := by
    have : T = (Set.univ : Set (S : Subgroup G)) \ {1} := by
      ext
      simp [T]
    rw [this, Set.ncard_sdiff_singleton_of_mem (Set.mem_univ _), Set.ncard_univ, fr.card_S]
  have hTinv : ∀ a : N, ∀ z ∈ T, a • z ∈ T := by
    intro a z hz h1
    apply hz
    have h1' : ((a • z : (S : Subgroup G)) : G) = 1 := congrArg Subtype.val h1
    change (a : G) * z * (a : G)⁻¹ = 1 at h1'
    apply Subtype.ext
    change (z : G) = 1
    have := congrArg (fun w => (a : G)⁻¹ * w * a) h1'
    simpa [mul_assoc] using this
  have horbit : ∀ z ∈ T, MulAction.orbit N z = T := by
    apply JT.orbit_eq_of_ncard_eq_seven T hTcard hTinv
    intro z hz
    rw [← MulAction.index_stabilizer]
    have hle : (S : Subgroup G).subgroupOf N ≤ MulAction.stabilizer N z := by
      intro s hs
      rw [MulAction.mem_stabilizer_iff]
      apply Subtype.ext
      change (s : G) * z * (s : G)⁻¹ = z
      have := congrArg Subtype.val (hab.is_comm.comm ⟨s, hs⟩ z)
      change (s : G) * z = z * s at this
      rw [this, mul_inv_cancel_right]
    refine ⟨?_, ?_⟩
    · have h1 := Subgroup.index_dvd_of_le hle
      have h2 : ((S : Subgroup G).subgroupOf N).index ∣ (S : Subgroup G).index :=
        Subgroup.relIndex_dvd_index_of_le Subgroup.le_normalizer
      rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
      exact fun h3 => S.not_dvd_index (h3.trans (h1.trans h2))
    · intro h1
      rw [Subgroup.index_eq_one] at h1
      obtain ⟨n, hn, hnz⟩ := fr.exists_not_commute hidx z.2 (fun h0 => hz (Subtype.ext h0))
      apply hnz
      have hmem : (⟨n, hn⟩ : N) ∈ MulAction.stabilizer N z := by
        rw [h1]
        exact Subgroup.mem_top _
      have := congrArg Subtype.val (MulAction.mem_stabilizer_iff.mp hmem)
      change n * z * n⁻¹ = z at this
      calc n * z = (n * z * n⁻¹) * n := by group
        _ = z * n := by rw [this]
  have hxT : (⟨x, hx⟩ : (S : Subgroup G)) ∈ T := fun h0 => hx1 (congrArg Subtype.val h0)
  have hyT : (⟨y, hy⟩ : (S : Subgroup G)) ∈ T := fun h0 => hy1 (congrArg Subtype.val h0)
  rw [← horbit _ hxT] at hyT
  obtain ⟨n, hn⟩ := hyT
  exact ⟨n, n.2, congrArg Subtype.val hn⟩

theorem normalizer_S_inf_H :
    Subgroup.normalizer ((fr.S : Subgroup G) : Set G) ⊓ h.H =
      h.H ⊓ Subgroup.normalizer (fr.T : Set G) := by
  apply le_antisymm
  · rintro x ⟨hxN, hxH⟩
    refine ⟨hxH, JT.mem_normalizer_of_conj_mem fun t ht => ?_⟩
    exact ⟨(Subgroup.mem_normalizer_iff.mp hxN t).mp ht.1, h.conj_mem_K hxH ht.2⟩
  · rintro x ⟨hxH, hxN⟩
    refine ⟨JT.mem_normalizer_of_conj_mem fun s hs => ?_, hxH⟩
    rw [← fr.zpowers_J_sup_T] at hs ⊢
    have hTN : Subgroup.zpowers h.J ≤ Subgroup.normalizer (fr.T : Set G) := by
      rw [Subgroup.zpowers_le]
      exact JT.mem_normalizer_of_conj_mem fun y hy => by
        rw [← h.commute_J (h.K_le_H hy.2), mul_inv_cancel_right]
        exact hy
    rw [sup_comm] at hs ⊢
    obtain ⟨t, ht, j, hj, rfl⟩ := (mem_sup_iff_of_le_normalizer hTN).mp hs
    have hj' : x * j * x⁻¹ = j := by
      rcases eq_one_or_eq_of_mem_zpowers h.orderOf_J hj with rfl | rfl
      · group
      · rw [h.commute_J hxH, mul_inv_cancel_right]
    have : x * (t * j) * x⁻¹ = (x * t * x⁻¹) * (x * j * x⁻¹) := by group
    rw [this, hj']
    exact mul_mem (Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp hxN t).mp ht))
      (Subgroup.mem_sup_right hj)

theorem relIndex_normalizer_S_inf_H (hidx : ∀ N : Subgroup G, N.Normal → N.index ≠ 2) :
    (Subgroup.normalizer ((fr.S : Subgroup G) : Set G) ⊓ h.H).relIndex
      (Subgroup.normalizer ((fr.S : Subgroup G) : Set G)) = 7 := by
  classical
  set N := Subgroup.normalizer ((fr.S : Subgroup G) : Set G)
  let := JT.conjAct N fr.S le_rfl
  set J' : (fr.S : Subgroup G) := ⟨h.J, fr.J_mem⟩
  have hstab : MulAction.stabilizer N J' = h.H.subgroupOf N := by
    ext n
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, h.mem_H_iff]
    constructor
    · intro hn
      have := congrArg Subtype.val hn
      change (n : G) * h.J * (n : G)⁻¹ = h.J at this
      calc (n : G) * h.J = ((n : G) * h.J * (n : G)⁻¹) * n := by group
        _ = h.J * n := by rw [this]
    · intro hn
      apply Subtype.ext
      change (n : G) * h.J * (n : G)⁻¹ = h.J
      rw [hn, mul_inv_cancel_right]
  have horbit : MulAction.orbit N J' = {z | z ≠ 1} := by
    ext z
    constructor
    · rintro ⟨n, rfl⟩ h1
      have := congrArg Subtype.val h1
      change (n : G) * h.J * (n : G)⁻¹ = 1 at this
      apply h.J_ne_one
      have := congrArg (fun w => (n : G)⁻¹ * w * n) this
      simpa [mul_assoc] using this
    · intro hz
      obtain ⟨n, hn, hnz⟩ := fr.exists_conj_of_mem_S hidx fr.J_mem h.J_ne_one z.2
        (fun h0 => hz (Subtype.ext h0))
      exact ⟨⟨n, hn⟩, Subtype.ext hnz⟩
  have h7 : (MulAction.orbit N J').ncard = 7 := by
    have : ({z | z ≠ 1} : Set (fr.S : Subgroup G)) =
        (Set.univ : Set (fr.S : Subgroup G)) \ {1} := by
      ext
      simp
    rw [horbit, this, Set.ncard_sdiff_singleton_of_mem (Set.mem_univ _), Set.ncard_univ,
      fr.card_S]
  rw [Subgroup.relIndex, Subgroup.inf_subgroupOf_left, ← hstab, MulAction.index_stabilizer, h7]

theorem index_CS_normalizer_S
    (hidx : ∀ N : Subgroup G, N.Normal → N.index ≠ 2) :
    (fr.CS.subgroupOf (Subgroup.normalizer ((fr.S : Subgroup G) : Set G))).index = 21 := by
  set N := Subgroup.normalizer ((fr.S : Subgroup G) : Set G)
  have hCSN : fr.CS ≤ N ⊓ h.H := by
    rw [fr.normalizer_S_inf_H]
    exact fr.CS_le_normalizer_T
  have hidx3 : (fr.CS.subgroupOf (N ⊓ h.H)).index = 3 := by
    rw [fr.normalizer_S_inf_H]
    exact fr.index_CS_and_normalizer_T.1
  have hmul := Subgroup.relIndex_mul_relIndex fr.CS (N ⊓ h.H) N hCSN inf_le_left
  rw [Subgroup.relIndex, hidx3, fr.relIndex_normalizer_S_inf_H hidx] at hmul
  change (fr.CS.subgroupOf N).index = 21
  rw [← Subgroup.relIndex, ← hmul]

include fr in
theorem exists_conj_eq_J (hidx : ∀ N : Subgroup G, N.Normal → N.index ≠ 2) {x : G}
    (hx : orderOf x = 2) : ∃ g : G, g * x * g⁻¹ = h.J := by
  have hx2 : IsPGroup 2 (Subgroup.zpowers x) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨S', hS'⟩ := hx2.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S' fr.S
  have hgx : g * x * g⁻¹ ∈ (fr.S : Subgroup G) := by
    rw [← hg]
    change g * x * g⁻¹ ∈ MulAut.conj g • (S' : Subgroup G)
    have := Subgroup.smul_mem_pointwise_smul x (MulAut.conj g) (S' : Subgroup G)
      (hS' (Subgroup.mem_zpowers x))
    simpa [MulAut.smul_def, MulAut.conj_apply] using this
  have hgx1 : g * x * g⁻¹ ≠ 1 := by
    intro h1
    have := congrArg (fun w => g⁻¹ * w * g) h1
    simp only [mul_one, inv_mul_cancel, mul_assoc, inv_mul_cancel_left] at this
    rw [this, orderOf_one] at hx
    omega
  obtain ⟨n, -, hn⟩ := fr.exists_conj_of_mem_S hidx hgx hgx1 fr.J_mem h.J_ne_one
  exact ⟨n * g, by rw [← hn]; group⟩

end Frame

theorem lemma_2_2 : S_lemma_2_2 := by
  intro G _ _ h fr hidx
  refine ⟨fr.index_CS_normalizer_S hidx, fun s hs t ht hs2 ht2 => ?_, fun x y hx hy => ?_⟩
  · have hs1 : s ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hs2; omega
    have ht1 : t ≠ 1 := fun h1 => by rw [h1, orderOf_one] at ht2; omega
    exact fr.exists_conj_of_mem_S hidx hs hs1 ht ht1
  · obtain ⟨g, hg⟩ := fr.exists_conj_eq_J hidx hx
    obtain ⟨k, hk⟩ := fr.exists_conj_eq_J hidx hy
    refine isConj_iff.mpr ⟨k⁻¹ * g, ?_⟩
    rw [show k⁻¹ * g * x * (k⁻¹ * g)⁻¹ = k⁻¹ * (g * x * g⁻¹) * k by group, hg, ← hk]
    group

end CFSG.Walter.W67
