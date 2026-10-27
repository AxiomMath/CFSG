module

public import Mathlib.GroupTheory.Sylow
public import CFSG.Quasithin.H13.SubgroupCoverFour

public section

namespace CFSG.Quasithin.H13.K1262Two.RuP

open CFSG.Quasithin.H13.Cover

variable {Γ : Type} [Group Γ]

@[expose] def NoBig (R : Subgroup Γ) : Prop :=
  Nat.card R = 2 ^ 13 ∧ ∀ Y : Subgroup Γ, R ≤ Y → Y ≠ ⊤ → ¬ 2 ∣ (R.subgroupOf Y).index →
    9 ∣ Nat.card Y → 5 ∣ Nat.card Y → False

theorem index_mul_card_inf [Finite Γ] (V Y : Subgroup Γ) :
    (V.subgroupOf Y).index * Nat.card ↥(V ⊓ Y) = Nat.card Y :=
  Subgroup.relIndex_mul_card V Y

theorem dvd_index_of_dvd_card [Finite Γ] (Y V : Subgroup Γ) {N q k : ℕ} (hq : q.Prime)
    (hk : q ^ k ∣ Nat.card Y) (hV : Nat.card V ∣ N) (hN : ¬ q ^ k ∣ N) :
    q ∣ (V.subgroupOf Y).index := by
  by_contra hnd
  have hcop : Nat.Coprime (q ^ k) (V.subgroupOf Y).index :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hq).2 hnd)
  rw [← index_mul_card_inf V Y] at hk
  have h2 : q ^ k ∣ Nat.card ↥(V ⊓ Y) := hcop.dvd_of_dvd_mul_left hk
  exact hN (h2.trans ((Subgroup.card_dvd_of_le inf_le_left).trans hV))

theorem le_or_le_of_cover_two {Y V0 V1 : Subgroup Γ} (h : ∀ g ∈ Y, g ∈ V0 ∨ g ∈ V1) :
    Y ≤ V0 ∨ Y ≤ V1 := by
  by_contra hn
  rw [not_or] at hn
  obtain ⟨a, haY, haV0⟩ := SetLike.not_le_iff_exists.mp hn.1
  obtain ⟨b, hbY, hbV1⟩ := SetLike.not_le_iff_exists.mp hn.2
  have haV1 : a ∈ V1 := (h a haY).resolve_left haV0
  have hbV0 : b ∈ V0 := (h b hbY).resolve_right hbV1
  rcases h (a * b) (Y.mul_mem haY hbY) with h0 | h1
  · exact haV0 (by simpa using V0.mul_mem h0 (V0.inv_mem hbV0))
  · exact hbV1 (by simpa using V1.mul_mem (V1.inv_mem haV1) h1)

structure Covers (t1 t2 t3 : Γ) : Prop where
  c100 : NoBig (Subgroup.closure {x | x ∈ [t2, t1 * t2 * t1, t3, t1 * t3 * t1]})
  c010 : NoBig (Subgroup.closure {x | x ∈ [t1, t2 * t1 * t2, t3, t2 * t3 * t2]})
  c001 : NoBig (Subgroup.closure {x | x ∈ [t1, t3 * t1 * t3, t2, t3 * t2 * t3]})
  c110 : NoBig (Subgroup.closure {x | x ∈ [t2 * t1, t3, t1 * t3 * t1]})
  c101 : NoBig (Subgroup.closure {x | x ∈ [t2, t1 * t2 * t1, t3 * t1]})
  c011 : NoBig (Subgroup.closure {x | x ∈ [t1, t2 * t1 * t2, t3 * t2]})
  c111 : NoBig (Subgroup.closure {x | x ∈ [t2 * t1, t3 * t1]})

theorem mul_mem_of_not_mem [Finite Γ] {T S : Subgroup Γ} (hST : S ≤ T)
    (hcard : Nat.card T = 2 * Nat.card S) {a b : Γ} (ha : a ∈ T) (hb : b ∈ T) (ha' : a ∉ S)
    (hb' : b ∉ S) : a * b ∈ S := by
  have hSpos : 0 < Nat.card S := Nat.card_pos
  have hidx : (S.subgroupOf T).index = 2 := by
    have h := Subgroup.relIndex_mul_card S T
    rw [inf_of_le_left hST] at h
    exact Nat.eq_of_mul_eq_mul_right hSpos (h.trans hcard)
  have hmem : (⟨a, ha⟩ : T) * ⟨b, hb⟩ ∈ S.subgroupOf T := by
    rw [Subgroup.mul_mem_iff_of_index_two hidx]
    exact iff_of_false (fun h => ha' h) (fun h => hb' h)
  exact hmem

theorem exists_sub_of_dvd [Finite Γ] (H : Subgroup Γ) (h : 2 ^ 13 ∣ Nat.card H) :
    ∃ K : Subgroup Γ, K ≤ H ∧ Nat.card K = 2 ^ 13 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥H) 2 h
  exact ⟨K.map H.subtype, Subgroup.map_subtype_le K, by
    rw [Subgroup.card_map_of_injective H.subtype_injective]; exact hK⟩

theorem exists_conj_le [Finite Γ] {T K : Subgroup Γ} (hT : IsPGroup 2 T) (hTi : ¬ 2 ∣ T.index)
    (hK : IsPGroup 2 K) : ∃ g : Γ, K.map (MulAut.conj g⁻¹).toMonoidHom ≤ T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hKP⟩ := hK.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Γ (hT.toSylow hTi) P
  have h := congrArg (fun Q : Sylow 2 Γ => (Q : Subgroup Γ)) hg
  rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at h
  refine ⟨g, ?_⟩
  rintro _ ⟨k, hk, rfl⟩
  have hk' : k ∈ T.map (MulAut.conj g).toMonoidHom := by
    have : k ∈ (P : Subgroup Γ) := hKP hk
    rw [← h] at this
    exact this
  obtain ⟨t, ht, hkt⟩ := hk'
  have : (MulAut.conj g⁻¹).toMonoidHom k = t := by
    rw [← hkt]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    group
  rw [this]
  exact ht

theorem noBig_of_sub [Finite Γ] {t1 t2 t3 : Γ} (hC : Covers t1 t2 t3) {T S H : Subgroup Γ}
    (hT : T = Subgroup.closure {x | x ∈ [t1, t2, t3]}) (hTc : Nat.card T = 2 ^ 14)
    (hSc : Nat.card S = 2 ^ 13) (hST : S ≤ T) (hSH : S ≤ H) (hH : H ≠ ⊤)
    (h14 : ¬ 2 ^ 14 ∣ Nat.card H) (h9 : 9 ∣ Nat.card H) (h5 : 5 ∣ Nat.card H) : False := by
  have ht1 : t1 ∈ T := hT ▸ Subgroup.subset_closure (by simp)
  have ht2 : t2 ∈ T := hT ▸ Subgroup.subset_closure (by simp)
  have ht3 : t3 ∈ T := hT ▸ Subgroup.subset_closure (by simp)
  have hSpos : 0 < Nat.card S := Nat.card_pos
  have hcard : Nat.card T = 2 * Nat.card S := by rw [hTc, hSc]; norm_num
  have hodd : ∀ R : Subgroup Γ, Nat.card R = 2 ^ 13 → R ≤ H → ¬ 2 ∣ (R.subgroupOf H).index := by
    intro R hR hRH h2
    have h := index_mul_card_inf R H
    rw [inf_of_le_left hRH, hR] at h
    apply h14
    rw [← h]
    obtain ⟨c, hc⟩ := h2
    exact ⟨c, by rw [hc]; ring⟩
  have hB : ∀ s t : Γ, s ∈ T → t ∈ T → s ∉ S → t ∈ S → s * t * s ∈ S := by
    intro s t hs ht hs' ht'
    have hst : s * t ∉ S := fun h => hs' (by simpa using S.mul_mem h (S.inv_mem ht'))
    exact mul_mem_of_not_mem hST hcard (T.mul_mem hs ht) hs hst hs'
  have hC' : ∀ a b : Γ, a ∈ T → b ∈ T → a ∉ S → b ∉ S → a * b ∈ S := fun a b ha hb ha' hb' =>
    mul_mem_of_not_mem hST hcard ha hb ha' hb'
  have hcl : ∀ L : List Γ, (∀ x ∈ L, x ∈ S) → Subgroup.closure {x | x ∈ L} ≤ H := fun L hL =>
    ((Subgroup.closure_le S).mpr fun x hx => hL x hx).trans hSH
  by_cases a1 : t1 ∈ S <;> by_cases a2 : t2 ∈ S <;> by_cases a3 : t3 ∈ S
  ·
    have hle : T ≤ S := by
      rw [hT, Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with h | h | h <;> rw [h] <;> assumption
    have := Subgroup.card_le_of_le hle
    omega
  ·
    have hle := hcl [t1, t3 * t1 * t3, t2, t3 * t2 * t3] (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with h | h | h | h <;> rw [h]
      · exact a1
      · exact hB _ _ ht3 ht1 a3 a1
      · exact a2
      · exact hB _ _ ht3 ht2 a3 a2)
    exact hC.c001.2 H hle hH (hodd _ hC.c001.1 hle) h9 h5
  ·
    have hle := hcl [t1, t2 * t1 * t2, t3, t2 * t3 * t2] (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with h | h | h | h <;> rw [h]
      · exact a1
      · exact hB _ _ ht2 ht1 a2 a1
      · exact a3
      · exact hB _ _ ht2 ht3 a2 a3)
    exact hC.c010.2 H hle hH (hodd _ hC.c010.1 hle) h9 h5
  ·
    have hle := hcl [t1, t2 * t1 * t2, t3 * t2] (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with h | h | h <;> rw [h]
      · exact a1
      · exact hB _ _ ht2 ht1 a2 a1
      · exact hC' _ _ ht3 ht2 a3 a2)
    exact hC.c011.2 H hle hH (hodd _ hC.c011.1 hle) h9 h5
  ·
    have hle := hcl [t2, t1 * t2 * t1, t3, t1 * t3 * t1] (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with h | h | h | h <;> rw [h]
      · exact a2
      · exact hB _ _ ht1 ht2 a1 a2
      · exact a3
      · exact hB _ _ ht1 ht3 a1 a3)
    exact hC.c100.2 H hle hH (hodd _ hC.c100.1 hle) h9 h5
  ·
    have hle := hcl [t2, t1 * t2 * t1, t3 * t1] (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with h | h | h <;> rw [h]
      · exact a2
      · exact hB _ _ ht1 ht2 a1 a2
      · exact hC' _ _ ht3 ht1 a3 a1)
    exact hC.c101.2 H hle hH (hodd _ hC.c101.1 hle) h9 h5
  ·
    have hle := hcl [t2 * t1, t3, t1 * t3 * t1] (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with h | h | h <;> rw [h]
      · exact hC' _ _ ht2 ht1 a2 a1
      · exact a3
      · exact hB _ _ ht1 ht3 a1 a3)
    exact hC.c110.2 H hle hH (hodd _ hC.c110.1 hle) h9 h5
  ·
    have hle := hcl [t2 * t1, t3 * t1] (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with h | h <;> rw [h]
      · exact hC' _ _ ht2 ht1 a2 a1
      · exact hC' _ _ ht3 ht1 a3 a1)
    exact hC.c111.2 H hle hH (hodd _ hC.c111.1 hle) h9 h5

theorem noBig_of_covers [Finite Γ] {t1 t2 t3 : Γ} (hC : Covers t1 t2 t3) {T : Subgroup Γ}
    (hT : T = Subgroup.closure {x | x ∈ [t1, t2, t3]}) (hTc : Nat.card T = 2 ^ 14)
    (hTi : ¬ 2 ∣ T.index) (H : Subgroup Γ) (hH : H ≠ ⊤) (h13 : 2 ^ 13 ∣ Nat.card H)
    (h14 : ¬ 2 ^ 14 ∣ Nat.card H) (h9 : 9 ∣ Nat.card H) (h5 : 5 ∣ Nat.card H) : False := by
  obtain ⟨K, hKH, hKc⟩ := exists_sub_of_dvd H h13
  obtain ⟨g, hg⟩ := exists_conj_le (IsPGroup.of_card hTc) hTi (IsPGroup.of_card hKc)
  set e : Γ ≃* Γ := MulAut.conj g⁻¹ with he
  have hcH : Nat.card (H.map e.toMonoidHom) = Nat.card H :=
    Subgroup.card_map_of_injective e.injective
  refine noBig_of_sub hC hT hTc (S := K.map e.toMonoidHom) (H := H.map e.toMonoidHom) ?_ hg
    (Subgroup.map_mono hKH) ?_ (by rwa [hcH]) (by rwa [hcH]) (by rwa [hcH])
  · rw [Subgroup.card_map_of_injective e.injective]
    exact hKc
  · intro htop
    apply hH
    refine Subgroup.eq_top_of_card_eq H ?_
    rw [← hcH, htop, Subgroup.card_top]

end CFSG.Quasithin.H13.K1262Two.RuP
