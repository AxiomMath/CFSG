module

public import CFSG.Quasithin.H13.GoldschmidtCTKFamTwoBender

public section

namespace CFSG.Quasithin.H13.CTK

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

theorem exists_commutator_decomp_five : ∀ w : Fin 5 → ZMod 2, (∑ i, w i = 0) →
    ∃ v : Fin 5 → ZMod 2, (∑ i, v i = 0) ∧ ∃ τ : Equiv.Perm (Fin 5), Equiv.Perm.sign τ = 1 ∧
      ∀ i, w i = v i + v (τ⁻¹ i) := by
  decide +kernel

theorem commutator_alt5_eq_top : _root_.commutator (alternatingGroup (Fin 5)) = ⊤ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (_root_.commutator (alternatingGroup (Fin 5))) with h | h
  · exfalso
    apply not_isSolvable_alt5
    apply Group.isSolvable_of_comm
    intro a b
    have : ⁅a, b⁆ ∈ _root_.commutator (alternatingGroup (Fin 5)) :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact this
  · exact h

section Facts

variable {K : Type*} [Group K] {V : Subgroup K}

theorem IsDelta5Ext.exists_coords (h : IsDelta5Ext K V) :
    ∃ (α : K →* alternatingGroup (Fin 5)) (c : ↥V → Fin 5 → ZMod 2),
      Function.Surjective α ∧ α.ker = V ∧ (∀ u u', c (u * u') = c u + c u') ∧ c 1 = 0 ∧
      Function.Injective c ∧ (∀ u, ∑ i, c u i = 0) ∧
      (∀ w : Fin 5 → ZMod 2, (∑ i, w i = 0) → ∃ u, c u = w) ∧
      ∀ (ℓ : K) (u v : ↥V), (v : K) = ℓ * u * ℓ⁻¹ → ∀ i,
        c v i = c u (((α ℓ : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5))⁻¹ i) := by
  obtain ⟨α, hα, hαk, β, hβ, hequiv⟩ := h
  refine ⟨α, fun u i => ((Multiplicative.toAdd (β u) : evenWeight 5) : Fin 5 → ZMod 2) i, hα, hαk,
    ?_, ?_, ?_, ?_, ?_, hequiv⟩
  · intro u u'
    funext i
    simp [map_mul]
  · funext i
    simp
  · intro u u' huu'
    apply hβ.1
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    funext i
    simpa using congrFun huu' i
  · intro u
    exact (Multiplicative.toAdd (β u)).2
  · intro w hw
    obtain ⟨u, hu⟩ := hβ.2 (Multiplicative.ofAdd (⟨w, hw⟩ : evenWeight 5))
    exact ⟨u, by funext i; simp [hu]⟩

theorem IsDelta5Ext.mul_self_eq_one (h : IsDelta5Ext K V) {v : K} (hv : v ∈ V) : v * v = 1 := by
  obtain ⟨-, c, -, -, hmul, hone, hinj, -⟩ := h.exists_coords
  have : (⟨v, hv⟩ : ↥V) * ⟨v, hv⟩ = 1 := by
    apply hinj
    rw [hmul, hone]
    funext i
    simp only [Pi.add_apply, Pi.zero_apply]
    exact CharTwo.add_self_eq_zero _
  simpa using congrArg Subtype.val this

theorem IsDelta5Ext.comm (h : IsDelta5Ext K V) {v w : K} (hv : v ∈ V) (hw : w ∈ V) :
    v * w = w * v := by
  obtain ⟨-, c, -, -, hmul, -, hinj, -⟩ := h.exists_coords
  have : (⟨v, hv⟩ : ↥V) * ⟨w, hw⟩ = ⟨w, hw⟩ * ⟨v, hv⟩ := by
    apply hinj
    rw [hmul, hmul, add_comm]
  simpa using congrArg Subtype.val this

theorem IsDelta5Ext.isPGroup (h : IsDelta5Ext K V) : IsPGroup 2 V := fun v =>
  ⟨1, Subtype.ext (by simpa [pow_one, sq] using h.mul_self_eq_one v.2)⟩

theorem IsDelta5Ext.le_of_normal_pGroup (h : IsDelta5Ext K V) {W : Subgroup K} [W.Normal]
    (hW : IsPGroup 2 W) : W ≤ V := by
  obtain ⟨α, hα, hαk, -⟩ := h
  have hn : (W.map α).Normal := Subgroup.Normal.map inferInstance α hα
  have hW' : IsPGroup 2 (W.map α) := hW.map α
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (W.map α) with h0 | h0
  · intro x hx
    rw [← hαk, MonoidHom.mem_ker]
    have : α x ∈ W.map α := Subgroup.mem_map_of_mem α hx
    rwa [h0, Subgroup.mem_bot] at this
  · exfalso
    rw [h0] at hW'
    obtain ⟨k, hk⟩ := hW'.exists_card_eq
    have hcard : Nat.card (↥(⊤ : Subgroup (alternatingGroup (Fin 5)))) = 60 := by
      rw [Subgroup.card_top, Nat.card_eq_fintype_card, card_alternatingGroup]
      decide
    rw [hcard] at hk
    have h3 : 3 ∣ 2 ^ k := by rw [← hk]; norm_num
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)

theorem IsDelta5Ext.commutator_eq_top (h : IsDelta5Ext K V) : _root_.commutator K = ⊤ := by
  obtain ⟨α, c, hα, hαk, hmul, hone, hinj, hsum, hsurj, hequiv⟩ := h.exists_coords
  have hVn : V.Normal := hαk ▸ α.normal_ker
  have hVC : V ≤ _root_.commutator K := by
    intro v hv
    obtain ⟨v', hv', τ, hτ, hw⟩ := exists_commutator_decomp_five (c ⟨v, hv⟩) (hsum _)
    obtain ⟨u', hu'⟩ := hsurj v' hv'
    obtain ⟨t, ht⟩ := hα ⟨τ, Equiv.Perm.mem_alternatingGroup.mpr hτ⟩
    let u1 : ↥V := ⟨t * (u' : K) * t⁻¹, hVn.conj_mem _ u'.2 t⟩
    have hu1 : ∀ i, c u1 i = c u' (τ⁻¹ i) := fun i => by
      have := hequiv t u' u1 rfl i
      simpa [ht] using this
    have hinv : ∀ u : ↥V, c u⁻¹ = c u := by
      intro u
      have h1 : c (u⁻¹ * u) = c u⁻¹ + c u := hmul _ _
      rw [inv_mul_cancel, hone] at h1
      funext i
      have := congrFun h1 i
      simp only [Pi.zero_apply, Pi.add_apply] at this
      exact CharTwo.add_eq_zero.1 this.symm
    have hx : u1 * u'⁻¹ = ⟨v, hv⟩ := by
      apply hinj
      rw [hmul, hinv]
      funext i
      simp only [Pi.add_apply]
      rw [hu1, hw i, hu', add_comm]
    have hv' : v = ⁅t, (u' : K)⁆ := by
      have := congrArg Subtype.val hx
      simpa [u1, commutatorElement_def] using this.symm
    rw [hv', _root_.commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have hmapC : (_root_.commutator K).map α = ⊤ := by
    rw [_root_.commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective α hα,
      ← _root_.commutator_def, commutator_alt5_eq_top]
  rw [eq_top_iff]
  intro k _
  obtain ⟨c0, hc0, hc0k⟩ := Subgroup.mem_map.1 (hmapC ▸ Subgroup.mem_top (α k))
  have hkc : k * c0⁻¹ ∈ V := by
    rw [← hαk, MonoidHom.mem_ker, map_mul, map_inv, hc0k, mul_inv_cancel]
  have : k = (k * c0⁻¹) * c0 := by group
  rw [this]
  exact Subgroup.mul_mem _ (hVC hkc) hc0

end Facts

section Ambient

variable {S : Type*} [Group S] {K V : Subgroup S}

theorem IsDelta5Ext.perfect (h : IsDelta5Ext ↥K (V.subgroupOf K)) : ⁅K, K⁆ = K := by
  have h1 := h.commutator_eq_top
  rw [_root_.commutator_def] at h1
  have h2 := congrArg (Subgroup.map K.subtype) h1
  rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype] at h2
  exact h2

theorem IsDelta5Ext.inf_le {Q : Subgroup S} (h : IsDelta5Ext ↥K (V.subgroupOf K))
    (hKQ : K ≤ Subgroup.normalizer (Q : Set S)) (hQ : IsPGroup 2 Q) : K ⊓ Q ≤ V := by
  have hn : ((K ⊓ Q).subgroupOf K).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left]
    exact fun k hk => Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hk, hKQ hk⟩
  have hW : IsPGroup 2 ((K ⊓ Q).subgroupOf K) :=
    (hQ.to_le (inf_le_right : K ⊓ Q ≤ Q)).of_equiv
      (Subgroup.subgroupOfEquivOfLe (inf_le_left : K ⊓ Q ≤ K)).symm
  have := h.le_of_normal_pGroup hW
  intro x hx
  exact (Subgroup.mem_subgroupOf.1 (this (show (⟨x, hx.1⟩ : ↥K) ∈ (K ⊓ Q).subgroupOf K from hx)))

theorem IsDelta5Ext.comm_of_mem (hVK : V ≤ K) (h : IsDelta5Ext ↥K (V.subgroupOf K)) :
    ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb => by
  have := h.comm (v := ⟨a, hVK ha⟩) (w := ⟨b, hVK hb⟩) ha hb
  exact congrArg Subtype.val this

theorem IsDelta5Ext.isPGroup_of_le (hVK : V ≤ K) (h : IsDelta5Ext ↥K (V.subgroupOf K)) :
    IsPGroup 2 V :=
  h.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hVK)

end Ambient

end CFSG.Quasithin.H13.CTK
