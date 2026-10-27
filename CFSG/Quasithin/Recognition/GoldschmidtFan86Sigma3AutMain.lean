module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sigma3AutImage

public section

namespace CFSG.Quasithin.Fan86.Sigma3

open DihedralGroup

variable {H : Type*} [Group H]

def prodSubgroup (V Q0 : Subgroup H) (hc : ∀ a ∈ V, ∀ b ∈ Q0, a * b = b * a) : Subgroup H where
  carrier := {w | ∃ a ∈ V, ∃ b ∈ Q0, w = a * b}
  one_mem' := ⟨1, V.one_mem, 1, Q0.one_mem, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
    refine ⟨a * a', V.mul_mem ha ha', b * b', Q0.mul_mem hb hb', ?_⟩
    have := hc a' ha' b hb
    calc a * b * (a' * b') = a * (b * a') * b' := by group
      _ = a * (a' * b) * b' := by rw [← this]
      _ = a * a' * (b * b') := by group
  inv_mem' := by
    rintro _ ⟨a, ha, b, hb, rfl⟩
    refine ⟨a⁻¹, V.inv_mem ha, b⁻¹, Q0.inv_mem hb, ?_⟩
    have := hc a⁻¹ (V.inv_mem ha) b hb
    calc (a * b)⁻¹ = b⁻¹ * a⁻¹ := by group
      _ = a⁻¹ * b⁻¹ := by
        have h2 := hc a⁻¹ (V.inv_mem ha) b⁻¹ (Q0.inv_mem hb)
        exact h2.symm

theorem exists_mul_of_split {S D Q0 : Subgroup H} (hDS : D ≤ S) (hQS : Q0 ≤ S)
    (hc : ∀ d ∈ D, ∀ q ∈ Q0, d * q = q * d) (hDQ : D ⊓ Q0 = ⊥) (h : D ⊔ Q0 = S)
    (eD : ↥D ≃* DihedralGroup 4) (s : ↥S) : ∃ d ∈ D, ∃ b ∈ Q0, (s : H) = d * b := by
  set e := splitEquiv hDS hQS hc hDQ h eD with he
  have hs : s = e.symm (e s) := (e.symm_apply_apply s).symm
  have h1 : (s : H) = ((eD.symm (e s).1 : ↥D) : H) * (((e s).2 : ↥(Q0.subgroupOf S)) : S) := by
    have := splitEquiv_symm_apply hDS hQS hc hDQ h eD (e s).1 (e s).2
    rw [he] at this ⊢
    conv_lhs => rw [hs]
    simpa using this
  exact ⟨_, (eD.symm (e s).1).2, _, ((e s).2).2, h1⟩

theorem conj_mem_V_S {S V D Q0 : Subgroup H} (hVk : IsKleinFour ↥V) (hVD : V ≤ D) (hDS : D ≤ S)
    (hQS : Q0 ≤ S) (hc : ∀ d ∈ D, ∀ q ∈ Q0, d * q = q * d) (hDQ : D ⊓ Q0 = ⊥)
    (h : D ⊔ Q0 = S) (eD : ↥D ≃* DihedralGroup 4) (s : ↥S) (v : H) (hv : v ∈ V) :
    (s : H) * v * (s : H)⁻¹ ∈ V := by
  obtain ⟨d, hd, b, hb, hsdb⟩ := exists_mul_of_split hDS hQS hc hDQ h eD s
  have hbv : b * v * b⁻¹ = v := by
    have := hc v (hVD hv) b hb
    rw [mul_inv_eq_iff_eq_mul]; exact this.symm
  have : (s : H) * v * (s : H)⁻¹ = d * v * d⁻¹ := by
    rw [hsdb]
    calc d * b * v * (d * b)⁻¹ = d * (b * v * b⁻¹) * d⁻¹ := by group
      _ = d * v * d⁻¹ := by rw [hbv]
  rw [this]
  exact conj_mem_V hVk hVD eD ⟨d, hd⟩ v hv

theorem no_aut_of_s4data [Finite H] {S : Subgroup H} {x : H} (hd : S4Data S x)
    (hx3 : orderOf x = 3) (f : MulAut ↥S) (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2)
    (hfq : orderOf f = q)
    (hno : ∀ K : Subgroup H, K ≤ S → (∀ s : ↥S, (s : H) ∈ K → ((f s : ↥S) : H) ∈ K) →
      K.Normal → K = ⊥) : False := by
  obtain ⟨V, D, Q0, hVk, hVD, hDS, hQS, hc, hDQ, hDQS, ⟨eD⟩, hxQ, hxV⟩ := hd.ex
  have hVS : V ≤ S := hVD.trans hDS
  have hcVQ : ∀ a ∈ V, ∀ b ∈ Q0, a * b = b * a := fun a ha b hb => hc a (hVD ha) b hb
  let fi : ℕ → (↥S →* ↥S) := fun i => MulEquiv.toMonoidHom (f ^ i)
  let WS : Subgroup ↥S := ⨆ i : ℕ, (V.subgroupOf S).map (fi i)
  let W : Subgroup H := WS.map S.subtype
  have hgen : ∀ i, (V.subgroupOf S).map (fi i) ≤ WS := fun i =>
    le_iSup (fun i => (V.subgroupOf S).map (fi i)) i
  have hVW : V ≤ W := by
    intro v hv
    refine ⟨⟨v, hVS hv⟩, hgen 0 ⟨⟨v, hVS hv⟩, hv, by simp [fi]⟩, rfl⟩
  have hWle : W ≤ prodSubgroup V Q0 hcVQ := by
    rintro w ⟨t, ht, rfl⟩
    have : WS ≤ (prodSubgroup V Q0 hcVQ).comap S.subtype := by
      refine iSup_le fun i => ?_
      rintro _ ⟨v, hv, rfl⟩
      obtain ⟨a, b, ha, hb, hab⟩ :=
        image_pow_mem hVk hVD hDS hQS hc hDQ hDQS eD f q hq hq2 hfq i v hv
      exact ⟨a, ha, b, hb, hab⟩
    exact this ht
  have hWSf : ∀ s : ↥S, s ∈ WS → f s ∈ WS := by
    intro s hs
    refine Subgroup.iSup_induction (fun i => (V.subgroupOf S).map (fi i))
      (C := fun t => f t ∈ WS) hs ?_ ?_ ?_
    · intro i t ht
      obtain ⟨v, hv, rfl⟩ := ht
      have : f ((fi i) v) = (fi (i + 1)) v := by simp [fi, pow_succ']
      rw [this]
      exact hgen (i + 1) ⟨v, hv, rfl⟩
    · simp
    · intro a b ha hb
      rw [map_mul]; exact WS.mul_mem ha hb
  have hVSn : (V.subgroupOf S).Normal := ⟨fun n hn g => by
    have := conj_mem_V_S hVk hVD hDS hQS hc hDQ hDQS eD g n hn
    exact Subgroup.mem_subgroupOf.2 (by simpa using this)⟩
  have hmapn : ∀ i, ((V.subgroupOf S).map (fi i)).Normal := fun i =>
    hVSn.map (fi i) (f ^ i).surjective
  have hWSn : WS.Normal := by
    have := hmapn
    exact Subgroup.iSup_normal _
  have hSW : ∀ s ∈ S, ∀ w ∈ W, s * w * s⁻¹ ∈ W := by
    rintro s hs _ ⟨t, ht, rfl⟩
    exact ⟨⟨s, hs⟩ * t * ⟨s, hs⟩⁻¹, hWSn.conj_mem t ht ⟨s, hs⟩, by simp⟩
  have h3 : x * x * x = 1 := by
    have h := (hx3 ▸ pow_orderOf_eq_one x : x ^ 3 = 1)
    rwa [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, pow_two] at h
  have hx2 : x⁻¹ = x * x := by
    rw [inv_eq_iff_mul_eq_one, ← mul_assoc]; exact h3
  have hxW : ∀ w ∈ W, x * w * x⁻¹ ∈ W := by
    intro w hw
    obtain ⟨a, ha, b, hb, rfl⟩ := hWle hw
    have hbW : b ∈ W := by
      have : b = a⁻¹ * (a * b) := by group
      rw [this]; exact W.mul_mem (W.inv_mem (hVW ha)) hw
    have e1 : x * (a * b) * x⁻¹ = (x * a * x⁻¹) * b := by
      have := hxQ b hb
      calc x * (a * b) * x⁻¹ = (x * a * x⁻¹) * (x * b) * x⁻¹ := by group
        _ = (x * a * x⁻¹) * (b * x) * x⁻¹ := by rw [this]
        _ = (x * a * x⁻¹) * b := by group
    rw [e1]
    exact W.mul_mem (hVW (hxV a ha)) hbW
  have hxW' : ∀ w ∈ W, x⁻¹ * w * x ∈ W := by
    intro w hw
    have : x⁻¹ * w * x = x * (x * w * x⁻¹) * x⁻¹ := by
      have hxi : x = (x * x)⁻¹ := by
        rw [eq_comm, inv_eq_iff_mul_eq_one]; exact h3
      calc x⁻¹ * w * x = (x * x) * w * (x * x)⁻¹ := by rw [← hxi, ← hx2]
        _ = x * (x * w * x⁻¹) * x⁻¹ := by group
    rw [this]
    exact hxW _ (hxW w hw)
  have hS_le : S ≤ Subgroup.normalizer (W : Set H) := fun s hs =>
    Subgroup.mem_normalizer_iff.2 fun w =>
    ⟨fun hw => hSW s hs w hw, fun hw => by
      have := hSW s⁻¹ (S.inv_mem hs) _ hw
      have e : s⁻¹ * (s * w * s⁻¹) * s⁻¹⁻¹ = w := by group
      rwa [e] at this⟩
  have hx_le : Subgroup.zpowers x ≤ Subgroup.normalizer (W : Set H) := Subgroup.zpowers_le.2
    (Subgroup.mem_normalizer_iff.2 fun w => ⟨fun hw => hxW w hw, fun hw => by
      have := hxW' _ hw
      have e : x⁻¹ * (x * w * x⁻¹) * x = w := by group
      rwa [e] at this⟩)
  have hnorm : W.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff]
    intro g _
    exact (sup_le hS_le hx_le) (hd.gen ▸ Subgroup.mem_top g)
  have hWbot : W = ⊥ := hno W (Subgroup.map_subtype_le _) (fun s hs => by
    obtain ⟨t, ht, hts⟩ := hs
    have hts' : t = s := Subtype.ext hts
    subst hts'
    exact ⟨f t, hWSf t ht, rfl⟩) hnorm
  have hV0 : V = ⊥ := le_bot_iff.1 (hWbot ▸ hVW)
  have h4 := hVk.card_four
  rw [hV0, Subgroup.card_bot] at h4
  exact absurd h4 (by decide)

end CFSG.Quasithin.Fan86.Sigma3
