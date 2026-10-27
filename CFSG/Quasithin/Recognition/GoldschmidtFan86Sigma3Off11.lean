module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sigma3Off10
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sigma3Off9

public section

namespace CFSG.Quasithin.Fan86.Sigma3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique.Setup

variable {H : Type*} [Group H] [Finite H] {S : Subgroup H} {x : H}

theorem Hyp3.exists_smallClass (h : Hyp3 H S x) {a : H} (ha : a ∈ S) (haQ : a ∉ oQ H) :
    ∃ t' ∈ smallClass ↥S, (t' : H) ∉ oQ H := by
  by_contra hcon
  push Not at hcon
  have hKSchar : (Subgroup.closure (smallClass ↥S)).Characteristic := smallClass_char
  set K : Subgroup H := (Subgroup.closure (smallClass ↥S)).map S.subtype with hK
  have hKsub : K.subgroupOf S = Subgroup.closure (smallClass ↥S) :=
    Subgroup.comap_map_eq_self_of_injective S.subtype_injective _
  have hKS' : K ≤ S := Subgroup.map_subtype_le _
  have hNK : ∀ n ∈ nQ H x, n ∈ K := fun n hn =>
    ⟨⟨n, nQ_le_S h.sig hn⟩, Subgroup.subset_closure (h.nQ_mem_smallClass ha haQ hn), rfl⟩
  have hKQ : K ≤ oQ H := by
    rintro _ ⟨k, hk, rfl⟩
    have : Subgroup.closure (smallClass ↥S) ≤ (oQ H).subgroupOf S :=
      (Subgroup.closure_le _).2 fun t ht => Subgroup.mem_subgroupOf.2 (hcon t ht)
    exact Subgroup.mem_subgroupOf.1 (this hk)
  have hnorm : K.Normal := by
    refine normal_of_gen (mul_mul_eq_one_of_orderOf h.ord) (h.sig.gen h.ord) K ?_ ?_
    · intro s hs k hk
      have hn : (K.subgroupOf S).Normal := by rw [hKsub]; infer_instance
      have := hn.conj_mem ⟨k, hKS' hk⟩ (Subgroup.mem_subgroupOf.2 hk) ⟨s, hs⟩
      exact Subgroup.mem_subgroupOf.1 this
    · intro k hk
      have hkQ := hKQ hk
      have hc : x * k * x⁻¹ * k⁻¹ ∈ nQ H x := by
        rw [← h.oL_inf_Q]
        exact ⟨comm_mem_oL h.ord k, (oQ H).mul_mem
          ((inferInstance : (oQ H).Normal).conj_mem k hkQ x) ((oQ H).inv_mem hkQ)⟩
      have : x * k * x⁻¹ = (x * k * x⁻¹ * k⁻¹) * k := by group
      rw [this]
      exact K.mul_mem (hNK _ hc) hk
  have hKbot : K = ⊥ := h.no K hKS' (by rw [hKsub]; exact hKSchar) hnorm
  exact h.nQ_ne_bot (le_bot_iff.1 (hKbot ▸ fun n hn => hNK n hn))

theorem Hyp3.exists_t (h : Hyp3 H S x) :
    ∃ t ∈ S, t ∉ oQ H ∧ t * t = 1 ∧ (∀ q ∈ q0Sub H x, t * q = q * t) ∧
      ∃ n ∈ nQ H x, t * n * t⁻¹ ≠ n := by
  obtain ⟨-, a, -, haS, haQ, n₀, hn₀, hne⟩ := h.offender
  have hNn : (nQ H x).Normal := h.sig.nQ_normal h.ord
  obtain ⟨t', ht'c, ht'Q⟩ := h.exists_smallClass haS haQ
  have htS : (t' : H) ∈ S := t'.2
  have ht2 : (t' : H) * t' = 1 := congrArg Subtype.val ht'c.1
  have hmoved : (t' : H) * n₀ * (t' : H)⁻¹ ≠ n₀ := by
    rw [h.conj_nQ haS haQ htS ht'Q hn₀]
    exact hne
  refine ⟨t', htS, ht'Q, ht2, fun q₀ hq₀ => ?_, n₀, hn₀, hmoved⟩
  have hn₀S := nQ_le_S h.sig hn₀
  have hq₀S : q₀ ∈ S := h.sig.Q_le_S (q0Sub_le_Q hq₀)
  rcases ht'c.2 1 ⟨n₀, hn₀S⟩ ⟨q₀, hq₀S⟩ with e | e | e
  · exfalso
    have e' : (t' : H) = n₀ * t' * n₀⁻¹ := by simpa using congrArg Subtype.val e
    apply hmoved
    calc (t' : H) * n₀ * (t' : H)⁻¹ = (n₀ * t' * n₀⁻¹) * n₀ * (t' : H)⁻¹ := by rw [← e']
      _ = n₀ := by group
  · have e' : (t' : H) = q₀ * t' * q₀⁻¹ := by simpa using congrArg Subtype.val e
    calc (t' : H) * q₀ = (q₀ * t' * q₀⁻¹) * q₀ := by rw [← e']
      _ = q₀ * t' := by group
  · exfalso
    apply hmoved
    have e' : n₀ * t' * n₀⁻¹ = q₀ * t' * q₀⁻¹ := by simpa using congrArg Subtype.val e
    have h1 : (q₀⁻¹ * n₀) * t' * (q₀⁻¹ * n₀)⁻¹ = (t' : H) := by
      calc (q₀⁻¹ * n₀) * t' * (q₀⁻¹ * n₀)⁻¹ = q₀⁻¹ * (n₀ * t' * n₀⁻¹) * q₀ := by group
        _ = q₀⁻¹ * (q₀ * t' * q₀⁻¹) * q₀ := by rw [e']
        _ = t' := by group
    have h2 : (q₀⁻¹ * n₀) * t' = (t' : H) * (q₀⁻¹ * n₀) := mul_inv_eq_iff_eq_mul.1 h1
    have hw : (t' : H) * (q₀⁻¹ * n₀) * (t' : H)⁻¹ = q₀⁻¹ * n₀ := by rw [← h2]; group
    have hu0 : (t' : H) * q₀⁻¹ * (t' : H)⁻¹ ∈ q0Sub H x :=
      h.q0_normal.conj_mem q₀⁻¹ ((q0Sub H x).inv_mem hq₀) t'
    have hv0 : (t' : H) * n₀ * (t' : H)⁻¹ ∈ nQ H x := hNn.conj_mem n₀ hn₀ t'
    have huv : ((t' : H) * q₀⁻¹ * (t' : H)⁻¹) * ((t' : H) * n₀ * (t' : H)⁻¹) = q₀⁻¹ * n₀ := by
      rw [← hw]
      group
    have hz : q₀ * ((t' : H) * q₀⁻¹ * (t' : H)⁻¹) = n₀ * ((t' : H) * n₀ * (t' : H)⁻¹)⁻¹ := by
      calc q₀ * ((t' : H) * q₀⁻¹ * (t' : H)⁻¹)
          = q₀ * (((t' : H) * q₀⁻¹ * (t' : H)⁻¹) * ((t' : H) * n₀ * (t' : H)⁻¹)) *
              ((t' : H) * n₀ * (t' : H)⁻¹)⁻¹ := by group
        _ = q₀ * (q₀⁻¹ * n₀) * ((t' : H) * n₀ * (t' : H)⁻¹)⁻¹ := by rw [huv]
        _ = n₀ * ((t' : H) * n₀ * (t' : H)⁻¹)⁻¹ := by group
    have hz1 : q₀ * ((t' : H) * q₀⁻¹ * (t' : H)⁻¹) = 1 :=
      h.nQ_inf_q0 (by rw [hz]; exact (nQ H x).mul_mem hn₀ ((nQ H x).inv_mem hv0))
        ((q0Sub H x).mul_mem hq₀ hu0)
    rw [hz] at hz1
    exact (mul_inv_eq_one.1 hz1).symm

end CFSG.Quasithin.Fan86.Sigma3
