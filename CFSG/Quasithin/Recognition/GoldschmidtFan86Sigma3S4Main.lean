module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sigma3S4Sub
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sigma3Off9

public section

namespace CFSG.Quasithin.Fan86.Sigma3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique.Setup

variable {H : Type*} [Group H] [Finite H] {S : Subgroup H} {x : H}

theorem Hyp3.card_Q (h : Hyp3 H S x) : Nat.card (oQ H) = 4 * Nat.card (q0Sub H x) := by
  have : (q0Sub H x).Normal := h.q0_normal
  have hdisj : nQ H x ⊓ q0Sub H x = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    rintro n ⟨hn, hq⟩
    exact h.nQ_inf_q0 hn hq
  have hsup : nQ H x ⊔ q0Sub H x = oQ H := by
    refine le_antisymm (sup_le ((nQ_le x).trans oneCenter_le) q0Sub_le_Q) ?_
    intro q hq
    obtain ⟨n, hn, q₀, hq₀, rfl⟩ := h.decomp hq
    exact Subgroup.mul_mem_sup hn hq₀
  have h1 := card_sup_of_inf_eq_bot (nQ H x) (q0Sub H x) hdisj
  rw [hsup, h.offender.1] at h1
  exact h1

theorem Hyp3.card_eq (h : Hyp3 H S x) : Nat.card H = 24 * Nat.card (q0Sub H x) := by
  have h1 : Nat.card H = 6 * Nat.card (oQ H) := h.sig.card_Q
  have h2 := h.card_Q
  omega

theorem Hyp3.exists_perm4 (h : Hyp3 H S x) {t : H} (htS : t ∈ S) (htQ : t ∉ oQ H)
    (ht2 : t * t = 1) (htc : ∀ q ∈ q0Sub H x, t * q = q * t) :
    ∃ T : Subgroup H, Nonempty (↥T ≃* Equiv.Perm (Fin 4)) ∧
      (∀ s ∈ T, ∀ c ∈ q0Sub H x, s * c = c * s) ∧ T ⊓ q0Sub H x = ⊥ ∧
      T ⊔ q0Sub H x = ⊤ := by
  have hk := h.klein24 htS htQ ht2
  have hcomm : ∀ s ∈ permSub H t, ∀ c ∈ q0Sub H x, s * c = c * s := by
    have hle : permSub H t ≤ Subgroup.centralizer (q0Sub H x : Set H) := by
      refine sup_le ?_ (Subgroup.zpowers_le.2
        (Subgroup.mem_centralizer_iff.2 fun c hc => (htc c hc).symm))
      rw [h.oL_eq]
      refine sup_le (fun n hn => Subgroup.mem_centralizer_iff.2 fun c hc =>
        (nQ_q0_comm hn hc).symm) (Subgroup.zpowers_le.2
        (Subgroup.mem_centralizer_iff.2 fun c hc => (mem_q0Sub.1 hc).2))
    intro s hs c hc
    exact (Subgroup.mem_centralizer_iff.1 (hle hs) c hc).symm
  have hbot : permSub H t ⊓ q0Sub H x = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    rintro m ⟨hmT, hmQ⟩
    have hmc : (⟨m, hmT⟩ : ↥(permSub H t)) ∈ Subgroup.center ↥(permSub H t) := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hcomm g g.2 m hmQ)
    rw [hk.center_eq_bot, Subgroup.mem_bot] at hmc
    exact congrArg Subtype.val hmc
  have htop : permSub H t ⊔ q0Sub H x = ⊤ := by
    have : (q0Sub H x).Normal := h.q0_normal
    apply Subgroup.eq_top_of_card_eq
    rw [card_sup_of_inf_eq_bot _ _ hbot, h.card_permSub htQ ht2, h.card_eq]
  exact ⟨permSub H t, hk.nonempty_perm_four, hcomm, hbot, htop⟩

end CFSG.Quasithin.Fan86.Sigma3
