module

public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenFixed
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenFive
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenU

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup

variable {G : Type} [Group G] [Finite G]

theorem Sit813.odd_relIndex_inf_sGrp {V H T A L K : Subgroup G} {i : ℕ}
    (h : Sit813 V H T i A L K) : Odd ((K ⊓ sGrp H T A K).relIndex K) := by
  obtain ⟨hα, hβ⟩ := (Sit813.isSylowIn_sup_iff h).mp h.isSylowIn_sup
  have hcard := Sit813.card_inf_sGrp h
  rw [hα, Subgroup.card_bot, h.card_A_eq_four] at hcard
  have hPK : K ⊓ sGrp H T A K ≤ K := inf_le_left
  have hNK : oTwoMod (cGrp H T) K ≤ K := oTwoMod_le_self
  have hTN : T ⊓ oTwoMod (cGrp H T) K ≤ oTwoMod (cGrp H T) K := inf_le_right
  have e1 : (K ⊓ sGrp H T A K).relIndex K * Nat.card ↥(K ⊓ sGrp H T A K) = Nat.card ↥K := by
    simpa [inf_of_le_left hPK] using
      Subgroup.relIndex_mul_card (H := K ⊓ sGrp H T A K) (K := K)
  have e2 : (T ⊓ oTwoMod (cGrp H T) K).relIndex (oTwoMod (cGrp H T) K) *
      Nat.card ↥(T ⊓ oTwoMod (cGrp H T) K) = Nat.card ↥(oTwoMod (cGrp H T) K) := by
    simpa [inf_of_le_left hTN] using
      Subgroup.relIndex_mul_card (H := T ⊓ oTwoMod (cGrp H T) K) (K := oTwoMod (cGrp H T) K)
  have e3 : (oTwoMod (cGrp H T) K).relIndex K * Nat.card ↥(oTwoMod (cGrp H T) K) =
      Nat.card ↥K := by
    simpa [inf_of_le_left hNK] using
      Subgroup.relIndex_mul_card (H := oTwoMod (cGrp H T) K) (K := K)
  rw [h.kn4] at e3
  have hpos : 0 < Nat.card ↥(T ⊓ oTwoMod (cGrp H T) K) := Nat.card_pos
  have hodd : Odd ((T ⊓ oTwoMod (cGrp H T) K).relIndex (oTwoMod (cGrp H T) K)) := by
    have h2 := hβ.not_dvd_relIndex
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    exact h2
  have hmain : (K ⊓ sGrp H T A K).relIndex K =
      15 * (T ⊓ oTwoMod (cGrp H T) K).relIndex (oTwoMod (cGrp H T) K) := by
    have h1 : (K ⊓ sGrp H T A K).relIndex K * (Nat.card ↥(T ⊓ oTwoMod (cGrp H T) K) * (4 / 1)) =
        (60 * (T ⊓ oTwoMod (cGrp H T) K).relIndex (oTwoMod (cGrp H T) K)) *
          Nat.card ↥(T ⊓ oTwoMod (cGrp H T) K) := by
      rw [← hcard, e1, ← e3, ← e2]
      ring
    have h2 : (K ⊓ sGrp H T A K).relIndex K * 4 =
        60 * (T ⊓ oTwoMod (cGrp H T) K).relIndex (oTwoMod (cGrp H T) K) := by
      have h3 : ((K ⊓ sGrp H T A K).relIndex K * 4) *
          Nat.card ↥(T ⊓ oTwoMod (cGrp H T) K) =
          (60 * (T ⊓ oTwoMod (cGrp H T) K).relIndex (oTwoMod (cGrp H T) K)) *
            Nat.card ↥(T ⊓ oTwoMod (cGrp H T) K) := by
        rw [← h1]
        norm_num
        ring
      exact Nat.eq_of_mul_eq_mul_right hpos h3
    omega
  rw [hmain]
  exact Odd.mul (by decide) hodd

theorem Sit813.fiveData {V H T A L K : Subgroup G} {i : ℕ} (h : Sit813 V H T i A L K) :
    Five.FiveData V K (oTwoMod (cGrp H T) K) T (rGrp H T K) A (uGrp V K) where
  setup := ⟨inf_le_left, h.oTwoMod_le_inf, h.oTwoMod_normal, h.concl813.d_index, h.kn1, h.kn2⟩
  ti := h.isTI_form
  a_card := h.card_A_eq_four
  a_sq := fun a ha => h.isElemAbelian_A.mul_self_eq_one ha
  a_comm := fun a ha b hb => h.isElemAbelian_A.comm ha hb
  a_le_T := h.mem.1
  a_normV := h.a_le_normalizer_V
  a_normK := Sit813.a_le_normalizer h
  r_le_T := Sit813.rGrp_le_T
  r_comm := fun t ht k hk => (Sit813.mem_rGrp_iff.mp ht).2.2 k hk
  inf_le_R := fun x hx hxT => h.mem_rGrp_of_mem_oTwoMod hx hxT
  decomp := fun a ha => h.exists_decomp ha
  alpha := ((Sit813.isSylowIn_sup_iff h).mp h.isSylowIn_sup).1
  u_comm := fun x hx y hy => h.isElemAbelian_uGrp.comm hx hy
  u_sq := fun x hx => h.isElemAbelian_uGrp.mul_self_eq_one hx
  u_normK := le_normalizer_conjClosure V K
  u_normA := h.a_le_normalizer_uGrp
  u_gen := fun k hk v hv => mem_conjClosure hk hv
  u_cent := (Sit813.faithful h).2

theorem Sit813.commutator_sGrp_ne_bot {V H T A L K : Subgroup G} {i : ℕ}
    (h : Sit813 V H T i A L K) : ∃ s ∈ sGrp H T A K, ∃ v ∈ V, s * v ≠ v * s := by
  by_contra hcon
  push Not at hcon
  obtain ⟨v, hvV, hv1, hvfix⟩ := h.exists_fixed_vector (K ⊓ sGrp H T A K) inf_le_left
    h.odd_relIndex_inf_sGrp fun p hp w hw => hcon p (Subgroup.mem_inf.mp hp).2 w hw
  obtain ⟨a, ha, w, hw, hne⟩ := Five.five_conjugates h.fiveData hvV hv1 hvfix
  exact hne (hcon a ((le_sup_right : A ≤ sGrp H T A K) ha) w hw)

theorem Sit813.v1Grp_ne {V H T A L K : Subgroup G} {i : ℕ} (h : Sit813 V H T i A L K) :
    v1Grp V H T A K ≠ V := by
  intro heq
  obtain ⟨s, hs, v, hv, hne⟩ := h.commutator_sGrp_ne_bot
  have hv1 : v ∈ v1Grp V H T A K := by rw [heq]; exact hv
  exact hne (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hv1).2 s hs)

end CFSG.LocalAnalysis.WeakClosure81

end
