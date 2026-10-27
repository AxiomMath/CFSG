module

public import CFSG.LocalAnalysis.StandardType.PhanEFlagMovePerm

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Flag

open Module CFSG.ClassicalInvolution.Phan.PhanE

open Classical

variable {K : Type} [Field K] {m : ℕ}

lemma q2cFM_finrank_sup_eq (F P Q : Submodule K (Fin (m + 1) → K)) (hPQ : P ≤ Q) :
    finrank K ↥((F ⊓ Q) ⊔ P) = finrank K ↥(F ⊓ Q) + finrank K P - finrank K ↥(F ⊓ P) := by
  have h : (F ⊓ Q) ⊓ P = F ⊓ P := by rw [inf_assoc, inf_eq_right.mpr hPQ]
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq (F ⊓ Q) P
  rw [h] at hsup
  omega

lemma q2cFM_finrank_inter_line (F P Q M : Submodule K (Fin (m + 1) → K))
    (hPM : P ≤ M) (hMQ : M ≤ Q) (hPQ : P ≤ Q)
    (hMdim : finrank K M = finrank K P + 1) :
    finrank K ↥(F ⊓ M) = finrank K ↥(F ⊓ P) + (if M ≤ (F ⊓ Q) ⊔ P then 1 else 0) := by
  have hinf : (F ⊓ M) ⊓ P = F ⊓ P := by rw [inf_assoc, inf_eq_right.mpr hPM]
  by_cases h : M ≤ (F ⊓ Q) ⊔ P
  · rw [if_pos h]
    have hMeq : M = (F ⊓ M) ⊔ P := by
      apply le_antisymm
      · intro m hm
        obtain ⟨x, hx, p, hp, rfl⟩ := Submodule.mem_sup.mp (h hm)
        have hxM : x ∈ M := by
          have := sub_mem hm (hPM hp)
          simpa using this
        exact Submodule.mem_sup.mpr ⟨x, ⟨hx.1, hxM⟩, p, hp, by abel⟩
      · exact sup_le inf_le_right hPM
    have hdim := Submodule.finrank_sup_add_finrank_inf_eq (F ⊓ M) P
    rw [← hMeq, hinf] at hdim
    omega
  · rw [if_neg h]
    have hlt : (F ⊓ M) ⊔ P < M := by
      refine lt_of_le_of_ne (sup_le inf_le_right hPM) ?_
      intro heq
      exact h (heq ▸ sup_le_sup (inf_le_inf (le_refl F) hMQ) le_rfl)
    have hfinT : finrank K ↥((F ⊓ M) ⊔ P) = finrank K P := by
      have h1 := Submodule.finrank_lt_finrank_of_lt hlt
      have h2 := Submodule.finrank_mono (show P ≤ (F ⊓ M) ⊔ P from le_sup_right)
      omega
    have hdim := Submodule.finrank_sup_add_finrank_inf_eq (F ⊓ M) P
    rw [hfinT, hinf] at hdim
    omega

noncomputable def q2cFM_jump (E : FlagK K (m + 1))
    (P Q M : Submodule K (Fin (m + 1) → K)) : ℕ := by
  classical
  exact if _h : ∃ a, M ≤ (E.E a ⊓ Q) ⊔ P then Nat.find _h else m + 1

lemma q2cFM_jump_spec (E : FlagK K (m + 1))
    (P Q M : Submodule K (Fin (m + 1) → K)) (hMQ : M ≤ Q) (hPQ : P ≤ Q) :
    M ≤ (E.E (q2cFM_jump E P Q M) ⊓ Q) ⊔ P := by
  have hex : ∃ a, M ≤ (E.E a ⊓ Q) ⊔ P := ⟨m + 1, by
    have htop : E.E (m + 1) = ⊤ := E.top (m + 1) le_rfl
    rw [htop, top_inf_eq]
    exact le_trans hMQ le_sup_left⟩
  unfold q2cFM_jump
  rw [dif_pos hex]
  exact Nat.find_spec hex

lemma q2cFM_jump_min' (E : FlagK K (m + 1))
    (P Q M : Submodule K (Fin (m + 1) → K)) (hMQ : M ≤ Q) {a : ℕ}
    (h : M ≤ (E.E a ⊓ Q) ⊔ P) : q2cFM_jump E P Q M ≤ a := by
  have hex : ∃ a, M ≤ (E.E a ⊓ Q) ⊔ P := ⟨a, h⟩
  unfold q2cFM_jump
  rw [dif_pos hex]
  exact Nat.find_min' hex h

lemma q2cFM_jump_le_iff (E : FlagK K (m + 1))
    (P Q M : Submodule K (Fin (m + 1) → K)) (hMQ : M ≤ Q) (hPQ : P ≤ Q) (a : ℕ) :
    M ≤ (E.E a ⊓ Q) ⊔ P ↔ q2cFM_jump E P Q M ≤ a := by
  constructor
  · intro h; exact q2cFM_jump_min' E P Q M hMQ h
  · intro h
    exact le_trans (q2cFM_jump_spec E P Q M hMQ hPQ)
      (sup_le_sup (inf_le_inf (E.mono h) le_rfl) le_rfl)

lemma q2cFM_finrank_jump (E : FlagK K (m + 1))
    (P Q M : Submodule K (Fin (m + 1) → K)) (hPM : P ≤ M) (hMQ : M ≤ Q) (hPQ : P ≤ Q)
    (hMdim : finrank K M = finrank K P + 1) (a : ℕ) :
    finrank K ↥(E.E a ⊓ M) =
      finrank K ↥(E.E a ⊓ P) + (if q2cFM_jump E P Q M ≤ a then 1 else 0) := by
  rw [q2cFM_finrank_inter_line (E.E a) P Q M hPM hMQ hPQ hMdim]
  by_cases h : M ≤ (E.E a ⊓ Q) ⊔ P
  · rw [if_pos h, if_pos ((q2cFM_jump_le_iff E P Q M hMQ hPQ a).mp h)]
  · rw [if_neg h, if_neg (fun hj => h ((q2cFM_jump_le_iff E P Q M hMQ hPQ a).mpr hj))]

lemma q2cFM_jump_mem (E : FlagK K (m + 1))
    (P Q M : Submodule K (Fin (m + 1) → K)) (hPM : P ≤ M) (hMQ : M ≤ Q) (hPQ : P ≤ Q)
    (hQdim : finrank K Q = finrank K P + 2)
    (hMdim : finrank K M = finrank K P + 1) {u v : ℕ} (huv : u ≠ v)
    (hs : ∀ a, a ≤ m + 1 → finrank K ↥((E.E a ⊓ Q) ⊔ P) =
      finrank K P + ((if u < a then 1 else 0) + (if v < a then 1 else 0)))
    (ha₂ : max u v + 1 ≤ m + 1) :
    q2cFM_jump E P Q M = min u v + 1 ∨ q2cFM_jump E P Q M = max u v + 1 := by
  set a₁ := min u v + 1 with ha₁
  set a₂ := max u v + 1 with ha₂'
  have hminmax : min u v < max u v := min_lt_max.mpr huv
  have ha₁a₂ : a₁ ≤ a₂ := by omega
  have ha₁m : a₁ ≤ m + 1 := le_trans ha₁a₂ ha₂
  have hs₁ : finrank K ↥((E.E a₁ ⊓ Q) ⊔ P) = finrank K P + 1 := by
    rw [hs a₁ ha₁m, q2cFM_ind_sum_one (u := u) (v := v) (a := a₁) (by omega) (by omega)]
  have hSa₂ : (E.E a₂ ⊓ Q) ⊔ P = Q := by
    apply Submodule.eq_of_le_of_finrank_eq (sup_le inf_le_right hPQ)
    rw [hs a₂ ha₂, q2cFM_ind_sum_two (u := u) (v := v) (a := a₂) (by omega), hQdim]
  have hS_const : ∀ a, a₁ ≤ a → a ≤ max u v →
      (E.E a ⊓ Q) ⊔ P = (E.E a₁ ⊓ Q) ⊔ P := by
    intro a ha₁a haa
    have ham : a ≤ m + 1 := by omega
    have hle : (E.E a₁ ⊓ Q) ⊔ P ≤ (E.E a ⊓ Q) ⊔ P :=
      sup_le_sup (inf_le_inf (E.mono ha₁a) le_rfl) le_rfl
    exact (Submodule.eq_of_le_of_finrank_eq hle (by
      rw [hs a₁ ha₁m, hs a ham,
        q2cFM_ind_sum_one (u := u) (v := v) (a := a₁) (by omega) (by omega),
        q2cFM_ind_sum_one (u := u) (v := v) (a := a) (by omega) (by omega)])).symm
  by_cases hM : M ≤ (E.E a₁ ⊓ Q) ⊔ P
  · left
    apply le_antisymm
    · exact q2cFM_jump_min' E P Q M hMQ hM
    · by_contra hlt
      rw [not_le] at hlt
      have hspec := q2cFM_jump_spec E P Q M hMQ hPQ
      have hdim : finrank K ↥((E.E (q2cFM_jump E P Q M) ⊓ Q) ⊔ P) = finrank K P := by
        rw [hs (q2cFM_jump E P Q M) (by omega),
          q2cFM_ind_sum_zero (u := u) (v := v) (a := q2cFM_jump E P Q M) (by omega), add_zero]
      have := Submodule.finrank_mono hspec
      rw [hdim] at this
      omega
  · right
    apply le_antisymm
    · refine q2cFM_jump_min' E P Q M hMQ ?_
      rw [hSa₂]; exact hMQ
    · by_contra hlt
      rw [not_le] at hlt
      have hspec := q2cFM_jump_spec E P Q M hMQ hPQ
      by_cases hj1 : q2cFM_jump E P Q M < a₁
      · have hdim : finrank K ↥((E.E (q2cFM_jump E P Q M) ⊓ Q) ⊔ P) = finrank K P := by
          rw [hs (q2cFM_jump E P Q M) (by omega),
            q2cFM_ind_sum_zero (u := u) (v := v) (a := q2cFM_jump E P Q M) (by omega), add_zero]
        have := Submodule.finrank_mono hspec
        rw [hdim] at this
        omega
      · rw [hS_const (q2cFM_jump E P Q M) (by omega) (by omega)] at hspec
        exact hM hspec

def q2cFM_replaceFlag (F : FlagK K (m + 1)) (i : Fin m)
    (N : Submodule K (Fin (m + 1) → K)) (hPN : F.E i.val ≤ N)
    (hNQ : N ≤ F.E (i.val + 2)) (hNdim : finrank K N = i.val + 1) : FlagK K (m + 1) where
  E j := if j = i.val + 1 then N else F.E j
  mono := by
    intro j k hjk
    change (if j = i.val + 1 then N else F.E j) ≤ (if k = i.val + 1 then N else F.E k)
    by_cases hj : j = i.val + 1
    · rw [if_pos hj]
      by_cases hk : k = i.val + 1
      · rw [if_pos hk]
      · rw [if_neg hk]
        exact hNQ.trans (F.mono (by omega))
    · rw [if_neg hj]
      by_cases hk : k = i.val + 1
      · rw [if_pos hk]
        exact (F.mono (by omega)).trans hPN
      · rw [if_neg hk]
        exact F.mono hjk
  dim := by
    intro j hj
    by_cases h : j = i.val + 1
    · rw [if_pos h, h]; exact hNdim
    · rw [if_neg h]; exact F.dim j hj
  top := by
    intro j hj
    have h : j ≠ i.val + 1 := by omega
    rw [if_neg h]; exact F.top j hj

lemma q2cFM_replaceFlag_E (F : FlagK K (m + 1)) (i : Fin m)
    (N : Submodule K (Fin (m + 1) → K)) (hPN : F.E i.val ≤ N)
    (hNQ : N ≤ F.E (i.val + 2)) (hNdim : finrank K N = i.val + 1) :
    (q2cFM_replaceFlag F i N hPN hNQ hNdim).E (i.val + 1) = N := by
  show (if i.val + 1 = i.val + 1 then N else F.E (i.val + 1)) = N
  rw [if_pos rfl]

lemma q2cFM_replaceFlag_E_of_ne (F : FlagK K (m + 1)) (i : Fin m)
    (N : Submodule K (Fin (m + 1) → K)) (hPN : F.E i.val ≤ N)
    (hNQ : N ≤ F.E (i.val + 2)) (hNdim : finrank K N = i.val + 1) {j : ℕ}
    (hj : j ≠ i.val + 1) :
    (q2cFM_replaceFlag F i N hPN hNQ hNdim).E j = F.E j := by
  show (if j = i.val + 1 then N else F.E j) = F.E j
  rw [if_neg hj]

lemma q2cFM_replaceFlag_adj (F : FlagK K (m + 1)) (i : Fin m)
    (N : Submodule K (Fin (m + 1) → K)) (hPN : F.E i.val ≤ N)
    (hNQ : N ≤ F.E (i.val + 2)) (hNdim : finrank K N = i.val + 1) :
    (flagSys K m).adj i F (q2cFM_replaceFlag F i N hPN hNQ hNdim) := by
  intro j hj
  exact (q2cFM_replaceFlag_E_of_ne F i N hPN hNQ hNdim hj).symm

lemma q2cFM_huv {i : Fin m} {σ : Equiv.Perm (Fin (m + 1))} :
    (σ⁻¹ i.castSucc).val ≠ (σ⁻¹ i.succ).val := by
  intro heq
  have h2 : i.castSucc = i.succ := σ⁻¹.injective (Fin.ext heq)
  have := congrArg Fin.val h2
  simp only [Fin.val_castSucc, Fin.val_succ] at this
  omega

lemma q2cFM_s_formula {E F : FlagK K (m + 1)} {i : Fin m}
    {σ : Equiv.Perm (Fin (m + 1))} (h : HasPos E F σ) :
    ∀ a, a ≤ m + 1 → finrank K ↥((E.E a ⊓ F.E (i.val + 2)) ⊔ F.E i.val) =
      finrank K ↥(F.E i.val) +
        ((if (σ⁻¹ i.castSucc).val < a then 1 else 0) +
         (if (σ⁻¹ i.succ).val < a then 1 else 0)) := by
  intro a ha
  have hPQ : F.E i.val ≤ F.E (i.val + 2) := F.mono (by omega)
  have hQ := h a (i.val + 2) ha (by omega)
  have hP := h a i.val ha (by omega)
  have hfin := q2cFM_finrank_sup_eq (E.E a) (F.E i.val) (F.E (i.val + 2)) hPQ
  simp only [rk] at hQ hP
  rw [hfin, hQ, hP,
    show permRk σ a (i.val + 2) = permRk σ a (i.val + 1) +
      (if (σ⁻¹ i.succ).val < a then 1 else 0) from q2cFM_permRk_succ σ a i.succ,
    show permRk σ a (i.val + 1) = permRk σ a i.val +
      (if (σ⁻¹ i.castSucc).val < a then 1 else 0) from q2cFM_permRk_succ σ a i.castSucc]
  omega

lemma q2cFM_dim_replace (F F' : FlagK K (m + 1)) (i : Fin m) :
    finrank K ↥(F'.E (i.val + 1)) = finrank K ↥(F.E i.val) + 1 := by
  rw [F'.dim (i.val + 1) (by omega), F.dim i.val (by omega)]

lemma q2cFM_jump_self (E F : FlagK K (m + 1)) {i : Fin m}
    {σ : Equiv.Perm (Fin (m + 1))} (h : HasPos E F σ) :
    q2cFM_jump E (F.E i.val) (F.E (i.val + 2)) (F.E (i.val + 1)) =
      (σ⁻¹ i.castSucc).val + 1 := by
  have hPQ : F.E i.val ≤ F.E (i.val + 2) := F.mono (by omega)
  have hM0Q : F.E (i.val + 1) ≤ F.E (i.val + 2) := F.mono (by omega)
  have hPM0 : F.E i.val ≤ F.E (i.val + 1) := F.mono (by omega)
  have hM0dim : finrank K ↥(F.E (i.val + 1)) = finrank K ↥(F.E i.val) + 1 :=
    q2cFM_dim_replace F F i
  have key : ∀ a, a ≤ m + 1 →
      (if q2cFM_jump E (F.E i.val) (F.E (i.val + 2)) (F.E (i.val + 1)) ≤ a then 1 else 0)
      = (if (σ⁻¹ i.castSucc).val < a then 1 else 0) := by
    intro a ha
    have h1 := q2cFM_finrank_jump E (F.E i.val) (F.E (i.val + 2)) (F.E (i.val + 1))
      hPM0 hM0Q hPQ hM0dim a
    have h2 : finrank K ↥(E.E a ⊓ F.E (i.val + 1)) =
        finrank K ↥(E.E a ⊓ F.E i.val) + (if (σ⁻¹ i.castSucc).val < a then 1 else 0) := by
      have hh := h a (i.val + 1) ha (by omega)
      have hp := h a i.val ha (by omega)
      simp only [rk] at hh hp
      rw [hh, hp, show permRk σ a (i.val + 1) = permRk σ a i.val +
        (if (σ⁻¹ i.castSucc).val < a then 1 else 0) from q2cFM_permRk_succ σ a i.castSucc]
    omega
  have hle : q2cFM_jump E (F.E i.val) (F.E (i.val + 2)) (F.E (i.val + 1))
      ≤ (σ⁻¹ i.castSucc).val + 1 := by
    by_contra hc
    rw [not_le] at hc
    have := key ((σ⁻¹ i.castSucc).val + 1) (by omega)
    rw [if_neg (by omega), if_pos (by omega)] at this
    omega
  have hge : (σ⁻¹ i.castSucc).val + 1
      ≤ q2cFM_jump E (F.E i.val) (F.E (i.val + 2)) (F.E (i.val + 1)) := by
    by_contra hc
    rw [not_le] at hc
    have := key ((σ⁻¹ i.castSucc).val) (by omega)
    rw [if_pos (by omega), if_neg (by omega)] at this
    omega
  omega

lemma q2cFM_hasPos_left {E F F' : FlagK K (m + 1)} {i : Fin m}
    {σ : Equiv.Perm (Fin (m + 1))} (hadj : (flagSys K m).adj i F F') (h : HasPos E F σ)
    (hPM' : F.E i.val ≤ F'.E (i.val + 1)) (hM'Q : F'.E (i.val + 1) ≤ F.E (i.val + 2))
    (hPQ : F.E i.val ≤ F.E (i.val + 2))
    (hM'dim : finrank K ↥(F'.E (i.val + 1)) = finrank K ↥(F.E i.val) + 1)
    (hj : q2cFM_jump E (F.E i.val) (F.E (i.val + 2)) (F'.E (i.val + 1)) =
      (σ⁻¹ i.castSucc).val + 1) :
    HasPos E F' σ := by
  intro a j ha hj'
  by_cases hji : j = i.val + 1
  · subst hji
    have h1 := q2cFM_finrank_jump E (F.E i.val) (F.E (i.val + 2)) (F'.E (i.val + 1))
      hPM' hM'Q hPQ hM'dim a
    have hP' : finrank K ↥(E.E a ⊓ F.E i.val) = permRk σ a i.val := by
      have := h a i.val ha (by omega)
      simpa only [rk] using this
    have hσ' : permRk σ a (i.val + 1) =
        permRk σ a i.val + (if (σ⁻¹ i.castSucc).val < a then 1 else 0) :=
      q2cFM_permRk_succ σ a i.castSucc
    have hstep : (if q2cFM_jump E (F.E i.val) (F.E (i.val + 2)) (F'.E (i.val + 1)) ≤ a
        then 1 else 0) = (if (σ⁻¹ i.castSucc).val < a then 1 else 0) := by
      rw [hj]
      by_cases h : (σ⁻¹ i.castSucc).val < a
      · rw [if_pos (by omega : (σ⁻¹ i.castSucc).val + 1 ≤ a), if_pos h]
      · rw [if_neg (by omega : ¬ (σ⁻¹ i.castSucc).val + 1 ≤ a), if_neg h]
    show rk E F' a (i.val + 1) = permRk σ a (i.val + 1)
    rw [show rk E F' a (i.val + 1) = finrank K ↥(E.E a ⊓ F'.E (i.val + 1)) from rfl,
      h1, hstep, hP', hσ']
  · have heq : F'.E j = F.E j := (hadj j hji).symm
    have hσ : rk E F a j = permRk σ a j := h a j ha hj'
    have hrk : rk E F' a j = rk E F a j := by simp only [rk]; rw [heq]
    show rk E F' a j = permRk σ a j
    rw [hrk, hσ]

lemma q2cFM_hasPos_right {E F F' : FlagK K (m + 1)} {i : Fin m}
    {σ : Equiv.Perm (Fin (m + 1))} (hadj : (flagSys K m).adj i F F') (h : HasPos E F σ)
    (hPM' : F.E i.val ≤ F'.E (i.val + 1)) (hM'Q : F'.E (i.val + 1) ≤ F.E (i.val + 2))
    (hPQ : F.E i.val ≤ F.E (i.val + 2))
    (hM'dim : finrank K ↥(F'.E (i.val + 1)) = finrank K ↥(F.E i.val) + 1)
    (hj : q2cFM_jump E (F.E i.val) (F.E (i.val + 2)) (F'.E (i.val + 1)) =
      (σ⁻¹ i.succ).val + 1) :
    HasPos E F' (adjSwap i * σ) := by
  intro a j ha hj'
  by_cases hji : j = i.val + 1
  · subst hji
    have h1 := q2cFM_finrank_jump E (F.E i.val) (F.E (i.val + 2)) (F'.E (i.val + 1))
      hPM' hM'Q hPQ hM'dim a
    have hP' : finrank K ↥(E.E a ⊓ F.E i.val) = permRk σ a i.val := by
      have := h a i.val ha (by omega)
      simpa only [rk] using this
    have hτ' : permRk (adjSwap i * σ) a (i.val + 1) =
        permRk σ a i.val + (if (σ⁻¹ i.succ).val < a then 1 else 0) :=
      q2cFM_permRk_adjSwap_mul_succ i σ a
    have hstep : (if q2cFM_jump E (F.E i.val) (F.E (i.val + 2)) (F'.E (i.val + 1)) ≤ a
        then 1 else 0) = (if (σ⁻¹ i.succ).val < a then 1 else 0) := by
      rw [hj]
      by_cases h : (σ⁻¹ i.succ).val < a
      · rw [if_pos (by omega : (σ⁻¹ i.succ).val + 1 ≤ a), if_pos h]
      · rw [if_neg (by omega : ¬ (σ⁻¹ i.succ).val + 1 ≤ a), if_neg h]
    show rk E F' a (i.val + 1) = permRk (adjSwap i * σ) a (i.val + 1)
    rw [show rk E F' a (i.val + 1) = finrank K ↥(E.E a ⊓ F'.E (i.val + 1)) from rfl,
      h1, hstep, hP', hτ']
  · have heq : F'.E j = F.E j := (hadj j hji).symm
    have hσ : rk E F a j = permRk σ a j := h a j ha hj'
    have hτσ : permRk (adjSwap i * σ) a j = permRk σ a j :=
      q2cFM_permRk_adjSwap_mul i σ a j hji
    have hrk : rk E F' a j = rk E F a j := by simp only [rk]; rw [heq]
    show rk E F' a j = permRk (adjSwap i * σ) a j
    rw [hrk, hσ, hτσ]

end CFSG.ClassicalInvolution.Phan.PhanE.Flag
