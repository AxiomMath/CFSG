module

public import CFSG.Quasithin.Background.FLcR2B
public import CFSG.Quasithin.Background.FLcPerf
public import CFSG.Quasithin.Background.FLcR2El

public section

namespace CFSG.Quasithin.FLc

open Matrix CFSG.Quasithin CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LieType.BorelTits CFSG.Open

variable {G : Type} [Group G]

namespace P0Setup

variable {L S UL : Subgroup G} {n : ℕ} {W : ℕ → Subgroup G} (D : P0Setup L S UL n W) [Finite G]

omit [Finite G] in
theorem mem_Ebk [Finite G] {i : ℕ} (hi : 1 ≤ i) (hin : i + 1 < n) {P Q : Fin n}
    (hP : P.val + 1 = i) (hQ : Q.val = i) {x : G} :
    x ∈ D.Ebk hi hin hP hQ ↔ x ∈ parab (L ⊔ S) n W i ∧
      ∃ l : ↥L, Dec L S UL x l ∧ blk P Q (D.α l) = 1 := Iff.rfl

include D

theorem rank2_b (hn : n = 4 ∨ n = 5) :
    ¬ pCoreOf 2 (oTwoUpper (parab (L ⊔ S) n W 2)) ≤ pCoreOf 2 (parab (L ⊔ S) n W 1) := by
  have h3 : 3 ≤ n := D.three_le
  have h2n : 2 + 1 < n := by omega
  obtain ⟨hT1, hT2, hU2, hc1, hc2, hc3, hc4⟩ := node_compute hn h3
  obtain ⟨hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10⟩ := node_blocks hn h3
  have ht : T2 n h3 ∈ Qn n 2 := (Qn n 2).mul_mem (Ut_le_Qn n 2 (tv_mem_Ut _))
    (reflection_mem_Qn (by norm_num) (by omega))
  have hu : E02 n h3 ∈ Ut n := tv_mem_Ut _
  obtain ⟨l, hlY, hlα⟩ := D.exists_comm_lift (j := 2) hT2 hU2 ht hu
  have hαU : D.α l ∈ Ut n ∧ blk (ix 1 (by omega)) (ix 2 (by omega)) (D.α l) = 1 ∧
      blk (ix 0 (by omega)) (ix 1 (by omega)) (D.α l) = tau2 := by
    rcases hlα with h | h
    · rw [h, hc1]
      exact ⟨tv_mem_Ut _, hb4, hb3⟩
    · rw [h, hc2]
      exact ⟨(Ut n).mul_mem (tv_mem_Ut _) (tv_mem_Ut _), hb6, hb5⟩
  intro hle
  have hlP2 : (l : G) ∈ parab (L ⊔ S) n W 2 := D.mem_parab_of_alpha l (Ut_le_Qn n 2 hαU.1)
  have hlE : (l : G) ∈ D.Ebk (i := 2) (by norm_num) h2n (P := ix 1 (by omega))
      (Q := ix 2 (by omega)) rfl rfl :=
    (D.mem_Ebk (i := 2) (by norm_num) h2n (P := ix 1 (by omega)) (Q := ix 2 (by omega))
      rfl rfl).2 ⟨hlP2, l, dec_self l, hαU.2.1⟩
  have hYn : parab (L ⊔ S) n W 2 ≤ Subgroup.normalizer (oTwoUpper (parab (L ⊔ S) n W 2) : Set G) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_oTwoUpper _)
  have hl_core : (l : G) ∈ pCoreOf 2 (oTwoUpper (parab (L ⊔ S) n W 2)) :=
    inf_le_pCoreOf (D.Ebk_isPGroup (i := 2) (by norm_num) h2n (P := ix 1 (by omega))
      (Q := ix 2 (by omega)) rfl rfl)
      (D.Ebk_normal (i := 2) (by norm_num) h2n (P := ix 1 (by omega)) (Q := ix 2 (by omega))
        rfl rfl) hYn (CFSG.Quasithin.oTwoUpper_le _) ⟨hlE, hlY⟩
  have hl_core1 := hle hl_core
  rw [D.pCoreOf_eq] at hl_core1
  have hcent : (l : G) ∈ Subgroup.centralizer (W 2 : Set G) := hl_core1.2
  set v : Vt n := Pi.single (ix 1 (by omega)) 1 with hv
  set u₁ : ↥UL := D.β.symm (Multiplicative.ofAdd v) with hu₁
  have hβu : Multiplicative.toAdd (D.β u₁) = v := by
    rw [hu₁, MulEquiv.apply_symm_apply, toAdd_ofAdd]
  have hvF : v ∈ flagSpace n (ZMod 2) 2 := by
    rw [mem_flagSpace]
    intro j hj
    have hne : j ≠ ix 1 (by omega) := fun h => by
      have := congrArg Fin.val h
      simp [ix] at this
      omega
    simp [hv, hne]
  have hu₁W : (u₁ : G) ∈ W 2 := by
    refine (D.W_mem (by norm_num) (by omega) u₁).2 ⟨u₁.2, ?_⟩
    show Multiplicative.toAdd (D.β u₁) ∈ _
    rw [hβu]
    exact hvF
  have hcomm := Subgroup.mem_centralizer_iff.1 hcent (u₁ : G) hu₁W
  have hconj : (u₁ : G) = (l : G) * (u₁ : G) * (l : G)⁻¹ := eq_mul_inv_iff_mul_eq.2 hcomm
  have hrel := D.rel l u₁ u₁ hconj
  rw [hβu] at hrel
  have h0 := congrFun hrel (ix 0 (by omega))
  have hent : mat (D.α l) (ix 0 (by omega)) (ix 1 (by omega)) = 1 := by
    have := congrFun (congrFun hαU.2.2 0) 1
    simpa [blk, tau2] using this
  have h1 : (mat (D.α l) *ᵥ v) (ix 0 (by omega)) = mat (D.α l) (ix 0 (by omega)) (ix 1 (by omega)) := by
    simp [hv]
  have h2 : v (ix 0 (by omega)) = 0 := by
    have hne : (ix 0 (by omega) : Fin n) ≠ ix 1 (by omega) := fun h => by
      have := congrArg Fin.val h
      simp [ix] at this
    simp [hv, hne]
  rw [h1, h2, hent] at h0
  exact zero_ne_one h0

theorem rank2_c (hn : n = 4 ∨ n = 5) :
    ⁅oTwoUpper (parab (L ⊔ S) n W 1) ⊔ oTwoUpper (parab (L ⊔ S) n W 2),
        oTwoUpper (parab (L ⊔ S) n W 1) ⊔ oTwoUpper (parab (L ⊔ S) n W 2)⁆ =
      oTwoUpper (parab (L ⊔ S) n W 1) ⊔ oTwoUpper (parab (L ⊔ S) n W 2) := by
  have h3 : 3 ≤ n := D.three_le
  obtain ⟨hT1, hT2, hU2, hc1, hc2, hc3, hc4⟩ := node_compute hn h3
  obtain ⟨hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10⟩ := node_blocks hn h3
  obtain ⟨hsq1, hsq2, hsq3, hsq4⟩ := node_squares hn h3
  have ht₂ : T2 n h3 ∈ Qn n 2 := (Qn n 2).mul_mem (Ut_le_Qn n 2 (tv_mem_Ut _))
    (reflection_mem_Qn (by norm_num) (by omega))
  have ht₁ : T1 n h3 ∈ Qn n 1 := (Qn n 1).mul_mem (Ut_le_Qn n 1 (tv_mem_Ut _))
    (reflection_mem_Qn (by norm_num) (by omega))
  have hu : E02 n h3 ∈ Ut n := tv_mem_Ut _
  obtain ⟨l₁, hl₁Y, hl₁α⟩ := D.exists_comm_lift (j := 2) hT2 hU2 ht₂ hu
  obtain ⟨l₂, hl₂Y, hl₂α⟩ := D.exists_comm_lift (j := 1) hT1 hU2 ht₁ hu
  have h₁ : D.α l₁ ∈ Ut n ∧ D.α l₁ * D.α l₁ = 1 ∧
      blk (ix 0 (by omega)) (ix 1 (by omega)) (D.α l₁) = tau2 := by
    rcases hl₁α with h | h
    · rw [h, hc1]
      exact ⟨tv_mem_Ut _, hsq1, hb3⟩
    · rw [h, hc2]
      exact ⟨(Ut n).mul_mem (tv_mem_Ut _) (tv_mem_Ut _), hsq3, hb5⟩
  have h₂ : D.α l₂ ∈ Ut n ∧ D.α l₂ * D.α l₂ = 1 ∧
      blk (ix 1 (by omega)) (ix 2 (by omega)) (D.α l₂) = tau2 := by
    rcases hl₂α with h | h
    · rw [h, hc3]
      exact ⟨tv_mem_Ut _, hsq2, hb8⟩
    · rw [h, hc4]
      exact ⟨(Ut n).mul_mem (tv_mem_Ut _) (tv_mem_Ut _), hsq4, hb10⟩
  have hl₁P : (l₁ : G) ∈ parab (L ⊔ S) n W 1 := D.mem_parab_of_alpha l₁ (Ut_le_Qn n 1 h₁.1)
  have hl₂P : (l₂ : G) ∈ parab (L ⊔ S) n W 2 := D.mem_parab_of_alpha l₂ (Ut_le_Qn n 2 h₂.1)
  refine le_antisymm (Subgroup.commutator_le.2 fun a ha b hb => ?_) (sup_le ?_ ?_)
  · exact (oTwoUpper (parab (L ⊔ S) n W 1) ⊔ oTwoUpper (parab (L ⊔ S) n W 2)).mul_mem
      ((oTwoUpper (parab (L ⊔ S) n W 1) ⊔ oTwoUpper (parab (L ⊔ S) n W 2)).mul_mem
        ((oTwoUpper (parab (L ⊔ S) n W 1) ⊔ oTwoUpper (parab (L ⊔ S) n W 2)).mul_mem ha hb)
        ((oTwoUpper (parab (L ⊔ S) n W 1) ⊔ oTwoUpper (parab (L ⊔ S) n W 2)).inv_mem ha))
      ((oTwoUpper (parab (L ⊔ S) n W 1) ⊔ oTwoUpper (parab (L ⊔ S) n W 2)).inv_mem hb)
  ·
    refine (Subgroup.closure_le _).2 fun x hx => ?_
    have hxK : x ∈ oTwoUpper (parab (L ⊔ S) n W 1) ⊔ oTwoUpper (parab (L ⊔ S) n W 2) :=
      (le_sup_left : oTwoUpper (parab (L ⊔ S) n W 1) ≤ _) (mem_oTwoUpper_of_odd hx.1 hx.2)
    have hyK : (l₁ : G) ∈ oTwoUpper (parab (L ⊔ S) n W 1) ⊔ oTwoUpper (parab (L ⊔ S) n W 2) :=
      (le_sup_right : oTwoUpper (parab (L ⊔ S) n W 2) ≤ _) hl₁Y
    obtain ⟨k, hk⟩ := D.inv_property (i := 1) (by norm_num) (by omega) (P := ix 0 (by omega))
      (Q := ix 1 (by omega)) rfl rfl hl₁P (dec_self l₁) rfl h₁.2.1 h₁.2.2 hx.1 hx.2
    exact mem_commutator_of_inverting hxK hyK hx.2 hk
  ·
    refine (Subgroup.closure_le _).2 fun x hx => ?_
    have hxK : x ∈ oTwoUpper (parab (L ⊔ S) n W 1) ⊔ oTwoUpper (parab (L ⊔ S) n W 2) :=
      (le_sup_right : oTwoUpper (parab (L ⊔ S) n W 2) ≤ _) (mem_oTwoUpper_of_odd hx.1 hx.2)
    have hyK : (l₂ : G) ∈ oTwoUpper (parab (L ⊔ S) n W 1) ⊔ oTwoUpper (parab (L ⊔ S) n W 2) :=
      (le_sup_left : oTwoUpper (parab (L ⊔ S) n W 1) ≤ _) hl₂Y
    obtain ⟨k, hk⟩ := D.inv_property (i := 2) (by norm_num) (by omega) (P := ix 1 (by omega))
      (Q := ix 2 (by omega)) rfl rfl hl₂P (dec_self l₂) rfl h₂.2.1 h₂.2.2 hx.1 hx.2
    exact mem_commutator_of_inverting hxK hyK hx.2 hk

end P0Setup

end CFSG.Quasithin.FLc
