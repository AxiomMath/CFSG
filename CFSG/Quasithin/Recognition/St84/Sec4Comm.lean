module

public import CFSG.Quasithin.Recognition.St84.Sec4Bounds
public import CFSG.Quasithin.Recognition.St84.Sec4Local

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86

open scoped Pointwise commutatorElement

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V} {s : ℕ}

namespace Setup

variable (X : Setup Γ G)
variable {r : ℕ}

private theorem s45_Z_one_le_Gi {d₁ : ℕ} (hd₁ : X.HasB 1 d₁) :
    X.Z 1 ≤ X.Gi ((d₁ : ℤ) + 1) ∧ ¬ X.Z 1 ≤ X.Q ((d₁ : ℤ) + 1) := by
  refine ⟨?_, ?_⟩
  · exact hd₁.Z_le_Gi (by omega)
  · have h := (X.not_Z_le_Q_edge hd₁).1
    simpa [add_comm] using h

private theorem s45_comm_le_inf_of_le {d₁ e : ℕ} (hd₁ : X.HasB 1 d₁)
    (he : X.HasB ((d₁ : ℤ) + 1) e) (hle : d₁ ≤ e) :
    ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Z 1 ⊓ X.Z ((d₁ : ℤ) + 1) := by
  have hnorm1 : X.Gi 1 ≤ Subgroup.normalizer (X.Z 1 : Set G) := fun g hg =>
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr (X.Z_normal 1 g hg)
  have hnormh : X.Gi ((d₁ : ℤ) + 1) ≤ Subgroup.normalizer (X.Z ((d₁ : ℤ) + 1) : Set G) :=
    fun g hg => Subgroup.mem_normalizer_iff_map_conj_eq.mpr (X.Z_normal ((d₁ : ℤ) + 1) g hg)
  have hZ1Gh : X.Z 1 ≤ X.Gi ((d₁ : ℤ) + 1) := hd₁.Z_le_Gi (by omega)
  have hZhG1 : X.Z ((d₁ : ℤ) + 1) ≤ X.Gi 1 := he.Z_le_Gi (by omega)
  exact F7.commutator_le_inf_of_normalizes (hZ1Gh.trans hnormh) (hZhG1.trans hnorm1)

theorem s45_lt_odd_of_not_comm_le (H : X.Sec4Hyp s r) {d₀ d₁ : ℕ} (hd₀ : X.HasB 0 d₀)
    (hd₁ : X.HasB 1 d₁)
    (hna : ¬ ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Z 1 ⊓ X.Z ((d₁ : ℤ) + 1)) :
    d₀ < d₁ ∧ Odd d₁ ∧ X.HasB ((d₁ : ℤ) + 1) d₀ ∧
      ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≠ ⊥ := by
  obtain ⟨e, he⟩ := X.exists_hasB H ((d₁ : ℤ) + 1)
  have hlt : e < d₁ := by
    by_contra h
    exact hna (X.s45_comm_le_inf_of_le hd₁ he (by omega))
  have heven : Even ((d₁ : ℤ) + 1) := by
    by_contra h
    have hodd : Odd ((d₁ : ℤ) + 1) := Int.not_even_iff_odd.mp h
    have hev1 : Even (((d₁ : ℤ) + 1) - 1) := by
      obtain ⟨k, hk⟩ := hodd
      exact ⟨k, by omega⟩
    have hd1e : X.HasB 1 e :=
      (X.hasB_iff_of_even (i := (d₁ : ℤ) + 1) (j := 1) hev1 e).mp he
    have := hd1e.unique hd₁
    omega
  have hd0e : X.HasB 0 e :=
    (X.hasB_iff_of_even (i := (d₁ : ℤ) + 1) (j := 0) (by simpa using heven) e).mp he
  have hdeq : e = d₀ := hd0e.unique hd₀
  have hodd : Odd d₁ := by
    obtain ⟨k, hk⟩ := heven
    have hodd' : Odd ((d₁ : ℤ)) := ⟨k - 1, by omega⟩
    exact (Int.odd_coe_nat d₁).mp hodd'
  have hHasB : X.HasB ((d₁ : ℤ) + 1) d₀ := by
    rw [← hdeq]
    exact he
  refine ⟨by omega, hodd, hHasB, ?_⟩
  intro hR
  exact hna (by rw [hR]; exact bot_le)

theorem Z_le_Q_inf_of_hasB {i : ℤ} {d : ℕ} (hd : X.HasB i d) (h2 : 2 ≤ d) :
    X.Z i ≤ X.Q (i - 1) ⊓ X.Q (i + 1) :=
  le_inf (X.Z_le_Q_of_lt hd (by omega)) (X.Z_le_Q_of_lt hd (by omega))

private theorem L_zero_le_centralizer_Z_zero (H : X.Sec4Hyp s r)
    (hS0 : X.edgeSylow 0 ≤ Subgroup.centralizer (X.Z 0 : Set G)) :
    X.L 0 ≤ Subgroup.centralizer (X.Z 0 : Set G) := by
  obtain ⟨t, ht, htref⟩ := X.exists_reflection H 0
  have hZnorm : conjSub t (X.Z 0) = X.Z 0 := X.Z_normal 0 t ht.1
  have hSconj : conjSub t (X.edgeSylow 0) = X.edgeSylow (-1) :=
    X.conjSub_edgeSylow_swap (by simpa using htref 0) (by simpa using htref 1)
  have hCS : conjSub t (Subgroup.centralizer (X.Z 0 : Set G)) =
      Subgroup.centralizer (X.Z 0 : Set G) := by
    rw [← conjSub_centralizer t (X.Z 0), hZnorm]
  have hSneg : X.edgeSylow (-1) ≤ Subgroup.centralizer (X.Z 0 : Set G) := by
    rw [← hSconj]
    exact hCS ▸ conjSub_mono t hS0
  have hLeq : X.L 0 = X.edgeSylow (-1) ⊔ X.edgeSylow 0 := by
    simpa using (X.edgeSylow_sup_edgeSylow 0).symm
  rw [hLeq]
  exact sup_le hSneg hS0

theorem s45_Z_zero_not_central (H : X.Sec4Hyp s r) {d₀ d₁ : ℕ} (hd₀ : X.HasB 0 d₀)
    (hd₁ : X.HasB 1 d₁)
    (hna : ¬ ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Z 1 ⊓ X.Z ((d₁ : ℤ) + 1))
    (hev : Even d₀) :
    ¬ X.Z 0 ≤ Subgroup.centralizer (X.L 0 : Set G) ∧ ⁅X.Z 0, X.Z d₀⁆ ≠ ⊥ := by
  have hA3 := X.s45_lt_odd_of_not_comm_le H hd₀ hd₁ hna
  obtain ⟨-, hodd, -, -⟩ := hA3
  have hZ0L : X.Z 0 ≤ X.L 0 := (X.Z_le_Q 0).trans (X.Q_le_L 0)
  have hnotcentral : ¬ X.Z 0 ≤ Subgroup.centralizer (X.L 0 : Set G) := by
    intro hZ0C
    have hZ0 : X.Z 0 = centerOf (X.L 0) :=
      le_antisymm (le_inf hZ0L hZ0C) (X.centerOf_L_le_Z H.char 0)
    have hevenh : Even (((d₁ : ℤ) + 1) - 0) := by
      obtain ⟨k, hk⟩ := hodd
      exact ⟨(k : ℤ) + 1, by omega⟩
    have hZh : X.Z ((d₁ : ℤ) + 1) = centerOf (X.L ((d₁ : ℤ) + 1)) :=
      X.Z_eq_centerOf_of_even_sub hevenh hZ0
    have hRbot : ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ = ⊥ := by
      refine Subgroup.commutator_eq_bot_iff_le_centralizer.mpr ?_
      rw [hZh]
      intro z hz
      rw [Subgroup.mem_centralizer_iff]
      intro c hc
      have hZG : X.Z 1 ≤ X.Gi ((d₁ : ℤ) + 1) :=
        (X.s45_Z_one_le_Gi hd₁).1
      have hzL : z ∈ X.L ((d₁ : ℤ) + 1) :=
        le_oTwoPrime_of_isPGroup
          ((pCoreOf_isPGroup' (X.Gi 1)).to_le (X.Z_le_Q 1)) hZG hz
      have hcC : c ∈ Subgroup.centralizer (X.L ((d₁ : ℤ) + 1) : Set G) :=
        (Subgroup.mem_inf.mp hc).2
      exact (Subgroup.mem_centralizer_iff.mp hcC z hzL).symm
    exact hna (by rw [hRbot]; exact bot_le)
  refine ⟨hnotcentral, ?_⟩
  intro hXbot
  have hdEd : X.HasB d₀ d₀ :=
    (X.hasB_iff_of_even (i := d₀) (j := 0) (by simpa using hev) d₀).mpr hd₀
  have hd1 : 1 ≤ d₀ := X.one_le_of_hasB hd₀
  have hd2 : 2 ≤ d₀ := by
    obtain ⟨k, hk⟩ := hev
    omega
  have hA : X.Z d₀ ≤ X.edgeSylow 0 := by
    have h1 : (1 - (d₀ : ℤ)).natAbs < d₀ := by
      have hcast : ((d₀ - 1 : ℕ) : ℤ) = (d₀ : ℤ) - 1 := by
        rw [Nat.cast_sub hd1]
        norm_num
      rw [show (1 : ℤ) - (d₀ : ℤ) = -(((d₀ - 1 : ℕ)) : ℤ) by omega]
      rw [Int.natAbs_neg, Int.natAbs_natCast]
      omega
    exact (X.Z_le_Q_of_lt hdEd h1).trans (by simpa using X.Q_le_edgeSylow (0 : ℤ))
  have hnotQ : ¬ X.Z d₀ ≤ X.Q 0 := by
    simpa using (X.not_Z_le_Q_edge hdEd).2
  have hK : X.K ≤ Subgroup.normalizer (X.Z d₀ : Set G) := fun k hk =>
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr (X.Z_normal d₀ k (X.K_le_Gi d₀ hk))
  have hsup := X.sup_Q_eq_edgeSylow_of_left_gen 0 (inf_le_left.trans hK) hA hnotQ
  have hXbot' : ⁅X.Z d₀, X.Z 0⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact hXbot
  have hE : X.Z d₀ ≤ Subgroup.centralizer (X.Z 0 : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hXbot'
  have hQ : X.Q 0 ≤ Subgroup.centralizer (X.Z 0 : Set G) := by
    intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hzc : z ∈ Subgroup.centralizer (X.Q 0 : Set G) :=
      (Subgroup.mem_inf.mp (X.Z_le_center 0 hz)).2
    exact (Subgroup.mem_centralizer_iff.mp hzc q hq).symm
  have hS0 : X.edgeSylow 0 ≤ Subgroup.centralizer (X.Z 0 : Set G) := by
    rw [← hsup]
    exact sup_le hE hQ
  exact hnotcentral (Subgroup.le_centralizer_iff.mpr (X.L_zero_le_centralizer_Z_zero H hS0))

theorem s45_step1 (H : X.Sec4Hyp s r) {d₀ d₁ : ℕ} (hd₀ : X.HasB 0 d₀)
    (hd₁ : X.HasB 1 d₁)
    (hna : ¬ ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Z 1 ⊓ X.Z ((d₁ : ℤ) + 1))
    (hev : Even d₀) :
    d₀ + 1 = d₁ ∧ 2 * d₀ < r ∧ r ≤ 2 * d₀ + 4 := by
  obtain ⟨hlt, hodd, -, -⟩ := X.s45_lt_odd_of_not_comm_le H hd₀ hd₁ hna
  have hb0 := X.hasB_zero_bounds H hd₀
  have hb1 := X.hasB_one_bounds H hd₁
  have hd1 : d₀ + 1 = d₁ := by
    rcases (by omega : d₁ = d₀ + 1 ∨ d₁ = d₀ + 2) with h' | h'
    · omega
    · exfalso
      obtain ⟨k, hk⟩ := hev
      obtain ⟨l, hl⟩ := hodd
      omega
  refine ⟨hd1, ?_, hb0.2⟩
  have := hb1.1
  omega

theorem s45_step3 (H : X.Sec4Hyp s r) (hb : r + 1 ≠ s) : s < r := by
  have h5 := H.five_le
  have h1 : s ≤ r + 1 := by
    have := H.le_r
    omega
  have hne : s ≠ r := by
    intro h
    have hodd : Odd r := h ▸ H.odd_s
    exact Nat.not_even_iff_odd.mpr hodd H.even_r
  have hne' : s ≠ r + 1 := fun h => hb h.symm
  omega

theorem arcStab_zero_five_eq_six (H : X.Sec4Hyp s r) (hs : s = 5) :
    X.arcStab 0 5 = X.arcStab 0 6 := by
  have hnot : ¬ X.RightTransAt 0 5 := by
    intro h
    have h := (H.ends_even 0 5 (by omega)).1 h
    norm_num at h
  have hQfix : pCoreOf 2 (X.arcStab 0 5) ≤ X.Gi 6 := by
    by_contra hcon
    exact hnot ((X.rightTransAt_iff H (m := 0) (r' := 5) (by norm_num)).mpr hcon)
  refine le_antisymm ?_ (X.arcStab_anti le_rfl (by norm_num))
  intro x hx
  have hx5 : x ∈ X.arcStab 0 5 := hx
  have hsup : x ∈ X.K ⊔ pCoreOf 2 (X.arcStab 0 5) := by
    rwa [← X.arcStab_eq_K_sup_pCoreOf (by norm_num : (0:ℤ) < 5)]
  have hsup' : x ∈ pCoreOf 2 (X.arcStab 0 5) ⊔ X.K := by rwa [sup_comm] at hsup
  have hKnorm : X.K ≤ Subgroup.normalizer (pCoreOf 2 (X.arcStab 0 5) : Set G) :=
    (X.K_le_GT.trans (X.GT_le_arcStab 0 5)).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  obtain ⟨q, hq, k, hk, hxqk⟩ :=
    (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_normalizes hKnorm).mp hsup'
  rw [Setup.arcStab, Fan86.mem_fixSet] at hx5 ⊢
  rintro v ⟨j, hj, rfl⟩
  rw [Set.mem_Icc] at hj
  rw [hxqk, mul_smul]
  rcases (by omega : j ≤ 5 ∨ j = 6) with hj5 | hj6
  · have hv : X.vert j ∈ X.vert '' Set.Icc (0:ℤ) 5 := ⟨j, by rw [Set.mem_Icc]; omega, rfl⟩
    calc q • (k • X.vert j) = q • X.vert j := by rw [X.K_fix k hk j]
      _ = (q * k) • X.vert j := by rw [mul_smul, X.K_fix k hk j]
      _ = x • X.vert j := by rw [hxqk]
      _ = X.vert j := hx5 (X.vert j) hv
  · subst hj6
    rw [X.K_fix k hk 6]
    exact MulAction.mem_stabilizer_iff.mp (hQfix hq)

theorem card_S_of_s_five_of_r_six (H : X.Sec4Hyp s r) (hs : s = 5) (hr : r = 6) :
    Nat.card X.S = 2 ^ (3 * X.n 0 + 2 * X.n 1) := by
  have hcard := X.card_S_eq_pow H.sing H.odd_s
  rw [hs] at hcard
  have hpc : pCoreOf 2 (X.arcStab 0 ((5 : ℕ) : ℤ)) =
      pCoreOf 2 (X.arcStab 0 (0 + (r : ℤ))) := by
    have h5 : ((5 : ℕ) : ℤ) = (5 : ℤ) := by norm_num
    rw [h5, X.arcStab_zero_five_eq_six H hs, hr]
    norm_num
  have hQne : pCoreOf 2 (X.arcStab 0 (0 + (r : ℤ))) ≠ ⊥ := by
    simpa [Setup.Qg] using X.Qg_ne_bot H
  have hQcard := (X.pCoreOf_arcStab_r H 0 hQne).1
  rw [show (5 - 1) / 2 = 2 by norm_num, hpc, hQcard] at hcard
  rw [hcard, mul_pow, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
  congr 1
  ring

theorem card_Q_one_of_s_five_of_r_six (H : X.Sec4Hyp s r) (hs : s = 5) (hr : r = 6) :
    Nat.card (X.Q 1) = 2 ^ (3 * X.n 0 + X.n 1) := by
  have hS := X.card_S_of_s_five_of_r_six H hs hr
  have hQleS : X.Q 1 ≤ X.S := X.Q_le_edgeSylow_right 1
  have hrel : (X.Q 1).relIndex X.S = 2 ^ X.n 1 := by
    have h := X.relIndex_Q_succ_edgeSylow (0 : ℤ)
    rw [show X.edgeSylow 0 = X.S from rfl, show (0 : ℤ) + 1 = 1 by norm_num] at h
    simpa using h
  have hcard := Subgroup.relIndex_mul_card (H := X.Q 1) (K := X.S)
  rw [inf_eq_left.mpr hQleS, hrel, hS] at hcard
  have hpow : 2 ^ X.n 1 * 2 ^ (3 * X.n 0 + X.n 1) =
      2 ^ (3 * X.n 0 + 2 * X.n 1) := by
    rw [← pow_add]
    congr 1
    ring
  rw [← hpow] at hcard
  exact Nat.eq_of_mul_eq_mul_left (by positivity) hcard

theorem card_Q_zero_of_s_five_of_r_six (H : X.Sec4Hyp s r) (hs : s = 5) (hr : r = 6) :
    Nat.card (X.Q 0) = 2 ^ (2 * X.n 0 + 2 * X.n 1) := by
  have hS := X.card_S_of_s_five_of_r_six H hs hr
  have hQleS : X.Q 0 ≤ X.S := X.Q_le_edgeSylow_left 0
  have hrel : (X.Q 0).relIndex X.S = 2 ^ X.n 0 := by
    have h := X.relIndex_Q_edgeSylow (0 : ℤ)
    rw [show X.edgeSylow 0 = X.S from rfl] at h
    simpa using h
  have hcard := Subgroup.relIndex_mul_card (H := X.Q 0) (K := X.S)
  rw [inf_eq_left.mpr hQleS, hrel, hS] at hcard
  have hpow : 2 ^ X.n 0 * 2 ^ (2 * X.n 0 + 2 * X.n 1) =
      2 ^ (3 * X.n 0 + 2 * X.n 1) := by
    rw [← pow_add]
    congr 1
    ring
  rw [← hpow] at hcard
  exact Nat.eq_of_mul_eq_mul_left (by positivity) hcard

end Setup

end CFSG.Quasithin.St84
