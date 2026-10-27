module

public import CFSG.LocalAnalysis.StandardType.GGTorusMaxSieveAux3

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.EvenSmallLie.CatalogOrders CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator

theorem tmSieve_reeF4_contra7 {m : ℕ} (hm : 1 ≤ m)
    (hdvd : orderTwistedF4 (2 ^ (2 * m + 1)) ∣ orderE7 2)
    (hM : 3 ^ 11 ∣ orderTwistedF4 (2 ^ (2 * m + 1)) * (2 * m + 1)) : False := by
  have hq : (2 ^ (2 * m + 1)) ^ 12 ∣ orderTwistedF4 (2 ^ (2 * m + 1)) := by
    unfold orderTwistedF4
    rw [mul_assoc, mul_assoc, mul_assoc]
    exact dvd_mul_right _ _
  have hpow : 2 ^ (12 * (2 * m + 1)) ∣ orderE7 2 := by
    rw [← pow_mul] at hq
    simpa [mul_comm] using hq.trans hdvd
  have hm5 : m ≤ 5 := by
    by_contra h; push Not at h
    have h133 : 133 ≤ 12 * (2 * m + 1) := by omega
    have h2 : 2 ^ 133 ≤ 2 ^ (12 * (2 * m + 1)) := Nat.pow_le_pow_right (by norm_num) h133
    have hle : 2 ^ (12 * (2 * m + 1)) ≤ orderE7 2 :=
      Nat.le_of_dvd (by norm_num [orderE7]) hpow
    have hlt : orderE7 2 < 2 ^ 133 := by norm_num [orderE7]
    exact absurd (le_trans h2 hle) (not_le.mpr hlt)
  have hcheck : ¬ (orderTwistedF4 (2 ^ (2 * m + 1)) ∣ orderE7 2 ∧
      3 ^ 11 ∣ orderTwistedF4 (2 ^ (2 * m + 1)) * (2 * m + 1)) := by
    interval_cases m <;> decide
  exact hcheck ⟨hdvd, hM⟩

theorem tmSieve_tits_contra7 (hdvd : orderTits ∣ orderE7 2)
    (hM : 3 ^ 11 ∣ orderTits * 2) : False := by
  have hcheck : ¬ (orderTits ∣ orderE7 2 ∧ 3 ^ 11 ∣ orderTits * 2) := by decide
  exact hcheck ⟨hdvd, hM⟩

theorem tmSieve_reeF4_contra8 {m : ℕ} (hm : 1 ≤ m)
    (hdvd : orderTwistedF4 (2 ^ (2 * m + 1)) ∣ orderE8 2)
    (hM : 3 ^ 13 ∣ orderTwistedF4 (2 ^ (2 * m + 1)) * (2 * m + 1)) : False := by
  have hq : (2 ^ (2 * m + 1)) ^ 12 ∣ orderTwistedF4 (2 ^ (2 * m + 1)) := by
    unfold orderTwistedF4
    rw [mul_assoc, mul_assoc, mul_assoc]
    exact dvd_mul_right _ _
  have hpow : 2 ^ (12 * (2 * m + 1)) ∣ orderE8 2 := by
    rw [← pow_mul] at hq
    simpa [mul_comm] using hq.trans hdvd
  have hm5 : m ≤ 9 := by
    by_contra h; push Not at h
    have h133 : 248 ≤ 12 * (2 * m + 1) := by omega
    have h2 : 2 ^ 248 ≤ 2 ^ (12 * (2 * m + 1)) := Nat.pow_le_pow_right (by norm_num) h133
    have hle : 2 ^ (12 * (2 * m + 1)) ≤ orderE8 2 :=
      Nat.le_of_dvd (by norm_num [orderE8]) hpow
    have hlt : orderE8 2 < 2 ^ 248 := by norm_num [orderE8]
    exact absurd (le_trans h2 hle) (not_le.mpr hlt)
  have hcheck : ¬ (orderTwistedF4 (2 ^ (2 * m + 1)) ∣ orderE8 2 ∧
      3 ^ 13 ∣ orderTwistedF4 (2 ^ (2 * m + 1)) * (2 * m + 1)) := by
    interval_cases m <;> decide
  exact hcheck ⟨hdvd, hM⟩

theorem tmSieve_tits_contra8 (hdvd : orderTits ∣ orderE8 2)
    (hM : 3 ^ 13 ∣ orderTits * 2) : False := by
  have hcheck : ¬ (orderTits ∣ orderE8 2 ∧ 3 ^ 13 ∣ orderTits * 2) := by decide
  exact hcheck ⟨hdvd, hM⟩

theorem tmSpor_check8 : ∀ s : TauCeti.SporadicName,
    ¬ (3 ^ 13 ∣ sporOrd s ∧ sporOrd s ∣ orderE8 2) := by
  decide +kernel

theorem tmSieve_spor_contra8 (s : TauCeti.SporadicName) {J : Type} [Group J] [Finite J]
    (e : J ≃* (TauCeti.CFSGIndex.sporadic s).Group) (hSpor : TmSporadicOutInput)
    (hSporOrd : SporadicOrdersTable) (hdvd : Nat.card J ∣ orderE8 2)
    (hM : 3 ^ 13 ∣ Nat.card (MulAut J)) : False := by
  have hcard : Nat.card J = sporOrd s := by
    rw [Nat.card_congr e.toEquiv, hSporOrd s]
  have hout : Nat.card (MulAut J) ∣ Nat.card J * 2 := hSpor s J ⟨e⟩
  have h3 : 3 ^ 13 ∣ sporOrd s * 2 := dvd_trans hM (by rwa [hcard] at hout)
  have h3' : 3 ^ 13 ∣ sporOrd s :=
    Nat.Coprime.dvd_of_dvd_mul_right (by norm_num : Nat.Coprime (3 ^ 13) 2) h3
  exact tmSpor_check8 s ⟨h3', hcard ▸ hdvd⟩

theorem tmSieve_lie_E7 (d : TauCeti.ValidLieTypeIndex) (J : Type) [Group J] [Finite J]
    (e : J ≃* (TauCeti.CFSGIndex.lie d).Group) (hLie : TmLieOutAll) (hLieOrd : LieOrderBridge)
    (hdvd : Nat.card J ∣ orderE7 2) (hlt : Nat.card J < orderE7 2)
    (hM : 3 ^ 7 * 2903040 ∣ Nat.card (MulAut J)) :
    ∃ (d' : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower), d'.1 = .twistedA 8 q ∧
      q.card = 2 ∧ Nonempty (J ≃* (TauCeti.CFSGIndex.lie d').Group) := by
  have hcard : Nat.card J = CFSG.HardMathSupport.Solomon.Coordinator.I1420.lieOrderFormula d.1 :=
    hLieOrd d J ⟨e⟩
  have hout : Nat.card (MulAut J) ∣ Nat.card J * tmLieOut d.1 := hLie d J ⟨e⟩
  have h311 : 3 ^ 11 ∣ Nat.card (MulAut J) :=
    dvd_trans (by norm_num : 3 ^ 11 ∣ 3 ^ 7 * 2903040) hM
  by_cases htag : tmTag d.1 ∈ searchTags
  · have hord := tm_order_bridge d.1 htag
    have houtb := tm_out_bridge d.1 htag
    have hd : lieOrd (tmTag d.1) (tmRank d.1) (tmChar d.1 ^ tmDeg d.1) ∣ orderE7 2 := by
      rw [← hord, ← hcard]; exact hdvd
    have hlt' : lieOrd (tmTag d.1) (tmRank d.1) (tmChar d.1 ^ tmDeg d.1) < orderE7 2 := by
      rw [← hord, ← hcard]; exact hlt
    have hM' : 3 ^ 7 * 2903040 ∣
        lieOrd (tmTag d.1) (tmRank d.1) (tmChar d.1 ^ tmDeg d.1) *
          tmOutTag (tmTag d.1) (tmRank d.1) (tmChar d.1) (tmDeg d.1) := by
      rw [← houtb, ← hord, ← hcard]; exact dvd_trans hM hout
    have hp : (tmChar d.1).Prime := tmChar_prime d.1
    have hf : 1 ≤ tmDeg d.1 := tmDeg_pos d.1
    have hn : tmMin (tmTag d.1) ≤ tmRank d.1 := tmRank_min d.1 d.2 htag
    have hlog : lieExp (tmTag d.1) (tmRank d.1) ≤ 132 :=
      tm_log_bound (N := orderE7 2) (k := 132) (by norm_num [orderE7]) (by norm_num [orderE7]) hn hd
    have hnmem : tmRank d.1 ∈ List.range 18 := by
      rw [List.mem_range]; exact tmRank_lt_18 d.1 d.2 htag hlog
    have hadm : lieAdm (tmTag d.1) (tmChar d.1) (tmDeg d.1) = true := tmAdm d.1 d.2 htag
    have hC := tmSearch_sound (ns := List.range 18) (ps := tmPs7) (N := orderE7 2)
      (by norm_num [orderE7]) tmSieve_hps7 tmSearch_E7 htag hp hf hn hnmem hadm hd
    have htgt : tmIsTarget7 (tmTag d.1) (tmRank d.1) (tmChar d.1) (tmDeg d.1) = true := by
      have hlt'' : decide (lieOrd (tmTag d.1) (tmRank d.1) (tmChar d.1 ^ tmDeg d.1) <
          orderE7 2) = true := by rw [decide_eq_true_eq]; exact hlt'
      have hmod : (lieOrd (tmTag d.1) (tmRank d.1) (tmChar d.1 ^ tmDeg d.1) *
          tmOutTag (tmTag d.1) (tmRank d.1) (tmChar d.1) (tmDeg d.1)) %
            (3 ^ 7 * 2903040) = 0 := Nat.mod_eq_zero_of_dvd hM'
      simp only [tmC7] at hC
      rw [hlt'', hmod] at hC
      simpa using hC
    obtain ⟨n, q, hq⟩ := tmIsTarget7_twistedA htgt
    rw [hq] at htgt
    simp only [tmTag, tmRank, tmChar, tmDeg, tmIsTarget7] at htgt
    simp only [beq_iff_eq, Bool.and_eq_true, Bool.true_and, Bool.not_true] at htgt
    obtain ⟨⟨⟨-, h2⟩, h3⟩, h4⟩ := htgt
    have hn8 : n = 8 := by omega
    refine ⟨d, q, ?_, ?_, ⟨e⟩⟩
    · rw [hq, hn8]
    · rw [TauCeti.PrimePower.card_def, h3, h4]; norm_num
  · rcases tmTag_not_mem_cases htag with ⟨m, hm⟩ | ht
    · have hcard' : Nat.card J = orderTwistedF4 (2 ^ (2 * m + 1)) := by rw [hcard, hm]; rfl
      have hout' : Nat.card (MulAut J) ∣ Nat.card J * (2 * m + 1) := by
        have := hout; rw [hm] at this; exact this
      have hm1 : 1 ≤ m := by
        have hstd := ((TauCeti.LieTypeIndex.valid_iff (.reeF4 m)).1 (hm ▸ d.2)).1
        rw [TauCeti.LieTypeIndex.inStandardRange_iff] at hstd
        simpa using hstd
      exact (tmSieve_reeF4_contra7 hm1 (by rw [← hcard']; exact hdvd) (by
        have := dvd_trans h311 hout'
        rwa [hcard'] at this)).elim
    · have hcard' : Nat.card J = orderTits := by rw [hcard, ht]; rfl
      have hout' : Nat.card (MulAut J) ∣ Nat.card J * 2 := by
        have := hout; rw [ht] at this; exact this
      exact (tmSieve_tits_contra7 (by rw [← hcard']; exact hdvd) (by
        have := dvd_trans h311 hout'
        rwa [hcard'] at this)).elim

theorem tmSieve_lie_E8 (d : TauCeti.ValidLieTypeIndex) (J : Type) [Group J] [Finite J]
    (e : J ≃* (TauCeti.CFSGIndex.lie d).Group) (hLie : TmLieOutAll) (hLieOrd : LieOrderBridge)
    (hdvd : Nat.card J ∣ orderE8 2) (hlt : Nat.card J < orderE8 2)
    (hM : 3 ^ 8 * 696729600 ∣ Nat.card (MulAut J)) :
    (∃ (d' : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower), d'.1 = .twistedA 9 q ∧
        q.card = 2 ∧ Nonempty (J ≃* (TauCeti.CFSGIndex.lie d').Group)) ∨
      (∃ (d' : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower), d'.1 = .D 4 q ∧
        q.card = 3 ∧ Nonempty (J ≃* (TauCeti.CFSGIndex.lie d').Group)) := by
  have hcard : Nat.card J = CFSG.HardMathSupport.Solomon.Coordinator.I1420.lieOrderFormula d.1 :=
    hLieOrd d J ⟨e⟩
  have hout : Nat.card (MulAut J) ∣ Nat.card J * tmLieOut d.1 := hLie d J ⟨e⟩
  have h313 : 3 ^ 13 ∣ Nat.card (MulAut J) :=
    dvd_trans (by norm_num : 3 ^ 13 ∣ 3 ^ 8 * 696729600) hM
  by_cases htag : tmTag d.1 ∈ searchTags
  · have hord := tm_order_bridge d.1 htag
    have houtb := tm_out_bridge d.1 htag
    have hd : lieOrd (tmTag d.1) (tmRank d.1) (tmChar d.1 ^ tmDeg d.1) ∣ orderE8 2 := by
      rw [← hord, ← hcard]; exact hdvd
    have hlt' : lieOrd (tmTag d.1) (tmRank d.1) (tmChar d.1 ^ tmDeg d.1) < orderE8 2 := by
      rw [← hord, ← hcard]; exact hlt
    have hM' : 3 ^ 8 * 696729600 ∣
        lieOrd (tmTag d.1) (tmRank d.1) (tmChar d.1 ^ tmDeg d.1) *
          tmOutTag (tmTag d.1) (tmRank d.1) (tmChar d.1) (tmDeg d.1) := by
      rw [← houtb, ← hord, ← hcard]; exact dvd_trans hM hout
    have hp : (tmChar d.1).Prime := tmChar_prime d.1
    have hf : 1 ≤ tmDeg d.1 := tmDeg_pos d.1
    have hn : tmMin (tmTag d.1) ≤ tmRank d.1 := tmRank_min d.1 d.2 htag
    have hlog : lieExp (tmTag d.1) (tmRank d.1) ≤ 247 :=
      tm_log_bound (N := orderE8 2) (k := 247) (by norm_num [orderE8]) (by norm_num [orderE8]) hn hd
    have hnmem : tmRank d.1 ∈ List.range 24 := by
      rw [List.mem_range]; exact tmRank_lt_24 d.1 d.2 htag hlog
    have hadm : lieAdm (tmTag d.1) (tmChar d.1) (tmDeg d.1) = true := tmAdm d.1 d.2 htag
    have hC := tmSearch_sound (ns := List.range 24) (ps := tmPs8) (N := orderE8 2)
      (by norm_num [orderE8]) tmSieve_hps8 tmSearch_E8 htag hp hf hn hnmem hadm hd
    have htgt : tmIsTarget8 (tmTag d.1) (tmRank d.1) (tmChar d.1) (tmDeg d.1) = true := by
      have hlt'' : decide (lieOrd (tmTag d.1) (tmRank d.1) (tmChar d.1 ^ tmDeg d.1) <
          orderE8 2) = true := by rw [decide_eq_true_eq]; exact hlt'
      have hmod : (lieOrd (tmTag d.1) (tmRank d.1) (tmChar d.1 ^ tmDeg d.1) *
          tmOutTag (tmTag d.1) (tmRank d.1) (tmChar d.1) (tmDeg d.1)) %
            (3 ^ 8 * 696729600) = 0 := Nat.mod_eq_zero_of_dvd hM'
      simp only [tmC8] at hC
      rw [hlt'', hmod] at hC
      simpa using hC
    rcases tmIsTarget8_cases htgt with ⟨n, q, hq⟩ | ⟨n, q, hq⟩
    · rw [hq] at htgt
      simp only [tmIsTarget8, tmTag, tmRank, tmChar, tmDeg, Bool.or_eq_true,
        Bool.and_eq_true, beq_iff_eq, Bool.true_and, Bool.not_true, Bool.false_or] at htgt
      rcases htgt with h | h
      · obtain ⟨⟨⟨-, h2⟩, h3⟩, h4⟩ := h
        have hn9 : n = 9 := by omega
        exact Or.inl ⟨d, q, by rw [hq, hn9], by
          rw [TauCeti.PrimePower.card_def, h3, h4]; norm_num, ⟨e⟩⟩
      · obtain ⟨⟨⟨hbad, -⟩, -⟩, -⟩ := h
        exact absurd hbad (by decide)
    · rw [hq] at htgt
      simp only [tmIsTarget8, tmTag, tmRank, tmChar, tmDeg, Bool.or_eq_true,
        Bool.and_eq_true, beq_iff_eq, Bool.true_and, Bool.not_true, Bool.false_or] at htgt
      rcases htgt with h | h
      · obtain ⟨⟨⟨hbad, -⟩, -⟩, -⟩ := h
        exact absurd hbad (by decide)
      · obtain ⟨⟨⟨-, h2⟩, h3⟩, h4⟩ := h
        have hn4 : n = 4 := by omega
        exact Or.inr ⟨d, q, by rw [hq, hn4], by
          rw [TauCeti.PrimePower.card_def, h3, h4]; norm_num, ⟨e⟩⟩
  · rcases tmTag_not_mem_cases htag with ⟨m, hm⟩ | ht
    · have hcard' : Nat.card J = orderTwistedF4 (2 ^ (2 * m + 1)) := by rw [hcard, hm]; rfl
      have hout' : Nat.card (MulAut J) ∣ Nat.card J * (2 * m + 1) := by
        have := hout; rw [hm] at this; exact this
      have hm1 : 1 ≤ m := by
        have hstd := ((TauCeti.LieTypeIndex.valid_iff (.reeF4 m)).1 (hm ▸ d.2)).1
        rw [TauCeti.LieTypeIndex.inStandardRange_iff] at hstd
        simpa using hstd
      exact (tmSieve_reeF4_contra8 hm1 (by rw [← hcard']; exact hdvd) (by
        have := dvd_trans h313 hout'
        rwa [hcard'] at this)).elim
    · have hcard' : Nat.card J = orderTits := by rw [hcard, ht]; rfl
      have hout' : Nat.card (MulAut J) ∣ Nat.card J * 2 := by
        have := hout; rw [ht] at this; exact this
      exact (tmSieve_tits_contra8 (by rw [← hcard']; exact hdvd) (by
        have := dvd_trans h313 hout'
        rwa [hcard'] at this)).elim

end CFSG.StandardType.FrameRoute

end
