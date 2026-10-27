module

public import CFSG.LocalAnalysis.StandardType.GGTorusMaxSieveAux2
public import CFSG.LocalAnalysis.AGLEmbedding.AltOuterOdd
public import CFSG.LocalAnalysis.StandardType.GGSporKOrdBMOut
public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20LieEnd
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2FamSpor

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.EvenSmallLie.CatalogOrders CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.ComponentClassification.OuterAutomorphisms

theorem tm_orderTwistedA_eq {n q : ℕ} (hq : 1 ≤ q) : orderTwistedA n q = ordTwistedA n q := by
  have h : (∏ i ∈ Finset.Icc 2 (n + 1), (if Even i then q ^ i - 1 else q ^ i + 1)) =
      (∏ i ∈ Finset.Icc 2 (n + 1), ((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat) := by
    apply Finset.prod_congr rfl
    intro i _
    rcases Nat.even_or_odd i with he | ho
    · rw [if_pos he, CFSG.Timmesfeld.Orders.toNat_pow_sub_neg_one_pow_of_even hq he]
    · rw [if_neg (Nat.not_even_iff_odd.mpr ho),
        CFSG.Timmesfeld.Orders.toNat_pow_sub_neg_one_pow_of_odd ho]
  simp only [orderTwistedA, ordTwistedA, h]

theorem tm_order_bridge (d : TauCeti.LieTypeIndex) (h : tmTag d ∈ searchTags) :
    CFSG.HardMathSupport.Solomon.Coordinator.I1420.lieOrderFormula d =
      lieOrd (tmTag d) (tmRank d) (tmChar d ^ tmDeg d) := by
  cases d with
  | twistedA n q =>
      simp only [CFSG.HardMathSupport.Solomon.Coordinator.I1420.lieOrderFormula, lieOrd, tmTag,
        tmRank, tmChar, tmDeg, TauCeti.PrimePower.card_def, Nat.add_sub_cancel]
      exact tm_orderTwistedA_eq (n := n) (q := q.p ^ q.exponent)
        (one_le_pow₀ q.prime_p.one_le)
  | reeF4 m => exact absurd h (by simp [tmTag, searchTags])
  | tits => exact absurd h (by simp [tmTag, searchTags])
  | _ =>
      simp only [CFSG.HardMathSupport.Solomon.Coordinator.I1420.lieOrderFormula, lieOrd, tmTag,
        tmRank, tmChar, tmDeg, TauCeti.PrimePower.card_def, Nat.add_sub_cancel] <;>
      first | rfl | omega

theorem tm_out_bridge (d : TauCeti.LieTypeIndex) (h : tmTag d ∈ searchTags) :
    tmLieOut d = tmOutTag (tmTag d) (tmRank d) (tmChar d) (tmDeg d) := by
  cases d with
  | A n q =>
      simp only [tmLieOut, tmOutTag, tmTag, tmChar, tmDeg, TauCeti.PrimePower.card_def]
      by_cases hn : n = 1
      · subst hn; simp [tmRank]
      · have h2 : tmRank (.A n q) ≠ 2 := by simp [tmRank]; omega
        rw [if_neg hn, if_neg h2]
        simp [tmRank]
  | _ =>
      simp only [tmLieOut, tmOutTag, tmTag, tmRank, tmChar, tmDeg, TauCeti.PrimePower.card_def] <;>
      first | rfl | omega

theorem tmPrime_dvd_factorial_div_two {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpn : p ≤ n) :
    p ∣ n.factorial / 2 := by
  have hn2 : 2 ≤ n := by have := hp.two_le; omega
  have h2 : 2 ∣ n.factorial := Nat.dvd_factorial (by norm_num) hn2
  have hpf : p ∣ n.factorial := Nat.dvd_factorial hp.pos hpn
  have he : n.factorial = 2 * (n.factorial / 2) := (Nat.mul_div_cancel' h2).symm
  rw [he] at hpf
  exact ((Nat.Prime.dvd_mul hp).1 hpf).resolve_left
    (fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h))

theorem tmAlt_not_dvd {c : ℕ} (hc : 5 ≤ c) (hc22 : c ≤ 22) : ¬ 3 ^ 11 ∣ c.factorial / 2 := by
  interval_cases c <;> decide

theorem tmSieve_alt_contra {c k L : ℕ} (hc : 5 ≤ c) {J : Type} [Group J] [Finite J]
    (e : J ≃* alternatingGroup (Fin c)) (h23 : ¬ 23 ∣ L) (hdvd : Nat.card J ∣ L)
    (hk : 11 ≤ k) (hM : 3 ^ k ∣ Nat.card (MulAut J)) : False := by
  haveI : Nontrivial (Fin c) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have hcard : Nat.card J = c.factorial / 2 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
  have hcardA : Nat.card (alternatingGroup (Fin c)) = c.factorial / 2 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
  have haut : Nat.card (MulAut J) = Nat.card (MulAut (alternatingGroup (Fin c))) :=
    Nat.card_congr (MulAut.congr e).toEquiv
  have hdvd4 : Nat.card (MulAut (alternatingGroup (Fin c))) ∣
      Nat.card (alternatingGroup (Fin c)) * 4 :=
    CFSG.StandardType.SporadicShape.bmOut_card_aut_dvd
      (CFSG.AGLEmbedding.card_outer_alternatingGroup_dvd_four c hc)
  have h1 : 3 ^ k ∣ (c.factorial / 2) * 4 := by
    have h0 : 3 ^ k ∣ Nat.card (alternatingGroup (Fin c)) * 4 :=
      dvd_trans hM (by rw [haut]; exact hdvd4)
    rwa [hcardA] at h0
  have h2 : 3 ^ k ∣ c.factorial / 2 :=
    (Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 3 4)) h1)
  have hc22 : c ≤ 22 := by
    by_contra h
    push Not at h
    have h23c : 23 ∣ c.factorial / 2 :=
      tmPrime_dvd_factorial_div_two (by norm_num) (by norm_num) (by omega)
    exact h23 (h23c.trans (hcard ▸ hdvd))
  exact tmAlt_not_dvd hc hc22 ((pow_dvd_pow 3 hk).trans h2)

theorem tmSpor_check7 : ∀ s : TauCeti.SporadicName,
    ¬ (3 ^ 11 ∣ sporOrd s ∧ sporOrd s ∣ orderE7 2) := by
  decide +kernel

theorem tmSieve_spor_contra7 (s : TauCeti.SporadicName) {J : Type} [Group J] [Finite J]
    (e : J ≃* (TauCeti.CFSGIndex.sporadic s).Group) (hSpor : TmSporadicOutInput)
    (hSporOrd : SporadicOrdersTable) (hdvd : Nat.card J ∣ orderE7 2)
    (hM : 3 ^ 11 ∣ Nat.card (MulAut J)) : False := by
  have hcard : Nat.card J = sporOrd s := by
    rw [Nat.card_congr e.toEquiv, hSporOrd s]
  have hout : Nat.card (MulAut J) ∣ Nat.card J * 2 := hSpor s J ⟨e⟩
  have h3 : 3 ^ 11 ∣ sporOrd s * 2 := dvd_trans hM (by rwa [hcard] at hout)
  have h3' : 3 ^ 11 ∣ sporOrd s :=
    Nat.Coprime.dvd_of_dvd_mul_right (by norm_num : Nat.Coprime (3 ^ 11) 2) h3
  exact tmSpor_check7 s ⟨h3', hcard ▸ hdvd⟩


theorem tmChar_prime (d : TauCeti.LieTypeIndex) : (tmChar d).Prime := by
  cases d <;> simp only [tmChar] <;>
    first
      | (rename_i q; exact q.prime_p)
      | exact Nat.prime_two
      | exact Nat.prime_three

theorem tmDeg_pos (d : TauCeti.LieTypeIndex) : 1 ≤ tmDeg d := by
  cases d <;> simp only [tmDeg] <;>
    first
      | (rename_i q; exact Nat.one_le_iff_ne_zero.mpr q.exponent_pos.ne')
      | omega

theorem tmRank_min (d : TauCeti.LieTypeIndex) (h : d.Valid) (ht : tmTag d ∈ searchTags) :
    tmMin (tmTag d) ≤ tmRank d := by
  have hstd := ((TauCeti.LieTypeIndex.valid_iff d).1 h).1
  rw [TauCeti.LieTypeIndex.inStandardRange_iff] at hstd
  cases d <;> simp only [tmTag, tmMin, tmRank] at hstd ht ⊢ <;>
    first | omega | (exfalso; exact absurd ht (by decide))

theorem tmAdm (d : TauCeti.LieTypeIndex) (h : d.Valid) (ht : tmTag d ∈ searchTags) :
    lieAdm (tmTag d) (tmChar d) (tmDeg d) = true := by
  have hstd := ((TauCeti.LieTypeIndex.valid_iff d).1 h).1
  rw [TauCeti.LieTypeIndex.inStandardRange_iff] at hstd
  cases d with
  | suzuki m =>
      have hm : 1 ≤ m := by simpa using hstd
      have h1 : (2 * m + 1) % 2 = 1 := by omega
      have h2 : 3 ≤ 2 * m + 1 := by omega
      simp only [tmTag, tmChar, tmDeg, lieAdm]
      simp [h1, h2]
  | reeG2 m =>
      have hm : 1 ≤ m := by simpa using hstd
      have h1 : (2 * m + 1) % 2 = 1 := by omega
      have h2 : 3 ≤ 2 * m + 1 := by omega
      simp only [tmTag, tmChar, tmDeg, lieAdm]
      simp [h1, h2]
  | _ =>
      simp only [tmTag, tmChar, tmDeg, lieAdm] <;>
        first | rfl | (exfalso; exact absurd ht (by simp [tmTag, searchTags]))

theorem tmIsTarget7_twistedA {d : TauCeti.LieTypeIndex}
    (h : tmIsTarget7 (tmTag d) (tmRank d) (tmChar d) (tmDeg d) = true) :
    ∃ n q, d = .twistedA n q := by
  cases d with
  | twistedA n q => exact ⟨n, q, rfl⟩
  | _ => simp [tmTag, tmRank, tmChar, tmDeg, tmIsTarget7] at h

theorem tmIsTarget8_cases {d : TauCeti.LieTypeIndex}
    (h : tmIsTarget8 (tmTag d) (tmRank d) (tmChar d) (tmDeg d) = true) :
    (∃ n q, d = .twistedA n q) ∨ (∃ n q, d = .D n q) := by
  cases d with
  | twistedA n q => exact Or.inl ⟨n, q, rfl⟩
  | D n q => exact Or.inr ⟨n, q, rfl⟩
  | _ => simp [tmTag, tmRank, tmChar, tmDeg, tmIsTarget8] at h

theorem tmTag_not_mem_cases {d : TauCeti.LieTypeIndex} (h : tmTag d ∉ searchTags) :
    (∃ m, d = .reeF4 m) ∨ d = .tits := by
  cases d with
  | reeF4 m => exact Or.inl ⟨m, rfl⟩
  | tits => exact Or.inr rfl
  | _ => simp [tmTag, searchTags] at h

theorem tm_quad_le {n B : ℕ} (h : n * (n + 1) / 2 ≤ B) (hB : B ≤ 132) : n + 1 < 18 := by
  by_contra hc; push Not at hc
  have hm : 17 * 18 / 2 ≤ n * (n + 1) / 2 :=
    Nat.div_le_div_right (Nat.mul_le_mul (by omega) (by omega))
  omega

theorem tm_sq_le {n B : ℕ} (h : n * n ≤ B) (hB : B ≤ 132) : n < 18 := by
  by_contra hc; push Not at hc
  have hm : 18 * 18 ≤ n * n := Nat.mul_le_mul (by omega) (by omega)
  omega

theorem tm_prod_le {n B : ℕ} (h : n * (n - 1) ≤ B) (hB : B ≤ 132) : n < 18 := by
  by_contra hc; push Not at hc
  have hm : 18 * 17 ≤ n * (n - 1) := Nat.mul_le_mul (by omega) (by omega)
  omega

theorem tm_quad_le24 {n B : ℕ} (h : n * (n + 1) / 2 ≤ B) (hB : B ≤ 247) : n + 1 < 24 := by
  by_contra hc; push Not at hc
  have hm : 23 * 24 / 2 ≤ n * (n + 1) / 2 :=
    Nat.div_le_div_right (Nat.mul_le_mul (by omega) (by omega))
  omega

theorem tm_sq_le24 {n B : ℕ} (h : n * n ≤ B) (hB : B ≤ 247) : n < 24 := by
  by_contra hc; push Not at hc
  have hm : 24 * 24 ≤ n * n := Nat.mul_le_mul (by omega) (by omega)
  omega

theorem tm_prod_le24 {n B : ℕ} (h : n * (n - 1) ≤ B) (hB : B ≤ 247) : n < 24 := by
  by_contra hc; push Not at hc
  have hm : 24 * 23 ≤ n * (n - 1) := Nat.mul_le_mul (by omega) (by omega)
  omega

theorem tmRank_lt_18 (d : TauCeti.LieTypeIndex) (h : d.Valid) (ht : tmTag d ∈ searchTags)
    (hlog : lieExp (tmTag d) (tmRank d) ≤ 132) : tmRank d < 18 := by
  have hstd := ((TauCeti.LieTypeIndex.valid_iff d).1 h).1
  rw [TauCeti.LieTypeIndex.inStandardRange_iff] at hstd
  cases d <;> simp only [tmTag, tmRank, lieExp, Nat.add_sub_cancel] at hlog ht ⊢ <;>
    first
      | omega
      | exact tm_quad_le hlog le_rfl
      | exact tm_sq_le hlog le_rfl
      | exact tm_prod_le hlog le_rfl
      | (exfalso; exact absurd ht (by decide))

theorem tmRank_lt_24 (d : TauCeti.LieTypeIndex) (h : d.Valid) (ht : tmTag d ∈ searchTags)
    (hlog : lieExp (tmTag d) (tmRank d) ≤ 247) : tmRank d < 24 := by
  have hstd := ((TauCeti.LieTypeIndex.valid_iff d).1 h).1
  rw [TauCeti.LieTypeIndex.inStandardRange_iff] at hstd
  cases d <;> simp only [tmTag, tmRank, lieExp, Nat.add_sub_cancel] at hlog ht ⊢ <;>
    first
      | omega
      | exact tm_quad_le24 hlog le_rfl
      | exact tm_sq_le24 hlog le_rfl
      | exact tm_prod_le24 hlog le_rfl
      | (exfalso; exact absurd ht (by decide))

theorem tm_log_bound {d : TauCeti.LieTypeIndex} {N k : ℕ} (hN0 : 0 < N)
    (hN : N < 2 ^ (k + 1)) (hn : tmMin (tmTag d) ≤ tmRank d)
    (hd : lieOrd (tmTag d) (tmRank d) (tmChar d ^ tmDeg d) ∣ N) :
    lieExp (tmTag d) (tmRank d) ≤ k := by
  have h1 : (tmChar d ^ tmDeg d) ^ lieExp (tmTag d) (tmRank d) ∣ N :=
    (tmExp_dvd hn _).trans hd
  have h2 : 2 ^ lieExp (tmTag d) (tmRank d) ≤ N := by
    calc 2 ^ lieExp (tmTag d) (tmRank d)
        ≤ (tmChar d) ^ lieExp (tmTag d) (tmRank d) :=
          Nat.pow_le_pow_left (tmChar_prime d).two_le _
      _ ≤ (tmChar d) ^ (tmDeg d * lieExp (tmTag d) (tmRank d)) :=
          Nat.pow_le_pow_right (tmChar_prime d).pos
            (Nat.le_mul_of_pos_left _ (tmDeg_pos d))
      _ = (tmChar d ^ tmDeg d) ^ lieExp (tmTag d) (tmRank d) := by rw [pow_mul]
      _ ≤ N := Nat.le_of_dvd hN0 h1
  by_contra hc
  push Not at hc
  have : 2 ^ (k + 1) ≤ 2 ^ lieExp (tmTag d) (tmRank d) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

end CFSG.StandardType.FrameRoute

end
