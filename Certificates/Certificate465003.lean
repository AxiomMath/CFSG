
module

public import Certificates.Certificate465003Base1

public import CFSG.LocalAnalysis.StandardType.L34SylowKBridge
public import Certificates.Kernel.L34Syl.ChkPow
public import Certificates.Kernel.L34Syl.ChkRec
public import Certificates.Kernel.L34Syl.ChkOrb
public import Certificates.Kernel.L34Syl.Bind

public section

open CFSG.StandardType.L34Sylow CFSG.PSL3Four.Native

namespace Certificates

local instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

open CFSG.KC.L34Syl CFSG.StandardType.L34Sylow CFSG.PSL3Four.Native CertificateChecks.KernelL34Syl CertificateChecks.Batch465003
open CFSG.ComponentClassification.PSL3Four (TabRep)

open CFSG.StandardType.L34Sylow CFSG.PSL3Four.Native in
def RecOK (p RT cnt : ℕ) (x : ℕ) : Prop :=
  PermN 42 6 63 x ∧ x < 2 ^ 252 ∧ CanonGen p (pp 42 6 63 x) ∧
    orderOf (pp 42 6 63 x) = p ∧ pp 42 6 63 x ∈ closureTabs gensS ∧ pp 42 6 63 x ≠ 1 ∧
    pp 42 6 63 x ^ p = 1 ∧ ∃ c ∈ closureTabs pGens, ∃ i < cnt,
      c⁻¹ * pp 42 6 63 x * c ∈ Subgroup.zpowers (pp 42 6 63 (lane 252 pm252 RT ((p - 1) * i)))

def PowFacts (p RT cnt : ℕ) : Prop :=
  ∀ i < cnt, (∀ k < p - 1, PermN 42 6 63 (lane 252 pm252 RT ((p - 1) * i + k)) ∧
      pp 42 6 63 (lane 252 pm252 RT ((p - 1) * i + k)) =
        pp 42 6 63 (lane 252 pm252 RT ((p - 1) * i)) ^ (k + 1)) ∧
    pp 42 6 63 (lane 252 pm252 RT ((p - 1) * i)) ^ p = 1 ∧
    pp 42 6 63 (lane 252 pm252 RT ((p - 1) * i)) ≠ 1

theorem hLP : LettersInv 42 6 63 (lane 252 pm252 LP) 2 := lettersOK_sound ch465003_lp

theorem hLS : LettersInv 42 6 63 (lane 252 pm252 LS) 3 := lettersOK_sound ch465003_ls

theorem hLZ : LettersInv 42 6 63 (lane 252 pm252 LZ) 3 := lettersOK_sound ch465003_lz

theorem tp : TabRep pT (pp 42 6 63 (lane 252 pm252 LP 0)) := tabRep_pp (hLP 0 (by omega)).1 ch465003_bp

theorem tq : TabRep qT (pp 42 6 63 (lane 252 pm252 LP 2)) := tabRep_pp (hLP 1 (by omega)).1 ch465003_bq

theorem gS : closureTabs gensS = gen 42 6 63 (lane 252 pm252 LS) 3 := by
  rw [closureTabs_eq_closure (ng := 3) (F := fun j => pp 42 6 63 (lane 252 pm252 LS (2 * j))) rfl]
  · rfl
  intro j hj
  interval_cases j
  · exact tabRep_pp (hLS 0 (by omega)).1 ch465003_bs0
  · exact tabRep_pp (hLS 1 (by omega)).1 ch465003_bs1
  · exact tabRep_pp (hLS 2 (by omega)).1 ch465003_bs2

theorem gP : closureTabs pGens = gen 42 6 63 (lane 252 pm252 LP) 2 := by
  rw [closureTabs_eq_closure (ng := 2) (F := fun j => pp 42 6 63 (lane 252 pm252 LP (2 * j))) rfl]
  · rfl
  intro j hj
  interval_cases j
  · exact tp
  · exact tq

theorem pS : pp 42 6 63 (lane 252 pm252 LP 0) ∈ closureTabs gensS ∧
    pp 42 6 63 (lane 252 pm252 LP 2) ∈ closureTabs gensS := by
  have h := wordsK_sound (ng := 3) hLS ch465003_ps
  rw [gS]
  have h0 := (h 0 (by rw [ch465003_len.2.2.2.2.1]; omega)).2
  have h1 := (h 1 (by rw [ch465003_len.2.2.2.2.1]; omega)).2
  exact ⟨h0, h1⟩

theorem hPS : closureTabs pGens ≤ closureTabs gensS := by
  rw [gP]
  refine gen_le fun j hj => ?_
  interval_cases j
  · exact pS.1
  · exact pS.2

theorem hPgrp : (∀ k < 9, PermN 42 6 63 (lane 252 pm252 PT k)) ∧
    (∀ k < 9, ∀ k' < 9, pp 42 6 63 (lane 252 pm252 PT k) = pp 42 6 63 (lane 252 pm252 PT k') →
      k = k') ∧
    ∀ g, g ∈ gen 42 6 63 (lane 252 pm252 LP) 2 ↔ ∃ k < 9, pp 42 6 63 (lane 252 pm252 PT k) = g :=
  grpK_sound (by norm_num) (by norm_num) (by norm_num) hLP ch465003_p

theorem hP9 : Nat.card ↥(closureTabs pGens) = 9 := by
  rw [gP]
  exact card_gen_eq hPgrp.2.1 hPgrp.2.2

theorem hPT : ∀ c < 9, PermN 42 6 63 (lane 252 pm252 PT c) ∧
    pp 42 6 63 (lane 252 pm252 PT c) ∈ closureTabs pGens := by
  intro c hc
  rw [gP]
  exact ⟨hPgrp.1 c hc, (hPgrp.2.2 _).2 ⟨c, hc, rfl⟩⟩

theorem gM {LM j : ℕ} (hj : j < 6) (hLM : lettersOK 42 6 63 252 (lane 252 pm252 LM) 3 = true)
    (he : lane 252 pm252 LM 0 = lane 252 pm252 LP 0 ∧ lane 252 pm252 LM 2 = lane 252 pm252 LP 2 ∧
      lane 252 pm252 LM 4 = lane 252 pm252 TG (j + 1))
    (hb : tabEqB mRs[j]! (lane 252 pm252 TG (j + 1)) = true) :
    closureTabs (pGensWith mRs[j]!) = gen 42 6 63 (lane 252 pm252 LM) 3 := by
  have hL := lettersOK_sound hLM
  rw [closureTabs_eq_closure (ng := 3) (F := fun k => pp 42 6 63 (lane 252 pm252 LM (2 * k))) rfl]
  · rfl
  intro k hk
  interval_cases k
  · change TabRep pT (pp 42 6 63 (lane 252 pm252 LM 0))
    rw [he.1]
    exact tp
  · change TabRep qT (pp 42 6 63 (lane 252 pm252 LM 2))
    rw [he.2.1]
    exact tq
  · change TabRep mRs[j]! (pp 42 6 63 (lane 252 pm252 LM 4))
    have hp := (hL 2 (by omega)).1
    change PermN 42 6 63 (lane 252 pm252 LM 4) at hp
    rw [he.2.2] at hp ⊢
    exact tabRep_pp hp hb

theorem MS {j : ℕ} (hj : j < 6) (hb : tabEqB mRs[j]! (lane 252 pm252 TG (j + 1)) = true) :
    closureTabs (pGensWith mRs[j]!) ≤ closureTabs gensS := by
  have h := wordsK_sound (ng := 3) hLS ch465003_rs
  have hr := h j (by rw [ch465003_len.2.2.2.2.2.1]; omega)
  refine closureTabs_le fun k hk => ?_
  rw [pGensWith_size] at hk
  interval_cases k
  · exact ⟨_, pS.1, by rw [pGensWith_zero]; exact tp⟩
  · exact ⟨_, pS.2, by rw [pGensWith_one]; exact tq⟩
  · refine ⟨_, ?_, by rw [pGensWith_two]; exact tabRep_pp (by simpa using hr.1) hb⟩
    rw [gS]
    simpa using hr.2

theorem aSix : ∀ j < 6, ASixData (closureTabs gensS) (closureTabs (pGensWith mRs[j]!)) := by
  intro j hj
  interval_cases j
  · exact aSixData_of_checks gS (gM (by omega) ch465003_lm0 ch465003_em0 ch465003_bm0)
      (MS (by omega) ch465003_bm0) ch465003_ls ch465003_lm0 ch465003_orb0 ch465003_sub0
      ch465003_res0 ch465003_sx0 ch465003_st0 ch465003_cw0 ch465003_len.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      rfl ch465003_cn.1
  · exact aSixData_of_checks gS (gM (by omega) ch465003_lm1 ch465003_em1 ch465003_bm1)
      (MS (by omega) ch465003_bm1) ch465003_ls ch465003_lm1 ch465003_orb1 ch465003_sub1
      ch465003_res1 ch465003_sx1 ch465003_st1 ch465003_cw1
      ch465003_len.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl ch465003_cn.2.1
  · exact aSixData_of_checks gS (gM (by omega) ch465003_lm2 ch465003_em2 ch465003_bm2)
      (MS (by omega) ch465003_bm2) ch465003_ls ch465003_lm2 ch465003_orb2 ch465003_sub2
      ch465003_res2 ch465003_sx2 ch465003_st2 ch465003_cw2
      ch465003_len.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl ch465003_cn.2.2.1
  · exact aSixData_of_checks gS (gM (by omega) ch465003_lm3 ch465003_em3 ch465003_bm3)
      (MS (by omega) ch465003_bm3) ch465003_ls ch465003_lm3 ch465003_orb3 ch465003_sub3
      ch465003_res3 ch465003_sx3 ch465003_st3 ch465003_cw3
      ch465003_len.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl ch465003_cn.2.2.2.1
  · exact aSixData_of_checks gS (gM (by omega) ch465003_lm4 ch465003_em4 ch465003_bm4)
      (MS (by omega) ch465003_bm4) ch465003_ls ch465003_lm4 ch465003_orb4 ch465003_sub4
      ch465003_res4 ch465003_sx4 ch465003_st4 ch465003_cw4
      ch465003_len.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl ch465003_cn.2.2.2.2.1
  · exact aSixData_of_checks gS (gM (by omega) ch465003_lm5 ch465003_em5 ch465003_bm5)
      (MS (by omega) ch465003_bm5) ch465003_ls ch465003_lm5 ch465003_orb5 ch465003_sub5
      ch465003_res5 ch465003_sx5 ch465003_st5 ch465003_cw5
      ch465003_len.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 rfl ch465003_cn.2.2.2.2.2

theorem W_le (r : Equiv.Perm (Fin 42)) :
    Subgroup.closure {pp 42 6 63 (lane 252 pm252 LP 0), pp 42 6 63 (lane 252 pm252 LP 2), r} ≤
      closureTabs pGens ⊔ Subgroup.zpowers r := by
  refine (Subgroup.closure_le _).2 ?_
  rintro g (rfl | rfl | rfl)
  · exact Subgroup.mem_sup_left (mem_closureTabs (j := 0) (by decide) tp)
  · exact Subgroup.mem_sup_left (mem_closureTabs (j := 1) (by decide) tq)
  · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers g)

theorem S_le {r : Equiv.Perm (Fin 42)}
    (hz : pp 42 6 63 (lane 252 pm252 TG 0) ∈
      Subgroup.closure {pp 42 6 63 (lane 252 pm252 LP 0), pp 42 6 63 (lane 252 pm252 LP 2), r}) :
    closureTabs gensS ≤
      Subgroup.closure {pp 42 6 63 (lane 252 pm252 LP 0), pp 42 6 63 (lane 252 pm252 LP 2), r} := by
  have hZ : gen 42 6 63 (lane 252 pm252 LZ) 3 ≤
      Subgroup.closure {pp 42 6 63 (lane 252 pm252 LP 0), pp 42 6 63 (lane 252 pm252 LP 2), r} := by
    refine gen_le fun j hj => ?_
    interval_cases j
    · change pp 42 6 63 (lane 252 pm252 LZ 0) ∈ _
      rw [ch465003_ez.1]
      exact Subgroup.subset_closure (Set.mem_insert _ _)
    · change pp 42 6 63 (lane 252 pm252 LZ 2) ∈ _
      rw [ch465003_ez.2.1]
      exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
    · change pp 42 6 63 (lane 252 pm252 LZ 4) ∈ _
      rw [ch465003_ez.2.2]
      exact hz
  have h := wordsK_sound (ng := 3) hLZ ch465003_zw
  rw [gS]
  refine gen_le fun j hj => hZ ?_
  have := (h j (by rw [ch465003_len.2.2.2.2.2.2.1]; omega)).2
  simpa using this

theorem target_le {r tg : ℕ} (htg : tg < 7) (hp : PermN 42 6 63 (lane 252 pm252 TG tg))
    (hm : pp 42 6 63 (lane 252 pm252 TG tg) ∈ Subgroup.closure
      {pp 42 6 63 (lane 252 pm252 LP 0), pp 42 6 63 (lane 252 pm252 LP 2), pp 42 6 63 r}) :
    closureTabs gensS ≤ closureTabs pGens ⊔ Subgroup.zpowers (pp 42 6 63 r) ∨
      ∃ j < 6, closureTabs (pGensWith mRs[j]!) ≤ closureTabs pGens ⊔ Subgroup.zpowers (pp 42 6 63 r) := by
  have hW := W_le (pp 42 6 63 r)
  have hM : ∀ j < 6, tabEqB mRs[j]! (lane 252 pm252 TG (j + 1)) = true → tg = j + 1 →
      closureTabs (pGensWith mRs[j]!) ≤ closureTabs pGens ⊔ Subgroup.zpowers (pp 42 6 63 r) := by
    intro j hj hb he
    subst he
    refine le_trans (closureTabs_le fun k hk => ?_) hW
    rw [pGensWith_size] at hk
    interval_cases k
    · exact ⟨_, Subgroup.subset_closure (Set.mem_insert _ _), by rw [pGensWith_zero]; exact tp⟩
    · exact ⟨_, Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _)),
        by rw [pGensWith_one]; exact tq⟩
    · exact ⟨_, hm, by rw [pGensWith_two]; exact tabRep_pp hp hb⟩
  interval_cases tg
  · exact Or.inl ((S_le hm).trans hW)
  · exact Or.inr ⟨0, by omega, hM 0 (by omega) ch465003_bm0 rfl⟩
  · exact Or.inr ⟨1, by omega, hM 1 (by omega) ch465003_bm1 rfl⟩
  · exact Or.inr ⟨2, by omega, hM 2 (by omega) ch465003_bm2 rfl⟩
  · exact Or.inr ⟨3, by omega, hM 3 (by omega) ch465003_bm3 rfl⟩
  · exact Or.inr ⟨4, by omega, hM 4 (by omega) ch465003_bm4 rfl⟩
  · exact Or.inr ⟨5, by omega, hM 5 (by omega) ch465003_bm5 rfl⟩

theorem pow5 : PowFacts 5 RT5 224 := powsK_sound (by norm_num) ch465003_pow5

theorem pow7 : PowFacts 7 RT7 112 := powsK_sound (by norm_num) ch465003_pow7

theorem rep5S : ∀ i < 224, pp 42 6 63 (lane 252 pm252 RT5 ((5 - 1) * i)) ∈ closureTabs gensS := by
  intro i hi
  have h := wordsK_sound (ng := 3) hLS ch465003_mem5
  rw [gS]
  have := (h i (by rw [ch465003_len.1]; omega)).2
  simpa using this

theorem rep7S : ∀ i < 112, pp 42 6 63 (lane 252 pm252 RT7 ((7 - 1) * i)) ∈ closureTabs gensS := by
  intro i hi
  have h := wordsK_sound (ng := 3) hLS ch465003_mem7
  rw [gS]
  have := (h i (by rw [ch465003_len.2.1]; omega)).2
  simpa using this

theorem rowHyp {p RT cnt : ℕ} (hp : 2 ≤ p) (hpow : PowFacts p RT cnt) :
    ∀ k < cnt, PermN 42 6 63 (lane 252 pm252 RT ((p - 1) * (0 + k))) ∧
      PermN 42 6 63 (lane 252 pm252 RT ((p - 1) * (0 + k) + (p - 2))) ∧
      pp 42 6 63 (lane 252 pm252 RT ((p - 1) * (0 + k) + (p - 2))) =
        (pp 42 6 63 (lane 252 pm252 RT ((p - 1) * (0 + k))))⁻¹ := by
  intro k hk
  rw [Nat.zero_add]
  obtain ⟨hk1, hrp, -⟩ := hpow k hk
  have h0 := hk1 0 (by omega)
  have hl := hk1 (p - 2) (by omega)
  rw [Nat.add_zero] at h0
  refine ⟨h0.1, hl.1, ?_⟩
  rw [hl.2]
  apply eq_inv_of_mul_eq_one_left
  rw [← pow_succ, show p - 2 + 1 + 1 = p by omega, hrp]

theorem chunk {p : ℕ} [Fact p.Prime] {RT cnt hi lo : ℕ} {L : List (ℕ × ℕ)} (hp2 : 2 ≤ p)
    (hpow : PowFacts p RT cnt)
    (hrepS : ∀ i < cnt, pp 42 6 63 (lane 252 pm252 RT ((p - 1) * i)) ∈ closureTabs gensS)
    (h : recsK 42 6 63 252 pm252 p 9 ((p - 1) * cnt) PT RT hi L lo = true) :
    (L.map Prod.fst).Pairwise (· < ·) ∧ ∀ x ∈ L.map Prod.fst, lo < x ∧ x ≤ hi ∧ RecOK p RT cnt x := by
  obtain ⟨hpw, hall⟩ := recFacts hp2 hPS hPT hpow hrepS h
  refine ⟨hpw, fun x hx => ?_⟩
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hall e he
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

theorem keys : K5A ≤ K5B ∧ K5B ≤ K5C ∧ K5C ≤ K5D ∧ K7A ≤ K7B := by decide +kernel

theorem lists {p RT cnt lo hi : ℕ} [Fact p.Prime] {T : Subgroup (Equiv.Perm (Fin 42)) → Prop}
    {K : List ℕ} (hK : K.Pairwise (· < ·) ∧ ∀ x ∈ K, lo < x ∧ x ≤ hi ∧ RecOK p RT cnt x)
    (hpowOf : ∀ i < cnt, pp 42 6 63 (lane 252 pm252 RT ((p - 1) * i)) ^ p = 1)
    (hT : ∀ i < cnt, T (closureTabs pGens ⊔
      Subgroup.zpowers (pp 42 6 63 (lane 252 pm252 RT ((p - 1) * i))))) :
    (∀ X ∈ K.map (pp 42 6 63), X ∈ closureTabs gensS ∧ X ≠ 1 ∧ X ^ p = 1) ∧
    (K.map (pp 42 6 63)).Pairwise (fun X Y => Subgroup.zpowers X ≠ Subgroup.zpowers Y) ∧
    ∀ X ∈ K.map (pp 42 6 63), ∃ c ∈ closureTabs pGens, ∃ r : Equiv.Perm (Fin 42), r ^ p = 1 ∧
      c⁻¹ * X * c ∈ Subgroup.zpowers r ∧ T (closureTabs pGens ⊔ Subgroup.zpowers r) := by
  refine ⟨fun X hX => ?_, pairwise_zpowers_ne (p := p) hK.1 fun x hx => ?_, fun X hX => ?_⟩
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hX
    obtain ⟨-, -, -, -, h5, h6, h7, -⟩ := (hK.2 x hx).2.2
    exact ⟨h5, h6, h7⟩
  · obtain ⟨h1, h2, h3, h4, -⟩ := (hK.2 x hx).2.2
    exact ⟨h1, h2, h3, h4⟩
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hX
    obtain ⟨-, -, -, -, -, -, -, c, hc, i, hi, hci⟩ := (hK.2 x hx).2.2
    exact ⟨c, hc, _, (hpowOf i hi), hci, hT i hi⟩

theorem T5 : ∀ i < 224, closureTabs gensS ≤ closureTabs pGens ⊔
      Subgroup.zpowers (pp 42 6 63 (lane 252 pm252 RT5 ((5 - 1) * i))) ∨
    ∃ j < 6, closureTabs (pGensWith mRs[j]!) ≤ closureTabs pGens ⊔
      Subgroup.zpowers (pp 42 6 63 (lane 252 pm252 RT5 ((5 - 1) * i))) := by
  intro i hi
  have hrows := rowsK_sound (i := 0) hLP (fun k hk => rowHyp (by norm_num) pow5 k
    (by rw [ch465003_len.2.2.1] at hk; exact hk)) ch465003_row5
  obtain ⟨tg, htg, hp, hm⟩ := hrows i (by rw [ch465003_len.2.2.1]; exact hi)
  rw [Nat.zero_add] at hm
  exact target_le htg hp hm

theorem T7 : ∀ i < 112, closureTabs gensS ≤ closureTabs pGens ⊔
      Subgroup.zpowers (pp 42 6 63 (lane 252 pm252 RT7 ((7 - 1) * i))) := by
  intro i hi
  have hrows := rowsK_sound (i := 0) hLP (fun k hk => rowHyp (by norm_num) pow7 k
    (by rw [ch465003_len.2.2.2.1] at hk; exact hk)) ch465003_row7
  obtain ⟨tg, htg, -, hm⟩ := hrows i (by rw [ch465003_len.2.2.2.1]; exact hi)
  obtain rfl : tg = 0 := by omega
  rw [Nat.zero_add] at hm
  exact (S_le hm).trans (W_le _)

theorem K5 : (REC5A.map Prod.fst ++ REC5B.map Prod.fst ++ REC5C.map Prod.fst ++
      REC5D.map Prod.fst).Pairwise (· < ·) ∧
    ∀ x ∈ REC5A.map Prod.fst ++ REC5B.map Prod.fst ++ REC5C.map Prod.fst ++ REC5D.map Prod.fst,
      0 < x ∧ x ≤ K5D ∧ RecOK 5 RT5 224 x :=
  chunk_append (chunk_append (chunk_append
    (chunk (p := 5) (cnt := 224) (by norm_num) pow5 rep5S ch465003_rec5a)
    (chunk (p := 5) (cnt := 224) (by norm_num) pow5 rep5S ch465003_rec5b) keys.1 (Nat.zero_le _))
    (chunk (p := 5) (cnt := 224) (by norm_num) pow5 rep5S ch465003_rec5c) keys.2.1
      (Nat.zero_le _))
    (chunk (p := 5) (cnt := 224) (by norm_num) pow5 rep5S ch465003_rec5d) keys.2.2.1
      (Nat.zero_le _)

theorem K7 : (REC7A.map Prod.fst ++ REC7B.map Prod.fst).Pairwise (· < ·) ∧
    ∀ x ∈ REC7A.map Prod.fst ++ REC7B.map Prod.fst, 0 < x ∧ x ≤ K7B ∧ RecOK 7 RT7 112 x :=
  chunk_append
    (chunk (p := 7) (cnt := 112) (by norm_num) pow7 rep7S ch465003_rec7a)
    (chunk (p := 7) (cnt := 112) (by norm_num) pow7 rep7S ch465003_rec7b) keys.2.2.2
      (Nat.zero_le _)

public theorem certificate465003 : Facts465003 := by
  obtain ⟨-, -, -, -, -, -, -, h5a, h5b, h5c, h5d, h7a, h7b, -⟩ := ch465003_len
  obtain ⟨h5L, h5nd, h5r⟩ := lists (T := fun Y => closureTabs CFSG.PSL3Four.Native.gensS ≤ Y ∨
    ∃ j < 6, closureTabs (pGensWith mRs[j]!) ≤ Y) K5 (fun i hi => (pow5 i hi).2.1) T5
  obtain ⟨h7L, h7nd, h7r⟩ := lists (T := fun Y => closureTabs CFSG.PSL3Four.Native.gensS ≤ Y) K7
    (fun i hi => (pow7 i hi).2.1) T7
  exact certificate465003_of_lists hcardS hP9 hPS aSix _
    (by simp [h5a, h5b, h5c, h5d]) h5L h5nd h5r _ (by simp [h7a, h7b]) h7L h7nd h7r

end Certificates
