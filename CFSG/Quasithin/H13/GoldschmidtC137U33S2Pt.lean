module

public import CFSG.Quasithin.H13.GoldschmidtC137U33S2Cls
public import CFSG.Quasithin.H13.GoldschmidtC137U33S2PtGen

public section

namespace CFSG.Quasithin.H13.U3.GC137.S2

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.Orbit
  CFSG.Quasithin.H13.G2Dat

theorem cls_cnt_Q : ∀ e < 8, (∀ l ∈ sE8.getD e [], ∃ k < 32, l = 2 * k) →
    8 ≤ cntQ (sE8.getD e []) → e = 2 := by
  decide +kernel

theorem cls_cnt_O : ∀ e < 8, (∀ l ∈ sE8.getD e [], ∃ k < 32, l = 2 * k) →
    16 ≤ cntO (sE8.getD e []) → e = 2 := by
  decide +kernel

theorem sE8_two : sE8.getD 2 [] = Alist := by
  decide

theorem CR_Q : ∀ k < 32, (∀ c ∈ o0Codes, (∀ i ∈ Alist, fixQB (sM i) c = true) →
    fixQB (sM (2 * k)) c = true) → 2 * k ∈ Alist := by
  decide +kernel

theorem CR_O : ∀ k < 32, (∀ c ∈ o0Codes, (∀ i ∈ Alist, fixOB (sM i) c = true) →
    fixOB (sM (2 * k)) c = true) → 2 * k ∈ Alist := by
  decide +kernel

theorem eq_Asub_of_idx {B : Subgroup Gam} (hB : B ≤ sSubG) (h : ∀ l, l ∈ idx B ↔ l ∈ Alist) :
    B = Asub := by
  refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
  · obtain ⟨i, hi, rfl⟩ := mem_sSubG.1 (hB hx)
    exact ⟨i, (h i).1 (mem_idx.2 ⟨hi, hx⟩), rfl⟩
  · obtain ⟨i, hi, rfl⟩ := hx
    exact (mem_idx.1 ((h i).2 hi)).2

theorem even_of_mem_idx {B : Subgroup Gam} (hB : B ≤ Rsub) {i : ℕ} (hi : i ∈ idx B) :
    ∃ k < 32, i = 2 * k := by
  obtain ⟨hi64, hmem⟩ := mem_idx.1 hi
  obtain ⟨k, hk, hik⟩ := hB hmem
  exact ⟨k, hk, sEltG_injective hi64 (by omega) hik⟩

theorem act_codeQ_iff {i : ℕ} (hi : i < 64) (c : O0C) :
    g2QAct (ZMod 2) (sEltG i) (codeQ c) = codeQ c ↔ fixQB (sM i) c.1 = true := by
  rw [g2QAct_codeQ, eq_comm, codeQ_eq_iff, o0Act_sEltG hi]
  have hm : mact (sM i) c.1 ∈ o0Codes := by
    rw [← o0Act_sEltG hi]
    exact (o0Act (sEltG i) c).2
  exact (fixQB_iff (sM i) c.2 hm).symm

theorem act_codeO_iff {i : ℕ} (hi : i < 64) (c : O0C) :
    g2OAct (ZMod 2) (sEltG i) (codeO c) = codeO c ↔ fixOB (sM i) c.1 = true := by
  rw [g2OAct_codeO]
  constructor
  · intro h
    have := congrArg Subtype.val (codeO_injective h)
    rw [o0Act_sEltG hi] at this
    simp [fixOB, this]
  · intro h
    congr 1
    apply Subtype.ext
    rw [o0Act_sEltG hi]
    simpa [fixOB] using h

end CFSG.Quasithin.H13.U3.GC137.S2

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.Orbit
  CFSG.Quasithin.H13.G2Dat CFSG.Quasithin.H13.U3.GC137.S2

theorem rk_A_Q : rkIdx (fixV (Asub.map (g2QAct (ZMod 2)))) = 3 := by
  have h := rkIdx_of_cards (fixV (Asub.map (g2QAct (ZMod 2)))) (a := 3) (b := 6)
    (by rw [card_ModQ]; norm_num)
    (by rw [card_fixV_Q_lst (le_refl Asub), lst_Asub, cntQ_A]; norm_num)
  exact h

theorem hff_Q : ∀ B : Subgroup (MulAut ModQ), B ≤ Asub.map (g2QAct (ZMod 2)) →
    Nat.card ↥B * Nat.card ↥(fixV B) ≤
      Nat.card ↥(Asub.map (g2QAct (ZMod 2))) * Nat.card ↥(fixV (Asub.map (g2QAct (ZMod 2)))) := by
  intro B hB
  set B' : Subgroup Gam := B.comap (g2QAct (ZMod 2)) with hB'
  have hBB : B'.map (g2QAct (ZMod 2)) = B :=
    Subgroup.map_comap_eq_self (hB.trans (Subgroup.map_le_range _ _))
  have hB'A : B' ≤ Asub := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hB hx
    rwa [← g2QAct_injective hyx]
  rw [← hBB, Subgroup.card_map_of_injective g2QAct_injective, card_lst hB'A,
    card_fixV_Q_lst hB'A, Subgroup.card_map_of_injective g2QAct_injective, card_Asub,
    card_fixV_Q_lst (le_refl Asub), lst_Asub]
  have := subA_Q (lst B') (lst_sublist B')
  omega

theorem hcls_Q : ∀ B : Subgroup Gam, B ≤ Rsub → B ≠ ⊥ → IsElemAbelian2 (B.map (g2QAct (ZMod 2))) →
    Nat.card ModQ ≤ Nat.card ↥(B.map (g2QAct (ZMod 2))) *
      Nat.card ↥(fixV (B.map (g2QAct (ZMod 2)))) → B = Asub := by
  intro B hBR hB1 hBe hff
  have hBS : B ≤ sSubG := hBR.trans Rsub_le_S
  have hc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := fun a ha b hb =>
    g2QAct_injective (by rw [map_mul, map_mul]; exact hBe.1 _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩)
  have h2 : ∀ b ∈ B, b ^ 2 = 1 := fun b hb =>
    g2QAct_injective (by rw [map_pow, map_one]; exact hBe.2 _ ⟨b, hb, rfl⟩)
  rw [Subgroup.card_map_of_injective g2QAct_injective, card_eq_idx hBS, card_ModQ] at hff
  obtain ⟨e, he, hiff, hcnt⟩ := cls_Q hBS hB1 hc h2 hff
  have hev : ∀ l ∈ sE8.getD e [], ∃ k < 32, l = 2 * k := fun l hl =>
    even_of_mem_idx hBR ((hiff l).2 hl)
  have he2 := cls_cnt_Q e he hev hcnt
  subst he2
  exact eq_Asub_of_idx hBS fun l => by rw [hiff l, sE8_two]

theorem hCR_Q : ∀ r ∈ Rsub, (∀ w ∈ fixV (Asub.map (g2QAct (ZMod 2))),
    g2QAct (ZMod 2) r w = w) → r ∈ Asub := by
  rintro _ ⟨k, hk, rfl⟩ h
  have h64 : 2 * k < 64 := by omega
  have hall : ∀ c ∈ o0Codes, (∀ i ∈ Alist, fixQB (sM i) c = true) →
      fixQB (sM (2 * k)) c = true := by
    intro c hc hfix
    have hmem : codeQ ⟨c, hc⟩ ∈ fixV (Asub.map (g2QAct (ZMod 2))) := by
      rw [mem_fixV_codeQ Asub_le_S]
      intro i hi
      exact hfix i (mem_idx_Asub.1 hi)
    exact (act_codeQ_iff h64 ⟨c, hc⟩).1 (h _ hmem)
  obtain ⟨i, hi, hik⟩ : ∃ i ∈ Alist, i = 2 * k := ⟨2 * k, CR_Q k hk hall, rfl⟩
  exact ⟨i, hi, by rw [hik]⟩

theorem g2Point_Q : G2Point (g2QAct (ZMod 2)).range
    ((g2Derived (ZMod 2)).map (g2QAct (ZMod 2))) (Ppt.map (g2QAct (ZMod 2))) :=
  g2Point_of _ g2QAct_injective rk_A_Q hff_Q hcls_Q hCR_Q

theorem rk_A_O : rkIdx (fixV (Asub.map (g2OAct (ZMod 2)))) = 3 := by
  have h := rkIdx_of_cards (fixV (Asub.map (g2OAct (ZMod 2)))) (a := 4) (b := 7)
    (by rw [card_ModO]; norm_num)
    (by rw [card_fixV_O_lst (le_refl Asub), lst_Asub, cntO_A]; norm_num)
  exact h

theorem hff_O : ∀ B : Subgroup (MulAut ModO), B ≤ Asub.map (g2OAct (ZMod 2)) →
    Nat.card ↥B * Nat.card ↥(fixV B) ≤
      Nat.card ↥(Asub.map (g2OAct (ZMod 2))) * Nat.card ↥(fixV (Asub.map (g2OAct (ZMod 2)))) := by
  intro B hB
  set B' : Subgroup Gam := B.comap (g2OAct (ZMod 2)) with hB'
  have hBB : B'.map (g2OAct (ZMod 2)) = B :=
    Subgroup.map_comap_eq_self (hB.trans (Subgroup.map_le_range _ _))
  have hB'A : B' ≤ Asub := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hB hx
    rwa [← g2OAct_injective hyx]
  rw [← hBB, Subgroup.card_map_of_injective g2OAct_injective, card_lst hB'A,
    card_fixV_O_lst hB'A, Subgroup.card_map_of_injective g2OAct_injective, card_Asub,
    card_fixV_O_lst (le_refl Asub), lst_Asub]
  have := subA_O (lst B') (lst_sublist B')
  omega

theorem hcls_O : ∀ B : Subgroup Gam, B ≤ Rsub → B ≠ ⊥ → IsElemAbelian2 (B.map (g2OAct (ZMod 2))) →
    Nat.card ModO ≤ Nat.card ↥(B.map (g2OAct (ZMod 2))) *
      Nat.card ↥(fixV (B.map (g2OAct (ZMod 2)))) → B = Asub := by
  intro B hBR hB1 hBe hff
  have hBS : B ≤ sSubG := hBR.trans Rsub_le_S
  have hc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := fun a ha b hb =>
    g2OAct_injective (by rw [map_mul, map_mul]; exact hBe.1 _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩)
  have h2 : ∀ b ∈ B, b ^ 2 = 1 := fun b hb =>
    g2OAct_injective (by rw [map_pow, map_one]; exact hBe.2 _ ⟨b, hb, rfl⟩)
  rw [Subgroup.card_map_of_injective g2OAct_injective, card_eq_idx hBS, card_ModO] at hff
  obtain ⟨e, he, hiff, hcnt⟩ := cls_O hBS hB1 hc h2 hff
  have hev : ∀ l ∈ sE8.getD e [], ∃ k < 32, l = 2 * k := fun l hl =>
    even_of_mem_idx hBR ((hiff l).2 hl)
  have he2 := cls_cnt_O e he hev hcnt
  subst he2
  exact eq_Asub_of_idx hBS fun l => by rw [hiff l, sE8_two]

theorem hCR_O : ∀ r ∈ Rsub, (∀ w ∈ fixV (Asub.map (g2OAct (ZMod 2))),
    g2OAct (ZMod 2) r w = w) → r ∈ Asub := by
  rintro _ ⟨k, hk, rfl⟩ h
  have h64 : 2 * k < 64 := by omega
  have hall : ∀ c ∈ o0Codes, (∀ i ∈ Alist, fixOB (sM i) c = true) →
      fixOB (sM (2 * k)) c = true := by
    intro c hc hfix
    have hmem : codeO ⟨c, hc⟩ ∈ fixV (Asub.map (g2OAct (ZMod 2))) := by
      rw [mem_fixV_codeO Asub_le_S]
      intro i hi
      exact hfix i (mem_idx_Asub.1 hi)
    exact (act_codeO_iff h64 ⟨c, hc⟩).1 (h _ hmem)
  obtain ⟨i, hi, hik⟩ : ∃ i ∈ Alist, i = 2 * k := ⟨2 * k, CR_O k hk hall, rfl⟩
  exact ⟨i, hi, by rw [hik]⟩

theorem g2Point_O : G2Point (g2OAct (ZMod 2)).range
    ((g2Derived (ZMod 2)).map (g2OAct (ZMod 2))) (Ppt.map (g2OAct (ZMod 2))) :=
  g2Point_of _ g2OAct_injective rk_A_O hff_O hcls_O hCR_O

end CFSG.Quasithin.H13.U3.GC137
