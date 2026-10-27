module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8IotaDat
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8IotaGood
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8Def
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP7Card
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP7Gen

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open U42F431
open CFSG.Quasithin.H13.F431.U42 (P45 L0S image_lineSet lineSet_eq_of_sameSet sameSet_of_lineSet_eq)

theorem memB_iff {g : Ah} {l : PL} (h : RepL l (g : P45)) : g ∈ Bh ↔ memB l = true := by
  have hg0 : l.getD 0 0 = ((g : P45) 0 : ℕ) := h.2 0
  have h1 : g ∈ P1h ↔ l.getD 0 0 = 0 := by
    rw [mem_P1h_iff, hg0, ← Fin.val_inj]
    rfl
  have h2 : g ∈ P2h ↔ sameSet (imgSet l L0) L0 = true := by
    rw [mem_P2h_iff, L0S, image_lineSet h (by decide)]
    exact ⟨sameSet_of_lineSet_eq, lineSet_eq_of_sameSet⟩
  rw [Subgroup.mem_inf, h1, h2]
  simp [memB]

theorem repL_conj {r x : Ah} {lr lx : PL} (hr : RepL lr (r : P45)) (hx : RepL lx (x : P45)) :
    RepL (conjL lr lx) ((r * x * r : Ah) : P45) := by
  have := repL_mul hr (repL_mul hx hr)
  rw [← mul_assoc] at this
  exact this

theorem repL_powL' {σ : P45} {l : PL} (h : RepL l σ) (n : ℕ) : RepL (powL l n) (σ ^ n) := by
  induction n with
  | zero => exact repL_one 45
  | succ n ih =>
    rw [pow_succ']
    exact repL_mul h ih

theorem mul_self_of_comp {g : Ah} {l : PL} (h : RepL l (g : P45)) (hl : comp l l = idL) :
    g * g = 1 :=
  eq_of_repL_eq (repL_mul h h) (repL_one 45) hl

theorem uGood_of_chk {s t u : Ah} {ls lt lu : PL} (hs : RepL ls (s : P45)) (ht : RepL lt (t : P45))
    (hu : RepL lu (u : P45)) (h : chkU ls lt lu = true) : UGood s t u := by
  unfold UGood
  simp only [chkU, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  have e1 := repL_conj ht hu
  have e2 := repL_conj hs e1
  have e3 := repL_conj ht e2
  have e4 := repL_conj hs hu
  refine ⟨mul_self_of_comp hu h1, (memB_iff hu).2 h2, (memB_iff e1).2 h3, (memB_iff e2).2 h4,
    (memB_iff e3).2 h5, fun hmem => ?_⟩
  have := (memB_iff e4).1 hmem
  rw [h6] at this
  exact absurd this (by simp)

theorem wGood_of_chk {s t w : Ah} {ls lt lw : PL} (hs : RepL ls (s : P45)) (ht : RepL lt (t : P45))
    (hw : RepL lw (w : P45)) (h : chkW ls lt lw = true) : WGood s t w := by
  unfold WGood
  simp only [chkW, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  have e1 := repL_conj hs hw
  have e2 := repL_conj ht e1
  have e3 := repL_conj hs e2
  have e4 := repL_conj ht hw
  refine ⟨mul_self_of_comp hw h1, (memB_iff hw).2 h2, (memB_iff e1).2 h3, (memB_iff e2).2 h4,
    (memB_iff e3).2 h5, fun hmem => ?_⟩
  have := (memB_iff e4).1 hmem
  rw [h6] at this
  exact absurd this (by simp)

theorem repL_mem_Dl1 :
    ∀ g ∈ P1h ⊓ Subgroup.centralizer ({fhatA} : Set Ah), ∃ l ∈ Dl1, RepL l (g : P45) :=
  rep_mem_D D1w Dl1 Dl1_eq (fun w hw => mem_P1h_of_repL (repL_aW w) (D1_check.2.2.1 w hw))
    D1_check.2.2.2 D1_check.1 card_C1 D1_check.2.1

theorem repL_mem_Dl2 :
    ∀ g ∈ P2h ⊓ Subgroup.centralizer ({fhatA} : Set Ah), ∃ l ∈ Dl2, RepL l (g : P45) :=
  rep_mem_D D2w Dl2 Dl2_eq (fun w hw => mem_P2h_of_repL (repL_aW w) (D2_check.2.2.1 w hw))
    D2_check.2.2.2 D2_check.1 card_C2 D2_check.2.1

theorem exists_ahBN {s t : Ah}
    (h : IsCoxPair s t) : ∃ us ut : List Ah, AhBN s t us ut := by
  obtain ⟨hs1, hs3, hs2, ht1, ht3, ht2, h4, -⟩ := h
  have hsP1 : s ∈ P1h := hs1.1.1
  have htP2 : t ∈ P2h := ht1.1.1
  have hss : s * s = 1 := by rw [← pow_two]; exact hs2
  have htt : t * t = 1 := by rw [← pow_two]; exact ht2
  obtain ⟨l, hl, hls⟩ := repL_mem_Dl1 s ⟨hsP1, hs1.2⟩
  obtain ⟨m, hm, hmt⟩ := repL_mem_Dl2 t ⟨htP2, ht1.2⟩
  have hcond : ∀ {g : Ah} {k : PL}, RepL k (g : P45) → g * g = 1 → g ∉ Bh → condS k = true := by
    intro g k hk hgg hgB
    simp only [condS, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true']
    have hmb : ¬ memB k = true := fun hmem => hgB ((memB_iff hk).2 hmem)
    refine ⟨repL_unique (repL_mul hk hk) ?_, by simpa using hmb⟩
    have : RepL idL ((g * g : Ah) : P45) := by rw [hgg]; exact repL_one 45
    exact this
  have hpow : powL (comp l m) 4 = idL := by
    have h1 : RepL (powL (comp l m) 4) (((s * t : Ah) : P45) ^ 4) :=
      repL_powL' (repL_mul hls hmt) 4
    have h2 : RepL idL (((s * t : Ah) : P45) ^ 4) := by
      have : (((s * t : Ah) : P45) ^ 4) = 1 := by
        have := congrArg Subtype.val h4
        simpa using this
      rw [this]
      exact repL_one 45
    exact repL_unique h1 h2
  obtain ⟨e, he, hel, hem⟩ := pairTable_complete l hl (hcond hls hss hs3) m hm
    (hcond hmt htt ht3) hpow
  have hchk := List.all_eq_true.1 pairTable_check e he
  obtain ⟨hb1, hb2, hb3, hb4⟩ := pairTable_idx e he
  obtain ⟨u, huT, hu⟩ := exists_That_of_mem_Thl (getD_mem_Thl hb1)
  obtain ⟨w₁, hw₁T, hw₁⟩ := exists_That_of_mem_Thl (getD_mem_Thl hb2)
  obtain ⟨w₂, hw₂T, hw₂⟩ := exists_That_of_mem_Thl (getD_mem_Thl hb3)
  obtain ⟨w₃, hw₃T, hw₃⟩ := exists_That_of_mem_Thl (getD_mem_Thl hb4)
  simp only [chkE, hel, hem, Bool.and_eq_true, Bool.not_eq_true'] at hchk
  obtain ⟨⟨⟨⟨⟨⟨hU, hW1⟩, hW2⟩, hW3⟩, hp12⟩, hp13⟩, hp23⟩ := hchk
  have hpair : ∀ {a b : Ah} {la lb : PL}, RepL la (a : P45) → RepL lb (b : P45) →
      memB (conjL m (comp la lb)) = false → t * (a * b) * t ∉ Bh := by
    intro a b la lb ha hb hmem hmemB
    have := (memB_iff (repL_conj hmt (repL_mul ha hb))).1 hmemB
    change memB (conjL m (comp la lb)) = true at this
    rw [hmem] at this
    exact absurd this (by simp)
  exact ⟨_, _, ahBN_of_good hsP1 hss hs3 htP2 htt ht3 h4 (uGood_of_chk hls hmt hu hU)
    (wGood_of_chk hls hmt hw₁ hW1) (wGood_of_chk hls hmt hw₂ hW2) (wGood_of_chk hls hmt hw₃ hW3)
    (hpair hw₁ hw₂ hp12) (hpair hw₁ hw₃ hp13) (hpair hw₂ hw₃ hp23)⟩

end CFSG.Quasithin.H13.F431.U42Aut
