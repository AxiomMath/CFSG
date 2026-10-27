module

public import Certificates.Kernel.Co2Cen.GlueBase
public import Certificates.Kernel.Co2Cen.Scan1
public import Certificates.Kernel.Co2Cen.Cent
public import Certificates.Kernel.Co2Cen.Img
public import Certificates.Kernel.Co2Cen.Tree
public import Certificates.Kernel.Co2JRank.Facts
public import CFSG.Certificates.Kernel.Co2Cen.Glue

public section

namespace CertificateChecks.KernelSpor.Co2Cen

open CFSG.KC.Co2InvS CFSG.KC.Co2Syl CFSG.KC.Co2Cls CFSG.KC.Co2J CFSG.KC.Co2Cen CFSG.KC.Co2JRank
  CFSG.KC.TabMatGrp CertificateChecks.KernelSpor.Co2Syl CertificateChecks.KernelSpor.Co2TInv
  CFSG.RankThree.Co2

local notation "M22" => Matrix (Fin 22) (Fin 22) (ZMod 2)

theorem W_eq : genMon Co2JRank.WG = matGrp wGenWords :=
  genMon_five rfl Co2JRank.wGenWords_lt Co2JRank.wGens

theorem WGx_eq {i : ℕ} (hi : i < 5) : WGx i = Co2JRank.WG i := by
  unfold WGx
  rw [selN_eq, if_pos (blt_iff.2 hi)]

theorem wg_sq : ∀ i < 5, MatP 22 (Co2JRank.WG i) * MatP 22 (Co2JRank.WG i) = 1 := fun i hi => by
  rw [← WGx_eq hi]
  exact (jGen_sound wGen).1 i (by omega)

theorem wg_comm : ∀ i < 5, ∀ j < 5, Commute (MatP 22 (Co2JRank.WG i)) (MatP 22 (Co2JRank.WG j)) :=
  fun i hi j hj => by
    rw [← WGx_eq hi, ← WGx_eq hj]
    exact (jGen_sound wGen).2 i (by omega) j (by omega)

theorem wMat_xP : wMat = xP (fun i => MatP 22 (Co2JRank.WG i)) 5 :=
  funext fun u => Co2JRank.wMat_eq u

theorem mem_W {x : M22} : x ∈ matGrp wGenWords ↔ ∃ u < 32, wMat u = x := by
  rw [← W_eq, ← genMonN_five, mem_genJ wg_comm wg_sq, wMat_xP]
  rfl

theorem wMat_mem (u : ℕ) : wMat u ∈ matGrp wGenWords := by
  rw [← W_eq, wMat_xP]
  exact xP_mem _ 5 u fun i hi => gen_mem _ hi

theorem wMat_xor (s t : ℕ) : wMat (s ^^^ t) = wMat s * wMat t := by
  have h := @xP_xor M22 _ (fun i => MatP 22 (Co2JRank.WG i)) 5
  rw [wMat_xP]
  exact h wg_comm wg_sq s t

theorem wMat_zero : wMat 0 = 1 := by
  rw [wMat_xP]
  exact xP_zero _ 5

theorem wMat_gen {k : ℕ} (hk : k < 5) : wMat (2 ^ k) = MatP 22 (Co2JRank.WG k) := by
  rw [wMat_xP]
  exact xP_two_pow _ 5 k hk

theorem wMat_one : wMat 1 = repMat 1 := by
  have h := wMat_gen (k := 0) (by norm_num)
  rw [pow_zero, Co2JRank.MatP_WG (by norm_num)] at h
  rw [h]
  rfl

theorem wMat_two : wMat 2 = repMat 0 := by
  have h := wMat_gen (k := 1) (by norm_num)
  rw [pow_one, Co2JRank.MatP_WG (by norm_num)] at h
  rw [h]
  rfl

theorem wMat_inj {s t : ℕ} (hs : s < 32) (ht : t < 32) (e : wMat s = wMat t) : s = t := by
  have hne : ∀ u, 0 < u → u < 2 ^ 5 → xP (fun i => MatP 22 (Co2JRank.WG i)) 5 u ≠ 1 :=
    fun u hu hu' => by
      rw [← wMat_xP]
      exact Co2JRank.wRankFacts.ne_one u hu hu'
  have h := @xP_injOn M22 _ (fun i => MatP 22 (Co2JRank.WG i)) 5
  rw [wMat_xP] at e
  exact h wg_comm wg_sq hne hs ht e

theorem w_comm {x y : M22} (hx : x ∈ matGrp wGenWords) (hy : y ∈ matGrp wGenWords) :
    x * y = y * x := by
  obtain ⟨s, -, rfl⟩ := mem_W.1 hx
  obtain ⟨t, -, rfl⟩ := mem_W.1 hy
  rw [← wMat_xor, ← wMat_xor, Nat.xor_comm]

theorem w_sq {x : M22} (hx : x ∈ matGrp wGenWords) : x * x = 1 := by
  obtain ⟨s, -, rfl⟩ := mem_W.1 hx
  rw [← wMat_xor, Nat.xor_self, wMat_zero]

theorem card_W : Nat.card (matGrp wGenWords) = 32 := by
  rw [← W_eq, ← genMonN_five, card_genJ wg_comm wg_sq Co2JRank.wWalk Co2JRank.wNz (by norm_num)
    (by norm_num)]
  norm_num

theorem a_sq : repMat 1 * repMat 1 = 1 := by
  rw [← wMat_one]
  exact w_sq (wMat_mem 1)

theorem MatP_bitMul_W (u : ℕ) : MatP 22 (bitMul Co2JRank.WG 5 u) = wMat u := by
  rw [MatP_bitMul, wMat_xP]
  exact xP_eq_asc (f := fun i => MatP 22 (Co2JRank.WG i))
    (B := bitProd fun i => MatP 22 (Co2JRank.WG i)) (fun _ => rfl) (fun _ _ => rfl) 5 wg_comm u

theorem mem_A {c : ℕ} (hc : c < 16) (h : (133 : ℕ).testBit c = true) : c ∈ [0, 2, 7] := by
  revert h
  interval_cases c <;> decide

theorem mem_B {c : ℕ} (hc : c < 16) (h : (42 : ℕ).testBit c = true) : c ∈ [1, 3, 5] := by
  revert h
  interval_cases c <;> decide

theorem typeAB_look {s : ℕ} (hs : s < 15) :
    InA (wMat (lwU s)) ∧ InB (wMat (lwU s) * repMat 1) := by
  have h := lookW s hs
  rw [andK_eq, Bool.and_eq_true] at h
  obtain ⟨b1, e1⟩ := crConj_look (by norm_num) h.1
  obtain ⟨b2, e2⟩ := crConj_look (by norm_num) h.2
  rw [MatP_bitMul_W] at e1
  rw [MatP_mulV, MatP_bitMul_W, ← Co2Syl.repMat_eq (by norm_num)] at e2
  exact ⟨⟨_, mem_A (Nat.and_lt_two_pow _ (by norm_num : 15 < 2 ^ 4)) b1, e1⟩,
    ⟨_, mem_B (Nat.and_lt_two_pow _ (by norm_num : 15 < 2 ^ 4)) b2, e2⟩⟩

theorem typeBA_look {s : ℕ} (hs : s < 15) :
    InB (wMat (lwU s ^^^ 1)) ∧ InA (wMat (lwU s ^^^ 1) * repMat 1) := by
  obtain ⟨h1, h2⟩ := typeAB_look hs
  rw [wMat_xor, wMat_one, mul_assoc, a_sq, mul_one]
  exact ⟨h2, h1⟩

theorem w_cases {x : M22} (hx : x ∈ matGrp wGenWords) :
    x = 1 ∨ x = repMat 1 ∨ (InA x ∧ InB (x * repMat 1)) ∨ (InB x ∧ InA (x * repMat 1)) := by
  obtain ⟨u, hu, rfl⟩ := mem_W.1 hx
  rcases lwU_cover u hu with rfl | rfl | ⟨s, hs, e | e⟩
  · exact Or.inl wMat_zero
  · exact Or.inr (Or.inl wMat_one)
  · rw [← e]
    exact Or.inr (Or.inr (Or.inl (typeAB_look hs)))
  · have e' : u = lwU s ^^^ 1 := by rw [e, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
    rw [e']
    exact Or.inr (Or.inr (Or.inr (typeBA_look hs)))

theorem rank_one_add_one : ((1 : M22) + 1).rank = 0 := by
  have e : (1 + 1 : M22) = 0 := by
    ext i j
    rw [Matrix.add_apply, CharTwo.add_self_eq_zero, Matrix.zero_apply]
  rw [e, Matrix.rank_zero]

theorem typeAB_iff {x : M22} :
    (x ∈ matGrp wGenWords ∧ InA x ∧ InB (x * repMat 1)) ↔ ∃ s < 15, wMat (lwU s) = x := by
  constructor
  · rintro ⟨hx, hA, -⟩
    have h6 := rank_InA hA
    obtain ⟨u, hu, rfl⟩ := mem_W.1 hx
    rcases lwU_cover u hu with rfl | rfl | ⟨s, hs, e | e⟩
    · rw [wMat_zero, rank_one_add_one] at h6
      exact absurd h6 (by norm_num)
    · rw [wMat_one, rk_rep.2.1] at h6
      exact absurd h6 (by norm_num)
    · exact ⟨s, hs, by rw [e]⟩
    · have e' : u = lwU s ^^^ 1 := by rw [e, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
      rw [e', rank_InB (typeBA_look hs).1] at h6
      exact absurd h6 (by norm_num)
  · rintro ⟨s, hs, rfl⟩
    exact ⟨wMat_mem _, typeAB_look hs⟩

theorem card_typeAB :
    Nat.card {x : M22 // x ∈ matGrp wGenWords ∧ InA x ∧ InB (x * repMat 1)} = 15 := by
  have hF : Function.Bijective (fun s : Fin 15 =>
      (⟨wMat (lwU s), typeAB_iff.2 ⟨s, s.isLt, rfl⟩⟩ :
        {x : M22 // x ∈ matGrp wGenWords ∧ InA x ∧ InB (x * repMat 1)})) := by
    refine ⟨fun s t e => ?_, fun x => ?_⟩
    · simp only [Subtype.mk.injEq] at e
      exact Fin.ext (lwU_inj s s.isLt t t.isLt (wMat_inj (lwU_lt s s.isLt) (lwU_lt t t.isLt) e))
    · obtain ⟨s, hs, e⟩ := typeAB_iff.1 x.2
      exact ⟨⟨s, hs⟩, Subtype.ext e⟩
  rw [← Nat.card_eq_of_bijective _ hF, Nat.card_fin]

theorem r_central : ∀ g ∈ Cm, g * repMat 0 = repMat 0 * g := by
  intro g hg
  rw [Cm_eq] at hg
  rw [Co2Syl.repMat_eq (by norm_num)]
  unfold genMonN at hg
  induction hg using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨⟨j, hj⟩, rfl⟩ := hx
    exact commK_sound (Co2Cls.cent0 j hj)
  | one => rw [one_mul, mul_one]
  | mul x y _ _ hx hy => rw [mul_assoc, hy, ← mul_assoc, hx, mul_assoc]

theorem a_mem_Cm : repMat 1 ∈ Cm := by
  rw [Cm_eq, Co2Syl.repMat_eq (by norm_num)]
  exact Co2Cls.repMat_mem (by norm_num)

theorem mem_W_of_scan {CF CR : ℕ → ℕ} {k : ℕ}
    (h : scanC CF CR (exW Co2JRank.WG 5) (RP 1) 8 k = true)
    (hc : MatP 22 (elemAt CF k) * repMat 1 = repMat 1 * MatP 22 (elemAt CF k))
    (hB : InB (MatP 22 (elemAt CF k) * repMat 1)) : MatP 22 (elemAt CF k) ∈ matGrp wGenWords := by
  rw [Co2Syl.repMat_eq (by norm_num)] at hc hB
  rcases scanC_sound h hc with ⟨-, hx⟩ | hx
  · rw [exW_sound hx, ← W_eq]
    exact (xP_eq_asc (f := fun i => MatP 22 (Co2JRank.WG i))
      (B := bitProd fun i => MatP 22 (Co2JRank.WG i)) (fun _ => rfl) (fun _ _ => rfl) 5 wg_comm
      _).symm ▸ xP_mem _ 5 _ fun i hi => gen_mem _ hi
  · exact absurd (rank_InB hB) hx

theorem mem_W_of_AB {x : M22} (hx : x ∈ Cm) (hc : x * repMat 1 = repMat 1 * x) (hA : InA x)
    (hB : InB (x * repMat 1)) : x ∈ matGrp wGenWords := by
  obtain ⟨c, hcl, hconj⟩ := hA
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hcl
  rcases hcl with rfl | rfl | rfl
  · obtain ⟨g, hg, e⟩ := hconj
    rw [r_central g hg] at e
    rw [(isUnit_Cm g hg).mul_left_inj.1 e.symm, ← wMat_two]
    exact wMat_mem 2
  · obtain ⟨k, hk, rfl⟩ := rec_of_conj2 hconj
    exact mem_W_of_scan (scan21 k hk) hc hB
  · obtain ⟨k, hk, rfl⟩ := rec_of_conj7 hconj
    exact mem_W_of_scan (scan71 k hk) hc hB

theorem mem_W_of_type {x : M22} (hx : x ∈ Cm) (hc : x * repMat 1 = repMat 1 * x)
    (ht : (InA x ∧ InB (x * repMat 1)) ∨ (InB x ∧ InA (x * repMat 1))) :
    x ∈ matGrp wGenWords := by
  rcases ht with ⟨hA, hB⟩ | ⟨hB, hA⟩
  · exact mem_W_of_AB hx hc hA hB
  · have hy : x * repMat 1 * repMat 1 = x := by rw [mul_assoc, a_sq, mul_one]
    have hyW := mem_W_of_AB (Cm.mul_mem hx a_mem_Cm)
      (by rw [mul_assoc, a_sq, mul_one, hc, ← mul_assoc, a_sq, one_mul]) hA (by rw [hy]; exact hB)
    rw [← hy]
    exact (matGrp wGenWords).mul_mem hyW (by rw [← wMat_one]; exact wMat_mem 1)

theorem gens_W_le : ∀ k < 5, MatP 22 (Co2JRank.WG k) ∈ genMon G1 := fun k hk =>
  word_sound (wInP1 k hk)

theorem W_le_P1 : matGrp wGenWords ≤ matGrp pWords1 := by
  rw [← W_eq, ← genMon1]
  unfold genMon
  rw [Submonoid.closure_le]
  rintro _ ⟨⟨k, hk⟩, rfl⟩
  exact gens_W_le k hk

theorem pow1 : ∀ x ∈ genMon G1, x ^ 32 = 1 := by
  rw [genMon1]
  exact facts1.1.pow

theorem JE_F1 {i : ℕ} (hi : i < 4) :
    MatP 22 (Co2J.JE (F1 i)) = 1 ∨ MatP 22 (Co2J.JE (F1 i)) = repMat 1 ∨
      MatP 22 (Co2J.JE (F1 i)) = repMat 0 ∨ MatP 22 (Co2J.JE (F1 i)) = repMat 0 * repMat 1 := by
  rw [Nat.eq_of_beq_eq_true (fix1_JE i hi), Co2Syl.repMat_eq (by norm_num : 0 < 10),
    Co2Syl.repMat_eq (by norm_num : 1 < 10)]
  interval_cases i
  · exact Or.inl MatP_IDP
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (MatP_mulV _ _)))

theorem center_P1 (hc : Nat.card (matGrp pWords1) ≤ 2 ^ 17) {x : M22}
    (hx : x ∈ matGrp pWords1) (hz : ∀ y ∈ matGrp pWords1, x * y = y * x) :
    x = 1 ∨ x = repMat 1 ∨ x = repMat 0 ∨ x = repMat 0 * repMat 1 := by
  rw [← genMon1] at hc hx hz
  obtain ⟨i, hi, rfl⟩ := center_of_fixK Co2J.jGen Co2J.jEnum jInP1 coord1 (unit_of_pow pow1) fix1
    (treeNK_spec img1) (hc.trans (by norm_num)) hx hz
  exact JE_F1 hi

theorem card_cent_W (hc : Nat.card (matGrp pWords1) ≤ 2 ^ 17) :
    Nat.card {x : M22 // x ∈ matGrp pWords1 ∧ ∀ w ∈ matGrp wGenWords, x * w = w * x} ≤ 2048 := by
  classical
  have hunit := genMon_unit (unit_of_pow pow1)
  have hconj := tw_conj tree
  choose g hg hgx using hconj
  rw [← genMon1] at hc ⊢
  have hF : Function.Injective (fun p : Fin 64 ×
      {x : M22 // x ∈ genMon G1 ∧ ∀ w ∈ matGrp wGenWords, x * w = w * x} =>
      (⟨g p.1 p.1.isLt * p.2.1, (genMon G1).mul_mem (hg _ _)
        p.2.2.1⟩ : genMon G1)) := by
    rintro ⟨s, c, hc1, hc2⟩ ⟨t, d, hd1, hd2⟩ e
    simp only [Subtype.mk.injEq] at e
    have e' : g s s.isLt * c = g t t.isLt * d := e
    have hh : ∀ (u : Fin 64) (y : M22), (∀ w ∈ matGrp wGenWords, y * w = w * y) → ∀ i < 5,
        g u u.isLt * y * MatP 22 (Co2JRank.WG i) =
          MatP 22 (twComp (TW u) i) * (g u u.isLt * y) := by
      intro u y hy i hi
      rw [mul_assoc, hy _ (by rw [← W_eq]; exact gen_mem _ hi), ← mul_assoc, hgx u u.isLt i hi,
        mul_assoc]
    have hst : s = t := by
      refine Fin.ext (tw_inj tree s s.isLt t t.isLt fun i hi => ?_)
      have e1 := hh s c hc2 i hi
      have e2 := hh t d hd2 i hi
      rw [e'] at e1
      exact (hunit _ ((genMon G1).mul_mem (hg _ _) hd1)).mul_left_inj.1
        (e1.symm.trans e2)
    subst hst
    have hcd : c = d := (hunit _ (hg _ _)).mul_right_inj.1 e'
    subst hcd
    rfl
  have hle := Nat.card_le_card_of_injective _ hF
  rw [Nat.card_prod, Nat.card_fin] at hle
  have : 64 * Nat.card {x : M22 // x ∈ genMon G1 ∧ ∀ w ∈ matGrp wGenWords, x * w = w * x} ≤
      64 * 2048 := hle.trans (hc.trans (by norm_num))
  exact Nat.le_of_mul_le_mul_left this (by norm_num)

theorem odd_of {X : ℕ} {p : ℕ} (hX : MatP 22 X ∈ Cm)
    (h : andK (Nat.beq (powK X p) IDP) (andK (commK X (RP 1)) (notK (commK (Co2JRank.WG 2) X))) =
      true) :
    ∃ x ∈ Cm, x ^ p = 1 ∧ x * repMat 1 = repMat 1 * x ∧
      ∃ w ∈ matGrp wGenWords, w * x ≠ x * w := by
  simp only [andK_eq, notK_eq, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨MatP 22 X, hX, ?_, ?_, MatP 22 (Co2JRank.WG 2), by rw [← W_eq]; exact gen_mem _ (by
    norm_num), fun e => ?_⟩
  · rw [← MatP_powK, Nat.eq_of_beq_eq_true h1, MatP_IDP]
  · rw [Co2Syl.repMat_eq (by norm_num)]
    exact commK_sound h2
  · rw [← MatP_mulV, ← MatP_mulV] at e
    have e' := MatP_inj' (mulV_lt _ _) (mulV_lt _ _) e
    unfold commK at h3
    rw [e', Nat.beq_refl] at h3
    exact Bool.noConfusion h3

theorem wordK_mem_Cm {w : List ℕ} (hw : ∀ l ∈ w, l < 42) :
    MatP 22 (CertificateChecks.KernelSpor.Co2Syl.wordK w) ∈ Cm := by
  rw [Cm_eq]
  exact Co2Cls.wordK_mem w hw

theorem odd_facts : (∃ x ∈ Cm, x ^ 3 = 1 ∧ x * repMat 1 = repMat 1 * x ∧
      ∃ w ∈ matGrp wGenWords, w * x ≠ x * w) ∧
    ∃ x ∈ Cm, x ^ 7 = 1 ∧ x * repMat 1 = repMat 1 * x ∧
      ∃ w ∈ matGrp wGenWords, w * x ≠ x * w :=
  ⟨odd_of (wordK_mem_Cm xW_lt.1) odd3, odd_of (wordK_mem_Cm xW_lt.2) odd7⟩

theorem wFacts : WFacts where
  comm _ hx _ hy := w_comm hx hy
  sq _ hx := w_sq hx
  card := card_W
  cases _ hx := w_cases hx
  card_typeAB := card_typeAB
  closed _ hx hc ht := mem_W_of_type hx hc ht
  le := W_le_P1
  center hc _ hx hz := center_P1 hc hx hz
  cent := card_cent_W
  odd3 := odd_facts.1
  odd7 := odd_facts.2

end CertificateChecks.KernelSpor.Co2Cen

end
