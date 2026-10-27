module

public import Certificates.Kernel.Co2JRank.Checks
public import Certificates.Kernel.Co2JRank.W
public import Certificates.Kernel.Co2JRank.WGens
public import Certificates.Kernel.Co2J.Facts
public import CFSG.Certificates.Kernel.Co2JRank.Tab
public import CFSG.RankThree.Co2.JRankFacts
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.BSeed.Sound

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelSpor.Co2JRank

open CFSG.KC.Loop CFSG.KC.Co2InvS CFSG.KC.Co2Syl CFSG.KC.Co2JRank CFSG.KC.TabMatGrp
  CFSG.RankThree.Co2

local notation "M22" => Matrix (Fin 22) (Fin 22) (ZMod 2)

theorem gJ_sq : ∀ i < 10, MatP 22 (Co2J.GJ i) * MatP 22 (Co2J.GJ i) = 1 :=
  (CFSG.KC.Co2J.jGen_sound Co2J.jGen).1

theorem gJ_comm : ∀ i < 10, ∀ j < 10, Commute (MatP 22 (Co2J.GJ i)) (MatP 22 (Co2J.GJ j)) :=
  (CFSG.KC.Co2J.jGen_sound Co2J.jGen).2

theorem jMat_xP : jMat = xP (fun i => MatP 22 (Co2J.GJ i)) 10 := by
  rw [Co2J.jMat_eq]
  funext v
  exact xP_eq_asc (f := fun i => MatP 22 (Co2J.GJ i))
    (B := CFSG.KC.Co2J.bitProd fun i => MatP 22 (Co2J.GJ i)) (fun _ => rfl) (fun _ _ => rfl) 10
    gJ_comm v

theorem jMat_xor (s t : ℕ) : jMat (s ^^^ t) = jMat s * jMat t := by
  have h := @xP_xor M22 _ (fun i => MatP 22 (Co2J.GJ i)) 10
  rw [jMat_xP]
  exact h gJ_comm gJ_sq s t

theorem jMat_zero : jMat 0 = 1 := by
  rw [jMat_xP]
  exact xP_zero (fun i => MatP 22 (Co2J.GJ i)) 10

theorem jMat_256 : jMat 256 = MatP 22 (Co2J.GJ 8) := by
  have h := xP_two_pow (fun i => MatP 22 (Co2J.GJ i)) 10 8 (by norm_num)
  have e : (2 : ℕ) ^ 8 = 256 := by norm_num
  rw [e] at h
  rw [jMat_xP]
  exact h

theorem GJ8_eq : Nat.beq (Co2J.GJ 8) (CertificateChecks.KernelSpor.Co2Syl.wordK [9]) = true := by
  quickRfl

theorem repMat_zero : repMat 0 = jMat 256 := by
  rw [jMat_256, Nat.eq_of_beq_eq_true GJ8_eq, Co2J.MatP_wordK' (by decide)]
  rfl

theorem jBij : Set.BijOn jMat (Set.Iio 1024) (matGrp jWords) := by
  rw [← Co2J.genJ_GJ, Co2J.jMat_eq]
  exact CFSG.KC.Co2J.jm_bij Co2J.jGen Co2J.jEnum

theorem mem_J {x : M22} : x ∈ matGrp jWords ↔ ∃ v < 1024, jMat v = x := by
  constructor
  · intro hx
    obtain ⟨v, hv, e⟩ := jBij.surjOn hx
    exact ⟨v, hv, e⟩
  · rintro ⟨v, hv, rfl⟩
    exact jBij.mapsTo hv

theorem jMat_inj {s t : ℕ} (hs : s < 1024) (ht : t < 1024) (e : jMat s = jMat t) : s = t :=
  jBij.injOn hs ht e

theorem jMat_mem {v : ℕ} (hv : v < 1024) : jMat v ∈ matGrp jWords := mem_J.2 ⟨v, hv, rfl⟩

theorem MatP_JE {v : ℕ} (hv : v < 1024) : MatP 22 (Co2J.JE v) = jMat v := by
  rw [((CFSG.KC.Co2J.jEnum_sound Co2J.jEnum).1 v hv).2, Co2J.jMat_eq]

theorem jRanks {v : ℕ} (hv : v < 1024) :
    (jMat v + 1).rank = kAt K1 v ∧ (kAt K1 v = 10 → kAt K1 (v ^^^ 256) = 10 →
      ((repMat 0 + 1) * (jMat v + 1)).rank = kAt K3 v) := by
  have h := allPt_ranks ranks (by norm_num) v hv
  rw [MatP_JE hv, ← jMat_256, ← repMat_zero] at h
  exact h

theorem clsOf_eq (a b c : ℕ) : clsOf a b c = rkCls a b c := by
  unfold clsOf rkCls
  simp only [selN_eq, Nat.beq_eq]

theorem rkCls_third {a b : ℕ} (h : ¬ (a = 10 ∧ b = 10)) (c c' : ℕ) :
    rkCls a b c = rkCls a b c' := by
  unfold rkCls
  split_ifs <;> first | rfl | omega

theorem clsJ_eq {v : ℕ} (hv : v < 1024) : clsJ K1 K3 256 v = jCls (jMat v) := by
  obtain ⟨h1, h3⟩ := jRanks hv
  have hv' : v ^^^ 256 < 1024 := Nat.xor_lt_two_pow (n := 10) hv (by norm_num)
  have h2 : (jMat v * repMat 0 + 1).rank = kAt K1 (v ^^^ 256) := by
    rw [repMat_zero, ← jMat_xor]
    exact (jRanks hv').1
  change clsOf (kAt K1 v) (kAt K1 (v ^^^ 256)) (kAt K3 v) =
    rkCls (jMat v + 1).rank (jMat v * repMat 0 + 1).rank ((repMat 0 + 1) * (jMat v + 1)).rank
  rw [clsOf_eq, h1, h2]
  by_cases hab : kAt K1 v = 10 ∧ kAt K1 (v ^^^ 256) = 10
  · rw [h3 hab.1 hab.2]
  · exact rkCls_third hab _ _

theorem omC_inΩ {v : ℕ} (hv : v < 1024) : omC (clsJ K1 K3 256 v) = true ↔ InΩ (jMat v) := by
  rw [omC_iff, clsJ_eq hv]
  rfl

theorem card_range_filter {P Q : ℕ → Prop} [DecidablePred Q] {N : ℕ}
    (h : ∀ v < N, (P v ↔ Q v)) :
    Nat.card {v // v < N ∧ P v} = ((Finset.range N).filter Q).card := by
  have e : {v // v < N ∧ P v} ≃ ((Finset.range N).filter Q) :=
    Equiv.subtypeEquivRight fun v => by
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨fun ⟨a, b⟩ => ⟨a, (h v a).1 b⟩, fun ⟨a, b⟩ => ⟨a, (h v a).2 b⟩⟩
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]

theorem card_J_sub (P : M22 → Prop) :
    Nat.card {x // x ∈ matGrp jWords ∧ P x} = Nat.card {v // v < 1024 ∧ P (jMat v)} := by
  rw [← card_image_sub (e := jMat) (fun s hs t ht e => jMat_inj hs ht e) P]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x => by rw [mem_J])

theorem parts : nzK K1 1024 16 = true ∧ cntK K1 K3 256 CNT = true ∧ omK K1 K3 256 OM = true ∧
    olK OM OL 77 = true ∧ nK K1 K3 256 OM OL 77 NT = true ∧ w5K OM W5 = true ∧
    w3K K1 K3 256 W3 = true ∧ spK K1 K3 256 C = true :=
  tabJ_parts tab

theorem cnt_vals : ∀ c < 10, fld(CNT, Nat.mul 12 c, 4095) = jClsCount[c]! := by decide +kernel

theorem n_vals : ∀ c < 9, fld(NT, Nat.mul 4 c, 15) = jNVal[c]! := by decide +kernel

theorem card_cls {c : ℕ} (hc : c < 10) :
    Nat.card {x // x ∈ matGrp jWords ∧ jCls x = c} = jClsCount[c]! := by
  rw [card_J_sub, card_range_filter (Q := fun v => clsJ K1 K3 256 v = c)
    (fun v hv => by rw [clsJ_eq hv]), cntK_sound parts.2.1 c hc]
  exact cnt_vals c hc

theorem card_n {y : M22} (hy : y ∈ matGrp jWords) (hc : jCls y < 9) :
    Nat.card {t // t ∈ matGrp jWords ∧ InΩ t ∧ InΩ (t * y)} = jNVal[jCls y]! := by
  obtain ⟨w, hw, rfl⟩ := mem_J.1 hy
  rw [card_J_sub (fun t => InΩ t ∧ InΩ (t * jMat w)),
    card_range_filter (Q := fun t => omC (clsJ K1 K3 256 t) = true ∧
      omC (clsJ K1 K3 256 (t ^^^ w)) = true) fun v hv => by
        rw [omC_inΩ hv, omC_inΩ (Nat.xor_lt_two_pow (n := 10) hv hw), jMat_xor]]
  rw [← clsJ_eq hw] at hc ⊢
  rw [nK_sound parts.2.2.1 parts.2.2.2.1 parts.2.2.2.2.1 w hw hc]
  exact n_vals _ hc

theorem five : ∃ t₁ ∈ matGrp jWords, ∃ t₂ ∈ matGrp jWords, ∃ t₃ ∈ matGrp jWords,
    ∃ t₄ ∈ matGrp jWords, ∃ t₅ ∈ matGrp jWords,
      InΩ t₁ ∧ InΩ t₂ ∧ InΩ t₃ ∧ InΩ t₄ ∧ InΩ t₅ ∧ t₁ * t₂ * t₃ * t₄ * t₅ = 1 := by
  obtain ⟨hm, hx⟩ := w5K_sound parts.2.2.2.2.2.1
  obtain ⟨-, hOM⟩ := omK_sound parts.2.2.1
  have hin : ∀ i < 5, InΩ (jMat (fldJ W5 i)) := fun i hi =>
    (omC_inΩ (fldJ_lt _ _)).1 ((hOM _ (fldJ_lt _ _)).1 (hm i hi))
  refine ⟨_, jMat_mem (fldJ_lt W5 0), _, jMat_mem (fldJ_lt W5 1), _, jMat_mem (fldJ_lt W5 2),
    _, jMat_mem (fldJ_lt W5 3), _, jMat_mem (fldJ_lt W5 4), hin 0 (by norm_num),
    hin 1 (by norm_num), hin 2 (by norm_num), hin 3 (by norm_num), hin 4 (by norm_num), ?_⟩
  rw [← jMat_xor, ← jMat_xor, ← jMat_xor, ← jMat_xor, hx, jMat_zero]

theorem three : ∃ u₁ ∈ matGrp jWords, ∃ u₂ ∈ matGrp jWords, ∃ u₃ ∈ matGrp jWords,
    jCls u₁ = 4 ∧ jCls u₂ = 4 ∧ jCls u₃ = 4 ∧ (u₁ * u₂ * u₃ = 1 ∨ u₁ * u₂ * u₃ = repMat 0) := by
  obtain ⟨hm, hx⟩ := w3K_sound parts.2.2.2.2.2.2.1
  have hc : ∀ i < 3, jCls (jMat (fldJ W3 i)) = 4 := fun i hi => by
    rw [← clsJ_eq (fldJ_lt _ _)]
    exact hm i hi
  refine ⟨_, jMat_mem (fldJ_lt W3 0), _, jMat_mem (fldJ_lt W3 1), _, jMat_mem (fldJ_lt W3 2),
    hc 0 (by norm_num), hc 1 (by norm_num), hc 2 (by norm_num), ?_⟩
  rw [← jMat_xor, ← jMat_xor, repMat_zero]
  rcases hx with e | e
  · exact Or.inl (by rw [e, jMat_zero])
  · exact Or.inr (by rw [e])

theorem card_closure22 {e : ℕ → M22} (he : ∀ s < 1024, ∀ t < 1024, e (s ^^^ t) = e s * e t)
    (he0 : e 0 = 1) (hinj : ∀ s < 1024, ∀ t < 1024, e s = e t → s = t)
    {A : ℕ → Prop} {C n : ℕ} (hC : ∀ i < n, A (fldJ C i))
    (hA : ∀ v < 1024, A v → ∃ u < 2 ^ n, xsub C n u = v) :
    Nat.card (Submonoid.closure {x | ∃ v < 1024, A v ∧ e v = x}) =
      ((Finset.range (2 ^ n)).image (xsub C n)).card := by
  have h := @card_closure_xsub M22 _ e
  exact h he he0 hinj hC hA

theorem span : Nat.card (Submonoid.closure {x | x ∈ matGrp jWords ∧ (jCls x = 0 ∨ jCls x = 7)}) =
    64 := by
  obtain ⟨hcard, hcov, hC⟩ := spK_sound parts.2.2.2.2.2.2.2
  have hset : {x | x ∈ matGrp jWords ∧ (jCls x = 0 ∨ jCls x = 7)} =
      {x | ∃ v < 1024, vC (clsJ K1 K3 256 v) = true ∧ jMat v = x} := by
    ext x
    simp only [Set.mem_setOf_eq, mem_J]
    constructor
    · rintro ⟨⟨v, hv, rfl⟩, h⟩
      exact ⟨v, hv, by rw [vC_iff, clsJ_eq hv]; exact h, rfl⟩
    · rintro ⟨v, hv, h, rfl⟩
      rw [vC_iff, clsJ_eq hv] at h
      exact ⟨⟨v, hv, rfl⟩, h⟩
  have e64 : (2 : ℕ) ^ 6 = 64 := by norm_num
  have hcov' : ∀ v < 1024, vC (clsJ K1 K3 256 v) = true → ∃ u < 2 ^ 6, xsub C 6 u = v := by
    rw [e64]
    exact hcov
  have h := card_closure22 (e := jMat) (fun s _ t _ => jMat_xor s t) jMat_zero
    (fun s hs t ht e => jMat_inj hs ht e) (A := fun v => vC (clsJ K1 K3 256 v) = true) (n := 6)
    hC hcov'
  rw [e64] at h
  rw [hset, h]
  exact hcard

theorem jRankFacts : JRankFacts where
  r_mem := by
    rw [repMat_zero]
    exact jMat_mem (by norm_num)
  card _ hc := card_cls hc
  n _ hy hc := card_n hy hc
  five := five
  three := three
  span := span
  one := by
    have h : 0 < Nat.card {x // x ∈ matGrp jWords ∧ jCls x = 1} := by
      rw [card_cls (by norm_num)]
      decide
    obtain ⟨⟨⟨x, hx, e⟩⟩, -⟩ := Nat.card_pos_iff.1 h
    exact ⟨x, hx, e⟩

theorem wGenWords_lt : ∀ k < 5, ∀ l ∈ wGenWords[k]!, l < 42 := by decide +kernel

theorem MatP_WG {k : ℕ} (hk : k < 5) : MatP 22 (WG k) = wordMat wGenWords[k]! := by
  rw [Nat.eq_of_beq_eq_true (wGens k hk), Co2J.MatP_wordK' (wGenWords_lt k hk)]

theorem wMatN_eq (u : ℕ) : ∀ n ≤ 5, wMatN n u = xP (fun i => MatP 22 (WG i)) n u
  | 0, _ => rfl
  | n + 1, hn => by
    simp only [wMatN, xP]
    rw [wMatN_eq u n (by omega), MatP_WG (by omega : n < 5)]

theorem wMat_eq (u : ℕ) : wMat u = xM WG 5 u := wMatN_eq u 5 le_rfl

theorem wRanks {u : ℕ} (hu : u < 32) : (wMat u + 1).rank = kAt K1W u := by
  rw [wMat_eq]
  exact walk1_ranks wWalk u hu

theorem wRankFacts : WRankFacts where
  ne_one u hu hu' := by
    rw [wMat_eq]
    exact xM_ne_one wWalk wNz (by norm_num) (by norm_num) u hu hu'
  par u hu := by
    rw [wRanks hu, wRanks (Nat.xor_lt_two_pow (n := 5) hu (by norm_num))]
    exact parK_sound wPar (by norm_num) u hu

end CertificateChecks.KernelSpor.Co2JRank

end
