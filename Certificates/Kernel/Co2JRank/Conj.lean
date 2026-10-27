module

public import Certificates.Kernel.Co2JRank.Facts
public import Certificates.Kernel.Co2JRank.KReps
public import Certificates.Kernel.Co2Fuse.Final
public import CFSG.Certificates.Kernel.Co2Fuse.Sound
public import CFSG.RankThree.Co2.JConjFacts
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelSpor.Co2JRank

open CFSG.KC.Loop CFSG.KC.Co2InvS CFSG.KC.Co2Syl CFSG.KC.Co2JRank CFSG.KC.TabMatGrp
  CFSG.KC.Co2Cls CFSG.KC.Co2Fuse CFSG.RankThree.Co2 CertificateChecks.KernelSpor.Co2Syl

local notation "M22" => Matrix (Fin 22) (Fin 22) (ZMod 2)

theorem rk_le : ∀ i < 10, kS (KR (Nat.mul 3 i)) ≤ 22 ∧ kS (KR (Nat.add (Nat.mul 3 i) 1)) ≤ 22 ∧
    kS (KR (Nat.add (Nat.mul 3 i) 2)) ≤ 22 := by decide +kernel

theorem rk_cls : ∀ i < 10,
    rkCls (kS (KR (Nat.mul 3 i))) (kS (KR (Nat.add (Nat.mul 3 i) 1)))
      (kS (KR (Nat.add (Nat.mul 3 i) 2))) = i := by decide +kernel

theorem rk_six : ∀ i < 10, kS (KR (Nat.mul 3 i)) = 6 → i = 0 ∨ i = 2 ∨ i = 7 := by decide +kernel

theorem rk_eight : ∀ i < 10, kS (KR (Nat.mul 3 i)) = 8 → i = 1 ∨ i = 3 ∨ i = 5 := by decide +kernel

theorem rank_slot {M c : ℕ} (h : rkS M c = true) (hc : kS c ≤ 22) : (MatP 22 M).rank = kS c := by
  rw [rkS_sound h, Nat.min_eq_left hc]

theorem kappa_rep {i : ℕ} (hi : i < 10) : kappa (repMat 0) (repMat i) =
    (kS (KR (Nat.mul 3 i)), kS (KR (Nat.add (Nat.mul 3 i) 1)), kS (KR (Nat.add (Nat.mul 3 i) 2))) := by
  have h := kReps i hi
  unfold kRepK at h
  rw [andK_eq, andK_eq, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨l1, l2, l3⟩ := rk_le i hi
  have e1 := rank_slot h1 l1
  have e2 := rank_slot h2 l2
  have e3 := rank_slot h3 l3
  rw [MatP_xorI] at e1
  rw [MatP_xorI, MatP_mulV] at e2
  rw [MatP_mulV, MatP_xorI, MatP_xorI] at e3
  rw [repMat_eq hi, repMat_eq (j := 0) (by norm_num)]
  unfold kappa
  rw [e1, e2, e3]

theorem jCls_eq (x : M22) : jCls x =
    rkCls (kappa (repMat 0) x).1 (kappa (repMat 0) x).2.1 (kappa (repMat 0) x).2.2 := rfl

theorem jCls_rep {i : ℕ} (hi : i < 10) : jCls (repMat i) = i := by
  rw [jCls_eq, kappa_rep hi]
  exact rk_cls i hi

theorem jCls_of_crConj {c : ℕ} (hc : c < 10) {x : M22} (h : CrConj (repMat c) x) : jCls x = c := by
  obtain ⟨g, hg, e⟩ := h
  rw [jCls_eq, kappa_conj (Co2Fuse.isUnit_Cm g hg) (Co2Fuse.cent_r g hg) e, ← jCls_eq, jCls_rep hc]

theorem rank_of_crConj {c : ℕ} (hc : c < 10) {x : M22} (h : CrConj (repMat c) x) :
    (x + 1).rank = kS (KR (Nat.mul 3 c)) := by
  obtain ⟨g, hg, e⟩ := h
  have := congrArg (·.1) (kappa_conj (Co2Fuse.isUnit_Cm g hg) (Co2Fuse.cent_r g hg) e)
  rw [kappa_rep hc] at this
  exact this

theorem two_eq_zero : (1 : M22) + 1 = 0 := by
  ext i j
  simp only [Matrix.add_apply, Matrix.zero_apply]
  exact CharTwo.add_self_eq_zero _

theorem jCls_one : jCls 1 = 10 := by
  unfold jCls
  rw [two_eq_zero, Matrix.rank_zero]
  unfold rkCls
  simp

theorem J_le_T : matGrp jWords ≤ matGrp sylWords := by
  rw [← Co2J.genJ_GJ, ← Co2J.genMon_G]
  exact CFSG.KC.Co2J.genJ_le Co2J.jInT

theorem J_le_Cm : matGrp jWords ≤ Cm := fun _ hx => Co2TInv.T_le_Cm (J_le_T hx)

theorem J_sq {x : M22} (hx : x ∈ matGrp jWords) : x * x = 1 := by
  obtain ⟨v, -, rfl⟩ := mem_J.1 hx
  rw [← jMat_xor, Nat.xor_self, jMat_zero]

theorem crConj_iff {x : M22} (hx : x ∈ matGrp jWords) {c : ℕ} (hc : c < 10) :
    CrConj (repMat c) x ↔ jCls x = c := by
  refine ⟨jCls_of_crConj hc, fun e => ?_⟩
  have h1 : x ≠ 1 := by
    rintro rfl
    rw [jCls_one] at e
    omega
  obtain ⟨i, hi, hci⟩ := Co2Fuse.cmCensus x (J_le_Cm hx) (J_sq hx) h1
  have e' := jCls_of_crConj hi hci
  rw [e] at e'
  rw [e']
  exact hci

theorem clsA_iff {x : M22} (hx : x ∈ matGrp jWords) : ClsA x ↔ InΩ x := by
  unfold ClsA InΩ
  rw [crConj_iff hx (c := 0) (by norm_num), crConj_iff hx (c := 2) (by norm_num),
    crConj_iff hx (c := 7) (by norm_num)]

theorem clsB_iff {x : M22} (hx : x ∈ matGrp jWords) :
    ClsB x ↔ jCls x = 1 ∨ jCls x = 3 ∨ jCls x = 5 := by
  unfold ClsB
  rw [crConj_iff hx (c := 1) (by norm_num), crConj_iff hx (c := 3) (by norm_num),
    crConj_iff hx (c := 5) (by norm_num)]

theorem clsC_iff {x : M22} (hx : x ∈ matGrp jWords) :
    ClsC x ↔ jCls x = 4 ∨ jCls x = 6 ∨ jCls x = 8 := by
  unfold ClsC
  rw [crConj_iff hx (c := 4) (by norm_num), crConj_iff hx (c := 6) (by norm_num),
    crConj_iff hx (c := 8) (by norm_num)]

theorem nJ_eq {c : ℕ} (hc : c < 10) : CFSG.RankThree.Co2.nJ c = jClsCount[c]! := by
  unfold CFSG.RankThree.Co2.nJ
  rw [← card_cls hc]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x =>
    ⟨fun ⟨hx, h⟩ => ⟨hx, (crConj_iff hx hc).1 h⟩, fun ⟨hx, h⟩ => ⟨hx, (crConj_iff hx hc).2 h⟩⟩)

theorem nA_eq {y : M22} (hy : y ∈ matGrp jWords) (hc : jCls y < 9) : nA y = jNVal[jCls y]! := by
  unfold nA
  rw [← card_n hy hc]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun t => ?_)
  constructor
  · rintro ⟨ht, h1, h2⟩
    exact ⟨ht, (clsA_iff ht).1 h1, (clsA_iff ((matGrp jWords).mul_mem ht hy)).1 h2⟩
  · rintro ⟨ht, h1, h2⟩
    exact ⟨ht, (clsA_iff ht).2 h1, (clsA_iff ((matGrp jWords).mul_mem ht hy)).2 h2⟩

theorem card_A : Nat.card {x // x ∈ matGrp jWords ∧ ClsA x} = 77 := by
  have e1 : Nat.card {x // x ∈ matGrp jWords ∧ ClsA x} =
      Nat.card {x // x ∈ matGrp jWords ∧ InΩ x} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x =>
      ⟨fun ⟨hx, h⟩ => ⟨hx, (clsA_iff hx).1 h⟩, fun ⟨hx, h⟩ => ⟨hx, (clsA_iff hx).2 h⟩⟩)
  rw [e1, card_J_sub, card_range_filter (Q := fun v => OM.testBit v = true) fun v hv => by
    rw [(omK_sound parts.2.2.1).2 v hv, omC_inΩ hv]]
  obtain ⟨himg, hinj⟩ := olK_sound parts.2.2.2.1
  rw [← himg, Finset.card_image_of_injOn hinj, Finset.card_range]

theorem not_nine {x : M22} (hx : x ∈ matGrp jWords) : ¬ CrConj (repMat 9) x := by
  intro h
  have hc := card_cls (c := 9) (by norm_num)
  have h0 : jClsCount[9]! = 0 := rfl
  rw [h0] at hc
  have : Nonempty {y // y ∈ matGrp jWords ∧ jCls y = 9} :=
    ⟨⟨x, hx, jCls_of_crConj (by norm_num) h⟩⟩
  have hp := Nat.card_pos (α := {y // y ∈ matGrp jWords ∧ jCls y = 9})
  omega

theorem jClassFacts : JClassFacts where
  r_mem := jRankFacts.r_mem
  two := by rw [nJ_eq (by norm_num)]; rfl
  seven := by rw [nJ_eq (by norm_num)]; rfl
  not_nine _ hx := not_nine hx
  span := by
    have hset : {x | x ∈ matGrp jWords ∧ (CrConj (repMat 0) x ∨ CrConj (repMat 7) x)} =
        {x | x ∈ matGrp jWords ∧ (jCls x = 0 ∨ jCls x = 7)} := by
      ext x
      simp only [Set.mem_setOf_eq]
      constructor
      · rintro ⟨hx, h⟩
        rw [crConj_iff hx (c := 0) (by norm_num), crConj_iff hx (c := 7) (by norm_num)] at h
        exact ⟨hx, h⟩
      · rintro ⟨hx, h⟩
        rw [← crConj_iff hx (c := 0) (by norm_num), ← crConj_iff hx (c := 7) (by norm_num)] at h
        exact ⟨hx, h⟩
    rw [hset]
    exact span

theorem jOrbitFacts : JOrbitFacts where
  card_A := card_A
  one := by rw [nJ_eq (by norm_num)]; rfl
  three := by rw [nJ_eq (by norm_num)]; rfl
  four := by rw [nJ_eq (by norm_num)]; rfl
  five := by rw [nJ_eq (by norm_num)]; rfl
  six := by rw [nJ_eq (by norm_num)]; rfl
  eight := by rw [nJ_eq (by norm_num)]; rfl
  nA_A y hy h := by
    have h' := (clsA_iff hy).1 h
    unfold InΩ at h'
    rcases h' with e | e | e <;>
      · rw [nA_eq hy (by omega), e]
        rfl
  nA_B y hy h := by
    rcases (clsB_iff hy).1 h with e | e | e <;>
      · rw [nA_eq hy (by omega), e]
        rfl
  nA_C y hy h := by
    rcases (clsC_iff hy).1 h with e | e | e <;>
      · rw [nA_eq hy (by omega), e]
        rfl

theorem jHypFacts : JHypFacts where
  five := by
    obtain ⟨t₁, h₁, t₂, h₂, t₃, h₃, t₄, h₄, t₅, h₅, c₁, c₂, c₃, c₄, c₅, e⟩ := five
    exact ⟨t₁, h₁, t₂, h₂, t₃, h₃, t₄, h₄, t₅, h₅, (clsA_iff h₁).2 c₁, (clsA_iff h₂).2 c₂,
      (clsA_iff h₃).2 c₃, (clsA_iff h₄).2 c₄, (clsA_iff h₅).2 c₅, e⟩
  three := by
    obtain ⟨u₁, h₁, u₂, h₂, u₃, h₃, c₁, c₂, c₃, e⟩ := three
    exact ⟨u₁, h₁, u₂, h₂, u₃, h₃, (crConj_iff h₁ (by norm_num)).2 c₁,
      (crConj_iff h₂ (by norm_num)).2 c₂, (crConj_iff h₃ (by norm_num)).2 c₃, e⟩

@[expose] noncomputable def wf (i : ℕ) : M22 := MatP 22 (WG i)

theorem wGen_parts : (∀ i < 5, wf i * wf i = 1) ∧ ∀ i < 5, ∀ k < 5, Commute (wf i) (wf k) := by
  have h := wGen
  unfold wGenK at h
  rw [andK_eq, Bool.and_eq_true] at h
  refine ⟨fun i hi => ?_, fun i hi k hk => ?_⟩
  · unfold wf
    rw [← MatP_mulV, Nat.eq_of_beq_eq_true (CFSG.KC.Co2J.allK_spec h.1 i hi), MatP_IDP]
  · unfold wf Commute SemiconjBy
    rw [← MatP_mulV, ← MatP_mulV,
      Nat.eq_of_beq_eq_true (CFSG.KC.Co2J.allK_spec (CFSG.KC.Co2J.allK_spec h.2 i hi) k hk)]

theorem wMat_xP (u : ℕ) : wMat u = xP wf 5 u := wMatN_eq u 5 le_rfl

theorem wMat_xor (s t : ℕ) : wMat (s ^^^ t) = wMat s * wMat t := by
  have h := @xP_xor M22 _ wf 5
  rw [wMat_xP, wMat_xP, wMat_xP]
  exact h wGen_parts.2 wGen_parts.1 s t

theorem wMat_zero : wMat 0 = 1 := by
  rw [wMat_xP]
  exact xP_zero wf 5

theorem wMat_sq (u : ℕ) : wMat u * wMat u = 1 := by
  rw [← wMat_xor, Nat.xor_self, wMat_zero]

theorem wMat_two_pow {j : ℕ} (hj : j < 5) : wMat (2 ^ j) = wordMat wGenWords[j]! := by
  rw [wMat_xP, xP_two_pow wf 5 j hj]
  exact MatP_WG hj

theorem wMat_xor_one (u : ℕ) : wMat (u ^^^ 1) = wMat u * repMat 1 := by
  rw [wMat_xor]
  have e : wMat 1 = wordMat wGenWords[0]! := wMat_two_pow (j := 0) (by norm_num)
  rw [e]
  rfl

theorem range_eq {ws : Array (List ℕ)} {n : ℕ} (hs : ws.size = n) {f : ℕ → M22}
    (hf : ∀ k < n, f k = wordMat ws[k]!) :
    Set.range (fun k : Fin ws.size => wordMat ws[k]) = Set.range fun j : Fin n => f j := by
  subst hs
  ext x
  constructor
  · rintro ⟨⟨k, hk⟩, rfl⟩
    refine ⟨⟨k, hk⟩, ?_⟩
    change f k = wordMat ws[k]
    rw [hf k hk, getElem!_pos ws k hk]
  · rintro ⟨⟨k, hk⟩, rfl⟩
    refine ⟨⟨k, hk⟩, ?_⟩
    change wordMat ws[k] = f k
    rw [hf k hk, getElem!_pos ws k hk]

theorem W_eq : matGrp wGenWords = Submonoid.closure (Set.range fun j : Fin 5 => wf j) := by
  unfold matGrp
  rw [range_eq (n := 5) rfl fun k hk => MatP_WG hk]
  rfl

theorem mem_W {x : M22} : x ∈ matGrp wGenWords ↔ ∃ u < 32, wMat u = x := by
  have h := @mem_closure_iff M22 _ wf 5
  rw [W_eq, h wGen_parts.2 wGen_parts.1]
  simp only [wMat_xP]
  rfl

theorem wMat_mem {u : ℕ} (hu : u < 32) : wMat u ∈ matGrp wGenWords := mem_W.2 ⟨u, hu, rfl⟩

theorem W_le_Cm : matGrp wGenWords ≤ Cm := by
  rw [Co2TInv.Cm_eq]
  exact Co2Cls.matGrp_le rfl wGenWords_lt

@[expose] def w0e : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, v => (if v.testBit k then (2 ^ (k + 1) ^^^ 1) else 0) ^^^ w0e k v

@[expose] noncomputable def g0 (k : ℕ) : M22 := wMat (2 ^ (k + 1) ^^^ 1)

theorem w0GenWords_eq : ∀ k < 4, w0GenWords[k]! = wGenWords[k + 1]! ++ wGenWords[0]! := by decide

theorem wordMat_append (w w' : List ℕ) : wordMat (w ++ w') = wordMat w * wordMat w' := by
  rw [wordMat_eq_prod, wordMat_eq_prod, wordMat_eq_prod, List.map_append, List.prod_append]

theorem g0_eq {k : ℕ} (hk : k < 4) : g0 k = wordMat w0GenWords[k]! := by
  rw [w0GenWords_eq k hk, wordMat_append, ← wMat_two_pow (by omega : k + 1 < 5),
    ← wMat_two_pow (j := 0) (by norm_num), ← wMat_xor]
  rfl

theorem g0_parts : (∀ i < 4, g0 i * g0 i = 1) ∧ ∀ i < 4, ∀ k < 4, Commute (g0 i) (g0 k) := by
  refine ⟨fun i _ => wMat_sq _, fun i _ k _ => ?_⟩
  unfold g0 Commute SemiconjBy
  rw [← wMat_xor, ← wMat_xor, Nat.xor_comm]

theorem xP_g0 (v : ℕ) : ∀ k, xP g0 k v = wMat (w0e k v)
  | 0 => by rw [xP, w0e, wMat_zero]
  | k + 1 => by
    rw [xP, w0e, xP_g0 v k, wMat_xor]
    split_ifs
    · rfl
    · rw [wMat_zero]

theorem w0e_vals : ∀ v < 16, (0 < v → w0e 4 v ≠ 0) ∧ w0e 4 v < 32 ∧
    (w0e 4 v ≠ 0 →
      w0e 4 v ≠ 0 ∧ Even ((Finset.range 5).filter fun i => (w0e 4 v).testBit i = true).card) := by
  decide +kernel

theorem w0e_onto : ∀ u < 32,
    (u ≠ 0 ∧ Even ((Finset.range 5).filter fun i => u.testBit i = true).card) →
      ∃ v < 16, w0e 4 v = u := by
  decide +kernel

theorem W0_eq : matGrp w0GenWords = Submonoid.closure (Set.range fun j : Fin 4 => g0 j) := by
  unfold matGrp
  rw [range_eq (n := 4) rfl fun k hk => g0_eq hk]

theorem mem_W0 {x : M22} : x ∈ matGrp w0GenWords ↔ ∃ v < 16, wMat (w0e 4 v) = x := by
  have h := @mem_closure_iff M22 _ g0 4
  rw [W0_eq, h g0_parts.2 g0_parts.1]
  simp only [xP_g0]
  rfl

theorem card_W0 : Nat.card (matGrp w0GenWords) = 16 := by
  have h := @card_closure M22 _ g0 4 g0_parts.2 g0_parts.1 fun v hv hv' => by
    rw [xP_g0]
    have h := w0e_vals v hv'
    exact wRankFacts.ne_one _ (Nat.pos_of_ne_zero (h.1 hv)) h.2.1
  rw [W0_eq, h]
  rfl

theorem W_ne_one {u : ℕ} (hu : u < 32) (h0 : u ≠ 0) : wMat u ≠ 1 :=
  wRankFacts.ne_one u (Nat.pos_of_ne_zero h0) hu

theorem clsB_iff_rank {x : M22} (hx : x ∈ Cm) (hsq : x * x = 1) (h1 : x ≠ 1) :
    ClsB x ↔ (x + 1).rank = 8 := by
  constructor
  · rintro (h | h | h)
    · rw [rank_of_crConj (by norm_num) h]; rfl
    · rw [rank_of_crConj (by norm_num) h]; rfl
    · rw [rank_of_crConj (by norm_num) h]; rfl
  · intro e
    obtain ⟨i, hi, h⟩ := Co2Fuse.cmCensus x hx hsq h1
    rw [rank_of_crConj hi h] at e
    rcases rk_eight i hi e with rfl | rfl | rfl
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)

theorem clsA_iff_rank {x : M22} (hx : x ∈ Cm) (hsq : x * x = 1) (h1 : x ≠ 1) :
    ClsA x ↔ (x + 1).rank = 6 := by
  constructor
  · rintro (h | h | h)
    · rw [rank_of_crConj (by norm_num) h]; rfl
    · rw [rank_of_crConj (by norm_num) h]; rfl
    · rw [rank_of_crConj (by norm_num) h]; rfl
  · intro e
    obtain ⟨i, hi, h⟩ := Co2Fuse.cmCensus x hx hsq h1
    rw [rank_of_crConj hi h] at e
    rcases rk_six i hi e with rfl | rfl | rfl
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)

theorem typeBA_iff {u : ℕ} (hu : u < 32) : MatTypeBA (wMat u) ↔
    (u ≠ 0 ∧ Even ((Finset.range 5).filter fun i => u.testBit i = true).card) := by
  rw [wRankFacts.par u hu]
  have hu1 : u ^^^ 1 < 32 := Nat.xor_lt_two_pow (n := 5) hu (by norm_num)
  unfold MatTypeBA
  constructor
  · rintro ⟨hB, hA⟩
    have h0 : u ≠ 0 := by
      rintro rfl
      rcases hB with h | h | h <;>
        · have h' := jCls_of_crConj (by norm_num) h
          rw [wMat_zero, jCls_one] at h'
          omega
    have h01 : u ^^^ 1 ≠ 0 := by
      intro e
      rcases hA with h | h | h <;>
        · have h' := jCls_of_crConj (by norm_num) h
          rw [← wMat_xor_one, e, wMat_zero, jCls_one] at h'
          omega
    refine ⟨(clsB_iff_rank (W_le_Cm (wMat_mem hu)) (wMat_sq u) (W_ne_one hu h0)).1 hB, ?_⟩
    rw [← wMat_xor_one] at hA
    exact (clsA_iff_rank (W_le_Cm (wMat_mem hu1)) (wMat_sq _) (W_ne_one hu1 h01)).1 hA
  · rintro ⟨e8, e6⟩
    have h0 : u ≠ 0 := by
      rintro rfl
      rw [wMat_zero, two_eq_zero, Matrix.rank_zero] at e8
      exact absurd e8 (by norm_num)
    have h01 : u ^^^ 1 ≠ 0 := by
      intro e
      rw [e, wMat_zero, two_eq_zero, Matrix.rank_zero] at e6
      exact absurd e6 (by norm_num)
    refine ⟨(clsB_iff_rank (W_le_Cm (wMat_mem hu)) (wMat_sq u) (W_ne_one hu h0)).2 e8, ?_⟩
    rw [← wMat_xor_one]
    exact (clsA_iff_rank (W_le_Cm (wMat_mem hu1)) (wMat_sq _) (W_ne_one hu1 h01)).2 e6

theorem w0Facts : W0Facts where
  card := card_W0
  le x hx := by
    obtain ⟨v, hv, rfl⟩ := mem_W0.1 hx
    exact wMat_mem (w0e_vals v hv).2.1
  typeBA_of_mem x hx h1 := by
    obtain ⟨v, hv, rfl⟩ := mem_W0.1 hx
    have h := w0e_vals v hv
    have hne : w0e 4 v ≠ 0 := by
      intro e
      rw [e, wMat_zero] at h1
      exact h1 rfl
    exact (typeBA_iff h.2.1).2 (h.2.2 hne)
  mem_of_typeBA x hx h := by
    obtain ⟨u, hu, rfl⟩ := mem_W.1 hx
    obtain ⟨v, hv, e⟩ := w0e_onto u hu ((typeBA_iff hu).1 h)
    exact mem_W0.2 ⟨v, hv, by rw [e]⟩
  ja := by
    obtain ⟨x, hx, e⟩ := jRankFacts.one
    exact ⟨x, hx, (crConj_iff hx (by norm_num)).2 e⟩

end CertificateChecks.KernelSpor.Co2JRank

end
