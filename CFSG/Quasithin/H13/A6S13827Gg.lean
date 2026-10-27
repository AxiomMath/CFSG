module

public import CFSG.Quasithin.H13.A6S13827Gf
public import CFSG.Quasithin.Background.SmithB42U33Gen
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.Vol2.Ch12Sec4G2NormZorn

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.Orbit CFSG.Quasithin.B42U33
open scoped Pointwise

namespace A6G2

@[expose] noncomputable def stabQ (x : ModQ) : Subgroup ↥(quasithinG2 (ZMod 2)) :=
  (MulAction.stabilizer (MulAut ModQ) x).comap (g2QAct (ZMod 2))

theorem mem_stabQ {x : ModQ} {g : ↥(quasithinG2 (ZMod 2))} :
    g ∈ stabQ x ↔ g2QAct (ZMod 2) g x = x := Iff.rfl

theorem eight_mem_o0Codes : (8 : ℕ) ∈ o0Codes := by decide

theorem two_mem_o0Codes : (2 : ℕ) ∈ o0Codes := by decide

@[expose] noncomputable def x₀ : ModQ := codeQ ⟨8, eight_mem_o0Codes⟩

theorem g2QAct_codeQ_mk (g : ↥(quasithinG2 (ZMod 2))) {c : ℕ} (hc : c ∈ o0Codes)
    (hgc : mact (matCode g.1) c ∈ o0Codes) :
    g2QAct (ZMod 2) g (codeQ ⟨c, hc⟩) = codeQ ⟨mact (matCode g.1) c, hgc⟩ := by
  rw [g2QAct_codeQ]
  rfl

theorem sSubG_le_stabQ : sSubG ≤ stabQ x₀ := by
  intro g hg
  obtain ⟨i, hi, rfl⟩ := mem_sSubG.1 hg
  rw [mem_stabQ, x₀, g2QAct_codeQ]
  congr 1
  apply Subtype.ext
  change mact (matCode (sEltG i).1) 8 = 8
  rw [matCode_sEltG hi]
  exact fix_eight.1 i hi

theorem exists_derived_apply_eq_x₀
    {x : ModQ} (hx : x ≠ 1) :
    ∃ g ∈ g2Derived (ZMod 2), g2QAct (ZMod 2) g x = x₀ := by
  obtain ⟨c, rfl⟩ := codeQ_surjective x
  have h0 : ¬ (c.1 = 0 ∨ c.1 = 129) := fun h => hx ((codeQ_eq_one_iff c).2 h)
  rw [not_or] at h0
  obtain ⟨c', hc'mem, hcc', hn, hd0, hd1⟩ : ∃ c' : ℕ, ∃ h : c' ∈ o0Codes,
      codeQ c = codeQ ⟨c', h⟩ ∧ zornNorm (decodeZ c') = 0 ∧ decodeZ c' ≠ 0 ∧
        decodeZ c' ≠ zornOne := by
    rcases singular_or c.1 c.2 h0.1 h0.2 with ⟨hn, hd0, hd1⟩ | ⟨hn, hd0, hd1⟩
    · exact ⟨c.1, c.2, rfl, hn, hd0, hd1⟩
    · exact ⟨c.1 ^^^ 129, xor_mem_o0Codes c.2 (by decide), (codeQ_eq_iff _ _).2 (Or.inr rfl),
        hn, hd0, hd1⟩
  obtain ⟨hwc, hwl⟩ := singular_word hc'mem hn hd0 hd1
  have he := codeQ_word_e hwl hc'mem two_mem_o0Codes hwc
  have h8 : mact (matCode (B42U33.wordG [0, 1, 0]).1) 2 = 8 := by
    change mact (matCode (wordE [0, 1, 0])) 2 = 8
    rw [matCode_wordE]
    exact fix_eight.2.2.2
  have hg8 : g2QAct (ZMod 2) (B42U33.wordG [0, 1, 0]) (codeQ ⟨2, two_mem_o0Codes⟩) = x₀ := by
    rw [g2QAct_codeQ_mk _ two_mem_o0Codes (by rw [h8]; exact eight_mem_o0Codes), x₀]
    exact congrArg codeQ (Subtype.ext h8)
  refine ⟨B42U33.wordG [0, 1, 0] * (wordGG (g2Words.getD c' []))⁻¹,
    (g2Derived (ZMod 2)).mul_mem (B42U33.wordG_mem _)
      ((g2Derived (ZMod 2)).inv_mem (wordGG_mem_derived _)), ?_⟩
  rw [hcc', ← he, map_mul, MulAut.mul_apply, map_inv, MulAut.inv_apply_self, hg8]

theorem exists_conj_le_sylow {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) {N B : Subgroup G} (hPN : (P : Subgroup G) ≤ N) (hBN : B ≤ N)
    (hB : IsPGroup p ↥B) : ∃ n ∈ N, B.map (MulAut.conj n).toMonoidHom ≤ P := by
  let P' : Sylow p ↥N := P.subtype hPN
  have hB' : IsPGroup p ↥(B.subgroupOf N) := hB.of_equiv (Subgroup.subgroupOfEquivOfLe hBN).symm
  obtain ⟨Q, hQ⟩ := hB'.exists_le_sylow
  obtain ⟨n, hn⟩ := MulAction.exists_smul_eq ↥N Q P'
  refine ⟨n, n.2, ?_⟩
  rintro _ ⟨b, hb, rfl⟩
  have hbQ : (⟨b, hBN hb⟩ : ↥N) ∈ (Q : Subgroup ↥N) := hQ (Subgroup.mem_subgroupOf.2 hb)
  have h1 : MulAut.conj n • (⟨b, hBN hb⟩ : ↥N) ∈ MulAut.conj n • (Q : Subgroup ↥N) :=
    Subgroup.smul_mem_pointwise_smul _ _ _ hbQ
  rw [← Sylow.coe_subgroup_smul, hn, Sylow.coe_subtype, Subgroup.mem_subgroupOf] at h1
  exact h1

theorem exists_conj_le_sSubG
    {x : ModQ} (hx : x ≠ 1)
    {B : Subgroup ↥(quasithinG2 (ZMod 2))} (hB2 : IsPGroup 2 ↥B) (hBx : B ≤ stabQ x) :
    ∃ r : ↥(quasithinG2 (ZMod 2)), g2QAct (ZMod 2) r x = x₀ ∧
      B.map (MulAut.conj r).toMonoidHom ≤ sSubG := by
  obtain ⟨g, -, hg⟩ := exists_derived_apply_eq_x₀ hx
  set B₁ := B.map (MulAut.conj g).toMonoidHom with hB₁
  have hB₁x : B₁ ≤ stabQ x₀ := by
    rintro _ ⟨b, hb, rfl⟩
    rw [mem_stabQ]
    have hbx := hBx hb
    rw [mem_stabQ] at hbx
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv, MulAut.mul_apply]
    rw [← hg, MulAut.inv_apply_self, hbx]
  have hB₁2 : IsPGroup 2 ↥B₁ := hB2.map _
  have hS : (sylowSub : Subgroup ↥(quasithinG2 (ZMod 2))) ≤ stabQ x₀ := by
    rw [coe_sylowSub]
    exact sSubG_le_stabQ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn, hle⟩ := exists_conj_le_sylow sylowSub hS hB₁x hB₁2
  refine ⟨n * g, ?_, ?_⟩
  · rw [map_mul, MulAut.mul_apply, hg]
    exact hn
  · rw [← coe_sylowSub]
    rintro _ ⟨b, hb, rfl⟩
    have h1 : (MulAut.conj n).toMonoidHom ((MulAut.conj g).toMonoidHom b) ∈
        (sylowSub : Subgroup ↥(quasithinG2 (ZMod 2))) := hle ⟨_, ⟨b, hb, rfl⟩, rfl⟩
    have e : (MulAut.conj (n * g)).toMonoidHom b =
        (MulAut.conj n).toMonoidHom ((MulAut.conj g).toMonoidHom b) := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_inv_rev]
      group
    rw [e]
    exact h1

theorem wordE_pow4 (w : List ℕ) : wordE (pow4 w) = wordE w ^ 4 := by
  simp only [pow4, wordE_append, pow_succ, pow_zero, one_mul]

theorem matCode_conj_pow4
    (w : List ℕ) {i : ℕ} (hi : i < 64) :
    matCode ⇑((B42U33.wordG w).1 ^ 4 * (sEltG i).1 * ((B42U33.wordG w).1 ^ 4)⁻¹) =
      conjC (pow4 w) (sM i) := by
  change matCode ⇑(wordE w ^ 4 * sElt i * (wordE w ^ 4)⁻¹) = _
  rw [← wordE_pow4, ← wordE_invW, matCode_mul, matCode_mul, matCode_wordE, matCode_sElt hi,
    matCode_wordE]
  rfl

theorem finite_e4
    {B : Subgroup ↥(quasithinG2 (ZMod 2))} (hBS : B ≤ sSubG)
    (hB1 : B ≠ ⊥) (hB2 : ∀ b ∈ B, b ^ 2 = 1) (hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    (hB4 : Nat.card B ≤ 4)
    (hBn : ∀ w ∈ [tW1, tW2], ∀ b ∈ B,
      B42U33.wordG w ^ 4 * b * (B42U33.wordG w ^ 4)⁻¹ ∈ B) :
    Nat.card B = 4 ∧ sEltG 2 ∈ B ∧ sEltG 4 ∈ B ∧ sEltG 6 ∈ B := by
  classical
  have hcard := card_eq_idx hBS
  have hconj : ∀ w ∈ [tW1, tW2], ∀ i ∈ idx B, ∃ k ∈ idx B, conjC (pow4 w) (sM i) = sM k ∧
      (i ≠ 0 → k ≠ 0) := by
    intro w hw i hi
    have hmem := hBn w hw _ (mem_idx.1 hi).2
    obtain ⟨k, hk, hke⟩ := mem_sSubG.1 (hBS hmem)
    refine ⟨k, mem_idx.2 ⟨hk, hke ▸ hmem⟩, ?_, fun hi0 hk0 => hi0 ?_⟩
    · rw [← matCode_conj_pow4 w (mem_idx.1 hi).1, ← matCode_sEltG hk, hke]
      rfl
    · rw [hk0, sEltG_zero] at hke
      have h1 : sEltG i = 1 := by
        have := hke.symm
        rwa [mul_inv_eq_one, mul_eq_left] at this
      exact sEltG_injective (mem_idx.1 hi).1 (by norm_num) (h1.trans sEltG_zero.symm)
  have hp : IsPGroup 2 ↥B := fun g => ⟨1, Subtype.ext (by rw [pow_one]; exact hB2 g.1 g.2)⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hp
  have hn0 : n ≠ 0 := fun h => hB1 (Subgroup.eq_bot_of_card_eq _ (by rw [hn, h, pow_zero]))
  have hn2 : n ≤ 2 := by
    rw [hn] at hB4
    by_contra h
    have : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h0 := zero_mem_idx (B := B)
  obtain ⟨i, hi, hi0⟩ : ∃ i ∈ idx B, i ≠ 0 := by
    by_contra h
    push Not at h
    have : idx B ⊆ {0} := fun i hi => Finset.mem_singleton.2 (h i hi)
    have h1 := Finset.card_le_card this
    rw [Finset.card_singleton, ← hcard, hn] at h1
    have : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hiInv := idx_inv hB2 hi hi0
  rcases (show n = 1 ∨ n = 2 by omega) with rfl | rfl
  ·
    exfalso
    have hidx : idx B = {0, i} := by
      refine (Finset.eq_of_subset_of_card_le (Finset.insert_subset h0
        (Finset.singleton_subset_iff.2 hi)) ?_).symm
      rw [← hcard, hn, Finset.card_pair (Ne.symm hi0)]
      norm_num
    have hfix : ∀ w ∈ [tW1, tW2], conjC (pow4 w) (sM i) = sM i := by
      intro w hw
      obtain ⟨k, hk, hke, hk0⟩ := hconj w hw i hi
      rw [hidx, Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl
      · exact absurd rfl (hk0 hi0)
      · exact hke
    exact no_inv_fixed i hiInv ⟨hfix tW1 (by simp), hfix tW2 (by simp)⟩
  ·
    obtain ⟨j, hj, hj0, hji⟩ : ∃ j ∈ idx B, j ≠ 0 ∧ j ≠ i := by
      by_contra h
      push Not at h
      have : idx B ⊆ {0, i} := fun j hj => by
        by_cases hj0 : j = 0
        · rw [hj0]; simp
        · rw [h j hj hj0]; simp
      have h1 := Finset.card_le_card this
      rw [← hcard, hn] at h1
      have h2 := Finset.card_le_two (a := 0) (b := i)
      omega
    have hjInv := idx_inv hB2 hj hj0
    have hcomm := idx_comm hBc hi hj
    have hprod : sEltG i * sEltG j ∈ B := B.mul_mem (mem_idx.1 hi).2 (mem_idx.1 hj).2
    obtain ⟨l, hl, hle⟩ := mem_sSubG.1 (hBS hprod)
    have hlcode : sM l = mmul (sM i) (sM j) := by
      rw [← matCode_sEltG hl, hle]
      exact matCode_mul_sElt (mem_idx.1 hi).1 (mem_idx.1 hj).1
    have hlf : sFind (mmul (sM i) (sM j)) = l := by rw [← hlcode]; exact sFind_sM l hl
    have hlB : l ∈ idx B := mem_idx.2 ⟨hl, hle ▸ hprod⟩
    have hinv : ∀ e ∈ idx B, (sEltG e)⁻¹ = sEltG e := fun e he => by
      have := hB2 _ (mem_idx.1 he).2
      rw [pow_two] at this
      exact inv_eq_of_mul_eq_one_right this
    have hl0 : l ≠ 0 := by
      intro h
      rw [h, sEltG_zero] at hle
      have h1 : sEltG j = (sEltG i)⁻¹ := eq_inv_of_mul_eq_one_right hle.symm
      exact hji (sEltG_injective (mem_idx.1 hj).1 (mem_idx.1 hi).1 (h1.trans (hinv i hi)))
    have hli : l ≠ i := by
      intro h
      rw [h] at hle
      have h1 : sEltG j = 1 := left_eq_mul.1 hle
      exact hj0 (sEltG_injective (mem_idx.1 hj).1 (by norm_num) (h1.trans sEltG_zero.symm))
    have hlj : l ≠ j := by
      intro h
      rw [h] at hle
      have h1 : sEltG i = 1 := right_eq_mul.1 hle
      exact hi0 (sEltG_injective (mem_idx.1 hi).1 (by norm_num) (h1.trans sEltG_zero.symm))
    have hc4 : ({0, i, j, l} : Finset ℕ).card = 4 := by
      rw [Finset.card_insert_of_notMem (by simp [Ne.symm hi0, Ne.symm hj0, Ne.symm hl0]),
        Finset.card_insert_of_notMem (by simp [Ne.symm hji, Ne.symm hli]),
        Finset.card_pair (Ne.symm hlj)]
    have hidx : idx B = {0, i, j, l} := by
      refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
      · intro e he
        simp only [Finset.mem_insert, Finset.mem_singleton] at he
        rcases he with rfl | rfl | rfl | rfl
        exacts [h0, hi, hj, hlB]
      · rw [← hcard, hn, hc4]
        norm_num
    have hnorm : ∀ e ∈ [i, j, sFind (mmul (sM i) (sM j))], ∀ w ∈ [tW1, tW2],
        conjC (pow4 w) (sM e) ∈ [sM i, sM j, sM (sFind (mmul (sM i) (sM j)))] := by
      rw [hlf]
      intro e he w hw
      have heB : e ∈ idx B := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl | rfl
        exacts [hi, hj, hlB]
      have he0 : e ≠ 0 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl | rfl
        exacts [hi0, hj0, hl0]
      obtain ⟨k, hk, hke, hk0⟩ := hconj w hw e heB
      rw [hidx] at hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rw [hke]
      rcases hk with rfl | rfl | rfl | rfl
      · exact absurd rfl (hk0 he0)
      all_goals simp
    obtain ⟨hi246, hj246⟩ := e4_normalized i hiInv j hjInv (Ne.symm hji) hcomm hnorm
    obtain ⟨hl246, hli', hlj'⟩ := z0_third i hi246 j hj246 (Ne.symm hji)
    rw [hlf] at hl246 hli' hlj'
    have hall : ∀ e ∈ [2, 4, 6], e ∈ idx B := by
      intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he hi246 hj246 hl246
      have : e = i ∨ e = j ∨ e = l := by omega
      rcases this with rfl | rfl | rfl
      exacts [hi, hj, hlB]
    refine ⟨by rw [hn]; norm_num, (mem_idx.1 (hall 2 (by simp))).2,
      (mem_idx.1 (hall 4 (by simp))).2, (mem_idx.1 (hall 6 (by simp))).2⟩

@[expose] def selCode (a : Bool) (n : ℕ) : ℕ := if a then n else 0

theorem eight_le_card_commV {B : Subgroup ↥(quasithinG2 (ZMod 2))} (h4 : sEltG 4 ∈ B)
    (h6 : sEltG 6 ∈ B) : 8 ≤ Nat.card (commV (B.map (g2QAct (ZMod 2)))) := by
  classical
  have hcodes : ∀ a b c : Bool, selCode a 8 ^^^ selCode b 48 ^^^ selCode c 32 ∈ o0Codes := by
    decide
  have hm : ∀ c : ℕ, c ∈ o0Codes → ∀ i < 64, mact (sM i) c ∈ o0Codes := fun c hc i hi => by
    have := mact_mem_o0Codes (sEltG i).2 hc
    rwa [matCode_sEltG hi] at this
  have hcomm : ∀ i (hi : i < 64) (c : ℕ) (hc : c ∈ o0Codes),
      g2QAct (ZMod 2) (sEltG i) (codeQ ⟨c, hc⟩) * (codeQ ⟨c, hc⟩)⁻¹ =
        codeQ ⟨mact (sM i) c ^^^ c, xor_mem_o0Codes (hm c hc i hi) hc⟩ := by
    intro i hi c hc
    rw [g2QAct_codeQ_mk _ hc (by rw [matCode_sEltG hi]; exact hm c hc i hi), codeQ_inv,
      ← codeQ_xor]
    congr 1
    apply Subtype.ext
    change mact (matCode (sEltG i).1) c ^^^ c = mact (sM i) c ^^^ c
    rw [matCode_sEltG hi]
  have hmem : ∀ i (hi : i < 64), sEltG i ∈ B → ∀ (c : ℕ) (hc : c ∈ o0Codes),
      codeQ ⟨mact (sM i) c ^^^ c, xor_mem_o0Codes (hm c hc i hi) hc⟩ ∈
        commV (B.map (g2QAct (ZMod 2))) := by
    intro i hi hiB c hc
    rw [← hcomm i hi c hc]
    exact Subgroup.subset_closure ⟨_, ⟨sEltG i, hiB, rfl⟩, _, rfl⟩
  obtain ⟨w1, w2, w3, -⟩ := comm_witness
  have h8 : codeQ ⟨8, by decide⟩ ∈ commV (B.map (g2QAct (ZMod 2))) := by
    have := hmem 6 (by norm_num) h6 2 (by decide)
    convert this using 3
    exact w1.symm
  have h48 : codeQ ⟨48, by decide⟩ ∈ commV (B.map (g2QAct (ZMod 2))) := by
    have := hmem 6 (by norm_num) h6 64 (by decide)
    convert this using 3
    exact w2.symm
  have h32 : codeQ ⟨32, by decide⟩ ∈ commV (B.map (g2QAct (ZMod 2))) := by
    have := hmem 4 (by norm_num) h4 64 (by decide)
    convert this using 3
    exact w3.symm
  have hprod : ∀ a b c : Bool,
      codeQ ⟨selCode a 8 ^^^ selCode b 48 ^^^ selCode c 32, hcodes a b c⟩ ∈
        commV (B.map (g2QAct (ZMod 2))) := by
    intro a b c
    have hsplit : codeQ ⟨selCode a 8 ^^^ selCode b 48 ^^^ selCode c 32, hcodes a b c⟩ =
        codeQ ⟨selCode a 8, by cases a <;> decide⟩ *
          codeQ ⟨selCode b 48, by cases b <;> decide⟩ *
            codeQ ⟨selCode c 32, by cases c <;> decide⟩ := by
      rw [← codeQ_xor, ← codeQ_xor]
      rfl
    rw [hsplit]
    refine Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_
    · cases a
      · exact (congrArg (· ∈ commV (B.map (g2QAct (ZMod 2)))) codeQ_zero).mpr (Subgroup.one_mem _)
      · exact h8
    · cases b
      · exact (congrArg (· ∈ commV (B.map (g2QAct (ZMod 2)))) codeQ_zero).mpr (Subgroup.one_mem _)
      · exact h48
    · cases c
      · exact (congrArg (· ∈ commV (B.map (g2QAct (ZMod 2)))) codeQ_zero).mpr (Subgroup.one_mem _)
      · exact h32
  let F : Bool × Bool × Bool → ↥(commV (B.map (g2QAct (ZMod 2)))) := fun t =>
    ⟨_, hprod t.1 t.2.1 t.2.2⟩
  have hF : Function.Injective F := by
    rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
    have h1 := congrArg Subtype.val h
    change codeQ _ = codeQ _ at h1
    rw [codeQ_eq_iff] at h1
    have key : ∀ a b c a' b' c' : Bool,
        (selCode a' 8 ^^^ selCode b' 48 ^^^ selCode c' 32 =
            selCode a 8 ^^^ selCode b 48 ^^^ selCode c 32 ∨
          selCode a' 8 ^^^ selCode b' 48 ^^^ selCode c' 32 =
            selCode a 8 ^^^ selCode b 48 ^^^ selCode c 32 ^^^ 129) →
        a = a' ∧ b = b' ∧ c = c' := by decide
    obtain ⟨rfl, rfl, rfl⟩ := key a b c a' b' c' h1
    rfl
  have : Finite ModQ := Nat.finite_of_card_ne_zero (by rw [card_ModQ]; norm_num)
  have h := Nat.card_le_card_of_injective F hF
  simpa using h

theorem wordG_fix_x₀
    {w : List ℕ} (hw : w ∈ [tW1, tW2]) :
    g2QAct (ZMod 2) (B42U33.wordG w) x₀ = x₀ := by
  have h8 : mact (matCode (B42U33.wordG w).1) 8 = 8 := by
    change mact (matCode (wordE w)) 8 = 8
    rw [matCode_wordE]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    exacts [fix_eight.2.1, fix_eight.2.2.1]
  rw [x₀, g2QAct_codeQ_mk _ eight_mem_o0Codes (by rw [h8]; exact eight_mem_o0Codes)]
  exact congrArg codeQ (Subtype.ext h8)

theorem conj_pow4_mem {Γ : Type*} [Group Γ] {B : Subgroup Γ} {r t : Γ}
    (h : ∀ c ∈ B, (r⁻¹ * t * r) ^ 4 * c * ((r⁻¹ * t * r) ^ 4)⁻¹ ∈ B) {b : Γ} (hb : b ∈ B) :
    t ^ 4 * (MulAut.conj r).toMonoidHom b * (t ^ 4)⁻¹ ∈ B.map (MulAut.conj r).toMonoidHom := by
  refine ⟨_, h b hb, ?_⟩
  have e : (r⁻¹ * t * r) ^ 4 = r⁻¹ * t ^ 4 * r := by
    simpa using conj_pow (a := r⁻¹) (b := t) (i := 4)
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, e]
  group

theorem e4_of_fix
    {x : ModQ} (hx : x ≠ 1) {Z : Subgroup (MulAut ModQ)}
    (hZG : Z ≤ (g2QAct (ZMod 2)).range) (hZ1 : Z ≠ ⊥) (hZ2 : ∀ z ∈ Z, z ^ 2 = 1)
    (hZc : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a) (hZ4 : Nat.card Z ≤ 4) (hZx : ∀ z ∈ Z, z x = x)
    (hZn : ∀ t ∈ g2Derived (ZMod 2), g2QAct (ZMod 2) t x = x → ∀ z ∈ Z,
      g2QAct (ZMod 2) t ^ 4 * z * (g2QAct (ZMod 2) t ^ 4)⁻¹ ∈ Z) :
    Nat.card Z = 4 ∧ 8 ≤ Nat.card (commV Z) := by
  classical
  have hinj := g2QAct_injective
  have hBZ : (Z.comap (g2QAct (ZMod 2))).map (g2QAct (ZMod 2)) = Z :=
    Subgroup.map_comap_eq_self hZG
  have hBx : Z.comap (g2QAct (ZMod 2)) ≤ stabQ x := fun b hb => hZx _ hb
  have hB2 : ∀ b ∈ Z.comap (g2QAct (ZMod 2)), b ^ 2 = 1 := fun b hb =>
    hinj (by rw [map_pow, map_one]; exact hZ2 _ hb)
  have hBc : ∀ a ∈ Z.comap (g2QAct (ZMod 2)), ∀ b ∈ Z.comap (g2QAct (ZMod 2)),
      a * b = b * a := fun a ha b hb =>
    hinj (by rw [map_mul, map_mul]; exact hZc _ ha _ hb)
  have hBp : IsPGroup 2 ↥(Z.comap (g2QAct (ZMod 2))) := fun g =>
    ⟨1, Subtype.ext (by rw [pow_one]; exact hB2 g.1 g.2)⟩
  obtain ⟨r, hrx, hle⟩ := exists_conj_le_sSubG hx hBp hBx
  have hcardB : Nat.card ((Z.comap (g2QAct (ZMod 2))).map (MulAut.conj r).toMonoidHom) =
      Nat.card Z := by
    rw [Subgroup.card_map_of_injective (MulAut.conj r).injective]
    conv_rhs => rw [← hBZ]
    rw [Subgroup.card_map_of_injective hinj]
  have hB'1 : (Z.comap (g2QAct (ZMod 2))).map (MulAut.conj r).toMonoidHom ≠ ⊥ := fun h =>
    hZ1 (Subgroup.eq_bot_of_card_eq _ (by rw [← hcardB, h, Subgroup.card_bot]))
  have hB'2 : ∀ b ∈ (Z.comap (g2QAct (ZMod 2))).map (MulAut.conj r).toMonoidHom,
      b ^ 2 = 1 := by
    rintro _ ⟨b, hb, rfl⟩
    rw [← MonoidHom.map_pow, hB2 b hb, MonoidHom.map_one]
  have hB'c : ∀ a ∈ (Z.comap (g2QAct (ZMod 2))).map (MulAut.conj r).toMonoidHom,
      ∀ b ∈ (Z.comap (g2QAct (ZMod 2))).map (MulAut.conj r).toMonoidHom, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← MonoidHom.map_mul, ← MonoidHom.map_mul, hBc a ha b hb]
  have hB'n : ∀ w ∈ [tW1, tW2],
      ∀ b ∈ (Z.comap (g2QAct (ZMod 2))).map (MulAut.conj r).toMonoidHom,
      B42U33.wordG w ^ 4 * b * (B42U33.wordG w ^ 4)⁻¹ ∈
        (Z.comap (g2QAct (ZMod 2))).map (MulAut.conj r).toMonoidHom := by
    rintro w hw _ ⟨b, hb, rfl⟩
    refine conj_pow4_mem (fun c hc => ?_) hb
    have htd : r⁻¹ * B42U33.wordG w * r⁻¹⁻¹ ∈ g2Derived (ZMod 2) :=
      (g2Derived_isNormal (ZMod 2)).conj_mem _ (B42U33.wordG_mem w) r⁻¹
    rw [inv_inv] at htd
    have htx : g2QAct (ZMod 2) (r⁻¹ * B42U33.wordG w * r) x = x := by
      rw [MonoidHom.map_mul, MonoidHom.map_mul, MulAut.mul_apply, MulAut.mul_apply, hrx,
        wordG_fix_x₀ hw, MonoidHom.map_inv, ← hrx, MulAut.inv_apply_self]
    rw [Subgroup.mem_comap, MonoidHom.map_mul, MonoidHom.map_mul, MonoidHom.map_inv,
      MonoidHom.map_pow]
    exact hZn _ htd htx _ hc
  obtain ⟨h4, -, hs4, hs6⟩ := finite_e4 hle hB'1 hB'2 hB'c (by rw [hcardB]; exact hZ4) hB'n
  refine ⟨hcardB.symm.trans h4, ?_⟩
  have h8 := eight_le_card_commV hs4 hs6
  have hmap : ((Z.comap (g2QAct (ZMod 2))).map (MulAut.conj r).toMonoidHom).map
      (g2QAct (ZMod 2)) = Z.map (MulAut.congr (g2QAct (ZMod 2) r)).toMonoidHom := by
    conv_rhs => rw [← hBZ]
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    refine MonoidHom.ext fun b => ?_
    change g2QAct (ZMod 2) (r * b * r⁻¹) =
      MulAut.congr (g2QAct (ZMod 2) r) (g2QAct (ZMod 2) b)
    rw [MonoidHom.map_mul, MonoidHom.map_mul, MonoidHom.map_inv]
    ext v
    rfl
  rw [hmap, H13.commV_map_congr, Subgroup.card_map_of_injective
    (f := (g2QAct (ZMod 2) r).toMonoidHom) (g2QAct (ZMod 2) r).injective] at h8
  exact h8

end A6G2

end CFSG.Quasithin.H13.A6
