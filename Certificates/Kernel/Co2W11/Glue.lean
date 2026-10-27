
module

public import Certificates.Kernel.Co2W11.Forms
public import Certificates.Kernel.Co2W11.OWords
public import CFSG.Certificates.Kernel.F2TriSepSound
public import CFSG.Certificates.Kernel.F2FormIdSound
public import CFSG.Certificates.Kernel.VecKRegs
public import CFSG.GF2Type.Widths1112.Co2FormsBase
import all CFSG.Blueprint.NativeSporadic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CertificateChecks.KernelCo2W11

open CFSG.GF2Type.Widths1112 CFSG.Blueprint CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
  CFSG.GF2W1112 CFSG.KC.M1F2 CFSG.KC.Co1F2 CFSG.KC.F2W CFSG.KC.F2TriSep CFSG.KC.F2FormId
  CFSG.KC.F2OrbW CertificateChecks.KernelLC.Co2Ops Matrix

theorem unpack_SA : unpackR 22 SA.M = w12Co2RowsA () := by
  rw [← bind_sound SA.bind, ← SA.eq]
  rfl

theorem unpack_SB : unpackR 22 SB.M = w12Co2RowsB () := by
  rw [← bind_sound SB.bind, ← SB.eq]
  rfl

theorem unpack_wordB (w : List Bool) : ∀ acc : Nat, unpackR 22 (wordB 22 SA.M SB.M w acc) =
    w.foldl (fun acc b => mulRows 22 acc (if b then w12Co2RowsA () else w12Co2RowsB ()))
      (unpackR 22 acc) := by
  induction w with
  | nil => intro acc; rfl
  | cons b w ih =>
    intro acc
    rw [List.foldl_cons]
    have e : wordB 22 SA.M SB.M (b :: w) acc =
        wordB 22 SA.M SB.M w (mulW 22 acc (if b then SA.M else SB.M)) := by
      cases b <;> exact strictN_eq _ _
    rw [e, ih, ← mulRows_unpackW]
    cases b
    · rw [if_neg (by decide), if_neg (by decide), unpack_SB]
    · rw [if_pos rfl, if_pos rfl, unpack_SA]

theorem mat_word (w : List Bool) : rowsMatrix 22 (unpackR 22 (wordB 22 SA.M SB.M w (idF 22))) =
    rowsMatrix 22 (w12WordRows (w12Co2RowsA ()) (w12Co2RowsB ()) w) := by
  rw [unpack_wordB, CFSG.KC.VecK.unpackR_idF]
  rfl

theorem exists_word_elt (w : List Bool) :
    ∃ g : NativeSporadic.Co2, ∀ v,
      co2Act g v = rowsMatrix 22 (unpackR 22 (wordB 22 SA.M SB.M w (idF 22))) *ᵥ v := by
  obtain ⟨g, hg⟩ := exists_co2_word w
  exact ⟨g, fun v => by rw [co2Act_def, hg, mat_word]⟩

theorem mat_mulVec (g v : Nat) :
    rowsMatrix 22 (unpackR 22 g) *ᵥ toVecD 22 v = toVecD 22 (vmF 22 (trK 22 g) v) := by
  rw [rowsMatrix_mulVec, transposeRows_unpackR, vecMulN_unpackR]

theorem mem_gensOf {ws : List (List Bool)} {g : Nat} (h : g ∈ gensOf ws) :
    ∃ w, g = wordB 22 SA.M SB.M w (idF 22) := by
  induction ws with
  | nil => exact absurd h List.not_mem_nil
  | cons w ws ih =>
    change g ∈ wordB 22 SA.M SB.M w (idF 22) :: gensOf ws at h
    rcases List.mem_cons.1 h with rfl | h'
    · exact ⟨w, rfl⟩
    · exact ih h'

theorem fixL_mem {G : List Nat} {w : Nat} (h : fixL 22 G w = true) :
    ∀ g ∈ G, vmF 22 (trK 22 g) w = w := by
  induction G with
  | nil => intro g hg; exact absurd hg List.not_mem_nil
  | cons g G ih =>
    have hab : Nat.beq (vmF 22 (trK 22 g) w) w = true ∧ fixL 22 G w = true := by
      revert h
      change CFSG.KLie.CT.andB (Nat.beq (vmF 22 (trK 22 g) w) w) (fixL 22 G w) = true → _
      cases Nat.beq (vmF 22 (trK 22 g) w) w <;> cases fixL 22 G w <;> decide
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx'
    · exact Nat.eq_of_beq_eq_true hab.1
    · exact ih hab.2 x hx'

theorem gens_pres {ws : List (List Bool)} {w : Nat}
    (hfix : fixL 22 (gensOf ws) w = true) (U : Submodule (ZMod 2) Vec22)
    (hU : ∀ g : NativeSporadic.Co2, co2Act g (toVecD 22 w) = toVecD 22 w → ∀ u ∈ U, co2Act g u ∈ U) :
    ∀ g ∈ gensOf ws, ∀ u ∈ U, rowsMatrix 22 (unpackR 22 g) *ᵥ u ∈ U := by
  intro g hg u hu
  obtain ⟨wd, rfl⟩ := mem_gensOf hg
  obtain ⟨x, hx⟩ := exists_word_elt wd
  rw [← hx]
  refine hU x ?_ u hu
  rw [hx, mat_mulVec, fixL_mem hfix _ hg]

theorem wordsToK_mem {A B v : Nat} {P : List (Nat × List Bool)} (h : wordsToK 22 A B v P = true) :
    ∀ p ∈ P, vmF 22 (trK 22 (wordB 22 A B p.2 (idF 22))) v = p.1 := by
  induction P with
  | nil => intro p hp; exact absurd hp List.not_mem_nil
  | cons e P ih =>
    obtain ⟨t, w⟩ := e
    have hab : Nat.beq (vmF 22 (trK 22 (wordB 22 A B w (idF 22))) v) t = true ∧
        wordsToK 22 A B v P = true := by
      revert h
      change (Nat.beq (vmF 22 (trK 22 (wordB 22 A B w (idF 22))) v) t && wordsToK 22 A B v P)
        = true → _
      rw [Bool.and_eq_true]
      exact id
    intro p hp
    rcases List.mem_cons.1 hp with rfl | hp'
    · exact Nat.eq_of_beq_eq_true hab.1
    · exact ih hab.2 p hp'

theorem ow_mem {p : Nat × List Bool} (hp : p ∈ Ow.ts.zip Ow.ws) :
    toVecD 22 p.1 ∈ co2Orbit 0 := by
  obtain ⟨x, hx⟩ := exists_word_elt p.2
  refine ⟨x, ?_⟩
  change co2Act x (toVecD 22 40) = toVecD 22 p.1
  rw [hx, mat_mulVec, wordsToK_mem owords_ok p hp]

@[expose] noncomputable def tgtOK (ts : List Nat) (r : Nat) : Bool :=
  (List.range 20).all fun k => (Ow.ts.zip Ow.ws).any (fun p => p.1 == getL 0 ts k) &&
    getL 0 ts k != r && decide (getL 0 ts k < 2 ^ 22)

theorem f3_rep {words : List (List Bool)}
    {tree : List (Nat × Nat)} {masks ts : List Nat} {F Dm w r : Nat}
    (htri : triK 22 (gensOf words) tree masks ts F Dm w = true)
    (hfix : fixL 22 (gensOf words) w = true) (hwr : w = r) (htgt : tgtOK ts r = true) (hr : r < 2 ^ 22)
    (hF0 : toVecD 22 (rowF 22 F 0) = (Qm22 + Qm22ᵀ) *ᵥ toVecD 22 r)
    (U : Submodule (ZMod 2) Vec22) (hrU : toVecD 22 r ∈ U)
    (hperp : ∀ u ∈ U, bil₀₂ u (toVecD 22 r) = 0)
    (hU : ∀ g : NativeSporadic.Co2, co2Act g (toVecD 22 r) = toVecD 22 r → ∀ u ∈ U, co2Act g u ∈ U)
    (y : Vec22) (hyU : y ∈ U) (hy : y ∉ Submodule.span (ZMod 2) {toVecD 22 r}) :
    ∃ u ∈ U, u ≠ toVecD 22 r ∧ u ∈ co2Orbit 0 := by
  subst hwr
  have h0 : toVecD 22 (rowF 22 F 0) ⬝ᵥ y = 0 := by
    rw [hF0, ← bil₀₂_eq_F, bil₀₂_comm]
    exact hperp y hyU
  obtain ⟨k, hk, hkU⟩ := triK_sound htri U (gens_pres hfix U hU) hrU hyU h0 hy
  have hk' : k < 20 := hk
  have ht := List.all_eq_true.1 htgt k (List.mem_range.2 hk')
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at ht
  obtain ⟨⟨hany, hne⟩, hlt⟩ := ht
  obtain ⟨p, hp, hpe⟩ := List.any_eq_true.1 hany
  refine ⟨_, hkU, fun e => hne (toVecD_injective hlt hr e), ?_⟩
  rw [← beq_iff_eq.1 hpe]
  exact ow_mem hp

theorem irr_rep0
    (hts : (List.range 20).all (fun k => getL 0 S0.ts k == S0.spinV) = true)
    (hF0 : toVecD 22 (rowF 22 S0.F 0) = (Qm22 + Qm22ᵀ) *ᵥ toVecD 22 40)
    (he : bil₀₂ (toVecD 22 S0.spinE) (toVecD 22 40) = 1)
    (Y : Submodule (ZMod 2) Vec22) (hrY : toVecD 22 40 ∈ Y)
    (hperp : ∀ y ∈ Y, bil₀₂ y (toVecD 22 40) = 0)
    (hinv : ∀ g : NativeSporadic.Co2, co2Act g (toVecD 22 40) = toVecD 22 40 →
      ∀ y ∈ Y, co2Act g y ∈ Y) :
    Y = Submodule.span (ZMod 2) {toVecD 22 40} ∨ ∀ y, bil₀₂ y (toVecD 22 40) = 0 → y ∈ Y := by
  by_cases hsub : Y ≤ Submodule.span (ZMod 2) {toVecD 22 40}
  · exact Or.inl (le_antisymm hsub ((Submodule.span_singleton_le_iff_mem _ _).2 hrY))
  right
  obtain ⟨y, hyY, hy⟩ : ∃ y ∈ Y, y ∉ Submodule.span (ZMod 2) {toVecD 22 40} := by
    by_contra hcon
    push Not at hcon
    exact hsub fun z hz => hcon z hz
  have hG := gens_pres (ws := S0.words) (w := 40) fix0_ok Y hinv
  have h0 : toVecD 22 (rowF 22 S0.F 0) ⬝ᵥ y = 0 := by
    rw [hF0, ← bil₀₂_eq_F, bil₀₂_comm]
    exact hperp y hyY
  obtain ⟨k, hk, hkY⟩ := triK_sound sep0_ok Y hG hrY hyY h0 hy
  have hk' : k < 20 := hk
  have hv : toVecD 22 S0.spinV ∈ Y := by
    have h := List.all_eq_true.1 hts k (List.mem_range.2 hk')
    rw [← beq_iff_eq.1 h]
    exact hkY
  intro x hx
  obtain ⟨a, ha⟩ := spinK_sound spin0_ok Y hG hv x
  have hcase : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  rcases hcase a with rfl | rfl
  · rw [zero_smul, add_zero] at ha
    exact ha
  · exfalso
    have h := hperp _ ha
    rw [one_smul, bil₀₂_add_left, hx, he] at h
    exact absurd h (by decide)

theorem unpack_Q : unpackR 22 Fm.Q = w12Co2QRows := by decide +kernel

theorem unpack_polF : unpackR 22 (polF Fm.Q) = w12Co2F0Rows () := by decide +kernel

theorem mat_Q : rowsMatrix 22 (unpackR 22 Fm.Q) = Qm22 := by
  rw [unpack_Q]
  rfl

theorem mat_polF : rowsMatrix 22 (unpackR 22 (polF Fm.Q)) = Qm22 + Qm22ᵀ := by
  rw [unpack_polF, co2F0_eq]

theorem mat_idF : rowsMatrix 22 (unpackR 22 (idF 22)) = 1 := by
  rw [CFSG.KC.VecK.unpackR_idF, rowsMatrix_idRows]

theorem mat_mulW (X Y : Nat) :
    rowsMatrix 22 (unpackR 22 (mulW 22 X Y)) = rowsMatrix 22 (unpackR 22 X) * rowsMatrix 22 (unpackR 22 Y) := by
  rw [← mulRows_unpackW, rowsMatrix_mulRows]

theorem q_mat {M : Nat} (h : invQK 22 Fm.Q M = true) (x : Vec22) :
    q₀₂ (rowsMatrix 22 (unpackR 22 M) *ᵥ x) = q₀₂ x := by
  have e := invQK_sound h x
  rw [mat_Q] at e
  exact e

theorem mat_SA :
    rowsMatrix 22 (unpackR 22 SA.M) = NativeSporadic.decode 2 22 1 NativeSporadic.Co2Seed1 := by
  rw [unpack_SA]
  exact rowsMatrix_rowsOfPayload 22 NativeSporadic.Co2Seed1

theorem mat_SB :
    rowsMatrix 22 (unpackR 22 SB.M) = NativeSporadic.decode 2 22 1 NativeSporadic.Co2Seed2 := by
  rw [unpack_SB]
  exact rowsMatrix_rowsOfPayload 22 NativeSporadic.Co2Seed2

theorem forms_q (g : NativeSporadic.Co2) (v : Vec22) : q₀₂ (co2Act g v) = q₀₂ v := by
  have hAB := invQ_ok
  rw [Bool.and_eq_true] at hAB
  have hmem : (g.val.val : Matrix (Fin 22) (Fin 22) (ZMod 2)) ∈ Submonoid.closure
      ({NativeSporadic.decode 2 22 1 NativeSporadic.Co2Seed1,
        NativeSporadic.decode 2 22 1 NativeSporadic.Co2Seed2} :
        Set (Matrix (Fin 22) (Fin 22) (ZMod 2))) := g.val.2
  rw [co2Act_def]
  generalize (g.val.val : Matrix (Fin 22) (Fin 22) (ZMod 2)) = M at hmem ⊢
  induction hmem using Submonoid.closure_induction generalizing v with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · rw [← mat_SA]
      exact q_mat hAB.1 v
    · rw [← mat_SB]
      exact q_mat hAB.2 v
  | one => rw [Matrix.one_mulVec]
  | mul x y _ _ hx hy => rw [← Matrix.mulVec_mulVec, hx, hy]

theorem forms_nondeg (u : Vec22) (h : ∀ v, bil₀₂ u v = 0) : u = 0 := by
  have hFu : (Qm22 + Qm22ᵀ) *ᵥ u = 0 := by
    funext i
    have hi := h (Pi.single i 1)
    rw [bil₀₂_eq_F, dotProduct_single] at hi
    simpa only [mul_one, Pi.zero_apply] using hi
  have hMN : rowsMatrix 22 (unpackR 22 (polF Fm.Q)) * rowsMatrix 22 (unpackR 22 Fm.Finv) = 1 := by
    rw [← mat_mulW, Nat.eq_of_beq_eq_true nondeg_ok, mat_idF]
  have hNM := (Matrix.mul_eq_one_comm_of_card_eq (Fin 22) (Fin 22) (ZMod 2) rfl).1 hMN
  rw [mat_polF] at hNM
  calc u = (rowsMatrix 22 (unpackR 22 Fm.Finv) * (Qm22 + Qm22ᵀ)) *ᵥ u := by
        rw [hNM, Matrix.one_mulVec]
    _ = 0 := by rw [← Matrix.mulVec_mulVec, hFu, Matrix.mulVec_zero]

theorem covec_vecMul (H : Matrix (Fin 22) (Fin 22) (ZMod 2)) (c : Vec22)
    (h : ∀ y, c ⬝ᵥ (H *ᵥ y) = c ⬝ᵥ y) : c ᵥ* H = c := by
  funext j
  have h1 := h (Pi.single j 1)
  rw [Matrix.dotProduct_mulVec, dotProduct_single, dotProduct_single, mul_one, mul_one] at h1
  exact h1

theorem exists_seed_elt (b : Bool) :
    ∃ g : NativeSporadic.Co2, ∀ v,
      co2Act g v = rowsMatrix 22 (unpackR 22 (if b then SA.M else SB.M)) *ᵥ v := by
  obtain ⟨g, hg⟩ := exists_word_elt [b]
  refine ⟨g, fun v => ?_⟩
  rw [hg, mat_word]
  change rowsMatrix 22 (mulRows 22 (idRows 22) (if b then w12Co2RowsA () else w12Co2RowsB ())) *ᵥ v = _
  rw [rowsMatrix_mulRows, rowsMatrix_idRows, one_mul]
  cases b
  · rw [if_neg (by decide), if_neg (by decide), unpack_SB]
  · rw [if_pos rfl, if_pos rfl, unpack_SA]

theorem forms_nofix (c : Vec22)
    (h : ∀ (g : NativeSporadic.Co2) (v : Vec22), c ⬝ᵥ co2Act g v = c ⬝ᵥ v) : c = 0 := by
  have hb : ∀ b : Bool, c ᵥ* rowsMatrix 22 (unpackR 22 (if b then SA.M else SB.M)) = c := by
    intro b
    obtain ⟨g, hg⟩ := exists_seed_elt b
    exact covec_vecMul _ c fun y => by rw [← hg]; exact h g y
  have hs := fixSumK_sound (d := 22) (P := [(SA.M, Fm.X1), (SB.M, Fm.X2)]) (c := c) (by
    intro e he
    rcases List.mem_cons.1 he with rfl | he
    · exact hb true
    · rw [List.mem_singleton] at he
      subst he
      exact hb false)
  rw [Nat.eq_of_beq_eq_true nofix_ok, mat_idF, Matrix.vecMul_one] at hs
  exact hs

theorem toVecD_two_pow (p : Fin 22) : toVecD 22 (2 ^ p.val) = Pi.single p 1 := by
  funext j
  rw [toVecD_apply, Nat.testBit_two_pow, Pi.single_apply]
  by_cases h : j = p
  · subst h
    simp
  · have h' : ¬ (p.val = j.val) := fun e => h (Fin.ext e).symm
    simp [h, h']

theorem rows_fixH0 : ∀ i : Fin 22,
    rowF 22 (Nat.xor (idF 22) (Nat.shiftLeft Fm.lam (Nat.mul 22 Fm.p))) i.val =
      if i.val = 3 then 2 ^ i.val ^^^ Fm.lam else 2 ^ i.val := by
  decide +kernel

theorem vecMul_fixH0 (c : Vec22) :
    c ᵥ* rowsMatrix 22 (unpackR 22 (Nat.xor (idF 22) (Nat.shiftLeft Fm.lam (Nat.mul 22 Fm.p)))) =
      c + c 3 • toVecD 22 Fm.lam := by
  have hrow : ∀ i : Fin 22,
      rowsMatrix 22 (unpackR 22 (Nat.xor (idF 22) (Nat.shiftLeft Fm.lam (Nat.mul 22 Fm.p)))) i =
        Pi.single i 1 + if i = 3 then toVecD 22 Fm.lam else 0 := by
    intro i
    have e : (unpackR 22 (Nat.xor (idF 22) (Nat.shiftLeft Fm.lam (Nat.mul 22 Fm.p))))[i.val]? =
        some (rowF 22 (Nat.xor (idF 22) (Nat.shiftLeft Fm.lam (Nat.mul 22 Fm.p))) i.val) := by
      simp [unpackR, rowF_eq, i.isLt]
    funext j
    rw [rowsMatrix_apply, e, Option.getD_some, rows_fixH0 i]
    by_cases hi : i = 3
    · have hi' : i.val = 3 := by rw [hi]; rfl
      rw [if_pos hi', if_pos hi, toVecD_xor, toVecD_two_pow]
    · have hi' : ¬ (i.val = 3) := fun h => hi (Fin.ext h)
      rw [if_neg hi', if_neg hi, toVecD_two_pow, add_zero]
  generalize toVecD 22 Fm.lam = L at hrow ⊢
  generalize rowsMatrix 22 (unpackR 22 (Nat.xor (idF 22) (Nat.shiftLeft Fm.lam (Nat.mul 22 Fm.p))))
    = M at hrow ⊢
  funext j
  change ∑ i, c i * M i j = c j + c 3 * L j
  have e : ∀ i, c i * M i j = (if i = j then c i else 0) + (if i = 3 then c i * L j else 0) := by
    intro i
    rw [hrow i, Pi.add_apply, Pi.single_apply, mul_add]
    split_ifs <;> simp_all
  rw [Finset.sum_congr rfl (fun i _ => e i), Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]

theorem forms_fixH0 (c : Vec22)
    (h : ∀ g : NativeSporadic.Co2, co2Act g (toVecD 22 40) = toVecD 22 40 →
      ∀ v : Vec22, c ⬝ᵥ co2Act g v = c ⬝ᵥ v) :
    c = 0 ∨ ∀ v : Vec22, c ⬝ᵥ v = bil₀₂ (toVecD 22 40) v := by
  have hH := fixH0_ok
  simp only [Bool.and_eq_true] at hH
  obtain ⟨⟨hlam, -⟩, hsum⟩ := hH
  have hw : S0.w = 40 := by decide +kernel
  have hfix := fix0_ok
  rw [hw] at hfix
  have hR : ∀ R ∈ gensOf S0.words, c ᵥ* rowsMatrix 22 (unpackR 22 R) = c := by
    intro R hR
    obtain ⟨wd, rfl⟩ := mem_gensOf hR
    obtain ⟨x, hx⟩ := exists_word_elt wd
    refine covec_vecMul _ c fun y => ?_
    rw [← hx]
    refine h x ?_ y
    rw [hx, mat_mulVec, fixL_mem hfix _ hR]
  have hs := fixSumK_sound (d := 22) (P := (gensOf S0.words).zip Fm.Xs) (c := c)
    (fun e he => hR e.1 (List.of_mem_zip he).1)
  rw [Nat.eq_of_beq_eq_true hsum, vecMul_fixH0] at hs
  have hc : c = c 3 • toVecD 22 Fm.lam := by
    calc c = c + c 3 • toVecD 22 Fm.lam + c 3 • toVecD 22 Fm.lam := by
          rw [add_assoc, add_self_vec, add_zero]
      _ = c 3 • toVecD 22 Fm.lam := by rw [hs, zero_add]
  have hlamv : toVecD 22 Fm.lam = (Qm22 + Qm22ᵀ) *ᵥ toVecD 22 40 := by
    rw [← mat_polF, mat_mulVec, Nat.eq_of_beq_eq_true hlam]
  have hcase : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  rcases hcase (c 3) with h0 | h1
  · left
    rw [hc, h0, zero_smul]
  · right
    intro v
    rw [hc, h1, one_smul, hlamv, ← bil₀₂_eq_F]

theorem forms_reps : ∀ i < 3, toVecD 22 (w12Co2Rep i) ≠ 0 ∧ q₀₂ (toVecD 22 (w12Co2Rep i)) = 0 := by
  have key : ∀ r : Nat, r ≠ 0 → r < 2 ^ 22 → w12QN 22 (w12Co2QT ()) r = false →
      toVecD 22 r ≠ 0 ∧ q₀₂ (toVecD 22 r) = 0 := by
    intro r hr hlt hq
    refine ⟨fun h0 => hr (toVecD_injective hlt (by positivity)
      (h0.trans (toVecD_zero 22).symm)), ?_⟩
    rw [q₀₂_toVecD, hq]
    rfl
  intro i hi
  interval_cases i
  · exact key 40 (by decide) (by decide) (by decide +kernel)
  · exact key 65536 (by decide) (by decide) (by decide +kernel)
  · exact key 8 (by decide) (by decide) (by decide +kernel)

theorem s0_ts : (List.range 20).all (fun k => getL 0 S0.ts k == S0.spinV) = true := by
  decide +kernel

theorem s1_tgt : tgtOK S1.ts (w12Co2Rep 1) = true := by decide +kernel

theorem s2_tgt : tgtOK S2.ts (w12Co2Rep 2) = true := by decide +kernel

theorem s1_w : S1.w = w12Co2Rep 1 := by decide +kernel

theorem s2_w : S2.w = w12Co2Rep 2 := by decide +kernel

theorem s0_w : S0.w = 40 := by decide +kernel

theorem f0_row (F r : Nat) (h : rowF 22 F 0 = vecMulN 22 (w12Co2FT ()) r) :
    toVecD 22 (rowF 22 F 0) = (Qm22 + Qm22ᵀ) *ᵥ toVecD 22 r := by
  rw [h, co2F0_eq, rowsMatrix_mulVec]
  rfl

theorem s0_F0 : rowF 22 S0.F 0 = vecMulN 22 (w12Co2FT ()) 40 := by decide +kernel

theorem s1_F0 : rowF 22 S1.F 0 = vecMulN 22 (w12Co2FT ()) (w12Co2Rep 1) := by decide +kernel

theorem s2_F0 : rowF 22 S2.F 0 = vecMulN 22 (w12Co2FT ()) (w12Co2Rep 2) := by decide +kernel

theorem s0_spinE : w12BN 22 (w12Co2FT ()) S0.spinE 40 = true := by decide +kernel

theorem pair_1 : w12BN 22 (w12Co2FT ()) 1 40 = false := by decide +kernel

theorem pair_128 : w12BN 22 (w12Co2FT ()) 128 40 = false := by decide +kernel

theorem pair_1_128 : w12BN 22 (w12Co2FT ()) 1 128 = true := by decide +kernel

end CertificateChecks.KernelCo2W11

end
