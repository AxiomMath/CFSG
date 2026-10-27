module

public import CFSG.LocalAnalysis.WeakClosure81.W183FinSp44Refine
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bAut
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Sp44

open CFSG.GH74.KGroups
open CFSG.ComponentClassification.UnbalancedCatalog

instance instCharPGF4 : CharP GF4 2 :=
  CharTwo.of_one_ne_zero_of_two_eq_zero (by decide) (by decide)

abbrev S4 : Type := SpChain.antiSp GF4

theorem validB_iff {x : El} :
    validB x = true ↔ x.1 < 4294967296 ∧ symp x.1 = true ∧ x.2 < 4 := by
  simp [validB, and_assoc]

theorem validB_symp {x : El} (h : validB x = true) : symp x.1 = true := (validB_iff.mp h).2.1

private theorem w183finSp44_gmul_lt {a b : Nat} (ha : a < 4) (hb : b < 4) : gmul a b < 4 := by
  interval_cases a <;> interval_cases b <;> decide

private theorem w183finSp44_e2_lt (M i j : Nat) : e2 M i j < 4 := by
  unfold e2
  exact Nat.and_lt_two_pow _ (y := 3) (n := 2) (by norm_num)

private theorem w183finSp44_or8_lo (a b c d e f g h : Nat) (ha : a < 4) (hb : b < 4)
    (hc : c < 4) (hd : d < 4) (he : e < 4) (hf : f < 4) (hg : g < 4) (hh : h < 4) :
    a ||| (b <<< 2) ||| (c <<< 4) ||| (d <<< 6) ||| (e <<< 8) ||| (f <<< 10) |||
      (g <<< 12) ||| (h <<< 14) < 2^16 := by
  repeat' apply Nat.or_lt_two_pow (n := 16)
  all_goals
    first
    | apply Nat.shiftLeft_lt
    | skip
  all_goals omega

private theorem w183finSp44_or8_hi (a b c d e f g h : Nat) (ha : a < 4) (hb : b < 4)
    (hc : c < 4) (hd : d < 4) (he : e < 4) (hf : f < 4) (hg : g < 4) (hh : h < 4) :
    (a <<< 16) ||| (b <<< 18) ||| (c <<< 20) ||| (d <<< 22) ||| (e <<< 24) |||
      (f <<< 26) ||| (g <<< 28) ||| (h <<< 30) < 2^32 := by
  have hshift : (a ||| (b <<< 2) ||| (c <<< 4) ||| (d <<< 6) ||| (e <<< 8) |||
      (f <<< 10) ||| (g <<< 12) ||| (h <<< 14)) <<< 16 =
      (a <<< 16) ||| (b <<< 18) ||| (c <<< 20) ||| (d <<< 22) ||| (e <<< 24) |||
      (f <<< 26) ||| (g <<< 28) ||| (h <<< 30) := by
    rw [Nat.shiftLeft_or_distrib]
    repeat rw [Nat.shiftLeft_or_distrib]
    simp only [← Nat.shiftLeft_add]
  rw [← hshift]
  exact Nat.shiftLeft_lt (n := 16)
    (w183finSp44_or8_lo a b c d e f g h ha hb hc hd he hf hg hh)

private theorem w183finSp44_or16 (a b c d e f g h i j k l m n o p : Nat)
    (ha : a < 4) (hb : b < 4) (hc : c < 4) (hd : d < 4) (he : e < 4) (hf : f < 4)
    (hg : g < 4) (hh : h < 4) (hi : i < 4) (hj : j < 4) (hk : k < 4) (hl : l < 4)
    (hm : m < 4) (hn : n < 4) (ho : o < 4) (hp : p < 4) :
    (a ||| (b <<< 2) ||| (c <<< 4) ||| (d <<< 6) ||| (e <<< 8) ||| (f <<< 10) |||
      (g <<< 12) ||| (h <<< 14)) |||
      ((i <<< 16) ||| (j <<< 18) ||| (k <<< 20) ||| (l <<< 22) ||| (m <<< 24) |||
      (n <<< 26) ||| (o <<< 28) ||| (p <<< 30)) < 2^32 := by
  apply Nat.or_lt_two_pow (n := 32)
  · exact lt_of_lt_of_le (w183finSp44_or8_lo a b c d e f g h ha hb hc hd he hf hg hh)
      (by norm_num)
  · exact w183finSp44_or8_hi i j k l m n o p hi hj hk hl hm hn ho hp

private theorem w183finSp44_or16_left (a b c d e f g h i j k l m n o p : Nat)
    (ha : a < 4) (hb : b < 4) (hc : c < 4) (hd : d < 4) (he : e < 4) (hf : f < 4)
    (hg : g < 4) (hh : h < 4) (hi : i < 4) (hj : j < 4) (hk : k < 4) (hl : l < 4)
    (hm : m < 4) (hn : n < 4) (ho : o < 4) (hp : p < 4) :
    a ||| (b <<< 2) ||| (c <<< 4) ||| (d <<< 6) ||| (e <<< 8) ||| (f <<< 10) |||
      (g <<< 12) ||| (h <<< 14) ||| (i <<< 16) ||| (j <<< 18) ||| (k <<< 20) |||
      (l <<< 22) ||| (m <<< 24) ||| (n <<< 26) ||| (o <<< 28) ||| (p <<< 30) < 2^32 := by
  have h := w183finSp44_or16 a b c d e f g h i j k l m n o p ha hb hc hd he hf hg hh hi hj
    hk hl hm hn ho hp
  convert h using 1
  simp only [Nat.or_assoc]

private theorem w183finSp44_rho_lt (g : Nat) : rho g < 4294967296 := by
  rw [show (4294967296 : Nat) = 2^32 by norm_num]
  simp only [rho, idxA]
  apply w183finSp44_or16_left
  all_goals
    exact Nat.xor_lt_two_pow (n := 2) (w183finSp44_gmul_lt (w183finSp44_e2_lt _ _ _)
      (w183finSp44_e2_lt _ _ _)) (w183finSp44_gmul_lt (w183finSp44_e2_lt _ _ _)
      (w183finSp44_e2_lt _ _ _))

private theorem w183finSp44_rhoPow_lt (n : Nat) {g : Nat} (hg : g < 4294967296) :
    rhoPow n g < 4294967296 := by
  induction n generalizing g with
  | zero => simpa [rhoPow] using hg
  | succ n ih => simpa [rhoPow] using ih (g := rho g) (w183finSp44_rho_lt g)

private theorem w183finSp44_mulW_lt {b : Nat} (hb : b < 256) : mulW b < 256 := by
  unfold mulW
  apply Nat.or_lt_two_pow (n := 8)
  · exact lt_of_lt_of_le (Nat.and_lt_two_pow _ (y := 0x55) (n := 7) (by norm_num))
      (by norm_num)
  · apply Nat.shiftLeft_lt (n := 7)
    exact Nat.xor_lt_two_pow (Nat.and_lt_two_pow _ (y := 0x55) (n := 7) (by norm_num))
      (Nat.and_lt_two_pow _ (y := 0x55) (n := 7) (by norm_num))

private theorem w183finSp44_scal_lt {a b : Nat} (hb : b < 256) : scal a b < 256 := by
  unfold scal
  split_ifs with h0 h1 h2
  · norm_num
  · exact hb
  · exact w183finSp44_mulW_lt hb
  · apply Nat.xor_lt_two_pow (n := 8) hb
    exact w183finSp44_mulW_lt hb

private theorem w183finSp44_row_lt (M i : Nat) : row M i < 256 := by
  unfold row
  exact Nat.and_lt_two_pow _ (y := 255) (n := 8) (by norm_num)

private theorem w183finSp44_mulRow_lt (r B : Nat) : mulRow r B < 256 := by
  unfold mulRow
  repeat' apply Nat.xor_lt_two_pow (n := 8)
  all_goals exact w183finSp44_scal_lt (w183finSp44_row_lt B _)

private theorem w183finSp44_mmul_lt (A B : Nat) : mmul A B < 4294967296 := by
  rw [show (4294967296 : Nat) = 2^32 by norm_num]
  unfold mmul
  have hm0 := w183finSp44_mulRow_lt (row A 0) B
  have hm1 := w183finSp44_mulRow_lt (row A 1) B
  have hm2 := w183finSp44_mulRow_lt (row A 2) B
  have hm3 := w183finSp44_mulRow_lt (row A 3) B
  apply Nat.or_lt_two_pow (n := 32)
  · apply Nat.or_lt_two_pow (n := 32)
    · apply Nat.or_lt_two_pow (n := 32)
      · exact lt_of_lt_of_le hm0 (by norm_num)
      · exact lt_of_lt_of_le (Nat.shiftLeft_lt (n := 8) hm1) (by norm_num)
    · exact lt_of_lt_of_le (Nat.shiftLeft_lt (n := 8) hm2) (by norm_num)
  · exact Nat.shiftLeft_lt (n := 8) hm3

@[expose] noncomputable def toS4 (g : Nat) (hg : symp g = true) : S4 :=
  let M := decodeM g
  let J := SpChain.minorJ GF4
  have hJ : M.transpose * J * M = J := (symp_iff g).mp hg
  have h2 : (J * M.transpose * J) * M = 1 := by
    calc (J * M.transpose * J) * M = J * (M.transpose * J * M) := by
          simp only [Matrix.mul_assoc]
      _ = J * J := by rw [hJ]
      _ = 1 := SpChain.minorJ_mul_self
  ⟨⟨M, J * M.transpose * J, mul_eq_one_comm.mp h2, h2⟩, hJ⟩

theorem toS4_val (g : Nat) (hg : symp g = true) :
    ((toS4 g hg : GL (Fin 4) GF4) : Matrix (Fin 4) (Fin 4) GF4) = decodeM g := rfl

@[expose] noncomputable def autOf (x : El) : MulAut S4 :=
  if h : validB x = true then
    MulAut.conj (toS4 x.1 (validB_symp h)) * SpChain.minorAut GF4 ^ x.2
  else 1

theorem validB_oneE : validB oneE = true := by
  decide

private theorem w183finSp44_toS4_idM (h : symp idM = true) : toS4 idM h = 1 := by
  apply Subtype.ext
  apply Units.ext
  rw [toS4_val, decodeM_idM]
  rfl

private theorem w183finSp44_symp_mmul {a b : Nat} (ha : symp a = true) (hb : symp b = true) :
    symp (mmul a b) = true := by
  rw [symp_iff]
  rw [decodeM_mmul]
  have hmem : (toS4 a ha * toS4 b hb : GL (Fin 4) GF4) ∈ SpChain.antiSp GF4 :=
    (SpChain.antiSp GF4).mul_mem (toS4 a ha).2 (toS4 b hb).2
  have h := (SpChain.mem_antiSp.mp hmem)
  simpa only [SpChain.glMat, Units.val_mul, toS4_val] using h

private theorem w183finSp44_symp_Jm : symp Jm = true := by
  rw [symp_iff, decodeM_Jm, SpChain.minorJ_transpose, SpChain.minorJ_mul_self]
  rw [Matrix.one_mul]

private theorem w183finSp44_symp_transp {g : Nat} (hg : symp g = true) :
    symp (transp g) = true := by
  have hg' := hg
  rw [symp_iff] at hg ⊢
  rw [decodeM_transp]
  have hmem : (toS4 g hg' : GL (Fin 4) GF4) ∈ SpChain.antiSp GF4 := (toS4 g hg').2
  have h := SpChain.mul_minorJ_mul_transpose_of_mem hmem
  simp only [SpChain.glMat] at h
  rw [toS4_val] at h
  simpa using h

theorem symp_rho {g : Nat} (hg : symp g = true) : symp (rho g) = true := by
  have hg' := hg
  rw [symp_iff] at hg ⊢
  rw [decodeM_rho]
  have hmem : (toS4 g hg' : GL (Fin 4) GF4) ∈ SpChain.antiSp GF4 := (toS4 g hg').2
  have h := SpChain.minorMap_mem hmem
  simp only [SpChain.glMat] at h
  rw [toS4_val] at h
  simpa using h

private theorem w183finSp44_symp_rhoPow (n : Nat) {g : Nat} (hg : symp g = true) :
    symp (rhoPow n g) = true := by
  induction n generalizing g with
  | zero => simpa [rhoPow] using hg
  | succ n ih => simpa [rhoPow] using ih (g := rho g) (symp_rho hg)

theorem minorAut_toS4 (g : Nat) (hg : symp g = true) :
    SpChain.minorAut GF4 (toS4 g hg) = toS4 (rho g) (symp_rho hg) := by
  apply Subtype.ext
  apply Units.ext
  apply Matrix.ext
  intro i j
  change SpChain.glMat ((SpChain.minorAut GF4 (toS4 g hg) : S4) : GL (Fin 4) GF4) i j =
    SpChain.glMat ((toS4 (rho g) (symp_rho hg) : S4) : GL (Fin 4) GF4) i j
  rw [SpChain.glMat_minorAut]
  simp only [SpChain.glMat]
  rw [toS4_val, toS4_val, decodeM_rho]

private theorem w183finSp44_symp_invMat {g : Nat} (hg : symp g = true) :
    symp (mmul Jm (mmul (transp g) Jm)) = true := by
  apply w183finSp44_symp_mmul w183finSp44_symp_Jm
  exact w183finSp44_symp_mmul (w183finSp44_symp_transp hg) w183finSp44_symp_Jm

private theorem w183finSp44_toS4_inv {g : Nat} (hg : symp g = true) :
    toS4 (mmul Jm (mmul (transp g) Jm)) (w183finSp44_symp_invMat hg) = (toS4 g hg)⁻¹ := by
  apply Subtype.ext
  apply Units.ext
  apply Matrix.ext
  intro i j
  rw [toS4_val]
  simp only [decodeM_mmul, decodeM_Jm, decodeM_transp]
  change (SpChain.minorJ GF4 * ((decodeM g).transpose * SpChain.minorJ GF4)) i j =
    (SpChain.minorJ GF4 * (decodeM g).transpose * SpChain.minorJ GF4) i j
  rw [Matrix.mul_assoc]

private theorem w183finSp44_toS4_mmul {a b : Nat} (ha : symp a = true) (hb : symp b = true)
    {h : symp (mmul a b) = true} :
    toS4 (mmul a b) h = toS4 a ha * toS4 b hb := by
  apply Subtype.ext
  apply Units.ext
  apply Matrix.ext
  intro i j
  rw [toS4_val]
  rw [Subgroup.coe_mul]
  simp only [Units.val_mul, toS4_val, decodeM_mmul]

private theorem w183finSp44_toS4_rhoPow {g : Nat} (hg : symp g = true) (n : Nat)
    (h : symp (rhoPow n g) = true) :
    toS4 (rhoPow n g) h = (SpChain.minorAut GF4 ^ n) (toS4 g hg) := by
  induction n generalizing g with
  | zero =>
      simp only [rhoPow, pow_zero]
      rfl
  | succ n ih =>
      change toS4 (rhoPow n (rho g)) h = (SpChain.minorAut GF4 ^ (n + 1)) (toS4 g hg)
      rw [ih (g := rho g) (symp_rho hg) h]
      rw [pow_succ, MulAut.mul_apply, minorAut_toS4]

private theorem w183finSp44_orderOf_minorAut : orderOf (SpChain.minorAut GF4) = 4 := by
  have hcard : Nat.card GF4 = 2 ^ 2 := by
    rw [Nat.card_eq_fintype_card]
    rfl
  obtain ⟨Fr, hFr, hord, hzp⟩ :=
    CFSG.QuasithinUnique.Setup.X7b.exists_frobenius_data (K := GF4) (by norm_num) hcard
  have hγ : orderOf (CFSG.QuasithinUnique.Setup.X7b.autCongr GF4 (SpChain.minorAut GF4)) = 4 := by
    rw [CFSG.QuasithinUnique.Setup.X7b.autCongr_minorAut]
    simpa using (SpChain.exceptionalAut_structure (K := GF4) (f := 2) (by norm_num) hFr hord
      hzp).1
  have h := MulEquiv.orderOf_eq (CFSG.QuasithinUnique.Setup.X7b.autCongr GF4)
    (SpChain.minorAut GF4)
  rw [hγ] at h
  exact h.symm

private theorem w183finSp44_minorAut_pow_mod (n : Nat) :
    SpChain.minorAut GF4 ^ (n % 4) = SpChain.minorAut GF4 ^ n := by
  rw [pow_eq_pow_iff_modEq, w183finSp44_orderOf_minorAut]
  exact Nat.mod_modEq n 4

private theorem w183finSp44_pow_inv_mul_pow_mod (i j : Nat) :
    (SpChain.minorAut GF4 ^ i)⁻¹ * SpChain.minorAut GF4 ^ ((i + j) % 4) =
      SpChain.minorAut GF4 ^ j := by
  have h : SpChain.minorAut GF4 ^ ((i + j) % 4) = SpChain.minorAut GF4 ^ (i + j) :=
    w183finSp44_minorAut_pow_mod (i + j)
  rw [h, pow_add]
  group

private theorem w183finSp44_toS4_gmulE {x y : El} (hx : validB x = true) (hy : validB y = true)
    {h : symp (gmulE x y).1 = true} :
    toS4 (gmulE x y).1 h =
      toS4 x.1 (validB_symp hx) *
        (SpChain.minorAut GF4 ^ x.2) (toS4 y.1 (validB_symp hy)) := by
  revert h
  rw [show (gmulE x y).1 = mmul x.1 (rhoPow x.2 y.1) from rfl]
  intro h
  rw [w183finSp44_toS4_mmul (validB_symp hx) (w183finSp44_symp_rhoPow x.2 (validB_symp hy))]
  rw [w183finSp44_toS4_rhoPow (validB_symp hy) x.2
    (w183finSp44_symp_rhoPow x.2 (validB_symp hy))]

private theorem w183finSp44_toS4_invE {x : El} (hx : validB x = true)
    {h : symp (invE x).1 = true} :
    toS4 (invE x).1 h =
      (SpChain.minorAut GF4 ^ ((4 - x.2) % 4)) ((toS4 x.1 (validB_symp hx))⁻¹) := by
  revert h
  rw [show (invE x).1 = rhoPow ((4 - x.2) % 4) (mmul Jm (mmul (transp x.1) Jm)) from rfl]
  intro h
  rw [w183finSp44_toS4_rhoPow (w183finSp44_symp_invMat (validB_symp hx)) ((4 - x.2) % 4) h]
  rw [w183finSp44_toS4_inv (validB_symp hx)]

theorem validB_gmulE {x y : El} (hx : validB x = true) (hy : validB y = true) :
    validB (gmulE x y) = true := by
  have hx' := validB_symp hx
  have hy' := validB_symp hy
  rw [validB_iff] at hx hy ⊢
  refine ⟨?_, ?_, ?_⟩
  · exact w183finSp44_mmul_lt _ _
  · exact w183finSp44_symp_mmul hx' (w183finSp44_symp_rhoPow x.2 hy')
  · exact Nat.mod_lt _ (by norm_num)

theorem validB_invE {x : El} (hx : validB x = true) : validB (invE x) = true := by
  have hx' := validB_symp hx
  rw [validB_iff] at hx ⊢
  refine ⟨?_, ?_, ?_⟩
  · exact w183finSp44_rhoPow_lt _ (w183finSp44_mmul_lt _ _)
  · exact w183finSp44_symp_rhoPow _ (w183finSp44_symp_invMat hx')
  · exact Nat.mod_lt _ (by norm_num)

theorem autOf_gmulE {x y : El} (hx : validB x = true) (hy : validB y = true) :
    autOf (gmulE x y) = autOf x * autOf y := by
  rw [autOf, dif_pos (validB_gmulE hx hy), autOf, dif_pos hx, autOf, dif_pos hy]
  rw [w183finSp44_toS4_gmulE hx hy]
  simp only [gmulE]
  rw [map_mul]
  rw [CFSG.QuasithinUnique.Setup.X7b.conj_apply_eq']
  rw [← w183finSp44_pow_inv_mul_pow_mod x.2 y.2]
  group

theorem autOf_oneE : autOf oneE = 1 := by
  rw [autOf, dif_pos validB_oneE]
  simp only [oneE, pow_zero, mul_one]
  rw [w183finSp44_toS4_idM]
  exact map_one _

theorem autOf_invE {x : El} (hx : validB x = true) : autOf (invE x) = (autOf x)⁻¹ := by
  have hx' := validB_symp hx
  have hi : x.2 < 4 := (validB_iff.mp hx).2.2
  have hjin : (x.2 + (4 - x.2) % 4) % 4 = 0 := by
    interval_cases x.2 <;> norm_num
  have hpj : SpChain.minorAut GF4 ^ ((4 - x.2) % 4) =
      (SpChain.minorAut GF4 ^ x.2)⁻¹ := by
    have h1 : SpChain.minorAut GF4 ^ x.2 *
        SpChain.minorAut GF4 ^ ((4 - x.2) % 4) = 1 := by
      rw [← pow_add, ← w183finSp44_minorAut_pow_mod (x.2 + (4 - x.2) % 4), hjin, pow_zero]
    exact eq_inv_of_mul_eq_one_right h1
  rw [autOf, dif_pos (validB_invE hx), autOf, dif_pos hx]
  rw [w183finSp44_toS4_invE hx]
  simp only [invE]
  rw [CFSG.QuasithinUnique.Setup.X7b.conj_apply_eq']
  rw [hpj]
  simp only [inv_inv]
  rw [map_inv (MulAut.conj : S4 →* MulAut S4)]
  group

end CFSG.LocalAnalysis.WeakClosure81.Sp44

end
