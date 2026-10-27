module

public import Certificates.Kernel.Co2Census.S0K
public import Certificates.Kernel.Co2Census.TRK
public import Certificates.Kernel.Co2SmithS.Smith
public import CFSG.Certificates.Kernel.Co2Census.Conj
public import CFSG.Sporadic.Co2Smith.HPCount
public import CFSG.Sporadic.Co2Smith.HPRep

public section

namespace CertificateChecks.KernelCo2Census

open CFSG.Sporadic.Co2Smith CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
open CFSG.KC.Co2InvS CFSG.KC.Co2Census CFSG.KC.Co1F2
open CertificateChecks.KernelCo2SmithS (PT PI chain_ok chainRecOK chainStepK colAct_eq mRows_eq
  mRows_two mRows_three)
open CFSG.KC.Co2SmithS (validM_unpack)
open scoped Matrix

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

@[expose] def repK (x : K) (M : ℕ) : Prop := M < 2 ^ 484 ∧ x.val.val = rowsMatrix 22 (unpackR 22 M)

theorem repK_mul {x y : K} {M N : ℕ} (hx : repK x M) (hy : repK y N) : repK (x * y) (mulV M N) :=
  ⟨mulV_lt M N, by rw [val_val_mul, hx.2, hy.2, ← rowsMatrix_mulRows, mulRows_unpack]⟩

theorem repK_fun {x y : K} {M : ℕ} (hx : repK x M) (hy : repK y M) : x = y :=
  eq_of_val_eq (hx.2.trans hy.2.symm)

theorem repK_unique {x : K} {M M' : ℕ} (h : repK x M) (h' : repK x M') : M = M' :=
  unpack_inj h.1 h'.1
    (eq_of_rowsMatrix_eq (validM_unpack M) (validM_unpack M') (h.2.symm.trans h'.2))

theorem repK_one : repK 1 IDP := ⟨IDP_lt, by rw [val_val_one, ← idRows_eq, rowsMatrix_idRows]⟩

theorem repK_inv {x : K} {M M' : ℕ} (h : repK x M) (h' : M' < 2 ^ 484)
    (e : mulV M M' = IDP) : repK x⁻¹ M' := by
  refine ⟨h', ?_⟩
  have hr : x.val.val * rowsMatrix 22 (unpackR 22 M') = 1 := by
    rw [h.2, ← rowsMatrix_mulRows, mulRows_unpack, e, ← idRows_eq, rowsMatrix_idRows]
  calc (x⁻¹).val.val = (x⁻¹).val.val * (x.val.val * rowsMatrix 22 (unpackR 22 M')) := by
        rw [hr, mul_one]
    _ = rowsMatrix 22 (unpackR 22 M') := by
        rw [← mul_assoc, ← val_val_mul, inv_mul_cancel, val_val_one, one_mul]

theorem chainRec_rec {k : ℕ} (hk : k < 6) :
    CFSG.Sporadic.Co2Smith.chainRec k = (Array.ofFn (n := Native.chainOrb[k]!) fun i => PT (k + 1) i.val,
      Array.ofFn (n := Native.chainOrb[k]!) fun i => PI (k + 1) 0 i.val,
      Array.ofFn (n := Native.chainOrb[k]!) fun i => PI (k + 1) 1 i.val) := by
  have h := chain_ok
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨-, -⟩, -⟩, hk'⟩ := h
  rw [List.all_eq_true] at hk'
  obtain ⟨⟨hrec, hw⟩, -⟩ := Bool.and_eq_true _ _ ▸ Bool.and_eq_true _ _ ▸
    hk' k (List.mem_range.2 hk)
  have hw' : ∀ l < ((Native.chainGens ())[k]!).size, ∀ x ∈ ((Native.chainGens ())[k]!)[l]!,
      x < 4 := by
    intro l hl x hx
    rw [List.all_eq_true] at hw
    have hm : ((Native.chainGens ())[k]!)[l]! ∈ ((Native.chainGens ())[k]!).toList := by
      rw [getElem!_pos _ l hl]
      exact Array.getElem_mem_toList hl
    exact of_decide_eq_true (List.all_eq_true.1 (hw _ hm) x hx)
  have hG : ∀ l < ((Native.chainGens ())[k]!).size,
      (((Native.chainGens ())[k]!).map (Native.mRows seedRowsArr))[l]! =
        unpackR 22 (CFSG.KC.Co2SmithS.wK KernelCo2SmithS.LT (((Native.chainGens ())[k]!)[l]!)) := by
    intro l hl
    rw [getElem!_pos _ l (by simpa using hl), Array.getElem_map, ← getElem!_pos _ l hl,
      mRows_eq (hw' l hl)]
  have hstep : ∀ l < (((Native.chainGens ())[k]!).map (Native.mRows seedRowsArr)).size, ∀ x,
      Native.vecStep (((Native.chainGens ())[k]!).map (Native.mRows seedRowsArr)) l x =
        chainStepK k l x := by
    intro l hl x
    rw [Array.size_map] at hl
    unfold Native.vecStep
    rw [hG l hl, colAct_eq]
    rfl
  unfold chainRecOK at hrec
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at hrec
  obtain ⟨⟨⟨hr, hl⟩, hpos⟩, hle⟩ := hrec
  exact (CFSG.KC.Co2SmithS.orbRec_sound (cap := 100) hpos hle hstep (Nat.eq_of_beq_eq_true hl) (by
    intro i hi
    rw [Array.size_map]
    exact hr i hi)).1

theorem trOK_spec {k : ℕ} (hk : k < 6) :
    TRt (trOff k) = IDP ∧ ∀ i < Native.chainOrb[k]!, i ≠ 0 →
      PI (k + 1) 0 i < i ∧ PI (k + 1) 1 i < ((Native.chainGens ())[k]!).size ∧
      TRt (trOff k + i) = mulV (CFSG.KC.Co2SmithS.wK KernelCo2SmithS.LT (((Native.chainGens ())[k]!)[PI (k + 1) 1 i]!))
        (TRt (trOff k + PI (k + 1) 0 i)) := by
  have h := List.all_eq_true.1 tr_ok k (List.mem_range.2 hk)
  simp only [trOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    Nat.beq_eq, Nat.blt_eq] at h
  refine ⟨h.1, fun i hi hi0 => ?_⟩
  rcases h.2 i hi with h0 | h1
  · exact absurd h0 hi0
  · exact ⟨h1.1.1, h1.1.2, h1.2⟩

theorem tRows_eq {k : ℕ} (hk : k < 6) : ∀ i < Native.chainOrb[k]!,
    Native.tRowsN (CFSG.Sporadic.Co2Smith.chainRec k) (chainRows k) i = unpackR 22 (TRt (trOff k + i)) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    obtain ⟨h0, hs⟩ := trOK_spec hk
    by_cases hi0 : i = 0
    · subst hi0
      rw [tRowsN_zero, Nat.add_zero, h0, idRows_eq]
    · obtain ⟨hp, hl, he⟩ := hs i hi hi0
      have hpar : (CFSG.Sporadic.Co2Smith.chainRec k).2.1[i]! = PI (k + 1) 0 i := by
        rw [chainRec_rec hk, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]
      have hlet : (CFSG.Sporadic.Co2Smith.chainRec k).2.2[i]! = PI (k + 1) 1 i := by
        rw [chainRec_rec hk, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]
      rw [tRowsN_of_lt hi0 (by rw [hpar]; exact hp), hpar, hlet,
        ih _ hp (hp.trans hi), he]
      have hw : ∀ x ∈ ((Native.chainGens ())[k]!)[PI (k + 1) 1 i]!, x < 4 := by
        have h := chain_ok
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨⟨⟨-, -⟩, -⟩, hk'⟩ := h
        rw [List.all_eq_true] at hk'
        obtain ⟨⟨-, hw⟩, -⟩ := Bool.and_eq_true _ _ ▸ Bool.and_eq_true _ _ ▸
          hk' k (List.mem_range.2 hk)
        intro x hx
        rw [List.all_eq_true] at hw
        have hm : ((Native.chainGens ())[k]!)[PI (k + 1) 1 i]! ∈
            ((Native.chainGens ())[k]!).toList := by
          rw [getElem!_pos ((Native.chainGens ())[k]!) (PI (k + 1) 1 i) hl]
          exact Array.getElem_mem_toList hl
        exact of_decide_eq_true (List.all_eq_true.1 (hw _ hm) x hx)
      have hG : (chainRows k)[PI (k + 1) 1 i]! = unpackR 22 (CFSG.KC.Co2SmithS.wK
          KernelCo2SmithS.LT (((Native.chainGens ())[k]!)[PI (k + 1) 1 i]!)) := by
        rw [chainRows, getElem!_pos _ (PI (k + 1) 1 i) (by simpa using hl), Array.getElem_map,
          ← getElem!_pos ((Native.chainGens ())[k]!) (PI (k + 1) 1 i) hl, mRows_eq hw]
      rw [hG, mulRows_unpack]

theorem cT_get {k i : ℕ} (hk : k < 6) (hi : i < Native.chainOrb[k]!) :
    (cT[k]!)[i]! = unpackR 22 (TRt (trOff k + i)) := by
  rw [cT_eq, tArrN_get hk hi]
  exact tRows_eq hk i hi

theorem sRowsF_SK (n : ℕ) : Native.sRowsF cT n = unpackR 22 (SK n) := by
  have h0 : (cT[0]!)[n % 63]! = unpackR 22 (TRt (n % 63)) :=
    (cT_get (k := 0) (by norm_num) (by rw [show Native.chainOrb[0]! = 63 from rfl]; omega)).trans
      (by rw [show trOff 0 = 0 from rfl, Nat.zero_add])
  have h1 : (cT[1]!)[n / 63 % 32]! = unpackR 22 (TRt (63 + n / 63 % 32)) :=
    cT_get (k := 1) (by norm_num) (by rw [show Native.chainOrb[1]! = 32 from rfl]; omega)
  have h2 : (cT[2]!)[n / 2016 % 15]! = unpackR 22 (TRt (95 + n / 2016 % 15)) :=
    cT_get (k := 2) (by norm_num) (by rw [show Native.chainOrb[2]! = 15 from rfl]; omega)
  have h3 : (cT[3]!)[n / 30240 % 8]! = unpackR 22 (TRt (110 + n / 30240 % 8)) :=
    cT_get (k := 3) (by norm_num) (by rw [show Native.chainOrb[3]! = 8 from rfl]; omega)
  have h4 : (cT[4]!)[n / 241920 % 3]! = unpackR 22 (TRt (118 + n / 241920 % 3)) :=
    cT_get (k := 4) (by norm_num) (by rw [show Native.chainOrb[4]! = 3 from rfl]; omega)
  have h5 : (cT[5]!)[n / 725760 % 2]! = unpackR 22 (TRt (121 + n / 725760 % 2)) :=
    cT_get (k := 5) (by norm_num) (by rw [show Native.chainOrb[5]! = 2 from rfl]; omega)
  rw [Native.sRowsF, h0, h1, h2, h3, h4, h5]
  simp only [mulRowsF_eq, mulRows_unpack]
  rfl

theorem repK_sElt
    (n : ℕ) : repK (sElt n) (SK n) := by
  refine ⟨mulV_lt _ _, ?_⟩
  rw [sElt_val', ← sRowsF_eq, sRowsF_SK]

@[expose] noncomputable def gAB (l : ℕ) : K :=
  if l = 0 then aE else bE

theorem gensSub_gAB : gensSub gAB 2 = S0 := by
  have e : gAB '' {l | l < 2} = {aE, bE} := by
    ext x
    simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, gAB]
    constructor
    · rintro ⟨l, hl, rfl⟩
      rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact ⟨0, by norm_num, rfl⟩
      · exact ⟨1, by norm_num, rfl⟩
  rw [gensSub, e]

theorem L_misc_spec : ABt 0 = mulV (KernelCo2SmithS.LT 2) IDP ∧
    ABt 1 = mulV (KernelCo2SmithS.LT 3) IDP ∧ mulV (ABt 0) (ABIt 0) = IDP ∧
    mulV (ABt 1) (ABIt 1) = IDP ∧ Lrt 0 = 0 ∧ LPt 0 = IDP ∧
    (∀ j < 5, Lrt j < 5104 ∧ rtOf LXt (Lrt j) = Lrt j ∧
      rootCount LXt 5104 80 (Lrt j) = s0Sizes.getD j 0) ∧
    ∀ j < 4, LPt (Lrt (j + 1)) = SK (s0Reps.getD j 0) ∧
      mulV (LPt (Lrt (j + 1))) (LPt (Lrt (j + 1))) = IDP := by
  have h := L_misc
  simp only [Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq, List.all_eq_true, List.mem_range] at h
  exact ⟨h.1.1.1.1.1.1.1, h.1.1.1.1.1.1.2, h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2,
    fun j hj => ⟨(h.1.2 j hj).1.1, (h.1.2 j hj).1.2, (h.1.2 j hj).2⟩, h.2⟩

theorem ABIt_lt {l : ℕ} (hl : l < 2) : ABIt l < 2 ^ 484 := by
  have h := ABI_lt
  simp only [Bool.and_eq_true, Nat.blt_eq] at h
  rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
  · exact h.1
  · exact h.2

theorem repK_gAB {l : ℕ} (hl : l < 2) :
    repK (gAB l) (ABt l) ∧ repK (gAB l)⁻¹ (ABIt l) := by
  obtain ⟨h0, h1, h2, h3, -⟩ := L_misc_spec
  have ha : repK aE (ABt 0) := ⟨by rw [h0]; exact mulV_lt _ _, by
    rw [← mWord_two, mWord_val _ (by decide), mRows_two, h0]⟩
  have hb : repK bE (ABt 1) := ⟨by rw [h1]; exact mulV_lt _ _, by
    rw [← mWord_three, mWord_val _ (by decide), mRows_three, h1]⟩
  rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
  · exact ⟨ha, repK_inv ha (ABIt_lt (by norm_num)) h2⟩
  · exact ⟨hb, repK_inv hb (ABIt_lt (by norm_num)) h3⟩

theorem conjSteps_L : ConjSteps repK stL 2 gAB := by
  intro l hl x M hx
  obtain ⟨h1, h2⟩ := repK_gAB hl
  exact repK_mul (repK_mul h1 hx) h2

@[expose] noncomputable def s0Rep (j : ℕ) : K :=
  if j = 0 then 1 else sElt (s0Reps.getD (j - 1) 0)

theorem repK_s0Rep
    {j : ℕ} (hj : j < 5) : repK (s0Rep j) (LPt (Lrt j)) := by
  obtain ⟨-, -, -, -, h4, h5, -, h7⟩ := L_misc_spec
  by_cases h0 : j = 0
  · subst h0
    rw [s0Rep, if_pos rfl, h4, h5]
    exact repK_one
  · obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero h0
    rw [s0Rep, if_neg h0, Nat.succ_sub_one, (h7 j' (by omega)).1]
    exact repK_sElt _

theorem s0_class
    {j : ℕ} (hj : j < 5) :
    segSet repK 5104 LPt LXt (Lrt j) = {y | ∃ w ∈ S0, y = w * s0Rep j * w⁻¹} ∧
      (segSet repK 5104 LPt LXt (Lrt j)).ncard = s0Sizes.getD j 0 := by
  obtain ⟨-, -, -, -, -, -, h6, -⟩ := L_misc_spec
  obtain ⟨hlt, hroot, hcnt⟩ := h6 j hj
  have hfun : ∀ x y M, repK x M → repK y M → x = y := fun _ _ _ h h' => repK_fun h h'
  refine ⟨?_, ?_⟩
  · rw [seg_class hfun conjSteps_L L_tree L_clos hlt hroot (repK_s0Rep hj), gensSub_gAB]
  · rw [seg_ncard hfun (fun _ _ _ h h' => repK_unique h h') conjSteps_L L_tree hlt hroot
      (repK_s0Rep hj), ← rootCount_eq (hi := 80) (by norm_num), hcnt]

end CertificateChecks.KernelCo2Census

end
