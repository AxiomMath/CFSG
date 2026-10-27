module

public import CFSG.Quasithin.Background.ShultG53TotPack
public import CFSG.Quasithin.Background.ShultG53IdentPack
public import CFSG.Quasithin.Background.ShultG53Layers

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.ShultG53.Part5Pack

open CFSG.Permutation.FinPack CFSG.Quasithin.ShultG53.Pack CFSG.Quasithin.ShultG53.IdentPack
  CFSG.Quasithin.ShultG53.TotPack CFSG.Quasithin.H13.A6 CFSG.Quasithin.RonanG51 Equiv Matrix

@[expose] def u2a : ℕ := 65484

@[expose] def u2b : ℕ := 53244

@[expose] def cfT : ℕ :=
  38748014849374315733909681789393899517216024112956231614585888741788599713792

@[expose] def cfK (x w : ℕ) : ℕ := bitK cfT (Nat.add (Nat.mul 16 x) w)

theorem u2a_val : ∀ w : V4, (U2gen 0 w).val = bitK u2a (vc w) := by decide +kernel

theorem u2b_val : ∀ w : V4, (U2gen 1 w).val = bitK u2b (vc w) := by decide +kernel

theorem cf_val : ∀ x w : V4, (Cf x w).val = cfK (vc x) (vc w) := by decide +kernel

theorem val_add2 : ∀ a b : ZMod 2, (a + b).val = Nat.xor a.val b.val := by decide

theorem vc_x00 : vc (x0 0) = 5 := by decide

theorem vc_x01 : vc (x0 1) = 1 := by decide

@[expose] noncomputable def eqK (f g : ℕ → ℕ) : Bool :=
  allK (fun v => Nat.beq (f v) (g v)) codes16

@[expose] noncomputable def notinK (f : ℕ → ℕ) : Bool :=
  allK (fun x => anyK (fun w => !Nat.beq (f w) (cfK x w)) codes16) codes16

theorem eqK_sound {F G : V4 → ZMod 2} {f g : ℕ → ℕ} (hF : ∀ w, (F w).val = f (vc w))
    (hG : ∀ w, (G w).val = g (vc w)) (h : eqK f g = true) : ∀ w, F w = G w := by
  intro w
  have h1 := allK_iff.1 h _ (vc_mem w)
  rw [Nat.beq_eq, ← hF, ← hG] at h1
  exact ZMod.val_injective _ h1

theorem notinK_sound {F : V4 → ZMod 2} {f : ℕ → ℕ} (hF : ∀ w, (F w).val = f (vc w))
    (h : notinK f = true) : ∀ x : V4, ∃ w : V4, F w ≠ Cf x w := by
  intro x
  obtain ⟨c, hc, hw⟩ := anyK_iff.1 (allK_iff.1 h _ (vc_mem x))
  obtain ⟨w, rfl⟩ := vc_surj c hc
  refine ⟨w, fun e => ?_⟩
  rw [Bool.not_eq_true', ← hF w, ← cf_val x w, e] at hw
  exact Nat.ne_of_beq_eq_false hw rfl

theorem pair_sound {F G : V4 → ZMod 2} {f g : ℕ → ℕ} (hF : ∀ w, (F w).val = f (vc w))
    (hG : ∀ w, (G w).val = g (vc w)) (h : notinK (fun v => Nat.xor (f v) (g v)) = true) :
    (∀ x : V4, ∃ w : V4, F w + G w ≠ Cf x w) ∧ (∀ x : V4, ∃ w : V4, G w + F w ≠ Cf x w) := by
  have hFG : ∀ w, (F w + G w).val = Nat.xor (f (vc w)) (g (vc w)) := fun w => by
    rw [val_add2, hF, hG]
  have h1 : ∀ x : V4, ∃ w : V4, F w + G w ≠ Cf x w :=
    notinK_sound (F := fun w => F w + G w) (f := fun v => Nat.xor (f v) (g v)) hFG h
  refine ⟨h1, fun x => ?_⟩
  obtain ⟨w, hw⟩ := h1 x
  exact ⟨w, by rwa [add_comm]⟩

@[expose] def uA : Fin 3 → Fn :=
  ![U2gen 0, fun w => U2gen 0 (Matrix.mulVec (Rm 0 (T5_0 0)⁻¹) w),
    fun w => U2gen 0 (Matrix.mulVec (Rm 0 (T5_0 1)⁻¹) w)]

@[expose] def uB : Fin 3 → Fn :=
  ![U2gen 1, fun w => U2gen 1 (Matrix.mulVec (Rm 1 (T5_1 0)⁻¹) w),
    fun w => U2gen 1 (Matrix.mulVec (Rm 1 (T5_1 1)⁻¹) w)]

theorem enc_T50_inv : enc (T5_0 0)⁻¹ = 4534560 ∧ enc (T5_0 1)⁻¹ = 5509920 := by decide +kernel

theorem totK_T51_inv : totK (enc (T5_1 0)⁻¹) = 4534785 ∧ totK (enc (T5_1 1)⁻¹) = 3490320 := by
  decide +kernel

@[expose] def fA0 (v : ℕ) : ℕ := bitK u2a v

@[expose] def fA1 (v : ℕ) : ℕ := bitK u2a (hK 4534560 v)

@[expose] def fA2 (v : ℕ) : ℕ := bitK u2a (hK 5509920 v)

@[expose] def fB0 (v : ℕ) : ℕ := bitK u2b v

@[expose] def fB1 (v : ℕ) : ℕ := bitK u2b (hK 4534785 v)

@[expose] def fB2 (v : ℕ) : ℕ := bitK u2b (hK 3490320 v)

theorem uA_zero : uA 0 = U2gen 0 := rfl

theorem uB_zero : uB 0 = U2gen 1 := rfl

theorem uA_v0 (w : V4) : (uA 0 w).val = fA0 (vc w) := u2a_val w

theorem uA_v1 (w : V4) : (uA 1 w).val = fA1 (vc w) := by
  change (U2gen 0 (Rm 0 (T5_0 0)⁻¹ *ᵥ w)).val = bitK u2a (hK 4534560 (vc w))
  rw [u2a_val, vc_Rm0, enc_T50_inv.1]

theorem uA_v2 (w : V4) : (uA 2 w).val = fA2 (vc w) := by
  change (U2gen 0 (Rm 0 (T5_0 1)⁻¹ *ᵥ w)).val = bitK u2a (hK 5509920 (vc w))
  rw [u2a_val, vc_Rm0, enc_T50_inv.2]

theorem uB_v0 (w : V4) : (uB 0 w).val = fB0 (vc w) := u2b_val w

theorem uB_v1 (w : V4) : (uB 1 w).val = fB1 (vc w) := by
  change (U2gen 1 (Rm 1 (T5_1 0)⁻¹ *ᵥ w)).val = bitK u2b (hK 4534785 (vc w))
  rw [u2b_val, vc_Rm1, totK_T51_inv.1]

theorem uB_v2 (w : V4) : (uB 2 w).val = fB2 (vc w) := by
  change (U2gen 1 (Rm 1 (T5_1 1)⁻¹ *ᵥ w)).val = bitK u2b (hK 3490320 (vc w))
  rw [u2b_val, vc_Rm1, totK_T51_inv.2]

theorem check_nA0 : notinK fA0 = true := by decide +kernel

theorem check_nA1 : notinK fA1 = true := by decide +kernel

theorem check_nA2 : notinK fA2 = true := by decide +kernel

theorem check_nB0 : notinK fB0 = true := by decide +kernel

theorem check_nB1 : notinK fB1 = true := by decide +kernel

theorem check_nB2 : notinK fB2 = true := by decide +kernel

theorem check_pA01 : notinK (fun v => Nat.xor (fA0 v) (fA1 v)) = true := by decide +kernel

theorem check_pA02 : notinK (fun v => Nat.xor (fA0 v) (fA2 v)) = true := by decide +kernel

theorem check_pA12 : notinK (fun v => Nat.xor (fA1 v) (fA2 v)) = true := by decide +kernel

theorem check_pB01 : notinK (fun v => Nat.xor (fB0 v) (fB1 v)) = true := by decide +kernel

theorem check_pB02 : notinK (fun v => Nat.xor (fB0 v) (fB2 v)) = true := by decide +kernel

theorem check_pB12 : notinK (fun v => Nat.xor (fB1 v) (fB2 v)) = true := by decide +kernel

theorem check_sA : eqK (fun v => Nat.xor (Nat.xor (fA0 v) (fA1 v)) (fA2 v)) (cfK 5) = true := by
  decide +kernel

theorem check_sB : eqK (fun v => Nat.xor (Nat.xor (fB0 v) (fB1 v)) (fB2 v)) (cfK 1) = true := by
  decide +kernel

theorem U2gen_notin_code : ∀ k : Fin 2, ∀ x : V4, ∃ w : V4, U2gen k w ≠ Cf x w := by
  rw [Fin.forall_fin_two]
  exact ⟨notinK_sound u2a_val check_nA0, notinK_sound u2b_val check_nB0⟩

theorem uA_notin : ∀ i : Fin 3, ∀ x : V4, ∃ w : V4, uA i w ≠ Cf x w := by
  intro i
  fin_cases i
  exacts [notinK_sound uA_v0 check_nA0, notinK_sound uA_v1 check_nA1,
    notinK_sound uA_v2 check_nA2]

theorem uB_notin : ∀ i : Fin 3, ∀ x : V4, ∃ w : V4, uB i w ≠ Cf x w := by
  intro i
  fin_cases i
  exacts [notinK_sound uB_v0 check_nB0, notinK_sound uB_v1 check_nB1,
    notinK_sound uB_v2 check_nB2]

theorem uA_pair : ∀ i j : Fin 3, i ≠ j → ∀ x : V4, ∃ w : V4, uA i w + uA j w ≠ Cf x w := by
  have p01 := pair_sound uA_v0 uA_v1 check_pA01
  have p02 := pair_sound uA_v0 uA_v2 check_pA02
  have p12 := pair_sound uA_v1 uA_v2 check_pA12
  intro i j hij
  fin_cases i <;> fin_cases j
  exacts [(hij rfl).elim, p01.1, p02.1, p01.2, (hij rfl).elim, p12.1, p02.2, p12.2,
    (hij rfl).elim]

theorem uB_pair : ∀ i j : Fin 3, i ≠ j → ∀ x : V4, ∃ w : V4, uB i w + uB j w ≠ Cf x w := by
  have p01 := pair_sound uB_v0 uB_v1 check_pB01
  have p02 := pair_sound uB_v0 uB_v2 check_pB02
  have p12 := pair_sound uB_v1 uB_v2 check_pB12
  intro i j hij
  fin_cases i <;> fin_cases j
  exacts [(hij rfl).elim, p01.1, p02.1, p01.2, (hij rfl).elim, p12.1, p02.2, p12.2,
    (hij rfl).elim]

theorem uA_sum : ∀ w : V4, uA 0 w + uA 1 w + uA 2 w = Cf (x0 0) w :=
  eqK_sound (F := fun w => uA 0 w + uA 1 w + uA 2 w) (G := Cf (x0 0))
    (fun w => by beta_reduce; rw [val_add2, val_add2, uA_v0, uA_v1, uA_v2])
    (fun w => by rw [cf_val, vc_x00]) check_sA

theorem uB_sum : ∀ w : V4, uB 0 w + uB 1 w + uB 2 w = Cf (x0 1) w :=
  eqK_sound (F := fun w => uB 0 w + uB 1 w + uB 2 w) (G := Cf (x0 1))
    (fun w => by beta_reduce; rw [val_add2, val_add2, uB_v0, uB_v1, uB_v2])
    (fun w => by rw [cf_val, vc_x01]) check_sB

theorem T5_0_eq : T5_0 0 = swap 1 2 * swap 4 5 ∧ T5_0 1 = swap 1 3 * swap 2 3 := by decide +kernel

theorem T5_1_eq : T5_1 0 = swap 2 4 * swap 3 5 ∧
    T5_1 1 = swap 0 2 * swap 2 4 * swap 1 3 * swap 3 5 := by decide +kernel

theorem check_t50 : lineK lineB (totK (enc (T5_0 0))) = true ∧
    lineK lineB (totK (enc (T5_0 1))) = true := by decide +kernel

theorem check_t51 : lineK lineA (enc (T5_1 0)) = true ∧ lineK lineA (enc (T5_1 1)) = true := by
  decide +kernel

theorem T5_0_prop : ∀ i : Fin 2, Perm.sign (T5_0 i) = 1 ∧
    ∀ y : V4, predLine4b y → predLine4b (Matrix.mulVec (Rm 1 (T5_0 i)) y) := by
  rw [Fin.forall_fin_two]
  refine ⟨⟨?_, (line_iff lineB_iff (vc_Rm1 _)).2 check_t50.1⟩,
    ⟨?_, (line_iff lineB_iff (vc_Rm1 _)).2 check_t50.2⟩⟩
  · rw [T5_0_eq.1]
    exact sign_swap2 _ _ _ _ (by decide) (by decide)
  · rw [T5_0_eq.2]
    exact sign_swap2 _ _ _ _ (by decide) (by decide)

theorem T5_1_prop : ∀ i : Fin 2, Perm.sign (T5_1 i) = 1 ∧
    ∀ y : V4, predLine4a y → predLine4a (Matrix.mulVec (Rm 0 (T5_1 i)) y) := by
  rw [Fin.forall_fin_two]
  refine ⟨⟨?_, (line_iff lineA_iff (vc_Rm0 _)).2 check_t51.1⟩,
    ⟨?_, (line_iff lineA_iff (vc_Rm0 _)).2 check_t51.2⟩⟩
  · rw [T5_1_eq.1]
    exact sign_swap2 _ _ _ _ (by decide) (by decide)
  · rw [T5_1_eq.2]
    exact sign_swap4 _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (by decide)

@[expose] noncomputable def fixK (f : ℕ → ℕ) (m : ℕ) : Bool := eqK f (fun v => f (hK m v))

@[expose] noncomputable def orbK (f0 f1 f2 : ℕ → ℕ) (m : ℕ) : Bool :=
  eqK f0 (fun v => f0 (hK m v)) || eqK f0 (fun v => f1 (hK m v)) || eqK f0 (fun v => f2 (hK m v))

@[expose] noncomputable def p5K (c t : ℕ) : Bool :=
  (!lineK lineB t || orbK fA0 fA1 fA2 c) && (!Nat.beq (hK t 1) 1 || fixK fA0 c) &&
    (!lineK lineA c || orbK fB0 fB1 fB2 t) && (!Nat.beq (hK c 5) 5 || fixK fB0 t)

theorem check_p5 : allK (fun q => p5K (lo6 (pR q)) (tR q)) evenTot = true := by decide +kernel

theorem imp_of_or {a b : Bool} (h : (!a || b) = true) (ha : a = true) : b = true := by
  rw [ha] at h
  exact h

theorem p5K_parts {c t : ℕ} (h : p5K c t = true) :
    (lineK lineB t = true → orbK fA0 fA1 fA2 c = true) ∧
    (Nat.beq (hK t 1) 1 = true → fixK fA0 c = true) ∧
    (lineK lineA c = true → orbK fB0 fB1 fB2 t = true) ∧
    (Nat.beq (hK c 5) 5 = true → fixK fB0 t = true) := by
  rw [p5K, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨imp_of_or h1, imp_of_or h2, imp_of_or h3, imp_of_or h4⟩

theorem p5_of (σ : Perm (Fin 6)) (hs : Perm.sign σ = 1) : p5K (enc σ) (totK (enc σ)) = true := by
  obtain ⟨q, hq, hp, ht⟩ := exists_tot σ hs
  have h := allK_iff.1 check_p5 q hq
  rw [hp, ht, lo6_pc6] at h
  exact h

theorem Rm_mul_inv (k : Fin 2) (σ : Perm (Fin 6)) : Rm k σ * Rm k σ⁻¹ = 1 := by
  rw [← Rm_mul, mul_inv_cancel, Rm_one]

theorem orb_sound {U : Fin 3 → V4 → ZMod 2} {f0 f1 f2 : ℕ → ℕ}
    (h0 : ∀ w, (U 0 w).val = f0 (vc w)) (h1 : ∀ w, (U 1 w).val = f1 (vc w))
    (h2 : ∀ w, (U 2 w).val = f2 (vc w)) {M M' : Matrix (Fin 4) (Fin 4) (ZMod 2)} {m : ℕ}
    (hM : ∀ v, vc (M *ᵥ v) = hK m (vc v)) (hMM : M * M' = 1) (h : orbK f0 f1 f2 m = true) :
    ∃ i : Fin 3, ∀ w, U 0 (M' *ᵥ w) = U i w := by
  have key : ∀ (i : Fin 3) {fi : ℕ → ℕ}, (∀ w, (U i w).val = fi (vc w)) →
      eqK f0 (fun v => fi (hK m v)) = true → ∀ w, U 0 (M' *ᵥ w) = U i w := by
    intro i fi hi he w
    have e : ∀ v, U 0 v = U i (M *ᵥ v) :=
      eqK_sound (G := fun v => U i (M *ᵥ v)) h0 (fun v => by beta_reduce; rw [hi, hM]) he
    rw [e (M' *ᵥ w), mulVec_mulVec, hMM, one_mulVec]
  rw [orbK, Bool.or_eq_true, Bool.or_eq_true] at h
  rcases h with (h | h) | h
  exacts [⟨0, key 0 h0 h⟩, ⟨1, key 1 h1 h⟩, ⟨2, key 2 h2 h⟩]

theorem fix_sound {U : V4 → ZMod 2} {f : ℕ → ℕ} (h0 : ∀ w, (U w).val = f (vc w))
    {M M' : Matrix (Fin 4) (Fin 4) (ZMod 2)} {m : ℕ} (hM : ∀ v, vc (M *ᵥ v) = hK m (vc v))
    (hMM : M * M' = 1) (h : fixK f m = true) : ∀ w, U (M' *ᵥ w) = U w := by
  have e : ∀ v, U v = U (M *ᵥ v) :=
    eqK_sound (G := fun v => U (M *ᵥ v)) h0 (fun v => by beta_reduce; rw [h0, hM]) h
  intro w
  rw [e (M' *ᵥ w), mulVec_mulVec, hMM, one_mulVec]

theorem orbit0 : ∀ σ : Perm (Fin 6), Perm.sign σ = 1 →
    (∀ y : V4, predLine4b y → predLine4b (Matrix.mulVec (Rm 1 σ) y)) →
    ∃ i : Fin 3, ∀ w : V4, U2gen 0 (Matrix.mulVec (Rm 0 σ⁻¹) w) = uA i w := by
  intro σ hs hl
  have h := orb_sound (U := uA) uA_v0 uA_v1 uA_v2 (vc_Rm0 σ) (Rm_mul_inv 0 σ)
    ((p5K_parts (p5_of σ hs)).1 ((line_iff lineB_iff (vc_Rm1 σ)).1 hl))
  rw [uA_zero] at h
  exact h

theorem orbit1 : ∀ σ : Perm (Fin 6), Perm.sign σ = 1 →
    (∀ y : V4, predLine4a y → predLine4a (Matrix.mulVec (Rm 0 σ) y)) →
    ∃ i : Fin 3, ∀ w : V4, U2gen 1 (Matrix.mulVec (Rm 1 σ⁻¹) w) = uB i w := by
  intro σ hs hl
  have h := orb_sound (U := uB) uB_v0 uB_v1 uB_v2 (vc_Rm1 σ) (Rm_mul_inv 1 σ)
    ((p5K_parts (p5_of σ hs)).2.2.1 ((line_iff lineA_iff (vc_Rm0 σ)).1 hl))
  rw [uB_zero] at h
  exact h

theorem fix0 : ∀ σ : Perm (Fin 6), Perm.sign σ = 1 →
    Matrix.mulVec (Rm 1 σ) (x0 1) = x0 1 →
    ∀ w : V4, U2gen 0 (Matrix.mulVec (Rm 0 σ⁻¹) w) = U2gen 0 w := by
  intro σ hs hx
  have e := congrArg vc hx
  rw [vc_Rm1, vc_x01] at e
  have hb : Nat.beq (hK (totK (enc σ)) 1) 1 = true := by rw [Nat.beq_eq]; exact e
  have h := fix_sound (U := uA 0) uA_v0 (vc_Rm0 σ) (Rm_mul_inv 0 σ)
    ((p5K_parts (p5_of σ hs)).2.1 hb)
  rw [uA_zero] at h
  exact h

theorem fix1 : ∀ σ : Perm (Fin 6), Perm.sign σ = 1 →
    Matrix.mulVec (Rm 0 σ) (x0 0) = x0 0 →
    ∀ w : V4, U2gen 1 (Matrix.mulVec (Rm 1 σ⁻¹) w) = U2gen 1 w := by
  intro σ hs hx
  have e := congrArg vc hx
  rw [vc_Rm0, vc_x00] at e
  have hb : Nat.beq (hK (enc σ) 5) 5 = true := by rw [Nat.beq_eq]; exact e
  have h := fix_sound (U := uB 0) uB_v0 (vc_Rm1 σ) (Rm_mul_inv 1 σ)
    ((p5K_parts (p5_of σ hs)).2.2.2 hb)
  rw [uB_zero] at h
  exact h

end CFSG.Quasithin.ShultG53.Part5Pack
