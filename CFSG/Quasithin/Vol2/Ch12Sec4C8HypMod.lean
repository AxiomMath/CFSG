module

public import CFSG.Quasithin.Background.StabTransport
public import CFSG.Quasithin.Background.StabSubBasics
public import CFSG.Quasithin.Vol2.Ch12Sec4C8HypData
public import CFSG.Quasithin.Vol2.Ch12Sec4G2NormZorn

public section

namespace CFSG.Quasithin.H13

open CFSG.Open Orbit

namespace G2Hyp

@[expose] noncomputable def cO (c : ℕ) : ModO := if h : c ∈ o0Codes then codeO ⟨c, h⟩ else 1

theorem cO_of_mem {c : ℕ} (h : c ∈ o0Codes) : cO c = codeO ⟨c, h⟩ := by
  simp [cO, h]

theorem cO_zero : cO 0 = 1 := by
  rw [cO_of_mem zero_mem_o0Codes]
  exact codeO_zero

theorem cO_xor {c d : ℕ} (hc : c ∈ o0Codes) (hd : d ∈ o0Codes) : cO (c ^^^ d) = cO c * cO d := by
  rw [cO_of_mem (xor_mem_o0Codes hc hd), cO_of_mem hc, cO_of_mem hd, ← codeO_xor]
  rfl

theorem cO_inj {c d : ℕ} (hc : c ∈ o0Codes) (hd : d ∈ o0Codes) (h : cO c = cO d) : c = d := by
  rw [cO_of_mem hc, cO_of_mem hd] at h
  exact congrArg Subtype.val (codeO_injective h)

theorem exists_cO (v : ModO) : ∃ c ∈ o0Codes, cO c = v := by
  obtain ⟨c, rfl⟩ := codeO_surjective v
  exact ⟨c.1, c.2, cO_of_mem c.2⟩

theorem mact_mem {g : ↥(quasithinG2 (ZMod 2))} {c : ℕ} (hc : c ∈ o0Codes) :
    mact (matCode g.1) c ∈ o0Codes :=
  mact_mem_o0Codes g.2 hc

theorem act_cO (g : ↥(quasithinG2 (ZMod 2))) {c : ℕ} (hc : c ∈ o0Codes) :
    g2OAct (ZMod 2) g (cO c) = cO (mact (matCode g.1) c) := by
  rw [cO_of_mem hc, cO_of_mem (mact_mem hc), g2OAct_codeO]
  rfl

theorem mact_mul (g h : ↥(quasithinG2 (ZMod 2))) {c : ℕ} (hc : c < 256) :
    mact (matCode (g * h).1) c = mact (matCode g.1) (mact (matCode h.1) c) := by
  apply decodeZ_injective (mact_lt' _ _) (mact_lt' _ _)
  rw [decodeZ_mact' (g * h).1 hc, decodeZ_mact' g.1 (mact_lt' _ _), decodeZ_mact' h.1 hc]
  rfl

theorem mact_one {c : ℕ} (hc : c < 256) :
    mact (matCode (1 : ↥(quasithinG2 (ZMod 2))).1) c = c := by
  apply decodeZ_injective (mact_lt' _ _) hc
  rw [decodeZ_mact' _ hc]
  rfl

@[expose] def HasCode (U : Subgroup ModO) (b : ℕ) : Prop :=
  ∀ c ∈ o0Codes, cO c ∈ U ↔ parB b c = true

theorem eq_of_hasCode {U U' : Subgroup ModO} {b : ℕ} (h : HasCode U b) (h' : HasCode U' b) :
    U = U' := by
  ext v
  obtain ⟨c, hc, rfl⟩ := exists_cO v
  rw [h c hc, h' c hc]

theorem parB_129 (b : ℕ) : parB b 129 = false := by
  have h0 : Nat.testBit 129 0 = true := by decide
  have h1 : Nat.testBit 129 1 = false := by decide
  have h2 : Nat.testBit 129 2 = false := by decide
  have h3 : Nat.testBit 129 3 = false := by decide
  have h4 : Nat.testBit 129 4 = false := by decide
  have h5 : Nat.testBit 129 5 = false := by decide
  have h6 : Nat.testBit 129 6 = false := by decide
  simp [parB, h0, h1, h2, h3, h4, h5, h6]

theorem mem129 : (129 : ℕ) ∈ o0Codes := by decide

theorem cO_129_not_mem {U : Subgroup ModO} {b : ℕ} (h : HasCode U b) : cO 129 ∉ U := by
  rw [h 129 mem129, parB_129]
  exact Bool.false_ne_true

theorem act_cO_129 (g : ↥(quasithinG2 (ZMod 2))) : g2OAct (ZMod 2) g (cO 129) = cO 129 := by
  rw [cO_of_mem mem129, g2OAct_codeO, o0Act_one g mem129]

theorem foldr_mem (L : List ℕ) (hL : ∀ d ∈ L, d ∈ o0Codes) : L.foldr (· ^^^ ·) 0 ∈ o0Codes := by
  induction L with
  | nil => exact zero_mem_o0Codes
  | cons d L ih =>
    exact xor_mem_o0Codes (hL d List.mem_cons_self)
      (ih fun e he => hL e (List.mem_cons_of_mem _ he))

theorem cO_foldr (L : List ℕ) (hL : ∀ d ∈ L, d ∈ o0Codes) :
    cO (L.foldr (· ^^^ ·) 0) = (L.map cO).prod := by
  induction L with
  | nil => exact cO_zero
  | cons d L ih =>
    have hL' : ∀ e ∈ L, e ∈ o0Codes := fun e he => hL e (List.mem_cons_of_mem _ he)
    rw [List.foldr_cons, cO_xor (hL d List.mem_cons_self) (foldr_mem L hL'), ih hL',
      List.map_cons, List.prod_cons]

open Classical in
theorem mem_prod_iff {U : Subgroup ModO} (hU : U.index = 2) (L : List ModO) :
    L.prod ∈ U ↔ Even (L.countP fun v => decide (v ∉ U)) := by
  induction L with
  | nil => simp [one_mem]
  | cons v L ih =>
    rw [List.prod_cons, Subgroup.mul_mem_iff_of_index_two hU, ih, List.countP_cons]
    by_cases hv : v ∈ U
    · simp [hv]
    · simp [hv, Nat.even_add_one]

open Classical in
theorem hasCode_of_bits {U : Subgroup ModO} (hU : U.index = 2) (h129 : cO 129 ∉ U) {b : ℕ}
    (hb64 : b < 64) (hb : ∀ k < 6, (cO (2 ^ (k + 1)) ∉ U ↔ b.testBit k = true)) :
    HasCode U b := by
  intro c hc
  obtain ⟨hdec, hbas, hpar⟩ := decomp_check
  have hsub : ∀ d ∈ decomp c, d ∈ o0Codes := fun d hd => hbas d (List.mem_filter.1 hd).1
  rw [← hdec c hc, cO_foldr _ hsub, mem_prod_iff hU, List.countP_map, hdec c hc, ← hpar b hb64 c hc]
  have hcongr : (decomp c).countP ((fun v => decide (v ∉ U)) ∘ cO) =
      (decomp c).countP (outB b) := by
    refine List.countP_congr fun d hd => ?_
    have hd' : d ∈ basO := (List.mem_filter.1 hd).1
    simp only [basO, List.mem_cons, List.not_mem_nil, or_false] at hd'
    simp only [Function.comp_apply, decide_eq_true_eq]
    have e2 : cO 2 ∉ U ↔ b.testBit 0 = true := by simpa using hb 0 (by norm_num)
    have e4 : cO 4 ∉ U ↔ b.testBit 1 = true := by simpa using hb 1 (by norm_num)
    have e8 : cO 8 ∉ U ↔ b.testBit 2 = true := by simpa using hb 2 (by norm_num)
    have e16 : cO 16 ∉ U ↔ b.testBit 3 = true := by simpa using hb 3 (by norm_num)
    have e32 : cO 32 ∉ U ↔ b.testBit 4 = true := by simpa using hb 4 (by norm_num)
    have e64 : cO 64 ∉ U ↔ b.testBit 5 = true := by simpa using hb 5 (by norm_num)
    rcases hd' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp [outB, h129]
    · simp [outB, e2]
    · simp [outB, e4]
    · simp [outB, e8]
    · simp [outB, e16]
    · simp [outB, e32]
    · simp [outB, e64]
  rw [hcongr]
  simp

theorem bit_lt {β : Bool} {n m : ℕ} (h : n < 2 ^ m) : Nat.bit β n < 2 ^ (m + 1) := by
  cases β <;> simp [Nat.bit, pow_succ] <;> omega

open Classical in
theorem exists_hasCode {U : Subgroup ModO} (hU : U.index = 2) (h129 : cO 129 ∉ U) :
    ∃ b < 64, HasCode U b := by
  set β : ℕ → Bool := fun k => decide (cO (2 ^ (k + 1)) ∉ U) with hβ
  set b := Nat.bit (β 0) (Nat.bit (β 1) (Nat.bit (β 2) (Nat.bit (β 3) (Nat.bit (β 4)
    (Nat.bit (β 5) 0))))) with hbdef
  have hb64 : b < 64 := by
    have h0 : (0 : ℕ) < 2 ^ 0 := by norm_num
    exact bit_lt (bit_lt (bit_lt (bit_lt (bit_lt (bit_lt h0)))))
  refine ⟨b, hb64, hasCode_of_bits hU h129 hb64 fun k hk => ?_⟩
  interval_cases k <;> simp [hbdef, hβ, Nat.testBit_bit_succ]

theorem hasCode_map {U : Subgroup ModO} {b b' : ℕ} (hU : HasCode U b)
    {g : ↥(quasithinG2 (ZMod 2))} (hg : hypMaps (matCode g.1) b b' = true) :
    HasCode (U.map (g2OAct (ZMod 2) g).toMonoidHom) b' := by
  have hg' : ∀ d ∈ o0Codes, parB b' (mact (matCode g.1) d) = parB b d := by
    intro d hd
    have := List.all_eq_true.1 hg d hd
    simpa using this
  intro c hc
  constructor
  · rintro ⟨u, hu, hcu⟩
    obtain ⟨d, hd, rfl⟩ := exists_cO u
    have h1 : cO (mact (matCode g.1) d) = cO c := by
      rw [← act_cO g hd]
      exact hcu
    rw [← cO_inj (mact_mem hd) hc h1, hg' d hd]
    exact (hU d hd).1 hu
  · intro hpc
    set d := mact (matCode g⁻¹.1) c with hddef
    have hd : d ∈ o0Codes := mact_mem hc
    have hgd : mact (matCode g.1) d = c := by
      rw [hddef, ← mact_mul _ _ (mem_o0Codes.1 hc).1, mul_inv_cancel, mact_one (mem_o0Codes.1 hc).1]
    refine ⟨cO d, (hU d hd).2 ?_, ?_⟩
    · rw [← hg' d hd, hgd]
      exact hpc
    · change g2OAct (ZMod 2) g (cO d) = cO c
      rw [act_cO g hd, hgd]

theorem mem_stabSub_of_hasCode_map {U : Subgroup ModO} {φ : MulAut ModO}
    (h : U.map φ.toMonoidHom = U) : φ ∈ stabSub U :=
  CFSG.Quasithin.StabLat.mem_stabSub_of_map_eq h

theorem mem_stabSub_of_hypMaps {U : Subgroup ModO} {b : ℕ} (hU : HasCode U b)
    {g : ↥(quasithinG2 (ZMod 2))} (hg : hypMaps (matCode g.1) b b = true) :
    g2OAct (ZMod 2) g ∈ stabSub U :=
  mem_stabSub_of_hasCode_map (eq_of_hasCode (hasCode_map hU hg) hU)

theorem not_mem_stabSub_of {U : Subgroup ModO} {b : ℕ} (hU : HasCode U b)
    {g : ↥(quasithinG2 (ZMod 2))}
    (hg : ∃ c ∈ o0Codes, parB b c = true ∧ parB b (mact (matCode g.1) c) = false) :
    g2OAct (ZMod 2) g ∉ stabSub U := by
  obtain ⟨c, hc, h1, h2⟩ := hg
  intro hs
  have h3 := (hs (cO c)).2 ((hU c hc).2 h1)
  rw [act_cO g hc, hU _ (mact_mem hc), h2] at h3
  exact Bool.false_ne_true h3

theorem not_mem_centSub_of {U : Subgroup ModO} {b : ℕ} (hU : HasCode U b)
    {g : ↥(quasithinG2 (ZMod 2))}
    (hg : ∃ c ∈ o0Codes, parB b c = true ∧ mact (matCode g.1) c ≠ c) :
    g2OAct (ZMod 2) g ∉ centSub U := by
  obtain ⟨c, hc, h1, h2⟩ := hg
  intro hs
  have h3 := hs (cO c) ((hU c hc).2 h1)
  rw [act_cO g hc] at h3
  exact h2 (cO_inj (mact_mem hc) hc h3)

theorem sing_eq {U : Subgroup ModO} {b b' : ℕ} (hU : HasCode U b) (g : ↥(quasithinG2 (ZMod 2)))
    (hU' : HasCode (U.map (g2OAct (ZMod 2) g).toMonoidHom) b') : sing b' = sing b := by
  have key : ∀ c : O0C, (parB b' (o0Act g c).1 && decide (zornNorm (decodeZ (o0Act g c).1) = 0))
      = (parB b c.1 && decide (zornNorm (decodeZ c.1) = 0)) := by
    intro c
    have hn : zornNorm (decodeZ (o0Act g c).1) = zornNorm (decodeZ c.1) := by
      change zornNorm (decodeZ (mact (matCode g.1) c.1)) = _
      rw [decodeZ_mact' g.1 (mem_o0Codes.1 c.2).1]
      exact quasithinG2_norm g.2 _
    have hp : parB b' (o0Act g c).1 = parB b c.1 := by
      have h1 := hU' (o0Act g c).1 (o0Act g c).2
      have h2 : cO (o0Act g c).1 ∈ U.map (g2OAct (ZMod 2) g).toMonoidHom ↔ cO c.1 ∈ U := by
        change cO (mact (matCode g.1) c.1) ∈ _ ↔ _
        rw [← act_cO g c.2]
        constructor
        · rintro ⟨u, hu, hgu⟩
          have := (g2OAct (ZMod 2) g).injective hgu
          rw [← this]
          exact hu
        · intro h
          exact ⟨_, h, rfl⟩
      rw [h2, hU c.1 c.2] at h1
      exact Bool.eq_iff_iff.2 h1.symm
    rw [hn, hp]
  have e : {c : O0C // (parB b c.1 && decide (zornNorm (decodeZ c.1) = 0)) = true} ≃
      {c : O0C // (parB b' c.1 && decide (zornNorm (decodeZ c.1) = 0)) = true} :=
    { toFun := fun c => ⟨o0Act g c.1, by rw [key]; exact c.2⟩
      invFun := fun c => ⟨o0Act g⁻¹ c.1, by
        have := key (o0Act g⁻¹ c.1)
        have hgg : o0Act g (o0Act g⁻¹ c.1) = c.1 := by
          apply Subtype.ext
          change mact (matCode g.1) (mact (matCode g⁻¹.1) c.1.1) = c.1.1
          rw [← mact_mul _ _ (mem_o0Codes.1 c.1.2).1, mul_inv_cancel,
            mact_one (mem_o0Codes.1 c.1.2).1]
        rw [hgg] at this
        rw [← this]
        exact c.2⟩
      left_inv := fun c => by
        apply Subtype.ext
        apply Subtype.ext
        change mact (matCode g⁻¹.1) (mact (matCode g.1) c.1.1) = c.1.1
        rw [← mact_mul _ _ (mem_o0Codes.1 c.1.2).1, inv_mul_cancel,
          mact_one (mem_o0Codes.1 c.1.2).1]
      right_inv := fun c => by
        apply Subtype.ext
        apply Subtype.ext
        change mact (matCode g.1) (mact (matCode g⁻¹.1) c.1.1) = c.1.1
        rw [← mact_mul _ _ (mem_o0Codes.1 c.1.2).1, mul_inv_cancel,
          mact_one (mem_o0Codes.1 c.1.2).1] }
  have h1 := card_o0C_filter fun c => parB b c && decide (zornNorm (decodeZ c) = 0)
  have h2 := card_o0C_filter fun c => parB b' c && decide (zornNorm (decodeZ c) = 0)
  rw [sing, sing, ← h1, ← h2]
  exact (Nat.card_congr e).symm

theorem orbR_eq_of_sing {b r : ℕ} (hb : b < 64) (hr : r = 0 ∨ r = 9) (h : sing b = sing r) :
    orbR.getD b 0 = r := by
  obtain ⟨horb, hne⟩ := orb_check
  obtain ⟨-, -, -, h09, hs⟩ := horb b hb
  rcases h09 with h0 | h9 <;> rcases hr with rfl | rfl
  · exact h0
  · rw [hs, h0] at h; exact absurd h hne
  · rw [hs, h9] at h; exact absurd h.symm hne
  · exact h9

theorem matCode_wordGG {w : List ℕ} (hw : ∀ t ∈ w, t = 1 ∨ t = 2) :
    matCode (wordGG w).1 = wMat w := by
  change matCode ⇑(wordG (R := ZMod 2) w) = _
  unfold matCode wMat
  refine List.map_congr_left fun k hk => ?_
  have hk8 : 2 ^ k < 256 := by
    have h8 : k < 8 := List.mem_range.1 hk
    calc 2 ^ k < 2 ^ 8 := Nat.pow_lt_pow_right (by norm_num) h8
      _ = 256 := by norm_num
  obtain ⟨h1, h2⟩ := decodeZ_applyG hw hk8
  rw [← h1, encodeZ_decodeZ _ h2]

theorem matCode_mulG' (g h : ↥(quasithinG2 (ZMod 2))) :
    matCode (g * h).1 = mmul (matCode g.1) (matCode h.1) :=
  matCode_mul g.1 h.1

@[expose] def wElt (gs : List ↥(quasithinG2 (ZMod 2))) (w : List ℕ) : ↥(quasithinG2 (ZMod 2)) :=
  (w.map fun i => gs.getD i 1).prod

theorem matCode_wElt (gs : List ↥(quasithinG2 (ZMod 2))) {w : List ℕ}
    (hw : ∀ i ∈ w, i < gs.length) :
    matCode (wElt gs w).1 = wprod (gs.map fun g => matCode g.1) w := by
  induction w with
  | nil => exact matCode_one
  | cons i w ih =>
    have hw' : ∀ j ∈ w, j < gs.length := fun j hj => hw j (List.mem_cons_of_mem _ hj)
    have hi : i < gs.length := hw i List.mem_cons_self
    rw [wElt, List.map_cons, List.prod_cons]
    change matCode ((gs.getD i 1) * wElt gs w).1 = _
    rw [matCode_mulG', ih hw']
    show mmul _ (wprod _ w) = mmul _ (wprod _ w)
    congr 1
    rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ (by simpa using hi),
      List.getElem_map]

theorem wElt_mem (gs : List ↥(quasithinG2 (ZMod 2))) (w : List ℕ)
    {H : Subgroup ↥(quasithinG2 (ZMod 2))}
    (hgs : ∀ g ∈ gs, g ∈ H) : wElt gs w ∈ H := by
  refine H.list_prod_mem fun g hg => ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hg
  by_cases hi : i < gs.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact hgs _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact one_mem H

theorem eq_of_matCode {g h : ↥(quasithinG2 (ZMod 2))} (e : matCode g.1 = matCode h.1) : g = h :=
  Subtype.ext (linearEquiv_eq_of_matCode e)

theorem orderOf_act_eq_three {g : ↥(quasithinG2 (ZMod 2))}
    (h3 : mmul (matCode g.1) (mmul (matCode g.1) (matCode g.1)) = idMat)
    (h1 : matCode g.1 ≠ idMat) : orderOf (g2OAct (ZMod 2) g) = 3 := by
  rw [orderOf_injective _ g2OAct_injective]
  have hg3 : g ^ 3 = 1 := by
    rw [pow_three]
    apply eq_of_matCode
    rw [matCode_mulG', matCode_mulG', h3]
    exact matCode_one.symm
  exact orderOf_eq_prime hg3 fun h => h1 (by rw [h]; exact matCode_one)

section Transport

variable {W W' : Type} [CommGroup W] [CommGroup W']

@[expose] def HypXConcl (Lb Mb : Subgroup (MulAut W)) (U : Subgroup W) : Prop :=
  (∃ X : Subgroup (MulAut W), X ≤ Lb ⊓ stabSub U ∧ Nat.card X = 3 ∧ ¬ X ≤ centSub U ∧
    ∃ t ∈ Mb ⊓ Subgroup.normalizer (X : Set (MulAut W)), t ∉ stabSub U ∧ t ^ 2 ∈ stabSub U) ∨
  ∃ Y : Subgroup (MulAut W), Y ≤ Lb ⊓ stabSub U ∧ Nat.card Y = 27 ∧
    (∀ y ∈ Y, y ^ 3 = 1) ∧ Y ⊓ centSub U = ⊥

@[expose] def HypConcl (X Lb : Subgroup (MulAut W)) (U : Subgroup W) : Prop :=
  IsMaxSubgroupIn X (X ⊓ stabSub U) ∧ (X ⊓ stabSub U).relIndex X ≠ 2 ∧
    ∃ Y : Subgroup (MulAut W), Y ≤ Lb ⊓ stabSub U ∧ Nat.card Y = 3 ∧ ¬ Y ≤ centSub U

theorem stabSub_map (e : W ≃* W') (U : Subgroup W) :
    stabSub (U.map e.toMonoidHom) = (stabSub U).map (MulAut.congr e).toMonoidHom :=
  CFSG.Quasithin.StabLat.stabSub_map_equiv e U

theorem centSub_map (e : W ≃* W') (U : Subgroup W) :
    centSub (U.map e.toMonoidHom) = (centSub U).map (MulAut.congr e).toMonoidHom :=
  CFSG.Quasithin.StabLat.centSub_map_equiv e U

theorem HypXConcl.map (e : W ≃* W') {Lb Mb : Subgroup (MulAut W)} {U : Subgroup W}
    (h : HypXConcl Lb Mb U) :
    HypXConcl (Lb.map (MulAut.congr e).toMonoidHom) (Mb.map (MulAut.congr e).toMonoidHom)
      (U.map e.toMonoidHom) := by
  rw [HypXConcl, stabSub_map, centSub_map]
  set φ := (MulAut.congr e).toMonoidHom with hφ
  have hinj : Function.Injective φ := (MulAut.congr e).injective
  rcases h with ⟨X, hX, hX3, hXc, t, ⟨htM, htN⟩, htU, ht2⟩ | ⟨Y, hY, hY27, hY3, hYc⟩
  · left
    refine ⟨X.map φ, ?_, by rw [Subgroup.card_map_of_injective hinj, hX3], ?_, φ t,
      ⟨Subgroup.mem_map_of_mem _ htM, Subgroup.le_normalizer_map φ (Subgroup.mem_map_of_mem _ htN)⟩,
      ?_, ?_⟩
    · rw [← Subgroup.map_inf_eq _ _ φ hinj]
      exact Subgroup.map_mono hX
    · rwa [Subgroup.map_le_map_iff_of_injective hinj]
    · rwa [Subgroup.mem_map_iff_mem hinj]
    · rw [← map_pow]
      exact Subgroup.mem_map_of_mem _ ht2
  · right
    refine ⟨Y.map φ, ?_, by rw [Subgroup.card_map_of_injective hinj, hY27], ?_, ?_⟩
    · rw [← Subgroup.map_inf_eq _ _ φ hinj]
      exact Subgroup.map_mono hY
    · rintro _ ⟨y, hy, rfl⟩
      rw [← map_pow, hY3 y hy, map_one]
    · rw [← Subgroup.map_inf_eq _ _ φ hinj, hYc, Subgroup.map_bot]

theorem HypConcl.map (e : W ≃* W') {X Lb : Subgroup (MulAut W)} {U : Subgroup W}
    (h : HypConcl X Lb U) :
    HypConcl (X.map (MulAut.congr e).toMonoidHom) (Lb.map (MulAut.congr e).toMonoidHom)
      (U.map e.toMonoidHom) := by
  obtain ⟨⟨hlt, hmax⟩, hidx, Y, hY, hY3, hYc⟩ := h
  rw [HypConcl, stabSub_map, centSub_map]
  set φ := (MulAut.congr e).toMonoidHom with hφ
  have hinj : Function.Injective φ := (MulAut.congr e).injective
  have hsurj : Function.Surjective φ := (MulAut.congr e).surjective
  rw [← Subgroup.map_inf_eq _ _ φ hinj]
  refine ⟨⟨(Subgroup.map_lt_map_iff_of_injective hinj).2 hlt, fun K hK hKX => ?_⟩, ?_, Y.map φ,
    ?_, by rw [Subgroup.card_map_of_injective hinj, hY3], by
      rwa [Subgroup.map_le_map_iff_of_injective hinj]⟩
  · have hKe : (K.comap φ).map φ = K := Subgroup.map_comap_eq_self_of_surjective hsurj K
    rw [← hKe] at hK hKX ⊢
    rw [hmax (K.comap φ) ((Subgroup.map_lt_map_iff_of_injective hinj).1 hK)
      ((Subgroup.map_le_map_iff_of_injective hinj).1 hKX)]
  · rwa [Subgroup.relIndex_map_map_of_injective _ _ hinj]
  · rw [← Subgroup.map_inf_eq _ _ φ hinj]
    exact Subgroup.map_mono hY

theorem HypXConcl.mono {Lb Mb Mb' : Subgroup (MulAut W)} {U : Subgroup W} (hM : Mb ≤ Mb')
    (h : HypXConcl Lb Mb U) : HypXConcl Lb Mb' U := by
  rcases h with ⟨X, hX, hX3, hXc, t, ⟨htM, htN⟩, htU, ht2⟩ | h
  · exact Or.inl ⟨X, hX, hX3, hXc, t, ⟨hM htM, htN⟩, htU, ht2⟩
  · exact Or.inr h

theorem map_congr_self {H : Subgroup (MulAut W)} {ψ : MulAut W} (hψ : ψ ∈ H) :
    H.map (MulAut.congr ψ).toMonoidHom = H := by
  ext a
  constructor
  · rintro ⟨b, hb, rfl⟩
    change MulAut.congr ψ b ∈ H
    rw [congr_eq_conj]
    exact H.mul_mem (H.mul_mem hψ hb) (H.inv_mem hψ)
  · intro ha
    refine ⟨ψ⁻¹ * a * ψ, H.mul_mem (H.mul_mem (H.inv_mem hψ) ha) hψ, ?_⟩
    change MulAut.congr ψ (ψ⁻¹ * a * ψ) = a
    rw [congr_eq_conj]
    group

end Transport

@[expose] noncomputable def Lb0 : Subgroup (MulAut ModO) :=
  (g2Derived (ZMod 2)).map (g2OAct (ZMod 2))

@[expose] noncomputable def Mb0 : Subgroup (MulAut ModO) := (g2OAct (ZMod 2)).range

theorem act_mem_Lb0 (w : List ℕ) : g2OAct (ZMod 2) (wordGG w) ∈ Lb0 :=
  ⟨_, wordGG_mem_derived w, rfl⟩

theorem Lb0_le_Mb0 : Lb0 ≤ Mb0 := Subgroup.map_le_range _ _

theorem mem_normalizer_zpowers {G : Type} [Group G] [Finite G] {x t : G}
    (h : t * x * t⁻¹ ∈ Subgroup.zpowers x) :
    t ∈ Subgroup.normalizer (Subgroup.zpowers x : Set G) := by
  classical
  set X := Subgroup.zpowers x
  have hconj : ∀ y ∈ X, t * y * t⁻¹ ∈ X := by
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    have e : t * x ^ k * t⁻¹ = (t * x * t⁻¹) ^ k := by
      rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply]
    rw [e]
    exact X.zpow_mem h k
  let f : ↥X → ↥X := fun y => ⟨t * y * t⁻¹, hconj y y.2⟩
  have hf : Function.Injective f := fun y z hyz => by
    have h1 : t * (y : G) * t⁻¹ = t * z * t⁻¹ := congrArg Subtype.val hyz
    exact Subtype.ext (by simpa using h1)
  have hfs : Function.Surjective f := Finite.injective_iff_surjective.1 hf
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨fun hg => hconj g hg, fun hg => ?_⟩
  obtain ⟨y, hy⟩ := hfs ⟨t * g * t⁻¹, hg⟩
  have h1 : t * (y : G) * t⁻¹ = t * g * t⁻¹ := congrArg Subtype.val hy
  have h2 : (y : G) = g := by simpa using h1
  rw [← h2]
  exact y.2

theorem finite_modO : Finite ModO := Nat.finite_of_card_ne_zero (by rw [card_ModO]; norm_num)

instance : Finite (MulAut ModO) :=
  have := finite_modO
  Finite.of_injective _ DFunLike.coe_injective

theorem hypX_zero_left {U : Subgroup ModO} (hU : HasCode U 0) :
    ∃ X : Subgroup (MulAut ModO), X ≤ Lb0 ⊓ stabSub U ∧ Nat.card X = 3 ∧ ¬ X ≤ centSub U ∧
      ∃ t ∈ Mb0 ⊓ Subgroup.normalizer (X : Set (MulAut ModO)), t ∉ stabSub U ∧
        t ^ 2 ∈ stabSub U := by
  obtain ⟨htw, hx3, hx1, hxs, hxm, ht2, htm, htx⟩ := t0_check
  have hw1 : ∀ t ∈ [1], t = 1 ∨ t = 2 := by simp
  set x := wordGG [1] with hxdef
  have hxc : matCode x.1 = wMat [1] := matCode_wordGG hw1
  set t₀ : ↥(quasithinG2 (ZMod 2)) := wordGG tW0 * ⟨zX, mem_quasithinG2 zX_mul⟩ with ht₀
  have htc : matCode t₀.1 = mmul (wMat tW0) matX := by
    rw [matCode_mulG', matCode_wordGG htw]
    exact congrArg _ matCode_zX
  have hrel : t₀ * x * t₀⁻¹ = x * x := by
    have h1 : t₀ * x = x * x * t₀ := by
      apply eq_of_matCode
      calc matCode (t₀ * x).1 = mmul (matCode t₀.1) (matCode x.1) := matCode_mulG' _ _
        _ = mmul (mmul (wMat tW0) matX) (wMat [1]) := by rw [htc, hxc]
        _ = mmul (mmul (wMat [1]) (wMat [1])) (mmul (wMat tW0) matX) := htx
        _ = mmul (mmul (matCode x.1) (matCode x.1)) (matCode t₀.1) := by rw [htc, hxc]
        _ = matCode (x * x * t₀).1 := by rw [matCode_mulG' (x * x) t₀, matCode_mulG' x x]
    rw [h1, mul_inv_cancel_right]
  refine ⟨Subgroup.zpowers (g2OAct (ZMod 2) x), ?_, ?_, ?_, g2OAct (ZMod 2) t₀,
    ⟨⟨t₀, rfl⟩, ?_⟩, ?_, ?_⟩
  · rw [Subgroup.zpowers_le]
    exact ⟨act_mem_Lb0 [1], mem_stabSub_of_hypMaps hU (by rw [hxc]; exact hxs)⟩
  · rw [Nat.card_zpowers, orderOf_act_eq_three (by rw [hxc]; exact hx3) (by rw [hxc]; exact hx1)]
  · intro h
    exact not_mem_centSub_of hU (by rw [hxc]; exact hxm) (h (Subgroup.mem_zpowers _))
  · apply mem_normalizer_zpowers
    rw [← map_inv, ← map_mul, ← map_mul, hrel, map_mul]
    exact Subgroup.mul_mem _ (Subgroup.mem_zpowers _) (Subgroup.mem_zpowers _)
  · exact not_mem_stabSub_of hU (by rw [htc]; exact htm)
  · rw [← map_pow]
    exact mem_stabSub_of_hypMaps hU (by rw [pow_two, matCode_mulG', htc]; exact ht2)

theorem hypX_zero {U : Subgroup ModO} (hU : HasCode U 0) : HypXConcl Lb0 Mb0 U :=
  Or.inl (hypX_zero_left hU)

@[expose] noncomputable def Y0 : Subgroup ↥(quasithinG2 (ZMod 2)) where
  carrier := {g | matCode g.1 ∈ yMats}
  mul_mem' {a b} ha hb := by
    obtain ⟨-, -, -, -, -, -, hcl, -⟩ := y_check
    change matCode (a * b).1 ∈ yMats
    rw [matCode_mulG']
    exact hcl _ ha _ hb
  one_mem' := by
    obtain ⟨-, -, -, -, -, -, -, h1, -⟩ := y_check
    change matCode (1 : ↥(quasithinG2 (ZMod 2))).1 ∈ yMats
    rw [show matCode (1 : ↥(quasithinG2 (ZMod 2))).1 = idMat from matCode_one]
    exact h1
  inv_mem' {a} ha := by
    obtain ⟨-, -, -, -, -, -, hcl, -, hcube, -⟩ := y_check
    have h3 : a * (a * a) = 1 := eq_of_matCode (by
      rw [matCode_mulG', matCode_mulG', hcube _ ha]
      exact matCode_one.symm)
    have hinv : a⁻¹ = a * a := inv_eq_of_mul_eq_one_right h3
    change matCode a⁻¹.1 ∈ yMats
    rw [hinv, matCode_mulG']
    exact hcl _ ha _ ha

theorem mem_Y0 {g : ↥(quasithinG2 (ZMod 2))} : g ∈ Y0 ↔ matCode g.1 ∈ yMats := Iff.rfl

@[expose] def yGens : List ↥(quasithinG2 (ZMod 2)) := [wordGG yaW, wordGG ybW]

theorem Y0_eq_wElt {g : ↥(quasithinG2 (ZMod 2))} (hg : g ∈ Y0) :
    ∃ i < 27, g = wElt yGens (yWords.getD i []) := by
  obtain ⟨hwa, hwb, hlen, -, hwlen, hw, -⟩ := y_check
  obtain ⟨i, hi, hgi⟩ := List.getElem_of_mem (mem_Y0.1 hg)
  rw [hlen] at hi
  refine ⟨i, hi, eq_of_matCode ?_⟩
  obtain ⟨hcode, hj⟩ := hw i hi
  rw [matCode_wElt yGens (fun j hj' => by simpa [yGens] using hj j hj')]
  simp only [yGens, List.map_cons, List.map_nil]
  rw [matCode_wordGG hwa, matCode_wordGG hwb, hcode, List.getD_eq_getElem _ _ (by omega), hgi]

theorem Y0_le_derived : Y0 ≤ g2Derived (ZMod 2) := by
  intro g hg
  obtain ⟨i, -, rfl⟩ := Y0_eq_wElt hg
  refine wElt_mem _ _ fun h hh => ?_
  simp only [yGens, List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl <;> exact wordGG_mem_derived _

theorem card_Y0 : Nat.card Y0 = 27 := by
  obtain ⟨hwa, hwb, hlen, hnd, hwlen, hw, -⟩ := y_check
  have e : ↥Y0 ≃ {m : List ℕ // m ∈ yMats} :=
    { toFun := fun g => ⟨matCode g.1.1, g.2⟩
      invFun := fun m => ⟨wElt yGens (yWords.getD (yMats.idxOf m.1) []), by
        have hi : yMats.idxOf m.1 < 27 := hlen ▸ List.idxOf_lt_length_of_mem m.2
        obtain ⟨hcode, hj⟩ := hw _ hi
        change matCode (wElt yGens _).1 ∈ yMats
        rw [matCode_wElt yGens (fun j hj' => by simpa [yGens] using hj j hj')]
        simp only [yGens, List.map_cons, List.map_nil]
        rw [matCode_wordGG hwa, matCode_wordGG hwb, hcode, List.getD_eq_getElem _ _ (by omega)]
        exact List.getElem_mem _⟩
      left_inv := fun g => by
        apply Subtype.ext
        apply eq_of_matCode
        have hi : yMats.idxOf (matCode g.1.1) < 27 := hlen ▸ List.idxOf_lt_length_of_mem g.2
        obtain ⟨hcode, hj⟩ := hw _ hi
        change matCode (wElt yGens _).1 = _
        rw [matCode_wElt yGens (fun j hj' => by simpa [yGens] using hj j hj')]
        simp only [yGens, List.map_cons, List.map_nil]
        rw [matCode_wordGG hwa, matCode_wordGG hwb, hcode,
          List.getD_eq_getElem _ _ (by omega), List.getElem_idxOf]
      right_inv := fun m => by
        apply Subtype.ext
        have hi : yMats.idxOf m.1 < 27 := hlen ▸ List.idxOf_lt_length_of_mem m.2
        obtain ⟨hcode, hj⟩ := hw _ hi
        change matCode (wElt yGens _).1 = m.1
        rw [matCode_wElt yGens (fun j hj' => by simpa [yGens] using hj j hj')]
        simp only [yGens, List.map_cons, List.map_nil]
        rw [matCode_wordGG hwa, matCode_wordGG hwb, hcode,
          List.getD_eq_getElem _ _ (by omega), List.getElem_idxOf] }
  have e' : {m : List ℕ // m ∈ yMats} ≃ ↥(yMats.toFinset) :=
    Equiv.subtypeEquivRight fun m => by simp
  rw [Nat.card_congr (e.trans e'), Nat.card_eq_fintype_card, Fintype.card_coe,
    List.toFinset_card_of_nodup hnd, hlen]

theorem hypX_nine_right {U : Subgroup ModO} (hU : HasCode U 9) :
    ∃ Y : Subgroup (MulAut ModO), Y ≤ Lb0 ⊓ stabSub U ∧ Nat.card Y = 27 ∧
      (∀ y ∈ Y, y ^ 3 = 1) ∧ Y ⊓ centSub U = ⊥ := by
  obtain ⟨-, -, -, -, -, -, -, -, hcube, hst, hmove⟩ := y_check
  refine ⟨Y0.map (g2OAct (ZMod 2)), ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨g, hg, rfl⟩
    exact ⟨⟨g, Y0_le_derived hg, rfl⟩, mem_stabSub_of_hypMaps hU (hst _ hg)⟩
  · rw [Subgroup.card_map_of_injective g2OAct_injective, card_Y0]
  · rintro _ ⟨g, hg, rfl⟩
    rw [← map_pow]
    have h3 : g * (g * g) = 1 := eq_of_matCode (by
      rw [matCode_mulG', matCode_mulG', hcube _ hg]
      exact matCode_one.symm)
    rw [pow_three, h3, map_one]
  · refine eq_bot_iff.2 ?_
    rintro _ ⟨⟨g, hg, rfl⟩, hc⟩
    rw [Subgroup.mem_bot]
    by_cases h1 : matCode g.1 = idMat
    · have : g = 1 := eq_of_matCode (by rw [h1]; exact matCode_one.symm)
      rw [this, map_one]
    · exact absurd hc (not_mem_centSub_of hU (hmove _ hg h1))

theorem hypX_nine {U : Subgroup ModO} (hU : HasCode U 9) : HypXConcl Lb0 Mb0 U :=
  Or.inr (hypX_nine_right hU)

theorem index_map_act (U : Subgroup ModO) (φ : MulAut ModO) :
    (U.map φ.toMonoidHom).index = U.index :=
  Subgroup.index_map_equiv (H := U) φ

theorem map_act_mul (U : Subgroup ModO) (g h : ↥(quasithinG2 (ZMod 2))) :
    U.map (g2OAct (ZMod 2) (g * h)).toMonoidHom =
      (U.map (g2OAct (ZMod 2) h).toMonoidHom).map (g2OAct (ZMod 2) g).toMonoidHom := by
  rw [Subgroup.map_map, map_mul]
  rfl

theorem exists_code_image {r : ℕ} (hr : r = 0 ∨ r = 9) {U : Subgroup ModO} (hU : HasCode U r)
    (hidx : U.index = 2) (g : ↥(quasithinG2 (ZMod 2))) :
    ∃ b < 64, orbR.getD b 0 = r ∧ HasCode (U.map (g2OAct (ZMod 2) g).toMonoidHom) b := by
  have hidx' : (U.map (g2OAct (ZMod 2) g).toMonoidHom).index = 2 := by
    rw [index_map_act, hidx]
  have h129 : cO 129 ∉ U.map (g2OAct (ZMod 2) g).toMonoidHom := by
    rw [Subgroup.mem_map_equiv]
    have e : (g2OAct (ZMod 2) g).symm (cO 129) = cO 129 := by
      rw [MulEquiv.symm_apply_eq]
      exact (act_cO_129 g).symm
    rw [e]
    exact cO_129_not_mem hU
  obtain ⟨b, hb, hcb⟩ := exists_hasCode hidx' h129
  exact ⟨b, hb, orbR_eq_of_sing hb hr (sing_eq hU g hcb), hcb⟩

theorem hasCode_orb {r : ℕ} {U : Subgroup ModO} (hU : HasCode U r) {b : ℕ} (hb : b < 64)
    (hrb : orbR.getD b 0 = r) :
    HasCode (U.map (g2OAct (ZMod 2) (wordGG (orbW.getD b []))).toMonoidHom) b := by
  obtain ⟨hw, hm, hmaps, -, -⟩ := orb_check.1 b hb
  refine hasCode_map hU ?_
  rw [matCode_wordGG hw, hm, ← hrb]
  exact hmaps

theorem mem_stabSub_of_map_eq {U : Subgroup ModO} {φ ψ : MulAut ModO}
    (h : U.map φ.toMonoidHom = U.map ψ.toMonoidHom) : ψ⁻¹ * φ ∈ stabSub U := by
  apply mem_stabSub_of_hasCode_map
  have e : (ψ⁻¹ * φ).toMonoidHom = (ψ⁻¹).toMonoidHom.comp φ.toMonoidHom := rfl
  rw [e, ← Subgroup.map_map, h, Subgroup.map_map]
  have e2 : (ψ⁻¹).toMonoidHom.comp ψ.toMonoidHom = MonoidHom.id ModO := by
    ext v
    simp
  rw [e2, Subgroup.map_id]

theorem wordGG_nil : wordGG [] = 1 := rfl

theorem wordGG_cons (t : ℕ) (w : List ℕ) : wordGG (t :: w) = wordGG [t] * wordGG w := by
  apply Subtype.ext
  simp [wordGG, wordG]

theorem act_wordGG_mem {K : Subgroup (MulAut ModO)} (h1 : g2OAct (ZMod 2) (wordGG [1]) ∈ K)
    (h2 : g2OAct (ZMod 2) (wordGG [2]) ∈ K) (w : List ℕ) (hw : ∀ t ∈ w, t = 1 ∨ t = 2) :
    g2OAct (ZMod 2) (wordGG w) ∈ K := by
  induction w with
  | nil => rw [wordGG_nil, map_one]; exact one_mem K
  | cons t w ih =>
    rw [wordGG_cons, map_mul]
    refine K.mul_mem ?_ (ih fun s hs => hw s (List.mem_cons_of_mem _ hs))
    rcases hw t List.mem_cons_self with rfl | rfl
    · exact h1
    · exact h2

theorem isMax_of_check {r : ℕ} (hr : r = 0 ∨ r = 9) {U : Subgroup ModO} (hU : HasCode U r)
    (hidx : U.index = 2) {X : Subgroup (MulAut ModO)} (hLX : Lb0 ≤ X) (hXr : X ≤ Mb0)
    {h1W h2W reps : List ℕ} {subW : List (ℕ × List ℕ × ℕ)} {cW : List (ℕ × List ℕ × List ℕ)}
    (hck : (∀ t ∈ h1W, t = 1 ∨ t = 2) ∧ (∀ t ∈ h2W, t = 1 ∨ t = 2) ∧
      hypMaps (wMat h1W) r r = true ∧ hypMaps (wMat h2W) r r = true ∧
      (∀ e ∈ subW, hypMaps (wprod [wMat h1W, wMat h2W] e.2.1) e.1 e.2.2 = true ∧
        e.2.2 ∈ reps ∧ ∀ j ∈ e.2.1, j < 2) ∧
      (∀ b < 64, orbR.getD b 0 = r → b ≠ r → ∃ e ∈ subW, e.1 = b) ∧
      (∀ ρ ∈ reps, ρ < 64 ∧ orbR.getD ρ 0 = r ∧ ∃ e ∈ cW, e.1 = ρ) ∧
      (∀ e ∈ cW, wprod [wMat h1W, wMat h2W, orbM.getD e.1 []] e.2.1 = wMat [1] ∧
        wprod [wMat h1W, wMat h2W, orbM.getD e.1 []] e.2.2 = wMat [2] ∧
        (∀ j ∈ e.2.1, j < 3) ∧ ∀ j ∈ e.2.2, j < 3))
    {o : ↥(quasithinG2 (ZMod 2))} (hoX : g2OAct (ZMod 2) o ∈ X)
    (hoU : g2OAct (ZMod 2) o ∉ stabSub U) : IsMaxSubgroupIn X (X ⊓ stabSub U) := by
  obtain ⟨hw1, hw2, hh1, hh2, hsub, hcov, hreps, hcw⟩ := hck
  set h₁ := wordGG h1W with hh₁
  set h₂ := wordGG h2W with hh₂
  have hc1 : matCode h₁.1 = wMat h1W := matCode_wordGG hw1
  have hc2 : matCode h₂.1 = wMat h2W := matCode_wordGG hw2
  have hS1 : g2OAct (ZMod 2) h₁ ∈ X ⊓ stabSub U :=
    ⟨hLX (act_mem_Lb0 _), mem_stabSub_of_hypMaps hU (by rw [hc1]; exact hh1)⟩
  have hS2 : g2OAct (ZMod 2) h₂ ∈ X ⊓ stabSub U :=
    ⟨hLX (act_mem_Lb0 _), mem_stabSub_of_hypMaps hU (by rw [hc2]; exact hh2)⟩
  have hfin : ∀ K : Subgroup (MulAut ModO), X ⊓ stabSub U ≤ K →
      g2OAct (ZMod 2) (wordGG [1]) ∈ K → g2OAct (ZMod 2) (wordGG [2]) ∈ K → X ≤ K := by
    intro K hK hk1 hk2 x hx
    obtain ⟨g, rfl⟩ := hXr hx
    obtain ⟨b, hb, hrb, hcb⟩ := exists_code_image hr hU hidx g
    have he := hasCode_orb hU hb hrb
    have hs := mem_stabSub_of_map_eq (eq_of_hasCode hcb he)
    have heK : g2OAct (ZMod 2) (wordGG (orbW.getD b [])) ∈ K :=
      act_wordGG_mem hk1 hk2 _ (orb_check.1 b hb).1
    have hmem : (g2OAct (ZMod 2) (wordGG (orbW.getD b [])))⁻¹ * g2OAct (ZMod 2) g ∈ K :=
      hK ⟨X.mul_mem (X.inv_mem (hLX (act_mem_Lb0 _))) hx, hs⟩
    have e : g2OAct (ZMod 2) g = g2OAct (ZMod 2) (wordGG (orbW.getD b [])) *
        ((g2OAct (ZMod 2) (wordGG (orbW.getD b [])))⁻¹ * g2OAct (ZMod 2) g) := by group
    rw [e]
    exact K.mul_mem heK hmem
  refine ⟨lt_of_le_of_ne inf_le_left fun h => hoU (by rw [← h] at hoX; exact hoX.2),
    fun K hlt hKX => le_antisymm hKX ?_⟩
  obtain ⟨k, hkK, hkS⟩ := IsConcreteLE.exists_of_lt hlt
  have hkX := hKX hkK
  have hkU : k ∉ stabSub U := fun h => hkS ⟨hkX, h⟩
  obtain ⟨gk, rfl⟩ := hXr hkX
  obtain ⟨b', hb', hrb', hcb'⟩ := exists_code_image hr hU hidx gk
  have hb'r : b' ≠ r := by
    rintro rfl
    exact hkU (mem_stabSub_of_hasCode_map (eq_of_hasCode hcb' hU))
  obtain ⟨ent, hent, rfl⟩ := hcov _ hb' hrb' hb'r
  obtain ⟨hmaps, hρ, hj⟩ := hsub ent hent
  obtain ⟨hρ64, hrρ, ec, hec, hecρ⟩ := hreps ent.2.2 hρ
  obtain ⟨hcw1, hcw2, hj1, hj2⟩ := hcw ec hec
  set hE := wElt [h₁, h₂] ent.2.1 with hhE
  have hEc : matCode hE.1 = wprod [wMat h1W, wMat h2W] ent.2.1 := by
    rw [hhE, matCode_wElt _ (fun j hj' => by simpa using hj j hj')]
    simp [hc1, hc2]
  have hES : g2OAct (ZMod 2) hE ∈ X ⊓ stabSub U :=
    wElt_mem [h₁, h₂] ent.2.1 (H := (X ⊓ stabSub U).comap (g2OAct (ZMod 2))) (by
      intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl
      · exact hS1
      · exact hS2)
  have hρc : HasCode (U.map (g2OAct (ZMod 2) (hE * gk)).toMonoidHom) ent.2.2 := by
    rw [map_act_mul]
    exact hasCode_map hcb' (by rw [hEc]; exact hmaps)
  set y := wordGG (orbW.getD ent.2.2 []) with hy
  have hyc := hasCode_orb hU hρ64 hrρ
  have hs := mem_stabSub_of_map_eq (eq_of_hasCode hρc hyc)
  have hyX : g2OAct (ZMod 2) y ∈ X := hLX (act_mem_Lb0 _)
  have hEgK : g2OAct (ZMod 2) (hE * gk) ∈ K := by
    rw [map_mul]
    exact K.mul_mem (hlt.le hES) hkK
  have hmem : (g2OAct (ZMod 2) y)⁻¹ * g2OAct (ZMod 2) (hE * gk) ∈ K :=
    hlt.le ⟨X.mul_mem (X.inv_mem hyX) (hKX hEgK), hs⟩
  have hyK : g2OAct (ZMod 2) y ∈ K := by
    have e : g2OAct (ZMod 2) y = g2OAct (ZMod 2) (hE * gk) *
        ((g2OAct (ZMod 2) y)⁻¹ * g2OAct (ZMod 2) (hE * gk))⁻¹ := by group
    rw [e]
    exact K.mul_mem hEgK (K.inv_mem hmem)
  have hyc' : matCode y.1 = orbM.getD ent.2.2 [] := by
    obtain ⟨hw, hm, -⟩ := orb_check.1 _ hρ64
    rw [hy, matCode_wordGG hw, hm]
  have hgens : ∀ g ∈ [h₁, h₂, y], g ∈ K.comap (g2OAct (ZMod 2)) := by
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl
    · exact hlt.le hS1
    · exact hlt.le hS2
    · exact hyK
  have hcode : ∀ w : List ℕ, (∀ j ∈ w, j < 3) → matCode (wElt [h₁, h₂, y] w).1 =
      wprod [wMat h1W, wMat h2W, orbM.getD ec.1 []] w := by
    intro w hw
    rw [matCode_wElt _ (fun j hj' => by simpa using hw j hj'), hecρ]
    simp [hc1, hc2, hyc']
  have hk1 : g2OAct (ZMod 2) (wordGG [1]) ∈ K := by
    have e1 : wordGG [1] = wElt [h₁, h₂, y] ec.2.1 := eq_of_matCode (by
      rw [hcode _ hj1, hcw1]
      exact matCode_wordGG (by simp))
    rw [e1]
    exact wElt_mem _ _ hgens
  have hk2 : g2OAct (ZMod 2) (wordGG [2]) ∈ K := by
    have e2 : wordGG [2] = wElt [h₁, h₂, y] ec.2.2 := eq_of_matCode (by
      rw [hcode _ hj2, hcw2]
      exact matCode_wordGG (by simp))
    rw [e2]
    exact wElt_mem _ _ hgens
  exact hfin K hlt.le hk1 hk2

theorem relIndex_ne_two_of {U : Subgroup ModO} {X : Subgroup (MulAut ModO)}
    {o : ↥(quasithinG2 (ZMod 2))} (hoX : g2OAct (ZMod 2) o ∈ X)
    (hoU : g2OAct (ZMod 2) o ∉ stabSub U)
    (ho3 : mmul (matCode o.1) (mmul (matCode o.1) (matCode o.1)) = idMat) :
    (X ⊓ stabSub U).relIndex X ≠ 2 := by
  intro h
  have h2 : ((X ⊓ stabSub U).subgroupOf X).index = 2 := h
  set y : ↥X := ⟨g2OAct (ZMod 2) o, hoX⟩ with hydef
  have ho : o * (o * o) = 1 := eq_of_matCode (by
    rw [matCode_mulG', matCode_mulG', ho3]
    exact matCode_one.symm)
  have hy3 : y * (y * y) = 1 := by
    apply Subtype.ext
    change g2OAct (ZMod 2) o * (g2OAct (ZMod 2) o * g2OAct (ZMod 2) o) = 1
    rw [← map_mul, ← map_mul, ho, map_one]
  have hy4 := Subgroup.mul_self_mem_of_index_two h2 (y * y)
  have e : y * y * (y * y) = y := by
    calc y * y * (y * y) = y * (y * (y * y)) := by group
      _ = y := by rw [hy3, mul_one]
  rw [e] at hy4
  exact hoU (Subgroup.mem_subgroupOf.1 hy4).2

theorem exists_three_of_faithful {U : Subgroup ModO} {Y : Subgroup (MulAut ModO)}
    (hY : Y ≤ Lb0 ⊓ stabSub U) (hY27 : Nat.card Y = 27) (hYc : Y ⊓ centSub U = ⊥) :
    ∃ Z : Subgroup (MulAut ModO), Z ≤ Lb0 ⊓ stabSub U ∧ Nat.card Z = 3 ∧ ¬ Z ≤ centSub U := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥Y) 3 (by rw [hY27]; norm_num)
  refine ⟨Subgroup.zpowers (y : MulAut ModO), (Subgroup.zpowers_le.2 y.2).trans hY,
    by rw [Nat.card_zpowers, Subgroup.orderOf_coe, hy], fun h => ?_⟩
  have h1 : (y : MulAut ModO) ∈ Y ⊓ centSub U := ⟨y.2, h (Subgroup.mem_zpowers _)⟩
  rw [hYc, Subgroup.mem_bot] at h1
  have : y = 1 := Subtype.ext h1
  rw [this, orderOf_one] at hy
  norm_num at hy

theorem hypConcl_zero {U : Subgroup ModO} (hU : HasCode U 0) (hidx : U.index = 2)
    {X : Subgroup (MulAut ModO)} (hLX : Lb0 ≤ X) (hXr : X ≤ Mb0) : HypConcl X Lb0 U := by
  obtain ⟨ho1, -, ho3, hom, -⟩ := o3_check
  have hoc : matCode (wordGG o3W0).1 = wMat o3W0 := matCode_wordGG ho1
  have hoU : g2OAct (ZMod 2) (wordGG o3W0) ∉ stabSub U :=
    not_mem_stabSub_of hU (by rw [hoc]; exact hom)
  obtain ⟨Y, hY, hY3, hYc, -⟩ := hypX_zero_left hU
  exact ⟨isMax_of_check (Or.inl rfl) hU hidx hLX hXr max_check0 (hLX (act_mem_Lb0 _)) hoU,
    relIndex_ne_two_of (hLX (act_mem_Lb0 _)) hoU (by rw [hoc]; exact ho3), Y, hY, hY3, hYc⟩

theorem hypConcl_nine {U : Subgroup ModO} (hU : HasCode U 9) (hidx : U.index = 2)
    {X : Subgroup (MulAut ModO)} (hLX : Lb0 ≤ X) (hXr : X ≤ Mb0) : HypConcl X Lb0 U := by
  obtain ⟨-, ho1, -, -, ho3, hom⟩ := o3_check
  have hoc : matCode (wordGG o3W9).1 = wMat o3W9 := matCode_wordGG ho1
  have hoU : g2OAct (ZMod 2) (wordGG o3W9) ∉ stabSub U :=
    not_mem_stabSub_of hU (by rw [hoc]; exact hom)
  obtain ⟨Y, hY, hY27, -, hYc⟩ := hypX_nine_right hU
  exact ⟨isMax_of_check (Or.inr rfl) hU hidx hLX hXr max_check9 (hLX (act_mem_Lb0 _)) hoU,
    relIndex_ne_two_of (hLX (act_mem_Lb0 _)) hoU (by rw [hoc]; exact ho3),
    exists_three_of_faithful hY hY27 hYc⟩

theorem exists_base (U : Subgroup ModO) {b : ℕ} (hb : b < 64) (hcb : HasCode U b) :
    ∃ ψ ∈ Lb0, HasCode (U.map (ψ⁻¹).toMonoidHom) (orbR.getD b 0) ∧
      (U.map (ψ⁻¹).toMonoidHom).map ψ.toMonoidHom = U ∧
      (orbR.getD b 0 = 0 ∨ orbR.getD b 0 = 9) := by
  obtain ⟨hw, hm, hmaps, h09, -⟩ := orb_check.1 b hb
  refine ⟨g2OAct (ZMod 2) (wordGG (orbW.getD b [])), act_mem_Lb0 _, ?_, ?_, h09⟩
  · intro c hc
    rw [Subgroup.mem_map_equiv]
    change g2OAct (ZMod 2) (wordGG (orbW.getD b [])) (cO c) ∈ U ↔ _
    rw [act_cO _ hc, hcb _ (mact_mem hc), matCode_wordGG hw, hm]
    have := List.all_eq_true.1 hmaps c hc
    simpa using this
  · rw [Subgroup.map_map]
    have e : (g2OAct (ZMod 2) (wordGG (orbW.getD b []))).toMonoidHom.comp
        ((g2OAct (ZMod 2) (wordGG (orbW.getD b [])))⁻¹).toMonoidHom = MonoidHom.id ModO := by
      ext v
      simp
    rw [e, Subgroup.map_id]

theorem hypX_model {U : Subgroup ModO} (hidx : U.index = 2) (h129 : cO 129 ∉ U) :
    HypXConcl Lb0 Mb0 U := by
  obtain ⟨b, hb, hcb⟩ := exists_hasCode hidx h129
  obtain ⟨ψ, hψ, hUr, hUrU, h09⟩ := exists_base U hb hcb
  have hbase : HypXConcl Lb0 Mb0 (U.map (ψ⁻¹).toMonoidHom) := by
    rcases h09 with h0 | h9
    · exact hypX_zero (h0 ▸ hUr)
    · exact hypX_nine (h9 ▸ hUr)
  have h := hbase.map ψ
  rwa [map_congr_self hψ, map_congr_self (Lb0_le_Mb0 hψ), hUrU] at h

theorem hyp_model {X : Subgroup (MulAut ModO)} (hLX : Lb0 ≤ X) (hXr : X ≤ Mb0)
    {U : Subgroup ModO} (hidx : U.index = 2) (h129 : cO 129 ∉ U) : HypConcl X Lb0 U := by
  obtain ⟨b, hb, hcb⟩ := exists_hasCode hidx h129
  obtain ⟨ψ, hψ, hUr, hUrU, h09⟩ := exists_base U hb hcb
  have hidx' : (U.map (ψ⁻¹).toMonoidHom).index = 2 := by rw [index_map_act, hidx]
  have hbase : HypConcl X Lb0 (U.map (ψ⁻¹).toMonoidHom) := by
    rcases h09 with h0 | h9
    · exact hypConcl_zero (h0 ▸ hUr) hidx' hLX hXr
    · exact hypConcl_nine (h9 ▸ hUr) hidx' hLX hXr
  have h := hbase.map ψ
  rwa [map_congr_self (hLX hψ), map_congr_self hψ, hUrU] at h

end G2Hyp

end CFSG.Quasithin.H13
