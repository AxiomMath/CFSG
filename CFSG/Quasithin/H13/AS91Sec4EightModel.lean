module

public import Certificates.Certificate89408
public import CFSG.Quasithin.H13.AS91Sec4SixModel

public section

namespace CFSG.Quasithin.H13.AS91.Two

open Subgroup CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA
open CFSG.GF2Type.Smith1979.GammaU.Viol CFSG.GF2Type.Smith1979.GammaU.Enum
open CFSG.GF2Type.Smith1979.IdxFour
open scoped Pointwise

@[expose] def xorFold (f : ℕ → ℕ) (k n : ℕ) : ℕ :=
  (List.range k).foldl (fun acc j => if n.testBit j then acc ^^^ f j else acc) 0

theorem xorFold_succ (f : ℕ → ℕ) (k n : ℕ) :
    xorFold f (k + 1) n = xorFold f k n ^^^ (if n.testBit k then f k else 0) := by
  simp only [xorFold, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
  split_ifs <;> simp

theorem xorFold_zero_left (f : ℕ → ℕ) (n : ℕ) : xorFold f 0 n = 0 := by
  simp [xorFold]

theorem xorFold_xor (f : ℕ → ℕ) (k a b : ℕ) :
    xorFold f k (a ^^^ b) = xorFold f k a ^^^ xorFold f k b := by
  induction k with
  | zero => simp [xorFold_zero_left]
  | succ k ih =>
    rw [xorFold_succ, xorFold_succ, xorFold_succ, ih, Nat.testBit_xor]
    cases a.testBit k <;> cases b.testBit k <;> simp [Nat.xor_assoc, Nat.xor_comm, Nat.xor_left_comm]

theorem app7_eq (M : Array ℕ) (n : ℕ) : app7 M n = xorFold (fun j => M[j]!) 7 n := rfl

theorem app7_xor (M : Array ℕ) (a b : ℕ) : app7 M (a ^^^ b) = app7 M a ^^^ app7 M b := by
  simp only [app7_eq, xorFold_xor]

theorem xorFold_congr {f g : ℕ → ℕ} {k : ℕ} (hfg : ∀ j < k, f j = g j) (n : ℕ) :
    xorFold f k n = xorFold g k n := by
  have key : ∀ m ≤ k, xorFold f m n = xorFold g m n := by
    intro m hm
    induction m with
    | zero => rfl
    | succ m ih => rw [xorFold_succ, xorFold_succ, ih (by omega), hfg m (by omega)]
  exact key k le_rfl

@[expose] def lam6 (M : Array ℕ) : ℕ :=
  M[1]! % 2 + 2 * (M[2]! % 2) + 4 * (M[3]! % 2) + 8 * (M[4]! % 2) + 16 * (M[5]! % 2) +
    32 * (M[6]! % 2)

theorem lam6_lt (M : Array ℕ) : lam6 M < 64 := by
  unfold lam6
  omega

theorem mk7_size (l : ℕ) (A : List ℕ) : (mk7 l A).size = 7 := by simp [mk7]

theorem mk7_getElem (l : ℕ) (A : List ℕ) {i : ℕ} (hi : i < 7) :
    (mk7 l A)[i]! = if i = 0 then 1 else (l >>> (i - 1)) % 2 + 2 * A.getD (i - 1) 0 := by
  have hs : (mk7 l A).size = 7 := by simp [mk7]
  rw [getElem!_pos _ i (by omega)]
  interval_cases i <;> simp [mk7]

theorem eq_mk7 {M : Array ℕ} (hs : M.size = 7) (h0 : M[0]! = 1) : M = mk7 (lam6 M) (aPart M) := by
  have key : ∀ j < 7, M[j]! = (mk7 (lam6 M) (aPart M))[j]! := by
    intro j hj
    rw [mk7_getElem _ _ hj]
    interval_cases j
    · simpa using h0
    all_goals
      simp only [lam6, aPart, Nat.shiftRight_eq_div_pow, List.getD_eq_getElem?_getD]
      simp [List.getElem?_drop, List.getElem?_map, Array.getElem?_toList, getElem!_pos, hs]
      omega
  apply Array.ext
  · rw [hs, mk7_size]
  · intro i h1 h2
    have := key i (by omega)
    rwa [getElem!_pos M i h1, getElem!_pos _ i h2] at this

@[expose] def vec6 (c : ℕ) : ℕ := xorFold (fun i => w1Basis.getD i 0) 6 c

theorem vec6_crd6 : ∀ w ∈ w1List, vec6 (crd6 w) = w := by decide

theorem crd6_lt : ∀ w ∈ w1List, crd6 w < 64 := by decide

@[expose] def wv7 (c : ℕ) : ℕ := xorFold (fun j => if j = 0 then 0 else w1Basis.getD (j - 1) 0) 7 c

theorem wv7_two_mul : ∀ b < 64, wv7 (2 * b) = vec6 b := by decide

theorem lt_two_of_wv7 : ∀ c < 128, wv7 c = 0 → c < 2 := by decide

theorem two_mul_xor_one : ∀ b < 64, 2 * b ^^^ 1 = 2 * b + 1 := by decide

theorem w1Basis_getD_mem (i : ℕ) : w1Basis.getD i 0 ∈ w1List := by
  have h0 : (0 : ℕ) ∈ w1List := by decide
  have hb : ∀ b ∈ w1Basis, b ∈ w1List := by decide
  rcases lt_or_ge i w1Basis.length with hi | hi
  · rw [List.getD_eq_getElem _ _ hi]
    exact hb _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ hi]
    exact h0

theorem ok48_parts :
    crdOK48 () = true ∧ stabOK48 () = true ∧ c3OK48 () = true ∧ iOK48 () = true ∧
      tOK48 () = true ∧ fusOK48 () = true ∧ orbOK48 () = true := by
  have h := Certificates.certificate89408
  simp only [ok48, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

theorem stabOK48_spec :
    gensOKb (stabGens48 ()) = true ∧
      (∀ g ∈ stabGens48 (), appN g q0c ^^^ q0c ∈ w1List) ∧
      idR ∈ enumGrp (stabGens48 ()) ∧ closedCheck (stabGens48 ()) (enumGrp (stabGens48 ())) = true ∧
      (enumGrp (stabGens48 ())).dedup.length = 768 ∧ (tOrbit ()).dedup.length = 45 := by
  have h := ok48_parts.2.1
  simp only [stabOK48, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.contains_iff_mem] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem c3OK48_spec :
    (∀ A ∈ s48 (), A.length = 6 ∧ ∀ a ∈ A, a < 64) ∧ (c3List ()).dedup.length = 3072 ∧
      (b7List ()).dedup.length = 16 ∧ t7el ∈ b7List () ∧
      (∀ x ∈ b7List (), ∀ y ∈ b7List (), mul7 x y = mul7 y x) ∧
      (∀ x ∈ b7List (), mul7 x x = id7) ∧
      ∀ X ∈ c3List (), (∀ b ∈ b7List (), mul7 X b = mul7 b X) → X ∈ b7List () := by
  have h := ok48_parts.2.2.1
  simp only [c3OK48, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.contains_iff_mem,
    Std.HashSet.contains_ofList, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  refine ⟨fun A hA => ⟨(h1 A hA).1, fun a ha => (h1 A hA).2 a ha⟩, h2, h3, h4, h5, h6, ?_⟩
  intro X hX hc
  rcases h7 X hX with h' | h'
  · exact absurd (List.all_eq_true.mpr fun b hb => beq_iff_eq.mpr (hc b hb)) (by simp [h'])
  · exact h'

theorem iOK48_spec :
    (itList ()).length = 8 ∧ (∀ w ∈ itList (), w ∈ w1List) ∧
      (∀ w ∈ itList (), 2 * crd6 w ∈ i7List ∧ 2 * crd6 w + 1 ∈ i7List) ∧
      (∀ c ∈ i7List, ∃ w ∈ itList (), crd6 w = c / 2) ∧
      (∀ w ∈ itList (), inO1b w = true → 2 * crd6 w ∈ omList ∧ 2 * crd6 w + 1 ∈ omList) ∧
      (∀ c ∈ omList, ∃ w ∈ itList (), inO1b w = true ∧ crd6 w = c / 2) ∧
      (∀ X ∈ c3List (), ∀ c ∈ omList, app7 X c ∈ omList) ∧
      (∀ c ∈ omList, ∃ X ∈ c3List (), app7 X 2 = c) ∧
      wit48.1 ∈ c3List () ∧ wit48.2 ∈ c3List () ∧
      app7 wit48.1 (app7 wit48.2 2) ≠ app7 wit48.2 (app7 wit48.1 2) ∧
      inIb iWit48 = true ∧ q0c ^^^ iWit48 ∈ w1List := by
  have h := ok48_parts.2.2.2.1
  simp only [iOK48, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.any_eq_true,
    List.contains_iff_mem, Bool.or_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩ := h
  refine ⟨h1, h2, h3, fun c hc => ?_, fun w hw hO => ?_, fun c hc => ?_, h7, fun c hc => ?_, h9,
    h10, h11, h12, h13⟩
  · obtain ⟨w, hw, he⟩ := h4 c hc
    exact ⟨w, hw, he⟩
  · rcases h5 w hw with h' | h'
    · exact absurd hO (by rw [h']; exact Bool.false_ne_true)
    · exact h'
  · obtain ⟨w, hw, he1, he2⟩ := h6 c hc
    exact ⟨w, hw, he1, he2⟩
  · obtain ⟨X, hX, he⟩ := h8 c hc
    exact ⟨X, hX, he⟩

theorem omList_xor_one : ∀ c ∈ omList, c ^^^ 1 ∈ omList := by decide

theorem omList_lt : ∀ c ∈ omList, c < 128 := by decide

theorem mem_c3List {X : Array ℕ} :
    X ∈ c3List () ↔ ∃ A ∈ s48 (), ∃ l < 64, mk7 l A = X := by
  simp only [c3List, List.mem_flatMap, List.mem_map, List.mem_range]

@[expose] def S0 : Set V12 := {v | v + vecOf q0c ∈ W1}

theorem codeOf_add_q0c (v : V12) : codeOf (v + vecOf q0c) = codeOf v ^^^ q0c := by
  have h1 : vecOf (codeOf v ^^^ q0c) = v + vecOf q0c := by rw [vecOf_xor, vecOf_codeOf]
  rw [← h1, codeOf_vecOf (Nat.xor_lt_two_pow (n := 12) (codeOf_lt v) (by decide))]

theorem setOfMask_s0Mask : setOfMask (s0Mask ()) = S0 := by
  ext v
  rw [mem_setOfMask, s0Mask, testBit_maskOf]
  simp only [S0, Set.mem_setOf_eq, List.mem_map]
  rw [mem_W1_iff, codeOf_add_q0c]
  constructor
  · rintro ⟨w, hw, he⟩
    rw [← he, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
    exact hw
  · intro h
    exact ⟨codeOf v ^^^ q0c, h, by rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]⟩

theorem isMask_s0Mask : IsMask (s0Mask ()) := isMask_maskOf (by decide)

theorem image_S0_eq_iff {U : V12 ≃ₗ[ZMod 2] V12} (hU : U '' W1 = W1) :
    U '' S0 = S0 ↔ U (vecOf q0c) + vecOf q0c ∈ W1 := by
  have hmem : ∀ v, v ∈ W1 ↔ U v ∈ W1 := fun v => by
    constructor
    · intro hv
      rw [← hU]
      exact Set.mem_image_of_mem _ hv
    · intro hv
      rw [← hU] at hv
      obtain ⟨w, hw, hwv⟩ := hv
      rwa [← U.injective hwv]
  have himg : ∀ u, u ∈ U '' S0 ↔ u + U (vecOf q0c) ∈ W1 := fun u => by
    constructor
    · rintro ⟨v, hv, rfl⟩
      rw [← map_add]
      exact (hmem _).mp hv
    · intro hu
      refine ⟨U.symm u, ?_, U.apply_symm_apply u⟩
      show U.symm u + vecOf q0c ∈ W1
      rw [hmem, map_add, U.apply_symm_apply]
      exact hu
  constructor
  · intro h
    have : U (vecOf q0c) ∈ U '' S0 := ⟨vecOf q0c, by
      show vecOf q0c + vecOf q0c ∈ W1
      rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]
      exact zero_mem_W1, rfl⟩
    rw [h] at this
    exact this
  · intro h
    ext u
    rw [himg]
    show u + U (vecOf q0c) ∈ W1 ↔ u + vecOf q0c ∈ W1
    constructor
    · intro hu
      have := add_mem_W1 hu h
      rwa [add_assoc, ← add_assoc (U _), CharTwo.add_self_eq_zero, zero_add] at this
    · intro hu
      have := add_mem_W1 hu h
      rwa [add_comm (U _) (vecOf q0c), ← add_assoc, add_assoc u, CharTwo.add_self_eq_zero,
        add_zero] at this

theorem exists_of_mem_tOrbit {m : ℕ} (hm : m ∈ tOrbit ()) :
    ∃ U ∈ genGrp (g13Gens ()), setOfMask m = U '' S0 := by
  unfold tOrbit at hm
  refine bfsClosure_inv _ _ (P := fun m => ∃ U ∈ genGrp (g13Gens ()), setOfMask m = U '' S0) ?_
    _ _ _ _ ?_ (by simp) m hm
  · intro f hf m ⟨U, hU, hmU⟩
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hf
    obtain ⟨hgok, -, h1, h2⟩ := gensOK_g13 g hg
    refine ⟨eqvOf g (invR g) h1 h2 * U, mul_mem (gen_mem gensOK_g13 hg) hU, ?_⟩
    rw [setOfMask_imgMask (okRows_lt hgok), hmU]
    exact image_mul_eq (fun v => eqvOf_apply g (invR g) h1 h2 v) S0
  · simp only [List.mem_singleton, forall_eq]
    exact ⟨1, one_mem _, by rw [setOfMask_s0Mask]; simp⟩

theorem isMask_of_mem_tOrbit {m : ℕ} (hm : m ∈ tOrbit ()) :
    IsMask m := by
  unfold tOrbit at hm
  refine bfsClosure_inv _ _ (P := IsMask) ?_ _ _ _ _ ?_ (by simp) m hm
  · intro f hf m _
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hf
    exact isMask_imgMask (okRows_lt (gensOK_g13 g hg).1) m
  · simp only [List.mem_singleton, forall_eq]
    exact isMask_s0Mask

theorem gensOK_stab48 : GensOK (stabGens48 ()) :=
  gensOK_of_gensOKb stabOK48_spec.1

theorem card_stab48 : Nat.card (genGrp (stabGens48 ())) = 768 := by
  obtain ⟨-, -, hid, hc, hn, -⟩ := stabOK48_spec
  rw [card_genGrp (enumGrp_sound gensOK_stab48) hid hc, hn]

theorem stab48_le_g13 :
    genGrp (stabGens48 ()) ≤ g13Grp := by
  refine genGrp_le_of_rep fun g hg => ?_
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hg
  have hlen : (g13Gens ()).length = 2 := by simp [g13Gens, g13Words]
  have hw2 : ∀ w ∈ stabWords48, ∀ i ∈ w, i < 2 := by decide
  have hwl : ∀ i ∈ w, i < (g13Gens ()).length := fun i hi => hlen ▸ hw2 w hw i hi
  obtain ⟨hok, U, hU, hUx⟩ := rep_word gensOK_g13 w hwl
  exact ⟨hok, U, g13Gens_le_g13Grp hU, hUx⟩

theorem stab48_fix {U : V12 ≃ₗ[ZMod 2] V12}
    (hU : U ∈ genGrp (stabGens48 ())) : U '' S0 = S0 := by
  have hW : ∀ V ∈ genGrp (stabGens48 ()), V '' W1 = W1 := fun V hV =>
    (mem_g13Grp.mp (stab48_le_g13 hV)).2
  let K : Subgroup (V12 ≃ₗ[ZMod 2] V12) :=
    { carrier := {V | V '' S0 = S0}
      mul_mem' := fun {a b} ha hb => by
        change ⇑(a * b) '' S0 = S0
        rw [show ⇑(a * b) = ⇑a ∘ ⇑b from rfl, Set.image_comp]
        rw [show (⇑b '' S0) = S0 from hb, show (⇑a '' S0) = S0 from ha]
      one_mem' := by change ⇑(1 : V12 ≃ₗ[ZMod 2] V12) '' S0 = S0; simp
      inv_mem' := fun {a} ha => by
        change ⇑a⁻¹ '' S0 = S0
        have ha' : ⇑a '' S0 = S0 := ha
        conv_lhs => rw [← ha']
        rw [← Set.image_comp]
        have : ⇑a⁻¹ ∘ ⇑a = id := funext fun x => by simp
        rw [this, Set.image_id] }
  have hle : genGrp (stabGens48 ()) ≤ K := by
    refine (Subgroup.closure_le K).2 ?_
    rintro l ⟨r, hr, hl⟩
    have hrS := (gensOK_stab48 r hr)
    have hlr : l = eqvOf r (invR r) hrS.2.2.1 hrS.2.2.2 :=
      LinearEquiv.ext fun x => (hl x).trans (eqvOf_apply r (invR r) _ _ x).symm
    have hlmem : l ∈ genGrp (stabGens48 ()) := hlr ▸ gen_mem gensOK_stab48 hr
    show l '' S0 = S0
    refine (image_S0_eq_iff (hW l hlmem)).mpr ?_
    have h1 := stabOK48_spec.2.1 r hr
    rw [hl, ← vecOf_appN, ← vecOf_xor]
    exact (vecOf_mem_W1 (by
      have : appN r q0c < 4096 := appN_lt (okRows_spec hrS.1).2 _
      exact Nat.xor_lt_two_pow (n := 12) this (by decide))).mpr h1
  exact hle hU

theorem mem_stab48
    (hcard : Nat.card g13Grp = 34560) {U : V12 ≃ₗ[ZMod 2] V12} (hU : U ∈ g13Grp)
    (hfix : U (vecOf q0c) + vecOf q0c ∈ W1) : U ∈ genGrp (stabGens48 ()) := by
  set St := MulAction.stabilizer ↥g13Grp S0
  have horb : 45 ≤ (MulAction.orbit ↥g13Grp S0).ncard := by
    have hsub : setOfMask '' {m | m ∈ tOrbit ()} ⊆ MulAction.orbit ↥g13Grp S0 := by
      rintro _ ⟨m, hm, rfl⟩
      obtain ⟨V, hV, hmV⟩ := exists_of_mem_tOrbit hm
      exact ⟨⟨V, g13Gens_le_g13Grp hV⟩, by rw [hmV]; rfl⟩
    have hinj : Set.InjOn setOfMask ((tOrbit ()).toFinset : Set ℕ) := fun m hm m' hm' he =>
      eq_of_setOfMask_eq (isMask_of_mem_tOrbit (by simpa using hm))
        (isMask_of_mem_tOrbit (by simpa using hm')) he
    have e : {m | m ∈ tOrbit ()} = ((tOrbit ()).toFinset : Set ℕ) := by
      ext m
      simp
    have h45 : (setOfMask '' {m | m ∈ tOrbit ()}).ncard = 45 := by
      rw [e, hinj.ncard_image, Set.ncard_coe_finset, List.card_toFinset,
        stabOK48_spec.2.2.2.2.2]
    calc 45 = _ := h45.symm
      _ ≤ _ := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h1 := Subgroup.card_mul_index St
  rw [MulAction.index_stabilizer, hcard] at h1
  have hSt : Nat.card St ≤ 768 := by
    by_contra hlt
    push Not at hlt
    have : 769 * 45 ≤ Nat.card St * (MulAction.orbit ↥g13Grp S0).ncard :=
      Nat.mul_le_mul hlt horb
    omega
  have hle : genGrp (stabGens48 ()) ≤ St.map g13Grp.subtype := by
    intro V hV
    exact ⟨⟨V, stab48_le_g13 hV⟩, stab48_fix hV, rfl⟩
  have heq : genGrp (stabGens48 ()) = St.map g13Grp.subtype :=
    Subgroup.eq_of_le_of_card_ge hle (by
      rw [Subgroup.card_map_of_injective g13Grp.subtype_injective, card_stab48]
      exact hSt)
  rw [heq]
  exact ⟨⟨U, hU⟩, (image_S0_eq_iff (mem_g13Grp.mp hU).2).mpr hfix, rfl⟩

end CFSG.Quasithin.H13.AS91.Two
