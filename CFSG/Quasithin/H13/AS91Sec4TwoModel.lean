module

public import CFSG.GF2Type.Smith1979.IdxFourModelEnumGen
public import Certificates.Certificate89401
public import CFSG.GF2Type.Smith1979.IdxFourModelOrbitBase
public import Mathlib.Data.Rat.Floor

public section

namespace CFSG.Quasithin.H13.AS91.Two

open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA
open CFSG.GF2Type.Smith1979.GammaU.Viol CFSG.GF2Type.Smith1979.GammaU.Enum
open CFSG.GF2Type.Smith1979.IdxFour CFSG.GF2Type.Smith1979.IdxFour.Orb

theorem invPairs42_ok : ∀ p ∈ invPairs42, p.1.size = 12 ∧ (∀ x ∈ p.1.toList, x < 4096) ∧
    p.2.size = 12 ∧ (∀ x ∈ p.2.toList, x < 4096) ∧ mulR p.1 p.2 = idR ∧ mulR p.2 p.1 = idR := by
  decide +kernel

theorem gensOK_gamGens : GensOK gamGens :=
  gensOK_of_pairs invPairs42 invPairs42_ok (by decide +kernel)

theorem gensOK_gamGensI : GensOK gamGensI :=
  gensOK_of_pairs invPairs42 invPairs42_ok (by decide +kernel)

theorem gensOK_nGensI : GensOK nGensI :=
  gensOK_of_pairs invPairs42 invPairs42_ok (by decide +kernel)

theorem gensOK_s : GensOK [sRows] :=
  gensOK_of_pairs invPairs42 invPairs42_ok (by decide +kernel)

abbrev gamGrp : Subgroup (V12 ≃ₗ[ZMod 2] V12) := genGrp gamGens

abbrev nGrp : Subgroup (V12 ≃ₗ[ZMod 2] V12) := genGrp nGensI

theorem rep_mono {N N' : Subgroup (V12 ≃ₗ[ZMod 2] V12)} (h : N ≤ N') {x : Array ℕ}
    (hx : Rep N x) : Rep N' x := by
  obtain ⟨hok, U, hU, hUx⟩ := hx
  exact ⟨hok, U, h hU, hUx⟩

theorem rep_invR {gs : List (Array ℕ)} (hgs : GensOK gs) {g : Array ℕ} (hg : g ∈ gs) :
    Rep (genGrp gs) (invR g) :=
  ⟨(hgs g hg).2.1, (eqvOf g (invR g) (hgs g hg).2.2.1 (hgs g hg).2.2.2)⁻¹,
    inv_mem (gen_mem hgs hg), fun v => eqvOf_inv_apply _ _ _ _ v⟩

theorem gamGrp_le_nGrp : gamGrp ≤ nGrp :=
  genGrp_le_of_rep fun g hg => rep_gen gensOK_nGensI (by
    simp only [gamGens, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl <;> simp [nGensI])

theorem genGrp_gamGensI_le : genGrp gamGensI ≤ gamGrp := by
  refine genGrp_le_of_rep fun g hg => ?_
  have hm1 : m1Rows ∈ gamGens := by simp [gamGens]
  have hm2 : m2Rows ∈ gamGens := by simp [gamGens]
  have hinv : invR m2Rows = m2InvRows := invR_eq (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  simp only [gamGensI, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact rep_gen gensOK_gamGens hm1
  · exact rep_gen gensOK_gamGens hm2
  · exact rep_gen gensOK_gamGens hm1
  · rw [← hinv]
    exact rep_invR gensOK_gamGens hm2

theorem sRows_mul_inv : mulR sRows sInvRows = idR := by decide +kernel

theorem sInvRows_mul : mulR sInvRows sRows = idR := by decide +kernel

@[expose] noncomputable def sE : V12 ≃ₗ[ZMod 2] V12 :=
  eqvOf sRows sInvRows sRows_mul_inv sInvRows_mul

theorem sE_apply (v : V12) : sE v = linOfRows sRows v := rfl

theorem sE_inv_apply (v : V12) : sE⁻¹ v = linOfRows sInvRows v := rfl

theorem sE_mem : sE ∈ nGrp := Subgroup.subset_closure ⟨sRows, by simp [nGensI], fun _ => rfl⟩

theorem sE_conj_mem {x : V12 ≃ₗ[ZMod 2] V12} (hx : x ∈ gamGrp) : sE * x * sE⁻¹ ∈ gamGrp := by
  have hinv : invR sRows = sInvRows := invR_eq sRows_mul_inv sInvRows_mul (by decide +kernel)
    (by decide +kernel)
  have hw1 : mulR sRows (mulR m1Rows sInvRows) = wordRows gamGensI conjWord1 := by decide +kernel
  have hw2 : mulR sRows (mulR m2Rows sInvRows) = wordRows gamGensI conjWord2 := by decide +kernel
  have key := conj_mem_of_gens gensOK_s (gsH := gamGens) (fun g hg e he => by
    simp only [List.mem_singleton] at hg
    subst hg
    rw [hinv]
    simp only [gamGens, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · rw [hw1]
      exact rep_mono genGrp_gamGensI_le (rep_word gensOK_gamGensI _ (by decide))
    · rw [hw2]
      exact rep_mono genGrp_gamGensI_le (rep_word gensOK_gamGensI _ (by decide)))
  have hs : sE ∈ genGrp [sRows] := Subgroup.subset_closure ⟨sRows, by simp, fun _ => rfl⟩
  exact key sE hs x hx

theorem sE_theta0 (v : V12) : sE (theta0 v) = theta0 (theta0 (sE v)) := by
  have h : mulR sRows omegaRows = mulR omegaRows (mulR omegaRows sRows) := by decide +kernel
  have := congrArg (fun r => linOfRows r v) h
  simp only [linOfRows_mulR, linOfRows_omegaRows] at this
  exact this

@[expose] def InO1 (v : V12) : Prop := inO1b (codeOf v) = true

@[expose] def InO2 (v : V12) : Prop := inO2b (codeOf v) = true

theorem orbitOK42_spec :
    orbitSetOK gamGens 3 inO1b = true ∧ orbitSetOK gamGens 5 inO2b = true ∧
      orbitSetOK gamGens 1 q0b = true ∧
      (∀ n < 4096, ∀ g ∈ nGensI, (inO1b n = true → inO1b (appN g n) = true) ∧
        (inO2b n = true → inO2b (appN g n) = true)) ∧
      (∀ n < 4096, ([q0b n, inO1b n, inO2b n].filter id).length = if n = 0 then 0 else 1) ∧
      ((List.range 4096).filter inO1b).length = 693 ∧
      ((List.range 4096).filter inO2b).length = 1386 := by
  have h := Certificates.certificate89401
  simp only [orbitOK42, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  refine ⟨h1, h2, h3, fun n hn g hg => ?_, fun n hn => ?_, h6, h7⟩
  · have := List.all_eq_true.1 (List.all_eq_true.1 h4 n (List.mem_range.2 hn)) g hg
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at this
    obtain ⟨ha, hb⟩ := this
    refine ⟨fun hP => ?_, fun hP => ?_⟩
    · rcases ha with ha | ha
      · rw [hP] at ha; exact absurd ha (by simp)
      · exact ha
    · rcases hb with hb | hb
      · rw [hP] at hb; exact absurd hb (by simp)
      · exact hb
  · have := List.all_eq_true.1 h5 n (List.mem_range.2 hn)
    split_ifs with h0
    · subst h0
      simpa using this
    · simpa [h0] using this

theorem exists_of_inO1 {v : V12} (hv : InO1 v) :
    ∃ U ∈ gamGrp, U (vecOf 3) = v := by
  have hs := orbitSetOK_spec orbitOK42_spec.1
  refine exists_of_reach gensOK_gamGens (fun n hn hP => (hs.2 n hn hP).1) ?_ hv
  rw [codeOf_vecOf (by norm_num)]
  exact hs.1

theorem exists_of_inO2 {v : V12} (hv : InO2 v) :
    ∃ U ∈ gamGrp, U (vecOf 5) = v := by
  have hs := orbitSetOK_spec orbitOK42_spec.2.1
  refine exists_of_reach gensOK_gamGens (fun n hn hP => (hs.2 n hn hP).1) ?_ hv
  rw [codeOf_vecOf (by norm_num)]
  exact hs.1

theorem exists_of_q0 {v : V12} (hv : q0b (codeOf v) = true) :
    ∃ U ∈ gamGrp, U (vecOf 1) = v := by
  have hs := orbitSetOK_spec orbitOK42_spec.2.2.1
  refine exists_of_reach gensOK_gamGens (fun n hn hP => (hs.2 n hn hP).1) ?_ hv
  rw [codeOf_vecOf (by norm_num)]
  exact hs.1

theorem inO1_invariant {U : V12 ≃ₗ[ZMod 2] V12} (hU : U ∈ nGrp)
    {v : V12} (hv : InO1 v) : InO1 (U v) := by
  have := invariant_of_gens gensOK_nGensI (P := inO1b)
    (fun n hn hP g hg => (orbitOK42_spec.2.2.2.1 n hn g hg).1 hP) U hU _ (codeOf_lt v) hv
  rwa [vecOf_codeOf] at this

theorem inO2_invariant {U : V12 ≃ₗ[ZMod 2] V12} (hU : U ∈ nGrp)
    {v : V12} (hv : InO2 v) : InO2 (U v) := by
  have := invariant_of_gens gensOK_nGensI (P := inO2b)
    (fun n hn hP g hg => (orbitOK42_spec.2.2.2.1 n hn g hg).2 hP) U hU _ (codeOf_lt v) hv
  rwa [vecOf_codeOf] at this

theorem code_cases {n : ℕ} (hn : n < 4096) :
    (n = 0 ∧ q0b n = false ∧ inO1b n = false ∧ inO2b n = false) ∨
      (n ≠ 0 ∧ q0b n = true ∧ inO1b n = false ∧ inO2b n = false) ∨
      (n ≠ 0 ∧ q0b n = false ∧ inO1b n = true ∧ inO2b n = false) ∨
      (n ≠ 0 ∧ q0b n = false ∧ inO1b n = false ∧ inO2b n = true) := by
  have h := orbitOK42_spec.2.2.2.2.1 n hn
  by_cases h0 : n = 0
  · subst h0
    simp only [↓reduceIte] at h
    left
    cases h1 : q0b 0 <;> cases h2 : inO1b 0 <;> cases h3 : inO2b 0 <;> simp_all
  · simp only [h0, ↓reduceIte] at h
    right
    cases h1 : q0b n <;> cases h2 : inO1b n <;> cases h3 : inO2b n <;> simp_all

theorem q0b_eq_false_iff {v : V12} : q0b (codeOf v) = false ↔ q0 v = 0 := by
  have := q0_vecOf (codeOf v)
  rw [vecOf_codeOf] at this
  rw [this]
  cases q0b (codeOf v) <;> simp

theorem singular_cases42 {v : V12} (hv : v ≠ 0) (hq : q0 v = 0) :
    InO1 v ∨ InO2 v := by
  have hq' : q0b (codeOf v) = false := q0b_eq_false_iff.2 hq
  have hn0 : codeOf v ≠ 0 := fun h => hv (by rw [← vecOf_codeOf v, h, vecOf_zero])
  rcases code_cases (codeOf_lt v) with h | h | h | h
  · exact absurd h.1 hn0
  · rw [hq'] at h; exact absurd h.2.1 (by simp)
  · exact Or.inl h.2.2.1
  · exact Or.inr h.2.2.2

theorem inO2_singular {v : V12} (hv : InO2 v) :
    v ≠ 0 ∧ q0 v = 0 ∧ ¬ InO1 v := by
  rcases code_cases (codeOf_lt v) with h | h | h | h
  · rw [InO2, h.2.2.2] at hv; exact absurd hv (by simp)
  · rw [InO2, h.2.2.2] at hv; exact absurd hv (by simp)
  · rw [InO2, h.2.2.2] at hv; exact absurd hv (by simp)
  · refine ⟨fun h0 => h.1 (by rw [h0]; simp [codeOf]), q0b_eq_false_iff.1 h.2.1, ?_⟩
    rw [InO1, h.2.2.1]
    simp

theorem inO1_three : InO1 (vecOf 3) := by
  rw [InO1, codeOf_vecOf (by norm_num)]
  decide +kernel

theorem inO2_five : InO2 (vecOf 5) := by
  rw [InO2, codeOf_vecOf (by norm_num)]
  decide +kernel

theorem ncard_inO1 : {v : V12 | InO1 v}.ncard = 693 := by
  rw [← Nat.card_coe_set_eq, ← orbitOK42_spec.2.2.2.2.2.1]
  refine card_of_codes (P := fun v => v ∈ {v : V12 | InO1 v}) (List.nodup_range.filter _)
    (fun n hn => List.mem_range.1 (List.mem_of_mem_filter hn)) (fun y => ?_)
  simp only [Set.mem_setOf_eq, List.mem_filter, List.mem_range, InO1, decide_eq_true_eq]
  exact ⟨fun h => ⟨codeOf_lt y, h⟩, fun h => h.2⟩

theorem ncard_inO2 : {v : V12 | InO2 v}.ncard = 1386 := by
  rw [← Nat.card_coe_set_eq, ← orbitOK42_spec.2.2.2.2.2.2]
  refine card_of_codes (P := fun v => v ∈ {v : V12 | InO2 v}) (List.nodup_range.filter _)
    (fun n hn => List.mem_range.1 (List.mem_of_mem_filter hn)) (fun y => ?_)
  simp only [Set.mem_setOf_eq, List.mem_filter, List.mem_range, InO2, decide_eq_true_eq]
  exact ⟨fun h => ⟨codeOf_lt y, h⟩, fun h => h.2⟩

@[expose] def fval (a b c : ZMod 2) (n : ℕ) : ZMod 2 :=
  (if q0b n then a else 0) + (if inO1b n then b else 0) + (if inO2b n then c else 0)

theorem form_b : ∀ a b c : ZMod 2,
    fval a b c (2552 ^^^ 1047 ^^^ 3039) + (fval a b c 2552 + fval a b c 1047 + fval a b c 3039) =
      fval a b c (2552 ^^^ 1047) + fval a b c (1047 ^^^ 3039) + fval a b c (3039 ^^^ 2552) →
      b = 0 := by
  decide +kernel

theorem form_c : ∀ a b c : ZMod 2,
    fval a b c (3179 ^^^ 3864 ^^^ 1021) + (fval a b c 3179 + fval a b c 3864 + fval a b c 1021) =
      fval a b c (3179 ^^^ 3864) + fval a b c (3864 ^^^ 1021) + fval a b c (1021 ^^^ 3179) →
      c = 0 := by
  decide +kernel

theorem eq_q0_of_invariant (f : V12 → ZMod 2)
    (hf : ∀ x y z, f (x + y + z) + (f x + f y + f z) = f (x + y) + f (y + z) + f (z + x))
    (h0 : f 0 = 0) (hinv : ∀ U ∈ gamGrp, ∀ x, f (U x) = f x) (hne : ∃ x, f x ≠ 0) :
    ∀ x, f x = q0 x := by
  set a := f (vecOf 1)
  set b := f (vecOf 3)
  set c := f (vecOf 5)
  have hval : ∀ n < 4096, f (vecOf n) = fval a b c n := by
    intro n hn
    rcases code_cases hn with h | h | h | h
    · obtain ⟨rfl, h1, h2, h3⟩ := h
      rw [vecOf_zero, h0]
      simp [fval, h1, h2, h3]
    · obtain ⟨U, hU, hUv⟩ := exists_of_q0 (v := vecOf n) (by rw [codeOf_vecOf hn]; exact h.2.1)
      rw [← hUv, hinv U hU]
      simp [fval, h.2.1, h.2.2.1, h.2.2.2, a]
    · obtain ⟨U, hU, hUv⟩ := exists_of_inO1 (v := vecOf n)
        (by rw [InO1, codeOf_vecOf hn]; exact h.2.2.1)
      rw [← hUv, hinv U hU]
      simp [fval, h.2.1, h.2.2.1, h.2.2.2, b]
    · obtain ⟨U, hU, hUv⟩ := exists_of_inO2 (v := vecOf n)
        (by rw [InO2, codeOf_vecOf hn]; exact h.2.2.2)
      rw [← hUv, hinv U hU]
      simp [fval, h.2.1, h.2.2.1, h.2.2.2, c]
  have htrip : ∀ x y z : ℕ, x < 4096 → y < 4096 → z < 4096 →
      fval a b c (x ^^^ y ^^^ z) + (fval a b c x + fval a b c y + fval a b c z) =
        fval a b c (x ^^^ y) + fval a b c (y ^^^ z) + fval a b c (z ^^^ x) := by
    intro x y z hx hy hz
    have hxy : x ^^^ y < 4096 := Nat.xor_lt_two_pow (n := 12) hx hy
    have hyz : y ^^^ z < 4096 := Nat.xor_lt_two_pow (n := 12) hy hz
    have hzx : z ^^^ x < 4096 := Nat.xor_lt_two_pow (n := 12) hz hx
    have hxyz : x ^^^ y ^^^ z < 4096 := Nat.xor_lt_two_pow (n := 12) hxy hz
    have := hf (vecOf x) (vecOf y) (vecOf z)
    rw [← vecOf_xor, ← vecOf_xor, ← vecOf_xor, ← vecOf_xor] at this
    rwa [hval _ hxyz, hval _ hx, hval _ hy, hval _ hz, hval _ hxy, hval _ hyz, hval _ hzx] at this
  have hb : b = 0 := form_b a b c (htrip _ _ _ (by norm_num) (by norm_num) (by norm_num))
  have hc : c = 0 := form_c a b c (htrip _ _ _ (by norm_num) (by norm_num) (by norm_num))
  have ha : a = 1 := by
    obtain ⟨x, hx⟩ := hne
    rw [← vecOf_codeOf x, hval _ (codeOf_lt x), fval, hb, hc] at hx
    have h2 : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
    refine h2 a fun ha0 => hx ?_
    simp [ha0]
  intro x
  rw [← vecOf_codeOf x, hval _ (codeOf_lt x), q0_vecOf, fval, ha, hb, hc]
  simp

@[expose] def iterSqR (k : ℕ) (r : Array ℕ) : Array ℕ :=
  (List.range k).foldl (fun y _ => mulR y y) r

theorem iterSqR_succ (k : ℕ) (r : Array ℕ) :
    iterSqR (k + 1) r = mulR (iterSqR k r) (iterSqR k r) := by
  rw [iterSqR, List.range_succ, List.foldl_append]
  rfl

theorem pow_two_pow_apply {U : V12 ≃ₗ[ZMod 2] V12} {r : Array ℕ} (hU : ∀ v, U v = linOfRows r v)
    (k : ℕ) (v : V12) : (U ^ (2 ^ k)) v = linOfRows (iterSqR k r) v := by
  induction k generalizing v with
  | zero => simpa [iterSqR] using hU v
  | succ k ih =>
    rw [iterSqR_succ, linOfRows_mulR, ← ih, ← ih, pow_succ, pow_mul, sq, LinearEquiv.mul_apply]

theorem pow256R_eq (r : Array ℕ) : pow256R r = iterSqR 8 r := rfl

theorem okRows_iterSqR {r : Array ℕ} (h : okRows r = true) : ∀ k, okRows (iterSqR k r) = true
  | 0 => by simpa [iterSqR] using h
  | k + 1 => by
    rw [iterSqR_succ]
    exact okRows_mulR (okRows_iterSqR h k) (okRows_iterSqR h k)

theorem okRows_pow256R {r : Array ℕ} (h : okRows r = true) : okRows (pow256R r) = true :=
  okRows_iterSqR h 8

theorem pow256_apply {U : V12 ≃ₗ[ZMod 2] V12} {r : Array ℕ} (hU : ∀ v, U v = linOfRows r v)
    (v : V12) : (U ^ 256) v = linOfRows (pow256R r) v := by
  rw [pow256R_eq, ← pow_two_pow_apply hU 8 v]
  norm_num

theorem gensOK_of_gensOKb {gs : List (Array ℕ)} (h : gensOKb gs = true) : GensOK gs := by
  intro g hg
  have := List.all_eq_true.1 h g hg
  simp only [Bool.and_eq_true, beq_iff_eq] at this
  exact ⟨this.1.1.1, this.1.1.2, this.1.2, this.2⟩

theorem rep_of_contains {gs : List (Array ℕ)} (hgs : GensOK gs) {x : Array ℕ}
    (h : (Std.HashSet.ofList (enumGrp gs)).contains x = true) : Rep (genGrp gs) x := by
  rw [Std.HashSet.contains_ofList, List.contains_iff_mem] at h
  exact enumGrp_sound hgs x h

theorem stabOK_spec {v : ℕ} {gs ps : List (Array ℕ)} {W : List (Array ℕ × Array ℕ)} {nS nP : ℕ}
    (h : stabOK v gs ps W nS nP = true) :
    GensOK gs ∧ (∀ U ∈ genGrp gs, U (vecOf v) = vecOf v) ∧ Nat.card (genGrp gs) = nS ∧
      Nat.card (genGrp ps) = nP ∧ genGrp ps ≤ genGrp gs ∧
      (∀ t ∈ genGrp gs, ∀ p ∈ genGrp ps, t * p * t⁻¹ ∈ genGrp ps) ∧
      ∀ x ∈ genGrp gs, x ^ 256 = 1 → x ∉ genGrp ps →
        ∃ t ∈ genGrp gs, (x * (t * x * t⁻¹)) ^ 256 ≠ 1 := by
  simp only [stabOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hg, hp⟩, hfix⟩, hidX⟩, hcX⟩, hnX⟩, hidP⟩, hcP⟩, hnP⟩, hPX⟩, hnorm⟩,
    hW⟩, hwit⟩ := h
  have hgs := gensOK_of_gensOKb hg
  have hps := gensOK_of_gensOKb hp
  have hidX' : idR ∈ enumGrp gs := by simpa using hidX
  have hidP' : idR ∈ enumGrp ps := by simpa using hidP
  refine ⟨hgs, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro U hU
    have hU' : U ∈ Submonoid.closure (GenSet gs) := by
      rw [← Subgroup.closure_toSubmonoid_of_finite]
      exact hU
    refine Submonoid.closure_induction (motive := fun U _ => U (vecOf v) = vecOf v) ?_ ?_ ?_ hU'
    · rintro x ⟨r, hr, hx⟩
      rw [hx, ← vecOf_appN]
      have := List.all_eq_true.1 hfix r hr
      simp only [beq_iff_eq] at this
      rw [this]
    · rfl
    · intro x y _ _ hx hy
      rw [LinearEquiv.mul_apply, hy, hx]
  · rw [card_genGrp (enumGrp_sound hgs) hidX' hcX, hnX]
  · rw [card_genGrp (enumGrp_sound hps) hidP' hcP, hnP]
  · exact genGrp_le_of_rep fun p hp' => rep_of_contains hgs (List.all_eq_true.1 hPX p hp')
  · exact conj_mem_of_gens hgs fun g hg' e he =>
      rep_of_contains hps (List.all_eq_true.1 (List.all_eq_true.1 hnorm g hg') e he)
  · intro x hx hx256 hxP
    obtain ⟨r, hrX, hxr⟩ := complete hidX' hcX x hx
    have hr256 : pow256R r = idR := by
      refine rows_eq (okRows_spec ?_).1 (by simp [idR]) (okRows_spec ?_).2 (by decide) fun u => ?_
      · exact okRows_pow256R (enumGrp_sound hgs r hrX).1
      · exact okRows_pow256R (enumGrp_sound hgs r hrX).1
      · rw [← pow256_apply hxr, hx256, linOfRows_idR]
        rfl
    have := List.all_eq_true.1 hwit r hrX
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, List.any_eq_true] at this
    rcases this with (h1 | h1) | ⟨w, hwW, hw⟩
    · exact absurd hr256 h1
    · obtain ⟨-, U, hU, hUr⟩ := rep_of_contains hps h1
      exact absurd (show x ∈ genGrp ps by
        rw [show x = U from LinearEquiv.ext fun u => (hxr u).trans (hUr u).symm]
        exact hU) hxP
    · have hw' := List.all_eq_true.1 hW w hwW
      simp only [Bool.and_eq_true, beq_iff_eq] at hw'
      obtain ⟨⟨⟨hw1, hw2ok⟩, hw12⟩, hw21⟩ := hw'
      obtain ⟨-, T, hT, hTw⟩ := rep_of_contains hgs hw1
      refine ⟨T, hT, fun h256 => hw ?_⟩
      have hTinv : ∀ u, T⁻¹ u = linOfRows w.2 u := fun u => by
        change T.symm u = _
        rw [LinearEquiv.symm_apply_eq, hTw, ← linOfRows_mulR, hw12, linOfRows_idR]
      have hprod : ∀ u, (x * (T * x * T⁻¹)) u = linOfRows (mulR r (mulR w.1 (mulR r w.2))) u :=
        fun u => by
          simp only [LinearEquiv.mul_apply, hxr, hTw, hTinv, linOfRows_mulR]
      refine rows_eq (okRows_spec ?_).1 (by simp [idR]) (okRows_spec ?_).2 (by decide) fun u => ?_
      · exact okRows_pow256R (okRows_mulR (enumGrp_sound hgs r hrX).1
          (okRows_mulR (enumGrp_sound hgs w.1 (by
            rw [Std.HashSet.contains_ofList, List.contains_iff_mem] at hw1; exact hw1)).1
            (okRows_mulR (enumGrp_sound hgs r hrX).1 hw2ok)))
      · exact okRows_pow256R (okRows_mulR (enumGrp_sound hgs r hrX).1
          (okRows_mulR (enumGrp_sound hgs w.1 (by
            rw [Std.HashSet.contains_ofList, List.contains_iff_mem] at hw1; exact hw1)).1
            (okRows_mulR (enumGrp_sound hgs r hrX).1 hw2ok)))
      · rw [← pow256_apply hprod, h256, linOfRows_idR]
        rfl

end CFSG.Quasithin.H13.AS91.Two
