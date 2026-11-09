module

public import CFSG.Quasithin.Recognition.Kleidman.ThreeLocalCentralizerAnalysis.BetaModels
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import CFSG.Permutation.FinPackDec
public import CFSG.Permutation.FinPackSignCount

public section

namespace CFSG.Quasithin.Kleidman.ThreeLocal

@[expose] def c0A6 : alternatingGroup (Fin 6) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

namespace BetaA6

open CFSG.Permutation.FinPack Equiv Finset

local notation "A6" => alternatingGroup (Fin 6)

@[expose] noncomputable def cd (x : A6) : ℕ := enc x.1

@[expose] def E6 : ℕ := 5517840

@[expose] def C0 : ℕ := 5513985

theorem hn6 : 6 ≤ 16 := by norm_num

theorem cd_mul (x y : A6) : cd (x * y) = mulK 6 (cd x) (cd y) := enc_mul hn6 x.1 y.1

theorem cd_inv (x : A6) : cd x⁻¹ = invCK 6 (cd x) := enc_inv_invCK hn6 x.1

theorem cd_one : cd 1 = E6 := by
  unfold cd E6
  decide +kernel

theorem cd_c0 : cd c0A6 = C0 := by
  unfold cd C0
  decide +kernel

theorem cd_inj {x y : A6} (h : cd x = cd y) : x = y := Subtype.ext (enc_inj hn6 h)

theorem cd_eq_iff {x y : A6} : x = y ↔ Nat.beq (cd x) (cd y) = true := by
  rw [Nat.beq_eq]
  exact ⟨congrArg cd, cd_inj⟩

theorem evenK_cd (x : A6) : evenK 6 (cd x) = true :=
  (sign_eq_one_iff_evenK hn6 x.1).1 (Perm.mem_alternatingGroup.1 x.2)

theorem forall_cd {Q : ℕ → Bool} (h : walkK 6 (fun c => !evenK 6 c || Q c) 6 0 0 0 = true)
    (x : A6) : Q (cd x) = true := by
  have h1 := walkK_sound h x.1
  change (!evenK 6 (cd x) || Q (cd x)) = true at h1
  rw [evenK_cd, Bool.not_true, Bool.false_or] at h1
  exact h1

theorem exists_cd_eq {d : ℕ} (h : (permValidK 6 d && evenK 6 d) = true) : ∃ x : A6, cd x = d := by
  rw [Bool.and_eq_true] at h
  obtain ⟨σ, rfl⟩ := exists_enc_of_permValidK h.1
  exact ⟨⟨σ, Perm.mem_alternatingGroup.2 ((sign_eq_one_iff_evenK hn6 σ).2 h.2)⟩, rfl⟩

theorem mem_map_cd {x : A6} {L : List A6} : x ∈ L ↔ memK (cd x) (L.map cd) = true := by
  rw [memK_iff, List.mem_map]
  exact ⟨fun h => ⟨x, h, rfl⟩, fun ⟨y, hy, e⟩ => cd_inj e ▸ hy⟩

theorem card_filter_cd (f : ℕ → Bool) :
    (univ.filter fun g : A6 => f (cd g) = true).card =
      cntK 6 (fun c => f c && evenK 6 c) 6 0 0 0 := by
  rw [← card_sign_filter_eq_cntK hn6]
  refine Finset.card_bij (fun g _ => g.1) ?_ ?_ ?_
  · intro g hg
    rw [Finset.mem_filter] at hg ⊢
    exact ⟨Finset.mem_univ _, Perm.mem_alternatingGroup.1 g.2, hg.2⟩
  · intro a _ b _ h
    exact Subtype.ext h
  · intro σ hσ
    rw [Finset.mem_filter] at hσ
    exact ⟨⟨σ, Perm.mem_alternatingGroup.2 hσ.2.1⟩,
      Finset.mem_filter.2 ⟨Finset.mem_univ _, hσ.2.2⟩, rfl⟩

@[expose] noncomputable def kK (C T : ℕ) : List ℕ := [E6, C, T, mulK 6 C T]

@[expose] noncomputable def nK (C T g : ℕ) : Bool :=
  allK (fun v => memK (mulK 6 (mulK 6 g v) (invCK 6 g)) (kK C T)) (kK C T)

@[expose] def tK (a b c s : ℕ) (i : Fin 7) : ℕ := [E6, a, b, c, E6, E6, s].getD i.1 E6

@[expose] noncomputable def wK (a b c s : ℕ) (r : List (Fin 7 × Bool)) : ℕ :=
  r.foldr (fun x acc => mulK 6 (if x.2 then tK a b c s x.1 else invCK 6 (tK a b c s x.1)) acc) E6

theorem kleinSet_map (c t : A6) : (kleinSet c t).map cd = kK (cd c) (cd t) := by
  simp only [kleinSet, kK, List.map_cons, List.map_nil, cd_one, cd_mul]

theorem mem_normSet_iff (c t g : A6) : g ∈ normSet c t ↔ nK (cd c) (cd t) (cd g) = true := by
  simp only [normSet, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [nK, allK_iff, ← kleinSet_map, List.forall_mem_map]
  refine forall_congr' fun v => imp_congr_right fun _ => ?_
  rw [mem_map_cd, cd_mul, cd_mul, cd_inv]

theorem betaTup_cd (a b c s : A6) (i : Fin 7) :
    cd (betaTup a b c s i) = tK (cd a) (cd b) (cd c) (cd s) i := by
  fin_cases i <;> simp [betaTup, tK, cd_one]

theorem evalWord_cd (a b c s : A6) (r : List (Fin 7 × Bool)) :
    cd (evalWord (betaTup a b c s) r) = wK (cd a) (cd b) (cd c) (cd s) r := by
  unfold evalWord wK
  induction r with
  | nil => exact cd_one
  | cons x r ih =>
    rw [List.map_cons, List.prod_cons, cd_mul, ih, List.foldr_cons]
    obtain ⟨i, b⟩ := x
    cases b
    · simp only [Bool.false_eq_true, ite_false, cd_inv, betaTup_cd]
    · simp only [ite_true, betaTup_cd]

theorem rels_iff (a b c s : A6) (R : List (List (Fin 7 × Bool))) :
    (∀ r ∈ R, evalWord (betaTup a b c s) r = 1) ↔
      R.all (fun r => Nat.beq (wK (cd a) (cd b) (cd c) (cd s) r) E6) = true := by
  rw [List.all_eq_true]
  refine forall_congr' fun r => imp_congr_right fun _ => ?_
  rw [cd_eq_iff, evalWord_cd, cd_one]

@[expose] def cenL : List ℕ :=
  [5517840, 4530960, 4534785, 5513985, 5509170, 4522290, 4526115, 5505315]

@[expose] def T1 : ℕ := 5509170

@[expose] def nL1 : List ℕ :=
  [5517840, 4530960, 4534560, 5509920, 5513520, 4526640, 4534785, 5513985, 5517345, 4522785,
    4530225, 5505585, 5517570, 4526850, 4534290, 5505810, 5509170, 4522290, 4530435, 5509635,
    5513235, 4522515, 4526115, 5505315]

@[expose] def T2 : ℕ := 4530960

@[expose] def nL2 : List ℕ :=
  [5517840, 4530960, 3298320, 2311440, 4534785, 5513985, 2315265, 3294465, 5509170, 4522290,
    1070130, 83250, 4526115, 5505315, 87075, 1066275, 3280980, 2294100, 1061460, 74580, 2297925,
    3277125, 78405, 1057605]

@[expose] def conjL : List ℕ :=
  [86850, 148305, 152625, 217665, 275025, 283425, 344625, 1065810, 1070130, 1200960, 1262160,
    1266720, 1331760, 1389120, 1393440, 2118465, 2179920, 2184240, 2314560, 2371920, 2380560,
    2441520, 3162705, 3167265, 3232320, 3293520, 3298320, 3428640, 3481920, 3490320, 4215345,
    4272720, 4281120, 4346160, 4399440, 4411920, 4534560, 5255745, 5260065, 5325360, 5386560,
    5391120, 5456160, 5513520, 5517840]

@[expose] noncomputable def tChk (T : ℕ) (NL : List ℕ) : Bool :=
  (permValidK 6 T && evenK 6 T) &&
  Nat.beq (mulK 6 T T) E6 && Nat.beq (mulK 6 T C0) (mulK 6 C0 T) && !Nat.beq T E6 &&
  !Nat.beq T C0 &&
  Nat.beq (cntK 6 (fun c => memK c NL && evenK 6 c) 6 0 0 0) 24 &&
  allK (fun p => allK (fun q => memK (mulK 6 p q) NL) NL) NL &&
  allK (fun p => memK (invCK 6 p) NL) NL && memK C0 NL &&
  allK (fun p => !Nat.beq (mulK 6 p (mulK 6 p p)) E6 || Nat.beq p E6 ||
    anyK (fun u => Nat.beq (mulK 6 (mulK 6 u p) (invCK 6 u)) (invCK 6 p)) NL) NL &&
  allK (fun p => permValidK 6 p && evenK 6 p) NL

@[expose] noncomputable def pairOK (NL : List ℕ) (x y : ℕ) : Bool :=
  memK x NL && memK y NL &&
    anyK (fun s => a2Rels.all fun r => Nat.beq (wK x y C0 s r) E6) NL

theorem c0_sq : Nat.beq (mulK 6 C0 C0) E6 = true := by
  decide +kernel

theorem c0_ne : Nat.beq C0 E6 = false := by
  decide +kernel

theorem cen_walk : walkK 6 (fun c => !evenK 6 c || (!Nat.beq (mulK 6 c C0) (mulK 6 C0 c) ||
    memK c cenL)) 6 0 0 0 = true := by
  decide +kernel

theorem conj_walk : walkK 6 (fun c => !evenK 6 c || (!Nat.beq (mulK 6 c c) E6 || Nat.beq c E6 ||
    anyK (fun d => (permValidK 6 d && evenK 6 d) &&
      Nat.beq (mulK 6 (mulK 6 d C0) (invCK 6 d)) c) conjL)) 6 0 0 0 = true := by
  decide +kernel

theorem norm1_walk :
    walkK 6 (fun c => !evenK 6 c || (nK C0 T1 c == memK c nL1)) 6 0 0 0 = true := by
  decide +kernel

theorem norm2_walk :
    walkK 6 (fun c => !evenK 6 c || (nK C0 T2 c == memK c nL2)) 6 0 0 0 = true := by
  decide +kernel

theorem t_chk : (tChk T1 nL1 && tChk T2 nL2) = true := by
  decide +kernel

theorem pairs_chk : allK (fun x => allK (fun y =>
    !(d8Rels.all fun r => Nat.beq (wK x y C0 E6 r) E6) || pairOK nL1 x y || pairOK nL2 x y)
      cenL) cenL = true := by
  decide +kernel

theorem normSet_iff_of_walk {T : ℕ} {NL : List ℕ} (t : A6) (ht : cd t = T)
    (hw : walkK 6 (fun c => !evenK 6 c || (nK C0 T c == memK c NL)) 6 0 0 0 = true) (g : A6) :
    g ∈ normSet c0A6 t ↔ memK (cd g) NL = true := by
  have h := forall_cd hw g
  rw [beq_iff_eq] at h
  rw [mem_normSet_iff, cd_c0, ht, h]

theorem exists_t_of_chk {T : ℕ} {NL : List ℕ} (hc : tChk T NL = true)
    (hw : walkK 6 (fun c => !evenK 6 c || (nK C0 T c == memK c NL)) 6 0 0 0 = true)
    (a2 a3 : A6) (hp : pairOK NL (cd a2) (cd a3) = true) :
    ∃ t : A6, t * t = 1 ∧ t * c0A6 = c0A6 * t ∧ t ≠ 1 ∧ t ≠ c0A6 ∧
      (normSet c0A6 t).card = 24 ∧
      (∀ x ∈ normSet c0A6 t, ∀ y ∈ normSet c0A6 t, x * y ∈ normSet c0A6 t) ∧
      (∀ x ∈ normSet c0A6 t, x⁻¹ ∈ normSet c0A6 t) ∧
      a2 ∈ normSet c0A6 t ∧ a3 ∈ normSet c0A6 t ∧ c0A6 ∈ normSet c0A6 t ∧
      (∀ x ∈ normSet c0A6 t, x ^ 3 = 1 → x ≠ 1 → ∃ u ∈ normSet c0A6 t, u * x * u⁻¹ = x⁻¹) ∧
      ∃ s ∈ normSet c0A6 t, ∀ r ∈ a2Rels, evalWord (betaTup a2 a3 c0A6 s) r = 1 := by
  simp only [tChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hTv, hTe⟩, hTT⟩, hTc⟩, hT1⟩, hTc0⟩, hcard⟩, hmul⟩, hinv⟩, hc0⟩, hord⟩, hval⟩ :=
    hc
  obtain ⟨t, ht⟩ := exists_cd_eq (by rw [hTv, hTe]; rfl)
  have hN := normSet_iff_of_walk t ht hw
  have hex : ∀ {P : A6 → Prop} {q : ℕ → Bool}, (∀ g, P g ↔ q (cd g) = true) →
      anyK (fun d => memK d NL && q d) NL = true → ∃ g ∈ normSet c0A6 t, P g := by
    intro P q hPq h
    obtain ⟨d, hd, hq⟩ := anyK_iff.1 h
    rw [Bool.and_eq_true] at hq
    obtain ⟨g, rfl⟩ := exists_cd_eq (allK_iff.1 hval d hd)
    exact ⟨g, (hN g).2 hq.1, (hPq g).2 hq.2⟩
  simp only [pairOK, Bool.and_eq_true] at hp
  obtain ⟨⟨ha2, ha3⟩, hs⟩ := hp
  refine ⟨t, ?_, ?_, ?_, ?_, ?_, ?_, ?_, (hN a2).2 ha2, (hN a3).2 ha3, ?_, ?_, ?_⟩
  · rw [cd_eq_iff, cd_mul, ht, cd_one]
    exact hTT
  · rw [cd_eq_iff, cd_mul, cd_mul, ht, cd_c0]
    exact hTc
  · rw [Ne, cd_eq_iff, ht, cd_one]
    intro h
    rw [h] at hT1
    exact absurd hT1 (by decide)
  · rw [Ne, cd_eq_iff, ht, cd_c0]
    intro h
    rw [h] at hTc0
    exact absurd hTc0 (by decide)
  · have he : normSet c0A6 t = univ.filter fun g : A6 => memK (cd g) NL = true := by
      ext g
      rw [hN, Finset.mem_filter]
      exact ⟨fun h => ⟨Finset.mem_univ _, h⟩, fun h => h.2⟩
    rw [he, card_filter_cd (fun c => memK c NL)]
    exact Nat.eq_of_beq_eq_true hcard
  · intro x hx y hy
    rw [hN] at hx hy ⊢
    rw [cd_mul]
    exact allK_iff.1 (allK_iff.1 hmul _ (memK_iff.1 hx)) _ (memK_iff.1 hy)
  · intro x hx
    rw [hN] at hx ⊢
    rw [cd_inv]
    exact allK_iff.1 hinv _ (memK_iff.1 hx)
  · rw [hN, cd_c0]
    exact hc0
  · intro x hx hx3 hx1
    rw [hN] at hx
    have h := allK_iff.1 hord _ (memK_iff.1 hx)
    have h3 : Nat.beq (mulK 6 (cd x) (mulK 6 (cd x) (cd x))) E6 = true := by
      rw [← cd_mul, ← cd_mul, ← cd_one, ← cd_eq_iff, ← pow_three]
      exact hx3
    have h1 : Nat.beq (cd x) E6 = false := by
      rw [← cd_one, ← Bool.not_eq_true, ← cd_eq_iff]
      exact hx1
    rw [h3, h1, Bool.not_true, Bool.false_or, Bool.false_or] at h
    refine hex (P := fun u => u * x * u⁻¹ = x⁻¹)
      (q := fun u => Nat.beq (mulK 6 (mulK 6 u (cd x)) (invCK 6 u)) (invCK 6 (cd x))) ?_ ?_
    · intro u
      rw [cd_eq_iff, cd_mul, cd_mul, cd_inv, cd_inv]
    · obtain ⟨d, hd, hq⟩ := anyK_iff.1 h
      exact anyK_iff.2 ⟨d, hd, by rw [memK_iff.2 hd, Bool.true_and]; exact hq⟩
  · refine hex (P := fun s => ∀ r ∈ a2Rels, evalWord (betaTup a2 a3 c0A6 s) r = 1)
      (q := fun s => a2Rels.all fun r => Nat.beq (wK (cd a2) (cd a3) C0 s r) E6) ?_ ?_
    · intro s
      rw [rels_iff, cd_c0]
    · obtain ⟨d, hd, hq⟩ := anyK_iff.1 hs
      exact anyK_iff.2 ⟨d, hd, by rw [memK_iff.2 hd, Bool.true_and]; exact hq⟩

end BetaA6

open BetaA6 CFSG.Permutation.FinPack in
theorem betaCheck_A6 : BetaCheck (alternatingGroup (Fin 6)) c0A6 := by
  have hcm : c0A6 * c0A6 = 1 := by
    rw [cd_eq_iff, cd_mul, cd_c0, cd_one]
    exact c0_sq
  refine ⟨hcm, ?_, ?_, ?_⟩
  · rw [Ne, cd_eq_iff, cd_c0, cd_one, c0_ne]
    exact Bool.false_ne_true
  · intro a ha ha1
    have h := forall_cd conj_walk a
    have h2 : Nat.beq (mulK 6 (cd a) (cd a)) E6 = true := by
      rw [← cd_mul, ← cd_one, ← cd_eq_iff]
      exact ha
    have h1 : Nat.beq (cd a) E6 = false := by
      rw [← cd_one, ← Bool.not_eq_true, ← cd_eq_iff]
      exact ha1
    rw [h2, h1, Bool.not_true, Bool.false_or, Bool.false_or] at h
    obtain ⟨d, -, hd⟩ := anyK_iff.1 h
    rw [Bool.and_eq_true] at hd
    obtain ⟨g, rfl⟩ := exists_cd_eq hd.1
    refine ⟨g, ?_⟩
    rw [cd_eq_iff, cd_mul, cd_mul, cd_inv, cd_c0]
    exact hd.2
  · intro a2 ha2 a3 ha3 hd8
    have hcen : ∀ a ∈ centSet c0A6, memK (cd a) cenL = true := by
      intro a ha
      have h := forall_cd cen_walk a
      have hc : Nat.beq (mulK 6 (cd a) C0) (mulK 6 C0 (cd a)) = true := by
        rw [← cd_c0, ← cd_mul, ← cd_mul, ← cd_eq_iff]
        exact (Finset.mem_filter.1 ha).2
      rw [hc, Bool.not_true, Bool.false_or] at h
      exact h
    have h := allK_iff.1 (allK_iff.1 pairs_chk _ (memK_iff.1 (hcen a2 ha2))) _
      (memK_iff.1 (hcen a3 ha3))
    have hd : (d8Rels.all fun r => Nat.beq (wK (cd a2) (cd a3) C0 E6 r) E6) = true := by
      have h8 := (rels_iff _ _ _ _ _).1 hd8
      rwa [cd_c0, cd_one] at h8
    rw [hd, Bool.not_true, Bool.false_or, Bool.or_eq_true] at h
    have ht := t_chk
    rw [Bool.and_eq_true] at ht
    rcases h with h | h
    · exact exists_t_of_chk ht.1 norm1_walk a2 a3 h
    · exact exists_t_of_chk ht.2 norm2_walk a2 a3 h

end CFSG.Quasithin.Kleidman.ThreeLocal
