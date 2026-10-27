module

public import CFSG.Permutation.UnitaryThreeRecognition.AbelianQFiveModel

public section

open CFSG CFSG.UnitaryThreeRecognition CFSG.UnitaryThreeRecognition.AbelianQFive

namespace CertificateChecks.Batch8052

open CFSG CFSG.UnitaryThreeRecognition CFSG.UnitaryThreeRecognition.AbelianQFive

private def dec (c : ℕ) : M :=
  (((c / 25 : ℕ) : ZMod 5), ((c / 5 % 5 : ℕ) : ZMod 5), ((c % 5 : ℕ) : ZMod 5))

private theorem dec_enc {z a b : ℕ} (ha : a < 5) (hb : b < 5) :
    dec (25 * z + 5 * a + b) = ((z : ZMod 5), (a : ZMod 5), (b : ZMod 5)) := by
  have h1 : (25 * z + 5 * a + b) / 25 = z := by omega
  have h2 : (25 * z + 5 * a + b) / 5 % 5 = a := by omega
  have h3 : (25 * z + 5 * a + b) % 5 = b := by omega
  simp only [dec, h1, h2, h3]

private theorem code_lt (u : M) : code u < 125 := by
  have := ZMod.val_lt u.1
  have := ZMod.val_lt u.2.1
  have := ZMod.val_lt u.2.2
  unfold code
  omega

private theorem code_dec {c : ℕ} (hc : c < 125) : code (dec c) = c := by
  simp only [code, dec, ZMod.val_natCast]
  omega

private theorem dec_code (u : M) : dec (code u) = u := by
  obtain ⟨z, a, b⟩ := u
  simp only [code]
  rw [dec_enc (ZMod.val_lt a) (ZMod.val_lt b)]
  simp only [ZMod.natCast_zmod_val]

private theorem dec_inj {c d : ℕ} (hc : c < 125) (hd : d < 125) (h : dec c = dec d) : c = d := by
  rw [← code_dec hc, ← code_dec hd, h]

private theorem dec_zero : dec 0 = 0 := by
  simp [dec]

private theorem dec_eq_zero {c : ℕ} (hc : c < 125) : dec c = 0 ↔ c = 0 :=
  ⟨fun h => dec_inj hc (by decide) (h.trans dec_zero.symm), fun h => h ▸ dec_zero⟩

private theorem dec_snd_eq_zero : ∀ c < 125, ((dec c).2 = 0 ↔ c % 25 = 0) := by
  decide +kernel

private def addC (x y : ℕ) : ℕ :=
  25 * ((x / 25 + y / 25) % 5) + 5 * ((x / 5 % 5 + y / 5 % 5) % 5) + (x % 5 + y % 5) % 5

private def negC (x : ℕ) : ℕ :=
  25 * ((5 - x / 25) % 5) + 5 * ((5 - x / 5 % 5) % 5) + (5 - x % 5) % 5

private def gC (nu al be x : ℕ) : ℕ :=
  25 * (nu * (x / 25) % 5) + 5 * (be * (x % 5) % 5) + (x / 5 % 5 + al * (x % 5)) % 5

private theorem addC_lt (x y : ℕ) : addC x y < 125 := by
  unfold addC
  omega

private theorem negC_lt (x : ℕ) : negC x < 125 := by
  unfold negC
  omega

private theorem gC_lt (nu al be x : ℕ) : gC nu al be x < 125 := by
  unfold gC
  have := Nat.mod_lt (nu * (x / 25)) (show 0 < 5 by decide)
  have := Nat.mod_lt (be * (x % 5)) (show 0 < 5 by decide)
  have := Nat.mod_lt (x / 5 % 5 + al * (x % 5)) (show 0 < 5 by decide)
  omega

private theorem dec_addC (x y : ℕ) : dec (addC x y) = dec x + dec y := by
  unfold addC
  rw [dec_enc (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))]
  simp only [dec, ZMod.natCast_mod, Nat.cast_add, Prod.mk_add_mk]

private theorem addC_negC : ∀ x < 125, addC (negC x) x = 0 := by
  decide +kernel

private theorem dec_negC {x : ℕ} (hx : x < 125) : dec (negC x) = -dec x := by
  have h := dec_addC (negC x) x
  rw [addC_negC x hx, dec_zero] at h
  exact eq_neg_of_add_eq_zero_left h.symm

private theorem dec_gC (nu al be x : ℕ) :
    dec (gC nu al be x) = gen (nu : ZMod 5) (al : ZMod 5) (be : ZMod 5) (dec x) := by
  unfold gC
  rw [dec_enc (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))]
  simp only [gen, dec, ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul]

private theorem gC_iterate (nu al be j x : ℕ) (hx : x < 125) :
    (gC nu al be)^[j] x < 125 ∧
      dec ((gC nu al be)^[j] x) = (gen (nu : ZMod 5) (al : ZMod 5) (be : ZMod 5))^[j] (dec x) := by
  induction j with
  | zero => exact ⟨hx, rfl⟩
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact ⟨gC_lt _ _ _ _, by rw [dec_gC, ih.2]⟩

private def pack : List ℕ → ℕ
  | [] => 0
  | a :: l => a + 128 * pack l

private def rd (t i : ℕ) : ℕ := t / 128 ^ i % 128

private def lget : List ℕ → ℕ → ℕ
  | [], _ => 0
  | a :: _, 0 => a
  | _ :: l, n + 1 => lget l n

private def lset : List ℕ → ℕ → ℕ → List ℕ
  | [], _, _ => []
  | _ :: l, 0, v => v :: l
  | a :: l, n + 1, v => a :: lset l n v

private theorem lget_lset (A : List ℕ) (j v i : ℕ) :
    lget (lset A j v) i = if i = j ∧ j < A.length then v else lget A i := by
  induction A generalizing j i with
  | nil => simp [lset, lget]
  | cons a l ih =>
    cases j with
    | zero => cases i <;> simp [lset, lget]
    | succ j => cases i <;> simp [lset, lget, ih]

private theorem lget_replicate (n i : ℕ) : lget (List.replicate n 0) i = 0 := by
  induction n generalizing i with
  | zero => simp [lget]
  | succ n ih => cases i <;> simp [List.replicate_succ, lget, ih]

variable {P : Params} {D : Tables}

private def TB (P : Params) (D : Tables) (B : Array (Option M)) (u : M) : M :=
  (tauA P D B u).getD 0

private structure Good (P : Params) (D : Tables) (B : Array (Option M)) : Prop where
  size : B.size = D.reps.size
  full : ∀ i < B.size, ∃ b, B[i]? = some (some b)
  pass : chk P D B = true

private def Clause (P : Params) (D : Tables) (B : Array (Option M)) (r : M) (k : ℕ) : Prop :=
  ∀ w : M, w ≠ 0 → r + TB P D B w ≠ 0 → w - TB P D B (-r) ≠ 0 →
    TB P D B (r + TB P D B w) = TB P D B r + P.g^[k] (TB P D B (w - TB P D B (-r)))

private theorem tauA_good (hT : TablesOK P D) {B : Array (Option M)} (hB : Good P D B)
    (u : M) : tauA P D B u = some (TB P D B u) := by
  have : ∃ x, tauA P D B u = some x := by
    unfold tauA
    split_ifs with hu
    · exact ⟨0, rfl⟩
    · obtain ⟨i, k, hl, hi, -⟩ := hT.2 u hu
      obtain ⟨b, hb⟩ := hB.full i (hB.size ▸ hi)
      rw [hl]
      simp [hb]
  obtain ⟨x, hx⟩ := this
  simp [TB, hx]

private theorem TB_zero (hT : TablesOK P D) {B : Array (Option M)} (hB : Good P D B) :
    TB P D B 0 = 0 := by
  have h := tauA_good hT hB 0
  simp [tauA] at h
  exact h.symm

private theorem TB_orbit (hT : TablesOK P D) {B : Array (Option M)} (hB : Good P D B) {u : M}
    (hu : u ≠ 0) {i e : ℕ} (hl : look D u = some (i, e)) {b : M} (hb : B[i]? = some (some b)) :
    TB P D B u = P.g^[(P.m * e) % 8] b := by
  have h := tauA_good hT hB u
  simp [tauA, hu, hl, hb] at h
  exact h.symm

private theorem good_p1 (hT : TablesOK P D) {B : Array (Option M)} (hB : Good P D B) {i : ℕ}
    (hi : i < D.reps.size) {b : M} (hb : B[i]? = some (some b)) :
    b ≠ 0 ∧ (D.reps[i].2 = 0 ↔ b.2 = 0) ∧ TB P D B b = D.reps[i] := by
  have h := hB.pass
  unfold chk at h
  rw [Bool.and_eq_true, List.all_eq_true] at h
  have h1 := h.1 i (List.mem_range.mpr hi)
  simp only [hb, Array.getElem?_eq_getElem hi, Option.join_some, tauA_good hT hB,
    Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, decide_eq_decide] at h1
  exact ⟨h1.1.1, h1.1.2, h1.2⟩

private theorem good_p2 (hT : TablesOK P D) {B : Array (Option M)} (hB : Good P D B) {i : ℕ}
    (hi : i < D.reps.size) : ∃ k < 8, Clause P D B D.reps[i] k := by
  have h := hB.pass
  unfold chk at h
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at h
  have h2 := h.2 i (List.mem_range.mpr hi)
  simp only [Array.getElem?_eq_getElem hi, tauA_good hT hB, List.any_eq_true, List.mem_range,
    List.all_eq_true] at h2
  obtain ⟨k, hk, hk'⟩ := h2
  refine ⟨k, hk, fun w hw h1 h2 => ?_⟩
  have := hk' w (mem_allM w)
  simpa [hw, h1, h2] using this

private structure Cd where
  nu : ℕ
  al : ℕ
  be : ℕ
  m : ℕ
  orb : ℕ
  rep : ℕ
  gp : ℕ

private def Cd.orbAt (cd : Cd) (c : ℕ) : ℕ := rd cd.orb c

private def Cd.repAt (cd : Cd) (i : ℕ) : ℕ := rd cd.rep i

private def Cd.gpAt (cd : Cd) (j x : ℕ) : ℕ := rd cd.gp (125 * j + x)

private structure CdOK (P : Params) (D : Tables) (cd : Cd) : Prop where
  size : D.reps.size = 16
  rep : ∀ i < 16, (D.reps[i]?).map code = some (cd.repAt i)
  orb : ∀ c < 125, c ≠ 0 →
    cd.orbAt c / 8 < 16 ∧ (D.lookup[c]?).join = some (cd.orbAt c / 8, cd.orbAt c % 8)
  gp : ∀ j < 8, ∀ x < 125, cd.gpAt j x = (gC cd.nu cd.al cd.be)^[j] x
  nu : P.ν = cd.nu
  al : P.α = cd.al
  be : P.β = cd.be
  m : cd.m = P.m

private theorem rep_spec {cd : Cd} (hc : CdOK P D cd) {i : ℕ} (hi : i < 16) :
    cd.repAt i < 125 ∧ ∃ h : i < D.reps.size, D.reps[i] = dec (cd.repAt i) := by
  have h := hc.rep i hi
  have hi' : i < D.reps.size := hc.size ▸ hi
  rw [Array.getElem?_eq_getElem hi', Option.map_some] at h
  have h' : code D.reps[i] = cd.repAt i := Option.some.inj h
  exact ⟨h' ▸ code_lt _, hi', by rw [← h', dec_code]⟩

private theorem look_spec {cd : Cd} (hc : CdOK P D cd) {c : ℕ} (hc' : c < 125) (h0 : c ≠ 0) :
    cd.orbAt c / 8 < 16 ∧ look D (dec c) = some (cd.orbAt c / 8, cd.orbAt c % 8) := by
  obtain ⟨h1, h2⟩ := hc.orb c hc' h0
  exact ⟨h1, by unfold look; rw [code_dec hc']; exact h2⟩

private theorem gp_spec {cd : Cd} (hc : CdOK P D cd) {j x : ℕ} (hj : j < 8) (hx : x < 125) :
    cd.gpAt j x < 125 ∧ dec (cd.gpAt j x) = P.g^[j] (dec x) := by
  rw [hc.gp j hj x hx]
  obtain ⟨h1, h2⟩ := gC_iterate cd.nu cd.al cd.be j x hx
  refine ⟨h1, ?_⟩
  rw [h2, Params.g_def, hc.nu, hc.al, hc.be]

private theorem iter_inv (h8 : ∀ u, P.g^[8] u = u) {e : ℕ} (he : e < 8) (b : M) :
    P.g^[(8 - e) % 8] (P.g^[e] b) = b := by
  rw [← Function.iterate_add_apply, ← iterate_mod h8]
  have : ((8 - e) % 8 + e) % 8 = 0 := by omega
  rw [this]
  rfl

private def TS (cd : Cd) (A : List ℕ) (c : ℕ) : ℕ :=
  if c = 0 then 1 else
    match lget A (cd.orbAt c / 8) with
    | 0 => 0
    | a + 1 => cd.gpAt (cd.m * (cd.orbAt c % 8) % 8) a + 1

private def Valid (P : Params) (D : Tables) (A K : List ℕ) (B : Array (Option M)) : Prop :=
  (∀ i v, lget A i = v + 1 → v < 125 ∧ B[i]? = some (some (dec v))) ∧
  ∀ i k, lget K i = k + 1 → k < 8 ∧ ∃ hi : i < D.reps.size, Clause P D B D.reps[i] k

private theorem valid_lset {A K : List ℕ} {B : Array (Option M)} (hV : Valid P D A K B)
    {j v : ℕ} (hv : v < 125) (hB : B[j]? = some (some (dec v))) :
    Valid P D (lset A j (v + 1)) K B := by
  refine ⟨fun i w hw => ?_, hV.2⟩
  rw [lget_lset] at hw
  split_ifs at hw with h
  · obtain ⟨rfl, -⟩ := h
    obtain rfl : w = v := by omega
    exact ⟨hv, hB⟩
  · exact hV.1 i w hw

private theorem TS_spec (hT : TablesOK P D) {cd : Cd} (hc : CdOK P D cd) {B : Array (Option M)}
    (hB : Good P D B) {A K : List ℕ} (hV : Valid P D A K B) {c t : ℕ} (hc' : c < 125)
    (h : TS cd A c = t + 1) : t < 125 ∧ TB P D B (dec c) = dec t := by
  unfold TS at h
  split_ifs at h with h0
  · subst h0
    obtain rfl : t = 0 := by omega
    exact ⟨by decide, by rw [dec_zero, TB_zero hT hB]⟩
  · rcases ha : lget A (cd.orbAt c / 8) with _ | a
    · rw [ha] at h
      simp at h
    · rw [ha] at h
      simp only [Nat.add_right_cancel_iff] at h
      obtain ⟨ha1, ha2⟩ := hV.1 _ _ ha
      obtain ⟨-, hl⟩ := look_spec hc hc' h0
      have hdc : dec c ≠ 0 := fun h' => h0 ((dec_eq_zero hc').mp h')
      obtain ⟨hlt, hg⟩ := gp_spec hc (j := cd.m * (cd.orbAt c % 8) % 8)
        (Nat.mod_lt _ (by decide)) ha1
      subst h
      refine ⟨hlt, ?_⟩
      rw [TB_orbit hT hB hdc hl ha2, hg, hc.m]

private def asg (cd : Cd) (A : List ℕ) (j v : ℕ) : List ℕ :=
  if v ≠ 0 ∧ lget (lset A j (v + 1)) (cd.orbAt v / 8) = 0 then
    lset (lset A j (v + 1)) (cd.orbAt v / 8)
      (cd.gpAt ((8 - cd.m * (cd.orbAt v % 8) % 8) % 8) (cd.repAt j) + 1)
  else lset A j (v + 1)

private theorem asg_spec (hT : TablesOK P D) (h8 : ∀ u, P.g^[8] u = u) {cd : Cd} (hc : CdOK P D cd)
    {B : Array (Option M)} (hB : Good P D B) {A K : List ℕ} (hV : Valid P D A K B) {j v : ℕ}
    (hj : j < 16) (hv : v < 125) (hBj : B[j]? = some (some (dec v))) :
    Valid P D (asg cd A j v) K B := by
  have hV1 := valid_lset hV hv hBj
  unfold asg
  split_ifs with h
  · obtain ⟨h0, -⟩ := h
    obtain ⟨ho, hl⟩ := look_spec hc hv h0
    have hj' : j < D.reps.size := hc.size ▸ hj
    obtain ⟨b, hb⟩ := hB.full (cd.orbAt v / 8) (by rw [hB.size, hc.size]; exact ho)
    have h1 := TB_orbit hT hB (fun h' => h0 ((dec_eq_zero hv).mp h')) hl hb
    obtain ⟨-, -, h2⟩ := good_p1 hT hB hj' hBj
    obtain ⟨hr, _, hr'⟩ := rep_spec hc hj
    obtain ⟨hlt, hg⟩ := gp_spec hc (j := (8 - cd.m * (cd.orbAt v % 8) % 8) % 8)
      (Nat.mod_lt _ (by decide)) hr
    refine valid_lset hV1 hlt ?_
    rw [hb, hg, ← hr', ← h2, h1, hc.m, iter_inv h8 (Nat.mod_lt _ (by decide))]
  · exact hV1

private theorem derive_spec (hT : TablesOK P D) (h8 : ∀ u, P.g^[8] u = u) {cd : Cd}
    (hc : CdOK P D cd) {B : Array (Option M)} (hB : Good P D B) {A K : List ℕ}
    (hV : Valid P D A K B) {x val : ℕ} (hx : x < 125) (hx0 : x ≠ 0) (hval : val < 125)
    (h : TB P D B (dec x) = dec val) :
    Valid P D (asg cd A (cd.orbAt x / 8)
      (cd.gpAt ((8 - cd.m * (cd.orbAt x % 8) % 8) % 8) val)) K B := by
  obtain ⟨ho, hl⟩ := look_spec hc hx hx0
  obtain ⟨b, hb⟩ := hB.full (cd.orbAt x / 8) (by rw [hB.size, hc.size]; exact ho)
  have h1 := TB_orbit hT hB (fun h' => hx0 ((dec_eq_zero hx).mp h')) hl hb
  obtain ⟨hlt, hg⟩ := gp_spec hc (j := (8 - cd.m * (cd.orbAt x % 8) % 8) % 8)
    (Nat.mod_lt _ (by decide)) hval
  refine asg_spec hT h8 hc hB hV ho hlt ?_
  rw [hb, hg, ← h, h1, hc.m, iter_inv h8 (Nat.mod_lt _ (by decide))]

private def p1fails (cd : Cd) (A : List ℕ) (j : ℕ) : Bool :=
  match lget A j with
  | 0 => false
  | v + 1 =>
    v == 0 || (cd.repAt j % 25 == 0) != (v % 25 == 0) ||
      match TS cd A v with
      | 0 => false
      | t + 1 => t != cd.repAt j

private theorem p1_spec (hT : TablesOK P D) {cd : Cd} (hc : CdOK P D cd)
    {B : Array (Option M)} (hB : Good P D B) {A K : List ℕ} (hV : Valid P D A K B) {j : ℕ}
    (h : p1fails cd A j = true) : False := by
  unfold p1fails at h
  rcases ha : lget A j with _ | v
  · rw [ha] at h
    simp at h
  rw [ha] at h
  obtain ⟨hv, hBj⟩ := hV.1 j v ha
  have hjB : j < B.size := by
    rcases Nat.lt_or_ge j B.size with h' | h'
    · exact h'
    · rw [Array.getElem?_eq_none h'] at hBj
      simp at hBj
  have hj : j < D.reps.size := hB.size ▸ hjB
  obtain ⟨hne, hcen, hTB⟩ := good_p1 hT hB hj hBj
  obtain ⟨hr, _, hr'⟩ := rep_spec hc (hc.size ▸ hj)
  rw [hr'] at hcen hTB
  rw [dec_snd_eq_zero _ hr, dec_snd_eq_zero _ hv] at hcen
  simp only [Bool.or_eq_true] at h
  rcases h with (h | h) | h
  · rw [beq_iff_eq] at h
    subst h
    exact hne dec_zero
  · by_cases h1 : cd.repAt j % 25 = 0 <;> by_cases h2 : v % 25 = 0 <;> simp_all
  · rcases ht : TS cd A v with _ | t
    · rw [ht] at h
      simp at h
    · rw [ht] at h
      obtain ⟨htl, htb⟩ := TS_spec hT hc hB hV hv ht
      have := dec_inj htl hr (htb.symm.trans hTB)
      simp [this] at h

private inductive Res
  | fail
  | leaf
  | next (A : List ℕ)

private def clStep (cd : Cd) (A K : List ℕ) (i w : ℕ) : Res :=
  match lget K i with
  | 0 => .fail
  | k + 1 =>
    match TS cd A (cd.repAt i), TS cd A (negC (cd.repAt i)), TS cd A w with
    | tu + 1, tnu + 1, tw + 1 =>
      if w = 0 ∨ 125 ≤ w ∨ addC (cd.repAt i) tw = 0 ∨ addC w (negC tnu) = 0 then .fail else
      match TS cd A (addC (cd.repAt i) tw), TS cd A (addC w (negC tnu)) with
      | tx + 1, ty + 1 => if tx = addC tu (cd.gpAt k ty) then .fail else .leaf
      | 0, ty + 1 =>
        .next (asg cd A (cd.orbAt (addC (cd.repAt i) tw) / 8)
          (cd.gpAt ((8 - cd.m * (cd.orbAt (addC (cd.repAt i) tw) % 8) % 8) % 8)
            (addC tu (cd.gpAt k ty))))
      | tx + 1, 0 =>
        .next (asg cd A (cd.orbAt (addC w (negC tnu)) / 8)
          (cd.gpAt ((8 - cd.m * (cd.orbAt (addC w (negC tnu)) % 8) % 8) % 8)
            (cd.gpAt ((8 - k) % 8) (addC tx (negC tu)))))
      | 0, 0 => .fail
    | _, _, _ => .fail

private theorem cl_spec (hT : TablesOK P D) (h8 : ∀ u, P.g^[8] u = u) {cd : Cd}
    (hc : CdOK P D cd) {B : Array (Option M)} (hB : Good P D B) {A K : List ℕ}
    (hV : Valid P D A K B) {i w : ℕ} {r : Res} (hr : clStep cd A K i w = r) :
    (r = .leaf → False) ∧ ∀ A', r = .next A' → Valid P D A' K B := by
  unfold clStep at hr
  split at hr
  · subst hr
    simp
  rename_i k hk
  obtain ⟨hk8, hi, hcl⟩ := hV.2 i k hk
  obtain ⟨hru, _, hri⟩ := rep_spec hc (hc.size ▸ hi)
  split at hr
  · rename_i tu tnu tw htu htnu htw
    split_ifs at hr with hcond
    · subst hr
      simp
    simp only [not_or, not_le] at hcond
    obtain ⟨hw0, hw, hx0, hy0⟩ := hcond
    obtain ⟨htu1, htu2⟩ := TS_spec hT hc hB hV hru htu
    obtain ⟨htnu1, htnu2⟩ := TS_spec hT hc hB hV (negC_lt _) htnu
    obtain ⟨htw1, htw2⟩ := TS_spec hT hc hB hV hw htw
    rw [dec_negC hru, ← hri] at htnu2
    rw [← hri] at htu2
    have hdw : dec w ≠ 0 := fun h' => hw0 ((dec_eq_zero hw).mp h')
    have hdx : D.reps[i] + TB P D B (dec w) ≠ 0 := by
      rw [htw2, hri, ← dec_addC]
      exact fun h' => hx0 ((dec_eq_zero (addC_lt _ _)).mp h')
    have hdy : dec w - TB P D B (-D.reps[i]) ≠ 0 := by
      rw [htnu2, sub_eq_add_neg, ← dec_negC htnu1, ← dec_addC]
      exact fun h' => hy0 ((dec_eq_zero (addC_lt _ _)).mp h')
    have key := hcl (dec w) hdw hdx hdy
    have ex : D.reps[i] + TB P D B (dec w) = dec (addC (cd.repAt i) tw) := by
      rw [htw2, hri, dec_addC]
    have ey : dec w - TB P D B (-D.reps[i]) = dec (addC w (negC tnu)) := by
      rw [htnu2, dec_addC, dec_negC htnu1, sub_eq_add_neg]
    rw [ex, ey, htu2] at key
    split at hr
    · rename_i tx ty htx hty
      obtain ⟨htx1, htx2⟩ := TS_spec hT hc hB hV (addC_lt _ _) htx
      obtain ⟨hty1, hty2⟩ := TS_spec hT hc hB hV (addC_lt _ _) hty
      split_ifs at hr with heq
      · subst hr
        simp
      · subst hr
        refine ⟨fun _ => heq ?_, fun _ h => by cases h⟩
        obtain ⟨hg1, hg2⟩ := gp_spec hc hk8 hty1
        apply dec_inj htx1 (addC_lt _ _)
        rw [dec_addC, hg2, ← hty2, ← htx2, key]
    · rename_i ty htx hty
      obtain ⟨hty1, hty2⟩ := TS_spec hT hc hB hV (addC_lt _ _) hty
      subst hr
      refine ⟨fun h => (by cases h), fun A' h => ?_⟩
      cases h
      obtain ⟨hg1, hg2⟩ := gp_spec hc hk8 hty1
      refine derive_spec hT h8 hc hB hV (addC_lt _ _) hx0 (addC_lt _ _) ?_
      rw [key, hty2, dec_addC, hg2]
    · rename_i tx htx hty
      obtain ⟨htx1, htx2⟩ := TS_spec hT hc hB hV (addC_lt _ _) htx
      subst hr
      refine ⟨fun h => (by cases h), fun A' h => ?_⟩
      cases h
      obtain ⟨hg1, hg2⟩ := gp_spec hc (j := (8 - k) % 8) (Nat.mod_lt _ (by decide))
        (addC_lt tx (negC tu))
      refine derive_spec hT h8 hc hB hV (addC_lt _ _) hy0 hg1 ?_
      have e1 : dec (addC tx (negC tu)) =
          P.g^[k] (TB P D B (dec (addC w (negC tnu)))) := by
        rw [dec_addC, dec_negC htu1, ← htx2, key, ← sub_eq_add_neg, add_sub_cancel_left]
      rw [hg2, e1, iter_inv h8 hk8]
    · subst hr
      simp
  · subst hr
    simp

private inductive Op
  | p1 (j : ℕ)
  | cl (i w : ℕ)
  | bk (i : ℕ)
  | bv (j : ℕ)

private def run (cd : Cd) : ℕ → List (List ℕ × List ℕ) → List Op → Bool
  | 0, _, _ => false
  | _ + 1, [], _ => true
  | _ + 1, _ :: _, [] => false
  | n + 1, (A, K) :: stk, op :: ops =>
    match op with
    | .p1 j => p1fails cd A j && run cd n stk ops
    | .cl i w =>
      match clStep cd A K i w with
      | .fail => false
      | .leaf => run cd n stk ops
      | .next A' => run cd n ((A', K) :: stk) ops
    | .bk i =>
      decide (i < 16) && run cd n ((List.range 8).map (fun k => (A, lset K i (k + 1))) ++ stk) ops
    | .bv j =>
      decide (j < 16) && run cd n ((List.range 124).map (fun v => (asg cd A j (v + 1), K)) ++ stk)
        ops

private theorem run_spec (hT : TablesOK P D) (h8 : ∀ u, P.g^[8] u = u) {cd : Cd}
    (hc : CdOK P D cd) : ∀ n stk ops, run cd n stk ops = true →
      ∀ s ∈ stk, ∀ B, Good P D B → Valid P D s.1 s.2 B → False := by
  intro n
  induction n with
  | zero =>
    intro stk ops h
    simp [run] at h
  | succ n ih =>
    intro stk ops h s hs B hB hV
    rcases stk with _ | ⟨⟨A, K⟩, stk⟩
    · simp at hs
    rcases ops with _ | ⟨op, ops⟩
    · simp [run] at h
    have hs' : s = (A, K) ∨ s ∈ stk := List.mem_cons.mp hs
    cases op with
    | p1 j =>
      simp only [run, Bool.and_eq_true] at h
      rcases hs' with rfl | hs'
      · exact p1_spec hT hc hB hV h.1
      · exact ih _ _ h.2 s hs' B hB hV
    | cl i w =>
      simp only [run] at h
      rcases hcs : clStep cd A K i w with _ | _ | A'
      · rw [hcs] at h
        simp at h
      · rw [hcs] at h
        rcases hs' with rfl | hs'
        · exact (cl_spec hT h8 hc hB hV hcs).1 rfl
        · exact ih _ _ h s hs' B hB hV
      · rw [hcs] at h
        rcases hs' with rfl | hs'
        · exact ih _ _ h (A', K) List.mem_cons_self B hB ((cl_spec hT h8 hc hB hV hcs).2 A' rfl)
        · exact ih _ _ h s (List.mem_cons_of_mem _ hs') B hB hV
    | bk i =>
      simp only [run, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨hi, h⟩ := h
      rcases hs' with rfl | hs'
      · have hi' : i < D.reps.size := hc.size ▸ hi
        obtain ⟨k, hk, hcl⟩ := good_p2 hT hB hi'
        refine ih _ _ h (A, lset K i (k + 1))
          (List.mem_append_left _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩)) B hB
          ⟨hV.1, fun i' k' hk' => ?_⟩
        rw [lget_lset] at hk'
        split_ifs at hk' with h'
        · obtain ⟨rfl, -⟩ := h'
          obtain rfl : k' = k := by omega
          exact ⟨hk, hi', hcl⟩
        · exact hV.2 i' k' hk'
      · exact ih _ _ h s (List.mem_append_right _ hs') B hB hV
    | bv j =>
      simp only [run, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨hj, h⟩ := h
      rcases hs' with rfl | hs'
      · have hj' : j < D.reps.size := hc.size ▸ hj
        obtain ⟨b, hb⟩ := hB.full j (hB.size ▸ hj')
        obtain ⟨hne, -, -⟩ := good_p1 hT hB hj' hb
        have hcb := code_lt b
        have hcb0 : code b ≠ 0 := fun h' => hne (by rw [← dec_code b, h', dec_zero])
        have hv : code b - 1 + 1 = code b := by omega
        refine ih _ _ h (asg cd A j (code b - 1 + 1), K)
          (List.mem_append_left _
            (List.mem_map.mpr ⟨code b - 1, List.mem_range.mpr (by omega), rfl⟩)) B hB ?_
        rw [hv]
        exact asg_spec hT h8 hc hB hV hj hcb (by rw [dec_code]; exact hb)
      · exact ih _ _ h s (List.mem_append_right _ hs') B hB hV

private def z16 : List ℕ := List.replicate 16 0

private theorem refute (hT : TablesOK P D) (h8 : ∀ u, P.g^[8] u = u) {cd : Cd}
    (hc : CdOK P D cd) {n : ℕ} {ops : List Op} (h : run cd n [(z16, z16)] ops = true)
    (B : Array (Option M)) (hB : Good P D B) : False :=
  run_spec hT h8 hc n _ ops h _ List.mem_cons_self B hB
    ⟨fun i v hv => absurd hv (by rw [z16, lget_replicate]; omega),
      fun i k hk => absurd hk (by rw [z16, lget_replicate]; omega)⟩

private theorem count_set_some (A : Array (Option M)) (i : ℕ) (x : M) :
    (A.set! i (some x)).count none ≤ A.count none ∧
      (A[i]? = some none → (A.set! i (some x)).count none + 1 = A.count none) := by
  rw [Array.set!_eq_setIfInBounds, Array.setIfInBounds_def]
  split_ifs with hi
  · have hsx : (some x == none) = false := rfl
    rw [Array.count_set hi, hsx]
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    refine ⟨Nat.sub_le _ _, fun h => ?_⟩
    rw [Array.getElem?_eq_getElem hi, Option.some.injEq] at h
    have hpos : 0 < A.count none := Array.count_pos_iff.mpr (h ▸ Array.getElem_mem hi)
    have hn : (A[i] == none) = true := by
      rw [h]
      rfl
    simp only [hn, ↓reduceIte]
    omega
  · refine ⟨le_rfl, fun h => ?_⟩
    rw [Array.getElem?_eq_none (Nat.le_of_not_lt hi)] at h
    simp at h

private theorem count_extend (A : Array (Option M)) (i : ℕ) (val : M)
    (h : A[i]? = some none) : (extend P D A i val).count none + 1 ≤ A.count none := by
  have h1 := (count_set_some A i val).2 h
  unfold extend
  dsimp only
  split
  · split_ifs
    · exact (Nat.add_le_add_right (count_set_some _ _ _).1 1).trans h1.le
    · exact h1.le
  · exact h1.le

private theorem search_true (hR : ∀ B, Good P D B → False) :
    ∀ fuel (A : Array (Option M)), A.size = D.reps.size → A.count none < fuel →
      search P D fuel A = true := by
  intro fuel
  induction fuel with
  | zero =>
    intro A _ h
    omega
  | succ fuel ih =>
    intro A hA hcnt
    unfold search
    rcases hf : A.findIdx? (· = none) with _ | i
    · simp only [Bool.not_eq_true']
      by_contra hchk
      refine hR A ⟨hA, fun j hj => ?_, by simpa using hchk⟩
      have := Array.findIdx?_eq_none_iff.mp hf A[j] (Array.getElem_mem hj)
      rcases hAj : A[j] with _ | b
      · rw [hAj] at this
        simp at this
      · exact ⟨b, by rw [Array.getElem?_eq_getElem hj, hAj]⟩
    · obtain ⟨hi, hnone, -⟩ := Array.findIdx?_eq_some_iff_getElem.mp hf
      have hAi : A[i]? = some none := by
        rw [Array.getElem?_eq_getElem hi]
        simpa using hnone
      simp only [List.all_eq_true, Bool.or_eq_true]
      intro val _
      right
      right
      apply ih _ ((extend_size P D A i val).trans hA)
      have := count_extend (P := P) (D := D) A i val hAi
      omega

private theorem search_case (hT : tablesOKb P D = true) (h8 : g8b P = true) {cd : Cd}
    (hc : CdOK P D cd) {n : ℕ} {ops : List Op} (h : run cd n [(z16, z16)] ops = true) :
    (tablesOKb P D && g8b P && search P D 17 (Array.replicate D.reps.size none)) = true := by
  rw [hT, h8, Bool.true_and, Bool.true_and]
  refine search_true (refute (tablesOK_of_tablesOKb hT) (g8_of_g8b h8) hc h) 17 _ (by simp) ?_
  rw [Array.count_replicate, hc.size]
  simp

private theorem tables_ext {D D' : Tables} (h1 : D.lookup = D'.lookup)
    (h2 : D.reps = D'.reps) : D = D' := by
  cases D
  cases D'
  simp_all

private theorem orbitData_congr {P Q : Params} (h : P.g = Q.g) : orbitData P = orbitData Q := by
  unfold orbitData
  rw [h]

private theorem tablesOKb_congr {P Q : Params} {D : Tables} (h : P.g = Q.g) :
    tablesOKb P D = tablesOKb Q D := by
  unfold tablesOKb
  rw [h]

private theorem g8b_congr {P Q : Params} (h : P.g = Q.g) : g8b P = g8b Q := by
  unfold g8b
  rw [h]

private def tab22 : Tables where
  lookup := #[
    none, some (0, 0), some (0, 2), some (0, 6), some (0, 4), some (0, 7), some (1, 0),
    some (2, 0), some (1, 7), some (2, 5), some (0, 1), some (1, 1), some (1, 2), some (2, 7),
    some (2, 2), some (0, 5), some (2, 6), some (2, 3), some (1, 6), some (1, 5), some (0, 3),
    some (2, 1), some (1, 3), some (2, 4), some (1, 4), some (3, 0), some (4, 0), some (5, 0),
    some (5, 4), some (4, 4), some (6, 0), some (7, 0), some (8, 0), some (9, 0), some (10, 0),
    some (11, 0), some (12, 0), some (13, 0), some (14, 0), some (15, 0), some (11, 4),
    some (15, 4), some (14, 4), some (13, 4), some (12, 4), some (6, 4), some (10, 4), some (9, 4),
    some (8, 4), some (7, 4), some (3, 1), some (6, 1), some (11, 1), some (11, 5), some (6, 5),
    some (5, 5), some (9, 1), some (14, 1), some (13, 5), some (8, 5), some (4, 1), some (7, 1),
    some (12, 1), some (15, 5), some (10, 5), some (4, 5), some (10, 1), some (15, 1),
    some (12, 5), some (7, 5), some (5, 1), some (8, 1), some (13, 1), some (14, 5), some (9, 5),
    some (3, 3), some (11, 7), some (6, 3), some (6, 7), some (11, 3), some (4, 7), some (12, 7),
    some (10, 3), some (7, 7), some (15, 3), some (5, 7), some (13, 7), some (9, 3), some (8, 7),
    some (14, 3), some (5, 3), some (14, 7), some (8, 3), some (9, 7), some (13, 3), some (4, 3),
    some (15, 7), some (7, 3), some (10, 7), some (12, 3), some (3, 2), some (5, 6), some (4, 2),
    some (4, 6), some (5, 2), some (11, 6), some (13, 6), some (15, 6), some (12, 6), some (14, 6),
    some (6, 2), some (9, 2), some (7, 2), some (10, 2), some (8, 2), some (6, 6), some (8, 6),
    some (10, 6), some (7, 6), some (9, 6), some (11, 2), some (14, 2), some (12, 2), some (15, 2),
    some (13, 2)]
  reps := #[
    (0, 0, 1), (0, 1, 1), (0, 1, 2), (1, 0, 0), (1, 0, 1), (1, 0, 2), (1, 1, 0), (1, 1, 1),
    (1, 1, 2), (1, 1, 3), (1, 1, 4), (1, 2, 0), (1, 2, 1), (1, 2, 2), (1, 2, 3), (1, 2, 4)]

private def orb22 : ℕ := pack [
    0, 0, 2, 6, 4, 7, 8, 16, 15, 21, 1, 9, 10, 23, 18, 5, 22, 19, 14, 13, 3, 17, 11, 20, 12, 24,
    32, 40, 44, 36, 48, 56, 64, 72, 80, 88, 96, 104, 112, 120, 92, 124, 116, 108, 100, 52, 84, 76,
    68, 60, 25, 49, 89, 93, 53, 45, 73, 113, 109, 69, 33, 57, 97, 125, 85, 37, 81, 121, 101, 61,
    41, 65, 105, 117, 77, 27, 95, 51, 55, 91, 39, 103, 83, 63, 123, 47, 111, 75, 71, 115, 43, 119,
    67, 79, 107, 35, 127, 59, 87, 99, 26, 46, 34, 38, 42, 94, 110, 126, 102, 118, 50, 74, 58, 82,
    66, 54, 70, 86, 62, 78, 90, 114, 98, 122, 106]

private def rep22 : ℕ := pack [
    1, 6, 7, 25, 26, 27, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39]

private def gp22 : ℕ := pack [
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25,
    26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49,
    50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73,
    74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97,
    98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116,
    117, 118, 119, 120, 121, 122, 123, 124, 0, 10, 20, 5, 15, 1, 11, 21, 6, 16, 2, 12, 22, 7, 17,
    3, 13, 23, 8, 18, 4, 14, 24, 9, 19, 50, 60, 70, 55, 65, 51, 61, 71, 56, 66, 52, 62, 72, 57, 67,
    53, 63, 73, 58, 68, 54, 64, 74, 59, 69, 100, 110, 120, 105, 115, 101, 111, 121, 106, 116, 102,
    112, 122, 107, 117, 103, 113, 123, 108, 118, 104, 114, 124, 109, 119, 25, 35, 45, 30, 40, 26,
    36, 46, 31, 41, 27, 37, 47, 32, 42, 28, 38, 48, 33, 43, 29, 39, 49, 34, 44, 75, 85, 95, 80, 90,
    76, 86, 96, 81, 91, 77, 87, 97, 82, 92, 78, 88, 98, 83, 93, 79, 89, 99, 84, 94, 0, 2, 4, 1, 3,
    10, 12, 14, 11, 13, 20, 22, 24, 21, 23, 5, 7, 9, 6, 8, 15, 17, 19, 16, 18, 100, 102, 104, 101,
    103, 110, 112, 114, 111, 113, 120, 122, 124, 121, 123, 105, 107, 109, 106, 108, 115, 117, 119,
    116, 118, 75, 77, 79, 76, 78, 85, 87, 89, 86, 88, 95, 97, 99, 96, 98, 80, 82, 84, 81, 83, 90,
    92, 94, 91, 93, 50, 52, 54, 51, 53, 60, 62, 64, 61, 63, 70, 72, 74, 71, 73, 55, 57, 59, 56, 58,
    65, 67, 69, 66, 68, 25, 27, 29, 26, 28, 35, 37, 39, 36, 38, 45, 47, 49, 46, 48, 30, 32, 34, 31,
    33, 40, 42, 44, 41, 43, 0, 20, 15, 10, 5, 2, 22, 17, 12, 7, 4, 24, 19, 14, 9, 1, 21, 16, 11, 6,
    3, 23, 18, 13, 8, 75, 95, 90, 85, 80, 77, 97, 92, 87, 82, 79, 99, 94, 89, 84, 76, 96, 91, 86,
    81, 78, 98, 93, 88, 83, 25, 45, 40, 35, 30, 27, 47, 42, 37, 32, 29, 49, 44, 39, 34, 26, 46, 41,
    36, 31, 28, 48, 43, 38, 33, 100, 120, 115, 110, 105, 102, 122, 117, 112, 107, 104, 124, 119,
    114, 109, 101, 121, 116, 111, 106, 103, 123, 118, 113, 108, 50, 70, 65, 60, 55, 52, 72, 67, 62,
    57, 54, 74, 69, 64, 59, 51, 71, 66, 61, 56, 53, 73, 68, 63, 58, 0, 4, 3, 2, 1, 20, 24, 23, 22,
    21, 15, 19, 18, 17, 16, 10, 14, 13, 12, 11, 5, 9, 8, 7, 6, 25, 29, 28, 27, 26, 45, 49, 48, 47,
    46, 40, 44, 43, 42, 41, 35, 39, 38, 37, 36, 30, 34, 33, 32, 31, 50, 54, 53, 52, 51, 70, 74, 73,
    72, 71, 65, 69, 68, 67, 66, 60, 64, 63, 62, 61, 55, 59, 58, 57, 56, 75, 79, 78, 77, 76, 95, 99,
    98, 97, 96, 90, 94, 93, 92, 91, 85, 89, 88, 87, 86, 80, 84, 83, 82, 81, 100, 104, 103, 102,
    101, 120, 124, 123, 122, 121, 115, 119, 118, 117, 116, 110, 114, 113, 112, 111, 105, 109, 108,
    107, 106, 0, 15, 5, 20, 10, 4, 19, 9, 24, 14, 3, 18, 8, 23, 13, 2, 17, 7, 22, 12, 1, 16, 6, 21,
    11, 50, 65, 55, 70, 60, 54, 69, 59, 74, 64, 53, 68, 58, 73, 63, 52, 67, 57, 72, 62, 51, 66, 56,
    71, 61, 100, 115, 105, 120, 110, 104, 119, 109, 124, 114, 103, 118, 108, 123, 113, 102, 117,
    107, 122, 112, 101, 116, 106, 121, 111, 25, 40, 30, 45, 35, 29, 44, 34, 49, 39, 28, 43, 33, 48,
    38, 27, 42, 32, 47, 37, 26, 41, 31, 46, 36, 75, 90, 80, 95, 85, 79, 94, 84, 99, 89, 78, 93, 83,
    98, 88, 77, 92, 82, 97, 87, 76, 91, 81, 96, 86, 0, 3, 1, 4, 2, 15, 18, 16, 19, 17, 5, 8, 6, 9,
    7, 20, 23, 21, 24, 22, 10, 13, 11, 14, 12, 100, 103, 101, 104, 102, 115, 118, 116, 119, 117,
    105, 108, 106, 109, 107, 120, 123, 121, 124, 122, 110, 113, 111, 114, 112, 75, 78, 76, 79, 77,
    90, 93, 91, 94, 92, 80, 83, 81, 84, 82, 95, 98, 96, 99, 97, 85, 88, 86, 89, 87, 50, 53, 51, 54,
    52, 65, 68, 66, 69, 67, 55, 58, 56, 59, 57, 70, 73, 71, 74, 72, 60, 63, 61, 64, 62, 25, 28, 26,
    29, 27, 40, 43, 41, 44, 42, 30, 33, 31, 34, 32, 45, 48, 46, 49, 47, 35, 38, 36, 39, 37, 0, 5,
    10, 15, 20, 3, 8, 13, 18, 23, 1, 6, 11, 16, 21, 4, 9, 14, 19, 24, 2, 7, 12, 17, 22, 75, 80, 85,
    90, 95, 78, 83, 88, 93, 98, 76, 81, 86, 91, 96, 79, 84, 89, 94, 99, 77, 82, 87, 92, 97, 25, 30,
    35, 40, 45, 28, 33, 38, 43, 48, 26, 31, 36, 41, 46, 29, 34, 39, 44, 49, 27, 32, 37, 42, 47,
    100, 105, 110, 115, 120, 103, 108, 113, 118, 123, 101, 106, 111, 116, 121, 104, 109, 114, 119,
    124, 102, 107, 112, 117, 122, 50, 55, 60, 65, 70, 53, 58, 63, 68, 73, 51, 56, 61, 66, 71, 54,
    59, 64, 69, 74, 52, 57, 62, 67, 72]

private theorem orbitData22 : orbitData ⟨2, 0, 2, 3⟩ = tab22 := by
  have h1 : (orbitData ⟨2, 0, 2, 3⟩).lookup = tab22.lookup := by
    decide +kernel
  have h2 : (orbitData ⟨2, 0, 2, 3⟩).reps = tab22.reps := by
    decide +kernel
  exact tables_ext h1 h2

private theorem tablesOKb22 : tablesOKb ⟨2, 0, 2, 3⟩ tab22 = true := by
  decide +kernel

private theorem g8b22 : g8b ⟨2, 0, 2, 3⟩ = true := by
  decide +kernel

private def cd223 : Cd := ⟨2, 0, 2, 3, orb22, rep22, gp22⟩

private def cert223 : List Op := [
    .bv 0, .bk 0, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .bv 1, .p1 1, .p1 1, .p1 1, .p1 1, .p1 1,
    .cl 0 5, .p1 2, .cl 0 5, .p1 1, .bk 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1,
    .cl 1 1, .cl 1 1, .p1 1, .p1 1, .cl 0 5, .p1 2, .cl 0 5, .cl 0 5, .p1 1, .cl 0 5, .cl 0 5,
    .cl 0 5, .p1 2, .p1 1, .p1 1, .cl 0 5, .p1 1, .cl 0 5, .cl 0 5, .cl 0 7, .p1 1, .cl 0 5, .p1 2,
    .cl 0 5, .cl 0 6, .cl 0 5, .p1 2, .cl 0 5, .cl 0 7, .cl 0 5, .cl 0 8, .p1 3, .cl 0 5, .cl 0 8,
    .p1 3, .cl 0 5, .cl 0 9, .p1 12, .cl 0 5, .cl 0 9, .p1 13, .cl 0 5, .cl 0 9, .p1 14, .cl 0 5,
    .cl 0 7, .p1 13, .cl 0 5, .cl 0 9, .cl 0 5, .cl 0 6, .cl 0 7, .p1 15, .cl 0 5, .cl 0 7, .p1 11,
    .cl 0 5, .cl 0 7, .p1 12, .cl 0 5, .cl 0 8, .cl 0 5, .cl 0 8, .p1 12, .cl 0 5, .cl 0 6,
    .cl 0 8, .cl 0 5, .cl 0 8, .cl 0 5, .cl 0 7, .cl 0 8, .cl 0 5, .cl 0 7, .p1 3, .cl 0 5,
    .cl 0 9, .p1 3, .cl 0 5, .cl 0 9, .p1 4, .cl 0 5, .cl 0 7, .cl 0 9, .cl 0 5, .cl 0 9, .p1 5,
    .p1 1, .cl 0 5, .p1 2, .cl 0 5, .cl 0 6, .cl 0 5, .p1 2, .cl 0 5, .cl 0 7, .cl 0 5, .cl 0 8,
    .p1 3, .cl 0 5, .cl 0 8, .p1 3, .cl 0 5, .cl 0 9, .p1 7, .cl 0 5, .cl 0 9, .p1 12, .cl 0 5,
    .cl 0 9, .p1 15, .cl 0 5, .cl 0 7, .p1 12, .cl 0 5, .cl 0 9, .cl 0 5, .cl 0 6, .cl 0 7, .p1 10,
    .cl 0 5, .cl 0 7, .p1 4, .cl 0 5, .cl 0 7, .p1 7, .cl 0 5, .cl 0 8, .cl 0 5, .cl 0 8, .p1 7,
    .cl 0 5, .cl 0 6, .cl 0 8, .cl 0 5, .cl 0 8, .cl 0 5, .cl 0 7, .cl 0 8, .cl 0 5, .cl 0 7,
    .p1 3, .cl 0 5, .cl 0 9, .p1 3, .cl 0 5, .cl 0 9, .p1 6, .cl 0 5, .cl 0 7, .cl 0 9, .cl 0 5,
    .cl 0 9, .p1 11, .p1 1, .cl 0 5, .p1 2, .cl 0 5, .cl 0 6, .cl 0 5, .p1 2, .cl 0 5, .cl 0 7,
    .cl 0 5, .cl 0 8, .p1 3, .cl 0 5, .cl 0 8, .p1 3, .cl 0 5, .cl 0 9, .p1 13, .cl 0 5, .cl 0 9,
    .p1 9, .cl 0 5, .cl 0 9, .p1 8, .cl 0 5, .cl 0 7, .p1 9, .cl 0 5, .cl 0 9, .cl 0 5, .cl 0 6,
    .cl 0 7, .p1 14, .cl 0 5, .cl 0 7, .p1 5, .cl 0 5, .cl 0 7, .p1 13, .cl 0 5, .cl 0 8, .cl 0 5,
    .cl 0 8, .p1 13, .cl 0 5, .cl 0 6, .cl 0 8, .cl 0 5, .cl 0 8, .cl 0 5, .cl 0 7, .cl 0 8,
    .cl 0 5, .cl 0 7, .p1 3, .cl 0 5, .cl 0 9, .p1 3, .cl 0 5, .cl 0 9, .p1 11, .cl 0 5, .cl 0 7,
    .cl 0 9, .cl 0 5, .cl 0 9, .p1 6, .p1 1, .cl 0 5, .p1 2, .cl 0 5, .cl 0 6, .cl 0 5, .p1 2,
    .cl 0 5, .cl 0 7, .cl 0 5, .cl 0 8, .p1 3, .cl 0 5, .cl 0 8, .p1 3, .cl 0 5, .cl 0 9, .p1 9,
    .cl 0 5, .cl 0 9, .p1 7, .cl 0 5, .cl 0 9, .p1 10, .cl 0 5, .cl 0 7, .p1 7, .cl 0 5, .cl 0 9,
    .cl 0 5, .cl 0 6, .cl 0 7, .p1 8, .cl 0 5, .cl 0 7, .p1 6, .cl 0 5, .cl 0 7, .p1 9, .cl 0 5,
    .cl 0 8, .cl 0 5, .cl 0 8, .p1 9, .cl 0 5, .cl 0 6, .cl 0 8, .cl 0 5, .cl 0 8, .cl 0 5,
    .cl 0 7, .cl 0 8, .cl 0 5, .cl 0 7, .p1 3, .cl 0 5, .cl 0 9, .p1 3, .cl 0 5, .cl 0 9, .p1 5,
    .cl 0 5, .cl 0 7, .cl 0 9, .cl 0 5, .cl 0 9, .p1 4, .cl 0 1, .cl 0 1, .cl 0 1, .bk 0, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .bv 1, .p1 1, .p1 1, .p1 1, .p1 1, .p1 1, .cl 0 5,
    .p1 2, .cl 0 5, .p1 1, .cl 0 5, .p1 1, .p1 1, .cl 0 5, .p1 2, .bk 1, .cl 1 1, .cl 1 1, .cl 1 1,
    .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 0 5, .p1 1, .cl 0 5, .cl 0 5, .cl 0 6, .p1 1,
    .p1 1, .cl 0 5, .p1 1, .cl 0 5, .cl 0 5, .p1 2, .p1 1, .cl 0 5, .p1 2, .cl 0 5, .p1 2, .cl 0 5,
    .cl 0 6, .cl 0 6, .p1 3, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 5,
    .cl 0 6, .cl 0 7, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 6, .p1 12,
    .cl 0 5, .cl 0 6, .p1 13, .cl 0 6, .p1 14, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 5, .cl 0 6,
    .cl 0 7, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 5, .cl 0 6, .cl 0 7,
    .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 6, .p1 3, .cl 0 5, .cl 0 6,
    .cl 0 7, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 5, .cl 0 6, .cl 0 7,
    .p1 1, .cl 0 5, .p1 2, .cl 0 5, .p1 2, .cl 0 5, .cl 0 6, .cl 0 6, .p1 3, .cl 0 5, .cl 0 6,
    .cl 0 7, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 5, .cl 0 6, .cl 0 7,
    .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 6, .p1 7, .cl 0 5, .cl 0 6, .p1 12, .cl 0 6, .p1 15, .cl 0 5,
    .cl 0 6, .cl 0 7, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 5, .cl 0 6,
    .cl 0 7, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 5, .cl 0 6, .cl 0 7,
    .cl 0 6, .p1 3, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 5, .cl 0 6,
    .cl 0 7, .cl 0 5, .cl 0 6, .cl 0 7, .p1 1, .cl 0 5, .p1 2, .cl 0 5, .p1 2, .cl 0 5, .cl 0 6,
    .cl 0 6, .p1 3, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 5, .cl 0 6,
    .cl 0 7, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 6, .p1 13, .cl 0 5,
    .cl 0 6, .p1 9, .cl 0 6, .p1 8, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 5,
    .cl 0 6, .cl 0 7, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 5, .cl 0 6,
    .cl 0 7, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 6, .p1 3, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 5,
    .cl 0 6, .cl 0 7, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 5, .cl 0 6, .cl 0 7, .p1 1, .cl 0 5, .p1 2,
    .cl 0 5, .p1 2, .cl 0 5, .cl 0 6, .cl 0 6, .p1 3, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 5, .cl 0 6,
    .cl 0 7, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 5, .cl 0 6, .cl 0 7,
    .cl 0 6, .p1 9, .cl 0 5, .cl 0 6, .p1 7, .cl 0 6, .p1 10, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 5,
    .cl 0 6, .cl 0 7, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 5, .cl 0 6,
    .cl 0 7, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 6, .p1 3, .cl 0 5,
    .cl 0 6, .cl 0 7, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 5, .cl 0 6,
    .cl 0 7, .cl 0 1, .bk 0, .cl 0 1, .cl 0 1, .bv 1, .p1 1, .p1 1, .p1 1, .p1 1, .p1 1, .cl 0 5,
    .p1 2, .cl 0 5, .p1 1, .cl 0 5, .p1 1, .p1 1, .cl 0 5, .p1 2, .cl 0 5, .cl 0 5, .p1 1, .cl 0 5,
    .bk 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 0 5,
    .cl 0 6, .p1 1, .p1 1, .cl 0 5, .p1 1, .cl 0 5, .cl 0 5, .p1 2, .p1 1, .cl 0 5, .cl 0 7, .p1 6,
    .cl 0 5, .cl 0 6, .cl 0 5, .cl 0 7, .p1 8, .cl 0 5, .cl 0 6, .p1 3, .cl 0 5, .cl 0 6, .p1 7,
    .cl 0 5, .cl 0 7, .p1 11, .cl 0 5, .cl 0 6, .p1 9, .cl 0 5, .cl 0 7, .p1 13, .cl 0 5, .cl 0 7,
    .p1 14, .cl 0 5, .p1 2, .cl 0 5, .cl 0 7, .p1 11, .cl 0 5, .cl 0 6, .cl 0 5, .cl 0 7, .cl 0 5,
    .cl 0 7, .p1 13, .cl 0 5, .cl 0 6, .p1 15, .cl 0 5, .cl 0 7, .p1 6, .cl 0 5, .cl 0 7, .p1 10,
    .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 5, .cl 0 7, .p1 8, .cl 0 5, .p1 2, .cl 0 5, .cl 0 7, .p1 3,
    .cl 0 5, .cl 0 7, .p1 4, .cl 0 5, .cl 0 7, .cl 0 5, .cl 0 7, .p1 5, .p1 1, .cl 0 5, .cl 0 7,
    .p1 5, .cl 0 5, .cl 0 6, .cl 0 5, .cl 0 7, .p1 14, .cl 0 5, .cl 0 6, .p1 3, .cl 0 5, .cl 0 6,
    .p1 9, .cl 0 5, .cl 0 7, .p1 4, .cl 0 5, .cl 0 6, .p1 13, .cl 0 5, .cl 0 7, .p1 12, .cl 0 5,
    .cl 0 7, .p1 15, .cl 0 5, .p1 2, .cl 0 5, .cl 0 7, .p1 4, .cl 0 5, .cl 0 6, .cl 0 5, .cl 0 7,
    .cl 0 5, .cl 0 7, .p1 12, .cl 0 5, .cl 0 6, .p1 10, .cl 0 5, .cl 0 7, .p1 5, .cl 0 5, .cl 0 7,
    .p1 8, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 5, .cl 0 7, .p1 14, .cl 0 5, .p1 2, .cl 0 5, .cl 0 7,
    .p1 3, .cl 0 5, .cl 0 7, .p1 6, .cl 0 5, .cl 0 7, .cl 0 5, .cl 0 7, .p1 11, .p1 1, .cl 0 5,
    .cl 0 7, .p1 4, .cl 0 5, .cl 0 6, .cl 0 5, .cl 0 7, .p1 10, .cl 0 5, .cl 0 6, .p1 3, .cl 0 5,
    .cl 0 6, .p1 12, .cl 0 5, .cl 0 7, .p1 5, .cl 0 5, .cl 0 6, .p1 7, .cl 0 5, .cl 0 7, .p1 9,
    .cl 0 5, .cl 0 7, .p1 8, .cl 0 5, .p1 2, .cl 0 5, .cl 0 7, .p1 5, .cl 0 5, .cl 0 6, .cl 0 5,
    .cl 0 7, .cl 0 5, .cl 0 7, .p1 9, .cl 0 5, .cl 0 6, .p1 14, .cl 0 5, .cl 0 7, .p1 4, .cl 0 5,
    .cl 0 7, .p1 15, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 5, .cl 0 7, .p1 10, .cl 0 5, .p1 2, .cl 0 5,
    .cl 0 7, .p1 3, .cl 0 5, .cl 0 7, .p1 11, .cl 0 5, .cl 0 7, .cl 0 5, .cl 0 7, .p1 6, .p1 1,
    .cl 0 5, .cl 0 7, .p1 11, .cl 0 5, .cl 0 6, .cl 0 5, .cl 0 7, .p1 15, .cl 0 5, .cl 0 6, .p1 3,
    .cl 0 5, .cl 0 6, .p1 13, .cl 0 5, .cl 0 7, .p1 6, .cl 0 5, .cl 0 6, .p1 12, .cl 0 5, .cl 0 7,
    .p1 7, .cl 0 5, .cl 0 7, .p1 10, .cl 0 5, .p1 2, .cl 0 5, .cl 0 7, .p1 6, .cl 0 5, .cl 0 6,
    .cl 0 5, .cl 0 7, .cl 0 5, .cl 0 7, .p1 7, .cl 0 5, .cl 0 6, .p1 8, .cl 0 5, .cl 0 7, .p1 11,
    .cl 0 5, .cl 0 7, .p1 14, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 5, .cl 0 7, .p1 15, .cl 0 5, .p1 2,
    .cl 0 5, .cl 0 7, .p1 3, .cl 0 5, .cl 0 7, .p1 5, .cl 0 5, .cl 0 7, .cl 0 5, .cl 0 7, .p1 4,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .bk 0, .bv 1, .p1 1, .p1 1, .p1 1, .p1 1, .p1 1,
    .cl 0 5, .p1 2, .cl 0 5, .p1 1, .cl 0 5, .p1 1, .p1 1, .cl 0 5, .p1 2, .cl 0 5, .cl 0 5, .p1 1,
    .cl 0 5, .cl 0 5, .cl 0 5, .p1 2, .p1 1, .p1 1, .bk 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1,
    .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .p1 1, .cl 0 5, .cl 0 6, .p1 1, .cl 0 5, .cl 0 6, .p1 5,
    .cl 0 6, .cl 0 5, .cl 0 6, .p1 4, .cl 0 6, .p1 3, .cl 0 5, .p1 2, .cl 0 5, .cl 0 6, .p1 8,
    .cl 0 5, .cl 0 6, .cl 0 5, .cl 0 6, .p1 10, .cl 0 5, .cl 0 6, .p1 6, .cl 0 5, .p1 2, .cl 0 5,
    .cl 0 6, .p1 13, .cl 0 5, .cl 0 6, .p1 14, .cl 0 5, .cl 0 6, .p1 15, .cl 0 5, .cl 0 6, .p1 11,
    .cl 0 5, .cl 0 6, .p1 15, .cl 0 5, .cl 0 6, .p1 14, .cl 0 5, .cl 0 6, .p1 13, .cl 0 5, .cl 0 6,
    .p1 12, .cl 0 5, .cl 0 6, .p1 11, .cl 0 5, .cl 0 6, .p1 10, .cl 0 5, .cl 0 6, .p1 9, .cl 0 5,
    .cl 0 6, .p1 8, .cl 0 5, .cl 0 6, .p1 7, .cl 0 5, .cl 0 6, .p1 6, .p1 1, .cl 0 5, .cl 0 6,
    .p1 11, .cl 0 6, .cl 0 5, .cl 0 6, .p1 6, .cl 0 6, .p1 3, .cl 0 5, .p1 2, .cl 0 5, .cl 0 6,
    .p1 14, .cl 0 5, .cl 0 6, .cl 0 5, .cl 0 6, .p1 8, .cl 0 5, .cl 0 6, .p1 5, .cl 0 5, .p1 2,
    .cl 0 5, .cl 0 6, .p1 12, .cl 0 5, .cl 0 6, .p1 15, .cl 0 5, .cl 0 6, .p1 10, .cl 0 5, .cl 0 6,
    .p1 4, .cl 0 5, .cl 0 6, .p1 10, .cl 0 5, .cl 0 6, .p1 15, .cl 0 5, .cl 0 6, .p1 12, .cl 0 5,
    .cl 0 6, .p1 7, .cl 0 5, .cl 0 6, .p1 4, .cl 0 5, .cl 0 6, .p1 8, .cl 0 5, .cl 0 6, .p1 13,
    .cl 0 5, .cl 0 6, .p1 14, .cl 0 5, .cl 0 6, .p1 9, .cl 0 5, .cl 0 6, .p1 5, .p1 1, .cl 0 5,
    .cl 0 6, .p1 6, .cl 0 6, .cl 0 5, .cl 0 6, .p1 11, .cl 0 6, .p1 3, .cl 0 5, .p1 2, .cl 0 5,
    .cl 0 6, .p1 10, .cl 0 5, .cl 0 6, .cl 0 5, .cl 0 6, .p1 15, .cl 0 5, .cl 0 6, .p1 4, .cl 0 5,
    .p1 2, .cl 0 5, .cl 0 6, .p1 9, .cl 0 5, .cl 0 6, .p1 8, .cl 0 5, .cl 0 6, .p1 14, .cl 0 5,
    .cl 0 6, .p1 5, .cl 0 5, .cl 0 6, .p1 14, .cl 0 5, .cl 0 6, .p1 8, .cl 0 5, .cl 0 6, .p1 9,
    .cl 0 5, .cl 0 6, .p1 13, .cl 0 5, .cl 0 6, .p1 5, .cl 0 5, .cl 0 6, .p1 15, .cl 0 5, .cl 0 6,
    .p1 7, .cl 0 5, .cl 0 6, .p1 10, .cl 0 5, .cl 0 6, .p1 12, .cl 0 5, .cl 0 6, .p1 4, .p1 1,
    .cl 0 5, .cl 0 6, .p1 4, .cl 0 6, .cl 0 5, .cl 0 6, .p1 5, .cl 0 6, .p1 3, .cl 0 5, .p1 2,
    .cl 0 5, .cl 0 6, .p1 15, .cl 0 5, .cl 0 6, .cl 0 5, .cl 0 6, .p1 14, .cl 0 5, .cl 0 6, .p1 11,
    .cl 0 5, .p1 2, .cl 0 5, .cl 0 6, .p1 7, .cl 0 5, .cl 0 6, .p1 10, .cl 0 5, .cl 0 6, .p1 8,
    .cl 0 5, .cl 0 6, .p1 6, .cl 0 5, .cl 0 6, .p1 8, .cl 0 5, .cl 0 6, .p1 10, .cl 0 5, .cl 0 6,
    .p1 7, .cl 0 5, .cl 0 6, .p1 9, .cl 0 5, .cl 0 6, .p1 6, .cl 0 5, .cl 0 6, .p1 14, .cl 0 5,
    .cl 0 6, .p1 12, .cl 0 5, .cl 0 6, .p1 15, .cl 0 5, .cl 0 6, .p1 13, .cl 0 5, .cl 0 6, .p1 11,
    .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .p1 0, .bk 0, .cl 0 2, .cl 0 2,
    .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 4, .bk 0, .cl 0 2, .cl 0 2, .cl 0 2,
    .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .bk 0, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2,
    .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .bk 0, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .p1 0, .bk 0, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .bk 0, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3,
    .cl 0 3, .bk 0, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .bk 0,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .p1 0, .bk 0, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .bk 0, .cl 0 3, .cl 0 3,
    .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .bk 0, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 1, .bk 0, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .p1 0, .bk 0, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 4, .cl 0 2,
    .cl 0 2, .cl 0 2, .cl 0 2, .bk 0, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2,
    .cl 0 2, .cl 0 2, .bk 0, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2,
    .cl 0 2, .bk 0, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .p1 0,
    .bk 0, .cl 0 1, .p1 5, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2,
    .cl 0 1, .cl 0 2, .cl 0 1, .p1 3, .cl 0 1, .cl 0 2, .bk 0, .cl 0 1, .cl 0 2, .cl 0 1, .p1 4,
    .cl 0 1, .cl 0 2, .cl 0 1, .p1 4, .cl 0 1, .cl 0 2, .cl 0 1, .p1 4, .cl 0 1, .cl 0 4, .cl 0 1,
    .p1 4, .bk 0, .cl 0 1, .p1 3, .cl 0 1, .cl 0 3, .cl 0 1, .p1 4, .cl 0 1, .cl 0 3, .cl 0 1,
    .cl 0 3, .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3, .bk 0, .cl 0 2, .cl 0 3,
    .cl 0 2, .p1 5, .cl 0 2, .cl 0 4, .cl 0 2, .p1 5, .cl 0 2, .cl 0 3, .cl 0 2, .p1 5, .cl 0 2,
    .cl 0 3, .cl 0 2, .p1 5, .bk 0, .cl 0 5, .p1 3, .cl 0 5, .p1 3, .cl 0 5, .p1 3, .cl 0 5, .p1 3,
    .cl 0 5, .p1 3, .cl 0 10, .cl 0 5, .p1 3, .cl 0 5, .p1 3, .bk 0, .cl 0 31, .cl 0 33, .p1 2,
    .cl 0 31, .cl 0 33, .cl 0 45, .cl 0 31, .cl 0 47, .p1 2, .cl 0 31, .cl 0 47, .cl 0 31,
    .cl 0 33, .cl 0 35, .cl 0 31, .cl 0 47, .cl 0 31, .cl 0 56, .cl 0 58, .p1 15, .cl 0 31,
    .cl 0 33, .cl 0 37, .bk 0, .cl 0 32, .cl 0 38, .cl 0 42, .cl 0 32, .cl 0 38, .cl 0 42,
    .cl 0 32, .cl 0 38, .cl 0 32, .cl 0 38, .cl 0 32, .cl 0 38, .cl 0 32, .cl 0 38, .p1 1,
    .cl 0 32, .cl 0 38, .cl 0 42, .cl 0 32, .cl 0 38, .bk 0, .cl 0 33, .cl 0 37, .cl 0 33,
    .cl 0 37, .cl 0 43, .cl 0 33, .cl 0 37, .cl 0 38, .cl 0 33, .cl 0 37, .cl 0 33, .cl 0 37,
    .cl 0 43, .cl 0 33, .cl 0 37, .p1 2, .cl 0 33, .cl 0 37, .cl 0 33, .cl 0 37, .bk 0, .cl 0 34,
    .cl 0 48, .cl 0 34, .cl 0 48, .cl 0 59, .cl 0 60, .cl 0 34, .cl 0 48, .cl 0 59, .cl 0 63,
    .cl 0 34, .cl 0 48, .cl 0 34, .cl 0 48, .cl 0 34, .cl 0 48, .cl 0 34, .cl 0 48, .p1 1,
    .cl 0 34, .cl 0 48, .cl 0 56, .cl 0 58, .p1 15, .bk 0, .cl 0 10, .p1 3, .cl 0 10, .p1 3,
    .cl 0 10, .p1 3, .cl 0 10, .p1 3, .cl 0 10, .p1 3, .cl 0 10, .p1 3, .cl 0 10, .p1 3, .cl 0 20,
    .bk 0, .cl 0 36, .cl 0 49, .cl 0 36, .cl 0 49, .cl 0 36, .cl 0 49, .cl 0 36, .cl 0 49,
    .cl 0 58, .cl 0 36, .cl 0 49, .cl 0 61, .p1 9, .cl 0 36, .cl 0 49, .cl 0 36, .cl 0 49,
    .cl 0 52, .cl 0 56, .cl 0 36, .cl 0 49, .p1 2, .bk 0, .cl 0 37, .cl 0 44, .cl 0 47, .cl 0 37,
    .cl 0 44, .cl 0 58, .p1 11, .cl 0 37, .cl 0 44, .cl 0 37, .cl 0 44, .cl 0 55, .cl 0 57, .p1 6,
    .cl 0 37, .cl 0 44, .p1 2, .cl 0 37, .cl 0 44, .cl 0 37, .cl 0 44, .cl 0 37, .cl 0 44, .bk 0,
    .cl 0 38, .cl 0 41, .p1 1, .cl 0 38, .cl 0 39, .cl 0 41, .cl 0 38, .cl 0 41, .cl 0 38,
    .cl 0 39, .cl 0 40, .cl 0 38, .cl 0 41, .cl 0 48, .cl 0 38, .cl 0 41, .cl 0 38, .cl 0 39,
    .p1 1, .cl 0 38, .cl 0 41, .bk 0, .cl 0 39, .cl 0 46, .cl 0 49, .cl 0 39, .cl 0 46, .cl 0 39,
    .cl 0 46, .cl 0 52, .cl 0 56, .cl 0 39, .cl 0 46, .cl 0 57, .cl 0 39, .cl 0 46, .cl 0 39,
    .cl 0 46, .cl 0 39, .cl 0 46, .cl 0 39, .cl 0 46, .p1 1, .bk 0, .cl 0 5, .cl 0 5, .cl 0 5,
    .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .bk 0, .cl 0 41, .cl 0 64, .p1 3, .cl 0 41,
    .cl 0 46, .p1 1, .cl 0 41, .cl 0 63, .p1 4, .cl 0 41, .cl 0 63, .p1 4, .cl 0 41, .cl 0 46,
    .cl 0 48, .cl 0 41, .cl 0 46, .cl 0 55, .cl 0 41, .cl 0 46, .cl 0 60, .cl 0 41, .cl 0 63,
    .cl 0 66, .cl 0 71, .cl 0 72, .bk 0, .cl 0 42, .cl 0 67, .cl 0 73, .cl 0 76, .p1 6, .cl 0 42,
    .cl 0 63, .p1 3, .cl 0 42, .cl 0 67, .cl 0 79, .p1 7, .cl 0 42, .cl 0 73, .p1 11, .cl 0 42,
    .cl 0 63, .p1 3, .cl 0 42, .cl 0 63, .p1 3, .cl 0 42, .cl 0 63, .p1 3, .cl 0 42, .cl 0 73,
    .cl 0 76, .cl 0 81, .p1 9, .bk 0, .cl 0 43, .cl 0 62, .p1 3, .cl 0 43, .cl 0 62, .p1 3,
    .cl 0 43, .cl 0 44, .cl 0 45, .cl 0 43, .cl 0 72, .p1 11, .cl 0 43, .cl 0 68, .cl 0 69, .p1 8,
    .cl 0 43, .cl 0 44, .cl 0 49, .cl 0 43, .cl 0 44, .p1 2, .cl 0 43, .cl 0 44, .cl 0 52, .bk 0,
    .cl 0 44, .cl 0 49, .cl 0 56, .p1 6, .cl 0 44, .cl 0 49, .p1 2, .cl 0 44, .cl 0 49, .cl 0 60,
    .cl 0 44, .cl 0 61, .p1 3, .cl 0 44, .cl 0 61, .p1 3, .cl 0 44, .cl 0 49, .cl 0 55, .cl 0 44,
    .cl 0 62, .p1 4, .cl 0 44, .cl 0 62, .cl 0 72, .bk 0, .cl 0 15, .cl 0 15, .cl 0 15, .cl 0 15,
    .cl 0 15, .cl 0 15, .cl 0 15, .cl 0 15, .bk 0, .cl 0 46, .cl 0 48, .p1 1, .cl 0 46, .cl 0 64,
    .p1 6, .cl 0 46, .cl 0 59, .p1 3, .cl 0 46, .cl 0 48, .cl 0 57, .p1 5, .cl 0 46, .cl 0 48,
    .cl 0 52, .cl 0 46, .cl 0 48, .cl 0 51, .p1 3, .cl 0 46, .cl 0 71, .cl 0 73, .p1 12, .cl 0 46,
    .cl 0 59, .p1 3, .bk 0, .cl 0 47, .cl 0 56, .cl 0 58, .p1 3, .cl 0 47, .cl 0 56, .p1 5,
    .cl 0 47, .cl 0 58, .p1 3, .cl 0 47, .cl 0 56, .p1 3, .cl 0 47, .cl 0 56, .p1 5, .cl 0 47,
    .cl 0 56, .cl 0 61, .cl 0 47, .cl 0 58, .p1 3, .cl 0 47, .cl 0 56, .cl 0 68, .p1 11, .bk 0,
    .cl 0 48, .cl 0 59, .p1 5, .cl 0 48, .cl 0 57, .p1 3, .cl 0 48, .cl 0 57, .p1 3, .cl 0 48,
    .cl 0 57, .p1 3, .cl 0 48, .cl 0 59, .cl 0 70, .p1 3, .cl 0 48, .cl 0 59, .cl 0 64, .cl 0 48,
    .cl 0 57, .p1 3, .cl 0 48, .cl 0 59, .cl 0 67, .p1 11, .bk 0, .cl 0 49, .cl 0 56, .p1 3,
    .cl 0 49, .cl 0 61, .p1 6, .cl 0 49, .cl 0 61, .cl 0 62, .cl 0 49, .cl 0 56, .p1 3, .cl 0 49,
    .cl 0 61, .cl 0 78, .p1 14, .cl 0 49, .cl 0 61, .cl 0 69, .p1 14, .cl 0 49, .cl 0 56, .p1 3,
    .cl 0 49, .cl 0 56, .p1 3, .p1 0, .bk 0, .cl 0 1, .p1 11, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2,
    .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .p1 3, .cl 0 1, .cl 0 2, .bk 0,
    .cl 0 1, .cl 0 2, .cl 0 1, .p1 6, .cl 0 1, .cl 0 2, .cl 0 1, .p1 6, .cl 0 1, .cl 0 2, .cl 0 1,
    .p1 6, .cl 0 1, .cl 0 4, .cl 0 1, .p1 6, .bk 0, .cl 0 1, .p1 3, .cl 0 1, .cl 0 3, .cl 0 1,
    .p1 6, .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3, .cl 0 1,
    .cl 0 3, .bk 0, .cl 0 2, .cl 0 3, .cl 0 2, .p1 11, .cl 0 2, .cl 0 4, .cl 0 2, .p1 11, .cl 0 2,
    .cl 0 3, .cl 0 2, .p1 11, .cl 0 2, .cl 0 3, .cl 0 2, .p1 11, .bk 0, .cl 0 5, .p1 3, .cl 0 5,
    .p1 3, .cl 0 5, .p1 3, .cl 0 5, .p1 3, .cl 0 5, .p1 3, .cl 0 10, .cl 0 5, .p1 3, .cl 0 5,
    .p1 3, .bk 0, .cl 0 56, .cl 0 58, .p1 2, .cl 0 56, .cl 0 58, .cl 0 70, .cl 0 56, .cl 0 72,
    .p1 2, .cl 0 56, .cl 0 72, .cl 0 56, .cl 0 58, .cl 0 60, .cl 0 56, .cl 0 72, .cl 0 56,
    .cl 0 72, .cl 0 83, .p1 15, .cl 0 56, .cl 0 58, .cl 0 62, .bk 0, .cl 0 57, .cl 0 63, .cl 0 67,
    .cl 0 57, .cl 0 63, .cl 0 67, .cl 0 57, .cl 0 63, .cl 0 57, .cl 0 63, .cl 0 57, .cl 0 63,
    .cl 0 57, .cl 0 63, .p1 1, .cl 0 57, .cl 0 63, .cl 0 67, .cl 0 57, .cl 0 63, .bk 0, .cl 0 58,
    .cl 0 62, .cl 0 58, .cl 0 62, .cl 0 68, .cl 0 58, .cl 0 62, .cl 0 63, .cl 0 58, .cl 0 62,
    .cl 0 58, .cl 0 62, .cl 0 68, .cl 0 58, .cl 0 62, .p1 2, .cl 0 58, .cl 0 62, .cl 0 58,
    .cl 0 62, .bk 0, .cl 0 59, .cl 0 73, .cl 0 59, .cl 0 73, .cl 0 77, .p1 3, .cl 0 59, .cl 0 73,
    .cl 0 82, .p1 12, .cl 0 59, .cl 0 73, .cl 0 59, .cl 0 73, .cl 0 59, .cl 0 73, .cl 0 59,
    .cl 0 73, .p1 1, .cl 0 59, .cl 0 88, .bk 0, .cl 0 10, .p1 3, .cl 0 10, .p1 3, .cl 0 10, .p1 3,
    .cl 0 10, .p1 3, .cl 0 10, .p1 3, .cl 0 10, .p1 3, .cl 0 10, .p1 3, .cl 0 20, .bk 0, .cl 0 61,
    .cl 0 74, .cl 0 61, .cl 0 74, .cl 0 61, .cl 0 74, .cl 0 61, .cl 0 74, .cl 0 81, .p1 14,
    .cl 0 61, .cl 0 74, .cl 0 87, .cl 0 61, .cl 0 74, .cl 0 61, .cl 0 74, .cl 0 80, .p1 3,
    .cl 0 61, .cl 0 74, .p1 2, .bk 0, .cl 0 62, .cl 0 69, .cl 0 72, .cl 0 81, .p1 13, .cl 0 62,
    .cl 0 69, .cl 0 62, .cl 0 69, .cl 0 76, .p1 3, .cl 0 62, .cl 0 69, .p1 2, .cl 0 62, .cl 0 69,
    .cl 0 62, .cl 0 69, .cl 0 62, .cl 0 69, .bk 0, .cl 0 63, .cl 0 66, .p1 1, .cl 0 63, .cl 0 64,
    .cl 0 66, .cl 0 63, .cl 0 66, .cl 0 63, .cl 0 64, .cl 0 65, .cl 0 63, .cl 0 66, .cl 0 73,
    .cl 0 63, .cl 0 66, .cl 0 63, .cl 0 64, .p1 1, .cl 0 63, .cl 0 66, .bk 0, .cl 0 64, .cl 0 71,
    .cl 0 74, .cl 0 64, .cl 0 71, .cl 0 64, .cl 0 71, .cl 0 80, .p1 3, .cl 0 64, .cl 0 71,
    .cl 0 82, .cl 0 64, .cl 0 71, .cl 0 64, .cl 0 71, .cl 0 64, .cl 0 71, .cl 0 64, .cl 0 71,
    .p1 1, .bk 0, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .bk 0,
    .cl 0 66, .cl 0 88, .cl 0 95, .p1 12, .cl 0 66, .cl 0 71, .p1 1, .cl 0 66, .cl 0 92, .cl 0 93,
    .p1 12, .cl 0 66, .cl 0 82, .cl 0 66, .cl 0 71, .cl 0 73, .cl 0 66, .cl 0 71, .cl 0 79,
    .cl 0 66, .cl 0 71, .cl 0 77, .cl 0 78, .cl 0 81, .cl 0 66, .cl 0 82, .bk 0, .cl 0 67,
    .cl 0 82, .cl 0 92, .cl 0 67, .cl 0 84, .cl 0 96, .cl 0 121, .cl 0 67, .cl 0 84, .cl 0 67,
    .cl 0 82, .cl 0 85, .cl 0 67, .cl 0 84, .cl 0 67, .cl 0 113, .p1 3, .cl 0 67, .cl 0 84, .bk 0,
    .cl 0 68, .cl 0 83, .cl 0 85, .cl 0 68, .cl 0 81, .cl 0 68, .cl 0 69, .cl 0 70, .cl 0 68,
    .cl 0 81, .cl 0 68, .cl 0 83, .cl 0 93, .cl 0 68, .cl 0 69, .cl 0 74, .cl 0 68, .cl 0 69,
    .p1 2, .cl 0 68, .cl 0 81, .bk 0, .cl 0 69, .cl 0 74, .cl 0 86, .p1 3, .cl 0 69, .cl 0 74,
    .p1 2, .cl 0 69, .cl 0 74, .cl 0 77, .cl 0 78, .cl 0 84, .cl 0 69, .cl 0 83, .cl 0 69,
    .cl 0 87, .cl 0 95, .p1 15, .cl 0 69, .cl 0 74, .cl 0 76, .cl 0 69, .cl 0 93, .cl 0 97,
    .cl 0 69, .cl 0 83, .bk 0, .cl 0 15, .cl 0 15, .cl 0 15, .cl 0 15, .cl 0 15, .cl 0 15,
    .cl 0 15, .cl 0 15, .bk 0, .cl 0 71, .cl 0 73, .p1 1, .cl 0 88, .p1 10, .cl 0 71, .cl 0 89,
    .p1 3, .cl 0 71, .cl 0 73, .cl 0 84, .p1 3, .cl 0 71, .cl 0 73, .cl 0 80, .cl 0 88, .p1 10,
    .cl 0 71, .cl 0 89, .cl 0 91, .cl 0 95, .p1 3, .cl 0 88, .p1 10, .bk 0, .cl 0 72, .cl 0 81,
    .p1 5, .cl 0 72, .cl 0 81, .p1 3, .cl 0 72, .cl 0 81, .cl 0 85, .p1 8, .cl 0 86, .p1 9,
    .cl 0 72, .cl 0 86, .cl 0 99, .p1 15, .cl 0 86, .p1 9, .cl 0 72, .cl 0 86, .cl 0 87, .p1 10,
    .cl 0 86, .p1 9, .bk 0, .cl 0 73, .cl 0 89, .cl 0 96, .p1 12, .cl 0 73, .cl 0 84, .p1 3,
    .cl 0 73, .cl 0 96, .cl 0 99, .cl 0 89, .p1 8, .cl 0 73, .cl 0 84, .p1 5, .cl 0 89, .p1 8,
    .cl 0 73, .cl 0 84, .cl 0 85, .p1 9, .cl 0 89, .p1 8, .bk 0, .cl 0 74, .cl 0 106, .p1 3,
    .cl 0 87, .p1 7, .cl 0 74, .cl 0 86, .cl 0 94, .cl 0 95, .p1 3, .cl 0 87, .p1 7, .cl 0 87,
    .cl 0 112, .cl 0 74, .cl 0 86, .p1 6, .cl 0 74, .cl 0 86, .p1 3, .cl 0 87, .p1 7, .p1 0, .bk 0,
    .cl 0 1, .p1 6, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2,
    .cl 0 1, .cl 0 2, .cl 0 1, .p1 3, .cl 0 1, .cl 0 2, .bk 0, .cl 0 1, .cl 0 2, .cl 0 1, .p1 11,
    .cl 0 1, .cl 0 2, .cl 0 1, .p1 11, .cl 0 1, .cl 0 2, .cl 0 1, .p1 11, .cl 0 1, .cl 0 4,
    .cl 0 1, .p1 11, .bk 0, .cl 0 1, .p1 3, .cl 0 1, .cl 0 3, .cl 0 1, .p1 11, .cl 0 1, .cl 0 3,
    .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3, .bk 0, .cl 0 2,
    .cl 0 3, .cl 0 2, .p1 6, .cl 0 2, .cl 0 4, .cl 0 2, .p1 6, .cl 0 2, .cl 0 3, .cl 0 2, .p1 6,
    .cl 0 2, .cl 0 3, .cl 0 2, .p1 6, .bk 0, .cl 0 5, .p1 3, .cl 0 5, .p1 3, .cl 0 5, .p1 3,
    .cl 0 5, .p1 3, .cl 0 5, .p1 3, .cl 0 10, .cl 0 5, .p1 3, .cl 0 5, .p1 3, .bk 0, .cl 0 62,
    .cl 0 83, .p1 2, .cl 0 68, .p1 13, .cl 0 62, .cl 0 69, .p1 3, .cl 0 68, .p1 13, .cl 0 62,
    .cl 0 83, .cl 0 85, .cl 0 68, .p1 13, .cl 0 62, .cl 0 69, .cl 0 70, .cl 0 73, .cl 0 76, .p1 2,
    .cl 0 68, .p1 13, .bk 0, .cl 0 64, .cl 0 71, .p1 4, .cl 0 66, .p1 15, .cl 0 64, .cl 0 71,
    .cl 0 77, .p1 3, .cl 0 66, .p1 15, .cl 0 64, .cl 0 66, .cl 0 84, .p1 1, .cl 0 66, .p1 15,
    .cl 0 64, .cl 0 66, .cl 0 67, .p1 13, .cl 0 66, .p1 15, .bk 0, .cl 0 61, .cl 0 69, .cl 0 81,
    .p1 2, .cl 0 69, .p1 12, .cl 0 61, .cl 0 87, .cl 0 88, .cl 0 69, .p1 12, .cl 0 61, .cl 0 74,
    .p1 4, .cl 0 69, .p1 12, .cl 0 61, .cl 0 74, .cl 0 77, .p1 5, .cl 0 69, .p1 12, .bk 0,
    .cl 0 63, .cl 0 82, .cl 0 85, .cl 0 63, .cl 0 64, .cl 0 67, .cl 0 63, .cl 0 64, .cl 0 69,
    .cl 0 67, .p1 14, .cl 0 63, .cl 0 82, .p1 1, .cl 0 63, .cl 0 66, .p1 11, .cl 0 63, .cl 0 66,
    .p1 3, .cl 0 67, .p1 14, .bk 0, .cl 0 10, .p1 3, .cl 0 10, .p1 3, .cl 0 10, .p1 3, .cl 0 10,
    .p1 3, .cl 0 10, .p1 3, .cl 0 10, .p1 3, .cl 0 10, .p1 3, .cl 0 20, .bk 0, .cl 0 58, .cl 0 72,
    .cl 0 74, .p1 11, .cl 0 58, .p1 9, .cl 0 58, .cl 0 72, .cl 0 87, .p1 2, .cl 0 58, .p1 9,
    .cl 0 72, .cl 0 81, .cl 0 83, .cl 0 58, .p1 9, .cl 0 58, .cl 0 72, .cl 0 81, .cl 0 87, .p1 8,
    .cl 0 58, .p1 9, .bk 0, .cl 0 56, .cl 0 74, .cl 0 83, .cl 0 91, .p1 15, .cl 0 56, .p1 7,
    .cl 0 74, .cl 0 86, .p1 2, .cl 0 56, .p1 7, .cl 0 74, .cl 0 94, .p1 2, .cl 0 56, .p1 7,
    .cl 0 74, .cl 0 94, .cl 0 56, .p1 7, .bk 0, .cl 0 59, .cl 0 71, .cl 0 82, .cl 0 84, .cl 0 59,
    .p1 10, .cl 0 71, .cl 0 91, .cl 0 59, .p1 10, .cl 0 59, .cl 0 71, .cl 0 73, .cl 0 82, .p1 4,
    .cl 0 59, .p1 10, .cl 0 59, .cl 0 71, .cl 0 82, .cl 0 83, .p1 15, .cl 0 59, .p1 10, .bk 0,
    .cl 0 57, .cl 0 59, .cl 0 73, .cl 0 57, .p1 8, .cl 0 57, .cl 0 73, .cl 0 84, .cl 0 88, .p1 9,
    .cl 0 57, .p1 8, .cl 0 57, .cl 0 71, .cl 0 73, .cl 0 57, .p1 8, .cl 0 57, .cl 0 73, .cl 0 88,
    .p1 1, .cl 0 57, .p1 8, .bk 0, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5,
    .cl 0 5, .bk 0, .cl 0 57, .cl 0 63, .cl 0 70, .p1 9, .cl 0 73, .p1 8, .cl 0 57, .cl 0 67,
    .cl 0 68, .p1 9, .cl 0 57, .cl 0 67, .cl 0 68, .cl 0 57, .cl 0 67, .cl 0 68, .cl 0 73, .p1 8,
    .cl 0 57, .cl 0 63, .p1 5, .cl 0 57, .cl 0 63, .p1 3, .bk 0, .cl 0 59, .cl 0 73, .cl 0 78,
    .p1 15, .cl 0 71, .p1 10, .cl 0 59, .cl 0 89, .cl 0 71, .p1 10, .cl 0 59, .cl 0 73, .p1 3,
    .cl 0 71, .p1 10, .cl 0 59, .cl 0 89, .cl 0 71, .p1 10, .bk 0, .cl 0 56, .cl 0 58, .cl 0 60,
    .cl 0 56, .cl 0 58, .cl 0 73, .cl 0 56, .cl 0 86, .cl 0 56, .cl 0 72, .p1 6, .cl 0 56,
    .cl 0 58, .cl 0 68, .cl 0 74, .p1 7, .cl 0 56, .cl 0 86, .cl 0 56, .cl 0 58, .cl 0 73, .p1 10,
    .bk 0, .cl 0 58, .cl 0 72, .cl 0 74, .p1 10, .cl 0 72, .p1 9, .cl 0 58, .cl 0 62, .p1 5,
    .cl 0 58, .cl 0 68, .cl 0 69, .p1 10, .cl 0 58, .cl 0 62, .cl 0 70, .p1 8, .cl 0 72, .p1 9,
    .cl 0 58, .cl 0 68, .cl 0 72, .cl 0 58, .cl 0 62, .p1 3, .bk 0, .cl 0 15, .cl 0 15, .cl 0 15,
    .cl 0 15, .cl 0 15, .cl 0 15, .cl 0 15, .cl 0 15, .bk 0, .cl 0 67, .cl 0 82, .cl 0 63, .p1 14,
    .cl 0 67, .cl 0 82, .p1 1, .cl 0 63, .p1 14, .cl 0 67, .cl 0 82, .cl 0 63, .p1 14, .cl 0 63,
    .cl 0 67, .cl 0 82, .p1 1, .cl 0 63, .p1 14, .bk 0, .cl 0 61, .cl 0 81, .cl 0 61, .p1 12,
    .cl 0 61, .cl 0 68, .cl 0 69, .cl 0 61, .p1 12, .cl 0 61, .cl 0 69, .cl 0 74, .p1 8, .cl 0 61,
    .p1 12, .cl 0 61, .cl 0 62, .cl 0 69, .cl 0 61, .p1 12, .bk 0, .cl 0 64, .cl 0 66, .cl 0 71,
    .p1 9, .cl 0 64, .p1 15, .cl 0 66, .cl 0 71, .cl 0 74, .cl 0 64, .p1 15, .cl 0 64, .cl 0 84,
    .cl 0 64, .p1 15, .cl 0 64, .cl 0 66, .cl 0 67, .p1 6, .cl 0 64, .p1 15, .bk 0, .cl 0 68,
    .cl 0 83, .cl 0 62, .p1 13, .cl 0 68, .cl 0 69, .cl 0 74, .cl 0 62, .p1 13, .cl 0 68, .cl 0 83,
    .cl 0 62, .p1 13, .cl 0 68, .cl 0 69, .cl 0 70, .cl 0 74, .p1 15, .cl 0 62, .p1 13, .p1 0,
    .bk 0, .cl 0 1, .p1 4, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2,
    .cl 0 1, .cl 0 2, .cl 0 1, .p1 3, .cl 0 1, .cl 0 2, .bk 0, .cl 0 1, .cl 0 2, .cl 0 1, .p1 5,
    .cl 0 1, .cl 0 2, .cl 0 1, .p1 5, .cl 0 1, .cl 0 2, .cl 0 1, .p1 5, .cl 0 1, .cl 0 4, .cl 0 1,
    .p1 5, .bk 0, .cl 0 1, .p1 3, .cl 0 1, .cl 0 3, .cl 0 1, .p1 5, .cl 0 1, .cl 0 3, .cl 0 1,
    .cl 0 3, .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3, .bk 0, .cl 0 2, .cl 0 3,
    .cl 0 2, .p1 4, .cl 0 2, .cl 0 4, .cl 0 2, .p1 4, .cl 0 2, .cl 0 3, .cl 0 2, .p1 4, .cl 0 2,
    .cl 0 3, .cl 0 2, .p1 4, .bk 0, .cl 0 5, .p1 3, .cl 0 5, .p1 3, .cl 0 5, .p1 3, .cl 0 5, .p1 3,
    .cl 0 5, .p1 3, .cl 0 10, .cl 0 5, .p1 3, .cl 0 5, .p1 3, .bk 0, .cl 0 37, .cl 0 43, .cl 0 56,
    .p1 5, .cl 0 43, .p1 9, .cl 0 37, .cl 0 44, .p1 3, .cl 0 43, .p1 9, .cl 0 37, .cl 0 43,
    .cl 0 56, .p1 14, .cl 0 43, .p1 9, .cl 0 37, .cl 0 43, .cl 0 44, .cl 0 45, .cl 0 48, .cl 0 51,
    .cl 0 43, .p1 9, .bk 0, .cl 0 39, .cl 0 46, .p1 11, .cl 0 41, .p1 14, .cl 0 39, .cl 0 46,
    .cl 0 52, .p1 3, .cl 0 41, .p1 14, .cl 0 39, .cl 0 41, .cl 0 57, .p1 13, .cl 0 41, .p1 14,
    .cl 0 39, .cl 0 41, .cl 0 42, .p1 9, .cl 0 41, .p1 14, .bk 0, .cl 0 36, .cl 0 44, .cl 0 58,
    .p1 14, .cl 0 44, .p1 13, .cl 0 36, .cl 0 44, .cl 0 58, .p1 9, .cl 0 44, .p1 13, .cl 0 36,
    .cl 0 49, .p1 11, .cl 0 44, .p1 13, .cl 0 36, .cl 0 49, .cl 0 53, .p1 3, .cl 0 44, .p1 13,
    .bk 0, .cl 0 38, .cl 0 42, .cl 0 59, .p1 13, .cl 0 38, .cl 0 39, .cl 0 42, .cl 0 38, .cl 0 39,
    .cl 0 44, .cl 0 42, .p1 8, .cl 0 38, .cl 0 42, .cl 0 59, .p1 5, .cl 0 38, .cl 0 41, .p1 5,
    .cl 0 38, .cl 0 41, .p1 3, .cl 0 42, .p1 8, .bk 0, .cl 0 10, .p1 3, .cl 0 10, .p1 3, .cl 0 10,
    .p1 3, .cl 0 10, .p1 3, .cl 0 10, .p1 3, .cl 0 10, .p1 3, .cl 0 10, .p1 3, .cl 0 20, .bk 0,
    .cl 0 33, .cl 0 47, .cl 0 49, .p1 5, .cl 0 33, .p1 7, .cl 0 47, .cl 0 58, .cl 0 33, .p1 7,
    .cl 0 33, .cl 0 47, .cl 0 58, .cl 0 61, .cl 0 33, .p1 7, .cl 0 47, .cl 0 58, .cl 0 33, .p1 7,
    .bk 0, .cl 0 49, .cl 0 56, .cl 0 58, .p1 5, .cl 0 31, .p1 12, .cl 0 49, .cl 0 56, .cl 0 31,
    .p1 12, .cl 0 49, .cl 0 56, .cl 0 31, .p1 12, .cl 0 49, .cl 0 56, .cl 0 58, .cl 0 59, .cl 0 61,
    .cl 0 31, .p1 12, .bk 0, .cl 0 46, .cl 0 48, .cl 0 53, .p1 13, .cl 0 34, .p1 15, .cl 0 34,
    .cl 0 46, .cl 0 63, .p1 7, .cl 0 34, .p1 15, .cl 0 46, .cl 0 48, .cl 0 59, .p1 1, .cl 0 34,
    .p1 15, .cl 0 46, .cl 0 59, .cl 0 34, .p1 15, .bk 0, .cl 0 32, .cl 0 34, .cl 0 48, .cl 0 32,
    .p1 10, .cl 0 48, .cl 0 57, .cl 0 32, .p1 10, .cl 0 32, .cl 0 46, .cl 0 48, .cl 0 32, .p1 10,
    .cl 0 48, .cl 0 57, .cl 0 32, .p1 10, .bk 0, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5,
    .cl 0 5, .cl 0 5, .cl 0 5, .bk 0, .cl 0 32, .cl 0 38, .cl 0 45, .p1 7, .cl 0 48, .p1 10,
    .cl 0 32, .cl 0 42, .cl 0 43, .p1 7, .cl 0 32, .cl 0 42, .cl 0 43, .cl 0 32, .cl 0 42,
    .cl 0 43, .cl 0 48, .p1 10, .cl 0 32, .cl 0 38, .p1 6, .cl 0 32, .cl 0 38, .p1 3, .bk 0,
    .cl 0 34, .cl 0 46, .cl 0 48, .cl 0 52, .cl 0 58, .cl 0 46, .p1 15, .cl 0 34, .cl 0 46,
    .cl 0 59, .p1 1, .cl 0 46, .p1 15, .cl 0 34, .cl 0 48, .p1 3, .cl 0 46, .p1 15, .cl 0 34,
    .cl 0 46, .cl 0 59, .cl 0 46, .p1 15, .bk 0, .cl 0 31, .cl 0 33, .cl 0 35, .cl 0 31, .cl 0 33,
    .cl 0 48, .cl 0 31, .cl 0 49, .cl 0 56, .cl 0 31, .cl 0 47, .p1 4, .cl 0 31, .cl 0 33,
    .cl 0 43, .cl 0 49, .p1 12, .cl 0 31, .cl 0 49, .cl 0 56, .p1 2, .cl 0 31, .cl 0 33, .cl 0 48,
    .p1 15, .bk 0, .cl 0 33, .cl 0 47, .cl 0 49, .p1 15, .cl 0 47, .p1 7, .cl 0 33, .cl 0 37,
    .p1 6, .cl 0 33, .cl 0 43, .cl 0 44, .p1 15, .cl 0 33, .cl 0 37, .cl 0 45, .p1 10, .cl 0 47,
    .p1 7, .cl 0 33, .cl 0 43, .cl 0 47, .cl 0 33, .cl 0 37, .p1 3, .bk 0, .cl 0 15, .cl 0 15,
    .cl 0 15, .cl 0 15, .cl 0 15, .cl 0 15, .cl 0 15, .cl 0 15, .bk 0, .cl 0 42, .cl 0 57, .p1 6,
    .cl 0 38, .p1 8, .cl 0 38, .cl 0 59, .p1 3, .cl 0 38, .p1 8, .cl 0 42, .cl 0 57, .cl 0 63,
    .cl 0 38, .p1 8, .cl 0 42, .cl 0 63, .cl 0 64, .p1 4, .cl 0 38, .p1 8, .bk 0, .cl 0 44,
    .cl 0 61, .cl 0 36, .p1 13, .cl 0 36, .cl 0 43, .cl 0 44, .cl 0 36, .p1 13, .cl 0 36, .cl 0 44,
    .cl 0 49, .p1 10, .cl 0 36, .p1 13, .cl 0 36, .cl 0 37, .cl 0 44, .cl 0 36, .p1 13, .bk 0,
    .cl 0 39, .cl 0 41, .cl 0 46, .p1 7, .cl 0 39, .p1 14, .cl 0 41, .cl 0 46, .cl 0 49, .cl 0 39,
    .p1 14, .cl 0 41, .cl 0 64, .cl 0 39, .p1 14, .cl 0 39, .cl 0 41, .cl 0 42, .p1 4, .cl 0 39,
    .p1 14, .bk 0, .cl 0 43, .cl 0 58, .cl 0 62, .cl 0 37, .p1 9, .cl 0 43, .cl 0 44, .cl 0 49,
    .cl 0 37, .p1 9, .cl 0 43, .cl 0 58, .p1 6, .cl 0 37, .p1 9, .cl 0 43, .cl 0 44, .cl 0 45,
    .cl 0 49, .p1 14, .cl 0 37, .p1 9]

private theorem cdOK223 : CdOK ⟨2, 0, 2, 3⟩ tab22 cd223 where
  size := by decide +kernel
  rep := by decide +kernel
  orb := by decide +kernel
  gp := by decide +kernel
  nu := by decide +kernel
  al := by decide +kernel
  be := by decide +kernel
  m := by decide +kernel

private theorem run223 : run cd223 3382 [(z16, z16)] cert223 = true := by
  decide +kernel

private theorem case223 :
    (tablesOKb ⟨2, 0, 2, 3⟩ (orbitData ⟨2, 0, 2, 3⟩) && g8b ⟨2, 0, 2, 3⟩ &&
      search ⟨2, 0, 2, 3⟩ (orbitData ⟨2, 0, 2, 3⟩) 17
        (Array.replicate (orbitData ⟨2, 0, 2, 3⟩).reps.size none)) = true := by
  rw [orbitData22]
  exact search_case tablesOKb22 g8b22 cdOK223 run223

private def cd227 : Cd := ⟨2, 0, 2, 7, orb22, rep22, gp22⟩

private def cert227 : List Op := [
    .bv 0, .bk 0, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .bv 1, .p1 1, .p1 1, .p1 1, .p1 1, .p1 1,
    .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .p1 1, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .p1 1, .cl 0 5,
    .bk 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 0 5,
    .cl 0 5, .p1 1, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .p1 1, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5,
    .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5,
    .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5,
    .p1 1, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5,
    .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5,
    .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .p1 1, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5,
    .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5,
    .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5,
    .p1 1, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5,
    .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5,
    .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 1, .cl 0 1, .cl 0 1, .bk 0, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .bv 1, .p1 1, .p1 1, .p1 1, .p1 1, .p1 1, .cl 0 6,
    .p1 2, .cl 0 5, .cl 0 6, .p1 2, .bk 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1,
    .cl 1 1, .cl 1 1, .p1 1, .cl 0 8, .p1 2, .cl 0 6, .cl 0 7, .cl 0 5, .cl 0 5, .p1 1, .cl 0 5,
    .cl 0 5, .cl 0 6, .cl 0 6, .p1 1, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 5, .cl 0 6, .p1 1, .cl 0 8,
    .p1 7, .cl 0 6, .cl 0 8, .p1 9, .cl 0 6, .p1 3, .cl 0 6, .p1 3, .cl 0 8, .p1 12, .cl 0 8,
    .p1 13, .cl 0 8, .p1 14, .cl 0 8, .p1 15, .cl 0 8, .cl 0 8, .p1 15, .cl 0 6, .cl 0 8, .cl 0 8,
    .p1 13, .cl 0 8, .p1 12, .cl 0 6, .p1 15, .cl 0 8, .p1 10, .cl 0 8, .p1 9, .cl 0 8, .p1 8,
    .cl 0 8, .p1 7, .cl 0 8, .p1 3, .cl 0 8, .p1 4, .cl 0 8, .p1 5, .cl 0 8, .p1 5, .cl 0 8, .p1 4,
    .p1 1, .cl 0 8, .p1 9, .cl 0 6, .cl 0 8, .p1 13, .cl 0 6, .p1 3, .cl 0 6, .p1 3, .cl 0 8,
    .p1 7, .cl 0 8, .p1 12, .cl 0 8, .p1 15, .cl 0 8, .p1 10, .cl 0 8, .cl 0 8, .p1 10, .cl 0 6,
    .cl 0 8, .cl 0 8, .p1 12, .cl 0 8, .p1 7, .cl 0 6, .p1 10, .cl 0 8, .p1 8, .cl 0 8, .p1 13,
    .cl 0 8, .p1 14, .cl 0 8, .p1 9, .cl 0 8, .p1 3, .cl 0 8, .p1 6, .cl 0 8, .p1 11, .cl 0 8,
    .p1 11, .cl 0 8, .p1 6, .p1 1, .cl 0 8, .p1 12, .cl 0 6, .cl 0 8, .p1 7, .cl 0 6, .p1 3,
    .cl 0 6, .p1 3, .cl 0 8, .p1 13, .cl 0 8, .p1 9, .cl 0 8, .p1 8, .cl 0 8, .p1 14, .cl 0 8,
    .cl 0 8, .p1 14, .cl 0 6, .cl 0 8, .cl 0 8, .p1 9, .cl 0 8, .p1 13, .cl 0 6, .p1 14, .cl 0 8,
    .p1 15, .cl 0 8, .p1 7, .cl 0 8, .p1 10, .cl 0 8, .p1 12, .cl 0 8, .p1 3, .cl 0 8, .p1 11,
    .cl 0 8, .p1 6, .cl 0 8, .p1 6, .cl 0 8, .p1 11, .p1 1, .cl 0 8, .p1 13, .cl 0 6, .cl 0 8,
    .p1 12, .cl 0 6, .p1 3, .cl 0 6, .p1 3, .cl 0 8, .p1 9, .cl 0 8, .p1 7, .cl 0 8, .p1 10,
    .cl 0 8, .p1 8, .cl 0 8, .cl 0 8, .p1 8, .cl 0 6, .cl 0 8, .cl 0 8, .p1 7, .cl 0 8, .p1 9,
    .cl 0 6, .p1 8, .cl 0 8, .p1 14, .cl 0 8, .p1 12, .cl 0 8, .p1 15, .cl 0 8, .p1 13, .cl 0 8,
    .p1 3, .cl 0 8, .p1 5, .cl 0 8, .p1 4, .cl 0 8, .p1 4, .cl 0 8, .p1 5, .cl 0 1, .bk 0, .cl 0 1,
    .cl 0 1, .bv 1, .p1 1, .p1 1, .p1 1, .p1 1, .p1 1, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .p1 1,
    .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .p1 1, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .p1 1, .bk 1,
    .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 0 5, .cl 0 5,
    .cl 0 5, .p1 1, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5,
    .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5,
    .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .p1 1, .cl 0 5, .cl 0 5, .cl 0 5,
    .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5,
    .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5,
    .cl 0 5, .p1 1, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5,
    .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5,
    .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .p1 1, .cl 0 5, .cl 0 5, .cl 0 5,
    .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5,
    .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5,
    .cl 0 5, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .bk 0, .bv 1, .p1 1, .p1 1, .p1 1, .p1 1,
    .p1 1, .cl 0 6, .p1 2, .cl 0 5, .cl 0 6, .p1 2, .cl 0 5, .p1 1, .cl 0 6, .cl 0 6, .p1 2, .bk 1,
    .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 0 5, .p1 1,
    .cl 0 5, .cl 0 5, .cl 0 6, .cl 0 6, .p1 1, .cl 0 5, .cl 0 6, .p1 2, .cl 0 5, .cl 0 6, .p1 1,
    .cl 0 6, .p1 5, .cl 0 6, .cl 0 6, .p1 4, .cl 0 6, .p1 3, .cl 0 6, .p1 7, .cl 0 6, .p1 8,
    .cl 0 6, .p1 9, .cl 0 6, .p1 10, .cl 0 6, .p1 6, .cl 0 6, .p1 12, .cl 0 6, .p1 13, .cl 0 6,
    .p1 14, .cl 0 6, .p1 15, .cl 0 6, .p1 11, .cl 0 6, .p1 15, .cl 0 6, .p1 14, .cl 0 6, .p1 13,
    .cl 0 6, .p1 12, .cl 0 6, .p1 11, .cl 0 6, .p1 10, .cl 0 6, .p1 9, .cl 0 6, .p1 8, .cl 0 6,
    .p1 7, .cl 0 6, .p1 6, .p1 1, .cl 0 6, .p1 11, .cl 0 6, .cl 0 6, .p1 6, .cl 0 6, .p1 3,
    .cl 0 6, .p1 9, .cl 0 6, .p1 14, .cl 0 6, .p1 13, .cl 0 6, .p1 8, .cl 0 6, .p1 5, .cl 0 6,
    .p1 7, .cl 0 6, .p1 12, .cl 0 6, .p1 15, .cl 0 6, .p1 10, .cl 0 6, .p1 4, .cl 0 6, .p1 10,
    .cl 0 6, .p1 15, .cl 0 6, .p1 12, .cl 0 6, .p1 7, .cl 0 6, .p1 4, .cl 0 6, .p1 8, .cl 0 6,
    .p1 13, .cl 0 6, .p1 14, .cl 0 6, .p1 9, .cl 0 6, .p1 5, .p1 1, .cl 0 6, .p1 6, .cl 0 6,
    .cl 0 6, .p1 11, .cl 0 6, .p1 3, .cl 0 6, .p1 12, .cl 0 6, .p1 10, .cl 0 6, .p1 7, .cl 0 6,
    .p1 15, .cl 0 6, .p1 4, .cl 0 6, .p1 13, .cl 0 6, .p1 9, .cl 0 6, .p1 8, .cl 0 6, .p1 14,
    .cl 0 6, .p1 5, .cl 0 6, .p1 14, .cl 0 6, .p1 8, .cl 0 6, .p1 9, .cl 0 6, .p1 13, .cl 0 6,
    .p1 5, .cl 0 6, .p1 15, .cl 0 6, .p1 7, .cl 0 6, .p1 10, .cl 0 6, .p1 12, .cl 0 6, .p1 4,
    .p1 1, .cl 0 6, .p1 4, .cl 0 6, .cl 0 6, .p1 5, .cl 0 6, .p1 3, .cl 0 6, .p1 13, .cl 0 6,
    .p1 15, .cl 0 6, .p1 12, .cl 0 6, .p1 14, .cl 0 6, .p1 11, .cl 0 6, .p1 9, .cl 0 6, .p1 7,
    .cl 0 6, .p1 10, .cl 0 6, .p1 8, .cl 0 6, .p1 6, .cl 0 6, .p1 8, .cl 0 6, .p1 10, .cl 0 6,
    .p1 7, .cl 0 6, .p1 9, .cl 0 6, .p1 6, .cl 0 6, .p1 14, .cl 0 6, .p1 12, .cl 0 6, .p1 15,
    .cl 0 6, .p1 13, .cl 0 6, .p1 11, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2,
    .cl 0 2, .bk 0, .cl 0 5, .cl 0 5, .cl 0 5, .bv 1, .p1 1, .p1 1, .p1 1, .p1 1, .p1 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .p1 1, .cl 0 1, .cl 0 1, .cl 0 1, .bk 1, .cl 1 1, .cl 1 1, .cl 1 1,
    .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .p1 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .p1 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .p1 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .p1 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .p1 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .p1 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .bk 0, .cl 0 2,
    .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .bk 0, .cl 0 2, .cl 0 2,
    .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .bk 0, .cl 0 2, .cl 0 2, .cl 0 2,
    .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .bk 0, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .bk 0, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .bv 1,
    .p1 1, .p1 1, .p1 1, .p1 1, .p1 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .p1 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .p1 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .p1 1, .cl 0 1, .cl 0 1, .bk 1,
    .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 0 1, .p1 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .p1 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .p1 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .p1 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 5,
    .cl 0 5, .bk 0, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .bk 0,
    .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .bk 0, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .bk 0, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .bk 0, .cl 0 5, .bv 1, .p1 1, .p1 1,
    .p1 1, .p1 1, .p1 1, .cl 0 3, .bk 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1,
    .cl 1 1, .cl 1 1, .cl 0 3, .cl 0 1, .p1 1, .cl 0 3, .cl 0 3, .cl 0 1, .cl 0 1, .p1 1, .cl 0 1,
    .cl 0 1, .cl 0 3, .cl 0 3, .p1 1, .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3, .p1 1, .cl 0 3, .cl 0 3,
    .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3,
    .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3,
    .cl 0 3, .cl 0 3, .p1 1, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3,
    .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3,
    .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .p1 1, .cl 0 3, .cl 0 3,
    .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3,
    .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3,
    .cl 0 3, .cl 0 3, .p1 1, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3,
    .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3,
    .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 5, .cl 0 5, .cl 0 5,
    .cl 0 5, .cl 0 5, .cl 0 5, .bk 0, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .bk 0, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3,
    .cl 0 3, .bk 0, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .bk 0,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .bk 0, .cl 0 10,
    .cl 0 10, .cl 0 10, .cl 0 10, .cl 0 10, .cl 0 10, .cl 0 10, .bv 1, .p1 1, .p1 1, .p1 1, .p1 1,
    .p1 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .p1 1, .cl 0 2, .cl 0 2, .cl 0 1, .cl 0 1, .p1 1,
    .bk 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 0 1,
    .cl 0 2, .cl 0 2, .p1 1, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .p1 1, .cl 0 2, .cl 0 2, .cl 0 2,
    .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2,
    .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2,
    .cl 0 2, .p1 1, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2,
    .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2,
    .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .p1 1, .cl 0 2, .cl 0 2, .cl 0 2,
    .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2,
    .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2,
    .cl 0 2, .p1 1, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2,
    .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2,
    .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .bk 0, .cl 0 2, .cl 0 2, .cl 0 2,
    .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .bk 0, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2,
    .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .bk 0, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2,
    .cl 0 2, .cl 0 2, .cl 0 2, .bk 0, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .p1 0, .bk 0, .cl 0 1, .p1 5, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1,
    .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .p1 3, .cl 0 1, .cl 0 2, .bk 0, .cl 0 1,
    .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1,
    .cl 0 2, .cl 0 1, .cl 0 4, .cl 0 1, .cl 0 2, .bk 0, .cl 0 1, .p1 3, .cl 0 1, .cl 0 3, .cl 0 1,
    .p1 4, .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3, .cl 0 1,
    .cl 0 3, .bk 0, .cl 0 2, .cl 0 3, .cl 0 2, .cl 0 3, .cl 0 2, .cl 0 4, .cl 0 2, .cl 0 3,
    .cl 0 2, .cl 0 3, .cl 0 2, .cl 0 3, .cl 0 2, .cl 0 3, .cl 0 2, .cl 0 3, .bk 0, .cl 0 5,
    .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5,
    .p1 3, .cl 0 5, .cl 0 10, .cl 0 5, .p1 11, .bk 0, .cl 0 31, .cl 0 33, .cl 0 34, .cl 0 31,
    .cl 0 33, .cl 0 38, .cl 0 31, .cl 0 47, .p1 2, .cl 0 31, .cl 0 47, .cl 0 31, .cl 0 33,
    .cl 0 36, .cl 0 31, .cl 0 47, .cl 0 31, .cl 0 47, .cl 0 61, .p1 14, .cl 0 31, .cl 0 33, .p1 2,
    .bk 0, .cl 0 32, .cl 0 38, .cl 0 32, .cl 0 38, .p1 1, .cl 0 32, .cl 0 38, .cl 0 42, .cl 0 32,
    .cl 0 38, .cl 0 32, .cl 0 38, .cl 0 42, .cl 0 32, .cl 0 38, .cl 0 42, .cl 0 32, .cl 0 38,
    .cl 0 32, .cl 0 38, .bk 0, .cl 0 33, .cl 0 37, .cl 0 43, .cl 0 33, .cl 0 37, .p1 2, .cl 0 33,
    .cl 0 37, .cl 0 33, .cl 0 37, .cl 0 33, .cl 0 37, .cl 0 33, .cl 0 37, .cl 0 43, .cl 0 33,
    .cl 0 37, .cl 0 38, .cl 0 33, .cl 0 37, .bk 0, .cl 0 34, .cl 0 48, .cl 0 34, .cl 0 48,
    .cl 0 59, .cl 0 60, .cl 0 34, .cl 0 48, .cl 0 59, .cl 0 63, .cl 0 34, .cl 0 48, .cl 0 34,
    .cl 0 48, .cl 0 34, .cl 0 48, .cl 0 34, .cl 0 48, .p1 1, .cl 0 34, .cl 0 48, .cl 0 56,
    .cl 0 59, .cl 0 61, .bk 0, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5,
    .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 20, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10, .bk 0,
    .cl 0 36, .cl 0 49, .cl 0 62, .p1 8, .cl 0 36, .cl 0 49, .cl 0 36, .cl 0 49, .cl 0 53, .p1 3,
    .cl 0 36, .cl 0 49, .p1 2, .cl 0 36, .cl 0 49, .cl 0 36, .cl 0 49, .cl 0 36, .cl 0 49,
    .cl 0 36, .cl 0 49, .cl 0 62, .p1 8, .bk 0, .cl 0 37, .cl 0 44, .cl 0 47, .cl 0 37, .cl 0 44,
    .cl 0 67, .p1 4, .cl 0 37, .cl 0 44, .cl 0 37, .cl 0 44, .cl 0 55, .p1 3, .cl 0 37, .cl 0 44,
    .p1 2, .cl 0 37, .cl 0 44, .cl 0 37, .cl 0 44, .cl 0 37, .cl 0 44, .bk 0, .cl 0 38, .cl 0 41,
    .p1 1, .cl 0 38, .cl 0 39, .p1 1, .cl 0 38, .cl 0 41, .cl 0 38, .cl 0 39, .cl 0 41, .cl 0 38,
    .cl 0 41, .cl 0 48, .cl 0 38, .cl 0 41, .cl 0 38, .cl 0 41, .cl 0 38, .cl 0 41, .bk 0,
    .cl 0 39, .cl 0 46, .cl 0 39, .cl 0 46, .cl 0 39, .cl 0 46, .cl 0 39, .cl 0 46, .p1 1,
    .cl 0 39, .cl 0 46, .cl 0 49, .cl 0 39, .cl 0 46, .cl 0 39, .cl 0 46, .cl 0 52, .p1 3,
    .cl 0 39, .cl 0 46, .cl 0 63, .p1 9, .bk 0, .cl 0 5, .cl 0 15, .cl 0 5, .p1 6, .cl 0 5,
    .cl 0 15, .cl 0 5, .cl 0 15, .cl 0 5, .cl 0 15, .cl 0 5, .cl 0 15, .cl 0 5, .cl 0 15, .cl 0 5,
    .p1 3, .bk 0, .cl 0 41, .cl 0 46, .p1 1, .cl 0 41, .cl 0 46, .cl 0 57, .p1 8, .cl 0 41,
    .cl 0 46, .cl 0 47, .cl 0 41, .cl 0 67, .cl 0 73, .cl 0 41, .cl 0 64, .p1 3, .cl 0 41,
    .cl 0 46, .cl 0 62, .p1 5, .cl 0 41, .cl 0 67, .p1 9, .cl 0 41, .cl 0 64, .p1 3, .bk 0,
    .cl 0 42, .cl 0 57, .cl 0 69, .cl 0 42, .cl 0 63, .p1 3, .cl 0 42, .cl 0 57, .cl 0 69,
    .cl 0 42, .cl 0 57, .p1 7, .cl 0 42, .cl 0 57, .p1 7, .cl 0 42, .cl 0 63, .p1 1, .cl 0 42,
    .cl 0 57, .p1 3, .cl 0 42, .cl 0 57, .cl 0 61, .p1 5, .bk 0, .cl 0 43, .cl 0 58, .p1 10,
    .cl 0 43, .cl 0 62, .p1 3, .cl 0 43, .cl 0 44, .cl 0 47, .cl 0 43, .cl 0 58, .p1 10, .cl 0 43,
    .cl 0 58, .cl 0 66, .cl 0 43, .cl 0 44, .p1 2, .cl 0 43, .cl 0 44, .cl 0 57, .p1 6, .cl 0 43,
    .cl 0 44, .cl 0 46, .bk 0, .cl 0 44, .cl 0 61, .p1 3, .cl 0 44, .cl 0 49, .cl 0 58, .p1 9,
    .cl 0 44, .cl 0 68, .p1 8, .cl 0 44, .cl 0 68, .cl 0 72, .cl 0 44, .cl 0 49, .p1 2, .cl 0 44,
    .cl 0 49, .cl 0 61, .p1 3, .cl 0 44, .cl 0 49, .cl 0 59, .cl 0 44, .cl 0 61, .p1 3, .bk 0,
    .cl 0 10, .cl 0 15, .cl 0 10, .cl 0 20, .cl 0 10, .cl 0 15, .cl 0 10, .cl 0 15, .cl 0 10,
    .cl 0 15, .cl 0 10, .cl 0 15, .cl 0 10, .cl 0 15, .cl 0 10, .cl 0 15, .bk 0, .cl 0 46,
    .cl 0 48, .cl 0 49, .cl 0 46, .cl 0 66, .p1 13, .cl 0 46, .cl 0 59, .p1 3, .cl 0 46, .cl 0 48,
    .p1 1, .cl 0 46, .cl 0 59, .p1 3, .cl 0 46, .cl 0 48, .cl 0 58, .p1 4, .cl 0 46, .cl 0 66,
    .cl 0 72, .cl 0 46, .cl 0 59, .p1 3, .bk 0, .cl 0 47, .cl 0 74, .p1 15, .cl 0 47, .cl 0 72,
    .cl 0 74, .cl 0 77, .cl 0 80, .p1 11, .cl 0 47, .cl 0 58, .p1 2, .cl 0 47, .cl 0 72, .cl 0 81,
    .p1 3, .cl 0 47, .cl 0 86, .cl 0 47, .cl 0 58, .p1 3, .cl 0 47, .cl 0 58, .p1 3, .cl 0 47,
    .cl 0 58, .p1 3, .bk 0, .cl 0 48, .cl 0 71, .cl 0 73, .p1 15, .cl 0 48, .cl 0 71, .cl 0 73,
    .cl 0 78, .cl 0 80, .p1 11, .cl 0 48, .cl 0 57, .p1 3, .cl 0 48, .cl 0 71, .cl 0 84, .p1 3,
    .cl 0 48, .cl 0 71, .p1 12, .cl 0 48, .cl 0 57, .p1 3, .cl 0 48, .cl 0 57, .p1 1, .cl 0 48,
    .cl 0 57, .p1 3, .bk 0, .cl 0 49, .cl 0 56, .p1 3, .cl 0 49, .cl 0 69, .p1 14, .cl 0 49,
    .cl 0 69, .cl 0 73, .cl 0 49, .cl 0 56, .p1 2, .cl 0 49, .cl 0 69, .cl 0 73, .cl 0 49,
    .cl 0 69, .cl 0 73, .cl 0 49, .cl 0 56, .p1 3, .cl 0 49, .cl 0 56, .p1 3, .p1 0, .bk 0,
    .cl 0 1, .p1 11, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2,
    .cl 0 1, .cl 0 2, .cl 0 1, .p1 3, .cl 0 1, .cl 0 2, .bk 0, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2,
    .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 4,
    .cl 0 1, .cl 0 2, .bk 0, .cl 0 1, .p1 3, .cl 0 1, .cl 0 3, .cl 0 1, .p1 6, .cl 0 1, .cl 0 3,
    .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3, .bk 0, .cl 0 2,
    .cl 0 3, .cl 0 2, .cl 0 3, .cl 0 2, .cl 0 4, .cl 0 2, .cl 0 3, .cl 0 2, .cl 0 3, .cl 0 2,
    .cl 0 3, .cl 0 2, .cl 0 3, .cl 0 2, .cl 0 3, .bk 0, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10,
    .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5, .p1 3, .cl 0 5, .cl 0 10,
    .cl 0 5, .p1 4, .bk 0, .cl 0 56, .cl 0 58, .cl 0 59, .cl 0 56, .cl 0 58, .cl 0 63, .cl 0 56,
    .cl 0 72, .p1 2, .cl 0 56, .cl 0 72, .cl 0 56, .cl 0 58, .cl 0 61, .cl 0 56, .cl 0 72,
    .cl 0 56, .cl 0 72, .cl 0 83, .p1 15, .cl 0 56, .cl 0 58, .p1 2, .bk 0, .cl 0 57, .cl 0 63,
    .cl 0 57, .cl 0 63, .p1 1, .cl 0 57, .cl 0 63, .cl 0 67, .cl 0 57, .cl 0 63, .cl 0 57,
    .cl 0 63, .cl 0 67, .cl 0 57, .cl 0 63, .cl 0 67, .cl 0 57, .cl 0 63, .cl 0 57, .cl 0 63,
    .bk 0, .cl 0 58, .cl 0 62, .cl 0 68, .cl 0 58, .cl 0 62, .p1 2, .cl 0 58, .cl 0 62, .cl 0 58,
    .cl 0 62, .cl 0 58, .cl 0 62, .cl 0 58, .cl 0 62, .cl 0 68, .cl 0 58, .cl 0 62, .cl 0 63,
    .cl 0 58, .cl 0 62, .bk 0, .cl 0 59, .cl 0 73, .cl 0 59, .cl 0 73, .cl 0 77, .cl 0 84, .p1 4,
    .cl 0 59, .cl 0 73, .cl 0 82, .p1 12, .cl 0 59, .cl 0 73, .cl 0 59, .cl 0 73, .cl 0 59,
    .cl 0 73, .cl 0 59, .cl 0 73, .p1 1, .cl 0 59, .cl 0 73, .cl 0 89, .bk 0, .cl 0 5, .cl 0 10,
    .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 20,
    .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10, .bk 0, .cl 0 61, .cl 0 74, .cl 0 87, .cl 0 61, .cl 0 74,
    .cl 0 61, .cl 0 74, .cl 0 80, .cl 0 83, .cl 0 84, .p1 11, .cl 0 61, .cl 0 74, .p1 2, .cl 0 61,
    .cl 0 74, .cl 0 61, .cl 0 74, .cl 0 61, .cl 0 74, .cl 0 61, .cl 0 74, .cl 0 81, .p1 14, .bk 0,
    .cl 0 62, .cl 0 69, .cl 0 72, .cl 0 62, .cl 0 69, .cl 0 82, .cl 0 62, .cl 0 69, .cl 0 62,
    .cl 0 69, .cl 0 83, .cl 0 62, .cl 0 69, .p1 2, .cl 0 62, .cl 0 69, .cl 0 62, .cl 0 69,
    .cl 0 62, .cl 0 69, .bk 0, .cl 0 63, .cl 0 66, .p1 1, .cl 0 63, .cl 0 64, .p1 1, .cl 0 63,
    .cl 0 66, .cl 0 63, .cl 0 64, .cl 0 66, .cl 0 63, .cl 0 66, .cl 0 73, .cl 0 63, .cl 0 66,
    .cl 0 63, .cl 0 66, .cl 0 63, .cl 0 66, .bk 0, .cl 0 64, .cl 0 71, .cl 0 64, .cl 0 71,
    .cl 0 64, .cl 0 71, .cl 0 64, .cl 0 71, .p1 1, .cl 0 64, .cl 0 71, .cl 0 74, .cl 0 64,
    .cl 0 71, .cl 0 64, .cl 0 71, .cl 0 82, .cl 0 84, .p1 13, .cl 0 64, .cl 0 71, .cl 0 82, .bk 0,
    .cl 0 5, .cl 0 15, .cl 0 5, .p1 5, .cl 0 5, .cl 0 15, .cl 0 5, .cl 0 15, .cl 0 5, .cl 0 15,
    .cl 0 5, .cl 0 15, .cl 0 5, .cl 0 15, .cl 0 5, .p1 3, .bk 0, .cl 0 66, .cl 0 71, .p1 1,
    .cl 0 66, .cl 0 71, .cl 0 88, .p1 4, .cl 0 66, .cl 0 71, .cl 0 72, .cl 0 66, .cl 0 88,
    .cl 0 91, .p1 12, .cl 0 66, .cl 0 88, .cl 0 98, .cl 0 106, .cl 0 66, .cl 0 71, .cl 0 83,
    .cl 0 66, .cl 0 92, .p1 9, .cl 0 66, .cl 0 92, .p1 3, .bk 0, .cl 0 67, .cl 0 82, .cl 0 83,
    .p1 6, .cl 0 67, .cl 0 96, .cl 0 98, .cl 0 109, .cl 0 111, .cl 0 67, .cl 0 96, .cl 0 107,
    .cl 0 109, .p1 13, .cl 0 67, .cl 0 82, .p1 7, .cl 0 67, .cl 0 82, .p1 3, .cl 0 67, .cl 0 82,
    .cl 0 97, .cl 0 101, .p1 12, .cl 0 67, .cl 0 107, .p1 3, .cl 0 67, .cl 0 96, .cl 0 98, .p1 11,
    .bk 0, .cl 0 68, .cl 0 83, .p1 3, .cl 0 68, .cl 0 97, .cl 0 99, .cl 0 106, .cl 0 109,
    .cl 0 110, .cl 0 68, .cl 0 69, .cl 0 72, .cl 0 68, .cl 0 83, .p1 10, .cl 0 68, .cl 0 83,
    .cl 0 84, .cl 0 87, .p1 3, .cl 0 68, .cl 0 69, .p1 2, .cl 0 68, .cl 0 69, .cl 0 83, .cl 0 91,
    .cl 0 68, .cl 0 69, .cl 0 71, .bk 0, .cl 0 69, .cl 0 87, .cl 0 89, .cl 0 91, .p1 6, .cl 0 69,
    .cl 0 74, .cl 0 87, .p1 4, .cl 0 69, .cl 0 93, .p1 8, .cl 0 69, .cl 0 87, .cl 0 94, .p1 15,
    .cl 0 69, .cl 0 74, .p1 2, .cl 0 69, .cl 0 74, .cl 0 82, .cl 0 69, .cl 0 74, .cl 0 89,
    .cl 0 90, .cl 0 91, .cl 0 69, .cl 0 93, .p1 3, .bk 0, .cl 0 10, .cl 0 15, .cl 0 10, .cl 0 20,
    .cl 0 10, .cl 0 15, .cl 0 10, .cl 0 15, .cl 0 10, .cl 0 15, .cl 0 10, .cl 0 15, .cl 0 10,
    .cl 0 15, .cl 0 10, .cl 0 15, .bk 0, .cl 0 71, .cl 0 73, .cl 0 74, .cl 0 71, .cl 0 91, .p1 13,
    .cl 0 71, .cl 0 91, .p1 3, .cl 0 71, .cl 0 73, .p1 1, .cl 0 71, .cl 0 73, .cl 0 88, .cl 0 71,
    .cl 0 73, .cl 0 81, .cl 0 89, .cl 0 71, .cl 0 89, .cl 0 91, .cl 0 93, .cl 0 71, .cl 0 88,
    .cl 0 89, .cl 0 98, .p1 7, .bk 0, .cl 0 72, .cl 0 99, .p1 15, .cl 0 72, .cl 0 81, .cl 0 90,
    .cl 0 72, .cl 0 86, .cl 0 87, .p1 10, .cl 0 86, .cl 0 111, .cl 0 72, .cl 0 81, .cl 0 85, .p1 8,
    .cl 0 72, .cl 0 81, .cl 0 85, .p1 8, .cl 0 72, .cl 0 81, .cl 0 86, .cl 0 87, .p1 8, .cl 0 72,
    .cl 0 108, .p1 3, .bk 0, .cl 0 73, .cl 0 84, .cl 0 85, .p1 9, .cl 0 73, .cl 0 84, .cl 0 90,
    .cl 0 73, .cl 0 84, .cl 0 89, .cl 0 90, .cl 0 92, .cl 0 89, .cl 0 114, .cl 0 73, .cl 0 96,
    .p1 12, .cl 0 73, .cl 0 84, .cl 0 85, .p1 9, .cl 0 73, .cl 0 96, .cl 0 99, .cl 0 105, .cl 0 73,
    .cl 0 107, .p1 3, .bk 0, .cl 0 74, .cl 0 106, .p1 3, .cl 0 74, .cl 0 94, .p1 14, .cl 0 74,
    .cl 0 86, .cl 0 99, .p1 10, .cl 0 74, .cl 0 87, .cl 0 94, .cl 0 97, .cl 0 87, .cl 0 112,
    .cl 0 74, .cl 0 86, .cl 0 87, .cl 0 74, .cl 0 86, .cl 0 88, .p1 3, .cl 0 74, .cl 0 86,
    .cl 0 87, .cl 0 97, .p1 10, .p1 0, .bk 0, .cl 0 1, .p1 6, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2,
    .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .p1 3, .cl 0 1, .cl 0 2, .bk 0,
    .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2,
    .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 4, .cl 0 1, .cl 0 2, .bk 0, .cl 0 1, .p1 3, .cl 0 1, .cl 0 3,
    .cl 0 1, .p1 11, .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3,
    .cl 0 1, .cl 0 3, .bk 0, .cl 0 2, .cl 0 3, .cl 0 2, .cl 0 3, .cl 0 2, .cl 0 4, .cl 0 2,
    .cl 0 3, .cl 0 2, .cl 0 3, .cl 0 2, .cl 0 3, .cl 0 2, .cl 0 3, .cl 0 2, .cl 0 3, .bk 0,
    .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10,
    .cl 0 5, .p1 3, .cl 0 5, .cl 0 10, .cl 0 5, .p1 5, .bk 0, .cl 0 62, .cl 0 83, .cl 0 84,
    .cl 0 62, .cl 0 68, .cl 0 69, .p1 11, .cl 0 62, .cl 0 69, .cl 0 79, .cl 0 62, .cl 0 68,
    .cl 0 72, .p1 4, .cl 0 62, .cl 0 68, .cl 0 83, .p1 2, .cl 0 62, .cl 0 68, .cl 0 86, .p1 2,
    .cl 0 62, .cl 0 68, .cl 0 69, .cl 0 74, .p1 3, .cl 0 62, .cl 0 83, .p1 2, .bk 0, .cl 0 64,
    .cl 0 66, .cl 0 84, .p1 1, .cl 0 64, .cl 0 66, .cl 0 71, .cl 0 83, .p1 5, .cl 0 64, .cl 0 66,
    .cl 0 67, .p1 13, .cl 0 64, .cl 0 88, .cl 0 64, .cl 0 66, .cl 0 71, .p1 4, .cl 0 64, .cl 0 66,
    .cl 0 71, .cl 0 73, .p1 3, .cl 0 64, .cl 0 71, .cl 0 72, .cl 0 85, .p1 14, .cl 0 64, .cl 0 88,
    .bk 0, .cl 0 61, .cl 0 69, .cl 0 74, .p1 4, .cl 0 61, .cl 0 69, .cl 0 74, .cl 0 82, .p1 5,
    .cl 0 61, .cl 0 87, .cl 0 61, .cl 0 87, .cl 0 61, .cl 0 69, .cl 0 81, .p1 2, .cl 0 61,
    .cl 0 74, .cl 0 86, .cl 0 61, .cl 0 87, .cl 0 88, .cl 0 61, .cl 0 87, .bk 0, .cl 0 63,
    .cl 0 67, .cl 0 82, .p1 1, .cl 0 63, .cl 0 66, .cl 0 67, .cl 0 63, .cl 0 64, .cl 0 68,
    .cl 0 63, .cl 0 67, .cl 0 73, .p1 4, .cl 0 63, .cl 0 67, .cl 0 82, .cl 0 89, .cl 0 91, .p1 9,
    .cl 0 63, .cl 0 64, .p1 7, .cl 0 63, .cl 0 64, .p1 3, .cl 0 63, .cl 0 64, .cl 0 67, .cl 0 69,
    .cl 0 73, .p1 13, .bk 0, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5,
    .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 20, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10, .bk 0,
    .cl 0 72, .cl 0 81, .p1 2, .cl 0 58, .cl 0 72, .cl 0 81, .cl 0 87, .cl 0 88, .cl 0 72,
    .cl 0 81, .cl 0 82, .cl 0 72, .cl 0 99, .p1 2, .cl 0 58, .cl 0 72, .cl 0 74, .p1 11, .cl 0 58,
    .cl 0 72, .cl 0 81, .p1 2, .cl 0 58, .cl 0 72, .cl 0 87, .p1 2, .cl 0 58, .cl 0 72, .cl 0 93,
    .cl 0 97, .p1 4, .bk 0, .cl 0 56, .cl 0 74, .cl 0 94, .p1 2, .cl 0 56, .cl 0 61, .cl 0 74,
    .cl 0 74, .cl 0 86, .cl 0 88, .cl 0 56, .cl 0 83, .cl 0 56, .cl 0 74, .cl 0 83, .cl 0 91,
    .p1 15, .cl 0 56, .cl 0 69, .cl 0 72, .cl 0 73, .p1 3, .cl 0 56, .cl 0 74, .cl 0 86, .p1 2,
    .cl 0 56, .cl 0 74, .cl 0 83, .p1 10, .bk 0, .cl 0 71, .cl 0 73, .p1 3, .cl 0 59, .cl 0 64,
    .cl 0 71, .cl 0 59, .cl 0 71, .cl 0 82, .cl 0 83, .cl 0 84, .cl 0 59, .cl 0 82, .cl 0 59,
    .cl 0 71, .cl 0 73, .cl 0 74, .cl 0 82, .cl 0 59, .cl 0 66, .cl 0 71, .cl 0 71, .cl 0 91,
    .cl 0 71, .cl 0 73, .p1 13, .bk 0, .cl 0 57, .cl 0 71, .cl 0 73, .cl 0 73, .cl 0 84, .cl 0 86,
    .cl 0 57, .cl 0 73, .cl 0 88, .p1 1, .cl 0 73, .cl 0 96, .p1 1, .cl 0 57, .cl 0 59, .cl 0 73,
    .cl 0 57, .cl 0 73, .cl 0 84, .p1 1, .cl 0 57, .cl 0 73, .cl 0 84, .cl 0 88, .p1 9, .cl 0 57,
    .cl 0 73, .cl 0 96, .p1 1, .bk 0, .cl 0 5, .cl 0 15, .cl 0 5, .p1 4, .cl 0 5, .cl 0 15,
    .cl 0 5, .cl 0 15, .cl 0 5, .cl 0 15, .cl 0 5, .cl 0 15, .cl 0 5, .cl 0 15, .cl 0 5, .p1 3,
    .bk 0, .cl 0 57, .cl 0 67, .cl 0 68, .cl 0 69, .cl 0 57, .cl 0 84, .cl 0 57, .cl 0 63,
    .cl 0 70, .p1 9, .cl 0 57, .cl 0 63, .cl 0 66, .p1 9, .cl 0 57, .cl 0 84, .cl 0 57, .cl 0 84,
    .cl 0 57, .cl 0 67, .p1 12, .cl 0 57, .cl 0 67, .p1 3, .bk 0, .cl 0 59, .cl 0 73, .cl 0 84,
    .cl 0 59, .cl 0 73, .cl 0 78, .p1 3, .cl 0 59, .cl 0 89, .cl 0 59, .cl 0 71, .cl 0 82, .p1 1,
    .cl 0 59, .cl 0 73, .cl 0 74, .p1 3, .cl 0 59, .cl 0 89, .cl 0 91, .cl 0 59, .cl 0 89,
    .cl 0 59, .cl 0 71, .cl 0 73, .p1 6, .bk 0, .cl 0 56, .cl 0 58, .p1 3, .cl 0 56, .cl 0 72,
    .cl 0 77, .p1 3, .cl 0 56, .cl 0 86, .cl 0 56, .cl 0 58, .p1 14, .cl 0 56, .cl 0 58, .cl 0 59,
    .cl 0 62, .p1 3, .cl 0 56, .cl 0 58, .cl 0 73, .cl 0 80, .p1 2, .cl 0 56, .cl 0 86, .cl 0 56,
    .cl 0 72, .cl 0 74, .bk 0, .cl 0 58, .cl 0 62, .cl 0 64, .cl 0 66, .p1 11, .cl 0 58, .cl 0 81,
    .cl 0 58, .cl 0 68, .p1 15, .cl 0 58, .cl 0 62, .cl 0 69, .p1 8, .cl 0 58, .cl 0 68, .cl 0 72,
    .cl 0 74, .cl 0 58, .cl 0 81, .cl 0 58, .cl 0 62, .cl 0 70, .p1 8, .cl 0 58, .cl 0 68, .p1 3,
    .bk 0, .cl 0 10, .cl 0 15, .cl 0 10, .cl 0 20, .cl 0 10, .cl 0 15, .cl 0 10, .cl 0 15,
    .cl 0 10, .cl 0 15, .cl 0 10, .cl 0 15, .cl 0 10, .cl 0 15, .cl 0 10, .cl 0 15, .bk 0,
    .cl 0 67, .cl 0 82, .cl 0 67, .cl 0 82, .cl 0 67, .cl 0 82, .p1 1, .cl 0 63, .cl 0 67,
    .cl 0 73, .p1 9, .cl 0 67, .cl 0 82, .cl 0 63, .cl 0 89, .cl 0 63, .cl 0 67, .cl 0 82, .p1 1,
    .cl 0 67, .cl 0 82, .bk 0, .cl 0 69, .cl 0 74, .p1 8, .cl 0 69, .cl 0 74, .cl 0 82, .cl 0 61,
    .cl 0 62, .cl 0 69, .cl 0 61, .cl 0 69, .cl 0 81, .cl 0 89, .cl 0 61, .cl 0 81, .cl 0 69,
    .cl 0 74, .p1 3, .cl 0 61, .cl 0 68, .cl 0 69, .cl 0 61, .cl 0 81, .cl 0 84, .p1 5, .bk 0,
    .cl 0 64, .cl 0 84, .cl 0 66, .cl 0 71, .cl 0 74, .cl 0 77, .p1 3, .cl 0 64, .cl 0 66,
    .cl 0 67, .p1 6, .cl 0 64, .cl 0 66, .cl 0 84, .cl 0 86, .cl 0 66, .cl 0 71, .p1 9, .cl 0 66,
    .cl 0 71, .p1 3, .cl 0 66, .cl 0 71, .cl 0 74, .cl 0 76, .p1 1, .cl 0 64, .cl 0 66, .cl 0 88,
    .p1 1, .bk 0, .cl 0 68, .cl 0 83, .cl 0 68, .cl 0 69, .p1 10, .cl 0 68, .cl 0 69, .cl 0 82,
    .cl 0 62, .cl 0 68, .cl 0 69, .cl 0 72, .cl 0 68, .cl 0 83, .cl 0 62, .cl 0 86, .cl 0 68,
    .cl 0 69, .p1 3, .cl 0 68, .cl 0 83, .p1 0, .bk 0, .cl 0 1, .p1 4, .cl 0 1, .cl 0 2, .cl 0 1,
    .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .p1 3, .cl 0 1,
    .cl 0 2, .bk 0, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2,
    .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 4, .cl 0 1, .cl 0 2, .bk 0, .cl 0 1, .p1 3,
    .cl 0 1, .cl 0 3, .cl 0 1, .p1 5, .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3,
    .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3, .bk 0, .cl 0 2, .cl 0 3, .cl 0 2, .cl 0 3, .cl 0 2,
    .cl 0 4, .cl 0 2, .cl 0 3, .cl 0 2, .cl 0 3, .cl 0 2, .cl 0 3, .cl 0 2, .cl 0 3, .cl 0 2,
    .cl 0 3, .bk 0, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10,
    .cl 0 5, .cl 0 10, .cl 0 5, .p1 3, .cl 0 5, .cl 0 10, .cl 0 5, .p1 6, .bk 0, .cl 0 37,
    .cl 0 43, .cl 0 56, .p1 5, .cl 0 37, .cl 0 43, .cl 0 44, .p1 5, .cl 0 37, .cl 0 44, .cl 0 55,
    .cl 0 37, .cl 0 43, .cl 0 47, .p1 11, .cl 0 37, .cl 0 43, .cl 0 56, .p1 14, .cl 0 37, .cl 0 43,
    .cl 0 56, .p1 10, .cl 0 37, .cl 0 43, .cl 0 44, .cl 0 49, .p1 3, .cl 0 37, .cl 0 43, .cl 0 56,
    .p1 6, .bk 0, .cl 0 39, .cl 0 41, .cl 0 57, .p1 9, .cl 0 39, .cl 0 46, .cl 0 52, .cl 0 39,
    .cl 0 41, .cl 0 42, .p1 9, .cl 0 39, .cl 0 41, .cl 0 57, .p1 12, .cl 0 39, .cl 0 41, .cl 0 46,
    .p1 11, .cl 0 39, .cl 0 41, .cl 0 46, .cl 0 48, .p1 3, .cl 0 39, .cl 0 46, .cl 0 47, .cl 0 51,
    .p1 7, .cl 0 39, .cl 0 41, .cl 0 57, .p1 11, .bk 0, .cl 0 36, .cl 0 44, .cl 0 49, .p1 11,
    .cl 0 36, .cl 0 49, .cl 0 53, .cl 0 36, .cl 0 49, .cl 0 53, .p1 9, .cl 0 36, .cl 0 44,
    .cl 0 58, .p1 15, .cl 0 36, .cl 0 44, .cl 0 58, .p1 8, .cl 0 36, .cl 0 44, .cl 0 49, .cl 0 53,
    .cl 0 55, .p1 8, .cl 0 36, .cl 0 44, .cl 0 58, .p1 5, .cl 0 36, .cl 0 44, .cl 0 58, .p1 11,
    .bk 0, .cl 0 38, .cl 0 57, .p1 13, .cl 0 38, .cl 0 41, .cl 0 42, .cl 0 38, .cl 0 39, .cl 0 43,
    .cl 0 38, .cl 0 42, .cl 0 48, .p1 11, .cl 0 38, .cl 0 42, .cl 0 59, .p1 5, .cl 0 38, .cl 0 39,
    .p1 12, .cl 0 38, .cl 0 39, .p1 3, .cl 0 38, .cl 0 39, .cl 0 42, .cl 0 44, .cl 0 48, .p1 9,
    .bk 0, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5,
    .cl 0 10, .cl 0 5, .cl 0 20, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10, .bk 0, .cl 0 47, .cl 0 56,
    .cl 0 58, .p1 2, .cl 0 47, .cl 0 58, .cl 0 47, .cl 0 56, .p1 8, .cl 0 47, .cl 0 58, .cl 0 33,
    .cl 0 47, .cl 0 49, .p1 5, .cl 0 47, .cl 0 56, .p1 8, .cl 0 33, .cl 0 47, .cl 0 56, .p1 8,
    .cl 0 33, .cl 0 47, .cl 0 56, .cl 0 57, .bk 0, .cl 0 31, .cl 0 62, .cl 0 31, .cl 0 36,
    .cl 0 49, .cl 0 49, .cl 0 56, .cl 0 49, .cl 0 56, .cl 0 49, .cl 0 56, .cl 0 31, .cl 0 44,
    .cl 0 47, .cl 0 48, .p1 3, .cl 0 49, .cl 0 56, .cl 0 58, .p1 5, .cl 0 49, .cl 0 56, .bk 0,
    .cl 0 46, .cl 0 48, .p1 3, .cl 0 34, .cl 0 39, .cl 0 46, .cl 0 34, .cl 0 46, .cl 0 63, .p1 7,
    .cl 0 46, .cl 0 59, .cl 0 46, .cl 0 48, .cl 0 49, .cl 0 56, .cl 0 58, .p1 11, .cl 0 34,
    .cl 0 41, .cl 0 46, .cl 0 46, .cl 0 59, .cl 0 46, .cl 0 48, .p1 9, .bk 0, .cl 0 32, .cl 0 46,
    .cl 0 48, .cl 0 48, .cl 0 57, .cl 0 48, .cl 0 57, .cl 0 48, .cl 0 57, .cl 0 32, .cl 0 34,
    .cl 0 48, .cl 0 48, .cl 0 59, .p1 9, .cl 0 48, .cl 0 57, .cl 0 48, .cl 0 57, .cl 0 63, .p1 7,
    .bk 0, .cl 0 5, .cl 0 15, .cl 0 5, .p1 11, .cl 0 5, .cl 0 15, .cl 0 5, .cl 0 15, .cl 0 5,
    .cl 0 15, .cl 0 5, .cl 0 15, .cl 0 5, .cl 0 15, .cl 0 5, .p1 3, .bk 0, .cl 0 32, .cl 0 42,
    .cl 0 43, .cl 0 44, .cl 0 32, .cl 0 48, .cl 0 57, .cl 0 32, .cl 0 38, .cl 0 45, .p1 7,
    .cl 0 32, .cl 0 38, .cl 0 41, .p1 7, .cl 0 32, .cl 0 38, .cl 0 51, .p1 15, .cl 0 32, .cl 0 48,
    .cl 0 57, .p1 1, .cl 0 32, .cl 0 42, .p1 13, .cl 0 32, .cl 0 42, .p1 3, .bk 0, .cl 0 34,
    .cl 0 46, .cl 0 59, .cl 0 34, .cl 0 48, .cl 0 58, .p1 7, .cl 0 34, .cl 0 46, .cl 0 59, .p1 1,
    .cl 0 34, .cl 0 46, .cl 0 59, .cl 0 34, .cl 0 48, .cl 0 49, .p1 3, .cl 0 34, .cl 0 46,
    .cl 0 59, .p1 1, .cl 0 34, .cl 0 46, .cl 0 59, .cl 0 34, .cl 0 46, .cl 0 48, .p1 4, .bk 0,
    .cl 0 31, .cl 0 33, .p1 3, .cl 0 31, .cl 0 49, .cl 0 56, .p1 2, .cl 0 31, .cl 0 49, .cl 0 56,
    .cl 0 31, .cl 0 33, .p1 8, .cl 0 31, .cl 0 33, .cl 0 34, .cl 0 37, .p1 3, .cl 0 31, .cl 0 33,
    .cl 0 48, .cl 0 53, .cl 0 31, .cl 0 49, .cl 0 56, .p1 2, .cl 0 31, .cl 0 47, .cl 0 49, .bk 0,
    .cl 0 33, .cl 0 37, .cl 0 39, .cl 0 41, .p1 5, .cl 0 33, .cl 0 47, .cl 0 58, .cl 0 33,
    .cl 0 43, .p1 14, .cl 0 33, .cl 0 37, .cl 0 44, .p1 10, .cl 0 33, .cl 0 43, .cl 0 47, .cl 0 49,
    .cl 0 33, .cl 0 47, .cl 0 58, .p1 2, .cl 0 33, .cl 0 37, .cl 0 45, .p1 10, .cl 0 33, .cl 0 43,
    .p1 3, .bk 0, .cl 0 10, .cl 0 15, .cl 0 10, .cl 0 20, .cl 0 10, .cl 0 15, .cl 0 10, .cl 0 15,
    .cl 0 10, .cl 0 15, .cl 0 10, .cl 0 15, .cl 0 10, .cl 0 15, .cl 0 10, .cl 0 15, .bk 0,
    .cl 0 42, .cl 0 63, .cl 0 42, .cl 0 63, .cl 0 38, .cl 0 59, .p1 3, .cl 0 38, .cl 0 42,
    .cl 0 48, .p1 7, .cl 0 42, .cl 0 63, .cl 0 64, .p1 4, .cl 0 42, .cl 0 63, .cl 0 42, .cl 0 63,
    .cl 0 66, .p1 9, .cl 0 38, .cl 0 42, .cl 0 63, .cl 0 64, .p1 4, .bk 0, .cl 0 44, .cl 0 49,
    .p1 10, .cl 0 36, .cl 0 44, .cl 0 49, .cl 0 64, .cl 0 36, .cl 0 37, .cl 0 44, .cl 0 44,
    .cl 0 61, .cl 0 44, .cl 0 61, .cl 0 44, .cl 0 49, .p1 3, .cl 0 36, .cl 0 43, .cl 0 44,
    .cl 0 44, .cl 0 62, .p1 15, .bk 0, .cl 0 41, .cl 0 63, .p1 12, .cl 0 41, .cl 0 46, .cl 0 49,
    .cl 0 52, .p1 3, .cl 0 39, .cl 0 41, .cl 0 42, .p1 4, .cl 0 41, .cl 0 64, .cl 0 41, .cl 0 46,
    .p1 7, .cl 0 41, .cl 0 46, .p1 3, .cl 0 41, .cl 0 46, .cl 0 49, .cl 0 60, .cl 0 41, .cl 0 63,
    .p1 12, .bk 0, .cl 0 37, .cl 0 43, .cl 0 68, .cl 0 43, .cl 0 44, .p1 15, .cl 0 37, .cl 0 43,
    .cl 0 44, .cl 0 63, .cl 0 66, .p1 5, .cl 0 37, .cl 0 43, .cl 0 44, .cl 0 47, .cl 0 43,
    .cl 0 62, .cl 0 43, .cl 0 62, .cl 0 43, .cl 0 44, .p1 3, .cl 0 37, .cl 0 43, .cl 0 62, .cl 0 68]

private theorem cdOK227 : CdOK ⟨2, 0, 2, 7⟩ tab22 cd227 where
  size := by decide +kernel
  rep := by decide +kernel
  orb := by decide +kernel
  gp := by decide +kernel
  nu := by decide +kernel
  al := by decide +kernel
  be := by decide +kernel
  m := by decide +kernel

private theorem run227 : run cd227 3736 [(z16, z16)] cert227 = true := by
  decide +kernel

private theorem case227 :
    (tablesOKb ⟨2, 0, 2, 7⟩ (orbitData ⟨2, 0, 2, 7⟩) && g8b ⟨2, 0, 2, 7⟩ &&
      search ⟨2, 0, 2, 7⟩ (orbitData ⟨2, 0, 2, 7⟩) 17
        (Array.replicate (orbitData ⟨2, 0, 2, 7⟩).reps.size none)) = true := by
  rw [orbitData_congr (P := ⟨2, 0, 2, 7⟩) (Q := ⟨2, 0, 2, 3⟩) rfl, orbitData22]
  refine search_case ?_ ?_ cdOK227 run227
  · rw [tablesOKb_congr (P := ⟨2, 0, 2, 7⟩) (Q := ⟨2, 0, 2, 3⟩) rfl]
    exact tablesOKb22
  · rw [g8b_congr (P := ⟨2, 0, 2, 7⟩) (Q := ⟨2, 0, 2, 3⟩) rfl]
    exact g8b22

private def tab23 : Tables where
  lookup := #[
    none, some (0, 0), some (0, 6), some (0, 2), some (0, 4), some (0, 7), some (1, 0),
    some (1, 7), some (2, 0), some (2, 5), some (0, 5), some (2, 6), some (1, 6), some (2, 3),
    some (1, 5), some (0, 1), some (1, 1), some (2, 7), some (1, 2), some (2, 2), some (0, 3),
    some (2, 1), some (2, 4), some (1, 3), some (1, 4), some (3, 0), some (4, 0), some (5, 0),
    some (5, 4), some (4, 4), some (6, 0), some (7, 0), some (8, 0), some (9, 0), some (10, 0),
    some (11, 0), some (12, 0), some (13, 0), some (14, 0), some (15, 0), some (11, 4),
    some (15, 4), some (14, 4), some (13, 4), some (12, 4), some (6, 4), some (10, 4), some (9, 4),
    some (8, 4), some (7, 4), some (3, 1), some (6, 1), some (11, 1), some (11, 5), some (6, 5),
    some (5, 1), some (8, 1), some (13, 1), some (14, 5), some (9, 5), some (4, 5), some (10, 1),
    some (15, 1), some (12, 5), some (7, 5), some (4, 1), some (7, 1), some (12, 1), some (15, 5),
    some (10, 5), some (5, 5), some (9, 1), some (14, 1), some (13, 5), some (8, 5), some (3, 3),
    some (11, 3), some (6, 7), some (6, 3), some (11, 7), some (4, 7), some (15, 3), some (7, 7),
    some (10, 3), some (12, 7), some (5, 7), some (14, 3), some (8, 7), some (9, 3), some (13, 7),
    some (5, 3), some (13, 3), some (9, 7), some (8, 3), some (14, 7), some (4, 3), some (12, 3),
    some (10, 7), some (7, 3), some (15, 7), some (3, 2), some (5, 2), some (4, 6), some (4, 2),
    some (5, 6), some (11, 2), some (13, 2), some (15, 2), some (12, 2), some (14, 2), some (6, 6),
    some (9, 6), some (7, 6), some (10, 6), some (8, 6), some (6, 2), some (8, 2), some (10, 2),
    some (7, 2), some (9, 2), some (11, 6), some (14, 6), some (12, 6), some (15, 6), some (13, 6)]
  reps := #[
    (0, 0, 1), (0, 1, 1), (0, 1, 3), (1, 0, 0), (1, 0, 1), (1, 0, 2), (1, 1, 0), (1, 1, 1),
    (1, 1, 2), (1, 1, 3), (1, 1, 4), (1, 2, 0), (1, 2, 1), (1, 2, 2), (1, 2, 3), (1, 2, 4)]

private def orb23 : ℕ := pack [
    0, 0, 6, 2, 4, 7, 8, 15, 16, 21, 5, 22, 14, 19, 13, 1, 9, 23, 10, 18, 3, 17, 20, 11, 12, 24,
    32, 40, 44, 36, 48, 56, 64, 72, 80, 88, 96, 104, 112, 120, 92, 124, 116, 108, 100, 52, 84, 76,
    68, 60, 25, 49, 89, 93, 53, 41, 65, 105, 117, 77, 37, 81, 121, 101, 61, 33, 57, 97, 125, 85,
    45, 73, 113, 109, 69, 27, 91, 55, 51, 95, 39, 123, 63, 83, 103, 47, 115, 71, 75, 111, 43, 107,
    79, 67, 119, 35, 99, 87, 59, 127, 26, 42, 38, 34, 46, 90, 106, 122, 98, 114, 54, 78, 62, 86,
    70, 50, 66, 82, 58, 74, 94, 118, 102, 126, 110]

private def rep23 : ℕ := pack [
    1, 6, 8, 25, 26, 27, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39]

private def gp23 : ℕ := pack [
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25,
    26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49,
    50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73,
    74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97,
    98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116,
    117, 118, 119, 120, 121, 122, 123, 124, 0, 15, 5, 20, 10, 1, 16, 6, 21, 11, 2, 17, 7, 22, 12,
    3, 18, 8, 23, 13, 4, 19, 9, 24, 14, 50, 65, 55, 70, 60, 51, 66, 56, 71, 61, 52, 67, 57, 72, 62,
    53, 68, 58, 73, 63, 54, 69, 59, 74, 64, 100, 115, 105, 120, 110, 101, 116, 106, 121, 111, 102,
    117, 107, 122, 112, 103, 118, 108, 123, 113, 104, 119, 109, 124, 114, 25, 40, 30, 45, 35, 26,
    41, 31, 46, 36, 27, 42, 32, 47, 37, 28, 43, 33, 48, 38, 29, 44, 34, 49, 39, 75, 90, 80, 95, 85,
    76, 91, 81, 96, 86, 77, 92, 82, 97, 87, 78, 93, 83, 98, 88, 79, 94, 84, 99, 89, 0, 3, 1, 4, 2,
    15, 18, 16, 19, 17, 5, 8, 6, 9, 7, 20, 23, 21, 24, 22, 10, 13, 11, 14, 12, 100, 103, 101, 104,
    102, 115, 118, 116, 119, 117, 105, 108, 106, 109, 107, 120, 123, 121, 124, 122, 110, 113, 111,
    114, 112, 75, 78, 76, 79, 77, 90, 93, 91, 94, 92, 80, 83, 81, 84, 82, 95, 98, 96, 99, 97, 85,
    88, 86, 89, 87, 50, 53, 51, 54, 52, 65, 68, 66, 69, 67, 55, 58, 56, 59, 57, 70, 73, 71, 74, 72,
    60, 63, 61, 64, 62, 25, 28, 26, 29, 27, 40, 43, 41, 44, 42, 30, 33, 31, 34, 32, 45, 48, 46, 49,
    47, 35, 38, 36, 39, 37, 0, 20, 15, 10, 5, 3, 23, 18, 13, 8, 1, 21, 16, 11, 6, 4, 24, 19, 14, 9,
    2, 22, 17, 12, 7, 75, 95, 90, 85, 80, 78, 98, 93, 88, 83, 76, 96, 91, 86, 81, 79, 99, 94, 89,
    84, 77, 97, 92, 87, 82, 25, 45, 40, 35, 30, 28, 48, 43, 38, 33, 26, 46, 41, 36, 31, 29, 49, 44,
    39, 34, 27, 47, 42, 37, 32, 100, 120, 115, 110, 105, 103, 123, 118, 113, 108, 101, 121, 116,
    111, 106, 104, 124, 119, 114, 109, 102, 122, 117, 112, 107, 50, 70, 65, 60, 55, 53, 73, 68, 63,
    58, 51, 71, 66, 61, 56, 54, 74, 69, 64, 59, 52, 72, 67, 62, 57, 0, 4, 3, 2, 1, 20, 24, 23, 22,
    21, 15, 19, 18, 17, 16, 10, 14, 13, 12, 11, 5, 9, 8, 7, 6, 25, 29, 28, 27, 26, 45, 49, 48, 47,
    46, 40, 44, 43, 42, 41, 35, 39, 38, 37, 36, 30, 34, 33, 32, 31, 50, 54, 53, 52, 51, 70, 74, 73,
    72, 71, 65, 69, 68, 67, 66, 60, 64, 63, 62, 61, 55, 59, 58, 57, 56, 75, 79, 78, 77, 76, 95, 99,
    98, 97, 96, 90, 94, 93, 92, 91, 85, 89, 88, 87, 86, 80, 84, 83, 82, 81, 100, 104, 103, 102,
    101, 120, 124, 123, 122, 121, 115, 119, 118, 117, 116, 110, 114, 113, 112, 111, 105, 109, 108,
    107, 106, 0, 10, 20, 5, 15, 4, 14, 24, 9, 19, 3, 13, 23, 8, 18, 2, 12, 22, 7, 17, 1, 11, 21, 6,
    16, 50, 60, 70, 55, 65, 54, 64, 74, 59, 69, 53, 63, 73, 58, 68, 52, 62, 72, 57, 67, 51, 61, 71,
    56, 66, 100, 110, 120, 105, 115, 104, 114, 124, 109, 119, 103, 113, 123, 108, 118, 102, 112,
    122, 107, 117, 101, 111, 121, 106, 116, 25, 35, 45, 30, 40, 29, 39, 49, 34, 44, 28, 38, 48, 33,
    43, 27, 37, 47, 32, 42, 26, 36, 46, 31, 41, 75, 85, 95, 80, 90, 79, 89, 99, 84, 94, 78, 88, 98,
    83, 93, 77, 87, 97, 82, 92, 76, 86, 96, 81, 91, 0, 2, 4, 1, 3, 10, 12, 14, 11, 13, 20, 22, 24,
    21, 23, 5, 7, 9, 6, 8, 15, 17, 19, 16, 18, 100, 102, 104, 101, 103, 110, 112, 114, 111, 113,
    120, 122, 124, 121, 123, 105, 107, 109, 106, 108, 115, 117, 119, 116, 118, 75, 77, 79, 76, 78,
    85, 87, 89, 86, 88, 95, 97, 99, 96, 98, 80, 82, 84, 81, 83, 90, 92, 94, 91, 93, 50, 52, 54, 51,
    53, 60, 62, 64, 61, 63, 70, 72, 74, 71, 73, 55, 57, 59, 56, 58, 65, 67, 69, 66, 68, 25, 27, 29,
    26, 28, 35, 37, 39, 36, 38, 45, 47, 49, 46, 48, 30, 32, 34, 31, 33, 40, 42, 44, 41, 43, 0, 5,
    10, 15, 20, 2, 7, 12, 17, 22, 4, 9, 14, 19, 24, 1, 6, 11, 16, 21, 3, 8, 13, 18, 23, 75, 80, 85,
    90, 95, 77, 82, 87, 92, 97, 79, 84, 89, 94, 99, 76, 81, 86, 91, 96, 78, 83, 88, 93, 98, 25, 30,
    35, 40, 45, 27, 32, 37, 42, 47, 29, 34, 39, 44, 49, 26, 31, 36, 41, 46, 28, 33, 38, 43, 48,
    100, 105, 110, 115, 120, 102, 107, 112, 117, 122, 104, 109, 114, 119, 124, 101, 106, 111, 116,
    121, 103, 108, 113, 118, 123, 50, 55, 60, 65, 70, 52, 57, 62, 67, 72, 54, 59, 64, 69, 74, 51,
    56, 61, 66, 71, 53, 58, 63, 68, 73]

private theorem orbitData23 : orbitData ⟨2, 0, 3, 3⟩ = tab23 := by
  have h1 : (orbitData ⟨2, 0, 3, 3⟩).lookup = tab23.lookup := by
    decide +kernel
  have h2 : (orbitData ⟨2, 0, 3, 3⟩).reps = tab23.reps := by
    decide +kernel
  exact tables_ext h1 h2

private theorem tablesOKb23 : tablesOKb ⟨2, 0, 3, 3⟩ tab23 = true := by
  decide +kernel

private theorem g8b23 : g8b ⟨2, 0, 3, 3⟩ = true := by
  decide +kernel

private def cd233 : Cd := ⟨2, 0, 3, 3, orb23, rep23, gp23⟩

private def cert233 : List Op := [
    .bv 0, .bk 0, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .bv 1, .p1 1, .p1 1, .p1 1, .p1 1, .p1 1,
    .cl 0 5, .p1 2, .p1 1, .cl 0 5, .cl 0 5, .p1 1, .cl 0 5, .cl 0 5, .cl 0 6, .cl 0 5, .p1 1,
    .p1 1, .p1 1, .bk 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1,
    .cl 0 5, .p1 2, .cl 0 5, .p1 1, .cl 0 5, .cl 0 5, .p1 1, .cl 0 5, .p1 2, .p1 1, .cl 0 5, .p1 2,
    .cl 0 6, .cl 0 5, .p1 2, .cl 0 6, .p1 3, .cl 0 5, .cl 0 7, .p1 3, .cl 0 5, .cl 0 6, .cl 0 8,
    .cl 0 5, .cl 0 6, .cl 0 8, .cl 0 5, .cl 0 6, .cl 0 8, .cl 0 5, .cl 0 6, .cl 0 8, .cl 0 6,
    .p1 12, .cl 0 5, .cl 0 6, .cl 0 8, .cl 0 6, .p1 14, .cl 0 5, .cl 0 6, .p1 15, .cl 0 5, .cl 0 6,
    .cl 0 7, .p1 10, .cl 0 5, .cl 0 7, .cl 0 5, .cl 0 6, .cl 0 8, .cl 0 5, .cl 0 6, .cl 0 7,
    .cl 0 5, .cl 0 7, .cl 0 5, .cl 0 7, .p1 15, .cl 0 6, .p1 3, .cl 0 5, .cl 0 6, .cl 0 8, .cl 0 5,
    .cl 0 6, .cl 0 8, .cl 0 5, .cl 0 6, .cl 0 8, .cl 0 5, .cl 0 6, .cl 0 8, .p1 1, .cl 0 5, .p1 2,
    .cl 0 6, .cl 0 5, .p1 2, .cl 0 6, .p1 3, .cl 0 5, .cl 0 7, .p1 3, .cl 0 5, .cl 0 6, .cl 0 8,
    .cl 0 5, .cl 0 6, .cl 0 8, .cl 0 5, .cl 0 6, .cl 0 8, .cl 0 5, .cl 0 6, .cl 0 8, .cl 0 6,
    .p1 10, .cl 0 5, .cl 0 6, .cl 0 8, .cl 0 6, .p1 12, .cl 0 5, .cl 0 6, .p1 7, .cl 0 5, .cl 0 6,
    .cl 0 7, .p1 9, .cl 0 5, .cl 0 7, .cl 0 5, .cl 0 6, .cl 0 8, .cl 0 5, .cl 0 6, .cl 0 7,
    .cl 0 5, .cl 0 7, .cl 0 5, .cl 0 7, .p1 7, .cl 0 6, .p1 3, .cl 0 5, .cl 0 6, .cl 0 8, .cl 0 5,
    .cl 0 6, .cl 0 8, .cl 0 5, .cl 0 6, .cl 0 8, .cl 0 5, .cl 0 6, .cl 0 8, .p1 1, .cl 0 5, .p1 2,
    .cl 0 6, .cl 0 5, .p1 2, .cl 0 6, .p1 3, .cl 0 5, .cl 0 7, .p1 3, .cl 0 5, .cl 0 6, .cl 0 8,
    .cl 0 5, .cl 0 6, .cl 0 8, .cl 0 5, .cl 0 6, .cl 0 8, .cl 0 5, .cl 0 6, .cl 0 8, .cl 0 6,
    .p1 14, .cl 0 5, .cl 0 6, .cl 0 8, .cl 0 6, .p1 9, .cl 0 5, .cl 0 6, .p1 13, .cl 0 5, .cl 0 6,
    .cl 0 7, .p1 12, .cl 0 5, .cl 0 7, .cl 0 5, .cl 0 6, .cl 0 8, .cl 0 5, .cl 0 6, .cl 0 7,
    .cl 0 5, .cl 0 7, .cl 0 5, .cl 0 7, .p1 13, .cl 0 6, .p1 3, .cl 0 5, .cl 0 6, .cl 0 8, .cl 0 5,
    .cl 0 6, .cl 0 8, .cl 0 5, .cl 0 6, .cl 0 8, .cl 0 5, .cl 0 6, .cl 0 8, .p1 1, .cl 0 5, .p1 2,
    .cl 0 6, .cl 0 5, .p1 2, .cl 0 6, .p1 3, .cl 0 5, .cl 0 7, .p1 3, .cl 0 5, .cl 0 6, .cl 0 8,
    .cl 0 5, .cl 0 6, .cl 0 8, .cl 0 5, .cl 0 6, .cl 0 8, .cl 0 5, .cl 0 6, .cl 0 8, .cl 0 6,
    .p1 9, .cl 0 5, .cl 0 6, .cl 0 8, .cl 0 6, .p1 10, .cl 0 5, .cl 0 6, .p1 8, .cl 0 5, .cl 0 6,
    .cl 0 7, .p1 14, .cl 0 5, .cl 0 7, .cl 0 5, .cl 0 6, .cl 0 8, .cl 0 5, .cl 0 6, .cl 0 7,
    .cl 0 5, .cl 0 7, .cl 0 5, .cl 0 7, .p1 8, .cl 0 6, .p1 3, .cl 0 5, .cl 0 6, .cl 0 8, .cl 0 5,
    .cl 0 6, .cl 0 8, .cl 0 5, .cl 0 6, .cl 0 8, .cl 0 5, .cl 0 6, .cl 0 8, .cl 0 1, .cl 0 1,
    .cl 0 1, .bk 0, .cl 0 1, .cl 0 1, .bv 1, .p1 1, .p1 1, .p1 1, .p1 1, .p1 1, .cl 0 5, .cl 0 6,
    .p1 1, .cl 0 5, .bk 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1,
    .p1 1, .cl 0 5, .cl 0 5, .p1 2, .cl 0 5, .p1 1, .p1 1, .p1 1, .cl 0 5, .cl 0 5, .p1 2, .cl 0 5,
    .p1 1, .cl 0 5, .cl 0 5, .p1 1, .cl 0 5, .p1 2, .p1 1, .cl 0 5, .cl 0 8, .p1 6, .cl 0 5,
    .cl 0 6, .cl 0 5, .cl 0 7, .cl 0 8, .cl 0 5, .cl 0 6, .p1 3, .cl 0 5, .cl 0 8, .p1 15, .cl 0 5,
    .cl 0 8, .p1 11, .cl 0 5, .cl 0 8, .p1 12, .cl 0 5, .cl 0 8, .p1 13, .cl 0 5, .cl 0 8, .p1 14,
    .cl 0 5, .p1 2, .cl 0 5, .cl 0 8, .p1 11, .cl 0 5, .cl 0 6, .cl 0 5, .cl 0 8, .cl 0 5, .cl 0 8,
    .p1 13, .cl 0 5, .cl 0 7, .cl 0 5, .cl 0 8, .p1 6, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 5, .cl 0 8,
    .p1 9, .cl 0 5, .cl 0 8, .p1 8, .cl 0 5, .p1 2, .cl 0 5, .cl 0 8, .p1 3, .cl 0 5, .cl 0 6,
    .p1 8, .cl 0 5, .cl 0 8, .cl 0 5, .cl 0 6, .p1 3, .p1 1, .cl 0 5, .cl 0 8, .p1 5, .cl 0 5,
    .cl 0 6, .cl 0 5, .cl 0 7, .cl 0 8, .cl 0 5, .cl 0 6, .p1 3, .cl 0 5, .cl 0 8, .p1 7, .cl 0 5,
    .cl 0 8, .p1 4, .cl 0 5, .cl 0 8, .p1 10, .cl 0 5, .cl 0 8, .p1 15, .cl 0 5, .cl 0 8, .p1 12,
    .cl 0 5, .p1 2, .cl 0 5, .cl 0 8, .p1 4, .cl 0 5, .cl 0 6, .cl 0 5, .cl 0 8, .cl 0 5, .cl 0 8,
    .p1 15, .cl 0 5, .cl 0 7, .cl 0 5, .cl 0 8, .p1 5, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 5, .cl 0 8,
    .p1 14, .cl 0 5, .cl 0 8, .p1 13, .cl 0 5, .p1 2, .cl 0 5, .cl 0 8, .p1 3, .cl 0 5, .cl 0 6,
    .p1 13, .cl 0 5, .cl 0 8, .cl 0 5, .cl 0 6, .p1 3, .p1 1, .cl 0 5, .cl 0 8, .p1 4, .cl 0 5,
    .cl 0 6, .cl 0 5, .cl 0 7, .cl 0 8, .cl 0 5, .cl 0 6, .p1 3, .cl 0 5, .cl 0 8, .p1 13, .cl 0 5,
    .cl 0 8, .p1 5, .cl 0 5, .cl 0 8, .p1 14, .cl 0 5, .cl 0 8, .p1 8, .cl 0 5, .cl 0 8, .p1 9,
    .cl 0 5, .p1 2, .cl 0 5, .cl 0 8, .p1 5, .cl 0 5, .cl 0 6, .cl 0 5, .cl 0 8, .cl 0 5, .cl 0 8,
    .p1 8, .cl 0 5, .cl 0 7, .cl 0 5, .cl 0 8, .p1 4, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 5, .cl 0 8,
    .p1 10, .cl 0 5, .cl 0 8, .p1 7, .cl 0 5, .p1 2, .cl 0 5, .cl 0 8, .p1 3, .cl 0 5, .cl 0 6,
    .p1 7, .cl 0 5, .cl 0 8, .cl 0 5, .cl 0 6, .p1 3, .p1 1, .cl 0 5, .cl 0 8, .p1 11, .cl 0 5,
    .cl 0 6, .cl 0 5, .cl 0 7, .cl 0 8, .cl 0 5, .cl 0 6, .p1 3, .cl 0 5, .cl 0 8, .p1 8, .cl 0 5,
    .cl 0 8, .p1 6, .cl 0 5, .cl 0 8, .p1 9, .cl 0 5, .cl 0 8, .p1 7, .cl 0 5, .cl 0 8, .p1 10,
    .cl 0 5, .p1 2, .cl 0 5, .cl 0 8, .p1 6, .cl 0 5, .cl 0 6, .cl 0 5, .cl 0 8, .cl 0 5, .cl 0 8,
    .p1 7, .cl 0 5, .cl 0 7, .cl 0 5, .cl 0 8, .p1 11, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 5, .cl 0 8,
    .p1 12, .cl 0 5, .cl 0 8, .p1 15, .cl 0 5, .p1 2, .cl 0 5, .cl 0 8, .p1 3, .cl 0 5, .cl 0 6,
    .p1 15, .cl 0 5, .cl 0 8, .cl 0 5, .cl 0 6, .p1 3, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .bk 0, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .bv 1, .p1 1, .p1 1, .p1 1, .p1 1,
    .p1 1, .cl 0 5, .cl 0 6, .p1 1, .cl 0 5, .cl 0 5, .p1 1, .cl 0 5, .cl 0 5, .p1 2, .cl 0 5,
    .p1 1, .p1 1, .p1 1, .cl 0 5, .cl 0 5, .p1 2, .cl 0 5, .p1 1, .bk 1, .cl 1 1, .cl 1 1, .cl 1 1,
    .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 0 5, .p1 1, .cl 0 5, .p1 2, .p1 1, .cl 0 5,
    .cl 0 6, .cl 0 5, .cl 0 6, .cl 0 5, .p1 2, .cl 0 5, .p1 2, .cl 0 7, .p1 3, .cl 0 5, .cl 0 7,
    .p1 4, .cl 0 5, .cl 0 7, .p1 5, .cl 0 5, .cl 0 6, .p1 3, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 5,
    .cl 0 7, .p1 6, .cl 0 5, .cl 0 7, .p1 7, .cl 0 5, .cl 0 7, .p1 8, .cl 0 5, .cl 0 7, .p1 9,
    .cl 0 5, .cl 0 7, .p1 10, .cl 0 7, .cl 0 5, .cl 0 6, .p1 14, .cl 0 5, .cl 0 6, .cl 0 7,
    .cl 0 5, .cl 0 6, .p1 12, .cl 0 5, .cl 0 6, .p1 11, .cl 0 5, .cl 0 7, .p1 11, .cl 0 5, .cl 0 7,
    .p1 15, .cl 0 5, .cl 0 7, .p1 14, .cl 0 5, .cl 0 7, .p1 13, .cl 0 5, .cl 0 7, .p1 12, .p1 1,
    .cl 0 5, .cl 0 6, .cl 0 5, .cl 0 6, .cl 0 5, .p1 2, .cl 0 5, .p1 2, .cl 0 7, .p1 3, .cl 0 5,
    .cl 0 7, .p1 6, .cl 0 5, .cl 0 7, .p1 11, .cl 0 5, .cl 0 6, .p1 3, .cl 0 5, .cl 0 6, .cl 0 7,
    .cl 0 5, .cl 0 7, .p1 5, .cl 0 5, .cl 0 7, .p1 8, .cl 0 5, .cl 0 7, .p1 13, .cl 0 5, .cl 0 7,
    .p1 14, .cl 0 5, .cl 0 7, .p1 9, .cl 0 7, .cl 0 5, .cl 0 6, .p1 12, .cl 0 5, .cl 0 6, .cl 0 7,
    .cl 0 5, .cl 0 6, .p1 10, .cl 0 5, .cl 0 6, .p1 4, .cl 0 5, .cl 0 7, .p1 4, .cl 0 5, .cl 0 7,
    .p1 7, .cl 0 5, .cl 0 7, .p1 12, .cl 0 5, .cl 0 7, .p1 15, .cl 0 5, .cl 0 7, .p1 10, .p1 1,
    .cl 0 5, .cl 0 6, .cl 0 5, .cl 0 6, .cl 0 5, .p1 2, .cl 0 5, .p1 2, .cl 0 7, .p1 3, .cl 0 5,
    .cl 0 7, .p1 11, .cl 0 5, .cl 0 7, .p1 6, .cl 0 5, .cl 0 6, .p1 3, .cl 0 5, .cl 0 6, .cl 0 7,
    .cl 0 5, .cl 0 7, .p1 4, .cl 0 5, .cl 0 7, .p1 15, .cl 0 5, .cl 0 7, .p1 7, .cl 0 5, .cl 0 7,
    .p1 10, .cl 0 5, .cl 0 7, .p1 12, .cl 0 7, .cl 0 5, .cl 0 6, .p1 9, .cl 0 5, .cl 0 6, .cl 0 7,
    .cl 0 5, .cl 0 6, .p1 14, .cl 0 5, .cl 0 6, .p1 5, .cl 0 5, .cl 0 7, .p1 5, .cl 0 5, .cl 0 7,
    .p1 13, .cl 0 5, .cl 0 7, .p1 9, .cl 0 5, .cl 0 7, .p1 8, .cl 0 5, .cl 0 7, .p1 14, .p1 1,
    .cl 0 5, .cl 0 6, .cl 0 5, .cl 0 6, .cl 0 5, .p1 2, .cl 0 5, .p1 2, .cl 0 7, .p1 3, .cl 0 5,
    .cl 0 7, .p1 5, .cl 0 5, .cl 0 7, .p1 4, .cl 0 5, .cl 0 6, .p1 3, .cl 0 5, .cl 0 6, .cl 0 7,
    .cl 0 5, .cl 0 7, .p1 11, .cl 0 5, .cl 0 7, .p1 13, .cl 0 5, .cl 0 7, .p1 15, .cl 0 5, .cl 0 7,
    .p1 12, .cl 0 5, .cl 0 7, .p1 14, .cl 0 7, .cl 0 5, .cl 0 6, .p1 10, .cl 0 5, .cl 0 6, .cl 0 7,
    .cl 0 5, .cl 0 6, .p1 9, .cl 0 5, .cl 0 6, .p1 6, .cl 0 5, .cl 0 7, .p1 6, .cl 0 5, .cl 0 7,
    .p1 8, .cl 0 5, .cl 0 7, .p1 10, .cl 0 5, .cl 0 7, .p1 7, .cl 0 5, .cl 0 7, .p1 9, .cl 0 1,
    .bk 0, .bv 1, .p1 1, .p1 1, .p1 1, .p1 1, .p1 1, .cl 0 5, .p1 2, .p1 1, .cl 0 5, .cl 0 5,
    .p1 1, .cl 0 5, .cl 0 5, .cl 0 6, .bk 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1,
    .cl 1 1, .cl 1 1, .p1 1, .p1 1, .p1 1, .cl 0 5, .cl 0 5, .p1 2, .cl 0 5, .p1 1, .cl 0 5,
    .cl 0 5, .p1 1, .cl 0 5, .p1 2, .p1 1, .cl 0 5, .cl 0 6, .p1 5, .cl 0 6, .cl 0 5, .cl 0 6,
    .p1 4, .cl 0 6, .p1 3, .cl 0 5, .cl 0 6, .p1 7, .cl 0 5, .cl 0 6, .p1 8, .cl 0 5, .cl 0 6,
    .p1 9, .cl 0 5, .cl 0 6, .p1 10, .cl 0 5, .cl 0 6, .p1 6, .cl 0 5, .cl 0 6, .p1 12, .cl 0 5,
    .cl 0 6, .p1 13, .cl 0 5, .cl 0 6, .p1 14, .cl 0 5, .cl 0 6, .p1 15, .cl 0 5, .cl 0 6, .p1 11,
    .cl 0 5, .p1 2, .cl 0 5, .cl 0 6, .p1 14, .cl 0 5, .cl 0 6, .p1 13, .cl 0 5, .cl 0 6, .p1 12,
    .cl 0 5, .cl 0 6, .p1 11, .cl 0 5, .p1 2, .cl 0 5, .cl 0 6, .p1 9, .cl 0 5, .cl 0 6, .cl 0 5,
    .cl 0 6, .p1 7, .cl 0 5, .cl 0 6, .p1 6, .p1 1, .cl 0 5, .cl 0 6, .p1 11, .cl 0 6, .cl 0 5,
    .cl 0 6, .p1 6, .cl 0 6, .p1 3, .cl 0 5, .cl 0 6, .p1 8, .cl 0 5, .cl 0 6, .p1 13, .cl 0 5,
    .cl 0 6, .p1 14, .cl 0 5, .cl 0 6, .p1 9, .cl 0 5, .cl 0 6, .p1 5, .cl 0 5, .cl 0 6, .p1 10,
    .cl 0 5, .cl 0 6, .p1 15, .cl 0 5, .cl 0 6, .p1 12, .cl 0 5, .cl 0 6, .p1 7, .cl 0 5, .cl 0 6,
    .p1 4, .cl 0 5, .p1 2, .cl 0 5, .cl 0 6, .p1 12, .cl 0 5, .cl 0 6, .p1 15, .cl 0 5, .cl 0 6,
    .p1 10, .cl 0 5, .cl 0 6, .p1 4, .cl 0 5, .p1 2, .cl 0 5, .cl 0 6, .p1 14, .cl 0 5, .cl 0 6,
    .cl 0 5, .cl 0 6, .p1 8, .cl 0 5, .cl 0 6, .p1 5, .p1 1, .cl 0 5, .cl 0 6, .p1 6, .cl 0 6,
    .cl 0 5, .cl 0 6, .p1 11, .cl 0 6, .p1 3, .cl 0 5, .cl 0 6, .p1 15, .cl 0 5, .cl 0 6, .p1 7,
    .cl 0 5, .cl 0 6, .p1 10, .cl 0 5, .cl 0 6, .p1 12, .cl 0 5, .cl 0 6, .p1 4, .cl 0 5, .cl 0 6,
    .p1 14, .cl 0 5, .cl 0 6, .p1 8, .cl 0 5, .cl 0 6, .p1 9, .cl 0 5, .cl 0 6, .p1 13, .cl 0 5,
    .cl 0 6, .p1 5, .cl 0 5, .p1 2, .cl 0 5, .cl 0 6, .p1 9, .cl 0 5, .cl 0 6, .p1 8, .cl 0 5,
    .cl 0 6, .p1 14, .cl 0 5, .cl 0 6, .p1 5, .cl 0 5, .p1 2, .cl 0 5, .cl 0 6, .p1 10, .cl 0 5,
    .cl 0 6, .cl 0 5, .cl 0 6, .p1 15, .cl 0 5, .cl 0 6, .p1 4, .p1 1, .cl 0 5, .cl 0 6, .p1 4,
    .cl 0 6, .cl 0 5, .cl 0 6, .p1 5, .cl 0 6, .p1 3, .cl 0 5, .cl 0 6, .p1 13, .cl 0 5, .cl 0 6,
    .p1 15, .cl 0 5, .cl 0 6, .p1 12, .cl 0 5, .cl 0 6, .p1 14, .cl 0 5, .cl 0 6, .p1 11, .cl 0 5,
    .cl 0 6, .p1 9, .cl 0 5, .cl 0 6, .p1 7, .cl 0 5, .cl 0 6, .p1 10, .cl 0 5, .cl 0 6, .p1 8,
    .cl 0 5, .cl 0 6, .p1 6, .cl 0 5, .p1 2, .cl 0 5, .cl 0 6, .p1 10, .cl 0 5, .cl 0 6, .p1 7,
    .cl 0 5, .cl 0 6, .p1 9, .cl 0 5, .cl 0 6, .p1 6, .cl 0 5, .p1 2, .cl 0 5, .cl 0 6, .p1 12,
    .cl 0 5, .cl 0 6, .cl 0 5, .cl 0 6, .p1 13, .cl 0 5, .cl 0 6, .p1 11, .cl 0 2, .cl 0 2,
    .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .p1 0, .bk 0, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .bk 0, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3,
    .cl 0 3, .cl 0 3, .cl 0 3, .bk 0, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 2, .bk 0, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .p1 0, .bk 0, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 4, .cl 0 2, .cl 0 2,
    .bk 0, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .bk 0, .cl 0 2,
    .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .bk 0, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .p1 0, .bk 0, .cl 0 2, .cl 0 4, .cl 0 2,
    .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .bk 0, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2,
    .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .bk 0, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2,
    .cl 0 2, .cl 0 2, .cl 0 2, .bk 0, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .p1 0, .bk 0, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .bk 0, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .bk 0,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .bk 0, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .p1 0, .bk 0, .cl 0 1, .p1 5,
    .cl 0 1, .cl 0 2, .cl 0 1, .p1 3, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2,
    .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .bk 0, .cl 0 1, .cl 0 2, .cl 0 1, .p1 4, .cl 0 1, .cl 0 4,
    .cl 0 1, .p1 4, .cl 0 1, .cl 0 2, .cl 0 1, .p1 4, .cl 0 1, .cl 0 2, .cl 0 1, .p1 4, .bk 0,
    .cl 0 1, .p1 3, .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3,
    .cl 0 1, .cl 0 3, .cl 0 1, .p1 4, .cl 0 1, .cl 0 3, .bk 0, .cl 0 2, .cl 0 3, .cl 0 2, .p1 5,
    .cl 0 2, .cl 0 3, .cl 0 2, .p1 5, .cl 0 2, .cl 0 3, .cl 0 2, .p1 5, .cl 0 2, .cl 0 4, .cl 0 2,
    .p1 5, .bk 0, .cl 0 5, .p1 3, .cl 0 10, .cl 0 5, .p1 3, .cl 0 5, .p1 3, .cl 0 5, .p1 3,
    .cl 0 5, .p1 3, .cl 0 5, .p1 3, .cl 0 5, .p1 3, .bk 0, .cl 0 31, .cl 0 48, .cl 0 31, .cl 0 32,
    .cl 0 35, .cl 0 31, .cl 0 48, .cl 0 31, .cl 0 48, .cl 0 56, .cl 0 61, .cl 0 62, .cl 0 65,
    .cl 0 31, .cl 0 32, .cl 0 45, .cl 0 31, .cl 0 32, .cl 0 37, .cl 0 31, .cl 0 32, .cl 0 39,
    .cl 0 31, .cl 0 48, .cl 0 55, .cl 0 56, .bk 0, .cl 0 32, .cl 0 37, .cl 0 39, .cl 0 32,
    .cl 0 37, .cl 0 43, .cl 0 32, .cl 0 43, .cl 0 53, .p1 6, .cl 0 32, .cl 0 43, .cl 0 32,
    .cl 0 43, .cl 0 32, .cl 0 43, .cl 0 32, .cl 0 43, .cl 0 47, .cl 0 32, .cl 0 37, .cl 0 43,
    .bk 0, .cl 0 33, .cl 0 42, .cl 0 33, .cl 0 38, .cl 0 42, .cl 0 33, .cl 0 42, .cl 0 48,
    .cl 0 33, .cl 0 42, .cl 0 33, .cl 0 42, .cl 0 33, .cl 0 42, .cl 0 33, .cl 0 42, .cl 0 52,
    .p1 6, .cl 0 33, .cl 0 38, .cl 0 42, .bk 0, .cl 0 34, .cl 0 61, .p1 3, .cl 0 34, .cl 0 47,
    .cl 0 34, .cl 0 47, .p1 1, .cl 0 34, .cl 0 47, .cl 0 49, .cl 0 34, .cl 0 47, .cl 0 34,
    .cl 0 47, .cl 0 34, .cl 0 47, .cl 0 34, .cl 0 47, .cl 0 55, .cl 0 59, .bk 0, .cl 0 10, .p1 3,
    .cl 0 10, .p1 3, .cl 0 10, .p1 3, .cl 0 10, .p1 3, .cl 0 10, .p1 3, .cl 0 10, .p1 3, .cl 0 10,
    .p1 3, .cl 0 20, .bk 0, .cl 0 36, .cl 0 61, .cl 0 65, .cl 0 36, .cl 0 61, .cl 0 67, .cl 0 36,
    .cl 0 46, .cl 0 47, .cl 0 36, .cl 0 83, .cl 0 36, .cl 0 69, .p1 3, .cl 0 36, .cl 0 46,
    .cl 0 60, .cl 0 36, .cl 0 46, .cl 0 55, .cl 0 61, .cl 0 62, .cl 0 36, .cl 0 46, .cl 0 58,
    .bk 0, .cl 0 37, .cl 0 41, .cl 0 37, .cl 0 41, .cl 0 42, .cl 0 37, .cl 0 39, .cl 0 40,
    .cl 0 37, .cl 0 41, .cl 0 37, .cl 0 39, .cl 0 41, .cl 0 37, .cl 0 41, .cl 0 57, .p1 12,
    .cl 0 37, .cl 0 41, .cl 0 37, .cl 0 41, .bk 0, .cl 0 38, .cl 0 44, .p1 1, .cl 0 38, .cl 0 44,
    .cl 0 57, .p1 11, .cl 0 38, .cl 0 44, .cl 0 38, .cl 0 44, .cl 0 38, .cl 0 44, .cl 0 38,
    .cl 0 44, .cl 0 58, .p1 15, .cl 0 38, .cl 0 44, .cl 0 47, .cl 0 38, .cl 0 44, .bk 0, .cl 0 39,
    .cl 0 66, .p1 3, .cl 0 39, .cl 0 66, .p1 3, .cl 0 39, .cl 0 49, .cl 0 55, .cl 0 61, .p1 6,
    .cl 0 39, .cl 0 82, .cl 0 39, .cl 0 64, .cl 0 65, .cl 0 39, .cl 0 49, .cl 0 60, .cl 0 39,
    .cl 0 49, .cl 0 66, .p1 3, .cl 0 39, .cl 0 49, .cl 0 57, .bk 0, .cl 0 5, .cl 0 5, .cl 0 5,
    .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .bk 0, .cl 0 41, .cl 0 49, .cl 0 63, .p1 4,
    .cl 0 41, .cl 0 49, .cl 0 57, .p1 8, .cl 0 41, .cl 0 49, .cl 0 41, .cl 0 49, .p1 2, .cl 0 41,
    .cl 0 49, .cl 0 54, .p1 11, .cl 0 41, .cl 0 49, .cl 0 41, .cl 0 49, .cl 0 41, .cl 0 49, .bk 0,
    .cl 0 42, .cl 0 58, .cl 0 71, .cl 0 72, .cl 0 77, .cl 0 42, .cl 0 63, .p1 3, .cl 0 42,
    .cl 0 44, .cl 0 52, .cl 0 42, .cl 0 44, .cl 0 45, .cl 0 42, .cl 0 44, .cl 0 47, .cl 0 42,
    .cl 0 58, .cl 0 67, .cl 0 69, .p1 7, .cl 0 42, .cl 0 63, .p1 3, .cl 0 42, .cl 0 44, .cl 0 46,
    .bk 0, .cl 0 43, .cl 0 57, .p1 6, .cl 0 43, .cl 0 62, .p1 3, .cl 0 43, .cl 0 62, .p1 3,
    .cl 0 43, .cl 0 62, .p1 3, .cl 0 43, .cl 0 57, .cl 0 77, .p1 3, .cl 0 43, .cl 0 57, .cl 0 77,
    .p1 12, .cl 0 43, .cl 0 57, .p1 3, .cl 0 43, .cl 0 57, .p1 6, .bk 0, .cl 0 44, .cl 0 46,
    .cl 0 51, .p1 11, .cl 0 44, .cl 0 46, .cl 0 58, .p1 9, .cl 0 44, .cl 0 46, .cl 0 44, .cl 0 46,
    .p1 1, .cl 0 44, .cl 0 46, .cl 0 61, .p1 3, .cl 0 44, .cl 0 46, .cl 0 44, .cl 0 46, .cl 0 44,
    .cl 0 46, .bk 0, .cl 0 15, .cl 0 15, .cl 0 15, .cl 0 15, .cl 0 15, .cl 0 15, .cl 0 15,
    .cl 0 15, .bk 0, .cl 0 46, .cl 0 59, .p1 3, .cl 0 46, .cl 0 47, .cl 0 59, .p1 3, .cl 0 46,
    .cl 0 69, .cl 0 79, .p1 3, .cl 0 46, .cl 0 59, .p1 3, .cl 0 46, .cl 0 47, .cl 0 51, .cl 0 46,
    .cl 0 47, .cl 0 52, .p1 8, .cl 0 46, .cl 0 47, .cl 0 59, .p1 3, .cl 0 46, .cl 0 69, .cl 0 71,
    .cl 0 72, .p1 13, .bk 0, .cl 0 47, .cl 0 59, .p1 4, .cl 0 47, .cl 0 59, .cl 0 61, .cl 0 62,
    .cl 0 47, .cl 0 58, .p1 3, .cl 0 47, .cl 0 58, .p1 3, .cl 0 47, .cl 0 58, .p1 3, .cl 0 47,
    .cl 0 59, .p1 4, .cl 0 47, .cl 0 59, .cl 0 72, .cl 0 79, .cl 0 47, .cl 0 58, .p1 3, .bk 0,
    .cl 0 48, .cl 0 57, .p1 3, .cl 0 48, .cl 0 56, .cl 0 64, .cl 0 71, .p1 15, .cl 0 48, .cl 0 56,
    .cl 0 73, .cl 0 76, .cl 0 48, .cl 0 56, .p1 3, .cl 0 48, .cl 0 56, .p1 4, .cl 0 48, .cl 0 56,
    .p1 4, .cl 0 48, .cl 0 57, .p1 3, .cl 0 48, .cl 0 57, .p1 3, .bk 0, .cl 0 49, .cl 0 56, .p1 3,
    .cl 0 49, .cl 0 66, .p1 11, .cl 0 49, .cl 0 66, .p1 11, .cl 0 49, .cl 0 56, .p1 3, .cl 0 49,
    .cl 0 56, .p1 3, .cl 0 49, .cl 0 56, .p1 3, .cl 0 49, .cl 0 66, .cl 0 76, .p1 3, .cl 0 49,
    .cl 0 66, .cl 0 76, .p1 9, .p1 0, .bk 0, .cl 0 1, .p1 11, .cl 0 1, .cl 0 2, .cl 0 1, .p1 3,
    .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2,
    .bk 0, .cl 0 1, .cl 0 2, .cl 0 1, .p1 6, .cl 0 1, .cl 0 4, .cl 0 1, .p1 6, .cl 0 1, .cl 0 2,
    .cl 0 1, .p1 6, .cl 0 1, .cl 0 2, .cl 0 1, .p1 6, .bk 0, .cl 0 1, .p1 3, .cl 0 1, .cl 0 3,
    .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3, .cl 0 1, .p1 6,
    .cl 0 1, .cl 0 3, .bk 0, .cl 0 2, .cl 0 3, .cl 0 2, .p1 11, .cl 0 2, .cl 0 3, .cl 0 2, .p1 11,
    .cl 0 2, .cl 0 3, .cl 0 2, .p1 11, .cl 0 2, .cl 0 4, .cl 0 2, .p1 11, .bk 0, .cl 0 5, .p1 3,
    .cl 0 10, .cl 0 5, .p1 3, .cl 0 5, .p1 3, .cl 0 5, .p1 3, .cl 0 5, .p1 3, .cl 0 5, .p1 3,
    .cl 0 5, .p1 3, .bk 0, .cl 0 56, .cl 0 73, .cl 0 56, .cl 0 57, .cl 0 60, .cl 0 56, .cl 0 73,
    .cl 0 56, .cl 0 87, .cl 0 56, .cl 0 57, .cl 0 70, .cl 0 56, .cl 0 57, .cl 0 62, .cl 0 56,
    .cl 0 57, .cl 0 64, .cl 0 56, .cl 0 73, .cl 0 76, .bk 0, .cl 0 57, .cl 0 62, .cl 0 64,
    .cl 0 57, .cl 0 62, .cl 0 68, .cl 0 57, .cl 0 81, .cl 0 91, .cl 0 93, .cl 0 57, .cl 0 68,
    .cl 0 57, .cl 0 68, .cl 0 57, .cl 0 68, .cl 0 57, .cl 0 68, .cl 0 72, .cl 0 57, .cl 0 62,
    .cl 0 68, .bk 0, .cl 0 58, .cl 0 67, .cl 0 58, .cl 0 63, .cl 0 67, .cl 0 58, .cl 0 67,
    .cl 0 73, .cl 0 58, .cl 0 67, .cl 0 58, .cl 0 67, .cl 0 58, .cl 0 67, .cl 0 58, .cl 0 67,
    .cl 0 84, .cl 0 89, .cl 0 91, .p1 10, .cl 0 58, .cl 0 63, .cl 0 67, .bk 0, .cl 0 59, .cl 0 72,
    .cl 0 86, .p1 11, .cl 0 59, .cl 0 72, .cl 0 59, .cl 0 72, .p1 1, .cl 0 59, .cl 0 72, .cl 0 74,
    .cl 0 59, .cl 0 72, .cl 0 59, .cl 0 72, .cl 0 59, .cl 0 72, .cl 0 59, .cl 0 72, .cl 0 76,
    .cl 0 77, .cl 0 78, .bk 0, .cl 0 10, .p1 3, .cl 0 10, .p1 3, .cl 0 10, .p1 3, .cl 0 10, .p1 3,
    .cl 0 10, .p1 3, .cl 0 10, .p1 3, .cl 0 10, .p1 3, .cl 0 20, .bk 0, .cl 0 61, .cl 0 88, .p1 7,
    .cl 0 83, .p1 12, .cl 0 61, .cl 0 71, .cl 0 72, .cl 0 83, .p1 12, .cl 0 61, .cl 0 83, .cl 0 92,
    .p1 5, .cl 0 61, .cl 0 71, .cl 0 78, .p1 15, .cl 0 61, .cl 0 71, .cl 0 79, .cl 0 61, .cl 0 71,
    .cl 0 83, .bk 0, .cl 0 62, .cl 0 66, .cl 0 62, .cl 0 66, .cl 0 67, .cl 0 62, .cl 0 64,
    .cl 0 65, .cl 0 62, .cl 0 66, .cl 0 62, .cl 0 64, .cl 0 66, .cl 0 62, .cl 0 66, .cl 0 77,
    .cl 0 62, .cl 0 66, .cl 0 62, .cl 0 66, .bk 0, .cl 0 63, .cl 0 69, .p1 1, .cl 0 63, .cl 0 69,
    .cl 0 81, .cl 0 63, .cl 0 69, .cl 0 63, .cl 0 69, .cl 0 63, .cl 0 69, .cl 0 63, .cl 0 69,
    .cl 0 78, .cl 0 63, .cl 0 69, .cl 0 72, .cl 0 63, .cl 0 69, .bk 0, .cl 0 64, .cl 0 82,
    .cl 0 93, .p1 5, .cl 0 82, .p1 15, .cl 0 64, .cl 0 74, .cl 0 76, .cl 0 82, .p1 15, .cl 0 64,
    .cl 0 87, .p1 10, .cl 0 64, .cl 0 74, .cl 0 77, .p1 12, .cl 0 64, .cl 0 74, .cl 0 89, .cl 0 64,
    .cl 0 74, .cl 0 81, .p1 11, .bk 0, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5,
    .cl 0 5, .cl 0 5, .bk 0, .cl 0 66, .cl 0 74, .cl 0 93, .cl 0 66, .cl 0 82, .cl 0 66, .cl 0 74,
    .cl 0 66, .cl 0 74, .p1 2, .cl 0 66, .cl 0 74, .cl 0 87, .cl 0 66, .cl 0 74, .cl 0 66,
    .cl 0 74, .cl 0 66, .cl 0 74, .bk 0, .cl 0 67, .cl 0 97, .cl 0 99, .cl 0 67, .cl 0 84,
    .cl 0 67, .cl 0 69, .cl 0 83, .p1 6, .cl 0 67, .cl 0 69, .cl 0 70, .cl 0 67, .cl 0 69,
    .cl 0 72, .cl 0 67, .cl 0 84, .cl 0 67, .cl 0 83, .p1 3, .cl 0 67, .cl 0 69, .cl 0 71, .bk 0,
    .cl 0 68, .cl 0 82, .cl 0 102, .cl 0 68, .cl 0 81, .cl 0 68, .cl 0 82, .p1 3, .cl 0 68,
    .cl 0 81, .cl 0 68, .cl 0 98, .cl 0 99, .cl 0 102, .cl 0 68, .cl 0 81, .cl 0 68, .cl 0 98,
    .cl 0 99, .cl 0 106, .cl 0 68, .cl 0 81, .bk 0, .cl 0 69, .cl 0 71, .cl 0 88, .cl 0 69,
    .cl 0 83, .cl 0 69, .cl 0 71, .cl 0 69, .cl 0 71, .p1 1, .cl 0 69, .cl 0 71, .cl 0 88,
    .cl 0 90, .cl 0 91, .cl 0 69, .cl 0 71, .cl 0 69, .cl 0 71, .cl 0 69, .cl 0 71, .bk 0,
    .cl 0 15, .cl 0 15, .cl 0 15, .cl 0 15, .cl 0 15, .cl 0 15, .cl 0 15, .cl 0 15, .bk 0,
    .cl 0 71, .cl 0 94, .p1 3, .cl 0 71, .cl 0 72, .cl 0 84, .p1 3, .cl 0 71, .cl 0 86, .cl 0 87,
    .cl 0 71, .cl 0 86, .cl 0 87, .p1 12, .cl 0 71, .cl 0 86, .cl 0 87, .cl 0 88, .cl 0 71,
    .cl 0 72, .cl 0 80, .cl 0 71, .cl 0 72, .cl 0 83, .p1 4, .cl 0 71, .cl 0 86, .p1 8, .bk 0,
    .cl 0 72, .cl 0 86, .cl 0 92, .p1 15, .cl 0 86, .p1 9, .cl 0 72, .cl 0 84, .cl 0 86, .cl 0 86,
    .p1 9, .cl 0 72, .cl 0 86, .cl 0 88, .p1 6, .cl 0 86, .p1 9, .cl 0 72, .cl 0 84, .cl 0 86,
    .cl 0 88, .cl 0 95, .cl 0 72, .cl 0 84, .p1 3, .bk 0, .cl 0 73, .cl 0 107, .p1 3, .cl 0 89,
    .p1 8, .cl 0 73, .cl 0 81, .cl 0 95, .cl 0 97, .p1 14, .cl 0 89, .p1 8, .cl 0 73, .cl 0 89,
    .cl 0 93, .p1 12, .cl 0 89, .p1 8, .cl 0 73, .cl 0 81, .cl 0 89, .cl 0 73, .cl 0 81, .p1 3,
    .bk 0, .cl 0 74, .cl 0 89, .cl 0 92, .p1 12, .cl 0 87, .p1 7, .cl 0 74, .cl 0 91, .cl 0 101,
    .cl 0 87, .p1 7, .cl 0 74, .cl 0 91, .p1 3, .cl 0 87, .p1 7, .cl 0 74, .cl 0 89, .cl 0 92,
    .cl 0 97, .p1 15, .cl 0 87, .p1 7, .p1 0, .bk 0, .cl 0 1, .p1 6, .cl 0 1, .cl 0 2, .cl 0 1,
    .p1 3, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1,
    .cl 0 2, .bk 0, .cl 0 1, .cl 0 2, .cl 0 1, .p1 11, .cl 0 1, .cl 0 4, .cl 0 1, .p1 11, .cl 0 1,
    .cl 0 2, .cl 0 1, .p1 11, .cl 0 1, .cl 0 2, .cl 0 1, .p1 11, .bk 0, .cl 0 1, .p1 3, .cl 0 1,
    .cl 0 3, .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3, .cl 0 1,
    .p1 11, .cl 0 1, .cl 0 3, .bk 0, .cl 0 2, .cl 0 3, .cl 0 2, .p1 6, .cl 0 2, .cl 0 3, .cl 0 2,
    .p1 6, .cl 0 2, .cl 0 3, .cl 0 2, .p1 6, .cl 0 2, .cl 0 4, .cl 0 2, .p1 6, .bk 0, .cl 0 5,
    .p1 3, .cl 0 10, .cl 0 5, .p1 3, .cl 0 5, .p1 3, .cl 0 5, .p1 3, .cl 0 5, .p1 3, .cl 0 5,
    .p1 3, .cl 0 5, .p1 3, .bk 0, .cl 0 62, .cl 0 64, .p1 3, .cl 0 68, .p1 13, .cl 0 62, .cl 0 66,
    .cl 0 67, .cl 0 62, .cl 0 64, .cl 0 68, .cl 0 62, .cl 0 66, .cl 0 67, .cl 0 68, .cl 0 68,
    .p1 13, .cl 0 62, .cl 0 64, .cl 0 65, .cl 0 72, .p1 9, .cl 0 62, .cl 0 66, .p1 12, .bk 0,
    .cl 0 64, .cl 0 87, .cl 0 89, .cl 0 66, .p1 15, .cl 0 64, .cl 0 66, .cl 0 74, .p1 5, .cl 0 66,
    .p1 15, .cl 0 64, .cl 0 66, .cl 0 68, .p1 11, .cl 0 66, .p1 15, .cl 0 64, .cl 0 74, .cl 0 79,
    .cl 0 80, .cl 0 66, .p1 15, .bk 0, .cl 0 61, .cl 0 92, .cl 0 69, .p1 12, .cl 0 61, .cl 0 71,
    .cl 0 76, .cl 0 80, .cl 0 69, .p1 12, .cl 0 61, .cl 0 92, .cl 0 69, .p1 12, .cl 0 61, .cl 0 69,
    .cl 0 71, .p1 5, .cl 0 69, .p1 12, .bk 0, .cl 0 63, .cl 0 67, .cl 0 69, .cl 0 71, .p1 3,
    .cl 0 67, .p1 14, .cl 0 63, .cl 0 67, .cl 0 83, .p1 1, .cl 0 67, .p1 14, .cl 0 63, .cl 0 67,
    .cl 0 86, .cl 0 88, .p1 11, .cl 0 67, .p1 14, .cl 0 63, .cl 0 69, .cl 0 81, .cl 0 67, .p1 14,
    .bk 0, .cl 0 10, .p1 3, .cl 0 10, .p1 3, .cl 0 10, .p1 3, .cl 0 10, .p1 3, .cl 0 10, .p1 3,
    .cl 0 10, .p1 3, .cl 0 10, .p1 3, .cl 0 20, .bk 0, .cl 0 58, .cl 0 72, .cl 0 84, .cl 0 88,
    .cl 0 58, .p1 9, .cl 0 58, .cl 0 71, .cl 0 72, .cl 0 58, .p1 9, .cl 0 58, .cl 0 72, .cl 0 84,
    .cl 0 88, .cl 0 90, .p1 3, .cl 0 58, .p1 9, .cl 0 58, .cl 0 59, .cl 0 72, .cl 0 58, .p1 9,
    .bk 0, .cl 0 74, .cl 0 91, .cl 0 56, .p1 7, .cl 0 74, .cl 0 89, .cl 0 90, .cl 0 56, .p1 7,
    .cl 0 56, .cl 0 74, .cl 0 89, .p1 2, .cl 0 56, .p1 7, .cl 0 74, .cl 0 91, .cl 0 56, .p1 7,
    .bk 0, .cl 0 71, .cl 0 72, .cl 0 76, .p1 1, .cl 0 59, .p1 10, .cl 0 71, .cl 0 72, .p1 3,
    .cl 0 59, .p1 10, .cl 0 71, .cl 0 94, .cl 0 59, .p1 10, .cl 0 71, .cl 0 86, .cl 0 90, .cl 0 59,
    .p1 10, .bk 0, .cl 0 57, .cl 0 73, .cl 0 81, .cl 0 87, .cl 0 90, .p1 3, .cl 0 57, .p1 8,
    .cl 0 73, .cl 0 81, .cl 0 57, .p1 8, .cl 0 73, .cl 0 81, .cl 0 86, .cl 0 57, .p1 8, .cl 0 57,
    .cl 0 73, .cl 0 74, .p1 12, .cl 0 57, .p1 8, .bk 0, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5,
    .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .bk 0, .cl 0 57, .cl 0 68, .p1 14, .cl 0 57, .cl 0 62,
    .p1 3, .cl 0 57, .cl 0 81, .cl 0 82, .cl 0 73, .p1 8, .cl 0 57, .cl 0 62, .cl 0 65, .cl 0 57,
    .cl 0 68, .cl 0 72, .p1 3, .cl 0 57, .cl 0 73, .cl 0 74, .p1 6, .cl 0 57, .cl 0 62, .cl 0 65,
    .bk 0, .cl 0 59, .cl 0 72, .cl 0 74, .cl 0 71, .p1 10, .cl 0 59, .cl 0 71, .cl 0 72, .cl 0 74,
    .p1 15, .cl 0 71, .p1 10, .cl 0 59, .cl 0 86, .p1 1, .cl 0 71, .p1 10, .cl 0 59, .cl 0 71,
    .cl 0 83, .cl 0 84, .p1 6, .cl 0 71, .p1 10, .bk 0, .cl 0 56, .cl 0 57, .cl 0 76, .p1 2,
    .cl 0 56, .cl 0 57, .cl 0 60, .cl 0 65, .p1 3, .cl 0 56, .cl 0 57, .p1 3, .cl 0 74, .p1 7,
    .cl 0 74, .cl 0 82, .cl 0 84, .p1 2, .cl 0 56, .cl 0 57, .cl 0 74, .cl 0 56, .cl 0 73,
    .cl 0 81, .cl 0 74, .p1 7, .bk 0, .cl 0 58, .cl 0 63, .cl 0 65, .cl 0 58, .cl 0 63, .p1 3,
    .cl 0 72, .cl 0 88, .p1 3, .cl 0 72, .p1 9, .cl 0 58, .cl 0 63, .cl 0 65, .cl 0 66, .p1 13,
    .cl 0 58, .cl 0 67, .cl 0 69, .p1 9, .cl 0 72, .cl 0 88, .p1 13, .cl 0 58, .cl 0 63, .cl 0 65,
    .bk 0, .cl 0 15, .cl 0 15, .cl 0 15, .cl 0 15, .cl 0 15, .cl 0 15, .cl 0 15, .cl 0 15, .bk 0,
    .cl 0 67, .cl 0 69, .p1 3, .cl 0 63, .p1 14, .cl 0 67, .cl 0 83, .cl 0 63, .p1 14, .cl 0 63,
    .cl 0 67, .cl 0 83, .p1 1, .cl 0 63, .p1 14, .cl 0 67, .cl 0 69, .cl 0 77, .p1 1, .cl 0 63,
    .p1 14, .bk 0, .cl 0 61, .cl 0 67, .cl 0 69, .cl 0 61, .p1 12, .cl 0 61, .cl 0 69, .cl 0 71,
    .cl 0 79, .cl 0 81, .p1 13, .cl 0 61, .p1 12, .cl 0 61, .cl 0 63, .cl 0 69, .cl 0 61, .p1 12,
    .cl 0 69, .cl 0 71, .p1 7, .cl 0 61, .p1 12, .bk 0, .cl 0 64, .cl 0 81, .p1 3, .cl 0 64,
    .p1 15, .cl 0 66, .cl 0 74, .p1 10, .cl 0 64, .p1 15, .cl 0 64, .cl 0 66, .cl 0 68, .p1 9,
    .cl 0 64, .p1 15, .cl 0 64, .cl 0 81, .cl 0 64, .p1 15, .bk 0, .cl 0 62, .cl 0 68, .cl 0 82,
    .p1 2, .cl 0 62, .p1 13, .cl 0 68, .cl 0 82, .p1 2, .cl 0 62, .p1 13, .cl 0 68, .cl 0 82,
    .cl 0 62, .p1 13, .cl 0 68, .cl 0 82, .cl 0 62, .p1 13, .p1 0, .bk 0, .cl 0 1, .p1 4, .cl 0 1,
    .cl 0 2, .cl 0 1, .p1 3, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1,
    .cl 0 2, .cl 0 1, .cl 0 2, .bk 0, .cl 0 1, .cl 0 2, .cl 0 1, .p1 5, .cl 0 1, .cl 0 4, .cl 0 1,
    .p1 5, .cl 0 1, .cl 0 2, .cl 0 1, .p1 5, .cl 0 1, .cl 0 2, .cl 0 1, .p1 5, .bk 0, .cl 0 1,
    .p1 3, .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3, .cl 0 1,
    .cl 0 3, .cl 0 1, .p1 5, .cl 0 1, .cl 0 3, .bk 0, .cl 0 2, .cl 0 3, .cl 0 2, .p1 4, .cl 0 2,
    .cl 0 3, .cl 0 2, .p1 4, .cl 0 2, .cl 0 3, .cl 0 2, .p1 4, .cl 0 2, .cl 0 4, .cl 0 2, .p1 4,
    .bk 0, .cl 0 5, .p1 3, .cl 0 10, .cl 0 5, .p1 3, .cl 0 5, .p1 3, .cl 0 5, .p1 3, .cl 0 5,
    .p1 3, .cl 0 5, .p1 3, .cl 0 5, .p1 3, .bk 0, .cl 0 37, .cl 0 39, .p1 3, .cl 0 43, .p1 8,
    .cl 0 37, .cl 0 41, .cl 0 42, .cl 0 37, .cl 0 39, .cl 0 43, .cl 0 37, .cl 0 41, .cl 0 42,
    .cl 0 43, .cl 0 43, .p1 8, .cl 0 37, .cl 0 39, .cl 0 40, .cl 0 47, .p1 10, .cl 0 37, .cl 0 41,
    .p1 14, .bk 0, .cl 0 39, .cl 0 41, .cl 0 57, .p1 8, .cl 0 41, .p1 13, .cl 0 39, .cl 0 41,
    .cl 0 49, .p1 6, .cl 0 41, .p1 13, .cl 0 39, .cl 0 41, .cl 0 43, .p1 5, .cl 0 41, .p1 13,
    .cl 0 39, .cl 0 49, .cl 0 51, .cl 0 55, .p1 8, .cl 0 41, .p1 13, .bk 0, .cl 0 36, .cl 0 44,
    .cl 0 58, .p1 13, .cl 0 44, .p1 14, .cl 0 36, .cl 0 46, .cl 0 54, .cl 0 55, .p1 9, .cl 0 44,
    .p1 14, .cl 0 36, .cl 0 44, .cl 0 58, .p1 9, .cl 0 44, .p1 14, .cl 0 36, .cl 0 44, .cl 0 46,
    .p1 6, .cl 0 44, .p1 14, .bk 0, .cl 0 38, .cl 0 42, .cl 0 44, .cl 0 46, .p1 3, .cl 0 42, .p1 9,
    .cl 0 38, .cl 0 42, .cl 0 59, .p1 8, .cl 0 42, .p1 9, .cl 0 38, .cl 0 42, .cl 0 59, .p1 5,
    .cl 0 42, .p1 9, .cl 0 38, .cl 0 44, .cl 0 53, .p1 7, .cl 0 42, .p1 9, .bk 0, .cl 0 10, .p1 3,
    .cl 0 10, .p1 3, .cl 0 10, .p1 3, .cl 0 10, .p1 3, .cl 0 10, .p1 3, .cl 0 10, .p1 3, .cl 0 10,
    .p1 3, .cl 0 20, .bk 0, .cl 0 47, .cl 0 58, .cl 0 33, .p1 10, .cl 0 33, .cl 0 46, .cl 0 47,
    .cl 0 33, .p1 10, .cl 0 47, .cl 0 59, .p1 3, .cl 0 33, .p1 10, .cl 0 33, .cl 0 34, .cl 0 47,
    .cl 0 33, .p1 10, .bk 0, .cl 0 49, .cl 0 56, .cl 0 31, .p1 15, .cl 0 49, .cl 0 56, .cl 0 57,
    .cl 0 58, .cl 0 59, .cl 0 31, .p1 15, .cl 0 49, .cl 0 56, .cl 0 31, .p1 15, .cl 0 49, .cl 0 56,
    .cl 0 57, .p1 14, .cl 0 31, .p1 15, .bk 0, .cl 0 46, .cl 0 59, .cl 0 34, .p1 12, .cl 0 46,
    .cl 0 47, .p1 3, .cl 0 34, .p1 12, .cl 0 46, .cl 0 59, .cl 0 34, .p1 12, .cl 0 46, .cl 0 59,
    .cl 0 61, .cl 0 62, .p1 5, .cl 0 34, .p1 12, .bk 0, .cl 0 48, .cl 0 56, .p1 3, .cl 0 32, .p1 7,
    .cl 0 48, .cl 0 56, .p1 5, .cl 0 32, .p1 7, .cl 0 48, .cl 0 57, .cl 0 32, .p1 7, .cl 0 32,
    .cl 0 48, .cl 0 49, .p1 14, .cl 0 32, .p1 7, .bk 0, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5,
    .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .bk 0, .cl 0 32, .cl 0 43, .p1 9, .cl 0 32, .cl 0 37,
    .p1 3, .cl 0 32, .cl 0 48, .cl 0 57, .cl 0 48, .p1 7, .cl 0 32, .cl 0 37, .cl 0 40, .cl 0 32,
    .cl 0 43, .cl 0 47, .p1 3, .cl 0 32, .cl 0 48, .cl 0 49, .p1 4, .cl 0 32, .cl 0 37, .cl 0 40,
    .bk 0, .cl 0 34, .cl 0 47, .cl 0 49, .cl 0 46, .p1 12, .cl 0 34, .cl 0 46, .cl 0 47, .cl 0 49,
    .p1 13, .cl 0 46, .p1 12, .cl 0 34, .cl 0 46, .cl 0 59, .cl 0 46, .p1 12, .cl 0 34, .cl 0 46,
    .cl 0 59, .p1 1, .cl 0 46, .p1 12, .bk 0, .cl 0 31, .cl 0 32, .cl 0 55, .cl 0 31, .cl 0 32,
    .cl 0 35, .cl 0 40, .p1 3, .cl 0 31, .cl 0 32, .p1 3, .cl 0 49, .p1 15, .cl 0 31, .cl 0 48,
    .cl 0 51, .p1 14, .cl 0 31, .cl 0 32, .cl 0 49, .cl 0 31, .cl 0 49, .cl 0 56, .p1 2, .cl 0 49,
    .p1 15, .bk 0, .cl 0 33, .cl 0 38, .cl 0 40, .cl 0 33, .cl 0 38, .p1 3, .cl 0 33, .cl 0 47,
    .cl 0 58, .p1 1, .cl 0 47, .p1 10, .cl 0 33, .cl 0 38, .cl 0 40, .cl 0 41, .p1 8, .cl 0 33,
    .cl 0 42, .cl 0 44, .p1 10, .cl 0 33, .cl 0 47, .cl 0 58, .cl 0 33, .cl 0 38, .cl 0 40, .bk 0,
    .cl 0 15, .cl 0 15, .cl 0 15, .cl 0 15, .cl 0 15, .cl 0 15, .cl 0 15, .cl 0 15, .bk 0,
    .cl 0 42, .cl 0 44, .p1 3, .cl 0 38, .p1 9, .cl 0 42, .cl 0 63, .cl 0 38, .p1 9, .cl 0 42,
    .cl 0 58, .cl 0 63, .cl 0 38, .p1 9, .cl 0 42, .cl 0 63, .cl 0 38, .p1 9, .bk 0, .cl 0 36,
    .cl 0 42, .cl 0 44, .cl 0 36, .p1 14, .cl 0 36, .cl 0 44, .cl 0 46, .cl 0 55, .p1 6, .cl 0 36,
    .p1 14, .cl 0 36, .cl 0 38, .cl 0 44, .cl 0 36, .p1 14, .cl 0 44, .cl 0 46, .p1 15, .cl 0 36,
    .p1 14, .bk 0, .cl 0 41, .cl 0 62, .p1 4, .cl 0 39, .p1 13, .cl 0 41, .cl 0 49, .p1 12,
    .cl 0 39, .p1 13, .cl 0 39, .cl 0 41, .cl 0 43, .p1 10, .cl 0 39, .p1 13, .cl 0 39, .cl 0 41,
    .cl 0 49, .cl 0 55, .p1 6, .cl 0 39, .p1 13, .bk 0, .cl 0 43, .cl 0 57, .cl 0 62, .cl 0 37,
    .p1 8, .cl 0 43, .cl 0 62, .cl 0 37, .p1 8, .cl 0 37, .cl 0 56, .p1 3, .cl 0 37, .p1 8,
    .cl 0 43, .cl 0 62, .cl 0 37, .p1 8]

private theorem cdOK233 : CdOK ⟨2, 0, 3, 3⟩ tab23 cd233 where
  size := by decide +kernel
  rep := by decide +kernel
  orb := by decide +kernel
  gp := by decide +kernel
  nu := by decide +kernel
  al := by decide +kernel
  be := by decide +kernel
  m := by decide +kernel

private theorem run233 : run cd233 3403 [(z16, z16)] cert233 = true := by
  decide +kernel

private theorem case233 :
    (tablesOKb ⟨2, 0, 3, 3⟩ (orbitData ⟨2, 0, 3, 3⟩) && g8b ⟨2, 0, 3, 3⟩ &&
      search ⟨2, 0, 3, 3⟩ (orbitData ⟨2, 0, 3, 3⟩) 17
        (Array.replicate (orbitData ⟨2, 0, 3, 3⟩).reps.size none)) = true := by
  rw [orbitData23]
  exact search_case tablesOKb23 g8b23 cdOK233 run233

private def cd237 : Cd := ⟨2, 0, 3, 7, orb23, rep23, gp23⟩

private def cert237 : List Op := [
    .bv 0, .bk 0, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .bv 1, .p1 1, .p1 1, .p1 1, .p1 1, .p1 1,
    .cl 0 5, .cl 0 5, .cl 0 5, .bk 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1,
    .cl 1 1, .cl 1 1, .p1 1, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .p1 1, .cl 0 5, .cl 0 5, .cl 0 5,
    .cl 0 5, .p1 1, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .p1 1, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5,
    .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5,
    .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5,
    .p1 1, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5,
    .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5,
    .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .p1 1, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5,
    .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5,
    .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5,
    .p1 1, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5,
    .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5,
    .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 1, .cl 0 1, .cl 0 1, .bk 0, .cl 0 1,
    .cl 0 1, .bv 1, .p1 1, .p1 1, .p1 1, .p1 1, .p1 1, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .p1 1,
    .cl 0 5, .cl 0 5, .bk 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1,
    .cl 1 1, .cl 0 5, .p1 1, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .p1 1, .cl 0 5, .cl 0 5, .cl 0 5,
    .cl 0 5, .p1 1, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5,
    .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5,
    .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .p1 1, .cl 0 5, .cl 0 5, .cl 0 5,
    .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5,
    .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5,
    .cl 0 5, .p1 1, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5,
    .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5,
    .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .p1 1, .cl 0 5, .cl 0 5, .cl 0 5,
    .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5,
    .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5,
    .cl 0 5, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .bk 0, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .bv 1, .p1 1, .p1 1, .p1 1, .p1 1, .p1 1, .cl 0 6, .p1 2, .cl 0 7,
    .cl 0 5, .cl 0 5, .p1 1, .cl 0 5, .cl 0 7, .p1 2, .cl 0 5, .cl 0 6, .p1 2, .p1 1, .cl 0 7,
    .p1 2, .bk 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 0 7,
    .cl 0 5, .p1 1, .cl 0 5, .cl 0 5, .cl 0 7, .cl 0 6, .p1 2, .p1 1, .cl 0 7, .p1 7, .cl 0 7,
    .p1 8, .cl 0 7, .p1 9, .cl 0 7, .p1 10, .cl 0 7, .p1 11, .cl 0 7, .p1 12, .cl 0 7, .p1 13,
    .cl 0 7, .p1 14, .cl 0 7, .p1 15, .cl 0 7, .cl 0 7, .p1 15, .cl 0 7, .p1 14, .cl 0 7, .p1 13,
    .cl 0 7, .p1 12, .cl 0 7, .p1 6, .cl 0 7, .p1 10, .cl 0 7, .p1 9, .cl 0 7, .p1 8, .cl 0 7,
    .p1 7, .cl 0 7, .p1 3, .cl 0 7, .p1 4, .cl 0 7, .p1 5, .cl 0 7, .p1 5, .cl 0 7, .p1 4, .p1 1,
    .cl 0 7, .p1 8, .cl 0 7, .p1 13, .cl 0 7, .p1 14, .cl 0 7, .p1 9, .cl 0 7, .p1 4, .cl 0 7,
    .p1 10, .cl 0 7, .p1 15, .cl 0 7, .p1 12, .cl 0 7, .p1 7, .cl 0 7, .cl 0 7, .p1 7, .cl 0 7,
    .p1 12, .cl 0 7, .p1 15, .cl 0 7, .p1 10, .cl 0 7, .p1 5, .cl 0 7, .p1 9, .cl 0 7, .p1 14,
    .cl 0 7, .p1 13, .cl 0 7, .p1 8, .cl 0 7, .p1 3, .cl 0 7, .p1 6, .cl 0 7, .p1 11, .cl 0 7,
    .p1 11, .cl 0 7, .p1 6, .p1 1, .cl 0 7, .p1 15, .cl 0 7, .p1 7, .cl 0 7, .p1 10, .cl 0 7,
    .p1 12, .cl 0 7, .p1 5, .cl 0 7, .p1 14, .cl 0 7, .p1 8, .cl 0 7, .p1 9, .cl 0 7, .p1 13,
    .cl 0 7, .cl 0 7, .p1 13, .cl 0 7, .p1 9, .cl 0 7, .p1 8, .cl 0 7, .p1 14, .cl 0 7, .p1 4,
    .cl 0 7, .p1 12, .cl 0 7, .p1 10, .cl 0 7, .p1 7, .cl 0 7, .p1 15, .cl 0 7, .p1 3, .cl 0 7,
    .p1 11, .cl 0 7, .p1 6, .cl 0 7, .p1 6, .cl 0 7, .p1 11, .p1 1, .cl 0 7, .p1 13, .cl 0 7,
    .p1 15, .cl 0 7, .p1 12, .cl 0 7, .p1 14, .cl 0 7, .p1 6, .cl 0 7, .p1 9, .cl 0 7, .p1 7,
    .cl 0 7, .p1 10, .cl 0 7, .p1 8, .cl 0 7, .cl 0 7, .p1 8, .cl 0 7, .p1 10, .cl 0 7, .p1 7,
    .cl 0 7, .p1 9, .cl 0 7, .p1 11, .cl 0 7, .p1 14, .cl 0 7, .p1 12, .cl 0 7, .p1 15, .cl 0 7,
    .p1 13, .cl 0 7, .p1 3, .cl 0 7, .p1 5, .cl 0 7, .p1 4, .cl 0 7, .p1 4, .cl 0 7, .p1 5,
    .cl 0 1, .bk 0, .bv 1, .p1 1, .p1 1, .p1 1, .p1 1, .p1 1, .cl 0 6, .cl 0 6, .p1 2, .cl 0 5,
    .cl 0 5, .p1 1, .cl 0 5, .cl 0 6, .p1 2, .cl 0 5, .cl 0 6, .p1 1, .cl 0 6, .p1 2, .cl 0 5,
    .cl 0 6, .p1 2, .cl 0 5, .p1 1, .bk 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1,
    .cl 1 1, .cl 1 1, .cl 0 5, .cl 0 6, .cl 0 6, .p1 1, .cl 0 6, .p1 5, .cl 0 6, .cl 0 6, .p1 4,
    .cl 0 6, .p1 3, .cl 0 6, .p1 7, .cl 0 6, .p1 8, .cl 0 6, .p1 9, .cl 0 6, .p1 10, .cl 0 6,
    .p1 6, .cl 0 6, .p1 12, .cl 0 6, .p1 13, .cl 0 6, .p1 14, .cl 0 6, .p1 15, .cl 0 6, .p1 11,
    .cl 0 6, .p1 15, .cl 0 6, .p1 14, .cl 0 6, .p1 13, .cl 0 6, .p1 12, .cl 0 6, .p1 11, .cl 0 6,
    .p1 10, .cl 0 6, .p1 9, .cl 0 6, .p1 8, .cl 0 6, .p1 7, .cl 0 6, .p1 6, .p1 1, .cl 0 6, .p1 11,
    .cl 0 6, .cl 0 6, .p1 6, .cl 0 6, .p1 3, .cl 0 6, .p1 8, .cl 0 6, .p1 13, .cl 0 6, .p1 14,
    .cl 0 6, .p1 9, .cl 0 6, .p1 5, .cl 0 6, .p1 10, .cl 0 6, .p1 15, .cl 0 6, .p1 12, .cl 0 6,
    .p1 7, .cl 0 6, .p1 4, .cl 0 6, .p1 7, .cl 0 6, .p1 12, .cl 0 6, .p1 15, .cl 0 6, .p1 10,
    .cl 0 6, .p1 4, .cl 0 6, .p1 9, .cl 0 6, .p1 14, .cl 0 6, .p1 13, .cl 0 6, .p1 8, .cl 0 6,
    .p1 5, .p1 1, .cl 0 6, .p1 6, .cl 0 6, .cl 0 6, .p1 11, .cl 0 6, .p1 3, .cl 0 6, .p1 15,
    .cl 0 6, .p1 7, .cl 0 6, .p1 10, .cl 0 6, .p1 12, .cl 0 6, .p1 4, .cl 0 6, .p1 14, .cl 0 6,
    .p1 8, .cl 0 6, .p1 9, .cl 0 6, .p1 13, .cl 0 6, .p1 5, .cl 0 6, .p1 13, .cl 0 6, .p1 9,
    .cl 0 6, .p1 8, .cl 0 6, .p1 14, .cl 0 6, .p1 5, .cl 0 6, .p1 12, .cl 0 6, .p1 10, .cl 0 6,
    .p1 7, .cl 0 6, .p1 15, .cl 0 6, .p1 4, .p1 1, .cl 0 6, .p1 4, .cl 0 6, .cl 0 6, .p1 5,
    .cl 0 6, .p1 3, .cl 0 6, .p1 13, .cl 0 6, .p1 15, .cl 0 6, .p1 12, .cl 0 6, .p1 14, .cl 0 6,
    .p1 11, .cl 0 6, .p1 9, .cl 0 6, .p1 7, .cl 0 6, .p1 10, .cl 0 6, .p1 8, .cl 0 6, .p1 6,
    .cl 0 6, .p1 8, .cl 0 6, .p1 10, .cl 0 6, .p1 7, .cl 0 6, .p1 9, .cl 0 6, .p1 6, .cl 0 6,
    .p1 14, .cl 0 6, .p1 12, .cl 0 6, .p1 15, .cl 0 6, .p1 13, .cl 0 6, .p1 11, .cl 0 2, .cl 0 2,
    .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .bk 0, .cl 0 5, .cl 0 5, .cl 0 5, .bv 1, .p1 1,
    .p1 1, .p1 1, .p1 1, .p1 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .p1 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .p1 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .p1 1, .cl 0 1, .bk 1, .cl 1 1,
    .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 0 1, .cl 0 1, .p1 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .p1 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .p1 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .p1 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 5,
    .cl 0 5, .cl 0 5, .cl 0 5, .bk 0, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .bk 0, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3,
    .cl 0 3, .bk 0, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .bk 0,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .bk 0, .cl 0 5, .bv 1,
    .p1 1, .p1 1, .p1 1, .p1 1, .p1 1, .cl 0 2, .cl 0 2, .cl 0 1, .cl 0 1, .p1 1, .cl 0 1, .cl 0 2,
    .cl 0 1, .cl 0 2, .p1 1, .cl 0 2, .cl 0 1, .cl 0 2, .bk 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1,
    .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .p1 1, .cl 0 1, .cl 0 1, .cl 0 2, .cl 0 2, .p1 1, .cl 0 2,
    .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2,
    .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2,
    .cl 0 2, .cl 0 2, .cl 0 2, .p1 1, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2,
    .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2,
    .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .p1 1, .cl 0 2,
    .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2,
    .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2,
    .cl 0 2, .cl 0 2, .cl 0 2, .p1 1, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2,
    .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2,
    .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 5, .cl 0 5,
    .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .bk 0, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2,
    .cl 0 2, .cl 0 2, .cl 0 2, .bk 0, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2,
    .cl 0 2, .cl 0 2, .bk 0, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2,
    .cl 0 2, .bk 0, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .bk 0,
    .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .bv 1, .p1 1, .p1 1, .p1 1, .p1 1, .p1 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .p1 1, .bk 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1,
    .cl 1 1, .cl 1 1, .cl 0 1, .cl 0 1, .cl 0 1, .p1 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .p1 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .p1 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .p1 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .p1 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .p1 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 5, .cl 0 5, .bk 0, .cl 0 2, .cl 0 2, .cl 0 2,
    .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .bk 0, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2,
    .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .bk 0, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2,
    .cl 0 2, .cl 0 2, .cl 0 2, .bk 0, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .bk 0, .cl 0 10, .cl 0 10, .cl 0 10, .cl 0 10, .cl 0 10, .cl 0 10, .cl 0 10,
    .bv 1, .p1 1, .p1 1, .p1 1, .p1 1, .p1 1, .cl 0 3, .cl 0 3, .bk 1, .cl 1 1, .cl 1 1, .cl 1 1,
    .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 0 1, .p1 1, .cl 0 1, .cl 0 3, .cl 0 1,
    .cl 0 3, .p1 1, .cl 0 3, .cl 0 1, .cl 0 3, .cl 0 1, .p1 1, .cl 0 1, .cl 0 1, .cl 0 3, .cl 0 3,
    .p1 1, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3,
    .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3,
    .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .p1 1, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3,
    .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3,
    .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3,
    .p1 1, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3,
    .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3,
    .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .p1 1, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3,
    .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3,
    .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3,
    .bk 0, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .bk 0, .cl 0 3,
    .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .bk 0, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .bk 0, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .p1 0, .bk 0, .cl 0 1, .p1 5, .cl 0 1, .cl 0 2,
    .cl 0 1, .p1 3, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2,
    .cl 0 1, .cl 0 2, .bk 0, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 4, .cl 0 1,
    .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .bk 0,
    .cl 0 1, .p1 3, .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3,
    .cl 0 1, .cl 0 3, .cl 0 1, .p1 4, .cl 0 1, .cl 0 3, .bk 0, .cl 0 2, .cl 0 3, .cl 0 2, .cl 0 3,
    .cl 0 2, .cl 0 3, .cl 0 2, .cl 0 3, .cl 0 2, .cl 0 3, .cl 0 2, .cl 0 3, .cl 0 2, .cl 0 4,
    .cl 0 2, .cl 0 3, .bk 0, .cl 0 5, .cl 0 10, .cl 0 5, .p1 3, .cl 0 5, .cl 0 10, .cl 0 5,
    .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5, .p1 11, .bk 0,
    .cl 0 31, .cl 0 32, .cl 0 36, .cl 0 31, .cl 0 32, .cl 0 33, .cl 0 31, .cl 0 32, .p1 2,
    .cl 0 31, .cl 0 48, .cl 0 56, .cl 0 61, .cl 0 31, .cl 0 48, .cl 0 31, .cl 0 32, .p1 2,
    .cl 0 31, .cl 0 48, .cl 0 31, .cl 0 48, .cl 0 55, .p1 12, .bk 0, .cl 0 32, .cl 0 37, .cl 0 38,
    .cl 0 32, .cl 0 37, .p1 2, .cl 0 32, .cl 0 43, .cl 0 47, .cl 0 32, .cl 0 43, .cl 0 32,
    .cl 0 37, .p1 2, .cl 0 32, .cl 0 43, .cl 0 32, .cl 0 43, .cl 0 52, .p1 10, .cl 0 32, .cl 0 37,
    .cl 0 43, .bk 0, .cl 0 33, .cl 0 38, .p1 1, .cl 0 33, .cl 0 38, .p1 1, .cl 0 33, .cl 0 42,
    .cl 0 52, .p1 3, .cl 0 33, .cl 0 42, .cl 0 33, .cl 0 42, .cl 0 33, .cl 0 42, .cl 0 33,
    .cl 0 42, .cl 0 48, .cl 0 33, .cl 0 38, .cl 0 42, .bk 0, .cl 0 34, .cl 0 47, .cl 0 34,
    .cl 0 47, .cl 0 34, .cl 0 47, .cl 0 34, .cl 0 47, .cl 0 49, .cl 0 34, .cl 0 47, .p1 1,
    .cl 0 34, .cl 0 47, .cl 0 34, .cl 0 47, .p1 1, .cl 0 34, .cl 0 47, .cl 0 55, .p1 15, .bk 0,
    .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 20, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10,
    .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10, .bk 0, .cl 0 36, .cl 0 61, .cl 0 63,
    .cl 0 66, .cl 0 67, .p1 1, .cl 0 36, .cl 0 63, .p1 3, .cl 0 36, .cl 0 46, .cl 0 49, .cl 0 36,
    .cl 0 63, .p1 7, .cl 0 36, .cl 0 63, .cl 0 64, .p1 8, .cl 0 36, .cl 0 46, .cl 0 57, .cl 0 36,
    .cl 0 46, .p1 1, .cl 0 36, .cl 0 46, .p1 1, .bk 0, .cl 0 37, .cl 0 39, .p1 2, .cl 0 37,
    .cl 0 41, .cl 0 42, .cl 0 37, .cl 0 41, .cl 0 37, .cl 0 39, .p1 2, .cl 0 37, .cl 0 41,
    .cl 0 37, .cl 0 41, .cl 0 60, .p1 9, .cl 0 37, .cl 0 39, .cl 0 41, .cl 0 37, .cl 0 41, .bk 0,
    .cl 0 38, .cl 0 44, .cl 0 38, .cl 0 44, .cl 0 57, .p1 11, .cl 0 38, .cl 0 44, .p1 1, .cl 0 38,
    .cl 0 44, .cl 0 38, .cl 0 44, .p1 1, .cl 0 38, .cl 0 44, .cl 0 60, .p1 8, .cl 0 38, .cl 0 44,
    .cl 0 38, .cl 0 44, .bk 0, .cl 0 39, .cl 0 66, .p1 3, .cl 0 39, .cl 0 62, .p1 3, .cl 0 39,
    .cl 0 49, .p1 2, .cl 0 39, .cl 0 62, .p1 10, .cl 0 39, .cl 0 62, .cl 0 63, .p1 9, .cl 0 39,
    .cl 0 49, .cl 0 58, .cl 0 39, .cl 0 64, .p1 8, .cl 0 39, .cl 0 49, .p1 2, .bk 0, .cl 0 5,
    .cl 0 15, .cl 0 5, .cl 0 15, .cl 0 5, .cl 0 15, .cl 0 5, .cl 0 15, .cl 0 5, .cl 0 15, .cl 0 5,
    .p1 6, .cl 0 5, .cl 0 15, .cl 0 5, .p1 3, .bk 0, .cl 0 41, .cl 0 49, .cl 0 51, .p1 14,
    .cl 0 41, .cl 0 49, .p1 2, .cl 0 41, .cl 0 49, .cl 0 41, .cl 0 49, .p1 2, .cl 0 41, .cl 0 49,
    .cl 0 62, .p1 5, .cl 0 41, .cl 0 49, .cl 0 41, .cl 0 49, .cl 0 41, .cl 0 49, .bk 0, .cl 0 42,
    .cl 0 44, .p1 1, .cl 0 42, .cl 0 67, .cl 0 72, .cl 0 74, .p1 7, .cl 0 42, .cl 0 63, .p1 3,
    .cl 0 42, .cl 0 44, .cl 0 63, .p1 3, .cl 0 42, .cl 0 72, .p1 15, .cl 0 42, .cl 0 63, .p1 3,
    .cl 0 42, .cl 0 44, .cl 0 48, .cl 0 42, .cl 0 44, .p1 1, .bk 0, .cl 0 43, .cl 0 73, .p1 12,
    .cl 0 43, .cl 0 68, .cl 0 71, .cl 0 73, .cl 0 43, .cl 0 62, .p1 3, .cl 0 43, .cl 0 68, .p1 7,
    .cl 0 43, .cl 0 73, .cl 0 74, .cl 0 43, .cl 0 62, .p1 3, .cl 0 43, .cl 0 62, .p1 3, .cl 0 43,
    .cl 0 62, .p1 2, .bk 0, .cl 0 44, .cl 0 61, .p1 3, .cl 0 44, .cl 0 46, .p1 1, .cl 0 44,
    .cl 0 46, .cl 0 44, .cl 0 46, .p1 1, .cl 0 44, .cl 0 46, .cl 0 51, .p1 3, .cl 0 44, .cl 0 46,
    .cl 0 44, .cl 0 46, .cl 0 44, .cl 0 46, .bk 0, .cl 0 10, .cl 0 15, .cl 0 10, .cl 0 15,
    .cl 0 10, .cl 0 15, .cl 0 10, .cl 0 15, .cl 0 10, .cl 0 15, .cl 0 10, .cl 0 20, .cl 0 10,
    .cl 0 15, .cl 0 10, .cl 0 15, .bk 0, .cl 0 46, .cl 0 59, .p1 3, .cl 0 46, .cl 0 47, .p1 1,
    .cl 0 46, .cl 0 47, .p1 1, .cl 0 46, .cl 0 61, .cl 0 66, .p1 13, .cl 0 46, .cl 0 59, .p1 3,
    .cl 0 46, .cl 0 47, .cl 0 48, .cl 0 46, .cl 0 61, .p1 8, .cl 0 46, .cl 0 59, .p1 3, .bk 0,
    .cl 0 47, .cl 0 72, .p1 12, .cl 0 47, .cl 0 71, .p1 13, .cl 0 47, .cl 0 58, .p1 3, .cl 0 47,
    .cl 0 58, .p1 3, .cl 0 47, .cl 0 58, .p1 1, .cl 0 47, .cl 0 71, .cl 0 83, .p1 3, .cl 0 47,
    .cl 0 71, .cl 0 73, .cl 0 74, .cl 0 47, .cl 0 58, .p1 3, .bk 0, .cl 0 48, .cl 0 57, .p1 2,
    .cl 0 48, .cl 0 74, .p1 14, .cl 0 48, .cl 0 73, .cl 0 74, .cl 0 81, .cl 0 83, .cl 0 48,
    .cl 0 57, .p1 3, .cl 0 48, .cl 0 73, .p1 15, .cl 0 48, .cl 0 74, .cl 0 82, .p1 3, .cl 0 48,
    .cl 0 57, .p1 3, .cl 0 48, .cl 0 57, .p1 3, .bk 0, .cl 0 49, .cl 0 56, .p1 3, .cl 0 49,
    .cl 0 56, .p1 2, .cl 0 49, .cl 0 64, .p1 9, .cl 0 49, .cl 0 64, .cl 0 69, .p1 14, .cl 0 49,
    .cl 0 56, .p1 3, .cl 0 49, .cl 0 74, .p1 13, .cl 0 49, .cl 0 64, .cl 0 81, .p1 3, .cl 0 49,
    .cl 0 56, .p1 3, .p1 0, .bk 0, .cl 0 1, .p1 11, .cl 0 1, .cl 0 2, .cl 0 1, .p1 3, .cl 0 1,
    .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .bk 0,
    .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 4, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2,
    .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .bk 0, .cl 0 1, .p1 3, .cl 0 1, .cl 0 3,
    .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3, .cl 0 1, .p1 6,
    .cl 0 1, .cl 0 3, .bk 0, .cl 0 2, .cl 0 3, .cl 0 2, .cl 0 3, .cl 0 2, .cl 0 3, .cl 0 2,
    .cl 0 3, .cl 0 2, .cl 0 3, .cl 0 2, .cl 0 3, .cl 0 2, .cl 0 4, .cl 0 2, .cl 0 3, .bk 0,
    .cl 0 5, .cl 0 10, .cl 0 5, .p1 3, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10,
    .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5, .p1 4, .bk 0, .cl 0 56, .cl 0 57, .cl 0 61,
    .cl 0 56, .cl 0 57, .cl 0 58, .cl 0 56, .cl 0 57, .p1 2, .cl 0 56, .cl 0 73, .cl 0 91,
    .cl 0 56, .cl 0 73, .cl 0 56, .cl 0 57, .p1 2, .cl 0 56, .cl 0 73, .cl 0 56, .cl 0 73,
    .cl 0 89, .bk 0, .cl 0 57, .cl 0 62, .cl 0 63, .cl 0 57, .cl 0 62, .p1 2, .cl 0 57, .cl 0 68,
    .cl 0 72, .cl 0 57, .cl 0 68, .cl 0 57, .cl 0 62, .p1 2, .cl 0 57, .cl 0 68, .cl 0 57,
    .cl 0 81, .cl 0 84, .cl 0 57, .cl 0 62, .cl 0 68, .bk 0, .cl 0 58, .cl 0 63, .p1 1, .cl 0 58,
    .cl 0 63, .p1 1, .cl 0 58, .cl 0 84, .cl 0 89, .cl 0 58, .cl 0 67, .cl 0 58, .cl 0 67,
    .cl 0 58, .cl 0 67, .cl 0 58, .cl 0 67, .cl 0 73, .cl 0 58, .cl 0 63, .cl 0 67, .bk 0,
    .cl 0 59, .cl 0 72, .cl 0 59, .cl 0 72, .cl 0 59, .cl 0 72, .cl 0 59, .cl 0 72, .cl 0 74,
    .cl 0 59, .cl 0 72, .p1 1, .cl 0 59, .cl 0 72, .cl 0 59, .cl 0 72, .p1 1, .cl 0 59, .cl 0 72,
    .cl 0 76, .cl 0 77, .cl 0 85, .p1 12, .bk 0, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 20, .cl 0 5,
    .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5,
    .cl 0 10, .bk 0, .cl 0 61, .cl 0 92, .p1 5, .cl 0 61, .cl 0 83, .cl 0 92, .cl 0 101, .p1 15,
    .cl 0 61, .cl 0 71, .cl 0 74, .cl 0 61, .cl 0 83, .cl 0 88, .cl 0 96, .p1 8, .cl 0 61,
    .cl 0 83, .cl 0 88, .p1 7, .cl 0 61, .cl 0 71, .cl 0 81, .cl 0 86, .p1 8, .cl 0 61, .cl 0 71,
    .p1 1, .cl 0 61, .cl 0 71, .p1 1, .bk 0, .cl 0 62, .cl 0 64, .p1 2, .cl 0 62, .cl 0 66,
    .cl 0 67, .cl 0 62, .cl 0 66, .cl 0 62, .cl 0 64, .p1 2, .cl 0 62, .cl 0 66, .cl 0 62,
    .cl 0 66, .cl 0 78, .cl 0 82, .cl 0 83, .cl 0 62, .cl 0 64, .cl 0 66, .cl 0 62, .cl 0 66,
    .bk 0, .cl 0 63, .cl 0 69, .cl 0 63, .cl 0 69, .cl 0 83, .cl 0 63, .cl 0 69, .p1 1, .cl 0 63,
    .cl 0 69, .cl 0 63, .cl 0 69, .p1 1, .cl 0 63, .cl 0 69, .cl 0 77, .cl 0 79, .cl 0 80, .p1 14,
    .cl 0 63, .cl 0 69, .cl 0 63, .cl 0 69, .bk 0, .cl 0 64, .cl 0 82, .cl 0 87, .p1 10, .cl 0 64,
    .cl 0 82, .cl 0 93, .cl 0 104, .p1 12, .cl 0 64, .cl 0 74, .p1 2, .cl 0 64, .cl 0 82, .cl 0 87,
    .cl 0 99, .p1 9, .cl 0 64, .cl 0 87, .cl 0 88, .cl 0 64, .cl 0 87, .p1 3, .cl 0 64, .cl 0 74,
    .cl 0 87, .p1 10, .cl 0 64, .cl 0 74, .p1 2, .bk 0, .cl 0 5, .cl 0 15, .cl 0 5, .cl 0 15,
    .cl 0 5, .cl 0 15, .cl 0 5, .cl 0 15, .cl 0 5, .cl 0 15, .cl 0 5, .p1 5, .cl 0 5, .cl 0 15,
    .cl 0 5, .p1 3, .bk 0, .cl 0 66, .cl 0 74, .cl 0 87, .cl 0 66, .cl 0 74, .p1 2, .cl 0 66,
    .cl 0 74, .cl 0 66, .cl 0 74, .p1 2, .cl 0 66, .cl 0 87, .cl 0 90, .cl 0 66, .cl 0 74,
    .cl 0 66, .cl 0 74, .cl 0 66, .cl 0 74, .bk 0, .cl 0 67, .cl 0 69, .p1 1, .cl 0 67, .cl 0 83,
    .p1 6, .cl 0 67, .cl 0 83, .cl 0 92, .cl 0 67, .cl 0 69, .cl 0 82, .cl 0 67, .cl 0 96,
    .cl 0 97, .cl 0 99, .cl 0 105, .p1 7, .cl 0 67, .cl 0 96, .cl 0 97, .p1 15, .cl 0 67, .cl 0 69,
    .cl 0 73, .cl 0 67, .cl 0 69, .p1 1, .bk 0, .cl 0 68, .cl 0 99, .cl 0 106, .p1 8, .cl 0 68,
    .cl 0 82, .p1 6, .cl 0 68, .cl 0 98, .p1 3, .cl 0 68, .cl 0 118, .p1 8, .cl 0 68, .cl 0 82,
    .cl 0 94, .cl 0 99, .cl 0 106, .p1 11, .cl 0 68, .cl 0 82, .cl 0 83, .p1 11, .cl 0 68,
    .cl 0 82, .cl 0 93, .cl 0 68, .cl 0 112, .p1 2, .bk 0, .cl 0 69, .cl 0 88, .cl 0 90, .cl 0 69,
    .cl 0 71, .p1 1, .cl 0 69, .cl 0 71, .cl 0 69, .cl 0 71, .p1 1, .cl 0 69, .cl 0 71, .cl 0 88,
    .cl 0 69, .cl 0 71, .cl 0 69, .cl 0 71, .cl 0 69, .cl 0 71, .bk 0, .cl 0 10, .cl 0 15,
    .cl 0 10, .cl 0 15, .cl 0 10, .cl 0 15, .cl 0 10, .cl 0 15, .cl 0 10, .cl 0 15, .cl 0 10,
    .cl 0 20, .cl 0 10, .cl 0 15, .cl 0 10, .cl 0 15, .bk 0, .cl 0 71, .cl 0 72, .cl 0 82, .p1 5,
    .cl 0 71, .cl 0 72, .p1 1, .cl 0 71, .cl 0 72, .p1 1, .cl 0 71, .cl 0 86, .cl 0 87, .cl 0 71,
    .cl 0 94, .cl 0 96, .cl 0 71, .cl 0 72, .cl 0 73, .cl 0 71, .cl 0 86, .cl 0 87, .cl 0 96,
    .cl 0 71, .cl 0 86, .cl 0 87, .bk 0, .cl 0 72, .cl 0 86, .cl 0 88, .p1 6, .cl 0 72, .cl 0 86,
    .cl 0 96, .cl 0 111, .p1 5, .cl 0 72, .cl 0 84, .cl 0 95, .cl 0 72, .cl 0 96, .p1 3, .cl 0 72,
    .cl 0 86, .cl 0 92, .p1 15, .cl 0 72, .cl 0 84, .cl 0 86, .cl 0 87, .cl 0 92, .p1 3, .cl 0 72,
    .cl 0 84, .p1 4, .cl 0 72, .cl 0 84, .cl 0 86, .cl 0 95, .p1 7, .bk 0, .cl 0 73, .cl 0 89,
    .cl 0 93, .p1 12, .cl 0 73, .cl 0 89, .cl 0 99, .cl 0 111, .cl 0 114, .cl 0 73, .cl 0 81,
    .p1 4, .cl 0 73, .cl 0 99, .p1 3, .cl 0 89, .cl 0 114, .p1 10, .cl 0 73, .cl 0 81, .cl 0 88,
    .cl 0 89, .cl 0 93, .p1 3, .cl 0 73, .cl 0 81, .cl 0 89, .cl 0 93, .cl 0 94, .cl 0 73,
    .cl 0 81, .cl 0 89, .cl 0 95, .p1 10, .bk 0, .cl 0 74, .cl 0 91, .cl 0 99, .cl 0 74, .cl 0 87,
    .cl 0 98, .p1 14, .cl 0 74, .cl 0 87, .cl 0 89, .cl 0 98, .p1 14, .cl 0 74, .cl 0 91, .p1 11,
    .cl 0 74, .cl 0 89, .p1 3, .cl 0 87, .cl 0 112, .p1 12, .cl 0 74, .cl 0 87, .cl 0 91, .cl 0 97,
    .cl 0 98, .p1 3, .cl 0 74, .cl 0 87, .cl 0 89, .p1 9, .p1 0, .bk 0, .cl 0 1, .p1 6, .cl 0 1,
    .cl 0 2, .cl 0 1, .p1 3, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1,
    .cl 0 2, .cl 0 1, .cl 0 2, .bk 0, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 4,
    .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2,
    .bk 0, .cl 0 1, .p1 3, .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3,
    .cl 0 1, .cl 0 3, .cl 0 1, .p1 11, .cl 0 1, .cl 0 3, .bk 0, .cl 0 2, .cl 0 3, .cl 0 2, .cl 0 3,
    .cl 0 2, .cl 0 3, .cl 0 2, .cl 0 3, .cl 0 2, .cl 0 3, .cl 0 2, .cl 0 3, .cl 0 2, .cl 0 4,
    .cl 0 2, .cl 0 3, .bk 0, .cl 0 5, .cl 0 10, .cl 0 5, .p1 3, .cl 0 5, .cl 0 10, .cl 0 5,
    .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5, .p1 5, .bk 0,
    .cl 0 62, .cl 0 66, .p1 3, .cl 0 62, .cl 0 68, .cl 0 73, .p1 5, .cl 0 62, .cl 0 64, .cl 0 68,
    .cl 0 73, .cl 0 77, .p1 9, .cl 0 62, .cl 0 66, .cl 0 67, .cl 0 62, .cl 0 64, .cl 0 78, .p1 2,
    .cl 0 62, .cl 0 82, .p1 2, .cl 0 62, .cl 0 66, .cl 0 67, .cl 0 68, .cl 0 73, .p1 5, .cl 0 62,
    .cl 0 64, .p1 6, .bk 0, .cl 0 64, .cl 0 66, .cl 0 68, .p1 11, .cl 0 64, .cl 0 87, .p1 2,
    .cl 0 64, .cl 0 66, .cl 0 81, .p1 2, .cl 0 64, .cl 0 74, .cl 0 89, .cl 0 64, .cl 0 87, .p1 2,
    .cl 0 64, .cl 0 93, .cl 0 64, .cl 0 74, .p1 5, .cl 0 64, .cl 0 87, .cl 0 93, .bk 0, .cl 0 61,
    .cl 0 88, .p1 1, .cl 0 61, .cl 0 88, .p1 1, .cl 0 61, .cl 0 71, .p1 5, .cl 0 61, .cl 0 71,
    .cl 0 86, .cl 0 61, .cl 0 92, .cl 0 61, .cl 0 92, .cl 0 61, .cl 0 69, .cl 0 84, .p1 1,
    .cl 0 61, .cl 0 88, .cl 0 92, .bk 0, .cl 0 63, .cl 0 67, .cl 0 86, .cl 0 88, .p1 11, .cl 0 63,
    .cl 0 67, .cl 0 72, .p1 5, .cl 0 63, .cl 0 69, .cl 0 81, .p1 8, .cl 0 63, .cl 0 67, .cl 0 69,
    .p1 15, .cl 0 63, .cl 0 69, .p1 3, .cl 0 63, .cl 0 83, .p1 1, .cl 0 63, .cl 0 83, .p1 1,
    .cl 0 63, .cl 0 69, .cl 0 81, .bk 0, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 20, .cl 0 5, .cl 0 10,
    .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10,
    .bk 0, .cl 0 58, .cl 0 72, .cl 0 84, .cl 0 88, .cl 0 90, .p1 15, .cl 0 72, .cl 0 84, .cl 0 58,
    .cl 0 59, .cl 0 72, .cl 0 72, .cl 0 84, .cl 0 58, .cl 0 72, .cl 0 84, .cl 0 88, .cl 0 72,
    .cl 0 84, .p1 1, .cl 0 58, .cl 0 71, .cl 0 72, .cl 0 72, .cl 0 84, .p1 1, .bk 0, .cl 0 74,
    .cl 0 89, .p1 2, .cl 0 56, .cl 0 74, .cl 0 82, .p1 2, .cl 0 74, .cl 0 91, .cl 0 56, .cl 0 64,
    .cl 0 74, .cl 0 74, .cl 0 91, .cl 0 56, .cl 0 98, .cl 0 74, .cl 0 89, .cl 0 91, .cl 0 56,
    .cl 0 66, .cl 0 74, .bk 0, .cl 0 71, .cl 0 94, .cl 0 71, .cl 0 72, .cl 0 73, .p1 6, .cl 0 71,
    .cl 0 86, .cl 0 94, .cl 0 59, .cl 0 61, .cl 0 71, .cl 0 59, .cl 0 71, .cl 0 72, .cl 0 79,
    .cl 0 80, .cl 0 71, .cl 0 72, .p1 11, .cl 0 71, .cl 0 72, .cl 0 79, .p1 1, .cl 0 59, .cl 0 69,
    .cl 0 71, .bk 0, .cl 0 73, .cl 0 81, .cl 0 86, .cl 0 73, .cl 0 81, .cl 0 57, .cl 0 73,
    .cl 0 74, .p1 12, .cl 0 73, .cl 0 81, .cl 0 57, .cl 0 73, .cl 0 81, .cl 0 87, .cl 0 90, .p1 12,
    .cl 0 73, .cl 0 81, .p1 2, .cl 0 73, .cl 0 81, .cl 0 73, .cl 0 81, .p1 2, .bk 0, .cl 0 5,
    .cl 0 15, .cl 0 5, .cl 0 15, .cl 0 5, .cl 0 15, .cl 0 5, .cl 0 15, .cl 0 5, .cl 0 15, .cl 0 5,
    .p1 4, .cl 0 5, .cl 0 15, .cl 0 5, .p1 3, .bk 0, .cl 0 57, .cl 0 62, .p1 4, .cl 0 57, .cl 0 68,
    .p1 3, .cl 0 57, .cl 0 73, .cl 0 74, .p1 6, .cl 0 57, .cl 0 62, .cl 0 65, .cl 0 66, .cl 0 57,
    .cl 0 62, .cl 0 65, .cl 0 57, .cl 0 62, .cl 0 66, .cl 0 57, .cl 0 81, .p1 2, .cl 0 57,
    .cl 0 68, .cl 0 86, .p1 10, .bk 0, .cl 0 59, .cl 0 86, .p1 1, .cl 0 59, .cl 0 72, .cl 0 73,
    .p1 3, .cl 0 59, .cl 0 71, .cl 0 83, .cl 0 84, .p1 6, .cl 0 71, .cl 0 83, .p1 7, .cl 0 59,
    .cl 0 72, .cl 0 74, .cl 0 77, .p1 15, .cl 0 59, .cl 0 71, .cl 0 72, .p1 8, .cl 0 59, .cl 0 72,
    .p1 3, .cl 0 71, .cl 0 83, .p1 3, .bk 0, .cl 0 56, .cl 0 73, .cl 0 74, .cl 0 82, .cl 0 83,
    .p1 2, .cl 0 56, .cl 0 57, .p1 11, .cl 0 56, .cl 0 73, .p1 3, .cl 0 74, .cl 0 82, .p1 10,
    .cl 0 56, .cl 0 57, .cl 0 74, .cl 0 79, .cl 0 80, .cl 0 56, .cl 0 57, .cl 0 58, .p1 6,
    .cl 0 56, .cl 0 57, .cl 0 68, .cl 0 74, .cl 0 82, .p1 3, .bk 0, .cl 0 58, .cl 0 63, .cl 0 65,
    .cl 0 58, .cl 0 67, .p1 3, .cl 0 58, .cl 0 84, .p1 1, .cl 0 58, .cl 0 63, .cl 0 65, .cl 0 69,
    .cl 0 58, .cl 0 63, .p1 4, .cl 0 58, .cl 0 63, .cl 0 65, .cl 0 66, .p1 11, .cl 0 72, .cl 0 88,
    .p1 8, .cl 0 58, .cl 0 67, .cl 0 87, .bk 0, .cl 0 10, .cl 0 15, .cl 0 10, .cl 0 15, .cl 0 10,
    .cl 0 15, .cl 0 10, .cl 0 15, .cl 0 10, .cl 0 15, .cl 0 10, .cl 0 20, .cl 0 10, .cl 0 15,
    .cl 0 10, .cl 0 15, .bk 0, .cl 0 67, .cl 0 83, .p1 1, .cl 0 63, .cl 0 67, .cl 0 72, .p1 7,
    .cl 0 63, .cl 0 67, .cl 0 69, .cl 0 78, .cl 0 83, .cl 0 67, .cl 0 69, .p1 6, .cl 0 67,
    .cl 0 69, .cl 0 71, .cl 0 67, .cl 0 83, .cl 0 67, .cl 0 83, .cl 0 63, .cl 0 67, .cl 0 69,
    .cl 0 72, .cl 0 74, .cl 0 77, .p1 1, .bk 0, .cl 0 61, .cl 0 63, .cl 0 69, .cl 0 69, .cl 0 71,
    .cl 0 81, .cl 0 61, .cl 0 69, .cl 0 71, .p1 7, .cl 0 69, .cl 0 71, .p1 3, .cl 0 61, .cl 0 67,
    .cl 0 69, .cl 0 69, .cl 0 88, .p1 1, .cl 0 69, .cl 0 71, .cl 0 74, .cl 0 61, .cl 0 69,
    .cl 0 84, .cl 0 86, .bk 0, .cl 0 64, .cl 0 66, .cl 0 68, .p1 9, .cl 0 64, .cl 0 66, .cl 0 74,
    .cl 0 81, .cl 0 83, .cl 0 64, .cl 0 81, .cl 0 66, .cl 0 74, .p1 3, .cl 0 64, .cl 0 81, .p1 12,
    .cl 0 64, .cl 0 81, .cl 0 83, .p1 3, .cl 0 64, .cl 0 66, .cl 0 74, .p1 10, .cl 0 66, .cl 0 87,
    .bk 0, .cl 0 68, .cl 0 82, .cl 0 62, .cl 0 68, .cl 0 73, .p1 10, .cl 0 68, .cl 0 82, .cl 0 62,
    .cl 0 91, .cl 0 68, .cl 0 82, .p1 2, .cl 0 68, .cl 0 82, .cl 0 68, .cl 0 82, .p1 2, .cl 0 68,
    .cl 0 82, .cl 0 84, .p1 0, .bk 0, .cl 0 1, .p1 4, .cl 0 1, .cl 0 2, .cl 0 1, .p1 3, .cl 0 1,
    .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .bk 0,
    .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 4, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2,
    .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .bk 0, .cl 0 1, .p1 3, .cl 0 1, .cl 0 3,
    .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3, .cl 0 1, .p1 5,
    .cl 0 1, .cl 0 3, .bk 0, .cl 0 2, .cl 0 3, .cl 0 2, .cl 0 3, .cl 0 2, .cl 0 3, .cl 0 2,
    .cl 0 3, .cl 0 2, .cl 0 3, .cl 0 2, .cl 0 3, .cl 0 2, .cl 0 4, .cl 0 2, .cl 0 3, .bk 0,
    .cl 0 5, .cl 0 10, .cl 0 5, .p1 3, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10,
    .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5, .p1 6, .bk 0, .cl 0 37, .cl 0 41, .p1 3,
    .cl 0 37, .cl 0 43, .cl 0 48, .p1 6, .cl 0 37, .cl 0 39, .cl 0 43, .cl 0 48, .cl 0 54,
    .cl 0 37, .cl 0 41, .cl 0 42, .cl 0 43, .cl 0 56, .cl 0 37, .cl 0 43, .cl 0 56, .p1 9,
    .cl 0 37, .cl 0 41, .cl 0 42, .cl 0 43, .cl 0 48, .p1 6, .cl 0 37, .cl 0 39, .p1 4, .bk 0,
    .cl 0 39, .cl 0 41, .cl 0 43, .p1 5, .cl 0 39, .cl 0 41, .cl 0 49, .cl 0 54, .cl 0 57,
    .cl 0 39, .cl 0 49, .cl 0 51, .cl 0 41, .cl 0 57, .cl 0 39, .cl 0 41, .cl 0 57, .p1 14,
    .cl 0 39, .cl 0 41, .cl 0 57, .p1 14, .cl 0 39, .cl 0 49, .p1 6, .cl 0 39, .cl 0 41, .cl 0 57,
    .p1 11, .bk 0, .cl 0 36, .cl 0 44, .cl 0 58, .p1 13, .cl 0 36, .cl 0 44, .cl 0 46, .cl 0 51,
    .cl 0 58, .cl 0 36, .cl 0 46, .p1 6, .cl 0 36, .cl 0 44, .cl 0 46, .cl 0 51, .cl 0 52, .p1 4,
    .cl 0 36, .cl 0 44, .cl 0 58, .p1 9, .cl 0 36, .cl 0 44, .cl 0 58, .p1 13, .cl 0 36, .cl 0 46,
    .cl 0 54, .cl 0 36, .cl 0 44, .cl 0 58, .p1 11, .bk 0, .cl 0 38, .cl 0 58, .p1 8, .cl 0 38,
    .cl 0 42, .cl 0 47, .p1 6, .cl 0 38, .cl 0 44, .cl 0 56, .cl 0 57, .cl 0 38, .cl 0 42,
    .cl 0 44, .p1 13, .cl 0 38, .cl 0 44, .p1 3, .cl 0 38, .cl 0 58, .p1 8, .cl 0 38, .cl 0 42,
    .cl 0 59, .p1 13, .cl 0 38, .cl 0 42, .cl 0 44, .cl 0 47, .cl 0 51, .p1 4, .bk 0, .cl 0 5,
    .cl 0 10, .cl 0 5, .cl 0 20, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5,
    .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10, .bk 0, .cl 0 47, .cl 0 58, .cl 0 33, .cl 0 61,
    .cl 0 33, .cl 0 34, .cl 0 47, .cl 0 47, .cl 0 58, .cl 0 47, .cl 0 58, .cl 0 59, .p1 3,
    .cl 0 47, .cl 0 58, .cl 0 59, .p1 5, .cl 0 33, .cl 0 46, .cl 0 47, .cl 0 47, .cl 0 58, .bk 0,
    .cl 0 49, .cl 0 56, .cl 0 31, .cl 0 49, .cl 0 56, .cl 0 57, .cl 0 62, .cl 0 49, .cl 0 56,
    .cl 0 57, .p1 14, .cl 0 31, .cl 0 39, .cl 0 49, .cl 0 49, .cl 0 56, .cl 0 49, .cl 0 56,
    .cl 0 31, .cl 0 49, .cl 0 56, .cl 0 57, .p1 14, .cl 0 31, .cl 0 41, .cl 0 49, .bk 0, .cl 0 46,
    .cl 0 59, .cl 0 46, .cl 0 47, .cl 0 48, .p1 4, .cl 0 46, .cl 0 59, .cl 0 61, .p1 15, .cl 0 34,
    .cl 0 36, .cl 0 46, .cl 0 46, .cl 0 59, .cl 0 46, .cl 0 47, .p1 5, .cl 0 46, .cl 0 47,
    .cl 0 59, .p1 1, .cl 0 34, .cl 0 44, .cl 0 46, .bk 0, .cl 0 32, .cl 0 48, .cl 0 57, .cl 0 62,
    .cl 0 64, .cl 0 48, .cl 0 57, .cl 0 62, .p1 12, .cl 0 32, .cl 0 48, .cl 0 49, .p1 14, .cl 0 48,
    .cl 0 57, .cl 0 48, .cl 0 57, .cl 0 32, .cl 0 48, .cl 0 57, .cl 0 62, .p1 12, .cl 0 48,
    .cl 0 57, .cl 0 62, .p1 3, .cl 0 48, .cl 0 57, .bk 0, .cl 0 5, .cl 0 15, .cl 0 5, .cl 0 15,
    .cl 0 5, .cl 0 15, .cl 0 5, .cl 0 15, .cl 0 5, .cl 0 15, .cl 0 5, .p1 11, .cl 0 5, .cl 0 15,
    .cl 0 5, .p1 3, .bk 0, .cl 0 32, .cl 0 37, .p1 11, .cl 0 32, .cl 0 43, .p1 3, .cl 0 32,
    .cl 0 48, .cl 0 49, .p1 4, .cl 0 32, .cl 0 37, .cl 0 40, .cl 0 41, .cl 0 32, .cl 0 37,
    .cl 0 40, .cl 0 32, .cl 0 37, .cl 0 41, .cl 0 32, .cl 0 56, .p1 10, .cl 0 32, .cl 0 48,
    .cl 0 57, .bk 0, .cl 0 34, .cl 0 46, .cl 0 59, .cl 0 34, .cl 0 47, .cl 0 48, .p1 3, .cl 0 34,
    .cl 0 46, .cl 0 59, .p1 1, .cl 0 34, .cl 0 46, .cl 0 59, .cl 0 34, .cl 0 47, .cl 0 49,
    .cl 0 58, .cl 0 34, .cl 0 46, .cl 0 47, .p1 7, .cl 0 34, .cl 0 47, .p1 3, .cl 0 34, .cl 0 46,
    .cl 0 59, .p1 1, .bk 0, .cl 0 31, .cl 0 49, .cl 0 56, .cl 0 31, .cl 0 32, .p1 5, .cl 0 31,
    .cl 0 48, .p1 3, .cl 0 31, .cl 0 49, .cl 0 56, .cl 0 31, .cl 0 49, .cl 0 56, .cl 0 31,
    .cl 0 32, .cl 0 33, .p1 4, .cl 0 31, .cl 0 32, .cl 0 43, .cl 0 31, .cl 0 49, .cl 0 56, .p1 2,
    .bk 0, .cl 0 33, .cl 0 38, .cl 0 40, .cl 0 33, .cl 0 42, .p1 3, .cl 0 33, .cl 0 47, .cl 0 58,
    .p1 1, .cl 0 33, .cl 0 38, .cl 0 40, .cl 0 44, .cl 0 33, .cl 0 38, .p1 11, .cl 0 33, .cl 0 38,
    .cl 0 40, .cl 0 41, .p1 5, .cl 0 33, .cl 0 47, .cl 0 58, .cl 0 33, .cl 0 47, .cl 0 58, .bk 0,
    .cl 0 10, .cl 0 15, .cl 0 10, .cl 0 15, .cl 0 10, .cl 0 15, .cl 0 10, .cl 0 15, .cl 0 10,
    .cl 0 15, .cl 0 10, .cl 0 20, .cl 0 10, .cl 0 15, .cl 0 10, .cl 0 15, .bk 0, .cl 0 38,
    .cl 0 59, .p1 3, .cl 0 38, .cl 0 42, .cl 0 47, .p1 15, .cl 0 38, .cl 0 42, .cl 0 44, .cl 0 59,
    .p1 3, .cl 0 42, .cl 0 44, .p1 4, .cl 0 42, .cl 0 44, .cl 0 46, .cl 0 38, .cl 0 42, .cl 0 67,
    .cl 0 42, .cl 0 63, .cl 0 38, .cl 0 42, .cl 0 44, .cl 0 47, .cl 0 49, .cl 0 51, .p1 3, .bk 0,
    .cl 0 36, .cl 0 38, .cl 0 44, .cl 0 36, .cl 0 44, .cl 0 46, .cl 0 58, .p1 3, .cl 0 36,
    .cl 0 44, .cl 0 46, .p1 15, .cl 0 44, .cl 0 46, .p1 3, .cl 0 36, .cl 0 42, .cl 0 44, .cl 0 44,
    .cl 0 61, .cl 0 44, .cl 0 46, .cl 0 49, .cl 0 44, .cl 0 61, .cl 0 63, .cl 0 65, .p1 13, .bk 0,
    .cl 0 39, .cl 0 41, .cl 0 43, .p1 10, .cl 0 39, .cl 0 41, .cl 0 49, .cl 0 57, .p1 3, .cl 0 41,
    .cl 0 49, .cl 0 61, .p1 11, .cl 0 41, .cl 0 49, .p1 3, .cl 0 39, .cl 0 41, .cl 0 66, .cl 0 41,
    .cl 0 64, .cl 0 39, .cl 0 41, .cl 0 49, .p1 12, .cl 0 39, .cl 0 41, .cl 0 64, .cl 0 66, .bk 0,
    .cl 0 43, .cl 0 62, .cl 0 64, .p1 10, .cl 0 37, .cl 0 43, .cl 0 48, .p1 12, .cl 0 43, .cl 0 62,
    .cl 0 43, .cl 0 62, .cl 0 37, .cl 0 56, .p1 3, .cl 0 43, .cl 0 62, .cl 0 64, .p1 3, .cl 0 43,
    .cl 0 62, .cl 0 43, .cl 0 62, .cl 0 66, .p1 5]

private theorem cdOK237 : CdOK ⟨2, 0, 3, 7⟩ tab23 cd237 where
  size := by decide +kernel
  rep := by decide +kernel
  orb := by decide +kernel
  gp := by decide +kernel
  nu := by decide +kernel
  al := by decide +kernel
  be := by decide +kernel
  m := by decide +kernel

private theorem run237 : run cd237 3752 [(z16, z16)] cert237 = true := by
  decide +kernel

private theorem case237 :
    (tablesOKb ⟨2, 0, 3, 7⟩ (orbitData ⟨2, 0, 3, 7⟩) && g8b ⟨2, 0, 3, 7⟩ &&
      search ⟨2, 0, 3, 7⟩ (orbitData ⟨2, 0, 3, 7⟩) 17
        (Array.replicate (orbitData ⟨2, 0, 3, 7⟩).reps.size none)) = true := by
  rw [orbitData_congr (P := ⟨2, 0, 3, 7⟩) (Q := ⟨2, 0, 3, 3⟩) rfl, orbitData23]
  refine search_case ?_ ?_ cdOK237 run237
  · rw [tablesOKb_congr (P := ⟨2, 0, 3, 7⟩) (Q := ⟨2, 0, 3, 3⟩) rfl]
    exact tablesOKb23
  · rw [g8b_congr (P := ⟨2, 0, 3, 7⟩) (Q := ⟨2, 0, 3, 3⟩) rfl]
    exact g8b23

private def tab32 : Tables where
  lookup := #[
    none, some (0, 0), some (0, 2), some (0, 6), some (0, 4), some (0, 7), some (1, 0),
    some (2, 0), some (1, 7), some (2, 5), some (0, 1), some (1, 1), some (1, 2), some (2, 7),
    some (2, 2), some (0, 5), some (2, 6), some (2, 3), some (1, 6), some (1, 5), some (0, 3),
    some (2, 1), some (1, 3), some (2, 4), some (1, 4), some (3, 0), some (4, 0), some (5, 0),
    some (5, 4), some (4, 4), some (6, 0), some (7, 0), some (8, 0), some (9, 0), some (10, 0),
    some (11, 0), some (12, 0), some (13, 0), some (14, 0), some (15, 0), some (11, 4),
    some (15, 4), some (14, 4), some (13, 4), some (12, 4), some (6, 4), some (10, 4), some (9, 4),
    some (8, 4), some (7, 4), some (3, 3), some (11, 7), some (6, 3), some (6, 7), some (11, 3),
    some (4, 7), some (12, 7), some (10, 3), some (7, 7), some (15, 3), some (5, 7), some (13, 7),
    some (9, 3), some (8, 7), some (14, 3), some (5, 3), some (14, 7), some (8, 3), some (9, 7),
    some (13, 3), some (4, 3), some (15, 7), some (7, 3), some (10, 7), some (12, 3), some (3, 1),
    some (6, 1), some (11, 1), some (11, 5), some (6, 5), some (5, 5), some (9, 1), some (14, 1),
    some (13, 5), some (8, 5), some (4, 1), some (7, 1), some (12, 1), some (15, 5), some (10, 5),
    some (4, 5), some (10, 1), some (15, 1), some (12, 5), some (7, 5), some (5, 1), some (8, 1),
    some (13, 1), some (14, 5), some (9, 5), some (3, 2), some (5, 6), some (4, 2), some (4, 6),
    some (5, 2), some (11, 6), some (13, 6), some (15, 6), some (12, 6), some (14, 6), some (6, 2),
    some (9, 2), some (7, 2), some (10, 2), some (8, 2), some (6, 6), some (8, 6), some (10, 6),
    some (7, 6), some (9, 6), some (11, 2), some (14, 2), some (12, 2), some (15, 2), some (13, 2)]
  reps := #[
    (0, 0, 1), (0, 1, 1), (0, 1, 2), (1, 0, 0), (1, 0, 1), (1, 0, 2), (1, 1, 0), (1, 1, 1),
    (1, 1, 2), (1, 1, 3), (1, 1, 4), (1, 2, 0), (1, 2, 1), (1, 2, 2), (1, 2, 3), (1, 2, 4)]

private def orb32 : ℕ := pack [
    0, 0, 2, 6, 4, 7, 8, 16, 15, 21, 1, 9, 10, 23, 18, 5, 22, 19, 14, 13, 3, 17, 11, 20, 12, 24,
    32, 40, 44, 36, 48, 56, 64, 72, 80, 88, 96, 104, 112, 120, 92, 124, 116, 108, 100, 52, 84, 76,
    68, 60, 27, 95, 51, 55, 91, 39, 103, 83, 63, 123, 47, 111, 75, 71, 115, 43, 119, 67, 79, 107,
    35, 127, 59, 87, 99, 25, 49, 89, 93, 53, 45, 73, 113, 109, 69, 33, 57, 97, 125, 85, 37, 81,
    121, 101, 61, 41, 65, 105, 117, 77, 26, 46, 34, 38, 42, 94, 110, 126, 102, 118, 50, 74, 58, 82,
    66, 54, 70, 86, 62, 78, 90, 114, 98, 122, 106]

private def rep32 : ℕ := pack [
    1, 6, 7, 25, 26, 27, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39]

private def gp32 : ℕ := pack [
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25,
    26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49,
    50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73,
    74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97,
    98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116,
    117, 118, 119, 120, 121, 122, 123, 124, 0, 10, 20, 5, 15, 1, 11, 21, 6, 16, 2, 12, 22, 7, 17,
    3, 13, 23, 8, 18, 4, 14, 24, 9, 19, 75, 85, 95, 80, 90, 76, 86, 96, 81, 91, 77, 87, 97, 82, 92,
    78, 88, 98, 83, 93, 79, 89, 99, 84, 94, 25, 35, 45, 30, 40, 26, 36, 46, 31, 41, 27, 37, 47, 32,
    42, 28, 38, 48, 33, 43, 29, 39, 49, 34, 44, 100, 110, 120, 105, 115, 101, 111, 121, 106, 116,
    102, 112, 122, 107, 117, 103, 113, 123, 108, 118, 104, 114, 124, 109, 119, 50, 60, 70, 55, 65,
    51, 61, 71, 56, 66, 52, 62, 72, 57, 67, 53, 63, 73, 58, 68, 54, 64, 74, 59, 69, 0, 2, 4, 1, 3,
    10, 12, 14, 11, 13, 20, 22, 24, 21, 23, 5, 7, 9, 6, 8, 15, 17, 19, 16, 18, 100, 102, 104, 101,
    103, 110, 112, 114, 111, 113, 120, 122, 124, 121, 123, 105, 107, 109, 106, 108, 115, 117, 119,
    116, 118, 75, 77, 79, 76, 78, 85, 87, 89, 86, 88, 95, 97, 99, 96, 98, 80, 82, 84, 81, 83, 90,
    92, 94, 91, 93, 50, 52, 54, 51, 53, 60, 62, 64, 61, 63, 70, 72, 74, 71, 73, 55, 57, 59, 56, 58,
    65, 67, 69, 66, 68, 25, 27, 29, 26, 28, 35, 37, 39, 36, 38, 45, 47, 49, 46, 48, 30, 32, 34, 31,
    33, 40, 42, 44, 41, 43, 0, 20, 15, 10, 5, 2, 22, 17, 12, 7, 4, 24, 19, 14, 9, 1, 21, 16, 11, 6,
    3, 23, 18, 13, 8, 50, 70, 65, 60, 55, 52, 72, 67, 62, 57, 54, 74, 69, 64, 59, 51, 71, 66, 61,
    56, 53, 73, 68, 63, 58, 100, 120, 115, 110, 105, 102, 122, 117, 112, 107, 104, 124, 119, 114,
    109, 101, 121, 116, 111, 106, 103, 123, 118, 113, 108, 25, 45, 40, 35, 30, 27, 47, 42, 37, 32,
    29, 49, 44, 39, 34, 26, 46, 41, 36, 31, 28, 48, 43, 38, 33, 75, 95, 90, 85, 80, 77, 97, 92, 87,
    82, 79, 99, 94, 89, 84, 76, 96, 91, 86, 81, 78, 98, 93, 88, 83, 0, 4, 3, 2, 1, 20, 24, 23, 22,
    21, 15, 19, 18, 17, 16, 10, 14, 13, 12, 11, 5, 9, 8, 7, 6, 25, 29, 28, 27, 26, 45, 49, 48, 47,
    46, 40, 44, 43, 42, 41, 35, 39, 38, 37, 36, 30, 34, 33, 32, 31, 50, 54, 53, 52, 51, 70, 74, 73,
    72, 71, 65, 69, 68, 67, 66, 60, 64, 63, 62, 61, 55, 59, 58, 57, 56, 75, 79, 78, 77, 76, 95, 99,
    98, 97, 96, 90, 94, 93, 92, 91, 85, 89, 88, 87, 86, 80, 84, 83, 82, 81, 100, 104, 103, 102,
    101, 120, 124, 123, 122, 121, 115, 119, 118, 117, 116, 110, 114, 113, 112, 111, 105, 109, 108,
    107, 106, 0, 15, 5, 20, 10, 4, 19, 9, 24, 14, 3, 18, 8, 23, 13, 2, 17, 7, 22, 12, 1, 16, 6, 21,
    11, 75, 90, 80, 95, 85, 79, 94, 84, 99, 89, 78, 93, 83, 98, 88, 77, 92, 82, 97, 87, 76, 91, 81,
    96, 86, 25, 40, 30, 45, 35, 29, 44, 34, 49, 39, 28, 43, 33, 48, 38, 27, 42, 32, 47, 37, 26, 41,
    31, 46, 36, 100, 115, 105, 120, 110, 104, 119, 109, 124, 114, 103, 118, 108, 123, 113, 102,
    117, 107, 122, 112, 101, 116, 106, 121, 111, 50, 65, 55, 70, 60, 54, 69, 59, 74, 64, 53, 68,
    58, 73, 63, 52, 67, 57, 72, 62, 51, 66, 56, 71, 61, 0, 3, 1, 4, 2, 15, 18, 16, 19, 17, 5, 8, 6,
    9, 7, 20, 23, 21, 24, 22, 10, 13, 11, 14, 12, 100, 103, 101, 104, 102, 115, 118, 116, 119, 117,
    105, 108, 106, 109, 107, 120, 123, 121, 124, 122, 110, 113, 111, 114, 112, 75, 78, 76, 79, 77,
    90, 93, 91, 94, 92, 80, 83, 81, 84, 82, 95, 98, 96, 99, 97, 85, 88, 86, 89, 87, 50, 53, 51, 54,
    52, 65, 68, 66, 69, 67, 55, 58, 56, 59, 57, 70, 73, 71, 74, 72, 60, 63, 61, 64, 62, 25, 28, 26,
    29, 27, 40, 43, 41, 44, 42, 30, 33, 31, 34, 32, 45, 48, 46, 49, 47, 35, 38, 36, 39, 37, 0, 5,
    10, 15, 20, 3, 8, 13, 18, 23, 1, 6, 11, 16, 21, 4, 9, 14, 19, 24, 2, 7, 12, 17, 22, 50, 55, 60,
    65, 70, 53, 58, 63, 68, 73, 51, 56, 61, 66, 71, 54, 59, 64, 69, 74, 52, 57, 62, 67, 72, 100,
    105, 110, 115, 120, 103, 108, 113, 118, 123, 101, 106, 111, 116, 121, 104, 109, 114, 119, 124,
    102, 107, 112, 117, 122, 25, 30, 35, 40, 45, 28, 33, 38, 43, 48, 26, 31, 36, 41, 46, 29, 34,
    39, 44, 49, 27, 32, 37, 42, 47, 75, 80, 85, 90, 95, 78, 83, 88, 93, 98, 76, 81, 86, 91, 96, 79,
    84, 89, 94, 99, 77, 82, 87, 92, 97]

private theorem orbitData32 : orbitData ⟨3, 0, 2, 3⟩ = tab32 := by
  have h1 : (orbitData ⟨3, 0, 2, 3⟩).lookup = tab32.lookup := by
    decide +kernel
  have h2 : (orbitData ⟨3, 0, 2, 3⟩).reps = tab32.reps := by
    decide +kernel
  exact tables_ext h1 h2

private theorem tablesOKb32 : tablesOKb ⟨3, 0, 2, 3⟩ tab32 = true := by
  decide +kernel

private theorem g8b32 : g8b ⟨3, 0, 2, 3⟩ = true := by
  decide +kernel

private def cd323 : Cd := ⟨3, 0, 2, 3, orb32, rep32, gp32⟩

private def cert323 : List Op := [
    .bv 0, .bk 0, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .bv 1, .p1 1, .p1 1, .p1 1, .p1 1, .p1 1,
    .cl 0 5, .p1 2, .cl 0 5, .p1 1, .bk 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1,
    .cl 1 1, .cl 1 1, .p1 1, .p1 1, .cl 0 5, .p1 2, .cl 0 5, .cl 0 5, .p1 1, .cl 0 5, .cl 0 5,
    .cl 0 5, .p1 2, .p1 1, .p1 1, .cl 0 5, .p1 1, .cl 0 5, .cl 0 5, .cl 0 7, .p1 1, .cl 0 5, .p1 2,
    .cl 0 5, .cl 0 6, .cl 0 5, .p1 2, .cl 0 5, .cl 0 7, .cl 0 5, .cl 0 8, .p1 3, .cl 0 5, .cl 0 8,
    .p1 3, .cl 0 5, .cl 0 9, .p1 12, .cl 0 5, .cl 0 9, .p1 13, .cl 0 5, .cl 0 9, .p1 14, .cl 0 5,
    .cl 0 7, .p1 13, .cl 0 5, .cl 0 9, .cl 0 5, .cl 0 6, .cl 0 7, .p1 15, .cl 0 5, .cl 0 7, .p1 11,
    .cl 0 5, .cl 0 7, .p1 12, .cl 0 5, .cl 0 8, .cl 0 5, .cl 0 8, .p1 12, .cl 0 5, .cl 0 6,
    .cl 0 8, .cl 0 5, .cl 0 8, .cl 0 5, .cl 0 7, .cl 0 8, .cl 0 5, .cl 0 7, .p1 3, .cl 0 5,
    .cl 0 9, .p1 3, .cl 0 5, .cl 0 9, .p1 4, .cl 0 5, .cl 0 7, .cl 0 9, .cl 0 5, .cl 0 9, .p1 5,
    .p1 1, .cl 0 5, .p1 2, .cl 0 5, .cl 0 6, .cl 0 5, .p1 2, .cl 0 5, .cl 0 7, .cl 0 5, .cl 0 8,
    .p1 3, .cl 0 5, .cl 0 8, .p1 3, .cl 0 5, .cl 0 9, .p1 13, .cl 0 5, .cl 0 9, .p1 9, .cl 0 5,
    .cl 0 9, .p1 8, .cl 0 5, .cl 0 7, .p1 9, .cl 0 5, .cl 0 9, .cl 0 5, .cl 0 6, .cl 0 7, .p1 14,
    .cl 0 5, .cl 0 7, .p1 5, .cl 0 5, .cl 0 7, .p1 13, .cl 0 5, .cl 0 8, .cl 0 5, .cl 0 8, .p1 13,
    .cl 0 5, .cl 0 6, .cl 0 8, .cl 0 5, .cl 0 8, .cl 0 5, .cl 0 7, .cl 0 8, .cl 0 5, .cl 0 7,
    .p1 3, .cl 0 5, .cl 0 9, .p1 3, .cl 0 5, .cl 0 9, .p1 11, .cl 0 5, .cl 0 7, .cl 0 9, .cl 0 5,
    .cl 0 9, .p1 6, .p1 1, .cl 0 5, .p1 2, .cl 0 5, .cl 0 6, .cl 0 5, .p1 2, .cl 0 5, .cl 0 7,
    .cl 0 5, .cl 0 8, .p1 3, .cl 0 5, .cl 0 8, .p1 3, .cl 0 5, .cl 0 9, .p1 7, .cl 0 5, .cl 0 9,
    .p1 12, .cl 0 5, .cl 0 9, .p1 15, .cl 0 5, .cl 0 7, .p1 12, .cl 0 5, .cl 0 9, .cl 0 5, .cl 0 6,
    .cl 0 7, .p1 10, .cl 0 5, .cl 0 7, .p1 4, .cl 0 5, .cl 0 7, .p1 7, .cl 0 5, .cl 0 8, .cl 0 5,
    .cl 0 8, .p1 7, .cl 0 5, .cl 0 6, .cl 0 8, .cl 0 5, .cl 0 8, .cl 0 5, .cl 0 7, .cl 0 8,
    .cl 0 5, .cl 0 7, .p1 3, .cl 0 5, .cl 0 9, .p1 3, .cl 0 5, .cl 0 9, .p1 6, .cl 0 5, .cl 0 7,
    .cl 0 9, .cl 0 5, .cl 0 9, .p1 11, .p1 1, .cl 0 5, .p1 2, .cl 0 5, .cl 0 6, .cl 0 5, .p1 2,
    .cl 0 5, .cl 0 7, .cl 0 5, .cl 0 8, .p1 3, .cl 0 5, .cl 0 8, .p1 3, .cl 0 5, .cl 0 9, .p1 9,
    .cl 0 5, .cl 0 9, .p1 7, .cl 0 5, .cl 0 9, .p1 10, .cl 0 5, .cl 0 7, .p1 7, .cl 0 5, .cl 0 9,
    .cl 0 5, .cl 0 6, .cl 0 7, .p1 8, .cl 0 5, .cl 0 7, .p1 6, .cl 0 5, .cl 0 7, .p1 9, .cl 0 5,
    .cl 0 8, .cl 0 5, .cl 0 8, .p1 9, .cl 0 5, .cl 0 6, .cl 0 8, .cl 0 5, .cl 0 8, .cl 0 5,
    .cl 0 7, .cl 0 8, .cl 0 5, .cl 0 7, .p1 3, .cl 0 5, .cl 0 9, .p1 3, .cl 0 5, .cl 0 9, .p1 5,
    .cl 0 5, .cl 0 7, .cl 0 9, .cl 0 5, .cl 0 9, .p1 4, .cl 0 1, .cl 0 1, .cl 0 1, .bk 0, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .bv 1, .p1 1, .p1 1, .p1 1, .p1 1, .p1 1, .cl 0 5,
    .p1 2, .cl 0 5, .p1 1, .cl 0 5, .p1 1, .p1 1, .cl 0 5, .p1 2, .bk 1, .cl 1 1, .cl 1 1, .cl 1 1,
    .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 0 5, .p1 1, .cl 0 5, .cl 0 5, .cl 0 6, .p1 1,
    .p1 1, .cl 0 5, .p1 1, .cl 0 5, .cl 0 5, .p1 2, .p1 1, .cl 0 5, .p1 2, .cl 0 5, .p1 2, .cl 0 5,
    .cl 0 6, .cl 0 6, .p1 3, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 5,
    .cl 0 6, .cl 0 7, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 6, .p1 12,
    .cl 0 5, .cl 0 6, .p1 13, .cl 0 6, .p1 14, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 5, .cl 0 6,
    .cl 0 7, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 5, .cl 0 6, .cl 0 7,
    .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 6, .p1 3, .cl 0 5, .cl 0 6,
    .cl 0 7, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 5, .cl 0 6, .cl 0 7,
    .p1 1, .cl 0 5, .p1 2, .cl 0 5, .p1 2, .cl 0 5, .cl 0 6, .cl 0 6, .p1 3, .cl 0 5, .cl 0 6,
    .cl 0 7, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 5, .cl 0 6, .cl 0 7,
    .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 6, .p1 13, .cl 0 5, .cl 0 6, .p1 9, .cl 0 6, .p1 8, .cl 0 5,
    .cl 0 6, .cl 0 7, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 5, .cl 0 6,
    .cl 0 7, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 5, .cl 0 6, .cl 0 7,
    .cl 0 6, .p1 3, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 5, .cl 0 6,
    .cl 0 7, .cl 0 5, .cl 0 6, .cl 0 7, .p1 1, .cl 0 5, .p1 2, .cl 0 5, .p1 2, .cl 0 5, .cl 0 6,
    .cl 0 6, .p1 3, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 5, .cl 0 6,
    .cl 0 7, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 6, .p1 7, .cl 0 5,
    .cl 0 6, .p1 12, .cl 0 6, .p1 15, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 5, .cl 0 6, .cl 0 7,
    .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 5,
    .cl 0 6, .cl 0 7, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 6, .p1 3, .cl 0 5, .cl 0 6, .cl 0 7,
    .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 5, .cl 0 6, .cl 0 7, .p1 1,
    .cl 0 5, .p1 2, .cl 0 5, .p1 2, .cl 0 5, .cl 0 6, .cl 0 6, .p1 3, .cl 0 5, .cl 0 6, .cl 0 7,
    .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 5,
    .cl 0 6, .cl 0 7, .cl 0 6, .p1 9, .cl 0 5, .cl 0 6, .p1 7, .cl 0 6, .p1 10, .cl 0 5, .cl 0 6,
    .cl 0 7, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 5, .cl 0 6, .cl 0 7,
    .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 6,
    .p1 3, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 5, .cl 0 6, .cl 0 7,
    .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 1, .bk 0, .cl 0 1, .cl 0 1, .bv 1, .p1 1, .p1 1, .p1 1, .p1 1,
    .p1 1, .cl 0 5, .p1 2, .cl 0 5, .p1 1, .cl 0 5, .p1 1, .p1 1, .cl 0 5, .p1 2, .cl 0 5, .cl 0 5,
    .p1 1, .cl 0 5, .bk 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1,
    .cl 0 5, .cl 0 6, .p1 1, .p1 1, .cl 0 5, .p1 1, .cl 0 5, .cl 0 5, .p1 2, .p1 1, .cl 0 5,
    .cl 0 7, .p1 6, .cl 0 5, .cl 0 6, .cl 0 5, .cl 0 7, .p1 8, .cl 0 5, .cl 0 6, .p1 3, .cl 0 5,
    .cl 0 6, .p1 7, .cl 0 5, .cl 0 7, .p1 11, .cl 0 5, .cl 0 6, .p1 9, .cl 0 5, .cl 0 7, .p1 13,
    .cl 0 5, .cl 0 7, .p1 14, .cl 0 5, .p1 2, .cl 0 5, .cl 0 7, .p1 11, .cl 0 5, .cl 0 6, .cl 0 5,
    .cl 0 7, .cl 0 5, .cl 0 7, .p1 13, .cl 0 5, .cl 0 6, .p1 15, .cl 0 5, .cl 0 7, .p1 6, .cl 0 5,
    .cl 0 7, .p1 10, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 5, .cl 0 7, .p1 8, .cl 0 5, .p1 2, .cl 0 5,
    .cl 0 7, .p1 3, .cl 0 5, .cl 0 7, .p1 4, .cl 0 5, .cl 0 7, .cl 0 5, .cl 0 7, .p1 5, .p1 1,
    .cl 0 5, .cl 0 7, .p1 4, .cl 0 5, .cl 0 6, .cl 0 5, .cl 0 7, .p1 10, .cl 0 5, .cl 0 6, .p1 3,
    .cl 0 5, .cl 0 6, .p1 12, .cl 0 5, .cl 0 7, .p1 5, .cl 0 5, .cl 0 6, .p1 7, .cl 0 5, .cl 0 7,
    .p1 9, .cl 0 5, .cl 0 7, .p1 8, .cl 0 5, .p1 2, .cl 0 5, .cl 0 7, .p1 5, .cl 0 5, .cl 0 6,
    .cl 0 5, .cl 0 7, .cl 0 5, .cl 0 7, .p1 9, .cl 0 5, .cl 0 6, .p1 14, .cl 0 5, .cl 0 7, .p1 4,
    .cl 0 5, .cl 0 7, .p1 15, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 5, .cl 0 7, .p1 10, .cl 0 5, .p1 2,
    .cl 0 5, .cl 0 7, .p1 3, .cl 0 5, .cl 0 7, .p1 11, .cl 0 5, .cl 0 7, .cl 0 5, .cl 0 7, .p1 6,
    .p1 1, .cl 0 5, .cl 0 7, .p1 5, .cl 0 5, .cl 0 6, .cl 0 5, .cl 0 7, .p1 14, .cl 0 5, .cl 0 6,
    .p1 3, .cl 0 5, .cl 0 6, .p1 9, .cl 0 5, .cl 0 7, .p1 4, .cl 0 5, .cl 0 6, .p1 13, .cl 0 5,
    .cl 0 7, .p1 12, .cl 0 5, .cl 0 7, .p1 15, .cl 0 5, .p1 2, .cl 0 5, .cl 0 7, .p1 4, .cl 0 5,
    .cl 0 6, .cl 0 5, .cl 0 7, .cl 0 5, .cl 0 7, .p1 12, .cl 0 5, .cl 0 6, .p1 10, .cl 0 5,
    .cl 0 7, .p1 5, .cl 0 5, .cl 0 7, .p1 8, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 5, .cl 0 7, .p1 14,
    .cl 0 5, .p1 2, .cl 0 5, .cl 0 7, .p1 3, .cl 0 5, .cl 0 7, .p1 6, .cl 0 5, .cl 0 7, .cl 0 5,
    .cl 0 7, .p1 11, .p1 1, .cl 0 5, .cl 0 7, .p1 11, .cl 0 5, .cl 0 6, .cl 0 5, .cl 0 7, .p1 15,
    .cl 0 5, .cl 0 6, .p1 3, .cl 0 5, .cl 0 6, .p1 13, .cl 0 5, .cl 0 7, .p1 6, .cl 0 5, .cl 0 6,
    .p1 12, .cl 0 5, .cl 0 7, .p1 7, .cl 0 5, .cl 0 7, .p1 10, .cl 0 5, .p1 2, .cl 0 5, .cl 0 7,
    .p1 6, .cl 0 5, .cl 0 6, .cl 0 5, .cl 0 7, .cl 0 5, .cl 0 7, .p1 7, .cl 0 5, .cl 0 6, .p1 8,
    .cl 0 5, .cl 0 7, .p1 11, .cl 0 5, .cl 0 7, .p1 14, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 5,
    .cl 0 7, .p1 15, .cl 0 5, .p1 2, .cl 0 5, .cl 0 7, .p1 3, .cl 0 5, .cl 0 7, .p1 5, .cl 0 5,
    .cl 0 7, .cl 0 5, .cl 0 7, .p1 4, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .bk 0, .bv 1,
    .p1 1, .p1 1, .p1 1, .p1 1, .p1 1, .cl 0 5, .p1 2, .cl 0 5, .p1 1, .cl 0 5, .p1 1, .p1 1,
    .cl 0 5, .p1 2, .cl 0 5, .cl 0 5, .p1 1, .cl 0 5, .cl 0 5, .cl 0 5, .p1 2, .p1 1, .p1 1, .bk 1,
    .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .p1 1, .cl 0 5,
    .cl 0 6, .p1 1, .cl 0 5, .cl 0 6, .p1 5, .cl 0 6, .cl 0 5, .cl 0 6, .p1 4, .cl 0 6, .p1 3,
    .cl 0 5, .p1 2, .cl 0 5, .cl 0 6, .p1 8, .cl 0 5, .cl 0 6, .cl 0 5, .cl 0 6, .p1 10, .cl 0 5,
    .cl 0 6, .p1 6, .cl 0 5, .p1 2, .cl 0 5, .cl 0 6, .p1 13, .cl 0 5, .cl 0 6, .p1 14, .cl 0 5,
    .cl 0 6, .p1 15, .cl 0 5, .cl 0 6, .p1 11, .cl 0 5, .cl 0 6, .p1 15, .cl 0 5, .cl 0 6, .p1 14,
    .cl 0 5, .cl 0 6, .p1 13, .cl 0 5, .cl 0 6, .p1 12, .cl 0 5, .cl 0 6, .p1 11, .cl 0 5, .cl 0 6,
    .p1 10, .cl 0 5, .cl 0 6, .p1 9, .cl 0 5, .cl 0 6, .p1 8, .cl 0 5, .cl 0 6, .p1 7, .cl 0 5,
    .cl 0 6, .p1 6, .p1 1, .cl 0 5, .cl 0 6, .p1 6, .cl 0 6, .cl 0 5, .cl 0 6, .p1 11, .cl 0 6,
    .p1 3, .cl 0 5, .p1 2, .cl 0 5, .cl 0 6, .p1 10, .cl 0 5, .cl 0 6, .cl 0 5, .cl 0 6, .p1 15,
    .cl 0 5, .cl 0 6, .p1 4, .cl 0 5, .p1 2, .cl 0 5, .cl 0 6, .p1 9, .cl 0 5, .cl 0 6, .p1 8,
    .cl 0 5, .cl 0 6, .p1 14, .cl 0 5, .cl 0 6, .p1 5, .cl 0 5, .cl 0 6, .p1 14, .cl 0 5, .cl 0 6,
    .p1 8, .cl 0 5, .cl 0 6, .p1 9, .cl 0 5, .cl 0 6, .p1 13, .cl 0 5, .cl 0 6, .p1 5, .cl 0 5,
    .cl 0 6, .p1 15, .cl 0 5, .cl 0 6, .p1 7, .cl 0 5, .cl 0 6, .p1 10, .cl 0 5, .cl 0 6, .p1 12,
    .cl 0 5, .cl 0 6, .p1 4, .p1 1, .cl 0 5, .cl 0 6, .p1 11, .cl 0 6, .cl 0 5, .cl 0 6, .p1 6,
    .cl 0 6, .p1 3, .cl 0 5, .p1 2, .cl 0 5, .cl 0 6, .p1 14, .cl 0 5, .cl 0 6, .cl 0 5, .cl 0 6,
    .p1 8, .cl 0 5, .cl 0 6, .p1 5, .cl 0 5, .p1 2, .cl 0 5, .cl 0 6, .p1 12, .cl 0 5, .cl 0 6,
    .p1 15, .cl 0 5, .cl 0 6, .p1 10, .cl 0 5, .cl 0 6, .p1 4, .cl 0 5, .cl 0 6, .p1 10, .cl 0 5,
    .cl 0 6, .p1 15, .cl 0 5, .cl 0 6, .p1 12, .cl 0 5, .cl 0 6, .p1 7, .cl 0 5, .cl 0 6, .p1 4,
    .cl 0 5, .cl 0 6, .p1 8, .cl 0 5, .cl 0 6, .p1 13, .cl 0 5, .cl 0 6, .p1 14, .cl 0 5, .cl 0 6,
    .p1 9, .cl 0 5, .cl 0 6, .p1 5, .p1 1, .cl 0 5, .cl 0 6, .p1 4, .cl 0 6, .cl 0 5, .cl 0 6,
    .p1 5, .cl 0 6, .p1 3, .cl 0 5, .p1 2, .cl 0 5, .cl 0 6, .p1 15, .cl 0 5, .cl 0 6, .cl 0 5,
    .cl 0 6, .p1 14, .cl 0 5, .cl 0 6, .p1 11, .cl 0 5, .p1 2, .cl 0 5, .cl 0 6, .p1 7, .cl 0 5,
    .cl 0 6, .p1 10, .cl 0 5, .cl 0 6, .p1 8, .cl 0 5, .cl 0 6, .p1 6, .cl 0 5, .cl 0 6, .p1 8,
    .cl 0 5, .cl 0 6, .p1 10, .cl 0 5, .cl 0 6, .p1 7, .cl 0 5, .cl 0 6, .p1 9, .cl 0 5, .cl 0 6,
    .p1 6, .cl 0 5, .cl 0 6, .p1 14, .cl 0 5, .cl 0 6, .p1 12, .cl 0 5, .cl 0 6, .p1 15, .cl 0 5,
    .cl 0 6, .p1 13, .cl 0 5, .cl 0 6, .p1 11, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2,
    .cl 0 2, .cl 0 2, .p1 0, .bk 0, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2,
    .cl 0 4, .bk 0, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .bk 0,
    .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .bk 0, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .p1 0, .bk 0, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .bk 0, .cl 0 3, .cl 0 3, .cl 0 3,
    .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .bk 0, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .bk 0, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .p1 0, .bk 0, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .bk 0, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3,
    .cl 0 3, .bk 0, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 1, .bk 0,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .p1 0, .bk 0, .cl 0 2,
    .cl 0 2, .cl 0 2, .cl 0 4, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .bk 0, .cl 0 2, .cl 0 2,
    .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .bk 0, .cl 0 2, .cl 0 2, .cl 0 2,
    .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .bk 0, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .p1 0, .bk 0, .cl 0 1, .p1 5, .cl 0 1, .cl 0 2, .cl 0 1,
    .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .p1 3, .cl 0 1,
    .cl 0 2, .bk 0, .cl 0 1, .cl 0 2, .cl 0 1, .p1 4, .cl 0 1, .cl 0 2, .cl 0 1, .p1 4, .cl 0 1,
    .cl 0 2, .cl 0 1, .p1 4, .cl 0 1, .cl 0 4, .cl 0 1, .p1 4, .bk 0, .cl 0 1, .p1 3, .cl 0 1,
    .cl 0 3, .cl 0 1, .p1 4, .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3, .cl 0 1,
    .cl 0 3, .cl 0 1, .cl 0 3, .bk 0, .cl 0 2, .cl 0 3, .cl 0 2, .p1 5, .cl 0 2, .cl 0 4, .cl 0 2,
    .p1 5, .cl 0 2, .cl 0 3, .cl 0 2, .p1 5, .cl 0 2, .cl 0 3, .cl 0 2, .p1 5, .bk 0, .cl 0 5,
    .p1 3, .cl 0 5, .p1 3, .cl 0 5, .p1 3, .cl 0 5, .p1 3, .cl 0 5, .p1 3, .cl 0 10, .cl 0 5,
    .p1 3, .cl 0 5, .p1 3, .bk 0, .cl 0 31, .cl 0 44, .cl 0 46, .cl 0 31, .cl 0 44, .cl 0 31,
    .cl 0 44, .cl 0 31, .cl 0 44, .cl 0 31, .cl 0 44, .cl 0 54, .p1 6, .cl 0 31, .cl 0 36,
    .cl 0 44, .cl 0 31, .cl 0 36, .cl 0 37, .cl 0 31, .cl 0 36, .cl 0 44, .bk 0, .cl 0 32,
    .cl 0 46, .cl 0 32, .cl 0 34, .cl 0 39, .cl 0 32, .cl 0 46, .cl 0 32, .cl 0 46, .cl 0 47,
    .cl 0 32, .cl 0 34, .cl 0 38, .cl 0 32, .cl 0 34, .cl 0 35, .cl 0 32, .cl 0 34, .cl 0 45,
    .cl 0 32, .cl 0 46, .cl 0 55, .cl 0 57, .bk 0, .cl 0 33, .cl 0 49, .p1 2, .cl 0 33, .cl 0 49,
    .cl 0 33, .cl 0 49, .cl 0 58, .cl 0 61, .cl 0 33, .cl 0 49, .cl 0 58, .cl 0 67, .cl 0 33,
    .cl 0 49, .cl 0 33, .cl 0 49, .cl 0 33, .cl 0 49, .cl 0 33, .cl 0 49, .cl 0 55, .cl 0 58,
    .bk 0, .cl 0 34, .cl 0 41, .cl 0 51, .p1 6, .cl 0 34, .cl 0 41, .cl 0 34, .cl 0 41, .cl 0 34,
    .cl 0 41, .cl 0 34, .cl 0 41, .cl 0 49, .cl 0 34, .cl 0 39, .cl 0 41, .cl 0 34, .cl 0 41,
    .cl 0 34, .cl 0 39, .cl 0 41, .bk 0, .cl 0 10, .p1 3, .cl 0 10, .p1 3, .cl 0 10, .p1 3,
    .cl 0 10, .p1 3, .cl 0 10, .p1 3, .cl 0 10, .p1 3, .cl 0 10, .p1 3, .cl 0 20, .bk 0, .cl 0 36,
    .cl 0 43, .cl 0 36, .cl 0 43, .cl 0 56, .p1 14, .cl 0 36, .cl 0 37, .cl 0 43, .cl 0 36,
    .cl 0 43, .cl 0 36, .cl 0 37, .cl 0 40, .cl 0 36, .cl 0 43, .cl 0 56, .p1 14, .cl 0 36,
    .cl 0 43, .cl 0 36, .cl 0 43, .bk 0, .cl 0 37, .cl 0 47, .cl 0 49, .cl 0 37, .cl 0 47,
    .cl 0 60, .cl 0 37, .cl 0 62, .cl 0 65, .cl 0 37, .cl 0 81, .cl 0 37, .cl 0 47, .cl 0 55,
    .cl 0 63, .p1 6, .cl 0 37, .cl 0 68, .p1 3, .cl 0 37, .cl 0 68, .p1 3, .cl 0 37, .cl 0 47,
    .cl 0 56, .bk 0, .cl 0 38, .cl 0 48, .cl 0 55, .cl 0 62, .p1 6, .cl 0 38, .cl 0 48, .cl 0 60,
    .cl 0 38, .cl 0 67, .p1 3, .cl 0 38, .cl 0 66, .cl 0 82, .cl 0 83, .cl 0 38, .cl 0 66, .p1 4,
    .cl 0 38, .cl 0 63, .cl 0 66, .cl 0 38, .cl 0 63, .cl 0 65, .cl 0 38, .cl 0 48, .cl 0 59,
    .bk 0, .cl 0 39, .cl 0 42, .cl 0 46, .cl 0 39, .cl 0 42, .cl 0 59, .p1 13, .cl 0 39, .cl 0 42,
    .cl 0 39, .cl 0 42, .cl 0 39, .cl 0 42, .cl 0 39, .cl 0 42, .cl 0 44, .cl 0 39, .cl 0 42,
    .p1 1, .cl 0 39, .cl 0 42, .bk 0, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5,
    .cl 0 5, .cl 0 5, .bk 0, .cl 0 41, .cl 0 64, .p1 3, .cl 0 41, .cl 0 59, .cl 0 66, .cl 0 67,
    .p1 9, .cl 0 41, .cl 0 42, .cl 0 46, .cl 0 41, .cl 0 42, .cl 0 45, .cl 0 41, .cl 0 42,
    .cl 0 51, .cl 0 41, .cl 0 64, .p1 3, .cl 0 41, .cl 0 59, .cl 0 73, .cl 0 76, .p1 8, .cl 0 41,
    .cl 0 42, .cl 0 48, .bk 0, .cl 0 42, .cl 0 48, .cl 0 42, .cl 0 48, .cl 0 42, .cl 0 48,
    .cl 0 61, .p1 5, .cl 0 42, .cl 0 48, .p1 1, .cl 0 42, .cl 0 48, .cl 0 42, .cl 0 48, .cl 0 59,
    .p1 10, .cl 0 42, .cl 0 48, .cl 0 53, .p1 11, .cl 0 42, .cl 0 48, .bk 0, .cl 0 43, .cl 0 47,
    .cl 0 43, .cl 0 47, .cl 0 43, .cl 0 47, .cl 0 52, .p1 11, .cl 0 43, .cl 0 47, .p1 2, .cl 0 43,
    .cl 0 47, .cl 0 43, .cl 0 47, .cl 0 56, .p1 7, .cl 0 43, .cl 0 47, .cl 0 62, .p1 3, .cl 0 43,
    .cl 0 47, .bk 0, .cl 0 44, .cl 0 56, .p1 3, .cl 0 44, .cl 0 56, .cl 0 76, .p1 14, .cl 0 44,
    .cl 0 56, .cl 0 76, .p1 3, .cl 0 44, .cl 0 61, .p1 3, .cl 0 44, .cl 0 61, .p1 3, .cl 0 44,
    .cl 0 61, .p1 3, .cl 0 44, .cl 0 56, .p1 6, .cl 0 44, .cl 0 56, .p1 6, .bk 0, .cl 0 15,
    .cl 0 15, .cl 0 15, .cl 0 15, .cl 0 15, .cl 0 15, .cl 0 15, .cl 0 15, .bk 0, .cl 0 46,
    .cl 0 57, .cl 0 71, .cl 0 77, .cl 0 46, .cl 0 57, .p1 5, .cl 0 46, .cl 0 59, .p1 3, .cl 0 46,
    .cl 0 57, .p1 3, .cl 0 46, .cl 0 59, .p1 3, .cl 0 46, .cl 0 57, .cl 0 63, .cl 0 72, .p1 14,
    .cl 0 46, .cl 0 57, .p1 5, .cl 0 46, .cl 0 59, .p1 3, .bk 0, .cl 0 47, .cl 0 68, .cl 0 78,
    .p1 3, .cl 0 47, .cl 0 49, .cl 0 51, .cl 0 54, .cl 0 47, .cl 0 58, .p1 3, .cl 0 47, .cl 0 58,
    .p1 3, .cl 0 47, .cl 0 49, .cl 0 58, .p1 3, .cl 0 47, .cl 0 49, .cl 0 56, .cl 0 57, .p1 4,
    .cl 0 47, .cl 0 49, .cl 0 52, .cl 0 47, .cl 0 68, .cl 0 72, .cl 0 74, .p1 15, .bk 0, .cl 0 48,
    .cl 0 67, .p1 11, .cl 0 48, .cl 0 57, .p1 3, .cl 0 48, .cl 0 57, .p1 3, .cl 0 48, .cl 0 57,
    .p1 3, .cl 0 48, .cl 0 67, .cl 0 77, .p1 3, .cl 0 48, .cl 0 67, .p1 11, .cl 0 48, .cl 0 57,
    .p1 3, .cl 0 48, .cl 0 67, .cl 0 77, .p1 7, .bk 0, .cl 0 49, .cl 0 56, .p1 3, .cl 0 49,
    .cl 0 58, .p1 5, .cl 0 49, .cl 0 58, .p1 5, .cl 0 49, .cl 0 56, .p1 3, .cl 0 49, .cl 0 58,
    .cl 0 74, .cl 0 78, .cl 0 49, .cl 0 58, .cl 0 62, .cl 0 64, .cl 0 49, .cl 0 56, .p1 3,
    .cl 0 49, .cl 0 56, .p1 3, .p1 0, .bk 0, .cl 0 1, .p1 6, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2,
    .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .p1 3, .cl 0 1, .cl 0 2, .bk 0,
    .cl 0 1, .cl 0 2, .cl 0 1, .p1 11, .cl 0 1, .cl 0 2, .cl 0 1, .p1 11, .cl 0 1, .cl 0 2,
    .cl 0 1, .p1 11, .cl 0 1, .cl 0 4, .cl 0 1, .p1 11, .bk 0, .cl 0 1, .p1 3, .cl 0 1, .cl 0 3,
    .cl 0 1, .p1 11, .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3,
    .cl 0 1, .cl 0 3, .bk 0, .cl 0 2, .cl 0 3, .cl 0 2, .p1 6, .cl 0 2, .cl 0 4, .cl 0 2, .p1 6,
    .cl 0 2, .cl 0 3, .cl 0 2, .p1 6, .cl 0 2, .cl 0 3, .cl 0 2, .p1 6, .bk 0, .cl 0 5, .p1 3,
    .cl 0 5, .p1 3, .cl 0 5, .p1 3, .cl 0 5, .p1 3, .cl 0 5, .p1 3, .cl 0 10, .cl 0 5, .p1 3,
    .cl 0 5, .p1 3, .bk 0, .cl 0 56, .cl 0 69, .cl 0 71, .cl 0 56, .cl 0 69, .cl 0 56, .cl 0 69,
    .cl 0 56, .cl 0 69, .cl 0 56, .cl 0 69, .cl 0 83, .cl 0 88, .cl 0 92, .p1 9, .cl 0 56,
    .cl 0 61, .cl 0 69, .cl 0 56, .cl 0 61, .cl 0 62, .cl 0 56, .cl 0 61, .cl 0 69, .bk 0,
    .cl 0 57, .cl 0 71, .cl 0 57, .cl 0 59, .cl 0 64, .cl 0 57, .cl 0 71, .cl 0 57, .cl 0 71,
    .cl 0 72, .cl 0 57, .cl 0 59, .cl 0 63, .cl 0 57, .cl 0 59, .cl 0 60, .cl 0 57, .cl 0 59,
    .cl 0 70, .cl 0 57, .cl 0 71, .cl 0 77, .bk 0, .cl 0 58, .cl 0 74, .p1 2, .cl 0 58, .cl 0 74,
    .cl 0 58, .cl 0 74, .cl 0 87, .p1 11, .cl 0 58, .cl 0 86, .cl 0 58, .cl 0 74, .cl 0 58,
    .cl 0 74, .cl 0 58, .cl 0 74, .cl 0 58, .cl 0 74, .cl 0 78, .bk 0, .cl 0 59, .cl 0 66,
    .cl 0 82, .cl 0 87, .cl 0 93, .p1 8, .cl 0 59, .cl 0 66, .cl 0 59, .cl 0 66, .cl 0 59,
    .cl 0 66, .cl 0 59, .cl 0 66, .cl 0 74, .cl 0 59, .cl 0 64, .cl 0 66, .cl 0 59, .cl 0 66,
    .cl 0 59, .cl 0 64, .cl 0 66, .bk 0, .cl 0 10, .p1 3, .cl 0 10, .p1 3, .cl 0 10, .p1 3,
    .cl 0 10, .p1 3, .cl 0 10, .p1 3, .cl 0 10, .p1 3, .cl 0 10, .p1 3, .cl 0 20, .bk 0, .cl 0 61,
    .cl 0 68, .cl 0 61, .cl 0 68, .cl 0 76, .cl 0 61, .cl 0 62, .cl 0 68, .cl 0 61, .cl 0 68,
    .cl 0 61, .cl 0 62, .cl 0 65, .cl 0 61, .cl 0 68, .cl 0 81, .cl 0 61, .cl 0 68, .cl 0 61,
    .cl 0 68, .bk 0, .cl 0 62, .cl 0 72, .cl 0 74, .cl 0 62, .cl 0 72, .cl 0 76, .p1 14, .cl 0 62,
    .cl 0 86, .p1 8, .cl 0 81, .p1 13, .cl 0 62, .cl 0 72, .cl 0 78, .cl 0 81, .p1 13, .cl 0 62,
    .cl 0 81, .cl 0 94, .p1 4, .cl 0 62, .cl 0 72, .cl 0 81, .bk 0, .cl 0 63, .cl 0 73, .cl 0 77,
    .cl 0 63, .cl 0 73, .cl 0 79, .p1 13, .cl 0 63, .cl 0 84, .cl 0 91, .p1 4, .cl 0 84, .p1 14,
    .cl 0 63, .cl 0 73, .cl 0 88, .cl 0 84, .p1 14, .cl 0 63, .cl 0 89, .p1 9, .cl 0 63, .cl 0 73,
    .cl 0 82, .p1 11, .bk 0, .cl 0 64, .cl 0 67, .cl 0 71, .cl 0 64, .cl 0 67, .cl 0 76, .cl 0 77,
    .cl 0 78, .cl 0 64, .cl 0 67, .cl 0 64, .cl 0 67, .cl 0 64, .cl 0 67, .cl 0 64, .cl 0 67,
    .cl 0 69, .cl 0 64, .cl 0 67, .p1 1, .cl 0 64, .cl 0 67, .bk 0, .cl 0 5, .cl 0 5, .cl 0 5,
    .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .bk 0, .cl 0 66, .cl 0 84, .p1 3, .cl 0 66,
    .cl 0 82, .cl 0 66, .cl 0 67, .cl 0 71, .cl 0 66, .cl 0 67, .cl 0 70, .cl 0 66, .cl 0 67,
    .cl 0 84, .p1 6, .cl 0 66, .cl 0 82, .cl 0 66, .cl 0 96, .cl 0 97, .cl 0 66, .cl 0 67,
    .cl 0 73, .bk 0, .cl 0 67, .cl 0 73, .cl 0 67, .cl 0 73, .cl 0 67, .cl 0 73, .cl 0 91,
    .cl 0 67, .cl 0 73, .p1 1, .cl 0 67, .cl 0 73, .cl 0 67, .cl 0 84, .cl 0 67, .cl 0 73,
    .cl 0 89, .cl 0 67, .cl 0 73, .bk 0, .cl 0 68, .cl 0 72, .cl 0 68, .cl 0 72, .cl 0 68,
    .cl 0 72, .cl 0 86, .cl 0 68, .cl 0 72, .p1 2, .cl 0 68, .cl 0 72, .cl 0 68, .cl 0 81,
    .cl 0 68, .cl 0 72, .cl 0 86, .cl 0 90, .cl 0 92, .cl 0 68, .cl 0 72, .bk 0, .cl 0 69,
    .cl 0 106, .p1 3, .cl 0 69, .cl 0 83, .cl 0 69, .cl 0 97, .cl 0 99, .cl 0 101, .cl 0 69,
    .cl 0 83, .cl 0 69, .cl 0 81, .p1 3, .cl 0 69, .cl 0 83, .cl 0 69, .cl 0 81, .cl 0 101,
    .cl 0 69, .cl 0 83, .bk 0, .cl 0 15, .cl 0 15, .cl 0 15, .cl 0 15, .cl 0 15, .cl 0 15,
    .cl 0 15, .cl 0 15, .bk 0, .cl 0 71, .cl 0 82, .cl 0 88, .cl 0 89, .cl 0 95, .cl 0 88, .p1 10,
    .cl 0 71, .cl 0 88, .cl 0 89, .p1 6, .cl 0 88, .p1 10, .cl 0 71, .cl 0 82, .cl 0 88, .cl 0 88,
    .p1 10, .cl 0 71, .cl 0 88, .cl 0 91, .p1 13, .cl 0 71, .cl 0 82, .p1 3, .bk 0, .cl 0 72,
    .cl 0 87, .cl 0 89, .cl 0 72, .cl 0 74, .cl 0 80, .cl 0 72, .cl 0 93, .p1 3, .cl 0 86, .p1 9,
    .cl 0 72, .cl 0 74, .cl 0 81, .p1 5, .cl 0 72, .cl 0 74, .cl 0 83, .p1 3, .cl 0 72, .cl 0 86,
    .cl 0 87, .cl 0 89, .p1 14, .cl 0 86, .p1 9, .bk 0, .cl 0 73, .cl 0 92, .cl 0 102, .cl 0 89,
    .p1 8, .cl 0 73, .cl 0 88, .cl 0 94, .p1 13, .cl 0 89, .p1 8, .cl 0 73, .cl 0 88, .cl 0 94,
    .cl 0 99, .p1 14, .cl 0 89, .p1 8, .cl 0 73, .cl 0 92, .p1 3, .cl 0 73, .cl 0 88, .p1 7, .bk 0,
    .cl 0 74, .cl 0 83, .cl 0 87, .cl 0 87, .p1 7, .cl 0 74, .cl 0 87, .cl 0 94, .p1 14, .cl 0 87,
    .p1 7, .cl 0 74, .cl 0 83, .cl 0 95, .cl 0 96, .p1 15, .cl 0 87, .p1 7, .cl 0 74, .cl 0 106,
    .p1 3, .cl 0 74, .cl 0 83, .p1 3, .p1 0, .bk 0, .cl 0 1, .p1 11, .cl 0 1, .cl 0 2, .cl 0 1,
    .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .p1 3, .cl 0 1,
    .cl 0 2, .bk 0, .cl 0 1, .cl 0 2, .cl 0 1, .p1 6, .cl 0 1, .cl 0 2, .cl 0 1, .p1 6, .cl 0 1,
    .cl 0 2, .cl 0 1, .p1 6, .cl 0 1, .cl 0 4, .cl 0 1, .p1 6, .bk 0, .cl 0 1, .p1 3, .cl 0 1,
    .cl 0 3, .cl 0 1, .p1 6, .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3, .cl 0 1,
    .cl 0 3, .cl 0 1, .cl 0 3, .bk 0, .cl 0 2, .cl 0 3, .cl 0 2, .p1 11, .cl 0 2, .cl 0 4, .cl 0 2,
    .p1 11, .cl 0 2, .cl 0 3, .cl 0 2, .p1 11, .cl 0 2, .cl 0 3, .cl 0 2, .p1 11, .bk 0, .cl 0 5,
    .p1 3, .cl 0 5, .p1 3, .cl 0 5, .p1 3, .cl 0 5, .p1 3, .cl 0 5, .p1 3, .cl 0 10, .cl 0 5,
    .p1 3, .cl 0 5, .p1 3, .bk 0, .cl 0 62, .cl 0 72, .cl 0 77, .cl 0 80, .cl 0 68, .p1 13,
    .cl 0 62, .cl 0 68, .cl 0 69, .p1 11, .cl 0 68, .p1 13, .cl 0 62, .cl 0 68, .cl 0 72, .p1 4,
    .cl 0 68, .p1 13, .cl 0 62, .cl 0 86, .cl 0 87, .cl 0 68, .p1 13, .bk 0, .cl 0 64, .cl 0 67,
    .cl 0 69, .cl 0 66, .p1 15, .cl 0 64, .cl 0 66, .cl 0 88, .cl 0 89, .p1 11, .cl 0 66, .p1 15,
    .cl 0 64, .cl 0 66, .cl 0 84, .p1 1, .cl 0 66, .p1 15, .cl 0 64, .cl 0 66, .cl 0 67, .cl 0 69,
    .p1 7, .cl 0 66, .p1 15, .bk 0, .cl 0 61, .cl 0 62, .cl 0 65, .cl 0 71, .p1 10, .cl 0 69,
    .p1 12, .cl 0 61, .cl 0 68, .cl 0 69, .cl 0 72, .p1 3, .cl 0 61, .cl 0 62, .cl 0 69, .cl 0 61,
    .cl 0 68, .cl 0 80, .cl 0 81, .cl 0 69, .p1 12, .cl 0 61, .cl 0 62, .p1 3, .cl 0 61, .cl 0 68,
    .p1 14, .bk 0, .cl 0 63, .cl 0 67, .cl 0 73, .p1 4, .cl 0 67, .p1 14, .cl 0 63, .cl 0 91,
    .cl 0 67, .p1 14, .cl 0 63, .cl 0 73, .cl 0 78, .cl 0 80, .cl 0 67, .p1 14, .cl 0 63, .cl 0 91,
    .cl 0 67, .p1 14, .bk 0, .cl 0 10, .p1 3, .cl 0 10, .p1 3, .cl 0 10, .p1 3, .cl 0 10, .p1 3,
    .cl 0 10, .p1 3, .cl 0 10, .p1 3, .cl 0 10, .p1 3, .cl 0 20, .bk 0, .cl 0 72, .cl 0 74, .p1 3,
    .cl 0 58, .p1 9, .cl 0 72, .cl 0 74, .cl 0 77, .p1 2, .cl 0 58, .p1 9, .cl 0 72, .cl 0 87,
    .cl 0 90, .cl 0 58, .p1 9, .cl 0 72, .cl 0 93, .cl 0 58, .p1 9, .bk 0, .cl 0 56, .cl 0 72,
    .cl 0 74, .cl 0 56, .p1 7, .cl 0 56, .cl 0 74, .cl 0 83, .cl 0 86, .cl 0 56, .p1 7, .cl 0 56,
    .cl 0 58, .cl 0 74, .cl 0 56, .p1 7, .cl 0 56, .cl 0 74, .cl 0 83, .cl 0 86, .cl 0 90, .p1 3,
    .cl 0 56, .p1 7, .bk 0, .cl 0 71, .cl 0 82, .cl 0 59, .p1 10, .cl 0 59, .cl 0 71, .cl 0 82,
    .cl 0 89, .cl 0 90, .p1 3, .cl 0 59, .p1 10, .cl 0 59, .cl 0 71, .cl 0 73, .p1 13, .cl 0 59,
    .p1 10, .cl 0 71, .cl 0 82, .cl 0 87, .cl 0 59, .p1 10, .bk 0, .cl 0 73, .cl 0 88, .cl 0 90,
    .cl 0 57, .p1 8, .cl 0 73, .cl 0 92, .cl 0 57, .p1 8, .cl 0 73, .cl 0 92, .cl 0 57, .p1 8,
    .cl 0 57, .cl 0 73, .cl 0 88, .p1 1, .cl 0 57, .p1 8, .bk 0, .cl 0 5, .cl 0 5, .cl 0 5,
    .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .bk 0, .cl 0 57, .cl 0 59, .p1 3, .cl 0 57,
    .cl 0 59, .cl 0 73, .cl 0 57, .cl 0 59, .cl 0 77, .p1 1, .cl 0 73, .p1 8, .cl 0 57, .cl 0 71,
    .cl 0 72, .cl 0 73, .cl 0 57, .cl 0 59, .cl 0 60, .cl 0 65, .p1 3, .cl 0 57, .cl 0 71,
    .cl 0 72, .cl 0 73, .p1 8, .bk 0, .cl 0 59, .cl 0 82, .cl 0 84, .cl 0 59, .cl 0 66, .cl 0 67,
    .p1 10, .cl 0 59, .cl 0 66, .p1 12, .cl 0 71, .p1 10, .cl 0 59, .cl 0 71, .cl 0 73, .p1 6,
    .cl 0 59, .cl 0 64, .p1 3, .cl 0 59, .cl 0 64, .cl 0 65, .cl 0 59, .cl 0 64, .cl 0 65, .bk 0,
    .cl 0 74, .cl 0 86, .p1 3, .cl 0 56, .cl 0 69, .cl 0 71, .p1 3, .cl 0 56, .cl 0 61, .cl 0 65,
    .cl 0 74, .p1 7, .cl 0 74, .cl 0 86, .p1 15, .cl 0 56, .cl 0 61, .p1 3, .cl 0 56, .cl 0 61,
    .cl 0 65, .cl 0 67, .p1 15, .cl 0 56, .cl 0 61, .cl 0 65, .bk 0, .cl 0 58, .cl 0 72, .cl 0 74,
    .cl 0 81, .p1 8, .cl 0 72, .p1 9, .cl 0 72, .cl 0 81, .cl 0 82, .p1 2, .cl 0 72, .p1 9,
    .cl 0 58, .cl 0 72, .cl 0 81, .cl 0 83, .p1 6, .cl 0 72, .p1 9, .cl 0 58, .cl 0 87, .p1 2,
    .cl 0 72, .p1 9, .bk 0, .cl 0 15, .cl 0 15, .cl 0 15, .cl 0 15, .cl 0 15, .cl 0 15, .cl 0 15,
    .cl 0 15, .bk 0, .cl 0 67, .cl 0 73, .p1 9, .cl 0 63, .p1 14, .cl 0 63, .cl 0 64, .cl 0 67,
    .cl 0 63, .p1 14, .cl 0 67, .cl 0 73, .cl 0 77, .cl 0 81, .cl 0 63, .p1 14, .cl 0 63, .cl 0 66,
    .cl 0 67, .cl 0 63, .p1 14, .bk 0, .cl 0 69, .cl 0 81, .cl 0 61, .p1 12, .cl 0 69, .cl 0 81,
    .cl 0 61, .p1 12, .cl 0 69, .cl 0 81, .p1 2, .cl 0 61, .p1 12, .cl 0 61, .cl 0 69, .cl 0 81,
    .p1 2, .cl 0 61, .p1 12, .bk 0, .cl 0 66, .cl 0 67, .cl 0 76, .p1 1, .cl 0 64, .p1 15,
    .cl 0 64, .cl 0 66, .cl 0 84, .p1 1, .cl 0 64, .p1 15, .cl 0 66, .cl 0 84, .cl 0 64, .p1 15,
    .cl 0 66, .cl 0 67, .p1 3, .cl 0 64, .p1 15, .bk 0, .cl 0 62, .cl 0 68, .cl 0 72, .cl 0 78,
    .cl 0 82, .p1 15, .cl 0 62, .p1 13, .cl 0 62, .cl 0 68, .cl 0 69, .p1 10, .cl 0 62, .p1 13,
    .cl 0 68, .cl 0 72, .p1 8, .cl 0 62, .p1 13, .cl 0 62, .cl 0 83, .p1 3, .cl 0 62, .p1 13,
    .p1 0, .bk 0, .cl 0 1, .p1 4, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1,
    .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .p1 3, .cl 0 1, .cl 0 2, .bk 0, .cl 0 1, .cl 0 2, .cl 0 1,
    .p1 5, .cl 0 1, .cl 0 2, .cl 0 1, .p1 5, .cl 0 1, .cl 0 2, .cl 0 1, .p1 5, .cl 0 1, .cl 0 4,
    .cl 0 1, .p1 5, .bk 0, .cl 0 1, .p1 3, .cl 0 1, .cl 0 3, .cl 0 1, .p1 5, .cl 0 1, .cl 0 3,
    .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3, .bk 0, .cl 0 2,
    .cl 0 3, .cl 0 2, .p1 4, .cl 0 2, .cl 0 4, .cl 0 2, .p1 4, .cl 0 2, .cl 0 3, .cl 0 2, .p1 4,
    .cl 0 2, .cl 0 3, .cl 0 2, .p1 4, .bk 0, .cl 0 5, .p1 3, .cl 0 5, .p1 3, .cl 0 5, .p1 3,
    .cl 0 5, .p1 3, .cl 0 5, .p1 3, .cl 0 10, .cl 0 5, .p1 3, .cl 0 5, .p1 3, .bk 0, .cl 0 37,
    .cl 0 47, .cl 0 53, .cl 0 55, .p1 7, .cl 0 43, .p1 12, .cl 0 37, .cl 0 43, .cl 0 44, .p1 4,
    .cl 0 43, .p1 12, .cl 0 37, .cl 0 43, .cl 0 47, .p1 6, .cl 0 43, .p1 12, .cl 0 37, .cl 0 43,
    .cl 0 56, .p1 7, .cl 0 43, .p1 12, .bk 0, .cl 0 39, .cl 0 42, .cl 0 44, .cl 0 41, .p1 10,
    .cl 0 39, .cl 0 41, .cl 0 57, .p1 4, .cl 0 41, .p1 10, .cl 0 39, .cl 0 41, .cl 0 57, .p1 7,
    .cl 0 41, .p1 10, .cl 0 39, .cl 0 41, .cl 0 42, .cl 0 44, .p1 9, .cl 0 41, .p1 10, .bk 0,
    .cl 0 36, .cl 0 37, .cl 0 40, .cl 0 46, .p1 8, .cl 0 44, .p1 7, .cl 0 36, .cl 0 43, .cl 0 44,
    .cl 0 47, .p1 3, .cl 0 36, .cl 0 37, .cl 0 44, .cl 0 36, .cl 0 43, .cl 0 51, .p1 8, .cl 0 44,
    .p1 7, .cl 0 36, .cl 0 37, .p1 3, .cl 0 36, .cl 0 43, .p1 15, .bk 0, .cl 0 38, .cl 0 42,
    .cl 0 48, .p1 6, .cl 0 42, .p1 15, .cl 0 38, .cl 0 42, .cl 0 59, .p1 10, .cl 0 42, .p1 15,
    .cl 0 38, .cl 0 48, .cl 0 52, .cl 0 55, .p1 10, .cl 0 42, .p1 15, .cl 0 38, .cl 0 42, .cl 0 59,
    .p1 12, .cl 0 42, .p1 15, .bk 0, .cl 0 10, .p1 3, .cl 0 10, .p1 3, .cl 0 10, .p1 3, .cl 0 10,
    .p1 3, .cl 0 10, .p1 3, .cl 0 10, .p1 3, .cl 0 10, .p1 3, .cl 0 20, .bk 0, .cl 0 47, .cl 0 49,
    .p1 3, .cl 0 33, .p1 13, .cl 0 47, .cl 0 58, .cl 0 33, .p1 13, .cl 0 33, .cl 0 61, .cl 0 33,
    .p1 13, .cl 0 47, .cl 0 58, .cl 0 33, .p1 13, .bk 0, .cl 0 31, .cl 0 47, .cl 0 49, .cl 0 31,
    .p1 9, .cl 0 49, .cl 0 56, .cl 0 31, .p1 9, .cl 0 31, .cl 0 33, .cl 0 49, .cl 0 31, .p1 9,
    .cl 0 49, .cl 0 58, .p1 3, .cl 0 31, .p1 9, .bk 0, .cl 0 46, .cl 0 57, .p1 4, .cl 0 34, .p1 8,
    .cl 0 46, .cl 0 57, .p1 3, .cl 0 34, .p1 8, .cl 0 34, .cl 0 46, .cl 0 48, .p1 12, .cl 0 34,
    .p1 8, .cl 0 46, .cl 0 59, .cl 0 34, .p1 8, .bk 0, .cl 0 32, .cl 0 64, .cl 0 32, .p1 14,
    .cl 0 48, .cl 0 57, .cl 0 32, .p1 14, .cl 0 48, .cl 0 57, .cl 0 59, .p1 12, .cl 0 32, .p1 14,
    .cl 0 48, .cl 0 57, .cl 0 32, .p1 14, .bk 0, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5,
    .cl 0 5, .cl 0 5, .cl 0 5, .bk 0, .cl 0 32, .cl 0 34, .p1 3, .cl 0 32, .cl 0 34, .cl 0 48,
    .cl 0 32, .cl 0 34, .cl 0 55, .cl 0 48, .p1 14, .cl 0 32, .cl 0 46, .cl 0 47, .cl 0 48,
    .cl 0 32, .cl 0 34, .cl 0 35, .cl 0 40, .p1 3, .cl 0 32, .cl 0 46, .cl 0 47, .cl 0 48, .p1 14,
    .bk 0, .cl 0 34, .cl 0 46, .cl 0 59, .cl 0 34, .cl 0 41, .cl 0 42, .p1 8, .cl 0 34, .cl 0 41,
    .p1 7, .cl 0 46, .p1 8, .cl 0 34, .cl 0 46, .cl 0 48, .p1 5, .cl 0 34, .cl 0 39, .p1 3,
    .cl 0 34, .cl 0 39, .cl 0 40, .cl 0 34, .cl 0 39, .cl 0 40, .bk 0, .cl 0 31, .cl 0 49,
    .cl 0 56, .p1 2, .cl 0 31, .cl 0 44, .cl 0 46, .p1 3, .cl 0 31, .cl 0 36, .cl 0 40, .cl 0 49,
    .p1 9, .cl 0 31, .cl 0 49, .cl 0 56, .cl 0 31, .cl 0 36, .p1 3, .cl 0 31, .cl 0 36, .cl 0 40,
    .cl 0 42, .p1 10, .cl 0 31, .cl 0 36, .cl 0 40, .bk 0, .cl 0 33, .cl 0 47, .cl 0 58, .p1 2,
    .cl 0 47, .p1 13, .cl 0 33, .cl 0 49, .cl 0 53, .p1 15, .cl 0 47, .p1 13, .cl 0 33, .cl 0 47,
    .cl 0 58, .p1 2, .cl 0 47, .p1 13, .cl 0 33, .cl 0 47, .cl 0 58, .cl 0 47, .p1 13, .bk 0,
    .cl 0 15, .cl 0 15, .cl 0 15, .cl 0 15, .cl 0 15, .cl 0 15, .cl 0 15, .cl 0 15, .bk 0,
    .cl 0 42, .cl 0 48, .p1 13, .cl 0 38, .p1 15, .cl 0 38, .cl 0 39, .cl 0 42, .cl 0 38, .p1 15,
    .cl 0 38, .cl 0 42, .cl 0 48, .cl 0 55, .p1 6, .cl 0 38, .p1 15, .cl 0 38, .cl 0 41, .cl 0 42,
    .cl 0 38, .p1 15, .bk 0, .cl 0 44, .cl 0 61, .cl 0 36, .p1 7, .cl 0 44, .cl 0 56, .p1 11,
    .cl 0 36, .p1 7, .cl 0 44, .cl 0 61, .cl 0 36, .p1 7, .cl 0 44, .cl 0 56, .cl 0 61, .cl 0 36,
    .p1 7, .bk 0, .cl 0 41, .cl 0 64, .cl 0 39, .p1 10, .cl 0 41, .cl 0 59, .cl 0 64, .cl 0 39,
    .p1 10, .cl 0 41, .cl 0 64, .cl 0 39, .p1 10, .cl 0 41, .cl 0 42, .p1 3, .cl 0 39, .p1 10,
    .bk 0, .cl 0 37, .cl 0 43, .cl 0 47, .cl 0 55, .p1 6, .cl 0 37, .p1 12, .cl 0 37, .cl 0 43,
    .cl 0 44, .p1 8, .cl 0 37, .p1 12, .cl 0 43, .cl 0 47, .p1 14, .cl 0 37, .p1 12, .cl 0 43,
    .cl 0 61, .p1 5, .cl 0 37, .p1 12]

private theorem cdOK323 : CdOK ⟨3, 0, 2, 3⟩ tab32 cd323 where
  size := by decide +kernel
  rep := by decide +kernel
  orb := by decide +kernel
  gp := by decide +kernel
  nu := by decide +kernel
  al := by decide +kernel
  be := by decide +kernel
  m := by decide +kernel

private theorem run323 : run cd323 3417 [(z16, z16)] cert323 = true := by
  decide +kernel

private theorem case323 :
    (tablesOKb ⟨3, 0, 2, 3⟩ (orbitData ⟨3, 0, 2, 3⟩) && g8b ⟨3, 0, 2, 3⟩ &&
      search ⟨3, 0, 2, 3⟩ (orbitData ⟨3, 0, 2, 3⟩) 17
        (Array.replicate (orbitData ⟨3, 0, 2, 3⟩).reps.size none)) = true := by
  rw [orbitData32]
  exact search_case tablesOKb32 g8b32 cdOK323 run323

private def cd327 : Cd := ⟨3, 0, 2, 7, orb32, rep32, gp32⟩

private def cert327 : List Op := [
    .bv 0, .bk 0, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .bv 1, .p1 1, .p1 1, .p1 1, .p1 1, .p1 1,
    .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .p1 1, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .p1 1, .cl 0 5,
    .bk 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 0 5,
    .cl 0 5, .p1 1, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .p1 1, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5,
    .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5,
    .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5,
    .p1 1, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5,
    .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5,
    .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .p1 1, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5,
    .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5,
    .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5,
    .p1 1, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5,
    .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5,
    .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 1, .cl 0 1, .cl 0 1, .bk 0, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .bv 1, .p1 1, .p1 1, .p1 1, .p1 1, .p1 1, .cl 0 6,
    .p1 2, .cl 0 5, .cl 0 6, .p1 2, .bk 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1,
    .cl 1 1, .cl 1 1, .p1 1, .cl 0 8, .p1 2, .cl 0 6, .cl 0 7, .cl 0 5, .cl 0 5, .p1 1, .cl 0 5,
    .cl 0 5, .cl 0 6, .cl 0 6, .p1 1, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 5, .cl 0 6, .p1 1, .cl 0 8,
    .p1 7, .cl 0 6, .cl 0 8, .p1 9, .cl 0 6, .p1 3, .cl 0 6, .p1 3, .cl 0 8, .p1 12, .cl 0 8,
    .p1 13, .cl 0 8, .p1 14, .cl 0 8, .p1 15, .cl 0 8, .cl 0 8, .p1 15, .cl 0 6, .cl 0 8, .cl 0 8,
    .p1 13, .cl 0 8, .p1 12, .cl 0 6, .p1 15, .cl 0 8, .p1 10, .cl 0 8, .p1 9, .cl 0 8, .p1 8,
    .cl 0 8, .p1 7, .cl 0 8, .p1 3, .cl 0 8, .p1 4, .cl 0 8, .p1 5, .cl 0 8, .p1 5, .cl 0 8, .p1 4,
    .p1 1, .cl 0 8, .p1 12, .cl 0 6, .cl 0 8, .p1 7, .cl 0 6, .p1 3, .cl 0 6, .p1 3, .cl 0 8,
    .p1 13, .cl 0 8, .p1 9, .cl 0 8, .p1 8, .cl 0 8, .p1 14, .cl 0 8, .cl 0 8, .p1 14, .cl 0 6,
    .cl 0 8, .cl 0 8, .p1 9, .cl 0 8, .p1 13, .cl 0 6, .p1 14, .cl 0 8, .p1 15, .cl 0 8, .p1 7,
    .cl 0 8, .p1 10, .cl 0 8, .p1 12, .cl 0 8, .p1 3, .cl 0 8, .p1 11, .cl 0 8, .p1 6, .cl 0 8,
    .p1 6, .cl 0 8, .p1 11, .p1 1, .cl 0 8, .p1 9, .cl 0 6, .cl 0 8, .p1 13, .cl 0 6, .p1 3,
    .cl 0 6, .p1 3, .cl 0 8, .p1 7, .cl 0 8, .p1 12, .cl 0 8, .p1 15, .cl 0 8, .p1 10, .cl 0 8,
    .cl 0 8, .p1 10, .cl 0 6, .cl 0 8, .cl 0 8, .p1 12, .cl 0 8, .p1 7, .cl 0 6, .p1 10, .cl 0 8,
    .p1 8, .cl 0 8, .p1 13, .cl 0 8, .p1 14, .cl 0 8, .p1 9, .cl 0 8, .p1 3, .cl 0 8, .p1 6,
    .cl 0 8, .p1 11, .cl 0 8, .p1 11, .cl 0 8, .p1 6, .p1 1, .cl 0 8, .p1 13, .cl 0 6, .cl 0 8,
    .p1 12, .cl 0 6, .p1 3, .cl 0 6, .p1 3, .cl 0 8, .p1 9, .cl 0 8, .p1 7, .cl 0 8, .p1 10,
    .cl 0 8, .p1 8, .cl 0 8, .cl 0 8, .p1 8, .cl 0 6, .cl 0 8, .cl 0 8, .p1 7, .cl 0 8, .p1 9,
    .cl 0 6, .p1 8, .cl 0 8, .p1 14, .cl 0 8, .p1 12, .cl 0 8, .p1 15, .cl 0 8, .p1 13, .cl 0 8,
    .p1 3, .cl 0 8, .p1 5, .cl 0 8, .p1 4, .cl 0 8, .p1 4, .cl 0 8, .p1 5, .cl 0 1, .bk 0, .cl 0 1,
    .cl 0 1, .bv 1, .p1 1, .p1 1, .p1 1, .p1 1, .p1 1, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .p1 1,
    .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .p1 1, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .p1 1, .bk 1,
    .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 0 5, .cl 0 5,
    .cl 0 5, .p1 1, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5,
    .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5,
    .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .p1 1, .cl 0 5, .cl 0 5, .cl 0 5,
    .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5,
    .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5,
    .cl 0 5, .p1 1, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5,
    .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5,
    .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .p1 1, .cl 0 5, .cl 0 5, .cl 0 5,
    .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5,
    .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5,
    .cl 0 5, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .bk 0, .bv 1, .p1 1, .p1 1, .p1 1, .p1 1,
    .p1 1, .cl 0 6, .p1 2, .cl 0 5, .cl 0 6, .p1 2, .cl 0 5, .p1 1, .cl 0 6, .cl 0 6, .p1 2, .bk 1,
    .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 0 5, .p1 1,
    .cl 0 5, .cl 0 5, .cl 0 6, .cl 0 6, .p1 1, .cl 0 5, .cl 0 6, .p1 2, .cl 0 5, .cl 0 6, .p1 1,
    .cl 0 6, .p1 5, .cl 0 6, .cl 0 6, .p1 4, .cl 0 6, .p1 3, .cl 0 6, .p1 7, .cl 0 6, .p1 8,
    .cl 0 6, .p1 9, .cl 0 6, .p1 10, .cl 0 6, .p1 6, .cl 0 6, .p1 12, .cl 0 6, .p1 13, .cl 0 6,
    .p1 14, .cl 0 6, .p1 15, .cl 0 6, .p1 11, .cl 0 6, .p1 15, .cl 0 6, .p1 14, .cl 0 6, .p1 13,
    .cl 0 6, .p1 12, .cl 0 6, .p1 11, .cl 0 6, .p1 10, .cl 0 6, .p1 9, .cl 0 6, .p1 8, .cl 0 6,
    .p1 7, .cl 0 6, .p1 6, .p1 1, .cl 0 6, .p1 6, .cl 0 6, .cl 0 6, .p1 11, .cl 0 6, .p1 3,
    .cl 0 6, .p1 12, .cl 0 6, .p1 10, .cl 0 6, .p1 7, .cl 0 6, .p1 15, .cl 0 6, .p1 4, .cl 0 6,
    .p1 13, .cl 0 6, .p1 9, .cl 0 6, .p1 8, .cl 0 6, .p1 14, .cl 0 6, .p1 5, .cl 0 6, .p1 14,
    .cl 0 6, .p1 8, .cl 0 6, .p1 9, .cl 0 6, .p1 13, .cl 0 6, .p1 5, .cl 0 6, .p1 15, .cl 0 6,
    .p1 7, .cl 0 6, .p1 10, .cl 0 6, .p1 12, .cl 0 6, .p1 4, .p1 1, .cl 0 6, .p1 11, .cl 0 6,
    .cl 0 6, .p1 6, .cl 0 6, .p1 3, .cl 0 6, .p1 9, .cl 0 6, .p1 14, .cl 0 6, .p1 13, .cl 0 6,
    .p1 8, .cl 0 6, .p1 5, .cl 0 6, .p1 7, .cl 0 6, .p1 12, .cl 0 6, .p1 15, .cl 0 6, .p1 10,
    .cl 0 6, .p1 4, .cl 0 6, .p1 10, .cl 0 6, .p1 15, .cl 0 6, .p1 12, .cl 0 6, .p1 7, .cl 0 6,
    .p1 4, .cl 0 6, .p1 8, .cl 0 6, .p1 13, .cl 0 6, .p1 14, .cl 0 6, .p1 9, .cl 0 6, .p1 5, .p1 1,
    .cl 0 6, .p1 4, .cl 0 6, .cl 0 6, .p1 5, .cl 0 6, .p1 3, .cl 0 6, .p1 13, .cl 0 6, .p1 15,
    .cl 0 6, .p1 12, .cl 0 6, .p1 14, .cl 0 6, .p1 11, .cl 0 6, .p1 9, .cl 0 6, .p1 7, .cl 0 6,
    .p1 10, .cl 0 6, .p1 8, .cl 0 6, .p1 6, .cl 0 6, .p1 8, .cl 0 6, .p1 10, .cl 0 6, .p1 7,
    .cl 0 6, .p1 9, .cl 0 6, .p1 6, .cl 0 6, .p1 14, .cl 0 6, .p1 12, .cl 0 6, .p1 15, .cl 0 6,
    .p1 13, .cl 0 6, .p1 11, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .bk 0,
    .cl 0 5, .cl 0 5, .cl 0 5, .bv 1, .p1 1, .p1 1, .p1 1, .p1 1, .p1 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .p1 1, .cl 0 1, .cl 0 1, .cl 0 1, .bk 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1,
    .cl 1 1, .cl 1 1, .cl 1 1, .p1 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .p1 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .p1 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .p1 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .p1 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .p1 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .bk 0, .cl 0 2, .cl 0 2, .cl 0 2,
    .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .bk 0, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2,
    .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .bk 0, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2,
    .cl 0 2, .cl 0 2, .cl 0 2, .bk 0, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .bk 0, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .bv 1, .p1 1, .p1 1,
    .p1 1, .p1 1, .p1 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .p1 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .p1 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .p1 1, .cl 0 1, .cl 0 1, .bk 1, .cl 1 1,
    .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 0 1, .p1 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .p1 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .p1 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .p1 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 5, .cl 0 5,
    .bk 0, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .bk 0, .cl 0 3,
    .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .bk 0, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .bk 0, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .bk 0, .cl 0 5, .bv 1, .p1 1, .p1 1, .p1 1, .p1 1,
    .p1 1, .cl 0 3, .bk 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1,
    .cl 0 3, .cl 0 1, .p1 1, .cl 0 3, .cl 0 3, .cl 0 1, .cl 0 1, .p1 1, .cl 0 1, .cl 0 1, .cl 0 3,
    .cl 0 3, .p1 1, .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3, .p1 1, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3,
    .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3,
    .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3,
    .p1 1, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3,
    .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3,
    .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .p1 1, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3,
    .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3,
    .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3,
    .p1 1, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3,
    .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3,
    .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5,
    .cl 0 5, .bk 0, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .bk 0,
    .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .bk 0, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .bk 0, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .bk 0, .cl 0 10, .cl 0 10, .cl 0 10,
    .cl 0 10, .cl 0 10, .cl 0 10, .cl 0 10, .bv 1, .p1 1, .p1 1, .p1 1, .p1 1, .p1 1, .cl 0 2,
    .cl 0 1, .cl 0 2, .cl 0 1, .p1 1, .cl 0 2, .cl 0 2, .cl 0 1, .cl 0 1, .p1 1, .bk 1, .cl 1 1,
    .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 0 1, .cl 0 2, .cl 0 2,
    .p1 1, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .p1 1, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2,
    .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2,
    .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .p1 1,
    .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2,
    .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2,
    .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .p1 1, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2,
    .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2,
    .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .p1 1,
    .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2,
    .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2,
    .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .bk 0, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2,
    .cl 0 2, .cl 0 2, .cl 0 2, .bk 0, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2,
    .cl 0 2, .cl 0 2, .bk 0, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2,
    .cl 0 2, .bk 0, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .p1 0,
    .bk 0, .cl 0 1, .p1 5, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2,
    .cl 0 1, .cl 0 2, .cl 0 1, .p1 3, .cl 0 1, .cl 0 2, .bk 0, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2,
    .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 4,
    .cl 0 1, .cl 0 2, .bk 0, .cl 0 1, .p1 3, .cl 0 1, .cl 0 3, .cl 0 1, .p1 4, .cl 0 1, .cl 0 3,
    .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3, .bk 0, .cl 0 2,
    .cl 0 3, .cl 0 2, .cl 0 3, .cl 0 2, .cl 0 4, .cl 0 2, .cl 0 3, .cl 0 2, .cl 0 3, .cl 0 2,
    .cl 0 3, .cl 0 2, .cl 0 3, .cl 0 2, .cl 0 3, .bk 0, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10,
    .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5, .p1 3, .cl 0 5, .cl 0 10,
    .cl 0 5, .p1 11, .bk 0, .cl 0 31, .cl 0 44, .cl 0 51, .p1 8, .cl 0 31, .cl 0 44, .cl 0 31,
    .cl 0 36, .p1 2, .cl 0 31, .cl 0 44, .cl 0 31, .cl 0 44, .cl 0 46, .cl 0 31, .cl 0 36, .p1 2,
    .cl 0 31, .cl 0 36, .cl 0 39, .cl 0 31, .cl 0 36, .cl 0 44, .bk 0, .cl 0 32, .cl 0 34, .p1 1,
    .cl 0 32, .cl 0 34, .p1 1, .cl 0 32, .cl 0 34, .cl 0 37, .cl 0 32, .cl 0 46, .cl 0 47,
    .cl 0 32, .cl 0 46, .cl 0 32, .cl 0 46, .cl 0 32, .cl 0 46, .cl 0 32, .cl 0 46, .cl 0 55,
    .p1 13, .bk 0, .cl 0 33, .cl 0 49, .cl 0 33, .cl 0 49, .cl 0 33, .cl 0 49, .cl 0 33, .cl 0 49,
    .cl 0 62, .p1 11, .cl 0 33, .cl 0 49, .p1 2, .cl 0 33, .cl 0 49, .cl 0 33, .cl 0 49, .p1 2,
    .cl 0 33, .cl 0 49, .cl 0 55, .p1 14, .bk 0, .cl 0 34, .cl 0 41, .cl 0 49, .cl 0 34, .cl 0 41,
    .cl 0 34, .cl 0 41, .cl 0 34, .cl 0 41, .cl 0 34, .cl 0 41, .cl 0 51, .p1 3, .cl 0 34,
    .cl 0 39, .p1 1, .cl 0 34, .cl 0 39, .p1 1, .cl 0 34, .cl 0 39, .cl 0 41, .bk 0, .cl 0 5,
    .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5,
    .cl 0 20, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10, .bk 0, .cl 0 36, .cl 0 37, .cl 0 43, .cl 0 36,
    .cl 0 43, .cl 0 60, .p1 10, .cl 0 36, .cl 0 43, .cl 0 36, .cl 0 37, .p1 2, .cl 0 36, .cl 0 43,
    .cl 0 36, .cl 0 43, .cl 0 59, .p1 11, .cl 0 36, .cl 0 37, .p1 2, .cl 0 36, .cl 0 37, .cl 0 38,
    .bk 0, .cl 0 37, .cl 0 47, .cl 0 48, .cl 0 37, .cl 0 47, .cl 0 59, .cl 0 37, .cl 0 61,
    .cl 0 63, .cl 0 64, .cl 0 37, .cl 0 61, .p1 8, .cl 0 37, .cl 0 47, .p1 2, .cl 0 37, .cl 0 61,
    .p1 3, .cl 0 37, .cl 0 61, .cl 0 63, .p1 10, .cl 0 37, .cl 0 47, .p1 2, .bk 0, .cl 0 38,
    .cl 0 48, .p1 1, .cl 0 38, .cl 0 48, .cl 0 56, .cl 0 38, .cl 0 67, .p1 3, .cl 0 38, .cl 0 64,
    .p1 9, .cl 0 38, .cl 0 63, .p1 10, .cl 0 38, .cl 0 64, .p1 3, .cl 0 38, .cl 0 63, .cl 0 64,
    .cl 0 68, .cl 0 69, .p1 5, .cl 0 38, .cl 0 48, .p1 1, .bk 0, .cl 0 39, .cl 0 42, .cl 0 39,
    .cl 0 42, .cl 0 60, .p1 7, .cl 0 39, .cl 0 42, .p1 1, .cl 0 39, .cl 0 42, .cl 0 39, .cl 0 42,
    .p1 1, .cl 0 39, .cl 0 42, .cl 0 44, .cl 0 39, .cl 0 42, .cl 0 39, .cl 0 42, .bk 0, .cl 0 5,
    .cl 0 15, .cl 0 5, .p1 6, .cl 0 5, .cl 0 15, .cl 0 5, .cl 0 15, .cl 0 5, .cl 0 15, .cl 0 5,
    .cl 0 15, .cl 0 5, .cl 0 15, .cl 0 5, .p1 3, .bk 0, .cl 0 41, .cl 0 42, .cl 0 49, .cl 0 41,
    .cl 0 64, .p1 3, .cl 0 41, .cl 0 71, .p1 13, .cl 0 41, .cl 0 42, .cl 0 43, .cl 0 41, .cl 0 64,
    .p1 3, .cl 0 41, .cl 0 66, .cl 0 71, .cl 0 72, .p1 9, .cl 0 41, .cl 0 42, .p1 1, .cl 0 41,
    .cl 0 42, .p1 1, .bk 0, .cl 0 42, .cl 0 48, .cl 0 42, .cl 0 48, .cl 0 42, .cl 0 48, .cl 0 52,
    .p1 12, .cl 0 42, .cl 0 48, .p1 1, .cl 0 42, .cl 0 48, .cl 0 42, .cl 0 48, .p1 1, .cl 0 42,
    .cl 0 48, .cl 0 61, .p1 5, .cl 0 42, .cl 0 48, .bk 0, .cl 0 43, .cl 0 47, .cl 0 43, .cl 0 47,
    .cl 0 43, .cl 0 47, .cl 0 61, .p1 4, .cl 0 43, .cl 0 47, .p1 2, .cl 0 43, .cl 0 47, .cl 0 43,
    .cl 0 47, .p1 2, .cl 0 43, .cl 0 47, .cl 0 52, .p1 3, .cl 0 43, .cl 0 47, .bk 0, .cl 0 44,
    .cl 0 61, .p1 3, .cl 0 44, .cl 0 61, .p1 3, .cl 0 44, .cl 0 74, .cl 0 86, .p1 3, .cl 0 44,
    .cl 0 69, .p1 9, .cl 0 44, .cl 0 61, .p1 3, .cl 0 44, .cl 0 69, .cl 0 73, .cl 0 74, .cl 0 44,
    .cl 0 74, .p1 14, .cl 0 44, .cl 0 61, .p1 2, .bk 0, .cl 0 10, .cl 0 15, .cl 0 10, .cl 0 20,
    .cl 0 10, .cl 0 15, .cl 0 10, .cl 0 15, .cl 0 10, .cl 0 15, .cl 0 10, .cl 0 15, .cl 0 10,
    .cl 0 15, .cl 0 10, .cl 0 15, .bk 0, .cl 0 46, .cl 0 71, .cl 0 73, .cl 0 74, .cl 0 77,
    .cl 0 46, .cl 0 73, .cl 0 84, .p1 3, .cl 0 46, .cl 0 59, .p1 1, .cl 0 46, .cl 0 59, .p1 3,
    .cl 0 46, .cl 0 59, .p1 3, .cl 0 46, .cl 0 73, .p1 12, .cl 0 46, .cl 0 71, .p1 14, .cl 0 46,
    .cl 0 59, .p1 3, .bk 0, .cl 0 47, .cl 0 49, .p1 2, .cl 0 47, .cl 0 49, .cl 0 58, .p1 3,
    .cl 0 47, .cl 0 58, .p1 3, .cl 0 47, .cl 0 62, .cl 0 67, .p1 15, .cl 0 47, .cl 0 62, .p1 10,
    .cl 0 47, .cl 0 49, .p1 2, .cl 0 47, .cl 0 58, .p1 3, .cl 0 47, .cl 0 58, .p1 3, .bk 0,
    .cl 0 48, .cl 0 63, .p1 7, .cl 0 48, .cl 0 73, .p1 15, .cl 0 48, .cl 0 57, .p1 3, .cl 0 48,
    .cl 0 63, .cl 0 68, .p1 12, .cl 0 48, .cl 0 63, .cl 0 64, .cl 0 48, .cl 0 57, .p1 1, .cl 0 48,
    .cl 0 57, .p1 3, .cl 0 48, .cl 0 57, .p1 3, .bk 0, .cl 0 49, .cl 0 56, .p1 3, .cl 0 49,
    .cl 0 72, .cl 0 81, .p1 3, .cl 0 49, .cl 0 74, .p1 13, .cl 0 49, .cl 0 56, .p1 3, .cl 0 49,
    .cl 0 72, .cl 0 73, .p1 14, .cl 0 49, .cl 0 72, .p1 15, .cl 0 49, .cl 0 56, .p1 2, .cl 0 49,
    .cl 0 56, .p1 3, .p1 0, .bk 0, .cl 0 1, .p1 6, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1,
    .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .p1 3, .cl 0 1, .cl 0 2, .bk 0, .cl 0 1,
    .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1,
    .cl 0 2, .cl 0 1, .cl 0 4, .cl 0 1, .cl 0 2, .bk 0, .cl 0 1, .p1 3, .cl 0 1, .cl 0 3, .cl 0 1,
    .p1 11, .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3, .cl 0 1,
    .cl 0 3, .bk 0, .cl 0 2, .cl 0 3, .cl 0 2, .cl 0 3, .cl 0 2, .cl 0 4, .cl 0 2, .cl 0 3,
    .cl 0 2, .cl 0 3, .cl 0 2, .cl 0 3, .cl 0 2, .cl 0 3, .cl 0 2, .cl 0 3, .bk 0, .cl 0 5,
    .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5,
    .p1 3, .cl 0 5, .cl 0 10, .cl 0 5, .p1 5, .bk 0, .cl 0 56, .cl 0 83, .cl 0 88, .cl 0 56,
    .cl 0 69, .cl 0 56, .cl 0 61, .p1 2, .cl 0 56, .cl 0 69, .cl 0 56, .cl 0 69, .cl 0 71,
    .cl 0 56, .cl 0 61, .p1 2, .cl 0 56, .cl 0 61, .cl 0 64, .cl 0 56, .cl 0 61, .cl 0 69, .bk 0,
    .cl 0 57, .cl 0 59, .p1 1, .cl 0 57, .cl 0 59, .p1 1, .cl 0 57, .cl 0 59, .cl 0 62, .cl 0 57,
    .cl 0 71, .cl 0 72, .cl 0 57, .cl 0 71, .cl 0 57, .cl 0 71, .cl 0 57, .cl 0 71, .cl 0 57,
    .cl 0 71, .cl 0 88, .bk 0, .cl 0 58, .cl 0 74, .cl 0 58, .cl 0 74, .cl 0 58, .cl 0 74,
    .cl 0 58, .cl 0 87, .cl 0 88, .p1 6, .cl 0 58, .cl 0 74, .p1 2, .cl 0 58, .cl 0 74, .cl 0 58,
    .cl 0 74, .p1 2, .cl 0 58, .cl 0 74, .cl 0 77, .cl 0 79, .cl 0 85, .p1 13, .bk 0, .cl 0 59,
    .cl 0 66, .cl 0 74, .cl 0 59, .cl 0 66, .cl 0 59, .cl 0 66, .cl 0 59, .cl 0 66, .cl 0 59,
    .cl 0 82, .cl 0 83, .cl 0 59, .cl 0 64, .p1 1, .cl 0 59, .cl 0 64, .p1 1, .cl 0 59, .cl 0 64,
    .cl 0 66, .bk 0, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10,
    .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 20, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10, .bk 0, .cl 0 61,
    .cl 0 62, .cl 0 68, .cl 0 61, .cl 0 81, .cl 0 82, .cl 0 61, .cl 0 68, .cl 0 61, .cl 0 62,
    .p1 2, .cl 0 61, .cl 0 68, .cl 0 61, .cl 0 68, .cl 0 81, .cl 0 61, .cl 0 62, .p1 2, .cl 0 61,
    .cl 0 62, .cl 0 63, .bk 0, .cl 0 62, .cl 0 72, .cl 0 73, .cl 0 62, .cl 0 86, .p1 3, .cl 0 62,
    .cl 0 86, .cl 0 89, .cl 0 62, .cl 0 81, .cl 0 86, .cl 0 97, .p1 10, .cl 0 62, .cl 0 72, .p1 2,
    .cl 0 62, .cl 0 81, .cl 0 94, .cl 0 102, .p1 14, .cl 0 62, .cl 0 81, .cl 0 86, .p1 8, .cl 0 62,
    .cl 0 72, .p1 2, .bk 0, .cl 0 63, .cl 0 73, .p1 1, .cl 0 63, .cl 0 73, .cl 0 83, .cl 0 88,
    .p1 7, .cl 0 63, .cl 0 84, .cl 0 89, .p1 9, .cl 0 63, .cl 0 84, .cl 0 89, .cl 0 98, .p1 7,
    .cl 0 63, .cl 0 73, .cl 0 86, .cl 0 63, .cl 0 84, .cl 0 91, .cl 0 103, .p1 13, .cl 0 63,
    .cl 0 91, .p1 4, .cl 0 63, .cl 0 73, .p1 1, .bk 0, .cl 0 64, .cl 0 67, .cl 0 64, .cl 0 67,
    .cl 0 76, .cl 0 77, .cl 0 80, .p1 15, .cl 0 64, .cl 0 67, .p1 1, .cl 0 64, .cl 0 67, .cl 0 64,
    .cl 0 67, .p1 1, .cl 0 64, .cl 0 67, .cl 0 69, .cl 0 64, .cl 0 67, .cl 0 64, .cl 0 67, .bk 0,
    .cl 0 5, .cl 0 15, .cl 0 5, .p1 4, .cl 0 5, .cl 0 15, .cl 0 5, .cl 0 15, .cl 0 5, .cl 0 15,
    .cl 0 5, .cl 0 15, .cl 0 5, .cl 0 15, .cl 0 5, .p1 3, .bk 0, .cl 0 66, .cl 0 67, .cl 0 74,
    .cl 0 66, .cl 0 96, .cl 0 97, .cl 0 66, .cl 0 96, .cl 0 97, .cl 0 98, .cl 0 105, .p1 9,
    .cl 0 66, .cl 0 67, .cl 0 68, .cl 0 66, .cl 0 84, .cl 0 91, .cl 0 66, .cl 0 84, .p1 6,
    .cl 0 66, .cl 0 67, .p1 1, .cl 0 66, .cl 0 67, .p1 1, .bk 0, .cl 0 67, .cl 0 73, .cl 0 67,
    .cl 0 73, .cl 0 67, .cl 0 73, .cl 0 89, .cl 0 67, .cl 0 73, .p1 1, .cl 0 67, .cl 0 73,
    .cl 0 67, .cl 0 73, .p1 1, .cl 0 67, .cl 0 89, .cl 0 90, .cl 0 67, .cl 0 73, .bk 0, .cl 0 68,
    .cl 0 72, .cl 0 68, .cl 0 72, .cl 0 68, .cl 0 86, .cl 0 90, .cl 0 68, .cl 0 72, .p1 2,
    .cl 0 68, .cl 0 72, .cl 0 68, .cl 0 72, .p1 2, .cl 0 68, .cl 0 72, .cl 0 86, .cl 0 68,
    .cl 0 72, .bk 0, .cl 0 69, .cl 0 81, .cl 0 94, .cl 0 69, .cl 0 81, .cl 0 84, .p1 11, .cl 0 69,
    .cl 0 81, .cl 0 92, .cl 0 94, .p1 4, .cl 0 69, .cl 0 119, .p1 7, .cl 0 69, .cl 0 99, .p1 3,
    .cl 0 69, .cl 0 81, .p1 6, .cl 0 69, .cl 0 97, .cl 0 108, .p1 7, .cl 0 69, .cl 0 111, .p1 2,
    .bk 0, .cl 0 10, .cl 0 15, .cl 0 10, .cl 0 20, .cl 0 10, .cl 0 15, .cl 0 10, .cl 0 15,
    .cl 0 10, .cl 0 15, .cl 0 10, .cl 0 15, .cl 0 10, .cl 0 15, .cl 0 10, .cl 0 15, .bk 0,
    .cl 0 71, .cl 0 82, .p1 5, .cl 0 71, .cl 0 82, .cl 0 86, .cl 0 88, .cl 0 91, .p1 3, .cl 0 71,
    .cl 0 88, .cl 0 91, .p1 13, .cl 0 71, .cl 0 98, .p1 3, .cl 0 71, .cl 0 82, .cl 0 88, .cl 0 91,
    .cl 0 93, .cl 0 71, .cl 0 88, .cl 0 98, .cl 0 112, .cl 0 113, .cl 0 71, .cl 0 88, .cl 0 89,
    .p1 6, .cl 0 71, .cl 0 82, .cl 0 88, .cl 0 95, .p1 9, .bk 0, .cl 0 72, .cl 0 74, .p1 2,
    .cl 0 72, .cl 0 74, .cl 0 87, .p1 10, .cl 0 72, .cl 0 74, .cl 0 84, .p1 4, .cl 0 72, .cl 0 87,
    .cl 0 88, .p1 3, .cl 0 72, .cl 0 87, .cl 0 89, .cl 0 97, .cl 0 72, .cl 0 74, .p1 2, .cl 0 72,
    .cl 0 93, .cl 0 97, .cl 0 72, .cl 0 86, .cl 0 87, .p1 10, .bk 0, .cl 0 73, .cl 0 88, .cl 0 89,
    .cl 0 96, .p1 12, .cl 0 89, .cl 0 114, .p1 13, .cl 0 73, .cl 0 92, .cl 0 98, .cl 0 73,
    .cl 0 92, .p1 11, .cl 0 73, .cl 0 89, .cl 0 92, .cl 0 105, .cl 0 108, .cl 0 73, .cl 0 89,
    .cl 0 96, .p1 12, .cl 0 73, .cl 0 88, .p1 3, .cl 0 73, .cl 0 88, .cl 0 89, .bk 0, .cl 0 74,
    .cl 0 83, .cl 0 95, .cl 0 74, .cl 0 83, .cl 0 87, .cl 0 89, .cl 0 94, .p1 3, .cl 0 87,
    .cl 0 112, .p1 8, .cl 0 74, .cl 0 97, .p1 3, .cl 0 74, .cl 0 83, .p1 5, .cl 0 74, .cl 0 87,
    .cl 0 97, .cl 0 112, .p1 4, .cl 0 74, .cl 0 87, .cl 0 94, .p1 14, .cl 0 74, .cl 0 83, .cl 0 87,
    .cl 0 95, .p1 8, .p1 0, .bk 0, .cl 0 1, .p1 11, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1,
    .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .p1 3, .cl 0 1, .cl 0 2, .bk 0, .cl 0 1,
    .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1,
    .cl 0 2, .cl 0 1, .cl 0 4, .cl 0 1, .cl 0 2, .bk 0, .cl 0 1, .p1 3, .cl 0 1, .cl 0 3, .cl 0 1,
    .p1 6, .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3, .cl 0 1,
    .cl 0 3, .bk 0, .cl 0 2, .cl 0 3, .cl 0 2, .cl 0 3, .cl 0 2, .cl 0 4, .cl 0 2, .cl 0 3,
    .cl 0 2, .cl 0 3, .cl 0 2, .cl 0 3, .cl 0 2, .cl 0 3, .cl 0 2, .cl 0 3, .bk 0, .cl 0 5,
    .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5,
    .p1 3, .cl 0 5, .cl 0 10, .cl 0 5, .p1 4, .bk 0, .cl 0 62, .cl 0 72, .p1 4, .cl 0 62, .cl 0 94,
    .cl 0 62, .cl 0 86, .p1 2, .cl 0 62, .cl 0 72, .cl 0 87, .cl 0 62, .cl 0 68, .cl 0 83, .p1 2,
    .cl 0 62, .cl 0 86, .p1 2, .cl 0 62, .cl 0 68, .cl 0 69, .p1 11, .cl 0 62, .cl 0 86, .cl 0 94,
    .bk 0, .cl 0 64, .cl 0 84, .p1 1, .cl 0 64, .cl 0 84, .p1 1, .cl 0 64, .cl 0 67, .p1 3,
    .cl 0 64, .cl 0 66, .cl 0 67, .p1 13, .cl 0 64, .cl 0 66, .cl 0 67, .cl 0 69, .cl 0 71, .p1 4,
    .cl 0 64, .cl 0 66, .cl 0 71, .p1 4, .cl 0 64, .cl 0 66, .cl 0 88, .cl 0 89, .p1 11, .cl 0 64,
    .cl 0 67, .cl 0 68, .p1 3, .bk 0, .cl 0 61, .cl 0 68, .cl 0 82, .p1 10, .cl 0 61, .cl 0 81,
    .p1 2, .cl 0 61, .cl 0 62, .cl 0 79, .p1 2, .cl 0 61, .cl 0 62, .cl 0 63, .p1 11, .cl 0 61,
    .cl 0 62, .cl 0 69, .cl 0 74, .cl 0 76, .p1 10, .cl 0 61, .cl 0 69, .cl 0 74, .p1 4, .cl 0 61,
    .cl 0 68, .p1 3, .cl 0 61, .cl 0 62, .p1 6, .bk 0, .cl 0 63, .cl 0 67, .cl 0 82, .p1 1,
    .cl 0 63, .cl 0 91, .cl 0 63, .cl 0 91, .cl 0 63, .cl 0 73, .cl 0 88, .cl 0 63, .cl 0 73,
    .p1 4, .cl 0 63, .cl 0 89, .p1 1, .cl 0 63, .cl 0 89, .p1 1, .cl 0 63, .cl 0 89, .cl 0 91,
    .bk 0, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5,
    .cl 0 10, .cl 0 5, .cl 0 20, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10, .bk 0, .cl 0 72, .cl 0 87,
    .cl 0 93, .cl 0 72, .cl 0 74, .p1 11, .cl 0 72, .cl 0 93, .cl 0 58, .cl 0 62, .cl 0 72,
    .cl 0 72, .cl 0 74, .cl 0 78, .p1 2, .cl 0 58, .cl 0 72, .cl 0 74, .cl 0 78, .cl 0 81,
    .cl 0 58, .cl 0 72, .cl 0 74, .cl 0 78, .cl 0 80, .cl 0 58, .cl 0 68, .cl 0 72, .bk 0,
    .cl 0 56, .cl 0 58, .cl 0 74, .cl 0 74, .cl 0 83, .p1 2, .cl 0 56, .cl 0 74, .cl 0 83,
    .cl 0 86, .cl 0 90, .p1 14, .cl 0 74, .cl 0 83, .cl 0 56, .cl 0 72, .cl 0 74, .cl 0 74,
    .cl 0 83, .cl 0 56, .cl 0 74, .cl 0 83, .cl 0 86, .cl 0 74, .cl 0 83, .p1 2, .bk 0, .cl 0 59,
    .cl 0 71, .cl 0 73, .p1 13, .cl 0 71, .cl 0 82, .p1 1, .cl 0 71, .cl 0 82, .cl 0 87, .cl 0 71,
    .cl 0 82, .cl 0 71, .cl 0 82, .cl 0 71, .cl 0 82, .cl 0 59, .cl 0 71, .cl 0 82, .cl 0 89,
    .cl 0 90, .p1 13, .cl 0 71, .cl 0 82, .p1 1, .bk 0, .cl 0 73, .cl 0 92, .cl 0 57, .cl 0 96,
    .cl 0 73, .cl 0 88, .p1 1, .cl 0 57, .cl 0 63, .cl 0 73, .cl 0 73, .cl 0 88, .cl 0 92,
    .cl 0 57, .cl 0 73, .cl 0 84, .p1 1, .cl 0 73, .cl 0 92, .cl 0 57, .cl 0 67, .cl 0 73, .bk 0,
    .cl 0 5, .cl 0 15, .cl 0 5, .p1 5, .cl 0 5, .cl 0 15, .cl 0 5, .cl 0 15, .cl 0 5, .cl 0 15,
    .cl 0 5, .cl 0 15, .cl 0 5, .cl 0 15, .cl 0 5, .p1 3, .bk 0, .cl 0 57, .cl 0 71, .p1 3,
    .cl 0 57, .cl 0 71, .cl 0 72, .cl 0 57, .cl 0 71, .cl 0 72, .cl 0 76, .p1 13, .cl 0 73,
    .cl 0 84, .p1 9, .cl 0 57, .cl 0 59, .cl 0 66, .cl 0 57, .cl 0 59, .p1 11, .cl 0 57, .cl 0 59,
    .cl 0 73, .cl 0 78, .cl 0 80, .cl 0 73, .cl 0 84, .p1 3, .bk 0, .cl 0 59, .cl 0 71, .cl 0 73,
    .p1 6, .cl 0 59, .cl 0 64, .cl 0 67, .cl 0 59, .cl 0 64, .p1 5, .cl 0 59, .cl 0 64, .cl 0 65,
    .cl 0 67, .cl 0 59, .cl 0 82, .p1 1, .cl 0 59, .cl 0 66, .p1 3, .cl 0 59, .cl 0 64, .cl 0 65,
    .cl 0 59, .cl 0 66, .cl 0 86, .bk 0, .cl 0 56, .cl 0 83, .p1 2, .cl 0 56, .cl 0 61, .cl 0 65,
    .cl 0 67, .p1 11, .cl 0 56, .cl 0 61, .cl 0 65, .cl 0 56, .cl 0 61, .cl 0 65, .cl 0 68,
    .cl 0 74, .cl 0 86, .p1 10, .cl 0 56, .cl 0 69, .p1 3, .cl 0 56, .cl 0 61, .p1 5, .cl 0 56,
    .cl 0 69, .cl 0 74, .cl 0 86, .cl 0 88, .bk 0, .cl 0 58, .cl 0 72, .cl 0 81, .cl 0 83, .p1 6,
    .cl 0 58, .cl 0 72, .cl 0 74, .p1 10, .cl 0 58, .cl 0 87, .p1 2, .cl 0 72, .cl 0 81, .p1 8,
    .cl 0 58, .cl 0 74, .p1 3, .cl 0 72, .cl 0 81, .cl 0 58, .cl 0 72, .cl 0 74, .cl 0 81,
    .cl 0 82, .cl 0 84, .cl 0 72, .cl 0 81, .p1 3, .bk 0, .cl 0 10, .cl 0 15, .cl 0 10, .cl 0 20,
    .cl 0 10, .cl 0 15, .cl 0 10, .cl 0 15, .cl 0 10, .cl 0 15, .cl 0 10, .cl 0 15, .cl 0 10,
    .cl 0 15, .cl 0 10, .cl 0 15, .bk 0, .cl 0 67, .cl 0 73, .cl 0 81, .cl 0 67, .cl 0 89, .p1 1,
    .cl 0 63, .cl 0 66, .cl 0 67, .cl 0 67, .cl 0 73, .p1 3, .cl 0 63, .cl 0 67, .cl 0 73, .p1 9,
    .cl 0 67, .cl 0 73, .cl 0 81, .p1 12, .cl 0 63, .cl 0 64, .cl 0 67, .cl 0 63, .cl 0 67,
    .cl 0 82, .cl 0 88, .bk 0, .cl 0 69, .cl 0 81, .p1 2, .cl 0 69, .cl 0 81, .cl 0 69, .cl 0 81,
    .p1 2, .cl 0 61, .cl 0 69, .cl 0 81, .cl 0 87, .cl 0 89, .p1 14, .cl 0 69, .cl 0 81, .cl 0 61,
    .cl 0 69, .cl 0 74, .p1 8, .cl 0 69, .cl 0 81, .cl 0 69, .cl 0 81, .cl 0 82, .bk 0, .cl 0 66,
    .cl 0 84, .cl 0 66, .cl 0 84, .cl 0 66, .cl 0 67, .cl 0 73, .cl 0 66, .cl 0 67, .p1 6,
    .cl 0 64, .cl 0 66, .cl 0 67, .cl 0 79, .cl 0 84, .cl 0 64, .cl 0 66, .cl 0 71, .p1 9,
    .cl 0 66, .cl 0 84, .p1 1, .cl 0 66, .cl 0 67, .cl 0 68, .p1 11, .bk 0, .cl 0 62, .cl 0 68,
    .cl 0 72, .p1 8, .cl 0 62, .cl 0 83, .cl 0 84, .p1 3, .cl 0 62, .cl 0 83, .p1 14, .cl 0 68,
    .cl 0 72, .p1 3, .cl 0 68, .cl 0 72, .cl 0 73, .cl 0 68, .cl 0 72, .cl 0 82, .cl 0 62,
    .cl 0 68, .cl 0 69, .p1 10, .cl 0 68, .cl 0 86, .p1 0, .bk 0, .cl 0 1, .p1 4, .cl 0 1, .cl 0 2,
    .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .p1 3,
    .cl 0 1, .cl 0 2, .bk 0, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1,
    .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 4, .cl 0 1, .cl 0 2, .bk 0,
    .cl 0 1, .p1 3, .cl 0 1, .cl 0 3, .cl 0 1, .p1 5, .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3, .cl 0 1,
    .cl 0 3, .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3, .bk 0, .cl 0 2, .cl 0 3, .cl 0 2, .cl 0 3,
    .cl 0 2, .cl 0 4, .cl 0 2, .cl 0 3, .cl 0 2, .cl 0 3, .cl 0 2, .cl 0 3, .cl 0 2, .cl 0 3,
    .cl 0 2, .cl 0 3, .bk 0, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5,
    .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5, .p1 3, .cl 0 5, .cl 0 10, .cl 0 5, .p1 6, .bk 0,
    .cl 0 37, .cl 0 47, .p1 6, .cl 0 37, .cl 0 43, .cl 0 56, .p1 15, .cl 0 37, .cl 0 43, .cl 0 56,
    .p1 15, .cl 0 37, .cl 0 43, .cl 0 47, .cl 0 52, .cl 0 54, .p1 5, .cl 0 37, .cl 0 47, .cl 0 53,
    .cl 0 37, .cl 0 43, .cl 0 47, .cl 0 52, .cl 0 56, .cl 0 37, .cl 0 43, .cl 0 44, .p1 4,
    .cl 0 37, .cl 0 43, .cl 0 56, .p1 11, .bk 0, .cl 0 39, .cl 0 41, .cl 0 57, .p1 12, .cl 0 39,
    .cl 0 41, .cl 0 57, .p1 7, .cl 0 39, .cl 0 42, .p1 3, .cl 0 39, .cl 0 41, .cl 0 42, .p1 12,
    .cl 0 39, .cl 0 41, .cl 0 42, .cl 0 44, .cl 0 46, .p1 6, .cl 0 39, .cl 0 41, .cl 0 46, .p1 6,
    .cl 0 41, .cl 0 57, .cl 0 39, .cl 0 42, .cl 0 43, .p1 3, .bk 0, .cl 0 36, .cl 0 43, .cl 0 44,
    .cl 0 58, .cl 0 36, .cl 0 56, .p1 10, .cl 0 36, .cl 0 56, .p1 10, .cl 0 36, .cl 0 37, .cl 0 38,
    .p1 4, .cl 0 36, .cl 0 37, .cl 0 44, .cl 0 49, .cl 0 52, .cl 0 36, .cl 0 44, .cl 0 49, .p1 6,
    .cl 0 36, .cl 0 43, .p1 3, .cl 0 36, .cl 0 37, .p1 5, .bk 0, .cl 0 38, .cl 0 48, .cl 0 52,
    .cl 0 38, .cl 0 42, .cl 0 59, .p1 12, .cl 0 38, .cl 0 42, .cl 0 59, .p1 10, .cl 0 38, .cl 0 48,
    .cl 0 53, .cl 0 56, .p1 4, .cl 0 38, .cl 0 48, .p1 6, .cl 0 38, .cl 0 42, .cl 0 48, .cl 0 53,
    .cl 0 59, .cl 0 38, .cl 0 42, .cl 0 59, .p1 12, .cl 0 38, .cl 0 42, .cl 0 59, .p1 11, .bk 0,
    .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10,
    .cl 0 5, .cl 0 20, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10, .bk 0, .cl 0 33, .cl 0 47, .cl 0 61,
    .p1 5, .cl 0 47, .cl 0 49, .p1 4, .cl 0 47, .cl 0 58, .cl 0 33, .cl 0 37, .cl 0 47, .cl 0 47,
    .cl 0 49, .cl 0 58, .p1 2, .cl 0 47, .cl 0 49, .cl 0 55, .cl 0 47, .cl 0 58, .cl 0 33,
    .cl 0 43, .cl 0 47, .bk 0, .cl 0 31, .cl 0 33, .cl 0 49, .cl 0 49, .cl 0 56, .cl 0 58, .p1 4,
    .cl 0 49, .cl 0 56, .cl 0 49, .cl 0 56, .cl 0 31, .cl 0 47, .cl 0 49, .cl 0 49, .cl 0 56,
    .cl 0 58, .cl 0 61, .cl 0 49, .cl 0 56, .cl 0 58, .p1 3, .cl 0 49, .cl 0 56, .bk 0, .cl 0 34,
    .cl 0 46, .cl 0 48, .p1 12, .cl 0 34, .cl 0 46, .cl 0 63, .p1 6, .cl 0 34, .cl 0 46, .cl 0 63,
    .p1 13, .cl 0 46, .cl 0 59, .cl 0 34, .cl 0 46, .cl 0 59, .cl 0 63, .cl 0 34, .cl 0 63,
    .cl 0 46, .cl 0 59, .cl 0 46, .cl 0 59, .bk 0, .cl 0 48, .cl 0 57, .cl 0 59, .p1 12, .cl 0 48,
    .cl 0 57, .cl 0 48, .cl 0 57, .cl 0 32, .cl 0 38, .cl 0 48, .cl 0 32, .cl 0 48, .cl 0 57,
    .cl 0 59, .p1 12, .cl 0 48, .cl 0 63, .p1 3, .cl 0 48, .cl 0 57, .cl 0 32, .cl 0 42, .cl 0 48,
    .bk 0, .cl 0 5, .cl 0 15, .cl 0 5, .p1 11, .cl 0 5, .cl 0 15, .cl 0 5, .cl 0 15, .cl 0 5,
    .cl 0 15, .cl 0 5, .cl 0 15, .cl 0 5, .cl 0 15, .cl 0 5, .p1 3, .bk 0, .cl 0 32, .cl 0 46,
    .p1 3, .cl 0 32, .cl 0 46, .cl 0 47, .cl 0 32, .cl 0 48, .cl 0 57, .cl 0 32, .cl 0 48,
    .cl 0 57, .cl 0 32, .cl 0 34, .cl 0 41, .cl 0 32, .cl 0 34, .p1 4, .cl 0 32, .cl 0 48,
    .cl 0 57, .cl 0 32, .cl 0 48, .cl 0 57, .p1 1, .bk 0, .cl 0 34, .cl 0 46, .cl 0 48, .p1 5,
    .cl 0 34, .cl 0 39, .cl 0 42, .cl 0 34, .cl 0 39, .p1 11, .cl 0 34, .cl 0 39, .cl 0 40,
    .cl 0 42, .cl 0 34, .cl 0 57, .p1 9, .cl 0 34, .cl 0 41, .p1 3, .cl 0 34, .cl 0 39, .cl 0 40,
    .cl 0 34, .cl 0 46, .cl 0 59, .bk 0, .cl 0 31, .cl 0 49, .cl 0 56, .p1 2, .cl 0 31, .cl 0 36,
    .cl 0 40, .cl 0 42, .p1 4, .cl 0 31, .cl 0 36, .cl 0 40, .cl 0 31, .cl 0 36, .cl 0 40,
    .cl 0 43, .cl 0 31, .cl 0 49, .cl 0 56, .cl 0 31, .cl 0 44, .p1 3, .cl 0 31, .cl 0 36, .p1 11,
    .cl 0 31, .cl 0 49, .cl 0 56, .bk 0, .cl 0 33, .cl 0 47, .cl 0 58, .p1 2, .cl 0 33, .cl 0 47,
    .cl 0 49, .p1 8, .cl 0 33, .cl 0 47, .cl 0 58, .cl 0 33, .cl 0 47, .cl 0 58, .cl 0 33,
    .cl 0 49, .p1 3, .cl 0 33, .cl 0 49, .cl 0 57, .p1 5, .cl 0 33, .cl 0 47, .cl 0 58, .cl 0 33,
    .cl 0 47, .cl 0 58, .p1 2, .bk 0, .cl 0 10, .cl 0 15, .cl 0 10, .cl 0 20, .cl 0 10, .cl 0 15,
    .cl 0 10, .cl 0 15, .cl 0 10, .cl 0 15, .cl 0 10, .cl 0 15, .cl 0 10, .cl 0 15, .cl 0 10,
    .cl 0 15, .bk 0, .cl 0 42, .cl 0 48, .cl 0 61, .p1 6, .cl 0 42, .cl 0 63, .cl 0 38, .cl 0 41,
    .cl 0 42, .cl 0 42, .cl 0 48, .p1 3, .cl 0 38, .cl 0 42, .cl 0 48, .p1 13, .cl 0 38, .cl 0 42,
    .cl 0 48, .cl 0 59, .p1 3, .cl 0 38, .cl 0 39, .cl 0 42, .cl 0 42, .cl 0 63, .cl 0 64,
    .cl 0 65, .p1 12, .bk 0, .cl 0 44, .cl 0 61, .cl 0 44, .cl 0 61, .cl 0 62, .p1 3, .cl 0 36,
    .cl 0 58, .p1 3, .cl 0 44, .cl 0 61, .cl 0 44, .cl 0 61, .cl 0 36, .cl 0 44, .cl 0 49, .p1 14,
    .cl 0 44, .cl 0 61, .cl 0 62, .p1 8, .cl 0 44, .cl 0 61, .cl 0 68, .p1 4, .bk 0, .cl 0 41,
    .cl 0 64, .cl 0 39, .cl 0 41, .cl 0 66, .cl 0 41, .cl 0 42, .cl 0 48, .cl 0 41, .cl 0 42,
    .p1 5, .cl 0 39, .cl 0 41, .cl 0 42, .cl 0 57, .p1 3, .cl 0 39, .cl 0 41, .cl 0 46, .p1 13,
    .cl 0 39, .cl 0 57, .p1 3, .cl 0 41, .cl 0 42, .cl 0 43, .p1 4, .bk 0, .cl 0 37, .cl 0 43,
    .cl 0 47, .p1 14, .cl 0 43, .cl 0 62, .cl 0 37, .cl 0 43, .cl 0 68, .cl 0 43, .cl 0 47, .p1 3,
    .cl 0 43, .cl 0 47, .cl 0 48, .cl 0 37, .cl 0 43, .cl 0 47, .cl 0 56, .p1 3, .cl 0 37,
    .cl 0 43, .cl 0 44, .p1 8, .cl 0 37, .cl 0 43, .cl 0 62, .cl 0 68]

private theorem cdOK327 : CdOK ⟨3, 0, 2, 7⟩ tab32 cd327 where
  size := by decide +kernel
  rep := by decide +kernel
  orb := by decide +kernel
  gp := by decide +kernel
  nu := by decide +kernel
  al := by decide +kernel
  be := by decide +kernel
  m := by decide +kernel

private theorem run327 : run cd327 3740 [(z16, z16)] cert327 = true := by
  decide +kernel

private theorem case327 :
    (tablesOKb ⟨3, 0, 2, 7⟩ (orbitData ⟨3, 0, 2, 7⟩) && g8b ⟨3, 0, 2, 7⟩ &&
      search ⟨3, 0, 2, 7⟩ (orbitData ⟨3, 0, 2, 7⟩) 17
        (Array.replicate (orbitData ⟨3, 0, 2, 7⟩).reps.size none)) = true := by
  rw [orbitData_congr (P := ⟨3, 0, 2, 7⟩) (Q := ⟨3, 0, 2, 3⟩) rfl, orbitData32]
  refine search_case ?_ ?_ cdOK327 run327
  · rw [tablesOKb_congr (P := ⟨3, 0, 2, 7⟩) (Q := ⟨3, 0, 2, 3⟩) rfl]
    exact tablesOKb32
  · rw [g8b_congr (P := ⟨3, 0, 2, 7⟩) (Q := ⟨3, 0, 2, 3⟩) rfl]
    exact g8b32

private def tab33 : Tables where
  lookup := #[
    none, some (0, 0), some (0, 6), some (0, 2), some (0, 4), some (0, 7), some (1, 0),
    some (1, 7), some (2, 0), some (2, 5), some (0, 5), some (2, 6), some (1, 6), some (2, 3),
    some (1, 5), some (0, 1), some (1, 1), some (2, 7), some (1, 2), some (2, 2), some (0, 3),
    some (2, 1), some (2, 4), some (1, 3), some (1, 4), some (3, 0), some (4, 0), some (5, 0),
    some (5, 4), some (4, 4), some (6, 0), some (7, 0), some (8, 0), some (9, 0), some (10, 0),
    some (11, 0), some (12, 0), some (13, 0), some (14, 0), some (15, 0), some (11, 4),
    some (15, 4), some (14, 4), some (13, 4), some (12, 4), some (6, 4), some (10, 4), some (9, 4),
    some (8, 4), some (7, 4), some (3, 3), some (11, 3), some (6, 7), some (6, 3), some (11, 7),
    some (4, 7), some (15, 3), some (7, 7), some (10, 3), some (12, 7), some (5, 7), some (14, 3),
    some (8, 7), some (9, 3), some (13, 7), some (5, 3), some (13, 3), some (9, 7), some (8, 3),
    some (14, 7), some (4, 3), some (12, 3), some (10, 7), some (7, 3), some (15, 7), some (3, 1),
    some (6, 1), some (11, 1), some (11, 5), some (6, 5), some (5, 1), some (8, 1), some (13, 1),
    some (14, 5), some (9, 5), some (4, 5), some (10, 1), some (15, 1), some (12, 5), some (7, 5),
    some (4, 1), some (7, 1), some (12, 1), some (15, 5), some (10, 5), some (5, 5), some (9, 1),
    some (14, 1), some (13, 5), some (8, 5), some (3, 2), some (5, 2), some (4, 6), some (4, 2),
    some (5, 6), some (11, 2), some (13, 2), some (15, 2), some (12, 2), some (14, 2), some (6, 6),
    some (9, 6), some (7, 6), some (10, 6), some (8, 6), some (6, 2), some (8, 2), some (10, 2),
    some (7, 2), some (9, 2), some (11, 6), some (14, 6), some (12, 6), some (15, 6), some (13, 6)]
  reps := #[
    (0, 0, 1), (0, 1, 1), (0, 1, 3), (1, 0, 0), (1, 0, 1), (1, 0, 2), (1, 1, 0), (1, 1, 1),
    (1, 1, 2), (1, 1, 3), (1, 1, 4), (1, 2, 0), (1, 2, 1), (1, 2, 2), (1, 2, 3), (1, 2, 4)]

private def orb33 : ℕ := pack [
    0, 0, 6, 2, 4, 7, 8, 15, 16, 21, 5, 22, 14, 19, 13, 1, 9, 23, 10, 18, 3, 17, 20, 11, 12, 24,
    32, 40, 44, 36, 48, 56, 64, 72, 80, 88, 96, 104, 112, 120, 92, 124, 116, 108, 100, 52, 84, 76,
    68, 60, 27, 91, 55, 51, 95, 39, 123, 63, 83, 103, 47, 115, 71, 75, 111, 43, 107, 79, 67, 119,
    35, 99, 87, 59, 127, 25, 49, 89, 93, 53, 41, 65, 105, 117, 77, 37, 81, 121, 101, 61, 33, 57,
    97, 125, 85, 45, 73, 113, 109, 69, 26, 42, 38, 34, 46, 90, 106, 122, 98, 114, 54, 78, 62, 86,
    70, 50, 66, 82, 58, 74, 94, 118, 102, 126, 110]

private def rep33 : ℕ := pack [
    1, 6, 8, 25, 26, 27, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39]

private def gp33 : ℕ := pack [
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25,
    26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49,
    50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73,
    74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97,
    98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116,
    117, 118, 119, 120, 121, 122, 123, 124, 0, 15, 5, 20, 10, 1, 16, 6, 21, 11, 2, 17, 7, 22, 12,
    3, 18, 8, 23, 13, 4, 19, 9, 24, 14, 75, 90, 80, 95, 85, 76, 91, 81, 96, 86, 77, 92, 82, 97, 87,
    78, 93, 83, 98, 88, 79, 94, 84, 99, 89, 25, 40, 30, 45, 35, 26, 41, 31, 46, 36, 27, 42, 32, 47,
    37, 28, 43, 33, 48, 38, 29, 44, 34, 49, 39, 100, 115, 105, 120, 110, 101, 116, 106, 121, 111,
    102, 117, 107, 122, 112, 103, 118, 108, 123, 113, 104, 119, 109, 124, 114, 50, 65, 55, 70, 60,
    51, 66, 56, 71, 61, 52, 67, 57, 72, 62, 53, 68, 58, 73, 63, 54, 69, 59, 74, 64, 0, 3, 1, 4, 2,
    15, 18, 16, 19, 17, 5, 8, 6, 9, 7, 20, 23, 21, 24, 22, 10, 13, 11, 14, 12, 100, 103, 101, 104,
    102, 115, 118, 116, 119, 117, 105, 108, 106, 109, 107, 120, 123, 121, 124, 122, 110, 113, 111,
    114, 112, 75, 78, 76, 79, 77, 90, 93, 91, 94, 92, 80, 83, 81, 84, 82, 95, 98, 96, 99, 97, 85,
    88, 86, 89, 87, 50, 53, 51, 54, 52, 65, 68, 66, 69, 67, 55, 58, 56, 59, 57, 70, 73, 71, 74, 72,
    60, 63, 61, 64, 62, 25, 28, 26, 29, 27, 40, 43, 41, 44, 42, 30, 33, 31, 34, 32, 45, 48, 46, 49,
    47, 35, 38, 36, 39, 37, 0, 20, 15, 10, 5, 3, 23, 18, 13, 8, 1, 21, 16, 11, 6, 4, 24, 19, 14, 9,
    2, 22, 17, 12, 7, 50, 70, 65, 60, 55, 53, 73, 68, 63, 58, 51, 71, 66, 61, 56, 54, 74, 69, 64,
    59, 52, 72, 67, 62, 57, 100, 120, 115, 110, 105, 103, 123, 118, 113, 108, 101, 121, 116, 111,
    106, 104, 124, 119, 114, 109, 102, 122, 117, 112, 107, 25, 45, 40, 35, 30, 28, 48, 43, 38, 33,
    26, 46, 41, 36, 31, 29, 49, 44, 39, 34, 27, 47, 42, 37, 32, 75, 95, 90, 85, 80, 78, 98, 93, 88,
    83, 76, 96, 91, 86, 81, 79, 99, 94, 89, 84, 77, 97, 92, 87, 82, 0, 4, 3, 2, 1, 20, 24, 23, 22,
    21, 15, 19, 18, 17, 16, 10, 14, 13, 12, 11, 5, 9, 8, 7, 6, 25, 29, 28, 27, 26, 45, 49, 48, 47,
    46, 40, 44, 43, 42, 41, 35, 39, 38, 37, 36, 30, 34, 33, 32, 31, 50, 54, 53, 52, 51, 70, 74, 73,
    72, 71, 65, 69, 68, 67, 66, 60, 64, 63, 62, 61, 55, 59, 58, 57, 56, 75, 79, 78, 77, 76, 95, 99,
    98, 97, 96, 90, 94, 93, 92, 91, 85, 89, 88, 87, 86, 80, 84, 83, 82, 81, 100, 104, 103, 102,
    101, 120, 124, 123, 122, 121, 115, 119, 118, 117, 116, 110, 114, 113, 112, 111, 105, 109, 108,
    107, 106, 0, 10, 20, 5, 15, 4, 14, 24, 9, 19, 3, 13, 23, 8, 18, 2, 12, 22, 7, 17, 1, 11, 21, 6,
    16, 75, 85, 95, 80, 90, 79, 89, 99, 84, 94, 78, 88, 98, 83, 93, 77, 87, 97, 82, 92, 76, 86, 96,
    81, 91, 25, 35, 45, 30, 40, 29, 39, 49, 34, 44, 28, 38, 48, 33, 43, 27, 37, 47, 32, 42, 26, 36,
    46, 31, 41, 100, 110, 120, 105, 115, 104, 114, 124, 109, 119, 103, 113, 123, 108, 118, 102,
    112, 122, 107, 117, 101, 111, 121, 106, 116, 50, 60, 70, 55, 65, 54, 64, 74, 59, 69, 53, 63,
    73, 58, 68, 52, 62, 72, 57, 67, 51, 61, 71, 56, 66, 0, 2, 4, 1, 3, 10, 12, 14, 11, 13, 20, 22,
    24, 21, 23, 5, 7, 9, 6, 8, 15, 17, 19, 16, 18, 100, 102, 104, 101, 103, 110, 112, 114, 111,
    113, 120, 122, 124, 121, 123, 105, 107, 109, 106, 108, 115, 117, 119, 116, 118, 75, 77, 79, 76,
    78, 85, 87, 89, 86, 88, 95, 97, 99, 96, 98, 80, 82, 84, 81, 83, 90, 92, 94, 91, 93, 50, 52, 54,
    51, 53, 60, 62, 64, 61, 63, 70, 72, 74, 71, 73, 55, 57, 59, 56, 58, 65, 67, 69, 66, 68, 25, 27,
    29, 26, 28, 35, 37, 39, 36, 38, 45, 47, 49, 46, 48, 30, 32, 34, 31, 33, 40, 42, 44, 41, 43, 0,
    5, 10, 15, 20, 2, 7, 12, 17, 22, 4, 9, 14, 19, 24, 1, 6, 11, 16, 21, 3, 8, 13, 18, 23, 50, 55,
    60, 65, 70, 52, 57, 62, 67, 72, 54, 59, 64, 69, 74, 51, 56, 61, 66, 71, 53, 58, 63, 68, 73,
    100, 105, 110, 115, 120, 102, 107, 112, 117, 122, 104, 109, 114, 119, 124, 101, 106, 111, 116,
    121, 103, 108, 113, 118, 123, 25, 30, 35, 40, 45, 27, 32, 37, 42, 47, 29, 34, 39, 44, 49, 26,
    31, 36, 41, 46, 28, 33, 38, 43, 48, 75, 80, 85, 90, 95, 77, 82, 87, 92, 97, 79, 84, 89, 94, 99,
    76, 81, 86, 91, 96, 78, 83, 88, 93, 98]

private theorem orbitData33 : orbitData ⟨3, 0, 3, 3⟩ = tab33 := by
  have h1 : (orbitData ⟨3, 0, 3, 3⟩).lookup = tab33.lookup := by
    decide +kernel
  have h2 : (orbitData ⟨3, 0, 3, 3⟩).reps = tab33.reps := by
    decide +kernel
  exact tables_ext h1 h2

private theorem tablesOKb33 : tablesOKb ⟨3, 0, 3, 3⟩ tab33 = true := by
  decide +kernel

private theorem g8b33 : g8b ⟨3, 0, 3, 3⟩ = true := by
  decide +kernel

private def cd333 : Cd := ⟨3, 0, 3, 3, orb33, rep33, gp33⟩

private def cert333 : List Op := [
    .bv 0, .bk 0, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .bv 1, .p1 1, .p1 1, .p1 1, .p1 1, .p1 1,
    .cl 0 5, .p1 2, .p1 1, .cl 0 5, .cl 0 5, .p1 1, .cl 0 5, .cl 0 5, .cl 0 6, .cl 0 5, .p1 1,
    .p1 1, .p1 1, .bk 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1,
    .cl 0 5, .p1 2, .cl 0 5, .p1 1, .cl 0 5, .cl 0 5, .p1 1, .cl 0 5, .p1 2, .p1 1, .cl 0 5, .p1 2,
    .cl 0 6, .cl 0 5, .p1 2, .cl 0 6, .p1 3, .cl 0 5, .cl 0 7, .p1 3, .cl 0 5, .cl 0 6, .cl 0 8,
    .cl 0 5, .cl 0 6, .cl 0 8, .cl 0 5, .cl 0 6, .cl 0 8, .cl 0 5, .cl 0 6, .cl 0 8, .cl 0 6,
    .p1 12, .cl 0 5, .cl 0 6, .cl 0 8, .cl 0 6, .p1 14, .cl 0 5, .cl 0 6, .p1 15, .cl 0 5, .cl 0 6,
    .cl 0 7, .p1 10, .cl 0 5, .cl 0 7, .cl 0 5, .cl 0 6, .cl 0 8, .cl 0 5, .cl 0 6, .cl 0 7,
    .cl 0 5, .cl 0 7, .cl 0 5, .cl 0 7, .p1 15, .cl 0 6, .p1 3, .cl 0 5, .cl 0 6, .cl 0 8, .cl 0 5,
    .cl 0 6, .cl 0 8, .cl 0 5, .cl 0 6, .cl 0 8, .cl 0 5, .cl 0 6, .cl 0 8, .p1 1, .cl 0 5, .p1 2,
    .cl 0 6, .cl 0 5, .p1 2, .cl 0 6, .p1 3, .cl 0 5, .cl 0 7, .p1 3, .cl 0 5, .cl 0 6, .cl 0 8,
    .cl 0 5, .cl 0 6, .cl 0 8, .cl 0 5, .cl 0 6, .cl 0 8, .cl 0 5, .cl 0 6, .cl 0 8, .cl 0 6,
    .p1 14, .cl 0 5, .cl 0 6, .cl 0 8, .cl 0 6, .p1 9, .cl 0 5, .cl 0 6, .p1 13, .cl 0 5, .cl 0 6,
    .cl 0 7, .p1 12, .cl 0 5, .cl 0 7, .cl 0 5, .cl 0 6, .cl 0 8, .cl 0 5, .cl 0 6, .cl 0 7,
    .cl 0 5, .cl 0 7, .cl 0 5, .cl 0 7, .p1 13, .cl 0 6, .p1 3, .cl 0 5, .cl 0 6, .cl 0 8, .cl 0 5,
    .cl 0 6, .cl 0 8, .cl 0 5, .cl 0 6, .cl 0 8, .cl 0 5, .cl 0 6, .cl 0 8, .p1 1, .cl 0 5, .p1 2,
    .cl 0 6, .cl 0 5, .p1 2, .cl 0 6, .p1 3, .cl 0 5, .cl 0 7, .p1 3, .cl 0 5, .cl 0 6, .cl 0 8,
    .cl 0 5, .cl 0 6, .cl 0 8, .cl 0 5, .cl 0 6, .cl 0 8, .cl 0 5, .cl 0 6, .cl 0 8, .cl 0 6,
    .p1 10, .cl 0 5, .cl 0 6, .cl 0 8, .cl 0 6, .p1 12, .cl 0 5, .cl 0 6, .p1 7, .cl 0 5, .cl 0 6,
    .cl 0 7, .p1 9, .cl 0 5, .cl 0 7, .cl 0 5, .cl 0 6, .cl 0 8, .cl 0 5, .cl 0 6, .cl 0 7,
    .cl 0 5, .cl 0 7, .cl 0 5, .cl 0 7, .p1 7, .cl 0 6, .p1 3, .cl 0 5, .cl 0 6, .cl 0 8, .cl 0 5,
    .cl 0 6, .cl 0 8, .cl 0 5, .cl 0 6, .cl 0 8, .cl 0 5, .cl 0 6, .cl 0 8, .p1 1, .cl 0 5, .p1 2,
    .cl 0 6, .cl 0 5, .p1 2, .cl 0 6, .p1 3, .cl 0 5, .cl 0 7, .p1 3, .cl 0 5, .cl 0 6, .cl 0 8,
    .cl 0 5, .cl 0 6, .cl 0 8, .cl 0 5, .cl 0 6, .cl 0 8, .cl 0 5, .cl 0 6, .cl 0 8, .cl 0 6,
    .p1 9, .cl 0 5, .cl 0 6, .cl 0 8, .cl 0 6, .p1 10, .cl 0 5, .cl 0 6, .p1 8, .cl 0 5, .cl 0 6,
    .cl 0 7, .p1 14, .cl 0 5, .cl 0 7, .cl 0 5, .cl 0 6, .cl 0 8, .cl 0 5, .cl 0 6, .cl 0 7,
    .cl 0 5, .cl 0 7, .cl 0 5, .cl 0 7, .p1 8, .cl 0 6, .p1 3, .cl 0 5, .cl 0 6, .cl 0 8, .cl 0 5,
    .cl 0 6, .cl 0 8, .cl 0 5, .cl 0 6, .cl 0 8, .cl 0 5, .cl 0 6, .cl 0 8, .cl 0 1, .cl 0 1,
    .cl 0 1, .bk 0, .cl 0 1, .cl 0 1, .bv 1, .p1 1, .p1 1, .p1 1, .p1 1, .p1 1, .cl 0 5, .cl 0 6,
    .p1 1, .cl 0 5, .bk 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1,
    .p1 1, .cl 0 5, .cl 0 5, .p1 2, .cl 0 5, .p1 1, .p1 1, .p1 1, .cl 0 5, .cl 0 5, .p1 2, .cl 0 5,
    .p1 1, .cl 0 5, .cl 0 5, .p1 1, .cl 0 5, .p1 2, .p1 1, .cl 0 5, .cl 0 8, .p1 6, .cl 0 5,
    .cl 0 6, .cl 0 5, .cl 0 7, .cl 0 8, .cl 0 5, .cl 0 6, .p1 3, .cl 0 5, .cl 0 8, .p1 15, .cl 0 5,
    .cl 0 8, .p1 11, .cl 0 5, .cl 0 8, .p1 12, .cl 0 5, .cl 0 8, .p1 13, .cl 0 5, .cl 0 8, .p1 14,
    .cl 0 5, .p1 2, .cl 0 5, .cl 0 8, .p1 11, .cl 0 5, .cl 0 6, .cl 0 5, .cl 0 8, .cl 0 5, .cl 0 8,
    .p1 13, .cl 0 5, .cl 0 7, .cl 0 5, .cl 0 8, .p1 6, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 5, .cl 0 8,
    .p1 9, .cl 0 5, .cl 0 8, .p1 8, .cl 0 5, .p1 2, .cl 0 5, .cl 0 8, .p1 3, .cl 0 5, .cl 0 6,
    .p1 8, .cl 0 5, .cl 0 8, .cl 0 5, .cl 0 6, .p1 3, .p1 1, .cl 0 5, .cl 0 8, .p1 4, .cl 0 5,
    .cl 0 6, .cl 0 5, .cl 0 7, .cl 0 8, .cl 0 5, .cl 0 6, .p1 3, .cl 0 5, .cl 0 8, .p1 13, .cl 0 5,
    .cl 0 8, .p1 5, .cl 0 5, .cl 0 8, .p1 14, .cl 0 5, .cl 0 8, .p1 8, .cl 0 5, .cl 0 8, .p1 9,
    .cl 0 5, .p1 2, .cl 0 5, .cl 0 8, .p1 5, .cl 0 5, .cl 0 6, .cl 0 5, .cl 0 8, .cl 0 5, .cl 0 8,
    .p1 8, .cl 0 5, .cl 0 7, .cl 0 5, .cl 0 8, .p1 4, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 5, .cl 0 8,
    .p1 10, .cl 0 5, .cl 0 8, .p1 7, .cl 0 5, .p1 2, .cl 0 5, .cl 0 8, .p1 3, .cl 0 5, .cl 0 6,
    .p1 7, .cl 0 5, .cl 0 8, .cl 0 5, .cl 0 6, .p1 3, .p1 1, .cl 0 5, .cl 0 8, .p1 5, .cl 0 5,
    .cl 0 6, .cl 0 5, .cl 0 7, .cl 0 8, .cl 0 5, .cl 0 6, .p1 3, .cl 0 5, .cl 0 8, .p1 7, .cl 0 5,
    .cl 0 8, .p1 4, .cl 0 5, .cl 0 8, .p1 10, .cl 0 5, .cl 0 8, .p1 15, .cl 0 5, .cl 0 8, .p1 12,
    .cl 0 5, .p1 2, .cl 0 5, .cl 0 8, .p1 4, .cl 0 5, .cl 0 6, .cl 0 5, .cl 0 8, .cl 0 5, .cl 0 8,
    .p1 15, .cl 0 5, .cl 0 7, .cl 0 5, .cl 0 8, .p1 5, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 5, .cl 0 8,
    .p1 14, .cl 0 5, .cl 0 8, .p1 13, .cl 0 5, .p1 2, .cl 0 5, .cl 0 8, .p1 3, .cl 0 5, .cl 0 6,
    .p1 13, .cl 0 5, .cl 0 8, .cl 0 5, .cl 0 6, .p1 3, .p1 1, .cl 0 5, .cl 0 8, .p1 11, .cl 0 5,
    .cl 0 6, .cl 0 5, .cl 0 7, .cl 0 8, .cl 0 5, .cl 0 6, .p1 3, .cl 0 5, .cl 0 8, .p1 8, .cl 0 5,
    .cl 0 8, .p1 6, .cl 0 5, .cl 0 8, .p1 9, .cl 0 5, .cl 0 8, .p1 7, .cl 0 5, .cl 0 8, .p1 10,
    .cl 0 5, .p1 2, .cl 0 5, .cl 0 8, .p1 6, .cl 0 5, .cl 0 6, .cl 0 5, .cl 0 8, .cl 0 5, .cl 0 8,
    .p1 7, .cl 0 5, .cl 0 7, .cl 0 5, .cl 0 8, .p1 11, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 5, .cl 0 8,
    .p1 12, .cl 0 5, .cl 0 8, .p1 15, .cl 0 5, .p1 2, .cl 0 5, .cl 0 8, .p1 3, .cl 0 5, .cl 0 6,
    .p1 15, .cl 0 5, .cl 0 8, .cl 0 5, .cl 0 6, .p1 3, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .bk 0, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .bv 1, .p1 1, .p1 1, .p1 1, .p1 1,
    .p1 1, .cl 0 5, .cl 0 6, .p1 1, .cl 0 5, .cl 0 5, .p1 1, .cl 0 5, .cl 0 5, .p1 2, .cl 0 5,
    .p1 1, .p1 1, .p1 1, .cl 0 5, .cl 0 5, .p1 2, .cl 0 5, .p1 1, .bk 1, .cl 1 1, .cl 1 1, .cl 1 1,
    .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 0 5, .p1 1, .cl 0 5, .p1 2, .p1 1, .cl 0 5,
    .cl 0 6, .cl 0 5, .cl 0 6, .cl 0 5, .p1 2, .cl 0 5, .p1 2, .cl 0 7, .p1 3, .cl 0 5, .cl 0 7,
    .p1 4, .cl 0 5, .cl 0 7, .p1 5, .cl 0 5, .cl 0 6, .p1 3, .cl 0 5, .cl 0 6, .cl 0 7, .cl 0 5,
    .cl 0 7, .p1 6, .cl 0 5, .cl 0 7, .p1 7, .cl 0 5, .cl 0 7, .p1 8, .cl 0 5, .cl 0 7, .p1 9,
    .cl 0 5, .cl 0 7, .p1 10, .cl 0 7, .cl 0 5, .cl 0 6, .p1 14, .cl 0 5, .cl 0 6, .cl 0 7,
    .cl 0 5, .cl 0 6, .p1 12, .cl 0 5, .cl 0 6, .p1 11, .cl 0 5, .cl 0 7, .p1 11, .cl 0 5, .cl 0 7,
    .p1 15, .cl 0 5, .cl 0 7, .p1 14, .cl 0 5, .cl 0 7, .p1 13, .cl 0 5, .cl 0 7, .p1 12, .p1 1,
    .cl 0 5, .cl 0 6, .cl 0 5, .cl 0 6, .cl 0 5, .p1 2, .cl 0 5, .p1 2, .cl 0 7, .p1 3, .cl 0 5,
    .cl 0 7, .p1 11, .cl 0 5, .cl 0 7, .p1 6, .cl 0 5, .cl 0 6, .p1 3, .cl 0 5, .cl 0 6, .cl 0 7,
    .cl 0 5, .cl 0 7, .p1 4, .cl 0 5, .cl 0 7, .p1 15, .cl 0 5, .cl 0 7, .p1 7, .cl 0 5, .cl 0 7,
    .p1 10, .cl 0 5, .cl 0 7, .p1 12, .cl 0 7, .cl 0 5, .cl 0 6, .p1 9, .cl 0 5, .cl 0 6, .cl 0 7,
    .cl 0 5, .cl 0 6, .p1 14, .cl 0 5, .cl 0 6, .p1 5, .cl 0 5, .cl 0 7, .p1 5, .cl 0 5, .cl 0 7,
    .p1 13, .cl 0 5, .cl 0 7, .p1 9, .cl 0 5, .cl 0 7, .p1 8, .cl 0 5, .cl 0 7, .p1 14, .p1 1,
    .cl 0 5, .cl 0 6, .cl 0 5, .cl 0 6, .cl 0 5, .p1 2, .cl 0 5, .p1 2, .cl 0 7, .p1 3, .cl 0 5,
    .cl 0 7, .p1 6, .cl 0 5, .cl 0 7, .p1 11, .cl 0 5, .cl 0 6, .p1 3, .cl 0 5, .cl 0 6, .cl 0 7,
    .cl 0 5, .cl 0 7, .p1 5, .cl 0 5, .cl 0 7, .p1 8, .cl 0 5, .cl 0 7, .p1 13, .cl 0 5, .cl 0 7,
    .p1 14, .cl 0 5, .cl 0 7, .p1 9, .cl 0 7, .cl 0 5, .cl 0 6, .p1 12, .cl 0 5, .cl 0 6, .cl 0 7,
    .cl 0 5, .cl 0 6, .p1 10, .cl 0 5, .cl 0 6, .p1 4, .cl 0 5, .cl 0 7, .p1 4, .cl 0 5, .cl 0 7,
    .p1 7, .cl 0 5, .cl 0 7, .p1 12, .cl 0 5, .cl 0 7, .p1 15, .cl 0 5, .cl 0 7, .p1 10, .p1 1,
    .cl 0 5, .cl 0 6, .cl 0 5, .cl 0 6, .cl 0 5, .p1 2, .cl 0 5, .p1 2, .cl 0 7, .p1 3, .cl 0 5,
    .cl 0 7, .p1 5, .cl 0 5, .cl 0 7, .p1 4, .cl 0 5, .cl 0 6, .p1 3, .cl 0 5, .cl 0 6, .cl 0 7,
    .cl 0 5, .cl 0 7, .p1 11, .cl 0 5, .cl 0 7, .p1 13, .cl 0 5, .cl 0 7, .p1 15, .cl 0 5, .cl 0 7,
    .p1 12, .cl 0 5, .cl 0 7, .p1 14, .cl 0 7, .cl 0 5, .cl 0 6, .p1 10, .cl 0 5, .cl 0 6, .cl 0 7,
    .cl 0 5, .cl 0 6, .p1 9, .cl 0 5, .cl 0 6, .p1 6, .cl 0 5, .cl 0 7, .p1 6, .cl 0 5, .cl 0 7,
    .p1 8, .cl 0 5, .cl 0 7, .p1 10, .cl 0 5, .cl 0 7, .p1 7, .cl 0 5, .cl 0 7, .p1 9, .cl 0 1,
    .bk 0, .bv 1, .p1 1, .p1 1, .p1 1, .p1 1, .p1 1, .cl 0 5, .p1 2, .p1 1, .cl 0 5, .cl 0 5,
    .p1 1, .cl 0 5, .cl 0 5, .cl 0 6, .bk 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1,
    .cl 1 1, .cl 1 1, .p1 1, .p1 1, .p1 1, .cl 0 5, .cl 0 5, .p1 2, .cl 0 5, .p1 1, .cl 0 5,
    .cl 0 5, .p1 1, .cl 0 5, .p1 2, .p1 1, .cl 0 5, .cl 0 6, .p1 5, .cl 0 6, .cl 0 5, .cl 0 6,
    .p1 4, .cl 0 6, .p1 3, .cl 0 5, .cl 0 6, .p1 7, .cl 0 5, .cl 0 6, .p1 8, .cl 0 5, .cl 0 6,
    .p1 9, .cl 0 5, .cl 0 6, .p1 10, .cl 0 5, .cl 0 6, .p1 6, .cl 0 5, .cl 0 6, .p1 12, .cl 0 5,
    .cl 0 6, .p1 13, .cl 0 5, .cl 0 6, .p1 14, .cl 0 5, .cl 0 6, .p1 15, .cl 0 5, .cl 0 6, .p1 11,
    .cl 0 5, .p1 2, .cl 0 5, .cl 0 6, .p1 14, .cl 0 5, .cl 0 6, .p1 13, .cl 0 5, .cl 0 6, .p1 12,
    .cl 0 5, .cl 0 6, .p1 11, .cl 0 5, .p1 2, .cl 0 5, .cl 0 6, .p1 9, .cl 0 5, .cl 0 6, .cl 0 5,
    .cl 0 6, .p1 7, .cl 0 5, .cl 0 6, .p1 6, .p1 1, .cl 0 5, .cl 0 6, .p1 6, .cl 0 6, .cl 0 5,
    .cl 0 6, .p1 11, .cl 0 6, .p1 3, .cl 0 5, .cl 0 6, .p1 15, .cl 0 5, .cl 0 6, .p1 7, .cl 0 5,
    .cl 0 6, .p1 10, .cl 0 5, .cl 0 6, .p1 12, .cl 0 5, .cl 0 6, .p1 4, .cl 0 5, .cl 0 6, .p1 14,
    .cl 0 5, .cl 0 6, .p1 8, .cl 0 5, .cl 0 6, .p1 9, .cl 0 5, .cl 0 6, .p1 13, .cl 0 5, .cl 0 6,
    .p1 5, .cl 0 5, .p1 2, .cl 0 5, .cl 0 6, .p1 9, .cl 0 5, .cl 0 6, .p1 8, .cl 0 5, .cl 0 6,
    .p1 14, .cl 0 5, .cl 0 6, .p1 5, .cl 0 5, .p1 2, .cl 0 5, .cl 0 6, .p1 10, .cl 0 5, .cl 0 6,
    .cl 0 5, .cl 0 6, .p1 15, .cl 0 5, .cl 0 6, .p1 4, .p1 1, .cl 0 5, .cl 0 6, .p1 11, .cl 0 6,
    .cl 0 5, .cl 0 6, .p1 6, .cl 0 6, .p1 3, .cl 0 5, .cl 0 6, .p1 8, .cl 0 5, .cl 0 6, .p1 13,
    .cl 0 5, .cl 0 6, .p1 14, .cl 0 5, .cl 0 6, .p1 9, .cl 0 5, .cl 0 6, .p1 5, .cl 0 5, .cl 0 6,
    .p1 10, .cl 0 5, .cl 0 6, .p1 15, .cl 0 5, .cl 0 6, .p1 12, .cl 0 5, .cl 0 6, .p1 7, .cl 0 5,
    .cl 0 6, .p1 4, .cl 0 5, .p1 2, .cl 0 5, .cl 0 6, .p1 12, .cl 0 5, .cl 0 6, .p1 15, .cl 0 5,
    .cl 0 6, .p1 10, .cl 0 5, .cl 0 6, .p1 4, .cl 0 5, .p1 2, .cl 0 5, .cl 0 6, .p1 14, .cl 0 5,
    .cl 0 6, .cl 0 5, .cl 0 6, .p1 8, .cl 0 5, .cl 0 6, .p1 5, .p1 1, .cl 0 5, .cl 0 6, .p1 4,
    .cl 0 6, .cl 0 5, .cl 0 6, .p1 5, .cl 0 6, .p1 3, .cl 0 5, .cl 0 6, .p1 13, .cl 0 5, .cl 0 6,
    .p1 15, .cl 0 5, .cl 0 6, .p1 12, .cl 0 5, .cl 0 6, .p1 14, .cl 0 5, .cl 0 6, .p1 11, .cl 0 5,
    .cl 0 6, .p1 9, .cl 0 5, .cl 0 6, .p1 7, .cl 0 5, .cl 0 6, .p1 10, .cl 0 5, .cl 0 6, .p1 8,
    .cl 0 5, .cl 0 6, .p1 6, .cl 0 5, .p1 2, .cl 0 5, .cl 0 6, .p1 10, .cl 0 5, .cl 0 6, .p1 7,
    .cl 0 5, .cl 0 6, .p1 9, .cl 0 5, .cl 0 6, .p1 6, .cl 0 5, .p1 2, .cl 0 5, .cl 0 6, .p1 12,
    .cl 0 5, .cl 0 6, .cl 0 5, .cl 0 6, .p1 13, .cl 0 5, .cl 0 6, .p1 11, .cl 0 2, .cl 0 2,
    .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .p1 0, .bk 0, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .bk 0, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3,
    .cl 0 3, .cl 0 3, .cl 0 3, .bk 0, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 2, .bk 0, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .p1 0, .bk 0, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 4, .cl 0 2, .cl 0 2,
    .bk 0, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .bk 0, .cl 0 2,
    .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .bk 0, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .p1 0, .bk 0, .cl 0 2, .cl 0 4, .cl 0 2,
    .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .bk 0, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2,
    .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .bk 0, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2,
    .cl 0 2, .cl 0 2, .cl 0 2, .bk 0, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .p1 0, .bk 0, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .bk 0, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .bk 0,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .bk 0, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .p1 0, .bk 0, .cl 0 1, .p1 5,
    .cl 0 1, .cl 0 2, .cl 0 1, .p1 3, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2,
    .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .bk 0, .cl 0 1, .cl 0 2, .cl 0 1, .p1 4, .cl 0 1, .cl 0 4,
    .cl 0 1, .p1 4, .cl 0 1, .cl 0 2, .cl 0 1, .p1 4, .cl 0 1, .cl 0 2, .cl 0 1, .p1 4, .bk 0,
    .cl 0 1, .p1 3, .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3,
    .cl 0 1, .cl 0 3, .cl 0 1, .p1 4, .cl 0 1, .cl 0 3, .bk 0, .cl 0 2, .cl 0 3, .cl 0 2, .p1 5,
    .cl 0 2, .cl 0 3, .cl 0 2, .p1 5, .cl 0 2, .cl 0 3, .cl 0 2, .p1 5, .cl 0 2, .cl 0 4, .cl 0 2,
    .p1 5, .bk 0, .cl 0 5, .p1 3, .cl 0 10, .cl 0 5, .p1 3, .cl 0 5, .p1 3, .cl 0 5, .p1 3,
    .cl 0 5, .p1 3, .cl 0 5, .p1 3, .cl 0 5, .p1 3, .bk 0, .cl 0 31, .cl 0 39, .cl 0 31, .cl 0 39,
    .p1 2, .cl 0 31, .cl 0 39, .cl 0 41, .cl 0 31, .cl 0 39, .cl 0 31, .cl 0 39, .cl 0 41,
    .cl 0 31, .cl 0 39, .cl 0 41, .cl 0 31, .cl 0 39, .cl 0 31, .cl 0 39, .bk 0, .cl 0 32,
    .cl 0 49, .cl 0 57, .cl 0 62, .p1 12, .cl 0 32, .cl 0 49, .cl 0 32, .cl 0 49, .cl 0 32,
    .cl 0 49, .cl 0 32, .cl 0 49, .p1 2, .cl 0 32, .cl 0 49, .cl 0 57, .cl 0 60, .cl 0 32,
    .cl 0 49, .cl 0 32, .cl 0 49, .cl 0 57, .p1 15, .bk 0, .cl 0 33, .cl 0 46, .p1 1, .cl 0 33,
    .cl 0 46, .cl 0 33, .cl 0 34, .p1 1, .cl 0 33, .cl 0 46, .cl 0 33, .cl 0 58, .cl 0 59, .p1 13,
    .cl 0 33, .cl 0 34, .cl 0 45, .cl 0 33, .cl 0 34, .cl 0 35, .cl 0 33, .cl 0 34, .cl 0 36,
    .bk 0, .cl 0 34, .cl 0 36, .cl 0 39, .cl 0 34, .cl 0 36, .p1 1, .cl 0 34, .cl 0 36, .cl 0 34,
    .cl 0 36, .cl 0 34, .cl 0 36, .cl 0 34, .cl 0 36, .cl 0 44, .cl 0 34, .cl 0 36, .cl 0 44,
    .cl 0 34, .cl 0 36, .bk 0, .cl 0 10, .p1 3, .cl 0 10, .p1 3, .cl 0 10, .p1 3, .cl 0 10, .p1 3,
    .cl 0 10, .p1 3, .cl 0 10, .p1 3, .cl 0 10, .p1 3, .cl 0 20, .bk 0, .cl 0 36, .cl 0 38, .p1 1,
    .cl 0 36, .cl 0 42, .cl 0 36, .cl 0 42, .cl 0 46, .cl 0 36, .cl 0 38, .cl 0 40, .cl 0 36,
    .cl 0 42, .cl 0 36, .cl 0 38, .cl 0 42, .cl 0 36, .cl 0 42, .p1 1, .cl 0 36, .cl 0 42, .bk 0,
    .cl 0 37, .cl 0 48, .cl 0 54, .cl 0 57, .cl 0 37, .cl 0 48, .cl 0 37, .cl 0 48, .cl 0 62,
    .p1 7, .cl 0 37, .cl 0 48, .cl 0 56, .cl 0 37, .cl 0 48, .cl 0 37, .cl 0 48, .cl 0 37,
    .cl 0 48, .cl 0 37, .cl 0 48, .p1 2, .bk 0, .cl 0 38, .cl 0 47, .cl 0 38, .cl 0 47, .cl 0 38,
    .cl 0 47, .cl 0 38, .cl 0 47, .cl 0 59, .cl 0 38, .cl 0 47, .cl 0 54, .cl 0 57, .cl 0 38,
    .cl 0 47, .cl 0 38, .cl 0 47, .cl 0 48, .cl 0 38, .cl 0 47, .p1 1, .bk 0, .cl 0 39, .cl 0 43,
    .cl 0 39, .cl 0 43, .cl 0 39, .cl 0 43, .p1 2, .cl 0 39, .cl 0 43, .cl 0 56, .p1 11, .cl 0 39,
    .cl 0 43, .cl 0 39, .cl 0 43, .cl 0 56, .p1 11, .cl 0 39, .cl 0 43, .cl 0 49, .cl 0 39,
    .cl 0 43, .bk 0, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .bk 0,
    .cl 0 41, .cl 0 43, .p1 2, .cl 0 41, .cl 0 43, .cl 0 48, .cl 0 41, .cl 0 66, .cl 0 68, .p1 10,
    .cl 0 41, .cl 0 74, .p1 11, .cl 0 41, .cl 0 43, .cl 0 45, .cl 0 41, .cl 0 64, .p1 3, .cl 0 41,
    .cl 0 64, .p1 3, .cl 0 41, .cl 0 43, .cl 0 51, .p1 3, .bk 0, .cl 0 42, .cl 0 47, .cl 0 60,
    .cl 0 42, .cl 0 47, .cl 0 55, .cl 0 42, .cl 0 47, .cl 0 58, .p1 6, .cl 0 42, .cl 0 61, .p1 5,
    .cl 0 42, .cl 0 61, .p1 5, .cl 0 42, .cl 0 47, .p1 1, .cl 0 42, .cl 0 63, .p1 3, .cl 0 42,
    .cl 0 61, .cl 0 71, .bk 0, .cl 0 43, .cl 0 64, .p1 5, .cl 0 43, .cl 0 48, .cl 0 55, .cl 0 43,
    .cl 0 62, .p1 3, .cl 0 43, .cl 0 62, .p1 3, .cl 0 43, .cl 0 48, .cl 0 60, .cl 0 43, .cl 0 48,
    .p1 2, .cl 0 43, .cl 0 48, .cl 0 49, .cl 0 43, .cl 0 64, .cl 0 74, .bk 0, .cl 0 44, .cl 0 61,
    .p1 3, .cl 0 44, .cl 0 61, .p1 3, .cl 0 44, .cl 0 61, .p1 3, .cl 0 44, .cl 0 71, .p1 11,
    .cl 0 44, .cl 0 69, .cl 0 78, .p1 8, .cl 0 44, .cl 0 61, .p1 3, .cl 0 44, .cl 0 71, .cl 0 72,
    .cl 0 44, .cl 0 71, .cl 0 77, .cl 0 81, .p1 4, .bk 0, .cl 0 15, .cl 0 15, .cl 0 15, .cl 0 15,
    .cl 0 15, .cl 0 15, .cl 0 15, .cl 0 15, .bk 0, .cl 0 46, .cl 0 59, .p1 3, .cl 0 46, .cl 0 58,
    .cl 0 63, .cl 0 46, .cl 0 58, .cl 0 59, .p1 3, .cl 0 46, .cl 0 58, .p1 3, .cl 0 46, .cl 0 59,
    .p1 3, .cl 0 46, .cl 0 58, .p1 4, .cl 0 46, .cl 0 58, .p1 4, .cl 0 46, .cl 0 58, .cl 0 69,
    .p1 11, .bk 0, .cl 0 47, .cl 0 63, .cl 0 72, .cl 0 73, .p1 11, .cl 0 47, .cl 0 63, .cl 0 67,
    .p1 15, .cl 0 47, .cl 0 58, .p1 3, .cl 0 47, .cl 0 58, .p1 3, .cl 0 47, .cl 0 58, .p1 3,
    .cl 0 47, .cl 0 63, .p1 6, .cl 0 47, .cl 0 63, .cl 0 79, .p1 15, .cl 0 47, .cl 0 58, .p1 3,
    .bk 0, .cl 0 48, .cl 0 57, .p1 3, .cl 0 48, .cl 0 49, .cl 0 52, .cl 0 48, .cl 0 49, .p1 2,
    .cl 0 48, .cl 0 49, .cl 0 56, .p1 4, .cl 0 48, .cl 0 62, .cl 0 64, .cl 0 48, .cl 0 62, .p1 6,
    .cl 0 48, .cl 0 49, .cl 0 51, .cl 0 48, .cl 0 57, .p1 3, .bk 0, .cl 0 49, .cl 0 56, .p1 3,
    .cl 0 49, .cl 0 57, .cl 0 62, .cl 0 49, .cl 0 57, .p1 4, .cl 0 49, .cl 0 56, .p1 3, .cl 0 49,
    .cl 0 56, .p1 3, .cl 0 49, .cl 0 56, .p1 3, .cl 0 49, .cl 0 57, .cl 0 70, .p1 3, .cl 0 49,
    .cl 0 57, .cl 0 66, .p1 11, .p1 0, .bk 0, .cl 0 1, .p1 6, .cl 0 1, .cl 0 2, .cl 0 1, .p1 3,
    .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2,
    .bk 0, .cl 0 1, .cl 0 2, .cl 0 1, .p1 11, .cl 0 1, .cl 0 4, .cl 0 1, .p1 11, .cl 0 1, .cl 0 2,
    .cl 0 1, .p1 11, .cl 0 1, .cl 0 2, .cl 0 1, .p1 11, .bk 0, .cl 0 1, .p1 3, .cl 0 1, .cl 0 3,
    .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3, .cl 0 1, .p1 11,
    .cl 0 1, .cl 0 3, .bk 0, .cl 0 2, .cl 0 3, .cl 0 2, .p1 6, .cl 0 2, .cl 0 3, .cl 0 2, .p1 6,
    .cl 0 2, .cl 0 3, .cl 0 2, .p1 6, .cl 0 2, .cl 0 4, .cl 0 2, .p1 6, .bk 0, .cl 0 5, .p1 3,
    .cl 0 10, .cl 0 5, .p1 3, .cl 0 5, .p1 3, .cl 0 5, .p1 3, .cl 0 5, .p1 3, .cl 0 5, .p1 3,
    .cl 0 5, .p1 3, .bk 0, .cl 0 56, .cl 0 64, .cl 0 56, .cl 0 64, .p1 2, .cl 0 56, .cl 0 64,
    .cl 0 66, .cl 0 56, .cl 0 64, .cl 0 56, .cl 0 64, .cl 0 66, .cl 0 56, .cl 0 64, .cl 0 66,
    .cl 0 56, .cl 0 64, .cl 0 56, .cl 0 64, .bk 0, .cl 0 57, .cl 0 74, .cl 0 81, .p1 14, .cl 0 57,
    .cl 0 74, .cl 0 57, .cl 0 74, .cl 0 57, .cl 0 74, .cl 0 57, .cl 0 74, .p1 2, .cl 0 57,
    .cl 0 74, .cl 0 76, .p1 3, .cl 0 57, .cl 0 74, .cl 0 57, .cl 0 74, .cl 0 87, .bk 0, .cl 0 58,
    .cl 0 71, .p1 1, .cl 0 58, .cl 0 71, .cl 0 58, .cl 0 59, .p1 1, .cl 0 58, .cl 0 71, .cl 0 58,
    .cl 0 71, .cl 0 84, .p1 13, .cl 0 58, .cl 0 59, .cl 0 70, .cl 0 58, .cl 0 59, .cl 0 60,
    .cl 0 58, .cl 0 59, .cl 0 61, .bk 0, .cl 0 59, .cl 0 61, .cl 0 64, .cl 0 59, .cl 0 61, .p1 1,
    .cl 0 59, .cl 0 61, .cl 0 59, .cl 0 61, .cl 0 59, .cl 0 61, .cl 0 59, .cl 0 61, .cl 0 69,
    .cl 0 59, .cl 0 61, .cl 0 69, .cl 0 59, .cl 0 61, .bk 0, .cl 0 10, .p1 3, .cl 0 10, .p1 3,
    .cl 0 10, .p1 3, .cl 0 10, .p1 3, .cl 0 10, .p1 3, .cl 0 10, .p1 3, .cl 0 10, .p1 3, .cl 0 20,
    .bk 0, .cl 0 61, .cl 0 63, .p1 1, .cl 0 61, .cl 0 67, .cl 0 61, .cl 0 67, .cl 0 71, .cl 0 61,
    .cl 0 63, .cl 0 65, .cl 0 61, .cl 0 67, .cl 0 61, .cl 0 63, .cl 0 67, .cl 0 61, .cl 0 67,
    .p1 1, .cl 0 61, .cl 0 67, .bk 0, .cl 0 62, .cl 0 73, .cl 0 80, .p1 3, .cl 0 62, .cl 0 73,
    .cl 0 62, .cl 0 81, .cl 0 82, .p1 12, .cl 0 62, .cl 0 73, .cl 0 81, .cl 0 62, .cl 0 73,
    .cl 0 62, .cl 0 73, .cl 0 62, .cl 0 73, .cl 0 62, .cl 0 73, .p1 2, .bk 0, .cl 0 63, .cl 0 72,
    .cl 0 63, .cl 0 72, .cl 0 63, .cl 0 72, .cl 0 63, .cl 0 72, .cl 0 83, .p1 15, .cl 0 63,
    .cl 0 72, .cl 0 80, .p1 3, .cl 0 63, .cl 0 72, .cl 0 63, .cl 0 72, .cl 0 73, .cl 0 63,
    .cl 0 72, .p1 1, .bk 0, .cl 0 64, .cl 0 68, .cl 0 64, .cl 0 68, .cl 0 64, .cl 0 68, .p1 2,
    .cl 0 64, .cl 0 68, .cl 0 77, .p1 3, .cl 0 64, .cl 0 68, .cl 0 82, .p1 15, .cl 0 64, .cl 0 68,
    .cl 0 74, .cl 0 64, .cl 0 68, .bk 0, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5,
    .cl 0 5, .cl 0 5, .bk 0, .cl 0 66, .cl 0 68, .p1 2, .cl 0 66, .cl 0 68, .cl 0 73, .cl 0 66,
    .cl 0 81, .cl 0 91, .cl 0 66, .cl 0 82, .cl 0 66, .cl 0 68, .cl 0 70, .cl 0 66, .cl 0 82,
    .cl 0 66, .cl 0 81, .cl 0 85, .cl 0 66, .cl 0 68, .cl 0 80, .cl 0 81, .bk 0, .cl 0 67,
    .cl 0 72, .cl 0 76, .cl 0 79, .cl 0 82, .cl 0 67, .cl 0 72, .cl 0 78, .cl 0 67, .cl 0 72,
    .cl 0 88, .p1 3, .cl 0 67, .cl 0 84, .cl 0 67, .cl 0 94, .cl 0 96, .cl 0 67, .cl 0 72, .p1 1,
    .cl 0 67, .cl 0 86, .cl 0 95, .p1 13, .cl 0 67, .cl 0 84, .bk 0, .cl 0 68, .cl 0 91, .cl 0 94,
    .p1 14, .cl 0 68, .cl 0 73, .cl 0 77, .cl 0 68, .cl 0 89, .cl 0 95, .p1 14, .cl 0 68, .cl 0 81,
    .cl 0 68, .cl 0 73, .cl 0 76, .cl 0 79, .cl 0 83, .cl 0 68, .cl 0 73, .p1 2, .cl 0 68,
    .cl 0 73, .cl 0 74, .cl 0 68, .cl 0 81, .bk 0, .cl 0 69, .cl 0 111, .p1 3, .cl 0 69, .cl 0 83,
    .cl 0 69, .cl 0 84, .cl 0 85, .cl 0 69, .cl 0 83, .cl 0 97, .cl 0 122, .cl 0 69, .cl 0 83,
    .cl 0 69, .cl 0 84, .cl 0 94, .cl 0 69, .cl 0 83, .bk 0, .cl 0 15, .cl 0 15, .cl 0 15,
    .cl 0 15, .cl 0 15, .cl 0 15, .cl 0 15, .cl 0 15, .bk 0, .cl 0 71, .cl 0 83, .cl 0 85, .p1 7,
    .cl 0 88, .p1 10, .cl 0 71, .cl 0 83, .p1 4, .cl 0 88, .p1 10, .cl 0 71, .cl 0 97, .cl 0 98,
    .cl 0 71, .cl 0 83, .p1 3, .cl 0 71, .cl 0 88, .cl 0 97, .p1 13, .cl 0 88, .p1 10, .bk 0,
    .cl 0 72, .cl 0 88, .cl 0 92, .cl 0 95, .p1 3, .cl 0 86, .p1 9, .cl 0 72, .cl 0 108, .p1 3,
    .cl 0 86, .p1 9, .cl 0 72, .cl 0 88, .p1 3, .cl 0 86, .p1 9, .cl 0 86, .cl 0 111, .cl 0 86,
    .p1 9, .bk 0, .cl 0 73, .cl 0 87, .p1 3, .cl 0 73, .cl 0 87, .p1 6, .cl 0 73, .cl 0 74, .p1 2,
    .cl 0 73, .cl 0 74, .cl 0 82, .p1 3, .cl 0 73, .cl 0 87, .cl 0 93, .cl 0 95, .p1 3, .cl 0 89,
    .p1 8, .cl 0 73, .cl 0 74, .cl 0 80, .cl 0 89, .p1 8, .bk 0, .cl 0 74, .cl 0 87, .cl 0 89,
    .p1 9, .cl 0 87, .p1 7, .cl 0 74, .cl 0 87, .cl 0 98, .p1 14, .cl 0 87, .p1 7, .cl 0 74,
    .cl 0 82, .cl 0 85, .p1 10, .cl 0 74, .cl 0 82, .p1 3, .cl 0 74, .cl 0 82, .p1 4, .cl 0 87,
    .p1 7, .p1 0, .bk 0, .cl 0 1, .p1 11, .cl 0 1, .cl 0 2, .cl 0 1, .p1 3, .cl 0 1, .cl 0 2,
    .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .bk 0, .cl 0 1,
    .cl 0 2, .cl 0 1, .p1 6, .cl 0 1, .cl 0 4, .cl 0 1, .p1 6, .cl 0 1, .cl 0 2, .cl 0 1, .p1 6,
    .cl 0 1, .cl 0 2, .cl 0 1, .p1 6, .bk 0, .cl 0 1, .p1 3, .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3,
    .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3, .cl 0 1, .p1 6, .cl 0 1, .cl 0 3, .bk 0,
    .cl 0 2, .cl 0 3, .cl 0 2, .p1 11, .cl 0 2, .cl 0 3, .cl 0 2, .p1 11, .cl 0 2, .cl 0 3,
    .cl 0 2, .p1 11, .cl 0 2, .cl 0 4, .cl 0 2, .p1 11, .bk 0, .cl 0 5, .p1 3, .cl 0 10, .cl 0 5,
    .p1 3, .cl 0 5, .p1 3, .cl 0 5, .p1 3, .cl 0 5, .p1 3, .cl 0 5, .p1 3, .cl 0 5, .p1 3, .bk 0,
    .cl 0 62, .cl 0 73, .cl 0 76, .p1 3, .cl 0 68, .p1 13, .cl 0 62, .cl 0 73, .p1 5, .cl 0 68,
    .p1 13, .cl 0 62, .cl 0 89, .cl 0 91, .cl 0 68, .p1 13, .cl 0 62, .cl 0 68, .cl 0 82, .p1 2,
    .cl 0 68, .p1 13, .bk 0, .cl 0 64, .cl 0 66, .cl 0 68, .cl 0 70, .cl 0 71, .cl 0 74, .p1 5,
    .cl 0 66, .p1 15, .cl 0 64, .cl 0 81, .cl 0 85, .cl 0 66, .p1 15, .cl 0 64, .cl 0 68, .p1 3,
    .cl 0 66, .p1 15, .cl 0 64, .cl 0 81, .p1 2, .cl 0 66, .p1 15, .bk 0, .cl 0 61, .cl 0 67,
    .p1 3, .cl 0 61, .cl 0 67, .p1 11, .cl 0 61, .cl 0 84, .p1 1, .cl 0 61, .cl 0 63, .cl 0 68,
    .cl 0 61, .cl 0 63, .cl 0 68, .cl 0 61, .cl 0 63, .cl 0 68, .p1 15, .cl 0 61, .cl 0 84,
    .cl 0 85, .cl 0 69, .p1 12, .bk 0, .cl 0 63, .cl 0 67, .cl 0 69, .p1 15, .cl 0 67, .p1 14,
    .cl 0 63, .cl 0 67, .cl 0 83, .p1 1, .cl 0 67, .p1 14, .cl 0 63, .cl 0 72, .cl 0 76, .p1 4,
    .cl 0 67, .p1 14, .cl 0 63, .cl 0 72, .p1 5, .cl 0 67, .p1 14, .bk 0, .cl 0 10, .p1 3,
    .cl 0 10, .p1 3, .cl 0 10, .p1 3, .cl 0 10, .p1 3, .cl 0 10, .p1 3, .cl 0 10, .p1 3, .cl 0 10,
    .p1 3, .cl 0 20, .bk 0, .cl 0 58, .cl 0 72, .cl 0 84, .cl 0 87, .cl 0 88, .cl 0 58, .p1 9,
    .cl 0 58, .cl 0 72, .cl 0 92, .p1 1, .cl 0 58, .p1 9, .cl 0 72, .cl 0 92, .cl 0 58, .p1 9,
    .cl 0 72, .cl 0 92, .p1 1, .cl 0 58, .p1 9, .bk 0, .cl 0 56, .cl 0 74, .cl 0 82, .cl 0 89,
    .p1 10, .cl 0 56, .p1 7, .cl 0 56, .cl 0 57, .cl 0 74, .cl 0 56, .p1 7, .cl 0 56, .cl 0 74,
    .cl 0 89, .p1 2, .cl 0 56, .p1 7, .cl 0 56, .cl 0 73, .cl 0 74, .cl 0 56, .p1 7, .bk 0,
    .cl 0 59, .cl 0 71, .cl 0 86, .p1 1, .cl 0 59, .p1 10, .cl 0 59, .cl 0 71, .cl 0 72, .p1 11,
    .cl 0 59, .p1 10, .cl 0 59, .cl 0 71, .cl 0 83, .cl 0 86, .p1 7, .cl 0 59, .p1 10, .cl 0 71,
    .cl 0 83, .cl 0 84, .cl 0 59, .p1 10, .bk 0, .cl 0 73, .cl 0 93, .cl 0 57, .p1 8, .cl 0 57,
    .cl 0 73, .cl 0 81, .cl 0 82, .cl 0 57, .p1 8, .cl 0 57, .cl 0 73, .cl 0 81, .cl 0 84, .p1 13,
    .cl 0 57, .p1 8, .cl 0 57, .cl 0 73, .cl 0 74, .cl 0 81, .p1 5, .cl 0 57, .p1 8, .bk 0,
    .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .bk 0, .cl 0 57,
    .cl 0 87, .cl 0 73, .p1 8, .cl 0 57, .cl 0 74, .cl 0 79, .p1 13, .cl 0 73, .p1 8, .cl 0 57,
    .cl 0 87, .cl 0 73, .p1 8, .cl 0 57, .cl 0 74, .p1 3, .cl 0 73, .p1 8, .bk 0, .cl 0 59,
    .cl 0 61, .p1 4, .cl 0 71, .p1 10, .cl 0 59, .cl 0 71, .cl 0 72, .p1 8, .cl 0 71, .p1 10,
    .cl 0 59, .cl 0 69, .cl 0 71, .cl 0 71, .p1 10, .cl 0 59, .cl 0 61, .cl 0 70, .p1 7, .cl 0 59,
    .cl 0 61, .p1 3, .bk 0, .cl 0 56, .cl 0 66, .cl 0 69, .p1 10, .cl 0 74, .p1 7, .cl 0 56,
    .cl 0 64, .cl 0 70, .p1 10, .cl 0 56, .cl 0 66, .cl 0 68, .p1 9, .cl 0 56, .cl 0 64, .p1 4,
    .cl 0 74, .p1 7, .cl 0 56, .cl 0 66, .cl 0 69, .cl 0 56, .cl 0 64, .p1 3, .bk 0, .cl 0 58,
    .cl 0 88, .cl 0 72, .p1 9, .cl 0 58, .cl 0 59, .cl 0 60, .cl 0 58, .cl 0 71, .p1 6, .cl 0 58,
    .cl 0 88, .cl 0 72, .p1 9, .cl 0 58, .cl 0 59, .cl 0 69, .cl 0 58, .cl 0 59, .cl 0 72, .bk 0,
    .cl 0 15, .cl 0 15, .cl 0 15, .cl 0 15, .cl 0 15, .cl 0 15, .cl 0 15, .cl 0 15, .bk 0,
    .cl 0 63, .cl 0 67, .cl 0 69, .p1 6, .cl 0 63, .p1 14, .cl 0 63, .cl 0 83, .cl 0 63, .p1 14,
    .cl 0 67, .cl 0 72, .cl 0 73, .cl 0 63, .p1 14, .cl 0 63, .cl 0 67, .cl 0 72, .p1 7, .cl 0 63,
    .p1 14, .bk 0, .cl 0 61, .cl 0 69, .cl 0 84, .p1 1, .cl 0 61, .p1 12, .cl 0 69, .cl 0 84,
    .cl 0 61, .p1 12, .cl 0 69, .cl 0 84, .p1 1, .cl 0 61, .p1 12, .cl 0 69, .cl 0 84, .cl 0 61,
    .p1 12, .bk 0, .cl 0 66, .cl 0 68, .cl 0 70, .cl 0 73, .p1 14, .cl 0 64, .p1 15, .cl 0 66,
    .cl 0 81, .cl 0 64, .p1 15, .cl 0 66, .cl 0 68, .cl 0 73, .cl 0 64, .p1 15, .cl 0 66, .cl 0 81,
    .cl 0 64, .p1 15, .bk 0, .cl 0 62, .cl 0 64, .cl 0 68, .cl 0 62, .p1 13, .cl 0 62, .cl 0 68,
    .cl 0 73, .p1 10, .cl 0 62, .p1 13, .cl 0 62, .cl 0 66, .cl 0 68, .cl 0 62, .p1 13, .cl 0 62,
    .cl 0 82, .cl 0 62, .p1 13, .p1 0, .bk 0, .cl 0 1, .p1 4, .cl 0 1, .cl 0 2, .cl 0 1, .p1 3,
    .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2,
    .bk 0, .cl 0 1, .cl 0 2, .cl 0 1, .p1 5, .cl 0 1, .cl 0 4, .cl 0 1, .p1 5, .cl 0 1, .cl 0 2,
    .cl 0 1, .p1 5, .cl 0 1, .cl 0 2, .cl 0 1, .p1 5, .bk 0, .cl 0 1, .p1 3, .cl 0 1, .cl 0 3,
    .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3, .cl 0 1, .p1 5,
    .cl 0 1, .cl 0 3, .bk 0, .cl 0 2, .cl 0 3, .cl 0 2, .p1 4, .cl 0 2, .cl 0 3, .cl 0 2, .p1 4,
    .cl 0 2, .cl 0 3, .cl 0 2, .p1 4, .cl 0 2, .cl 0 4, .cl 0 2, .p1 4, .bk 0, .cl 0 5, .p1 3,
    .cl 0 10, .cl 0 5, .p1 3, .cl 0 5, .p1 3, .cl 0 5, .p1 3, .cl 0 5, .p1 3, .cl 0 5, .p1 3,
    .cl 0 5, .p1 3, .bk 0, .cl 0 37, .cl 0 48, .cl 0 51, .p1 3, .cl 0 43, .p1 15, .cl 0 37,
    .cl 0 48, .p1 11, .cl 0 43, .p1 15, .cl 0 37, .cl 0 43, .cl 0 56, .p1 7, .cl 0 43, .p1 15,
    .cl 0 37, .cl 0 43, .cl 0 56, .p1 12, .cl 0 43, .p1 15, .bk 0, .cl 0 39, .cl 0 41, .cl 0 43,
    .cl 0 45, .cl 0 46, .cl 0 49, .p1 11, .cl 0 41, .p1 7, .cl 0 39, .cl 0 41, .cl 0 57, .p1 12,
    .cl 0 41, .p1 7, .cl 0 39, .cl 0 43, .p1 3, .cl 0 41, .p1 7, .cl 0 39, .cl 0 41, .cl 0 57,
    .p1 4, .cl 0 41, .p1 7, .bk 0, .cl 0 36, .cl 0 42, .p1 3, .cl 0 36, .cl 0 42, .p1 4, .cl 0 36,
    .cl 0 44, .cl 0 58, .p1 4, .cl 0 36, .cl 0 38, .cl 0 43, .cl 0 36, .cl 0 38, .cl 0 43,
    .cl 0 36, .cl 0 38, .cl 0 43, .p1 7, .cl 0 36, .cl 0 44, .cl 0 58, .p1 15, .cl 0 44, .p1 10,
    .bk 0, .cl 0 38, .cl 0 42, .cl 0 44, .p1 7, .cl 0 42, .p1 12, .cl 0 38, .cl 0 42, .cl 0 59,
    .p1 15, .cl 0 42, .p1 12, .cl 0 38, .cl 0 47, .cl 0 54, .p1 3, .cl 0 42, .p1 12, .cl 0 38,
    .cl 0 47, .p1 11, .cl 0 42, .p1 12, .bk 0, .cl 0 10, .p1 3, .cl 0 10, .p1 3, .cl 0 10, .p1 3,
    .cl 0 10, .p1 3, .cl 0 10, .p1 3, .cl 0 10, .p1 3, .cl 0 10, .p1 3, .cl 0 20, .bk 0, .cl 0 47,
    .cl 0 58, .cl 0 33, .p1 14, .cl 0 47, .cl 0 58, .cl 0 59, .p1 4, .cl 0 33, .p1 14, .cl 0 33,
    .cl 0 47, .cl 0 61, .p1 8, .cl 0 33, .p1 14, .cl 0 47, .cl 0 58, .cl 0 33, .p1 14, .bk 0,
    .cl 0 49, .cl 0 56, .cl 0 31, .p1 8, .cl 0 31, .cl 0 32, .cl 0 49, .cl 0 31, .p1 8, .cl 0 49,
    .cl 0 56, .cl 0 31, .p1 8, .cl 0 31, .cl 0 48, .cl 0 49, .cl 0 31, .p1 8, .bk 0, .cl 0 46,
    .cl 0 59, .cl 0 34, .p1 9, .cl 0 34, .cl 0 46, .cl 0 47, .p1 4, .cl 0 34, .p1 9, .cl 0 46,
    .cl 0 59, .cl 0 34, .p1 9, .cl 0 34, .cl 0 46, .cl 0 59, .cl 0 61, .p1 8, .cl 0 34, .p1 9,
    .bk 0, .cl 0 32, .cl 0 48, .cl 0 57, .cl 0 62, .cl 0 64, .cl 0 32, .p1 13, .cl 0 48, .cl 0 49,
    .cl 0 54, .p1 12, .cl 0 32, .p1 13, .cl 0 48, .cl 0 57, .cl 0 32, .p1 13, .cl 0 48, .cl 0 49,
    .cl 0 57, .p1 2, .cl 0 32, .p1 13, .bk 0, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5,
    .cl 0 5, .cl 0 5, .bk 0, .cl 0 32, .cl 0 48, .cl 0 57, .p1 2, .cl 0 48, .p1 13, .cl 0 32,
    .cl 0 48, .cl 0 57, .cl 0 48, .p1 13, .cl 0 32, .cl 0 48, .cl 0 57, .cl 0 48, .p1 13, .cl 0 32,
    .cl 0 49, .p1 3, .cl 0 48, .p1 13, .bk 0, .cl 0 34, .cl 0 36, .p1 6, .cl 0 46, .p1 9, .cl 0 34,
    .cl 0 46, .cl 0 47, .p1 13, .cl 0 46, .p1 9, .cl 0 34, .cl 0 44, .cl 0 46, .cl 0 46, .p1 9,
    .cl 0 34, .cl 0 36, .cl 0 45, .p1 8, .cl 0 34, .cl 0 36, .p1 3, .bk 0, .cl 0 31, .cl 0 41,
    .cl 0 44, .p1 9, .cl 0 49, .p1 8, .cl 0 31, .cl 0 39, .cl 0 45, .p1 9, .cl 0 31, .cl 0 41,
    .cl 0 43, .p1 14, .cl 0 31, .cl 0 39, .p1 6, .cl 0 49, .p1 8, .cl 0 31, .cl 0 41, .cl 0 44,
    .cl 0 31, .cl 0 39, .p1 3, .bk 0, .cl 0 33, .cl 0 47, .cl 0 58, .cl 0 47, .p1 14, .cl 0 33,
    .cl 0 34, .cl 0 35, .cl 0 33, .cl 0 46, .p1 5, .cl 0 33, .cl 0 47, .cl 0 58, .p1 1, .cl 0 47,
    .p1 14, .cl 0 33, .cl 0 34, .cl 0 44, .cl 0 33, .cl 0 34, .cl 0 47, .bk 0, .cl 0 15, .cl 0 15,
    .cl 0 15, .cl 0 15, .cl 0 15, .cl 0 15, .cl 0 15, .cl 0 15, .bk 0, .cl 0 38, .cl 0 42,
    .cl 0 44, .p1 5, .cl 0 38, .p1 12, .cl 0 42, .cl 0 63, .cl 0 38, .p1 12, .cl 0 42, .cl 0 47,
    .cl 0 48, .cl 0 38, .p1 12, .cl 0 38, .cl 0 42, .cl 0 47, .p1 8, .cl 0 38, .p1 12, .bk 0,
    .cl 0 44, .cl 0 61, .cl 0 63, .p1 5, .cl 0 36, .p1 10, .cl 0 44, .cl 0 59, .cl 0 61, .cl 0 36,
    .p1 10, .cl 0 36, .cl 0 58, .p1 3, .cl 0 36, .p1 10, .cl 0 44, .cl 0 59, .p1 6, .cl 0 36,
    .p1 10, .bk 0, .cl 0 41, .cl 0 43, .cl 0 45, .cl 0 48, .p1 12, .cl 0 39, .p1 7, .cl 0 41,
    .cl 0 56, .p1 6, .cl 0 39, .p1 7, .cl 0 41, .cl 0 43, .cl 0 48, .cl 0 39, .p1 7, .cl 0 41,
    .cl 0 56, .cl 0 64, .cl 0 39, .p1 7, .bk 0, .cl 0 37, .cl 0 39, .cl 0 43, .cl 0 37, .p1 15,
    .cl 0 37, .cl 0 43, .cl 0 48, .p1 9, .cl 0 37, .p1 15, .cl 0 37, .cl 0 41, .cl 0 43, .cl 0 37,
    .p1 15, .cl 0 43, .cl 0 62, .cl 0 37, .p1 15]

private theorem cdOK333 : CdOK ⟨3, 0, 3, 3⟩ tab33 cd333 where
  size := by decide +kernel
  rep := by decide +kernel
  orb := by decide +kernel
  gp := by decide +kernel
  nu := by decide +kernel
  al := by decide +kernel
  be := by decide +kernel
  m := by decide +kernel

private theorem run333 : run cd333 3368 [(z16, z16)] cert333 = true := by
  decide +kernel

private theorem case333 :
    (tablesOKb ⟨3, 0, 3, 3⟩ (orbitData ⟨3, 0, 3, 3⟩) && g8b ⟨3, 0, 3, 3⟩ &&
      search ⟨3, 0, 3, 3⟩ (orbitData ⟨3, 0, 3, 3⟩) 17
        (Array.replicate (orbitData ⟨3, 0, 3, 3⟩).reps.size none)) = true := by
  rw [orbitData33]
  exact search_case tablesOKb33 g8b33 cdOK333 run333

private def cd337 : Cd := ⟨3, 0, 3, 7, orb33, rep33, gp33⟩

private def cert337 : List Op := [
    .bv 0, .bk 0, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .bv 1, .p1 1, .p1 1, .p1 1, .p1 1, .p1 1,
    .cl 0 5, .cl 0 5, .cl 0 5, .bk 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1,
    .cl 1 1, .cl 1 1, .p1 1, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .p1 1, .cl 0 5, .cl 0 5, .cl 0 5,
    .cl 0 5, .p1 1, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .p1 1, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5,
    .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5,
    .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5,
    .p1 1, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5,
    .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5,
    .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .p1 1, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5,
    .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5,
    .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5,
    .p1 1, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5,
    .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5,
    .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 1, .cl 0 1, .cl 0 1, .bk 0, .cl 0 1,
    .cl 0 1, .bv 1, .p1 1, .p1 1, .p1 1, .p1 1, .p1 1, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .p1 1,
    .cl 0 5, .cl 0 5, .bk 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1,
    .cl 1 1, .cl 0 5, .p1 1, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .p1 1, .cl 0 5, .cl 0 5, .cl 0 5,
    .cl 0 5, .p1 1, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5,
    .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5,
    .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .p1 1, .cl 0 5, .cl 0 5, .cl 0 5,
    .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5,
    .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5,
    .cl 0 5, .p1 1, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5,
    .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5,
    .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .p1 1, .cl 0 5, .cl 0 5, .cl 0 5,
    .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5,
    .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5,
    .cl 0 5, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .bk 0, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .bv 1, .p1 1, .p1 1, .p1 1, .p1 1, .p1 1, .cl 0 6, .p1 2, .cl 0 7,
    .cl 0 5, .cl 0 5, .p1 1, .cl 0 5, .cl 0 7, .p1 2, .cl 0 5, .cl 0 6, .p1 2, .p1 1, .cl 0 7,
    .p1 2, .bk 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 0 7,
    .cl 0 5, .p1 1, .cl 0 5, .cl 0 5, .cl 0 7, .cl 0 6, .p1 2, .p1 1, .cl 0 7, .p1 7, .cl 0 7,
    .p1 8, .cl 0 7, .p1 9, .cl 0 7, .p1 10, .cl 0 7, .p1 11, .cl 0 7, .p1 12, .cl 0 7, .p1 13,
    .cl 0 7, .p1 14, .cl 0 7, .p1 15, .cl 0 7, .cl 0 7, .p1 15, .cl 0 7, .p1 14, .cl 0 7, .p1 13,
    .cl 0 7, .p1 12, .cl 0 7, .p1 6, .cl 0 7, .p1 10, .cl 0 7, .p1 9, .cl 0 7, .p1 8, .cl 0 7,
    .p1 7, .cl 0 7, .p1 3, .cl 0 7, .p1 4, .cl 0 7, .p1 5, .cl 0 7, .p1 5, .cl 0 7, .p1 4, .p1 1,
    .cl 0 7, .p1 15, .cl 0 7, .p1 7, .cl 0 7, .p1 10, .cl 0 7, .p1 12, .cl 0 7, .p1 5, .cl 0 7,
    .p1 14, .cl 0 7, .p1 8, .cl 0 7, .p1 9, .cl 0 7, .p1 13, .cl 0 7, .cl 0 7, .p1 13, .cl 0 7,
    .p1 9, .cl 0 7, .p1 8, .cl 0 7, .p1 14, .cl 0 7, .p1 4, .cl 0 7, .p1 12, .cl 0 7, .p1 10,
    .cl 0 7, .p1 7, .cl 0 7, .p1 15, .cl 0 7, .p1 3, .cl 0 7, .p1 11, .cl 0 7, .p1 6, .cl 0 7,
    .p1 6, .cl 0 7, .p1 11, .p1 1, .cl 0 7, .p1 8, .cl 0 7, .p1 13, .cl 0 7, .p1 14, .cl 0 7,
    .p1 9, .cl 0 7, .p1 4, .cl 0 7, .p1 10, .cl 0 7, .p1 15, .cl 0 7, .p1 12, .cl 0 7, .p1 7,
    .cl 0 7, .cl 0 7, .p1 7, .cl 0 7, .p1 12, .cl 0 7, .p1 15, .cl 0 7, .p1 10, .cl 0 7, .p1 5,
    .cl 0 7, .p1 9, .cl 0 7, .p1 14, .cl 0 7, .p1 13, .cl 0 7, .p1 8, .cl 0 7, .p1 3, .cl 0 7,
    .p1 6, .cl 0 7, .p1 11, .cl 0 7, .p1 11, .cl 0 7, .p1 6, .p1 1, .cl 0 7, .p1 13, .cl 0 7,
    .p1 15, .cl 0 7, .p1 12, .cl 0 7, .p1 14, .cl 0 7, .p1 6, .cl 0 7, .p1 9, .cl 0 7, .p1 7,
    .cl 0 7, .p1 10, .cl 0 7, .p1 8, .cl 0 7, .cl 0 7, .p1 8, .cl 0 7, .p1 10, .cl 0 7, .p1 7,
    .cl 0 7, .p1 9, .cl 0 7, .p1 11, .cl 0 7, .p1 14, .cl 0 7, .p1 12, .cl 0 7, .p1 15, .cl 0 7,
    .p1 13, .cl 0 7, .p1 3, .cl 0 7, .p1 5, .cl 0 7, .p1 4, .cl 0 7, .p1 4, .cl 0 7, .p1 5,
    .cl 0 1, .bk 0, .bv 1, .p1 1, .p1 1, .p1 1, .p1 1, .p1 1, .cl 0 6, .cl 0 6, .p1 2, .cl 0 5,
    .cl 0 5, .p1 1, .cl 0 5, .cl 0 6, .p1 2, .cl 0 5, .cl 0 6, .p1 1, .cl 0 6, .p1 2, .cl 0 5,
    .cl 0 6, .p1 2, .cl 0 5, .p1 1, .bk 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1,
    .cl 1 1, .cl 1 1, .cl 0 5, .cl 0 6, .cl 0 6, .p1 1, .cl 0 6, .p1 5, .cl 0 6, .cl 0 6, .p1 4,
    .cl 0 6, .p1 3, .cl 0 6, .p1 7, .cl 0 6, .p1 8, .cl 0 6, .p1 9, .cl 0 6, .p1 10, .cl 0 6,
    .p1 6, .cl 0 6, .p1 12, .cl 0 6, .p1 13, .cl 0 6, .p1 14, .cl 0 6, .p1 15, .cl 0 6, .p1 11,
    .cl 0 6, .p1 15, .cl 0 6, .p1 14, .cl 0 6, .p1 13, .cl 0 6, .p1 12, .cl 0 6, .p1 11, .cl 0 6,
    .p1 10, .cl 0 6, .p1 9, .cl 0 6, .p1 8, .cl 0 6, .p1 7, .cl 0 6, .p1 6, .p1 1, .cl 0 6, .p1 6,
    .cl 0 6, .cl 0 6, .p1 11, .cl 0 6, .p1 3, .cl 0 6, .p1 15, .cl 0 6, .p1 7, .cl 0 6, .p1 10,
    .cl 0 6, .p1 12, .cl 0 6, .p1 4, .cl 0 6, .p1 14, .cl 0 6, .p1 8, .cl 0 6, .p1 9, .cl 0 6,
    .p1 13, .cl 0 6, .p1 5, .cl 0 6, .p1 13, .cl 0 6, .p1 9, .cl 0 6, .p1 8, .cl 0 6, .p1 14,
    .cl 0 6, .p1 5, .cl 0 6, .p1 12, .cl 0 6, .p1 10, .cl 0 6, .p1 7, .cl 0 6, .p1 15, .cl 0 6,
    .p1 4, .p1 1, .cl 0 6, .p1 11, .cl 0 6, .cl 0 6, .p1 6, .cl 0 6, .p1 3, .cl 0 6, .p1 8,
    .cl 0 6, .p1 13, .cl 0 6, .p1 14, .cl 0 6, .p1 9, .cl 0 6, .p1 5, .cl 0 6, .p1 10, .cl 0 6,
    .p1 15, .cl 0 6, .p1 12, .cl 0 6, .p1 7, .cl 0 6, .p1 4, .cl 0 6, .p1 7, .cl 0 6, .p1 12,
    .cl 0 6, .p1 15, .cl 0 6, .p1 10, .cl 0 6, .p1 4, .cl 0 6, .p1 9, .cl 0 6, .p1 14, .cl 0 6,
    .p1 13, .cl 0 6, .p1 8, .cl 0 6, .p1 5, .p1 1, .cl 0 6, .p1 4, .cl 0 6, .cl 0 6, .p1 5,
    .cl 0 6, .p1 3, .cl 0 6, .p1 13, .cl 0 6, .p1 15, .cl 0 6, .p1 12, .cl 0 6, .p1 14, .cl 0 6,
    .p1 11, .cl 0 6, .p1 9, .cl 0 6, .p1 7, .cl 0 6, .p1 10, .cl 0 6, .p1 8, .cl 0 6, .p1 6,
    .cl 0 6, .p1 8, .cl 0 6, .p1 10, .cl 0 6, .p1 7, .cl 0 6, .p1 9, .cl 0 6, .p1 6, .cl 0 6,
    .p1 14, .cl 0 6, .p1 12, .cl 0 6, .p1 15, .cl 0 6, .p1 13, .cl 0 6, .p1 11, .cl 0 2, .cl 0 2,
    .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .bk 0, .cl 0 5, .cl 0 5, .cl 0 5, .bv 1, .p1 1,
    .p1 1, .p1 1, .p1 1, .p1 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .p1 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .p1 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .p1 1, .cl 0 1, .bk 1, .cl 1 1,
    .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 0 1, .cl 0 1, .p1 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .p1 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .p1 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .p1 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 5,
    .cl 0 5, .cl 0 5, .cl 0 5, .bk 0, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .bk 0, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3,
    .cl 0 3, .bk 0, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .bk 0,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .bk 0, .cl 0 5, .bv 1,
    .p1 1, .p1 1, .p1 1, .p1 1, .p1 1, .cl 0 2, .cl 0 2, .cl 0 1, .cl 0 1, .p1 1, .cl 0 1, .cl 0 2,
    .cl 0 1, .cl 0 2, .p1 1, .cl 0 2, .cl 0 1, .cl 0 2, .bk 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1,
    .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .p1 1, .cl 0 1, .cl 0 1, .cl 0 2, .cl 0 2, .p1 1, .cl 0 2,
    .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2,
    .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2,
    .cl 0 2, .cl 0 2, .cl 0 2, .p1 1, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2,
    .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2,
    .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .p1 1, .cl 0 2,
    .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2,
    .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2,
    .cl 0 2, .cl 0 2, .cl 0 2, .p1 1, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2,
    .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2,
    .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 5, .cl 0 5,
    .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .bk 0, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2,
    .cl 0 2, .cl 0 2, .cl 0 2, .bk 0, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2,
    .cl 0 2, .cl 0 2, .bk 0, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2,
    .cl 0 2, .bk 0, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .bk 0,
    .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .cl 0 5, .bv 1, .p1 1, .p1 1, .p1 1, .p1 1, .p1 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .p1 1, .bk 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1,
    .cl 1 1, .cl 1 1, .cl 0 1, .cl 0 1, .cl 0 1, .p1 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .p1 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .p1 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .p1 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .p1 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .p1 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 5, .cl 0 5, .bk 0, .cl 0 2, .cl 0 2, .cl 0 2,
    .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .bk 0, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2,
    .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .bk 0, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2, .cl 0 2,
    .cl 0 2, .cl 0 2, .cl 0 2, .bk 0, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .bk 0, .cl 0 10, .cl 0 10, .cl 0 10, .cl 0 10, .cl 0 10, .cl 0 10, .cl 0 10,
    .bv 1, .p1 1, .p1 1, .p1 1, .p1 1, .p1 1, .cl 0 3, .cl 0 3, .bk 1, .cl 1 1, .cl 1 1, .cl 1 1,
    .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 1 1, .cl 0 1, .p1 1, .cl 0 1, .cl 0 3, .cl 0 1,
    .cl 0 3, .p1 1, .cl 0 3, .cl 0 1, .cl 0 3, .cl 0 1, .p1 1, .cl 0 1, .cl 0 1, .cl 0 3, .cl 0 3,
    .p1 1, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3,
    .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3,
    .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .p1 1, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3,
    .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3,
    .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3,
    .p1 1, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3,
    .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3,
    .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .p1 1, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3,
    .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3,
    .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3,
    .bk 0, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .bk 0, .cl 0 3,
    .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .cl 0 3, .bk 0, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .bk 0, .cl 0 1, .cl 0 1, .cl 0 1,
    .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .cl 0 1, .p1 0, .bk 0, .cl 0 1, .p1 5, .cl 0 1, .cl 0 2,
    .cl 0 1, .p1 3, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2,
    .cl 0 1, .cl 0 2, .bk 0, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 4, .cl 0 1,
    .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .bk 0,
    .cl 0 1, .p1 3, .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3,
    .cl 0 1, .cl 0 3, .cl 0 1, .p1 4, .cl 0 1, .cl 0 3, .bk 0, .cl 0 2, .cl 0 3, .cl 0 2, .cl 0 3,
    .cl 0 2, .cl 0 3, .cl 0 2, .cl 0 3, .cl 0 2, .cl 0 3, .cl 0 2, .cl 0 3, .cl 0 2, .cl 0 4,
    .cl 0 2, .cl 0 3, .bk 0, .cl 0 5, .cl 0 10, .cl 0 5, .p1 3, .cl 0 5, .cl 0 10, .cl 0 5,
    .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5, .p1 11, .bk 0,
    .cl 0 31, .cl 0 39, .cl 0 41, .cl 0 31, .cl 0 39, .cl 0 41, .cl 0 31, .cl 0 39, .cl 0 31,
    .cl 0 39, .cl 0 31, .cl 0 39, .cl 0 31, .cl 0 39, .p1 2, .cl 0 31, .cl 0 39, .cl 0 41,
    .cl 0 31, .cl 0 39, .bk 0, .cl 0 32, .cl 0 49, .cl 0 62, .p1 12, .cl 0 32, .cl 0 49, .cl 0 32,
    .cl 0 49, .cl 0 32, .cl 0 49, .cl 0 32, .cl 0 49, .p1 2, .cl 0 32, .cl 0 49, .cl 0 57,
    .cl 0 60, .cl 0 32, .cl 0 49, .cl 0 32, .cl 0 49, .cl 0 62, .p1 12, .bk 0, .cl 0 33, .cl 0 46,
    .p1 1, .cl 0 33, .cl 0 46, .cl 0 33, .cl 0 46, .cl 0 33, .cl 0 46, .cl 0 33, .cl 0 46,
    .cl 0 58, .cl 0 61, .cl 0 33, .cl 0 34, .cl 0 39, .cl 0 33, .cl 0 34, .cl 0 38, .cl 0 33,
    .cl 0 34, .p1 1, .bk 0, .cl 0 34, .cl 0 36, .cl 0 34, .cl 0 36, .cl 0 44, .cl 0 34, .cl 0 36,
    .cl 0 44, .cl 0 34, .cl 0 36, .cl 0 34, .cl 0 36, .cl 0 39, .cl 0 34, .cl 0 36, .p1 1,
    .cl 0 34, .cl 0 36, .cl 0 34, .cl 0 36, .bk 0, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 20, .cl 0 5,
    .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5,
    .cl 0 10, .bk 0, .cl 0 36, .cl 0 38, .cl 0 39, .cl 0 36, .cl 0 42, .cl 0 36, .cl 0 42,
    .cl 0 46, .cl 0 36, .cl 0 38, .cl 0 42, .cl 0 36, .cl 0 42, .cl 0 36, .cl 0 38, .p1 1,
    .cl 0 36, .cl 0 42, .p1 1, .cl 0 36, .cl 0 42, .bk 0, .cl 0 37, .cl 0 48, .cl 0 37, .cl 0 48,
    .cl 0 37, .cl 0 48, .cl 0 37, .cl 0 48, .p1 2, .cl 0 37, .cl 0 48, .cl 0 51, .p1 3, .cl 0 37,
    .cl 0 48, .cl 0 37, .cl 0 48, .cl 0 63, .p1 6, .cl 0 37, .cl 0 48, .cl 0 64, .p1 10, .bk 0,
    .cl 0 38, .cl 0 47, .cl 0 54, .p1 3, .cl 0 38, .cl 0 47, .cl 0 38, .cl 0 47, .cl 0 48,
    .cl 0 38, .cl 0 47, .p1 1, .cl 0 38, .cl 0 47, .cl 0 38, .cl 0 47, .cl 0 38, .cl 0 47,
    .cl 0 38, .cl 0 47, .cl 0 61, .p1 7, .bk 0, .cl 0 39, .cl 0 43, .cl 0 39, .cl 0 43, .cl 0 39,
    .cl 0 43, .p1 2, .cl 0 39, .cl 0 43, .cl 0 55, .p1 3, .cl 0 39, .cl 0 43, .cl 0 39, .cl 0 66,
    .p1 3, .cl 0 39, .cl 0 43, .cl 0 49, .cl 0 39, .cl 0 43, .bk 0, .cl 0 5, .cl 0 15, .cl 0 5,
    .cl 0 15, .cl 0 5, .cl 0 15, .cl 0 5, .cl 0 15, .cl 0 5, .cl 0 15, .cl 0 5, .p1 6, .cl 0 5,
    .cl 0 15, .cl 0 5, .p1 3, .bk 0, .cl 0 41, .cl 0 43, .cl 0 44, .cl 0 41, .cl 0 43, .p1 2,
    .cl 0 41, .cl 0 56, .cl 0 67, .cl 0 41, .cl 0 56, .p1 9, .cl 0 41, .cl 0 43, .cl 0 49,
    .cl 0 41, .cl 0 64, .p1 3, .cl 0 41, .cl 0 56, .p1 9, .cl 0 41, .cl 0 43, .cl 0 47, .bk 0,
    .cl 0 42, .cl 0 69, .p1 7, .cl 0 42, .cl 0 47, .cl 0 61, .p1 5, .cl 0 42, .cl 0 63, .p1 3,
    .cl 0 42, .cl 0 69, .cl 0 71, .cl 0 42, .cl 0 47, .cl 0 49, .cl 0 42, .cl 0 47, .cl 0 59,
    .p1 10, .cl 0 42, .cl 0 47, .p1 1, .cl 0 42, .cl 0 63, .p1 3, .bk 0, .cl 0 43, .cl 0 48,
    .cl 0 58, .cl 0 43, .cl 0 48, .cl 0 61, .p1 4, .cl 0 43, .cl 0 48, .p1 2, .cl 0 43, .cl 0 66,
    .cl 0 68, .cl 0 72, .cl 0 73, .p1 3, .cl 0 43, .cl 0 66, .p1 10, .cl 0 43, .cl 0 48, .cl 0 56,
    .p1 7, .cl 0 43, .cl 0 62, .p1 3, .cl 0 43, .cl 0 62, .p1 3, .bk 0, .cl 0 44, .cl 0 59, .p1 3,
    .cl 0 44, .cl 0 61, .p1 1, .cl 0 44, .cl 0 59, .p1 8, .cl 0 44, .cl 0 59, .p1 8, .cl 0 44,
    .cl 0 59, .cl 0 68, .cl 0 44, .cl 0 61, .p1 3, .cl 0 44, .cl 0 59, .cl 0 68, .cl 0 44,
    .cl 0 59, .cl 0 61, .p1 3, .bk 0, .cl 0 10, .cl 0 15, .cl 0 10, .cl 0 15, .cl 0 10, .cl 0 15,
    .cl 0 10, .cl 0 15, .cl 0 10, .cl 0 15, .cl 0 10, .cl 0 20, .cl 0 10, .cl 0 15, .cl 0 10,
    .cl 0 15, .bk 0, .cl 0 46, .cl 0 59, .p1 1, .cl 0 46, .cl 0 59, .p1 3, .cl 0 46, .cl 0 72,
    .p1 13, .cl 0 46, .cl 0 71, .cl 0 83, .p1 3, .cl 0 46, .cl 0 59, .p1 3, .cl 0 46, .cl 0 71,
    .cl 0 72, .cl 0 76, .cl 0 80, .p1 11, .cl 0 46, .cl 0 86, .p1 7, .cl 0 46, .cl 0 59, .p1 3,
    .bk 0, .cl 0 47, .cl 0 67, .cl 0 74, .cl 0 47, .cl 0 67, .cl 0 72, .p1 12, .cl 0 47, .cl 0 58,
    .p1 3, .cl 0 47, .cl 0 58, .p1 1, .cl 0 47, .cl 0 58, .p1 3, .cl 0 47, .cl 0 67, .p1 15,
    .cl 0 47, .cl 0 67, .cl 0 74, .cl 0 47, .cl 0 58, .p1 3, .bk 0, .cl 0 48, .cl 0 57, .p1 3,
    .cl 0 48, .cl 0 49, .cl 0 57, .p1 3, .cl 0 48, .cl 0 49, .cl 0 57, .p1 3, .cl 0 48, .cl 0 49,
    .p1 2, .cl 0 48, .cl 0 68, .cl 0 71, .cl 0 48, .cl 0 68, .p1 12, .cl 0 48, .cl 0 57, .p1 3,
    .cl 0 48, .cl 0 57, .p1 3, .bk 0, .cl 0 49, .cl 0 56, .p1 3, .cl 0 49, .cl 0 56, .p1 3,
    .cl 0 49, .cl 0 73, .cl 0 74, .p1 13, .cl 0 49, .cl 0 73, .cl 0 82, .p1 3, .cl 0 49, .cl 0 56,
    .p1 2, .cl 0 49, .cl 0 73, .cl 0 74, .cl 0 79, .cl 0 80, .p1 11, .cl 0 49, .cl 0 73, .p1 14,
    .cl 0 49, .cl 0 56, .p1 3, .p1 0, .bk 0, .cl 0 1, .p1 6, .cl 0 1, .cl 0 2, .cl 0 1, .p1 3,
    .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2,
    .bk 0, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 4, .cl 0 1, .cl 0 2, .cl 0 1,
    .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .bk 0, .cl 0 1, .p1 3, .cl 0 1,
    .cl 0 3, .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3, .cl 0 1,
    .p1 11, .cl 0 1, .cl 0 3, .bk 0, .cl 0 2, .cl 0 3, .cl 0 2, .cl 0 3, .cl 0 2, .cl 0 3, .cl 0 2,
    .cl 0 3, .cl 0 2, .cl 0 3, .cl 0 2, .cl 0 3, .cl 0 2, .cl 0 4, .cl 0 2, .cl 0 3, .bk 0,
    .cl 0 5, .cl 0 10, .cl 0 5, .p1 3, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10,
    .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5, .p1 5, .bk 0, .cl 0 56, .cl 0 64, .cl 0 66,
    .cl 0 56, .cl 0 64, .cl 0 66, .cl 0 56, .cl 0 64, .cl 0 56, .cl 0 64, .cl 0 56, .cl 0 64,
    .cl 0 56, .cl 0 64, .p1 2, .cl 0 56, .cl 0 64, .cl 0 66, .cl 0 56, .cl 0 64, .bk 0, .cl 0 57,
    .cl 0 74, .cl 0 81, .p1 14, .cl 0 57, .cl 0 74, .cl 0 57, .cl 0 74, .cl 0 57, .cl 0 74,
    .cl 0 57, .cl 0 74, .p1 2, .cl 0 57, .cl 0 74, .cl 0 76, .cl 0 82, .p1 5, .cl 0 57, .cl 0 74,
    .cl 0 57, .cl 0 74, .cl 0 87, .bk 0, .cl 0 58, .cl 0 71, .p1 1, .cl 0 58, .cl 0 71, .cl 0 58,
    .cl 0 71, .cl 0 58, .cl 0 71, .cl 0 58, .cl 0 71, .cl 0 84, .p1 13, .cl 0 58, .cl 0 59,
    .cl 0 64, .cl 0 58, .cl 0 59, .cl 0 63, .cl 0 58, .cl 0 59, .p1 1, .bk 0, .cl 0 59, .cl 0 61,
    .cl 0 59, .cl 0 61, .cl 0 69, .cl 0 59, .cl 0 61, .cl 0 69, .cl 0 59, .cl 0 61, .cl 0 59,
    .cl 0 61, .cl 0 64, .cl 0 59, .cl 0 61, .p1 1, .cl 0 59, .cl 0 61, .cl 0 59, .cl 0 61, .bk 0,
    .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 20, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10,
    .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10, .bk 0, .cl 0 61, .cl 0 63, .cl 0 64,
    .cl 0 61, .cl 0 67, .cl 0 61, .cl 0 67, .cl 0 71, .cl 0 61, .cl 0 63, .cl 0 67, .cl 0 61,
    .cl 0 67, .cl 0 61, .cl 0 63, .p1 1, .cl 0 61, .cl 0 67, .p1 1, .cl 0 61, .cl 0 67, .bk 0,
    .cl 0 62, .cl 0 73, .cl 0 62, .cl 0 73, .cl 0 62, .cl 0 73, .cl 0 62, .cl 0 73, .p1 2,
    .cl 0 62, .cl 0 73, .cl 0 81, .cl 0 82, .p1 12, .cl 0 62, .cl 0 73, .cl 0 62, .cl 0 81,
    .cl 0 82, .p1 12, .cl 0 62, .cl 0 73, .cl 0 81, .bk 0, .cl 0 63, .cl 0 72, .cl 0 80, .cl 0 88,
    .p1 11, .cl 0 63, .cl 0 72, .cl 0 63, .cl 0 72, .cl 0 73, .cl 0 63, .cl 0 72, .p1 1, .cl 0 63,
    .cl 0 72, .cl 0 63, .cl 0 72, .cl 0 63, .cl 0 72, .cl 0 63, .cl 0 72, .cl 0 83, .p1 15, .bk 0,
    .cl 0 64, .cl 0 68, .cl 0 64, .cl 0 68, .cl 0 64, .cl 0 68, .p1 2, .cl 0 64, .cl 0 68,
    .cl 0 81, .cl 0 64, .cl 0 68, .cl 0 64, .cl 0 68, .cl 0 81, .p1 11, .cl 0 64, .cl 0 68,
    .cl 0 74, .cl 0 64, .cl 0 68, .bk 0, .cl 0 5, .cl 0 15, .cl 0 5, .cl 0 15, .cl 0 5, .cl 0 15,
    .cl 0 5, .cl 0 15, .cl 0 5, .cl 0 15, .cl 0 5, .p1 4, .cl 0 5, .cl 0 15, .cl 0 5, .p1 3, .bk 0,
    .cl 0 66, .cl 0 68, .cl 0 69, .cl 0 66, .cl 0 68, .p1 2, .cl 0 66, .cl 0 81, .cl 0 84, .p1 6,
    .cl 0 66, .cl 0 81, .p1 9, .cl 0 66, .cl 0 68, .cl 0 74, .cl 0 66, .cl 0 98, .cl 0 99,
    .cl 0 107, .cl 0 108, .cl 0 110, .cl 0 66, .cl 0 81, .p1 3, .cl 0 66, .cl 0 68, .cl 0 72,
    .bk 0, .cl 0 67, .cl 0 94, .p1 7, .cl 0 67, .cl 0 72, .cl 0 81, .cl 0 67, .cl 0 86, .cl 0 87,
    .cl 0 93, .p1 6, .cl 0 67, .cl 0 86, .cl 0 92, .p1 13, .cl 0 67, .cl 0 72, .cl 0 74, .cl 0 67,
    .cl 0 72, .cl 0 86, .p1 5, .cl 0 67, .cl 0 72, .p1 1, .cl 0 67, .cl 0 94, .p1 3, .bk 0,
    .cl 0 68, .cl 0 73, .cl 0 88, .cl 0 90, .cl 0 92, .cl 0 68, .cl 0 73, .cl 0 84, .cl 0 68,
    .cl 0 73, .p1 2, .cl 0 68, .cl 0 89, .cl 0 93, .p1 14, .cl 0 68, .cl 0 91, .p1 10, .cl 0 68,
    .cl 0 73, .cl 0 89, .p1 5, .cl 0 68, .cl 0 89, .cl 0 99, .cl 0 108, .cl 0 68, .cl 0 91, .p1 3,
    .bk 0, .cl 0 69, .cl 0 97, .cl 0 108, .p1 10, .cl 0 69, .cl 0 84, .cl 0 99, .cl 0 101,
    .cl 0 69, .cl 0 84, .p1 3, .cl 0 69, .cl 0 84, .p1 8, .cl 0 69, .cl 0 109, .cl 0 118, .cl 0 69,
    .cl 0 111, .p1 3, .cl 0 69, .cl 0 84, .cl 0 98, .cl 0 69, .cl 0 96, .cl 0 97, .bk 0, .cl 0 10,
    .cl 0 15, .cl 0 10, .cl 0 15, .cl 0 10, .cl 0 15, .cl 0 10, .cl 0 15, .cl 0 10, .cl 0 15,
    .cl 0 10, .cl 0 20, .cl 0 10, .cl 0 15, .cl 0 10, .cl 0 15, .bk 0, .cl 0 71, .cl 0 97,
    .cl 0 98, .cl 0 99, .cl 0 71, .cl 0 83, .cl 0 85, .p1 7, .cl 0 71, .cl 0 97, .p1 13, .cl 0 88,
    .cl 0 113, .cl 0 71, .cl 0 83, .cl 0 88, .cl 0 90, .cl 0 94, .cl 0 71, .cl 0 83, .cl 0 90,
    .cl 0 71, .cl 0 83, .cl 0 85, .p1 7, .cl 0 71, .cl 0 109, .p1 3, .bk 0, .cl 0 72, .cl 0 92,
    .cl 0 93, .p1 11, .cl 0 72, .cl 0 86, .cl 0 88, .p1 6, .cl 0 72, .cl 0 108, .p1 3, .cl 0 72,
    .cl 0 86, .cl 0 92, .cl 0 93, .p1 11, .cl 0 72, .cl 0 88, .cl 0 89, .p1 3, .cl 0 72, .cl 0 92,
    .p1 15, .cl 0 86, .cl 0 111, .cl 0 72, .cl 0 86, .cl 0 88, .cl 0 96, .p1 8, .bk 0, .cl 0 73,
    .cl 0 93, .p1 3, .cl 0 73, .cl 0 74, .cl 0 83, .cl 0 87, .cl 0 73, .cl 0 74, .cl 0 86,
    .cl 0 73, .cl 0 74, .p1 2, .cl 0 73, .cl 0 87, .cl 0 93, .cl 0 94, .cl 0 73, .cl 0 93, .p1 12,
    .cl 0 73, .cl 0 74, .cl 0 87, .p1 6, .cl 0 73, .cl 0 87, .cl 0 89, .cl 0 99, .p1 9, .bk 0,
    .cl 0 74, .cl 0 82, .cl 0 87, .cl 0 89, .p1 10, .cl 0 74, .cl 0 82, .cl 0 85, .p1 10, .cl 0 74,
    .cl 0 82, .cl 0 85, .p1 10, .cl 0 87, .cl 0 112, .cl 0 74, .cl 0 87, .cl 0 89, .p1 9, .cl 0 74,
    .cl 0 82, .cl 0 90, .cl 0 74, .cl 0 98, .p1 14, .cl 0 74, .cl 0 106, .p1 3, .p1 0, .bk 0,
    .cl 0 1, .p1 11, .cl 0 1, .cl 0 2, .cl 0 1, .p1 3, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1,
    .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .bk 0, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2,
    .cl 0 1, .cl 0 4, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2,
    .cl 0 1, .cl 0 2, .bk 0, .cl 0 1, .p1 3, .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3,
    .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3, .cl 0 1, .p1 6, .cl 0 1, .cl 0 3, .bk 0, .cl 0 2, .cl 0 3,
    .cl 0 2, .cl 0 3, .cl 0 2, .cl 0 3, .cl 0 2, .cl 0 3, .cl 0 2, .cl 0 3, .cl 0 2, .cl 0 3,
    .cl 0 2, .cl 0 4, .cl 0 2, .cl 0 3, .bk 0, .cl 0 5, .cl 0 10, .cl 0 5, .p1 3, .cl 0 5,
    .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5,
    .p1 4, .bk 0, .cl 0 62, .cl 0 89, .cl 0 91, .cl 0 62, .cl 0 68, .cl 0 73, .cl 0 74, .p1 3,
    .cl 0 62, .cl 0 68, .cl 0 82, .p1 2, .cl 0 62, .cl 0 89, .cl 0 62, .cl 0 89, .cl 0 62,
    .cl 0 68, .cl 0 73, .cl 0 84, .p1 4, .cl 0 62, .cl 0 68, .cl 0 73, .p1 5, .cl 0 62, .cl 0 89,
    .bk 0, .cl 0 64, .cl 0 66, .cl 0 68, .cl 0 73, .p1 3, .cl 0 64, .cl 0 66, .cl 0 87, .p1 2,
    .cl 0 64, .cl 0 66, .cl 0 81, .p1 2, .cl 0 64, .cl 0 66, .cl 0 74, .p1 5, .cl 0 64, .cl 0 68,
    .cl 0 69, .p1 3, .cl 0 64, .cl 0 66, .cl 0 68, .p1 11, .cl 0 64, .cl 0 81, .cl 0 83, .cl 0 64,
    .cl 0 81, .p1 2, .bk 0, .cl 0 61, .cl 0 63, .p1 3, .cl 0 61, .cl 0 63, .p1 8, .cl 0 61,
    .cl 0 69, .cl 0 84, .cl 0 88, .cl 0 92, .p1 7, .cl 0 61, .cl 0 69, .cl 0 71, .p1 5, .cl 0 61,
    .cl 0 63, .cl 0 66, .cl 0 61, .cl 0 67, .cl 0 69, .cl 0 61, .cl 0 69, .cl 0 84, .p1 1,
    .cl 0 61, .cl 0 63, .cl 0 68, .cl 0 69, .cl 0 71, .p1 15, .bk 0, .cl 0 63, .cl 0 72, .cl 0 74,
    .cl 0 85, .p1 12, .cl 0 63, .cl 0 67, .cl 0 86, .p1 1, .cl 0 63, .cl 0 67, .cl 0 72, .p1 5,
    .cl 0 63, .cl 0 86, .cl 0 63, .cl 0 67, .cl 0 69, .p1 15, .cl 0 63, .cl 0 67, .cl 0 72,
    .cl 0 81, .p1 4, .cl 0 63, .cl 0 67, .cl 0 83, .p1 1, .cl 0 63, .cl 0 86, .bk 0, .cl 0 5,
    .cl 0 10, .cl 0 5, .cl 0 20, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5,
    .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10, .bk 0, .cl 0 72, .cl 0 88, .cl 0 89, .cl 0 58,
    .cl 0 67, .cl 0 72, .cl 0 58, .cl 0 72, .cl 0 92, .p1 1, .cl 0 58, .cl 0 84, .cl 0 58,
    .cl 0 72, .cl 0 88, .p1 1, .cl 0 58, .cl 0 63, .cl 0 72, .cl 0 72, .cl 0 92, .p1 1, .cl 0 58,
    .cl 0 72, .cl 0 84, .p1 8, .bk 0, .cl 0 56, .cl 0 74, .cl 0 89, .p1 2, .cl 0 56, .cl 0 74,
    .cl 0 82, .p1 2, .cl 0 56, .cl 0 73, .cl 0 74, .cl 0 74, .cl 0 98, .p1 2, .cl 0 74, .cl 0 82,
    .cl 0 84, .cl 0 74, .cl 0 82, .cl 0 88, .cl 0 56, .cl 0 57, .cl 0 74, .cl 0 56, .cl 0 74,
    .cl 0 98, .p1 2, .bk 0, .cl 0 59, .cl 0 71, .cl 0 83, .cl 0 86, .p1 7, .cl 0 59, .cl 0 71,
    .cl 0 83, .p1 1, .cl 0 71, .cl 0 83, .p1 1, .cl 0 71, .cl 0 97, .p1 1, .cl 0 59, .cl 0 71,
    .cl 0 86, .p1 1, .cl 0 71, .cl 0 83, .cl 0 87, .cl 0 59, .cl 0 71, .cl 0 72, .p1 11, .cl 0 59,
    .cl 0 71, .cl 0 94, .cl 0 96, .p1 5, .bk 0, .cl 0 57, .cl 0 73, .cl 0 81, .cl 0 84, .cl 0 87,
    .cl 0 57, .cl 0 68, .cl 0 73, .cl 0 73, .cl 0 74, .p1 3, .cl 0 57, .cl 0 81, .cl 0 73,
    .cl 0 93, .cl 0 57, .cl 0 62, .cl 0 73, .cl 0 57, .cl 0 73, .cl 0 81, .cl 0 82, .cl 0 73,
    .cl 0 74, .p1 12, .bk 0, .cl 0 5, .cl 0 15, .cl 0 5, .cl 0 15, .cl 0 5, .cl 0 15, .cl 0 5,
    .cl 0 15, .cl 0 5, .cl 0 15, .cl 0 5, .p1 5, .cl 0 5, .cl 0 15, .cl 0 5, .p1 3, .bk 0,
    .cl 0 57, .cl 0 87, .cl 0 57, .cl 0 87, .cl 0 88, .cl 0 57, .cl 0 74, .cl 0 82, .cl 0 57,
    .cl 0 73, .cl 0 81, .p1 2, .cl 0 57, .cl 0 87, .cl 0 57, .cl 0 74, .cl 0 79, .p1 3, .cl 0 57,
    .cl 0 74, .cl 0 79, .cl 0 57, .cl 0 73, .cl 0 74, .p1 6, .bk 0, .cl 0 59, .cl 0 69, .p1 13,
    .cl 0 59, .cl 0 83, .cl 0 59, .cl 0 61, .cl 0 62, .cl 0 68, .p1 11, .cl 0 59, .cl 0 61,
    .cl 0 67, .p1 7, .cl 0 59, .cl 0 61, .cl 0 70, .p1 7, .cl 0 59, .cl 0 83, .cl 0 59, .cl 0 69,
    .cl 0 71, .cl 0 72, .cl 0 59, .cl 0 69, .p1 3, .bk 0, .cl 0 56, .cl 0 64, .cl 0 70, .p1 10,
    .cl 0 56, .cl 0 82, .cl 0 56, .cl 0 66, .cl 0 69, .cl 0 76, .p1 2, .cl 0 56, .cl 0 64,
    .cl 0 68, .p1 10, .cl 0 56, .cl 0 66, .p1 14, .cl 0 56, .cl 0 82, .cl 0 56, .cl 0 82, .cl 0 56,
    .cl 0 66, .p1 3, .bk 0, .cl 0 58, .cl 0 88, .cl 0 58, .cl 0 59, .cl 0 74, .cl 0 80, .p1 1,
    .cl 0 58, .cl 0 59, .p1 3, .cl 0 58, .cl 0 59, .p1 15, .cl 0 58, .cl 0 88, .cl 0 58, .cl 0 71,
    .cl 0 76, .p1 3, .cl 0 58, .cl 0 59, .cl 0 73, .cl 0 58, .cl 0 71, .cl 0 72, .bk 0, .cl 0 10,
    .cl 0 15, .cl 0 10, .cl 0 15, .cl 0 10, .cl 0 15, .cl 0 10, .cl 0 15, .cl 0 10, .cl 0 15,
    .cl 0 10, .cl 0 20, .cl 0 10, .cl 0 15, .cl 0 10, .cl 0 15, .bk 0, .cl 0 67, .cl 0 72,
    .cl 0 73, .cl 0 74, .cl 0 67, .cl 0 72, .p1 3, .cl 0 67, .cl 0 72, .p1 7, .cl 0 63, .cl 0 67,
    .cl 0 83, .cl 0 87, .cl 0 63, .cl 0 67, .cl 0 69, .p1 6, .cl 0 67, .cl 0 72, .cl 0 73,
    .cl 0 76, .cl 0 77, .p1 1, .cl 0 63, .cl 0 83, .cl 0 63, .cl 0 67, .cl 0 86, .p1 1, .bk 0,
    .cl 0 61, .cl 0 69, .cl 0 84, .p1 1, .cl 0 61, .cl 0 88, .cl 0 69, .cl 0 84, .cl 0 61,
    .cl 0 69, .cl 0 71, .p1 7, .cl 0 69, .cl 0 84, .p1 1, .cl 0 69, .cl 0 84, .cl 0 69, .cl 0 84,
    .cl 0 69, .cl 0 84, .bk 0, .cl 0 66, .cl 0 68, .p1 3, .cl 0 64, .cl 0 87, .cl 0 66, .cl 0 81,
    .cl 0 64, .cl 0 66, .cl 0 68, .cl 0 74, .cl 0 66, .cl 0 68, .cl 0 69, .cl 0 71, .cl 0 72,
    .p1 3, .cl 0 66, .cl 0 68, .p1 9, .cl 0 66, .cl 0 81, .cl 0 66, .cl 0 81, .bk 0, .cl 0 62,
    .cl 0 66, .cl 0 68, .cl 0 68, .cl 0 73, .p1 3, .cl 0 62, .cl 0 82, .cl 0 62, .cl 0 68,
    .cl 0 82, .cl 0 88, .cl 0 62, .cl 0 64, .cl 0 68, .cl 0 68, .cl 0 73, .cl 0 84, .cl 0 68,
    .cl 0 73, .p1 10, .cl 0 62, .cl 0 82, .cl 0 83, .p1 4, .p1 0, .bk 0, .cl 0 1, .p1 4, .cl 0 1,
    .cl 0 2, .cl 0 1, .p1 3, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1,
    .cl 0 2, .cl 0 1, .cl 0 2, .bk 0, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 4,
    .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2, .cl 0 1, .cl 0 2,
    .bk 0, .cl 0 1, .p1 3, .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3, .cl 0 1, .cl 0 3,
    .cl 0 1, .cl 0 3, .cl 0 1, .p1 5, .cl 0 1, .cl 0 3, .bk 0, .cl 0 2, .cl 0 3, .cl 0 2, .cl 0 3,
    .cl 0 2, .cl 0 3, .cl 0 2, .cl 0 3, .cl 0 2, .cl 0 3, .cl 0 2, .cl 0 3, .cl 0 2, .cl 0 4,
    .cl 0 2, .cl 0 3, .bk 0, .cl 0 5, .cl 0 10, .cl 0 5, .p1 3, .cl 0 5, .cl 0 10, .cl 0 5,
    .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5, .p1 6, .bk 0,
    .cl 0 37, .cl 0 43, .cl 0 56, .p1 4, .cl 0 37, .cl 0 43, .cl 0 48, .cl 0 49, .p1 3, .cl 0 37,
    .cl 0 43, .cl 0 56, .p1 10, .cl 0 37, .cl 0 43, .cl 0 56, .p1 14, .cl 0 37, .cl 0 48, .cl 0 51,
    .p1 7, .cl 0 37, .cl 0 48, .cl 0 51, .cl 0 37, .cl 0 43, .cl 0 48, .p1 11, .cl 0 37, .cl 0 43,
    .cl 0 56, .p1 11, .bk 0, .cl 0 39, .cl 0 41, .cl 0 43, .cl 0 48, .p1 3, .cl 0 39, .cl 0 41,
    .cl 0 56, .p1 12, .cl 0 39, .cl 0 56, .p1 12, .cl 0 39, .cl 0 41, .cl 0 49, .p1 11, .cl 0 39,
    .cl 0 43, .cl 0 44, .p1 3, .cl 0 39, .cl 0 41, .cl 0 43, .p1 4, .cl 0 39, .cl 0 41, .cl 0 57,
    .p1 4, .cl 0 39, .cl 0 41, .cl 0 57, .p1 6, .bk 0, .cl 0 36, .cl 0 38, .p1 3, .cl 0 36,
    .cl 0 38, .p1 13, .cl 0 36, .cl 0 44, .cl 0 58, .p1 4, .cl 0 36, .cl 0 44, .cl 0 46, .p1 11,
    .cl 0 36, .cl 0 38, .cl 0 41, .cl 0 36, .cl 0 42, .cl 0 44, .cl 0 36, .cl 0 44, .cl 0 58,
    .p1 15, .cl 0 36, .cl 0 38, .cl 0 43, .cl 0 44, .cl 0 46, .p1 7, .bk 0, .cl 0 38, .cl 0 47,
    .cl 0 49, .cl 0 52, .p1 8, .cl 0 38, .cl 0 42, .cl 0 47, .cl 0 54, .cl 0 55, .p1 7, .cl 0 38,
    .cl 0 42, .cl 0 47, .p1 11, .cl 0 38, .cl 0 42, .cl 0 59, .p1 13, .cl 0 38, .cl 0 42, .cl 0 44,
    .p1 7, .cl 0 38, .cl 0 47, .cl 0 54, .cl 0 38, .cl 0 42, .cl 0 59, .p1 7, .cl 0 38, .cl 0 42,
    .cl 0 59, .p1 11, .bk 0, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 20, .cl 0 5, .cl 0 10, .cl 0 5,
    .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10, .cl 0 5, .cl 0 10, .bk 0,
    .cl 0 47, .cl 0 58, .cl 0 33, .cl 0 42, .cl 0 47, .cl 0 33, .cl 0 61, .cl 0 47, .cl 0 58,
    .cl 0 47, .cl 0 58, .cl 0 59, .p1 4, .cl 0 33, .cl 0 38, .cl 0 47, .cl 0 47, .cl 0 58,
    .cl 0 47, .cl 0 58, .bk 0, .cl 0 49, .cl 0 56, .cl 0 49, .cl 0 57, .p1 10, .cl 0 31, .cl 0 48,
    .cl 0 49, .cl 0 49, .cl 0 56, .cl 0 49, .cl 0 56, .cl 0 49, .cl 0 56, .cl 0 31, .cl 0 32,
    .cl 0 49, .cl 0 31, .cl 0 49, .cl 0 57, .cl 0 59, .bk 0, .cl 0 46, .cl 0 58, .p1 7, .cl 0 46,
    .cl 0 58, .p1 7, .cl 0 46, .cl 0 58, .cl 0 59, .p1 1, .cl 0 46, .cl 0 59, .cl 0 34, .cl 0 46,
    .cl 0 58, .p1 7, .cl 0 46, .cl 0 59, .cl 0 34, .cl 0 46, .cl 0 47, .p1 4, .cl 0 46, .cl 0 59,
    .cl 0 61, .p1 8, .bk 0, .cl 0 48, .cl 0 62, .p1 9, .cl 0 32, .cl 0 43, .cl 0 48, .cl 0 48,
    .cl 0 49, .p1 3, .cl 0 48, .cl 0 57, .cl 0 48, .cl 0 57, .cl 0 32, .cl 0 37, .cl 0 48,
    .cl 0 48, .cl 0 49, .cl 0 63, .p1 3, .cl 0 48, .cl 0 49, .p1 10, .bk 0, .cl 0 5, .cl 0 15,
    .cl 0 5, .cl 0 15, .cl 0 5, .cl 0 15, .cl 0 5, .cl 0 15, .cl 0 5, .cl 0 15, .cl 0 5, .p1 11,
    .cl 0 5, .cl 0 15, .cl 0 5, .p1 3, .bk 0, .cl 0 32, .cl 0 48, .cl 0 57, .p1 2, .cl 0 32,
    .cl 0 48, .cl 0 57, .p1 2, .cl 0 32, .cl 0 48, .cl 0 57, .cl 0 32, .cl 0 48, .cl 0 57,
    .cl 0 32, .cl 0 48, .cl 0 57, .cl 0 32, .cl 0 48, .cl 0 57, .p1 2, .cl 0 32, .cl 0 48,
    .cl 0 57, .p1 2, .cl 0 32, .cl 0 48, .cl 0 49, .p1 5, .bk 0, .cl 0 34, .cl 0 44, .p1 15,
    .cl 0 34, .cl 0 46, .cl 0 59, .p1 1, .cl 0 34, .cl 0 36, .cl 0 37, .cl 0 43, .p1 4, .cl 0 34,
    .cl 0 36, .cl 0 42, .p1 8, .cl 0 34, .cl 0 36, .cl 0 45, .p1 8, .cl 0 34, .cl 0 46, .cl 0 59,
    .cl 0 34, .cl 0 44, .cl 0 46, .cl 0 47, .cl 0 34, .cl 0 44, .p1 3, .bk 0, .cl 0 31, .cl 0 39,
    .cl 0 45, .p1 9, .cl 0 31, .cl 0 49, .cl 0 56, .p1 2, .cl 0 31, .cl 0 49, .cl 0 56, .p1 2,
    .cl 0 31, .cl 0 39, .cl 0 43, .p1 9, .cl 0 31, .cl 0 41, .p1 12, .cl 0 31, .cl 0 49, .cl 0 56,
    .cl 0 31, .cl 0 39, .cl 0 53, .p1 13, .cl 0 31, .cl 0 41, .p1 3, .bk 0, .cl 0 33, .cl 0 47,
    .cl 0 58, .cl 0 33, .cl 0 34, .cl 0 49, .cl 0 52, .cl 0 33, .cl 0 34, .p1 3, .cl 0 33,
    .cl 0 34, .p1 7, .cl 0 33, .cl 0 47, .cl 0 58, .p1 1, .cl 0 33, .cl 0 46, .cl 0 56, .p1 8,
    .cl 0 33, .cl 0 34, .cl 0 48, .cl 0 33, .cl 0 46, .cl 0 47, .bk 0, .cl 0 10, .cl 0 15,
    .cl 0 10, .cl 0 15, .cl 0 10, .cl 0 15, .cl 0 10, .cl 0 15, .cl 0 10, .cl 0 15, .cl 0 10,
    .cl 0 20, .cl 0 10, .cl 0 15, .cl 0 10, .cl 0 15, .bk 0, .cl 0 42, .cl 0 47, .cl 0 48,
    .cl 0 49, .cl 0 42, .cl 0 47, .p1 3, .cl 0 42, .cl 0 47, .p1 8, .cl 0 42, .cl 0 63, .cl 0 38,
    .cl 0 42, .cl 0 44, .p1 5, .cl 0 42, .cl 0 47, .cl 0 48, .cl 0 51, .p1 4, .cl 0 42, .cl 0 61,
    .p1 13, .cl 0 42, .cl 0 61, .p1 13, .bk 0, .cl 0 44, .cl 0 61, .cl 0 67, .p1 7, .cl 0 44,
    .cl 0 61, .cl 0 44, .cl 0 61, .cl 0 63, .p1 5, .cl 0 36, .cl 0 44, .cl 0 46, .p1 8, .cl 0 36,
    .cl 0 58, .p1 3, .cl 0 44, .cl 0 61, .cl 0 44, .cl 0 61, .cl 0 36, .cl 0 44, .cl 0 61,
    .cl 0 63, .p1 5, .bk 0, .cl 0 41, .cl 0 43, .p1 3, .cl 0 41, .cl 0 64, .cl 0 41, .cl 0 64,
    .cl 0 39, .cl 0 41, .cl 0 43, .cl 0 49, .cl 0 41, .cl 0 43, .cl 0 44, .cl 0 46, .cl 0 47,
    .p1 3, .cl 0 41, .cl 0 43, .p1 14, .cl 0 39, .cl 0 41, .cl 0 66, .cl 0 39, .cl 0 41, .cl 0 64,
    .cl 0 66, .bk 0, .cl 0 37, .cl 0 41, .cl 0 43, .cl 0 43, .cl 0 48, .p1 3, .cl 0 43, .cl 0 62,
    .cl 0 43, .cl 0 62, .cl 0 37, .cl 0 39, .cl 0 43, .cl 0 37, .cl 0 43, .cl 0 48, .cl 0 63,
    .cl 0 43, .cl 0 48, .p1 9, .cl 0 43, .cl 0 64, .p1 14]

private theorem cdOK337 : CdOK ⟨3, 0, 3, 7⟩ tab33 cd337 where
  size := by decide +kernel
  rep := by decide +kernel
  orb := by decide +kernel
  gp := by decide +kernel
  nu := by decide +kernel
  al := by decide +kernel
  be := by decide +kernel
  m := by decide +kernel

private theorem run337 : run cd337 3729 [(z16, z16)] cert337 = true := by
  decide +kernel

private theorem case337 :
    (tablesOKb ⟨3, 0, 3, 7⟩ (orbitData ⟨3, 0, 3, 7⟩) && g8b ⟨3, 0, 3, 7⟩ &&
      search ⟨3, 0, 3, 7⟩ (orbitData ⟨3, 0, 3, 7⟩) 17
        (Array.replicate (orbitData ⟨3, 0, 3, 7⟩).reps.size none)) = true := by
  rw [orbitData_congr (P := ⟨3, 0, 3, 7⟩) (Q := ⟨3, 0, 3, 3⟩) rfl, orbitData33]
  refine search_case ?_ ?_ cdOK337 run337
  · rw [tablesOKb_congr (P := ⟨3, 0, 3, 7⟩) (Q := ⟨3, 0, 3, 3⟩) rfl]
    exact tablesOKb33
  · rw [g8b_congr (P := ⟨3, 0, 3, 7⟩) (Q := ⟨3, 0, 3, 3⟩) rfl]
    exact g8b33

private theorem params_cases : ∀ ν α β : ZMod 5, ν * ν = -1 →
    (gen ν α β)^[4] (0, 1, 0) = (0, -1, 0) → (gen ν α β)^[4] (0, 0, 1) = (0, 0, -1) →
    (ν = 2 ∨ ν = 3) ∧ α = 0 ∧ (β = 2 ∨ β = 3) := by
  decide +kernel

private theorem search_all_0 : ∀ ν α β : ZMod 5, ∀ m ∈ [3, 7], ν * ν = -1 →
    (gen ν α β)^[4] (0, 1, 0) = (0, -1, 0) → (gen ν α β)^[4] (0, 0, 1) = (0, 0, -1) →
    (tablesOKb ⟨ν, α, β, m⟩ (orbitData ⟨ν, α, β, m⟩) && g8b ⟨ν, α, β, m⟩ &&
      search ⟨ν, α, β, m⟩ (orbitData ⟨ν, α, β, m⟩) 17
        (Array.replicate (orbitData ⟨ν, α, β, m⟩).reps.size none)) = true := by
  intro ν α β m hm hν h1 h2
  obtain ⟨hν', rfl, hβ⟩ := params_cases ν α β hν h1 h2
  have hm' : m = 3 ∨ m = 7 := by simpa using hm
  rcases hν' with rfl | rfl <;> rcases hβ with rfl | rfl <;> rcases hm' with rfl | rfl
  exacts [case223, case227, case233, case237, case323, case327, case333, case337]

end CertificateChecks.Batch8052

namespace Certificates

open CertificateChecks

open CFSG CFSG.UnitaryThreeRecognition CFSG.UnitaryThreeRecognition.AbelianQFive in
theorem certificate8052 : ∀ ν α β : ZMod 5, ∀ m ∈ [3, 7], ν * ν = -1 →
    (gen ν α β)^[4] (0, 1, 0) = (0, -1, 0) → (gen ν α β)^[4] (0, 0, 1) = (0, 0, -1) →
    (tablesOKb ⟨ν, α, β, m⟩ (orbitData ⟨ν, α, β, m⟩) && g8b ⟨ν, α, β, m⟩ &&
      search ⟨ν, α, β, m⟩ (orbitData ⟨ν, α, β, m⟩) 17
        (Array.replicate (orbitData ⟨ν, α, β, m⟩).reps.size none)) = true := by
  exact CertificateChecks.Batch8052.search_all_0

end Certificates
