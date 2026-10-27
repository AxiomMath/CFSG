module

public import CFSG.Permutation.FinPack
public import Mathlib.Tactic.Group

public section

namespace CFSG.Quasithin.H13.L32A.C.Alt7Pack

open Equiv CFSG.Permutation.FinPack

variable {n : ℕ}

@[expose] noncomputable def closedK (n e : ℕ) (C : List ℕ) : Bool :=
  memK e C && (allK (fun a => allK (fun b => memK (mulK n a b) C) C) C &&
    allK (fun a => anyK (fun b => Nat.beq (mulK n a b) e) C) C)

@[expose] noncomputable def commK (n e : ℕ) (b : Bool) (ev : ℕ → Bool) (S V : List ℕ) : Bool :=
  allK (fun g => allK (fun x =>
    !(Nat.beq (mulK n x (mulK n x x)) e) || !(ev g) ||
      anyK (fun v => Nat.beq (mulK n g x)
        (mulK n v (Bool.rec (motive := fun _ => ℕ) (mulK n x g) (mulK n x (mulK n x g)) b))) V)
    S) S

theorem closed_of_K (hn : n ≤ 16) (L : List (Perm (Fin n))) (C : List ℕ) (e : ℕ)
    (hC : (L.map enc == C) = true) (he : enc (1 : Perm (Fin n)) = e) (h : closedK n e C = true) :
    (1 : Perm (Fin n)) ∈ L ∧ (∀ a ∈ L, ∀ b ∈ L, a * b ∈ L) ∧ ∀ a ∈ L, a⁻¹ ∈ L := by
  rw [beq_iff_eq] at hC
  subst hC he
  simp only [closedK, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨(mem_iff_enc hn L 1).2 (memK_iff.1 h1), fun a ha b hb => ?_, fun a ha => ?_⟩
  · have hab := memK_iff.1 (allK_iff.1 (allK_iff.1 h2 _ (List.mem_map.2 ⟨a, ha, rfl⟩)) _
      (List.mem_map.2 ⟨b, hb, rfl⟩))
    rw [← enc_mul hn] at hab
    exact (mem_iff_enc hn L _).2 hab
  · obtain ⟨c, hc, hac⟩ := anyK_iff.1 (allK_iff.1 h3 _ (List.mem_map.2 ⟨a, ha, rfl⟩))
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hc
    rw [← enc_mul hn, Nat.beq_eq] at hac
    rw [inv_eq_of_mul_eq_one_right (enc_inj hn hac)]
    exact hb

theorem commK_entry (hn : n ≤ 16) {S V : List (Perm (Fin n))} {Sc Vc : List ℕ} {e : ℕ}
    {b : Bool} {ev : ℕ → Bool} (hS : (S.map enc == Sc) = true) (hV : (V.map enc == Vc) = true)
    (he : enc (1 : Perm (Fin n)) = e) (h : commK n e b ev Sc Vc = true)
    {g x : Perm (Fin n)} (hg : g ∈ S) (hx : x ∈ S) (hx3 : x ^ 3 = 1) (hev : ev (enc g) = true) :
    ∃ w ∈ V, enc (g * x) = mulK n (enc w) (Bool.rec (motive := fun _ => ℕ)
      (mulK n (enc x) (enc g)) (mulK n (enc x) (mulK n (enc x) (enc g))) b) := by
  rw [beq_iff_eq] at hS hV
  subst hS hV he
  have h1 := allK_iff.1 (allK_iff.1 h _ (List.mem_map.2 ⟨g, hg, rfl⟩)) _
    (List.mem_map.2 ⟨x, hx, rfl⟩)
  rw [← enc_mul hn x x, ← enc_mul hn x (x * x), ← pow_three, hx3, hev] at h1
  simp only [Nat.beq_refl, Bool.not_true, Bool.false_or] at h1
  obtain ⟨c, hc, hgc⟩ := anyK_iff.1 h1
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hc
  rw [Nat.beq_eq] at hgc
  exact ⟨w, hw, (enc_mul hn g x).trans hgc⟩

theorem commA_of_K (hn : n ≤ 16) (S V : List (Perm (Fin n))) (Sc Vc : List ℕ) (e : ℕ)
    (P : Perm (Fin n) → Prop) (ev : ℕ → Bool) (hev : ∀ g, P g → ev (enc g) = true)
    (hS : (S.map enc == Sc) = true) (hV : (V.map enc == Vc) = true)
    (he : enc (1 : Perm (Fin n)) = e) (h : commK n e false ev Sc Vc = true) :
    ∀ g ∈ S, ∀ x ∈ S, x ^ 3 = 1 → P g → g * x * g⁻¹ * x⁻¹ ∈ V := by
  intro g hg x hx hx3 hP
  obtain ⟨w, hw, hgx⟩ := commK_entry hn hS hV he h hg hx hx3 (hev g hP)
  change enc (g * x) = mulK n (enc w) (mulK n (enc x) (enc g)) at hgx
  rw [← enc_mul hn x g, ← enc_mul hn w] at hgx
  have e1 : g * x * g⁻¹ * x⁻¹ = w := by
    rw [enc_inj hn hgx]
    group
  rw [e1]
  exact hw

theorem commB_of_K (hn : n ≤ 16) (S V : List (Perm (Fin n))) (Sc Vc : List ℕ) (e : ℕ)
    (P : Perm (Fin n) → Prop) (ev : ℕ → Bool) (hev : ∀ g, P g → ev (enc g) = true)
    (hS : (S.map enc == Sc) = true) (hV : (V.map enc == Vc) = true)
    (he : enc (1 : Perm (Fin n)) = e) (h : commK n e true ev Sc Vc = true) :
    ∀ g ∈ S, ∀ x ∈ S, x ^ 3 = 1 → P g → g * x * g⁻¹ * x ∈ V := by
  intro g hg x hx hx3 hP
  obtain ⟨w, hw, hgx⟩ := commK_entry hn hS hV he h hg hx hx3 (hev g hP)
  change enc (g * x) = mulK n (enc w) (mulK n (enc x) (mulK n (enc x) (enc g))) at hgx
  rw [← enc_mul hn x g, ← enc_mul hn x (x * g), ← enc_mul hn w] at hgx
  have e1 : g * x * g⁻¹ * x = w * (x * (x * x)) := by
    rw [enc_inj hn hgx]
    simp only [mul_assoc, mul_inv_cancel_left]
  have hx3' : x * (x * x) = 1 := by
    rw [← pow_three]
    exact hx3
  rw [e1, hx3', mul_one]
  exact hw

@[expose] noncomputable def powK (n e c k : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) e (fun _ acc => mulK n c acc) k

theorem enc_pow (hn : n ≤ 16) (σ : Perm (Fin n)) (k : ℕ) :
    enc (σ ^ k) = powK n (enc (1 : Perm (Fin n))) (enc σ) k := by
  induction k with
  | zero =>
    change enc (σ ^ 0) = enc (1 : Perm (Fin n))
    rw [pow_zero]
  | succ k ih =>
    change _ = mulK n (enc σ) (powK n (enc (1 : Perm (Fin n))) (enc σ) k)
    rw [pow_succ', enc_mul hn, ih]

@[expose] noncomputable def powImpK (n e k m : ℕ) (S : List ℕ) : Bool :=
  allK (fun c => !(Nat.beq (powK n e c k) e) || Nat.beq (powK n e c m) e) S

theorem powImp_of_K (hn : n ≤ 16) (S : List (Perm (Fin n))) (Sc : List ℕ) (e k m : ℕ)
    (hS : (S.map enc == Sc) = true) (he : enc (1 : Perm (Fin n)) = e)
    (h : powImpK n e k m Sc = true) : ∀ x ∈ S, x ^ k = 1 → x ^ m = 1 := by
  rw [beq_iff_eq] at hS
  subst hS he
  intro x hx hxk
  have h1 := allK_iff.1 h _ (List.mem_map.2 ⟨x, hx, rfl⟩)
  rw [← enc_pow hn, ← enc_pow hn, hxk, Nat.beq_refl, Bool.not_true, Bool.false_or,
    Nat.beq_eq] at h1
  exact enc_inj hn h1

@[expose] noncomputable def evenOnK (c : ℕ) : Bool :=
  (Nat.beq (rd c 4) 4 && Nat.beq (rd c 5) 5) || ((Nat.beq (rd c 4) 5 && Nat.beq (rd c 5) 6) ||
    (Nat.beq (rd c 4) 6 && Nat.beq (rd c 5) 4))

theorem evenOnK_enc (g : Perm (Fin 7)) :
    evenOnK (enc g) = true ↔
      (g 4 = 4 ∧ g 5 = 5) ∨ (g 4 = 5 ∧ g 5 = 6) ∨ (g 4 = 6 ∧ g 5 = 4) := by
  have h4 : rd (enc g) 4 = ((g 4 : Fin 7) : ℕ) := rd_enc (by norm_num) g 4
  have h5 : rd (enc g) 5 = ((g 5 : Fin 7) : ℕ) := rd_enc (by norm_num) g 5
  simp only [evenOnK, h4, h5, Bool.or_eq_true, Bool.and_eq_true, Nat.beq_eq, Fin.ext_iff,
    Fin.val_ofNat, Fin.isValue]
  rfl

theorem not_evenOnK_enc (g : Perm (Fin 7))
    (h : ¬ ((g 4 = 4 ∧ g 5 = 5) ∨ (g 4 = 5 ∧ g 5 = 6) ∨ (g 4 = 6 ∧ g 5 = 4))) :
    (!evenOnK (enc g)) = true := by
  cases hc : evenOnK (enc g)
  · rfl
  · exact absurd ((evenOnK_enc g).1 hc) h

@[expose] def one7 : ℕ := 106181136

@[expose] def tsCodes : List ℕ :=
  [106181136, 105198096, 106172976, 105189936, 106177281, 105194241, 106169121, 105186081,
    106180626, 105197586, 106172466, 105189426, 106176771, 105193731, 106168611, 105185571]

@[expose] def taCodes : List ℕ :=
  [106181136, 105189936, 106177281, 105186081, 105197586, 106172466, 105193731, 106168611]

@[expose] def stabCodes : List ℕ :=
  [106181136, 73740816, 88486416, 90448656, 105194256, 72753936, 90452256, 105197856, 72757536,
    106173216, 73732896, 88478496, 106176816, 73736496, 88482096, 90444336, 105189936, 72749616,
    90452481, 105198081, 72757761, 106177281, 73736961, 88482561, 106180641, 73740321, 88485921,
    90440481, 105186081, 72745761, 90447921, 105193521, 72753201, 106168881, 73728561, 88474161,
    106180866, 73740546, 88486146, 90444546, 105190146, 72749826, 90451986, 105197586, 72757266,
    106169106, 73728786, 88474386, 106172466, 73732146, 88477746, 90439986, 105185586, 72745266,
    90448131, 105193731, 72753411, 106172931, 73732611, 88478211, 106176531, 73736211, 88481811,
    90440211, 105185811, 72745491, 90443811, 105189411, 72749091, 106168611, 73728291, 88473891]

@[expose] def v4Codes : List ℕ :=
  [106181136, 106177281, 106172466, 106168611]

@[expose] def raSCodes : List ℕ :=
  [106181136, 105198096, 106172976, 105189936, 103895616, 101929536, 103891536, 101925456,
    106177281, 105194241, 106169121, 105186081, 102781761, 100815681, 102777681, 100811601,
    106180626, 105197586, 106172466, 105189426, 103895106, 101929026, 103891026, 101924946,
    106176771, 105193731, 106168611, 105185571, 102781251, 100815171, 102777171, 100811091,
    103884036, 101917956, 102774036, 100807956, 103875876, 101909796, 102765876, 100799796,
    103883781, 101917701, 102773781, 100807701, 103875621, 101909541, 102765621, 100799541]

@[expose] def raACodes : List ℕ :=
  [106181136, 105189936, 103895616, 101925456, 106177281, 105186081, 102781761, 100811601,
    105197586, 106172466, 101929026, 103891026, 105193731, 106168611, 100815171, 102777171,
    103884036, 102774036, 101909796, 100799796, 101917701, 100807701, 103875621, 102765621]

@[expose] def rbSCodes : List ℕ :=
  [106181136, 105198096, 106177296, 105194256, 106180896, 105197856, 106173216, 105190176,
    106176816, 105193776, 106172976, 105189936, 106181121, 105198081, 106177281, 105194241,
    106180641, 105197601, 106169121, 105186081, 106176561, 105193521, 106168881, 105185841,
    106180866, 105197826, 106173186, 105190146, 106180626, 105197586, 106169106, 105186066,
    106172466, 105189426, 106168626, 105185586, 106176771, 105193731, 106172931, 105189891,
    106176531, 105193491, 106168851, 105185811, 106172451, 105189411, 106168611, 105185571]

@[expose] def rbACodes : List ℕ :=
  [106181136, 105194256, 105197856, 106173216, 106176816, 105189936, 105198081, 106177281,
    106180641, 105186081, 105193521, 106168881, 106180866, 105190146, 105197586, 106169106,
    106172466, 105185586, 105193731, 106172931, 106176531, 105185811, 105189411, 106168611]

@[expose] def rcSCodes : List ℕ :=
  [106181136, 90452496, 105198096, 73740816, 88486416, 72757776, 106172976, 90444336,
    105189936, 73732656, 88478256, 72749616, 106177281, 90448641, 105194241, 73736961,
    88482561, 72753921, 106169121, 90440481, 105186081, 73728801, 88474401, 72745761,
    106180626, 90451986, 105197586, 73740306, 88485906, 72757266, 106172466, 90443826,
    105189426, 73732146, 88477746, 72749106, 106176771, 90448131, 105193731, 73736451,
    88482051, 72753411, 106168611, 90439971, 105185571, 73728291, 88473891, 72745251]

@[expose] def rcACodes : List ℕ :=
  [106181136, 73740816, 88486416, 90444336, 105189936, 72749616, 106177281, 73736961,
    88482561, 90440481, 105186081, 72745761, 90451986, 105197586, 72757266, 106172466,
    73732146, 88477746, 90448131, 105193731, 72753411, 106168611, 73728291, 88473891]

@[expose] def s4Codes : List ℕ :=
  [106181136, 106177296, 106180896, 106173216, 106176816, 106172976, 106181121, 106177281,
    106180641, 106169121, 106176561, 106168881, 106180866, 106173186, 106180626, 106169106,
    106172466, 106168626, 106176771, 106172931, 106176531, 106168851, 106172451, 106168611]

end CFSG.Quasithin.H13.L32A.C.Alt7Pack
