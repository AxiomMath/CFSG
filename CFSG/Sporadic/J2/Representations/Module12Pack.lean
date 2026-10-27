module

public import CFSG.Certificates.Kernel.Misc.F2MatGroup
public import CFSG.Certificates.WordPresentation
public import CFSG.Sporadic.Bridge.Common
public import CFSG.Timmesfeld.Moufang.J2Mat

public section

namespace CFSG.Sporadic.J2.Module12Pack

open CFSG.KLie.CT CFSG.KC.M1F2 CFSG.KC.F2Mat CFSG.KC.WordPts CFSG.Certificates

@[expose] noncomputable def rowP (L : List ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) (nat_lit 0)
    (fun a _ ih => Nat.lor (Nat.land a (nat_lit 1)) (Nat.shiftLeft ih (nat_lit 1))) L

@[expose] noncomputable def packL (d : ℕ) (X : List (List ℕ)) : ℕ :=
  List.rec (motive := fun _ => ℕ) (nat_lit 0)
    (fun r _ ih => Nat.lor (rowP r) (Nat.shiftLeft ih d)) X

@[expose] noncomputable def wordK (d : ℕ) (P Q : ℕ → ℕ) (w : List (ℕ × Bool)) : ℕ :=
  List.rec (motive := fun _ => ℕ) (idF d)
    (fun l _ ih => mulF d (Prod.rec (motive := fun _ => ℕ)
      (fun i b => Bool.rec (motive := fun _ => ℕ) (Q i) (P i) b) l) ih) w

theorem wordK_nil (d : ℕ) (P Q : ℕ → ℕ) : wordK d P Q [] = idF d := rfl

theorem wordK_cons (d : ℕ) (P Q : ℕ → ℕ) (i : ℕ) (b : Bool) (w : List (ℕ × Bool)) :
    wordK d P Q ((i, b) :: w) = mulF d (if b then P i else Q i) (wordK d P Q w) := by
  cases b <;> rfl

@[expose] noncomputable def pick2 (a b : ℕ) (i : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) a (fun _ _ => b) i

@[expose] noncomputable def pick3 (a b c : ℕ) (i : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) a (fun k _ => Nat.rec (motive := fun _ => ℕ) b (fun _ _ => c) k) i

@[expose] noncomputable def selN (L : List ℕ) : ℕ → ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ) (fun _ => nat_lit 0)
    (fun a _ ih j => Nat.rec (motive := fun _ => ℕ) a (fun k _ => ih k) j) L

theorem selN_cons_zero (a : ℕ) (L : List ℕ) : selN (a :: L) 0 = a := rfl

theorem selN_cons_succ (a : ℕ) (L : List ℕ) (n : ℕ) : selN (a :: L) (n + 1) = selN L n := rfl

@[expose] def invW (w : List (ℕ × Bool)) : List (ℕ × Bool) := (w.map fun l => (l.1, !l.2)).reverse

theorem wordProd_cons {G : Type*} [Group G] (x : ℕ → G) (i : ℕ) (b : Bool) (w : List (ℕ × Bool)) :
    CFSG.Sporadic.Bridge.wordProd x ((i, b) :: w) =
      (if b then x i else (x i)⁻¹) * CFSG.Sporadic.Bridge.wordProd x w := by
  simp [CFSG.Sporadic.Bridge.wordProd]

theorem wordProd_append {G : Type*} [Group G] (x : ℕ → G) (u v : List (ℕ × Bool)) :
    CFSG.Sporadic.Bridge.wordProd x (u ++ v) =
      CFSG.Sporadic.Bridge.wordProd x u * CFSG.Sporadic.Bridge.wordProd x v := by
  simp [CFSG.Sporadic.Bridge.wordProd]

theorem wordProd_invW {G : Type*} [Group G] (x : ℕ → G) (w : List (ℕ × Bool)) :
    (CFSG.Sporadic.Bridge.wordProd x w)⁻¹ = CFSG.Sporadic.Bridge.wordProd x (invW w) := by
  induction w with
  | nil => simp [CFSG.Sporadic.Bridge.wordProd, invW]
  | cons l w ih =>
    obtain ⟨i, b⟩ := l
    have e : invW ((i, b) :: w) = invW w ++ [(i, !b)] := by simp [invW]
    rw [wordProd_cons, mul_inv_rev, ih, e, wordProd_append]
    cases b <;> simp [CFSG.Sporadic.Bridge.wordProd]

theorem coe_wordProd {d : ℕ} {x : ℕ → GL (Fin d) (ZMod 2)} {P Q : ℕ → ℕ}
    (hP : ∀ i, ((x i : GL (Fin d) (ZMod 2)) : Matrix (Fin d) (Fin d) (ZMod 2)) = matOfF d (P i))
    (hQ : ∀ i, (((x i)⁻¹ : GL (Fin d) (ZMod 2)) : Matrix (Fin d) (Fin d) (ZMod 2)) = matOfF d (Q i))
    (w : List (ℕ × Bool)) :
    ((CFSG.Sporadic.Bridge.wordProd x w : GL (Fin d) (ZMod 2)) : Matrix (Fin d) (Fin d) (ZMod 2)) =
      matOfF d (wordK d P Q w) := by
  induction w with
  | nil =>
    rw [wordK_nil, matOfF_idF]
    simp [CFSG.Sporadic.Bridge.wordProd]
  | cons l w ih =>
    obtain ⟨i, b⟩ := l
    rw [wordProd_cons, Units.val_mul, ih, wordK_cons, matOfF_mulF]
    cases b
    · simp only [Bool.false_eq_true, if_false]
      rw [hQ]
    · simp only [if_true]
      rw [hP]

theorem coe_signedProd {d m : ℕ} {x : Fin m → GL (Fin d) (ZMod 2)} {P Q : ℕ → ℕ}
    (hP : ∀ i, ((x i : GL (Fin d) (ZMod 2)) : Matrix (Fin d) (Fin d) (ZMod 2)) = matOfF d (P i))
    (hQ : ∀ i, (((x i)⁻¹ : GL (Fin d) (ZMod 2)) : Matrix (Fin d) (Fin d) (ZMod 2)) = matOfF d (Q i))
    (w : List (Fin m × Bool)) :
    ((signedProd x w : GL (Fin d) (ZMod 2)) : Matrix (Fin d) (Fin d) (ZMod 2)) =
      matOfF d (wordK d P Q (w.map fun l => (l.1.val, l.2))) := by
  induction w with
  | nil =>
    rw [List.map_nil, wordK_nil, matOfF_idF]
    simp
  | cons l w ih =>
    obtain ⟨i, b⟩ := l
    rw [signedProd_cons, Units.val_mul, ih, List.map_cons, wordK_cons, matOfF_mulF]
    cases b
    · simp only [Bool.false_eq_true, if_false]
      rw [hQ]
    · simp only [if_true]
      rw [hP]

@[expose] noncomputable def relsOK (d : ℕ) (P Q : ℕ → ℕ) (R : List (List (ℕ × Bool))) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun w _ ih => Bool.rec (motive := fun _ => Bool) false ih (Nat.beq (wordK d P Q w) (idF d))) R

theorem relsOK_sound {d : ℕ} {P Q : ℕ → ℕ} {R : List (List (ℕ × Bool))}
    (h : relsOK d P Q R = true) : ∀ w ∈ R, wordK d P Q w = idF d := by
  induction R with
  | nil => simp
  | cons w R ih =>
    intro v hv
    have h' : Bool.rec (motive := fun _ => Bool) false (relsOK d P Q R)
        (Nat.beq (wordK d P Q w) (idF d)) = true := h
    cases hb : Nat.beq (wordK d P Q w) (idF d)
    · rw [hb] at h'
      exact absurd h' Bool.false_ne_true
    · rw [hb] at h'
      rcases List.mem_cons.mp hv with rfl | hv
      · exact Nat.eq_of_beq_eq_true hb
      · exact ih h' v hv

theorem strictB_eq (y : ℕ) (k : ℕ → Bool) : strictB y k = k y := by
  cases y <;> rfl

@[expose] noncomputable def bindGo (k : List ℕ → Bool) (L : List ℕ) : List ℕ → Bool :=
  List.rec (motive := fun _ => List ℕ → Bool) (fun acc => k acc)
    (fun a _ ih acc => strictB a fun a => ih (List.append acc [a])) L

@[expose] noncomputable def bindL (L : List ℕ) (k : List ℕ → Bool) : Bool := bindGo k L []

theorem bindGo_eq (k : List ℕ → Bool) (L : List ℕ) : ∀ acc, bindGo k L acc = k (acc ++ L) := by
  induction L with
  | nil =>
    intro acc
    simp [bindGo]
  | cons a L ih =>
    intro acc
    change strictB a (fun a => bindGo k L (List.append acc [a])) = _
    rw [strictB_eq, ih]
    simp

theorem bindL_eq (L : List ℕ) (k : List ℕ → Bool) : bindL L k = k L := by
  rw [bindL, bindGo_eq, List.nil_append]

theorem signedProd_eq_one_of_relsOK {d m : ℕ} {x : Fin m → GL (Fin d) (ZMod 2)} {L LI : List ℕ}
    (hP : ∀ i, ((x i : GL (Fin d) (ZMod 2)) : Matrix (Fin d) (Fin d) (ZMod 2)) = matOfF d (selN L i))
    (hQ : ∀ i, (((x i)⁻¹ : GL (Fin d) (ZMod 2)) : Matrix (Fin d) (Fin d) (ZMod 2)) =
      matOfF d (selN LI i))
    {Rs : List (List (Fin m × Bool))}
    (h : bindL L (fun L => bindL LI fun LI =>
      relsOK d (selN L) (selN LI) (Rs.map fun w => w.map fun l => (l.1.val, l.2))) = true) :
    ∀ w ∈ Rs, signedProd x w = 1 := by
  rw [bindL_eq] at h
  beta_reduce at h
  rw [bindL_eq] at h
  beta_reduce at h
  intro w hw
  apply Units.ext
  rw [coe_signedProd hP hQ, relsOK_sound h _ (List.mem_map_of_mem hw), matOfF_idF, Units.val_one]

theorem selN_eq_getD (L : List ℕ) : ∀ j, selN L j = L.getD j 0 := by
  induction L with
  | nil =>
    intro j
    simp [selN]
  | cons a L ih =>
    intro j
    cases j with
    | zero => rfl
    | succ j =>
      rw [selN_cons_succ, ih, List.getD_cons_succ]

theorem selN_range_map (f : ℕ → ℕ) {n j : ℕ} (hj : j < n) :
    selN ((List.range n).map f) j = f j := by
  rw [selN_eq_getD, List.getD_eq_getElem _ _ (by simpa using hj)]
  simp

open CFSG.Timmesfeld.Moufang

@[expose] noncomputable def dK (a b bi : ℕ) : ℕ := wordK 12 (pick2 a b) (pick2 a bi) J2.wordD

@[expose] noncomputable def dIK (a b bi : ℕ) : ℕ :=
  wordK 12 (pick2 a b) (pick2 a bi) (invW J2.wordD)

@[expose] noncomputable def gK (a b bi : ℕ) (j : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) (dK a b bi)
    (fun k _ => wordK 12 (pick3 a b (dK a b bi)) (pick3 a bi (dIK a b bi)) (J2.genWord (k + 1))) j

@[expose] noncomputable def gIK (a b bi : ℕ) (j : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) (dIK a b bi)
    (fun k _ => wordK 12 (pick3 a b (dK a b bi)) (pick3 a bi (dIK a b bi))
      (invW (J2.genWord (k + 1)))) j

theorem relators_of_codes {A B : GL (Fin 12) (ZMod 2)} {a b bi : ℕ}
    (hA : ((A : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) = matOfF 12 a)
    (hAi : ((A⁻¹ : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) = matOfF 12 a)
    (hB : ((B : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) = matOfF 12 b)
    (hBi : ((B⁻¹ : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) = matOfF 12 bi)
    (u : ℕ → GL (Fin 12) (ZMod 2)) (hu0 : u 0 = A) (hu1 : u 1 = B)
    (hu2 : ∀ i, u (i + 2) =
      CFSG.Sporadic.Bridge.wordProd (fun i => if i = 0 then A else B) J2.wordD)
    (gen : Fin 7 → GL (Fin 12) (ZMod 2))
    (hg0 : ∀ h, gen ⟨0, h⟩ =
      CFSG.Sporadic.Bridge.wordProd (fun i => if i = 0 then A else B) J2.wordD)
    (hg : ∀ k h, gen ⟨k + 1, h⟩ = CFSG.Sporadic.Bridge.wordProd u (J2.genWord (k + 1)))
    {Rs : List (List (Fin 7 × Bool))}
    (h : bindL ((List.range 7).map (gK a b bi)) (fun L =>
      bindL ((List.range 7).map (gIK a b bi)) fun LI =>
        relsOK 12 (selN L) (selN LI) (Rs.map fun w => w.map fun l => (l.1.val, l.2))) = true) :
    ∀ w ∈ Rs, signedProd gen w = 1 := by
  have hx : ∀ i, (((fun i => if i = 0 then A else B) i : GL (Fin 12) (ZMod 2)) :
      Matrix (Fin 12) (Fin 12) (ZMod 2)) = matOfF 12 (pick2 a b i) := by
    intro i
    match i with
    | 0 => exact hA
    | i + 1 =>
      simp only [Nat.add_one_ne_zero, if_false]
      exact hB
  have hxi : ∀ i, ((((fun i => if i = 0 then A else B) i)⁻¹ : GL (Fin 12) (ZMod 2)) :
      Matrix (Fin 12) (Fin 12) (ZMod 2)) = matOfF 12 (pick2 a bi i) := by
    intro i
    match i with
    | 0 => exact hAi
    | i + 1 =>
      simp only [Nat.add_one_ne_zero, if_false]
      exact hBi
  have hD : ((CFSG.Sporadic.Bridge.wordProd (fun i => if i = 0 then A else B) J2.wordD :
      GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) = matOfF 12 (dK a b bi) :=
    coe_wordProd hx hxi _
  have hDi : (((CFSG.Sporadic.Bridge.wordProd (fun i => if i = 0 then A else B) J2.wordD)⁻¹ :
      GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) = matOfF 12 (dIK a b bi) := by
    rw [wordProd_invW]
    exact coe_wordProd hx hxi _
  have hy : ∀ i, ((u i : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) =
      matOfF 12 (pick3 a b (dK a b bi) i) := by
    intro i
    match i with
    | 0 =>
      rw [hu0]
      exact hA
    | 1 =>
      rw [hu1]
      exact hB
    | i + 2 =>
      rw [hu2]
      exact hD
  have hyi : ∀ i, (((u i)⁻¹ : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) =
      matOfF 12 (pick3 a bi (dIK a b bi) i) := by
    intro i
    match i with
    | 0 =>
      rw [hu0]
      exact hAi
    | 1 =>
      rw [hu1]
      exact hBi
    | i + 2 =>
      rw [hu2]
      exact hDi
  refine signedProd_eq_one_of_relsOK (L := (List.range 7).map (gK a b bi))
    (LI := (List.range 7).map (gIK a b bi)) ?_ ?_ h
  · intro ⟨k, hk⟩
    rw [selN_range_map _ hk]
    match k, hk with
    | 0, h0 =>
      rw [hg0 h0]
      exact hD
    | k + 1, h1 =>
      rw [hg k h1]
      exact coe_wordProd hy hyi _
  · intro ⟨k, hk⟩
    rw [selN_range_map _ hk]
    match k, hk with
    | 0, h0 =>
      rw [hg0 h0]
      exact hDi
    | k + 1, h1 =>
      rw [hg k h1, wordProd_invW]
      exact coe_wordProd hy hyi _

end CFSG.Sporadic.J2.Module12Pack
