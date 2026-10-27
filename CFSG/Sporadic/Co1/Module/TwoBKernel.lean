
module

public import CFSG.Sporadic.Co1.Module.TwoBFrame
public import CFSG.Certificates.Kernel.Co1M.TwoBKSound
public import CFSG.Certificates.Kernel.Spor.PackFld

public section

namespace CFSG.Sporadic.Co1.Module.TwoBK

open Equiv CFSG.Blueprint CFSG.KC.Co1M CFSG.KC.Co1F2 CFSG.KC.M1F2 CFSG.KC.TreeK
  CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.Module
  CFSG.Sporadic.Co1.Module.TwoBFrame

theorem strictN_eq (y : Nat) (k : Nat → Nat) : CFSG.KC.Loop.strictN y k = k y := by
  cases y <;> rfl

theorem orN_congr {f g : Nat → Nat} : ∀ n, (∀ i < n, f i = g i) →
    CFSG.KLie.CT.orN n f = CFSG.KLie.CT.orN n g
  | 0, _ => rfl
  | n + 1, h => by
    change Nat.lor (f n) (CFSG.KLie.CT.orN n f) = Nat.lor (g n) (CFSG.KLie.CT.orN n g)
    rw [h n (by omega), orN_congr n (fun i hi => h i (by omega))]

@[expose] def Canon (M : Nat) : Prop := M = CFSG.KLie.CT.orN 24 fun i => rowF 24 M i <<< (24 * i)

theorem canon_mulF (A B : Nat) : Canon (mulF 24 A B) := by
  unfold Canon
  rw [CFSG.KC.F2W.mulF_eq_orN]
  exact orN_congr 24 fun i hi => by
    rw [CFSG.KC.F2W.rowF_orN 24 (fun j _ => CFSG.KC.F2W.vmF_lt 24 B (rowF 24 A j)) hi]

theorem pw2_eq (i : Nat) : CFSG.KLie.CT.pw2 i = 2 ^ i := Nat.one_shiftLeft i

theorem rowF_idF {i : Nat} (hi : i < 24) : rowF 24 (idF 24) i = CFSG.KLie.CT.pw2 i :=
  CFSG.KC.F2W.rowF_orN 24 (f := CFSG.KLie.CT.pw2)
    (fun j hj => by rw [pw2_eq]; exact Nat.pow_lt_pow_right (by norm_num) hj) hi

theorem canon_idF : Canon (idF 24) := by
  unfold Canon
  change CFSG.KLie.CT.orN 24 (fun i => CFSG.KLie.CT.pw2 i <<< (24 * i)) =
    CFSG.KLie.CT.orN 24 (fun i => rowF 24 (idF 24) i <<< (24 * i))
  exact orN_congr 24 fun i hi => by rw [rowF_idF hi]

theorem unpackR_get (M : Nat) {i : Nat} (hi : i < 24) : (unpackR 24 M)[i]?.getD 0 = rowF 24 M i := by
  rw [CFSG.KC.F2W.rowF_eq]
  simp [unpackR, hi]

theorem eq_of_unpackR {A B : Nat} (hA : Canon A) (hB : Canon B) (h : unpackR 24 A = unpackR 24 B) :
    A = B := by
  rw [hA, hB]
  exact orN_congr 24 fun i hi => by rw [← unpackR_get A hi, ← unpackR_get B hi, h]

theorem unpackR_idF : unpackR 24 (idF 24) = idRows 24 := by
  apply Array.ext (by simp [unpackR, idRows])
  intro i h1 h2
  have hi : i < 24 := by simpa [unpackR] using h1
  have e := unpackR_get (idF 24) hi
  rw [rowF_idF hi] at e
  rw [Array.getElem?_eq_getElem h1, Option.getD_some] at e
  rw [e]
  simp [idRows, pw2_eq, Nat.one_shiftLeft]

@[expose] def PM (x : NativeSporadic.Co1) (M : Nat) : Prop := matHom x = rowsMatrix 24 (unpackR 24 M)

theorem rM_mul (A B : Nat) : rowsMatrix 24 (unpackR 24 A) * rowsMatrix 24 (unpackR 24 B) =
    rowsMatrix 24 (unpackR 24 (mulF 24 A B)) := by
  rw [← rowsMatrix_mulRows, CFSG.KC.F2W.mulRows_unpackR]

theorem pm_mul {x y : NativeSporadic.Co1} {A B : Nat} (hx : PM x A) (hy : PM y B) :
    PM (x * y) (mulF 24 A B) := by
  unfold PM at *
  rw [map_mul, hx, hy, rM_mul]

theorem pm_one : PM 1 (idF 24) := by
  unfold PM
  rw [map_one, unpackR_idF, rowsMatrix_idRows]

theorem powK_succ (M e : Nat) : powK 24 M (e + 1) = mulF 24 (powK 24 M e) M := by
  change CFSG.KC.Loop.strictN (powK 24 M e) (fun a => mulF 24 a M) = _
  exact strictN_eq _ _

theorem pm_pow {x : NativeSporadic.Co1} {M : Nat} (hx : PM x M) : ∀ e, PM (x ^ e) (powK 24 M e)
  | 0 => by
    rw [pow_zero]
    exact pm_one
  | e + 1 => by
    rw [pow_succ, powK_succ]
    exact pm_mul (pm_pow hx e) hx

@[expose] noncomputable def wGo (Ms : List Nat) (w : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun l _ ih acc => CFSG.KC.Loop.strictN (mulF (nat_lit 24) acc (getL (nat_lit 0) Ms l)) ih) w

theorem wK_eq (Ms w : List Nat) : wK Ms w = wGo Ms w (idF 24) := rfl

theorem pm_wGo (Ms : List Nat) (gens : ℕ → NativeSporadic.Co1) (n : ℕ)
    (hg : ∀ l < n, PM (gens l) (getL 0 Ms l)) :
    ∀ w : List ℕ, (∀ l ∈ w, l < n) → ∀ (x : NativeSporadic.Co1) (acc : Nat), PM x acc →
      PM (x * (w.map gens).prod) (wGo Ms w acc)
  | [], _, x, acc, h => by
    rw [List.map_nil, List.prod_nil, mul_one]
    exact h
  | l :: w, hw, x, acc, h => by
    have e : wGo Ms (l :: w) acc = wGo Ms w (mulF 24 acc (getL 0 Ms l)) := strictN_eq _ _
    rw [e, List.map_cons, List.prod_cons, ← mul_assoc]
    exact pm_wGo Ms gens n hg w (fun l' hl' => hw l' (List.mem_cons_of_mem _ hl')) _ _
      (pm_mul h (hg l (hw l (by simp))))

theorem pm_wK (Ms : List Nat) (gens : ℕ → NativeSporadic.Co1) (n : ℕ)
    (hg : ∀ l < n, PM (gens l) (getL 0 Ms l)) (w : List ℕ) (hw : ∀ l ∈ w, l < n) :
    PM (w.map gens).prod (wK Ms w) := by
  have h := pm_wGo Ms gens n hg w hw 1 (idF 24) pm_one
  rw [one_mul] at h
  exact h

theorem pm_act {x : NativeSporadic.Co1} {M MT : Nat} (hx : PM x M) (hT : trK 24 M = MT) (v : Nat) :
    co1Act x (toVecD 24 v) = toVecD 24 (vmF 24 MT v) := by
  have hb : Nat.beq (trK 24 M) MT = true := by rw [hT]; exact Nat.beq_refl MT
  rw [co1Act_eq_mulVec, hx, rowsMatrix_mulVec, tr_sound hb, CFSG.KC.F2W.vecMulN_unpackR]

theorem pm_eq {x y : NativeSporadic.Co1} {A B : Nat} (hx : PM x A) (hy : PM y B) (hA : Canon A)
    (hB : Canon B) (e : x = y) : A = B := by
  subst e
  exact eq_of_unpackR hA hB
    (rowsMatrix_injective_of_valid (validRows_unpackR A) (validRows_unpackR B) (hx.symm.trans hy))

theorem pm_mul_self {x : NativeSporadic.Co1} {E : Nat} (hx : PM x E) (h : mulF 24 E E = idF 24) :
    x * x = 1 := by
  apply matHom_injective
  have h2 := pm_mul hx hx
  rw [h] at h2
  rw [h2, map_one, unpackR_idF, rowsMatrix_idRows]

@[expose] def PermP (P : Nat) (ρ : Perm (Fin 24)) : Prop := ∀ i : Fin 24, ppg P i = (ρ i : ℕ)

theorem permP_of_check {P Pi : Nat} (h : permK P Pi = true) :
    ∃ ρ : Perm (Fin 24), PermP P ρ ∧ PermP Pi ρ⁻¹ := by
  have hs := perm_spec h
  exact ⟨⟨fun i => ⟨ppg P i, (hs i i.2).1⟩, fun i => ⟨ppg Pi i, (hs i i.2).2.1⟩,
    fun i => Fin.ext (hs i i.2).2.2.2, fun i => Fin.ext (hs i i.2).2.2.1⟩, fun _ => rfl, fun _ => rfl⟩

theorem permP_unique {P : Nat} {ρ σ : Perm (Fin 24)} (h1 : PermP P ρ) (h2 : PermP P σ) : ρ = σ :=
  Equiv.ext fun i => Fin.ext ((h1 i).symm.trans (h2 i))

theorem permP_ppc {P Q : Nat} {ρ σ : Perm (Fin 24)} (hP : PermP P ρ) (hQ : PermP Q σ) :
    PermP (ppc P Q) (ρ * σ) := by
  intro i
  have e1 := hQ i
  have e2 := hP (σ i)
  unfold ppg at e1 e2
  unfold ppc ppg
  rw [CFSG.KS.PackFld.pg_pcomp (by norm_num) i.2, e1, e2]
  rfl

theorem ppc_shr (P Q : Nat) : ppc P Q >>> 120 = 0 :=
  CFSG.KS.PackFld.pcomp_shr (n := 24) (w := 5) (p := P) (q := Q) (by norm_num) (by norm_num)

theorem testBit_of_permP {R : Nat} {ρ : Perm (Fin 24)} (hR : PermP R ρ) {b : Nat} (hb : b < 120) :
    R.testBit b = (ρ ⟨b / 5, by omega⟩ : ℕ).testBit (b % 5) := by
  calc R.testBit b = (decide (b % 5 < 5) && R.testBit (5 * (b / 5) + b % 5)) := by
        rw [Nat.div_add_mod b 5]
        simp [Nat.mod_lt b (by norm_num : 5 > 0)]
    _ = (CFSG.KC.Enum.pg 5 (CFSG.KS.mask 5) R (b / 5)).testBit (b % 5) :=
        (CFSG.KS.PackFld.testBit_pgM 5 R _ _).symm
    _ = _ := congrArg (fun z => Nat.testBit z (b % 5)) (hR ⟨b / 5, by omega⟩)

theorem permP_eq {P Q : Nat} {ρ : Perm (Fin 24)} (hP : PermP P ρ) (hQ : PermP Q ρ)
    (hP' : P >>> 120 = 0) (hQ' : Q >>> 120 = 0) : P = Q := by
  apply Nat.eq_of_testBit_eq
  intro b
  by_cases hb : b < 120
  · rw [testBit_of_permP hP hb, testBit_of_permP hQ hb]
  · have e : ∀ R : Nat, R.testBit b = (R >>> 120).testBit (b - 120) := fun R => by
      rw [Nat.testBit_shiftRight]
      congr 1
      omega
    rw [e P, e Q, hP', hQ']

theorem pwGo_cons (Ps : List Nat) (l : Nat) (t : List Nat) (acc : Nat) :
    pwGo Ps (l :: t) acc = pwGo Ps t (ppc acc (getL 0 Ps l)) := strictN_eq _ _

theorem permP_pwGo (Ps : List Nat) (gens : ℕ → Perm (Fin 24)) (n : ℕ)
    (hg : ∀ l < n, PermP (getL 0 Ps l) (gens l)) :
    ∀ w : List ℕ, (∀ l ∈ w, l < n) → ∀ (acc : Nat) (ρ : Perm (Fin 24)), PermP acc ρ →
      PermP (pwGo Ps w acc) (ρ * (w.map gens).prod)
  | [], _, acc, ρ, h => by
    rw [List.map_nil, List.prod_nil, mul_one]
    exact h
  | l :: w, hw, acc, ρ, h => by
    rw [pwGo_cons, List.map_cons, List.prod_cons, ← mul_assoc]
    exact permP_pwGo Ps gens n hg w (fun l' hl' => hw l' (List.mem_cons_of_mem _ hl')) _ _
      (permP_ppc h (hg l (hw l (by simp))))

theorem permP_pwK (Ps : List Nat) (gens : ℕ → Perm (Fin 24)) (n : ℕ)
    (hg : ∀ l < n, PermP (getL 0 Ps l) (gens l)) {w : List ℕ} (hne : w ≠ [])
    (hw : ∀ l ∈ w, l < n) : PermP (pwK Ps w) (w.map gens).prod := by
  match w, hne, hw with
  | l :: t, _, hw =>
    have h := permP_pwGo Ps gens n hg t (fun l' hl' => hw l' (List.mem_cons_of_mem _ hl'))
      (getL 0 Ps l) (gens l) (hg l (hw l (by simp)))
    rw [List.map_cons, List.prod_cons]
    exact h

@[expose] noncomputable def frA (AP : Nat) (i j : Fin 24) : Vec24 := toVecD 24 (avK AP i j)

theorem avK_lt (AP i j : Nat) : avK AP i j < 2 ^ 24 := CFSG.KC.F2W.rowF_lt 24 AP _

theorem frA_dist {AP w : Nat} (hd : distFK AP w = true) (hs : symK AP = true) (hw : w < 2 ^ 24) :
    ∀ i j k l : Fin 24, i ≠ j → k ≠ l →
      (frA AP i j = frA AP k l ∨ frA AP i j = frA AP k l + toVecD 24 w) → s(i, j) = s(k, l) := by
  intro i j k l hij hkl h
  have h' : avK AP i j = avK AP k l ∨ avK AP i j = avK AP k l ^^^ w := by
    rcases h with h | h
    · exact Or.inl (toVecD_injective (avK_lt _ _ _) (avK_lt _ _ _) h)
    · right
      rw [frA, frA, ← toVecD_xor] at h
      exact toVecD_injective (avK_lt _ _ _) (Nat.xor_lt_two_pow (avK_lt _ _ _) hw) h
  rcases dist_spec hd hs i j k l i.2 j.2 k.2 l.2 (fun e => hij (Fin.ext e))
      (fun e => hkl (Fin.ext e)) h' with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · rw [Fin.ext e1, Fin.ext e2]
  · rw [Fin.ext e1, Fin.ext e2]
    exact Sym2.eq_swap

theorem ind_of_check {AP w : Nat} (dist : ∀ i j k l : Fin 24, i ≠ j → k ≠ l →
      (frA AP i j = frA AP k l ∨ frA AP i j = frA AP k l + toVecD 24 w) → s(i, j) = s(k, l))
    {x : NativeSporadic.Co1} {M MT P : Nat} {ρ : Perm (Fin 24)} (hx : PM x M)
    (hT : trK 24 M = MT) (hP : PermP P ρ) (h : indK AP w MT P = true) (hs : symK AP = true) :
    (co1Frame (toVecD 24 w) (frA AP) dist).Ind x ρ := by
  obtain ⟨h0, h1⟩ := ind_full h hs (fun i hi => by rw [hP ⟨i, hi⟩]; exact (ρ _).2)
  refine ⟨?_, fun i j hij => ?_⟩
  · change co1Act x (toVecD 24 w) = toVecD 24 w
    rw [pm_act hx hT, h0]
  · change co1Act x (toVecD 24 (avK AP i j)) = toVecD 24 (avK AP (ρ i) (ρ j)) ∨
      co1Act x (toVecD 24 (avK AP i j)) = toVecD 24 (avK AP (ρ i) (ρ j)) + toVecD 24 w
    rw [pm_act hx hT]
    rcases h1 i i.2 j j.2 (fun e => hij (Fin.ext e)) with e | e
    · left
      rw [e, hP i, hP j]
    · right
      rw [e, hP i, hP j, toVecD_xor]

theorem ind1_of_check {AP w : Nat} (dist : ∀ i j k l : Fin 24, i ≠ j → k ≠ l →
      (frA AP i j = frA AP k l ∨ frA AP i j = frA AP k l + toVecD 24 w) → s(i, j) = s(k, l))
    {x : NativeSporadic.Co1} {M MT : Nat} (hx : PM x M) (hT : trK 24 M = MT)
    (h : ind1K AP w MT = true) (hs : symK AP = true) :
    (co1Frame (toVecD 24 w) (frA AP) dist).Ind x 1 := by
  obtain ⟨h0, h1⟩ := ind1_full h hs
  refine ⟨?_, fun i j hij => ?_⟩
  · change co1Act x (toVecD 24 w) = toVecD 24 w
    rw [pm_act hx hT, h0]
  · change co1Act x (toVecD 24 (avK AP i j)) = toVecD 24 (avK AP i j) ∨
      co1Act x (toVecD 24 (avK AP i j)) = toVecD 24 (avK AP i j) + toVecD 24 w
    rw [pm_act hx hT]
    rcases h1 i i.2 j j.2 (fun e => hij (Fin.ext e)) with e | e
    · left
      rw [e]
    · right
      rw [e, toVecD_xor]

@[expose] noncomputable def extGo (g : Nat) (L : List Nat) : List Nat → List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
    (fun a _ ih acc => ih (List.cons (mulF (nat_lit 24) a g) acc)) L

@[expose] noncomputable def copyL (L : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil (fun a _ ih => List.cons a ih) L

theorem extK_eq (g : Nat) (L : List Nat) : extK g L = extGo g L (copyL L) := rfl

theorem copyL_eq : ∀ L : List Nat, copyL L = L
  | [] => rfl
  | a :: L => congrArg (List.cons a) (copyL_eq L)

theorem extGo_eq (g : Nat) : ∀ L acc : List Nat,
    extGo g L acc = (L.map fun a => mulF 24 a g).reverse ++ acc
  | [], acc => rfl
  | a :: L, acc => by
    change extGo g L (mulF 24 a g :: acc) = _
    rw [extGo_eq g L]
    simp

theorem mem_extK {g : Nat} {L : List Nat} {M : Nat} (h : M ∈ extK g L) :
    M ∈ L ∨ ∃ a ∈ L, M = mulF 24 a g := by
  rw [extK_eq, copyL_eq, extGo_eq, List.mem_append, List.mem_reverse, List.mem_map] at h
  rcases h with ⟨a, ha, rfl⟩ | h
  · exact Or.inr ⟨a, ha, rfl⟩
  · exact Or.inl h

theorem mem_prodsK (E : List Nat) (Qp : NativeSporadic.Co1 → Prop) (h1 : Qp 1)
    (hmul : ∀ x y, Qp x → Qp y → Qp (x * y)) :
    ∀ n, (∀ h < n, ∃ y, Qp y ∧ PM y (getL 0 E h)) → ∀ M ∈ prodsK E n, ∃ x, Qp x ∧ PM x M
  | 0, _, M, hM => by
    have e : M = idF 24 := List.mem_singleton.1 hM
    exact ⟨1, h1, e ▸ pm_one⟩
  | n + 1, hg, M, hM => by
    rcases mem_extK hM with hM | ⟨a, ha, rfl⟩
    · exact mem_prodsK E Qp h1 hmul n (fun h hh => hg h (by omega)) M hM
    · obtain ⟨x, hx, hpx⟩ := mem_prodsK E Qp h1 hmul n (fun h hh => hg h (by omega)) a ha
      obtain ⟨y, hy, hpy⟩ := hg n (by omega)
      exact ⟨x * y, hmul x y hx hy, pm_mul hpx hpy⟩

@[expose] noncomputable def conjGo (s : Nat) (L : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil
    (fun e _ ih => List.cons (mulF (nat_lit 24) (mulF (nat_lit 24) e s) e) ih) L

theorem conjGo_eq (s : Nat) : ∀ L : List Nat, conjGo s L = L.map fun e => mulF 24 (mulF 24 e s) e
  | [] => rfl
  | _ :: L => congrArg (List.cons _) (conjGo_eq s L)

theorem conjK_eq (E : List Nat) (s : Nat) :
    conjK E s = (prodsK E 5).map fun e => mulF 24 (mulF 24 e s) e :=
  conjGo_eq s (prodsK E 5)

theorem tree_family_vec (C : Subgroup NativeSporadic.Co1) {MTs : List Nat} {ng np root : Nat}
    {recs : List (Nat × Nat)} (h : treeOK (actV MTs) ng np root recs = true) (hroot : root < 2 ^ 24)
    (gen : ℕ → NativeSporadic.Co1) (hgen : ∀ l < ng, gen l ∈ C)
    (hact : ∀ l < ng, ∀ v, co1Act (gen l) (toVecD 24 v) = toVecD 24 (vmF 24 (getL 0 MTs l) v)) :
    ∃ t : ℕ → NativeSporadic.Co1, (∀ i < recs.length + 1, t i ∈ C) ∧
      ∀ i < recs.length + 1, ∀ j < recs.length + 1,
        co1Act (t i) (toVecD 24 root) = co1Act (t j) (toVecD 24 root) → i = j := by
  obtain ⟨hnd, hlen, hreach⟩ := treeOK_sound h
  obtain ⟨t, ht, hd⟩ := exists_tree_family C co1Act co1Act_mul co1Act_one (toVecD 24) gen hgen
    (fun y => y < 2 ^ 24) hroot (fun l _ y _ => CFSG.KC.F2W.vmF_lt 24 _ y)
    (fun l hl y _ => (hact l hl y).symm) (fun x y hx hy e => toVecD_injective hx hy e) hnd hreach
  rw [hlen] at ht hd
  exact ⟨t, fun i hi => (ht i hi).1, hd⟩

@[expose] noncomputable def rAct (g : NativeSporadic.Co1) (M : Matrix (Fin 24) (Fin 24) (ZMod 2)) :
    Matrix (Fin 24) (Fin 24) (ZMod 2) := M * matHom g⁻¹

theorem tree_family_mat (C : Subgroup NativeSporadic.Co1) {Us : List Nat} {ng np : Nat}
    {recs : List (Nat × Nat)} (h : treeOK (actM Us) ng np (idF 24) recs = true)
    (gen : ℕ → NativeSporadic.Co1) (hgen : ∀ l < ng, gen l ∈ C)
    (hpm : ∀ l < ng, PM (gen l) (getL 0 Us l)) :
    ∃ u : ℕ → NativeSporadic.Co1, (∀ i < recs.length + 1, u i ∈ C) ∧
      ∀ i < recs.length + 1, ∀ j < recs.length + 1, u i = u j → i = j := by
  obtain ⟨hnd, hlen, hreach⟩ := treeOK_sound h
  have hop : ∀ g h M, rAct (g * h) M = rAct g (rAct h M) := fun g h M => by
    simp only [rAct, mul_inv_rev, map_mul, Matrix.mul_assoc]
  have hone : ∀ M, rAct 1 M = M := fun M => by simp [rAct]
  obtain ⟨t, ht, hd⟩ := exists_tree_family C rAct hop hone (fun X => rowsMatrix 24 (unpackR 24 X))
    (fun l => (gen l)⁻¹) (fun l hl => C.inv_mem (hgen l hl)) Canon canon_idF
    (fun l _ y _ => canon_mulF y _)
    (fun l hl y _ => by
      change rowsMatrix 24 (unpackR 24 (mulF 24 y (getL 0 Us l))) = rowsMatrix 24 (unpackR 24 y) *
        matHom (gen l)⁻¹⁻¹
      rw [inv_inv, ← rM_mul, hpm l hl])
    (fun x y hx hy e => eq_of_unpackR hx hy
      (rowsMatrix_injective_of_valid (validRows_unpackR x) (validRows_unpackR y) e)) hnd hreach
  rw [hlen] at ht hd
  refine ⟨fun i => (t i)⁻¹, fun i hi => C.inv_mem (ht i hi).1, fun i hi j hj e => hd i hi j hj ?_⟩
  rw [inv_injective e]

theorem tree_family_conj (C : Subgroup (Perm (Fin 24))) {H Hi : List Nat} {ng np root : Nat}
    {recs : List (Nat × Nat)} (h : treeOK (actX H Hi) ng np root recs = true)
    (gen : ℕ → Perm (Fin 24)) (hgen : ∀ l < ng, gen l ∈ C) (hH : ∀ l < ng, PermP (getL 0 H l) (gen l))
    (hHi : ∀ l < ng, PermP (getL 0 Hi l) (gen l)⁻¹) {τ₀ : Perm (Fin 24)} (hroot : PermP root τ₀)
    (hroot' : root >>> 120 = 0) :
    ∃ t : ℕ → Perm (Fin 24), (∀ i < recs.length + 1, t i ∈ C) ∧
      ∀ i < recs.length + 1, ∀ j < recs.length + 1,
        t i * τ₀ * (t i)⁻¹ = t j * τ₀ * (t j)⁻¹ → i = j := by
  classical
  obtain ⟨hnd, hlen, hreach⟩ := treeOK_sound h
  let enc : ℕ → Perm (Fin 24) := fun y => if hy : ∃ ρ, PermP y ρ then Classical.choose hy else 1
  have henc : ∀ {y ρ}, PermP y ρ → enc y = ρ := fun {y ρ} hy => by
    have hex : ∃ ρ, PermP y ρ := ⟨ρ, hy⟩
    simp only [enc, hex, ↓reduceDIte]
    exact permP_unique (Classical.choose_spec hex) hy
  let op : Perm (Fin 24) → Perm (Fin 24) → Perm (Fin 24) := fun g τ => g * τ * g⁻¹
  have hop : ∀ g k τ, op (g * k) τ = op g (op k τ) := fun g k τ => by
    simp only [op]
    group
  have hone : ∀ τ, op 1 τ = τ := fun τ => by simp [op]
  have hstep : ∀ l < ng, ∀ y ρ, PermP y ρ → PermP (actX H Hi l y) (gen l * ρ * (gen l)⁻¹) :=
    fun l hl y ρ hy => permP_ppc (permP_ppc (hH l hl) hy) (hHi l hl)
  obtain ⟨t, ht, hd⟩ := exists_tree_family C op hop hone enc gen hgen
    (fun y => (∃ ρ, PermP y ρ) ∧ y >>> 120 = 0) ⟨⟨τ₀, hroot⟩, hroot'⟩
    (fun l hl y ⟨⟨ρ, hy⟩, _⟩ => ⟨⟨_, hstep l hl y ρ hy⟩, ppc_shr _ _⟩)
    (fun l hl y ⟨⟨ρ, hy⟩, _⟩ => by rw [henc (hstep l hl y ρ hy), henc hy])
    (fun x y ⟨⟨ρ, hx⟩, hx'⟩ ⟨⟨σ, hy⟩, hy'⟩ e => by
      rw [henc hx, henc hy] at e
      subst e
      exact permP_eq hx hy hx' hy') hnd hreach
  rw [hlen] at ht hd
  refine ⟨t, fun i hi => (ht i hi).1, fun i hi j hj e => hd i hi j hj ?_⟩
  rw [henc hroot]
  exact e

theorem tree_family_pts (C : Subgroup (Perm (Fin 24))) {G : List Nat} {ng np : Nat}
    {recs : List (Nat × Nat)} (h : treeOK (actP G) ng np 1 recs = true)
    (gen : ℕ → Perm (Fin 24)) (hgen : ∀ l < ng, gen l ∈ C) (hG : ∀ l < ng, PermP (getL 0 G l) (gen l)) :
    ∃ t : ℕ → Perm (Fin 24), (∀ i < recs.length + 1, t i ∈ C) ∧
      ∀ i < recs.length + 1, ∀ j < recs.length + 1, t i 1 = t j 1 → i = j := by
  obtain ⟨hnd, hlen, hreach⟩ := treeOK_sound h
  let enc : ℕ → Fin 24 := fun y => ⟨y % 24, Nat.mod_lt _ (by norm_num)⟩
  have henc : ∀ {y} (hy : y < 24), enc y = ⟨y, hy⟩ := fun {y} hy => Fin.ext (Nat.mod_eq_of_lt hy)
  have hval : ∀ l < ng, ∀ y (hy : y < 24), actP G l y = (gen l ⟨y, hy⟩ : ℕ) :=
    fun l hl y hy => hG l hl ⟨y, hy⟩
  obtain ⟨t, ht, hd⟩ := exists_tree_family C (fun g x => g x) (fun _ _ _ => rfl) (fun _ => rfl) enc
    gen hgen (fun y => y < 24) (by norm_num)
    (fun l hl y hy => by rw [hval l hl y hy]; exact (gen l _).2)
    (fun l hl y hy => by
      rw [henc hy, Fin.ext_iff, hval l hl y hy]
      exact Nat.mod_eq_of_lt (gen l _).2)
    (fun x y hx hy e => by
      rw [henc hx, henc hy] at e
      exact Fin.ext_iff.1 e) hnd hreach
  rw [hlen] at ht hd
  have h1 : enc 1 = 1 := Fin.ext rfl
  refine ⟨t, fun i hi => (ht i hi).1, fun i hi j hj e => hd i hi j hj ?_⟩
  rw [h1]
  exact e

theorem uniTri_of_check {U : Nat} (h : uniK U = true) : UniTri (rowsMatrix 24 (unpackR 24 U)) := by
  have hs := uni_spec h
  have hr : ∀ i : Fin 24, (unpackR 24 U)[i.val]?.getD 0 = CFSG.KLie.CT.fget U i 24 := fun i =>
    unpackR_get U i.2
  refine ⟨fun i j hji => ?_, fun i => ?_⟩
  · rw [rowsMatrix_apply, toVecD_apply, hr i, (hs i i.2).1 j hji]
    rfl
  · rw [rowsMatrix_apply, toVecD_apply, hr i, (hs i i.2).2]
    rfl

end CFSG.Sporadic.Co1.Module.TwoBK

end
