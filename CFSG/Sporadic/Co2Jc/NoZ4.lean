module

public import CFSG.Sporadic.Co2Jc.NoZ4Coord
public import Certificates.Certificate719060

public section

namespace CFSG.Sporadic.Co2Jc

open CFSG.Sporadic.Co2Smith Subgroup
open CFSG.Sporadic.Co2Jc.Data
open CFSG.Sporadic.Co2Jc.Native
open CFSG.Sporadic.Co2Jc.Native.NoZ4
open CFSG.Sporadic.Co2Jc.NoZ4


private noncomputable def linPartNat
    (G X : Nat → Matrix (Fin 10) (Fin 10) (ZMod 4)) :
    List Nat → Matrix (Fin 10) (Fin 10) (ZMod 4)
  | [] => 0
  | k :: rest => G k * linPartNat G X rest + X k * (rest.map G).prod

private theorem prod_decompNat (G X : Nat → Matrix (Fin 10) (Fin 10) (ZMod 4))
    (w : List Nat) :
    (w.map (fun k => G k + (2 : ZMod 4) • X k)).prod =
      (w.map G).prod + (2 : ZMod 4) • linPartNat G X w := by
  induction w with
  | nil => simp [linPartNat]
  | cons k rest ih =>
    simp only [List.map_cons, List.prod_cons]
    rw [ih, linPartNat]
    rw [add_mul, mul_add, mul_add]
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul]
    rw [smul_smul, show (2 : ZMod 4) * 2 = 0 by decide, zero_smul]
    rw [smul_add]
    abel

private theorem pairing {R : Type} [CommSemiring R]
    (A Y B C : Matrix (Fin 10) (Fin 10) R) :
    (∑ a : Fin 10, ∑ b : Fin 10, C a b * (A * Y * B) a b) =
      (∑ p : Fin 10, ∑ q : Fin 10, (A.transpose * C * B.transpose) p q * Y p q) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.mul_sum, Finset.sum_mul]
  conv_rhs =>
    enter [2, x, 2, x_1]
    rw [Finset.sum_comm]
  conv_rhs =>
    enter [2, x]
    rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  conv_rhs =>
    enter [2, i, 2, x]
    rw [Finset.sum_comm]
  conv_rhs =>
    enter [2, i]
    rw [Finset.sum_comm]
  conv_rhs =>
    enter [2, i, 2, x_2]
    rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  ac_rfl

private theorem two_mul_add_eq_zero (x y : ZMod 4) (h : 2 * (x + y) = 0) :
    ZMod.castHom (by norm_num : 2 ∣ 4) (ZMod 2) y =
      ZMod.castHom (by norm_num : 2 ∣ 4) (ZMod 2) x := by
  revert x y
  decide

private theorem castHom_eq_val (x : ZMod 4) :
    ZMod.castHom (by norm_num : 2 ∣ 4) (ZMod 2) x = ((x.val : ℕ) : ZMod 2) := by
  fin_cases x <;> rfl

private theorem Tab.get_eq_toMat {R : Type} [Inhabited R] (T : Tab R) {a b : Nat}
    (ha : a < 10) (hb : b < 10) :
    T.get a b = T.toMat ⟨a, ha⟩ ⟨b, hb⟩ := by
  simp [Tab.get, Tab.toMat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

private theorem idEntry_eq_one_apply (a b : Fin 10) :
    (idEntry a.val b.val : ZMod 4) =
      (1 : Matrix (Fin 10) (Fin 10) (ZMod 4)) a b := by
  rw [Matrix.one_apply, idEntry]
  by_cases h : a = b
  · subst h
    simp
  · have hval : ¬ a.val = b.val := fun hv => h (Fin.ext hv)
    simp [h, hval, Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt]

private theorem list_sum_range_eq_finset_sum {M : Type} [AddCommMonoid M] (n : ℕ)
    (f : ℕ → M) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

private theorem regroup {M : Type} [AddCommMonoid M] (w : List Nat)
    (hw : ∀ k ∈ w, k < 3) (F : Nat → Nat → M) :
    ((List.range w.length).map fun i => F i (w[i]!)).sum =
      ((List.range 3).map fun k =>
        ((List.range w.length).map fun i =>
          if w[i]! = k then F i k else 0).sum).sum := by
  rw [list_sum_range_eq_finset_sum, list_sum_range_eq_finset_sum]
  conv_rhs =>
    enter [2, k]
    rw [list_sum_range_eq_finset_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i < w.length := Finset.mem_range.mp hi
  let a := w[i]'hi'
  have hget : w[i]! = a := by
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi']
    simp [a]
  have hget' : w[i]! = w[i]'hi' := by
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi']
    simp
  have hmem : w[i]! ∈ w := by
    rw [hget']
    exact List.getElem_mem hi'
  have hlt : a < 3 := by
    rw [← hget]
    exact hw _ hmem
  rw [Finset.sum_eq_single a]
  · simp [hget]
  · intro k _ hk
    have hka : a ≠ k := fun h => hk h.symm
    simp [hget, hka]
  · intro hnot
    exact absurd (Finset.mem_range.mpr hlt) hnot


private theorem EOK_spec (h : EOK = true) :
    (∀ p ∈ noZ4Sel, p.1 ∈ noZ4Rels ∧ p.2.1 < 10 ∧ p.2.2 < 10 ∧
      (prod4 (rels[p.1]!)).get p.2.1 p.2.2 =
        (idEntry p.2.1 p.2.2 : ZMod 4) +
          2 * Ebit (prod4 (rels[p.1]!)) p.2.1 p.2.2) ∧
    (noZ4Rels.map fun r =>
      ∑ a : Fin 10, ∑ b : Fin 10,
        (Csel r).toMat a b *
          ((Ebit (prod4 (rels[r]!)) a.val b.val).val : ZMod 2)).sum = 1 := by
  have hPof : ∀ r ∈ noZ4Rels,
      (if r = 1 then prod4 (rels[1]!) else prod4 (rels[9]!)) = prod4 (rels[r]!) := by
    intro r hr
    simp only [noZ4Rels, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp
  have h' := h
  simp only [EOK, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    decide_eq_true_eq, beq_iff_eq] at h'
  refine ⟨?_, ?_⟩
  · intro p hp
    have hp' := h'.1 p hp
    refine ⟨hp'.1.1.1, hp'.1.1.2, hp'.1.2, ?_⟩
    have heq := hp'.2
    rwa [hPof p.1 hp'.1.1.1] at heq
  · have hmap : (noZ4Rels.map fun r =>
        ∑ a : Fin 10, ∑ b : Fin 10,
          (Csel r).toMat a b *
            ((Ebit (if r = 1 then prod4 (rels[1]!) else prod4 (rels[9]!))
              a.val b.val).val : ZMod 2)) =
      (noZ4Rels.map fun r =>
        ∑ a : Fin 10, ∑ b : Fin 10,
          (Csel r).toMat a b *
            ((Ebit (prod4 (rels[r]!)) a.val b.val).val : ZMod 2)) := by
      apply List.map_congr_left
      intro r hr
      rw [hPof r hr]
    rw [← hmap]
    exact h'.2


private theorem getElem!_list_eq {α : Type} [Inhabited α] {l : List α} {i : Nat}
    (h : i < l.length) : l[i]! = l[i]'h := by
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem h]
  simp

private def redLinG (X2 : Nat → Matrix (Fin 10) (Fin 10) (ZMod 2)) (w : List Nat) :
    Matrix (Fin 10) (Fin 10) (ZMod 2) :=
  ((List.range w.length).map fun i =>
    ((w.take i).map G2).prod * X2 (w[i]!) * ((w.drop (i + 1)).map G2).prod).sum

private def termG (X2 : Nat → Matrix (Fin 10) (Fin 10) (ZMod 2)) (w : List Nat)
    (i : Nat) : Matrix (Fin 10) (Fin 10) (ZMod 2) :=
  ((w.take i).map G2).prod * X2 (w[i]!) * ((w.drop (i + 1)).map G2).prod

private def coG (C : Matrix (Fin 10) (Fin 10) (ZMod 2)) (w : List Nat) (k : Nat) :
    Matrix (Fin 10) (Fin 10) (ZMod 2) :=
  ((List.range w.length).map fun i =>
    if w[i]! = k then
      (prefList w)[i]!.toMat.transpose * C * (suffList w)[i + 1]!.toMat.transpose
    else 0).sum

private theorem termG_pair (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (X2 : Nat → Matrix (Fin 10) (Fin 10) (ZMod 2)) (w : List Nat) (i : Nat)
    (hi : i < w.length) :
    (∑ a : Fin 10, ∑ b : Fin 10, C a b * termG X2 w i a b) =
      (∑ p : Fin 10, ∑ q : Fin 10,
        ((prefList w)[i]!.toMat.transpose * C * (suffList w)[i + 1]!.toMat.transpose)
          p q * X2 (w[i]!) p q) := by
  have hAi : i < (prefList w).length := by simp [prefList]; omega
  have hBi : i + 1 < (suffList w).length := by simp [suffList]; omega
  have hA : ((w.take i).map G2).prod = (prefList w)[i]!.toMat := by
    rw [getElem!_list_eq hAi]
    exact (prefList_getElem_toMat w i hAi).symm
  have hB : ((w.drop (i + 1)).map G2).prod = (suffList w)[i + 1]!.toMat := by
    rw [getElem!_list_eq hBi]
    exact (suffList_getElem_toMat w (i + 1) hBi).symm
  rw [termG, hA, hB]
  exact pairing _ _ _ _

private theorem regroup_finset {M : Type} [AddCommMonoid M] (w : List Nat)
    (hw : ∀ k ∈ w, k < 3) (F : Nat → M) :
    (∑ i ∈ Finset.range w.length, F i) =
      ∑ k ∈ Finset.range 3, ∑ i ∈ Finset.range w.length,
        if w[i]! = k then F i else 0 := by
  simp_rw [← list_sum_range_eq_finset_sum]
  exact regroup w hw fun i _ => F i



private theorem sum_i_term_eq (X2 : Nat → Matrix (Fin 10) (Fin 10) (ZMod 2))
    (C : Matrix (Fin 10) (Fin 10) (ZMod 2)) (w : List Nat) (k : Nat) :
    (∑ i ∈ Finset.range w.length,
      if w[i]! = k then
        (∑ p : Fin 10, ∑ q : Fin 10,
          ((prefList w)[i]!.toMat.transpose * C *
            (suffList w)[i + 1]!.toMat.transpose) p q * X2 k p q)
      else 0) =
      ∑ p : Fin 10, ∑ q : Fin 10, coG C w k p q * X2 k p q := by
  have hco : coG C w k = ∑ i ∈ Finset.range w.length,
      (if w[i]! = k then
        (prefList w)[i]!.toMat.transpose * C * (suffList w)[i + 1]!.toMat.transpose
      else 0) := by
    rw [coG]
    exact list_sum_range_eq_finset_sum _ _
  rw [hco]
  simp only [Matrix.sum_apply]
  have hif : ∀ i : Nat,
      (if w[i]! = k then
        (∑ p : Fin 10, ∑ q : Fin 10,
          ((prefList w)[i]!.toMat.transpose * C *
            (suffList w)[i + 1]!.toMat.transpose) p q * X2 k p q)
      else 0) =
      ∑ p : Fin 10, ∑ q : Fin 10,
        (if w[i]! = k then
          ((prefList w)[i]!.toMat.transpose * C *
            (suffList w)[i + 1]!.toMat.transpose) p q * X2 k p q
        else 0) := by
    intro i
    by_cases h : w[i]?.getD 0 = k <;> simp [h]
  simp_rw [hif]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs =>
    enter [2, p]
    rw [Finset.sum_comm]
  conv_rhs =>
    enter [2, p, 2, q]
    rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : w[i]?.getD 0 = k <;> simp [h]


private theorem sum_if_F_eq (X2 : Nat → Matrix (Fin 10) (Fin 10) (ZMod 2))
    (C : Matrix (Fin 10) (Fin 10) (ZMod 2)) (w : List Nat) (k : Nat) :
    (∑ i ∈ Finset.range w.length,
      if w[i]! = k then
        (∑ a : Fin 10, ∑ b : Fin 10, C a b * termG X2 w i a b)
      else 0) =
      ∑ p : Fin 10, ∑ q : Fin 10, coG C w k p q * X2 k p q := by
  have h : (∑ i ∈ Finset.range w.length,
        if w[i]! = k then
          (∑ a : Fin 10, ∑ b : Fin 10, C a b * termG X2 w i a b)
        else 0) =
      ∑ i ∈ Finset.range w.length,
        if w[i]! = k then
          (∑ p : Fin 10, ∑ q : Fin 10,
            ((prefList w)[i]!.toMat.transpose * C *
              (suffList w)[i + 1]!.toMat.transpose) p q * X2 k p q)
        else 0 := by
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i < w.length := Finset.mem_range.mp hi
    by_cases hk : w[i]! = k
    · rw [if_pos hk, if_pos hk, termG_pair C X2 w i hi', hk]
    · rw [if_neg hk, if_neg hk]
  rw [h]
  exact sum_i_term_eq X2 C w k

private theorem sum_C_redLin_eq (X2 : Nat → Matrix (Fin 10) (Fin 10) (ZMod 2))
    (C : Matrix (Fin 10) (Fin 10) (ZMod 2)) (w : List Nat)
    (hw : ∀ k ∈ w, k < 3) :
    (∑ a : Fin 10, ∑ b : Fin 10, C a b * redLinG X2 w a b) =
      ∑ k ∈ Finset.range 3, ∑ p : Fin 10, ∑ q : Fin 10,
        coG C w k p q * X2 k p q := by
  have hred : redLinG X2 w = ∑ i ∈ Finset.range w.length, termG X2 w i := by
    rw [redLinG]
    exact list_sum_range_eq_finset_sum _ _
  have hstep1 : (∑ a : Fin 10, ∑ b : Fin 10, C a b * redLinG X2 w a b) =
      ∑ i ∈ Finset.range w.length,
        ∑ a : Fin 10, ∑ b : Fin 10, C a b * termG X2 w i a b := by
    rw [hred]
    simp only [Matrix.sum_apply, Finset.mul_sum]
    conv_lhs =>
      enter [2, a]
      rw [Finset.sum_comm]
    rw [Finset.sum_comm]
  rw [hstep1, regroup_finset w hw (fun i =>
    ∑ a : Fin 10, ∑ b : Fin 10, C a b * termG X2 w i a b)]
  apply Finset.sum_congr rfl
  intro k _
  exact sum_if_F_eq X2 C w k


private theorem foldl_ite_eq_sum_aux (l : List Nat) (p : Nat → Prop) [DecidablePred p]
    (f : Nat → Matrix (Fin 10) (Fin 10) (ZMod 2))
    (init : Matrix (Fin 10) (Fin 10) (ZMod 2)) :
    (l.foldl (fun acc i => if p i then acc + f i else acc) init) =
      init + (l.map (fun i => if p i then f i else 0)).sum := by
  induction l generalizing init with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    by_cases h : p a <;> simp [h, ih, add_assoc]

private theorem coeff2_toMat_coG (k : Nat) :
    (coeff2 k).toMat =
      (noZ4Rels.map fun r => coG (Csel r).toMat (rels[r]!) k).sum := by
  rw [coeff2_toMat]
  apply congrArg List.sum
  apply List.map_congr_left
  intro r _
  dsimp only
  rw [foldl_ite_eq_sum_aux, coG]
  simp


private theorem list_sum_finset_sum {ι κ M : Type} [AddCommMonoid M] (l : List ι)
    (s : Finset κ) (f : ι → κ → M) :
    (l.map fun i => ∑ j ∈ s, f i j).sum = ∑ j ∈ s, (l.map fun i => f i j).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, ih, Finset.sum_add_distrib]


private theorem list_sum_apply (l : List (Matrix (Fin 10) (Fin 10) (ZMod 2)))
    (p q : Fin 10) :
    l.sum p q = (l.map fun A => A p q).sum := by
  induction l with
  | nil => simp
  | cons A l ih => simp [List.sum_cons, Matrix.add_apply, ih]

private theorem coeff2_toMat_coG_apply (k : Nat) (p q : Fin 10) :
    (coeff2 k).toMat p q =
      (noZ4Rels.map fun r => coG (Csel r).toMat (rels[r]!) k p q).sum := by
  rw [coeff2_toMat_coG, list_sum_apply, List.map_map]
  rfl

private theorem matZero_eq_zero (M : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : matZero M = true) : M = 0 := by
  have h' : ∀ a b : Fin 10, M a b = 0 := by
    simpa [matZero, List.all_eq_true, List.mem_finRange] using h
  ext a b
  exact h' a b

private theorem Csel_toMat_apply (r : Nat) (a b : Fin 10) :
    (Csel r).toMat a b = if (r, a.val, b.val) ∈ noZ4Sel then 1 else 0 := by
  change (Tab.ofMat (Matrix.of (fun a b : Fin 10 =>
    if (r, a.val, b.val) ∈ noZ4Sel then 1 else 0))).toMat a b = _
  rw [Tab.toMat_ofMat, Matrix.of_apply]

theorem noZ4_Qj (V : Type) [CommGroup V] (ρ : Qj →* MulAut V) (ι : ↥Jc →* V)
    (hι : Function.Injective ι) (hρ : ∀ g a, ρ g (ι a) = ι ((g : MulAut ↥Jc) a))
    (h1 : ∀ v : V, ∃ a, v ^ 2 = ι a) (h2 : ∀ v : V, v ^ 2 = 1 → ∃ a, v = ι a)
    (h3 : ∀ a, ∃ v : V, v ^ 2 = ι a) : False := by
  classical
  letI : Module (ZMod 4) (Additive V) := VModule ι h1
  let v : Fin 10 → Additive V := fun i =>
    Additive.ofMul (Classical.choose (h3 (jcA (2 ^ i.val))))
  have hv : ∀ i, (2 : ZMod 4) • v i =
      iotaA ι (Additive.ofMul (jcA (2 ^ i.val))) := by
    intro i
    exact congrArg Additive.ofMul (Classical.choose_spec (h3 (jcA (2 ^ i.val))))
  let Φ : (Fin 10 → ZMod 4) ≃ₗ[ZMod 4] Additive V := phiEquiv hι h1 h2 hv
  have hΦ : ∀ x, Φ x = phi v x := fun _ => rfl
  have hOK : noZ4OK = true := Certificates.certificate719060
  have hTab : ∀ k : Fin 3, ∀ i : Fin 10,
      (CFSG.Sporadic.Co2Smith.Native.glNJTab[k.val]!)[i.val]! < 1024 := by
    have h := hOK
    simp only [noZ4OK, Bool.and_eq_true, and_assoc] at h
    obtain ⟨-, hTab, -, -⟩ := h
    simp only [noZ4TabOK, List.all_eq_true, List.mem_range] at hTab
    intro k i
    simpa using hTab k.val k.isLt i.val i.isLt
  let GhN (k : Nat) : Matrix (Fin 10) (Fin 10) (ZMod 4) := G4 k
  let XN (k : Nat) : Matrix (Fin 10) (Fin 10) (ZMod 4) :=
    if h : k < 3 then X ρ v Φ ⟨k, h⟩ else 0
  let qAjN (k : Nat) : Qj := if h : k < 3 then qAj ⟨k, h⟩ else 1
  have hdecomp : ∀ k, k < 3 →
      mat ρ v Φ (qAjN k) = GhN k + (2 : ZMod 4) • XN k := by
    intro k hk
    simp only [qAjN, XN, GhN, dif_pos hk]
    exact mat_qAj_decomp (ρ := ρ) (v := v) (Φ := Φ) hι hρ h1 h2 hv hΦ hTab ⟨k, hk⟩
  let linPartN : List Nat → Matrix (Fin 10) (Fin 10) (ZMod 4) :=
    linPartNat GhN XN
  have mat_prodN : ∀ w : List Nat, (∀ k ∈ w, k < 3) →
      mat ρ v Φ ((w.map qAjN).prod) = (w.map GhN).prod + (2 : ZMod 4) • linPartN w := by
    intro w
    induction w with
    | nil =>
      intro _
      simp only [List.map_nil, List.prod_nil]
      rw [mat_one ρ v Φ hΦ]
      simp [linPartN, linPartNat]
    | cons a l ih =>
      intro hw
      have ha : a < 3 := hw a (by simp)
      have hl : ∀ k ∈ l, k < 3 := fun k hk => hw k (by simp [hk])
      rw [List.map_cons, List.prod_cons, mat_mul ρ v Φ hΦ, ih hl, hdecomp a ha]
      rw [← prod_decompNat GhN XN l, ← prod_decompNat GhN XN (a :: l)]
      simp [linPartN, linPartNat, List.map_cons, List.prod_cons]
  have hRelAll : noZ4Rels.all noZ4RelOK = true := by
    have h := hOK
    simp only [noZ4OK, Bool.and_eq_true, and_assoc] at h
    exact h.1
  have rel_spec (r : Nat) (hr : noZ4RelOK r = true) :
      r < Data.rels.length ∧ (∀ k ∈ Data.rels[r]!, k < 3) ∧
      (∀ i < 10, wordAct (Data.rels[r]!) (2 ^ i) = 2 ^ i) := by
    simp only [noZ4RelOK, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hr
    obtain ⟨⟨hrlen, hw⟩, hb⟩ := hr
    exact ⟨by simpa using hrlen, fun k hk => by simpa using hw k hk,
      fun i hi => by simpa using hb i hi⟩
  have rel_eq (r : Nat) (hr : noZ4RelOK r = true) :
      let w := Data.rels[r]!
      (w.map GhN).prod + (2 : ZMod 4) • linPartN w = 1 := by
    dsimp only
    obtain ⟨hrlen, hw, hbasis⟩ := rel_spec r hr
    have hq : qWord (Data.rels[r]!) = 1 := by
      rw [qWord_eq_qWord (w' := []) hw (fun k hk => by simp at hk)
        (fun i hi => by simpa [wordAct] using hbasis i hi)]
      simpa using qWord_nil
    have hprod_aux : ∀ (w : List Nat), (∀ k ∈ w, k < 3) →
        (((w.map qAjN).prod : Qj) : MulAut ↥Jc) = qWord w := by
      intro w hw'
      induction w with
      | nil => simp [qWord, qAjN]
      | cons a l ih =>
        have ha : a < 3 := hw' a (by simp)
        have hl : ∀ k ∈ l, k < 3 := fun k hk => hw' k (by simp [hk])
        rw [List.map_cons, List.prod_cons, qWord_cons]
        simp only [Subgroup.coe_mul]
        rw [ih hl]
        simp [qAjN, ha, qAj]
    have hprod : (Data.rels[r]!.map qAjN).prod =
        (⟨qWord (Data.rels[r]!), qWord_mem hw⟩ : Qj) := by
      apply Subtype.ext
      exact hprod_aux (Data.rels[r]!) hw
    have hq' : (⟨qWord (Data.rels[r]!), qWord_mem hw⟩ : Qj) = 1 := Subtype.ext hq
    have hp := mat_prodN (Data.rels[r]!) hw
    rw [hprod, hq', mat_one ρ v Φ hΦ] at hp
    exact hp.symm

  let red : ZMod 4 →+* ZMod 2 := ZMod.castHom (by norm_num : 2 ∣ 4) (ZMod 2)
  have red_natCast (x : ZMod 2) : red ((x.val : ℕ) : ZMod 4) = x := by
    fin_cases x <;> rfl
  have red_G4 (k : Nat) : (GhN k).map red = G2 k := by
    ext j i
    simp [GhN, G4, G2, red_natCast]
  have prod_map_red : ∀ l : List Nat,
      ((l.map GhN).prod).map red = (l.map G2).prod := by
    intro l
    induction l with
    | nil => simp [Matrix.map_one]
    | cons a l ih =>
      rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons,
        Matrix.map_mul, ih, red_G4]
  let X2 (k : Nat) : Matrix (Fin 10) (Fin 10) (ZMod 2) := (XN k).map red
  let term (w : List Nat) (i : Nat) : Matrix (Fin 10) (Fin 10) (ZMod 2) :=
    ((w.take i).map G2).prod * X2 (w[i]!) * ((w.drop (i + 1)).map G2).prod
  let redLin (w : List Nat) : Matrix (Fin 10) (Fin 10) (ZMod 2) :=
    ((List.range w.length).map (term w)).sum
  have term_zero (a : Nat) (l : List Nat) :
      term (a :: l) 0 = X2 a * (l.map G2).prod := by
    simp [term]
  have term_succ (a : Nat) (l : List Nat) (j : Nat) :
      term (a :: l) (j + 1) = G2 a * term l j := by
    simp only [term]
    have htake : (a :: l).take (j + 1) = a :: l.take j := by simp
    have hdrop : (a :: l).drop (j + 1 + 1) = l.drop (j + 1) := by simp
    have hget : (a :: l)[j + 1]! = l[j]! := by simp
    rw [htake, hdrop, hget, List.map_cons, List.prod_cons]
    simp [mul_assoc]
  have map_add_matrix (A B : Matrix (Fin 10) (Fin 10) (ZMod 4)) :
      (A + B).map red = A.map red + B.map red := by
    ext i j
    simp [Matrix.map, Matrix.add]
  have map_mul_matrix (A B : Matrix (Fin 10) (Fin 10) (ZMod 4)) :
      (A * B).map red = A.map red * B.map red := Matrix.map_mul ..
  have redLin_cons (a : Nat) (l : List Nat) :
      redLin (a :: l) = X2 a * (l.map G2).prod + G2 a * redLin l := by
    simp only [redLin, List.length_cons]
    rw [List.range_succ_eq_map, List.map_cons, List.sum_cons, term_zero]
    have hshift : (List.map (term (a :: l)) (List.map Nat.succ (List.range l.length))).sum =
        (List.map (fun j => G2 a * term l j) (List.range l.length)).sum := by
      rw [List.map_map]
      apply congrArg List.sum
      apply List.map_congr_left
      intro j _
      exact term_succ a l j
    rw [hshift, List.sum_map_mul_left]
  have red_linPartN : ∀ w : List Nat, (linPartNat GhN XN w).map red = redLin w := by
    intro w
    induction w with
    | nil => simp [linPartNat, redLin]
    | cons a l ih =>
      rw [linPartNat, map_add_matrix, map_mul_matrix, map_mul_matrix, ih,
        prod_map_red, red_G4, redLin_cons]
      ac_rfl
  have hOK' := hOK
  simp only [noZ4OK, Bool.and_eq_true, and_assoc] at hOK'
  obtain ⟨-, -, hMatZero, hEOK⟩ := hOK'
  have hMatZero' : ∀ k : Nat, k < 3 → (coeff2 k).toMat = 0 := by
    intro k hk
    have h := hMatZero
    simp only [List.all_eq_true, List.mem_range] at h
    exact matZero_eq_zero (coeff2 k).toMat (h k hk)
  obtain ⟨hsel, hsumEOK⟩ := EOK_spec hEOK
  let S : ZMod 2 := (noZ4Rels.map fun r =>
    ∑ a : Fin 10, ∑ b : Fin 10,
      (Csel r).toMat a b * redLin (rels[r]!) a b).sum
  have hpoint : ∀ r ∈ noZ4Rels,
      (∑ a : Fin 10, ∑ b : Fin 10,
        (Csel r).toMat a b * redLin (rels[r]!) a b) =
      (∑ a : Fin 10, ∑ b : Fin 10,
        (Csel r).toMat a b *
          ((Ebit (prod4 (rels[r]!)) a.val b.val).val : ZMod 2)) := by
    intro r hr
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    have hCval : (Csel r).toMat a b =
        if (r, a.val, b.val) ∈ noZ4Sel then 1 else 0 :=
      Csel_toMat_apply r a b
    by_cases hC : (Csel r).toMat a b = 0
    · simp [hC]
    · have hmem : (r, a.val, b.val) ∈ noZ4Sel := by
        by_contra hp
        rw [hCval, if_neg hp] at hC
        exact hC rfl
      have hC1 : (Csel r).toMat a b = 1 := by
        rw [hCval, if_pos hmem]
      obtain ⟨-, -, -, hPeq⟩ := hsel (r, a.val, b.val) hmem
      have hrOK : noZ4RelOK r = true := by
        have h := hRelAll
        simp only [List.all_eq_true] at h
        exact h r hr
      have hrel := rel_eq r hrOK
      dsimp only at hrel
      have hrelab := congrFun (congrFun hrel a) b
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at hrelab
      have hid : (1 : Matrix (Fin 10) (Fin 10) (ZMod 4)) a b =
          (idEntry a.val b.val : ZMod 4) := (idEntry_eq_one_apply a b).symm
      rw [hid] at hrelab
      have hPget : (rels[r]!.map GhN).prod a b =
          (prod4 (rels[r]!)).get a.val b.val := by
        change (rels[r]!.map G4).prod a b =
          (prod4 (rels[r]!)).get a.val b.val
        rw [← prod4_toMat (rels[r]!)]
        rw [Tab.get_eq_toMat (prod4 (rels[r]!)) a.isLt b.isLt]
      rw [hPget] at hrelab
      have hzero : (2 : ZMod 4) *
          (Ebit (prod4 (rels[r]!)) a.val b.val +
            linPartN (rels[r]!) a b) = 0 := by
        calc (2 : ZMod 4) *
              (Ebit (prod4 (rels[r]!)) a.val b.val +
                linPartN (rels[r]!) a b)
            = ((idEntry a.val b.val : ZMod 4) +
                2 * Ebit (prod4 (rels[r]!)) a.val b.val) +
                2 * linPartN (rels[r]!) a b -
                (idEntry a.val b.val : ZMod 4) := by ring
          _ = (prod4 (rels[r]!)).get a.val b.val +
                2 * linPartN (rels[r]!) a b -
                (idEntry a.val b.val : ZMod 4) := by rw [hPeq]
          _ = (idEntry a.val b.val : ZMod 4) -
                (idEntry a.val b.val : ZMod 4) := by rw [hrelab]
          _ = 0 := by ring
      have hredL := two_mul_add_eq_zero
        (Ebit (prod4 (rels[r]!)) a.val b.val)
        (linPartN (rels[r]!) a b) hzero
      have hRL : redLin (rels[r]!) a b =
          red (linPartN (rels[r]!) a b) := by
        have h := congrFun (congrFun (red_linPartN (rels[r]!)) a) b
        simpa [Matrix.map_apply] using h.symm
      rw [hC1, hRL, hredL, castHom_eq_val]
  have hS1 : S = 1 := by
    dsimp only [S]
    rw [show (noZ4Rels.map fun r =>
          ∑ a : Fin 10, ∑ b : Fin 10,
            (Csel r).toMat a b * redLin (rels[r]!) a b) =
        (noZ4Rels.map fun r =>
          ∑ a : Fin 10, ∑ b : Fin 10,
            (Csel r).toMat a b *
              ((Ebit (prod4 (rels[r]!)) a.val b.val).val : ZMod 2)) from
      List.map_congr_left hpoint]
    exact hsumEOK
  have hrel_sum : ∀ r ∈ noZ4Rels,
      (∑ a : Fin 10, ∑ b : Fin 10,
        (Csel r).toMat a b * redLin (rels[r]!) a b) =
      ∑ k ∈ Finset.range 3, ∑ p : Fin 10, ∑ q : Fin 10,
        coG (Csel r).toMat (rels[r]!) k p q * X2 k p q := by
    intro r hr
    have hrOK : noZ4RelOK r = true := by
      have h := hRelAll
      simp only [List.all_eq_true] at h
      exact h r hr
    obtain ⟨-, hw, -⟩ := rel_spec r hrOK
    have h := sum_C_redLin_eq X2 (Csel r).toMat (rels[r]!) hw
    simpa only [redLinG, redLin, termG, term] using h
  have hS0eq : S = ∑ k ∈ Finset.range 3, ∑ p : Fin 10, ∑ q : Fin 10,
      (coeff2 k).toMat p q * X2 k p q := by
    dsimp only [S]
    rw [List.map_congr_left hrel_sum]
    rw [list_sum_finset_sum noZ4Rels (Finset.range 3) (fun r k =>
      ∑ p : Fin 10, ∑ q : Fin 10,
        coG (Csel r).toMat (rels[r]!) k p q * X2 k p q)]
    apply Finset.sum_congr rfl
    intro k _
    rw [list_sum_finset_sum noZ4Rels Finset.univ (fun r p =>
      ∑ q : Fin 10, coG (Csel r).toMat (rels[r]!) k p q * X2 k p q)]
    apply Finset.sum_congr rfl
    intro p _
    rw [list_sum_finset_sum noZ4Rels Finset.univ (fun r q =>
      coG (Csel r).toMat (rels[r]!) k p q * X2 k p q)]
    apply Finset.sum_congr rfl
    intro q _
    rw [List.sum_map_mul_right]
    rw [coeff2_toMat_coG_apply]
  have hS0 : S = 0 := by
    rw [hS0eq]
    apply Finset.sum_eq_zero
    intro k hk
    rw [hMatZero' k (Finset.mem_range.mp hk)]
    simp
  rw [hS1] at hS0
  exact absurd hS0 (by decide)

end CFSG.Sporadic.Co2Jc
