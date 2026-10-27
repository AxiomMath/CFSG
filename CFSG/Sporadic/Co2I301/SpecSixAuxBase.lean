
module

public import CFSG.Sporadic.Co2Schreier.SixGroup
public import CFSG.Sporadic.Co2I301.Inputs

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Co2I301

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Co2Cert CFSG.Sporadic.Co2Schreier
  CFSG.Sporadic.SmallF2 CFSG.Certificates CFSG.Certificates.Native CFSG.RankThree.Native
  CFSG.RankThree.PartOne CFSG.HardMathSupport.Dickson.I271
open CFSG.ComponentClassification.CatalogueBAlternatingIsometry (basisMatrixEquiv
  basisMatrixEquiv_mulVec basisMatrixEquiv_val)
open scoped Matrix

private theorem getD_find?_range_lt {n : ℕ} (hn : 0 < n) (f : ℕ → Bool) :
    ((List.range n).find? f).getD 0 < n := by
  cases h : (List.range n).find? f with
  | none => simpa using hn
  | some m => simpa using List.mem_of_find?_eq_some h

private theorem sixCoord_lt (x : ℕ) : sixCoord x < 64 :=
  getD_find?_range_lt (by norm_num) _

private theorem sixCols_size (t : Array ℕ) : (sixCols t).size = 6 := by
  simp [sixCols]

private theorem sixCols_get (t : Array ℕ) {k : ℕ} (hk : k < 6) :
    (sixCols t)[k]! = sixCoord (sixImage t k) := by
  rw [sixCols, getElem!_pos _ k (by simpa using hk)]
  simp

private theorem sixCols_lt (t : Array ℕ) : ∀ k < (sixCols t).size, (sixCols t)[k]! < 2 ^ 6 := by
  intro k hk
  rw [sixCols_size] at hk
  rw [sixCols_get t hk]
  exact sixCoord_lt _

private theorem sixColsOK_spec {t : Array ℕ} (h : sixColsOK t = true) {k : ℕ} (hk : k < 6) :
    xorBits sixPacked (sixCols t)[k]! = sixImage t k :=
  beq_iff_eq.1 (allLt_spec h hk)

private theorem toVecD_xorBits_cols {cs : Array ℕ} (hc : cs.size = 6) (x : ℕ) :
    toVecD 6 (xorBits cs x) =
      (Matrix.of fun j k : Fin 6 => toVecD 6 cs[(k : ℕ)]! j) *ᵥ toVecD 6 x := by
  rw [xorBits, foldl_xor_toVecD, toVecD_zero, zero_add]
  funext j
  rw [Matrix.mulVec, dotProduct, Finset.sum_apply, hc, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.of_apply, toVecD_apply 6 x k]
  by_cases hx : x.testBit k
  · simp [hx]
  · simp [hx]

private theorem perm63Of_get (t : Array ℕ) {p : ℕ} (hp : p < 63) :
    (perm63Of t)[p]! = xorBits (sixCols t) (p + 1) - 1 := by
  change (Array.ofFn (n := 63) fun q : Fin 63 => xorBits (sixCols t) (q.val + 1) - 1)[p]! = _
  rw [getElem!_ofFn_nat _ hp]

private theorem perm63Of_lt (t : Array ℕ) {p : ℕ} (hp : p < 63) : (perm63Of t)[p]! < 63 := by
  rw [perm63Of_get t hp]
  have := xorBits_lt (sixCols_lt t) (p + 1)
  norm_num at this
  omega

section Action

theorem sixAction_sixBasis_cols (c : locC) {t : Array ℕ}
    (ht : Rep 2300 t (c : Equiv.Perm (Fin 2300))) (hok : sixColsOK t = true) (k : Fin 6) :
    sixAction c (sixBasis k) = ∑ j : Fin 6, toVecD 6 (sixCols t)[(k : ℕ)]! j • sixBasis j := by
  apply Subtype.ext
  rw [sixAction_apply, sixBasis_apply, linC_sixVec, ← toVecD_sixImage ht k,
    ← sixColsOK_spec hok k.2, ← sum_sixVec, Submodule.coe_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Submodule.coe_smul, sixBasis_apply, toVecD_apply]
  split_ifs <;> simp

theorem toMatrix_sixAction_cols (c : locC) {t : Array ℕ}
    (ht : Rep 2300 t (c : Equiv.Perm (Fin 2300))) (hok : sixColsOK t = true) :
    LinearMap.toMatrix sixBasis sixBasis (sixAction c : V6 →ₗ[ZMod 2] V6) =
      Matrix.of fun j k : Fin 6 => toVecD 6 (sixCols t)[(k : ℕ)]! j := by
  ext j k
  rw [LinearMap.toMatrix_apply, LinearEquiv.coe_coe, sixAction_sixBasis_cols c ht hok,
    Module.Basis.repr_sum_self, Matrix.of_apply]

private theorem equivFun_sixAction_sixPt (c : locC) {t : Array ℕ}
    (ht : Rep 2300 t (c : Equiv.Perm (Fin 2300))) (hok : sixColsOK t = true) (p : ℕ) :
    sixBasis.equivFun (sixAction c (sixPt p)) = toVecD 6 (xorBits (sixCols t) (p + 1)) := by
  rw [← basisMatrixEquiv_mulVec sixBasis (sixAction c) (sixPt p), basisMatrixEquiv_val,
    toMatrix_sixAction_cols c ht hok, sixPt, LinearEquiv.apply_symm_apply,
    ← toVecD_xorBits_cols (sixCols_size t)]

private theorem xorBits_sixCols_ne_zero (c : locC) {t : Array ℕ}
    (ht : Rep 2300 t (c : Equiv.Perm (Fin 2300))) (hok : sixColsOK t = true) {p : ℕ}
    (hp : p < 63) : xorBits (sixCols t) (p + 1) ≠ 0 := by
  intro h0
  have h := equivFun_sixAction_sixPt c ht hok p
  rw [h0, toVecD_zero] at h
  have h1 : sixAction c (sixPt p) = 0 :=
    sixBasis.equivFun.injective (by rw [h, map_zero])
  exact sixPt_ne_zero hp ((LinearEquiv.map_eq_zero_iff _).1 h1)

theorem sixAction_sixPt_cols (c : locC) {t : Array ℕ}
    (ht : Rep 2300 t (c : Equiv.Perm (Fin 2300))) (hok : sixColsOK t = true) {p : ℕ}
    (hp : p < 63) : sixAction c (sixPt p) = sixPt ((perm63Of t)[p]!) := by
  apply sixBasis.equivFun.injective
  rw [equivFun_sixAction_sixPt c ht hok p, sixPt, LinearEquiv.apply_symm_apply,
    perm63Of_get t hp]
  have := xorBits_sixCols_ne_zero c ht hok hp
  congr 1
  omega

theorem rep_perm63Of (c : locC) {t : Array ℕ} (ht : Rep 2300 t (c : Equiv.Perm (Fin 2300)))
    (hok : sixColsOK t = true) : Rep 63 (perm63Of t) (toPerm63 (sixAction c)) := by
  intro x
  have h1 := congrArg Subtype.val (toPerm63_apply (sixAction c) x)
  change sixPt (toPerm63 (sixAction c) x : ℕ) = sixAction c (sixPt x) at h1
  rw [sixAction_sixPt_cols c ht hok x.2] at h1
  exact sixPt_injective (perm63Of_lt t x.2) (toPerm63 (sixAction c) x).2 h1.symm

end Action

private theorem rep_word63_foldl {g : Array (Array ℕ)} {Y : List (Equiv.Perm (Fin 63))} :
    ∀ (w : List ℕ) (acc : Array ℕ) (A : Equiv.Perm (Fin 63)), Rep 63 acc A →
      (∀ i ∈ w, Rep 63 g[i]! (Y.getD i 1)) →
      Rep 63 (w.foldl (fun acc i => compA 63 acc g[i]!) acc)
        (A * (w.map fun i => Y.getD i 1).prod)
  | [], acc, A, hA, _ => by simpa using hA
  | i :: w, acc, A, hA, hw => by
    rw [List.foldl_cons, List.map_cons, List.prod_cons, ← mul_assoc]
    exact rep_word63_foldl w _ _ (rep_compA hA (hw i List.mem_cons_self))
      fun j hj => hw j (List.mem_cons_of_mem _ hj)

theorem rep_word63 {g : Array (Array ℕ)} {Y : List (Equiv.Perm (Fin 63))} (w : List ℕ)
    (hw : ∀ i ∈ w, Rep 63 g[i]! (Y.getD i 1)) :
    Rep 63 (word63 g w) ((w.map fun i => Y.getD i 1).prod) := by
  have := rep_word63_foldl w (idA 63) 1 rep_idA hw
  rw [one_mul] at this
  exact this

private theorem invCand_eq_foldl_six (n : ℕ) (t : Array ℕ) :
    invCand n t = (List.range n).foldl (fun r i => r.set! t[i]! i) (Array.replicate n 0) := by
  unfold invCand
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl,
    Std.Legacy.Range.size]
  simp only [Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, bind_pure, List.range_eq_range']
  rfl

private theorem rep_invCand_six {n : ℕ} {t : Array ℕ} {g : Equiv.Perm (Fin n)}
    (ht : Rep n t g) : Rep n (invCand n t) g⁻¹ := by
  have key : ∀ k ≤ n, ((List.range k).foldl (fun r i => r.set! t[i]! i)
      (Array.replicate n 0)).size = n ∧ ∀ i < k, ((List.range k).foldl (fun r i => r.set! t[i]! i)
      (Array.replicate n 0))[t[i]!]! = i := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      obtain ⟨hs, hi⟩ := ih (by omega)
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      set r := (List.range k).foldl (fun r i => r.set! t[i]! i) (Array.replicate n 0)
      have htk : t[k]! < n := ht.lt (by omega)
      refine ⟨by rw [Array.size_set!, hs], fun i hik => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hik with hlt | rfl
      · have hne : t[i]! ≠ t[k]! := by
          intro e
          rw [ht.apply (by omega : i < n), ht.apply (by omega : k < n)] at e
          have := g.injective (Fin.ext e)
          simp at this
          omega
        rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hne)]
        exact hi i hlt
      · rw [Array.getElem!_set!_self _ _ _ (by rw [hs]; exact htk)]
  intro x
  obtain ⟨hs, hi⟩ := key n le_rfl
  rw [invCand_eq_foldl_six]
  have e : t[(g⁻¹ x : Fin n).val]! = x.val := by
    rw [ht.apply (g⁻¹ x).2]
    simp
  rw [← e, hi _ (g⁻¹ x).2]

private theorem anyLt_exists_six {n : ℕ} {p : ℕ → Bool}
    (h : CFSG.Sporadic.Schreier.Co3.Native.anyLt n p = true) : ∃ i < n, p i = true := by
  unfold CFSG.Sporadic.Schreier.Co3.Native.anyLt at h
  rw [Nat.any_eq_finRange_any, List.any_eq_true] at h
  obtain ⟨⟨i, hi⟩, -, h⟩ := h
  exact ⟨i, hi, h⟩

theorem leaf63_spec {HL : Array (Array ℕ)} {Y : ℕ → Equiv.Perm (Fin 63)}
    (hY : ∀ t < HL.size, Rep 63 HL[t]! (Y t)) {a : Array ℕ} {G : Equiv.Perm (Fin 63)}
    (hG : Rep 63 a G) (h : leaf63 HL a = true) (hGG : G * G = 1) (hG1 : G ≠ 1) :
    ∃ t < HL.size, ¬ Commute G (Y t * G * (Y t)⁻¹) := by
  have e1 : eqA 63 (compA 63 a a) (idA 63) = true := (eqA_iff (rep_compA hG hG) rep_idA).2 hGG
  have e2 : eqA 63 a (idA 63) = false := by
    cases h2 : eqA 63 a (idA 63)
    · rfl
    · exact absurd ((eqA_iff hG rep_idA).1 h2) hG1
  simp only [leaf63, e1, e2, Bool.not_true, Bool.false_or] at h
  obtain ⟨t, ht, hc⟩ := anyLt_exists_six h
  refine ⟨t, ht, fun hcomm => ?_⟩
  have hYt := hY t ht
  have hb : Rep 63 (compA 63 HL[t]! (compA 63 a (invCand 63 HL[t]!))) (Y t * G * (Y t)⁻¹) := by
    rw [mul_assoc]
    exact rep_compA hYt (rep_compA hG (rep_invCand_six hYt))
  have hc' : comm63 a (compA 63 HL[t]! (compA 63 a (invCand 63 HL[t]!))) = true :=
    (eqA_iff (rep_compA hG hb) (rep_compA hb hG)).2 hcomm.eq
  rw [hc'] at hc
  exact absurd hc (by decide)

section Small

end Small

private theorem hl63_size : (hl63 ()).size = hlWords.length := by
  simp [hl63]

private theorem hl63_get {t : ℕ} (ht : t < hlWords.length) :
    (hl63 ())[t]! = word63 #[perm63Of (i301K1 ()), perm63Of (i301K2 ()), perm63Of (i301D ())]
      (hlWords.getD t []) := by
  rw [List.getD_eq_getElem _ _ ht, getElem!_pos _ t (by rw [hl63_size]; exact ht)]
  simp [hl63]

private theorem hlWords_letters : ∀ w ∈ hlWords, ∀ i ∈ w, i < 3 := by
  decide

section Main

end Main

end CFSG.Sporadic.Co2I301
