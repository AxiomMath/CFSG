module

public import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalDetWitness
public import Certificates.Data.CoverCenterThreeCover

public section

namespace CFSG.SectionRank.OpsSpec

open CFSG.Blueprint CFSG.SectionRank.Native CFSG.SectionRank.LocalWitness
open CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest
open scoped Matrix commutatorElement

variable {M V : Type} {O : Ops M V} {p d : ℕ} (Sp : OpsSpec O p d)
include Sp

theorem evalWordN_spec [Inhabited M] {m : ℕ} {S : Submonoid (Matrix (Fin d) (Fin d) (ZMod p))}
    (G I : Array M) (g : Fin m → Sˣ)
    (hG : ∀ i : Fin m, Sp.WF G[i.val]! ∧ valHom S (g i) = Sp.toMat G[i.val]!)
    (hI : ∀ i : Fin m, Sp.WF I[i.val]! ∧ valHom S (g i)⁻¹ = Sp.toMat I[i.val]!) :
    ∀ w : List (Fin m × Bool),
      Sp.WF (O.evalWordN G I w) ∧ valHom S (evalW g w) = Sp.toMat (O.evalWordN G I w)
  | [] => ⟨Sp.one_wf, by rw [evalW_nil, map_one, Ops.evalWordN, Sp.toMat_one]⟩
  | x :: w => by
    obtain ⟨hw, ew⟩ := evalWordN_spec G I g hG hI w
    obtain ⟨i, b⟩ := x
    cases b
    · refine ⟨Sp.mul_wf (hI i).1 hw, ?_⟩
      rw [evalW_cons, Ops.evalWordN, map_mul, ew, ite_eq_right Bool.false_ne_true,
        Sp.toMat_mul (hI i).1 hw]
      simp only [Bool.cond_false]
      rw [(hI i).2]
    · refine ⟨Sp.mul_wf (hG i).1 hw, ?_⟩
      rw [evalW_cons, Ops.evalWordN, map_mul, ew, ite_eq_left rfl, Sp.toMat_mul (hG i).1 hw]
      simp only [Bool.cond_true]
      rw [(hG i).2]

theorem cover_of_check [Inhabited M] {m : ℕ} (D : CoverData m) (h : O.coverCheck D = true) :
    ∃ g : Fin m → (NativeSporadic.seedMonoid p d 1 D.seedA D.seedB)ˣ,
      (∀ i : Fin m, Sp.WF (O.coverGens D)[i.val]! ∧
        valHom _ (g i) = Sp.toMat (O.coverGens D)[i.val]!) ∧
      (∀ i : Fin m, D.invExp[i.val]! ≠ 0 ∧ g i ^ D.invExp[i.val]! = 1) ∧
      (∀ i, D.e i ≠ 0 → g i ^ D.e i = 1) ∧
      (∀ i, D.e i = 0 → g i = ⁅evalW g (D.cw i).1, evalW g (D.cw i).2⁆) ∧
      ∀ w ∈ D.rels, evalW g w = 1 := by
  set S := NativeSporadic.seedMonoid p d 1 D.seedA D.seedB
  unfold Ops.coverCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_finRange,
    true_implies] at h
  obtain ⟨⟨⟨⟨⟨⟨-, hprog⟩, hlen⟩, hlen'⟩, hregs⟩, hgen⟩, hrels⟩ := h
  set R := O.regsOf D.seedA D.seedB D.nregs D.prog
  set G := O.coverGens D
  set I := O.coverInvs D
  have hGi : ∀ i : Fin m, G[i.val]! = R[D.gens[i.val]]! := by
    intro i
    have hi : i.val < D.gens.length := by rw [hlen]; exact i.2
    simp only [G, Ops.coverGens]
    rw [getElem!_pos _ i.val (by simpa using hi)]
    simp [R]
  have hIi : ∀ i : Fin m, I[i.val]! = O.pow R[D.gens[i.val]]! (D.invExp[i.val]! - 1) := by
    intro i
    have hi : i.val < D.gens.length := by rw [hlen]; exact i.2
    have hi' : i.val < D.invExp.length := by rw [hlen']; exact i.2
    simp only [I, Ops.coverInvs]
    rw [getElem!_pos _ i.val (by simp [hi, hi']), getElem!_pos D.invExp i.val hi']
    simp [R]
  have hok : ∀ i : Fin m, Sp.WF G[i.val]! ∧ Sp.toMat G[i.val]! ∈ S := by
    intro i
    have hi : i.val < D.gens.length := by rw [hlen]; exact i.2
    rw [hGi]
    exact Sp.regsOf_ok (List.all_eq_true.mpr hprog) (hregs _ (List.getElem_mem hi))
  have hpow : ∀ i : Fin m, Sp.toMat G[i.val]! ^ D.invExp[i.val]! = 1 := fun i =>
    Sp.pow_eq_one_of_check (hok i).1 (hgen i).1.2
  have hne : ∀ i : Fin m, D.invExp[i.val]! ≠ 0 := fun i => (hgen i).1.1.ne'
  let g : Fin m → Sˣ := fun i => unitOf S (hok i).2 (hne i) (hpow i)
  have fg : ∀ i, valHom S (g i) = Sp.toMat G[i.val]! := fun i =>
    valHom_unitOf S (hok i).2 (hne i) (hpow i)
  have hgpow : ∀ i, g i ^ D.invExp[i.val]! = 1 := fun i => unitOf_pow S (hok i).2 (hne i) (hpow i)
  have hI : ∀ i : Fin m, Sp.WF I[i.val]! ∧ valHom S (g i)⁻¹ = Sp.toMat I[i.val]! := by
    intro i
    have hw := Sp.pow_spec (hok i).1 (D.invExp[i.val]! - 1)
    rw [hIi, ← hGi]
    refine ⟨hw.1, ?_⟩
    rw [hw.2, valHom_inv_of_pow S (hne i) (hgpow i), fg]
  have hW := Sp.evalWordN_spec G I g (fun i => ⟨(hok i).1, fg i⟩) hI
  refine ⟨g, fun i => ⟨(hok i).1, fg i⟩, fun i => ⟨hne i, hgpow i⟩, fun i hi => ?_,
    fun i hi => ?_, fun w hw => ?_⟩
  · have hc := (hgen i).2
    rw [ite_eq_right hi] at hc
    apply valHom_injective S
    rw [map_pow, map_one, fg]
    exact Sp.pow_eq_one_of_check (hok i).1 hc
  · have hc := (hgen i).2
    rw [ite_eq_left hi] at hc
    apply valHom_injective S
    have := Sp.toMat_eq (hok i).1 (hW _).1 hc
    rw [fg, this, ← (hW _).2, evalW_commW]
  · apply valHom_injective S
    have := Sp.toMat_eq (hW w).1 Sp.one_wf (hrels w hw)
    rw [(hW w).2, this, Sp.toMat_one, map_one]

end CFSG.SectionRank.OpsSpec

namespace CFSG.SectionRank.OpsSpec

open CFSG.Blueprint CFSG.SectionRank.Native CFSG.SectionRank.LocalWitness
open CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest
open scoped Matrix

variable {M V : Type} {O : Ops M V} {p d : ℕ} (Sp : OpsSpec O p d)

omit Sp in
theorem orbitVecs_succ [Inhabited M] [Inhabited V] (gens : Array M) (t : ℕ) (par lab : Array ℕ)
    (k : ℕ) : O.orbitVecs gens t par lab (k + 1) = (O.orbitVecs gens t par lab k).push
      (if k = 0 then O.unit t else
        O.vmul (O.orbitVecs gens t par lab k)[par[k]!]! gens[lab[k]!]!) := by
  unfold Ops.orbitVecs
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
  split_ifs <;> rfl

omit Sp in
theorem size_orbitVecs [Inhabited M] [Inhabited V] (gens : Array M) (t : ℕ) (par lab : Array ℕ) :
    ∀ k, (O.orbitVecs gens t par lab k).size = k
  | 0 => rfl
  | k + 1 => by rw [orbitVecs_succ, Array.size_push, size_orbitVecs gens t par lab k]

omit Sp in
theorem orbitVecs_getElem! [Inhabited M] [Inhabited V] (gens : Array M) (t : ℕ)
    (par lab : Array ℕ) {i k : ℕ} (hik : i < k) :
    (O.orbitVecs gens t par lab k)[i]! = (O.orbitVecs gens t par lab (i + 1))[i]! := by
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hik with h | rfl
    · rw [orbitVecs_succ, getElem!_pos _ i (by rw [Array.size_push, size_orbitVecs]; omega),
        Array.getElem_push_lt (by rw [size_orbitVecs]; exact h),
        ← getElem!_pos _ i (by rw [size_orbitVecs]; exact h), ih h]
    · rfl

omit Sp in
theorem orbitVecs_getElem!_eq [Inhabited M] [Inhabited V] (gens : Array M) (t : ℕ)
    (par lab : Array ℕ) {i n : ℕ} (hin : i < n) (hp : 0 < i → par[i]! < i) :
    (O.orbitVecs gens t par lab n)[i]! = if i = 0 then O.unit t else
      O.vmul (O.orbitVecs gens t par lab n)[par[i]!]! gens[lab[i]!]! := by
  have hsz : (O.orbitVecs gens t par lab i).size = i := size_orbitVecs gens t par lab i
  rw [orbitVecs_getElem! gens t par lab hin, orbitVecs_succ,
    getElem!_pos _ i (by rw [Array.size_push, size_orbitVecs]; omega)]
  have key : ∀ (A : Array V) (x : V), A.size = i → ∀ h : i < (A.push x).size,
      (A.push x)[i] = x := by
    intro A x hA h
    subst hA
    exact Array.getElem_push_eq
  rw [key _ _ hsz]
  split_ifs with h0
  · rfl
  · have hp' := hp (Nat.pos_of_ne_zero h0)
    rw [orbitVecs_getElem! gens t par lab hp',
      orbitVecs_getElem! gens t par lab (lt_trans hp' hin)]

include Sp

theorem toVec_orbitVecs [Inhabited M] [Inhabited V]
    {S : Submonoid (Matrix (Fin d) (Fin d) (ZMod p))} (gens : Array M) (g : ℕ → Sˣ)
    (fg : ∀ j < gens.size, Sp.WF gens[j]! ∧ valHom S (g j) = Sp.toMat gens[j]!) (t : ℕ)
    (par lab : Array ℕ) {n : ℕ}
    (htree : ∀ i < n, 0 < i → par[i]! < i ∧ lab[i]! < gens.size) :
    ∀ i < n, Sp.VWF (O.orbitVecs gens t par lab n)[i]! ∧
      Sp.toVec (O.orbitVecs gens t par lab n)[i]! =
        Sp.toVec (O.unit t) ᵥ* valHom S (treeElt par lab g i) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hin
    rw [orbitVecs_getElem!_eq gens t par lab hin fun h => (htree i hin h).1]
    split_ifs with h0
    · subst h0
      rw [treeElt_zero, map_one, Matrix.vecMul_one]
      exact ⟨Sp.unit_wf t, rfl⟩
    · obtain ⟨hp, hl⟩ := htree i hin (Nat.pos_of_ne_zero h0)
      obtain ⟨hw, hv⟩ := ih _ hp (lt_trans hp hin)
      refine ⟨Sp.vmul_wf hw (fg _ hl).1, ?_⟩
      rw [Sp.toVec_vmul hw (fg _ hl).1, hv, treeElt_of_lt par lab g (Nat.pos_of_ne_zero h0) hp,
        map_mul, ← (fg _ hl).2, Matrix.vecMul_vecMul]

omit Sp in
theorem lt_of_strictInc : ∀ (a : ℕ) (l : List ℕ), Ops.strictInc (a :: l) = true → ∀ c ∈ l, a < c
  | _, [], _ => by simp
  | a, b :: l, h => by
    simp only [Ops.strictInc, Bool.and_eq_true, decide_eq_true_eq] at h
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc'
    · exact h.1
    · exact lt_trans h.1 (lt_of_strictInc b l h.2 c hc')

omit Sp in
theorem nodup_of_strictInc : ∀ l : List ℕ, Ops.strictInc l = true → l.Nodup
  | [] , _ => List.nodup_nil
  | a :: l, h => by
    refine List.nodup_cons.mpr ⟨fun ha => absurd (lt_of_strictInc a l h a ha) (lt_irrefl a), ?_⟩
    cases l with
    | nil => exact List.nodup_nil
    | cons b l =>
      simp only [Ops.strictInc, Bool.and_eq_true] at h
      exact nodup_of_strictInc _ h.2

theorem le_card_closure_of_orbitOK [Inhabited M] [Inhabited V]
    {S : Submonoid (Matrix (Fin d) (Fin d) (ZMod p))} [Finite Sˣ] (gens : Array M) (g : ℕ → Sˣ)
    (fg : ∀ j < gens.size, Sp.WF gens[j]! ∧ valHom S (g j) = Sp.toMat gens[j]!) {t n : ℕ}
    {key : V → ℕ}
    (hkey : ∀ v w, Sp.VWF v → Sp.VWF w → Sp.toVec v = Sp.toVec w → key v = key w)
    {par lab : Array ℕ} (h : O.orbitOK gens t n key par lab = true) :
    n ≤ Nat.card (Subgroup.closure (g '' Set.Iio gens.size)) := by
  unfold Ops.orbitOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true] at h
  obtain ⟨⟨⟨⟨hpar, hlab⟩, hn⟩, htree⟩, hinc⟩ := h
  have htree' : ∀ i < n, 0 < i → par[i]! < i ∧ lab[i]! < gens.size := by
    intro i hi hpos
    rcases htree i hi with h0 | h1
    · omega
    · exact h1
  have hvec := Sp.toVec_orbitVecs gens g fg t par lab htree'
  have hmem : ∀ i < n, treeElt par lab g i ∈ Subgroup.closure (g '' Set.Iio gens.size) := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      rcases Nat.eq_zero_or_pos i with rfl | hpos
      · rw [treeElt_zero]; exact Subgroup.one_mem _
      · obtain ⟨hp, hl⟩ := htree' i hi hpos
        rw [treeElt_of_lt par lab g hpos hp]
        exact Subgroup.mul_mem _ (ih _ hp (lt_trans hp hi))
          (Subgroup.subset_closure ⟨_, hl, rfl⟩)
  set W := O.orbitVecs gens t par lab n
  have hW : W.size = n := size_orbitVecs gens t par lab n
  have hnodup : (W.toList.map key).Nodup :=
    (List.mergeSort_perm _ _).nodup_iff.mp (nodup_of_strictInc _ hinc)
  have hinj : ∀ i < n, ∀ j < n, treeElt par lab g i = treeElt par lab g j → i = j := by
    intro i hi j hj hij
    have hk : key W[i]! = key W[j]! := hkey _ _ (hvec i hi).1 (hvec j hj).1
      (by rw [(hvec i hi).2, (hvec j hj).2, hij])
    have hl : i < (W.toList.map key).length := by simp [hW, hi]
    have hl' : j < (W.toList.map key).length := by simp [hW, hj]
    refine (hnodup.getElem_inj_iff (hi := hl) (hj := hl')).mp ?_
    rw [List.getElem_map, List.getElem_map, Array.getElem_toList, Array.getElem_toList,
      ← getElem!_pos W i (by rw [hW]; exact hi), ← getElem!_pos W j (by rw [hW]; exact hj)]
    exact hk
  let F : Fin n → Subgroup.closure (g '' Set.Iio gens.size) := fun i =>
    ⟨treeElt par lab g i, hmem i i.2⟩
  have hF : Function.Injective F := fun a b hab =>
    Fin.ext (hinj a a.2 b b.2 (congrArg Subtype.val hab))
  simpa using Nat.card_le_card_of_injective F hF

end CFSG.SectionRank.OpsSpec
