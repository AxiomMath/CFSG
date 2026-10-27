module

public import CFSG.LocalAnalysis.StandardType.GGResE6DepCardSixDefs
public import CFSG.LocalAnalysis.StandardType.GGDepECheck
public import CFSG.Mathlib.Decide.Nodup

public section

namespace CFSG.StandardType

open Certificates.DepASmall

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def cs6RootL (i : Nat) : List Nat :=
  if i = 0 then [0, 1, 0, 2, 1, 0]
  else (List.range 6).map fun j => if j + 1 = i then 1 else 0

@[expose] def cs6AlphaL (i : Nat) : List Nat :=
  (List.range 6).map fun j => if h : j < 5 then ggDepAThreeE6Res 3 i (j + 1) else 0

@[expose] def cs6Gen (ha aa : List Nat) (g : Nat) : GGDepANPair :=
  if g < 6 then (cs6RootL g, cs6AlphaL g) else (ha, aa)

@[expose] def cs6Word (ha aa : List Nat) (q : GGDepANPair) (w : List Nat) : GGDepANPair :=
  w.foldr (fun g acc => ggDepANConj 3 acc (cs6Gen ha aa g)) q

@[expose] def cs6XL : List Nat := [0, 0, 0, 0, 0, 1]

@[expose] def cs6Apply (ha aa : List Nat) (w : List Nat) (v : List Nat) : List Nat :=
  w.foldr (fun g acc =>
    ggDepANSub 3 acc (ggDepANSmul 3 (ggDepANDot 3 (cs6Gen ha aa g).2 acc) (cs6Gen ha aa g).1)) v

@[expose] def cs6Orbit (ha aa : List Nat) (tree : List (Nat × Nat)) : List (List Nat) :=
  tree.foldl (fun acc e =>
    acc ++ [ggDepANSub 3 (acc.getD e.1 [])
      (ggDepANSmul 3 (ggDepANDot 3 (cs6Gen ha aa e.2).2 (acc.getD e.1 []))
        (cs6Gen ha aa e.2).1)]) [cs6XL]

@[expose] def cs6WitOK (jj : Fin 5) (pi yi : Nat) (ha aa : List Nat) : CS6Data.Wit → Bool
  | .tv g1 w1 g2 w2 =>
      ggDepANTestPair 3 (cs6Word ha aa (cs6Gen ha aa g1) w1) (cs6Word ha aa (cs6Gen ha aa g2) w2)
  | .inL k w lam =>
      decide (k < 6) && decide (lam = 1 ∨ lam = 2) && w.all (fun g => decide (g < 6)) &&
        (cs6Word ha aa (cs6Gen ha aa k) w).1 == ggDepANSmul 3 lam ha &&
        (cs6Word ha aa (cs6Gen ha aa k) w).2 == ggDepANSmul 3 lam aa
  | .orb w =>
      let y := (CS6Data.yReps.getD jj []).getD yi []
      cs6Apply ha aa w cs6XL == y || cs6Apply ha aa w cs6XL == ggDepANSmul 3 2 y
  | .cnt tree =>
      cs6PatDet jj pi == 6 && decide (121 ≤ tree.length) &&
        (List.range tree.length).all (fun k => match tree[k]? with
          | none => false
          | some e => decide (e.1 < k + 1) && decide (e.2 ≤ 6)) &&
        CFSG.Decide.bitsetNodup ((cs6Orbit ha aa tree).map (ggDepAThreeKey 3))

@[expose] def cs6CellsAt (jj pi yi : Nat) : Option (List (List Nat × List Nat × CS6Data.Wit)) :=
  match CS6Data.cells.find? (fun e => e.1 == jj && e.2.1 == pi && e.2.2.1 == yi) with
  | none => none
  | some e => some e.2.2.2

@[expose] def cs6CheckJJ (jj : Fin 5) : Bool :=
  (List.range (cs6NumPat jj)).all fun pi =>
    (List.range ((CS6Data.yReps.getD jj []).length)).all fun yi =>
      let pat := (CS6Data.patterns.getD jj []).getD pi []
      let y := (CS6Data.yReps.getD jj []).getD yi []
      let HS := (ggDepEAllVecs 3 6).filter fun ha =>
        (List.finRange 4).all fun i =>
          ggDepANDot 3 (cs6AlphaL (cs6J jj i).val) ha == (pat.getD i (0, 0)).1
      let AS := (ggDepEAllVecs 3 6).filter fun aa =>
        (List.finRange 4).all (fun i =>
          ggDepANDot 3 aa (cs6RootL (cs6J jj i).val) == (pat.getD i (0, 0)).2) &&
          ggDepANDot 3 aa y == 0
      match cs6CellsAt jj.val pi yi with
      | none => false
      | some lst =>
          HS.all fun ha => AS.all fun aa =>
            if ggDepANDot 3 aa ha == 2 then
              lst.any fun e => (ha == e.1 && aa == e.2.1) && cs6WitOK jj pi yi ha aa e.2.2
            else true

@[expose] def cs6Check : Bool := (List.finRange 5).all cs6CheckJJ

theorem cs6CheckJJ_0 : cs6CheckJJ (0 : Fin 5) = true := by decide +kernel
theorem cs6CheckJJ_1 : cs6CheckJJ (1 : Fin 5) = true := by decide +kernel
theorem cs6CheckJJ_2 : cs6CheckJJ (2 : Fin 5) = true := by decide +kernel
theorem cs6CheckJJ_3 : cs6CheckJJ (3 : Fin 5) = true := by decide +kernel
theorem cs6CheckJJ_4 : cs6CheckJJ (4 : Fin 5) = true := by decide +kernel

theorem cs6Check_eq_true : cs6Check = true := by
  rw [cs6Check, show List.finRange 5 = [0, 1, 2, 3, 4] from rfl]
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.true_and, cs6CheckJJ_0,
    cs6CheckJJ_1, cs6CheckJJ_2, cs6CheckJJ_3, cs6CheckJJ_4]

private lemma cs6RootL_length (i : Nat) : (cs6RootL i).length = 6 := by
  unfold cs6RootL; split_ifs <;> simp

private lemma cs6AlphaL_length (i : Nat) : (cs6AlphaL i).length = 6 := by
  simp [cs6AlphaL]

private lemma cs6_toZ_root (i : Fin 6) :
    ggDepANToZ 3 6 (cs6RootL i.val) = cs6Root i := by
  fin_cases i <;> funext j <;> fin_cases j <;> decide

private lemma cs6_toZ_alpha (i : Fin 6) :
    ggDepANToZ 3 6 (cs6AlphaL i.val) = cs6Alpha i := by
  fin_cases i <;> funext j <;> fin_cases j <;> decide

private lemma cs6_alpha_root_self (i : Fin 6) : ggDepAdot (cs6Alpha i) (cs6Root i) = 2 := by
  fin_cases i <;> decide

private lemma cs6_toZ_XL : ggDepANToZ 3 6 cs6XL = (cs6X : CS6E) := by
  funext j; fin_cases j <;> decide

private lemma cs6_gen_length1 {ha aa : List Nat} (hha : ha.length = 6) (haa : aa.length = 6)
    (g : Nat) : (cs6Gen ha aa g).1.length = 6 := by
  unfold cs6Gen; split_ifs
  · exact cs6RootL_length g
  · exact hha

private lemma cs6_gen_length2 {ha aa : List Nat} (hha : ha.length = 6) (haa : aa.length = 6)
    (g : Nat) : (cs6Gen ha aa g).2.length = 6 := by
  unfold cs6Gen; split_ifs
  · exact cs6AlphaL_length g
  · exact haa

private lemma cs6_gen_dot {ha aa : List Nat} (hha : ha.length = 6) (haa : aa.length = 6)
    (hdot : ggDepANDot 3 aa ha = 2 % 3) (g : Nat) :
    ggDepAdot (ggDepANToZ 3 6 (cs6Gen ha aa g).2) (ggDepANToZ 3 6 (cs6Gen ha aa g).1) = 2 := by
  by_cases h : g < 6
  · simp only [cs6Gen, if_pos h]
    rw [cs6_toZ_root ⟨g, h⟩, cs6_toZ_alpha ⟨g, h⟩]
    exact cs6_alpha_root_self ⟨g, h⟩
  · simp only [cs6Gen, if_neg h]
    rw [← ggDepANDot_cast (p := 3) (N := 6) aa ha haa hha, hdot, ZMod.natCast_mod]
    rfl

private lemma cs6_gen_mem {ha aa : List Nat} (g : Nat) :
    ggDepARefl (ggDepANToZ 3 6 (cs6Gen ha aa g).1) (ggDepANToZ 3 6 (cs6Gen ha aa g).2) ∈
      Submonoid.closure (Set.range cs6Refl ∪
        {ggDepARefl (ggDepANToZ 3 6 ha) (ggDepANToZ 3 6 aa)}) := by
  by_cases h : g < 6
  · simp only [cs6Gen, if_pos h]
    rw [cs6_toZ_root ⟨g, h⟩, cs6_toZ_alpha ⟨g, h⟩]
    exact Submonoid.subset_closure (Or.inl ⟨⟨g, h⟩, rfl⟩)
  · simp only [cs6Gen, if_neg h]
    exact Submonoid.subset_closure (Or.inr rfl)

private lemma cs6_word_cons (ha aa : List Nat) (q : GGDepANPair) (g : Nat) (w : List Nat) :
    cs6Word ha aa q (g :: w) = ggDepANConj 3 (cs6Word ha aa q w) (cs6Gen ha aa g) := rfl

private lemma cs6_word_length {ha aa : List Nat} (hha : ha.length = 6) (haa : aa.length = 6)
    (w : List Nat) (q : GGDepANPair) (hq1 : q.1.length = 6) (hq2 : q.2.length = 6) :
    (cs6Word ha aa q w).1.length = 6 ∧ (cs6Word ha aa q w).2.length = 6 := by
  induction w generalizing q with
  | nil => simpa [cs6Word] using ⟨hq1, hq2⟩
  | cons g w ih =>
      rw [cs6_word_cons]
      exact l05nNC_conj_length (ih q hq1 hq2).1 (ih q hq1 hq2).2
        (cs6_gen_length1 hha haa g) (cs6_gen_length2 hha haa g)

private lemma cs6_word_gen {ha aa : List Nat} (hha : ha.length = 6) (haa : aa.length = 6)
    (S : Submonoid (Module.End (ZMod 3) CS6E)) (P : Nat → Prop)
    (hdg : ∀ g, P g → ggDepAdot (ggDepANToZ 3 6 (cs6Gen ha aa g).2)
      (ggDepANToZ 3 6 (cs6Gen ha aa g).1) = 2)
    (hmem : ∀ g, P g → ggDepARefl (ggDepANToZ 3 6 (cs6Gen ha aa g).1)
      (ggDepANToZ 3 6 (cs6Gen ha aa g).2) ∈ S)
    (w : List Nat) (hw : ∀ g ∈ w, P g) (q : GGDepANPair) (hq1 : q.1.length = 6)
    (hq2 : q.2.length = 6)
    (hdq : ggDepAdot (ggDepANToZ 3 6 q.2) (ggDepANToZ 3 6 q.1) = 2)
    (hq : ggDepARefl (ggDepANToZ 3 6 q.1) (ggDepANToZ 3 6 q.2) ∈ S) :
    ggDepAdot (ggDepANToZ 3 6 (cs6Word ha aa q w).2)
        (ggDepANToZ 3 6 (cs6Word ha aa q w).1) = 2 ∧
      ggDepARefl (ggDepANToZ 3 6 (cs6Word ha aa q w).1)
        (ggDepANToZ 3 6 (cs6Word ha aa q w).2) ∈ S := by
  induction w generalizing q with
  | nil => exact ⟨by simpa [cs6Word] using hdq, by simpa [cs6Word] using hq⟩
  | cons g w ih =>
      have hPg : P g := hw g (by simp)
      have hw' : ∀ t ∈ w, P t := fun t ht => hw t (by simp [ht])
      rw [cs6_word_cons]
      have hQ1 : (cs6Word ha aa q w).1.length = 6 :=
        (cs6_word_length hha haa w q hq1 hq2).1
      have hQ2 : (cs6Word ha aa q w).2.length = 6 :=
        (cs6_word_length hha haa w q hq1 hq2).2
      have hG1 : (cs6Gen ha aa g).1.length = 6 := cs6_gen_length1 hha haa g
      have hG2 : (cs6Gen ha aa g).2.length = 6 := cs6_gen_length2 hha haa g
      obtain ⟨ihd, ihm⟩ := ih hw' q hq1 hq2 hdq hq
      obtain ⟨hc1, hc2⟩ := l05nNC_toZ_conj (p := 3) (N := 6)
        (q := cs6Word ha aa q w) (g := cs6Gen ha aa g) hQ1 hQ2 hG1 hG2
      rw [hc1, hc2]
      refine ⟨l05nNC_conj_dot _ _ _ _ ihd (hdg g hPg), ?_⟩
      rw [← l05nNC_refl_conj (ggDepANToZ 3 6 (cs6Word ha aa q w).1)
        (ggDepANToZ 3 6 (cs6Word ha aa q w).2)
        (ggDepANToZ 3 6 (cs6Gen ha aa g).1)
        (ggDepANToZ 3 6 (cs6Gen ha aa g).2) (hdg g hPg)]
      exact Submonoid.mul_mem _ (Submonoid.mul_mem _ (hmem g hPg) ihm) (hmem g hPg)

private lemma cs6_refl_smul_center (k : ZMod 3) (c f : CS6E) (hk : k * k = 1) :
    ggDepARefl (k • c) (k • f) = ggDepARefl c f := by
  apply LinearMap.ext; intro v; ext j
  simp only [l05nNC_refl_apply, Pi.sub_apply, Pi.smul_apply, l05nNC_dot_smul_left, smul_eq_mul]
  congr 1
  calc k * ggDepAdot f v * (k * c j) = (k * k) * (ggDepAdot f v * c j) := by ring
    _ = ggDepAdot f v * c j := by rw [hk, one_mul]

private lemma cs6_refl_toZ_sub {c f v : List Nat} (hc : c.length = 6) (hf : f.length = 6)
    (hv : v.length = 6) :
    ggDepARefl (ggDepANToZ 3 6 c) (ggDepANToZ 3 6 f) (ggDepANToZ 3 6 v) =
      ggDepANToZ 3 6 (ggDepANSub 3 v (ggDepANSmul 3 (ggDepANDot 3 f v) c)) := by
  rw [l05nNC_refl_apply, ← ggDepANDot_cast f v hf hv,
    l05nNC_toZ_sub hv (l05nNC_smul_length hc), l05nNC_toZ_smul hc]

private lemma cs6Apply_length (ha aa : List Nat) (hha : ha.length = 6) (haa : aa.length = 6)
    (w : List Nat) (v : List Nat) (hv : v.length = 6) : (cs6Apply ha aa w v).length = 6 := by
  induction w with
  | nil => simpa [cs6Apply] using hv
  | cons g w ih =>
      simp only [cs6Apply, List.foldr_cons]
      exact l05nNC_sub_length ih (l05nNC_smul_length (cs6_gen_length1 hha haa g))

@[expose] def cs6End (ha aa : List Nat) : List Nat → Module.End (ZMod 3) CS6E
  | [] => 1
  | g :: w => ggDepARefl (ggDepANToZ 3 6 (cs6Gen ha aa g).1)
      (ggDepANToZ 3 6 (cs6Gen ha aa g).2) * cs6End ha aa w

private lemma cs6End_apply (ha aa : List Nat) (hha : ha.length = 6) (haa : aa.length = 6)
    (w : List Nat) : cs6End ha aa w cs6X = ggDepANToZ 3 6 (cs6Apply ha aa w cs6XL) := by
  induction w with
  | nil => simpa [cs6End, cs6Apply] using cs6_toZ_XL.symm
  | cons g w ih =>
      simp only [cs6End, cs6Apply, List.foldr_cons]
      rw [Module.End.mul_apply, ih]
      exact cs6_refl_toZ_sub (cs6_gen_length1 hha haa g) (cs6_gen_length2 hha haa g)
        (cs6Apply_length ha aa hha haa w cs6XL (by simp [cs6XL]))

private lemma cs6End_mem (ha aa : List Nat) (w : List Nat) :
    cs6End ha aa w ∈ Submonoid.closure (Set.range cs6Refl ∪
      {ggDepARefl (ggDepANToZ 3 6 ha) (ggDepANToZ 3 6 aa)}) := by
  induction w with
  | nil => exact Submonoid.one_mem _
  | cons g w ih =>
      simp only [cs6End]
      exact Submonoid.mul_mem _ (cs6_gen_mem g) ih

private def cs6OrbitStep (ha aa : List Nat)
    (st : List (List Nat) × List (Module.End (ZMod 3) CS6E)) (e : Nat × Nat) :
    List (List Nat) × List (Module.End (ZMod 3) CS6E) :=
  let g := cs6Gen ha aa e.2
  (st.1 ++ [ggDepANSub 3 (st.1.getD e.1 [])
      (ggDepANSmul 3 (ggDepANDot 3 g.2 (st.1.getD e.1 [])) g.1)],
   st.2 ++ [ggDepARefl (ggDepANToZ 3 6 g.1) (ggDepANToZ 3 6 g.2) * st.2.getD e.1 1])

@[expose] def cs6OrbitStepV (ha aa : List Nat) (acc : List (List Nat)) (e : Nat × Nat) :
    List (List Nat) :=
  acc ++ [ggDepANSub 3 (acc.getD e.1 [])
    (ggDepANSmul 3 (ggDepANDot 3 (cs6Gen ha aa e.2).2 (acc.getD e.1 []))
      (cs6Gen ha aa e.2).1)]

private lemma cs6_orbit_vec_eq (ha aa : List Nat) (tree : List (Nat × Nat)) :
    cs6Orbit ha aa tree = tree.foldl (cs6OrbitStepV ha aa) [cs6XL] := by
  rfl

private lemma cs6_fold_fst (ha aa : List Nat) (tree : List (Nat × Nat))
    (v : List (List Nat)) (w : List (Module.End (ZMod 3) CS6E)) :
    (tree.foldl (cs6OrbitStep ha aa) (v, w)).1 = tree.foldl (cs6OrbitStepV ha aa) v := by
  induction tree generalizing v w with
  | nil => rfl
  | cons e t ih =>
      rw [List.foldl_cons, List.foldl_cons]
      exact ih _ _

private lemma cs6_getD_append_singleton {α : Type*} (l : List α) (a d : α) {n : ℕ}
    (h : n = l.length) : (l ++ [a]).getD n d = a := by
  subst h
  rw [List.getD_append_right (l := l) (l' := [a]) (d := d) (n := l.length) (le_refl _),
    Nat.sub_self]
  rfl

private lemma cs6_fold_inv (ha aa : List Nat) (hha : ha.length = 6) (haa : aa.length = 6)
    (tree : List (Nat × Nat)) (v : List (List Nat))
    (w : List (Module.End (ZMod 3) CS6E))
    (hlen : v.length = w.length)
    (hvlen : ∀ k, k < v.length → (v.getD k []).length = 6)
    (hax : ∀ k, k < v.length → w.getD k 1 cs6X = ggDepANToZ 3 6 (v.getD k []))
    (hcl : ∀ k, k < w.length → w.getD k 1 ∈ Submonoid.closure (Set.range cs6Refl ∪
      {ggDepARefl (ggDepANToZ 3 6 ha) (ggDepANToZ 3 6 aa)}))
    (hpar : ∀ k, k < tree.length → (tree.getD k (0, 0)).1 < v.length + k) :
    (tree.foldl (cs6OrbitStep ha aa) (v, w)).1.length =
        (tree.foldl (cs6OrbitStep ha aa) (v, w)).2.length ∧
      (∀ k, k < (tree.foldl (cs6OrbitStep ha aa) (v, w)).1.length →
        ((tree.foldl (cs6OrbitStep ha aa) (v, w)).1.getD k []).length = 6) ∧
      (∀ k, k < (tree.foldl (cs6OrbitStep ha aa) (v, w)).1.length →
        (tree.foldl (cs6OrbitStep ha aa) (v, w)).2.getD k 1 cs6X =
          ggDepANToZ 3 6 ((tree.foldl (cs6OrbitStep ha aa) (v, w)).1.getD k [])) ∧
      (∀ k, k < (tree.foldl (cs6OrbitStep ha aa) (v, w)).2.length →
        (tree.foldl (cs6OrbitStep ha aa) (v, w)).2.getD k 1 ∈
          Submonoid.closure (Set.range cs6Refl ∪
            {ggDepARefl (ggDepANToZ 3 6 ha) (ggDepANToZ 3 6 aa)})) := by
  induction tree generalizing v w with
  | nil => exact ⟨hlen, hvlen, hax, hcl⟩
  | cons e t ih =>
      rw [List.foldl_cons]
      apply ih
      · simp only [cs6OrbitStep, List.length_append, List.length_singleton]
        omega
      · intro k hk
        simp only [cs6OrbitStep, List.length_append, List.length_singleton] at hk
        simp only [cs6OrbitStep]
        by_cases hkv : k < v.length
        · rw [List.getD_append _ _ _ _ hkv]; exact hvlen k hkv
        · have hk' : k = v.length := by omega
          subst hk'
          rw [List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self]
          simp only [List.getD_cons_zero]
          exact l05nNC_sub_length (hvlen e.1 (by have := hpar 0 (by simp); simpa using this))
            (l05nNC_smul_length (cs6_gen_length1 hha haa e.2))
      · intro k hk
        simp only [cs6OrbitStep, List.length_append, List.length_singleton] at hk
        simp only [cs6OrbitStep]
        by_cases hkv : k < v.length
        · rw [List.getD_append _ _ _ _ (by rw [← hlen]; exact hkv),
            List.getD_append _ _ _ _ hkv, hax k hkv]
        · have hk' : k = v.length := by omega
          subst hk'
          rw [cs6_getD_append_singleton w
                (ggDepARefl (ggDepANToZ 3 6 (cs6Gen ha aa e.2).1)
                  (ggDepANToZ 3 6 (cs6Gen ha aa e.2).2) * w.getD e.1 1) 1 hlen,
            cs6_getD_append_singleton v
                (ggDepANSub 3 (v.getD e.1 [])
                  (ggDepANSmul 3 (ggDepANDot 3 (cs6Gen ha aa e.2).2 (v.getD e.1 []))
                    (cs6Gen ha aa e.2).1)) [] rfl]
          have hpe : e.1 < v.length := by have := hpar 0 (by simp); simpa using this
          have hve : (v.getD e.1 []).length = 6 := hvlen e.1 hpe
          rw [show (ggDepARefl (ggDepANToZ 3 6 (cs6Gen ha aa e.2).1)
                (ggDepANToZ 3 6 (cs6Gen ha aa e.2).2) * w.getD e.1 1) cs6X =
              ggDepARefl (ggDepANToZ 3 6 (cs6Gen ha aa e.2).1)
                (ggDepANToZ 3 6 (cs6Gen ha aa e.2).2) (w.getD e.1 1 cs6X) from rfl]
          rw [hax e.1 hpe]
          exact cs6_refl_toZ_sub (cs6_gen_length1 hha haa e.2) (cs6_gen_length2 hha haa e.2) hve
      · intro k hk
        simp only [cs6OrbitStep, List.length_append, List.length_singleton] at hk
        simp only [cs6OrbitStep]
        by_cases hkv : k < w.length
        · rw [List.getD_append _ _ _ _ hkv]; exact hcl k hkv
        · have hk' : k = w.length := by omega
          subst hk'
          rw [List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self]
          simp only [List.getD_cons_zero]
          have hpe : e.1 < v.length := by have := hpar 0 (by simp); simpa using this
          have hpew : e.1 < w.length := by rw [← hlen]; exact hpe
          exact Submonoid.mul_mem _ (cs6_gen_mem e.2) (hcl e.1 hpew)
      · intro k hk
        have hh := hpar (k + 1) (by simpa using hk)
        simp only [List.getD_cons_succ, List.length_append, List.length_singleton] at hh ⊢
        omega

private lemma cs6_key_append (p : ℕ) (a : List ℕ) (x : ℕ) :
    ggDepAThreeKey p (a ++ [x]) = ggDepAThreeKey p a * p + x % p := by
  simp only [ggDepAThreeKey, List.foldl_append, List.foldl_cons, List.foldl_nil]

private lemma cs6_key_mod (p : ℕ) (a : List ℕ) :
    ggDepAThreeKey p a = ggDepAThreeKey p (a.map (· % p)) := by
  induction a using List.reverseRecOn with
  | nil => rfl
  | append_singleton a x ih =>
      rw [List.map_append, List.map_cons, List.map_nil, cs6_key_append, cs6_key_append, ih,
        Nat.mod_mod]

private lemma cs6_key_congr {p : ℕ} {a b : List ℕ} (h : a.map (· % p) = b.map (· % p)) :
    ggDepAThreeKey p a = ggDepAThreeKey p b := by
  rw [cs6_key_mod p a, cs6_key_mod p b, h]

private lemma cs6_key_eq_of_toZ_eq {a b : List ℕ} (ha : a.length = 6) (hb : b.length = 6)
    (h : ggDepANToZ 3 6 a = ggDepANToZ 3 6 b) :
    ggDepAThreeKey 3 a = ggDepAThreeKey 3 b := by
  apply cs6_key_congr
  rw [List.ext_getElem?_iff']
  intro n hn
  rw [List.getElem?_map, List.getElem?_map]
  have hna : n < a.length := by
    have := hn; rw [List.length_map, List.length_map, ha, hb] at this; omega
  have hnb : n < b.length := by
    have := hn; rw [List.length_map, List.length_map, ha, hb] at this; omega
  rw [List.getElem?_eq_getElem hna, List.getElem?_eq_getElem hnb]
  have hcoord := congrFun h ⟨n, by omega⟩
  change ((a.getD n 0 : ℕ) : ZMod 3) = ((b.getD n 0 : ℕ) : ZMod 3) at hcoord
  rw [List.getD_eq_getElem (l := a) (d := 0) (by omega),
      List.getD_eq_getElem (l := b) (d := 0) (by omega)] at hcoord
  simp only [Option.map_some]
  exact congrArg some ((ZMod.natCast_eq_natCast_iff' (a[n]) (b[n]) 3).mp hcoord)

private lemma cs6_orbit_data (ha aa : List Nat) (hha : ha.length = 6) (haa : aa.length = 6)
    (tree : List (Nat × Nat))
    (hpar : ∀ k < tree.length, (tree.getD k (0, 0)).1 < 1 + k)
    (hkeynodup : (List.map (ggDepAThreeKey 3) (cs6Orbit ha aa tree)).Nodup) :
    ∃ w : Fin (cs6Orbit ha aa tree).length → Module.End (ZMod 3) CS6E,
      (∀ k, w k ∈ Submonoid.closure (Set.range cs6Refl ∪
        {ggDepARefl (ggDepANToZ 3 6 ha) (ggDepANToZ 3 6 aa)})) ∧
      (∀ k, w k cs6X = ggDepANToZ 3 6 ((cs6Orbit ha aa tree).getD k.1 [])) ∧
      Function.Injective (fun k : Fin (cs6Orbit ha aa tree).length => w k cs6X) := by
  have hpar0 : ∀ k, k < tree.length →
      (tree.getD k (0, 0)).1 < ([cs6XL] : List (List ℕ)).length + k := by
    intro k hk; have := hpar k hk; simpa using this
  have hvlen0 : ∀ k, k < ([cs6XL] : List (List ℕ)).length →
      (([cs6XL] : List (List ℕ)).getD k []).length = 6 := by
    intro k hk
    have : k = 0 := by simp at hk; omega
    subst this
    simp [cs6XL]
  have hax0 : ∀ k, k < ([cs6XL] : List (List ℕ)).length →
      ([1] : List (Module.End (ZMod 3) CS6E)).getD k 1 cs6X =
        ggDepANToZ 3 6 (([cs6XL] : List (List ℕ)).getD k []) := by
    intro k hk
    have : k = 0 := by simp at hk; omega
    subst this
    simp [cs6_toZ_XL]
  have hcl0 : ∀ k, k < ([1] : List (Module.End (ZMod 3) CS6E)).length →
      ([1] : List (Module.End (ZMod 3) CS6E)).getD k 1 ∈
        Submonoid.closure (Set.range cs6Refl ∪
          {ggDepARefl (ggDepANToZ 3 6 ha) (ggDepANToZ 3 6 aa)}) := by
    intro k hk
    have : k = 0 := by simp at hk; omega
    subst this
    exact Submonoid.one_mem _
  have hInv := cs6_fold_inv ha aa hha haa tree [cs6XL] [1] rfl hvlen0 hax0 hcl0 hpar0
  set V := (tree.foldl (cs6OrbitStep ha aa) ([cs6XL], [1])).1 with hV
  set W := (tree.foldl (cs6OrbitStep ha aa) ([cs6XL], [1])).2 with hW
  have hVlen : V.length = W.length := hInv.1
  have hVvlen : ∀ k, k < V.length → (V.getD k []).length = 6 := hInv.2.1
  have hVax : ∀ k, k < V.length → W.getD k 1 cs6X = ggDepANToZ 3 6 (V.getD k []) :=
    hInv.2.2.1
  have hWcl : ∀ k, k < W.length → W.getD k 1 ∈ Submonoid.closure (Set.range cs6Refl ∪
      {ggDepARefl (ggDepANToZ 3 6 ha) (ggDepANToZ 3 6 aa)}) := hInv.2.2.2
  have hVorbit : V = cs6Orbit ha aa tree := by
    rw [hV, cs6_fold_fst, cs6_orbit_vec_eq]
  have hlen2 : (cs6Orbit ha aa tree).length = W.length := by
    rw [← hVorbit]; exact hVlen
  refine ⟨fun k => W.getD k.1 1, ?_, ?_, ?_⟩
  · intro k
    exact hWcl k.1 (hlen2 ▸ k.2)
  · intro k
    have hk : k.1 < V.length := by rw [hVorbit]; exact k.2
    rw [hVax k.1 hk, hVorbit]
  · intro i j hij
    have hi : i.1 < V.length := by rw [hVorbit]; exact i.2
    have hj : j.1 < V.length := by rw [hVorbit]; exact j.2
    have htoZ : ggDepANToZ 3 6 ((cs6Orbit ha aa tree).getD i.1 []) =
        ggDepANToZ 3 6 ((cs6Orbit ha aa tree).getD j.1 []) := by
      have hi' := hVax i.1 hi
      have hj' := hVax j.1 hj
      rw [hVorbit] at hi' hj'
      rw [← hi', ← hj']
      exact hij
    have hvei : ((cs6Orbit ha aa tree).getD i.1 []).length = 6 := by
      have := hVvlen i.1 hi; rwa [hVorbit] at this
    have hvej : ((cs6Orbit ha aa tree).getD j.1 []).length = 6 := by
      have := hVvlen j.1 hj; rwa [hVorbit] at this
    have hkeyeq := cs6_key_eq_of_toZ_eq hvei hvej htoZ
    have hi' : i.1 < (List.map (ggDepAThreeKey 3) (cs6Orbit ha aa tree)).length := by
      rw [List.length_map]; exact i.2
    have hj' : j.1 < (List.map (ggDepAThreeKey 3) (cs6Orbit ha aa tree)).length := by
      rw [List.length_map]; exact j.2
    have heq : (List.map (ggDepAThreeKey 3) (cs6Orbit ha aa tree))[i.1] =
        (List.map (ggDepAThreeKey 3) (cs6Orbit ha aa tree))[j.1] := by
      rw [List.getElem_map, List.getElem_map]
      rw [List.getD_eq_getElem (l := cs6Orbit ha aa tree) (d := []) i.2,
          List.getD_eq_getElem (l := cs6Orbit ha aa tree) (d := []) j.2] at hkeyeq
      exact hkeyeq
    exact Fin.ext ((List.Nodup.getElem_inj_iff hkeynodup (i := i.1) (j := j.1)
      (hi := hi') (hj := hj')).mp heq)

private lemma cs6_foldV_length (ha aa : List Nat) (tree : List (Nat × Nat))
    (acc : List (List Nat)) :
    (tree.foldl (cs6OrbitStepV ha aa) acc).length = acc.length + tree.length := by
  induction tree generalizing acc with
  | nil => simp
  | cons e t ih =>
      rw [List.foldl_cons, ih]
      simp only [cs6OrbitStepV, List.length_append, List.length_singleton]
      rw [List.length_cons]
      omega

private lemma cs6_orbit_length (ha aa : List Nat) (tree : List (Nat × Nat)) :
    (cs6Orbit ha aa tree).length = tree.length + 1 := by
  rw [cs6_orbit_vec_eq, cs6_foldV_length]
  simp [cs6XL]; omega

private lemma cs6_yReps_mem_length (jj : Fin 5) :
    ∀ x ∈ CS6Data.yReps.getD jj [], x.length = 6 := by
  fin_cases jj <;> decide

private lemma cs6_yReps_getD_length (jj : Fin 5) {yi : Nat}
    (hyi : yi < (CS6Data.yReps.getD jj []).length) :
    ((CS6Data.yReps.getD jj []).getD yi []).length = 6 := by
  rw [List.getD_eq_getElem (l := CS6Data.yReps.getD jj []) (d := []) hyi]
  exact cs6_yReps_mem_length jj _ (List.getElem_mem hyi)

private theorem cs6WitOK_sound (jj : Fin 5) (pi yi : Nat) (ha aa : List Nat)
    (hha : ha.length = 6) (haa : aa.length = 6)
    (hyrep : ((CS6Data.yReps.getD jj []).getD yi []).length = 6)
    (hdot : ggDepANDot 3 aa ha = 2 % 3)
    (w : CS6Data.Wit) (hw : cs6WitOK jj pi yi ha aa w = true) :
    (∃ g ∈ Submonoid.closure (Set.range cs6Refl ∪
        {ggDepARefl (ggDepANToZ 3 6 ha) (ggDepANToZ 3 6 aa)}), GGDepAIsTv g) ∨
    (∃ g ∈ Submonoid.closure (Set.range cs6Refl ∪
        {ggDepARefl (ggDepANToZ 3 6 ha) (ggDepANToZ 3 6 aa)}),
        g cs6X = ggDepANToZ 3 6 ((CS6Data.yReps.getD jj []).getD yi []) ∨
        g cs6X = - ggDepANToZ 3 6 ((CS6Data.yReps.getD jj []).getD yi [])) ∨
    (cs6PatDet jj pi = 6 ∧ ∃ F : Finset CS6E, 122 ≤ F.card ∧
      ∀ v ∈ F, ∃ g ∈ Submonoid.closure (Set.range cs6Refl ∪
        {ggDepARefl (ggDepANToZ 3 6 ha) (ggDepANToZ 3 6 aa)}), g cs6X = v) ∨
    ggDepARefl (ggDepANToZ 3 6 ha) (ggDepANToZ 3 6 aa) ∈
      Submonoid.closure (Set.range cs6Refl) := by
  cases w with
  | tv g1 w1 g2 w2 =>
      have htest : ggDepANTestPair 3 (cs6Word ha aa (cs6Gen ha aa g1) w1)
          (cs6Word ha aa (cs6Gen ha aa g2) w2) = true := by
        simpa only [cs6WitOK] using hw
      set S0 := Submonoid.closure (Set.range cs6Refl ∪
        {ggDepARefl (ggDepANToZ 3 6 ha) (ggDepANToZ 3 6 aa)}) with hS0
      have hdg : ∀ g, ggDepAdot (ggDepANToZ 3 6 (cs6Gen ha aa g).2)
          (ggDepANToZ 3 6 (cs6Gen ha aa g).1) = 2 := fun g => cs6_gen_dot hha haa hdot g
      have hmem : ∀ g, ggDepARefl (ggDepANToZ 3 6 (cs6Gen ha aa g).1)
          (ggDepANToZ 3 6 (cs6Gen ha aa g).2) ∈ S0 := by
        intro g; rw [hS0]; exact cs6_gen_mem g
      set q1 : GGDepANPair := cs6Word ha aa (cs6Gen ha aa g1) w1 with hq1
      set q2 : GGDepANPair := cs6Word ha aa (cs6Gen ha aa g2) w2 with hq2
      have hL1 : q1.1.length = 6 :=
        (cs6_word_length hha haa w1 (cs6Gen ha aa g1)
          (cs6_gen_length1 hha haa g1) (cs6_gen_length2 hha haa g1)).1
      have hL2 : q1.2.length = 6 :=
        (cs6_word_length hha haa w1 (cs6Gen ha aa g1)
          (cs6_gen_length1 hha haa g1) (cs6_gen_length2 hha haa g1)).2
      have hL3 : q2.1.length = 6 :=
        (cs6_word_length hha haa w2 (cs6Gen ha aa g2)
          (cs6_gen_length1 hha haa g2) (cs6_gen_length2 hha haa g2)).1
      have hL4 : q2.2.length = 6 :=
        (cs6_word_length hha haa w2 (cs6Gen ha aa g2)
          (cs6_gen_length1 hha haa g2) (cs6_gen_length2 hha haa g2)).2
      have hword1 : ggDepAdot (ggDepANToZ 3 6 q1.2) (ggDepANToZ 3 6 q1.1) = 2 ∧
          ggDepARefl (ggDepANToZ 3 6 q1.1) (ggDepANToZ 3 6 q1.2) ∈ S0 := by
        rw [hq1]
        exact cs6_word_gen hha haa S0 (fun _ => True) (fun g _ => hdg g) (fun g _ => hmem g)
          w1 (fun _ _ => trivial) (cs6Gen ha aa g1) (cs6_gen_length1 hha haa g1)
          (cs6_gen_length2 hha haa g1) (hdg g1) (hmem g1)
      have hword2 : ggDepAdot (ggDepANToZ 3 6 q2.2) (ggDepANToZ 3 6 q2.1) = 2 ∧
          ggDepARefl (ggDepANToZ 3 6 q2.1) (ggDepANToZ 3 6 q2.2) ∈ S0 := by
        rw [hq2]
        exact cs6_word_gen hha haa S0 (fun _ => True) (fun g _ => hdg g) (fun g _ => hmem g)
          w2 (fun _ _ => trivial) (cs6Gen ha aa g2) (cs6_gen_length1 hha haa g2)
          (cs6_gen_length2 hha haa g2) (hdg g2) (hmem g2)
      have hdot1 : ggDepANDot 3 q1.2 q1.1 = 2 % 3 := by
        have hh := ggDepANDot_cast (p := 3) (N := 6) q1.2 q1.1 hL2 hL1
        rw [hword1.1] at hh
        have h2 : ((ggDepANDot 3 q1.2 q1.1 : Nat) : ZMod 3) = ((2 % 3 : Nat) : ZMod 3) := by
          rw [ZMod.natCast_mod]; exact hh
        rw [ZMod.natCast_eq_natCast_iff'] at h2
        simpa [ggDepANDot, Nat.mod_mod] using h2
      have hdot2 : ggDepANDot 3 q2.2 q2.1 = 2 % 3 := by
        have hh := ggDepANDot_cast (p := 3) (N := 6) q2.2 q2.1 hL4 hL3
        rw [hword2.1] at hh
        have h2 : ((ggDepANDot 3 q2.2 q2.1 : Nat) : ZMod 3) = ((2 % 3 : Nat) : ZMod 3) := by
          rw [ZMod.natCast_mod]; exact hh
        rw [ZMod.natCast_eq_natCast_iff'] at h2
        simpa [ggDepANDot, Nat.mod_mod] using h2
      have ht' : ggDepANTestPair 3 q1 q2 = true := by
        rw [hq1, hq2]; exact htest
      have htv := ggDepANTestPair_sound (p := 3) (N := 6) (by norm_num) q1 q2 hL1 hL2 hL3 hL4
        hdot1 hdot2 ht'
      refine Or.inl ⟨_, ?_, htv.2.2⟩
      exact Submonoid.mul_mem _ hword1.2 hword2.2
  | inL k wk lam =>
      simp only [cs6WitOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq]
        at hw
      have hk : k < 6 := by tauto
      have hlam : lam = 1 ∨ lam = 2 := by tauto
      have hwall : ∀ g ∈ wk, g < 6 := by tauto
      have heq1 : (cs6Word ha aa (cs6Gen ha aa k) wk).1 = ggDepANSmul 3 lam ha := by tauto
      have heq2 : (cs6Word ha aa (cs6Gen ha aa k) wk).2 = ggDepANSmul 3 lam aa := by tauto
      set q := cs6Word ha aa (cs6Gen ha aa k) wk with hq
      have hqrefl : ggDepARefl (ggDepANToZ 3 6 q.1) (ggDepANToZ 3 6 q.2) =
          ggDepARefl (ggDepANToZ 3 6 ha) (ggDepANToZ 3 6 aa) := by
        rw [hq, heq1, heq2, l05nNC_toZ_smul hha lam, l05nNC_toZ_smul haa lam]
        exact cs6_refl_smul_center (lam : ZMod 3) _ _
          (by rcases hlam with rfl | rfl <;> decide)
      have hdgP : ∀ g, g < 6 → ggDepAdot (ggDepANToZ 3 6 (cs6Gen ha aa g).2)
          (ggDepANToZ 3 6 (cs6Gen ha aa g).1) = 2 := fun g _ => cs6_gen_dot hha haa hdot g
      have hmemP : ∀ g, g < 6 → ggDepARefl (ggDepANToZ 3 6 (cs6Gen ha aa g).1)
          (ggDepANToZ 3 6 (cs6Gen ha aa g).2) ∈ Submonoid.closure (Set.range cs6Refl) := by
        intro g hg
        simp only [cs6Gen, if_pos hg]
        rw [cs6_toZ_root ⟨g, hg⟩, cs6_toZ_alpha ⟨g, hg⟩]
        exact Submonoid.subset_closure ⟨⟨g, hg⟩, rfl⟩
      have hmemL : ggDepARefl (ggDepANToZ 3 6 q.1) (ggDepANToZ 3 6 q.2) ∈
          Submonoid.closure (Set.range cs6Refl) :=
        (cs6_word_gen hha haa (Submonoid.closure (Set.range cs6Refl)) (fun g => g < 6)
          hdgP hmemP wk hwall (cs6Gen ha aa k) (cs6_gen_length1 hha haa k)
          (cs6_gen_length2 hha haa k) (hdgP k hk) (hmemP k hk)).2
      exact Or.inr (Or.inr (Or.inr (by rw [← hqrefl]; exact hmemL)))
  | orb wk =>
      simp only [cs6WitOK, Bool.or_eq_true, beq_iff_eq] at hw
      refine Or.inr (Or.inl ⟨cs6End ha aa wk, cs6End_mem ha aa wk, ?_⟩)
      have hact := cs6End_apply ha aa hha haa wk
      rcases hw with h | h
      · left; rw [hact, h]
      · right
        rw [hact, h, l05nNC_toZ_smul hyrep 2,
          show ((2 : ℕ) : ZMod 3) = -1 by decide, neg_one_smul]
  | cnt tree =>
      simp only [cs6WitOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
        List.mem_range] at hw
      have hd6 : cs6PatDet jj pi = 6 := by tauto
      have hlen : 121 ≤ tree.length := by tauto
      have hvalid : ∀ k, k < tree.length → (match tree[k]? with
          | none => false
          | some e => decide (e.1 < k + 1) && decide (e.2 ≤ 6)) = true := by tauto
      have hkey := (by tauto : CFSG.Decide.bitsetNodup
        ((cs6Orbit ha aa tree).map (ggDepAThreeKey 3)) = true)
      have hpar : ∀ k < tree.length, (tree.getD k (0, 0)).1 < 1 + k := by
        intro k hkt
        have h6 := hvalid k hkt
        rw [List.getElem?_eq_getElem hkt] at h6
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h6
        obtain ⟨h6a, -⟩ := h6
        rw [List.getD_eq_getElem (l := tree) (d := (0, 0)) hkt]
        omega
      have hnodup := CFSG.Decide.nodup_of_bitsetNodup_nat hkey
      obtain ⟨wf, hwcl, _hwax, hwinj⟩ := cs6_orbit_data ha aa hha haa tree hpar hnodup
      let F : Finset CS6E := (Finset.univ : Finset (Fin (cs6Orbit ha aa tree).length)).image
        (fun k => wf k cs6X)
      refine Or.inr (Or.inr (Or.inl ⟨hd6, F, ?_, ?_⟩))
      · have hc : F.card = (Finset.univ : Finset (Fin (cs6Orbit ha aa tree).length)).card :=
          Finset.card_image_of_injective _ hwinj
        rw [hc, Finset.card_univ, Fintype.card_fin, cs6_orbit_length]
        omega
      · intro v hv
        rw [Finset.mem_image] at hv
        obtain ⟨k, -, hk⟩ := hv
        exact ⟨wf k, hwcl k, hk⟩

private lemma cs6_mem_allVecs {p : Nat} (l : List Nat) (h : ∀ a ∈ l, a < p) :
    l ∈ ggDepEAllVecs p l.length := by
  induction l with
  | nil => simp [ggDepEAllVecs]
  | cons a t ih =>
      have ha : a ∈ List.range p := List.mem_range.mpr (h a (by simp))
      have ht : ∀ b ∈ t, b < p := fun b hb => h b (by simp [hb])
      have hmap : a :: t ∈ (ggDepEAllVecs p t.length).map (a :: ·) :=
        List.mem_map.mpr ⟨t, ih ht, rfl⟩
      show a :: t ∈ ggDepEAllVecs p (t.length + 1)
      simp only [ggDepEAllVecs]
      exact List.mem_flatMap.mpr ⟨a, ha, hmap⟩

private lemma cs6_allVecs_three (n : Nat) (v : Fin n → ZMod 3) :
    ∃ l ∈ ggDepEAllVecs 3 n, l.length = n ∧ (∀ a ∈ l, a < 3) ∧ ggDepANToZ 3 n l = v := by
  set l : List Nat := (List.range n).map fun j => if h : j < n then (v ⟨j, h⟩).val else 0
    with hl_def
  have hl_len : l.length = n := by simp [hl_def]
  have hl_lt : ∀ a ∈ l, a < 3 := by
    intro a ha
    rw [hl_def, List.mem_map] at ha
    obtain ⟨j, _, rfl⟩ := ha
    by_cases h : j < n
    · rw [dif_pos h]; exact ZMod.val_lt _
    · rw [dif_neg h]; omega
  have hl_getD : ∀ j : Fin n, l.getD j.val 0 = (v j).val := by
    intro j
    have hj : j.val < l.length := by rw [hl_len]; exact j.isLt
    rw [List.getD_eq_getElem l 0 hj]
    simp only [hl_def, List.getElem_map, List.getElem_range]
    rw [dif_pos j.isLt]
  have hl_toZ : ggDepANToZ 3 n l = v := by
    funext j
    rw [ggDepANToZ, hl_getD j, ZMod.natCast_zmod_val]
  exact ⟨l, by rw [← hl_len]; exact cs6_mem_allVecs l hl_lt, hl_len, hl_lt, hl_toZ⟩

private lemma cs6_zmod_eq_of_lt {x y : Nat} (hx : x < 3) (hy : y < 3)
    (h : (x : ZMod 3) = (y : ZMod 3)) : x = y := by
  have h2 := congrArg ZMod.val h
  rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at h2
  exact h2

private lemma cs6_pat_components_lt (jj : Fin 5) :
    ∀ pat ∈ CS6Data.patterns.getD jj [], ∀ x ∈ pat, x.1 < 3 ∧ x.2 < 3 := by
  fin_cases jj <;> decide

private lemma cs6_patterns_len (jj : Fin 5) :
    ∀ pat ∈ CS6Data.patterns.getD jj [], pat.length = 4 := by
  fin_cases jj <;> decide

theorem cs6_cells (jj : Fin 5) (pi : Nat) (ha aa y : CS6E)
    (h : CS6CellHyp jj pi ha aa y) : CS6Outcome (cs6PatDet jj pi) ha aa y := by
  obtain ⟨hpat, hy, hpair1, hpair2, hdoty, hdot2⟩ := h
  obtain ⟨r, hr_mem, hyr⟩ := hy
  rw [cs6Ys, List.mem_map] at hr_mem
  obtain ⟨yrep, hyrep_mem, rfl⟩ := hr_mem
  obtain ⟨yi, hyi_lt, hyrep_eq⟩ := List.mem_iff_getElem.mp hyrep_mem
  have hyrep_eq' : yrep = (CS6Data.yReps.getD jj []).getD yi [] := by
    rw [List.getD_eq_getElem (l := CS6Data.yReps.getD jj []) (d := []) hyi_lt]
    exact hyrep_eq.symm
  set ydata : List Nat := (CS6Data.yReps.getD jj []).getD yi [] with hydatadef
  rw [hyrep_eq'] at hyr
  obtain ⟨hal, hhal_mem, hhal_len, hhal_lt, hhal_toZ⟩ := cs6_allVecs_three 6 ha
  obtain ⟨aal, haal_mem, haal_len, haal_lt, haal_toZ⟩ := cs6_allVecs_three 6 aa
  have hdot : ggDepANDot 3 aal hal = 2 % 3 := by
    have hh := ggDepANDot_cast (p := 3) (N := 6) aal hal haal_len hhal_len
    rw [hhal_toZ, haal_toZ, hdot2] at hh
    have h2 : ((ggDepANDot 3 aal hal : Nat) : ZMod 3) = ((2 % 3 : Nat) : ZMod 3) := by
      rw [ZMod.natCast_mod]; exact hh
    rw [ZMod.natCast_eq_natCast_iff'] at h2
    simpa [ggDepANDot, Nat.mod_mod] using h2
  set pat : List (Nat × Nat) := (CS6Data.patterns.getD jj []).getD pi [] with hpatdef
  have hpi_lt : pi < (CS6Data.patterns.getD jj []).length := by simpa only [cs6NumPat] using hpat
  have hpat_mem : pat ∈ CS6Data.patterns.getD jj [] := by
    rw [hpatdef, List.getD_eq_getElem (l := CS6Data.patterns.getD jj []) (d := []) hpi_lt]
    exact List.getElem_mem hpi_lt
  have hxlt : ∀ i : Fin 4, (pat.getD i (0, 0)).1 < 3 ∧ (pat.getD i (0, 0)).2 < 3 := by
    intro i
    have hxmem : pat.getD i (0, 0) ∈ pat := by
      rw [List.getD_eq_getElem (l := pat) (d := (0, 0))
        (by rw [cs6_patterns_len jj pat hpat_mem]; exact i.isLt)]
      exact List.getElem_mem _
    exact cs6_pat_components_lt jj pat hpat_mem _ hxmem
  have hpair1N : ∀ i : Fin 4, ggDepANDot 3 (cs6AlphaL (cs6J jj i).val) hal =
      (pat.getD i (0, 0)).1 := by
    intro i
    have hp := hpair1 i
    have hL : ggDepAdot (cs6Alpha (cs6J jj i)) ha =
        ((ggDepANDot 3 (cs6AlphaL (cs6J jj i).val) hal : Nat) : ZMod 3) := by
      rw [← hhal_toZ, ← cs6_toZ_alpha (cs6J jj i)]
      exact (ggDepANDot_cast (p := 3) (N := 6) (cs6AlphaL (cs6J jj i).val) hal
        (cs6AlphaL_length _) hhal_len).symm
    have hR : (cs6PatPair jj pi i).1 = ((pat.getD i (0, 0)).1 : ZMod 3) := by
      rw [cs6PatPair, ← hpatdef]
    rw [hL, hR] at hp
    exact cs6_zmod_eq_of_lt (by rw [ggDepANDot]; exact Nat.mod_lt _ (by norm_num))
      (hxlt i).1 hp
  have hpair2N : ∀ i : Fin 4, ggDepANDot 3 aal (cs6RootL (cs6J jj i).val) =
      (pat.getD i (0, 0)).2 := by
    intro i
    have hp := hpair2 i
    have hL : ggDepAdot aa (cs6Root (cs6J jj i)) =
        ((ggDepANDot 3 aal (cs6RootL (cs6J jj i).val) : Nat) : ZMod 3) := by
      rw [← haal_toZ, ← cs6_toZ_root (cs6J jj i)]
      exact (ggDepANDot_cast (p := 3) (N := 6) aal (cs6RootL (cs6J jj i).val) haal_len
        (cs6RootL_length _)).symm
    have hR : (cs6PatPair jj pi i).2 = ((pat.getD i (0, 0)).2 : ZMod 3) := by
      rw [cs6PatPair, ← hpatdef]
    rw [hL, hR] at hp
    exact cs6_zmod_eq_of_lt (by rw [ggDepANDot]; exact Nat.mod_lt _ (by norm_num))
      (hxlt i).2 hp
  have hdotr : ggDepAdot aa (ggDepANToZ 3 6 ydata) = 0 := by
    rcases hyr with hyr | hyr
    · rw [hyr] at hdoty; exact hdoty
    · rw [hyr] at hdoty
      have hneg : ggDepAdot aa (-(ggDepANToZ 3 6 ydata)) =
          - ggDepAdot aa (ggDepANToZ 3 6 ydata) := by
        simp only [ggDepAdot, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
      rw [hneg, neg_eq_zero] at hdoty; exact hdoty
  have hdotANy : ggDepANDot 3 aal ydata = 0 := by
    refine cs6_zmod_eq_of_lt (by rw [ggDepANDot]; exact Nat.mod_lt _ (by norm_num))
      (by norm_num) ?_
    rw [ggDepANDot_cast (p := 3) (N := 6) aal ydata haal_len
      (by rw [hydatadef]; exact cs6_yReps_getD_length jj hyi_lt), haal_toZ]
    exact hdotr
  have hcheck := cs6Check_eq_true
  rw [cs6Check] at hcheck
  have hJJ : cs6CheckJJ jj = true := (List.all_eq_true.mp hcheck) jj (List.mem_finRange jj)
  rw [cs6CheckJJ] at hJJ
  have h1 := (List.all_eq_true.mp hJJ) pi (List.mem_range.mpr hpi_lt)
  have h2 := (List.all_eq_true.mp h1) yi (List.mem_range.mpr hyi_lt)
  dsimp only at h2
  set HS : List (List Nat) := (ggDepEAllVecs 3 6).filter (fun ha =>
    (List.finRange 4).all fun i =>
      ggDepANDot 3 (cs6AlphaL (cs6J jj i).val) ha == (pat.getD i (0, 0)).1) with hHS
  set AS : List (List Nat) := (ggDepEAllVecs 3 6).filter (fun aa =>
    (List.finRange 4).all (fun i =>
      ggDepANDot 3 aa (cs6RootL (cs6J jj i).val) == (pat.getD i (0, 0)).2) &&
      ggDepANDot 3 aa ydata == 0) with hAS
  have hHal_mem : hal ∈ HS := by
    rw [hHS, List.mem_filter]
    refine ⟨hhal_mem, ?_⟩
    rw [List.all_eq_true]
    intro i _
    exact beq_iff_eq.mpr (hpair1N i)
  have haal_mem : aal ∈ AS := by
    rw [hAS, List.mem_filter]
    refine ⟨haal_mem, ?_⟩
    rw [Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · rw [List.all_eq_true]
      intro i _
      exact beq_iff_eq.mpr (hpair2N i)
    · exact beq_iff_eq.mpr hdotANy
  cases hc : cs6CellsAt jj.val pi yi with
  | none => rw [hc] at h2; simp at h2
  | some lst =>
      rw [hc] at h2
      have h_ha := (List.all_eq_true.mp h2) hal hHal_mem
      have h_aa := (List.all_eq_true.mp h_ha) aal haal_mem
      have hcond : (ggDepANDot 3 aal hal == 2) = true := by
        rw [beq_iff_eq, hdot]
      rw [if_pos hcond] at h_aa
      obtain ⟨e, he_mem, he_test⟩ := List.any_eq_true.mp h_aa
      simp only [Bool.and_eq_true, beq_iff_eq] at he_test
      have hwtest : cs6WitOK jj pi yi hal aal e.2.2 = true := he_test.2
      have hhyrep : ydata.length = 6 := by rw [hydatadef]; exact cs6_yReps_getD_length jj hyi_lt
      have hsnd := cs6WitOK_sound jj pi yi hal aal hhal_len haal_len hhyrep hdot e.2.2 hwtest
      rw [hhal_toZ, haal_toZ] at hsnd
      rcases hsnd with hT | hY | hY' | hW
      · exact Or.inl hT
      · obtain ⟨g, hg, hgx⟩ := hY
        refine Or.inr (Or.inl ⟨g, hg, ?_⟩)
        rcases hyr with hyr | hyr
        · rw [← hyr] at hgx; exact hgx
        · have h1 : ggDepANToZ 3 6 ydata = -y := by rw [hyr]; simp
          have h2 : -ggDepANToZ 3 6 ydata = y := hyr.symm
          rw [h2, h1] at hgx
          exact hgx.symm
      · exact Or.inr (Or.inr (Or.inl hY'))
      · exact Or.inr (Or.inr (Or.inr hW))

end CFSG.StandardType
