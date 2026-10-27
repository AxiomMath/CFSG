module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallWord
public import Certificates.Data.CFSGNative.TwoNodeSmall.Verify

public section

namespace CFSG.TwoNodeSmall

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

lemma pww2_getD_range_map (D : ℕ) (F : ℕ → ℕ) (j : Fin D) :
    (((List.range D).map F).getD j.val 0) = F j.val := by
  have hlen : j.val < ((List.range D).map F).length := by simpa using j.isLt
  rw [List.getD_eq_getElem _ 0 hlen, List.getElem_map]
  have hr : (List.range D)[j.val] = j.val := List.getElem_range (by simpa using j.isLt)
  rw [hr]

lemma pww2_dot_add (P : Pt) (f x y : P.V) :
    P.dot f (x + y) = P.dot f x + P.dot f y := by
  simp only [Pt.dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

lemma pww2_dot_sub (P : Pt) (f x y : P.V) :
    P.dot f (x - y) = P.dot f x - P.dot f y := by
  simp only [Pt.dot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

lemma pww2_dot_smul (P : Pt) (f x : P.V) (a : ZMod P.p) :
    P.dot f (a • x) = a * P.dot f x := by
  simp only [Pt.dot, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

@[expose] noncomputable def pww2_dotLM (P : Pt) (f : P.V) : Module.Dual (ZMod P.p) P.V where
  toFun := P.dot f
  map_add' := pww2_dot_add P f
  map_smul' := by
    intro a x
    simpa using pww2_dot_smul P f x a

lemma pww2_dot_single (P : Pt) (f : P.V) (j : Fin P.D) :
    P.dot f (Pi.single j (1 : ZMod P.p)) = f j := by
  simp only [Pt.dot]
  rw [Finset.sum_eq_single j]
  · rw [Pi.single_eq_same]; ring
  · intro k _ hk
    rw [Pi.single_apply, if_neg hk, mul_zero]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

lemma pww2_cast_sigma_coord (p a b : ℕ) (hp : 0 < p) :
    (((a % p + (p - b % p)) % p : ℕ) : ZMod p) = (a : ZMod p) - (b : ZMod p) := by
  rw [ZMod.natCast_mod, Nat.cast_add, Nat.cast_sub (le_of_lt (Nat.mod_lt b hp))]
  rw [ZMod.natCast_mod, ZMod.natCast_mod, ZMod.natCast_self]
  ring

lemma pww2_vec_sigmaApply (P : Pt) [Fact P.p.Prime] (cb : Vec × Vec) (v : Vec) :
    P.vec (P.sigmaApply cb v) = P.vec v - (P.dotv cb.2 v : ZMod P.p) • P.vec cb.1 := by
  have hp : 0 < P.p := (Fact.out (p := P.p.Prime)).pos
  funext i
  simp only [Pt.sigmaApply, Pt.vec, Pt.ent, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [pww2_getD_range_map]
  rw [pww2_cast_sigma_coord P.p (v.getD i.val 0)
      (P.dotv cb.2 v * (cb.1.getD i.val 0 % P.p)) hp, Nat.cast_mul, ZMod.natCast_mod]

@[expose] noncomputable def pww2_reflLE (P : Pt) [Fact P.p.Prime] (hwf : P.WF) (r : Refl)
    (hr : r ∈ P.gens) : P.V ≃ₗ[ZMod P.p] P.V :=
  Module.reflection (x := P.vec r.h) (f := pww2_dotLM P (P.vec r.f)) (by
    change P.dot (P.vec r.f) (P.vec r.h) = 2
    rw [← Pt.dotv_spec P r.f r.h]
    have h := Pt.dotv_spec P r.f r.h
    rw [hwf r hr] at h
    exact h)

lemma pww2_reflLE_apply (P : Pt) [Fact P.p.Prime] (hwf : P.WF) (r : Refl)
    (hr : r ∈ P.gens) (v : P.V) :
    pww2_reflLE P hwf r hr v = v - P.dot (P.vec r.f) v • P.vec r.h := by
  rw [pww2_reflLE, Module.reflection_apply]
  rfl

lemma pww2_reflLE_mem (P : Pt) [Fact P.p.Prime] (hwf : P.WF) (r : Refl)
    (hr : r ∈ P.gens) : pww2_reflLE P hwf r hr ∈ P.group := by
  apply Subgroup.subset_closure
  exact ⟨r, hr, fun w => pww2_reflLE_apply P hwf r hr w⟩

lemma pww2_lin_ext_unit (P : Pt) [Fact P.p.Prime] {W : Type*} [AddCommMonoid W]
    [Module (ZMod P.p) W] {f g : P.V →ₗ[ZMod P.p] W}
    (h : ∀ j : Fin P.D, f (P.vec (P.unit j)) = g (P.vec (P.unit j))) : f = g := by
  apply LinearMap.ext
  intro z
  have hz : z = ∑ j : Fin P.D, z j • Pi.single j (1 : ZMod P.p) := by
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single i]
    · rw [Pi.single_eq_same]; ring
    · intro k _ hk
      rw [Pi.single_apply, if_neg (Ne.symm hk), mul_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  rw [hz]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Pt.vec_unit P j]
  exact congrArg (fun w => z j • w) (h j)

lemma pww2_le_ext_unit (P : Pt) [Fact P.p.Prime] {f g : P.V ≃ₗ[ZMod P.p] P.V}
    (h : ∀ j : Fin P.D, f (P.vec (P.unit j)) = g (P.vec (P.unit j))) : f = g := by
  have hlm : (f : P.V →ₗ[ZMod P.p] P.V) = (g : P.V →ₗ[ZMod P.p] P.V) := by
    apply pww2_lin_ext_unit P
    exact h
  apply LinearEquiv.ext
  intro z
  exact congrFun (congrArg (fun m : P.V →ₗ[ZMod P.p] P.V => (m : P.V → P.V)) hlm) z

lemma pww2_le_eq_one_of_unit (P : Pt) [Fact P.p.Prime] (f : P.V ≃ₗ[ZMod P.p] P.V)
    (h : ∀ j : Fin P.D, f (P.vec (P.unit j)) = P.vec (P.unit j)) : f = 1 := by
  apply pww2_le_ext_unit P
  intro j
  rw [h j]
  rfl

lemma pww2_applyWord_append (P : Pt) (x y : Word) (v : Vec) :
    P.applyWord (x ++ y) v = P.applyWord x (P.applyWord y v) := by
  simp only [Pt.applyWord, List.foldr_append]

lemma pww2_vec_applyRefl_eq (P : Pt) [Fact P.p.Prime] (r : Refl) (a b : Vec)
    (h : P.vec a = P.vec b) : P.vec (P.applyRefl r a) = P.vec (P.applyRefl r b) := by
  rw [Pt.vec_applyRefl, Pt.vec_applyRefl, h]

lemma pww2_applyRefl_invol (P : Pt) [Fact P.p.Prime] (hwf : P.WF) (r : Refl)
    (hr : r ∈ P.gens) (v : Vec) :
    P.vec (P.applyRefl r (P.applyRefl r v)) = P.vec v := by
  rw [Pt.vec_applyRefl P r (P.applyRefl r v), Pt.vec_applyRefl P r v]
  have hd : P.dot (P.vec r.f) (P.vec v - P.dot (P.vec r.f) (P.vec v) • P.vec r.h)
      = -(P.dot (P.vec r.f) (P.vec v)) := by
    rw [pww2_dot_sub, pww2_dot_smul, hwf r hr]; ring
  rw [hd, neg_smul, sub_neg_eq_add, sub_add_cancel]

lemma pww2_wordOK_reverse (P : Pt) (w : Word) (hw : P.wordOK w = true) :
    P.wordOK w.reverse = true := by
  simpa only [Pt.wordOK, List.all_reverse] using hw

lemma pww2_applyWord_reverse_inv (P : Pt) [Fact P.p.Prime] (hwf : P.WF) :
    ∀ (w : Word), P.wordOK w = true →
      ∀ v : Vec, P.vec (P.applyWord w (P.applyWord w.reverse v)) = P.vec v := by
  intro w
  induction w with
  | nil =>
      intro _ v
      simp only [Pt.applyWord, List.reverse_nil, List.foldr_nil]
  | cons i w ih =>
      intro hw v
      have hw' : ∀ x ∈ i :: w, decide (x < P.gens.length) = true :=
        List.all_eq_true.mp (by simpa only [Pt.wordOK] using hw)
      have hir : i < P.gens.length := by
        simpa using hw' i (by simp)
      have hwt : P.wordOK w = true := by
        apply List.all_eq_true.mpr
        intro x hx
        exact hw' x (List.mem_cons_of_mem i hx)
      have hword : P.applyWord (i :: w) (P.applyWord (i :: w).reverse v)
          = P.applyRefl (P.gens[i]'hir)
              (P.applyWord w (P.applyWord w.reverse (P.applyRefl (P.gens[i]'hir) v))) := by
        rw [List.reverse_cons, pww2_applyWord_append]
        simp only [Pt.applyWord, List.foldr_cons, List.foldr_nil, List.getElem?_eq_getElem hir]
      rw [hword, pww2_vec_applyRefl_eq P (P.gens[i]'hir) _ _
          (ih hwt (P.applyRefl (P.gens[i]'hir) v)),
        pww2_applyRefl_invol P hwf _ (List.getElem_mem hir) v]

@[expose] def pww2_S (P : Pt) (c : WWit) : List (Vec × Vec) :=
  c.sigma.map fun s => P.sigmaVecs s.1 s.2

@[expose] def pww2_cb (P : Pt) (c : WWit) (i : Fin P.D) : Vec × Vec :=
  (pww2_S P c).getD i.val ([], [])

lemma pww2_S_length (P : Pt) (c : WWit) : (pww2_S P c).length = c.sigma.length := by
  simp [pww2_S, List.length_map]

lemma pww2_cb_eq (P : Pt) (c : WWit) (i : Fin P.D) (hlt : i.val < c.sigma.length) :
    pww2_cb P c i
      = P.sigmaVecs ((c.sigma.getD i.val ([], 0)).1) ((c.sigma.getD i.val ([], 0)).2) := by
  unfold pww2_cb pww2_S
  rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hlt), List.getElem_map,
    List.getD_eq_getElem _ _ hlt]

lemma pww2_vec_of_vecEq (P : Pt) (v w : Vec) (h : P.vecEq v w = true) :
    P.vec v = P.vec w := by
  simp only [Pt.vecEq, List.all_eq_true, List.mem_range, beq_iff_eq, Pt.ent] at h
  funext i
  show ((v.getD i.val 0 : ℕ) : ZMod P.p) = ((w.getD i.val 0 : ℕ) : ZMod P.p)
  rw [← ZMod.natCast_mod (v.getD i.val 0) P.p,
    ← ZMod.natCast_mod (w.getD i.val 0) P.p, h i.val i.isLt]

@[expose] noncomputable def pww2_sigmaProd (P : Pt) [Fact P.p.Prime] {n : ℕ}
    (σ : Fin n → P.V ≃ₗ[ZMod P.p] P.V) :
    (w : Word) → (∀ i ∈ w, i < n) → P.V ≃ₗ[ZMod P.p] P.V
  | [], _ => 1
  | i :: w, hw =>
      σ ⟨i, hw i List.mem_cons_self⟩ *
        pww2_sigmaProd P σ w (fun j hj => hw j (List.mem_cons_of_mem i hj))

lemma pww2_sigmaProd_mem (P : Pt) [Fact P.p.Prime] {n : ℕ}
    (σ : Fin n → P.V ≃ₗ[ZMod P.p] P.V) :
    ∀ (w : Word) (hw : ∀ i ∈ w, i < n),
      pww2_sigmaProd P σ w hw ∈ Subgroup.closure (Set.range σ)
  | [], _ => by
      simp only [pww2_sigmaProd]
      exact Subgroup.one_mem _
  | i :: w, hw => by
      have hmem : σ ⟨i, hw i List.mem_cons_self⟩ ∈ Subgroup.closure (Set.range σ) :=
        Subgroup.subset_closure ⟨⟨i, hw i List.mem_cons_self⟩, rfl⟩
      have ih := pww2_sigmaProd_mem P σ w (fun j hj => hw j (List.mem_cons_of_mem i hj))
      simpa only [pww2_sigmaProd] using Subgroup.mul_mem _ hmem ih

lemma pww2_sigmaWord_vec (P : Pt) [Fact P.p.Prime] {n : ℕ} (S : List (Vec × Vec))
    (hSlen : S.length = n) (σ : Fin n → P.V ≃ₗ[ZMod P.p] P.V)
    (hσ : ∀ i : Fin n, ∀ v : Vec,
      σ i (P.vec v) = P.vec (P.sigmaApply (S.getD i.val ([], [])) v)) :
    ∀ (w : Word) (hw : ∀ i ∈ w, i < n) (v : Vec),
      P.vec (P.sigmaWord S w v) = pww2_sigmaProd P σ w hw (P.vec v)
  | [], _, v => by
      simp only [Pt.sigmaWord, List.foldr_nil, pww2_sigmaProd]
      rfl
  | i :: w, hw, v => by
      have hi : i < n := hw i List.mem_cons_self
      have hilt : i < S.length := by rw [hSlen]; exact hi
      have hwt : ∀ j ∈ w, j < n := fun j hj => hw j (List.mem_cons_of_mem i hj)
      have hgetD : S.getD i ([], []) = S[i]'hilt := List.getD_eq_getElem _ _ hilt
      have hstep : P.sigmaWord S (i :: w) v =
          P.sigmaApply (S[i]'hilt) (P.sigmaWord S w v) := by
        simp only [Pt.sigmaWord, List.foldr_cons, List.getElem?_eq_getElem hilt]
      rw [hstep, ← hgetD, ← hσ ⟨i, hi⟩ (P.sigmaWord S w v)]
      rw [pww2_sigmaWord_vec P S hSlen σ hσ w hwt v]
      simp only [pww2_sigmaProd, LinearEquiv.mul_apply]

lemma pww2_A_M (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    (CoxeterMatrix.A n).M i j =
      (if (j : ℕ) + 1 = (i : ℕ) ∨ (i : ℕ) + 1 = (j : ℕ) then 3 else 2) := by
  show (if i = j then 1 else
      (if (j : ℕ) + 1 = (i : ℕ) ∨ (i : ℕ) + 1 = (j : ℕ) then 3 else 2)) =
    (if (j : ℕ) + 1 = (i : ℕ) ∨ (i : ℕ) + 1 = (j : ℕ) then 3 else 2)
  rw [if_neg hij]

lemma pww2_B_M (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    (CoxeterMatrix.B n).M i j =
      (if ((i : ℕ) = n - 1 ∧ (j : ℕ) = n - 2) ∨ ((j : ℕ) = n - 1 ∧ (i : ℕ) = n - 2) then 4
       else if (j : ℕ) + 1 = (i : ℕ) ∨ (i : ℕ) + 1 = (j : ℕ) then 3 else 2) := by
  show (if i = j then 1 else
      (if ((i : ℕ) = n - 1 ∧ (j : ℕ) = n - 2) ∨ ((j : ℕ) = n - 1 ∧ (i : ℕ) = n - 2) then 4
       else if (j : ℕ) + 1 = (i : ℕ) ∨ (i : ℕ) + 1 = (j : ℕ) then 3 else 2)) =
    (if ((i : ℕ) = n - 1 ∧ (j : ℕ) = n - 2) ∨ ((j : ℕ) = n - 1 ∧ (i : ℕ) = n - 2) then 4
       else if (j : ℕ) + 1 = (i : ℕ) ∨ (i : ℕ) + 1 = (j : ℕ) then 3 else 2)
  rw [if_neg hij]

lemma pww2_cartanD_ne_of (n : ℕ) (hn : 4 ≤ n) (i j : Fin n) (hij : i ≠ j)
    (h : ((i : ℕ) + 1 = (j : ℕ) ∧ (j : ℕ) + 2 < n) ∨
         ((j : ℕ) + 1 = (i : ℕ) ∧ (i : ℕ) + 2 < n) ∨
         ((i : ℕ) + 3 = n ∧ ((j : ℕ) + 2 = n ∨ (j : ℕ) + 1 = n)) ∨
         ((j : ℕ) + 3 = n ∧ ((i : ℕ) + 2 = n ∨ (i : ℕ) + 1 = n))) :
    CartanMatrix.D n i j ≠ 0 := by
  show (if i = j then 2 else if n ≤ 2 then 0
      else if (i : ℕ) + 1 = (j : ℕ) ∧ (j : ℕ) + 2 < n then -1
      else if (j : ℕ) + 1 = (i : ℕ) ∧ (i : ℕ) + 2 < n then -1
      else if (i : ℕ) + 3 = n ∧ ((j : ℕ) + 2 = n ∨ (j : ℕ) + 1 = n) then -1
      else if (j : ℕ) + 3 = n ∧ ((i : ℕ) + 2 = n ∨ (i : ℕ) + 1 = n) then -1
      else 0) ≠ 0
  rw [if_neg hij, if_neg (by omega : ¬ n ≤ 2)]
  split_ifs <;> omega

lemma pww2_cartanD_eq_of_not (n : ℕ) (hn : 4 ≤ n) (i j : Fin n) (hij : i ≠ j)
    (h : ¬ (((i : ℕ) + 1 = (j : ℕ) ∧ (j : ℕ) + 2 < n) ∨
         ((j : ℕ) + 1 = (i : ℕ) ∧ (i : ℕ) + 2 < n) ∨
         ((i : ℕ) + 3 = n ∧ ((j : ℕ) + 2 = n ∨ (j : ℕ) + 1 = n)) ∨
         ((j : ℕ) + 3 = n ∧ ((i : ℕ) + 2 = n ∨ (i : ℕ) + 1 = n)))) :
    CartanMatrix.D n i j = 0 := by
  show (if i = j then 2 else if n ≤ 2 then 0
      else if (i : ℕ) + 1 = (j : ℕ) ∧ (j : ℕ) + 2 < n then -1
      else if (j : ℕ) + 1 = (i : ℕ) ∧ (i : ℕ) + 2 < n then -1
      else if (i : ℕ) + 3 = n ∧ ((j : ℕ) + 2 = n ∨ (j : ℕ) + 1 = n) then -1
      else if (j : ℕ) + 3 = n ∧ ((i : ℕ) + 2 = n ∨ (i : ℕ) + 1 = n) then -1
      else 0) = 0
  rw [if_neg hij, if_neg (by omega : ¬ n ≤ 2)]
  simp only [not_or] at h
  rw [if_neg h.1, if_neg h.2.1, if_neg h.2.2.1, if_neg h.2.2.2]

lemma pww2_e7M_eq (i j : Fin 7) (hij : i ≠ j) :
    (CoxeterMatrix.E₇).M i j =
      (if (i.val = 0 ∧ j.val = 2) ∨ (i.val = 2 ∧ j.val = 0) ∨
          (i.val = 1 ∧ j.val = 3) ∨ (i.val = 3 ∧ j.val = 1) ∨
          (i.val = 2 ∧ j.val = 3) ∨ (i.val = 3 ∧ j.val = 2) ∨
          (i.val = 3 ∧ j.val = 4) ∨ (i.val = 4 ∧ j.val = 3) ∨
          (i.val = 4 ∧ j.val = 5) ∨ (i.val = 5 ∧ j.val = 4) ∨
          (i.val = 5 ∧ j.val = 6) ∨ (i.val = 6 ∧ j.val = 5) then 3 else 2) := by
  fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | decide

end CFSG.TwoNodeSmall
