module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallE8
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallVerifyO
public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderExcWeyl

public section

namespace CFSG.TwoNodeSmall

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


private theorem pww_ord_card_coxeterE8 :
    Nat.card (CoxeterMatrix.E₈).Group = 696729600 := by
  have hc : CFSG.Blueprint.Chevalley.Tag.cartan .E8 = CartanMatrix.E 8 :=
    CFSG.LieType.Chevalley.cartanE_eq 8
  have hmat : CoxeterMatrix.E₈ =
      CFSG.LieType.RootSystem.coxeterMatrix (CFSG.LieType.Chevalley.isFiniteType_cartan .E8) := by
    have h := CFSG.StandardType.coxeterMatrix_eq_of_ggIntCartan
      (C := CFSG.Blueprint.Chevalley.Tag.cartan .E8)
      (M := CoxeterMatrix.E₈) (CFSG.LieType.Chevalley.isFiniteType_cartan .E8)
      (hc.symm ▸ CFSG.StandardType.ggIntCartan_E₈)
    exact h.symm
  have hgroup : CFSG.LieType.Chevalley.WeylGroup .E8 = (CoxeterMatrix.E₈).Group :=
    congrArg CoxeterMatrix.Group hmat.symm
  have hcardW : Nat.card (CFSG.LieType.Chevalley.WeylGroup .E8) =
      Nat.card (CoxeterMatrix.E₈).Group := Nat.card_congr (Equiv.cast hgroup)
  rw [← hcardW]
  exact CFSG.StandardType.NoOffExc.card_weyl_E8

private lemma pww_getD_range_map (D : ℕ) (F : ℕ → ℕ) (j : Fin D) :
    (((List.range D).map F).getD j.val 0) = F j.val := by
  have hlen : j.val < ((List.range D).map F).length := by simpa using j.isLt
  rw [List.getD_eq_getElem _ 0 hlen, List.getElem_map]
  have hr : (List.range D)[j.val] = j.val := List.getElem_range (by simpa using j.isLt)
  rw [hr]

private lemma pww_dot_add (P : Pt) (f x y : P.V) :
    P.dot f (x + y) = P.dot f x + P.dot f y := by
  simp only [Pt.dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

private lemma pww_dot_sub (P : Pt) (f x y : P.V) :
    P.dot f (x - y) = P.dot f x - P.dot f y := by
  simp only [Pt.dot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

private lemma pww_dot_smul (P : Pt) (f x : P.V) (a : ZMod P.p) :
    P.dot f (a • x) = a * P.dot f x := by
  simp only [Pt.dot, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

private noncomputable def pww_dotLM (P : Pt) (f : P.V) : Module.Dual (ZMod P.p) P.V where
  toFun := P.dot f
  map_add' := pww_dot_add P f
  map_smul' := by
    intro a x
    simpa using pww_dot_smul P f x a

private lemma pww_dot_single (P : Pt) (f : P.V) (j : Fin P.D) :
    P.dot f (Pi.single j (1 : ZMod P.p)) = f j := by
  simp only [Pt.dot]
  rw [Finset.sum_eq_single j]
  · rw [Pi.single_eq_same]; ring
  · intro k _ hk
    rw [Pi.single_apply, if_neg hk, mul_zero]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

private lemma pww_cast_sigma_coord (p a b : ℕ) (hp : 0 < p) :
    (((a % p + (p - b % p)) % p : ℕ) : ZMod p) = (a : ZMod p) - (b : ZMod p) := by
  rw [ZMod.natCast_mod, Nat.cast_add, Nat.cast_sub (le_of_lt (Nat.mod_lt b hp))]
  rw [ZMod.natCast_mod, ZMod.natCast_mod, ZMod.natCast_self]
  ring

private lemma pww_vec_sigmaApply (P : Pt) [Fact P.p.Prime] (cb : Vec × Vec) (v : Vec) :
    P.vec (P.sigmaApply cb v) = P.vec v - (P.dotv cb.2 v : ZMod P.p) • P.vec cb.1 := by
  have hp : 0 < P.p := (Fact.out (p := P.p.Prime)).pos
  funext i
  simp only [Pt.sigmaApply, Pt.vec, Pt.ent, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [pww_getD_range_map]
  rw [pww_cast_sigma_coord P.p (v.getD i.val 0)
      (P.dotv cb.2 v * (cb.1.getD i.val 0 % P.p)) hp, Nat.cast_mul, ZMod.natCast_mod]

private noncomputable def pww_reflLE (P : Pt) [Fact P.p.Prime] (hwf : P.WF) (r : Refl)
    (hr : r ∈ P.gens) : P.V ≃ₗ[ZMod P.p] P.V :=
  Module.reflection (x := P.vec r.h) (f := pww_dotLM P (P.vec r.f)) (by
    change P.dot (P.vec r.f) (P.vec r.h) = 2
    rw [← Pt.dotv_spec P r.f r.h]
    have h := Pt.dotv_spec P r.f r.h
    rw [hwf r hr] at h
    exact h)

private lemma pww_reflLE_apply (P : Pt) [Fact P.p.Prime] (hwf : P.WF) (r : Refl)
    (hr : r ∈ P.gens) (v : P.V) :
    pww_reflLE P hwf r hr v = v - P.dot (P.vec r.f) v • P.vec r.h := by
  rw [pww_reflLE, Module.reflection_apply]
  rfl

private lemma pww_reflLE_mem (P : Pt) [Fact P.p.Prime] (hwf : P.WF) (r : Refl)
    (hr : r ∈ P.gens) : pww_reflLE P hwf r hr ∈ P.group := by
  apply Subgroup.subset_closure
  exact ⟨r, hr, fun w => pww_reflLE_apply P hwf r hr w⟩

private lemma pww_lin_ext_unit (P : Pt) [Fact P.p.Prime] {W : Type*} [AddCommMonoid W]
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

private lemma pww_le_ext_unit (P : Pt) [Fact P.p.Prime] {f g : P.V ≃ₗ[ZMod P.p] P.V}
    (h : ∀ j : Fin P.D, f (P.vec (P.unit j)) = g (P.vec (P.unit j))) : f = g := by
  have hlm : (f : P.V →ₗ[ZMod P.p] P.V) = (g : P.V →ₗ[ZMod P.p] P.V) := by
    apply pww_lin_ext_unit P
    exact h
  apply LinearEquiv.ext
  intro z
  exact congrFun (congrArg (fun m : P.V →ₗ[ZMod P.p] P.V => (m : P.V → P.V)) hlm) z

private lemma pww_le_eq_one_of_unit (P : Pt) [Fact P.p.Prime] (f : P.V ≃ₗ[ZMod P.p] P.V)
    (h : ∀ j : Fin P.D, f (P.vec (P.unit j)) = P.vec (P.unit j)) : f = 1 := by
  apply pww_le_ext_unit P
  intro j
  rw [h j]
  rfl

private lemma pww_applyWord_append (P : Pt) (x y : Word) (v : Vec) :
    P.applyWord (x ++ y) v = P.applyWord x (P.applyWord y v) := by
  simp only [Pt.applyWord, List.foldr_append]

private lemma pww_vec_applyRefl_eq (P : Pt) [Fact P.p.Prime] (r : Refl) (a b : Vec)
    (h : P.vec a = P.vec b) : P.vec (P.applyRefl r a) = P.vec (P.applyRefl r b) := by
  rw [Pt.vec_applyRefl, Pt.vec_applyRefl, h]

private lemma pww_applyRefl_invol (P : Pt) [Fact P.p.Prime] (hwf : P.WF) (r : Refl)
    (hr : r ∈ P.gens) (v : Vec) :
    P.vec (P.applyRefl r (P.applyRefl r v)) = P.vec v := by
  rw [Pt.vec_applyRefl P r (P.applyRefl r v), Pt.vec_applyRefl P r v]
  have hd : P.dot (P.vec r.f) (P.vec v - P.dot (P.vec r.f) (P.vec v) • P.vec r.h)
      = -(P.dot (P.vec r.f) (P.vec v)) := by
    rw [pww_dot_sub, pww_dot_smul, hwf r hr]; ring
  rw [hd, neg_smul, sub_neg_eq_add, sub_add_cancel]

private lemma pww_wordOK_reverse (P : Pt) (w : Word) (hw : P.wordOK w = true) :
    P.wordOK w.reverse = true := by
  simpa only [Pt.wordOK, List.all_reverse] using hw

private lemma pww_applyWord_reverse_inv (P : Pt) [Fact P.p.Prime] (hwf : P.WF) :
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
        rw [List.reverse_cons, pww_applyWord_append]
        simp only [Pt.applyWord, List.foldr_cons, List.foldr_nil, List.getElem?_eq_getElem hir]
      rw [hword, pww_vec_applyRefl_eq P (P.gens[i]'hir) _ _
          (ih hwt (P.applyRefl (P.gens[i]'hir) v)),
        pww_applyRefl_invol P hwf _ (List.getElem_mem hir) v]

private def pww_S (P : Pt) (c : WWit) : List (Vec × Vec) :=
  c.sigma.map fun s => P.sigmaVecs s.1 s.2

private def pww_cb (P : Pt) (c : WWit) (i : Fin 8) : Vec × Vec :=
  (pww_S P c).getD i.val ([], [])

private lemma pww_S_length (P : Pt) (c : WWit) : (pww_S P c).length = c.sigma.length := by
  simp [pww_S, List.length_map]

private lemma pww_cb_eq (P : Pt) (c : WWit) (i : Fin 8) (hlt : i.val < c.sigma.length) :
    pww_cb P c i
      = P.sigmaVecs ((c.sigma.getD i.val ([], 0)).1) ((c.sigma.getD i.val ([], 0)).2) := by
  unfold pww_cb pww_S
  rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hlt), List.getElem_map,
    List.getD_eq_getElem _ _ hlt]

private lemma pww_e8M_eq (i j : Fin 8) :
    (e8M.getD i.val []).getD j.val 0 = CoxeterMatrix.E₈.M i j := by
  fin_cases i <;> fin_cases j <;> decide

private lemma pww_e8M_val (i j : Fin 8) (hij : i ≠ j) :
    CoxeterMatrix.E₈.M i j = 2 ∨ CoxeterMatrix.E₈.M i j = 3 := by
  fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | decide

private lemma pww_vec_of_vecEq (P : Pt) (v w : Vec) (h : P.vecEq v w = true) :
    P.vec v = P.vec w := by
  simp only [Pt.vecEq, List.all_eq_true, List.mem_range, beq_iff_eq, Pt.ent] at h
  funext i
  show ((v.getD i.val 0 : ℕ) : ZMod P.p) = ((w.getD i.val 0 : ℕ) : ZMod P.p)
  rw [← ZMod.natCast_mod (v.getD i.val 0) P.p,
    ← ZMod.natCast_mod (w.getD i.val 0) P.p, h i.val i.isLt]

private noncomputable def pww_sigmaProd (P : Pt) [Fact P.p.Prime]
    (σ : Fin 8 → P.V ≃ₗ[ZMod P.p] P.V) :
    (w : Word) → (∀ i ∈ w, i < 8) → P.V ≃ₗ[ZMod P.p] P.V
  | [], _ => 1
  | i :: w, hw =>
      σ ⟨i, hw i List.mem_cons_self⟩ *
        pww_sigmaProd P σ w (fun j hj => hw j (List.mem_cons_of_mem i hj))

private lemma pww_sigmaProd_mem (P : Pt) [Fact P.p.Prime]
    (σ : Fin 8 → P.V ≃ₗ[ZMod P.p] P.V) :
    ∀ (w : Word) (hw : ∀ i ∈ w, i < 8),
      pww_sigmaProd P σ w hw ∈ Subgroup.closure (Set.range σ)
  | [], _ => by
      simp only [pww_sigmaProd]
      exact Subgroup.one_mem _
  | i :: w, hw => by
      have hmem : σ ⟨i, hw i List.mem_cons_self⟩ ∈ Subgroup.closure (Set.range σ) :=
        Subgroup.subset_closure ⟨⟨i, hw i List.mem_cons_self⟩, rfl⟩
      have ih := pww_sigmaProd_mem P σ w (fun j hj => hw j (List.mem_cons_of_mem i hj))
      simpa only [pww_sigmaProd] using Subgroup.mul_mem _ hmem ih

private lemma pww_sigmaWord_vec (P : Pt) [Fact P.p.Prime] (S : List (Vec × Vec))
    (hSlen : S.length = 8) (σ : Fin 8 → P.V ≃ₗ[ZMod P.p] P.V)
    (hσ : ∀ i : Fin 8, ∀ v : Vec,
      σ i (P.vec v) = P.vec (P.sigmaApply (S.getD i.val ([], [])) v)) :
    ∀ (w : Word) (hw : ∀ i ∈ w, i < 8) (v : Vec),
      P.vec (P.sigmaWord S w v) = pww_sigmaProd P σ w hw (P.vec v)
  | [], _, v => by
      simp only [Pt.sigmaWord, List.foldr_nil, pww_sigmaProd]
      rfl
  | i :: w, hw, v => by
      have hi : i < 8 := hw i List.mem_cons_self
      have hilt : i < S.length := by rw [hSlen]; exact hi
      have hwt : ∀ j ∈ w, j < 8 := fun j hj => hw j (List.mem_cons_of_mem i hj)
      have hgetD : S.getD i ([], []) = S[i]'hilt := List.getD_eq_getElem _ _ hilt
      have hstep : P.sigmaWord S (i :: w) v =
          P.sigmaApply (S[i]'hilt) (P.sigmaWord S w v) := by
        simp only [Pt.sigmaWord, List.foldr_cons, List.getElem?_eq_getElem hilt]
      rw [hstep, ← hgetD, ← hσ ⟨i, hi⟩ (P.sigmaWord S w v)]
      rw [pww_sigmaWord_vec P S hSlen σ hσ w hwt v]
      simp only [pww_sigmaProd, LinearEquiv.mul_apply]

theorem verifyW_sound {P : Pt}
    [Fact P.p.Prime] (hwf : P.WF) {c : WWit} (h : verifyW P c = true) :
    CFSG.StandardType.ZS.LinWeyl P.p P.group := by
  have hex := h
  rw [verifyW] at hex
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, beq_iff_eq,
    decide_eq_true_eq] at hex
  obtain ⟨⟨⟨⟨hkind, hlen⟩, hwordOK⟩, ⟨⟨⟨hcbAll, hp8⟩, hexpr⟩, hgenAll⟩⟩, hO⟩ := hex
  have hcb : ∀ i : Fin 8, P.dotv (pww_cb P c i).2 (pww_cb P c i).1 = 2 % P.p := by
    intro i
    have hlt : i.val < c.sigma.length := by rw [hlen]; exact i.isLt
    have hlenS : i.val < (pww_S P c).length := by rw [pww_S_length]; exact hlt
    have hmem : (pww_S P c).getD i.val ([], []) ∈ pww_S P c := by
      rw [List.getD_eq_getElem _ _ hlenS]
      exact List.getElem_mem hlenS
    exact hcbAll _ hmem
  set β : Fin 8 → Module.Dual (ZMod P.p) P.V :=
    fun i => pww_dotLM P (P.vec (pww_cb P c i).2) with hβdef
  set cc : Fin 8 → P.V := fun i => P.vec (pww_cb P c i).1 with hccdef
  have hβc : ∀ i, β i (cc i) = 2 := by
    intro i
    rw [hβdef, hccdef]
    have h := Pt.dotv_spec P (pww_cb P c i).2 (pww_cb P c i).1
    rw [hcb i, ZMod.natCast_mod] at h
    exact h.symm
  set σ : Fin 8 → P.V ≃ₗ[ZMod P.p] P.V := fun i => Module.reflection (hβc i) with hσdef
  have hσi : ∀ i, σ i = Module.reflection (hβc i) := by
    intro i; rw [hσdef]
  have hσ : ∀ i v, σ i v = v - β i v • cc i := by
    intro i v
    rw [hσi i, Module.reflection_apply]
  have hσapply : ∀ i v, σ i (P.vec v) = P.vec (P.sigmaApply (pww_cb P c i) v) := by
    intro i v
    rw [hσi i, Module.reflection_apply, pww_vec_sigmaApply, hβdef, hccdef]
    rw [show (pww_dotLM P (P.vec (pww_cb P c i).2)) (P.vec v)
        = P.dot (P.vec (pww_cb P c i).2) (P.vec v) from rfl]
    rw [← Pt.dotv_spec P (pww_cb P c i).2 v]
  have hpair : ∀ i j : Fin 8, i ≠ j →
      (if (e8M.getD i.val []).getD j.val 0 = 2 then
         P.dotv (pww_cb P c i).2 (pww_cb P c j).1 = 0 ∧
           P.dotv (pww_cb P c j).2 (pww_cb P c i).1 = 0
       else (P.dotv (pww_cb P c i).2 (pww_cb P c j).1 *
             P.dotv (pww_cb P c j).2 (pww_cb P c i).1) % P.p = 1) := by
    intro i j hij
    have h := hp8 i.val (List.mem_range.mpr i.isLt) j.val (List.mem_range.mpr j.isLt)
    rcases h with h | h
    · exact absurd (Fin.ext h) hij
    · by_cases h2 : (e8M.getD i.val []).getD j.val 0 = 2
      · rw [if_pos h2] at h
        rw [if_pos h2]
        have hh : (P.dotv (pww_cb P c i).2 (pww_cb P c j).1 == 0) = true ∧
            (P.dotv (pww_cb P c j).2 (pww_cb P c i).1 == 0) = true := by
          simpa only [Bool.and_eq_true, pww_cb, pww_S] using h
        exact ⟨beq_iff_eq.mp hh.1, beq_iff_eq.mp hh.2⟩
      · rw [if_neg h2] at h
        rw [if_neg h2]
        exact beq_iff_eq.mp h
  have hσR : ∀ i, σ i ∈ P.group := by
    intro i
    have hlt : i.val < c.sigma.length := by rw [hlen]; exact i.isLt
    have hmem : c.sigma.getD i.val ([], 0) ∈ c.sigma := by
      rw [List.getD_eq_getElem _ _ hlt]; exact List.getElem_mem hlt
    obtain ⟨hwOK, hk⟩ := hwordOK _ hmem
    have hrmem : P.gens[(c.sigma.getD i.val ([], 0)).2]'hk ∈ P.gens := List.getElem_mem hk
    have hcbeq := pww_cb_eq P c i hlt
    have hcb1 : (pww_cb P c i).1 = P.applyWord (c.sigma.getD i.val ([], 0)).1
        (P.gens[(c.sigma.getD i.val ([], 0)).2]'hk).h := by
      rw [hcbeq]; simp only [Pt.sigmaVecs, List.getD_eq_getElem _ _ hk]
    have hcb2 : (pww_cb P c i).2 = (List.range P.D).map (fun j =>
        P.dotv (P.gens[(c.sigma.getD i.val ([], 0)).2]'hk).f
          (P.applyWord (c.sigma.getD i.val ([], 0)).1.reverse (P.unit j))) := by
      rw [hcbeq]; simp only [Pt.sigmaVecs, List.getD_eq_getElem _ _ hk]
    obtain ⟨γ, hγmem, hγapp⟩ := Pt.applyWord_spec P hwf (c.sigma.getD i.val ([], 0)).1 hwOK
    obtain ⟨δ, hδmem, hδapp⟩ := Pt.applyWord_spec P hwf (c.sigma.getD i.val ([], 0)).1.reverse
      (pww_wordOK_reverse P _ hwOK)
    have hγδ : γ * δ = 1 := by
      apply pww_le_eq_one_of_unit P
      intro j
      show (γ * δ) (P.vec (P.unit j)) = P.vec (P.unit j)
      rw [LinearEquiv.mul_apply, hδapp, hγapp,
        pww_applyWord_reverse_inv P hwf _ hwOK (P.unit j)]
    have hform : pww_dotLM P (P.vec (pww_cb P c i).2)
        = (pww_dotLM P (P.vec (P.gens[(c.sigma.getD i.val ([], 0)).2]'hk).f)).comp
            (δ : P.V →ₗ[ZMod P.p] P.V) := by
      apply pww_lin_ext_unit P
      intro j
      have hLHS : P.dot (P.vec (pww_cb P c i).2) (P.vec (P.unit j))
          = ((P.dotv (P.gens[(c.sigma.getD i.val ([], 0)).2]'hk).f
                (P.applyWord (c.sigma.getD i.val ([], 0)).1.reverse (P.unit j)) : ℕ)
              : ZMod P.p) := by
        rw [hcb2, Pt.vec_unit, pww_dot_single]
        simp only [Pt.vec, pww_getD_range_map]
      change P.dot (P.vec (pww_cb P c i).2) (P.vec (P.unit j))
        = P.dot (P.vec (P.gens[(c.sigma.getD i.val ([], 0)).2]'hk).f) (δ (P.vec (P.unit j)))
      rw [hLHS, hδapp,
        ← Pt.dotv_spec P (P.gens[(c.sigma.getD i.val ([], 0)).2]'hk).f
          (P.applyWord (c.sigma.getD i.val ([], 0)).1.reverse (P.unit j))]
    have heq : σ i = γ * pww_reflLE P hwf (P.gens[(c.sigma.getD i.val ([], 0)).2]'hk) hrmem * δ := by
      ext z
      have hformz : (pww_dotLM P (P.vec (pww_cb P c i).2)) z
          = P.dot (P.vec (P.gens[(c.sigma.getD i.val ([], 0)).2]'hk).f) (δ z) :=
        congrFun (congrArg (fun m : P.V →ₗ[ZMod P.p] ZMod P.p => (m : P.V → ZMod P.p)) hform) z
      have hγδz : γ (δ z) = z := by
        rw [← LinearEquiv.mul_apply, hγδ]; rfl
      rw [hσi i, Module.reflection_apply, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
        pww_reflLE_apply, map_sub, map_smul, hγδz, hγapp, hccdef, ← hcb1]
      rw [hβdef, hformz]
    rw [heq]
    exact P.group.mul_mem (P.group.mul_mem hγmem (pww_reflLE_mem P hwf _ hrmem)) hδmem
  have hrel : ∀ i j : Fin 8, i ≠ j → (σ i * σ j) ^ (CoxeterMatrix.E₈.M i j) = 1 := by
    intro i j hij
    have hM := pww_e8M_eq i j
    have hbij : β i (cc j) = ((P.dotv (pww_cb P c i).2 (pww_cb P c j).1 : ℕ) : ZMod P.p) := by
      rw [hβdef, hccdef]
      change P.dot (P.vec (pww_cb P c i).2) (P.vec (pww_cb P c j).1) = _
      rw [← Pt.dotv_spec P (pww_cb P c i).2 (pww_cb P c j).1]
    have hbji : β j (cc i) = ((P.dotv (pww_cb P c j).2 (pww_cb P c i).1 : ℕ) : ZMod P.p) := by
      rw [hβdef, hccdef]
      change P.dot (P.vec (pww_cb P c j).2) (P.vec (pww_cb P c i).1) = _
      rw [← Pt.dotv_spec P (pww_cb P c j).2 (pww_cb P c i).1]
    rw [hσi i, hσi j]
    by_cases h2 : (e8M.getD i.val []).getD j.val 0 = 2
    · have hMi : CoxeterMatrix.E₈.M i j = 2 := by rw [← hM, h2]
      rw [hMi]
      have hp := hpair i j hij
      rw [if_pos h2] at hp
      obtain ⟨ha, hb⟩ := hp
      have hfy : β i (cc j) = 0 := by rw [hbij, ha, Nat.cast_zero]
      have hgx : β j (cc i) = 0 := by rw [hbji, hb, Nat.cast_zero]
      exact CFSG.StandardType.reflection_mul_reflection_pow_two (hβc i) (hβc j) hfy hgx
    · have hMi : CoxeterMatrix.E₈.M i j = 3 := by
        rcases pww_e8M_val i j hij with h | h
        · exact absurd (by rw [hM]; exact h) h2
        · exact h
      rw [hMi]
      have hp := hpair i j hij
      rw [if_neg h2] at hp
      have hprod : β i (cc j) * β j (cc i) = 1 := by
        rw [hbij, hbji, ← Nat.cast_mul,
          ← ZMod.natCast_mod (P.dotv (pww_cb P c i).2 (pww_cb P c j).1 *
            P.dotv (pww_cb P c j).2 (pww_cb P c i).1) P.p, hp, Nat.cast_one]
      exact CFSG.StandardType.reflection_mul_reflection_pow_three (hβc i) (hβc j) hprod
  have hgen : P.group ≤ Subgroup.closure (Set.range σ) := by
    rw [Pt.group, Subgroup.closure_le]
    intro e he
    obtain ⟨r, hr, hee⟩ := he
    obtain ⟨g, hg, hgr⟩ := List.mem_iff_getElem.mp hr
    have hglenE : g < c.expr.length := by rw [hexpr]; exact hg
    let w : Word := c.expr[g]'hglenE
    have hzip : (c.expr[g]'hglenE, P.gens[g]'hg) ∈ c.expr.zip P.gens := by
      have hziplen : g < (c.expr.zip P.gens).length := by
        rw [List.length_zip]
        exact Nat.lt_min.mpr ⟨hglenE, hg⟩
      have hgzip : (c.expr.zip P.gens)[g]'hziplen = (c.expr[g]'hglenE, P.gens[g]'hg) := by
        rw [List.getElem_zip]
      rw [← hgzip]
      exact List.getElem_mem hziplen
    obtain ⟨hw8, hvec⟩ := hgenAll _ hzip
    rw [hgr] at hvec
    have hvec' : ∀ j : Fin P.D,
        P.vec (P.sigmaWord (pww_S P c) w (P.unit j)) = P.vec (P.applyRefl r (P.unit j)) := by
      intro j
      exact pww_vec_of_vecEq P _ _ (hvec j.val (List.mem_range.mpr j.isLt))
    have hprod : pww_sigmaProd P σ w hw8 = pww_reflLE P hwf r hr := by
      apply pww_le_ext_unit P
      intro j
      rw [← pww_sigmaWord_vec P (pww_S P c) (by rw [pww_S_length]; exact hlen) σ hσapply w hw8
          (P.unit j),
        hvec' j, Pt.vec_applyRefl, pww_reflLE_apply]
    have heq : e = pww_sigmaProd P σ w hw8 := by
      rw [show e = pww_reflLE P hwf r hr from by
        ext z
        rw [hee z, pww_reflLE_apply], ← hprod]
    rw [heq]
    exact pww_sigmaProd_mem P σ w hw8
  have hcard : Nat.card CoxeterMatrix.E₈.Group ≤ Nat.card P.group := by
    rw [pww_ord_card_coxeterE8]
    have := verifyO_sound (P := P) hwf hO
    omega
  exact linWeyl_E8_of_simple_system P.group σ hσR cc β hσ hβc hrel hgen hcard

end CFSG.TwoNodeSmall
