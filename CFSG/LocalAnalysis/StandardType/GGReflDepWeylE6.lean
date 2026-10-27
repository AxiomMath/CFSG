module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoAux
public import Certificates.Data.CFSGNative.DepFrame.Check
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallPosWeylLemmas
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallPosWeylSys
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallVerifyO

public section

namespace CFSG.DepFrame

open CFSG.TwoNodeSmall

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private def we6_cb (P : Pt) (c : WWit) (i : Fin 6) : Vec × Vec :=
  (pww2_S P c).getD i.val ([], [])

private lemma we6_cb_eq (P : Pt) (c : WWit) (i : Fin 6) (hlt : i.val < c.sigma.length) :
    we6_cb P c i
      = P.sigmaVecs ((c.sigma.getD i.val ([], 0)).1) ((c.sigma.getD i.val ([], 0)).2) := by
  unfold we6_cb pww2_S
  rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hlt), List.getElem_map,
    List.getD_eq_getElem _ _ hlt]

private lemma pww2_e6M_eq (i j : Fin 6) (hij : i ≠ j) :
    (CoxeterMatrix.E₆).M i j = (if e6Edge i.val j.val then 3 else 2) := by
  fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | decide

theorem verifyWE6_sound {P : Pt}
    [Fact P.p.Prime] (hwf : P.WF) {c : WWit} (h : verifyWE6 P c = true) :
    CFSG.StandardType.ZS.LinWeyl P.p P.group := by
  have hex := h
  unfold verifyWE6 at hex
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, beq_iff_eq,
    decide_eq_true_eq] at hex
  simp only [and_assoc] at hex
  obtain ⟨hlen, hwordAll, hcbAll, hp6, hexpr, hgenAll, hO⟩ := hex
  have hcb : ∀ i : Fin 6, P.dotv (we6_cb P c i).2 (we6_cb P c i).1 = 2 % P.p := by
    intro i
    have hlt : i.val < c.sigma.length := by rw [hlen]; exact i.isLt
    have hlenS : i.val < (pww2_S P c).length := by rw [pww2_S_length]; exact hlt
    have hmem : (pww2_S P c).getD i.val ([], []) ∈ pww2_S P c := by
      rw [List.getD_eq_getElem _ _ hlenS]
      exact List.getElem_mem hlenS
    exact hcbAll _ hmem
  set β : Fin 6 → Module.Dual (ZMod P.p) P.V :=
    fun i => pww2_dotLM P (P.vec (we6_cb P c i).2) with hβdef
  set cc : Fin 6 → P.V := fun i => P.vec (we6_cb P c i).1 with hccdef
  have hβc : ∀ i, β i (cc i) = 2 := by
    intro i
    rw [hβdef, hccdef]
    have h := Pt.dotv_spec P (we6_cb P c i).2 (we6_cb P c i).1
    rw [hcb i, ZMod.natCast_mod] at h
    exact h.symm
  set σ : Fin 6 → P.V ≃ₗ[ZMod P.p] P.V := fun i => Module.reflection (hβc i) with hσdef
  have hσi : ∀ i, σ i = Module.reflection (hβc i) := by
    intro i; rw [hσdef]
  have hσ : ∀ i v, σ i v = v - β i v • cc i := by
    intro i v
    rw [hσi i, Module.reflection_apply]
  have hσapply : ∀ i v, σ i (P.vec v) = P.vec (P.sigmaApply (we6_cb P c i) v) := by
    intro i v
    rw [hσi i, Module.reflection_apply, pww2_vec_sigmaApply, hβdef, hccdef]
    rw [show (pww2_dotLM P (P.vec (we6_cb P c i).2)) (P.vec v)
        = P.dot (P.vec (we6_cb P c i).2) (P.vec v) from rfl]
    rw [← Pt.dotv_spec P (we6_cb P c i).2 v]
  have hpair6 : ∀ i j : Fin 6, i ≠ j →
      (if e6Edge i.val j.val then
         (P.dotv (we6_cb P c i).2 (we6_cb P c j).1 *
           P.dotv (we6_cb P c j).2 (we6_cb P c i).1) % P.p = 1
       else P.dotv (we6_cb P c i).2 (we6_cb P c j).1 = 0 ∧
         P.dotv (we6_cb P c j).2 (we6_cb P c i).1 = 0) := by
    intro i j hij
    have h := hp6 i.val (List.mem_range.mpr i.isLt) j.val (List.mem_range.mpr j.isLt)
    rcases h with h | h
    · exact absurd (Fin.ext h) hij
    · by_cases hadj : e6Edge i.val j.val
      · rw [if_pos hadj] at h
        rw [if_pos hadj]
        have h' := beq_iff_eq.mp h
        simpa only [we6_cb, pww2_S] using h'
      · rw [if_neg hadj] at h
        rw [if_neg hadj]
        have hh : (P.dotv (we6_cb P c i).2 (we6_cb P c j).1 == 0) = true ∧
            (P.dotv (we6_cb P c j).2 (we6_cb P c i).1 == 0) = true := by
          simpa only [Bool.and_eq_true, we6_cb, pww2_S] using h
        exact ⟨beq_iff_eq.mp hh.1, beq_iff_eq.mp hh.2⟩
  have hσR : ∀ i, σ i ∈ P.group := by
    intro i
    have hlt : i.val < c.sigma.length := by rw [hlen]; exact i.isLt
    have hmem : c.sigma.getD i.val ([], 0) ∈ c.sigma := by
      rw [List.getD_eq_getElem _ _ hlt]; exact List.getElem_mem hlt
    obtain ⟨hwOK, hk⟩ := hwordAll _ hmem
    have hrmem : P.gens[(c.sigma.getD i.val ([], 0)).2]'hk ∈ P.gens := List.getElem_mem hk
    have hcbeq := we6_cb_eq P c i hlt
    have hcb1 : (we6_cb P c i).1 = P.applyWord (c.sigma.getD i.val ([], 0)).1
        (P.gens[(c.sigma.getD i.val ([], 0)).2]'hk).h := by
      rw [hcbeq]; simp only [Pt.sigmaVecs, List.getD_eq_getElem _ _ hk]
    have hcb2 : (we6_cb P c i).2 = (List.range P.D).map (fun j =>
        P.dotv (P.gens[(c.sigma.getD i.val ([], 0)).2]'hk).f
          (P.applyWord (c.sigma.getD i.val ([], 0)).1.reverse (P.unit j))) := by
      rw [hcbeq]; simp only [Pt.sigmaVecs, List.getD_eq_getElem _ _ hk]
    obtain ⟨γ, hγmem, hγapp⟩ := Pt.applyWord_spec P hwf (c.sigma.getD i.val ([], 0)).1 hwOK
    obtain ⟨δ, hδmem, hδapp⟩ := Pt.applyWord_spec P hwf (c.sigma.getD i.val ([], 0)).1.reverse
      (pww2_wordOK_reverse P _ hwOK)
    have hγδ : γ * δ = 1 := by
      apply pww2_le_eq_one_of_unit P
      intro j
      show (γ * δ) (P.vec (P.unit j)) = P.vec (P.unit j)
      rw [LinearEquiv.mul_apply, hδapp, hγapp,
        pww2_applyWord_reverse_inv P hwf _ hwOK (P.unit j)]
    have hform : pww2_dotLM P (P.vec (we6_cb P c i).2)
        = (pww2_dotLM P (P.vec (P.gens[(c.sigma.getD i.val ([], 0)).2]'hk).f)).comp
            (δ : P.V →ₗ[ZMod P.p] P.V) := by
      apply pww2_lin_ext_unit P
      intro j
      have hLHS : P.dot (P.vec (we6_cb P c i).2) (P.vec (P.unit j))
          = ((P.dotv (P.gens[(c.sigma.getD i.val ([], 0)).2]'hk).f
                (P.applyWord (c.sigma.getD i.val ([], 0)).1.reverse (P.unit j)) : ℕ)
              : ZMod P.p) := by
        rw [hcb2, Pt.vec_unit, pww2_dot_single]
        simp only [Pt.vec, pww2_getD_range_map]
      change P.dot (P.vec (we6_cb P c i).2) (P.vec (P.unit j))
        = P.dot (P.vec (P.gens[(c.sigma.getD i.val ([], 0)).2]'hk).f) (δ (P.vec (P.unit j)))
      rw [hLHS, hδapp,
        ← Pt.dotv_spec P (P.gens[(c.sigma.getD i.val ([], 0)).2]'hk).f
          (P.applyWord (c.sigma.getD i.val ([], 0)).1.reverse (P.unit j))]
    have heq : σ i = γ * pww2_reflLE P hwf (P.gens[(c.sigma.getD i.val ([], 0)).2]'hk) hrmem * δ := by
      ext z
      have hformz : (pww2_dotLM P (P.vec (we6_cb P c i).2)) z
          = P.dot (P.vec (P.gens[(c.sigma.getD i.val ([], 0)).2]'hk).f) (δ z) :=
        congrFun (congrArg (fun m : P.V →ₗ[ZMod P.p] ZMod P.p => (m : P.V → ZMod P.p)) hform) z
      have hγδz : γ (δ z) = z := by
        rw [← LinearEquiv.mul_apply, hγδ]; rfl
      rw [hσi i, Module.reflection_apply, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
        pww2_reflLE_apply, map_sub, map_smul, hγδz, hγapp, hccdef, ← hcb1]
      rw [hβdef, hformz]
    rw [heq]
    exact P.group.mul_mem (P.group.mul_mem hγmem (pww2_reflLE_mem P hwf _ hrmem)) hδmem
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
    obtain ⟨hw6, hvec⟩ := hgenAll _ hzip
    rw [hgr] at hvec
    have hvec' : ∀ j : Fin P.D,
        P.vec (P.sigmaWord (pww2_S P c) w (P.unit j)) = P.vec (P.applyRefl r (P.unit j)) := by
      intro j
      exact pww2_vec_of_vecEq P _ _ (hvec j.val (List.mem_range.mpr j.isLt))
    have hprod : pww2_sigmaProd P σ w hw6 = pww2_reflLE P hwf r hr := by
      apply pww2_le_ext_unit P
      intro j
      rw [← pww2_sigmaWord_vec P (pww2_S P c) (by rw [pww2_S_length]; exact hlen) σ hσapply w hw6
          (P.unit j),
        hvec' j, Pt.vec_applyRefl, pww2_reflLE_apply]
    have heq : e = pww2_sigmaProd P σ w hw6 := by
      rw [show e = pww2_reflLE P hwf r hr from by
        ext z
        rw [hee z, pww2_reflLE_apply], ← hprod]
    rw [heq]
    exact pww2_sigmaProd_mem P σ w hw6
  have hrel : ∀ i j : Fin 6, i ≠ j → (σ i * σ j) ^ (CoxeterMatrix.E₆).M i j = 1 := by
    intro i j hij
    have hbij : β i (cc j) = ((P.dotv (we6_cb P c i).2 (we6_cb P c j).1 : ℕ) : ZMod P.p) := by
      rw [hβdef, hccdef]
      change P.dot (P.vec (we6_cb P c i).2) (P.vec (we6_cb P c j).1) = _
      rw [← Pt.dotv_spec P (we6_cb P c i).2 (we6_cb P c j).1]
    have hbji : β j (cc i) = ((P.dotv (we6_cb P c j).2 (we6_cb P c i).1 : ℕ) : ZMod P.p) := by
      rw [hβdef, hccdef]
      change P.dot (P.vec (we6_cb P c j).2) (P.vec (we6_cb P c i).1) = _
      rw [← Pt.dotv_spec P (we6_cb P c j).2 (we6_cb P c i).1]
    have hp := hpair6 i j hij
    by_cases hadj : e6Edge i.val j.val
    · rw [if_pos hadj] at hp
      rw [pww2_e6M_eq i j hij, if_pos hadj]
      rw [hσi i, hσi j]
      have hprod : β i (cc j) * β j (cc i) = 1 := by
        rw [hbij, hbji, ← Nat.cast_mul,
          ← ZMod.natCast_mod (P.dotv (we6_cb P c i).2 (we6_cb P c j).1 *
            P.dotv (we6_cb P c j).2 (we6_cb P c i).1) P.p, hp, Nat.cast_one]
      exact CFSG.StandardType.reflection_mul_reflection_pow_three (hβc i) (hβc j) hprod
    · rw [if_neg hadj] at hp
      obtain ⟨ha, hb⟩ := hp
      rw [pww2_e6M_eq i j hij, if_neg hadj]
      rw [hσi i, hσi j]
      have hfy : β i (cc j) = 0 := by rw [hbij, ha, Nat.cast_zero]
      have hgx : β j (cc i) = 0 := by rw [hbji, hb, Nat.cast_zero]
      exact CFSG.StandardType.reflection_mul_reflection_pow_two (hβc i) (hβc j) hfy hgx
  have hcard : Nat.card (CoxeterMatrix.E₆).Group ≤ Nat.card P.group := by
    rw [CFSG.StandardType.card_coxeterE6_group]
    have := verifyO_sound (P := P) hwf hO
    omega
  haveI : Finite (CoxeterMatrix.E₆).Group := by
    apply Nat.finite_of_card_ne_zero
    rw [CFSG.StandardType.card_coxeterE6_group]
    norm_num
  exact pws_linWeyl_of_simple_system (CoxeterMatrix.E₆)
    CFSG.StandardType.ggIsWeylMatrix_E6 P.group σ hσR cc β hσ hβc hrel hgen hcard

end CFSG.DepFrame

end
