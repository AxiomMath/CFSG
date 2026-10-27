module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallPosWeylSys
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallPosWeylLemmas
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallVerifyO
public import Certificates.Data.CFSGNative.TwoNodeSmall.VerifyPos

public section

namespace CFSG.TwoNodeSmall

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem verifyWPos_sound {P : Pt}
    [Fact P.p.Prime] (hwf : P.WF) {c : WWit} (h : verifyWPos P c = true) :
    CFSG.StandardType.ZS.LinWeyl P.p P.group := by
  have hex := h
  unfold verifyWPos at hex
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, beq_iff_eq,
    decide_eq_true_eq] at hex
  obtain ⟨⟨⟨⟨⟨hkind, hbounds⟩, hlen⟩, hwordOK⟩, hEblock⟩, hO⟩ := hex
  obtain ⟨⟨⟨hcbAll, hp8⟩, hexpr⟩, hgenAll⟩ := hEblock
  have hk : c.kind = 0 ∨ c.kind = 1 ∨ c.kind = 2 ∨ c.kind = 3 := by omega
  have hcb : ∀ i : Fin P.D, P.dotv (pww2_cb P c i).2 (pww2_cb P c i).1 = 2 % P.p := by
    intro i
    have hlt : i.val < c.sigma.length := by rw [hlen]; exact i.isLt
    have hlenS : i.val < (pww2_S P c).length := by rw [pww2_S_length]; exact hlt
    have hmem : (pww2_S P c).getD i.val ([], []) ∈ pww2_S P c := by
      rw [List.getD_eq_getElem _ _ hlenS]
      exact List.getElem_mem hlenS
    exact hcbAll _ hmem
  set β : Fin P.D → Module.Dual (ZMod P.p) P.V :=
    fun i => pww2_dotLM P (P.vec (pww2_cb P c i).2) with hβdef
  set cc : Fin P.D → P.V := fun i => P.vec (pww2_cb P c i).1 with hccdef
  have hβc : ∀ i, β i (cc i) = 2 := by
    intro i
    rw [hβdef, hccdef]
    have h := Pt.dotv_spec P (pww2_cb P c i).2 (pww2_cb P c i).1
    rw [hcb i, ZMod.natCast_mod] at h
    exact h.symm
  set σ : Fin P.D → P.V ≃ₗ[ZMod P.p] P.V := fun i => Module.reflection (hβc i) with hσdef
  have hσi : ∀ i, σ i = Module.reflection (hβc i) := by
    intro i; rw [hσdef]
  have hσ : ∀ i v, σ i v = v - β i v • cc i := by
    intro i v
    rw [hσi i, Module.reflection_apply]
  have hσapply : ∀ i v, σ i (P.vec v) = P.vec (P.sigmaApply (pww2_cb P c i) v) := by
    intro i v
    rw [hσi i, Module.reflection_apply, pww2_vec_sigmaApply, hβdef, hccdef]
    rw [show (pww2_dotLM P (P.vec (pww2_cb P c i).2)) (P.vec v)
        = P.dot (P.vec (pww2_cb P c i).2) (P.vec v) from rfl]
    rw [← Pt.dotv_spec P (pww2_cb P c i).2 v]
  have hbij : ∀ i j : Fin P.D,
      β i (cc j) = ((P.dotv (pww2_cb P c i).2 (pww2_cb P c j).1 : ℕ) : ZMod P.p) := by
    intro i j
    rw [hβdef, hccdef]
    change P.dot (P.vec (pww2_cb P c i).2) (P.vec (pww2_cb P c j).1) = _
    rw [← Pt.dotv_spec P (pww2_cb P c i).2 (pww2_cb P c j).1]
  have hbji : ∀ i j : Fin P.D,
      β j (cc i) = ((P.dotv (pww2_cb P c j).2 (pww2_cb P c i).1 : ℕ) : ZMod P.p) := by
    intro i j
    rw [hβdef, hccdef]
    change P.dot (P.vec (pww2_cb P c j).2) (P.vec (pww2_cb P c i).1) = _
    rw [← Pt.dotv_spec P (pww2_cb P c j).2 (pww2_cb P c i).1]
  have hσR : ∀ i, σ i ∈ P.group := by
    intro i
    have hlt : i.val < c.sigma.length := by rw [hlen]; exact i.isLt
    have hmem : c.sigma.getD i.val ([], 0) ∈ c.sigma := by
      rw [List.getD_eq_getElem _ _ hlt]; exact List.getElem_mem hlt
    obtain ⟨hwOK, hk⟩ := hwordOK _ hmem
    have hrmem : P.gens[(c.sigma.getD i.val ([], 0)).2]'hk ∈ P.gens := List.getElem_mem hk
    have hcbeq := pww2_cb_eq P c i hlt
    have hcb1 : (pww2_cb P c i).1 = P.applyWord (c.sigma.getD i.val ([], 0)).1
        (P.gens[(c.sigma.getD i.val ([], 0)).2]'hk).h := by
      rw [hcbeq]; simp only [Pt.sigmaVecs, List.getD_eq_getElem _ _ hk]
    have hcb2 : (pww2_cb P c i).2 = (List.range P.D).map (fun j =>
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
    have hform : pww2_dotLM P (P.vec (pww2_cb P c i).2)
        = (pww2_dotLM P (P.vec (P.gens[(c.sigma.getD i.val ([], 0)).2]'hk).f)).comp
            (δ : P.V →ₗ[ZMod P.p] P.V) := by
      apply pww2_lin_ext_unit P
      intro j
      have hLHS : P.dot (P.vec (pww2_cb P c i).2) (P.vec (P.unit j))
          = ((P.dotv (P.gens[(c.sigma.getD i.val ([], 0)).2]'hk).f
                (P.applyWord (c.sigma.getD i.val ([], 0)).1.reverse (P.unit j)) : ℕ)
              : ZMod P.p) := by
        rw [hcb2, Pt.vec_unit, pww2_dot_single]
        simp only [Pt.vec, pww2_getD_range_map]
      change P.dot (P.vec (pww2_cb P c i).2) (P.vec (P.unit j))
        = P.dot (P.vec (P.gens[(c.sigma.getD i.val ([], 0)).2]'hk).f) (δ (P.vec (P.unit j)))
      rw [hLHS, hδapp,
        ← Pt.dotv_spec P (P.gens[(c.sigma.getD i.val ([], 0)).2]'hk).f
          (P.applyWord (c.sigma.getD i.val ([], 0)).1.reverse (P.unit j))]
    have heq : σ i = γ * pww2_reflLE P hwf (P.gens[(c.sigma.getD i.val ([], 0)).2]'hk) hrmem * δ := by
      ext z
      have hformz : (pww2_dotLM P (P.vec (pww2_cb P c i).2)) z
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
    obtain ⟨hw8, hvec⟩ := hgenAll _ hzip
    rw [hgr] at hvec
    have hvec' : ∀ j : Fin P.D,
        P.vec (P.sigmaWord (pww2_S P c) w (P.unit j)) = P.vec (P.applyRefl r (P.unit j)) := by
      intro j
      exact pww2_vec_of_vecEq P _ _ (hvec j.val (List.mem_range.mpr j.isLt))
    have hprod : pww2_sigmaProd P σ w hw8 = pww2_reflLE P hwf r hr := by
      apply pww2_le_ext_unit P
      intro j
      rw [← pww2_sigmaWord_vec P (pww2_S P c) (by rw [pww2_S_length]; exact hlen) σ hσapply w hw8
          (P.unit j),
        hvec' j, Pt.vec_applyRefl, pww2_reflLE_apply]
    have heq : e = pww2_sigmaProd P σ w hw8 := by
      rw [show e = pww2_reflLE P hwf r hr from by
        ext z
        rw [hee z, pww2_reflLE_apply], ← hprod]
    rw [heq]
    exact pww2_sigmaProd_mem P σ w hw8
  rcases hk with hk0 | hk1 | hk2 | hk3
  ·
    have hD1 : 1 ≤ P.D := by omega
    have hrel : ∀ i j : Fin P.D, i ≠ j →
        (σ i * σ j) ^ (CoxeterMatrix.A P.D).M i j = 1 := by
      intro i j hij
      have hp := hp8 i.val (List.mem_range.mpr i.isLt) j.val (List.mem_range.mpr j.isLt)
      rcases hp with hp | hp
      · exact absurd (Fin.ext hp) hij
      · rw [hk0] at hp
        rw [if_pos rfl] at hp
        by_cases hadj : i.val + 1 = j.val ∨ j.val + 1 = i.val
        · have h1 : (P.dotv (pww2_cb P c i).2 (pww2_cb P c j).1 *
              P.dotv (pww2_cb P c j).2 (pww2_cb P c i).1) % P.p = 1 := by
            have hh := hp
            rw [if_pos hadj] at hh
            simpa only [beq_iff_eq, pww2_cb, pww2_S] using hh
          rw [pww2_A_M P.D i j hij, if_pos (by tauto)]
          rw [hσi i, hσi j]
          have hprod : β i (cc j) * β j (cc i) = 1 := by
            rw [hbij i j, hbji i j, ← Nat.cast_mul,
              ← ZMod.natCast_mod (P.dotv (pww2_cb P c i).2 (pww2_cb P c j).1 *
                P.dotv (pww2_cb P c j).2 (pww2_cb P c i).1) P.p, h1, Nat.cast_one]
          exact CFSG.StandardType.reflection_mul_reflection_pow_three (hβc i) (hβc j) hprod
        · have h0 : P.dotv (pww2_cb P c i).2 (pww2_cb P c j).1 = 0 ∧
              P.dotv (pww2_cb P c j).2 (pww2_cb P c i).1 = 0 := by
            have hh := hp
            rw [if_neg hadj] at hh
            simpa only [Bool.and_eq_true, beq_iff_eq, pww2_cb, pww2_S] using hh
          rw [pww2_A_M P.D i j hij,
            if_neg (by tauto : ¬ ((j : ℕ) + 1 = (i : ℕ) ∨ (i : ℕ) + 1 = (j : ℕ)))]
          rw [hσi i, hσi j]
          have hfy : β i (cc j) = 0 := by rw [hbij i j, h0.1, Nat.cast_zero]
          have hgx : β j (cc i) = 0 := by rw [hbji i j, h0.2, Nat.cast_zero]
          exact CFSG.StandardType.reflection_mul_reflection_pow_two (hβc i) (hβc j) hfy hgx
    have hcard : Nat.card (CoxeterMatrix.A P.D).Group ≤ Nat.card P.group := by
      rw [pws_card_coxeterA]
      rw [hk0] at hO
      rw [if_pos rfl] at hO
      have hlt := verifyO_sound (P := P) hwf hO
      have hpos : 0 < natFact (P.D + 1) := by rw [natFact_eq]; exact Nat.factorial_pos _
      omega
    haveI : Finite (CoxeterMatrix.A P.D).Group := pws_finite_coxeterA P.D
    exact pws_linWeyl_of_simple_system (CoxeterMatrix.A P.D)
      (pws_ggIsWeylMatrix_A P.D hD1) P.group σ hσR cc β hσ hβc hrel hgen hcard
  ·
    have hD2 : 2 ≤ P.D := by omega
    have hrel : ∀ i j : Fin P.D, i ≠ j →
        (σ i * σ j) ^ (CoxeterMatrix.B P.D).M i j = 1 := by
      intro i j hij
      have hp := hp8 i.val (List.mem_range.mpr i.isLt) j.val (List.mem_range.mpr j.isLt)
      rcases hp with hp | hp
      · exact absurd (Fin.ext hp) hij
      · rw [hk1] at hp
        rw [if_neg (by decide : ¬ ((1:ℕ) = 0)), if_pos rfl] at hp
        by_cases hdb : (i.val = P.D - 1 ∧ j.val = P.D - 2) ∨
            (j.val = P.D - 1 ∧ i.val = P.D - 2)
        · have h2 : (P.dotv (pww2_cb P c i).2 (pww2_cb P c j).1 *
              P.dotv (pww2_cb P c j).2 (pww2_cb P c i).1) % P.p = 2 := by
            have hh := hp
            rw [if_pos hdb] at hh
            simpa only [beq_iff_eq, pww2_cb, pww2_S] using hh
          rw [pww2_B_M P.D i j hij, if_pos (by tauto)]
          rw [hσi i, hσi j]
          have hprod : β i (cc j) * β j (cc i) = 2 := by
            rw [hbij i j, hbji i j, ← Nat.cast_mul,
              ← ZMod.natCast_mod (P.dotv (pww2_cb P c i).2 (pww2_cb P c j).1 *
                P.dotv (pww2_cb P c j).2 (pww2_cb P c i).1) P.p, h2]
            norm_num
          exact CFSG.StandardType.reflection_mul_reflection_pow_four (hβc i) (hβc j) hprod
        · rw [if_neg (by tauto)] at hp
          by_cases hadj : i.val + 1 = j.val ∨ j.val + 1 = i.val
          · have h1 : (P.dotv (pww2_cb P c i).2 (pww2_cb P c j).1 *
                P.dotv (pww2_cb P c j).2 (pww2_cb P c i).1) % P.p = 1 := by
              have hh := hp
              rw [if_pos (by tauto)] at hh
              simpa only [beq_iff_eq, pww2_cb, pww2_S] using hh
            rw [pww2_B_M P.D i j hij,
              if_neg (by tauto : ¬ (((i : ℕ) = P.D - 1 ∧ (j : ℕ) = P.D - 2) ∨
                ((j : ℕ) = P.D - 1 ∧ (i : ℕ) = P.D - 2))),
              if_pos (by tauto)]
            rw [hσi i, hσi j]
            have hprod : β i (cc j) * β j (cc i) = 1 := by
              rw [hbij i j, hbji i j, ← Nat.cast_mul,
                ← ZMod.natCast_mod (P.dotv (pww2_cb P c i).2 (pww2_cb P c j).1 *
                  P.dotv (pww2_cb P c j).2 (pww2_cb P c i).1) P.p, h1, Nat.cast_one]
            exact CFSG.StandardType.reflection_mul_reflection_pow_three (hβc i) (hβc j) hprod
          · have h0 : P.dotv (pww2_cb P c i).2 (pww2_cb P c j).1 = 0 ∧
                P.dotv (pww2_cb P c j).2 (pww2_cb P c i).1 = 0 := by
              have hh := hp
              rw [if_neg (by tauto)] at hh
              simpa only [Bool.and_eq_true, beq_iff_eq, pww2_cb, pww2_S] using hh
            rw [pww2_B_M P.D i j hij,
              if_neg (by tauto : ¬ (((i : ℕ) = P.D - 1 ∧ (j : ℕ) = P.D - 2) ∨
                ((j : ℕ) = P.D - 1 ∧ (i : ℕ) = P.D - 2))),
              if_neg (by tauto : ¬ ((j : ℕ) + 1 = (i : ℕ) ∨ (i : ℕ) + 1 = (j : ℕ)))]
            rw [hσi i, hσi j]
            have hfy : β i (cc j) = 0 := by rw [hbij i j, h0.1, Nat.cast_zero]
            have hgx : β j (cc i) = 0 := by rw [hbji i j, h0.2, Nat.cast_zero]
            exact CFSG.StandardType.reflection_mul_reflection_pow_two (hβc i) (hβc j) hfy hgx
    have hcard : Nat.card (CoxeterMatrix.B P.D).Group ≤ Nat.card P.group := by
      rw [pws_card_coxeterB P.D hD2]
      rw [hk1] at hO
      rw [if_neg (by decide : ¬ ((1:ℕ) = 0)), if_pos rfl] at hO
      have hlt := verifyO_sound (P := P) hwf hO
      have hpos : 0 < 2 ^ P.D * natFact P.D := by rw [natFact_eq]; positivity
      omega
    haveI : Finite (CoxeterMatrix.B P.D).Group := pws_finite_coxeterB P.D hD2
    exact pws_linWeyl_of_simple_system (CoxeterMatrix.B P.D)
      (pws_ggIsWeylMatrix_B P.D hD2) P.group σ hσR cc β hσ hβc hrel hgen hcard
  ·
    have hD4 : 4 ≤ P.D := by omega
    have hrel : ∀ i j : Fin P.D, i ≠ j →
        (σ i * σ j) ^ (CFSG.StandardType.ggCoxeterMatrixD P.D).M i j = 1 := by
      intro i j hij
      have hp := hp8 i.val (List.mem_range.mpr i.isLt) j.val (List.mem_range.mpr j.isLt)
      rcases hp with hp | hp
      · exact absurd (Fin.ext hp) hij
      · rw [hk2] at hp
        rw [if_neg (by decide : ¬ ((2:ℕ) = 0)),
          if_neg (by decide : ¬ ((2:ℕ) = 1)), if_pos rfl] at hp
        by_cases hadj : ((i.val + 1 = j.val ∧ j.val + 2 < P.D) ∨
            (j.val + 1 = i.val ∧ i.val + 2 < P.D) ∨
            (i.val + 3 = P.D ∧ (j.val + 2 = P.D ∨ j.val + 1 = P.D)) ∨
            (j.val + 3 = P.D ∧ (i.val + 2 = P.D ∨ i.val + 1 = P.D)))
        · have h1 : (P.dotv (pww2_cb P c i).2 (pww2_cb P c j).1 *
              P.dotv (pww2_cb P c j).2 (pww2_cb P c i).1) % P.p = 1 := by
            have hh := hp
            rw [if_pos hadj] at hh
            simpa only [beq_iff_eq, pww2_cb, pww2_S] using hh
          rw [CFSG.StandardType.ggCoxeterMatrixD_apply, if_neg hij,
            if_neg (pww2_cartanD_ne_of P.D hD4 i j hij (by simpa using hadj))]
          rw [hσi i, hσi j]
          have hprod : β i (cc j) * β j (cc i) = 1 := by
            rw [hbij i j, hbji i j, ← Nat.cast_mul,
              ← ZMod.natCast_mod (P.dotv (pww2_cb P c i).2 (pww2_cb P c j).1 *
                P.dotv (pww2_cb P c j).2 (pww2_cb P c i).1) P.p, h1, Nat.cast_one]
          exact CFSG.StandardType.reflection_mul_reflection_pow_three (hβc i) (hβc j) hprod
        · have h0 : P.dotv (pww2_cb P c i).2 (pww2_cb P c j).1 = 0 ∧
              P.dotv (pww2_cb P c j).2 (pww2_cb P c i).1 = 0 := by
            have hh := hp
            rw [if_neg hadj] at hh
            simpa only [Bool.and_eq_true, beq_iff_eq, pww2_cb, pww2_S] using hh
          rw [CFSG.StandardType.ggCoxeterMatrixD_apply, if_neg hij,
            if_pos (pww2_cartanD_eq_of_not P.D hD4 i j hij (by simpa using hadj))]
          rw [hσi i, hσi j]
          have hfy : β i (cc j) = 0 := by rw [hbij i j, h0.1, Nat.cast_zero]
          have hgx : β j (cc i) = 0 := by rw [hbji i j, h0.2, Nat.cast_zero]
          exact CFSG.StandardType.reflection_mul_reflection_pow_two (hβc i) (hβc j) hfy hgx
    have hcard : Nat.card (CFSG.StandardType.ggCoxeterMatrixD P.D).Group ≤ Nat.card P.group := by
      rw [pws_card_coxeterD P.D hD4]
      rw [hk2] at hO
      rw [if_neg (by decide : ¬ ((2:ℕ) = 0)),
        if_neg (by decide : ¬ ((2:ℕ) = 1)), if_pos rfl] at hO
      have hlt := verifyO_sound (P := P) hwf hO
      have hpos : 0 < 2 ^ (P.D - 1) * natFact P.D := by rw [natFact_eq]; positivity
      omega
    haveI : Finite (CFSG.StandardType.ggCoxeterMatrixD P.D).Group := pws_finite_coxeterD P.D hD4
    exact pws_linWeyl_of_simple_system (CFSG.StandardType.ggCoxeterMatrixD P.D)
      (pws_ggIsWeylMatrix_D P.D hD4) P.group σ hσR cc β hσ hβc hrel hgen hcard
  ·
    have hD7 : P.D = 7 := by omega
    simp only [hD7, hk3, if_neg (by decide : ¬ ((3:ℕ) = 0)),
      if_neg (by decide : ¬ ((3:ℕ) = 1)),
      if_neg (by decide : ¬ ((3:ℕ) = 2))] at hp8
    set σ' : Fin 7 → P.V ≃ₗ[ZMod P.p] P.V := fun i => σ (Fin.cast hD7.symm i) with hσ'def
    set cc' : Fin 7 → P.V := fun i => cc (Fin.cast hD7.symm i) with hcc'def
    set β' : Fin 7 → Module.Dual (ZMod P.p) P.V := fun i => β (Fin.cast hD7.symm i) with hβ'def
    have hσ' : ∀ i v, σ' i v = v - β' i v • cc' i := by
      intro i v; rw [hσ'def, hβ'def, hcc'def]; exact hσ (Fin.cast hD7.symm i) v
    have hβc' : ∀ i, β' i (cc' i) = 2 := by
      intro i; rw [hβ'def, hcc'def]; exact hβc (Fin.cast hD7.symm i)
    have hσi' : ∀ i, σ' i = Module.reflection (hβc' i) := by
      intro i
      rw [hσ'def]
    have hbij' : ∀ i j : Fin 7, β' i (cc' j) =
        ((P.dotv (pww2_cb P c (Fin.cast hD7.symm i)).2
          (pww2_cb P c (Fin.cast hD7.symm j)).1 : ℕ) : ZMod P.p) := by
      intro i j
      rw [hβ'def, hcc'def]
      exact hbij (Fin.cast hD7.symm i) (Fin.cast hD7.symm j)
    have hbji' : ∀ i j : Fin 7, β' j (cc' i) =
        ((P.dotv (pww2_cb P c (Fin.cast hD7.symm j)).2
          (pww2_cb P c (Fin.cast hD7.symm i)).1 : ℕ) : ZMod P.p) := by
      intro i j
      rw [hβ'def, hcc'def]
      exact hbij (Fin.cast hD7.symm j) (Fin.cast hD7.symm i)
    have hσR' : ∀ i, σ' i ∈ P.group := by
      intro i; rw [hσ'def]; exact hσR (Fin.cast hD7.symm i)
    have hsurj_cast : Function.Surjective (Fin.cast hD7.symm : Fin 7 → Fin P.D) := by
      intro x
      exact ⟨Fin.cast hD7 x, by ext; rfl⟩
    have hrange_eq : Set.range σ' = Set.range σ := by
      rw [hσ'def]
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨Fin.cast hD7.symm i, rfl⟩
      · rintro ⟨j, rfl⟩
        obtain ⟨i, hi⟩ := hsurj_cast j
        exact ⟨i, by change σ (Fin.cast hD7.symm i) = σ j; rw [hi]⟩
    have hgen' : P.group ≤ Subgroup.closure (Set.range σ') := by
      rw [hrange_eq]; exact hgen
    have hrel' : ∀ i j : Fin 7, i ≠ j → (σ' i * σ' j) ^ (CoxeterMatrix.E₇).M i j = 1 := by
      intro i j hij
      have hp := hp8 i.val (List.mem_range.mpr i.isLt) j.val (List.mem_range.mpr j.isLt)
      rcases hp with hp | hp
      · exact absurd (Fin.ext hp) hij
      · by_cases hadj : (i.val = 0 ∧ j.val = 2) ∨ (i.val = 2 ∧ j.val = 0) ∨
            (i.val = 1 ∧ j.val = 3) ∨ (i.val = 3 ∧ j.val = 1) ∨
            (i.val = 2 ∧ j.val = 3) ∨ (i.val = 3 ∧ j.val = 2) ∨
            (i.val = 3 ∧ j.val = 4) ∨ (i.val = 4 ∧ j.val = 3) ∨
            (i.val = 4 ∧ j.val = 5) ∨ (i.val = 5 ∧ j.val = 4) ∨
            (i.val = 5 ∧ j.val = 6) ∨ (i.val = 6 ∧ j.val = 5)
        · have h1 : (P.dotv (pww2_cb P c (Fin.cast hD7.symm i)).2
                (pww2_cb P c (Fin.cast hD7.symm j)).1 *
              P.dotv (pww2_cb P c (Fin.cast hD7.symm j)).2
                (pww2_cb P c (Fin.cast hD7.symm i)).1) % P.p = 1 := by
            have hh := hp
            rw [if_pos hadj] at hh
            simpa only [beq_iff_eq, pww2_cb, pww2_S, Fin.cast] using hh
          rw [pww2_e7M_eq i j hij, if_pos hadj]
          rw [hσi' i, hσi' j]
          have hprod : β' i (cc' j) * β' j (cc' i) = 1 := by
            rw [hbij' i j, hbji' i j, ← Nat.cast_mul,
              ← ZMod.natCast_mod (P.dotv (pww2_cb P c (Fin.cast hD7.symm i)).2
                (pww2_cb P c (Fin.cast hD7.symm j)).1 *
                P.dotv (pww2_cb P c (Fin.cast hD7.symm j)).2
                  (pww2_cb P c (Fin.cast hD7.symm i)).1) P.p, h1, Nat.cast_one]
          exact CFSG.StandardType.reflection_mul_reflection_pow_three (hβc' i) (hβc' j) hprod
        · have h0 : P.dotv (pww2_cb P c (Fin.cast hD7.symm i)).2
                (pww2_cb P c (Fin.cast hD7.symm j)).1 = 0 ∧
              P.dotv (pww2_cb P c (Fin.cast hD7.symm j)).2
                (pww2_cb P c (Fin.cast hD7.symm i)).1 = 0 := by
            have hh := hp
            rw [if_neg hadj] at hh
            simpa only [Bool.and_eq_true, beq_iff_eq, pww2_cb, pww2_S, Fin.cast] using hh
          rw [pww2_e7M_eq i j hij, if_neg hadj]
          rw [hσi' i, hσi' j]
          have hfy : β' i (cc' j) = 0 := by rw [hbij' i j, h0.1, Nat.cast_zero]
          have hgx : β' j (cc' i) = 0 := by rw [hbji' i j, h0.2, Nat.cast_zero]
          exact CFSG.StandardType.reflection_mul_reflection_pow_two (hβc' i) (hβc' j) hfy hgx
    have hcard : Nat.card (CoxeterMatrix.E₇).Group ≤ Nat.card P.group := by
      rw [pws_card_coxeterE7]
      rw [hk3] at hO
      rw [if_neg (by decide : ¬ ((3:ℕ) = 0)),
        if_neg (by decide : ¬ ((3:ℕ) = 1)),
        if_neg (by decide : ¬ ((3:ℕ) = 2))] at hO
      have hlt := verifyO_sound (P := P) hwf hO
      omega
    haveI : Finite (CoxeterMatrix.E₇).Group := pws_finite_coxeterE7
    exact pws_linWeyl_of_simple_system (CoxeterMatrix.E₇)
      pws_ggIsWeylMatrix_E7 P.group σ' hσR' cc' β' hσ' hβc' hrel' hgen' hcard

end CFSG.TwoNodeSmall
