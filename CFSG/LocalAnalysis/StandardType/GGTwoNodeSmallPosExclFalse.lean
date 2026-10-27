module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallPosExclCoord
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeIndepDefs
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallPosModelled

public section

namespace CFSG.TwoNodeSmall

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

lemma pxe_model_false (p : ℕ) [Fact p.Prime] (hp : p = 5 ∨ p = 7)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V]
    (h : Fin (p - 1) → V) (α : Fin (p - 1) → Module.Dual (ZMod p) V) (x : V) (ha : V)
    (αa : Module.Dual (ZMod p) V) (hF : CFSG.StandardType.GGIndepAFrame p p h α x)
    (s : ℕ) (hs : s ≤ 2)
    (o : ℕ × ℕ × ℕ) (ho : o ∈ posOpts p p)
    (hH : ∀ j : Fin (p - 1), s ≤ (j : ℕ) → (j : ℕ) < s + (p - 3) →
      α j ha = (((if (j : ℕ) - s = o.1 then o.2.1 else 0 : ℕ)) : ZMod p))
    (hA : ∀ j : Fin (p - 1), s ≤ (j : ℕ) → (j : ℕ) < s + (p - 3) →
      αa (h j) = (((if (j : ℕ) - s = o.1 then o.2.2 else 0 : ℕ)) : ZMod p))
    (hdim : Module.finrank (ZMod p) V = p - 1)
    (cc : Fin (p - 1) → ZMod p) (hcc : ∑ i, cc i • h i = ha)
    (aa : Fin (p - 1) → ZMod p) (haa : ∑ i, aa i • h i = x)
    (m0 : ZMod p) (hm0eq : aa = fun i : Fin (p - 1) => m0 * (((i : ℕ) + 1 : ℕ) : ZMod p))
    (hm0 : m0 ≠ 0) (hcx : m0⁻¹ ≠ 0) :
    ModelledIn (exclCell false p p ++ exclCell true p p) s p h α x ha αa := by
    have hp5 : 5 ≤ p := by rcases hp with h | h <;> omega
    let inJ : ℕ → Bool := fun k => s ≤ k && k < s + (p - 3)
    let outs : List ℕ := (List.range (p - 1)).filter (fun k => !(inJ k))
    let g : ℕ → ℕ := fun k => if hk : k < p - 1 then ((αa (h ⟨k, hk⟩)).val) else 0
    let fr : Vec := outs.map g
    let vv : ℕ → ℕ := fun k =>
      if inJ k then (if k - s = o.1 then o.2.2 else 0)
      else if outs.head? = some k then fr.getD 0 0 else fr.getD 1 0
    let cvec : Vec := List.ofFn (fun i : Fin (p - 1) => (cc i).val)
    let x' : Vec := (List.range (p - 1)).map (fun k => k + 1)
    let gens : List Refl :=
      (List.range (p - 1)).map (fun k => (⟨cartanRowP p p k, unitP (p - 1) k⟩ : Refl)) ++
        [⟨(List.range (p - 1)).map vv, cvec⟩]
    have hout_len : outs.length = 2 := by
      simpa only [outs, inJ] using pxe_outs_len p s hp hs
    have hfr : fr ∈ allVecsP p 2 := by
      rw [pxe_mem_allVecsP p 2]
      refine ⟨by simp [fr, hout_len], ?_⟩
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨k, _, rfl⟩ := hx
      by_cases hk : k < p - 1
      · simp only [g, dif_pos hk]; exact ZMod.val_lt _
      · simp only [g, dif_neg hk]; omega
    have hc : cvec ∈ allVecsP p (p - 1) := by
      rw [pxe_mem_allVecsP p (p - 1)]
      refine ⟨by simp [cvec, List.length_ofFn], ?_⟩
      intro x hx
      rw [List.mem_ofFn] at hx
      obtain ⟨i, rfl⟩ := hx
      exact ZMod.val_lt _
    have hvv : ∀ k : Fin (p - 1), ((vv k.val : ℕ) : ZMod p) = αa (h k) := by
      intro k
      cases hb : inJ k.val
      · have hout : ¬ (s ≤ k.val ∧ k.val < s + (p - 3)) := by
          intro hh
          have htrue : inJ k.val = true := by
            simp only [inJ, Bool.and_eq_true, decide_eq_true_eq]; exact ⟨hh.1, hh.2⟩
          rw [hb] at htrue; exact Bool.noConfusion htrue
        have hv : vv k.val =
            (if outs.head? = some k.val then fr.getD 0 0 else fr.getD 1 0) := by
          simp [vv, hb]
        rw [hv, pxe_vv_out p s hp hs g k.val k.isLt hout]
        simp only [g, dif_pos k.isLt, ZMod.natCast_zmod_val]
      · have hik : s ≤ k.val ∧ k.val < s + (p - 3) := by
          simpa only [inJ, Bool.and_eq_true, decide_eq_true_eq] using hb
        have hv : vv k.val = (if k.val - s = o.1 then o.2.2 else 0) := by
          simp [vv, hb]
        rw [hv, ← hA k hik.1 hik.2]
    have hdot_alpha : ∀ j : Fin (p - 1),
        ((dotP p (cartanRowP p p j.val) cvec : ℕ) : ZMod p) = α j ha := by
      intro j
      calc ((dotP p (cartanRowP p p j.val) cvec : ℕ) : ZMod p)
          = ∑ i : Fin (p - 1), ((cartanRowP p p j.val).getD i.val 0 : ZMod p) *
              ((cvec.getD i.val 0 : ℕ) : ZMod p) :=
            pxe_dotP_cast p (p - 1) (cartanRowP p p j.val) cvec
              (by simp [cartanRowP]) (by simp [cvec, List.length_ofFn])
        _ = (pxe_A p (p - 1)).mulVec cc j := by
            simp only [pxe_A, Matrix.mulVec, dotProduct]
            apply Finset.sum_congr rfl
            intro i _
            rw [pxe_cartanRowP_eq p hp j i, pxe_cvec_getD p cc i, ZMod.natCast_zmod_val]
        _ = α j (∑ i, cc i • h i) :=
            (pxe_alpha_sum p h α (fun a b => hF.pair a b) cc j).symm
        _ = α j ha := by rw [hcc]
    have hf : (List.range (p - 1)).all (fun j =>
        !(inJ j) || dotP p (cartanRowP p p j) cvec ==
          (if j - s = o.1 then o.2.1 else 0)) = true := by
      rw [List.all_eq_true]
      intro j hj
      rw [List.mem_range] at hj
      cases hb : inJ j
      · simp only [hb, Bool.not_false, Bool.true_or]
      · have hik : s ≤ j ∧ j < s + (p - 3) := by
          simpa only [inJ, Bool.and_eq_true, decide_eq_true_eq] using hb
        have hpin_lt : (if j - s = o.1 then o.2.1 else 0) < p := by
          by_cases hsub : j - s = o.1
          · simp only [if_pos hsub]; exact pxe_opt_lt1 p p hp rfl o ho
          · simp only [if_neg hsub]; omega
        have heq : dotP p (cartanRowP p p j) cvec =
            (if j - s = o.1 then o.2.1 else 0) :=
          pxe_nat_eq_of_cast_eq p _ _ hpin_lt (by
            conv_lhs => rw [← ZMod.natCast_mod]
            exact (hdot_alpha ⟨j, hj⟩).trans (hH ⟨j, hj⟩ hik.1 hik.2))
        simp only [hb, Bool.not_true, Bool.false_or, beq_iff_eq]
        exact heq
    have hget_frame : ∀ i : Fin (p - 1),
        (⟨p, p - 1, p - 1, gens, x', posBound p p⟩ : Pt).gens.getD i ⟨[], []⟩ =
          (⟨cartanRowP p p i, unitP (p - 1) i⟩ : Refl) := by
      intro i
      simp only [gens]
      exact pxe_getD_map_range_lit
        (fun k => (⟨cartanRowP p p k, unitP (p - 1) k⟩ : Refl)) ⟨[], []⟩ _ i
    have hget_last :
        (⟨p, p - 1, p - 1, gens, x', posBound p p⟩ : Pt).gens.getD (p - 1) ⟨[], []⟩ =
          (⟨(List.range (p - 1)).map vv, cvec⟩ : Refl) := by
      simp only [gens]
      exact pxe_getD_append_last
        (l := (List.range (p - 1)).map
          (fun k => (⟨cartanRowP p p k, unitP (p - 1) k⟩ : Refl))) (z := _) (d := ⟨[], []⟩)
        (n := p - 1) (by simp)
    let ψ : (Fin (p - 1) → ZMod p) →ₗ[ZMod p] V :=
      { toFun := fun c => ∑ k : Fin (p - 1), c k • h k
        map_add' := by
          intro c d
          simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
        map_smul' := by
          intro r c
          simp only [Pi.smul_apply, Finset.smul_sum, smul_smul, smul_eq_mul, RingHom.id_apply] }
    have hψapp : ∀ c : Fin (p - 1) → ZMod p, ψ c = ∑ k, c k • h k := fun c => rfl
    have hψinj : Function.Injective ψ := by
      rw [← LinearMap.ker_eq_bot]
      ext c
      rw [LinearMap.mem_ker, Submodule.mem_bot]
      constructor
      · intro hc0
        funext i
        exact Fintype.linearIndependent_iff.mp hF.indep c (by simpa only [hψapp] using hc0) i
      · intro hc0; rw [hc0]; simp [hψapp]
    have hrank : Module.finrank (ZMod p) (Fin (p - 1) → ZMod p) =
        Module.finrank (ZMod p) V := by
      rw [Module.finrank_pi, Fintype.card_fin]; omega
    let Ψ : (Fin (p - 1) → ZMod p) ≃ₗ[ZMod p] V :=
      LinearEquiv.ofInjectiveOfFinrankEq ψ hψinj hrank
    let e : V ≃ₗ[ZMod p] (Fin (p - 1) → ZMod p) := Ψ.symm
    have he_apply : ∀ c : Fin (p - 1) → ZMod p, e (ψ c) = c := by
      intro c
      have hcoe : Ψ.toLinearMap = ψ :=
        LinearEquiv.coe_ofInjectiveOfFinrankEq ψ hψinj hrank
      have hΨc : Ψ c = ψ c := LinearMap.congr_fun hcoe c
      change Ψ.symm (ψ c) = c
      rw [← hΨc]
      exact LinearEquiv.symm_apply_apply Ψ c
    have he_h : ∀ i : Fin (p - 1),
        e (h i) = (Pi.single i (1 : ZMod p) : Fin (p - 1) → ZMod p) := by
      intro i
      have hψh : ψ (Pi.single i (1 : ZMod p)) = h i := by
        rw [hψapp, Finset.sum_eq_single i]
        · simp
        · intro k _ hk; rw [Pi.single_eq_of_ne hk, zero_smul]
        · intro hi; exact absurd (Finset.mem_univ i) hi
      calc e (h i) = e (ψ (Pi.single i 1)) := by rw [hψh]
        _ = Pi.single i 1 := he_apply _
    have hdecomp : ∀ w : V, w = ψ (e w) := by
      intro w
      exact (e.injective (he_apply (e w))).symm
    have hex : e x = aa := by
      rw [← haa, map_sum]
      simp only [map_smul, he_h]
      exact pxe_sum_single aa
    have hx_models : e (m0⁻¹ • x) =
        (⟨p, p - 1, p - 1, gens, x', posBound p p⟩ : Pt).vec
          (⟨p, p - 1, p - 1, gens, x', posBound p p⟩ : Pt).x := by
      rw [map_smul, hex]
      funext i
      simp only [Pi.smul_apply, smul_eq_mul, Pt.vec, x']
      rw [pxe_getD_map_range' (fun k => k + 1) 0 i, hm0eq]
      rw [← mul_assoc, inv_mul_cancel₀ hm0, one_mul]
    have hh_models : ∀ i : Fin (p - 1),
        e (h i) = (⟨p, p - 1, p - 1, gens, x', posBound p p⟩ : Pt).vec
          ((⟨p, p - 1, p - 1, gens, x', posBound p p⟩ : Pt).gens.getD i ⟨[], []⟩).h := by
      intro i
      rw [he_h i, hget_frame i]
      exact (pxe_vec_unitP (⟨p, p - 1, p - 1, gens, x', posBound p p⟩ : Pt) i).symm
    have hα_models : ∀ (i : Fin (p - 1)) (w : V),
        α i w = (⟨p, p - 1, p - 1, gens, x', posBound p p⟩ : Pt).dot
          ((⟨p, p - 1, p - 1, gens, x', posBound p p⟩ : Pt).vec
            ((⟨p, p - 1, p - 1, gens, x', posBound p p⟩ : Pt).gens.getD i ⟨[], []⟩).f) (e w) := by
      intro i w
      rw [hget_frame i]
      calc α i w = α i (ψ (e w)) := congrArg (α i) (hdecomp w)
        _ = (pxe_A p (p - 1)).mulVec (e w) i :=
            pxe_alpha_sum p h α (fun a b => hF.pair a b) (e w) i
        _ = ∑ j : Fin (p - 1), ((cartanRowP p p i).getD j.val 0 : ZMod p) * (e w) j := by
            simp only [pxe_A, Matrix.mulVec, dotProduct]
            apply Finset.sum_congr rfl
            intro j _
            rw [pxe_cartanRowP_eq p hp i j]
        _ = (⟨p, p - 1, p - 1, gens, x', posBound p p⟩ : Pt).dot
              ((⟨p, p - 1, p - 1, gens, x', posBound p p⟩ : Pt).vec
                (cartanRowP p p i)) (e w) := by
            simp only [Pt.dot, Pt.vec]
    have heha : e ha = cc := by
      rw [← hcc, map_sum]
      simp only [map_smul, he_h]
      exact pxe_sum_single cc
    have hha_models : e ha =
        (⟨p, p - 1, p - 1, gens, x', posBound p p⟩ : Pt).vec
          ((⟨p, p - 1, p - 1, gens, x', posBound p p⟩ : Pt).gens.getD (p - 1) ⟨[], []⟩).h := by
      rw [hget_last, heha]
      funext i
      simp only [Pt.vec]
      rw [pxe_cvec_getD p cc i, ZMod.natCast_zmod_val]
    have hαa_models : ∀ w : V,
        αa w = (⟨p, p - 1, p - 1, gens, x', posBound p p⟩ : Pt).dot
          ((⟨p, p - 1, p - 1, gens, x', posBound p p⟩ : Pt).vec
            ((⟨p, p - 1, p - 1, gens, x', posBound p p⟩ : Pt).gens.getD (p - 1) ⟨[], []⟩).f)
          (e w) := by
      intro w
      rw [hget_last]
      calc αa w = αa (ψ (e w)) := congrArg αa (hdecomp w)
        _ = ∑ k : Fin (p - 1), (e w) k * αa (h k) := by
            rw [hψapp, map_sum]
            simp only [map_smul, smul_eq_mul]
        _ = ∑ k : Fin (p - 1), (e w) k * ((vv k.val : ℕ) : ZMod p) := by
            apply Finset.sum_congr rfl
            intro k _
            rw [← hvv k]
        _ = (⟨p, p - 1, p - 1, gens, x', posBound p p⟩ : Pt).dot
              ((⟨p, p - 1, p - 1, gens, x', posBound p p⟩ : Pt).vec
                ((List.range (p - 1)).map vv)) (e w) := by
            simp only [Pt.dot, Pt.vec]
            apply Finset.sum_congr rfl
            intro k _
            rw [pxe_getD_map_range' vv 0 k]
            ring
    refine ⟨p - 1, p - 1, gens, x', posBound p p, ?_, m0⁻¹, hcx, e, ?_⟩
    · exact List.mem_append_left _ (by
        simp only [exclCell, List.mem_flatMap, List.mem_map, List.mem_filter]
        exact ⟨s, by simp only [List.mem_cons, List.not_mem_nil, or_false]; omega,
          o, ho, cvec, ⟨hc, hf⟩, fr, hfr, rfl⟩)
    · unfold Pt.Models
      exact ⟨rfl, by simp [gens], hx_models,
        fun i => ⟨hh_models i, hα_models i⟩, hha_models, hαa_models⟩

end CFSG.TwoNodeSmall
