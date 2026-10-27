module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallPosExclCoord
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeIndepDefs
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallPosModelled

public section

namespace CFSG.TwoNodeSmall

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

lemma pxe_model_true (p : ℕ) [Fact p.Prime] (hp : p = 5 ∨ p = 7)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V]
    (h : Fin (p - 1) → V) (α : Fin (p - 1) → Module.Dual (ZMod p) V) (x : V) (ha : V)
    (αa : Module.Dual (ZMod p) V) (hF : CFSG.StandardType.GGIndepAFrame p p h α x)
    (hx : αa x ≠ 0) (s : ℕ) (hs : s ≤ 2)
    (o : ℕ × ℕ × ℕ) (ho : o ∈ posOpts p p)
    (hH : ∀ j : Fin (p - 1), s ≤ (j : ℕ) → (j : ℕ) < s + (p - 3) →
      α j ha = (((if (j : ℕ) - s = o.1 then o.2.1 else 0 : ℕ)) : ZMod p))
    (hA : ∀ j : Fin (p - 1), s ≤ (j : ℕ) → (j : ℕ) < s + (p - 3) →
      αa (h j) = (((if (j : ℕ) - s = o.1 then o.2.2 else 0 : ℕ)) : ZMod p))
    (hdim : Module.finrank (ZMod p) V = p)
    (cc : Fin (p - 1) → ZMod p) (hcc : ∑ i, cc i • h i = ha)
    (aa : Fin (p - 1) → ZMod p) (haa : ∑ i, aa i • h i = x)
    (m0 : ZMod p) (hm0eq : aa = fun i : Fin (p - 1) => m0 * (((i : ℕ) + 1 : ℕ) : ZMod p))
    (hm0 : m0 ≠ 0) (hcx : m0⁻¹ ≠ 0)
    (φ : V →ₗ[ZMod p] (Fin (p - 1) → ZMod p)) (hφ : ∀ v i, φ v i = α i v)
    (hVd : Module.finrank (ZMod p) V = Module.finrank (ZMod p) (LinearMap.range φ) + 1) :
    ModelledIn (exclCell false p p ++ exclCell true p p) s p h α x ha αa := by
    have hp5 : 5 ≤ p := by rcases hp with h | h <;> omega
    let embed : Fin (p - 1) → Fin p := fun k => ⟨k.val, by omega⟩
    let last : Fin p := ⟨p - 1, by omega⟩
    let δ0 : Fin (p - 1) → ZMod p := Pi.single (⟨0, by omega⟩ : Fin (p - 1)) 1
    let inJ : ℕ → Bool := fun k => s ≤ k && k < s + (p - 3)
    let outs : List ℕ := (List.range (p - 1)).filter (fun k => !(inJ k))
    let g : ℕ → ℕ := fun k => if hk : k < p - 1 then ((αa (h ⟨k, hk⟩)).val) else 0
    let fr : Vec := outs.map g
    let vv : ℕ → ℕ := fun k =>
      if inJ k then (if k - s = o.1 then o.2.2 else 0)
      else if outs.head? = some k then fr.getD 0 0 else fr.getD 1 0
    let cvec : Vec := List.ofFn (fun i : Fin (p - 1) => (cc i).val)
    let x' : Vec := (List.range (p - 1)).map (fun k => k + 1) ++ [0]
    let gens : List Refl :=
      (List.range (p - 1)).map
          (fun k => (⟨cartanRowP p p k ++ [if k = 0 then 1 else 0], unitP p k⟩ : Refl)) ++
        [⟨(List.range (p - 1)).map vv ++ [0], cvec ++ [0]⟩]
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
    have hφx : φ x = 0 := by funext i; exact (hφ x i).trans (hF.x_ker i)
    have hrf : Module.finrank (ZMod p) (LinearMap.range φ) = p - 1 := by omega
    have hrange_top : LinearMap.range φ = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [hrf, Module.finrank_pi, Fintype.card_fin]
    have hδmem : δ0 ∈ LinearMap.range φ := by rw [hrange_top]; trivial
    obtain ⟨e0, he0⟩ := LinearMap.mem_range.mp hδmem
    let e2 : V := e0 - (αa e0 / αa x) • x
    have he2φ : φ e2 = δ0 := by
      simp only [e2, map_sub, map_smul]
      rw [he0, hφx, smul_zero, sub_zero]
    have he2a : αa e2 = 0 := by
      simp only [e2, map_sub, map_smul, smul_eq_mul]
      rw [div_mul_cancel₀ _ hx, sub_self]
    have he2i : ∀ i : Fin (p - 1), α i e2 = δ0 i :=
      fun i => (hφ e2 i).symm.trans (congrFun he2φ i)
    let ψ : (Fin p → ZMod p) →ₗ[ZMod p] V :=
      { toFun := fun c => c last • e2 + ∑ k : Fin (p - 1), c (embed k) • h k
        map_add' := by
          intro c d
          simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
          abel
        map_smul' := by
          intro r c
          simp only [Pi.smul_apply, smul_add, Finset.smul_sum, smul_smul, smul_eq_mul]
          rfl }
    have hψapp : ∀ c : Fin p → ZMod p,
        ψ c = c last • e2 + ∑ k, c (embed k) • h k := fun c => rfl
    have hcomp : ∀ c : Fin p → ZMod p,
        φ (ψ c) = c last • δ0 + (pxe_A p (p - 1)).mulVec (fun k => c (embed k)) := by
      intro c
      rw [hψapp, map_add, map_smul, he2φ]
      congr 1
      funext j
      exact (hφ (∑ k : Fin (p - 1), c (embed k) • h k) j).trans
        (pxe_alpha_sum p h α (fun a b => hF.pair a b) (fun k => c (embed k)) j)
    have hψinj : Function.Injective ψ := by
      intro c d hcd
      have hcd0 : ψ (c - d) = 0 := by rw [map_sub, hcd, sub_self]
      let cr : Fin (p - 1) → ZMod p := fun k => (c - d) (embed k)
      have hzero : φ (ψ (c - d)) = 0 := by rw [hcd0, map_zero]
      rw [hcomp (c - d)] at hzero
      have hlast : (c - d) last = 0 := by
        by_contra hne
        have hmulcr : (pxe_A p (p - 1)).mulVec cr = (-(c - d) last) • δ0 := by
          have h : (pxe_A p (p - 1)).mulVec cr = -((c - d) last • δ0) :=
            (eq_neg_iff_add_eq_zero).mpr (by rw [add_comm]; exact hzero)
          rwa [← neg_smul] at h
        refine pxe_noPreimage p (p - 1) hp rfl ((-(c - d) last)⁻¹ • cr) ?_
        have hsv : (pxe_A p (p - 1)).mulVec ((-(c - d) last)⁻¹ • cr)
            = (-(c - d) last)⁻¹ • (pxe_A p (p - 1)).mulVec cr := by
          ext j
          simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
        rw [hsv, hmulcr, smul_smul]
        rw [inv_mul_cancel₀ (neg_ne_zero.mpr hne), one_smul]
      have hmul : (pxe_A p (p - 1)).mulVec cr = 0 := by
        have h := hzero
        rw [hlast, zero_smul, zero_add] at h
        exact h
      obtain ⟨mz, hmz⟩ := pxe_ker_cartan p (p - 1) hp rfl cr hmul
      have hx_eq : x = m0 • (∑ k : Fin (p - 1), (((k : ℕ) + 1 : ℕ) : ZMod p) • h k) := by
        rw [← haa, Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [hm0eq, smul_smul]
      have hcrzero : cr = 0 := by
        have hψ0 : (∑ k : Fin (p - 1), cr k • h k) = 0 := by
          have h := hcd0
          rw [hψapp, hlast, zero_smul, zero_add] at h
          exact h
        have hx_sum : (∑ k : Fin (p - 1), (((k : ℕ) + 1 : ℕ) : ZMod p) • h k) = m0⁻¹ • x := by
          rw [hx_eq, smul_smul, inv_mul_cancel₀ hm0, one_smul]
        have hsum : (∑ k : Fin (p - 1), cr k • h k) =
            mz • (∑ k : Fin (p - 1), (((k : ℕ) + 1 : ℕ) : ZMod p) • h k) := by
          rw [hmz, Finset.smul_sum]
          apply Finset.sum_congr rfl
          intro k _
          rw [smul_smul]
        have h3 : (mz * m0⁻¹) • x = 0 := by
          rw [hsum, hx_sum, smul_smul] at hψ0
          exact hψ0
        have hmz0 : mz = 0 := by
          have h2 : mz * m0⁻¹ = 0 := (smul_eq_zero.mp h3).resolve_right hF.x_ne
          exact (mul_eq_zero.mp h2).resolve_right (inv_ne_zero hm0)
        rw [hmz, hmz0]
        funext k; simp
      have hdiff : c - d = 0 := by
        funext j
        by_cases hj : j = last
        · rw [hj]; simpa using hlast
        · have hjval : j.val < p - 1 := by
            by_contra hge
            exact hj (Fin.ext (by simp only [last, Fin.val_mk]; omega))
          have hh := congrFun hcrzero ⟨j.val, hjval⟩
          simpa [cr, embed] using hh
      exact sub_eq_zero.mp hdiff
    have hrank : Module.finrank (ZMod p) (Fin p → ZMod p) = Module.finrank (ZMod p) V := by
      rw [Module.finrank_pi, Fintype.card_fin]; omega
    let Ψ : (Fin p → ZMod p) ≃ₗ[ZMod p] V :=
      LinearEquiv.ofInjectiveOfFinrankEq ψ hψinj hrank
    let e : V ≃ₗ[ZMod p] (Fin p → ZMod p) := Ψ.symm
    have he_apply : ∀ c : Fin p → ZMod p, e (ψ c) = c := by
      intro c
      have hcoe : Ψ.toLinearMap = ψ :=
        LinearEquiv.coe_ofInjectiveOfFinrankEq ψ hψinj hrank
      have hΨc : Ψ c = ψ c := LinearMap.congr_fun hcoe c
      change Ψ.symm (ψ c) = c
      rw [← hΨc]
      exact LinearEquiv.symm_apply_apply Ψ c
    have he_h : ∀ i : Fin (p - 1), e (h i) = Pi.single (embed i) (1 : ZMod p) := by
      intro i
      have hlast0 : (Pi.single (embed i) (1 : ZMod p) : Fin p → ZMod p) last = 0 := by
        rw [Pi.single_eq_of_ne]
        intro hh
        have hv := congrArg Fin.val hh
        simp only [embed, last, Fin.val_mk] at hv
        omega
      have hψh : ψ (Pi.single (embed i) (1 : ZMod p)) = h i := by
        rw [hψapp, hlast0, zero_smul, zero_add, Finset.sum_eq_single i]
        · simp
        · intro k _ hk
          rw [Pi.single_eq_of_ne, zero_smul]
          intro hh
          exact hk (Fin.ext (by simpa [embed] using congrArg Fin.val hh))
        · intro hi; exact absurd (Finset.mem_univ i) hi
      calc e (h i) = e (ψ (Pi.single (embed i) 1)) := by rw [hψh]
        _ = Pi.single (embed i) 1 := he_apply _
    have hdecomp : ∀ w : V, w = ψ (e w) := by
      intro w
      exact (e.injective (he_apply (e w))).symm
    have hexsum : e x = (fun j : Fin p => if h : j.val < p - 1 then aa ⟨j.val, h⟩ else 0) := by
      rw [← haa, map_sum]
      trans (∑ i : Fin (p - 1), aa i • (Pi.single (embed i) (1 : ZMod p) : Fin p → ZMod p))
      · apply Finset.sum_congr rfl; intro i _; rw [map_smul, he_h i]
      · exact pxe_pi_single_embed p (by omega) aa
    have hx_models : e (m0⁻¹ • x) =
        (⟨p, p, p - 1, gens, x', posBound p p⟩ : Pt).vec
          (⟨p, p, p - 1, gens, x', posBound p p⟩ : Pt).x := by
      rw [map_smul, hexsum]
      funext j
      simp only [Pi.smul_apply, smul_eq_mul, Pt.vec, x']
      by_cases hj : j.val < p - 1
      · rw [dif_pos hj, List.getD_append _ _ _ _ (by simpa using hj),
          pxe_getD_map_range' (fun k => k + 1) 0 ⟨j.val, hj⟩, hm0eq]
        rw [← mul_assoc, inv_mul_cancel₀ hm0, one_mul]
      · rw [dif_neg hj, List.getD_append_right _ _ _ _ (by simp only [List.length_map, List.length_range]; omega)]
        simp
    have hδ0 : ∀ i : Fin (p - 1), δ0 i = ((if (i : ℕ) = 0 then 1 else 0 : ℕ) : ZMod p) := by
      intro i
      by_cases h : (i : ℕ) = 0
      · have hi : i = (⟨0, by omega⟩ : Fin (p - 1)) := Fin.ext h
        rw [hi]; simp [δ0]
      · have hi : i ≠ (⟨0, by omega⟩ : Fin (p - 1)) :=
          fun hh => h (by simpa using congrArg Fin.val hh)
        rw [if_neg h]
        simpa using Pi.single_eq_of_ne hi 1
    have hget_frame : ∀ i : Fin (p - 1),
        (⟨p, p, p - 1, gens, x', posBound p p⟩ : Pt).gens.getD i ⟨[], []⟩ =
          (⟨cartanRowP p p i ++ [if (i : ℕ) = 0 then 1 else 0], unitP p i⟩ : Refl) := by
      intro i
      simp only [gens]
      exact pxe_getD_map_range_lit
        (fun k => (⟨cartanRowP p p k ++ [if k = 0 then 1 else 0], unitP p k⟩ : Refl)) ⟨[], []⟩ _ i
    have hget_last :
        (⟨p, p, p - 1, gens, x', posBound p p⟩ : Pt).gens.getD (p - 1) ⟨[], []⟩ =
          (⟨(List.range (p - 1)).map vv ++ [0], cvec ++ [0]⟩ : Refl) := by
      simp only [gens]
      exact pxe_getD_append_last
        (l := (List.range (p - 1)).map
          (fun k => (⟨cartanRowP p p k ++ [if k = 0 then 1 else 0], unitP p k⟩ : Refl)))
        (z := _) (d := ⟨[], []⟩) (n := p - 1) (by simp)
    have hh_models : ∀ i : Fin (p - 1),
        e (h i) = (⟨p, p, p - 1, gens, x', posBound p p⟩ : Pt).vec
          ((⟨p, p, p - 1, gens, x', posBound p p⟩ : Pt).gens.getD i ⟨[], []⟩).h := by
      intro i
      rw [he_h i, hget_frame i]
      exact (pxe_vec_unitP (⟨p, p, p - 1, gens, x', posBound p p⟩ : Pt) (embed i)).symm
    have hdot_frame : ∀ (i : Fin (p - 1)) (w : V),
        (⟨p, p, p - 1, gens, x', posBound p p⟩ : Pt).dot
            ((⟨p, p, p - 1, gens, x', posBound p p⟩ : Pt).vec
              (cartanRowP p p i ++ [if (i : ℕ) = 0 then 1 else 0])) (e w) =
          (∑ k : Fin (p - 1), ((cartanRowP p p i).getD k.val 0 : ZMod p) * (e w) (embed k))
            + ((if (i : ℕ) = 0 then 1 else 0 : ℕ) : ZMod p) * (e w) last := by
      intro i w
      rw [Pt.dot]
      rw [pxe_sum_fin_last p (by omega) (fun j : Fin p =>
        ((⟨p, p, p - 1, gens, x', posBound p p⟩ : Pt).vec
          (cartanRowP p p i ++ [if (i : ℕ) = 0 then 1 else 0])) j * (e w) j)]
      congr 1
      · apply Finset.sum_congr rfl
        intro k _
        simp only [Pt.vec]
        rw [List.getD_append _ _ _ _ (by simp [cartanRowP])]
      · simp only [Pt.vec]
        rw [List.getD_append_right _ _ _ _ (by simp [cartanRowP])]
        simp [cartanRowP, last]
    have hα_models : ∀ (i : Fin (p - 1)) (w : V),
        α i w = (⟨p, p, p - 1, gens, x', posBound p p⟩ : Pt).dot
          ((⟨p, p, p - 1, gens, x', posBound p p⟩ : Pt).vec
            ((⟨p, p, p - 1, gens, x', posBound p p⟩ : Pt).gens.getD i ⟨[], []⟩).f) (e w) := by
      intro i w
      rw [hget_frame i, hdot_frame i w]
      calc α i w = α i (ψ (e w)) := congrArg (α i) (hdecomp w)
        _ = (e w) last * δ0 i + ∑ k : Fin (p - 1), (e w) (embed k) * α i (h k) := by
            rw [hψapp, map_add, map_smul, map_sum]
            simp only [map_smul, Pi.smul_apply, smul_eq_mul]
            rw [he2i i]
        _ = (∑ k : Fin (p - 1), ((cartanRowP p p i).getD k.val 0 : ZMod p) * (e w) (embed k))
              + ((if (i : ℕ) = 0 then 1 else 0 : ℕ) : ZMod p) * (e w) last := by
            rw [hδ0 i]
            rw [add_comm]
            congr 1
            · apply Finset.sum_congr rfl
              intro k _
              rw [hF.pair i k, pxe_cartanRowP_eq p hp i k]
              ring
            · ring
    have heha : e ha = (fun j : Fin p => if h : j.val < p - 1 then cc ⟨j.val, h⟩ else 0) := by
      rw [← hcc, map_sum]
      trans (∑ i : Fin (p - 1), cc i • (Pi.single (embed i) (1 : ZMod p) : Fin p → ZMod p))
      · apply Finset.sum_congr rfl; intro i _; rw [map_smul, he_h i]
      · exact pxe_pi_single_embed p (by omega) cc
    have hha_models : e ha =
        (⟨p, p, p - 1, gens, x', posBound p p⟩ : Pt).vec
          ((⟨p, p, p - 1, gens, x', posBound p p⟩ : Pt).gens.getD (p - 1) ⟨[], []⟩).h := by
      rw [hget_last, heha]
      funext j
      simp only [Pt.vec]
      by_cases hj : j.val < p - 1
      · rw [dif_pos hj, List.getD_append _ _ _ _ (by simpa [cvec, List.length_ofFn] using hj),
          pxe_cvec_getD p cc ⟨j.val, hj⟩, ZMod.natCast_zmod_val]
      · rw [dif_neg hj, List.getD_append_right _ _ _ _ (by simp [cvec, List.length_ofFn]; omega)]
        simp
    have hdot_last : ∀ w : V,
        (⟨p, p, p - 1, gens, x', posBound p p⟩ : Pt).dot
          ((⟨p, p, p - 1, gens, x', posBound p p⟩ : Pt).vec
            ((List.range (p - 1)).map vv ++ [0])) (e w) =
        (∑ k : Fin (p - 1), ((vv k.val : ℕ) : ZMod p) * (e w) (embed k))
          + 0 * (e w) last := by
      intro w
      rw [Pt.dot]
      rw [pxe_sum_fin_last p (by omega) (fun j : Fin p =>
        ((⟨p, p, p - 1, gens, x', posBound p p⟩ : Pt).vec
          ((List.range (p - 1)).map vv ++ [0])) j * (e w) j)]
      congr 1
      · apply Finset.sum_congr rfl
        intro k _
        simp only [Pt.vec]
        rw [List.getD_append _ _ _ _ (by simp), pxe_getD_map_range' vv 0 k]
      · simp only [Pt.vec]
        rw [List.getD_append_right _ _ _ _ (by simp)]
        simp
    have hαa_models : ∀ w : V,
        αa w = (⟨p, p, p - 1, gens, x', posBound p p⟩ : Pt).dot
          ((⟨p, p, p - 1, gens, x', posBound p p⟩ : Pt).vec
            ((⟨p, p, p - 1, gens, x', posBound p p⟩ : Pt).gens.getD (p - 1) ⟨[], []⟩).f)
          (e w) := by
      intro w
      rw [hget_last, hdot_last w]
      calc αa w = αa (ψ (e w)) := congrArg αa (hdecomp w)
        _ = (e w) last * αa e2 + ∑ k : Fin (p - 1), (e w) (embed k) * αa (h k) := by
            rw [hψapp, map_add, map_smul, map_sum]
            simp only [map_smul, Pi.smul_apply, smul_eq_mul]
        _ = ∑ k : Fin (p - 1), ((vv k.val : ℕ) : ZMod p) * (e w) (embed k)
              + 0 * (e w) last := by
            rw [he2a, mul_zero, zero_add, zero_mul, add_zero]
            apply Finset.sum_congr rfl
            intro k _
            rw [← hvv k]
            ring
    refine ⟨p, p - 1, gens, x', posBound p p, ?_, m0⁻¹, hcx, e, ?_⟩
    · exact List.mem_append_right _ (by
        simp only [exclCell, List.mem_flatMap, List.mem_map, List.mem_filter]
        exact ⟨s, by simp only [List.mem_cons, List.not_mem_nil, or_false]; omega,
          o, ho, cvec, ⟨hc, hf⟩, fr, hfr, rfl⟩)
    · unfold Pt.Models
      exact ⟨rfl, by simp [gens], hx_models,
        fun i => ⟨hh_models i, hα_models i⟩, hha_models, hαa_models⟩

end CFSG.TwoNodeSmall
