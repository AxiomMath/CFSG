module

public import CFSG.OddTranspositions.PartThree.Twelve.ElevenFiveChart
import CFSG.OddTranspositions.PartThree.Twelve.ElevenFiveOverlap
import CFSG.Mathlib.Algebra.IsSquareMul
public import CFSG.OddTranspositions.PartThree.Eleven.Five.FiveFormAux
public import CFSG.OddTranspositions.PartThree.Twelve.ElevenFiveNorm

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72 Matrix

variable {G G' : Type} [Group G] [Group G']

theorem mem_fiveOrth_span_singleton {k : ℕ} {ε : Bool} {a x : Fin (k + 1) → ZMod 5} :
    x ∈ fiveOrth k ε (Submodule.span (ZMod 5) {a}) ↔ fiveForm k ε x a = 0 := by
  rw [mem_fiveOrth]
  constructor
  · intro h
    exact h a (Submodule.mem_span_singleton_self a)
  · intro h u hu
    obtain ⟨ν, rfl⟩ := Submodule.mem_span_singleton.mp hu
    rw [fiveForm_smul_right, h, mul_zero]

theorem exists_normalized_axis {k : ℕ} {ε π : Bool} {a b : Fin (k + 1) → ZMod 5}
    (ha0 : fiveForm k ε a a ≠ 0) (haπ : IsSquare (fiveForm k ε a a) ↔ π = true)
    (hb0 : fiveForm k ε b b ≠ 0) (hbπ : IsSquare (fiveForm k ε b b) ↔ π = true)
    (hBab : fiveForm k ε a b ≠ 0) (hne : fiveReflOf k ε b ≠ fiveReflOf k ε a) :
    ∃ b' b'' : Fin (k + 1) → ZMod 5,
      b' = a + b'' ∧ fiveForm k ε a b'' = 0 ∧ b'' ≠ 0 ∧
      fiveReflOf k ε b' = fiveReflOf k ε b ∧
      (IsSquare (fiveForm k ε a a + fiveForm k ε b'' b'') ↔ π = true) ∧
      fiveForm k ε a a + fiveForm k ε b'' b'' ≠ 0 ∧
      orderOf (fiveReflOf k ε a * fiveReflOf k ε b) =
        (if fiveForm k ε b'' b'' = 0 then 5 else 3) := by
  set μ : ZMod 5 := fiveForm k ε a a * (fiveForm k ε a b)⁻¹ with hμ
  have hμ0 : μ ≠ 0 := mul_ne_zero ha0 (inv_ne_zero hBab)
  set b' : Fin (k + 1) → ZMod 5 := μ • b with hb'def
  set b'' : Fin (k + 1) → ZMod 5 := b' - a with hb''def
  have hsplit : b' = a + b'' := by rw [hb''def]; abel
  have hBab' : fiveForm k ε a b' = fiveForm k ε a a := by
    rw [hb'def, fiveForm_smul_right, hμ, mul_assoc, inv_mul_cancel₀ hBab, mul_one]
  have horth : fiveForm k ε a b'' = 0 := by
    rw [hb''def, fiveForm_sub_right, hBab', sub_self]
  have hrefl : fiveReflOf k ε b' = fiveReflOf k ε b := by
    rw [hb'def]; exact fiveReflOf_smul k ε b hμ0
  have hQb' : fiveForm k ε b' b' = fiveForm k ε a a + fiveForm k ε b'' b'' := by
    conv_lhs => rw [hsplit]
    rw [fiveForm_self_add, horth]
    ring
  have hb'0 : fiveForm k ε b' b' ≠ 0 := by
    rw [hb'def, fiveForm_smul_smul]
    exact mul_ne_zero (mul_ne_zero hμ0 hμ0) hb0
  have hb'π : IsSquare (fiveForm k ε b' b') ↔ π = true := by
    rw [hb'def, fiveForm_smul_smul]
    exact (isSquare_mul_self_mul_iff hμ0).trans hbπ
  have hsign : IsSquare (fiveForm k ε a a + fiveForm k ε b'' b'') ↔ π = true := by
    rw [← hQb']; exact hb'π
  have hsum_ne : fiveForm k ε a a + fiveForm k ε b'' b'' ≠ 0 := by
    rw [← hQb']; exact hb'0
  have hb''ne : b'' ≠ 0 := by
    intro h
    apply hne
    have hb'a : b' = a := by
      rw [hb''def] at h
      exact sub_eq_zero.mp h
    rw [← hrefl, hb'a]
  have hnonprop : ∀ ν : ZMod 5, b' ≠ ν • a := by
    intro ν hν
    apply hne
    have heq : fiveForm k ε a a = ν * fiveForm k ε a a := by
      conv_lhs => rw [← hBab']
      rw [hν, fiveForm_smul_right]
    have hν1 : ν = 1 := by
      have h0 : (ν - 1) * fiveForm k ε a a = 0 := by
        rw [sub_mul, one_mul, ← heq, sub_self]
      rcases mul_eq_zero.mp h0 with h | h
      · exact sub_eq_zero.mp h
      · exact absurd h ha0
    rw [← hrefl, hν, hν1, one_smul]
  have hord : orderOf (fiveReflOf k ε a * fiveReflOf k ε b) =
      (if fiveForm k ε b'' b'' = 0 then 5 else 3) := by
    have hformula := orderOf_fiveReflOf_mul k ε π ha0 haπ hb'0 hb'π hnonprop
    have hcond : fiveForm k ε a b' ^ 2 = fiveForm k ε a a * fiveForm k ε b' b' ↔
        fiveForm k ε b'' b'' = 0 := by
      rw [hBab', hQb']
      constructor
      · intro h
        have h2 : fiveForm k ε a a * fiveForm k ε b'' b'' = 0 := by
          have h3 : fiveForm k ε a a * (fiveForm k ε a a + fiveForm k ε b'' b'') -
              fiveForm k ε a a ^ 2 = 0 := by
            rw [← h]; ring
          ring_nf at h3
          exact h3
        exact (mul_eq_zero.mp h2).resolve_left ha0
      · intro h
        rw [h]; ring
    rw [← hrefl, hformula, if_neg (by rw [hBab']; exact ha0)]
    by_cases h : fiveForm k ε b'' b'' = 0
    · rw [if_pos h, if_pos (hcond.mpr h)]
    · rw [if_neg h, if_neg (fun hc => h (hcond.mp hc))]
  exact ⟨b', b'', hsplit, horth, hb''ne, hrefl, hsign, hsum_ne, hord⟩

private theorem zmod5_norm_unique (π : Bool) (qa qb qc : ZMod 5)
    (hqa : qa ≠ 0) (hsa : IsSquare qa ↔ π = true)
    (hqb : qb ≠ 0) (hsb : IsSquare (qa + qb) ↔ π = true) (hb0 : qa + qb ≠ 0)
    (hqc : qc ≠ 0) (hsc : IsSquare (qa + qc) ↔ π = true) (hc0 : qa + qc ≠ 0) :
    qb = qc := by
  revert π qa qb qc
  set_option synthInstance.maxSize 4000 in
  decide

theorem residualFusion_five {D : Set G} {k : ℕ} (hk : 4 ≤ k) {ε π : Bool} {v u : G}
    (cv : FiveLocalModel D v k ε π) (hu : u ∈ commSet D v) {s t : G} (hs : s ∈ commSet D v)
    (ht : t ∈ commSet D v) (hsu : ¬ Commute s u) (htu : ¬ Commute t u)
    (hord : orderOf (u * s) = orderOf (u * t)) :
    ∃ r ∈ Subgroup.closure (commSet D u ∩ commSet D v), r * s * r⁻¹ = t := by
  obtain ⟨a, ha0, haπ, ha⟩ := exists_axis_of_fiveLocalModel cv hu
  obtain ⟨b, hb0, hbπ, hb⟩ := exists_axis_of_fiveLocalModel cv hs
  obtain ⟨c, hc0, hcπ, hc⟩ := exists_axis_of_fiveLocalModel cv ht
  have hBab : fiveForm k ε a b ≠ 0 := by
    intro h0
    have hmem : s ∈ commSet D u := by
      rw [mem_commSet_iff_of_fiveLocalModel cv hu hs ha0 ha]
      rw [hb, fiveReflOf_mulVec, h0]
      simp
    exact hsu hmem.2.1
  have hBac : fiveForm k ε a c ≠ 0 := by
    intro h0
    have hmem : t ∈ commSet D u := by
      rw [mem_commSet_iff_of_fiveLocalModel cv hu ht ha0 ha]
      rw [hc, fiveReflOf_mulVec, h0]
      simp
    exact htu hmem.2.1
  have hba : fiveReflOf k ε b ≠ fiveReflOf k ε a := by
    intro h
    apply hsu
    have hsu' : (⟨s, Subgroup.subset_closure hs⟩ : Subgroup.closure (commSet D v)) =
        ⟨u, Subgroup.subset_closure hu⟩ := by
      apply cv.toMulEquiv.injective
      apply Subtype.ext
      rw [hb, ha, h]
    have hsu_eq : s = u := congrArg Subtype.val hsu'
    rw [hsu_eq]
  have hca : fiveReflOf k ε c ≠ fiveReflOf k ε a := by
    intro h
    apply htu
    have htu' : (⟨t, Subgroup.subset_closure ht⟩ : Subgroup.closure (commSet D v)) =
        ⟨u, Subgroup.subset_closure hu⟩ := by
      apply cv.toMulEquiv.injective
      apply Subtype.ext
      rw [hc, ha, h]
    have htu_eq : t = u := congrArg Subtype.val htu'
    rw [htu_eq]
  obtain ⟨b', b'', hb'split, hb''orth, hb''ne, hb'refl, hb''sign, hb''sum, hb''ord⟩ :=
    exists_normalized_axis ha0 haπ hb0 hbπ hBab hba
  obtain ⟨c', c'', hc'split, hc''orth, hc''ne, hc'refl, hc''sign, hc''sum, hc''ord⟩ :=
    exists_normalized_axis ha0 haπ hc0 hcπ hBac hca
  have hord' : (if fiveForm k ε b'' b'' = 0 then 5 else 3) =
      (if fiveForm k ε c'' c'' = 0 then 5 else 3) := by
    have hos : orderOf (u * s) = orderOf (fiveReflOf k ε a * fiveReflOf k ε b) := by
      rw [orderOf_mul_of_fiveLocalModel cv hu hs, ha, hb]
    have hot : orderOf (u * t) = orderOf (fiveReflOf k ε a * fiveReflOf k ε c) := by
      rw [orderOf_mul_of_fiveLocalModel cv hu ht, ha, hc]
    have hordr : orderOf (fiveReflOf k ε a * fiveReflOf k ε b) =
        orderOf (fiveReflOf k ε a * fiveReflOf k ε c) := by
      rw [← hos, hord, hot]
    rw [hb''ord, hc''ord] at hordr
    exact hordr
  have hW : IsFiveNondeg k ε (fiveOrth k ε (Submodule.span (ZMod 5) {a})) := by
    simpa only [top_inf_eq] using
      isFiveNondeg_inf_fiveOrth (isFiveNondeg_top k ε) (isFiveNondeg_span_singleton ha0) le_top
  have hWdim : 4 ≤ Module.finrank (ZMod 5)
      (fiveOrth k ε (Submodule.span (ZMod 5) {a})) := by
    have hdim := finrank_inf_fiveOrth_add (k := k) (ε := ε) (W := ⊤)
      (U := Submodule.span (ZMod 5) {a}) (isFiveNondeg_top k ε) le_top
    rw [top_inf_eq] at hdim
    have ha_ne : a ≠ 0 := by
      rintro rfl
      exact ha0 (by simp [fiveForm])
    have hspan1 : Module.finrank (ZMod 5) (Submodule.span (ZMod 5) {a}) = 1 :=
      @finrank_span_singleton (ZMod 5) (Fin (k + 1) → ZMod 5) _ _
        (Pi.Function.module _ _ _) (v := a) ha_ne
    have htop : Module.finrank (ZMod 5)
        (⊤ : Submodule (ZMod 5) (Fin (k + 1) → ZMod 5)) = k + 1 := by
      rw [finrank_top]
      exact Module.finrank_fin_fun (R := ZMod 5)
    rw [hspan1, htop] at hdim
    omega
  have hb''_in_W : b'' ∈ fiveOrth k ε (Submodule.span (ZMod 5) {a}) := by
    rw [mem_fiveOrth_span_singleton, fiveForm_comm]
    exact hb''orth
  have hc''_in_W : c'' ∈ fiveOrth k ε (Submodule.span (ZMod 5) {a}) := by
    rw [mem_fiveOrth_span_singleton, fiveForm_comm]
    exact hc''orth
  have hmain : ∃ g ∈ fiveReflectionGroupIn k ε π
      (fiveOrth k ε (Submodule.span (ZMod 5) {a})),
      (g : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ b'' = c'' := by
    rcases eq_or_ne (fiveForm k ε b'' b'') 0 with hb''s | hb''n
    · have hc''s : fiveForm k ε c'' c'' = 0 := by
        by_contra h
        rw [if_pos hb''s, if_neg h] at hord'
        norm_num at hord'
      exact exists_mem_fiveReflectionGroupIn_apply_eq_of_singular hW hWdim hb''_in_W hc''_in_W
        hb''ne hc''ne hb''s hc''s
    · have hc''n : fiveForm k ε c'' c'' ≠ 0 := by
        intro h
        rw [if_neg hb''n, if_pos h] at hord'
        norm_num at hord'
      have hqc : fiveForm k ε b'' b'' = fiveForm k ε c'' c'' :=
        zmod5_norm_unique π (fiveForm k ε a a) (fiveForm k ε b'' b'') (fiveForm k ε c'' c'')
          ha0 haπ hb''n hb''sign hb''sum hc''n hc''sign hc''sum
      exact exists_mem_fiveReflectionGroupIn_apply_eq hW hWdim hb''_in_W hc''_in_W hqc hb''n
  obtain ⟨g, hg, hgb⟩ := hmain
  have hgR : g ∈ fiveReflectionGroup k ε π := by
    refine Subgroup.closure_mono ?_ hg
    intro z hz
    obtain ⟨v, hvW, hv0, hvπ, hzform⟩ := hz
    exact ⟨v, hv0, hvπ, hzform⟩
  let gR : fiveReflectionGroup k ε π := ⟨g, hgR⟩
  let r : Subgroup.closure (commSet D v) := cv.toMulEquiv.symm gR
  have hrg : cv.toMulEquiv r = gR := MulEquiv.apply_symm_apply _ _
  have haH : a ∈ fiveOrth k ε (fiveOrth k ε (Submodule.span (ZMod 5) {a})) := by
    rw [mem_fiveOrth]
    intro u hu
    rw [mem_fiveOrth] at hu
    rw [fiveForm_comm]
    exact hu a (Submodule.mem_span_singleton_self a)
  have hga : (g : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ a = a :=
    fiveReflectionGroupIn_mulVec_eq_of_mem_fiveOrth haH g hg
  have hgpres : ∀ x y, fiveForm k ε
      ((g : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ x)
      ((g : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ y) = fiveForm k ε x y :=
    fiveForm_mulVec_of_mem hgR
  have hgb' : (g : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ b' = c' := by
    rw [hb'split, hc'split, Matrix.mulVec_add, hga, hgb]
  refine ⟨(r : G), ?_, ?_⟩
  · rw [mem_closure_commSet_inter_iff_of_fiveLocalModel cv hu ha0 ha r, hrg]
    exact hg
  · have key : r * ⟨s, Subgroup.subset_closure hs⟩ * r⁻¹ =
        ⟨t, Subgroup.subset_closure ht⟩ := by
      apply cv.toMulEquiv.injective
      rw [map_mul, map_mul, map_inv]
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hrg, hb, hc]
      rw [← hb'refl, ← hc'refl, ← hgb']
      exact conj_fiveReflOf hgpres b'
    simpa using congrArg Subtype.val key

set_option backward.isDefEq.respectTransparency false in
theorem hypLineGroup_localIso_five {D : Set G} {D' : Set G'} {k : ℕ} (hk : 4 ≤ k) {ε π : Bool}
    {u v : G} {u' v' : G'} (hu : u ∈ D) (hv : v ∈ commSet D u)
    (hv' : v' ∈ commSet D' u') (cu : FiveLocalModel D u k ε π) (cu' : FiveLocalModel D' u' k ε π)
    (hcu : FiveHyperplaneData cu) (hcu' : FiveHyperplaneData cu')
    (hθv : (cu.toLocalIso cu').app v = v') (ψ : LocalIso D v D' v') (hψu : ψ.app u = u')
    (hψθ : ∀ y ∈ Subgroup.closure (commSet D u ∩ commSet D v),
      ψ.app y = (cu.toLocalIso cu').app y)
    {s : G} (hs : s ∈ patchSlice D u v) :
    ∀ h ∈ Subgroup.closure (commSet D u),
      (h ∈ Subgroup.closure (commSet D u ∩ commSet D s) ↔
        (cu.toLocalIso cu').app h ∈
          Subgroup.closure (commSet D' u' ∩ commSet D' (ψ.app s))) := by
  intro h hh
  have hsu : ¬ Commute s u := hs.2
  have hsD : s ∈ D := hs.1.1
  have hu_v : u ∈ commSet D v := mem_commSet_symm hu hv
  obtain ⟨a, ha0, haπ, haeq⟩ := exists_axis_of_fiveLocalModel cu hv
  obtain ⟨z, hz0, hzsign, hzfix⟩ := hcu s hsD hsu
  have hs' : ψ.app s ∈ commSet D' v' := ψ.app_mem_commSet hs.1
  have hnc' : ¬ Commute (ψ.app s) u' := by
    rw [← hψu]
    intro hc
    exact hsu ((ψ.commute_iff (Subgroup.subset_closure hs.1)
      (Subgroup.subset_closure hu_v)).1 hc)
  obtain ⟨z', hz'0, hz'sign, hz'fix⟩ := hcu' (ψ.app s) hs'.1 hnc'
  have hvmem : v ∈ Subgroup.closure (commSet D u) := Subgroup.subset_closure hv
  have hcv' : (cu'.toMulEquiv ⟨v', Subgroup.subset_closure hv'⟩ : GL (Fin (k + 1)) (ZMod 5)) =
      fiveReflOf k ε a := by
    have hsub : (⟨v', Subgroup.subset_closure hv'⟩ : Subgroup.closure (commSet D' u')) =
        (cu.toLocalIso cu').toMulEquiv ⟨v, hvmem⟩ := by
      apply Subtype.ext
      exact hθv.symm.trans (LocalIso.app_of_mem (cu.toLocalIso cu') hvmem)
    rw [hsub]
    simp only [FiveLocalModel.toLocalIso, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
    exact haeq
  have hvs : Commute v s := hs.1.2.1.symm
  have hv_z : (cu.toMulEquiv ⟨v, hvmem⟩ : GL (Fin (k + 1)) (ZMod 5)) *ᵥ z = z :=
    (hzfix ⟨v, hvmem⟩ hv).1 hvs
  have haz : fiveForm k ε a z = 0 := by
    rw [haeq] at hv_z
    rw [fiveForm_comm k ε a z]
    exact (fiveReflOf_mulVec_eq_self_iff ha0).1 hv_z
  have hzW : z ∈ fiveOrth k ε (Submodule.span (ZMod 5) {a}) := by
    rw [mem_fiveOrth]
    intro q hq
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hq
    rw [fiveForm_smul_right, fiveForm_comm k ε z a, haz, mul_zero]
  have hv'mem : v' ∈ Subgroup.closure (commSet D' u') := Subgroup.subset_closure hv'
  have hv'_z' : (cu'.toMulEquiv ⟨v', hv'mem⟩ : GL (Fin (k + 1)) (ZMod 5)) *ᵥ z' = z' :=
    (hz'fix ⟨v', hv'mem⟩ hv').1 hs'.2.1.symm
  have haz' : fiveForm k ε a z' = 0 := by
    rw [hcv'] at hv'_z'
    rw [fiveForm_comm k ε a z']
    exact (fiveReflOf_mulVec_eq_self_iff ha0).1 hv'_z'
  have hz'W : z' ∈ fiveOrth k ε (Submodule.span (ZMod 5) {a}) := by
    rw [mem_fiveOrth]
    intro q hq
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hq
    rw [fiveForm_smul_right, fiveForm_comm k ε z' a, haz', mul_zero]
  have hW : IsFiveNondeg k ε (fiveOrth k ε (Submodule.span (ZMod 5) {a})) := by
    have h := isFiveNondeg_inf_fiveOrth (k := k) (ε := ε) (W := ⊤)
      (U := Submodule.span (ZMod 5) {a}) (isFiveNondeg_top k ε)
      (isFiveNondeg_span_singleton ha0) le_top
    simpa using h
  have hW4 : 4 ≤ Module.finrank (ZMod 5) (fiveOrth k ε (Submodule.span (ZMod 5) {a})) := by
    have h := finrank_fiveOrth_span_singleton ha0
    omega
  have hpoint : ∀ w, fiveForm k ε w w ≠ 0 → (IsSquare (fiveForm k ε w w) ↔ π = true) →
      w ∈ fiveOrth k ε (Submodule.span (ZMod 5) {a}) →
      (fiveForm k ε z w = 0 ↔ fiveForm k ε z' w = 0) := by
    intro w hwQ hwπ hwW
    have hrw : fiveReflOf k ε w ∈ fiveReflections k ε π := fiveReflOf_mem hwQ hwπ
    set r : fiveReflectionGroup k ε π :=
      ⟨fiveReflOf k ε w, Subgroup.subset_closure hrw⟩ with hrdef
    set y : Subgroup.closure (commSet D u) := cu.toMulEquiv.symm r with hydef
    have hcu_y : cu.toMulEquiv y = r := by rw [hydef, MulEquiv.apply_symm_apply]
    have hcu_y_gl : (cu.toMulEquiv y : GL (Fin (k + 1)) (ZMod 5)) = fiveReflOf k ε w := by
      rw [hcu_y, hrdef]
    have hydu : (y : G) ∈ commSet D u := (cu.mem_iff y).2 (by rw [hcu_y_gl]; exact hrw)
    have hwa : fiveForm k ε w a = 0 := by
      have h' := hwW
      rw [mem_fiveOrth] at h'
      exact h' a (Submodule.mem_span_singleton_self a)
    have ha_w : fiveForm k ε a w = 0 := by rwa [fiveForm_comm] at hwa
    have hcomma : Commute (fiveReflOf k ε a) (fiveReflOf k ε w) :=
      (commute_fiveReflOf_iff k ε ha0 hwQ).2 (Or.inl ha_w)
    have hcommv : Commute (cu.toMulEquiv ⟨v, hvmem⟩) (cu.toMulEquiv y) := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      rw [show ((cu.toMulEquiv ⟨v, hvmem⟩ : fiveReflectionGroup k ε π) :
            GL (Fin (k + 1)) (ZMod 5)) = fiveReflOf k ε a from haeq,
        show ((cu.toMulEquiv y : fiveReflectionGroup k ε π) :
            GL (Fin (k + 1)) (ZMod 5)) = fiveReflOf k ε w from hcu_y_gl]
      exact hcomma.eq
    have hyv : (y : G) ∈ commSet D v := by
      refine ⟨hydu.1, ?_, ?_⟩
      · have hH : Commute (⟨v, hvmem⟩ : Subgroup.closure (commSet D u)) y := by
          have h := hcommv.map (cu.toMulEquiv.symm : fiveReflectionGroup k ε π →*
              Subgroup.closure (commSet D u))
          simpa using h
        have hc : (y : G) * v = v * (y : G) := by
          have := congrArg Subtype.val hH.eq.symm
          simpa [Subgroup.coe_mul] using this
        exact hc
      · intro hyv_eq
        have hsub : y = ⟨v, hvmem⟩ := Subtype.ext hyv_eq
        have heq : fiveReflOf k ε w = fiveReflOf k ε a := by
          rw [← hcu_y_gl, hsub]
          exact haeq
        exact fiveReflOf_ne_of_fiveForm_eq_zero ha0 ha_w heq
    have hy_closure : (y : G) ∈ Subgroup.closure (commSet D u ∩ commSet D v) :=
      Subgroup.subset_closure ⟨hydu, hyv⟩
    have hψy : ψ.app (y : G) = (cu.toLocalIso cu').app (y : G) := hψθ (y : G) hy_closure
    have hθy_mem : (cu.toLocalIso cu').app (y : G) ∈ Subgroup.closure (commSet D' u') :=
      LocalIso.app_mem (cu.toLocalIso cu') y.2
    have hψy_mem : ψ.app (y : G) ∈ Subgroup.closure (commSet D' u') := by
      rw [hψy]; exact hθy_mem
    have hψy_du : ψ.app (y : G) ∈ commSet D' u' := by
      rw [hψy]
      exact (cu.toLocalIso cu').app_mem_commSet hydu
    have hcu'_y_gl : (cu'.toMulEquiv ⟨ψ.app (y : G), hψy_mem⟩ : GL (Fin (k + 1)) (ZMod 5)) =
        fiveReflOf k ε w := by
      have hsub : (⟨ψ.app (y : G), hψy_mem⟩ : Subgroup.closure (commSet D' u')) =
          (cu.toLocalIso cu').toMulEquiv y := by
        apply Subtype.ext
        exact hψy.trans (LocalIso.app_of_mem (cu.toLocalIso cu') y.2)
      rw [hsub]
      simp only [FiveLocalModel.toLocalIso, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
      exact hcu_y_gl
    have hcomm_ψ : Commute (ψ.app (y : G)) (ψ.app s) ↔ Commute (y : G) s :=
      ψ.commute_iff (Subgroup.subset_closure hyv) (Subgroup.subset_closure hs.1)
    have hz_iff : (fiveReflOf k ε w : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ z = z ↔
        fiveForm k ε z w = 0 :=
      fiveReflOf_mulVec_eq_self_iff hwQ
    have hz'_iff : (fiveReflOf k ε w : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ z' = z' ↔
        fiveForm k ε z' w = 0 :=
      fiveReflOf_mulVec_eq_self_iff hwQ
    constructor
    · intro hz
      have hy_s : Commute (y : G) s := (hzfix y hydu).2 (by rw [hcu_y_gl]; exact hz_iff.2 hz)
      have h2 : Commute (ψ.app (y : G)) (ψ.app s) := hcomm_ψ.2 hy_s
      have h3 : (cu'.toMulEquiv ⟨ψ.app (y : G), hψy_mem⟩ :
            GL (Fin (k + 1)) (ZMod 5)) *ᵥ z' = z' :=
        (hz'fix ⟨ψ.app (y : G), hψy_mem⟩ hψy_du).1 h2
      rw [hcu'_y_gl] at h3
      exact hz'_iff.1 h3
    · intro hz'
      have h2 : Commute (ψ.app (y : G)) (ψ.app s) :=
        (hz'fix ⟨ψ.app (y : G), hψy_mem⟩ hψy_du).2 (by rw [hcu'_y_gl]; exact hz'_iff.2 hz')
      have hy_s : Commute (y : G) s := hcomm_ψ.1 h2
      have h3 : (cu.toMulEquiv y : GL (Fin (k + 1)) (ZMod 5)) *ᵥ z = z :=
        (hzfix y hydu).1 hy_s
      rw [hcu_y_gl] at h3
      exact hz_iff.1 h3
  have hline := span_singleton_eq_of_fiveOrth_eq hW hW4 hzW hz'W hz0 hz'0 hpoint
  have himgR : (cu.toMulEquiv : Subgroup.closure (commSet D u) →*
      fiveReflectionGroup k ε π) '' ((Subgroup.closure (commSet D u)).subtype ⁻¹'
      (commSet D u ∩ commSet D s)) =
      (fiveReflectionGroup k ε π).subtype ⁻¹' (fiveReflectionsFixing k ε π z) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨(cu.mem_iff y).1 hy.1, (hzfix y hy.1).1 hy.2.2.1⟩
    · intro hx
      have hgrefl : (x : GL (Fin (k + 1)) (ZMod 5)) ∈ fiveReflections k ε π := hx.1
      have hgfix : (x : GL (Fin (k + 1)) (ZMod 5)) *ᵥ z = z := hx.2
      set y : Subgroup.closure (commSet D u) := cu.toMulEquiv.symm x with hydef
      have hxy : cu.toMulEquiv y = x := by rw [hydef, MulEquiv.apply_symm_apply]
      have hydu : (y : G) ∈ commSet D u := (cu.mem_iff y).2 (by rw [hxy]; exact hgrefl)
      have hys : (y : G) ∈ commSet D s := by
        refine ⟨hydu.1, ?_, ?_⟩
        · exact (hzfix y hydu).2 (by rw [hxy]; exact hgfix)
        · intro hys_eq
          have hc : Commute s u := by rw [← hys_eq]; exact hydu.2.1
          exact hsu hc
      exact ⟨y, ⟨hydu, hys⟩, hxy⟩
  have hmap : (((Subgroup.closure (commSet D u ∩ commSet D s)).subgroupOf
      (Subgroup.closure (commSet D u))).map cu.toMulEquiv) =
      (Subgroup.closure (fiveReflectionsFixing k ε π z)).subgroupOf
        (fiveReflectionGroup k ε π) := by
    rw [Subgroup.closure_subgroupOf (H := Subgroup.closure (commSet D u))
      (S := commSet D u ∩ commSet D s) (fun x hx => Subgroup.subset_closure hx.1),
      MonoidHom.map_closure,
      Subgroup.closure_subgroupOf (H := fiveReflectionGroup k ε π)
        (S := fiveReflectionsFixing k ε π z)
        (fiveReflectionsFixing_subset_fiveReflectionGroup ε π z),
      himgR]
  have himgR' : (cu'.toMulEquiv : Subgroup.closure (commSet D' u') →*
      fiveReflectionGroup k ε π) '' ((Subgroup.closure (commSet D' u')).subtype ⁻¹'
      (commSet D' u' ∩ commSet D' (ψ.app s))) =
      (fiveReflectionGroup k ε π).subtype ⁻¹' (fiveReflectionsFixing k ε π z') := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨(cu'.mem_iff y).1 hy.1, (hz'fix y hy.1).1 hy.2.2.1⟩
    · intro hx
      have hgrefl : (x : GL (Fin (k + 1)) (ZMod 5)) ∈ fiveReflections k ε π := hx.1
      have hgfix : (x : GL (Fin (k + 1)) (ZMod 5)) *ᵥ z' = z' := hx.2
      set y : Subgroup.closure (commSet D' u') := cu'.toMulEquiv.symm x with hydef
      have hxy : cu'.toMulEquiv y = x := by rw [hydef, MulEquiv.apply_symm_apply]
      have hydu : (y : G') ∈ commSet D' u' := (cu'.mem_iff y).2 (by rw [hxy]; exact hgrefl)
      have hys : (y : G') ∈ commSet D' (ψ.app s) := by
        refine ⟨hydu.1, ?_, ?_⟩
        · exact (hz'fix y hydu).2 (by rw [hxy]; exact hgfix)
        · intro hys_eq
          have hc : Commute (ψ.app s) u' := by rw [← hys_eq]; exact hydu.2.1
          exact hnc' hc
      exact ⟨y, ⟨hydu, hys⟩, hxy⟩
  have hmap' : (((Subgroup.closure (commSet D' u' ∩ commSet D' (ψ.app s))).subgroupOf
      (Subgroup.closure (commSet D' u'))).map cu'.toMulEquiv) =
      (Subgroup.closure (fiveReflectionsFixing k ε π z')).subgroupOf
        (fiveReflectionGroup k ε π) := by
    rw [Subgroup.closure_subgroupOf (H := Subgroup.closure (commSet D' u'))
      (S := commSet D' u' ∩ commSet D' (ψ.app s)) (fun x hx => Subgroup.subset_closure hx.1),
      MonoidHom.map_closure,
      Subgroup.closure_subgroupOf (H := fiveReflectionGroup k ε π)
        (S := fiveReflectionsFixing k ε π z')
        (fiveReflectionsFixing_subset_fiveReflectionGroup ε π z'),
      himgR']
  have hmem : h ∈ Subgroup.closure (commSet D u ∩ commSet D s) ↔
      (cu.toMulEquiv ⟨h, hh⟩ : fiveReflectionGroup k ε π) ∈
        (Subgroup.closure (fiveReflectionsFixing k ε π z)).subgroupOf
          (fiveReflectionGroup k ε π) := by
    have h1 : h ∈ Subgroup.closure (commSet D u ∩ commSet D s) ↔
        (⟨h, hh⟩ : Subgroup.closure (commSet D u)) ∈
          (Subgroup.closure (commSet D u ∩ commSet D s)).subgroupOf
            (Subgroup.closure (commSet D u)) := by
      rw [Subgroup.mem_subgroupOf]
    rw [h1, ← hmap]
    constructor
    · intro hx
      exact Subgroup.mem_map.mpr ⟨⟨h, hh⟩, hx, rfl⟩
    · intro hx
      obtain ⟨x, hxK, hxx⟩ := Subgroup.mem_map.mp hx
      have hxg : x = ⟨h, hh⟩ := cu.toMulEquiv.injective hxx
      rwa [hxg] at hxK
  have hmem' : (cu.toLocalIso cu').app h ∈
        Subgroup.closure (commSet D' u' ∩ commSet D' (ψ.app s)) ↔
      (cu.toMulEquiv ⟨h, hh⟩ : fiveReflectionGroup k ε π) ∈
        (Subgroup.closure (fiveReflectionsFixing k ε π z')).subgroupOf
          (fiveReflectionGroup k ε π) := by
    have hg' : (cu'.toMulEquiv.symm (cu.toMulEquiv ⟨h, hh⟩) : G') =
        (cu.toLocalIso cu').app h := by
      rw [LocalIso.app_of_mem (cu.toLocalIso cu') hh]
      dsimp only [FiveLocalModel.toLocalIso]
      rfl
    have h1 : (cu.toLocalIso cu').app h ∈
          Subgroup.closure (commSet D' u' ∩ commSet D' (ψ.app s)) ↔
        (cu'.toMulEquiv.symm (cu.toMulEquiv ⟨h, hh⟩)) ∈
          (Subgroup.closure (commSet D' u' ∩ commSet D' (ψ.app s))).subgroupOf
            (Subgroup.closure (commSet D' u')) := by
      rw [Subgroup.mem_subgroupOf, hg']
    rw [h1, ← hmap']
    constructor
    · intro hx
      exact Subgroup.mem_map.mpr ⟨cu'.toMulEquiv.symm (cu.toMulEquiv ⟨h, hh⟩), hx,
        MulEquiv.apply_symm_apply _ _⟩
    · intro hx
      obtain ⟨x, hxK, hxx⟩ := Subgroup.mem_map.mp hx
      have hxx' : cu'.toMulEquiv x = cu.toMulEquiv ⟨h, hh⟩ := hxx
      have hxg : x = cu'.toMulEquiv.symm (cu.toMulEquiv ⟨h, hh⟩) := by
        apply cu'.toMulEquiv.injective
        rw [hxx', MulEquiv.apply_symm_apply]
      rwa [hxg] at hxK
  rw [hmem, hmem', Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  have hgz : ((cu.toMulEquiv ⟨h, hh⟩ : fiveReflectionGroup k ε π) :
        GL (Fin (k + 1)) (ZMod 5)) ∈
        Subgroup.closure (fiveReflectionsFixing k ε π z) ↔
      (((cu.toMulEquiv ⟨h, hh⟩ : fiveReflectionGroup k ε π) :
        GL (Fin (k + 1)) (ZMod 5)) :
        Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ z = z := by
    rw [mem_closure_fiveReflectionsFixing_iff hk ε π hz0]
    exact ⟨fun h' => h'.2,
      fun h' => ⟨(cu.toMulEquiv ⟨h, hh⟩ : fiveReflectionGroup k ε π).2, h'⟩⟩
  have hgz' : ((cu.toMulEquiv ⟨h, hh⟩ : fiveReflectionGroup k ε π) :
        GL (Fin (k + 1)) (ZMod 5)) ∈
        Subgroup.closure (fiveReflectionsFixing k ε π z') ↔
      (((cu.toMulEquiv ⟨h, hh⟩ : fiveReflectionGroup k ε π) :
        GL (Fin (k + 1)) (ZMod 5)) :
        Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ z' = z' := by
    rw [mem_closure_fiveReflectionsFixing_iff hk ε π hz'0]
    exact ⟨fun h' => h'.2,
      fun h' => ⟨(cu.toMulEquiv ⟨h, hh⟩ : fiveReflectionGroup k ε π).2, h'⟩⟩
  rw [hgz, hgz']
  obtain ⟨u, hu⟩ := (Submodule.span_singleton_eq_span_singleton (x := z) (y := z')).mp hline
  have hkey : ∀ M : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5),
      M *ᵥ z = z ↔ M *ᵥ z' = z' := by
    intro M
    rw [← hu, Matrix.mulVec_smul]
    constructor
    · intro h'; rw [h']
    · intro h'
      have hc := congrArg (fun v => ((↑u : ZMod 5))⁻¹ • v) h'
      change (↑u : ZMod 5)⁻¹ • ((↑u : ZMod 5) • (M *ᵥ z)) =
        (↑u : ZMod 5)⁻¹ • ((↑u : ZMod 5) • z) at hc
      rw [inv_smul_smul₀ (Units.ne_zero u), inv_smul_smul₀ (Units.ne_zero u)] at hc
      exact hc
  exact hkey _

end CFSG.OddTranspositions.PartThree

end
