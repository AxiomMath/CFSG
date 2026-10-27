module

public import CFSG.LargeExtraspecial.SL4ModClassSpec
public import CFSG.Certificates.Kernel.SL4ModSound

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.SL4Mod

open Module Native CFSG.Sporadic.SmallF2.Native Matrix

theorem exists_equiv_of_validClass_ref {d : ℕ} {refs : Array (Array (Array ℕ))}
    {taus : Array (Array ℕ)} {X : Submodule (ZMod 2) (Fin 105 → ZMod 2)}
    (hX : IsIrredTau taus X d) {m : ℕ} (hm : vec m ∈ X) (hm0 : vec m ≠ 0) {c : ClassCert}
    (hc : validClass d refs taus m c = true) (hk : c.kind = 2) :
    c.ref < refs.size ∧ ∃ e : X ≃ₗ[ZMod 2] (Fin d → ZMod 2), ∀ (s : Fin 6) (F : X),
      e ⟨F.1 ∘ tauF taus[s.val]!, hX.1 s.val s.2 F.1 F.2⟩ =
        refMat d ((refs[c.ref]!)[s.val]!) *ᵥ e F := by
  rw [validClass, Bool.and_eq_true] at hc
  obtain ⟨hd, hc⟩ := hc
  have hL := mem_of_derivOK hX.1 hm hd
  have hL0 : c.L[0]! = m := by
    have h := hd
    rw [derivOK, Bool.and_eq_true, beq_iff_eq] at h
    exact h.1
  have hc2 : (decide (c.L.size = d) && decide (c.ref < refs.size) &&
      refOK taus c.L refs[c.ref]!) = true := by
    have h0 : ¬((c.kind == 0) = true) := by simp [hk]
    have h1 : ¬((c.kind == 1) = true) := by simp [hk]
    have h2 : (c.kind == 2) = true := by simp [hk]
    rw [if_neg h0, if_neg h1, if_pos h2] at hc
    exact hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc2
  obtain ⟨⟨hsz, hr⟩, hrf⟩ := hc2
  obtain ⟨-, -, hrows⟩ := forall_of_refOK hrf
  have hpos : 0 < c.L.size := by
    by_contra h
    have hsz0 : c.L.size = 0 := Nat.eq_zero_of_not_pos h
    have hnil : c.L = #[] := Array.size_eq_zero_iff.mp hsz0
    have h0 : c.L[0]! = 0 := by rw [getElem!_eq_toList_getD, hnil]; rfl
    rw [h0] at hL0
    exact hm0 (hL0 ▸ CFSG.Sporadic.SmallF2.toVecD_zero 105)
  have hS_le : spanB c.L ≤ X := by
    rw [spanB]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    exact hL i.val i.isLt
  have hvecm_S : vec m ∈ spanB c.L := by
    have h1 : vec m = vec c.L[0]! := by rw [hL0]
    rw [h1, spanB]
    exact Submodule.subset_span ⟨⟨0, hpos⟩, rfl⟩
  have hS_inv : IsTauInv taus (spanB c.L) :=
    isTauInv_spanB_of_forall fun t ht s hs => ⟨((refs[c.ref]!)[s]!)[t]!, hrows s hs t ht⟩
  have hne : X ⊓ spanB c.L ≠ ⊥ := by
    intro h0
    apply hm0
    have h1 : vec m ∈ X ⊓ spanB c.L := ⟨hm, hvecm_S⟩
    rw [h0, Submodule.mem_bot] at h1
    exact h1
  have hX_le : X ≤ spanB c.L :=
    (hX.2.2 (X ⊓ spanB c.L)
      (fun s hs F hF => ⟨hX.1 s hs F hF.1, hS_inv s hs F hF.2⟩)
      inf_le_left hne).trans inf_le_right
  have hSX : spanB c.L = X := le_antisymm hS_le hX_le
  let b : Fin d → X := fun k => ⟨vec c.L[k.val]!, hL k.val (by have := k.isLt; omega)⟩
  have hspans : ⊤ ≤ Submodule.span (ZMod 2) (Set.range b) := by
    have hset : X.subtype '' Set.range b =
        Set.range (fun i : Fin c.L.size => vec c.L[i.val]!) := by
      ext x
      simp only [Set.mem_image, Set.mem_range]
      constructor
      · rintro ⟨y, ⟨k, rfl⟩, rfl⟩
        exact ⟨⟨k.val, by have := k.isLt; omega⟩, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨b ⟨i.val, by omega⟩, ⟨⟨i.val, by omega⟩, rfl⟩, rfl⟩
    have hmap : Submodule.map X.subtype (Submodule.span (ZMod 2) (Set.range b)) =
        spanB c.L := by
      rw [Submodule.map_span, spanB, hset]
    have hN : Submodule.span (ZMod 2) (Set.range b) = ⊤ := by
      apply Submodule.map_injective_of_injective X.injective_subtype
      rw [hmap, Submodule.map_top, Submodule.range_subtype, hSX]
    exact hN.ge
  have hcard : Fintype.card (Fin d) = finrank (ZMod 2) X := by
    rw [Fintype.card_fin, hX.2.1]
  let B : Basis (Fin d) (ZMod 2) X := basisOfTopLeSpanOfCardEqFinrank b hspans hcard
  have hBcoe : ⇑B = b := Basis.coe_mk _ _
  refine ⟨hr, B.equivFun, fun s F => ?_⟩
  let M : Matrix (Fin d) (Fin d) (ZMod 2) := refMat d ((refs[c.ref]!)[s.val]!)
  let φ : X →ₗ[ZMod 2] X :=
    (LinearMap.funLeft (ZMod 2) (ZMod 2) (tauF taus[s.val]!)).restrict
      (fun F hF => hX.1 s.val s.2 F hF)
  have hmap2 : B.equivFun.toLinearMap ∘ₗ φ = M.mulVecLin ∘ₗ B.equivFun.toLinearMap := by
    apply Basis.ext B
    intro k
    rw [LinearMap.comp_apply, LinearMap.comp_apply, Matrix.mulVecLin_apply]
    have hBk : B k = b k := congrFun hBcoe k
    have hbk : (B k).1 = vec c.L[k.val]! := by rw [hBk]
    have heBk : B.equivFun (B k) = Pi.single k 1 := by
      funext j
      rw [Basis.equivFun_self, Pi.single_apply]
      by_cases h : j = k
      · subst h; simp
      · rw [if_neg (fun hkj => h hkj.symm), if_neg h]
    have hMcol : M *ᵥ B.equivFun (B k) = fun i : Fin d =>
        if (((refs[c.ref]!)[s.val]!)[k.val]!).testBit i.val then (1 : ZMod 2) else 0 := by
      rw [heBk, Matrix.mulVec_single_one]
      rfl
    have hLHS : (φ (B k)).1 = vec (xorSel (((refs[c.ref]!)[s.val]!)[k.val]!) c.L) := by
      rw [show (φ (B k)).1 = (B k).1 ∘ tauF taus[s.val]! from rfl, hbk, ← vec_actV,
        ← hrows s s.2 k.val (by omega)]
    have hsum : vec (xorSel (((refs[c.ref]!)[s.val]!)[k.val]!) c.L) =
        ∑ i : Fin d, (if (((refs[c.ref]!)[s.val]!)[k.val]!).testBit i.val
          then (1 : ZMod 2) else 0) • vec c.L[i.val]! := by
      rw [vec_xorSel, hsz]
      rw [← Fin.sum_univ_eq_sum_range
        (fun i => if (((refs[c.ref]!)[s.val]!)[k.val]!).testBit i then vec c.L[i]! else 0) d]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases h : (((refs[c.ref]!)[s.val]!)[k.val]!).testBit i.val <;> simp [h]
    have hRHS : (∑ i : Fin d, (if (((refs[c.ref]!)[s.val]!)[k.val]!).testBit i.val
          then (1 : ZMod 2) else 0) • B i).1 =
        ∑ i : Fin d, (if (((refs[c.ref]!)[s.val]!)[k.val]!).testBit i.val
          then (1 : ZMod 2) else 0) • vec c.L[i.val]! := by
      rw [hBcoe]
      simp only [Submodule.coe_sum, Submodule.coe_smul]
      rfl
    have hφBk : φ (B k) = B.equivFun.symm (fun i : Fin d =>
        if (((refs[c.ref]!)[s.val]!)[k.val]!).testBit i.val then (1 : ZMod 2) else 0) := by
      rw [Basis.equivFun_symm_apply]
      apply Subtype.ext
      rw [hLHS, hRHS]
      exact hsum
    have hsymm : (fun i : Fin d => if (((refs[c.ref]!)[s.val]!)[k.val]!).testBit i.val
        then (1 : ZMod 2) else 0) = M *ᵥ B.equivFun (B k) := by
      rw [← hMcol]
    rw [hφBk]
    exact (B.equivFun.apply_symm_apply _).trans hsymm
  have hφF : (⟨F.1 ∘ tauF taus[s.val]!, hX.1 s.val s.2 F.1 F.2⟩ : X) = φ F := rfl
  have hfin := LinearMap.congr_fun hmap2 F
  rw [LinearMap.comp_apply, LinearMap.comp_apply, Matrix.mulVecLin_apply] at hfin
  rw [hφF]
  exact hfin

end CFSG.LargeExtraspecial.SL4Mod
