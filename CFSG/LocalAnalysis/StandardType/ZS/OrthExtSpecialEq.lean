module

public import CFSG.LocalAnalysis.StandardType.ZS.OrthExtSpecialForm
public import CFSG.LocalAnalysis.StandardType.ZS.OrthExtSpecialData
import CFSG.LocalAnalysis.StandardType.ZS.ReflQuotient
public import CFSG.LocalAnalysis.StandardType.ZS.OrthExtBadRefl

public section

namespace CFSG.StandardType.ZS

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]
  {G H B : Subgroup (U ≃ₗ[ZMod p] U)} {h : U ≃ₗ[ZMod p] U}
  {r : Fin 3 → U ≃ₗ[ZMod p] U} {e : Fin 3 → U} {s : U ≃ₗ[ZMod p] U}

private theorem movedSpace_h_eq_span (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hD : LemmaTwoSevenData p G H B h) (hr : r 0 = h)
    (hT : IsCyclicRootTriple p H r e s) :
    HardMathSupport.Kantor79.movedSpace h = Submodule.span (ZMod p) {e 0} := by
  have hne : h (e 0) = -e 0 := hr ▸ (hT.1 0).2.2
  have h0 : e 0 ≠ 0 := hT.2.2.1.ne_zero 0
  exact IsRefl.movedSpace_eq_span hp hD.isRefl hne h0

private theorem Q2_e_ne_zero (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hD : LemmaTwoSevenData p G H B h) (hT : IsCyclicRootTriple p H r e s)
    {Q₂ : QuadraticForm (ZMod p) U} (hQ₂ : (QuadraticMap.polarBilin Q₂).Nondegenerate)
    (hBQ : ∀ g ∈ B, IsIsom p Q₂ g) (hrmem : ∀ i, i ≠ 0 → r i ∈ reflStab p H h)
    {i : Fin 3} (hi : i ≠ 0) : Q₂ (e i) ≠ 0 := by
  have hrB : r i ∈ B := hD.split.2.2.2.2 (hrmem i hi)
  have hrefl : IsRefl p (r i) := (hT.1 i).2.1
  have hrei : r i (e i) = -e i := (hT.1 i).2.2
  obtain ⟨x, hQx, hrx⟩ := DimThree.exists_root_of_isRefl_isIsom hp hQ₂ hrefl (hBQ (r i) hrB)
  have hxmem : x ∈ HardMathSupport.Kantor79.movedSpace (r i) :=
    HardMathSupport.Kantor79.mem_movedSpace_of_apply_eq_neg (ZMod.prime_ne_zero p 2 hp) hrx
  rw [IsRefl.movedSpace_eq_span hp hrefl hrei (hT.2.2.1.ne_zero i)] at hxmem
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hxmem
  intro h0
  exact hQx (by rw [QuadraticMap.map_smul, h0, smul_zero])

private theorem polar_mul_quadratic_eq (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hD : LemmaTwoSevenData p G H B h) (hT : IsCyclicRootTriple p H r e s)
    {Q₁ Q₂ : QuadraticForm (ZMod p) U} (hQ₁ : (QuadraticMap.polarBilin Q₁).Nondegenerate)
    (hoH : IsOrthOn p Q₁ H) (hQ₂ : (QuadraticMap.polarBilin Q₂).Nondegenerate)
    (hBQ : ∀ g ∈ B, IsIsom p Q₂ g) (hA : Q₁ (e 0) ≠ 0) (hQe : ∀ i, Q₁ (e i) = Q₁ (e 0))
    (hrmem : ∀ i, i ≠ 0 → r i ∈ reflStab p H h) {i : Fin 3} (hi : i ≠ 0) (x : U) :
    QuadraticMap.polar Q₁ (e i) x * Q₂ (e i) =
      QuadraticMap.polar Q₂ (e i) x * Q₁ (e i) := by
  have hrH : r i ∈ H := (hT.1 i).1
  have hrB : r i ∈ B := hD.split.2.2.2.2 (hrmem i hi)
  have hrefl : IsRefl p (r i) := (hT.1 i).2.1
  have hrei : r i (e i) = -e i := (hT.1 i).2.2
  have hei : Q₁ (e i) ≠ 0 := by rw [hQe i]; exact hA
  have hQi : Q₂ (e i) ≠ 0 := Q2_e_ne_zero hp hD hT hQ₂ hBQ hrmem hi
  have h1 : r i = CFSG.ClassicalGroups.Orthogonal.reflect Q₁ (e i) :=
    eq_reflect_of_isRefl_isIsom hp hQ₁ hrefl (hoH.isIsom hrH) hei hrei
  have h2 : r i = CFSG.ClassicalGroups.Orthogonal.reflect Q₂ (e i) :=
    eq_reflect_of_isRefl_isIsom hp hQ₂ hrefl (hBQ (r i) hrB) hQi hrei
  have heq : (QuadraticMap.polar Q₁ (e i) x / Q₁ (e i)) • e i =
      (QuadraticMap.polar Q₂ (e i) x / Q₂ (e i)) • e i := by
    have h := congrArg (fun g : U ≃ₗ[ZMod p] U => g x) (h1.symm.trans h2)
    rw [CFSG.ClassicalGroups.Orthogonal.reflect_apply hei,
      CFSG.ClassicalGroups.Orthogonal.reflect_apply hQi] at h
    have h2 : -((QuadraticMap.polar Q₁ (e i) x / Q₁ (e i)) • e i) =
        -((QuadraticMap.polar Q₂ (e i) x / Q₂ (e i)) • e i) :=
      add_left_cancel (a := x) (by simpa [sub_eq_add_neg] using h)
    exact neg_inj.mp h2
  have hcoef : QuadraticMap.polar Q₁ (e i) x / Q₁ (e i) =
      QuadraticMap.polar Q₂ (e i) x / Q₂ (e i) := by
    have h : (QuadraticMap.polar Q₁ (e i) x / Q₁ (e i) -
        QuadraticMap.polar Q₂ (e i) x / Q₂ (e i)) • e i = 0 := by
      rw [sub_smul, heq, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h).resolve_right (hT.2.2.1.ne_zero i))
  exact (div_eq_div_iff hei hQi).mp hcoef

private theorem Q2_ne_zero_of_mem_movedSpace (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {Q₂ : QuadraticForm (ZMod p) U} (hQ₂ : (QuadraticMap.polarBilin Q₂).Nondegenerate)
    (hBQ : ∀ g ∈ B, IsIsom p Q₂ g) {t : U ≃ₗ[ZMod p] U} (htB : t ∈ B) (htr : IsRefl p t)
    {z : U} (hz : z ∈ HardMathSupport.Kantor79.movedSpace t) (hz0 : z ≠ 0) : Q₂ z ≠ 0 := by
  obtain ⟨w, hQw, htw⟩ := DimThree.exists_root_of_isRefl_isIsom hp hQ₂ htr (hBQ t htB)
  have hspan_t : HardMathSupport.Kantor79.movedSpace t = ZMod p ∙ w :=
    IsRefl.movedSpace_eq_span hp htr htw (fun h => hQw (by rw [h]; exact map_zero Q₂))
  obtain ⟨lam, hlam⟩ := Submodule.mem_span_singleton.mp (hspan_t ▸ hz)
  have hlam0 : lam ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hlam
    exact hz0 hlam.symm
  rw [← hlam, QuadraticMap.map_smul]
  rintro h
  rcases smul_eq_zero.mp h with h1 | h2
  · exact hlam0 (mul_self_eq_zero.mp h1)
  · exact hQw h2

private theorem mul_eq_zero_of_polar_relations {Q₁ Q₂ : QuadraticForm (ZMod p) U}
    (hA : Q₁ (e 0) ≠ 0) (hne : Q₂ (e 2) ≠ Q₂ (e 1)) {b1 b2 c1 c2 : ZMod p}
    (hR1 : b1 * Q₂ (e 1) = c1 * Q₁ (e 0))
    (hR2 : b2 * Q₂ (e 2) = c2 * Q₁ (e 0))
    (hlin : c2 * b1 = c1 * b2) : c1 * c2 = 0 := by
  have h4 : c1 * c2 * Q₁ (e 0) * Q₂ (e 2) = c1 * c2 * Q₁ (e 0) * Q₂ (e 1) := by
    have h5 := congrArg (fun z => z * Q₂ (e 1) * Q₂ (e 2)) hlin
    calc c1 * c2 * Q₁ (e 0) * Q₂ (e 2)
        = c2 * (b1 * Q₂ (e 1)) * Q₂ (e 2) := by rw [hR1]; ring
      _ = (c2 * b1) * Q₂ (e 1) * Q₂ (e 2) := by ring
      _ = (c1 * b2) * Q₂ (e 2) * Q₂ (e 1) := by rw [h5]; ring
      _ = c1 * (b2 * Q₂ (e 2)) * Q₂ (e 1) := by ring
      _ = c1 * c2 * Q₁ (e 0) * Q₂ (e 1) := by rw [hR2]; ring
  have hprod : Q₁ (e 0) * (Q₂ (e 2) - Q₂ (e 1)) * (c1 * c2) = 0 := by
    have h6 : (c1 * c2 * Q₁ (e 0)) * (Q₂ (e 2) - Q₂ (e 1)) = 0 := by
      rw [mul_sub, sub_eq_zero.mpr h4]
    rw [show Q₁ (e 0) * (Q₂ (e 2) - Q₂ (e 1)) * (c1 * c2) =
      (c1 * c2 * Q₁ (e 0)) * (Q₂ (e 2) - Q₂ (e 1)) from by ring, h6]
  exact (mul_eq_zero.mp hprod).resolve_left (mul_ne_zero hA (sub_ne_zero.mpr hne))

private theorem polar_pair_mul_eq_zero (hp : p ≠ 2) (hp5 : 5 ≤ p) [Module.Finite (ZMod p) U]
    (hD : LemmaTwoSevenData p G H B h) (hT : IsCyclicRootTriple p H r e s)
    {Q₁ Q₂ : QuadraticForm (ZMod p) U} (hQ₁ : (QuadraticMap.polarBilin Q₁).Nondegenerate)
    (hoH : IsOrthOn p Q₁ H) (hQ₂ : (QuadraticMap.polarBilin Q₂).Nondegenerate)
    (hBQ : ∀ g ∈ B, IsIsom p Q₂ g) (hA : Q₁ (e 0) ≠ 0) (hQe : ∀ i, Q₁ (e i) = Q₁ (e 0))
    (hrmem : ∀ i, i ≠ 0 → r i ∈ reflStab p H h) (hne : Q₂ (e 2) ≠ Q₂ (e 1))
    {t : U ≃ₗ[ZMod p] U} (htB : t ∈ B) (htr : IsRefl p t) {w : U}
    (hw : w ∈ HardMathSupport.Kantor79.movedSpace t) :
    QuadraticMap.polar Q₂ (e 1) w * QuadraticMap.polar Q₂ (e 2) w = 0 := by
  by_cases hw0 : w = 0
  · rw [hw0]; simp
  obtain ⟨w₀, hQw₀, htw₀⟩ := DimThree.exists_root_of_isRefl_isIsom hp hQ₂ htr (hBQ t htB)
  have hw₀0 : w₀ ≠ 0 := fun h => hQw₀ (by rw [h]; exact map_zero Q₂)
  have hspan : HardMathSupport.Kantor79.movedSpace t = ZMod p ∙ w₀ :=
    IsRefl.movedSpace_eq_span hp htr htw₀ hw₀0
  have hQw : Q₂ w ≠ 0 := Q2_ne_zero_of_mem_movedSpace hp hQ₂ hBQ htB htr hw hw0
  have htw : t w = -w := HardMathSupport.Kantor79.apply_eq_neg_of_mem_movedSpace htr.1 hw
  have htref : t = CFSG.ClassicalGroups.Orthogonal.reflect Q₂ w :=
    eq_reflect_of_isRefl_isIsom hp hQ₂ htr (hBQ t htB) hQw htw
  have he1H : e 1 ∈ HardMathSupport.Kantor79.commutatorSpace H :=
    isCyclicRootTriple_root_mem_commutatorSpace hp hT 1
  have he2H : e 2 ∈ HardMathSupport.Kantor79.commutatorSpace H :=
    isCyclicRootTriple_root_mem_commutatorSpace hp hT 2
  set c1 : ZMod p := QuadraticMap.polar Q₂ (e 1) w with hc1
  set c2 : ZMod p := QuadraticMap.polar Q₂ (e 2) w with hc2
  have hvH : c2 • e 1 - c1 • e 2 ∈ HardMathSupport.Kantor79.commutatorSpace H :=
    Submodule.sub_mem _ (Submodule.smul_mem _ _ he1H) (Submodule.smul_mem _ _ he2H)
  have hbeta : QuadraticMap.polar Q₂ w (c2 • e 1 - c1 • e 2) = 0 := by
    rw [QuadraticMap.polar_sub_right, ClassicalGroups.Orthogonal.polar_smul_right_eq,
      ClassicalGroups.Orthogonal.polar_smul_right_eq,
      QuadraticMap.polar_comm Q₂ w (e 1), QuadraticMap.polar_comm Q₂ w (e 2),
      show QuadraticMap.polar Q₂ (e 1) w = c1 from hc1.symm,
      show QuadraticMap.polar Q₂ (e 2) w = c2 from hc2.symm]
    ring
  have htv : t (c2 • e 1 - c1 • e 2) = c2 • e 1 - c1 • e 2 := by
    rw [htref, CFSG.ClassicalGroups.Orthogonal.reflect_apply_of_polar_eq_zero hbeta]
  have hb1 : QuadraticMap.polar Q₁ (c2 • e 1 - c1 • e 2) w = 0 :=
    polar_eq_zero_of_apply_eq_neg_of_apply_eq hp5 hD hQ₁ hoH htB htw hvH htv
  rw [QuadraticMap.polar_sub_left, ClassicalGroups.Orthogonal.polar_smul_left_eq,
    ClassicalGroups.Orthogonal.polar_smul_left_eq] at hb1
  have hR1 := polar_mul_quadratic_eq hp hD hT hQ₁ hoH hQ₂ hBQ hA hQe hrmem (i := 1) (by decide) w
  have hR2 := polar_mul_quadratic_eq hp hD hT hQ₁ hoH hQ₂ hBQ hA hQe hrmem (i := 2) (by decide) w
  rw [hQe 1] at hR1
  rw [hQe 2] at hR2
  exact mul_eq_zero_of_polar_relations hA hne hR1 hR2 (sub_eq_zero.mp hb1)

private theorem finrank_commutatorSpace_reflStab (hp : p ≠ 2) (hp5 : 5 ≤ p)
    [Module.Finite (ZMod p) U] (hD : LemmaTwoSevenData p G H B h)
    (h4 : Module.finrank (ZMod p) U = 4) (hr : r 0 = h)
    (hT : IsCyclicRootTriple p H r e s) {Q₁ : QuadraticForm (ZMod p) U}
    (hQ₁ : (QuadraticMap.polarBilin Q₁).Nondegenerate) (hoH : IsOrthOn p Q₁ H) :
    Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace (reflStab p H h)) = 2 := by
  have hsplitH : SplitSupport H 3 := by simpa [h4] using hD.setting.sub.2.1
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have he0 : e 0 ≠ 0 := hT.2.2.1.ne_zero 0
  have hne : h (e 0) = -e 0 := hr ▸ (hT.1 0).2.2
  rw [commutatorSpace_reflStab hp hQ₁ hsplitH (by omega) (by intro h3; omega) hoH hD.mem
    hD.isRefl]
  have he0VH : e 0 ∈ HardMathSupport.Kantor79.commutatorSpace H :=
    HardMathSupport.Kantor79.movedSpace_le_commutatorSpace hD.mem
      (HardMathSupport.Kantor79.mem_movedSpace_of_apply_eq_neg h2 hne)
  have he0ker : e 0 ∉ LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1) := by
    intro h0
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply] at h0
    have h0' : (h : U →ₗ[ZMod p] U) (e 0) - e 0 = 0 := h0
    rw [show (h : U →ₗ[ZMod p] U) (e 0) = -e 0 from hne] at h0'
    have h3 : (2 : ZMod p) • e 0 = 0 := by
      rw [two_smul, ← neg_eq_zero, neg_add]
      rwa [sub_eq_add_neg] at h0'
    exact he0 ((smul_eq_zero.mp h3).resolve_left h2)
  have h := IsRefl.finrank_inf_ker_sub_one_add_one hp hD.isRefl (A :=
    HardMathSupport.Kantor79.commutatorSpace H) (a := e 0) he0VH he0ker
  rw [hsplitH.2.1] at h
  omega

private theorem finrank_span_e1_e2 (hcomm : HardMathSupport.Kantor79.commutatorSpace
    (reflStab p H h) = Submodule.span (ZMod p) {e 1, e 2})
    (h2 : Module.finrank (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace (reflStab p H h)) = 2) :
    Module.finrank (ZMod p) (Submodule.span (ZMod p) {e 1, e 2}) = 2 := by
  rw [← hcomm]
  exact h2

private theorem y_notMem_span_e1_e2 [Module.Finite (ZMod p) U]
    (hD : LemmaTwoSevenData p G H B h) (h4 : Module.finrank (ZMod p) U = 4)
    (hcomm : HardMathSupport.Kantor79.commutatorSpace (reflStab p H h) =
      Submodule.span (ZMod p) {e 1, e 2}) {y : U} (hyH : y ∈ centralizerSpace H)
    (hy0 : y ≠ 0) : y ∉ Submodule.span (ZMod p) {e 1, e 2} := by
  have hsplitH : SplitSupport H 3 := by simpa [h4] using hD.setting.sub.2.1
  rw [← hcomm]
  intro hy
  have hle := HardMathSupport.Kantor79.commutatorSpace_mono
    (H := reflStab p H h) (H' := H) (reflSubgroupIn_le H _)
  have hbot : y ∈ (⊥ : Submodule (ZMod p) U) := by
    rw [← hsplitH.1.inf_eq_bot]
    exact ⟨hle hy, hyH⟩
  exact hy0 (by simpa using hbot)

private theorem finrank_span_y_sup_span_e1_e2 [Module.Finite (ZMod p) U] {y : U} (hy0 : y ≠ 0)
    (hy : y ∉ Submodule.span (ZMod p) ({e 1, e 2} : Set U))
    (hfin : Module.finrank (ZMod p) ↥(Submodule.span (ZMod p) ({e 1, e 2} : Set U)) = 2) :
    Module.finrank (ZMod p) ↥(Submodule.span (ZMod p) ({y} : Set U) ⊔
      Submodule.span (ZMod p) ({e 1, e 2} : Set U)) = 3 := by
  have hdisj : Submodule.span (ZMod p) ({y} : Set U) ⊓
      Submodule.span (ZMod p) ({e 1, e 2} : Set U) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro z hz
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz.1
    by_cases hc : c = 0
    · rw [hc, zero_smul]
    · exfalso
      apply hy
      have hmem : y = c⁻¹ • (c • y) := by rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
      rw [hmem]
      exact Submodule.smul_mem _ _ hz.2
  have h := Submodule.finrank_sup_add_finrank_inf_eq
    (Submodule.span (ZMod p) ({y} : Set U)) (Submodule.span (ZMod p) ({e 1, e 2} : Set U))
  rw [hdisj, finrank_bot, finrank_span_singleton hy0, hfin] at h
  omega

private theorem span_e1_e2_y_eq_commutatorSpace (hp : p ≠ 2) (hp5 : 5 ≤ p)
    [Module.Finite (ZMod p) U] (hD : LemmaTwoSevenData p G H B h)
    (h4 : Module.finrank (ZMod p) U = 4) (hr : r 0 = h)
    (hT : IsCyclicRootTriple p H r e s) {Q₁ : QuadraticForm (ZMod p) U}
    (hQ₁ : (QuadraticMap.polarBilin Q₁).Nondegenerate) (hoH : IsOrthOn p Q₁ H)
    (hcomm : HardMathSupport.Kantor79.commutatorSpace (reflStab p H h) =
      Submodule.span (ZMod p) {e 1, e 2}) {y : U} (hyH : y ∈ centralizerSpace H)
    (hy0 : y ≠ 0) (hyB : y ∈ HardMathSupport.Kantor79.commutatorSpace B) :
    Submodule.span (ZMod p) ({e 1, e 2, y} : Set U) =
      HardMathSupport.Kantor79.commutatorSpace B := by
  have hfin : Module.finrank (ZMod p) (Submodule.span (ZMod p) {e 1, e 2}) = 2 :=
    finrank_span_e1_e2 hcomm (finrank_commutatorSpace_reflStab hp hp5 hD h4 hr hT hQ₁ hoH)
  have hy : y ∉ Submodule.span (ZMod p) {e 1, e 2} :=
    y_notMem_span_e1_e2 hD h4 hcomm hyH hy0
  have hset : ({e 1, e 2, y} : Set U) = insert y {e 1, e 2} := by
    ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have hspan : Submodule.span (ZMod p) ({e 1, e 2, y} : Set U) =
      Submodule.span (ZMod p) ({y} : Set U) ⊔ Submodule.span (ZMod p) ({e 1, e 2} : Set U) := by
    rw [hset]
    exact Submodule.span_insert y ({e 1, e 2} : Set U)
  have hfinS : Module.finrank (ZMod p) ↥(Submodule.span (ZMod p) ({y} : Set U) ⊔
      Submodule.span (ZMod p) ({e 1, e 2} : Set U)) = 3 :=
    finrank_span_y_sup_span_e1_e2 hy0 hy hfin
  have hle : Submodule.span (ZMod p) ({e 1, e 2, y} : Set U) ≤
      HardMathSupport.Kantor79.commutatorSpace B := by
    rw [hspan]
    refine sup_le ?_ ?_
    · refine Submodule.span_le.mpr ?_
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact hyB
    · rw [← hcomm]
      exact HardMathSupport.Kantor79.commutatorSpace_mono
        (H := reflStab p H h) (H' := B) hD.split.2.2.2.2
  have hfinVB : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace B) = 3 := by
    have := hD.split.2.2.1.2.1
    omega
  have hfin' : Module.finrank (ZMod p) (Submodule.span (ZMod p) ({e 1, e 2, y} : Set U)) = 3 := by
    rw [hspan]
    exact hfinS
  exact Submodule.eq_of_le_of_finrank_eq hle (by rw [hfin', hfinVB])

private theorem polar_e1_e2_eq_zero (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hD : LemmaTwoSevenData p G H B h)
    {Q₂ : QuadraticForm (ZMod p) U} (hBQ : ∀ g ∈ B, IsIsom p Q₂ g)
    (hrmem : ∀ i, i ≠ 0 → r i ∈ reflStab p H h)
    (hrapp : ∀ i j, r i (e j) = if i = j then -e j else e j) :
    QuadraticMap.polar Q₂ (e 1) (e 2) = 0 := by
  have hrB : r 1 ∈ B := hD.split.2.2.2.2 (hrmem 1 (by decide))
  have hr1 : r 1 (e 1) = -e 1 := by rw [hrapp]; simp
  have hr2 : r 1 (e 2) = e 2 := by rw [hrapp]; simp
  exact IsIsom.polar_eq_zero_of_apply_eq_neg_of_apply_eq hp (hBQ (r 1) hrB) hr1 hr2

private theorem polar_e_y_eq_zero (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hD : LemmaTwoSevenData p G H B h) (hT : IsCyclicRootTriple p H r e s)
    {Q₂ : QuadraticForm (ZMod p) U} (hBQ : ∀ g ∈ B, IsIsom p Q₂ g)
    (hrmem : ∀ i, i ≠ 0 → r i ∈ reflStab p H h)
    (hrapp : ∀ i j, r i (e j) = if i = j then -e j else e j) {y : U}
    (hyH : y ∈ centralizerSpace H) :
    QuadraticMap.polar Q₂ (e 1) y = 0 ∧ QuadraticMap.polar Q₂ (e 2) y = 0 := by
  constructor
  · have hrB : r 1 ∈ B := hD.split.2.2.2.2 (hrmem 1 (by decide))
    have hr1 : r 1 (e 1) = -e 1 := by rw [hrapp]; simp
    have hry : r 1 y = y := mem_centralizerSpace.mp hyH (r 1) (hT.1 1).1
    exact IsIsom.polar_eq_zero_of_apply_eq_neg_of_apply_eq hp (hBQ (r 1) hrB) hr1 hry
  · have hrB : r 2 ∈ B := hD.split.2.2.2.2 (hrmem 2 (by decide))
    have hr2 : r 2 (e 2) = -e 2 := by rw [hrapp]; simp
    have hry : r 2 y = y := mem_centralizerSpace.mp hyH (r 2) (hT.1 2).1
    exact IsIsom.polar_eq_zero_of_apply_eq_neg_of_apply_eq hp (hBQ (r 2) hrB) hr2 hry

private theorem polar_e0_y_eq_zero (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hD : LemmaTwoSevenData p G H B h) (hr : r 0 = h)
    (hT : IsCyclicRootTriple p H r e s) {Q₂ : QuadraticForm (ZMod p) U}
    (hBQ : ∀ g ∈ B, IsIsom p Q₂ g) {y : U}
    (hyB : y ∈ HardMathSupport.Kantor79.commutatorSpace B) :
    QuadraticMap.polar Q₂ y (e 0) = 0 := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have he0 : e 0 ≠ 0 := hT.2.2.1.ne_zero 0
  have hne : h (e 0) = -e 0 := hr ▸ (hT.1 0).2.2
  have he0C : e 0 ∈ centralizerSpace B := by
    rw [(commutatorSpace_eq_ker_of_isCentralizingSplit hp
    (by have := hD.setting.four_le; omega) hD.split hD.isRefl).2]
    exact HardMathSupport.Kantor79.mem_movedSpace_of_apply_eq_neg h2 hne
  rw [QuadraticMap.polar_comm]
  exact polar_eq_zero_of_mem_centralizerSpace (X := B) hBQ he0C hyB

private theorem isCompl_commutatorSpace_span_root (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hD : LemmaTwoSevenData p G H B h) (hr : r 0 = h)
    (hT : IsCyclicRootTriple p H r e s) :
    IsCompl (HardMathSupport.Kantor79.commutatorSpace B) (Submodule.span (ZMod p) {e 0}) := by
  rw [(commutatorSpace_eq_ker_of_isCentralizingSplit hp
      (by have := hD.setting.four_le; omega) hD.split hD.isRefl).1,
    ← movedSpace_h_eq_span hp hD hr hT,
    IsRefl.movedSpace_eq_ker_add_one hp hD.isRefl]
  exact IsRefl.isCompl_ker_sub_one_ker_add_one hp hD.isRefl

private theorem Q2_y_ne_zero (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hD : LemmaTwoSevenData p G H B h) (hr : r 0 = h)
    (hT : IsCyclicRootTriple p H r e s) {Q₂ : QuadraticForm (ZMod p) U}
    (hQ₂ : (QuadraticMap.polarBilin Q₂).Nondegenerate) (hBQ : ∀ g ∈ B, IsIsom p Q₂ g)
    {y : U} (hyB : y ∈ HardMathSupport.Kantor79.commutatorSpace B) (hy0 : y ≠ 0)
    (hy1 : QuadraticMap.polar Q₂ (e 1) y = 0)
    (hy2 : QuadraticMap.polar Q₂ (e 2) y = 0)
    (hspan : Submodule.span (ZMod p) ({e 1, e 2, y} : Set U) =
      HardMathSupport.Kantor79.commutatorSpace B) :
    Q₂ y ≠ 0 := by
  intro h0
  have hker : ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace B,
      QuadraticMap.polar Q₂ y v = 0 := by
    have hsub : Submodule.span (ZMod p) ({e 1, e 2, y} : Set U) ≤
        LinearMap.ker (QuadraticMap.polarBilin Q₂ y) := by
      rw [Submodule.span_le]
      rintro z (rfl | rfl | rfl)
      · exact LinearMap.mem_ker.mpr (by
          rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm]; exact hy1)
      · exact LinearMap.mem_ker.mpr (by
          rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm]; exact hy2)
      · exact LinearMap.mem_ker.mpr (by
          rw [QuadraticMap.polarBilin_apply_apply,
            CFSG.ClassicalGroups.Orthogonal.polar_self_eq_two_mul, h0, mul_zero])
    intro v hv
    rw [← hspan] at hv
    exact LinearMap.mem_ker.mp (hsub hv)
  have hye0 : QuadraticMap.polar Q₂ y (e 0) = 0 := polar_e0_y_eq_zero hp hD hr hT hBQ hyB
  have hcompl := isCompl_commutatorSpace_span_root hp hD hr hT
  refine hy0 (hQ₂.1 y fun u => ?_)
  obtain ⟨v, hv, w, hw, huv⟩ := Submodule.mem_sup.mp
    (hcompl.sup_eq_top ▸ (Submodule.mem_top : u ∈ (⊤ : Submodule (ZMod p) U)))
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hw
  rw [← huv, ← hc, map_add, map_smul, QuadraticMap.polarBilin_apply_apply,
    QuadraticMap.polarBilin_apply_apply, hker v hv, hye0, smul_zero, add_zero]

private theorem coord_of_mem_commutatorSpace {y : U}
    (hspan : Submodule.span (ZMod p) ({e 1, e 2, y} : Set U) =
      HardMathSupport.Kantor79.commutatorSpace B) {w : U}
    (hw : w ∈ HardMathSupport.Kantor79.commutatorSpace B) :
    ∃ a b c : ZMod p, w = a • e 1 + b • e 2 + c • y := by
  rw [← hspan] at hw
  rw [show ({e 1, e 2, y} : Set U) = insert (e 1) (insert (e 2) {y}) from by ext z; simp]
    at hw
  obtain ⟨a, z, hz, hwz⟩ := Submodule.mem_span_insert.mp hw
  obtain ⟨b, z', hz', hzz⟩ := Submodule.mem_span_insert.mp hz
  obtain ⟨c, hzc⟩ := Submodule.mem_span_singleton.mp hz'
  refine ⟨a, b, c, ?_⟩
  rw [hwz, hzz, hzc]
  abel

private theorem polar_e2_coord {Q₂ : QuadraticForm (ZMod p) U} {y : U}
    (h21 : QuadraticMap.polar Q₂ (e 2) (e 1) = 0)
    (h2y : QuadraticMap.polar Q₂ (e 2) y = 0) (a b c : ZMod p) :
    QuadraticMap.polar Q₂ (e 2) (a • e 1 + b • e 2 + c • y) = b * (2 * Q₂ (e 2)) := by
  rw [QuadraticMap.polar_add_right, QuadraticMap.polar_add_right,
    ClassicalGroups.Orthogonal.polar_smul_right_eq,
    ClassicalGroups.Orthogonal.polar_smul_right_eq,
    ClassicalGroups.Orthogonal.polar_smul_right_eq, h21, h2y,
    ClassicalGroups.Orthogonal.polar_self_eq_two_mul]
  ring

private theorem polar_e1_coord {Q₂ : QuadraticForm (ZMod p) U} {y : U}
    (h12 : QuadraticMap.polar Q₂ (e 1) (e 2) = 0)
    (h1y : QuadraticMap.polar Q₂ (e 1) y = 0) (a b c : ZMod p) :
    QuadraticMap.polar Q₂ (e 1) (a • e 1 + b • e 2 + c • y) = a * (2 * Q₂ (e 1)) := by
  rw [QuadraticMap.polar_add_right, QuadraticMap.polar_add_right,
    ClassicalGroups.Orthogonal.polar_smul_right_eq,
    ClassicalGroups.Orthogonal.polar_smul_right_eq,
    ClassicalGroups.Orthogonal.polar_smul_right_eq, h12, h1y,
    ClassicalGroups.Orthogonal.polar_self_eq_two_mul]
  ring

private theorem mem_span_e1_y_or_e2_y (hp : p ≠ 2) {Q₂ : QuadraticForm (ZMod p) U} {y : U}
    (hspan : Submodule.span (ZMod p) ({e 1, e 2, y} : Set U) =
      HardMathSupport.Kantor79.commutatorSpace B)
    (h12 : QuadraticMap.polar Q₂ (e 1) (e 2) = 0)
    (h1y : QuadraticMap.polar Q₂ (e 1) y = 0)
    (h2y : QuadraticMap.polar Q₂ (e 2) y = 0)
    (hQ1 : Q₂ (e 1) ≠ 0) (hQ2 : Q₂ (e 2) ≠ 0) {w : U}
    (hw : w ∈ HardMathSupport.Kantor79.commutatorSpace B)
    (hK : QuadraticMap.polar Q₂ (e 1) w * QuadraticMap.polar Q₂ (e 2) w = 0) :
    w ∈ Submodule.span (ZMod p) ({e 1, y} : Set U) ∨
      w ∈ Submodule.span (ZMod p) ({e 2, y} : Set U) := by
  have h21 : QuadraticMap.polar Q₂ (e 2) (e 1) = 0 := by
    rw [QuadraticMap.polar_comm]; exact h12
  obtain ⟨a, b, c, rfl⟩ := coord_of_mem_commutatorSpace hspan hw
  rw [polar_e1_coord h12 h1y, polar_e2_coord h21 h2y] at hK
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have h2a : (2 : ZMod p) * Q₂ (e 1) ≠ 0 := mul_ne_zero h2 hQ1
  have h2b : (2 : ZMod p) * Q₂ (e 2) ≠ 0 := mul_ne_zero h2 hQ2
  have hab : a = 0 ∨ b = 0 := by
    rcases mul_eq_zero.mp hK with h | h
    · exact Or.inl ((mul_eq_zero.mp h).resolve_right h2a)
    · exact Or.inr ((mul_eq_zero.mp h).resolve_right h2b)
  rcases hab with rfl | rfl
  · right
    refine Submodule.mem_span_pair.mpr ⟨b, c, ?_⟩
    rw [zero_smul, zero_add]
  · left
    refine Submodule.mem_span_pair.mpr ⟨a, c, ?_⟩
    rw [zero_smul, add_zero]

private theorem apply_mem_movedSpace_conj {g t : U ≃ₗ[ZMod p] U} {w : U}
    (hw : w ∈ HardMathSupport.Kantor79.movedSpace t) :
    g w ∈ HardMathSupport.Kantor79.movedSpace (g * t * g⁻¹) := by
  obtain ⟨v, hv⟩ := hw
  refine ⟨g v, ?_⟩
  change (g * t * g⁻¹) (g v) - g v = g w
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, show g⁻¹ (g v) = v from by simp, ← map_sub,
    show t v - v = w from hv]

private theorem polar_pair_coord {Q₂ : QuadraticForm (ZMod p) U} {y : U}
    (h12 : QuadraticMap.polar Q₂ (e 1) (e 2) = 0)
    (h1y : QuadraticMap.polar Q₂ (e 1) y = 0)
    (h2y : QuadraticMap.polar Q₂ (e 2) y = 0) (a b c c' : ZMod p) :
    QuadraticMap.polar Q₂ (a • e 1 + c • y) (b • e 2 + c' • y) = (c * c') * (2 * Q₂ y) := by
  have hy2 : QuadraticMap.polar Q₂ y (e 2) = 0 := by
    rw [QuadraticMap.polar_comm]; exact h2y
  simp only [QuadraticMap.polar_add_left, QuadraticMap.polar_add_right,
    ClassicalGroups.Orthogonal.polar_smul_left_eq,
    ClassicalGroups.Orthogonal.polar_smul_right_eq, h12, h1y, hy2,
    ClassicalGroups.Orthogonal.polar_self_eq_two_mul, mul_zero, add_zero]
  ring

private theorem polar_e2_eq_zero_of_mem_span_e1_y {Q₂ : QuadraticForm (ZMod p) U} {y : U}
    (h21 : QuadraticMap.polar Q₂ (e 2) (e 1) = 0)
    (h2y : QuadraticMap.polar Q₂ (e 2) y = 0) {x : U}
    (hx : x ∈ Submodule.span (ZMod p) ({e 1, y} : Set U)) :
    QuadraticMap.polar Q₂ (e 2) x = 0 := by
  obtain ⟨p, q, rfl⟩ := Submodule.mem_span_pair.mp hx
  rw [QuadraticMap.polar_add_right, ClassicalGroups.Orthogonal.polar_smul_right_eq,
    ClassicalGroups.Orthogonal.polar_smul_right_eq, h21, h2y, mul_zero, mul_zero, add_zero]

private theorem polar_e1_eq_zero_of_mem_span_e2_y {Q₂ : QuadraticForm (ZMod p) U} {y : U}
    (h12 : QuadraticMap.polar Q₂ (e 1) (e 2) = 0)
    (h1y : QuadraticMap.polar Q₂ (e 1) y = 0) {x : U}
    (hx : x ∈ Submodule.span (ZMod p) ({e 2, y} : Set U)) :
    QuadraticMap.polar Q₂ (e 1) x = 0 := by
  obtain ⟨p, q, rfl⟩ := Submodule.mem_span_pair.mp hx
  rw [QuadraticMap.polar_add_right, ClassicalGroups.Orthogonal.polar_smul_right_eq,
    ClassicalGroups.Orthogonal.polar_smul_right_eq, h12, h1y, mul_zero, mul_zero, add_zero]

private theorem roots_mem_planes (hp : p ≠ 2) (hp5 : 5 ≤ p) [Module.Finite (ZMod p) U]
    (hD : LemmaTwoSevenData p G H B h) (hT : IsCyclicRootTriple p H r e s)
    {Q₁ Q₂ : QuadraticForm (ZMod p) U} (hQ₁ : (QuadraticMap.polarBilin Q₁).Nondegenerate)
    (hoH : IsOrthOn p Q₁ H) (hQ₂ : (QuadraticMap.polarBilin Q₂).Nondegenerate)
    (hBQ : ∀ g ∈ B, IsIsom p Q₂ g) (hA : Q₁ (e 0) ≠ 0) (hQe : ∀ i, Q₁ (e i) = Q₁ (e 0))
    (hrmem : ∀ i, i ≠ 0 → r i ∈ reflStab p H h) (hne : Q₂ (e 2) ≠ Q₂ (e 1)) {y : U}
    (hspan : Submodule.span (ZMod p) ({e 1, e 2, y} : Set U) =
      HardMathSupport.Kantor79.commutatorSpace B)
    (h12 : QuadraticMap.polar Q₂ (e 1) (e 2) = 0)
    (h1y : QuadraticMap.polar Q₂ (e 1) y = 0)
    (h2y : QuadraticMap.polar Q₂ (e 2) y = 0) (hQ1 : Q₂ (e 1) ≠ 0) (hQ2 : Q₂ (e 2) ≠ 0) :
    ∀ t ∈ B, IsRefl p t → ∀ z ∈ HardMathSupport.Kantor79.movedSpace t,
      z ∈ Submodule.span (ZMod p) ({e 1, y} : Set U) ∨
        z ∈ Submodule.span (ZMod p) ({e 2, y} : Set U) := by
  intro t htB htr z hz
  exact mem_span_e1_y_or_e2_y hp hspan h12 h1y h2y hQ1 hQ2
    (HardMathSupport.Kantor79.movedSpace_le_commutatorSpace htB hz)
    (polar_pair_mul_eq_zero hp hp5 hD hT hQ₁ hoH hQ₂ hBQ hA hQe hrmem hne htB htr hz)

private theorem invariant_of_roots (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {Q₂ : QuadraticForm (ZMod p) U} (hQ₂ : (QuadraticMap.polarBilin Q₂).Nondegenerate)
    (hBQ : ∀ g ∈ B, IsIsom p Q₂ g) (hgen : ReflGen p B) {P L : Submodule (ZMod p) U}
    (hLorth : ∀ w ∈ L, ∀ x ∈ P, QuadraticMap.polar Q₂ w x = 0)
    (hroots : ∀ t ∈ B, IsRefl p t → ∀ z ∈ HardMathSupport.Kantor79.movedSpace t,
      z ∈ P ∨ z ∈ L) :
    ∀ g ∈ B, ∀ x ∈ P, g x ∈ P := by
  rw [hgen]
  refine forall_mem_closure_mapsTo_of_forall ?_
  rintro t ⟨htB, htr⟩ x hx
  obtain ⟨w, hQw, htw⟩ := DimThree.exists_root_of_isRefl_isIsom hp hQ₂ htr (hBQ t htB)
  have hmem : w ∈ HardMathSupport.Kantor79.movedSpace t :=
    HardMathSupport.Kantor79.mem_movedSpace_of_apply_eq_neg (ZMod.prime_ne_zero p 2 hp) htw
  have hteq : t = CFSG.ClassicalGroups.Orthogonal.reflect Q₂ w :=
    eq_reflect_of_isRefl_isIsom hp hQ₂ htr (hBQ t htB) hQw htw
  rcases hroots t htB htr w hmem with hP | hL
  · rw [hteq, CFSG.ClassicalGroups.Orthogonal.reflect_apply hQw]
    exact Submodule.sub_mem _ hx (Submodule.smul_mem _ _ hP)
  · rw [hteq, CFSG.ClassicalGroups.Orthogonal.reflect_apply_of_polar_eq_zero (hLorth w hL x hx)]
    exact hx

private theorem false_of_invariant_plane [Module.Finite (ZMod p) U]
    (hD : LemmaTwoSevenData p G H B h) (h4 : Module.finrank (ZMod p) U = 4)
    {P : Submodule (ZMod p) U} (hPle : P ≤ HardMathSupport.Kantor79.commutatorSpace B)
    (hPne : P ≠ ⊥) (hPfin : P ≠ HardMathSupport.Kantor79.commutatorSpace B)
    (hinv : ∀ g ∈ B, ∀ x ∈ P, g x ∈ P) : False := by
  have hsplitB : SplitSupport B 3 := by simpa [h4] using hD.split.2.2.1
  rcases hsplitB.2.2 P bot_le hPle hinv with hbot | htop
  · exact hPne hbot
  · exact hPfin htop

private theorem mem_span_e2_of_polar_eq_zero (hp : p ≠ 2) {Q₂ : QuadraticForm (ZMod p) U} {y : U}
    (h12 : QuadraticMap.polar Q₂ (e 1) (e 2) = 0)
    (h1y : QuadraticMap.polar Q₂ (e 1) y = 0)
    (h2y : QuadraticMap.polar Q₂ (e 2) y = 0) (hQy : Q₂ y ≠ 0)
    {w₀ w' : U} (hP1 : w₀ ∈ Submodule.span (ZMod p) ({e 1, y} : Set U))
    (he1 : w₀ ∉ Submodule.span (ZMod p) ({e 1} : Set U))
    (hP2' : w' ∈ Submodule.span (ZMod p) ({e 2, y} : Set U))
    (hβ : QuadraticMap.polar Q₂ w₀ w' = 0) :
    w' ∈ Submodule.span (ZMod p) ({e 2} : Set U) := by
  obtain ⟨a, c, hw₀eq⟩ := Submodule.mem_span_pair.mp hP1
  obtain ⟨b, c', hw'eq⟩ := Submodule.mem_span_pair.mp hP2'
  have hc : c ≠ 0 := by
    rintro rfl
    apply he1
    rw [← hw₀eq, zero_smul, add_zero]
    exact Submodule.mem_span_singleton.mpr ⟨a, rfl⟩
  rw [← hw₀eq, ← hw'eq, polar_pair_coord h12 h1y h2y] at hβ
  have hc' : c' = 0 := by
    rcases mul_eq_zero.mp hβ with h | h
    · exact (mul_eq_zero.mp h).resolve_left hc
    · exact absurd h (mul_ne_zero (ZMod.prime_ne_zero p 2 hp) hQy)
  rw [← hw'eq, hc', zero_smul, add_zero]
  exact Submodule.mem_span_singleton.mpr ⟨b, rfl⟩

private theorem root_conj_mem_span_e2 (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {Q₂ : QuadraticForm (ZMod p) U} {y : U}
    (hQ₂ : (QuadraticMap.polarBilin Q₂).Nondegenerate) (hBQ : ∀ g ∈ B, IsIsom p Q₂ g)
    (h12 : QuadraticMap.polar Q₂ (e 1) (e 2) = 0)
    (h1y : QuadraticMap.polar Q₂ (e 1) y = 0)
    (h2y : QuadraticMap.polar Q₂ (e 2) y = 0) (hQy : Q₂ y ≠ 0)
    {t₀ : U ≃ₗ[ZMod p] U} (ht₀B : t₀ ∈ B) (ht₀r : IsRefl p t₀) {w₀ : U}
    (hw₀ : w₀ ∈ HardMathSupport.Kantor79.movedSpace t₀) (hQw₀ : Q₂ w₀ ≠ 0)
    (hP1 : w₀ ∈ Submodule.span (ZMod p) ({e 1, y} : Set U))
    (hP2 : w₀ ∉ Submodule.span (ZMod p) ({e 2, y} : Set U))
    (he1 : w₀ ∉ Submodule.span (ZMod p) ({e 1} : Set U))
    {t' : U ≃ₗ[ZMod p] U} (ht'B : t' ∈ B) (ht'r : IsRefl p t') {w' : U}
    (hw' : w' ∈ HardMathSupport.Kantor79.movedSpace t')
    (hP2' : w' ∈ Submodule.span (ZMod p) ({e 2, y} : Set U))
    (hP1' : w' ∉ Submodule.span (ZMod p) ({e 1, y} : Set U))
    (hconj : ∀ z ∈ HardMathSupport.Kantor79.movedSpace (t₀ * t' * t₀⁻¹),
      z ∈ Submodule.span (ZMod p) ({e 1, y} : Set U) ∨
        z ∈ Submodule.span (ZMod p) ({e 2, y} : Set U)) :
    w' ∈ Submodule.span (ZMod p) ({e 2} : Set U) := by
  have ht₀w₀ : t₀ w₀ = -w₀ := HardMathSupport.Kantor79.apply_eq_neg_of_mem_movedSpace ht₀r.1 hw₀
  have ht₀eq : t₀ = CFSG.ClassicalGroups.Orthogonal.reflect Q₂ w₀ :=
    eq_reflect_of_isRefl_isIsom hp hQ₂ ht₀r (hBQ t₀ ht₀B) hQw₀ ht₀w₀
  have huB : t₀ * t' * t₀⁻¹ ∈ B := B.mul_mem (B.mul_mem ht₀B ht'B) (B.inv_mem ht₀B)
  have hur : IsRefl p (t₀ * t' * t₀⁻¹) := IsRefl.conj ht'r t₀
  have huw : t₀ w' ∈ HardMathSupport.Kantor79.movedSpace (t₀ * t' * t₀⁻¹) :=
    apply_mem_movedSpace_conj hw'
  have hplane := hconj (t₀ w') huw
  have ht₀w' : t₀ w' = w' - (QuadraticMap.polar Q₂ w₀ w' / Q₂ w₀) • w₀ := by
    rw [ht₀eq, CFSG.ClassicalGroups.Orthogonal.reflect_apply hQw₀]
  have hβ : QuadraticMap.polar Q₂ w₀ w' = 0 := by
    by_contra hβne
    have hκ : QuadraticMap.polar Q₂ w₀ w' / Q₂ w₀ ≠ 0 := div_ne_zero hβne hQw₀
    rcases hplane with hP | hL
    · exact hP1' (by
        have heq : w' = t₀ w' + (QuadraticMap.polar Q₂ w₀ w' / Q₂ w₀) • w₀ := by
          rw [ht₀w']; abel
        rw [heq]
        exact Submodule.add_mem _ hP (Submodule.smul_mem _ _ hP1))
    · apply hP2
      have h2 : w₀ = (QuadraticMap.polar Q₂ w₀ w' / Q₂ w₀)⁻¹ • (w' - t₀ w') := by
        rw [show (QuadraticMap.polar Q₂ w₀ w' / Q₂ w₀)⁻¹ • (w' - t₀ w') =
          (QuadraticMap.polar Q₂ w₀ w' / Q₂ w₀)⁻¹ •
            ((QuadraticMap.polar Q₂ w₀ w' / Q₂ w₀) • w₀) from by rw [ht₀w']; abel_nf, smul_smul,
          inv_mul_cancel₀ hκ, one_smul]
      rw [h2]
      exact Submodule.smul_mem _ _ (Submodule.sub_mem _ hP2' hL)
  exact mem_span_e2_of_polar_eq_zero hp h12 h1y h2y hQy hP1 he1 hP2' hβ

private theorem polar_eq_zero_of_span_e2_span_e1_y {Q₂ : QuadraticForm (ZMod p) U} {y : U}
    (h21 : QuadraticMap.polar Q₂ (e 2) (e 1) = 0)
    (h2y : QuadraticMap.polar Q₂ (e 2) y = 0) :
    ∀ w ∈ Submodule.span (ZMod p) ({e 2} : Set U),
      ∀ x ∈ Submodule.span (ZMod p) ({e 1, y} : Set U), QuadraticMap.polar Q₂ w x = 0 := by
  intro w hw x hx
  obtain ⟨mu, rfl⟩ := Submodule.mem_span_singleton.mp hw
  rw [ClassicalGroups.Orthogonal.polar_smul_left_eq, polar_e2_eq_zero_of_mem_span_e1_y h21 h2y hx,
    mul_zero]

private theorem polar_eq_zero_of_span_e1_span_e2_y {Q₂ : QuadraticForm (ZMod p) U} {y : U}
    (h12 : QuadraticMap.polar Q₂ (e 1) (e 2) = 0)
    (h1y : QuadraticMap.polar Q₂ (e 1) y = 0) :
    ∀ w ∈ Submodule.span (ZMod p) ({e 1} : Set U),
      ∀ x ∈ Submodule.span (ZMod p) ({e 2, y} : Set U), QuadraticMap.polar Q₂ w x = 0 := by
  intro w hw x hx
  obtain ⟨mu, rfl⟩ := Submodule.mem_span_singleton.mp hw
  rw [ClassicalGroups.Orthogonal.polar_smul_left_eq, polar_e1_eq_zero_of_mem_span_e2_y h12 h1y hx,
    mul_zero]

private theorem roots_mem_span_e1_y_or_e2 (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {Q₂ : QuadraticForm (ZMod p) U} (hQ₂ : (QuadraticMap.polarBilin Q₂).Nondegenerate)
    (hBQ : ∀ g ∈ B, IsIsom p Q₂ g) {y : U}
    (h12 : QuadraticMap.polar Q₂ (e 1) (e 2) = 0)
    (h1y : QuadraticMap.polar Q₂ (e 1) y = 0)
    (h2y : QuadraticMap.polar Q₂ (e 2) y = 0) (hQy : Q₂ y ≠ 0)
    {t₀ : U ≃ₗ[ZMod p] U} (ht₀B : t₀ ∈ B) (ht₀r : IsRefl p t₀) {w₀ : U}
    (hw₀ : w₀ ∈ HardMathSupport.Kantor79.movedSpace t₀) (hQw₀ : Q₂ w₀ ≠ 0)
    (hP1 : w₀ ∈ Submodule.span (ZMod p) ({e 1, y} : Set U))
    (hP2 : w₀ ∉ Submodule.span (ZMod p) ({e 2, y} : Set U))
    (he1 : w₀ ∉ Submodule.span (ZMod p) ({e 1} : Set U))
    (hrootA : ∀ t ∈ B, IsRefl p t → ∀ z ∈ HardMathSupport.Kantor79.movedSpace t,
      z ∈ Submodule.span (ZMod p) ({e 1, y} : Set U) ∨
        z ∈ Submodule.span (ZMod p) ({e 2, y} : Set U)) :
    ∀ t ∈ B, IsRefl p t → ∀ z ∈ HardMathSupport.Kantor79.movedSpace t,
      z ∈ Submodule.span (ZMod p) ({e 1, y} : Set U) ∨
        z ∈ Submodule.span (ZMod p) ({e 2} : Set U) := by
  intro t htB htr z hz
  obtain ⟨w, hQw, htw⟩ := DimThree.exists_root_of_isRefl_isIsom hp hQ₂ htr (hBQ t htB)
  have hwmem : w ∈ HardMathSupport.Kantor79.movedSpace t :=
    HardMathSupport.Kantor79.mem_movedSpace_of_apply_eq_neg (ZMod.prime_ne_zero p 2 hp) htw
  have hspan_t : HardMathSupport.Kantor79.movedSpace t = ZMod p ∙ w :=
    IsRefl.movedSpace_eq_span hp htr htw (fun h => hQw (by rw [h]; exact map_zero Q₂))
  obtain ⟨lam, hlam⟩ := Submodule.mem_span_singleton.mp (hspan_t ▸ hz)
  have hwplane : w ∈ Submodule.span (ZMod p) ({e 1, y} : Set U) ∨
      w ∈ Submodule.span (ZMod p) ({e 2} : Set U) := by
    rcases hrootA t htB htr w hwmem with hP | hL
    · exact Or.inl hP
    · by_cases hP : w ∈ Submodule.span (ZMod p) ({e 1, y} : Set U)
      · exact Or.inl hP
      · refine Or.inr (root_conj_mem_span_e2 hp hQ₂ hBQ h12 h1y h2y hQy ht₀B ht₀r hw₀ hQw₀
          hP1 hP2 he1 htB htr hwmem hL hP ?_)
        exact fun z hz => hrootA _ (B.mul_mem (B.mul_mem ht₀B htB) (B.inv_mem ht₀B))
          (IsRefl.conj htr t₀) z hz
  rcases hwplane with hP | hL
  · exact Or.inl (hlam ▸ Submodule.smul_mem _ _ hP)
  · exact Or.inr (hlam ▸ Submodule.smul_mem _ _ hL)

private theorem roots_mem_span_e2_y_or_e1 {y : U}
    (hnotA : ∀ t ∈ B, IsRefl p t → ∀ z ∈ HardMathSupport.Kantor79.movedSpace t,
      z ∈ Submodule.span (ZMod p) ({e 1, y} : Set U) →
      z ∈ Submodule.span (ZMod p) ({e 2, y} : Set U) ∨
        z ∈ Submodule.span (ZMod p) ({e 1} : Set U))
    (hrootA : ∀ t ∈ B, IsRefl p t → ∀ z ∈ HardMathSupport.Kantor79.movedSpace t,
      z ∈ Submodule.span (ZMod p) ({e 1, y} : Set U) ∨
        z ∈ Submodule.span (ZMod p) ({e 2, y} : Set U)) :
    ∀ t ∈ B, IsRefl p t → ∀ z ∈ HardMathSupport.Kantor79.movedSpace t,
      z ∈ Submodule.span (ZMod p) ({e 2, y} : Set U) ∨
        z ∈ Submodule.span (ZMod p) ({e 1} : Set U) := by
  intro t htB htr z hz
  rcases hrootA t htB htr z hz with hP1 | hP2
  · exact hnotA t htB htr z hz hP1
  · exact Or.inl hP2

private theorem false_of_caseA (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hD : LemmaTwoSevenData p G H B h) (h4 : Module.finrank (ZMod p) U = 4)
    {Q₂ : QuadraticForm (ZMod p) U} (hQ₂ : (QuadraticMap.polarBilin Q₂).Nondegenerate)
    (hBQ : ∀ g ∈ B, IsIsom p Q₂ g) {y : U}
    (h12 : QuadraticMap.polar Q₂ (e 1) (e 2) = 0)
    (h1y : QuadraticMap.polar Q₂ (e 1) y = 0)
    (h2y : QuadraticMap.polar Q₂ (e 2) y = 0) (hQy : Q₂ y ≠ 0)
    (he1_0 : e 1 ≠ 0) (hye1 : y ∉ Submodule.span (ZMod p) ({e 1} : Set U))
    (he1B : e 1 ∈ HardMathSupport.Kantor79.commutatorSpace B)
    (hyB : y ∈ HardMathSupport.Kantor79.commutatorSpace B)
    (hrootA : ∀ t ∈ B, IsRefl p t → ∀ z ∈ HardMathSupport.Kantor79.movedSpace t,
      z ∈ Submodule.span (ZMod p) ({e 1, y} : Set U) ∨
        z ∈ Submodule.span (ZMod p) ({e 2, y} : Set U))
    {t₀ : U ≃ₗ[ZMod p] U} (ht₀B : t₀ ∈ B) (ht₀r : IsRefl p t₀) {w₀ : U}
    (hw₀ : w₀ ∈ HardMathSupport.Kantor79.movedSpace t₀) (hQw₀ : Q₂ w₀ ≠ 0)
    (hP1 : w₀ ∈ Submodule.span (ZMod p) ({e 1, y} : Set U))
    (hP2 : w₀ ∉ Submodule.span (ZMod p) ({e 2, y} : Set U))
    (he1 : w₀ ∉ Submodule.span (ZMod p) ({e 1} : Set U)) : False := by
  have h21 : QuadraticMap.polar Q₂ (e 2) (e 1) = 0 := by
    rw [QuadraticMap.polar_comm]; exact h12
  have hinv := invariant_of_roots hp hQ₂ hBQ hD.split.2.1
    (P := Submodule.span (ZMod p) ({e 1, y} : Set U))
    (L := Submodule.span (ZMod p) ({e 2} : Set U))
    (polar_eq_zero_of_span_e2_span_e1_y h21 h2y)
    (roots_mem_span_e1_y_or_e2 hp hQ₂ hBQ h12 h1y h2y hQy ht₀B ht₀r hw₀ hQw₀ hP1 hP2 he1 hrootA)
  have hPle : Submodule.span (ZMod p) ({e 1, y} : Set U) ≤
      HardMathSupport.Kantor79.commutatorSpace B := by
    refine Submodule.span_le.mpr ?_
    rintro z (rfl | rfl)
    · exact he1B
    · exact hyB
  have hPne : Submodule.span (ZMod p) ({e 1, y} : Set U) ≠ ⊥ := by
    intro hbot
    have hmem : e 1 ∈ Submodule.span (ZMod p) ({e 1, y} : Set U) :=
      Submodule.subset_span (by simp)
    rw [hbot] at hmem
    exact he1_0 (by simpa using hmem)
  have hPfin : Submodule.span (ZMod p) ({e 1, y} : Set U) ≠
      HardMathSupport.Kantor79.commutatorSpace B := by
    intro heq
    have h1 : Module.finrank (ZMod p) (Submodule.span (ZMod p) ({e 1, y} : Set U)) = 2 :=
      finrank_span_pair_of_notMem he1_0 hye1
    have h2 : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace B) = 3 := by
      have := hD.split.2.2.1.2.1
      omega
    rw [heq, h2] at h1
    omega
  exact false_of_invariant_plane hD h4 hPle hPne hPfin hinv

private theorem false_of_caseB (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hD : LemmaTwoSevenData p G H B h) (h4 : Module.finrank (ZMod p) U = 4)
    {Q₂ : QuadraticForm (ZMod p) U} (hQ₂ : (QuadraticMap.polarBilin Q₂).Nondegenerate)
    (hBQ : ∀ g ∈ B, IsIsom p Q₂ g) {y : U}
    (h12 : QuadraticMap.polar Q₂ (e 1) (e 2) = 0)
    (h1y : QuadraticMap.polar Q₂ (e 1) y = 0)
    (he2_0 : e 2 ≠ 0) (hye2 : y ∉ Submodule.span (ZMod p) ({e 2} : Set U))
    (he2B : e 2 ∈ HardMathSupport.Kantor79.commutatorSpace B)
    (hyB : y ∈ HardMathSupport.Kantor79.commutatorSpace B)
    (hrootB : ∀ t ∈ B, IsRefl p t → ∀ z ∈ HardMathSupport.Kantor79.movedSpace t,
      z ∈ Submodule.span (ZMod p) ({e 2, y} : Set U) ∨
        z ∈ Submodule.span (ZMod p) ({e 1} : Set U)) : False := by
  have hinv := invariant_of_roots hp hQ₂ hBQ hD.split.2.1
    (P := Submodule.span (ZMod p) ({e 2, y} : Set U))
    (L := Submodule.span (ZMod p) ({e 1} : Set U))
    (polar_eq_zero_of_span_e1_span_e2_y h12 h1y) hrootB
  have hPle : Submodule.span (ZMod p) ({e 2, y} : Set U) ≤
      HardMathSupport.Kantor79.commutatorSpace B := by
    refine Submodule.span_le.mpr ?_
    rintro z (rfl | rfl)
    · exact he2B
    · exact hyB
  have hPne : Submodule.span (ZMod p) ({e 2, y} : Set U) ≠ ⊥ := by
    intro hbot
    have hmem : e 2 ∈ Submodule.span (ZMod p) ({e 2, y} : Set U) :=
      Submodule.subset_span (by simp)
    rw [hbot] at hmem
    exact he2_0 (by simpa using hmem)
  have hPfin : Submodule.span (ZMod p) ({e 2, y} : Set U) ≠
      HardMathSupport.Kantor79.commutatorSpace B := by
    intro heq
    have h1 : Module.finrank (ZMod p) (Submodule.span (ZMod p) ({e 2, y} : Set U)) = 2 :=
      finrank_span_pair_of_notMem he2_0 hye2
    have h2 : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace B) = 3 := by
      have := hD.split.2.2.1.2.1
      omega
    rw [heq, h2] at h1
    omega
  exact false_of_invariant_plane hD h4 hPle hPne hPfin hinv

private theorem not_caseA_roots (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {Q₂ : QuadraticForm (ZMod p) U} (hQ₂ : (QuadraticMap.polarBilin Q₂).Nondegenerate)
    (hBQ : ∀ g ∈ B, IsIsom p Q₂ g) {y : U}
    (hcase : ¬ ∃ (t₀ : U ≃ₗ[ZMod p] U) (w₀ : U), t₀ ∈ B ∧ IsRefl p t₀ ∧
      w₀ ∈ HardMathSupport.Kantor79.movedSpace t₀ ∧ Q₂ w₀ ≠ 0 ∧
      w₀ ∈ Submodule.span (ZMod p) ({e 1, y} : Set U) ∧
      w₀ ∉ Submodule.span (ZMod p) ({e 2, y} : Set U) ∧
      w₀ ∉ Submodule.span (ZMod p) ({e 1} : Set U)) :
    ∀ t ∈ B, IsRefl p t → ∀ z ∈ HardMathSupport.Kantor79.movedSpace t,
      z ∈ Submodule.span (ZMod p) ({e 1, y} : Set U) →
      z ∈ Submodule.span (ZMod p) ({e 2, y} : Set U) ∨
        z ∈ Submodule.span (ZMod p) ({e 1} : Set U) := by
  intro t htB htr z hz hP1
  by_cases hP2 : z ∈ Submodule.span (ZMod p) ({e 2, y} : Set U)
  · exact Or.inl hP2
  · by_cases h1 : z ∈ Submodule.span (ZMod p) ({e 1} : Set U)
    · exact Or.inr h1
    · exfalso
      apply hcase
      have hz0 : z ≠ 0 := fun h => hP2 (h ▸ Submodule.zero_mem _)
      exact ⟨t, z, htB, htr, hz, Q2_ne_zero_of_mem_movedSpace hp hQ₂ hBQ htB htr hz hz0,
        hP1, hP2, h1⟩

private theorem false_of_frame (hp : p ≠ 2) (hp5 : p = 5) [Module.Finite (ZMod p) U]
    (hD : LemmaTwoSevenData p G H B h) (h4 : Module.finrank (ZMod p) U = 4) (hr : r 0 = h)
    (hT : IsCyclicRootTriple p H r e s) {Q₁ Q₂ : QuadraticForm (ZMod p) U}
    (hQ₁ : (QuadraticMap.polarBilin Q₁).Nondegenerate) (hoH : IsOrthOn p Q₁ H)
    (hA : Q₁ (e 0) ≠ 0) (hQe : ∀ i, Q₁ (e i) = Q₁ (e 0))
    (hrapp : ∀ i j, r i (e j) = if i = j then -e j else e j)
    (hrmem : ∀ i, i ≠ 0 → r i ∈ reflStab p H h)
    (hcomm : HardMathSupport.Kantor79.commutatorSpace (reflStab p H h) =
      Submodule.span (ZMod p) {e 1, e 2})
    (hQ₂ : (QuadraticMap.polarBilin Q₂).Nondegenerate) (hBQ : ∀ g ∈ B, IsIsom p Q₂ g)
    (hne : Q₂ (e 2) ≠ Q₂ (e 1)) : False := by
  obtain ⟨y, hy0, hyH, hyB⟩ := exists_mem_centralizerSpace_of_lemmaTwoSevenData hp hD
  have hspan := span_e1_e2_y_eq_commutatorSpace hp (by omega) hD h4 hr hT hQ₁ hoH hcomm
    hyH hy0 hyB
  have h12 := polar_e1_e2_eq_zero hp hD hBQ hrmem hrapp
  obtain ⟨h1y, h2y⟩ := polar_e_y_eq_zero hp hD hT hBQ hrmem hrapp hyH
  have hQ1 := Q2_e_ne_zero hp hD hT hQ₂ hBQ hrmem (i := 1) (by decide)
  have hQ2 := Q2_e_ne_zero hp hD hT hQ₂ hBQ hrmem (i := 2) (by decide)
  have hQy := Q2_y_ne_zero hp hD hr hT hQ₂ hBQ hyB hy0 h1y h2y hspan
  have he1B : e 1 ∈ HardMathSupport.Kantor79.commutatorSpace B :=
    mem_commutatorSpace_of_isCyclicRootTriple hp hD h4 hr hT (i := 1) (by decide)
  have he2B : e 2 ∈ HardMathSupport.Kantor79.commutatorSpace B :=
    mem_commutatorSpace_of_isCyclicRootTriple hp hD h4 hr hT (i := 2) (by decide)
  have hye1 : y ∉ Submodule.span (ZMod p) ({e 1} : Set U) := fun h =>
    y_notMem_span_e1_e2 hD h4 hcomm hyH hy0
      (Submodule.span_mono (by rw [Set.singleton_subset_iff]; simp) h)
  have hye2 : y ∉ Submodule.span (ZMod p) ({e 2} : Set U) := fun h =>
    y_notMem_span_e1_e2 hD h4 hcomm hyH hy0
      (Submodule.span_mono (by rw [Set.singleton_subset_iff]; simp) h)
  have hrootA := roots_mem_planes hp (by omega) hD hT hQ₁ hoH hQ₂ hBQ hA hQe hrmem hne
    hspan h12 h1y h2y hQ1 hQ2
  by_cases hcase : ∃ (t₀ : U ≃ₗ[ZMod p] U) (w₀ : U), t₀ ∈ B ∧ IsRefl p t₀ ∧
      w₀ ∈ HardMathSupport.Kantor79.movedSpace t₀ ∧ Q₂ w₀ ≠ 0 ∧
      w₀ ∈ Submodule.span (ZMod p) ({e 1, y} : Set U) ∧
      w₀ ∉ Submodule.span (ZMod p) ({e 2, y} : Set U) ∧
      w₀ ∉ Submodule.span (ZMod p) ({e 1} : Set U)
  · obtain ⟨t₀, w₀, ht₀B, ht₀r, hw₀, hQw₀, hP1, hP2, he1⟩ := hcase
    exact false_of_caseA hp hD h4 hQ₂ hBQ h12 h1y h2y hQy (hT.2.2.1.ne_zero 1) hye1 he1B hyB
      hrootA ht₀B ht₀r hw₀ hQw₀ hP1 hP2 he1
  · exact false_of_caseB hp hD h4 hQ₂ hBQ h12 h1y (hT.2.2.1.ne_zero 2) hye2 he2B hyB
      (roots_mem_span_e2_y_or_e1 (not_caseA_roots hp hQ₂ hBQ hcase) hrootA)

theorem eq_of_isIsom_of_isCyclicRootTriple (hp5 : p = 5) [Module.Finite (ZMod p) U]
    (hD : LemmaTwoSevenData p G H B h) (h4 : Module.finrank (ZMod p) U = 4)
    {r : Fin 3 → U ≃ₗ[ZMod p] U} {e : Fin 3 → U} {s : U ≃ₗ[ZMod p] U} (hr : r 0 = h)
    (hT : IsCyclicRootTriple p H r e s) {Q₂ : QuadraticForm (ZMod p) U}
    (hQ₂ : (QuadraticMap.polarBilin Q₂).Nondegenerate) (hBQ : ∀ g ∈ B, IsIsom p Q₂ g) :
    Q₂ (e 2) = Q₂ (e 1) := by
  by_contra hne
  obtain ⟨Q₁, hQ₁, hoH, hA, hQe, horth, hrapp, hrmem, hcomm⟩ :=
    exists_frame_of_isCyclicRootTriple (by omega : p ≠ 2) hD h4 hr hT
  exact false_of_frame (by omega) hp5 hD h4 hr hT hQ₁ hoH hA hQe hrapp hrmem hcomm hQ₂ hBQ hne

theorem exists_eq_mul_of_isCyclicRootTriple (hp5 : p = 5) [Module.Finite (ZMod p) U]
    (hD : LemmaTwoSevenData p G H B h) (h4 : Module.finrank (ZMod p) U = 4)
    {r : Fin 3 → U ≃ₗ[ZMod p] U} {e : Fin 3 → U} {s : U ≃ₗ[ZMod p] U} (hr : r 0 = h)
    (hT : IsCyclicRootTriple p H r e s)
    (hψ : ∃ Q₂ : QuadraticForm (ZMod p) U, (QuadraticMap.polarBilin Q₂).Nondegenerate ∧
      ∀ g ∈ B, IsIsom p Q₂ g) :
    ∃ Q₁ Q₂ : QuadraticForm (ZMod p) U, (QuadraticMap.polarBilin Q₁).Nondegenerate ∧
      IsOrthOn p Q₁ H ∧ (QuadraticMap.polarBilin Q₂).Nondegenerate ∧ (∀ g ∈ B, IsIsom p Q₂ g) ∧
      ∃ c : ZMod p, c ≠ 0 ∧
        ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace (reflStab p H h), Q₂ v = c * Q₁ v := by
  obtain ⟨Q₂, hQ₂, hBQ⟩ := hψ
  obtain ⟨Q₁, hQ₁, hoH, hA, hQe, horth, hrapp, hrmem, hcomm⟩ :=
    exists_frame_of_isCyclicRootTriple (by omega : p ≠ 2) hD h4 hr hT
  have hp2 : p ≠ 2 := by omega
  have h12 : QuadraticMap.polar Q₂ (e 1) (e 2) = 0 :=
    polar_e1_e2_eq_zero hp2 hD hBQ hrmem hrapp
  have hQ2e1 : Q₂ (e 1) ≠ 0 := Q2_e_ne_zero hp2 hD hT hQ₂ hBQ hrmem (i := 1) (by decide)
  have hqe : Q₂ (e 2) = Q₂ (e 1) :=
    eq_of_isIsom_of_isCyclicRootTriple (r := r) (e := e) (s := s) hp5 hD h4 hr hT hQ₂ hBQ
  have hval : ∀ {Q : QuadraticForm (ZMod p) U} {x y : ZMod p},
      QuadraticMap.polar Q (e 1) (e 2) = 0 → Q (e 2) = Q (e 1) →
      Q (x • e 1 + y • e 2) = (x ^ 2 + y ^ 2) * Q (e 1) := by
    intro Q x y hpol heq
    rw [QuadraticMap.map_add Q (x • e 1) (y • e 2),
      ClassicalGroups.Orthogonal.map_smul_eq_sq,
      ClassicalGroups.Orthogonal.map_smul_eq_sq,
      ClassicalGroups.Orthogonal.polar_smul_left_eq,
      ClassicalGroups.Orthogonal.polar_smul_right_eq, hpol, heq]
    ring
  refine ⟨Q₁, Q₂, hQ₁, hoH, hQ₂, hBQ, Q₂ (e 1) / Q₁ (e 0), div_ne_zero hQ2e1 hA, ?_⟩
  intro v hv
  rw [hcomm] at hv
  obtain ⟨x, y, hxy⟩ := Submodule.mem_span_pair.mp hv
  have hQ2v : Q₂ (x • e 1 + y • e 2) = (x ^ 2 + y ^ 2) * Q₂ (e 1) := hval h12 hqe
  have hQ1v : Q₁ (x • e 1 + y • e 2) = (x ^ 2 + y ^ 2) * Q₁ (e 1) :=
    hval (horth 1 2 (by decide)) (by rw [hQe 2, ← hQe 1])
  rw [← hxy, hQ2v, hQ1v, hQe 1]
  field_simp

end CFSG.StandardType.ZS

end

