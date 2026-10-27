module

public import CFSG.OddTranspositions.PartThree.Twelve.ElevenFiveChart
import CFSG.OddTranspositions.PartThree.Twelve.ElevenFiveOverlap
import CFSG.OddTranspositions.PartThree.Twelve.ElevenFiveFusion
import CFSG.OddTranspositions.PartThree.Twelve.TenFive
import CFSG.OddTranspositions.PartThree.Twelve.SixFive
public import CFSG.OddTranspositions.PartThree.Twelve.SevenFive
public import CFSG.OddTranspositions.O4CloseReduction
import CFSG.OddTranspositions.PartThree.Twelve.Four
import CFSG.OddTranspositions.PartThree.Twelve.FiveCount
import CFSG.OddTranspositions.PartThree.Nine.Setup
import CFSG.OddTranspositions.PartFour.Fourteen.RootBlockFive

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72 CFSG.OddTranspositions.PartFour
  Matrix

variable {G : Type} [Group G] [Finite G] {D : Set G}

omit [Finite G] in
theorem halpha_eq_closure_commSet (hC : HypothesisC D) (hα : hC.alpha = {hC.d}) :
    Halpha D hC.alpha = Subgroup.closure (commSet D hC.d) := by
  rw [Halpha, CFSG.OddTranspositions.PartThree.Nine.DalphaStar_eq_commSet hC hα]

theorem alpha_eq_singleton_five (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    {k : ℕ} (hk : 4 ≤ k) {ε π : Bool} (h5 : IsFiveReflectionModel k ε π (imageClass hC)) :
    hC.alpha = {hC.d} := by
  have hcls := imageClass_isClass hC
  obtain ⟨s, hs⟩ := imageClass_nonempty hC
  obtain ⟨hb1, hne⟩ := subset_rootBlock_and_ne_of_isFiveReflectionModel hcls hk h5 hs
  exact alpha_eq_singleton_of_rootBlock_eq_singleton hC hMZ hs hb1 hne
    (rootBlock_eq_singleton_of_isFiveReflectionModel hcls hk h5 hs)

section Certs


theorem fiveLocalModel_of_center (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hα : hC.alpha = {hC.d}) {k : ℕ} (hk : 4 ≤ k) {ε π : Bool}
    (h5 : IsFiveReflectionModel k ε π (imageClass hC))
    (hcen : ∀ z ∈ Subgroup.center (Halpha D hC.alpha), (z : G) = 1 ∨ (z : G) = hC.d) :
    Nonempty (FiveLocalModel D hC.d k ε π) := by
  obtain ⟨φ, hφ⟩ := h5
  have hφ' : IsFiveMarking hC k ε π φ := fun x => by
    rw [hφ x]
    constructor
    · rintro ⟨r, hr, e⟩
      exact ⟨r, hr, e.symm⟩
    · rintro ⟨r, hr, e⟩
      exact ⟨r, hr, e.symm⟩
  obtain ⟨-, θ, -, hθ2, -⟩ := twelveTen_five_center hC hMZ hk hφ' hcen
  have hH := halpha_eq_closure_commSet hC hα
  let e : Subgroup.closure (commSet D hC.d) ≃* Halpha D hC.alpha :=
    MulEquiv.subgroupCongr hH.symm
  refine ⟨⟨e.trans θ, fun y => ?_⟩⟩
  have h1 := hθ2 (e y)
  rw [mem_DstarH_iff, CFSG.OddTranspositions.PartThree.Nine.DalphaStar_eq_commSet hC hα] at h1
  exact h1

end Certs

theorem not_o4PairData_five (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hα : hC.alpha = {hC.d}) {k : ℕ} (hk : 4 ≤ k)
    {ε π : Bool} (h5 : IsFiveReflectionModel k ε π (imageClass hC)) :
    ¬ CFSG.OddTranspositions.QZ.O4PairData G D := by
  obtain ⟨c⟩ := exists_fiveChart hC hMZ hα hk h5
  exact c.not_o4PairData (by omega)

private theorem fiveForm_eq_fiveSignRep_mul_fiveBilin (k : ℕ) (ε π : Bool)
    (z : Fin (k + 1) → ZMod 5) :
    fiveForm k ε z z = fiveSignRep π * fiveBilin k ε π z z := by
  rw [fiveBilin_apply, ← mul_assoc, five_mul_inv_cancel (fiveSignRep_ne_zero π), one_mul]

private theorem isSquare_two_mul_fiveSignRep (π : Bool) :
    IsSquare (2 * fiveSignRep π) ↔ π = false := by
  cases π <;> decide

private theorem fiveHyperplane_norm_of_ite (k : ℕ) (ε π : Bool) {m : ℕ}
    {z : Fin (k + 1) → ZMod 5}
    (hb : if m = 5 then fiveBilin k ε π z z = 0 else fiveBilin k ε π z z = 2) :
    (if m = 5 then fiveForm k ε z z = 0
      else fiveForm k ε z z ≠ 0 ∧ (IsSquare (fiveForm k ε z z) ↔ π = false)) := by
  by_cases h : m = 5
  · rw [if_pos h] at hb ⊢
    rw [fiveForm_eq_fiveSignRep_mul_fiveBilin, hb, mul_zero]
  · rw [if_neg h] at hb ⊢
    rw [fiveForm_eq_fiveSignRep_mul_fiveBilin, hb]
    have h2 : (2 : ZMod 5) ≠ 0 := by decide
    refine ⟨?_, ?_⟩
    · rw [mul_comm]
      exact mul_ne_zero h2 (fiveSignRep_ne_zero π)
    · rw [mul_comm]
      exact isSquare_two_mul_fiveSignRep π

private theorem sub_smul_eq_self_iff {m : ℕ} {z v : Fin m → ZMod 5} (hv : v ≠ 0)
    (a : ZMod 5) : z - a • v = z ↔ a = 0 := by
  rw [sub_eq_self, smul_eq_zero]
  simp [hv]

theorem fiveHyperplaneData_of_twelveSix (hC : HypothesisC D)
    (hα : hC.alpha = {hC.d}) {k : ℕ} (hk : 4 ≤ k) {ε π : Bool}
    (hdiam : ∀ w ∈ D, ¬ Commute w hC.d → (commSet D hC.d ∩ commSet D w).Nonempty)
    (hcen : ∀ z ∈ Subgroup.center (Halpha D hC.alpha), (z : G) = 1 ∨ (z : G) = hC.d)
    (c : FiveLocalModel D hC.d k ε π) : FiveHyperplaneData c := by
  have hH : Halpha D hC.alpha = Subgroup.closure (commSet D hC.d) :=
    halpha_eq_closure_commSet hC hα
  let θ : Halpha D hC.alpha ≃* fiveReflectionGroup k ε π :=
    (MulEquiv.subgroupCongr hH).trans c.toMulEquiv
  have hθ : ∀ x, x ∈ DstarH hC ↔
      (θ x : GL (Fin (k + 1)) (ZMod 5)) ∈ fiveReflections k ε π := by
    intro x
    rw [mem_DstarH_iff, CFSG.OddTranspositions.PartThree.Nine.DalphaStar_eq_commSet hC hα]
    have h := c.mem_iff ((MulEquiv.subgroupCongr hH) x)
    rw [show (((MulEquiv.subgroupCongr hH) x :
      Subgroup.closure (commSet D hC.d)) : G) = (x : G) from rfl] at h
    exact h
  obtain ⟨ch, hb, hact⟩ := exists_fiveChart_of_mulEquiv hC hα θ hθ
  intro s hs hsd
  obtain ⟨z, hz0, hznorm, hzcomm⟩ := twelveSix_five hC hα hk hdiam hcen ch hs hsd
  refine ⟨z, hz0, ?_, ?_⟩
  · exact fiveHyperplane_norm_of_ite (m := orderOf (hC.d * s)) k ε π (by rw [← hb]; exact hznorm)
  · intro y hy
    have hvne : ch.vec (y : G) ≠ 0 := by
      intro h0
      have h1 : fiveBilin k ε π (ch.vec (y : G)) (ch.vec (y : G)) = 1 := by
        simpa [hb] using ch.norm_vec (y : G) hy
      rw [h0] at h1
      simp at h1
    have hθcoe : (θ ⟨(y : G), mem_Halpha_of_mem_commSet hC hα hy⟩ :
        GL (Fin (k + 1)) (ZMod 5)) = (c.toMulEquiv y : GL (Fin (k + 1)) (ZMod 5)) := rfl
    have hfix : ((c.toMulEquiv y : GL (Fin (k + 1)) (ZMod 5)) :
        Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ z = z ↔
        fiveBilin k ε π z (ch.vec (y : G)) = 0 := by
      rw [← hθcoe, hact (y : G) hy z,
        sub_smul_eq_self_iff hvne (2 * fiveBilin k ε π z (ch.vec (y : G)))]
      constructor
      · intro h
        exact (mul_eq_zero.mp h).resolve_left (by decide)
      · intro h
        rw [h, mul_zero]
    rw [hzcomm (y : G) hy, hb, fiveBilin_comm]
    exact hfix.symm

omit [Finite G] in
theorem exists_hnbr_five (hC : HypothesisC D) {k : ℕ} (hk : 4 ≤ k) {ε π : Bool}
    (hD : FiveLocalData D k ε π)
    (hdiam : ∀ w ∈ D, ¬ Commute w hC.d → (commSet D hC.d ∩ commSet D w).Nonempty)
    (hfl : FiveLines D) {w : G} (hw : w ∈ D) (hwd : ¬ Commute w hC.d) :
    ∃ v ∈ commSet D hC.d ∩ commSet D w, ∀ x ∈ lineMem D hC.d w, x ≠ hC.d →
      ∃ g ∈ hypLineGroup D hC.d v, g * w * g⁻¹ = x := by
  obtain ⟨v, hv⟩ := hdiam w hw hwd
  have hvD : v ∈ D := hv.1.1
  obtain ⟨cv⟩ := (hD v hvD).1
  have hdv : hC.d ∈ commSet D v :=
    ⟨hC.hd, hv.1.2.1.symm, fun h => hv.1.2.2 h.symm⟩
  have hwv : w ∈ commSet D v :=
    ⟨hw, hv.2.2.1.symm, fun h => hv.2.2.2 h.symm⟩
  have hdw : ¬ Commute hC.d w := fun h => hwd h.symm
  obtain ⟨-, hcard, hthird⟩ := hfl v hvD hC.d hdv w hwv hdw
  refine ⟨v, hv, fun x hxline hxd => ?_⟩
  have hxmem : x ∈ D ∧ perpMem D hC.d ∩ perpMem D w ⊆ perpMem D x :=
    mem_lineMem.mp hxline
  have hcommv : Commute x v :=
    (hxmem.2 ⟨⟨hv.1.1, hv.1.2.1⟩, ⟨hv.1.1, hv.2.2.1⟩⟩).2.symm
  obtain ⟨hxd', hxeq⟩ := hthird x hxline hxd
  have hxnev : x ≠ v := fun h => hxd' (h ▸ hv.1.2.1)
  have hxv : x ∈ commSet D v := ⟨hxmem.1, hcommv, hxnev⟩
  have hxcard : (lineMem D hC.d x).ncard = orderOf (hC.d * x) :=
    (hfl v hvD hC.d hdv x hxv (fun h => hxd' h.symm)).2.1
  have hord : orderOf (hC.d * w) = orderOf (hC.d * x) := by
    rw [← hcard, ← hxeq, hxcard]
  obtain ⟨g, hg, hgconj⟩ := residualFusion_five hk cv hdv hwv hxv hwd hxd' hord
  exact ⟨g, hg, hgconj⟩

section Certs


theorem centralizer_eq_hypLineGroup_five (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hα : hC.alpha = {hC.d}) {k : ℕ} (hk : 4 ≤ k) {ε π : Bool}
    (h5 : IsFiveReflectionModel k ε π (imageClass hC))
    (hdiam : ∀ w ∈ D, ¬ Commute w hC.d → (commSet D hC.d ∩ commSet D w).Nonempty)
    (hcen : ∀ z ∈ Subgroup.center (Halpha D hC.alpha), (z : G) = 1 ∨ (z : G) = hC.d)
    (hD : FiveLocalData D k ε π) {w : G} (hw : w ∈ D) (hwd : ¬ Commute w hC.d) :
    Subgroup.closure (commSet D hC.d) ⊓ Subgroup.centralizer {w} =
      Subgroup.closure (commSet D hC.d ∩ commSet D w) := by
  obtain ⟨φ, hφ⟩ := id h5
  have hφ' : IsFiveMarking hC k ε π φ := fun x => by
    rw [hφ x]
    constructor
    · rintro ⟨r, hr, e⟩
      exact ⟨r, hr, e.symm⟩
    · rintro ⟨r, hr, e⟩
      exact ⟨r, hr, e.symm⟩
  have hfl := fiveLines_of_isFiveReflectionModel hC hMZ hα hk h5
  have h1 := (twelveTen_five_stabilizers hC hMZ hk hφ' hcen hfl hw hwd
    (fun c => twelveSix_five hC hα hk hdiam hcen c hw hwd)
    (exists_hnbr_five hC hk hD hdiam hfl hw hwd)).1
  rwa [halpha_eq_closure_commSet hC hα] at h1

end Certs

end CFSG.OddTranspositions.PartThree

end
