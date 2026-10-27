module

public import CFSG.OddTranspositions.PartThree.FiveReflection
public import CFSG.OddTranspositions.PartThree.Twelve.TenFiveModelStab
public import CFSG.OddTranspositions.PartThree.Twelve.TenFiveModelCenter
public import CFSG.OddTranspositions.PartThree.Twelve.TenFiveModelChar
public import CFSG.OddTranspositions.PartThree.Twelve.TenFiveModelWalk
public import CFSG.OddTranspositions.PartThree.Twelve.TenFiveModelConj
public import CFSG.OddTranspositions.PartThree.Twelve.TenFiveModelCoset
public import CFSG.Sporadic.Th.Max3.Data

public section

namespace CFSG.OddTranspositions.PartThree

open Matrix

abbrev fiveProjective (k : ℕ) (ε π : Bool) : Type :=
  fiveReflectionGroup k ε π ⧸ Subgroup.center (fiveReflectionGroup k ε π)

theorem exists_frame_of_neg_one_mem {k : ℕ} (hk : 4 ≤ k) {ε π : Bool}
    (hneg : (-1 : GL (Fin (k + 1)) (ZMod 5)) ∈ fiveReflectionGroup k ε π) :
    ∃ r : Fin (k + 1) → GL (Fin (k + 1)) (ZMod 5),
      (∀ i, r i ∈ fiveReflections k ε π) ∧ (∀ i j, Commute (r i) (r j)) ∧
        Function.Injective r ∧ (List.ofFn r).prod = -1 :=
  exists_frame_of_neg_one_mem_aux hk hneg

theorem mem_center_fiveReflectionGroup_iff {k : ℕ} (hk : 4 ≤ k) (ε π : Bool)
    (g : fiveReflectionGroup k ε π) :
    g ∈ Subgroup.center (fiveReflectionGroup k ε π) ↔
      (g : GL (Fin (k + 1)) (ZMod 5)) = 1 ∨ (g : GL (Fin (k + 1)) (ZMod 5)) = -1 := by
  constructor
  · intro hg
    have hcen : ∀ r ∈ fiveReflections k ε π,
        (g : GL (Fin (k + 1)) (ZMod 5)) * r = r * (g : GL (Fin (k + 1)) (ZMod 5)) := by
      intro r hr
      have := Subgroup.mem_center_iff.mp hg
        (⟨r, Subgroup.subset_closure hr⟩ : fiveReflectionGroup k ε π)
      exact (congrArg Subtype.val this).symm
    exact eq_one_or_eq_neg_one_of_mem_center_fiveReflectionGroup k ε π hk g.2 hcen
  · rintro (h | h)
    · exact Subgroup.mem_center_iff.mpr fun x => by
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        rw [h, one_mul, mul_one]
    · have hneg : (-1 : GL (Fin (k + 1)) (ZMod 5)) =
          Matrix.GeneralLinearGroup.scalar (Fin (k + 1)) (-1) :=
        Units.ext (by simp [Matrix.GeneralLinearGroup.scalar])
      exact Subgroup.mem_center_iff.mpr fun x => by
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        rw [h, hneg, Matrix.GeneralLinearGroup.scalar_commute]

theorem isConj_of_mem_fiveReflections {k : ℕ} (hk : 4 ≤ k) (ε π : Bool)
    {r s : GL (Fin (k + 1)) (ZMod 5)} (hr : r ∈ fiveReflections k ε π)
    (hs : s ∈ fiveReflections k ε π) :
    ∃ g ∈ fiveReflectionGroup k ε π, g * r * g⁻¹ = s :=
  isConj_of_mem_fiveReflections_aux hk ε π hr hs

set_option maxHeartbeats 400000 in
theorem mem_closure_fiveReflectionsFixing_iff {k : ℕ} (hk : 4 ≤ k) (ε π : Bool)
    {c : Fin (k + 1) → ZMod 5} (hc : c ≠ 0) (g : GL (Fin (k + 1)) (ZMod 5)) :
    g ∈ Subgroup.closure (fiveReflectionsFixing k ε π c) ↔
      g ∈ fiveReflectionGroup k ε π ∧
        (g : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ c = c := by
  have hLR : Subgroup.closure (fiveReflectionsFixing k ε π c) ≤ fiveReflectionGroup k ε π :=
    (Subgroup.closure_le (fiveReflectionGroup k ε π)).mpr
      (fun r hr => Subgroup.subset_closure hr.1)
  constructor
  · intro hg
    refine ⟨hLR hg, ?_⟩
    refine Subgroup.closure_induction (k := fiveReflectionsFixing k ε π c)
      (p := fun g _ => (g : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ c = c)
      ?_ ?_ ?_ ?_ hg
    · intro r hr; exact hr.2
    · simp
    · intro x y hx hy ihx ihy
      rw [Matrix.GeneralLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, ihy, ihx]
    · intro x hx ihx
      have h := congrArg
        (fun v => ((x⁻¹ : GL (Fin (k + 1)) (ZMod 5)) :
          Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ v) ihx
      rw [Matrix.mulVec_mulVec, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec] at h
      exact h.symm
  · rintro ⟨hgR, hgc⟩
    obtain ⟨l, hl, hprod⟩ := exists_fiveReflOf_list_prod_of_mulVec_eq hk ε hc
      (fiveForm_mulVec_of_mem hgR) hgc
    obtain ⟨u, huQ, huπ, huc⟩ := exists_fiveReflOf_orth_sign_not hk ε π hc
    set r : GL (Fin (k + 1)) (ZMod 5) := fiveReflOf k ε u with hrdef
    have hrpres : ∀ x y, fiveForm k ε
        ((r : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ x)
        ((r : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ y) = fiveForm k ε x y := by
      rw [hrdef]
      exact fiveForm_mulVec_of_mem (π := !π)
        (Subgroup.subset_closure (fiveReflOf_mem huQ huπ))
    have hrc : (r : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ c = c := by
      rw [hrdef, fiveReflOf_mulVec, fiveForm_comm k ε c u, huc, mul_zero, zero_mul, zero_smul]
      simp
    have hru : r * r = 1 := by
      rw [hrdef]
      apply Units.ext
      rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_one]
      exact fiveReflMatrix_mul_self k ε u
    have hrinv : r⁻¹ = r := inv_eq_of_mul_eq_one_right hru
    have hru_not : r ∉ fiveReflectionGroup k ε π := by
      rw [hrdef]; exact fiveReflOf_not_mem_fiveReflectionGroup hk ε π huQ huπ
    set L : Subgroup (GL (Fin (k + 1)) (ZMod 5)) :=
      Subgroup.closure (fiveReflectionsFixing k ε π c) with hLdef
    set L' : Subgroup (GL (Fin (k + 1)) (ZMod 5)) :=
      Subgroup.closure (fiveReflectionsFixing k ε π c ∪ {r}) with hL'def
    have hLR' : L ≤ fiveReflectionGroup k ε π := by
      rw [hLdef]
      exact (Subgroup.closure_le (fiveReflectionGroup k ε π)).mpr
        (fun x hx => Subgroup.subset_closure hx.1)
    have hconj_gen : ∀ s ∈ fiveReflectionsFixing k ε π c,
        r * s * r⁻¹ ∈ fiveReflectionsFixing k ε π c := by
      intro s hs
      obtain ⟨v, hv, hsign, rfl⟩ := exists_eq_fiveReflOf hs.1
      have hsc : fiveForm k ε c v = 0 := by
        have h := hs.2
        rw [fiveReflOf_mulVec] at h
        have hv0 : v ≠ 0 := by intro h0; rw [h0] at hv; simp [fiveForm] at hv
        have hcoef : 2 * fiveForm k ε c v * (fiveForm k ε v v)⁻¹ = 0 := by
          have h2 : (2 * fiveForm k ε c v * (fiveForm k ε v v)⁻¹) • v = 0 := by
            have hh : c = c + (2 * fiveForm k ε c v * (fiveForm k ε v v)⁻¹) • v :=
              sub_eq_iff_eq_add.mp h
            exact add_left_cancel (show c + (2 * fiveForm k ε c v * (fiveForm k ε v v)⁻¹) • v
                = c + 0 from by rw [add_zero]; exact hh.symm)
          rcases smul_eq_zero.mp h2 with hc | h0
          · exact hc
          · exact absurd h0 hv0
        have h2' : (2 : ZMod 5) * fiveForm k ε c v * (fiveForm k ε v v)⁻¹ = 0 := hcoef
        have h3 : (2 : ZMod 5) * fiveForm k ε c v = 0 := by
          rcases mul_eq_zero.mp h2' with h4 | h4
          · exact h4
          · exact absurd (inv_eq_zero.mp h4) hv
        exact (mul_eq_zero.mp h3).resolve_left (by decide)
      have hcrv : fiveForm k ε c
          (((r : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ v)) = 0 := by
        rw [← hrc, hrpres c v, hsc]
      rw [conj_fiveReflOf hrpres v]
      refine ⟨fiveReflOf_mem ?_ ?_, ?_⟩
      · rwa [hrpres v v]
      · rw [hrpres v v]; exact hsign
      · rw [fiveReflOf_mulVec, hcrv, mul_zero, zero_mul, zero_smul]
        simp
    have hconj : ∀ x ∈ L, r * x * r⁻¹ ∈ L := by
      intro x hx
      rw [hLdef] at hx ⊢
      induction hx using Subgroup.closure_induction with
      | mem s hs => exact Subgroup.subset_closure (hconj_gen s hs)
      | one => rw [mul_one, mul_inv_cancel]; exact Subgroup.one_mem _
      | mul x y hx hy ihx ihy =>
        have h1 : r * (x * y) * r⁻¹ = (r * x * r⁻¹) * (r * y * r⁻¹) := by group
        rw [h1]; exact Subgroup.mul_mem _ ihx ihy
      | inv x hx ihx =>
        have h1 : r * x⁻¹ * r⁻¹ = (r * x * r⁻¹)⁻¹ := by group
        rw [h1]; exact Subgroup.inv_mem _ ihx
    have hgL' : g ∈ L' := by
      rw [hL'def, hprod]
      apply Subgroup.list_prod_mem
      intro s hs
      rw [List.mem_map] at hs
      obtain ⟨w, hw, rfl⟩ := hs
      exact fiveReflOf_mem_closure_union hk ε π huQ huπ huc (hl w hw).2 (hl w hw).1
    have hcoset : ∀ x ∈ L', x ∈ L ∨ ∃ a ∈ L, a * r = x := by
      intro x hx
      rw [hL'def] at hx
      induction hx using Subgroup.closure_induction with
      | mem s hs =>
        rcases hs with hs | hs
        · exact Or.inl (Subgroup.subset_closure hs)
        · rw [Set.mem_singleton_iff] at hs; subst hs
          exact Or.inr ⟨1, Subgroup.one_mem _, one_mul r⟩
      | one => exact Or.inl (Subgroup.one_mem _)
      | mul x y hx hy ihx ihy =>
        rcases ihx with hx1 | ⟨lx, hlx, hlxr⟩ <;> rcases ihy with hy1 | ⟨ly, hly, hlyr⟩
        · exact Or.inl (Subgroup.mul_mem _ hx1 hy1)
        · refine Or.inr ⟨x * ly, Subgroup.mul_mem _ hx1 hly, ?_⟩
          rw [← hlyr]; group
        · refine Or.inr ⟨lx * (r * y * r⁻¹), Subgroup.mul_mem _ hlx (hconj y hy1), ?_⟩
          rw [← hlxr]; group
        · refine Or.inl ?_
          rw [← hlxr, ← hlyr]
          have h1 : (lx * r) * (ly * r) = lx * (r * ly * r⁻¹) := by
            rw [hrinv]; group
          rw [h1]
          exact Subgroup.mul_mem _ hlx (hconj ly hly)
      | inv x hx ihx =>
        rcases ihx with hx1 | ⟨lx, hlx, hlxr⟩
        · exact Or.inl (Subgroup.inv_mem _ hx1)
        · refine Or.inr ⟨(r * lx * r⁻¹)⁻¹, Subgroup.inv_mem _ (hconj lx hlx), ?_⟩
          rw [← hlxr]
          have h1 : (lx * r)⁻¹ = (r * lx * r⁻¹)⁻¹ * r := by
            rw [hrinv]; group
          rw [h1]
    rcases hcoset g hgL' with hgL | ⟨a, ha, har⟩
    · rw [hLdef] at hgL; exact hgL
    · exfalso
      have haR : a ∈ fiveReflectionGroup k ε π := hLR' ha
      have : r ∈ fiveReflectionGroup k ε π := by
        have h' : r = a⁻¹ * g := by
          rw [← har, ← mul_assoc, inv_mul_cancel, one_mul]
        rw [h']
        exact Subgroup.mul_mem (H := fiveReflectionGroup k ε π)
          (Subgroup.inv_mem (H := fiveReflectionGroup k ε π) haR) hgR
      exact hru_not this

theorem relIndex_normalizer_fiveReflectionsFixing {k : ℕ} (hk : 4 ≤ k) (ε π : Bool)
    {c : Fin (k + 1) → ZMod 5} (hc : c ≠ 0) :
    (Subgroup.closure (fiveReflectionsFixing k ε π c)).relIndex
        (fiveReflectionGroup k ε π ⊓
          Subgroup.normalizer (Subgroup.closure (fiveReflectionsFixing k ε π c) : Set _)) =
      if fiveForm k ε c c = 0 then 4 else 2 :=
  relIndex_normalizer_fiveReflectionsFixing_aux hk ε π hc
    (mem_closure_fiveReflectionsFixing_iff hk ε π hc)

end CFSG.OddTranspositions.PartThree
