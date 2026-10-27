module

public import CFSG.Quasithin.EmptyFaithful.A10ConfigurationQ
public import CFSG.Quasithin.EmptyFaithful.A10ConfigurationCaseModel
import all CFSG.Quasithin.EmptyFaithful.A10ConfigurationModel
import all CFSG.Quasithin.EmptyFaithful.A10ConfigurationFacts
import all CFSG.Quasithin.EmptyFaithful.A10ConfigurationClasses
import all CFSG.Quasithin.EmptyFaithful.A10ConfigurationQ

public section

namespace CFSG.Quasithin.A10

open CFSG.Open CFSG.Quasithin S4 Wc

@[expose] def cm (x y : Wc) : Wc := x * y * x⁻¹ * y⁻¹

@[expose] def u6 : Wc := ⟨v2, 1, false⟩

@[expose] def u7 : Wc := ⟨f1, v2, false⟩

def lamReps : List Wc := [t0, s0, u3, u4, u5, u6, u7]

def isCand (w : Wc) : Bool := thList.contains w && (w * w == 1) && (w != 1) && !(D1 w)

def orb (r : Wc) : List Wc := (thList.map fun v => v⁻¹ * r * v).dedup

def LS (Sel : List Wc) : List Wc := (Sel.flatMap orb).dedup

def okZ (L : List Wc) : Bool := L.all fun w => L.contains (w * z0)

def okC (L : List Wc) : Bool := L.all fun w => L.all fun w' => cm w w' == 1 || cm w w' == z0

def Rl (L : List Wc) : List Wc :=
  thList.filter fun x => L.all fun y => cm x y == 1 || cm x y == z0

theorem mem_thList : ∀ x : Wc, x ∈ thList ↔ x ∈ Th := by decide +kernel

theorem mem_orb {r w : Wc} : w ∈ orb r ↔ ∃ v ∈ Th, v⁻¹ * r * v = w := by
  simp only [orb, List.mem_dedup, List.mem_map, mem_thList]

theorem mem_LS {Sel : List Wc} {w : Wc} : w ∈ LS Sel ↔ ∃ r ∈ Sel, w ∈ orb r := by
  simp only [LS, List.mem_dedup, List.mem_flatMap]

theorem cand_cover : ∀ w : Wc, isCand w = true → ∃ r ∈ lamReps, w ∈ orb r := by decide +kernel

theorem isCand_iff {w : Wc} : isCand w = true ↔
    (w ∈ Th ∧ w * w = 1 ∧ w ≠ 1 ∧ D1 w = false) := by
  simp [isCand, mem_thList, and_assoc]

theorem classify_sel : ∀ Sel ∈ lamReps.sublists, t0 ∈ Sel → okZ (LS Sel) = true →
    okC (LS Sel) = true →
    Sel = [t0] ∨ Sel = [t0, s0] ∨ Sel = [t0, u4] ∨ Sel = [t0, s0, u4] ∨ Sel = [t0, u3, u5] ∨
      Sel = [t0, u3, u4, u5] ∨ Sel = [t0, u7] := by
  decide +kernel

theorem len_S0 : (LS [t0]).length = 2 := by decide +kernel
theorem len_S1 : (LS [t0, s0]).length = 10 := by decide +kernel
theorem len_S2 : (LS [t0, u4]).length = 6 := by decide +kernel
theorem len_S3 : (LS [t0, s0, u4]).length = 14 := by decide +kernel
theorem len_S4 : (LS [t0, u3, u5]).length = 10 := by decide +kernel
theorem len_S5 : (LS [t0, u3, u4, u5]).length = 14 := by decide +kernel
theorem len_S6 : (LS [t0, u7]).length = 10 := by decide +kernel

theorem Rlen_S1 : (Rl (LS [t0, s0])).length = 32 := by decide +kernel
theorem Rlen_S3 : (Rl (LS [t0, s0, u4])).length = 32 := by decide +kernel
theorem Rlen_S4 : (Rl (LS [t0, u3, u5])).length = 16 := by decide +kernel
theorem Rlen_S5 : (Rl (LS [t0, u3, u4, u5])).length = 16 := by decide +kernel
theorem Rlen_S6 : (Rl (LS [t0, u7])).length = 16 := by decide +kernel

theorem mem_Rl {L : List Wc} {x : Wc} :
    x ∈ Rl L ↔ x ∈ Th ∧ ∀ y ∈ L, cm x y = 1 ∨ cm x y = z0 := by
  simp [Rl, mem_thList, cm]

theorem thList_nodup : thList.Nodup := by decide +kernel

theorem nodup_Rl (L : List Wc) : (Rl L).Nodup := thList_nodup.filter _

theorem nodup_LS (Sel : List Wc) : (LS Sel).Nodup := List.nodup_dedup _

def Vh : Subgroup Wc where
  carrier := {x | x = 1 ∨ x = z0 ∨ x = t0 ∨ x = t0 * z0}
  one_mem' := Or.inl rfl
  mul_mem' := by
    rintro a b (rfl | rfl | rfl | rfl) (rfl | rfl | rfl | rfl) <;>
      first
        | exact Or.inl (by decide +kernel)
        | exact Or.inr (Or.inl (by decide +kernel))
        | exact Or.inr (Or.inr (Or.inl (by decide +kernel)))
        | exact Or.inr (Or.inr (Or.inr (by decide +kernel)))
  inv_mem' := by
    rintro a (rfl | rfl | rfl | rfl) <;>
      first
        | exact Or.inl (by decide +kernel)
        | exact Or.inr (Or.inl (by decide +kernel))
        | exact Or.inr (Or.inr (Or.inl (by decide +kernel)))
        | exact Or.inr (Or.inr (Or.inr (by decide +kernel)))

theorem mem_Vh {x : Wc} : x ∈ Vh ↔ x = 1 ∨ x = z0 ∨ x = t0 ∨ x = t0 * z0 := Iff.rfl

theorem Vh_le_Th : Vh ≤ Th := by
  intro x hx
  rcases mem_Vh.1 hx with rfl | rfl | rfl | rfl
  · exact Subgroup.one_mem _
  · exact z0_mem_Th
  · exact Jh_le_Th (T1h_le_Jh t0_mem_T1h)
  · exact Th.mul_mem (Jh_le_Th (T1h_le_Jh t0_mem_T1h)) z0_mem_Th

theorem isElemAbelian_Vh : IsElemAbelian 2 Vh := by
  refine isElemAbelian_of_forall Vh ?_ ?_
  · intro x hx y hy
    rcases mem_Vh.1 hx with rfl | rfl | rfl | rfl <;>
      rcases mem_Vh.1 hy with rfl | rfl | rfl | rfl <;> decide +kernel
  · intro x hx
    rcases mem_Vh.1 hx with rfl | rfl | rfl | rfl <;> decide +kernel

def vPred (x : Wc) : Bool := x == 1 || x == z0 || x == t0 || x == t0 * z0

theorem mem_Vh_iff_vPred {x : Wc} : x ∈ Vh ↔ vPred x = true := by
  simp [vPred, mem_Vh, or_assoc]

theorem Th_conj_Vh_aux : ∀ a ∈ dList, ∀ b ∈ dList, ∀ e : Bool, ∀ x ∈ [1, z0, t0, t0 * z0],
    vPred ((⟨a, b, e⟩ : Wc) * x * (⟨a, b, e⟩ : Wc)⁻¹) = true := by decide +kernel

theorem Th_conj_Vh : ∀ w ∈ Th, ∀ x ∈ Vh, w * x * w⁻¹ ∈ Vh :=
  forall_mem_Th fun a ha b hb e x hx => by
    have hx' : x ∈ [1, z0, t0, t0 * z0] := by
      rcases mem_Vh.1 hx with rfl | rfl | rfl | rfl <;> simp
    exact mem_Vh_iff_vPred.2 (Th_conj_Vh_aux a ha b hb e x hx')

theorem Th_le_normalizer_Vh : Th ≤ Subgroup.normalizer (Vh : Set Wc) :=
  le_normalizer_of_forall Th_conj_Vh

theorem s0_conj_t0 : s0⁻¹ * t0 * s0 = t0 * z0 := by decide +kernel
theorem t0_ne_z0 : t0 ≠ z0 := by decide +kernel

theorem mem_LS_true {w : Wc} : w ∈ LS [t0, u4] ↔ w ∈ A2 ∧ (D2 w = true ∨ D4 w = true) := by
  revert w
  decide +kernel

theorem A2_le_Rl_true : ∀ x ∈ A2, x ∈ Rl (LS [t0, u4]) := by decide +kernel

theorem Qh_le_Rl_true : ∀ x ∈ Qh, x ∈ Rl (LS [t0, u4]) :=
  forall_mem_Qh fun a ha c hc e => by revert a ha c hc e; decide +kernel

theorem sq_mem_Rl_S1 : ∀ x ∈ thList, x * x ∈ Rl (LS [t0, s0]) := by decide +kernel

theorem lam_classify (P : Wc → Prop)
    (h1 : ∀ w, P w → isCand w = true)
    (h2 : ∀ w, P w → ∀ v ∈ Th, P (v⁻¹ * w * v))
    (h3 : ∀ w, P w → P (w * z0))
    (h4 : ∀ w w', P w → P w' → cm w w' = 1 ∨ cm w w' = z0)
    (h5 : P t0) :
    ∃ Sel : List Wc, (Sel = [t0] ∨ Sel = [t0, s0] ∨ Sel = [t0, u4] ∨ Sel = [t0, s0, u4] ∨
      Sel = [t0, u3, u5] ∨ Sel = [t0, u3, u4, u5] ∨ Sel = [t0, u7]) ∧
      ∀ w, P w ↔ w ∈ LS Sel := by
  classical
  set Sel : List Wc := lamReps.filter fun r => decide (P r) with hSel
  have hsub : Sel ∈ lamReps.sublists := List.mem_sublists.2 List.filter_sublist
  have hmem : ∀ w, w ∈ LS Sel ↔ P w := by
    intro w
    rw [mem_LS]
    constructor
    · rintro ⟨r, hr, hw⟩
      have hr' := List.mem_filter.1 hr
      have hPr : P r := of_decide_eq_true hr'.2
      obtain ⟨v, hv, rfl⟩ := mem_orb.1 hw
      exact h2 r hPr v hv
    · intro hw
      obtain ⟨r, hr, hwr⟩ := cand_cover w (h1 w hw)
      obtain ⟨v, hv, hvw⟩ := mem_orb.1 hwr
      have hPr : P r := by
        have := h2 w hw v⁻¹ (Th.inv_mem hv)
        rw [← hvw] at this
        simpa [mul_assoc] using this
      exact ⟨r, List.mem_filter.2 ⟨hr, decide_eq_true hPr⟩, hwr⟩
  have ht0 : t0 ∈ Sel := List.mem_filter.2 ⟨by simp [lamReps], decide_eq_true h5⟩
  have hZ : okZ (LS Sel) = true := by
    unfold okZ
    rw [List.all_eq_true]
    intro w hw
    have := h3 w ((hmem w).1 hw)
    simpa using (hmem _).2 this
  have hC : okC (LS Sel) = true := by
    unfold okC
    rw [List.all_eq_true]
    intro w hw
    rw [List.all_eq_true]
    intro w' hw'
    rcases h4 w w' ((hmem w).1 hw) ((hmem w').1 hw') with h | h <;> simp [h]
  exact ⟨Sel, classify_sel Sel hsub ht0 hZ hC, fun w => (hmem w).symm⟩

end CFSG.Quasithin.A10
