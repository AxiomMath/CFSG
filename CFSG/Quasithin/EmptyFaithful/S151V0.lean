module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Tactic.Group

public section

namespace CFSG.Quasithin

open scoped commutatorElement

variable {G : Type*} [Group G]

theorem fpf_iff_surj [Finite G] {E : Subgroup G} (hE : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) {c : G}
    (hc : ∀ a ∈ E, c * a * c⁻¹ ∈ E) :
    (∀ a ∈ E, c * a * c⁻¹ = a → a = 1) ↔ ∀ a ∈ E, ∃ v ∈ E, ⁅v, c⁆ = a := by
  classical
  let _ : CommGroup E := { (inferInstance : Group E) with
    mul_comm := fun a b => Subtype.ext (hE a a.2 b b.2) }
  let cc : E → E := fun v => ⟨c * (v : G) * c⁻¹, hc v v.2⟩
  have hcc_mul : ∀ v w : E, cc (v * w) = cc v * cc w := fun v w => by
    apply Subtype.ext
    change c * ((v : G) * (w : G)) * c⁻¹ = (c * (v : G) * c⁻¹) * (c * (w : G) * c⁻¹)
    group
  have hcc_inv : ∀ v : E, cc v⁻¹ = (cc v)⁻¹ := fun v => by
    apply Subtype.ext
    change c * (v : G)⁻¹ * c⁻¹ = (c * (v : G) * c⁻¹)⁻¹
    group
  let f : E → E := fun v => v * (cc v)⁻¹
  have hf_coe : ∀ v : E, ((f v : E) : G) = ⁅(v : G), c⁆ := fun v => by
    change (v : G) * (c * (v : G) * c⁻¹)⁻¹ = ⁅(v : G), c⁆
    simp only [commutatorElement_def]
    group
  have hinj_iff : Function.Injective f ↔ ∀ a ∈ E, c * a * c⁻¹ = a → a = 1 := by
    constructor
    · intro hinj a ha hfix
      have h1 : f ⟨a, ha⟩ = f 1 := by
        change (⟨a, ha⟩ : E) * (cc ⟨a, ha⟩)⁻¹ = (1 : E) * (cc 1)⁻¹
        have : cc ⟨a, ha⟩ = ⟨a, ha⟩ := Subtype.ext hfix
        rw [this]
        have h1' : cc 1 = 1 := Subtype.ext (by change c * (1 : G) * c⁻¹ = 1; group)
        rw [h1']
        simp
      have := congrArg Subtype.val (hinj h1)
      simpa using this
    · intro hfix v w hvw
      have hvw' : v * (cc v)⁻¹ = w * (cc w)⁻¹ := hvw
      have hu : (v * w⁻¹ : E) = cc (v * w⁻¹) := by
        rw [hcc_mul, hcc_inv]
        rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff_mul_eq_mul]
        rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff_mul_eq_mul] at hvw'
        rw [mul_comm (cc v) w]
        exact hvw'
      have hu1 : c * ((v * w⁻¹ : E) : G) * c⁻¹ = ((v * w⁻¹ : E) : G) :=
        (congrArg Subtype.val hu).symm
      have := hfix _ (v * w⁻¹ : E).2 hu1
      have h2 : (v * w⁻¹ : E) = 1 := Subtype.ext this
      exact mul_inv_eq_one.mp h2
  have hfin : Finite E := inferInstance
  have hsurj_iff : Function.Injective f ↔ Function.Surjective f := Finite.injective_iff_surjective
  rw [← hinj_iff, hsurj_iff]
  constructor
  · intro hs a ha
    obtain ⟨v, hv⟩ := hs ⟨a, ha⟩
    exact ⟨v, v.2, by rw [← hf_coe v, hv]⟩
  · intro h ⟨a, ha⟩
    obtain ⟨v, hv, hva⟩ := h a ha
    exact ⟨⟨v, hv⟩, Subtype.ext (by rw [hf_coe]; exact hva)⟩

theorem fpf_of_commutator_eq [Finite G] {E Y : Subgroup G} (hE : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hN : ∀ y ∈ Y, ∀ a ∈ E, y * a * y⁻¹ ∈ E) {c : G} (hcY : c ∈ Y)
    (hpow : ∀ y ∈ Y, ∃ i : ℕ, ∀ a ∈ E, y * a * y⁻¹ = c ^ i * a * (c ^ i)⁻¹)
    (hEY : E ≤ ⁅E, Y⁆) : ∀ a ∈ E, c * a * c⁻¹ = a → a = 1 := by
  have hc : ∀ a ∈ E, c * a * c⁻¹ ∈ E := hN c hcY
  refine (fpf_iff_surj hE hc).mpr ?_
  have hcomm_mem : ∀ v ∈ E, ⁅v, c⁆ ∈ E := fun v hv => by
    have : ⁅v, c⁆ = v * (c * v⁻¹ * c⁻¹) := by simp only [commutatorElement_def, mul_assoc]
    rw [this]
    exact E.mul_mem hv (hc _ (E.inv_mem hv))
  have hmul : ∀ v w : G, v ∈ E → w ∈ E → ⁅v * w, c⁆ = ⁅v, c⁆ * ⁅w, c⁆ := by
    intro v w hv hw
    have h1 : ⁅v * w, c⁆ = (v * ⁅w, c⁆ * v⁻¹) * ⁅v, c⁆ := by
      simp only [commutatorElement_def]; group
    have h2 : v * ⁅w, c⁆ * v⁻¹ = ⁅w, c⁆ := by
      rw [hE _ hv _ (hcomm_mem w hw)]; group
    rw [h1, h2]
    exact hE _ (hcomm_mem w hw) _ (hcomm_mem v hv)
  let R : Subgroup G :=
    { carrier := {x | ∃ v ∈ E, ⁅v, c⁆ = x}
      mul_mem' := by
        rintro _ _ ⟨v, hv, rfl⟩ ⟨w, hw, rfl⟩
        exact ⟨v * w, E.mul_mem hv hw, hmul v w hv hw⟩
      one_mem' := ⟨1, E.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨v, hv, rfl⟩
        refine ⟨v⁻¹, E.inv_mem hv, ?_⟩
        have h2 : ⁅v⁻¹, c⁆ = v⁻¹ * (c * v * c⁻¹) := by
          simp only [commutatorElement_def]; group
        have h3 : ⁅v, c⁆⁻¹ = (c * v * c⁻¹) * v⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [h2, h3]
        exact (hE _ (E.inv_mem hv) _ (hc _ hv)) }
  have hconj : ∀ v ∈ E, c * ⁅v, c⁆ * c⁻¹ = ⁅c * v * c⁻¹, c⁆ := fun v _ => by
    simp only [commutatorElement_def]; group
  have hpow_mem : ∀ i : ℕ, ∀ v ∈ E, ⁅v, c ^ i⁆ ∈ R := by
    intro i
    induction i with
    | zero => intro v _; simp
    | succ i ih =>
      intro v hv
      have h1 : ⁅v, c ^ (i + 1)⁆ = ⁅v, c⁆ * (c * ⁅v, c ^ i⁆ * c⁻¹) := by
        rw [pow_succ']
        simp only [commutatorElement_def]; group
      rw [h1]
      refine R.mul_mem ⟨v, hv, rfl⟩ ?_
      have h2 : c * ⁅v, c ^ i⁆ * c⁻¹ = ⁅c * v * c⁻¹, c ^ i⁆ := by
        simp only [commutatorElement_def]
        have : c * c ^ i * c⁻¹ = c ^ i := by rw [← pow_succ', pow_succ, mul_assoc, mul_inv_cancel, mul_one]
        have h3 : c * (v * c ^ i * v⁻¹ * (c ^ i)⁻¹) * c⁻¹ =
            (c * v * c⁻¹) * (c * c ^ i * c⁻¹) * (c * v * c⁻¹)⁻¹ * (c * c ^ i * c⁻¹)⁻¹ := by group
        rw [h3, this]
      rw [h2]
      exact ih _ (hc v hv)
  have hcommY : ⁅E, Y⁆ ≤ R := by
    rw [Subgroup.commutator_le]
    intro v hv y hy
    obtain ⟨i, hi⟩ := hpow y hy
    have : ⁅v, y⁆ = ⁅v, c ^ i⁆ := by
      simp only [commutatorElement_def]
      have h4 := hi v⁻¹ (E.inv_mem hv)
      calc v * y * v⁻¹ * y⁻¹ = v * (y * v⁻¹ * y⁻¹) := by group
        _ = v * (c ^ i * v⁻¹ * (c ^ i)⁻¹) := by rw [h4]
        _ = v * c ^ i * v⁻¹ * (c ^ i)⁻¹ := by group
    rw [this]
    exact hpow_mem i v hv
  intro a ha
  exact hcommY (hEY ha)

end CFSG.Quasithin
