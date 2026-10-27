module

public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.Tactic.Group
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.Quasithin

open scoped commutatorElement

variable {S : Type*} [Group S]

theorem mul_inv_mem_of_index_two {C : Subgroup S} (hC : C.index = 2) {y s : S} (hy : y ∉ C)
    (hs : s ∉ C) : s * y⁻¹ ∈ C := by
  have := (Subgroup.mul_mem_iff_of_index_two hC (a := s) (b := y⁻¹)).mpr
  apply this
  constructor
  · intro h; exact absurd h hs
  · intro h; exact absurd (by simpa using C.inv_mem h) hy

theorem conj_eq_conj_inv_of_index_two {C : Subgroup S} (hC : C.index = 2)
    (hab : ∀ a ∈ C, ∀ b ∈ C, a * b = b * a) {y : S} {c : S} (hc : c ∈ C) :
    y * c * y⁻¹ = y⁻¹ * c * y := by
  have hy2 : y * y ∈ C := Subgroup.mul_self_mem_of_index_two hC y
  have hn : C.Normal := Subgroup.normal_of_index_eq_two hC
  have hc' : y⁻¹ * c * y ∈ C := by simpa using hn.conj_mem c hc y⁻¹
  have hcomm := hab _ hy2 _ hc'
  calc y * c * y⁻¹ = (y * y) * (y⁻¹ * c * y) * (y * y)⁻¹ * (y * y) * y⁻¹ * y⁻¹ := by group
    _ = (y⁻¹ * c * y) * (y * y) * (y * y)⁻¹ * (y * y) * y⁻¹ * y⁻¹ := by rw [hcomm]
    _ = y⁻¹ * c * y := by group

variable [Finite S]

theorem card_commutator_mul_card_le {C Z : Subgroup S} (hC : C.index = 2)
    (hab : ∀ a ∈ C, ∀ b ∈ C, a * b = b * a) (hZ : Z ≤ Subgroup.center S) (hZC : Z ≤ C) :
    Nat.card (commutator S) * Nat.card Z ≤ Nat.card C := by
  classical
  have hn : C.Normal := Subgroup.normal_of_index_eq_two hC
  obtain ⟨y, hy⟩ : ∃ y : S, y ∉ C := by
    by_contra hall
    push Not at hall
    have htop : C = ⊤ := eq_top_iff.mpr fun x _ => hall x
    rw [htop, Subgroup.index_top] at hC
    omega
  have hconj : ∀ c ∈ C, y⁻¹ * c * y ∈ C := fun c hc => by simpa using hn.conj_mem c hc y⁻¹
  let φ : C →* C :=
    { toFun := fun c => ⟨(c : S)⁻¹ * (y⁻¹ * c * y), C.mul_mem (C.inv_mem c.2) (hconj c c.2)⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by
        ext
        simp only [Subgroup.coe_mul]
        have h1 := hab _ (C.inv_mem a.2) _ (hconj b b.2)
        have h2 := hab _ (C.inv_mem b.2) _ (C.inv_mem a.2)
        calc ((a : S) * b)⁻¹ * (y⁻¹ * (a * b) * y)
            = (b : S)⁻¹ * ((a : S)⁻¹ * (y⁻¹ * a * y)) * (y⁻¹ * b * y) := by group
          _ = (a : S)⁻¹ * (y⁻¹ * a * y) * ((b : S)⁻¹ * (y⁻¹ * b * y)) := by
            have h3 := hab _ (C.inv_mem b.2) _
              (C.mul_mem (C.inv_mem a.2) (hconj a a.2))
            rw [h3]; group }
  have hφ : ∀ c : C, ((φ c : C) : S) = (c : S)⁻¹ * (y⁻¹ * c * y) := fun c => rfl
  set K : Subgroup S := φ.range.map C.subtype with hK
  have hKmem : ∀ c ∈ C, (c : S)⁻¹ * (y⁻¹ * c * y) ∈ K := fun c hc =>
    ⟨φ ⟨c, hc⟩, ⟨⟨c, hc⟩, rfl⟩, rfl⟩
  have hcomm_left : ∀ a ∈ C, ∀ b : S, ⁅a, b⁆ ∈ K := by
    intro a ha b
    by_cases hb : b ∈ C
    · rw [commutatorElement_def, hab a ha b hb, mul_inv_cancel_right, mul_inv_cancel]
      exact K.one_mem
    · have hc : b * y⁻¹ ∈ C := mul_inv_mem_of_index_two hC hy hb
      set c := b * y⁻¹ with hcdef
      have hb' : b = c * y := by rw [hcdef]; group
      have haY : y * a⁻¹ * y⁻¹ ∈ C := by simpa using hn.conj_mem a⁻¹ (C.inv_mem ha) y
      have e1 : ⁅a, b⁆ = c * (a * (y * a⁻¹ * y⁻¹)) * c⁻¹ := by
        calc ⁅a, b⁆ = a * c * y * a⁻¹ * y⁻¹ * c⁻¹ := by rw [commutatorElement_def, hb']; group
          _ = c * a * y * a⁻¹ * y⁻¹ * c⁻¹ := by rw [hab a ha c hc]
          _ = c * (a * (y * a⁻¹ * y⁻¹)) * c⁻¹ := by group
      have hmem : a * (y * a⁻¹ * y⁻¹) ∈ C := C.mul_mem ha haY
      have e2 : c * (a * (y * a⁻¹ * y⁻¹)) * c⁻¹ = a * (y * a⁻¹ * y⁻¹) := by
        rw [hab c hc _ hmem]; group
      rw [e1, e2, conj_eq_conj_inv_of_index_two hC hab (C.inv_mem ha)]
      have hw : y⁻¹ * a⁻¹ * y ∈ C := hconj _ (C.inv_mem ha)
      have e3 : a * (y⁻¹ * a⁻¹ * y) = (a⁻¹ * (y⁻¹ * a * y))⁻¹ := by
        rw [hab a ha _ hw]; group
      rw [e3]
      exact K.inv_mem (hKmem a ha)
  have hcomm : commutator S ≤ K := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    by_cases ha : a ∈ C
    · exact hcomm_left a ha b
    · by_cases hb : b ∈ C
      · have := K.inv_mem (hcomm_left b hb a)
        rwa [commutatorElement_inv] at this
      ·
        have hd : b * a⁻¹ ∈ C := mul_inv_mem_of_index_two hC ha hb
        have e : ⁅a, b⁆ = ⁅b * a⁻¹, a⁆⁻¹ := by
          rw [commutatorElement_inv, commutatorElement_def, commutatorElement_def]; group
        rw [e]
        exact K.inv_mem (hcomm_left _ hd a)
  have hZker : Z.subgroupOf C ≤ φ.ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    have hzZ : (z : S) ∈ Subgroup.center S := hZ (Subgroup.mem_subgroupOf.mp hz)
    have hc := (Subgroup.mem_center_iff.mp hzZ) y
    rw [hφ]
    simp only [Subgroup.coe_one]
    calc (z : S)⁻¹ * (y⁻¹ * z * y) = (z : S)⁻¹ * (y⁻¹ * (y * z)) := by rw [hc, mul_assoc]
      _ = 1 := by group
  have hKcard : Nat.card K = Nat.card φ.range := by
    rw [hK]
    exact Nat.card_congr (Subgroup.equivMapOfInjective _ _ C.subtype_injective).toEquiv.symm
  have hrange : Nat.card φ.range = φ.ker.index := (Subgroup.index_ker φ).symm
  have hidx : φ.ker.index ≤ (Z.subgroupOf C).index :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) (Subgroup.index_dvd_of_le hZker)
  have hZsub : Nat.card (Z.subgroupOf C) = Nat.card Z :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZC).toEquiv
  have hmul := (Z.subgroupOf C).card_mul_index
  rw [hZsub] at hmul
  have hS'K : Nat.card (commutator S) ≤ Nat.card K := Subgroup.card_le_of_le hcomm
  calc Nat.card (commutator S) * Nat.card Z ≤ Nat.card K * Nat.card Z :=
        Nat.mul_le_mul_right _ hS'K
    _ ≤ (Z.subgroupOf C).index * Nat.card Z := by
        rw [hKcard, hrange]; exact Nat.mul_le_mul_right _ hidx
    _ = Nat.card C := by rw [mul_comm, hmul]

theorem card_le_two_of_index_commutator {C Z : Subgroup S} (hC : C.index = 2)
    (hab : ∀ a ∈ C, ∀ b ∈ C, a * b = b * a) (hZ : Z ≤ Subgroup.center S) (hZC : Z ≤ C)
    (hS' : (commutator S).index = 4) : Nat.card Z ≤ 2 := by
  have h1 := card_commutator_mul_card_le hC hab hZ hZC
  have h2 := (commutator S).card_mul_index
  have h3 := C.card_mul_index
  rw [hS'] at h2
  rw [hC] at h3
  have hpos : 0 < Nat.card S := Nat.card_pos
  have h4 : Nat.card S * Nat.card Z ≤ Nat.card S * 2 := by
    have := Nat.mul_le_mul_right 4 h1
    nlinarith
  exact Nat.le_of_mul_le_mul_left h4 hpos

end CFSG.Quasithin
