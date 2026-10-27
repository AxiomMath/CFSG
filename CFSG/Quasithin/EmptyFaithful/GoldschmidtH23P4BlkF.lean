module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4BlkE

public section

namespace CFSG.Quasithin.H23P4

open scoped commutatorElement

variable {G : Type*} [Group G]

namespace ModData

variable {L U Z : Subgroup G} {y : G} (h : ModData L U Z y)
include h

theorem exists_mid_subgroup [Finite G] (hd : Z.relIndex U = 16) :
    ∃ X : Subgroup G, Z ≤ X ∧ X ≤ U ∧ X ≠ Z ∧ X ≠ U := by
  have hne : ¬ U ≤ Z := fun hle => by
    have := Subgroup.relIndex_eq_one.mpr hle
    omega
  obtain ⟨u, huU, huZ⟩ := Set.not_subset.mp hne
  have hu2 : u * u = 1 := by simpa [pow_two] using h.exp u huU
  have hinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  let S : Subgroup G :=
    { carrier := {x | x ∈ U ∧ (x ∈ Z ∨ u⁻¹ * x ∈ Z)}
      one_mem' := ⟨one_mem _, Or.inl (one_mem _)⟩
      mul_mem' := by
        rintro a b ⟨ha, ha' | ha'⟩ ⟨hb, hb' | hb'⟩
        · exact ⟨mul_mem ha hb, Or.inl (mul_mem ha' hb')⟩
        · refine ⟨mul_mem ha hb, Or.inr ?_⟩
          have hc := h.abel _ (inv_mem huU) a (h.ZU ha')
          rw [← mul_assoc, hc, mul_assoc]
          exact mul_mem ha' hb'
        · exact ⟨mul_mem ha hb, Or.inr (by rw [← mul_assoc]; exact mul_mem ha' hb')⟩
        · refine ⟨mul_mem ha hb, Or.inl ?_⟩
          have hc : (u⁻¹ * a) * u = u * (u⁻¹ * a) := h.abel _ (h.ZU ha') u huU
          have e : a * b = (u⁻¹ * a) * (u⁻¹ * b) := by
            calc a * b = (u * (u⁻¹ * a)) * (u * (u⁻¹ * b)) := by group
              _ = u * ((u⁻¹ * a) * u) * (u⁻¹ * b) := by group
              _ = u * (u * (u⁻¹ * a)) * (u⁻¹ * b) := by rw [hc]
              _ = (u * u) * (u⁻¹ * a) * (u⁻¹ * b) := by group
              _ = (u⁻¹ * a) * (u⁻¹ * b) := by rw [hu2, one_mul]
          rw [e]
          exact mul_mem ha' hb'
      inv_mem' := by
        rintro a ⟨ha, ha' | ha'⟩
        · exact ⟨inv_mem ha, Or.inl (inv_mem ha')⟩
        · refine ⟨inv_mem ha, Or.inr ?_⟩
          have hc : Commute u a := h.abel u huU a ha
          have e : u⁻¹ * a⁻¹ = (u⁻¹ * a)⁻¹ := by
            rw [mul_inv_rev, inv_inv, hinv]
            exact hc.inv_right.eq
          rw [e]
          exact inv_mem ha' }
  refine ⟨S, fun z hz => ⟨h.ZU hz, Or.inl hz⟩, fun x hx => hx.1, ?_, ?_⟩
  · intro hSZ
    have hmem : u ∈ S := ⟨huU, Or.inr (by simp)⟩
    rw [hSZ] at hmem
    exact huZ hmem
  · intro hSU
    have hcov : ∀ x ∈ U, x ∈ Z ∨ u⁻¹ * x ∈ Z := fun x hx => by
      have : x ∈ S := by rw [hSU]; exact hx
      exact this.2
    have h1 : Nat.card U = 16 * Nat.card Z := by
      have := Subgroup.relIndex_mul_card (H := Z) (K := U)
      rw [inf_eq_left.2 h.ZU, hd] at this
      exact this.symm
    have hsub : (U : Set G) ⊆ (Z : Set G) ∪ (fun z => u * z) '' (Z : Set G) := fun x hx => by
      rcases hcov x hx with h3 | h3
      · exact Or.inl h3
      · exact Or.inr ⟨u⁻¹ * x, h3, by group⟩
    have h3 := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h4 := Set.ncard_union_le (Z : Set G) ((fun z => u * z) '' (Z : Set G))
    have h5 : ((fun z => u * z) '' (Z : Set G)).ncard = (Z : Set G).ncard :=
      Set.ncard_image_of_injective _ (mul_right_injective u)
    have h6 : Nat.card U = (U : Set G).ncard := Nat.card_coe_set_eq (U : Set G)
    have h7 : Nat.card Z = (Z : Set G).ncard := Nat.card_coe_set_eq (Z : Set G)
    have h8 : 0 < Nat.card Z := Nat.card_pos
    omega

theorem false_of_sixteen [Finite G] (hperf : ⁅L, L⁆ = L) {k : ℕ} (hy : y ^ 5 ^ k = 1)
    (hW : h.twSub y = Z) (hd : Z.relIndex U = 16) : False := by
  have hL := h.comm_mem_of_twSub_eq hperf hy hW hd
  obtain ⟨X, hZX, hXU, hXZ, hXU'⟩ := h.exists_mid_subgroup hd
  have hinv : ∀ l ∈ L, ∀ w ∈ X, l * w * l⁻¹ ∈ X := by
    intro l hl w hw
    have hcz : ⁅l, w⁆ ∈ Z := hL l hl w (hXU hw)
    have e : l * w * l⁻¹ = ⁅l, w⁆ * w := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact mul_mem (hZX hcz) hw
  rcases h.irr X hZX hXU hinv with h1 | h1
  exacts [hXZ h1, hXU' h1]

theorem comm_mem_Z [Finite G] (hperf : ⁅L, L⁆ = L) {k : ℕ} (hy : y ^ 5 ^ k = 1) {d : ℕ}
    (hd : Z.relIndex U = 2 ^ d) (hd' : d = 3 ∨ d = 4 ∨ d = 6) : ∀ u ∈ U, ⁅y, u⁆ ∈ Z := by
  rcases h.irr (h.twSub y) (h.Z_le_twSub h.yZ) (h.twSub_le y)
    (fun l hl w hw => h.normal_twSub hl hw) with hW | hW
  · exfalso
    have hmod := h.relIndex_modEq_one' (X := U) h.ZU le_rfl h.yU hy hW
    rw [hd] at hmod
    rcases hd' with rfl | rfl | rfl
    · exact absurd hmod (by decide)
    · exact h.false_of_sixteen hperf hy hW (by simpa using hd)
    · exact absurd hmod (by decide)
  · intro u hu
    have hmem : u ∈ h.twSub y := by rw [hW]; exact hu
    exact (h.mem_twSub.1 hmem).2

theorem y_comm_commutator (h1 : ∀ u ∈ U, ⁅y, u⁆ ∈ Z) {u l : G} (hu : u ∈ U) (hl : l ∈ L) :
    y * ⁅u, l⁆ * y⁻¹ = ⁅u, l⁆ := by
  set z : G := ⁅y, u⁆ with hz
  set q : G := ⁅l, y⁆ with hq
  have hzZ : z ∈ Z := h1 u hu
  have hzU : z ∈ U := h.ZU hzZ
  have hau : y * u * y⁻¹ = z * u := by
    simp only [hz, commutatorElement_def]
    group
  have hal : y * l * y⁻¹ = q⁻¹ * l := by
    simp only [hq, commutatorElement_def]
    group
  have hzu : Commute z u := h.abel z hzU u hu
  have hzq : Commute z q := (h.comm l hl z hzU).symm
  have hzl : Commute z l := (h.cent z hzZ l hl).symm
  have hqu : Commute q u := h.comm l hl u hu
  have hc : ⁅u, l⁆ ∈ U := by
    have := mul_mem hu (h.normU l hl u⁻¹ (inv_mem hu))
    simpa [commutatorElement_def, mul_assoc] using this
  have hw : Commute z (u * q⁻¹ * l * u⁻¹) :=
    ((hzu.mul_right hzq.inv_right).mul_right hzl).mul_right hzu.inv_right
  have hqi : u * q⁻¹ = q⁻¹ * u := (hqu.inv_left.eq).symm
  have hqc : q * ⁅u, l⁆ = ⁅u, l⁆ * q := h.comm l hl _ hc
  calc y * ⁅u, l⁆ * y⁻¹
      = (y * u * y⁻¹) * (y * l * y⁻¹) * (y * u * y⁻¹)⁻¹ * (y * l * y⁻¹)⁻¹ := by
        simp only [commutatorElement_def]
        group
    _ = z * (u * q⁻¹ * l * u⁻¹) * z⁻¹ * (l⁻¹ * q) := by
        rw [hau, hal]
        group
    _ = (u * q⁻¹ * l * u⁻¹) * (l⁻¹ * q) := by rw [hw.mul_inv_cancel]
    _ = ((u * q⁻¹) * l * u⁻¹) * (l⁻¹ * q) := by group
    _ = ((q⁻¹ * u) * l * u⁻¹) * (l⁻¹ * q) := by rw [hqi]
    _ = q⁻¹ * ⁅u, l⁆ * q := by
        simp only [commutatorElement_def]
        group
    _ = ⁅u, l⁆ := by rw [mul_assoc, ← hqc, ← mul_assoc, inv_mul_cancel, one_mul]

end ModData

end CFSG.Quasithin.H23P4
