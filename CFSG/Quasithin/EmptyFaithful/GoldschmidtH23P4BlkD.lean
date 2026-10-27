module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4BlkB

public section

namespace CFSG.Quasithin.H23P4

open scoped commutatorElement

variable {G : Type*} [Group G]

structure ModData (L U Z : Subgroup G) (y : G) : Prop where
  ZU : Z ≤ U
  abel : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a
  exp : ∀ x ∈ U, x ^ 2 = 1
  cent : ∀ z ∈ Z, ∀ l ∈ L, l * z = z * l
  normU : ∀ l ∈ L, ∀ u ∈ U, l * u * l⁻¹ ∈ U
  yU : ∀ u ∈ U, y * u * y⁻¹ ∈ U
  yZ : ∀ z ∈ Z, y * z * y⁻¹ ∈ Z
  comm : ∀ l ∈ L, ∀ u ∈ U, ⁅l, y⁆ * u = u * ⁅l, y⁆
  irr : ∀ W : Subgroup G, Z ≤ W → W ≤ U → (∀ l ∈ L, ∀ w ∈ W, l * w * l⁻¹ ∈ W) →
    W = Z ∨ W = U

namespace ModData

variable {L U Z : Subgroup G} {y : G} (h : ModData L U Z y)
include h

theorem conj_comm {l u : G} (hl : l ∈ L) (hu : u ∈ U) :
    y * (l * u * l⁻¹) * y⁻¹ = l * (y * u * y⁻¹) * l⁻¹ := by
  have hw : (l * (y * u * y⁻¹) * l⁻¹) ∈ U := h.normU l hl _ (h.yU u hu)
  have hcomm := h.comm l hl _ hw
  have e1 : y * l * y⁻¹ = ⁅l, y⁆⁻¹ * l := by simp only [commutatorElement_def]; group
  have e2 : y * l⁻¹ * y⁻¹ = l⁻¹ * ⁅l, y⁆ := by simp only [commutatorElement_def]; group
  calc y * (l * u * l⁻¹) * y⁻¹
      = (y * l * y⁻¹) * (y * u * y⁻¹) * (y * l⁻¹ * y⁻¹) := by group
    _ = ⁅l, y⁆⁻¹ * (l * (y * u * y⁻¹) * l⁻¹) * ⁅l, y⁆ := by rw [e1, e2]; group
    _ = l * (y * u * y⁻¹) * l⁻¹ := by
      rw [mul_assoc, ← hcomm, ← mul_assoc, inv_mul_cancel, one_mul]

def twSub (g : G) : Subgroup G where
  carrier := {u | u ∈ U ∧ ⁅g, u⁆ ∈ Z}
  one_mem' := ⟨one_mem _, by simp [one_mem]⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨mul_mem ha hb, ?_⟩
    have e : ⁅g, a * b⁆ = ⁅g, a⁆ * (a * ⁅g, b⁆ * a⁻¹) := by
      simp only [commutatorElement_def]
      group
    have hc : a * ⁅g, b⁆ = ⁅g, b⁆ * a := h.abel a ha _ (h.ZU hb')
    have : a * ⁅g, b⁆ * a⁻¹ = ⁅g, b⁆ := by rw [hc, mul_assoc, mul_inv_cancel, mul_one]
    rw [e, this]
    exact mul_mem ha' hb'
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨inv_mem ha, ?_⟩
    have e : ⁅g, a⁻¹⁆ = a⁻¹ * ⁅g, a⁆⁻¹ * a := by
      simp only [commutatorElement_def]
      group
    have hc : a⁻¹ * ⁅g, a⁆⁻¹ = ⁅g, a⁆⁻¹ * a⁻¹ := h.abel _ (inv_mem ha) _ (h.ZU (inv_mem ha'))
    rw [e, hc, mul_assoc, inv_mul_cancel, mul_one]
    exact inv_mem ha'

theorem mem_twSub {g u : G} : u ∈ h.twSub g ↔ u ∈ U ∧ ⁅g, u⁆ ∈ Z := Iff.rfl

theorem twSub_le (g : G) : h.twSub g ≤ U := fun _ hu => hu.1

theorem Z_le_twSub {g : G} (hg : ∀ z ∈ Z, g * z * g⁻¹ ∈ Z) : Z ≤ h.twSub g := fun z hz =>
  ⟨h.ZU hz, by simpa [commutatorElement_def] using mul_mem (hg z hz) (inv_mem hz)⟩

theorem normal_twSub {l w : G} (hl : l ∈ L) (hw : w ∈ h.twSub y) :
    l * w * l⁻¹ ∈ h.twSub y := by
  obtain ⟨hwU, hz⟩ := hw
  refine ⟨h.normU l hl w hwU, ?_⟩
  have hz' : y * w * y⁻¹ = ⁅y, w⁆ * w := by
    simp only [commutatorElement_def]
    group
  have hlz : l * ⁅y, w⁆ * l⁻¹ = ⁅y, w⁆ := by
    rw [h.cent _ hz l hl, mul_assoc, mul_inv_cancel, mul_one]
  have e : ⁅y, l * w * l⁻¹⁆ = ⁅y, w⁆ := by
    rw [commutatorElement_def, h.conj_comm hl hwU, hz']
    calc l * (⁅y, w⁆ * w) * l⁻¹ * (l * w * l⁻¹)⁻¹ = l * ⁅y, w⁆ * l⁻¹ := by group
      _ = ⁅y, w⁆ := hlz
  rw [e]
  exact hz

theorem yConj_twSub {l u : G} (hl : l ∈ L) (hu : u ∈ h.twSub l) :
    y * u * y⁻¹ ∈ h.twSub l := by
  obtain ⟨huU, hz⟩ := hu
  refine ⟨h.yU u huU, ?_⟩
  have e : ⁅l, y * u * y⁻¹⁆ = y * ⁅l, u⁆ * y⁻¹ := by
    calc ⁅l, y * u * y⁻¹⁆ = l * (y * u * y⁻¹) * l⁻¹ * (y * u * y⁻¹)⁻¹ := by
          simp only [commutatorElement_def]
      _ = (y * (l * u * l⁻¹) * y⁻¹) * (y * u * y⁻¹)⁻¹ := by rw [h.conj_comm hl huU]
      _ = y * ⁅l, u⁆ * y⁻¹ := by simp only [commutatorElement_def]; group
  rw [e]
  exact h.yZ _ hz

theorem mem_twSub_of_fixed {x : G} (hx : x ∈ U) (hfx : y * x * y⁻¹ = x) : x ∈ h.twSub y := by
  refine ⟨hx, ?_⟩
  have : ⁅y, x⁆ = 1 := by
    rw [commutatorElement_def, hfx]
    group
  rw [this]
  exact one_mem _

theorem isPGroup_Z : IsPGroup 2 Z := fun z => ⟨1, Subtype.ext (by
  have := h.exp z (h.ZU z.2)
  simpa using this)⟩

variable [Finite G]

theorem relIndex_modEq_one' {X : Subgroup G} (hZX : Z ≤ X) (hXU : X ≤ U)
    (hX : ∀ x ∈ X, y * x * y⁻¹ ∈ X) {k : ℕ} (hy : y ^ 5 ^ k = 1) (hW : h.twSub y = Z) :
    Z.relIndex X ≡ 1 [MOD 5] :=
  relIndex_modEq_one hZX hX h.yZ hy (fun x hx hfx => by
    have := h.mem_twSub_of_fixed (hXU hx) hfx
    rwa [hW] at this) h.isPGroup_Z

theorem eq_or_eq_of_relIndex_sixteen {X : Subgroup G} (hZX : Z ≤ X) (hXU : X ≤ U)
    (hX : ∀ x ∈ X, y * x * y⁻¹ ∈ X) {k : ℕ} (hy : y ^ 5 ^ k = 1) (hW : h.twSub y = Z)
    (hd : Z.relIndex U = 16) : X = Z ∨ X = U := by
  have h1 := h.relIndex_modEq_one' hZX hXU hX hy hW
  have h2 : Z.relIndex X * X.relIndex U = 16 := by
    rw [Subgroup.relIndex_mul_relIndex Z X U hZX hXU, hd]
  have h3 : Z.relIndex X ∣ 16 := ⟨_, h2.symm⟩
  have h4 : Z.relIndex X = 1 ∨ Z.relIndex X = 16 := by
    have hle := Nat.le_of_dvd (by norm_num) h3
    unfold Nat.ModEq at h1
    generalize Z.relIndex X = r at *
    interval_cases r <;> omega
  rcases h4 with h4 | h4
  · exact Or.inl (le_antisymm (Subgroup.relIndex_eq_one.mp h4) hZX)
  · right
    rw [h4] at h2
    have h5 : X.relIndex U = 1 := by omega
    exact le_antisymm hXU (Subgroup.relIndex_eq_one.mp h5)

end ModData

end CFSG.Quasithin.H23P4
