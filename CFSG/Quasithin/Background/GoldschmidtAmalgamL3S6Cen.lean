module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3S6Pair
public import CFSG.Quasithin.Background.GoldschmidtAmalgamLab7Red
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3SPair

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {z : D} {V : Subgroup D}

namespace GoldHyp3

variable (h : GoldHyp3 A B z V)

include h

theorem centralizes_of_noACentral (hA : NoACentral A B) {x β : CosetGeom (A ⊔ B) A B}
    (hxβ : (graph (A ⊔ B) A B).Adj x β) (hx : vtype x = false) {ω : D}
    (hωT : ω ∈ stab x ⊓ stab β) (hωc : ∀ t ∈ stab x ⊓ stab β, t * ω = ω * t)
    (hω2 : ω ^ 2 = 1) : ∀ y ∈ stab β, y * ω * y⁻¹ = ω := by
  have h32 : 32 ≤ Nat.card ↥(A ⊓ B) := by
    have := h.sixty_four_le_card_inf
    omega
  obtain ⟨k, rfl, rfl⟩ := exists_smul_edge_AB hxβ hx
  rw [stab_smul, stab_smul, stab_γ₀ (le_sup_left : A ≤ A ⊔ B),
    stab_γ₁ (le_sup_right : B ≤ A ⊔ B), ← conjSub_inf] at hωT hωc
  have hω'T : (k : D)⁻¹ * ω * k ∈ A ⊓ B := mem_conjSub.mp hωT
  have hω'Z : (k : D)⁻¹ * ω * k ∈ centerOf (A ⊓ B) := by
    refine Subgroup.mem_inf.mpr ⟨hω'T, Subgroup.mem_centralizer_iff.mpr fun t ht => ?_⟩
    have hc := hωc ((k : D) * t * (k : D)⁻¹) (mul_mem_conjSub ht)
    calc t * ((k : D)⁻¹ * ω * k) = (k : D)⁻¹ * (((k : D) * t * (k : D)⁻¹) * ω) * k := by group
      _ = (k : D)⁻¹ * (ω * ((k : D) * t * (k : D)⁻¹)) * k := by rw [hc]
      _ = ((k : D)⁻¹ * ω * k) * t := by group
  have hω'2 : ((k : D)⁻¹ * ω * k) ^ 2 = 1 := by
    have e : ((k : D)⁻¹ * ω * k) ^ 2 = (k : D)⁻¹ * ω ^ 2 * k := by
      simp only [pow_two]
      group
    rw [e, hω2]
    group
  have hcen := hA.centralizes_of_involution h.gold h32 hω'Z hω'2
  intro y hy
  rw [stab_smul, stab_γ₁ (le_sup_right : B ≤ A ⊔ B), mem_conjSub] at hy
  have := hcen _ hy
  have e : y * ω * y⁻¹ = (k : D) * (((k : D)⁻¹ * y * k) * ((k : D)⁻¹ * ω * k) *
      ((k : D)⁻¹ * y * k)⁻¹) * (k : D)⁻¹ := by group
  rw [e, this]
  group

theorem inf_kernels_eq {β s₁ s₃ x : CosetGeom (A ⊔ B) A B} (hβ : vtype β = true)
    (h1 : (graph (A ⊔ B) A B).Adj β s₁) (h3 : (graph (A ⊔ B) A B).Adj β s₃)
    (hx : (graph (A ⊔ B) A B).Adj β x) (n13 : s₁ ≠ s₃) (n1x : s₁ ≠ x) (n3x : s₃ ≠ x)
    (hle : ballStab 1 s₁ ⊓ ballStab 1 β ≤ ballStab 1 s₃) :
    ballStab 1 s₃ ⊓ ballStab 1 β = ballStab 1 s₁ ⊓ ballStab 1 β ∧
      ballStab 1 x ⊓ ballStab 1 β = ballStab 1 s₁ ⊓ ballStab 1 β := by
  have hs1 := vtype_eq_false_of_adj h1 hβ
  have hs3 := vtype_eq_false_of_adj h3 hβ
  have e3 : ballStab 1 s₃ ⊓ ballStab 1 β = ballStab 1 s₁ ⊓ ballStab 1 β := by
    refine (Subgroup.eq_of_le_of_card_ge (le_inf hle inf_le_right) ?_).symm
    exact ((h.card_ballStab_inf_edge h3.symm hs3).trans
      (h.card_ballStab_inf_edge h1.symm hs1).symm).le
  refine ⟨e3, ?_⟩
  obtain ⟨k, hkβ, hks₁, hkx⟩ := h.exists_swap_B h1 hs1 h3 hx n13 n1x n3x
  have hkβ' : k • β = β := smul_eq_of_mem_stab hkβ
  have hks₁' : k • s₁ = s₁ := smul_eq_of_mem_stab hks₁
  have hcon : ∀ w : CosetGeom (A ⊔ B) A B, ballStab 1 (k • w) ⊓ ballStab 1 β =
      conjSub (k : D) (ballStab 1 w ⊓ ballStab 1 β) := by
    intro w
    rw [conjSub_inf, ← ballStab_smul, ← ballStab_smul, hkβ']
  calc ballStab 1 x ⊓ ballStab 1 β = ballStab 1 (k • s₃) ⊓ ballStab 1 β := by rw [hkx]
    _ = conjSub (k : D) (ballStab 1 s₃ ⊓ ballStab 1 β) := hcon s₃
    _ = conjSub (k : D) (ballStab 1 s₁ ⊓ ballStab 1 β) := by rw [e3]
    _ = ballStab 1 (k • s₁) ⊓ ballStab 1 β := (hcon s₁).symm
    _ = ballStab 1 s₁ ⊓ ballStab 1 β := by rw [hks₁']

theorem conj_factor {u β : CosetGeom (A ⊔ B) A B} (hu : vtype u = false)
    (huβ : (graph (A ⊔ B) A B).Adj u β) {g : D} (hgu : g ∈ stab u) (hgβ : g ∈ stab β) {a : D}
    (ha : a ∈ Vv V u) (ha1 : a ∉ Zv z β) :
    ∃ ζ ∈ Zv z β, g * a * g⁻¹ = ζ * a ∧ (ζ = 1 ↔ g ∈ ballStab 1 u) := by
  have hβ : vtype β = true := vtype_eq_true_of_adj huβ hu
  let k : ↥(A ⊔ B) := ⟨g, stab_le u hgu⟩
  have hku : k • u = u := smul_eq_of_mem_stab hgu
  have hkβ : k • β = β := smul_eq_of_mem_stab hgβ
  have hga : g * a * g⁻¹ ∈ Vv V u := by
    have : g * a * g⁻¹ ∈ Vv V (k • u) := by
      rw [h.Vv_smul' k u]
      exact mul_mem_conjSub ha
    rwa [hku] at this
  have hga1 : g * a * g⁻¹ ∉ Zv z β := fun hmem => ha1 ((h.conj_mem_Zv_iff hkβ).mp hmem)
  have hζ : (g * a * g⁻¹) * a⁻¹ ∈ Zv z β := h.mul_inv_mem_Zv_of_Vv hu huβ ha ha1 hga hga1
  refine ⟨(g * a * g⁻¹) * a⁻¹, hζ, by group, ⟨fun hζ1 => ?_, fun hgQ => ?_⟩⟩
  ·
    have hga' : g * a * g⁻¹ = a := by
      have : g * a * g⁻¹ = ((g * a * g⁻¹) * a⁻¹) * a := by group
      rw [this, hζ1]
      group
    refine h.mem_ballStab_one_of_centralizes hu hgu fun w hw => ?_
    have hle : Vv V u ≤ Subgroup.centralizer ({g} : Set D) := by
      refine (h.Vv_le_Zv_sup_zpowers hu huβ ha ha1).trans (sup_le ?_ ?_)
      · intro c hc
        rw [Subgroup.mem_centralizer_singleton_iff]
        have := h.conj_eq_of_mem_stab_Zv hβ hgβ hc
        exact (mul_inv_eq_iff_eq_mul.mp this).symm
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
        exact (mul_inv_eq_iff_eq_mul.mp hga').symm
    have := Subgroup.mem_centralizer_singleton_iff.mp (hle hw)
    exact mul_inv_eq_iff_eq_mul.mpr this.symm
  · have := h.ballStab_one_le_centralizer hu hgQ ha
    rw [this]
    group

end GoldHyp3

end GoldAmL3

end F6

end CFSG.Quasithin
