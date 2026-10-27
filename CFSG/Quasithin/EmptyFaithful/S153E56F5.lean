module

public import CFSG.Quasithin.EmptyFaithful.S153E55B
public import CFSG.Quasithin.EmptyFaithful.S153EDefs2

public section

namespace CFSG.Quasithin

namespace S153E56f

open scoped commutatorElement Pointwise MatrixGroups

section Abelian

variable {G : Type} [Group G]

theorem comm_one_of_comm {A : Type*} [CommGroup A] (a b : A) : a * b * a⁻¹ * b⁻¹ = 1 := by
  rw [mul_comm a b, mul_inv_cancel_right, mul_inv_cancel]

theorem comm_mem_of_nat {M Si S S₂ : Subgroup G} {s : ℕ} (h : IsSumOfNatSL2ModulesN153 s M Si S S₂) :
    ∀ x ∈ Si, ∀ y ∈ Si, x * y * x⁻¹ * y⁻¹ ∈ S₂ := by
  obtain ⟨β, φ, -, -, -, hφk, -⟩ := h
  intro x hx y hy
  have h1 : φ (⟨x, hx⟩ * ⟨y, hy⟩ * ⟨x, hx⟩⁻¹ * ⟨y, hy⟩⁻¹ : ↥Si) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    exact comm_one_of_comm (φ ⟨x, hx⟩) (φ ⟨y, hy⟩)
  exact (hφk _).1 h1

theorem pdecomp_comm_mem_V {I P V N₁ N₂ P₁ P₂ : Subgroup G}
    (pd : S153E55.PDecomp I P V N₁ N₂ P₁ P₂) (h₁ : ∀ x ∈ P₁, ∀ y ∈ P₁, x * y * x⁻¹ * y⁻¹ ∈ V)
    (h₂ : ∀ x ∈ P₂, ∀ y ∈ P₂, x * y * x⁻¹ * y⁻¹ ∈ V) {a b : G} (ha : a ∈ P) (hb : b ∈ P) :
    a * b * a⁻¹ * b⁻¹ ∈ V := by
  obtain ⟨p₁, hp₁, p₂, hp₂, rfl⟩ := pd.exists_mul ha
  obtain ⟨q₁, hq₁, q₂, hq₂, rfl⟩ := pd.exists_mul hb
  have hP₁ : p₁ ∈ P := pd.P₁_le_P hp₁
  have hQ₁ : q₁ ∈ P := pd.P₁_le_P hq₁
  have hc12 : ∀ x ∈ P₁, ∀ y ∈ P₂, x * y * x⁻¹ * y⁻¹ ∈ V := by
    intro x hx y hy
    rw [← pd.inf]
    refine ⟨?_, ?_⟩
    · have h := pd.conj_P₁ (pd.P_le_I (pd.P₂_le_P hy)) (P₁.inv_mem hx)
      have e : x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) := by group
      rw [e]
      exact P₁.mul_mem hx h
    · have h := pd.conj_P₂ (pd.P_le_I (pd.P₁_le_P hx)) hy
      exact P₂.mul_mem h (P₂.inv_mem hy)
  have hc21 : ∀ x ∈ P₂, ∀ y ∈ P₁, x * y * x⁻¹ * y⁻¹ ∈ V := by
    intro x hx y hy
    have h := hc12 y hy x hx
    have e : x * y * x⁻¹ * y⁻¹ = (y * x * y⁻¹ * x⁻¹)⁻¹ := by group
    rw [e]
    exact V.inv_mem h
  have hVc : ∀ g ∈ P, ∀ v ∈ V, g * v * g⁻¹ ∈ V := fun g hg v hv => pd.conj_V (pd.P_le_I hg) hv
  have e : p₁ * p₂ * (q₁ * q₂) * (p₁ * p₂)⁻¹ * (q₁ * q₂)⁻¹ =
      (p₁ * ((p₂ * q₁ * p₂⁻¹ * q₁⁻¹) * (q₁ * (p₂ * q₂ * p₂⁻¹ * q₂⁻¹) * q₁⁻¹)) * p₁⁻¹) *
        ((p₁ * q₁ * p₁⁻¹ * q₁⁻¹) * (q₁ * (p₁ * q₂ * p₁⁻¹ * q₂⁻¹) * q₁⁻¹)) := by
    group
  rw [e]
  have A : p₂ * q₁ * p₂⁻¹ * q₁⁻¹ ∈ V := hc21 p₂ hp₂ q₁ hq₁
  have B : p₂ * q₂ * p₂⁻¹ * q₂⁻¹ ∈ V := h₂ p₂ hp₂ q₂ hq₂
  have C : p₁ * q₁ * p₁⁻¹ * q₁⁻¹ ∈ V := h₁ p₁ hp₁ q₁ hq₁
  have D : p₁ * q₂ * p₁⁻¹ * q₂⁻¹ ∈ V := hc12 p₁ hp₁ q₂ hq₂
  exact V.mul_mem (hVc p₁ hP₁ _ (V.mul_mem A (hVc q₁ hQ₁ _ B)))
    (V.mul_mem C (hVc q₁ hQ₁ _ D))

end Abelian

section Fpf

theorem sl2_fpf : ∀ A : SL(2, ZMod 2), A ≠ 1 → A ^ 3 = 1 → ∀ v : Fin 2 → ZMod 2, A • v = v →
    v = 0 := by
  decide +kernel

variable {G : Type} [Group G]

theorem fpf_mem {I P V N₁ N₂ P₁ P₂ : Subgroup G} (pd : S153E55.PDecomp I P V N₁ N₂ P₁ P₂) {s : ℕ}
    (hnat : IsSumOfNatSL2ModulesN153 s N₁ P₁ P V) {g e : G} (hg : g ∈ N₁) (hgP : g ∉ P)
    (hg3 : g ^ 3 ∈ P) (he : e ∈ P) (hcomm : e * g * e⁻¹ * g⁻¹ ∈ V) : e ∈ P₂ := by
  obtain ⟨β, φ, -, hβ, -, hφ, hφN⟩ := hnat
  have hβg1 : β ⟨g, hg⟩ ≠ 1 := fun h => hgP ((hβ ⟨g, hg⟩).1 h)
  have hβg3 : β ⟨g, hg⟩ ^ 3 = 1 := by
    rw [← map_pow]
    exact (hβ _).2 (by simpa using hg3)
  obtain ⟨p₁, hp₁, p₂, hp₂, rfl⟩ := pd.exists_mul he
  have hp₂c : p₂ ∈ centralizerMod V P N₁ := by
    rw [← pd.cent₂]
    exact hp₂
  have hv : p₂ * g * p₂⁻¹ * g⁻¹ ∈ V := hp₂c.2.2 g hg
  have hw : p₁ * g * p₁⁻¹ * g⁻¹ ∈ V := by
    have e1 : p₁ * g * p₁⁻¹ * g⁻¹ = (p₁ * (p₂ * g * p₂⁻¹ * g⁻¹) * p₁⁻¹)⁻¹ *
        (p₁ * p₂ * g * (p₁ * p₂)⁻¹ * g⁻¹) := by group
    rw [e1]
    exact V.mul_mem (V.inv_mem (pd.conj_V (pd.P_le_I (pd.P₁_le_P hp₁)) hv)) hcomm
  have hgI : g ∈ I := pd.N₁_le_I hg
  have hgp : g * p₁⁻¹ * g⁻¹ ∈ P₁ := pd.conj_P₁ hgI (P₁.inv_mem hp₁)
  have hφy := hφN ⟨g, hg⟩ (⟨p₁, hp₁⟩ : ↥P₁)⁻¹ ⟨g * p₁⁻¹ * g⁻¹, hgp⟩ rfl
  have hprod : φ ⟨p₁, hp₁⟩ * φ ⟨g * p₁⁻¹ * g⁻¹, hgp⟩ = 1 := by
    rw [← map_mul]
    refine (hφ _).2 ?_
    show p₁ * (g * p₁⁻¹ * g⁻¹) ∈ V
    simpa [mul_assoc] using hw
  have hx' : Multiplicative.toAdd (φ (⟨p₁, hp₁⟩ : ↥P₁)⁻¹) = -Multiplicative.toAdd (φ ⟨p₁, hp₁⟩) := by
    rw [map_inv, toAdd_inv]
  have key := congrArg Multiplicative.toAdd hprod
  rw [toAdd_mul, hφy, toAdd_ofAdd, hx', toAdd_one] at key
  have hzero : Multiplicative.toAdd (φ ⟨p₁, hp₁⟩) = 0 := by
    funext j
    have h1 := congrFun key j
    simp only [Pi.add_apply, Pi.neg_apply, Pi.zero_apply] at h1
    have h2 : Multiplicative.toAdd (φ ⟨p₁, hp₁⟩) j = β ⟨g, hg⟩ • Multiplicative.toAdd (φ ⟨p₁, hp₁⟩) j := by
      have h3 := eq_neg_of_add_eq_zero_left h1
      have e1 : β ⟨g, hg⟩ • (-(Multiplicative.toAdd (φ ⟨p₁, hp₁⟩) j)) =
          -(β ⟨g, hg⟩ • Multiplicative.toAdd (φ ⟨p₁, hp₁⟩) j) := smul_neg _ _
      rw [e1] at h3
      exact h3.trans (neg_neg _)
    exact sl2_fpf _ hβg1 hβg3 _ h2.symm
  have hp₁V : p₁ ∈ V := by
    refine (hφ ⟨p₁, hp₁⟩).1 ?_
    rw [← ofAdd_toAdd (φ ⟨p₁, hp₁⟩), hzero]
    rfl
  exact P₂.mul_mem (pd.V_le_P₂ hp₁V) hp₂

end Fpf

end S153E56f

end CFSG.Quasithin
