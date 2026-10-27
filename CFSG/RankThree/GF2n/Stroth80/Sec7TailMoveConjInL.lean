module

public import CFSG.RankThree.GF2n.Stroth80.Sec7TailMoveFrameAPI
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailMoveGroup

public section

namespace CFSG.RankThree.GF2n.Stroth80

open Subgroup CFSG.CGT.Timmesfeld75
open scoped commutatorElement

variable {K E X : Type*} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [Group X] [Finite X]
  {B : LinearMap.BilinForm K E} {φ : X →* (E ≃ₗ[K] E)} {V L Nb Rb : Subgroup X}
  {Tt : X → Submodule K E} {q : ℕ}

theorem MoveFrame.exists_conj_in_L (F : MoveFrame B φ V L Nb Rb Tt q) (h : X)
    (hK : ∀ a ∈ V, h * a * h⁻¹ ∈ normalizer (V : Set X))
    (hRb : ∀ a ∈ V, h * a * h⁻¹ ∈ Rb)
    (hInf : ∀ a ∈ V, h * a * h⁻¹ ∈ Nb → a = 1)
    (hVnot : ∀ a ∈ V, a ≠ 1 → ∀ n ∈ L, (h * a * h⁻¹) * n * (h * a * h⁻¹)⁻¹ * n⁻¹ ∈ V →
      (h * a * h⁻¹) * n * (h * a * h⁻¹)⁻¹ * n⁻¹ = 1)
    (hfar : ∀ x ∈ L, ∀ b ∈ V, h⁻¹ * (x * (h * b * h⁻¹) * x⁻¹) * h ∈ Nb)
    (a : X) (ha : a ∈ V) (ha1 : a ≠ 1) (x : X) (hxL : x ∈ L)
    (hxy : x * (h * a * h⁻¹) * x⁻¹ ≠ h * a * h⁻¹) :
    ∃ s ∈ V, s ≠ 1 ∧ ∃ g : X, g * s * g⁻¹ ∈ L ∧ g * s * g⁻¹ ∉ V := by
  have hyY : h * a * h⁻¹ ∈ conjSubgroup h V := mem_conjSubgroup_iff'.mpr ⟨a, ha, rfl⟩
  have hy1 : h * a * h⁻¹ ≠ 1 := by
    intro h1
    apply ha1
    calc a = h⁻¹ * (h * a * h⁻¹) * h := by group
      _ = 1 := by rw [h1, mul_one, inv_mul_cancel]
  have hy2 : h * a * h⁻¹ * (h * a * h⁻¹) = 1 := by
    have e : h * a * h⁻¹ * (h * a * h⁻¹) = h * (a * a) * h⁻¹ := by group
    rw [e, F.V_sq a ha, mul_one, mul_inv_cancel]
  have hyV : ∃ a' ∈ V, a' ≠ 1 ∧ ∃ h' : X, h * a * h⁻¹ = h' * a' * h'⁻¹ :=
    ⟨a, ha, ha1, h, rfl⟩
  have hYL : ∀ z ∈ conjSubgroup h V, z ∈ L → z = 1 := by
    intro z hz hzL
    obtain ⟨a', ha', rfl⟩ := mem_conjSubgroup_iff'.mp hz
    have hNb : h * a' * h⁻¹ ∈ Nb := F.L_le_Nb hzL
    rw [hInf a' ha' hNb, mul_one, mul_inv_cancel]
  have hyL : ∀ l ∈ L, h * a * h⁻¹ * l * (h * a * h⁻¹)⁻¹ ∈ L :=
    fun l hl => F.L_norm (h * a * h⁻¹) (hK a ha) l hl
  have hti : ∀ g : X, ∀ z ∈ conjSubgroup h V, z ≠ 1 →
      g * z * g⁻¹ ∈ conjSubgroup h V → g ∈ normalizer ((conjSubgroup h V : Subgroup X) : Set X) :=
    fun g z hz hz1 hg => F.ti_conj h g hz hz1 hg
  have hsemi : ∀ z ∈ conjSubgroup h Nb, z ∉ conjSubgroup h V → ∀ w ∈ conjSubgroup h V,
      ∃ m ∈ conjSubgroup h Nb, m * z * m⁻¹ = w * z := by
    intro z hz hzV w hw
    have hzN : h⁻¹ * z * h ∈ Nb := CFSG.CGT.Timmesfeld75.mem_conjSubgroup.mp hz
    have hzV' : h⁻¹ * z * h ∉ V := fun hc =>
      hzV (CFSG.CGT.Timmesfeld75.mem_conjSubgroup.mpr hc)
    have hwV : h⁻¹ * w * h ∈ V := CFSG.CGT.Timmesfeld75.mem_conjSubgroup.mp hw
    obtain ⟨m', hm'N, hm'⟩ := F.Nb_semi (h⁻¹ * z * h) hzN hzV' (h⁻¹ * w * h) hwV
    refine ⟨h * m' * h⁻¹, CFSG.CGT.Timmesfeld75.mem_conjSubgroup.mpr ?_, ?_⟩
    · have e : h⁻¹ * (h * m' * h⁻¹) * h = m' := by group
      rw [e]
      exact hm'N
    · have e1 : h * m' * h⁻¹ * z * (h * m' * h⁻¹)⁻¹ =
          h * (m' * (h⁻¹ * z * h) * m'⁻¹) * h⁻¹ := by
        group
      rw [e1, hm']
      group
  have hxN : x * (h * a * h⁻¹) * x⁻¹ ∈ conjSubgroup h Nb :=
    CFSG.CGT.Timmesfeld75.mem_conjSubgroup.mpr (hfar x hxL a ha)
  exact exists_conj_in_L_of_adjacent V (conjSubgroup h V) L (conjSubgroup h Nb)
    (h * a * h⁻¹) x hYL F.L_comm hyL hti hsemi (hVnot a ha ha1) hyY hy1 hy2 hyV hxL hxy hxN

end CFSG.RankThree.GF2n.Stroth80
