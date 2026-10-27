module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.FiberConj

public section

namespace CFSG.Quasithin

open CFSG.Open hiding StatedSL StatedSp
open CFSG.LieType.BorelTits
open CFSG.Assembly.LowTwoRank (StatedSL)

namespace Stellmacher.L3YC

section S1S2

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem alpha_eq_of_mul_inv_mem {L : Subgroup G} {F : Type} [Field F]
    {α : ↥L →* ↥(StatedSL 3 F)} (hα : IsModO2Surj L α) {u v : G} (hu : u ∈ L) (hv : v ∈ L)
    (h : u * v⁻¹ ∈ pCoreOf 2 L) : α ⟨u, hu⟩ = α ⟨v, hv⟩ := by
  obtain ⟨p, hp, hp1⟩ := exists_mem_ker_of_mem_pCoreOf hα h
  have : (⟨u, hu⟩ : ↥L) = p * ⟨v, hv⟩ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, hp]
    group
  rw [this, map_mul, hp1, one_mul]

theorem exists_s1 {L S : Subgroup G} (hq : IsLnTwoQuot L 3) {F : Type} [Field F]
    (α : ↥L →* ↥(StatedSL 3 F)) (hα : IsModO2Surj L α) (hPS : pCoreOf 2 L ≤ S)
    (hSL : S ≤ Subgroup.normalizer (L : Set G)) {y x r : G} (hx : x ∈ L) (hx3 : orderOf x = 3)
    (hxy : x * y = y * x) (hxb : orderOf (α ⟨x, hx⟩) = 3) (hrS : r ∈ S) (hrN : r ∈ N0 L)
    (hry : r * y * r⁻¹ = y⁻¹) :
    ∃ s ∈ S, s * y * s⁻¹ = y⁻¹ ∧ s * x * s⁻¹ = x := by
  have hx₁L : r * x * r⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hSL hrS) x).mp hx
  have hx₁3 : orderOf (r * x * r⁻¹) = 3 := by rw [orderOf_conj_eq, hx3]
  have hx₁y : y * (r * x * r⁻¹) = (r * x * r⁻¹) * y := by
    have h1 : x * y⁻¹ = y⁻¹ * x := by
      calc x * y⁻¹ = y⁻¹ * (y * x) * y⁻¹ := by group
        _ = y⁻¹ * (x * y) * y⁻¹ := by rw [hxy]
        _ = y⁻¹ * x := by group
    have h2 : r * y⁻¹ * r⁻¹ = y := by
      have : r * y⁻¹ * r⁻¹ = (r * y * r⁻¹)⁻¹ := by group
      rw [this, hry, inv_inv]
    calc y * (r * x * r⁻¹) = (r * y⁻¹ * r⁻¹) * (r * x * r⁻¹) := by rw [h2]
      _ = r * (y⁻¹ * x) * r⁻¹ := by group
      _ = r * (x * y⁻¹) * r⁻¹ := by rw [h1]
      _ = (r * x * r⁻¹) * (r * y⁻¹ * r⁻¹) := by group
      _ = (r * x * r⁻¹) * y := by rw [h2]
  have hαx₁ : α ⟨r * x * r⁻¹, hx₁L⟩ = α ⟨x, hx⟩ := by
    apply alpha_eq_of_mul_inv_mem hα
    have := hrN.2 x hx
    simpa [mul_assoc] using this
  obtain ⟨o, hoP, hoy, hxo⟩ := exists_conj_of_same_image hq α hα hx hx₁L hx3 hx₁3 hxy.symm hx₁y hxb hαx₁
  have hoS : o ∈ S := hPS hoP
  refine ⟨o⁻¹ * r, S.mul_mem (S.inv_mem hoS) hrS, ?_, ?_⟩
  · have hoy' : o⁻¹ * y * o = y := by
      calc o⁻¹ * y * o = o⁻¹ * (y * o) * 1 := by group
        _ = o⁻¹ * (o * y) := by rw [hoy]; group
        _ = y := by group
    calc o⁻¹ * r * y * (o⁻¹ * r)⁻¹ = o⁻¹ * (r * y * r⁻¹) * o := by group
      _ = o⁻¹ * y⁻¹ * o := by rw [hry]
      _ = (o⁻¹ * y * o)⁻¹ := by group
      _ = y⁻¹ := by rw [hoy']
  · calc o⁻¹ * r * x * (o⁻¹ * r)⁻¹ = o⁻¹ * (r * x * r⁻¹) * o := by group
      _ = o⁻¹ * (o * x * o⁻¹) * o := by rw [← hxo]
      _ = x := by group

theorem exists_s2 {L S : Subgroup G} (hq : IsLnTwoQuot L 3) {F : Type} [Field F]
    (α : ↥L →* ↥(StatedSL 3 F)) (hα : IsModO2Surj L α) (hPS : pCoreOf 2 L ≤ S)
    {y x m : G} (hx : x ∈ L) (hx3 : orderOf x = 3) (hxy : x * y = y * x)
    (hxb : orderOf (α ⟨x, hx⟩) = 3) (hmS : m ∈ S) (hmL : m ∈ L) (hmy : m * y = y * m)
    (hmx : α ⟨m, hmL⟩ * α ⟨x, hx⟩ * (α ⟨m, hmL⟩)⁻¹ = (α ⟨x, hx⟩)⁻¹) :
    ∃ s ∈ S, s * y * s⁻¹ = y ∧ s * x * s⁻¹ = x⁻¹ := by
  have hx₁L : m * x * m⁻¹ ∈ L := L.mul_mem (L.mul_mem hmL hx) (L.inv_mem hmL)
  have hx₁3 : orderOf (m * x * m⁻¹) = 3 := by rw [orderOf_conj_eq, hx3]
  have hx₁y : y * (m * x * m⁻¹) = (m * x * m⁻¹) * y := by
    have hmy' : m⁻¹ * y = y * m⁻¹ := by
      calc m⁻¹ * y = m⁻¹ * y * m * m⁻¹ := by group
        _ = m⁻¹ * (y * m) * m⁻¹ := by group
        _ = m⁻¹ * (m * y) * m⁻¹ := by rw [hmy]
        _ = y * m⁻¹ := by group
    calc y * (m * x * m⁻¹) = (y * m) * x * m⁻¹ := by group
      _ = (m * y) * x * m⁻¹ := by rw [hmy]
      _ = m * (y * x) * m⁻¹ := by group
      _ = m * (x * y) * m⁻¹ := by rw [hxy]
      _ = m * x * (y * m⁻¹) := by group
      _ = m * x * (m⁻¹ * y) := by rw [hmy']
      _ = (m * x * m⁻¹) * y := by group
  have hxiL : x⁻¹ ∈ L := L.inv_mem hx
  have hxi3 : orderOf x⁻¹ = 3 := by rw [orderOf_inv, hx3]
  have hxiy : y * x⁻¹ = x⁻¹ * y := by
    calc y * x⁻¹ = x⁻¹ * (x * y) * x⁻¹ := by group
      _ = x⁻¹ * (y * x) * x⁻¹ := by rw [hxy]
      _ = x⁻¹ * y := by group
  have hαi : α ⟨x⁻¹, hxiL⟩ = (α ⟨x, hx⟩)⁻¹ := by
    rw [← map_inv]; rfl
  have hxib : orderOf (α ⟨x⁻¹, hxiL⟩) = 3 := by rw [hαi, orderOf_inv, hxb]
  have hαx₁ : α ⟨m * x * m⁻¹, hx₁L⟩ = α ⟨x⁻¹, hxiL⟩ := by
    rw [hαi, ← hmx]
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  obtain ⟨o, hoP, hoy, hxo⟩ := exists_conj_of_same_image hq α hα hxiL hx₁L hxi3 hx₁3 hxiy hx₁y hxib
    hαx₁
  have hoS : o ∈ S := hPS hoP
  refine ⟨o⁻¹ * m, S.mul_mem (S.inv_mem hoS) hmS, ?_, ?_⟩
  · have hoy' : o⁻¹ * y * o = y := by
      calc o⁻¹ * y * o = o⁻¹ * (y * o) := by group
        _ = o⁻¹ * (o * y) := by rw [hoy]
        _ = y := by group
    calc o⁻¹ * m * y * (o⁻¹ * m)⁻¹ = o⁻¹ * (m * y * m⁻¹) * o := by group
      _ = o⁻¹ * y * o := by rw [hmy]; group
      _ = y := hoy'
  · calc o⁻¹ * m * x * (o⁻¹ * m)⁻¹ = o⁻¹ * (m * x * m⁻¹) * o := by group
      _ = o⁻¹ * (o * x⁻¹ * o⁻¹) * o := by rw [← hxo]
      _ = x⁻¹ := by group

end S1S2

end Stellmacher.L3YC

end CFSG.Quasithin
