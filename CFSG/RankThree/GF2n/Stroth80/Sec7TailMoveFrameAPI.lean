module

public import CFSG.RankThree.GF2n.Stroth80.Sec7TailMoveFrame
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailMoveIsometry

public section

namespace CFSG.RankThree.GF2n.Stroth80

open Subgroup CFSG.CGT.Timmesfeld75
open scoped commutatorElement

variable {K E X : Type*} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E] [Group X]

theorem opm_mul (a b : E ≃ₗ[K] E) (w : E) :
    opm (a * b) w = opm a w + opm b w + opm a (opm b w) := by
  simp only [opm_apply, LinearEquiv.mul_apply, map_sub]
  abel

theorem opm_sq_eq_zero (h2 : (2 : K) = 0) {g : E ≃ₗ[K] E} (hg : g * g = 1) (w : E) :
    opm g (opm g w) = 0 := by
  have hgg : g (g w) = w := by
    have h' := DFunLike.congr_fun hg w
    rw [LinearEquiv.mul_apply] at h'
    exact h'
  simp only [opm_apply, map_sub, hgg]
  have key : (w - g w) - (g w - w) = (2 : K) • (w - g w) := by
    rw [two_smul]
    abel
  rw [key, h2, zero_smul]

theorem opm_comm_of_comm {a b : E ≃ₗ[K] E} (h : a * b = b * a) (w : E) :
    opm a (opm b w) = opm b (opm a w) := by
  have hab : a (b w) = b (a w) := by
    have h' := DFunLike.congr_fun h w
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply] at h'
    exact h'
  simp only [opm_apply, map_sub, hab]
  abel

theorem phi_apply_inv_apply (φ : X →* (E ≃ₗ[K] E)) (g : X) (w : E) :
    φ g (φ g⁻¹ w) = w := by
  have hmul : φ g * φ g⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  have h' := DFunLike.congr_fun hmul w
  rw [LinearEquiv.mul_apply] at h'
  exact h'

theorem phi_inv_apply_phi (φ : X →* (E ≃ₗ[K] E)) (g : X) (w : E) :
    φ g⁻¹ (φ g w) = w := by
  have hmul : φ g⁻¹ * φ g = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  have h' := DFunLike.congr_fun hmul w
  rw [LinearEquiv.mul_apply] at h'
  exact h'

theorem opm_conj (φ : X →* (E ≃ₗ[K] E)) (g a : X) (w : E) :
    opm (φ (g * a * g⁻¹)) w = φ g (opm (φ a) (φ g⁻¹ w)) := by
  rw [opm_apply, opm_apply, map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
    map_sub, phi_apply_inv_apply φ g w]

theorem mem_conjSubgroup_iff' {V : Subgroup X} {h z : X} :
    z ∈ conjSubgroup h V ↔ ∃ a ∈ V, z = h * a * h⁻¹ := by
  constructor
  · intro hz
    refine ⟨h⁻¹ * z * h, CFSG.CGT.Timmesfeld75.mem_conjSubgroup.mp hz, ?_⟩
    group
  · rintro ⟨a, ha, rfl⟩
    refine CFSG.CGT.Timmesfeld75.mem_conjSubgroup.mpr ?_
    have e : h⁻¹ * (h * a * h⁻¹) * h = a := by group
    rw [e]
    exact ha

theorem mem_normalizer_conjSubgroup_iff {V : Subgroup X} {h y : X} :
    y ∈ normalizer ((conjSubgroup h V : Subgroup X) : Set X) ↔
      h⁻¹ * y * h ∈ normalizer (V : Set X) := by
  simp only [Subgroup.mem_normalizer_iff, SetLike.mem_coe,
    CFSG.CGT.Timmesfeld75.mem_conjSubgroup]
  constructor
  · intro H x
    have H' := H (h * x * h⁻¹)
    have e1 : h⁻¹ * (h * x * h⁻¹) * h = x := by group
    have e2 : h⁻¹ * (y * (h * x * h⁻¹) * y⁻¹) * h = h⁻¹ * y * h * x * (h⁻¹ * y * h)⁻¹ := by
      group
    rw [e1, e2] at H'
    exact H'
  · intro H x
    have H' := H (h⁻¹ * x * h)
    have e2 : h⁻¹ * y * h * (h⁻¹ * x * h) * (h⁻¹ * y * h)⁻¹ = h⁻¹ * (y * x * y⁻¹) * h := by
      group
    rw [e2] at H'
    exact H'

section MoveFrameAPI

variable {B : LinearMap.BilinForm K E} {φ : X →* (E ≃ₗ[K] E)} {V L Nb Rb : Subgroup X}
  {Tt : X → Submodule K E} {q : ℕ}

theorem MoveFrame.exists_ne_one (F : MoveFrame B φ V L Nb Rb Tt q) : ∃ a ∈ V, a ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hV : V = ⊥ := (Subgroup.eq_bot_iff_forall V).mpr hcon
  have h1 := F.V_card
  rw [hV, Subgroup.card_bot] at h1
  have h2 := F.q_ge
  omega

theorem MoveFrame.range_opm_V (F : MoveFrame B φ V L Nb Rb Tt q) {a : X} (ha : a ∈ V)
    (h1 : a ≠ 1) : LinearMap.range (opm (φ a)) = Tt 1 := by
  have h := F.Tt_range 1 a ha h1
  rw [one_mul, inv_one, mul_one] at h
  exact h

theorem MoveFrame.Tt_eq_map (F : MoveFrame B φ V L Nb Rb Tt q) (g : X) :
    Tt g = (Tt 1).map (φ g : E →ₗ[K] E) := by
  obtain ⟨a, ha, h1⟩ := F.exists_ne_one
  rw [← F.Tt_range g a ha h1, ← F.range_opm_V ha h1]
  ext w
  constructor
  · rintro ⟨x, rfl⟩
    refine Submodule.mem_map.mpr ⟨opm (φ a) (φ g⁻¹ x), LinearMap.mem_range_self _ _, ?_⟩
    exact (opm_conj φ g a x).symm
  · intro hw
    obtain ⟨y, ⟨x, rfl⟩, rfl⟩ := Submodule.mem_map.mp hw
    refine LinearMap.mem_range.mpr ⟨φ g x, ?_⟩
    have h2 := opm_conj φ g a (φ g x)
    rw [phi_inv_apply_phi φ g x] at h2
    exact h2

theorem MoveFrame.Tt_eq_of_mem_normalizer (F : MoveFrame B φ V L Nb Rb Tt q) {y : X}
    (hy : y ∈ normalizer (V : Set X)) : Tt y = Tt 1 := by
  obtain ⟨a, ha, h1⟩ := F.exists_ne_one
  have hb : y * a * y⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hy a).mp ha
  have hb1 : y * a * y⁻¹ ≠ 1 := by
    intro h
    apply h1
    simpa using h
  rw [← F.Tt_range y a ha h1, ← F.Tt_range 1 (y * a * y⁻¹) hb hb1]
  simp only [one_mul, inv_one, mul_one]

theorem MoveFrame.map_Tt_one_le (F : MoveFrame B φ V L Nb Rb Tt q) {y : X}
    (hy : y ∈ normalizer (V : Set X)) {w : E} (hw : w ∈ Tt 1) : φ y w ∈ Tt 1 := by
  have h : φ y w ∈ (Tt 1).map (φ y : E →ₗ[K] E) := Submodule.mem_map_of_mem hw
  rw [← F.Tt_eq_map y, F.Tt_eq_of_mem_normalizer hy] at h
  exact h

theorem MoveFrame.map_orthogonal_le (F : MoveFrame B φ V L Nb Rb Tt q) {y : X}
    (hy : y ∈ normalizer (V : Set X)) {w : E} (hw : w ∈ B.orthogonal (Tt 1)) :
    φ y w ∈ B.orthogonal (Tt 1) := by
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  intro t ht
  have hs : φ y⁻¹ t ∈ Tt 1 := F.map_Tt_one_le (inv_mem hy) ht
  have e : φ y (φ y⁻¹ t) = t := phi_apply_inv_apply φ y t
  have h1 := F.isom y (φ y⁻¹ t) w
  rw [e] at h1
  rw [h1]
  exact LinearMap.BilinForm.mem_orthogonal_iff.mp hw _ hs

theorem MoveFrame.ker_opm_conj (F : MoveFrame B φ V L Nb Rb Tt q) (g : X) {a : X} (ha : a ∈ V)
    (h1 : a ≠ 1) : LinearMap.ker (opm (φ (g * a * g⁻¹))) = B.orthogonal (Tt g) := by
  rw [← F.Tt_range g a ha h1]
  exact ker_opm_eq_orthogonal_range B F.nondeg F.refl (φ (g * a * g⁻¹))
    (fun x y => F.isom (g * a * g⁻¹) x y)

theorem MoveFrame.finrank_range_opm_conj (F : MoveFrame B φ V L Nb Rb Tt q) (g : X) {a : X}
    (ha : a ∈ V) (h1 : a ≠ 1) :
    Module.finrank K (LinearMap.range (opm (φ (g * a * g⁻¹)))) = 6 := by
  rw [F.Tt_range g a ha h1]
  exact F.Tt_rank g

theorem MoveFrame.ti_conj (F : MoveFrame B φ V L Nb Rb Tt q) (h g : X) {z : X}
    (hz : z ∈ conjSubgroup h V) (hz1 : z ≠ 1) (hg : g * z * g⁻¹ ∈ conjSubgroup h V) :
    g ∈ normalizer ((conjSubgroup h V : Subgroup X) : Set X) := by
  obtain ⟨a, ha, rfl⟩ := mem_conjSubgroup_iff'.mp hz
  have ha1 : a ≠ 1 := by
    rintro rfl
    exact hz1 (by simp)
  have hk : h⁻¹ * g * h * a * (h⁻¹ * g * h)⁻¹ ∈ V := by
    have h2 := CFSG.CGT.Timmesfeld75.mem_conjSubgroup.mp hg
    have e : h⁻¹ * (g * (h * a * h⁻¹) * g⁻¹) * h = h⁻¹ * g * h * a * (h⁻¹ * g * h)⁻¹ := by
      group
    rw [e] at h2
    exact h2
  exact mem_normalizer_conjSubgroup_iff.mpr (F.ti (h⁻¹ * g * h) a ha ha1 hk)

theorem MoveFrame.opm_sq (F : MoveFrame B φ V L Nb Rb Tt q) {a : X} (ha : a ∈ V) (g : X)
    (w : E) : opm (φ (g * a * g⁻¹)) (opm (φ (g * a * g⁻¹)) w) = 0 := by
  have hsq : g * a * g⁻¹ * (g * a * g⁻¹) = 1 := by
    have e : g * a * g⁻¹ * (g * a * g⁻¹) = g * (a * a) * g⁻¹ := by group
    rw [e, F.V_sq a ha, mul_one, mul_inv_cancel]
  have hφ : φ (g * a * g⁻¹) * φ (g * a * g⁻¹) = 1 := by
    rw [← map_mul, hsq, map_one]
  exact opm_sq_eq_zero F.char2 hφ w

end MoveFrameAPI

end CFSG.RankThree.GF2n.Stroth80
