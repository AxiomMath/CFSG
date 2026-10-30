module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.GLTheoremA.CatB.A8Model
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.Sec21.FF84Defs

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open Equiv Equiv.Perm CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.CatB

theorem cen_c_mem3 {x : Perm (Fin 8)} (hxc : x * a8c = a8c * x) :
    x 0 = 0 ∨ x 0 = 1 ∨ x 0 = 2 := by
  have hcomm0 : a8c (x 0) = x 1 := by
    have := congrArg (fun f : Perm (Fin 8) => f 0) hxc
    simp only [Perm.mul_apply, a8c_apply0] at this
    exact this.symm
  by_contra hne
  push Not at hne
  have h3 : 3 ≤ (x 0).val := by
    by_contra hlt
    push Not at hlt
    rcases (fin8_lt3 _).1 hlt with e | e | e
    · exact hne.1 e
    · exact hne.2.1 e
    · exact hne.2.2 e
  have h1' : x 1 = x 0 := by rw [← hcomm0, a8c_fix _ h3]
  exact absurd (x.injective h1') (by decide)

theorem cen_c_swap0 {x y : Perm (Fin 8)} (hx : x * a8c = a8c * x) (hy : y * a8c = a8c * y) :
    (x * y) 0 = (y * x) 0 := by
  have key : ∀ x : Perm (Fin 8), x * a8c = a8c * x → ∃ a : ℕ, x 0 = (a8c ^ a) 0 := by
    intro x hx
    rcases cen_c_mem3 hx with e | e | e
    · exact ⟨0, by simp [e]⟩
    · exact ⟨1, by simp [e, a8c_apply0]⟩
    · exact ⟨2, by simp [e, pow_two, Perm.mul_apply, a8c_apply0, a8c_apply1]⟩
  have hp : ∀ z : Perm (Fin 8), z * a8c = a8c * z → ∀ k : ℕ, z ((a8c ^ k) 0) = (a8c ^ k) (z 0) := by
    intro z hz k
    have : z * a8c ^ k = a8c ^ k * z := ((show Commute z a8c from hz).pow_right k).eq
    exact congrArg (fun f : Perm (Fin 8) => f 0) this
  obtain ⟨a, ha⟩ := key x hx
  obtain ⟨b, hb⟩ := key y hy
  show x (y 0) = y (x 0)
  calc x (y 0) = x ((a8c ^ b) 0) := by rw [hb]
    _ = (a8c ^ b) (x 0) := hp x hx b
    _ = (a8c ^ b) ((a8c ^ a) 0) := by rw [ha]
    _ = (a8c ^ (b + a)) 0 := by rw [← Perm.mul_apply, ← pow_add]
    _ = (a8c ^ (a + b)) 0 := by rw [add_comm]
    _ = (a8c ^ a) ((a8c ^ b) 0) := by rw [pow_add, Perm.mul_apply]
    _ = (a8c ^ a) (y 0) := by rw [hb]
    _ = y ((a8c ^ a) 0) := (hp y hy a).symm
    _ = y (x 0) := by rw [ha]

theorem cen_c_comm_fix {x y : Perm (Fin 8)} (hx : x * a8c = a8c * x) (hy : y * a8c = a8c * y) :
    (x⁻¹ * y⁻¹ * x * y) 0 = 0 ∧ (x⁻¹ * y⁻¹ * x * y) 1 = 1 ∧ (x⁻¹ * y⁻¹ * x * y) 2 = 2 := by
  obtain ⟨z, hzd⟩ : ∃ z : Perm (Fin 8), z = x⁻¹ * y⁻¹ * x * y := ⟨_, rfl⟩
  rw [← hzd]
  have hz : z * a8c = a8c * z := by
    have hxc : Commute x a8c := hx
    have hyc : Commute y a8c := hy
    rw [hzd]
    exact ((((hxc.inv_left).mul_left (hyc.inv_left)).mul_left hxc).mul_left hyc).eq
  have h0 : z 0 = 0 := by
    have e : z = (y * x)⁻¹ * (x * y) := by rw [hzd]; group
    rw [e, Perm.mul_apply, cen_c_swap0 hx hy]
    exact (y * x).symm_apply_apply 0
  have h1 : z 1 = 1 := by
    have := congrArg (fun f : Perm (Fin 8) => f 0) hz
    simp only [Perm.mul_apply, a8c_apply0] at this
    rw [h0, a8c_apply0] at this
    exact this
  refine ⟨h0, h1, ?_⟩
  have := congrArg (fun f : Perm (Fin 8) => f 1) hz
  simp only [Perm.mul_apply, a8c_apply1] at this
  rw [h1, a8c_apply1] at this
  exact this

theorem perfect_cen_c {K₀ : Type*} [Group K₀] (hperf : commutator K₀ = ⊤)
    (φ : K₀ →* Perm (Fin 8)) (hc : ∀ k, φ k * a8c = a8c * φ k) :
    ∀ k, φ k 0 = 0 ∧ φ k 1 = 1 ∧ φ k 2 = 2 ∧ sign (φ k) = 1 := by
  let Q : Subgroup (Perm (Fin 8)) :=
    MulAction.stabilizer (Perm (Fin 8)) (0 : Fin 8) ⊓ MulAction.stabilizer (Perm (Fin 8)) (1 : Fin 8) ⊓
      MulAction.stabilizer (Perm (Fin 8)) (2 : Fin 8) ⊓ (sign : Perm (Fin 8) →* ℤˣ).ker
  have hQ : ∀ x : Perm (Fin 8), x ∈ Q ↔ x 0 = 0 ∧ x 1 = 1 ∧ x 2 = 2 ∧ sign x = 1 := by
    intro x
    simp only [Q, Subgroup.mem_inf, MulAction.mem_stabilizer_iff, Perm.smul_def, MonoidHom.mem_ker]
    tauto
  let H : Subgroup K₀ := Q.comap φ
  have hle : (⊤ : Subgroup K₀) ≤ H := by
    rw [← hperf]
    refine Subgroup.commutator_le.2 fun g₁ _ g₂ _ => ?_
    show φ (g₁ * g₂ * g₁⁻¹ * g₂⁻¹) ∈ Q
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hQ]
    have hx := hc g₁
    have hy := hc g₂
    have hx' : (φ g₁)⁻¹ * a8c = a8c * (φ g₁)⁻¹ := ((show Commute (φ g₁) a8c from hx).inv_left).eq
    have hy' : (φ g₂)⁻¹ * a8c = a8c * (φ g₂)⁻¹ := ((show Commute (φ g₂) a8c from hy).inv_left).eq
    obtain ⟨e0, e1, e2⟩ := cen_c_comm_fix hx' hy'
    simp only [inv_inv] at e0 e1 e2
    refine ⟨e0, e1, e2, ?_⟩
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    simp [mul_comm, mul_left_comm, mul_assoc]
  intro k
  exact (hQ _).1 (hle (Subgroup.mem_top k))

end CFSG.RankThree.PartTwo.Sec21.FF84.S4
