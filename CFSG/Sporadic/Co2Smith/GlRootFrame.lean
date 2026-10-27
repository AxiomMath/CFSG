module

public import CFSG.Sporadic.Co2Smith.GlDefs
public import CFSG.Sporadic.Co2Smith.GlDataRoot

public section

namespace CFSG.Sporadic.Co2Smith

open Subgroup CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Matrix

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

section Frame

variable {G : Type*} [Group G] {z : G}
  (φ : centralizer ({z} : Set G) ≃* Cz)

@[expose] noncomputable def phiInv (y : K) : G := by
  classical
  exact if h : y ∈ Cz then (φ.symm ⟨y, h⟩ : G) else 1

theorem phiInv_of_mem {y : K} (h : y ∈ Cz) : phiInv φ y = (φ.symm ⟨y, h⟩ : G) := by
  classical
  rw [phiInv, dite_eq_left h]

theorem phiInv_of_not_mem {y : K} (h : y ∉ Cz) : phiInv φ y = 1 := by
  classical
  rw [phiInv, dite_eq_right h]

theorem phiInv_mul {y y' : K} (h : y ∈ Cz) (h' : y' ∈ Cz) :
    phiInv φ (y * y') = phiInv φ y * phiInv φ y' := by
  rw [phiInv_of_mem φ (Cz.mul_mem h h'), phiInv_of_mem φ h, phiInv_of_mem φ h',
    show (⟨y * y', Cz.mul_mem h h'⟩ : Cz) = ⟨y, h⟩ * ⟨y', h'⟩ from rfl, map_mul]
  rfl

theorem phiInv_one : phiInv φ 1 = 1 := by
  rw [phiInv_of_mem φ Cz.one_mem, show (⟨1, Cz.one_mem⟩ : Cz) = 1 from rfl, map_one]
  rfl

theorem phiInv_inv {y : K} (h : y ∈ Cz) : phiInv φ y⁻¹ = (phiInv φ y)⁻¹ := by
  rw [phiInv_of_mem φ (Cz.inv_mem h), phiInv_of_mem φ h,
    show (⟨y⁻¹, Cz.inv_mem h⟩ : Cz) = (⟨y, h⟩ : Cz)⁻¹ from rfl, map_inv]
  rfl

theorem phiInv_mem (y : K) : phiInv φ y ∈ centralizer ({z} : Set G) := by
  by_cases h : y ∈ Cz
  · rw [phiInv_of_mem φ h]
    exact (φ.symm ⟨y, h⟩).2
  · rw [phiInv_of_not_mem φ h]
    exact Subgroup.one_mem _

theorem phiInv_injOn {y y' : K} (h : y ∈ Cz) (h' : y' ∈ Cz) (e : phiInv φ y = phiInv φ y') :
    y = y' := by
  rw [phiInv_of_mem φ h, phiInv_of_mem φ h'] at e
  have := φ.symm.injective (Subtype.ext e)
  exact congrArg Subtype.val this

theorem phi_phiInv {y : K} (h : y ∈ Cz) :
    (φ ⟨phiInv φ y, phiInv_mem φ y⟩ : K) = y := by
  have e : (⟨phiInv φ y, phiInv_mem φ y⟩ : centralizer ({z} : Set G)) = φ.symm ⟨y, h⟩ :=
    Subtype.ext (phiInv_of_mem φ h)
  rw [e, MulEquiv.apply_symm_apply]

theorem phiInv_phi (h : centralizer ({z} : Set G)) : phiInv φ (φ h : K) = (h : G) := by
  rw [phiInv_of_mem φ (φ h).2]
  simp

variable (ρ : C0c →* G)

@[expose] noncomputable def rhoK (g : K) : G := by
  classical
  exact if h : g ∈ C0c then ρ ⟨g, h⟩ else 1

theorem rhoK_of_mem {g : K} (h : g ∈ C0c) : rhoK ρ g = ρ ⟨g, h⟩ := by
  classical
  rw [rhoK, dite_eq_left h]

theorem rhoK_mul {g g' : K} (h : g ∈ C0c) (h' : g' ∈ C0c) :
    rhoK ρ (g * g') = rhoK ρ g * rhoK ρ g' := by
  rw [rhoK_of_mem ρ (C0c.mul_mem h h'), rhoK_of_mem ρ h, rhoK_of_mem ρ h', ← map_mul]
  rfl

theorem rhoK_one : rhoK ρ 1 = 1 := by
  rw [rhoK_of_mem ρ C0c.one_mem, show (⟨1, C0c.one_mem⟩ : C0c) = 1 from rfl, map_one]

theorem rhoK_inv {g : K} (h : g ∈ C0c) : rhoK ρ g⁻¹ = (rhoK ρ g)⁻¹ := by
  rw [rhoK_of_mem ρ (C0c.inv_mem h), rhoK_of_mem ρ h, ← map_inv]
  rfl

variable {φ ρ}

theorem rhoK_eq_phiInv {α3c : Cz} (hm : SmithC0Marking φ α3c ρ) {g : K} (hg : g ∈ C0c)
    (hz : g ∈ Cz) : rhoK ρ g = phiInv φ g := by
  rw [rhoK_of_mem ρ hg, phiInv_of_mem φ hz]
  exact hm.2.2 ⟨g, hg⟩ hz

theorem rhoK_conj_phiInv {α3c : Cz} (hm : SmithC0Marking φ α3c ρ) {g : K} (hg : g ∈ C0c)
    (hz : g ∈ Cz) (y : K) :
    rhoK ρ g * phiInv φ y * (rhoK ρ g)⁻¹ = phiInv φ (g * y * g⁻¹) := by
  rw [rhoK_eq_phiInv hm hg hz]
  by_cases hy : y ∈ Cz
  · rw [phiInv_mul φ (Cz.mul_mem hz hy) (Cz.inv_mem hz), phiInv_mul φ hz hy, phiInv_inv φ hz]
  · have hy' : g * y * g⁻¹ ∉ Cz := fun h => hy (by
      have := Cz.mul_mem (Cz.mul_mem (Cz.inv_mem hz) h) hz
      simpa [mul_assoc] using this)
    rw [phiInv_of_not_mem φ hy, phiInv_of_not_mem φ hy', mul_one, mul_inv_cancel]

end Frame

section Psi

variable {G : Type*} [Group G] {z : G}
  (φ : centralizer ({z} : Set G) ≃* Cz) (ρ : C0c →* G)

@[expose] noncomputable def psiE (y : K) : G := by
  classical
  exact if y ∈ Cz then phiInv φ y else rhoK ρ w1K * phiInv φ (w1K * y * w1K) * (rhoK ρ w1K)⁻¹

theorem psiE_of_mem {y : K} (h : y ∈ Cz) : psiE φ ρ y = phiInv φ y := by
  classical
  rw [psiE, ite_eq_left h]

theorem psiE_of_not_mem {y : K} (h : y ∉ Cz) :
    psiE φ ρ y = rhoK ρ w1K * phiInv φ (w1K * y * w1K) * (rhoK ρ w1K)⁻¹ := by
  classical
  rw [psiE, ite_eq_right h]

@[expose] noncomputable def rootSet : Set K := {y | ∃ r < 18, ∃ t < 4, y = xRootK r t}

@[expose] def Transp (g : K) : Prop :=
  (∀ y ∈ rootSet, g * y * g⁻¹ ∈ rootSet) ∧
    ∀ y ∈ rootSet, rhoK ρ g * psiE φ ρ y * (rhoK ρ g)⁻¹ = psiE φ ρ (g * y * g⁻¹)

variable {φ ρ}

theorem Transp.mul {g g' : K} (hg : g ∈ C0c) (hg' : g' ∈ C0c) (P : Transp φ ρ g)
    (P' : Transp φ ρ g') : Transp φ ρ (g * g') := by
  refine ⟨fun y hy => ?_, fun y hy => ?_⟩
  · have := P.1 _ (P'.1 y hy)
    simpa [mul_assoc] using this
  · rw [rhoK_mul ρ hg hg', _root_.mul_inv_rev]
    have e := P.2 _ (P'.1 y hy)
    rw [← P'.2 y hy] at e
    rw [show g * g' * y * (g * g')⁻¹ = g * (g' * y * g'⁻¹) * g⁻¹ by group, ← e]
    group

theorem Transp.one : Transp φ ρ 1 := by
  refine ⟨fun y hy => by simpa using hy, fun y _ => ?_⟩
  rw [rhoK_one, inv_one, one_mul, mul_one, one_mul, inv_one, mul_one]

end Psi

end CFSG.Sporadic.Co2Smith
