module

public import CFSG.Quasithin.Recognition.M12AscP2Elt
public import CFSG.Quasithin.Recognition.M12AscModel

public section

namespace CFSG.Quasithin

open Subgroup

variable {G : Type*} [Group G] {z : G}

@[expose] def nrmG (x f : G) : G := f * ((x * (f * (x * x))) * ((x * x) * (f * x)))

namespace AscModel

variable (m : AscModel z)

@[expose] noncomputable def ψ : ↥ascHModel →* G :=
  (ascH z).subtype.comp m.φ.symm.toMonoidHom

theorem ψ_apply (p : ↥ascHModel) : m.ψ p = ((m.φ.symm p : ↥(ascH z)) : G) := rfl

theorem ψ_mem (p : ↥ascHModel) : m.ψ p ∈ ascH z := (m.φ.symm p).2

theorem ψ_injective : Function.Injective m.ψ := fun _ _ h =>
  m.φ.symm.injective (Subtype.ext h)

theorem tb_ψ (p : ↥ascHModel) : m.tb (m.ψ p) = tabOf (p : Equiv.Perm (Fin 12)) := by
  rw [m.tb_of_mem (m.ψ_mem p)]
  have : (⟨m.ψ p, m.ψ_mem p⟩ : ↥(ascH z)) = m.φ.symm p := rfl
  rw [this, MulEquiv.apply_symm_apply]

theorem ψ_hz : m.ψ mZ = z := by
  have h : m.φ ⟨z, z_mem_ascH z⟩ = mZ := Subtype.ext (by rw [m.hz]; rfl)
  rw [ψ_apply, ← h]
  simp

theorem ψ_comm_z (p : ↥ascHModel) : m.ψ p * z = z * m.ψ p :=
  Subgroup.mem_centralizer_singleton_iff.1 (m.ψ_mem p)

theorem tb_nrmG [Finite G] {x f : G} (hx : x ∈ ascH z) (hf : f ∈ ascH z) :
    m.tb (nrmG x f) = nrm (m.tb x) (m.tb f) := by
  have hxx : x * x ∈ ascH z := mul_mem hx hx
  unfold nrmG nrm
  rw [m.tb_mul hf (mul_mem (mul_mem hx (mul_mem hf hxx)) (mul_mem hxx (mul_mem hf hx))),
    m.tb_mul (mul_mem hx (mul_mem hf hxx)) (mul_mem hxx (mul_mem hf hx)),
    m.tb_mul hx (mul_mem hf hxx), m.tb_mul hf hxx, m.tb_mul hx hx,
    m.tb_mul hxx (mul_mem hf hx), m.tb_mul hf hx, m.tb_mul hx hx]

end AscModel

end CFSG.Quasithin
