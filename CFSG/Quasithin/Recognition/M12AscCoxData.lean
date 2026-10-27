module

public import CFSG.Quasithin.Recognition.M12AscCox
public import CFSG.Quasithin.Recognition.M12AscCoxRel

public section

namespace CFSG.Quasithin

open Subgroup

open CFSG.GH74.M12 (Asc03Hyp)

variable {G : Type*} [Group G] {z : G}

structure AscCox (m : AscModel z) where
  u' : G
  x1 : G
  hu' : u' = m.ψ mU ∨ u' = m.ψ (mU * mZ)
  x1_ord : orderOf x1 = 3
  x1_x : x1 * m.ψ mX = m.ψ mX * x1
  x1_u : x1 * u' = u' * x1
  x1_z : z * x1 * z⁻¹ = x1⁻¹
  x1_X : x1 ∉ zpowers (m.ψ mX)
  ρ : Equiv.Perm (Fin 6) →* G
  ρ_inj : Function.Injective ρ
  ρ_z : ρ (Equiv.swap 0 1) = z
  ρ_x1z : ρ (Equiv.swap 1 2) = x1 * z
  ρ_au : ρ (Equiv.swap 2 3) = m.ψ mA * u'
  ρ_ux : ρ (Equiv.swap 3 4) = u' * m.ψ mX
  ρ_u : ρ (Equiv.swap 4 5) = u'
  g : G
  g_conj : g * z * g⁻¹ = z * m.ψ mA
  u'_Qs : u' ∈ ascQ (z * m.ψ mA)

namespace AscModel

variable (m : AscModel z)

theorem exists_cox
    [Finite G] [IsSimpleGroup G] (hyp : Asc03Hyp G z) (h27 : 27 ∣ Nat.card G) :
    Nonempty (AscCox m) := by
  obtain ⟨u', x1, hu', hx1o, hx1x, hx1u, hx1z, hx1X, hsq, hrel, h13, g, hg, hQs⟩ :=
    m.exists_coxeter hyp h27
  obtain ⟨ρ, hρ⟩ := exists_perm_hom_of_coxeter (coxVec z x1 (m.ψ mA) u' (m.ψ mX)) hsq hrel
  have h0 : ρ (Equiv.swap 0 1) = z := by simpa [coxVec] using hρ 0
  have h1 : ρ (Equiv.swap 1 2) = x1 * z := by simpa [coxVec] using hρ 1
  have h2 : ρ (Equiv.swap 2 3) = m.ψ mA * u' := by simpa [coxVec] using hρ 2
  have h3 : ρ (Equiv.swap 3 4) = u' * m.ψ mX := by simpa [coxVec] using hρ 3
  have h4 : ρ (Equiv.swap 4 5) = u' := by simpa [coxVec] using hρ 4
  refine ⟨⟨u', x1, hu', hx1o, hx1x, hx1u, hx1z, hx1X, ρ, ?_, h0, h1, h2, h3, h4, g, hg, hQs⟩⟩
  apply coxeterA5_injective
  intro h
  apply h13
  rw [map_mul, h0, h2] at h
  simpa [coxVec] using h

end AscModel

end CFSG.Quasithin
