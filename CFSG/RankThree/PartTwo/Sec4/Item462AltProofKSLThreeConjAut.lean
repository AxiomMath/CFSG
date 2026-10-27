module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiCaseA

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item462AltProof.KSLThree

open CFSG.RankThree.PartTwo.Sec4

theorem exists_conjAut_slPi {π : Bool} {p f : ℕ} {K : Type} [Field K] (hK : PiField π p f K)
    {H : GL (Fin 3) K} (hH : H ∈ glPi π 3 (p ^ f) K) :
    ∃ γ : MulAut (slPi π 3 (p ^ f) K),
      ∀ s, ((γ s : slPi π 3 (p ^ f) K) : GL (Fin 3) K) = H * (s : GL (Fin 3) K) * H⁻¹ := by
  have hπ : π = false → CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K :=
    fun h => by subst h; exact hK.unitary
  have h1 : ∀ s : slPi π 3 (p ^ f) K, H * (s : GL (Fin 3) K) * H⁻¹ ∈ slPi π 3 (p ^ f) K :=
    fun s => conj_mem_slPi hπ hH s.2
  have h2 : ∀ s : slPi π 3 (p ^ f) K, H⁻¹ * (s : GL (Fin 3) K) * H ∈ slPi π 3 (p ^ f) K :=
    fun s => by simpa using conj_mem_slPi hπ (inv_mem hH) s.2
  refine ⟨{ toFun := fun s => ⟨H * s * H⁻¹, h1 s⟩
            invFun := fun s => ⟨H⁻¹ * s * H, h2 s⟩
            left_inv := fun s => Subtype.ext (by
              show H⁻¹ * (H * (s : GL (Fin 3) K) * H⁻¹) * H = (s : GL (Fin 3) K)
              group)
            right_inv := fun s => Subtype.ext (by
              show H * (H⁻¹ * (s : GL (Fin 3) K) * H) * H⁻¹ = (s : GL (Fin 3) K)
              group)
            map_mul' := fun a b => Subtype.ext (by
              show H * ((a : GL (Fin 3) K) * (b : GL (Fin 3) K)) * H⁻¹ =
                (H * (a : GL (Fin 3) K) * H⁻¹) * (H * (b : GL (Fin 3) K) * H⁻¹)
              group) }, fun s => rfl⟩

end CFSG.RankThree.PartTwo.Sec4.Item462AltProof.KSLThree

end
