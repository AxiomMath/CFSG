module

public import CFSG.Quasithin.AppendixH.H9.H92.NonQuad.OrbitSubspace
public import CFSG.Quasithin.AppendixH.H9.H92.NonQuad.OrbitStabilizerCount

public section

open scoped Matrix

namespace CFSG.ASVolI.ChH

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem card_le_sixteen_of_finrank_nilOrbitSpace_eq_four {E : Subgroup (GL (Fin 5) (ZMod 2))}
    {𝒩 : Submodule (ZMod 2) (Matrix (Fin 5) (Fin 5) (ZMod 2))} (h : SubOneCover E 𝒩)
    {v : Fin 5 → ZMod 2} (hv : v ≠ 0)
    (hS : Module.finrank (ZMod 2) (nilOrbitSpace 𝒩 v) = 4) : Nat.card E ≤ 16 := by
  have hW : nilOrbitSpan 𝒩 v = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have h1 := finrank_nilOrbitSpace_lt h hv
    have h2 := Submodule.finrank_le (nilOrbitSpan 𝒩 v)
    rw [Module.finrank_fin_fun] at h2 ⊢
    omega
  have hfix : ∀ k ∈ E, (k : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ v = v → k = 1 := by
    intro k hk hkv
    refine eq_one_of_sub_one_mulVec_eq_zero fun w => ?_
    exact sub_one_mulVec_eq_zero_of_fix h hk hkv (by rw [hW]; exact Submodule.mem_top)
  have hcount := card_le_card_mul_card_of_stabilizer_embeds (E := E) (v := v)
    (nilOrbitSpace 𝒩 v) ⊥ (fun _ => 0)
    (fun k hk => mulVec_sub_self_mem_nilOrbitSpace h hk v) (fun k _ _ => Submodule.zero_mem _)
    (fun k₁ hk₁ k₂ hk₂ h1 h2 _ => (hfix k₁ hk₁ h1).trans (hfix k₂ hk₂ h2).symm)
  have hcardS : Nat.card (nilOrbitSpace 𝒩 v) = 16 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), hS, Nat.card_zmod]
    norm_num
  have hcardT : Nat.card (⊥ : Submodule (ZMod 2) (Fin 5 → ZMod 2)) = 1 := by simp
  rw [hcardS, hcardT] at hcount
  omega

end CFSG.ASVolI.ChH
