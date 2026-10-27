module

public import CFSG.LocalAnalysis.StandardType.GGTwE6KGA1Bridge
public import CFSG.LocalAnalysis.StandardType.GGTableBF4Three
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.StandardType.TwE6OuterGen

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open


theorem exists_conj_mem_torusGroup_of_le {K : Type} [Field K] [Finite K]
    (h3 : 3 ∣ Nat.card K - 1) {Y : Subgroup (ModGL TwistTag.E6.tag K)}
    (hY : Y ≤ twistedFixedGroup TwistTag.E6 K (RingHom.id K)) (hel : IsElemAbelian 3 Y)
    (hc : Nat.card Y = 3 ^ 4) :
    ∃ γ ∈ twistedFixedGroup TwistTag.E6 K (RingHom.id K),
      ∀ y ∈ Y, γ * y * γ⁻¹ ∈ torusGroup TwistTag.E6.tag K := by
  let Γ : Subgroup (ModGL TwistTag.E6.tag K) := twistedFixedGroup TwistTag.E6 K (RingHom.id K)
  let Ψ : Γ ≃* adjointGroup Tag.F4 K := CFSG.HardMathSupport.Lang.AnisoE6.e6FixedF4EquivAll K
  let E : Subgroup (adjointGroup Tag.F4 K) := (Y.subgroupOf Γ).map Ψ.toMonoidHom
  have hE : IsElemAbelian 3 E := (hel.subgroupOf Γ).map Ψ.toMonoidHom
  have hcard : Nat.card E = 3 ^ 4 := by
    have h1 : Nat.card E = Nat.card (Y.subgroupOf Γ) := Subgroup.card_map_of_injective Ψ.injective
    rw [h1, ← hc]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hY).toEquiv
  obtain ⟨g₄, hg₄⟩ := TableBF4.ggF4ToralRankInput_three (K := K) h3 E hE (le_of_eq hcard.symm)
  refine ⟨(Ψ.symm g₄ : ModGL TwistTag.E6.tag K), (Ψ.symm g₄).2, fun y hy => ?_⟩
  let yΓ : Γ := ⟨y, hY hy⟩
  have hyE : Ψ yΓ ∈ E := ⟨yΓ, hy, rfl⟩
  have hconj : (MulAut.conj g₄).toMonoidHom (Ψ yΓ) ∈ TableBF4.torusPow K 3 := by
    rw [← hg₄]
    exact ⟨Ψ yΓ, hyE, rfl⟩
  have hval : Ψ (Ψ.symm g₄ * yΓ * (Ψ.symm g₄)⁻¹) = (MulAut.conj g₄).toMonoidHom (Ψ yΓ) := by
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    rfl
  have hT := NoOffTwE6Three.e6FixedF4EquivAll_symm_mem_torusGroup
    (Ψ.symm g₄ * yΓ * (Ψ.symm g₄)⁻¹) (by rw [hval]; exact (TableBF4.mem_torusPow.mp hconj).1)
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv] at hT
  exact hT

end CFSG.StandardType.TwE6OuterGen

end
