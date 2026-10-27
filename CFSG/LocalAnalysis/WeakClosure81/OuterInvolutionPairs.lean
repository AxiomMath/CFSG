module

public import CFSG.LocalAnalysis.WeakClosure81.EightSixBorelGroup
public import CFSG.Quasithin.Vol2.Ch11SecU1U3C
public import CFSG.Quasithin.Vol2.Ch11SecU1U3A

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.Quasithin.Vol2.Ch11.SecU1.U3 (mem_of_isInnerAut)
open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem outer_pair_of_isCyclic_out_image {L : Subgroup G} [L.Normal]
    (hC : Subgroup.centralizer (L : Set G) = ⊥)
    (hOut : ∀ B : Subgroup (MulAut ↥L), IsPGroup 2 B →
      IsCyclic (B.map (QuotientGroup.mk' (inner ↥L)))) :
    ∀ t₁ t₂ : G, t₁ ∉ L → t₂ ∉ L →
      orderOf t₁ = 2 → orderOf t₂ = 2 → t₁ * t₂ = t₂ * t₁ → t₁ * t₂ ∈ L := by
  classical
  haveI : Finite ↥L := Subtype.finite
  intro t₁ t₂ ht₁L ht₂L ht₁ ht₂ hcomm
  have ht₁sq : t₁ * t₁ = 1 := by rw [← pow_two, ← ht₁, pow_orderOf_eq_one]
  have ht₂sq : t₂ * t₂ = 1 := by rw [← pow_two, ← ht₂, pow_orderOf_eq_one]
  have hα2 : MulAut.conjNormal (H := L) t₁ * MulAut.conjNormal (H := L) t₁ = 1 := by
    rw [← map_mul, ht₁sq, map_one]
  have hβ2 : MulAut.conjNormal (H := L) t₂ * MulAut.conjNormal (H := L) t₂ = 1 := by
    rw [← map_mul, ht₂sq, map_one]
  have hαβ : MulAut.conjNormal (H := L) t₁ * MulAut.conjNormal (H := L) t₂ =
      MulAut.conjNormal (H := L) t₂ * MulAut.conjNormal (H := L) t₁ := by
    rw [← map_mul, ← map_mul, hcomm]
  have hnot_inner : ∀ {t : G}, t ∉ L →
      MulAut.conjNormal (H := L) t ∉ (MulAut.conj : ↥L →* MulAut ↥L).range := by
    intro t htL hin
    apply htL
    apply mem_of_isInnerAut hC
    obtain ⟨l, hl⟩ := hin
    refine ⟨l⁻¹, fun x => ?_⟩
    have hx : MulAut.conjNormal (H := L) t x = MulAut.conj l x := DFunLike.congr_fun hl.symm x
    rw [hx, MulAut.conj_apply, inv_inv]
  have hαo := hnot_inner ht₁L
  have hβo := hnot_inner ht₂L
  have hmem : MulAut.conjNormal (H := L) t₁ * MulAut.conjNormal (H := L) t₂ ∈
      (MulAut.conj : ↥L →* MulAut ↥L).range :=
    mul_mem_range_conj_of_isCyclic_map hOut hα2 hβ2 hαβ hαo hβo
  have hmem' : MulAut.conjNormal (H := L) (t₁ * t₂) ∈
      (MulAut.conj : ↥L →* MulAut ↥L).range := by
    rw [map_mul]
    exact hmem
  apply mem_of_isInnerAut hC
  obtain ⟨l, hl⟩ := hmem'
  refine ⟨l⁻¹, fun x => ?_⟩
  have hx : MulAut.conjNormal (H := L) (t₁ * t₂) x = MulAut.conj l x :=
    DFunLike.congr_fun hl.symm x
  rw [hx, MulAut.conj_apply, inv_inv]

end CFSG.LocalAnalysis.WeakClosure81

end
