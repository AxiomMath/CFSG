module

import CFSG.RankThree.GF2n.Stroth80.ClassicalQuasisimple
import CFSG.GH74.GLS.Stage2.Bender.Thm2.L102Simple
public import CFSG.GroupTheory.Fitting.LayerTopBot
public import CFSG.RankThree.GF2n.Stroth80.Conclusion

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement

theorem layer_eq_top_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : layer A = ⊤) : layer B = ⊤ := by
  rw [← CFSG.WholeGroup.layer_map_mulEquiv e, h]
  exact Subgroup.map_top_of_surjective _ e.surjective

private theorem range_inl_normal (A B : Type) [Group A] [Group B] :
    ((MonoidHom.inl A B).range).Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨a, rfl⟩ := hn
  exact ⟨g.1 * a * g.1⁻¹, by ext <;> simp⟩

private theorem range_inr_normal (A B : Type) [Group A] [Group B] :
    ((MonoidHom.inr A B).range).Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨b, rfl⟩ := hn
  exact ⟨g.2 * b * g.2⁻¹, by ext <;> simp⟩

theorem layer_prod_eq_top {A B : Type} [Group A] [Group B] (hA : layer A = ⊤)
    (hB : layer B = ⊤) : layer (A × B) = ⊤ := by
  have hinl : (MonoidHom.inl A B).range ≤ layer (A × B) := by
    haveI := range_inl_normal A B
    have hinj : Function.Injective (MonoidHom.inl A B) := fun x y h => by
      simpa using congrArg Prod.fst h
    have hl : layer ↥(MonoidHom.inl A B).range = ⊤ :=
      layer_eq_top_of_mulEquiv (MonoidHom.ofInjective hinj) hA
    have h := CFSG.GH74.GLS.Stage2.Bender.Thm2.L102.map_layer_le_layer_of_normal
      (W := (MonoidHom.inl A B).range)
    rwa [hl, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
  have hinr : (MonoidHom.inr A B).range ≤ layer (A × B) := by
    haveI := range_inr_normal A B
    have hinj : Function.Injective (MonoidHom.inr A B) := fun x y h => by
      simpa using congrArg Prod.snd h
    have hl : layer ↥(MonoidHom.inr A B).range = ⊤ :=
      layer_eq_top_of_mulEquiv (MonoidHom.ofInjective hinj) hB
    have h := CFSG.GH74.GLS.Stage2.Bender.Thm2.L102.map_layer_le_layer_of_normal
      (W := (MonoidHom.inr A B).range)
    rwa [hl, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
  rw [eq_top_iff]
  intro x _
  have hx : x = MonoidHom.inl A B x.1 * MonoidHom.inr A B x.2 := by ext <;> simp
  rw [hx]
  exact mul_mem (hinl ⟨x.1, rfl⟩) (hinr ⟨x.2, rfl⟩)

theorem layer_eq_top_of_isSLModel_two {q : ℕ} (hq : 4 ≤ q) {A : Type} [Group A]
    (h : IsSLModel 2 q A) : layer A = ⊤ := by
  obtain ⟨K, _, _, hK, ⟨eA⟩⟩ := h
  exact layer_eq_top_of_mulEquiv eA.symm (CFSG.WholeGroup.layer_eq_top_of_isQuasisimple
    (statedSL_quasisimple_of_card 2 K le_rfl (hq.trans_eq hK.symm)))

end CFSG.RankThree.GF2n.Smith81
