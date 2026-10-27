module

public import CFSG.Quasithin.EmptyFaithful.SzPS8S6Class
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonClassification

public section

namespace CFSG.Quasithin

namespace SzPS8

namespace S6Class

open Equiv Equiv.Perm Subgroup

theorem nonempty_mulEquiv_psl25_alternatingGroup_five :
    Nonempty (↥psl25 ≃* ↥(alternatingGroup (Fin 5))) :=
  CFSG.Glauberman.Dickson.huppert_II_8_25_transitive_degree_six_order_sixty (Ω := Fin 6)
    isPretransitive_psl25 (by simp) card_psl25

theorem nonempty_mulEquiv_a5p_alternatingGroup_five :
    Nonempty (↥a5p ≃* ↥(alternatingGroup (Fin 5))) :=
  ⟨(MulEquiv.subgroupCongr a5p_eq_map).trans
    (Subgroup.equivMapOfInjective _ embedFive embedFive_injective).symm⟩

theorem conj_mem_inf_alternatingGroup {Y : Subgroup (Perm (Fin 6))} {x n : Perm (Fin 6)}
    (hx : x ∈ Y) (hn : n ∈ Y ⊓ alternatingGroup (Fin 6)) :
    x * n * x⁻¹ ∈ Y ⊓ alternatingGroup (Fin 6) :=
  Subgroup.mem_inf.mpr ⟨Y.mul_mem (Y.mul_mem hx (Subgroup.mem_inf.mp hn).1) (Y.inv_mem hx),
    (inferInstance : (alternatingGroup (Fin 6)).Normal).conj_mem n (Subgroup.mem_inf.mp hn).2 x⟩

theorem exists_normal_equiv_of_le_range {K G : Type*} [Group K] [Group G] (ψ : K →* G)
    (hψ : Function.Injective ψ) (N' : Subgroup G) (hle : N' ≤ ψ.range)
    (hnorm : ∀ x ∈ ψ.range, ∀ n ∈ N', x * n * x⁻¹ ∈ N') :
    ∃ N : Subgroup K, N.Normal ∧ Nonempty (↥N ≃* ↥N') := by
  refine ⟨N'.comap ψ, ⟨fun n hn k => ?_⟩, ⟨?_⟩⟩
  · have := hnorm (ψ k) ⟨k, rfl⟩ (ψ n) hn
    simpa [Subgroup.mem_comap] using this
  · exact (Subgroup.equivMapOfInjective (N'.comap ψ) ψ hψ).trans
      (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self hle))

theorem exists_normal_alt_of_not_isSolvable {K : Type*} [Group K] (φ : K →* Equiv.Perm (Fin 6))
    (hφ : Function.Injective φ) (hK : ¬ Group.IsSolvable K) :
    (∃ N : Subgroup K, N.Normal ∧ Nonempty (↥N ≃* ↥(alternatingGroup (Fin 5)))) ∨
      (∃ N : Subgroup K, N.Normal ∧ Nonempty (↥N ≃* ↥(alternatingGroup (Fin 6)))) := by
  obtain ⟨σ, hσ⟩ := exists_conj_range_mem_of_not_isSolvable φ hφ hK
  have hψinj : Function.Injective ((MulAut.conj σ).toMonoidHom.comp φ) :=
    (MulAut.conj σ).injective.comp hφ
  have hrange : ((MulAut.conj σ).toMonoidHom.comp φ).range =
      φ.range.map (MulAut.conj σ).toMonoidHom := MonoidHom.range_comp _ _
  rw [← hrange] at hσ
  generalize (MulAut.conj σ).toMonoidHom.comp φ = ψ at hσ hψinj hrange
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hσ
  have hA6 : ∀ x ∈ ψ.range, ∀ n ∈ alternatingGroup (Fin 6),
      x * n * x⁻¹ ∈ alternatingGroup (Fin 6) :=
    fun x _ n hn => (inferInstance : (alternatingGroup (Fin 6)).Normal).conj_mem n hn x
  rcases hσ with h | h | h | h | h | h
  · exact Or.inr (exists_normal_equiv_of_le_range ψ hψinj _ (by rw [h]) hA6)
  · exact Or.inr (exists_normal_equiv_of_le_range ψ hψinj _ (by rw [h]; exact le_top) hA6)
  · obtain ⟨N, hN, ⟨e⟩⟩ := exists_normal_equiv_of_le_range ψ hψinj a5p
      (by rw [h]; exact inf_le_left)
      (fun x hx n hn => conj_mem_inf_alternatingGroup (Y := s5p) (h ▸ hx) hn)
    obtain ⟨e5⟩ := nonempty_mulEquiv_a5p_alternatingGroup_five
    exact Or.inl ⟨N, hN, ⟨e.trans e5⟩⟩
  · obtain ⟨N, hN, ⟨e⟩⟩ := exists_normal_equiv_of_le_range ψ hψinj a5p
      (by rw [h])
      (fun x hx n hn =>
        conj_mem_inf_alternatingGroup (Y := s5p) (Subgroup.mem_inf.mp (h ▸ hx)).1 hn)
    obtain ⟨e5⟩ := nonempty_mulEquiv_a5p_alternatingGroup_five
    exact Or.inl ⟨N, hN, ⟨e.trans e5⟩⟩
  · obtain ⟨N, hN, ⟨e⟩⟩ := exists_normal_equiv_of_le_range ψ hψinj psl25
      (by rw [h]; exact inf_le_left)
      (fun x hx n hn => conj_mem_inf_alternatingGroup (Y := pgl25) (h ▸ hx) hn)
    obtain ⟨e5⟩ := nonempty_mulEquiv_psl25_alternatingGroup_five
    exact Or.inl ⟨N, hN, ⟨e.trans e5⟩⟩
  · obtain ⟨N, hN, ⟨e⟩⟩ := exists_normal_equiv_of_le_range ψ hψinj psl25
      (by rw [h])
      (fun x hx n hn =>
        conj_mem_inf_alternatingGroup (Y := pgl25) (Subgroup.mem_inf.mp (h ▸ hx)).1 hn)
    obtain ⟨e5⟩ := nonempty_mulEquiv_psl25_alternatingGroup_five
    exact Or.inl ⟨N, hN, ⟨e.trans e5⟩⟩

end S6Class

end SzPS8

end CFSG.Quasithin
