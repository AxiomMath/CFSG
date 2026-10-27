module

public import CFSG.RankThree.GF2n.Stroth80.Sec7TailTIConfig
public import CFSG.GroupTheory.Fitting.MulEquiv

public section

namespace CFSG.RankThree.GF2n.Stroth80

open Subgroup CFSG

theorem generalizedFitting_comap_eq {X Y : Type*} [Group X] [Finite X] [Group Y] [Finite Y]
    (f : Y →* X) (hf : Function.Injective f) {K' : Subgroup Y} {K N : Subgroup X}
    (hK : K'.map f = K) (hF : generalizedFitting ↥K = N.subgroupOf K) :
    generalizedFitting ↥K' = (N.comap f).subgroupOf K' := by
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ↥K' ≃* ↥K, ∀ y : ↥K', ((ψ.toMonoidHom y : ↥K) : X) = f (y : Y) :=
    ⟨(Subgroup.equivMapOfInjective K' f hf).trans (MulEquiv.subgroupCongr hK), fun y => rfl⟩
  have hmap : (generalizedFitting ↥K').map ψ.toMonoidHom = N.subgroupOf K := by
    rw [WholeGroup.generalizedFitting_map_mulEquiv ψ, hF]
  have hcomap : generalizedFitting ↥K' = (N.subgroupOf K).comap ψ.toMonoidHom := by
    rw [← hmap, Subgroup.comap_map_eq_self_of_injective (f := ψ.toMonoidHom) ψ.injective]
  rw [hcomap]
  ext y
  simp only [Subgroup.mem_comap, Subgroup.mem_subgroupOf, hψ]

theorem pCore_normalizer_eq {Y : Type*} [Group Y] [Finite Y] {V N : Subgroup Y}
    (h : TIConfig ⊤ V N) :
    pCore 2 ↥(normalizer (V : Set Y)) = N.subgroupOf (normalizer (V : Set Y)) := by
  set K : Subgroup Y := normalizer (V : Set Y) with hKdef
  have hNK : N ≤ K := fun x hx => (mem_NormIn.1 (h.N_le hx)).2
  have hKN : K ≤ normalizer (N : Set Y) :=
    fun k hk => h.N_normal k (mem_NormIn.2 ⟨Subgroup.mem_top k, hk⟩)
  apply le_antisymm
  · intro x hx
    set P : Subgroup Y := (pCore 2 ↥K).map K.subtype with hPdef
    have hPK : P ≤ K := by
      rintro _ ⟨w, _, rfl⟩
      exact w.2
    have hPnorm : ∀ k ∈ NormIn ⊤ V, k ∈ normalizer (P : Set Y) := by
      intro k hk
      have hkK : k ∈ K := (mem_NormIn.1 hk).2
      refine TIConfig.mem_normalizer_of_conj_mem ?_
      rintro z ⟨w, hw, rfl⟩
      refine Subgroup.mem_map.mpr ⟨(⟨k, hkK⟩ : ↥K) * w * (⟨k, hkK⟩ : ↥K)⁻¹, ?_, rfl⟩
      exact Subgroup.Normal.conj_mem (CFSG.pCore_normal (p := 2) (G := ↥K)) w hw ⟨k, hkK⟩
    have hPp : IsPGroup 2 P := IsPGroup.map (CFSG.pCore_isPGroup (p := 2) (G := ↥K)) K.subtype
    have hPN : P ≤ N :=
      h.pcore_le P (fun y hy => mem_NormIn.2 ⟨Subgroup.mem_top y, hPK hy⟩) hPnorm hPp
    exact hPN (Subgroup.mem_map_of_mem K.subtype hx)
  · have hnorm : (N.subgroupOf K).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hNK).2 hKN
    have hp : IsPGroup 2 (N.subgroupOf K) :=
      h.N_pgroup.of_equiv (Subgroup.subgroupOfEquivOfLe hNK).symm
    exact le_sSup ⟨hnorm, hp⟩

end CFSG.RankThree.GF2n.Stroth80
