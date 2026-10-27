module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S20
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ParabolicTransfer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KSUE

open CFSG.Open Subgroup

@[expose] def fixSub {W : Type} [CommGroup W] (H : Subgroup (MulAut W)) (S : Sylow 2 ↥H) :
    Subgroup ↥H :=
  letI : MulDistribMulAction ↥H W := MulDistribMulAction.compHom W H.subtype
  letI : MulAction ↥H W := MulAction.compHom W H.subtype
  letI : MulDistribMulAction ↥S W :=
    MulDistribMulAction.compHom W (H.subtype.comp (S : Subgroup ↥H).subtype)
  CFSG.fixingSubgroupOf ↥H W (CFSG.fixedPointSubgroup ↥S W : Set W)

@[expose] def Concl {X : Type} [Group X] (S P F : Subgroup X) : Prop :=
  ∃ E : Subgroup X, IsElemAbelian 3 E ∧ Nat.card ↥E = 9 ∧
    E ≤ Subgroup.normalizer (S : Set X) ∧
    E ⊓ F = E ⊓ Hinf P ∧ Nat.card ↥(E ⊓ Hinf P) = 3 ∧
    (∃ k ∈ Hinf P, ∃ e ∈ E ⊓ Hinf P, e * k ≠ k * e) ∧
    ∃ w : X, w ∉ P ∧ ∀ e ∈ E, w * e * w⁻¹ = e⁻¹

theorem Concl.map_mulEquiv {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y]
    (φ : X ≃* Y) {S P F : Subgroup X} (h : Concl S P F) :
    Concl (S.map φ.toMonoidHom) (P.map φ.toMonoidHom) (F.map φ.toMonoidHom) := by
  let f : X →* Y := φ.toMonoidHom
  have hf : Function.Injective f := fun _ _ hab => φ.injective hab
  have hfb : Function.Bijective f :=
    ⟨hf, fun y => by obtain ⟨x, hx⟩ := φ.surjective y; exact ⟨x, hx⟩⟩
  change Concl (S.map f) (P.map f) (F.map f)
  obtain ⟨E, hEab, hE9, hnorm, hEF, h3, ⟨k, hk, e, he, hne⟩, w, hw, hinv⟩ := h
  refine ⟨E.map f, ?_, ?_, ?_, ?_, ?_, ?_, f w, ?_, ?_⟩
  · haveI := hEab.1
    refine ⟨inferInstance, fun x hx => ?_⟩
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    rw [← map_pow, hEab.2 y hy, map_one]
  · rw [Subgroup.card_map_of_injective (f := f) (K := E) hf, hE9]
  · have h := Subgroup.map_mono (f := f) hnorm
    rwa [Subgroup.map_normalizer_eq_of_bijective S hfb] at h
  · rw [← Subgroup.map_inf_eq E F f hf, hEF, Subgroup.map_inf_eq E (Hinf P) f hf,
      Hinf_map f P]
  · rw [← Hinf_map f P, ← Subgroup.map_inf_eq E (Hinf P) f hf,
      Subgroup.card_map_of_injective (f := f) (K := E ⊓ Hinf P) hf, h3]
  · refine ⟨f k, ?_, f e, ?_, ?_⟩
    · rw [← Hinf_map f P]
      exact Subgroup.mem_map_of_mem f hk
    · refine ⟨Subgroup.mem_map_of_mem f he.1, ?_⟩
      rw [← Hinf_map f P]
      exact Subgroup.mem_map_of_mem f he.2
    · intro hcon
      exact hne (hf (by simpa only [map_mul] using hcon))
  · intro hmem
    exact hw ((Subgroup.mem_map_iff_mem hf).mp hmem)
  · rintro e' ⟨e, he, rfl⟩
    have h := congrArg f (hinv e he)
    simpa only [map_mul, map_inv] using h

end CFSG.LocalAnalysis.UniquenessCase.UC22.KSUE
