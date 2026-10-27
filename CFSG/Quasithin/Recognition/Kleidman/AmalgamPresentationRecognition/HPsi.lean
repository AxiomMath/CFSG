module

public import CFSG.Quasithin.Recognition.Kleidman.Split
public import CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition.HRelatorsModel

public section

namespace CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition

open CFSG.Quasithin.J2Cz

theorem exists_H_psi {G : Type} [Group G] [Finite G] {z : G} (h : CFSG.Quasithin.IsTypeH2 G z) :
    ∃ ψ : Model →* G, Function.Injective ψ ∧
      (∀ g : G, g ∈ Subgroup.centralizer ({z} : Set G) → g ∈ ψ.range) ∧
      (∀ m : Model, ψ m ∈ Subgroup.centralizer ({z} : Set G)) ∧
      ψ (modelTuple7 ⟨3, by decide⟩) = z := by
  obtain ⟨φ⟩ := CFSG.Quasithin.Kleidman.IsTypeH2.nonempty_mulEquiv_model_of_typeH2 h
  set C := Subgroup.centralizer ({z} : Set G) with hC
  let ψ : Model →* G := C.subtype.comp φ.symm.toMonoidHom
  have hzC : z ∈ C := by
    rw [hC, Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff.mp hg]
  have hcentral : ∀ g : Model, g * φ ⟨z, hzC⟩ = φ ⟨z, hzC⟩ * g := by
    intro g
    apply φ.symm.injective
    rw [map_mul, map_mul, MulEquiv.symm_apply_apply]
    apply Subtype.ext
    have h1 := Subgroup.mem_centralizer_iff.mp (φ.symm g).2
    exact (h1 z rfl).symm
  have hφz : φ ⟨z, hzC⟩ = ⟨QM.z, 1⟩ := by
    rcases eq_one_or_z_of_central _ (fun g => (hcentral g).symm.symm) with h1 | h1
    · exfalso
      have h2 : (⟨z, hzC⟩ : C) = 1 := φ.injective (h1.trans (map_one φ).symm)
      exact h.ne_one (congrArg Subtype.val h2)
    · exact h1
  refine ⟨ψ, fun a b hab => φ.symm.injective (Subtype.ext hab), ?_, fun m => (φ.symm m).2, ?_⟩
  · intro g hg
    exact ⟨φ ⟨g, hg⟩, by simp [ψ]⟩
  · have h1 : modelTuple7 ⟨3, by decide⟩ = ⟨QM.z, 1⟩ := rfl
    rw [h1, ← hφz]
    simp [ψ]

end CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition
