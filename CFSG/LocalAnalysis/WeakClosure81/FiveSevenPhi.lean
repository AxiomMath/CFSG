module

public import CFSG.LocalAnalysis.WeakClosure81.FiveSixAlt
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem fstar_le_group (H : Subgroup G) : Fstar H ≤ H := by
  unfold Fstar
  exact Subgroup.map_subtype_le _

theorem conj_mem_fstar {H : Subgroup G} {x f : G} (hx : x ∈ H) (hf : f ∈ Fstar H) :
    x * f * x⁻¹ ∈ Fstar H := by
  set F : Subgroup ↥H := CFSG.generalizedFitting ↥H with hF
  haveI hFn : F.Normal := (CFSG.LocalCores.generalized_fitting_characteristic (G := ↥H)).2
  have hFstar : Fstar H = F.map H.subtype := by
    unfold Fstar
    rw [CFSG.Adapters.genFittingFStar_eq_foundations]
  rw [hFstar] at hf ⊢
  obtain ⟨f', hf', rfl⟩ := Subgroup.mem_map.1 hf
  refine Subgroup.mem_map.2 ⟨⟨x, hx⟩ * f' * ⟨x, hx⟩⁻¹, hFn.conj_mem f' hf' ⟨x, hx⟩, ?_⟩
  simp

theorem mulAut_conj_injective_alternatingGroup {n : ℕ} (hn : 4 ≤ n) :
    Function.Injective
      (MulAut.conj : alternatingGroup (Fin n) →* MulAut (alternatingGroup (Fin n))) := by
  intro a b hab
  have hinj := CFSG.GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup n hn
  apply Subtype.ext
  apply hinj
  rw [MulAut.conjNormal_val, MulAut.conjNormal_val]
  exact hab

theorem exists_injective_conj_apply_of_fstar_alt {H : Subgroup G} {n : ℕ} (hn : 5 ≤ n)
    (e : ↥(Fstar H) ≃* alternatingGroup (Fin n)) :
    ∃ φ : ↥H →* MulAut (alternatingGroup (Fin n)), Function.Injective φ ∧
      (∀ (l : ↥H) (hl : (l : G) ∈ Fstar H), φ l = MulAut.conj (e ⟨(l : G), hl⟩)) ∧
      ∀ (x : ↥H) (f : ↥(Fstar H)),
        ((e.symm (φ x (e f)) : ↥(Fstar H)) : G) = (x : G) * (f : G) * (x : G)⁻¹ := by
  obtain ⟨φ, hφinj, hφ⟩ := exists_injective_conj_of_fstar_alt hn e
  refine ⟨φ, hφinj, hφ, fun x f => ?_⟩
  have hmem : (x : G) * (f : G) * (x : G)⁻¹ ∈ Fstar H := conj_mem_fstar x.2 f.2
  let f₂ : ↥(Fstar H) := ⟨(x : G) * (f : G) * (x : G)⁻¹, hmem⟩
  let fH : ↥H := ⟨(f : G), fstar_le_group H f.2⟩
  have hfH : (fH : G) ∈ Fstar H := f.2
  have h1 : φ (x * fH * x⁻¹) = MulAut.conj (e f₂) := hφ (x * fH * x⁻¹) hmem
  have h2 : φ (x * fH * x⁻¹) = φ x * MulAut.conj (e f) * (φ x)⁻¹ := by
    rw [map_mul, map_mul, map_inv, hφ fH hfH]
  have h3 : MulAut.conj (φ x (e f)) = φ x * MulAut.conj (e f) * (φ x)⁻¹ := by
    apply MulEquiv.ext
    intro y
    simp [MulAut.conj_apply]
  have h4 : MulAut.conj (φ x (e f)) = MulAut.conj (e f₂) := h3.trans (h2.symm.trans h1)
  have h5 : φ x (e f) = e f₂ := mulAut_conj_injective_alternatingGroup (by omega) h4
  rw [h5, MulEquiv.symm_apply_apply]

end CFSG.LocalAnalysis.WeakClosure81
