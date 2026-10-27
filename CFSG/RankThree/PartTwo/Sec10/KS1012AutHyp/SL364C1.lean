module

public import CFSG.RankThree.PartTwo.Sec10.KS1012AutHyp.SL34

public section

namespace CFSG.RankThree.PartTwo.Sec10.KS1012AutHyp

@[expose] def Conc (X : Type) [Group X] (F : Subgroup (MulAut X)) : Prop :=
  ∃ F' ≤ F, Nat.card F ≤ 3 * Nat.card F' ∧ ∃ V : Subgroup X, V ≠ ⊥ ∧ IsPGroup 2 V ∧
    ∀ f ∈ F', ∀ v ∈ V, f v ∈ V

theorem conc_of_conc_map {Q Q' : Type} [Group Q] [Group Q'] (e : Q ≃* Q')
    (F : Subgroup (MulAut Q)) (h : Conc Q' (F.map (MulAut.congr e).toMonoidHom)) : Conc Q F := by
  obtain ⟨F₁, hF₁, hcard₁, V₁, hV₁ne, hV₁p, hV₁st⟩ := h
  have hid : ∀ f : MulAut Q,
      (MulAut.congr e.symm).toMonoidHom ((MulAut.congr e).toMonoidHom f) = f := by
    intro f
    ext x
    simp [MulAut.congr_apply]
  refine ⟨F₁.map (MulAut.congr e.symm).toMonoidHom, ?_, ?_, V₁.map e.symm.toMonoidHom, ?_, ?_, ?_⟩
  · rintro _ ⟨g, hg, rfl⟩
    obtain ⟨f, hf, hfg⟩ := Subgroup.mem_map.mp (hF₁ hg)
    rw [← hfg, hid]
    exact hf
  · have h1 : Nat.card (F.map (MulAut.congr e).toMonoidHom) = Nat.card F :=
      Subgroup.card_map_of_injective (f := (MulAut.congr e).toMonoidHom) (MulEquiv.injective _)
    have h2 : Nat.card (F₁.map (MulAut.congr e.symm).toMonoidHom) = Nat.card F₁ :=
      Subgroup.card_map_of_injective (f := (MulAut.congr e.symm).toMonoidHom)
        (MulEquiv.injective _)
    rw [h2]
    rw [h1] at hcard₁
    exact hcard₁
  · intro h
    apply hV₁ne
    apply Subgroup.map_injective (f := e.symm.toMonoidHom) (MulEquiv.injective _)
    rw [h, Subgroup.map_bot]
  · exact isPGroup_map_mulEquiv 2 e.symm hV₁p
  · intro g hg v hv
    obtain ⟨g', hg', rfl⟩ := Subgroup.mem_map.mp hg
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hv
    have hkey : (MulAut.congr e.symm g') (e.symm w) = e.symm (g' w) := by
      simp [MulAut.congr_apply]
    show (MulAut.congr e.symm g') (e.symm w) ∈ V₁.map e.symm.toMonoidHom
    rw [hkey]
    exact Subgroup.mem_map.mpr ⟨g' w, hV₁st g' hg' w hw, rfl⟩

theorem conc_of_conj {X : Type} [Group X] (ψ : MulAut X) (F : Subgroup (MulAut X))
    (h : Conc X (F.map (MulAut.conj ψ).toMonoidHom)) : Conc X F := by
  refine conc_of_conc_map (ψ : X ≃* X) F ?_
  have : F.map (MulAut.congr (ψ : X ≃* X)).toMonoidHom = F.map (MulAut.conj ψ).toMonoidHom := by
    congr 1
  rw [this]
  exact h

end CFSG.RankThree.PartTwo.Sec10.KS1012AutHyp

end
