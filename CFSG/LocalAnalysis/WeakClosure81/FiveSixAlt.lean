module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.Adapters.WholeGroupLayer
public import CFSG.Adapters.GeneralizedFitting

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem exists_injective_conj_of_fstar_alt {H : Subgroup G} {n : ℕ} (hn : 5 ≤ n)
    (e : ↥(Fstar H) ≃* alternatingGroup (Fin n)) :
    ∃ φ : ↥H →* MulAut (alternatingGroup (Fin n)), Function.Injective φ ∧
      ∀ (l : ↥H) (hl : (l : G) ∈ Fstar H), φ l = MulAut.conj (e ⟨(l : G), hl⟩) := by
  set F : Subgroup ↥H := CFSG.generalizedFitting ↥H with hF
  haveI hFn : F.Normal := (CFSG.LocalCores.generalized_fitting_characteristic (G := ↥H)).2
  have hFstar : Fstar H = F.map H.subtype := by
    unfold Fstar
    rw [CFSG.Adapters.genFittingFStar_eq_foundations]
  let e₀ : ↥F ≃* ↥(Fstar H) :=
    (Subgroup.equivMapOfInjective F H.subtype H.subtype_injective).trans
      (MulEquiv.subgroupCongr hFstar.symm)
  let e' : ↥F ≃* alternatingGroup (Fin n) := e₀.trans e
  have hsimple : IsSimpleGroup ↥F := by
    haveI : IsSimpleGroup (alternatingGroup (Fin n)) :=
      alternatingGroup.isSimpleGroup (by simpa using hn)
    exact e'.isSimpleGroup
  have hnab : ∃ a b : ↥F, a * b ≠ b * a := by
    by_contra hc
    have hcomm : ∀ a b : ↥F, a * b = b * a := fun a b => by
      by_contra h
      exact hc ⟨a, b, h⟩
    have hAn : IsMulCommutative (alternatingGroup (Fin n)) :=
      ⟨⟨fun a b => by
        have := hcomm (e'.symm a) (e'.symm b)
        simpa using congrArg e' this⟩⟩
    have := alternatingGroup.isMulCommutative_iff_card_le_three.1 hAn
    simp at this
    omega
  have hC : Subgroup.centralizer (F : Set ↥H) = ⊥ :=
    CFSG.Adapters.centralizer_generalizedFitting_eq_bot_of_isSimpleGroup ↥H hsimple hnab
  have hinj : Function.Injective (MulAut.conjNormal : ↥H →* MulAut ↥F) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxc : x ∈ Subgroup.centralizer (F : Set ↥H) := by
      rw [Subgroup.mem_centralizer_iff]
      intro f hf
      have := congrArg (fun α : MulAut ↥F => ((α ⟨f, hf⟩ : ↥F) : ↥H)) hx
      simp only [MulAut.conjNormal_apply, MulAut.one_apply] at this
      calc f * x = x * f * x⁻¹ * x := by rw [this]
        _ = x * f := by group
    rw [hC] at hxc
    exact Subgroup.mem_bot.1 hxc
  refine ⟨(MulAut.congr e').toMonoidHom.comp MulAut.conjNormal, ?_, ?_⟩
  · exact (MulAut.congr e').injective.comp hinj
  · intro l hl
    have hlF : l ∈ F := by
      rw [hFstar] at hl
      obtain ⟨f, hf, hfl⟩ := Subgroup.mem_map.1 hl
      have : f = l := Subtype.ext hfl
      exact this ▸ hf
    have h1 : (MulAut.conjNormal l : MulAut ↥F) = MulAut.conj ⟨l, hlF⟩ :=
      MulAut.conjNormal_val (h := ⟨l, hlF⟩)
    have h2 : e' ⟨l, hlF⟩ = e ⟨(l : G), hl⟩ := rfl
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h1, ← h2]
    ext x
    simp [MulAut.congr_apply, MulAut.conj_apply]

end CFSG.LocalAnalysis.WeakClosure81
