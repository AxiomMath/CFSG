module

public import CFSG.LocalAnalysis.ComponentClassification.Quasisimple

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup

variable {X Y : Type} [Group X] [Group Y]

theorem s16h_quasisimple_center_quotient_mulEquiv_of_surjective_simple
    (hX : IsQuasisimple X) (hY : IsSimpleGroup Y)
    (π : X →* Y) (hπ : Function.Surjective π) :
    Nonempty (X ⧸ Subgroup.center X ≃* Y) := by
  have hker_ne_top : π.ker ≠ ⊤ := by
    intro htop
    obtain ⟨y, hy⟩ := exists_ne (1 : Y)
    obtain ⟨x, rfl⟩ := hπ y
    exact hy (MonoidHom.mem_ker.mp (htop ▸ Subgroup.mem_top x))
  have hker_le : π.ker ≤ Subgroup.center X :=
    CFSG.ComponentClassification.Quasisimple.normal_le_center_of_ne_top hX π.ker hker_ne_top
  let q : X ⧸ π.ker →* X ⧸ Subgroup.center X :=
    QuotientGroup.lift π.ker (QuotientGroup.mk' (Subgroup.center X)) (by
      rwa [QuotientGroup.ker_mk'])
  let e : X ⧸ π.ker ≃* Y := QuotientGroup.quotientKerEquivOfSurjective π hπ
  let f : Y →* X ⧸ Subgroup.center X := q.comp e.symm.toMonoidHom
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center X) y
    exact ⟨QuotientGroup.mk' π.ker x, by simp [q]⟩
  have hf : Function.Surjective f := hq.comp e.symm.surjective
  haveI : IsSimpleGroup (X ⧸ Subgroup.center X) := hX.2
  have hfker : f.ker = ⊥ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top f.ker with h | h
    · exact h
    · exfalso
      have hsub : Subsingleton (X ⧸ Subgroup.center X) := by
        refine ⟨fun a b => ?_⟩
        obtain ⟨ya, rfl⟩ := hf a
        obtain ⟨yb, rfl⟩ := hf b
        have hya : ya ∈ f.ker := h ▸ Subgroup.mem_top ya
        have hyb : yb ∈ f.ker := h ▸ Subgroup.mem_top yb
        rw [MonoidHom.mem_ker] at hya hyb
        rw [hya, hyb]
      exact not_subsingleton _ hsub
  exact ⟨(MulEquiv.ofBijective f ⟨(MonoidHom.ker_eq_bot_iff f).1 hfker, hf⟩).symm⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
