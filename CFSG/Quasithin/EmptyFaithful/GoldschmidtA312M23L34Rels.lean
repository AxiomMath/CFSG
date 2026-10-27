module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M23L34Gen
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple

public section

namespace CFSG.Quasithin.A312M23

open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34 CFSG.Quasithin
open CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.TwoGen

theorem isPSL_three_four_of_rels {Γ : Type} [Group Γ] {u v : Γ}
    (hrel : ∀ w ∈ rels.map (List.map fun l => (l.1.val, l.2)), wordProd (img2 u v) w = 1)
    (hu : u ≠ 1) : IsPSL 3 2 2 ↥(Subgroup.closure ({u, v} : Set Γ)) := by
  classical
  set f : FreeGroup (Fin 2) →* Γ := FreeGroup.lift (fun i : Fin 2 => img2 u v i.val) with hf
  have hker : (FreeGroup.lift genX).ker ≤ f.ker := by
    rw [isPresentation_genX.ker_lift]
    refine Subgroup.normalClosure_le_normal ?_
    intro r hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
    rw [SetLike.mem_coe, MonoidHom.mem_ker, hf, lift_mk_eq_wordProd]
    exact hrel _ (List.mem_map_of_mem hw)
  let e := QuotientGroup.quotientKerEquivOfSurjective (FreeGroup.lift genX)
    isPresentation_genX.lift_surjective
  let φ : PSL3 →* Γ := (QuotientGroup.lift (FreeGroup.lift genX).ker f hker).comp e.symm.toMonoidHom
  have hφ : ∀ z, φ (FreeGroup.lift genX z) = f z := by
    intro z
    have h1 : e.symm (FreeGroup.lift genX z) =
        (z : FreeGroup (Fin 2) ⧸ (FreeGroup.lift genX).ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    simp only [φ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h1, QuotientGroup.lift_mk]
  haveI : IsSimpleGroup PSL3 :=
    (CFSG.LinearGroups.linear_projective_simple (K := CFSG.Fischer.F4) (n := 3) (by norm_num)
      (Or.inl (by norm_num))).2.1
  have hφ0 : φ (genX 0) = u := by
    have := hφ (FreeGroup.of 0)
    rw [FreeGroup.lift_apply_of] at this
    rw [this, hf, FreeGroup.lift_apply_of]
    simp [img2]
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with h | h
    · exact h
    · exfalso
      apply hu
      rw [← hφ0]
      have hmem : genX 0 ∈ φ.ker := by rw [h]; exact Subgroup.mem_top _
      exact MonoidHom.mem_ker.mp hmem
  have hrange : φ.range = Subgroup.closure ({u, v} : Set Γ) := by
    have h1 : φ.range = f.range := by
      ext g
      constructor
      · rintro ⟨x, rfl⟩
        obtain ⟨z, rfl⟩ := isPresentation_genX.lift_surjective x
        exact ⟨z, (hφ z).symm⟩
      · rintro ⟨z, rfl⟩
        exact ⟨FreeGroup.lift genX z, hφ z⟩
    rw [h1, hf, FreeGroup.range_lift_eq_closure]
    congr 1
    ext z
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp [img2]
    · rintro (rfl | rfl)
      · exact ⟨0, by simp [img2]⟩
      · exact ⟨1, by simp [img2]⟩
  let ψ : PSL3 ≃* ↥(Subgroup.closure ({u, v} : Set Γ)) :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  exact isPSL_three_four_of_mulEquiv ψ.symm.symm

end CFSG.Quasithin.A312M23
