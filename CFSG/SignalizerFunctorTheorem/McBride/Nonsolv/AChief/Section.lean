module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.AChief.Simple

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.AChief

open CFSG.SignalizerFunctorTheorem.Nonsolvable

theorem exists_solvable_normalized {X : Type*} [Group X] (hnc : ∃ a b : X, a * b ≠ b * a)
    {C : Subgroup X} (hC : Group.IsSolvable C) :
    ∃ R : Subgroup X, R ≠ ⊥ ∧ Group.IsSolvable R ∧ C ≤ Subgroup.normalizer (R : Set X) := by
  by_cases hC1 : C = ⊥
  · obtain ⟨a, b, hab⟩ := hnc
    have ha : a ≠ 1 := fun h => hab (by rw [h, one_mul, mul_one])
    exact ⟨Subgroup.zpowers a, fun h => ha (Subgroup.zpowers_eq_bot.mp h), inferInstance,
      hC1 ▸ bot_le⟩
  · exact ⟨C, hC1, hC, Subgroup.le_normalizer⟩

variable {Γ : Type u} [Group Γ] [Finite Γ] {E Y : Subgroup Γ}

theorem isSectionOf_component (hA : IsASimple E Y) {T : Subgroup Γ} (hT : T ∈ simpleComponents Y)
    {S : Type*} [Group S] [IsSimpleGroup S] (hnc : ∃ a b : S, a * b ≠ b * a)
    (hS : IsSectionOf S ↥Y) : IsSectionOf S ↥T := by
  have hK := isDirectProduct_simpleComponents hA
  have hS' : IsSectionOf S ((J : simpleComponents Y) → ↥(J : Subgroup Γ)) :=
    hS.trans (IsSectionOf.of_mulEquiv hK.equiv)
  obtain ⟨J, hJ⟩ := IsSectionOf.of_pi hnc hS'
  obtain ⟨a, -, hJT⟩ := hA.components_transitive hT J.2
  exact hJ.trans (IsSectionOf.of_mulEquiv
    ((T.equivMapOfInjective (MulAut.conj a).toMonoidHom (MulAut.conj a).injective).trans
      (MulEquiv.subgroupCongr hJT.symm)))

theorem signalizerNearPSolvable_of_isASimple {p : ℕ} (hp : p.Prime) (hE : IsElemAbelian p E)
    (hA : IsASimple E Y) (hY : signalizerMcBrideHypothesisB p Y)
    (hsol : Group.IsSolvable (Y ⊓ Subgroup.centralizer (E : Set Γ) : Subgroup Γ))
    {T : Subgroup Γ} (hT : T ∈ simpleComponents Y) : signalizerNearPSolvable p ↥T := by
  obtain ⟨-, hTs, hTnc, -, -, hnear | hdich⟩ := hypA_of_mem_simpleComponents hY hT
  · exact hnear
  · exfalso
    obtain ⟨f, hf, φ, hφ⟩ := exists_fixed_embedding hp hE hA hY hT
    have hsolf : Group.IsSolvable (signalizerFixedSubgroup f) :=
      Group.isSolvable_of_isSolvable_injective hφ
    rcases hf with hf | hf
    ·
      let ψ : ↥T →* ↥(signalizerFixedSubgroup f) :=
        { toFun := fun t => ⟨t, by rw [hf]; rfl⟩
          map_one' := rfl
          map_mul' := fun _ _ => rfl }
      have hψ : Function.Injective ψ := fun x y h => congrArg Subtype.val h
      have hTsol : Group.IsSolvable ↥T := Group.isSolvable_of_isSolvable_injective hψ
      obtain ⟨a, b, hab⟩ := hTnc
      exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr hTsol a b)
    ·
      obtain ⟨R, hR1, hRs, hCR⟩ := exists_solvable_normalized hTnc hsolf
      exact (hdich f hf).1 R hR1 hRs hCR

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.AChief
