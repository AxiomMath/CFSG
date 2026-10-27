module

public import CFSG.Quasithin.EmptyFaithful.SzN6RL
public import CFSG.Quasithin.EmptyFaithful.SzN4Aux

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
  CFSG.Assembly.LowTwoRank

section Models

theorem szN6_sl2_four_equiv_alt5 :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2),
      Nonempty (Matrix.SpecialLinearGroup (Fin 2) K ≃* alternatingGroup (Fin 5)) := by
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let K := GaloisField 2 2
  have hK : Nat.card K = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  obtain ⟨e⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five K
    (Or.inl hK)
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hcen : Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) = ⊥ := by
    rw [eq_bot_iff]
    intro A hA
    exact szN4_sl2_center_trivial h2 A (fun B => (Subgroup.mem_center_iff.mp hA B).symm)
  let q : Matrix.SpecialLinearGroup (Fin 2) K →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K :=
    QuotientGroup.mk' _
  have hq : Function.Bijective q := by
    refine ⟨(injective_iff_map_eq_one q).mpr fun A hA => ?_, QuotientGroup.mk'_surjective _⟩
    have h1 : A ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) := by
      rw [← QuotientGroup.ker_mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K))]
      exact hA
    rw [hcen] at h1
    exact h1
  exact ⟨K, inferInstance, inferInstance, inferInstance,
    ⟨(MulEquiv.ofBijective q hq).trans ((projectiveSpecialLinearGroupEquivStatedProj 2 K).trans e)⟩⟩

end Models

section Main

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem szN6_RL_sylow_of_alt5 (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (ctx : Ctx15316 T Mc M V₁ V₂ Yp I L t) (hA : IsAltType L 5) :
    IsSylowTwoOf (R153 T V₁ Yp ⊓ L) L := by
  obtain ⟨α, hαs, hαk, -⟩ := hA
  obtain ⟨K, hK, hKf, hKc, ⟨e⟩⟩ := szN6_sl2_four_equiv_alt5
  let ρ : ↥L →* Matrix.SpecialLinearGroup (Fin 2) K := e.symm.toMonoidHom.comp α
  have hρ : Function.Surjective ρ := e.symm.surjective.comp hαs
  have hk : IsPGroup 2 ρ.ker := by
    have h1 : IsPGroup 2 α.ker := hαk ▸ CFSG.pCore_isPGroup
    refine h1.to_le fun x hx => ?_
    have hx' : e.symm (α x) = 1 := hx
    exact e.symm.injective (hx'.trans e.symm.map_one.symm)
  exact szN6_RL_sylow_of_quotient h37 h38 ctx ρ hρ hk SzN6.sl2_proper_overgroup_le_normalizer

end Main

end CFSG.Quasithin
