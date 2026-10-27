module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113F5113
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieD4Facts
public import CFSG.Quasithin.H13.NQCatG24Split

public section

namespace CFSG.Quasithin.H13

open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.QuasithinUnique.Setup.X6
  CFSG.QuasithinUnique.Vol2Native.L239.Lie.D4

namespace Sec526

theorem isSolvable_member_d42
    {Y : Type} [Group Y] (hY : IsLieOverTwo .trialityD4 0 1 Y) {T M₁ M₂ : Subgroup Y}
    (hpair : IsYAmalgamPair T M₁ M₂) : Group.IsSolvable ↥M₁ ∨ Group.IsSolvable ↥M₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hYm : ChevalleyExceptionalModel Y .trialityD4 2 1 := by
    rcases hY with ⟨h, -⟩ | ⟨-, -, h⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩
    · simp [classicalTags] at h
    · exact h
    · simp [reeTitsTags] at h
    · exact absurd h (by decide)
  obtain ⟨-, K₀, _, _, σ₀, -, -, ⟨e₀⟩⟩ := exists_mulEquiv_triality_model hYm
  have : Finite (ModGL TwistTag.D4.tag K₀) := finite_modGL
  have : Finite Y := Finite.of_equiv _ e₀.symm.toEquiv
  obtain ⟨K, _, _, σ, φ, hK, hσ, -, hres, -⟩ := even_rank_two_residual_triality hYm hpair.1
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have hK8 : Nat.card K = 2 ^ 3 := by rw [hK]; norm_num
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by norm_num) hK8
  have hσ3 : σ.toRingHom ^ 3 = 1 := by
    ext c
    have : Fintype K := Fintype.ofFinite K
    have hpow : c ^ 8 = c := by
      have := FiniteField.pow_card c
      rwa [← Nat.card_eq_fintype_card, hK8] at this
    show σ (σ (σ c)) = c
    rw [hσ, hσ, hσ, ← pow_mul, ← pow_mul]
    exact hpow
  have hBT := CFSG.LieType.BorelTits.holds_of_chevalleyExceptionalModel hYm
  have hPC : ∀ j : Fin 2, graphFixedParabolic TwistTag.D4 K σ.toRingHom {d4Index j} ≤
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    fun j => graphFixedParabolic_le _ _ _ _
  have hcases : ∀ a : Fin TwistTag.D4.foldedTag.rank, a = fa0 ∨ a = fa1 := by decide
  have hne : ∀ j : Fin 2, ({d4Index j} : Set (Fin TwistTag.D4.foldedTag.rank)) ≠ Set.univ :=
    fun j => by
      rcases hcases (d4Index j) with h | h <;> rw [h]
      · exact singleton_ne_univ_fa0
      · exact singleton_ne_univ_fa1
  have hQ : ∀ j : Fin 2,
      ((graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom {d4Index j}).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).map
          φ.symm.toMonoidHom ≠ ⊥ ∧
        IsPGroup 2 ↥(((graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom
          {d4Index j}).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).map φ.symm.toMonoidHom) ∧
        ((graphFixedParabolic TwistTag.D4 K σ.toRingHom {d4Index j}).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).map
            φ.symm.toMonoidHom ≤ Subgroup.normalizer ((((graphFixedParabolicRadical TwistTag.D4 K
              σ.toRingHom {d4Index j}).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).map φ.symm.toMonoidHom :
                Subgroup Y) : Set Y) := by
    intro j
    obtain ⟨hQP, hPN, hQ2, -⟩ := library_facts σ (d4Index j) (hne j)
    have hQC := hQP.trans (hPC j)
    refine ⟨?_, ?_, ?_⟩
    · intro h0
      have hna : ∃ x ∈ graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom {d4Index j},
          ∃ y ∈ graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom {d4Index j},
            x * y ≠ y * x := by
        rcases hcases (d4Index j) with h | h <;> rw [h]
        · exact nonabelian_a0 σ hσ3
        · exact nonabelian_a1 σ hσ3
      obtain ⟨x, hx, y, hy, hxy⟩ := hna
      have hx1 : φ.symm ⟨x, hQC hx⟩ = 1 := by
        have : φ.symm ⟨x, hQC hx⟩ ∈ ((graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom
            {d4Index j}).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).map φ.symm.toMonoidHom :=
          ⟨⟨x, hQC hx⟩, hx, rfl⟩
        rwa [h0, Subgroup.mem_bot] at this
      have hx' : x = 1 := by
        have := congrArg Subtype.val ((MulEquiv.map_eq_one_iff φ.symm).1 hx1)
        exact this
      exact hxy (by rw [hx', one_mul, mul_one])
    · exact (hQ2.of_equiv (Subgroup.subgroupOfEquivOfLe hQC).symm).map _
    · rintro _ ⟨p, hp, rfl⟩
      refine Subgroup.le_normalizer_map _ ⟨p, ?_, rfl⟩
      rw [← Subgroup.subgroupOf_normalizer_eq hQC]
      exact hPN hp
  set P : Fin 2 → Subgroup Y := fun j =>
    ((graphFixedParabolic TwistTag.D4 K σ.toRingHom {d4Index j}).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).map φ.symm.toMonoidHom with hP
  have hmem : ∀ M : Subgroup Y, (M = M₁ ∨ M = M₂) → ∃ j, M = P j := by
    intro M hM
    obtain ⟨hMmax, hTM⟩ := (hpair.2.2 M).2 hM
    obtain ⟨j, g, hMj⟩ := NQCat.G24Split.exists_eq_map_conj_of_isMaximalTwoLocal hpair.1 hres hBT
      (Q := fun j => ((graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom {d4Index j}).subgroupOf
        (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).map φ.symm.toMonoidHom) hQ hpair.1
      hMmax hTM
    have hPcov : P j ⋖ ⊤ := (hres.2.2.1 _ (hres.2.1 j)).mpr ⟨j, rfl⟩
    have hcov : M ⋖ ⊤ := by
      set e := MulAut.conj g
      have h1 := (apply_covBy_apply_iff (MulEquiv.mapSubgroup e)).mpr hPcov
      have h2 : MulEquiv.mapSubgroup e ⊤ = ⊤ := Subgroup.map_top_of_surjective _ e.surjective
      rw [h2] at h1
      rw [hMj]
      exact h1
    exact (hres.2.2.1 M (Subgroup.le_normalizer.trans hTM)).mp hcov
  obtain ⟨Ps, hTPs, hPscov, hPss⟩ := F5113.exists_coatom_d42 hYm hpair.1
  obtain ⟨js, hjs⟩ := (hres.2.2.1 Ps hTPs).mp hPscov
  obtain ⟨j₁, h₁⟩ := hmem M₁ (Or.inl rfl)
  obtain ⟨j₂, h₂⟩ := hmem M₂ (Or.inr rfl)
  have hj : j₁ ≠ j₂ := fun h => hpair.2.1 (by rw [h₁, h₂, h])
  have hjs' : js = j₁ ∨ js = j₂ := by
    revert hj
    fin_cases js <;> fin_cases j₁ <;> fin_cases j₂ <;> simp
  rcases hjs' with rfl | rfl
  · left
    rw [h₁, ← hjs]
    exact hPss
  · right
    rw [h₂, ← hjs]
    exact hPss

end Sec526

end CFSG.Quasithin.H13
