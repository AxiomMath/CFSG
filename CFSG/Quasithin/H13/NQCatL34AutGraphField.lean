module

public import CFSG.Quasithin.H13.NQCatL34AutGraph
public import CFSG.Quasithin.Recognition.HSTypeFactAut2

public section

namespace CFSG.Quasithin.H13.NQCat.L34Aut

open MulAction CFSG.Fischer CFSG.ComponentClassification.WittDesign CFSG.Quasithin.Asc94
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.LinearThreeFourOuter CFSG.RankThree.PartTwo.KFacts.L34
  CFSG.RankThree.Asc83Table Matrix
open CFSG.LocalAnalysis.ComponentInitial.GL3TwoFixedModel (autFixed mem_autFixed)

theorem exists_quaternion_le_normalizer {L : Type*} [Group L] [Finite L] {B : Subgroup L}
    (hN : Nat.card (Subgroup.normalizer (B : Set L)) = 72)
    (e : Automizer B ≃* QuaternionGroup 2) :
    ∃ Q : Subgroup L, Q ≤ Subgroup.normalizer (B : Set L) ∧ Nonempty (Q ≃* QuaternionGroup 2) := by
  have hQ8 : Nat.card (Automizer B) = 8 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hK : Nat.card ((Subgroup.centralizer (B : Set L)).subgroupOf
      (Subgroup.normalizer (B : Set L))) = 9 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
      ((Subgroup.centralizer (B : Set L)).subgroupOf (Subgroup.normalizer (B : Set L)))
    change _ = Nat.card (Automizer B) * _ at h
    rw [hN, hQ8] at h
    omega
  obtain ⟨S, hS⟩ := Sylow.exists_subgroup_card_pow_prime
    (G := Subgroup.normalizer (B : Set L)) 2 (n := 3) (by rw [hN]; norm_num)
  have hc : S.IsComplement' ((Subgroup.centralizer (B : Set L)).subgroupOf
      (Subgroup.normalizer (B : Set L))) :=
    Subgroup.isComplement'_of_coprime (by rw [hS, hK, hN]; norm_num) (by rw [hS, hK]; norm_num)
  exact ⟨S.map (Subgroup.normalizer (B : Set L)).subtype, Subgroup.map_subtype_le S,
    ⟨(S.equivMapOfInjective (Subgroup.normalizer (B : Set L)).subtype
      (Subgroup.normalizer (B : Set L)).subtype_injective).symm.trans
      (hc.QuotientMulEquiv.symm.trans e)⟩⟩

section Model

variable {k : Type} [Field k]

theorem exists_quaternion_le_normalizer_eZero (hk : Nat.card k = 4) :
    ∃ Q : Subgroup (projectiveSL 3 k), Q ≤ Subgroup.normalizer (eZero k : Set (projectiveSL 3 k)) ∧
      Nonempty (Q ≃* QuaternionGroup 2) := by
  have := LinearFieldFour.finite_of_card_eq_four hk
  obtain ⟨e⟩ := nonempty_automizer_eZero hk
  exact exists_quaternion_le_normalizer (card_normalizer_eZero hk) e

theorem graphField_fixed (hk : Nat.card k = 4) {σ : k ≃+* k} (hσ : ∀ a, σ a = a ^ 2)
    {A : GL (Fin 3) k} (hβ : nf σ A 1 1 * nf σ A 1 1 = 1) :
    (∃ Q : Subgroup (projectiveSL 3 k), Nonempty (Q ≃* QuaternionGroup 2) ∧
        ∀ e ∈ Q, nf σ A 1 1 e = e) ∧
      ∃ F : Subgroup (projectiveSL 3 k), Nat.card F = 9 ∧ ∀ f ∈ F, nf σ A 1 1 f = f := by
  have : CharP k 2 := LinearFieldFour.charP_two_of_card_eq_four hk
  have hff := fieldAut_sigma_mul_self hσ hk
  rcases involution_cases_card hk hσ hβ with ⟨d, hd⟩ | ⟨⟨H, hH⟩, -⟩ | ⟨⟨H, hH⟩, -⟩ |
    ⟨⟨H, hH⟩, -⟩
  ·
    exfalso
    obtain ⟨g, rfl⟩ := proj_surjective 3 k d
    rw [← conjAut_toGL, ← nf_zero_zero σ] at hd
    have h1 := (nf_inj hσ hk hd.symm).2.1
    revert h1
    decide
  ·
    exfalso
    rw [← map_inv, ← nf_zero_zero σ H, ← nf_zero_zero σ H⁻¹, ← nf_one_zero (k := k) σ,
      nf_mul σ hff, nf_mul σ hff] at hH
    have h1 := (nf_inj hσ hk hH).2.2
    revert h1
    decide
  ·
    exfalso
    rw [← map_inv, ← nf_zero_zero σ H, ← nf_zero_zero σ H⁻¹, ← nf_zero_one (k := k) σ,
      nf_mul σ hff, nf_mul σ hff] at hH
    have h1 := (nf_inj hσ hk hH).2.1
    revert h1
    decide
  ·
    have hfix : ∀ x ∈ (Subgroup.normalizer (eZero k : Set (projectiveSL 3 k))).map
        (conjAut 3 k H).toMonoidHom, nf σ A 1 1 x = x := by
      intro x hx
      rw [← autFixed_betaAut hk hσ, ← autFixed_conj, ← hH] at hx
      exact mem_autFixed.1 hx
    obtain ⟨Q, hQ, ⟨e⟩⟩ := exists_quaternion_le_normalizer_eZero hk
    exact ⟨⟨Q.map (conjAut 3 k H).toMonoidHom,
        ⟨(Q.equivMapOfInjective (conjAut 3 k H).toMonoidHom (conjAut 3 k H).injective).symm.trans
          e⟩,
        fun x hx => hfix x (Subgroup.map_mono hQ hx)⟩,
      (eZero k).map (conjAut 3 k H).toMonoidHom,
      by rw [Subgroup.card_map_of_injective (f := (conjAut 3 k H).toMonoidHom)
        (conjAut 3 k H).injective, card_eZero hk],
      fun x hx => hfix x (Subgroup.map_mono Subgroup.le_normalizer hx)⟩

theorem swap_aut_model (hk : Nat.card k = 4) {β : MulAut (projectiveSL 3 k)}
    (h1 : (projStabilizer (flagSpace 3 k 1)).map β.toMonoidHom = projStabilizer (flagSpace 3 k 2))
    (h2 : (projStabilizer (flagSpace 3 k 2)).map β.toMonoidHom =
      projStabilizer (flagSpace 3 k 1)) :
    (β * β ∈ (MulAut.conj : projectiveSL 3 k →* MulAut (projectiveSL 3 k)).range →
      ∃ M : SpecialLinearGroup (Fin 3) k, M ∈ stabilizer (flagSpace 3 k 1) ∧
        M ∈ stabilizer (flagSpace 3 k 2) ∧
          MulAut.conj (proj 3 k M) * β * (MulAut.conj (proj 3 k M) * β) = 1) ∧
    (β * β = 1 →
      ((∃ Q : Subgroup (projectiveSL 3 k), Nonempty (Q ≃* QuaternionGroup 2) ∧
          ∀ e ∈ Q, β e = e) ∧
        ∃ F : Subgroup (projectiveSL 3 k), Nat.card F = 9 ∧ ∀ f ∈ F, β f = f) ∨
      ∃ Y : SpecialLinearGroup (Fin 3) k, Y ∈ stabilizer (flagSpace 3 k 1) ∧
        Y ∈ stabilizer (flagSpace 3 k 2) ∧ orderOf (proj 3 k Y) = 3 ∧
          β (proj 3 k Y) = proj 3 k Y) := by
  have : CharP k 2 := LinearFieldFour.charP_two_of_card_eq_four hk
  have := LinearFieldFour.finite_of_card_eq_four hk
  have hσ : ∀ a, frobeniusEquiv k 2 a = a ^ 2 := fun a => frobeniusEquiv_apply k 2 a
  refine ⟨swap_aut_square hk hσ h1 h2, fun hβ => ?_⟩
  obtain ⟨A, a, rfl, hA12, hA22, hA21⟩ := swap_nf hk hσ h1 h2
  rcases zmod_two_cases a with rfl | rfl
  · exact Or.inr (swap_graph_fixed hk hσ hA12 hA22 hA21 hβ)
  · exact Or.inl (graphField_fixed hk hσ hβ)

end Model

theorem factAutL34GraphField_holds :
    HSType.FactAutL34GraphField := by
  intro β hβP
  obtain ⟨Ψ, hΨ1, hΨ2⟩ := exists_m22Zero_equiv
  obtain ⟨β', hβ'apply⟩ : ∃ β' : MulAut (projectiveSL 3 F4), ∀ y, β' y = Ψ (β (Ψ.symm y)) :=
    ⟨Ψ.symm.trans (β.trans Ψ), fun y => rfl⟩
  have hβ'x : ∀ x, β' (Ψ x) = Ψ (β x) := fun x => by rw [hβ'apply, MulEquiv.symm_apply_apply]
  have hsymm : ∀ y, β'.symm y = Ψ (β.symm (Ψ.symm y)) := fun y => by
    rw [MulEquiv.symm_apply_eq, hβ'x, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  have hfix : ∀ y, β' y = y → β (Ψ.symm y) = Ψ.symm y := fun y hy =>
    Ψ.injective ((hβ'apply y).symm.trans (hy.trans (Ψ.apply_symm_apply y).symm))
  have hcard : Nat.card F4 = 4 := by rw [Nat.card_eq_fintype_card, F4.card]
  have h1 : (projStabilizer (flagSpace 3 F4 1)).map β'.toMonoidHom =
      projStabilizer (flagSpace 3 F4 2) := by
    ext y
    rw [Subgroup.mem_map_equiv, hsymm, ← hΨ1, (hβP _).1, MulEquiv.apply_symm_apply, hΨ2,
      MulEquiv.apply_symm_apply]
  have h2 : (projStabilizer (flagSpace 3 F4 2)).map β'.toMonoidHom =
      projStabilizer (flagSpace 3 F4 1) := by
    ext y
    rw [Subgroup.mem_map_equiv, hsymm, ← hΨ2, (hβP _).2, MulEquiv.apply_symm_apply, hΨ1,
      MulEquiv.apply_symm_apply]
  have hstab : ∀ {i : ℕ} {M : SpecialLinearGroup (Fin 3) F4}, M ∈ stabilizer (flagSpace 3 F4 i) →
      Ψ (Ψ.symm (proj 3 F4 M)) ∈ projStabilizer (flagSpace 3 F4 i) := fun hM => by
    rw [MulEquiv.apply_symm_apply]
    exact proj_mem_projStabilizer_iff.2 hM
  obtain ⟨hsq, hinv⟩ := swap_aut_model hcard h1 h2
  refine ⟨fun ⟨ℓ, hℓ⟩ => ?_, fun hβ2 => ?_⟩
  ·
    have hinn : β' * β' ∈
        (MulAut.conj : projectiveSL 3 F4 →* MulAut (projectiveSL 3 F4)).range := by
      refine ⟨Ψ ℓ, ?_⟩
      ext y
      obtain ⟨x, rfl⟩ := Ψ.surjective y
      rw [MulAut.conj_apply, MulAut.mul_apply, hβ'x, hβ'x, hℓ, map_mul, map_mul, map_inv]
    obtain ⟨M, hM1, hM2, hMsq⟩ := hsq hinn
    refine ⟨Ψ.symm (proj 3 F4 M), (hΨ1 _).2 (hstab hM1), (hΨ2 _).2 (hstab hM2), fun x => ?_⟩
    apply Ψ.injective
    have h := congrArg (fun α : MulAut (projectiveSL 3 F4) => α (Ψ x)) hMsq
    simp only [MulAut.mul_apply, MulAut.one_apply, MulAut.conj_apply] at h
    have hm : Ψ (Ψ.symm (proj 3 F4 M)) = proj 3 F4 M := Ψ.apply_symm_apply _
    rw [map_mul Ψ, map_mul Ψ, map_inv Ψ, ← hβ'x, map_mul Ψ, map_mul Ψ, map_inv Ψ, ← hβ'x, hm]
    exact h
  ·
    have hβ'2 : β' * β' = 1 := by
      ext y
      rw [MulAut.mul_apply, hβ'apply, hβ'apply, MulEquiv.symm_apply_apply, hβ2,
        MulEquiv.apply_symm_apply, MulAut.one_apply]
    rcases hinv hβ'2 with ⟨⟨Q, ⟨eQ⟩, hQ⟩, F, hF, hFfix⟩ | ⟨Y, hY1, hY2, hY3, hYfix⟩
    · left
      refine ⟨⟨Q.map Ψ.symm.toMonoidHom,
          ⟨(Q.equivMapOfInjective Ψ.symm.toMonoidHom Ψ.symm.injective).symm.trans eQ⟩, ?_⟩,
        F.map Ψ.symm.toMonoidHom, by rw [Subgroup.card_map_of_injective Ψ.symm.injective]; exact hF,
        ?_⟩
      · rintro _ ⟨q, hq, rfl⟩
        exact hfix q (hQ q hq)
      · rintro _ ⟨f, hf, rfl⟩
        exact hfix f (hFfix f hf)
    · right
      exact ⟨Ψ.symm (proj 3 F4 Y), (hΨ1 _).2 (hstab hY1), (hΨ2 _).2 (hstab hY2),
        by rw [MulEquiv.orderOf_eq]; exact hY3, hfix _ hYfix⟩

end CFSG.Quasithin.H13.NQCat.L34Aut
