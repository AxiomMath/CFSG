module

public import CFSG.RankThree.PartTwo.Sec17.F174L3AutCore

open scoped MatrixGroups Matrix

public section

namespace CFSG.RankThree.PartTwo.Sec17.F174L3Aut.Final

theorem l3Aut_holds : ∀ (H : Type) [Group H] [Finite H] (n : ℕ), Odd n →
    Nonempty (H ≃* CFSG.PGLModel.projSL 3 (GaloisField 2 n)) →
    ∀ σ : MulAut H, (∃ k : ℕ, σ ^ (2 ^ k) = 1) → ∀ t : H, orderOf t = 3 → σ t = t →
      ∀ D : Subgroup H, D ≠ ⊥ → IsPGroup 2 D → (∀ d ∈ D, σ d ∈ D) →
        (∀ u : H, u * t = t * u → ∀ d ∈ D, u * d * u⁻¹ ∈ D) → σ = 1 := by
  intro H _ _ n hn ⟨e⟩ σ hσk t ht hσt D hD0 hD2 hσD hDt
  classical
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact absurd hn (by decide)
  letI : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  have hF : Fintype.card (GaloisField 2 n) = 2 ^ n := by
    rw [Fintype.card_eq_nat_card]
    exact GaloisField.card 2 n hn0
  have hω := Flag.hω_of_card hn hF
  have hcube : ∀ r : GaloisField 2 n, r ^ 3 = 1 → r = 1 := fun r hr =>
    Flag.eq_one_of_pow_three hω hr
  let eS : H ≃* SL(3, GaloisField 2 n) :=
    e.trans ((CFSG.RankThree.PartTwo.Sec4.projSLEquivProjectiveSL 3 (GaloisField 2 n)).trans
      (Tr.projEquiv hcube).symm)
  have hσ' : ∃ k : ℕ, (MulAut.congr eS σ) ^ (2 ^ k) = 1 := by
    obtain ⟨k, hk⟩ := hσk
    exact ⟨k, by rw [← map_pow, hk, map_one]⟩
  have ht' : orderOf (eS t) = 3 :=
    (orderOf_injective eS.toMonoidHom eS.injective t).trans ht
  have hσt' : (MulAut.congr eS σ) (eS t) = eS t := by
    rw [MulAut.congr_apply]
    simp [hσt]
  have hD0' : D.map eS.toMonoidHom ≠ ⊥ := by
    rw [Ne, Subgroup.map_eq_bot_iff_of_injective D eS.injective]
    exact hD0
  have hD2' : IsPGroup 2 ↥(D.map eS.toMonoidHom) := by
    rintro ⟨x, d, hd, rfl⟩
    obtain ⟨k, hk⟩ := hD2 ⟨d, hd⟩
    refine ⟨k, Subtype.ext ?_⟩
    have h1 : d ^ (2 ^ k) = 1 := congrArg Subtype.val hk
    show (eS d) ^ (2 ^ k) = 1
    rw [← map_pow, h1, map_one]
  have hσD' : ∀ d ∈ D.map eS.toMonoidHom, (MulAut.congr eS σ) d ∈ D.map eS.toMonoidHom := by
    rintro _ ⟨d, hd, rfl⟩
    refine ⟨σ d, hσD d hd, ?_⟩
    rw [MulAut.congr_apply]
    simp
  have hDt' : ∀ d ∈ D.map eS.toMonoidHom,
      eS t * d * (eS t)⁻¹ ∈ D.map eS.toMonoidHom := by
    rintro _ ⟨d, hd, rfl⟩
    refine ⟨t * d * t⁻¹, hDt t rfl d hd, ?_⟩
    simp
  have h1 := Core.l3Aut_core hn hF (MulAut.congr eS σ) hσ' (eS t) ht' hσt'
    (D.map eS.toMonoidHom) hD0' hD2' hσD' hDt'
  exact (MulAut.congr eS).injective (by rw [h1, map_one])

end CFSG.RankThree.PartTwo.Sec17.F174L3Aut.Final
