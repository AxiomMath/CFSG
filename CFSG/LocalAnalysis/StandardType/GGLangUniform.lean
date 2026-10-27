module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcInnerLang.Core
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TorusAtCore
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin

public section

namespace CFSG.StandardType.LangRat

section Uniform

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE


theorem exists_langSetup_of_toral_datum_uniform {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
    {ℓ f : ℕ} (hℓ : ℓ.Prime) [CharP L ℓ] (hf : 1 ≤ f) (D : LangDatum τ L) (hDq : D.q = ℓ ^ f)
    {p₀ : ℕ} (hp₀ : p₀.Prime) (hp₀ℓ : p₀ ≠ ℓ) (hq₀ : 5 ≤ p₀ ∨ 4 ≤ D.q)
    (hfin : Finite D.model) {C : Type} [Group C] (ι₀ : C →* ModGL τ L)
    (hι₀ : Function.Injective ι₀) (hΓ : D.Γ = ι₀.range.map (MulAut.conj D.g0⁻¹).toMonoidHom) :
    ∃ (S : LangSetup τ L p₀) (ι : C →* ModGL τ L),
      S.D = D ∧ (∀ c, ι c = D.g0⁻¹ * ι₀ c * D.g0) ∧ Function.Injective ι ∧ ι.range = S.Γ ∧
      ∀ u ∈ D.torus.map (MulAut.conj D.g0).toMonoidHom, ∃ a : Fin τ.rank → Lˣ,
        rootDiagUnit τ a ∈ S.D.torus ∧ rootDiagUnit τ a = D.g0⁻¹ * u * D.g0 ∧
        ∀ β : MulAut C, (∀ c, ι₀ (β c) = u * ι₀ c * u⁻¹) →
          ∀ c, ι (β c) = rootDiagUnit τ a * ι c * (rootDiagUnit τ a)⁻¹ := by
  classical
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hqpow : IsPrimePow D.q ∧ ((D.q : ℕ) : L) = 0 := by
    rw [hDq]
    exact ⟨hℓ.isPrimePow.pow (by omega), (CharP.cast_eq_zero_iff L ℓ _).2
      (dvd_pow_self ℓ (by omega))⟩
  have hpq : ¬ p₀ ∣ D.q := by
    rw [hDq]
    intro h
    exact hp₀ℓ ((Nat.prime_dvd_prime_iff_eq hp₀ hℓ).1 (hp₀.dvd_of_dvd_pow h))
  obtain ⟨ρ, hρ⟩ := frobeniusOnRoots_proved τ L D
  let ι : C →* ModGL τ L := (MulAut.conj D.g0⁻¹).toMonoidHom.comp ι₀
  have hι : ∀ c, ι c = D.g0⁻¹ * ι₀ c * D.g0 := fun c => by
    change (MulAut.conj D.g0⁻¹) (ι₀ c) = _
    rw [MulAut.conj_apply, inv_inv]
  refine ⟨D.toSetup p₀ ρ hρ hp₀ hq₀ hqpow hpq hfin, ι, rfl, hι,
    (MulAut.conj D.g0⁻¹).injective.comp hι₀, ?_, fun u hu => ?_⟩
  · show ι.range = D.Γ
    rw [hΓ]
    exact MonoidHom.range_comp (MulAut.conj D.g0⁻¹).toMonoidHom ι₀
  · obtain ⟨y, hy, hyu⟩ := hu
    have hyu' : y = D.g0⁻¹ * u * D.g0 := by
      have h : D.g0 * y * D.g0⁻¹ = u := hyu
      rw [← h]
      group
    obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (mem_twistedTorusOf.1 hy).1
    refine ⟨a, ha ▸ hy, ha.symm.trans hyu', fun β hβ c => ?_⟩
    rw [hι, hι, hβ c, ← ha, hyu']
    group


end Uniform

end CFSG.StandardType.LangRat
