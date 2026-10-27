module

public import CFSG.LinearAlgebra.RootGroupSL.UCasesAbs
public import CFSG.LinearAlgebra.RootGroupSL.DatumTransport
public import CFSG.LinearAlgebra.RootGroupSL.Transport
public import CFSG.LocalAnalysis.StandardType.GGSixStepOneCompDefs

public section

namespace CFSG.StandardType.StarFour

open CFSG.LinearAlgebra.RootGroupSL CFSG.Open CFSG.StandardType

variable {F E V : Type} [Field F] [Finite F] [CharP F 2] [Field E] [Algebra F E] [Finite E]
  [AddCommGroup V] [Module F V] [Module.Finite F V] {X : Type} [Group X]

private lemma mem_normalizer_comap_of_map_mem {S G : Type*} [Group S] [Group G]
    (f : S →* G) (H : Subgroup G) {n : S}
    (hn : f n ∈ Subgroup.normalizer (H : Set G)) :
    n ∈ Subgroup.normalizer ((H.comap f : Subgroup S) : Set S) := by
  rw [Subgroup.mem_normalizer_iff] at hn ⊢
  intro u
  rw [Subgroup.mem_comap, Subgroup.mem_comap]
  simpa [map_mul, map_inv] using hn (f u)

private lemma map_centralizer_le_centralizer_map {S G : Type*} [Group S] [Group G]
    (f : S →* G) (H : Subgroup S) :
    (Subgroup.centralizer (H : Set S)).map f ≤
      Subgroup.centralizer ((H.map f : Subgroup G) : Set G) := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  rw [Subgroup.mem_centralizer_iff] at hy ⊢
  intro z hz
  obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hz
  rw [← map_mul, ← map_mul, hy w hw]

theorem pCoreOf_inf_normalizer_map_datumRoot (ψ : SpecialLinearGroup F V →* X)
    (hψ : Function.Injective ψ) (ι : E →ₗ[F] V) (π : V →ₗ[F] E) (h : ∀ t, π (ι t) = 0)
    (hι : Function.Injective ι) (hπ : Function.Surjective π)
    (hV : 2 * Module.finrank F E < Module.finrank F V) :
    pCoreOf 2 (ψ.range ⊓ Subgroup.normalizer
        (((datumRoot ι π h).map ψ : Subgroup X) : Set X)) = (datumQ ι π).map ψ := by
  haveI : Module.Finite F E := Module.Finite.of_finite
  rw [map_normalizer_eq_inf_normalizer_map ψ hψ (datumRoot ι π h),
    pCoreOf_map_of_injective ψ hψ 2 (Subgroup.normalizer (datumRoot ι π h)),
    pCoreOf_normalizer_datumRoot ι π h hι hπ hV]

theorem map_datumQ0_le_ggCenterOf (ψ : SpecialLinearGroup F V →* X) (ι : E →ₗ[F] V)
    (π : V →ₗ[F] E) (h : ∀ t, π (ι t) = 0) :
    (datumQ0 ι π).map ψ ≤ ggCenterOf ((datumQ ι π).map ψ) := by
  intro x hx
  obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hx
  have hzQ : z ∈ datumQ ι π := datumQ0_le_datumQ ι π h hz
  refine Subgroup.mem_map.mpr ⟨⟨ψ z, Subgroup.mem_map_of_mem ψ hzQ⟩, ?_, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro w
  obtain ⟨q, hq, hqw⟩ := Subgroup.mem_map.mp w.2
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hqw, ← map_mul, ← map_mul]
  exact congrArg ψ (datumQ0_commute_datumQ ι π hq hz)

theorem eq_map_datumU_of_pCore (ψ : SpecialLinearGroup F V →* X) (hψ : Function.Injective ψ)
    (hd : 2 ≤ Module.finrank F E) (ι : E →ₗ[F] V) (π : V →ₗ[F] E) (h : ∀ t, π (ι t) = 0)
    (hι : Function.Injective ι) (hπ : Function.Surjective π)
    (hV : 2 * Module.finrank F E < Module.finrank F V) (U : Subgroup X)
    (hU₁ : ggCenterOf (pCoreOf 2 (ψ.range ⊓ Subgroup.normalizer
      (((datumRoot ι π h).map ψ : Subgroup X) : Set X))) ≤ U)
    (hU₂ : U ≤ pCoreOf 2 (ψ.range ⊓ Subgroup.normalizer
      (((datumRoot ι π h).map ψ : Subgroup X) : Set X)))
    (hU₃ : U ≠ pCoreOf 2 (ψ.range ⊓ Subgroup.normalizer
      (((datumRoot ι π h).map ψ : Subgroup X) : Set X)))
    (hU₄ : ¬ pCoreOf 2 (ψ.range ⊓ Subgroup.normalizer
      (((datumRoot ι π h).map ψ : Subgroup X) : Set X)) ≤ Subgroup.centralizer (U : Set X))
    (hU₅ : ψ.range ⊓ Subgroup.normalizer (((datumRoot ι π h).map ψ : Subgroup X) : Set X) ≤
      Subgroup.normalizer (U : Set X)) :
    U = (datumU1 ι).map ψ ∨ U = (datumU2 π).map ψ := by
  haveI : Module.Finite F E := Module.Finite.of_finite
  have hO : pCoreOf 2 (ψ.range ⊓ Subgroup.normalizer
      (((datumRoot ι π h).map ψ : Subgroup X) : Set X)) = (datumQ ι π).map ψ :=
    pCoreOf_inf_normalizer_map_datumRoot ψ hψ ι π h hι hπ hV
  rw [hO] at hU₁ hU₂ hU₃ hU₄
  have hUle : U ≤ ψ.range :=
    hU₂.trans (Subgroup.map_le_range ψ (datumQ ι π))
  have hUeq : U = (U.comap ψ).map ψ :=
    (Subgroup.map_comap_eq_self (f := ψ) hUle).symm
  have hQ0 : datumQ0 ι π ≤ U.comap ψ :=
    (Subgroup.map_le_iff_le_comap (f := ψ)).mp
      ((map_datumQ0_le_ggCenterOf ψ ι π h).trans hU₁)
  have hUQ : U.comap ψ ≤ datumQ ι π := by
    have hmono := Subgroup.comap_mono (f := ψ) hU₂
    rwa [Subgroup.comap_map_eq_self_of_injective hψ (datumQ ι π)] at hmono
  have hne : U.comap ψ ≠ datumQ ι π := by
    intro hcon
    apply hU₃
    rw [hUeq, hcon]
  have hN : Subgroup.normalizer (datumRoot ι π h : Set (SpecialLinearGroup F V)) ≤
      Subgroup.normalizer (U.comap ψ : Set (SpecialLinearGroup F V)) := by
    intro n hn
    have hmem : ψ n ∈ ψ.range ⊓ Subgroup.normalizer
        (((datumRoot ι π h).map ψ : Subgroup X) : Set X) := by
      rw [map_normalizer_eq_inf_normalizer_map ψ hψ (datumRoot ι π h)]
      exact Subgroup.mem_map_of_mem ψ hn
    have hψn : ψ n ∈ Subgroup.normalizer (U : Set X) := hU₅ hmem
    exact mem_normalizer_comap_of_map_mem ψ U hψn
  have hnc : ¬ datumQ ι π ≤
      Subgroup.centralizer (U.comap ψ : Set (SpecialLinearGroup F V)) := by
    intro hc
    apply hU₄
    calc (datumQ ι π).map ψ
        ≤ (Subgroup.centralizer (U.comap ψ : Set (SpecialLinearGroup F V))).map ψ :=
          Subgroup.map_mono (f := ψ) hc
      _ ≤ Subgroup.centralizer (((U.comap ψ).map ψ : Subgroup X) : Set X) :=
          map_centralizer_le_centralizer_map ψ (U.comap ψ)
      _ = Subgroup.centralizer (U : Set X) := by rw [← hUeq]
  rcases eq_datumU1_or_eq_datumU2 hd ι π h hι hπ (U.comap ψ) hQ0 hUQ hne hN hnc with
    h1 | h2
  · left
    rw [hUeq, h1]
  · right
    rw [hUeq, h2]

end CFSG.StandardType.StarFour
