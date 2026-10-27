module

public import CFSG.Quasithin.Vol2.Ch11SecQ9aCartE
public import CFSG.Quasithin.Vol2.Ch11SecQ9aCartD
public import CFSG.Quasithin.Vol2.Ch11SecSFactsCartan

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open Matrix CFSG.Quasithin CFSG.Quasithin.Vol2.KGNat
  CFSG.ClassicalInvolution.ModelFacts.OddCover CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Open (pCoreOf)
open CFSG.Assembly.LowTwoRank (StatedSL)

namespace C11P9A

variable {K : Type} [Field K] {W : Type*} [CommGroup W] {H : Subgroup (MulAut W)}
  {Z : Subgroup W} {π : ↥(StatedSL 3 K) →* ↥H} {f : W → (Fin 3 → K)}

theorem eq_map_psiW_of_sylow {P : Subgroup (MulAut W)} {g : SpecialLinearGroup (Fin 3) K}
    (hg : ∀ x : MulAut W, x ∈ P ↔ ∃ u ∈ Usl K, x = ((rho3 π (g * u * g⁻¹) : ↥H) : MulAut W)) :
    P = (unitriangular 3 K).map (psiW π g) := by
  ext x
  rw [hg, ← usl_eq_unitriangular]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, hu, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, hu, rfl⟩

theorem inf_normalizer_eq (hf : IsCoord (linModelNat (StatedSL 3 K)) H Z π f)
    (g : SpecialLinearGroup (Fin 3) K) :
    H ⊓ Subgroup.normalizer
        (((unitriangular 3 K).map (psiW π g) : Subgroup (MulAut W)) : Set (MulAut W)) =
      (upperTriangular 3 K).map (psiW π g) := by
  have hψ := psiW_injective hf g
  ext x
  constructor
  · rintro ⟨hxH, hxN⟩
    obtain ⟨A, rfl⟩ := exists_psiW_eq hf g hxH
    refine ⟨A, ?_, rfl⟩
    rw [← normalizer_unitriangular]
    exact (map_mem_normalizer_iff _ hψ).mp hxN
  · rintro ⟨A, hA, rfl⟩
    refine ⟨psiW_mem π g A, (map_mem_normalizer_iff _ hψ).mpr ?_⟩
    rw [normalizer_unitriangular]
    exact hA

theorem sylow_conj_mul {P : Subgroup (MulAut W)} {g x : SpecialLinearGroup (Fin 3) K}
    (hg : ∀ y : MulAut W, y ∈ P ↔ ∃ u ∈ Usl K, y = ((rho3 π (g * u * g⁻¹) : ↥H) : MulAut W))
    (hx : x ∈ unitriangular 3 K) :
    ∀ y : MulAut W, y ∈ P ↔
      ∃ u ∈ Usl K, y = ((rho3 π ((g * x) * u * (g * x)⁻¹) : ↥H) : MulAut W) := by
  intro y
  rw [hg, usl_eq_unitriangular]
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨x⁻¹ * u * x, (unitriangular 3 K).mul_mem ((unitriangular 3 K).mul_mem
      ((unitriangular 3 K).inv_mem hx) hu) hx, ?_⟩
    rw [show g * x * (x⁻¹ * u * x) * (g * x)⁻¹ = g * u * g⁻¹ by group]
  · rintro ⟨u, hu, rfl⟩
    refine ⟨x * u * x⁻¹, (unitriangular 3 K).mul_mem ((unitriangular 3 K).mul_mem hx hu)
      ((unitriangular 3 K).inv_mem hx), ?_⟩
    rw [show g * (x * u * x⁻¹) * g⁻¹ = g * x * u * (g * x)⁻¹ by group]

variable [Finite K]

theorem exists_eq_map_torus3 [CharP K 2] (hf : IsCoord (linModelNat (StatedSL 3 K)) H Z π f)
    (g : SpecialLinearGroup (Fin 3) K) {D : Subgroup (MulAut W)}
    (hD : CFSG.QuasithinUnique.Lin2.IsHallTwoPrimeOf D ((upperTriangular 3 K).map (psiW π g))) :
    ∃ x ∈ unitriangular 3 K, D = (torus3 K).map (psiW π (g * x)) := by
  have hψ := psiW_injective hf g
  obtain ⟨hDle, hDodd, k, hk⟩ := hD
  have hDeq : (D.comap (psiW π g)).map (psiW π g) = D :=
    Subgroup.map_comap_eq_self (hDle.trans (Subgroup.map_le_range _ _))
  have hD0 : CFSG.QuasithinUnique.Lin2.IsHallTwoPrimeOf (D.comap (psiW π g))
      (upperTriangular 3 K) := by
    refine ⟨?_, ?_, k, ?_⟩
    · have := Subgroup.comap_mono (f := psiW π g) hDle
      rwa [Subgroup.comap_map_eq_self_of_injective hψ] at this
    · rw [← Subgroup.card_map_of_injective hψ, hDeq]
      exact hDodd
    · rw [← Subgroup.relIndex_map_map_of_injective _ _ hψ, hDeq]
      exact hk
  obtain ⟨x, hx, hxD⟩ := exists_conj_torus3_of_isHall hD0
  refine ⟨x, hx, ?_⟩
  rw [← hDeq, hxD, Subgroup.map_map, psiW_mul]

theorem gammaW_one_eq (hSL : commutator (SpecialLinearGroup (Fin 2) K) = ⊤)
    (hf : IsCoord (linModelNat (StatedSL 3 K)) H Z π f) (g : SpecialLinearGroup (Fin 3) K) :
    gammaW H (hf.pre (gmap g (flagSpace 3 K 1)).toAddSubgroup) =
      (stabE0 K).map (psiW π g) := by
  ext x
  rw [gammaW, mem_perfectCore_HU1_iff hSL hf g x]
  constructor
  · rintro ⟨B, hB, rfl⟩
    exact ⟨B, hB, rfl⟩
  · rintro ⟨B, hB, rfl⟩
    exact ⟨B, hB, rfl⟩

theorem gammaW_two_eq (hSL : commutator (SpecialLinearGroup (Fin 2) K) = ⊤)
    (hf : IsCoord (linModelNat (StatedSL 3 K)) H Z π f) (g : SpecialLinearGroup (Fin 3) K) :
    gammaW H (hf.pre (gmap g (flagSpace 3 K 2)).toAddSubgroup) =
      (stabRow2 K).map (psiW π g) := by
  ext x
  rw [gammaW, mem_perfectCore_HU2_iff hSL hf g x]
  constructor
  · rintro ⟨B, hB, rfl⟩
    exact ⟨B, hB, rfl⟩
  · rintro ⟨B, hB, rfl⟩
    exact ⟨B, hB, rfl⟩

end C11P9A

open C11P9A in
theorem factCartanSL3_holds : FactCartanSL3 := by
  intro K _ _ n hn hK W _ _ hW H Z π hπ P hP U₁ U₂ hU₁ hU₂ D hD
  have : CharP K 2 := charP_two_of_card (by omega) hK
  have hSL := commutator_SL2_eq_top (four_le_card hn hK)
  obtain ⟨f, hf⟩ := exists_isCoord (linModelNat _) hπ
  obtain ⟨g, hg⟩ := exists_sylow_eq_conj_Usl hK (by omega) hf hP
  rw [eq_map_psiW_of_sylow hg, inf_normalizer_eq hf g] at hD
  obtain ⟨x, hx, hDx⟩ := exists_eq_map_torus3 hf g hD
  have hg' := sylow_conj_mul hg hx
  have hU1 := eq_U1_of_isFlagW hW hf hg' (by rw [hK]; exact hU₁)
  have hU2 := eq_U2_of_isFlagW hW hf hg' (by rw [hK]; exact hU₂)
  subst hU1 hU2
  have : Finite (MulAut W) := Finite.of_injective _ MulEquiv.toEquiv_injective
  have hψ := psiW_injective hf (g * x)
  have hO1 : pCoreOf 2 (gammaW H (hf.pre (gmap (g * x) (flagSpace 3 K 1)).toAddSubgroup)) =
      (rad1 K).map (psiW π (g * x)) := by
    rw [gammaW_one_eq hSL hf, pCoreOf_map_of_injective _ hψ, pCoreOf_stabE0]
  have hO2 : pCoreOf 2 (gammaW H (hf.pre (gmap (g * x) (flagSpace 3 K 2)).toAddSubgroup)) =
      (rad2 K).map (psiW π (g * x)) := by
    rw [gammaW_two_eq hSL hf, pCoreOf_map_of_injective _ hψ, pCoreOf_stabRow2]
  have hcard : Nat.card Kˣ = 2 ^ n - 1 := by rw [Nat.card_units, hK]
  unfold CartanConcl centW
  rw [hO1, hO2, gammaW_one_eq hSL hf, gammaW_two_eq hSL hf, hDx,
    map_inf_sectionCentralizer _ hψ, map_inf_sectionCentralizer _ hψ,
    ← Subgroup.map_inf_eq _ _ _ hψ, ← Subgroup.map_inf_eq _ _ _ hψ,
    map_inf_sectionCentralizer _ hψ, Subgroup.card_map_of_injective hψ,
    Subgroup.card_map_of_injective hψ, Subgroup.card_map_of_injective hψ,
    Subgroup.card_map_of_injective hψ, card_torus3_inf_stabE0, card_torus3_inf_sc1,
    card_torus3_inf_stabRow2, card_torus3_inf_sc2, torus3_inf_inf_sc2, Subgroup.map_bot,
    ← Subgroup.map_sup, ← Subgroup.map_sup, hcard]
  exact ⟨Subgroup.map_mono torus3_le_sc1_sup, Subgroup.map_mono torus3_le_sup, rfl, rfl, rfl,
    rfl, rfl⟩

end CFSG.Quasithin.Vol2.Ch11.SecS
