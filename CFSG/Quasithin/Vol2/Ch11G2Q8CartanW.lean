module

public import CFSG.Quasithin.Vol2.Ch11G2Q8Cartan
public import CFSG.Quasithin.Vol2.Ch11G2Q8LeviG2
public import CFSG.Quasithin.Vol2.Ch11SecQ9aCartE
public import CFSG.Quasithin.Vol2.Ch11SecQ9aCartA
public import CFSG.Quasithin.Vol2.Ch11SecSFactsCartan

public section

namespace CFSG.Quasithin.Vol2.Ch11.G2Q8

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
  CFSG.Quasithin.Vol2.KGNat Matrix
open CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A (map_inf_sectionCentralizer pCoreOf_map_of_injective
  map_mem_normalizer_iff)

variable {K : Type} [Field K] [CharP K 2]

section Real

variable {W : Type*} [CommGroup W] {H : Subgroup (MulAut W)} {Z : Subgroup W}
  {π : ↥⁅quasithinG2 K, quasithinG2 K⁆ →* ↥H} {f : W → (Ix3 → K)}

theorem psiG_mul {c₀ : K} (hc0 : c₀ ≠ 0) (hc1 : c₀ ≠ 1) (g x : ↥(cayleyGroup K)) :
    psiG hc0 hc1 π (g * x) = (psiG hc0 hc1 π g).comp (MulAut.conj x).toMonoidHom := by
  ext A
  rw [MonoidHom.comp_apply, psiG_apply, psiG_apply]
  congr 3

theorem exists_psiG_eq (hf : IsCoord (lmG K) H Z π f) {c₀ : K} (hc0 : c₀ ≠ 0) (hc1 : c₀ ≠ 1)
    (g : ↥(cayleyGroup K)) {x : MulAut W} (hx : x ∈ H) : ∃ A, psiG hc0 hc1 π g A = x := by
  obtain ⟨B, hB⟩ := (rhoG_bijective hf hc0 hc1).2 ⟨x, hx⟩
  exact ⟨g⁻¹ * B * g, by rw [psiG_apply, show g * (g⁻¹ * B * g) * g⁻¹ = B by group, hB]⟩

theorem eq_map_psiG_of_sylow {c₀ : K} {hc0 : c₀ ≠ 0} {hc1 : c₀ ≠ 1} {P : Subgroup (MulAut W)}
    {g : ↥(cayleyGroup K)}
    (hg : ∀ x : MulAut W,
      x ∈ P ↔ ∃ u ∈ U0 K, x = ((rhoG hc0 hc1 π (g * u * g⁻¹) : ↥H) : MulAut W)) :
    P = (U0 K).map (psiG hc0 hc1 π g) := by
  ext x
  rw [hg]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, hu, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, hu, rfl⟩

theorem inf_normalizer_eqG (hf : IsCoord (lmG K) H Z π f) {c₀ : K} (hc0 : c₀ ≠ 0) (hc1 : c₀ ≠ 1)
    (g : ↥(cayleyGroup K)) :
    H ⊓ Subgroup.normalizer
        (((U0 K).map (psiG hc0 hc1 π g) : Subgroup (MulAut W)) : Set (MulAut W)) =
      (Subgroup.normalizer (U0 K : Set ↥(cayleyGroup K))).map (psiG hc0 hc1 π g) := by
  have hψ := psiG_injective hf hc0 hc1 g
  ext x
  constructor
  · rintro ⟨hxH, hxN⟩
    obtain ⟨A, rfl⟩ := exists_psiG_eq hf hc0 hc1 g hxH
    exact ⟨A, (map_mem_normalizer_iff _ hψ).mp hxN, rfl⟩
  · rintro ⟨B, hB, rfl⟩
    exact ⟨(rhoG hc0 hc1 π _).2, (map_mem_normalizer_iff _ hψ).mpr hB⟩

theorem exists_eq_map_torusG [Finite K] (hf : IsCoord (lmG K) H Z π f) {c₀ : K} (hc0 : c₀ ≠ 0)
    (hc1 : c₀ ≠ 1) {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 1 ≤ n) (g : ↥(cayleyGroup K))
    {D : Subgroup (MulAut W)}
    (hD : CFSG.QuasithinUnique.Lin2.IsHallTwoPrimeOf D
      ((Subgroup.normalizer (U0 K : Set ↥(cayleyGroup K))).map (psiG hc0 hc1 π g))) :
    ∃ x ∈ U0 K, D = (torusG K).map (psiG hc0 hc1 π (g * x)) := by
  have hψ := psiG_injective hf hc0 hc1 g
  obtain ⟨hDle, hDodd, k, hk⟩ := hD
  have hDeq : (D.comap (psiG hc0 hc1 π g)).map (psiG hc0 hc1 π g) = D :=
    Subgroup.map_comap_eq_self (hDle.trans (Subgroup.map_le_range _ _))
  have hD0 : CFSG.QuasithinUnique.Lin2.IsHallTwoPrimeOf (D.comap (psiG hc0 hc1 π g))
      (Subgroup.normalizer (U0 K : Set ↥(cayleyGroup K))) := by
    refine ⟨?_, ?_, k, ?_⟩
    · have := Subgroup.comap_mono (f := psiG hc0 hc1 π g) hDle
      rwa [Subgroup.comap_map_eq_self_of_injective hψ] at this
    · rw [← Subgroup.card_map_of_injective hψ, hDeq]
      exact hDodd
    · rw [← Subgroup.relIndex_map_map_of_injective _ _ hψ, hDeq]
      exact hk
  obtain ⟨x, hx, hxD⟩ := exists_conj_torusG_of_isHall hK hn hD0
  refine ⟨x, hx, ?_⟩
  rw [← hDeq, hxD, Subgroup.map_map, psiG_mul]

theorem sylow_conj_mulG {c₀ : K} {hc0 : c₀ ≠ 0} {hc1 : c₀ ≠ 1} {P : Subgroup (MulAut W)}
    {g x : ↥(cayleyGroup K)}
    (hg : ∀ y : MulAut W,
      y ∈ P ↔ ∃ u ∈ U0 K, y = ((rhoG hc0 hc1 π (g * u * g⁻¹) : ↥H) : MulAut W))
    (hx : x ∈ U0 K) :
    ∀ y : MulAut W,
      y ∈ P ↔ ∃ u ∈ U0 K, y = ((rhoG hc0 hc1 π ((g * x) * u * (g * x)⁻¹) : ↥H) : MulAut W) := by
  intro y
  rw [hg]
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨x⁻¹ * u * x, (U0 K).mul_mem ((U0 K).mul_mem ((U0 K).inv_mem hx) hu) hx, ?_⟩
    rw [show g * x * (x⁻¹ * u * x) * (g * x)⁻¹ = g * u * g⁻¹ by group]
  · rintro ⟨u, hu, rfl⟩
    refine ⟨x * u * x⁻¹, (U0 K).mul_mem ((U0 K).mul_mem hx hu) ((U0 K).inv_mem hx), ?_⟩
    rw [show g * (x * u * x⁻¹) * g⁻¹ = g * x * u * (g * x)⁻¹ by group]

theorem eq_U2_of_isFlagWG [Finite K] (hW : ∀ w : W, w ^ 2 = 1) (hf : IsCoord (lmG K) H Z π f)
    {c : K} (hc0 : c ≠ 0) (hc1 : c ≠ 1) {P : Subgroup (MulAut W)} {g : ↥(cayleyGroup K)}
    (hg : ∀ x : MulAut W,
      x ∈ P ↔ ∃ u ∈ U0 K, x = ((rhoG hc0 hc1 π (g * u * g⁻¹) : ↥H) : MulAut W))
    {U : Subgroup W} (hU : Ch11.SecA.IsFlagW H P Z (Nat.card K) 2 U) :
    U = hf.pre (gmapG g (stdF K 2)).toAddSubgroup := by
  obtain ⟨S, hS, hc, rfl⟩ := exists_eq_preG_of_isFlagW hW hf hc0 hc1 hg hU
  rw [eq_stdF_of_card hS hc]

theorem gammaW_one_eqG [Finite K] (h4 : 4 ≤ Nat.card K) (hf : IsCoord (lmG K) H Z π f)
    {c₀ : K} (hc0 : c₀ ≠ 0) (hc1 : c₀ ≠ 1) (g : ↥(cayleyGroup K)) :
    Ch11.SecS.gammaW H (hf.pre (gmapG g (stdF K 1)).toAddSubgroup) =
      (stabV0 K).map (psiG hc0 hc1 π g) := by
  change perfectCore (H ⊓ Ch11.SecA.stabW _) = _
  rw [← map_stabQ_eq hf hc0 hc1 g, perfectCore_map _ (psiG_injective hf hc0 hc1 g),
    perfectCore_stabQ_one h4]

theorem gammaW_two_eqG (hf : IsCoord (lmG K) H Z π f) {c₀ : K} (hc0 : c₀ ≠ 0) (hc1 : c₀ ≠ 1)
    (g : ↥(cayleyGroup K)) :
    Ch11.SecS.gammaW H (hf.pre (gmapG g (stdF K 2)).toAddSubgroup) =
      (perfectCore (stabQ (stdF K 2))).map (psiG hc0 hc1 π g) := by
  change perfectCore (H ⊓ Ch11.SecA.stabW _) = _
  rw [← map_stabQ_eq hf hc0 hc1 g, perfectCore_map _ (psiG_injective hf hc0 hc1 g)]

end Real

theorem factCartanG2_holds : Ch11.SecS.FactCartanG2 := by
  intro K _ _ n hn hK W _ _ hW H Z π hπ P hP U₁ U₂ hU₁ hU₂ D hD
  have : CharP K 2 := KGNat.charP_two_of_card (by omega) hK
  have : Finite (MulAut W) := Finite.of_injective _ MulEquiv.toEquiv_injective
  have := finite_cayleyGroup (F := K)
  have h4 := four_le_card hn hK
  obtain ⟨c₀, hc0, hc1⟩ := exists_ne_zero_ne_one_of_card hn hK
  obtain ⟨f, hf⟩ := exists_isCoord (lmG K) hπ
  obtain ⟨g, hg⟩ := exists_sylow_eq_conj_U0 hK (by omega) hf hc0 hc1 hP
  rw [eq_map_psiG_of_sylow hg, inf_normalizer_eqG hf hc0 hc1 g] at hD
  obtain ⟨x, hx, hDx⟩ := exists_eq_map_torusG hf hc0 hc1 hK (by omega) g hD
  have hg' := sylow_conj_mulG hg hx
  have hU1 := eq_U1_of_isFlagWG hW hf hc0 hc1 hg' (by rw [hK]; exact hU₁)
  have hU2 := eq_U2_of_isFlagWG hW hf hc0 hc1 hg' (by rw [hK]; exact hU₂)
  subst hU1 hU2 hDx
  have hψ := psiG_injective hf hc0 hc1 (g * x)
  have hΓ1 := gammaW_one_eqG h4 hf hc0 hc1 (g * x)
  have hΓ2 := gammaW_two_eqG hf hc0 hc1 (g * x)
  have hO1 : pCoreOf 2 (Ch11.SecS.gammaW H (hf.pre (gmapG (g * x) (stdF K 1)).toAddSubgroup)) =
      (pCoreOf 2 (stabV0 K)).map (psiG hc0 hc1 π (g * x)) := by
    rw [hΓ1, pCoreOf_map_of_injective _ hψ]
  have hO2 : pCoreOf 2 (Ch11.SecS.gammaW H (hf.pre (gmapG (g * x) (stdF K 2)).toAddSubgroup)) =
      (pCoreOf 2 (perfectCore (stabQ (stdF K 2)))).map (psiG hc0 hc1 π (g * x)) := by
    rw [hΓ2, pCoreOf_map_of_injective _ hψ]
  unfold Ch11.SecS.CartanConcl Ch11.SecS.centW
  rw [hO1, hO2, hΓ1, hΓ2, map_inf_sectionCentralizer _ hψ, map_inf_sectionCentralizer _ hψ,
    ← Subgroup.map_inf_eq _ _ _ hψ, ← Subgroup.map_inf_eq _ _ _ hψ,
    map_inf_sectionCentralizer _ hψ, Subgroup.card_map_of_injective hψ,
    Subgroup.card_map_of_injective hψ, Subgroup.card_map_of_injective hψ,
    Subgroup.card_map_of_injective hψ, card_torusG_inf_stabV0, card_torusG_inf_sc1,
    card_torusG_inf_gam2 (by omega), card_torusG_inf_sc2 h4, torusG_inf_inf_sc2 h4,
    Subgroup.map_bot, ← Subgroup.map_sup, ← Subgroup.map_sup, hK]
  exact ⟨⟨Subgroup.map_mono torusG_le_sc1_sup, Subgroup.map_mono (torusG_le_sup12 (by omega)),
    rfl, rfl, rfl, rfl, rfl⟩, fun hn2 => Subgroup.map_mono (torusG_inf_sc1_le_gam2 (by
      rw [hK, hn2]
      norm_num))⟩

end CFSG.Quasithin.Vol2.Ch11.G2Q8
