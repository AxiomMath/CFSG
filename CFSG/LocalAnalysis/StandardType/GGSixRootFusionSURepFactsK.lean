module

public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionSURepFactsRad
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionSURepFactsBasic
public import CFSG.LieType.Steinberg.CentralExt.UnitaryField

public section

namespace CFSG.StandardType

namespace SUFacts

open CFSG.LieType.Universal.Unitary
open CFSG.LieType.BorelTits (unitaryInvolution)

section KSide

variable {F : Type} [Field F] [Finite F] [CharP F 2] {a : ℕ} {G : Type} [Group G]
  {ψ : SU (unitaryInvolution F 2 a) 6 →* G}

theorem ggCentOTwoPrime_one_le_map_centralizer_SU
    (hker : ψ.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 a) 6)) :
    ggCentOTwoPrime ψ.range (ψ (ggInvSU (unitaryInvolution F 2 a) 6 1)) ≤
      (Subgroup.centralizer {ggInvSU (unitaryInvolution F 2 a) 6 1}).map ψ := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro y ⟨⟨g, rfl⟩, hys, -⟩
  exact ⟨g, Subgroup.mem_centralizer_singleton_iff.mpr
    (commute_of_map_commute_SU hker (ggInvSU_mul_self_of_le (by norm_num)) hys), rfl⟩

theorem map_rootRad_le_ggCentOTwoPrime :
    (rootRad (unitaryInvolution F 2 a)).map ψ ≤
      ggCentOTwoPrime ψ.range (ψ (ggInvSU (unitaryInvolution F 2 a) 6 1)) := by
  rintro _ ⟨r, hr, rfl⟩
  refine Subgroup.subset_closure ⟨⟨r, rfl⟩, ?_, 2, ?_⟩
  · rw [← map_mul, ← map_mul, commute_ggInvSU_of_mem_rootRad hr]
  · rw [← map_pow, show 2 ^ 2 = 4 by norm_num, pow_four_eq_one_of_mem_rootRad hr, map_one]

theorem conj_mem_map_rootRad (hker : ψ.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 a) 6))
    {k x : G} (hk : k ∈ ggCentOTwoPrime ψ.range (ψ (ggInvSU (unitaryInvolution F 2 a) 6 1)))
    (hx : x ∈ (rootRad (unitaryInvolution F 2 a)).map ψ) :
    k * x * k⁻¹ ∈ (rootRad (unitaryInvolution F 2 a)).map ψ := by
  obtain ⟨c, hc, rfl⟩ := ggCentOTwoPrime_one_le_map_centralizer_SU hker hk
  obtain ⟨r, hr, rfl⟩ := hx
  have hc' : c * ggInvSU (unitaryInvolution F 2 a) 6 1 = ggInvSU (unitaryInvolution F 2 a) 6 1 * c :=
    Subgroup.mem_centralizer_singleton_iff.mp hc
  exact ⟨c * r * c⁻¹, conj_mem_rootRad hc' hr, by simp only [map_mul, map_inv]⟩

theorem card_le_of_abelian_map_rootRad (hF : Nat.card F = (2 ^ a) ^ 2)
    (hker : ψ.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 a) 6)) {A : Subgroup G}
    (hA : A ≤ (rootRad (unitaryInvolution F 2 a)).map ψ)
    (hc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) : Nat.card A ≤ 2 ^ (5 * a) := by
  set At : Subgroup (SU (unitaryInvolution F 2 a) 6) :=
    A.comap ψ ⊓ rootRad (unitaryInvolution F 2 a) with hAt
  have hmap : At.map ψ = A := by
    apply le_antisymm
    · rintro _ ⟨r, hr, rfl⟩
      exact hr.1
    · intro x hx
      obtain ⟨r, hr, rfl⟩ := hA hx
      exact ⟨r, ⟨hx, hr⟩, rfl⟩
  have hR2 := isPGroup_rootRad (unitaryInvolution F 2 a)
  have hAtc : ∀ x ∈ At, ∀ y ∈ At, x * y = y * x := fun x hx y hy =>
    eq_of_map_eq_of_isPGroup_SU hker hR2 (mul_mem hx.2 hy.2) (mul_mem hy.2 hx.2)
      (by rw [map_mul, map_mul, hc _ hx.1 _ hy.1])
  have hcard : Nat.card A = Nat.card At := by
    rw [← hmap]
    exact card_map_of_isPGroup_SU hker (hR2.to_le inf_le_right)
  rw [hcard]
  have hσu := CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution hF
  obtain ⟨θ, hθ⟩ := hσu.exists_ne
  have h := card_le_of_abelian_rootRad hσu.invol hθ hF (CFSG.LieType.Steinberg.card_traceZero hF)
    inf_le_right hAtc
  rwa [← pow_mul, mul_comm a 5] at h

theorem exists_normal_twoGroup_ggCentOTwoPrime_one [Finite G] (ha : 1 ≤ a)
    (hF : Nat.card F = (2 ^ a) ^ 2)
    (hker : ψ.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 a) 6)) :
    ∃ Q : Subgroup ↥(ggCentOTwoPrime ψ.range (ψ (ggInvSU (unitaryInvolution F 2 a) 6 1))),
      Q.Normal ∧ IsPGroup 2 Q ∧
      (∀ A : Subgroup ↥(ggCentOTwoPrime ψ.range (ψ (ggInvSU (unitaryInvolution F 2 a) 6 1))),
        A ≤ Q → (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) → Nat.card A ≤ 2 ^ (5 * a)) ∧
      ordProj[2] (Nat.card (↥(ggCentOTwoPrime ψ.range
        (ψ (ggInvSU (unitaryInvolution F 2 a) 6 1))) ⧸ Q)) ≤ 2 ^ (6 * a) := by
  set K := ggCentOTwoPrime ψ.range (ψ (ggInvSU (unitaryInvolution F 2 a) 6 1)) with hK
  set R := (rootRad (unitaryInvolution F 2 a)).map ψ with hR
  have hRK : R ≤ K := map_rootRad_le_ggCentOTwoPrime
  set Q : Subgroup K := R.subgroupOf K with hQ
  have hQn : Q.Normal := ⟨fun n hn k => by
    rw [hQ, Subgroup.mem_subgroupOf] at hn ⊢
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    exact conj_mem_map_rootRad hker k.2 hn⟩
  have hR2 : IsPGroup 2 R := (isPGroup_rootRad (unitaryInvolution F 2 a)).map ψ
  have hQ2 : IsPGroup 2 Q := hR2.comap_of_injective K.subtype K.subtype_injective
  refine ⟨Q, hQn, hQ2, fun A hAQ hAc => ?_, ?_⟩
  · have h := card_le_of_abelian_map_rootRad hF hker (A := A.map K.subtype)
      (by rintro _ ⟨x, hx, rfl⟩; exact hAQ hx)
      (by
        rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
        rw [← map_mul, ← map_mul, hAc x hx y hy])
    rwa [Subgroup.card_map_of_injective K.subtype_injective] at h
  · have hKr : K ≤ ψ.range := (Subgroup.closure_le _).mpr fun y hy => hy.1
    have : Finite K := finite_of_le_range_SU hKr
    have : Finite ψ.range := Finite.of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective
    have hKq : ordProj[2] (Nat.card K) ≤ 2 ^ (15 * a) := by
      have hdvd : Nat.card K ∣ Nat.card ψ.range := Subgroup.card_dvd_of_le hKr
      have h0 : Nat.card ψ.range ≠ 0 := Nat.card_pos.ne'
      have h1 := Nat.ordProj_dvd_ordProj_of_dvd h0 hdvd 2
      have h2 : ordProj[2] (Nat.card ψ.range) = 2 ^ (15 * a) := by
        rw [MonoidHom.range_eq_map, ordProj_two_card_map_SU hker ⊤, Subgroup.card_top,
          ordProj_two_card_SU_six ha hF]
      rw [h2] at h1
      exact Nat.le_of_dvd (by positivity) h1
    have hQcard : 2 ^ (9 * a) ≤ Nat.card Q := by
      rw [hQ, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRK).toEquiv, hR,
        card_map_of_isPGroup_SU hker (isPGroup_rootRad _)]
      have h := card_rootRad_ge (σ := unitaryInvolution F 2 a)
        (CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution hF).invol
      rw [hF, CFSG.LieType.Steinberg.card_traceZero hF] at h
      calc 2 ^ (9 * a) = ((2 ^ a) ^ 2) ^ 4 * 2 ^ a := by rw [← pow_mul, ← pow_mul, ← pow_add]; ring_nf
        _ ≤ _ := h
    have hsplit := Subgroup.card_eq_card_quotient_mul_card_subgroup Q
    have hKQ0 : Nat.card (K ⧸ Q) ≠ 0 := Nat.card_pos.ne'
    have hQ0 : Nat.card Q ≠ 0 := Nat.card_pos.ne'
    have hmul : ordProj[2] (Nat.card K) = ordProj[2] (Nat.card (K ⧸ Q)) * Nat.card Q := by
      rw [hsplit, Nat.ordProj_mul 2 hKQ0 hQ0, SLAlpha.ordProj_two_card_of_isPGroup hQ2]
    have h1 : ordProj[2] (Nat.card (K ⧸ Q)) * 2 ^ (9 * a) ≤ 2 ^ (6 * a) * 2 ^ (9 * a) := by
      calc ordProj[2] (Nat.card (K ⧸ Q)) * 2 ^ (9 * a)
          ≤ ordProj[2] (Nat.card (K ⧸ Q)) * Nat.card Q := Nat.mul_le_mul_left _ hQcard
        _ = ordProj[2] (Nat.card K) := hmul.symm
        _ ≤ 2 ^ (15 * a) := hKq
        _ = 2 ^ (6 * a) * 2 ^ (9 * a) := by rw [← pow_add]; congr 1; ring
    exact Nat.le_of_mul_le_mul_right h1 (by positivity)

end KSide

theorem ggSUSixKSideInput_holds : GGSUSixKSideInput := by
  intro G _ _ f ψ hker
  exact exists_normal_twoGroup_ggCentOTwoPrime_one (F := GaloisField 2 (2 * (f + 1))) (by omega)
    (CFSG.LieType.Universal.card_galoisField_two_mul 2 (f + 1) (by omega)) hker

end SUFacts

end CFSG.StandardType
