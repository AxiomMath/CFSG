module

public import CFSG.RankThree.PartOne.SEITZRF.Defs
import CFSG.SignalizerFunctorTheorem.CatalogBridge.LargeReeFixed
public import CFSG.LieType.Ree.LargeReeInvolutionTwoCentralizers

public noncomputable section

namespace CFSG.RankThree.PartOne.SEITZRF

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution

section BaseChange

variable {K : Type} [Field K] {a : ℕ}

theorem baseChangeGL_centralZ_one {k : Type} [Field k] (ι : k →+* K) (b : ℕ) :
    baseChangeGL ι (centralZ k b 1) = centralZ K a 1 := by
  simp only [centralZ, map_mul, baseChangeGL_pinnedX, map_one, one_pow]

theorem baseChangeGL_sylowL_one {k : Type} [Field k] (ι : k →+* K) (b : ℕ) :
    baseChangeGL ι (sylowL b k 1) = sylowL a K 1 := by
  simp only [sylowL, sylowX, largeReeSigma, map_mul, baseChangeGL_pinnedX, map_one, one_pow]

end BaseChange

section Coordinates

variable {K : Type} [Field K] {a : ℕ}

private theorem centralZ_one_eq_sylowVec :
    centralZ K a 1 = sylowVec a K (Pi.single 8 1) := by
  rw [← sylowH_zero_eq_centralZ]
  simp [sylowVec, sylowV, sylowA, sylowB, sylowD, sylowF, sylowJ, sylowK, sylowL, sylowX,
    largeReeSigma_zero, pinnedX_zero]

private theorem sylowL_one_eq_sylowVec :
    sylowL a K 1 = sylowVec a K (Pi.single 11 1) := by
  simp [sylowVec, sylowV, sylowA, sylowB, sylowD, sylowF, sylowH, sylowJ, sylowK, sylowX,
    largeReeSigma_zero, pinnedX_zero]

private theorem sylowVec_zero_eq_one : sylowVec a K 0 = 1 := by
  simp [sylowVec, sylowV, sylowA, sylowB, sylowD, sylowF, sylowH, sylowJ, sylowK, sylowL, sylowX,
    largeReeSigma_zero, pinnedX_zero]

end Coordinates

section Elements

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem centralZ_one_mem_Rf (hK : Nat.card K = 2 ^ (2 * a + 1)) (β : K ≃+* K) :
    centralZ K a 1 ∈ Rf K a β := by
  rw [centralZ_one_eq_sylowVec, sylowVec_mem_Rf_iff hK]
  intro i
  by_cases hi : i = 8
  · subst hi
    simp
  · simp [hi]

theorem sylowL_one_mem_Rf (hK : Nat.card K = 2 ^ (2 * a + 1)) (β : K ≃+* K) :
    sylowL a K 1 ∈ Rf K a β := by
  rw [sylowL_one_eq_sylowVec, sylowVec_mem_Rf_iff hK]
  intro i
  by_cases hi : i = 11
  · subst hi
    simp
  · simp [hi]

theorem sylowL_one_ne_one (hK : Nat.card K = 2 ^ (2 * a + 1)) : sylowL a K 1 ≠ 1 := by
  intro h
  have h1 : sylowVec a K (Pi.single 11 1) = sylowVec a K 0 := by
    rw [← sylowL_one_eq_sylowVec, h, sylowVec_zero_eq_one]
  have h2 := congrFun ((bijOn_sylowVec hK).injOn (Set.mem_univ _) (Set.mem_univ _) h1) 11
  simp at h2

omit [Finite K] [CharP K F4.prime] in
theorem centralZ_one_ne_one : centralZ K a 1 ≠ 1 := fun h =>
  one_ne_zero (centralZ_injective (h.trans centralZ_zero.symm))

omit [Finite K] in
theorem centralZ_one_sq : centralZ K a 1 ^ 2 = 1 := by
  have e : centralZ K a 1 = sylowV a K 0 0 0 0 0 0 0 0 1 0 0 0 := by
    rw [← sylowH_zero_eq_centralZ]
    simp [sylowV, sylowA, sylowB, sylowD, sylowF, sylowJ, sylowK, sylowL, sylowX,
      largeReeSigma_zero, pinnedX_zero]
  rw [e]
  exact (sylowV_zero_zero_sq_eq_one_iff (m := a) (K := K) 0 0 0 0 0 0 1 0 0 0).2
    ⟨rfl, rfl, rfl, rfl, zero_mul _⟩

omit [Finite K] in
theorem sylowL_one_sq : sylowL a K 1 ^ 2 = 1 := by
  have e : sylowL a K 1 = sylowV a K 0 0 0 0 0 0 0 0 0 0 0 1 := by
    simp [sylowV, sylowA, sylowB, sylowD, sylowF, sylowH, sylowJ, sylowK, sylowX,
      largeReeSigma_zero, pinnedX_zero]
  rw [e]
  exact (sylowV_zero_zero_sq_eq_one_iff (m := a) (K := K) 0 0 0 0 0 0 0 0 0 1).2
    ⟨rfl, rfl, rfl, rfl, zero_mul _⟩

theorem centralZ_one_not_conj_sylowL (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ∀ g ∈ F4.reeGamma K a, g * centralZ K a 1 * g⁻¹ ≠ sylowL a K 1 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hne⟩ :=
    large_Ree_two_involution_centralizers a ha K hK
  exact hne

theorem exists_conj_of_involution_Rf_odd (hK : Nat.card K = 2 ^ (2 * a + 1))
    (β : K ≃+* K) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hβ : orderOf β = p)
    (hk : Nat.card (CFSG.LieType.Chevalley.fixSubfield β) ≠ 2)
    {x : ModGL F4.tag K} (hx : x ∈ Rf K a β) (hx2 : x ^ 2 = 1) (hx1 : x ≠ 1) :
    ∃ r ∈ Rf K a β, r * x * r⁻¹ = centralZ K a 1 ∨ r * x * r⁻¹ = sylowL a K 1 := by
  obtain ⟨b, -, hbcard, hfix⟩ :=
    CFSG.SignalizerFunctorTheorem.CatalogBridge.largeRee_fixed_data_odd hK hp hp2 β hβ
  have hb : 1 ≤ b := by
    rcases Nat.eq_zero_or_pos b with h | h
    · exact absurd (by rw [hbcard, h]; rfl) hk
    · exact h
  have hmem : ∀ y ∈ Rf K a β, ∃ y' ∈ F4.reeGamma (fixSubfield β) b,
      baseChangeGL (fixSubfield β).subtype y' = y := by
    intro y hy
    have h1 : y ∈ (CFSG.RankThree.PartOne.CTP.fixedSubgroup
        (F4.reeGammaFieldAut K a β)).map (F4.reeGamma K a).subtype := by
      rw [map_fixedSubgroup_eq_Rf]
      exact hy
    have h2 : y ∈ ((F4.reeGammaFieldAut K a β).toMonoidHom.eqLocus (MonoidHom.id _)).map
        (F4.reeGamma K a).subtype := h1
    rw [hfix] at h2
    obtain ⟨y', hy', rfl⟩ := h2
    exact ⟨y', hy', rfl⟩
  have hmem' : ∀ y' ∈ F4.reeGamma (fixSubfield β) b,
      baseChangeGL (fixSubfield β).subtype y' ∈ Rf K a β := by
    intro y' hy'
    have h2 : baseChangeGL (fixSubfield β).subtype y' ∈
        (F4.reeGamma (fixSubfield β) b).map (baseChangeGL (fixSubfield β).subtype) :=
      ⟨y', hy', rfl⟩
    rw [← hfix] at h2
    rw [← map_fixedSubgroup_eq_Rf]
    exact h2
  obtain ⟨x', hx', rfl⟩ := hmem x hx
  have hx'2 : x' ^ 2 = 1 := by
    apply baseChangeGL_injective (fixSubfield β).subtype
    rw [map_pow, map_one]
    exact hx2
  have hx'1 : x' ≠ 1 := by
    rintro rfl
    exact hx1 (map_one _)
  obtain ⟨hfus, -⟩ := large_Ree_every_involution_fuses b hb (fixSubfield β) hbcard
  rcases hfus x' hx' hx'2 hx'1 with ⟨y, hy, hyx⟩ | ⟨y, hy, hyx⟩
  · refine ⟨baseChangeGL (fixSubfield β).subtype y, hmem' y hy, Or.inl ?_⟩
    rw [sylowH_zero_eq_centralZ] at hyx
    have h := congrArg (baseChangeGL (fixSubfield β).subtype) hyx
    rwa [map_mul, map_mul, map_inv, baseChangeGL_centralZ_one] at h
  · refine ⟨baseChangeGL (fixSubfield β).subtype y, hmem' y hy, Or.inr ?_⟩
    have h := congrArg (baseChangeGL (fixSubfield β).subtype) hyx
    rwa [map_mul, map_mul, map_inv, baseChangeGL_sylowL_one] at h

end Elements

end CFSG.RankThree.PartOne.SEITZRF
