module

public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5Lift
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5Torus
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5Cover

public section

namespace CFSG.StandardType.NbrU63

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.SectionRank.OddCover CFSG.RankThree.Classical2 CFSG.RankThree.Classical
  CFSG.StandardType.TableBU CFSG.Assembly CFSG.StandardType CFSG.StandardType.Line63.H5

variable {F : Type} [Field F] {n : ℕ}

theorem projMk_swapSU_six_ne_one (hKd : UnitaryFieldData 2 n F) (hpq : 3 ∣ 2 ^ n + 1) :
    LargeEvenProjMk (unitarySU 2 n F 6) (swapSU hKd) ≠ 1 := by
  haveI : Finite F := hKd.finite
  intro h
  obtain ⟨z, -, hz⟩ := exists_scalar_of_proj_eq_one hKd hpq h
  obtain ⟨ζ, hζo, -⟩ := exists_orderOf_eq_norm_one hKd Nat.prime_three hpq
  have hζ1 : ζ ≠ 1 := by
    rintro rfl
    simp at hζo
  apply permGL_swap_not_mem_center (K := F) (d := 6) (i := 0) (j := 1)
    (by simp [Fin.ext_iff]) hζ1
  have hw : (permGL (Equiv.swap (0 : Fin 6) 1) : GL (Fin 6) F) =
      GeneralLinearGroup.scalar (Fin 6) z := hz
  rw [hw, Subgroup.mem_center_iff]
  intro g
  exact (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar z g).eq

theorem commute_swapSU_of_mem_torus (hKd : UnitaryFieldData 2 n F)
    {E₀ : Subgroup ↥(unitarySU 2 n F 6)}
    (hE₀diag : ∀ e ∈ E₀, ∃ t : Fin 6 → Fˣ, (e : GL (Fin 6) F) = diagHom 6 t ∧ t 0 = t 1 ∧
      ∀ i, t i ^ 3 = 1) {s : ↥(unitarySU 2 n F 6)} (hs : s ∈ E₀) :
    Commute s (swapSU hKd) := by
  haveI : Finite F := hKd.finite
  obtain ⟨t, hst, ht01, -⟩ := hE₀diag s hs
  apply Subtype.ext
  show (s : GL (Fin 6) F) * permGL (Equiv.swap (0 : Fin 6) 1) =
    permGL (Equiv.swap (0 : Fin 6) 1) * (s : GL (Fin 6) F)
  rw [hst]
  exact (swap_commute_diagHom ht01).eq.symm

private theorem zpowers_ne_bot_isPGroup_two {P : Type*} [Group P] {g : P} (hg1 : g ≠ 1)
    (hg2 : g ^ 2 = 1) : Subgroup.zpowers g ≠ ⊥ ∧ IsPGroup 2 (Subgroup.zpowers g) := by
  refine ⟨by rw [Ne, Subgroup.zpowers_eq_bot]; exact hg1, ?_⟩
  refine IsPGroup.of_card_dvd_pow (n := 1) ?_
  rw [Nat.card_zpowers]
  exact orderOf_dvd_of_pow_eq_one (by simpa using hg2)

private theorem mem_normalizer_zpowers_of_commute {P : Type*} [Group P] {g h : P}
    (hgh : Commute h g) :
    h ∈ Subgroup.normalizer (Subgroup.zpowers g : Set P) := by
  refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun u hu => ?_)
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
  exact (hgh.zpow_right k).eq.symm

theorem exists_twoLocal_four_of_injective (hKd : UnitaryFieldData 2 n F) (hpq : 3 ∣ 2 ^ n + 1)
    {K P : Type*} [Group K] [Finite K] [Group P] (ψ : K →* P) (h2 : IsPGroup 2 ψ.ker)
    (φ : ↥(unitarySU 2 n F 6) →* P) (hφ : Function.Injective φ) (hφr : ∀ s, φ s ∈ ψ.range) :
    ∃ U E : Subgroup K, U ≠ ⊥ ∧ IsPGroup 2 U ∧ E ≤ Subgroup.normalizer (U : Set K) ∧
      CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4 := by
  haveI : Finite F := hKd.finite
  classical
  obtain ⟨E₀, hE₀ab, hE₀card, hE₀diag⟩ := exists_torusFour hKd hpq
  have hw1 : φ (swapSU hKd) ≠ 1 := by
    intro h
    apply projMk_swapSU_six_ne_one hKd hpq
    rw [hφ (h.trans (map_one φ).symm), map_one]
  have hww : (φ (swapSU hKd)) ^ 2 = 1 := by rw [← map_pow, swapSU_sq, map_one]
  obtain ⟨hU₀1, hU₀2⟩ := zpowers_ne_bot_isPGroup_two hw1 hww
  have hU₀r : Subgroup.zpowers (φ (swapSU hKd)) ≤ ψ.range :=
    (Subgroup.zpowers_le).mpr (hφr _)
  have hE₁ab : CFSG.Open.IsElemAbelian 3 (E₀.map φ) :=
    CFSG.StandardType.TableB.isElemAbelian_map hE₀ab φ
  have hE₁r : E₀.map φ ≤ ψ.range := by
    rintro _ ⟨s, -, rfl⟩
    exact hφr s
  have hE₁U : E₀.map φ ≤ Subgroup.normalizer
      (Subgroup.zpowers (φ (swapSU hKd)) : Set P) := by
    rintro _ ⟨s, hs, rfl⟩
    exact mem_normalizer_zpowers_of_commute ((commute_swapSU_of_mem_torus hKd hE₀diag hs).map φ)
  obtain ⟨U, E, hU, hU2, hEU, hE, hcard⟩ :=
    exists_lift_of_ker_two ψ h2 hE₁ab hE₁r hU₀2 hU₀r hU₀1 hE₁U
  refine ⟨U, E, hU, hU2, hEU, hE, ?_⟩
  rw [hcard, ← Nat.card_congr (E₀.equivMapOfInjective φ hφ).toEquiv, hE₀card]

theorem exists_twoLocal_three_of_quot (hKd : UnitaryFieldData 2 n F) (hpq : 3 ∣ 2 ^ n + 1)
    {K : Type*} [Group K] [Finite K] (ψ : K →* LargeEvenProj (unitarySU 2 n F 6))
    (hψ : Function.Surjective ψ) (h2 : IsPGroup 2 ψ.ker) :
    ∃ U E : Subgroup K, U ≠ ⊥ ∧ IsPGroup 2 U ∧ E ≤ Subgroup.normalizer (U : Set K) ∧
      CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 3 := by
  haveI : Finite F := hKd.finite
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨E₀, hE₀ab, hE₀card, hE₀diag⟩ := exists_torusFour hKd hpq
  set π := LargeEvenProjMk (unitarySU 2 n F 6) with hπ
  have hw1 : π (swapSU hKd) ≠ 1 := projMk_swapSU_six_ne_one hKd hpq
  have hww : (π (swapSU hKd)) ^ 2 = 1 := by rw [← map_pow, swapSU_sq, map_one]
  obtain ⟨hU₀1, hU₀2⟩ := zpowers_ne_bot_isPGroup_two hw1 hww
  set Φ : ↥E₀ →* LargeEvenProj (unitarySU 2 n F 6) := π.comp E₀.subtype with hΦ
  have hker : Nat.card Φ.ker ≤ 3 := by
    have hex : ∀ e : Φ.ker, ∃ z : rootsOfUnity 3 F,
        (((e : ↥E₀) : ↥(unitarySU 2 n F 6)) : GL (Fin 6) F) =
          GeneralLinearGroup.scalar (Fin 6) (z : Fˣ) := by
      intro e
      obtain ⟨z, hz3, hz⟩ := exists_scalar_of_proj_eq_one hKd hpq (e.2 : Φ ((e : ↥E₀)) = 1)
      exact ⟨⟨z, (mem_rootsOfUnity _ _).mpr hz3⟩, hz⟩
    choose f hf using hex
    have hfinj : Function.Injective f := by
      intro e e' h
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      rw [hf e, hf e', h]
    exact (Nat.card_le_card_of_injective f hfinj).trans (card_rootsOfUnity F 3)
  have hcardΦ := CFSG.StandardType.TableB.card_range_mul_card_ker Φ
  rw [hE₀card] at hcardΦ
  have hrange : 3 ^ 3 ≤ Nat.card Φ.range := by
    have h1 : Nat.card Φ.range * Nat.card Φ.ker ≤ Nat.card Φ.range * 3 :=
      Nat.mul_le_mul_left _ hker
    rw [hcardΦ] at h1
    omega
  have hE₀c : ∀ a b : ↥E₀, a * b = b * a := fun a b =>
    Subtype.ext (CFSG.StandardType.TableB.IsElemAbelian.comm hE₀ab a.2 b.2)
  have hE₀3 : ∀ a : ↥E₀, a ^ 3 = 1 := fun a => Subtype.ext (by simpa using hE₀ab.2 a a.2)
  have hΦab : CFSG.Open.IsElemAbelian 3 Φ.range := isElemAbelian_range hE₀c hE₀3 Φ
  have hΦp : IsPGroup 3 Φ.range := fun g => ⟨1, Subtype.ext (by simpa using hΦab.2 g g.2)⟩
  obtain ⟨Q, hQ⟩ := Sylow.exists_subgroup_card_pow_prime_of_le_card Nat.prime_three hΦp hrange
  set E₂ : Subgroup (LargeEvenProj (unitarySU 2 n F 6)) := Q.map Φ.range.subtype with hE₂
  have hE₂Φ : E₂ ≤ Φ.range := Subgroup.map_subtype_le Q
  have hE₂ab : CFSG.Open.IsElemAbelian 3 E₂ :=
    CFSG.StandardType.TableB.isElemAbelian_mono hΦab hE₂Φ
  have hE₂U : E₂ ≤ Subgroup.normalizer (Subgroup.zpowers (π (swapSU hKd)) : Set _) := by
    intro r hr
    obtain ⟨e, rfl⟩ := hE₂Φ hr
    exact mem_normalizer_zpowers_of_commute
      ((commute_swapSU_of_mem_torus hKd hE₀diag e.2).map π)
  obtain ⟨U, E, hU, hU2, hEU, hE, hcard⟩ :=
    exists_lift_of_ker_two ψ h2 hE₂ab (fun r _ => hψ r) hU₀2 (fun r _ => hψ r) hU₀1 hE₂U
  refine ⟨U, E, hU, hU2, hEU, hE, ?_⟩
  rw [hcard, hE₂, ← Nat.card_congr (Q.equivMapOfInjective _ Φ.range.subtype_injective).toEquiv,
    hQ]

end CFSG.StandardType.NbrU63

end
