module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91D4ThreeBCentralizer
import CFSG.GroupTheory.PrimeOrderSubgroups
import CFSG.Quasithin.Background.F918Z4c2Sl
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight56Spine

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.Blueprint.Chevalley (TwistTag)
open CFSG.LieType.Chevalley (graphFixedRootGroup orbitRankOneHom orbitRankOneHomFixed)
open CFSG.LocalAnalysis.UniquenessCase.UC22


private lemma k891inv_is3D4_model {X : Type} [Group X] {n : ℕ} (hX : Is3D4 X n) :
    1 ≤ n ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K) (σ : K ≃+* K),
      Nat.card K = (2 ^ n) ^ 3 ∧ (∀ c, σ c = c ^ 2 ^ n) ∧
        Nonempty (X ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  have hadm := hX.admissible
  rcases hX with ⟨ht, -⟩ | ⟨-, -, hM⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · exact absurd ht (by decide)
  · obtain ⟨K, _, _, σ, hcard, hσ, ⟨e⟩⟩ :=
      CFSG.LieType.Chevalley.exists_mulEquiv_graphFixedRootGroup_card .D4 Nat.prime_two
        hadm.2.1 hM.2
    exact ⟨hadm.2.1, K, inferInstance, inferInstance, σ, hcard, hσ, ⟨e⟩⟩
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)

theorem r891_exists_inv_of_central_sylow {X : Type} [Group X] [Finite X] {n : ℕ}
    (hX : Is3D4 X n) {P : Subgroup X} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P ⊤) {x : X}
    (hxc : ∀ p ∈ P, p * x = x * p) (hx3 : x ^ 3 = 1) :
    ∃ g : X, g * x * g⁻¹ = x⁻¹ := by
  by_cases hx1 : x = 1
  · exact ⟨1, by simp [hx1]⟩
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hn1, K, hKfield, hKfin, σ, hcard, hσ, ⟨e⟩⟩ := k891inv_is3D4_model hX
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (k := n * 3) (by omega) (by rw [hcard, pow_mul])
  let P' : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := P.map e.toMonoidHom
  have hP' : CFSG.ABGLocalTools.IsSylowOf 3 P' ⊤ := by
    apply CFSG.ABGLocalTools.isSylowOf_of_card le_top
    rw [show Nat.card P' = Nat.card P from Subgroup.card_map_of_injective
      (f := e.toMonoidHom) e.injective]
    simpa only [Subgroup.card_top, Nat.card_congr e.toEquiv] using hP.card_eq
  have hxc' : ∀ p ∈ P', p * e x = e x * p := by
    intro p hp
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hp
    change e a * e x = e x * e a
    simpa only [map_mul] using congrArg e (hxc a ha)
  have hx3' : (e x) ^ 3 = 1 := by rw [← map_pow, hx3, map_one]
  have hx1' : e x ≠ 1 := fun h => hx1 (e.injective (h.trans (map_one e).symm))
  obtain ⟨g, hgS⟩ :=
    D4ThreeBCentralizer.exists_conj_mem_short_of_central_sylow_three_triality_two
      hn1 hcard σ hσ hP' hxc' hx3' hx1'
  set R := orbitRankOneHomFixed TwistTag.D4 K σ.toRingHom
    CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.d4Outer with hR
  obtain ⟨A, hA⟩ := MonoidHom.mem_range.mp (Subgroup.mem_comap.mp hgS)
  have hA2 : R A = g * e x * g⁻¹ := Subtype.ext hA
  obtain ⟨w, hw⟩ := CFSG.Quasithin.Z4c2.exists_inverting_sl2 A
  have hW : R w * (g * e x * g⁻¹) * (R w)⁻¹ = (g * e x * g⁻¹)⁻¹ := by
    rw [← hA2]
    calc R w * R A * (R w)⁻¹ = R (w * A * w⁻¹) := by rw [map_mul, map_mul, map_inv]
      _ = R A⁻¹ := by rw [hw]
      _ = (R A)⁻¹ := map_inv R A
  refine ⟨e.symm (g⁻¹ * R w * g), e.injective ?_⟩
  simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
  calc g⁻¹ * R w * g * e x * (g⁻¹ * R w * g)⁻¹ =
        g⁻¹ * (R w * (g * e x * g⁻¹) * (R w)⁻¹) * g := by group
    _ = g⁻¹ * (g * e x * g⁻¹)⁻¹ * g := by rw [hW]
    _ = (e x)⁻¹ := by group

theorem r891_exists_inv_zOf_of_card_three {X : Type} [Group X] [Finite X] {n : ℕ}
    (hX : Is3D4 X n) {P : Subgroup X} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P ⊤)
    (hZ : Nat.card (ZOf P) = 3) : ∃ g : X, ∀ z ∈ ZOf P, g * z * g⁻¹ = z⁻¹ := by
  obtain ⟨x, hxZ, hx3, hZx⟩ := CFSG.GroupTheory.exists_generator_of_card_prime Nat.prime_three hZ
  have hxc : ∀ p ∈ P, p * x = x * p :=
    fun p hp => Subgroup.mem_centralizer_iff.mp hxZ.2 p hp
  have hx3' : x ^ 3 = 1 := by rw [← hx3]; exact pow_orderOf_eq_one x
  obtain ⟨g, hg⟩ := r891_exists_inv_of_central_sylow hX hP hxc hx3'
  refine ⟨g, fun z hz => ?_⟩
  rw [hZx] at hz
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  rw [← conj_zpow, hg, inv_zpow]

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
