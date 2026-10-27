module

public import CFSG.RankThree.PartTwo.KFacts.KS222SL3Tools
import CFSG.RankThree.PartTwo.Sec21.Item22L2
public import CFSG.RankThree.PartTwo.Sec21.Item211

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)

namespace SL3Lines

theorem map_fixedSubgroupOf_eq_of_conj {X M : Type*} [Group X] [Group M] {Y : Subgroup M}
    (ε : X ≃* Y) {τ : MulAut X} {y : M}
    (hy : ∀ x : X, ((ε (τ x) : Y) : M) = y * (ε x : M) * y⁻¹) :
    (fixedSubgroupOf τ).map (Y.subtype.comp ε.toMonoidHom) =
      Y ⊓ Subgroup.centralizer ({y} : Set M) := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨(ε x).2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have h := hy x
    rw [(mem_fixedSubgroupOf τ x).mp hx] at h
    show (ε x : M) * y = y * ε x
    calc (ε x : M) * y = y * ε x * y⁻¹ * y := by rw [← h]
      _ = y * ε x := by group
  · intro hz
    obtain ⟨hzY, hzC⟩ := Subgroup.mem_inf.mp hz
    rw [Subgroup.mem_centralizer_singleton_iff] at hzC
    refine ⟨ε.symm ⟨z, hzY⟩, ?_, by simp⟩
    show τ (ε.symm ⟨z, hzY⟩) = ε.symm ⟨z, hzY⟩
    apply ε.injective
    apply Subtype.ext
    rw [hy, ε.apply_symm_apply]
    show y * z * y⁻¹ = z
    calc y * z * y⁻¹ = z * y * y⁻¹ := by rw [hzC]
      _ = z := by group

end SL3Lines

theorem ks222SL3Bar :
    ∀ (G : Type) [Group G] [Finite G] (L A : Subgroup G) (n : ℕ), 0 < n → Even n →
      Nonempty (lBar L ≃* SL3 n) → IsTypeCOnBarSL A L →
      ∀ τ ∈ Sec4.autThetaQuot A L, (∃ z : lBar L, τ z ≠ z) →
        Even (Nat.card (fixedSubgroupOf τ)) →
        Nonempty (inSubgroup perfectResidual (fixedSubgroupOf τ) ≃* projSL 2 (GaloisField 2 n)) := by
  intro G _ _ L A n hn he ⟨eB⟩ hC τ hτ hnc hev
  obtain ⟨π, p, f, K, _, hPi, hmod, e, D, hD, hconj, -⟩ := hC
  obtain ⟨rfl, rfl, rfl⟩ := SL3Lines.params_eq hn he hPi hmod (eB.symm.trans e)
  have := hPi.finite
  have hn2 : 2 ≤ f := by obtain ⟨k, hk⟩ := he; omega
  have h2 : (2 : K) = 0 := SL3Lines.two_eq_zero_of_mulEquiv hn2
    (fun x hx => (Sec4.mem_slPi_true _).mp hx) (eB.symm.trans e)
  have : CharP K 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).mpr (by exact_mod_cast h2)
  have hK : Nat.card K = 2 ^ f := hPi.card
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hn2
  obtain ⟨y, hyD, hy⟩ := hconj τ hτ
  have hmap := SL3Lines.map_fixedSubgroupOf_eq_of_conj e hy
  have hιinj : Function.Injective ((Sec4.slPi true 3 (2 ^ f) K).subtype.comp e.toMonoidHom) :=
    (Sec4.slPi true 3 (2 ^ f) K).subtype_injective.comp e.injective
  have hnc' : ∃ M ∈ Sec4.slPi true 3 (2 ^ f) K, M * y ≠ y * M := by
    obtain ⟨z, hz⟩ := hnc
    refine ⟨e z, (e z).2, fun h => hz ?_⟩
    apply e.injective
    apply Subtype.ext
    rw [hy]
    calc y * (e z : GL (Fin 3) K) * y⁻¹ = (e z : GL (Fin 3) K) * y * y⁻¹ := by rw [h]
      _ = e z := by group
  have hev' : Even (Nat.card ↥(Sec4.slPi true 3 (2 ^ f) K ⊓ Subgroup.centralizer {y})) := by
    rw [← hmap, Subgroup.card_map_of_injective hιinj]
    exact hev
  obtain ⟨g, -, hdiag, -⟩ := Sec4.isTypeC_conj_std hPi hmod hD
  obtain ⟨l, s, t, -, -, hyg⟩ := hdiag y hyD
  obtain ⟨e₁⟩ := SL3Lines.perfectResidual_centralizer_of_conj hPi hK4 hyg hnc' hev'
  have hres : (inSubgroup perfectResidual (fixedSubgroupOf τ)).map
      ((Sec4.slPi true 3 (2 ^ f) K).subtype.comp e.toMonoidHom) =
      inSubgroup perfectResidual (Sec4.slPi true 3 (2 ^ f) K ⊓ Subgroup.centralizer {y}) := by
    rw [GroupTheory.SteinbergBY.map_inSubgroup_perfectResidual_of_injective _ hιinj, hmap]
  have := Fintype.ofFinite K
  have := Fintype.ofFinite (GaloisField 2 f)
  have hcard : Fintype.card K = Fintype.card (GaloisField 2 f) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK,
      GaloisField.card 2 f (by omega)]
  exact ⟨((inSubgroup perfectResidual (fixedSubgroupOf τ)).equivMapOfInjective _ hιinj).trans
    ((MulEquiv.subgroupCongr hres).trans (e₁.trans
      ((CFSG.Adapters.RankTwoModelTransports.specialLinearGroupCongr (Fin 2)
        (FiniteField.ringEquivOfCardEq hcard)).trans (projSLTwoEquivSL _).symm)))⟩

end CFSG.RankThree.PartTwo.Sec21
