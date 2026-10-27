module

public import CFSG.RankThree.PartTwo.Sec4.Item417Res6ProofExc
import CFSG.RankThree.PartTwo.Sec4.Item417Res6ProofTools
import CFSG.RankThree.PartTwo.Sec4.Item417Res7ProofD4Odd
import CFSG.RankThree.PartTwo.Sec4.Item417Res7ProofD4Toral
import CFSG.RankThree.PartTwo.Sec4.Item417Res8ProofD4Plane
import CFSG.RankThree.PartTwo.Sec21.Item223Rank2ProofD4
import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne
open Res417Three Res417Five Res417Six Res417Seven

namespace Res417Eight

theorem three_dvd_two_pow_pow_sub_one {f : ℕ} (hf : Even f) (k : ℕ) : 3 ∣ (2 ^ f) ^ k - 1 := by
  have h1 : 2 ^ f % 3 = 1 := by
    obtain ⟨m, rfl⟩ := hf
    rw [← two_mul, pow_mul, Nat.pow_mod]
    norm_num
  have h2 : (2 ^ f) ^ k % 3 = 1 := by simp [Nat.pow_mod, h1]
  have h3 : 1 ≤ (2 ^ f) ^ k := Nat.one_le_pow _ _ (by positivity)
  omega

section Main

theorem k417DatumD4Even_holds :
    K417DatumD4Even := by
  intro X _ f hev hX D hD
  obtain ⟨hDe, hmax, F, hFD, hF9, T, hT2, hFT, hTF⟩ := hD
  obtain ⟨K, _, _, _, σ, hK, hσ, hσ3, hf1, -, ⟨φ⟩⟩ := exists_graphFixedRootGroup_of_trialityD4 hX
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := finite_modGL (τ := TwistTag.D4.tag) (K := K)
  set C := graphFixedRootGroup TwistTag.D4 K σ.toRingHom with hC
  have : Finite X := Finite.of_equiv _ φ.symm.toEquiv
  have hD9 : Nat.card D ≤ 9 := by
    have h := Sec21.Item223Rank2Proof.card_le_nine_of_graphFixedRootGroup hf1 hK
      (σ := σ.toRingHom) hσ (D.map φ.toMonoidHom) (isElemAbelian_map φ.toMonoidHom hDe)
    rwa [Subgroup.card_map_of_injective φ.injective] at h
  have hFD' : F = D := Subgroup.eq_of_le_of_card_ge hFD (by omega)
  subst hFD'
  set ψ : X →* ModGL TwistTag.D4.tag K := C.subtype.comp φ.toMonoidHom with hψdef
  have hψ : Function.Injective ψ := Subtype.val_injective.comp φ.injective
  have hψC : ∀ x, ψ x ∈ C := fun x => (φ x).2
  have hT1 : T ≠ ⊥ := fun h => hTF (h ▸ bot_le)
  have hT'1 : T.map ψ ≠ ⊥ := fun h => hT1 ((Subgroup.map_eq_bot_iff_of_injective _ hψ).1 h)
  have hT'C : T.map ψ ≤ C := by
    rintro _ ⟨x, -, rfl⟩
    exact hψC x
  have hF'C : F.map ψ ≤ C := by
    rintro _ ⟨x, -, rfl⟩
    exact hψC x
  have hF'T' : F.map ψ ≤ Subgroup.normalizer ((T.map ψ : Subgroup (ModGL TwistTag.D4.tag K)) :
      Set (ModGL TwistTag.D4.tag K)) :=
    (Subgroup.map_mono hFT).trans (Subgroup.le_normalizer_map ψ)
  have hF'3 : ∀ y ∈ F.map ψ, y ^ 3 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hDe.2 x hx, map_one]
  have hF'p : IsPGroup 3 (F.map ψ) := fun y => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    exact hF'3 _ y.2)⟩
  obtain ⟨x, hxC, J, hJ, hle⟩ := exists_conj_le_graphFixedParabolicLevi TwistTag.D4 (r := 2)
    (p := 3) (by norm_num) σ hσ3 hF'C hF'p hT'C (hT2.map ψ) hT'1 hF'T'
  obtain ⟨a, haJ⟩ := exists_subset_singleton_of_ne_univ hJ
  have hσ' : ∀ c, σ.toRingHom c = c ^ ((2 ^ f) ^ 1) := fun c => by
    rw [pow_one]
    exact hσ c
  have h3L : ∀ b, 3 ∣ Nat.card (orbitField TwistTag.D4 K σ.toRingHom b) - 1 := fun b => by
    rw [card_orbitField_D4_orientation Nat.prime_two hf1 hK (Or.inl rfl) hσ' b]
    exact three_dvd_two_pow_pow_sub_one hev _
  obtain ⟨y, hyM, hyH⟩ := exists_conj_le_graphFixedRootTorus σ hσ3 a (h3L a)
    (hle.trans (graphFixedParabolicLevi_mono _ haJ)) (by
      rintro _ ⟨u, hu, rfl⟩
      rw [MulEquiv.coe_toMonoidHom, ← map_pow, hF'3 u hu, map_one])
  have hyC : y ∈ C := (range_le_graphFixedParabolicLevi σ.toRingHom a hyM).2
  set g : C := ⟨y * x, mul_mem hyC hxC⟩ with hg
  set V := K133H.d4Torsion σ.toRingHom 3 with hV
  have hgV : ∀ d ∈ F, g * φ d * g⁻¹ ∈ V.subgroupOf C := by
    intro d hd
    rw [Subgroup.mem_subgroupOf]
    have hH := hyH ⟨_, ⟨ψ d, ⟨d, hd, rfl⟩, rfl⟩, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hH
    have e : ((g * φ d * g⁻¹ : C) : ModGL TwistTag.D4.tag K) = y * (x * ψ d * x⁻¹) * y⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hg, hψdef, MonoidHom.coe_comp,
        Function.comp_apply, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom]
      group
    rw [e]
    refine ⟨hH, ?_⟩
    rw [conj_pow, conj_pow, ← map_pow, hDe.2 d hd, map_one, mul_one, mul_inv_cancel, mul_one,
      mul_inv_cancel]
  have hTcomm : ∀ s ∈ V.subgroupOf C, ∀ t ∈ V.subgroupOf C, s * t = t * s := fun s hs t ht =>
    Subtype.ext (K133H.graphFixedRootTorus_comm σ.toRingHom (Subgroup.mem_subgroupOf.1 hs).1
      (Subgroup.mem_subgroupOf.1 ht).1)
  have hTexp : ∀ t ∈ V.subgroupOf C, t ^ 3 = 1 := fun t ht => Subtype.ext (by
    rw [Subgroup.coe_pow]
    exact (Subgroup.mem_subgroupOf.1 ht).2)
  have hmap := map_eq_of_conj_le φ hmax hTcomm hTexp hgV
  obtain ⟨-, -, -, hL2, -⟩ := triality_all_characteristic_faithful_torus_coordinates K σ hσ3
  have hk3 : 3 ∣ Nat.card (trialityFixedField K σ.toRingHom) - 1 := by
    have h := h3L ⟨1, by decide⟩
    rwa [hL2] at h
  refine ⟨by omega, ?_⟩
  obtain ⟨ψ₁⟩ := nonempty_autIn_mulEquiv_of_map_eq _ hmap
  obtain ⟨ψ₂⟩ := nonempty_torusImage_d4Torsion_three_mulEquiv σ hσ3 hk3
  exact ⟨ψ₁.trans ψ₂⟩

end Main

end Res417Eight

end CFSG.RankThree.PartTwo.Sec4
