module

public import CFSG.RankThree.PartTwo.Sec21.Item223Rank2ProofD4
public import CFSG.RankThree.PartTwo.Sec4.Notation
public import CFSG.Blueprint.Catalog
public import CFSG.Assembly.Defs
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
import CFSG.RankThree.PartTwo.Sec4.Item417Res6ProofTools
import CFSG.RankThree.PartTwo.Sec4.Item417Res7ProofD4Odd
import CFSG.RankThree.PartTwo.Sec4.Item417Res7ProofD4Toral
import CFSG.RankThree.PartTwo.Sec4.Item417Res7ProofD4Levi
import CFSG.RankThree.PartTwo.Sec4.Item417Res8ProofD4Plane
import CFSG.RankThree.PartOne.K133H.D4Plane
import CFSG.LieType.Chevalley.TrialityAllCharTorusCoordinates
import CFSG.LieType.Chevalley.TrialityExactFiniteOrder
import CFSG.RankThree.PartTwo.Sec21.Item228Census6ProofTools
public import CFSG.Adapters.TauCetiExceptional.BridgeTransport
public import CFSG.LieType.Chevalley.EvenRootCommutatorF4
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Sporadic.Schreier.TitsOther
import CFSG.RankThree.PartOne.K128.D4Syl

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartOne
open CFSG.Assembly (IsElemAbelian)
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

namespace Item228Census6Proof


theorem nonempty_autIn_d4 {Y : Type} [Group Y] {f : ℕ} (hev : Even f)
    (hY : ChevalleyExceptionalModel Y .trialityD4 2 f) {B : Subgroup Y} (hB : IsElemAbelian 3 B)
    (hB9 : Nat.card B = 9) {T : Subgroup Y} (hT2 : IsPGroup 2 T) (hT1 : T ≠ ⊥)
    (hBT : B ≤ Subgroup.normalizer (T : Set Y)) :
    Nonempty (Sec4.autIn ⊤ B ≃* DihedralGroup 6) := by
  obtain ⟨K, _, _, _, σ, hK, hσ, hσ3, hf1, -, ⟨φ⟩⟩ :=
    Sec4.Res417Seven.exists_graphFixedRootGroup_of_trialityD4 hY
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := finite_modGL (τ := TwistTag.D4.tag) (K := K)
  set C := graphFixedRootGroup TwistTag.D4 K σ.toRingHom with hC
  set ψ : Y →* ModGL TwistTag.D4.tag K := C.subtype.comp φ.toMonoidHom with hψdef
  have hψ : Function.Injective ψ := Subtype.val_injective.comp φ.injective
  have hψC : ∀ x, ψ x ∈ C := fun x => (φ x).2
  have hT'1 : T.map ψ ≠ ⊥ := fun h => hT1 ((Subgroup.map_eq_bot_iff_of_injective _ hψ).1 h)
  have hT'C : T.map ψ ≤ C := by
    rintro _ ⟨x, -, rfl⟩
    exact hψC x
  have hB'C : B.map ψ ≤ C := by
    rintro _ ⟨x, -, rfl⟩
    exact hψC x
  have hB'T' : B.map ψ ≤ Subgroup.normalizer ((T.map ψ : Subgroup (ModGL TwistTag.D4.tag K)) :
      Set (ModGL TwistTag.D4.tag K)) :=
    (Subgroup.map_mono hBT).trans (Subgroup.le_normalizer_map ψ)
  have hB'3 : ∀ y ∈ B.map ψ, y ^ 3 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hB.2 x hx, map_one]
  have hB'p : IsPGroup 3 (B.map ψ) := fun y => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    exact hB'3 _ y.2)⟩
  obtain ⟨x, hxC, J, hJ, hle⟩ := Sec4.Res417Seven.exists_conj_le_graphFixedParabolicLevi
    TwistTag.D4 (r := 2) (p := 3) (by norm_num) σ hσ3 hB'C hB'p hT'C (hT2.map ψ) hT'1 hB'T'
  obtain ⟨a, haJ⟩ := Sec4.Res417Seven.exists_subset_singleton_of_ne_univ hJ
  have hσ' : ∀ c, σ.toRingHom c = c ^ ((2 ^ f) ^ 1) := fun c => by
    rw [pow_one]
    exact hσ c
  have h3L : ∀ b, 3 ∣ Nat.card (orbitField TwistTag.D4 K σ.toRingHom b) - 1 := fun b => by
    rw [card_orbitField_D4_orientation Nat.prime_two hf1 hK (Or.inl rfl) hσ' b, ← pow_mul]
    have h := two_pow_mod_three_of_even (hev.mul_right (TwistTag.D4.orbit b).card)
    have h1 : 1 ≤ 2 ^ (f * (TwistTag.D4.orbit b).card) := Nat.one_le_two_pow
    omega
  obtain ⟨y, hyM, hyH⟩ := Sec4.Res417Seven.exists_conj_le_graphFixedRootTorus σ hσ3 a (h3L a)
    (hle.trans (Sec4.Res417Seven.graphFixedParabolicLevi_mono _ haJ)) (by
      rintro _ ⟨u, hu, rfl⟩
      rw [MulEquiv.coe_toMonoidHom, ← map_pow, hB'3 u hu, map_one])
  have hyC : y ∈ C := (Sec4.Res417Seven.range_le_graphFixedParabolicLevi σ.toRingHom a hyM).2
  set g : C := ⟨y * x, mul_mem hyC hxC⟩ with hg
  set V := K133H.d4Torsion σ.toRingHom 3 with hV
  have hgV : ∀ d ∈ B, g * φ d * g⁻¹ ∈ V.subgroupOf C := by
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
    rw [conj_pow, conj_pow, ← map_pow, hB.2 d hd, map_one, mul_one, mul_inv_cancel, mul_one,
      mul_inv_cancel]
  have hVcomm : ∀ s ∈ V.subgroupOf C, ∀ t ∈ V.subgroupOf C, s * t = t * s := fun s hs t ht =>
    Subtype.ext (K133H.graphFixedRootTorus_comm σ.toRingHom (Subgroup.mem_subgroupOf.1 hs).1
      (Subgroup.mem_subgroupOf.1 ht).1)
  have hVexp : ∀ t ∈ V.subgroupOf C, t ^ 3 = 1 := fun t ht => Subtype.ext (by
    rw [Subgroup.coe_pow]
    exact (Subgroup.mem_subgroupOf.1 ht).2)
  have hVe : IsElemAbelian 3 (V.subgroupOf C) :=
    ⟨⟨⟨fun s t => Subtype.ext (hVcomm s s.2 t t.2)⟩⟩, hVexp⟩
  have hV9 : Nat.card (V.subgroupOf C) ≤ 9 :=
    Item223Rank2Proof.card_le_nine_of_graphFixedRootGroup hf1 hK (σ := σ.toRingHom) hσ
      (V.subgroupOf C) hVe
  have hleV : B.map (φ.trans (MulAut.conj g)).toMonoidHom ≤ V.subgroupOf C := by
    rintro _ ⟨d, hd, rfl⟩
    exact hgV d hd
  have hmap : B.map (φ.trans (MulAut.conj g)).toMonoidHom = V.subgroupOf C :=
    Subgroup.eq_of_le_of_card_ge hleV (by
      rw [Subgroup.card_map_of_injective (MulEquiv.injective _), hB9]
      exact hV9)
  obtain ⟨-, -, -, hL2, -⟩ := triality_all_characteristic_faithful_torus_coordinates K σ hσ3
  have hk3 : 3 ∣ Nat.card (trialityFixedField K σ.toRingHom) - 1 := by
    have h := h3L ⟨1, by decide⟩
    rwa [hL2] at h
  obtain ⟨ψ₁⟩ := Sec4.Res417Six.nonempty_autIn_mulEquiv_of_map_eq _ hmap
  obtain ⟨ψ₂⟩ := Sec4.Res417Eight.nonempty_torusImage_d4Torsion_three_mulEquiv σ hσ3 hk3
  exact ⟨ψ₁.trans ψ₂⟩

end Item228Census6Proof

end CFSG.RankThree.PartTwo.Sec21
