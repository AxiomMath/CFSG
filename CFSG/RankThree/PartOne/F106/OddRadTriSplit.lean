module

public import CFSG.RankThree.PartOne.F106.OddRadSL2
public import CFSG.RankThree.Chevalley.SteinbergCFTrialityToralSylow
public import CFSG.RankThree.Chevalley.SteinbergCFTrialityToralQuasisimple
public import CFSG.LieType.Chevalley.TrialityAllCharTorusCoordinates
public import CFSG.LieType.Chevalley.TrialityExactFiniteOrder
public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
public import CFSG.ClassicalInvolution.WeakCT.StandardPair
public import CFSG.LieType.CurtisTits.SpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical
public import CFSG.LocalAnalysis.SectionRank.Sporadic.TitsGen
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Perm.ChainSpec
public import CFSG.RankThree.PartOne.CTP.SeitzLinear
public import CFSG.RankThree.PartOne.F106.OddRadTools
public import CFSG.RankThree.PartOne.KC.LinearCommutatorOdd
public import CFSG.RankThree.PartOne.KC.LinearDegreeFive
public import CFSG.RankThree.PartOne.KC.LinearEndpointStatements
public import CFSG.RankThree.PartOne.KC.PlaneReductionGeneral
public import CFSG.RankThree.PartOne.N143.Weyl613Defs
public import CFSG.RankThree.PartOne.N143X.KF64WSimple
public import CFSG.RankThree.PartOne.S11d.OutLinear
public import CFSG.RankThree.Theta.ThreeComponentOrbitCover
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.Walter.Defs
public import Certificates.Certificate1
public import Certificates.Certificate2
public import Certificates.Certificate2267
public import Certificates.Certificate8033

public section

namespace CFSG.RankThree.PartOne.F106

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.Chevalley.TrialityFold
open scoped commutatorElement

set_option linter.unusedSectionVars false

theorem sigma_cube_apply_D4 {f : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f)) (c : K) :
    σ (σ (σ c)) = c := by
  have : Fintype K := Fintype.ofFinite K
  rw [hσ, hσ, hσ, ← pow_mul, ← pow_mul,
    show 2 ^ f * (2 ^ f * 2 ^ f) = (2 ^ f) ^ 3 by ring, ← hK, Nat.card_eq_fintype_card,
    FiniteField.pow_card]

theorem dichotomy_D4_split {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f))
    (hq : 5 ∣ 2 ^ f - 1) {x : ModGL TwistTag.D4.tag K}
    (hxH : x ∈ graphFixedRootTorus TwistTag.D4 K σ.toRingHom) (hx : orderOf x = 5) :
    (∀ u ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom ⊓ Subgroup.centralizer {x},
      ∀ v ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom ⊓ Subgroup.centralizer {x},
        u * v = v * u) ∨
    ∃ R : Subgroup (ModGL TwistTag.D4.tag K),
      ⁅graphFixedRootGroup TwistTag.D4 K σ.toRingHom ⊓ Subgroup.centralizer {x},
        graphFixedRootGroup TwistTag.D4 K σ.toRingHom ⊓ Subgroup.centralizer {x}⁆ = R ∧
      IsSimpleGroup ↥R ∧ Group.IsPerfect ↥R := by
  classical
  have hσ3 : σ ^ 3 = 1 := RingEquiv.ext fun c => sigma_cube_apply_D4 hK σ hσ c
  have hq6 : 5 ≤ 2 ^ f - 1 := Nat.le_of_dvd (by
    have : 2 ≤ 2 ^ f := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    omega) hq
  have : CharP K 2 :=
    finite_field_prime_power_characteristic Nat.prime_two (k := f * 3) (by omega)
      (by rw [hK, pow_mul])
  obtain ⟨-, ⟨e, he⟩, -⟩ := triality_all_characteristic_faithful_torus_coordinates K σ hσ3
  obtain ⟨⟨a, b⟩, hab⟩ := e.surjective ⟨x, hxH⟩
  have hxeq : x = trialityOuterTorus K σ a * trialityMiddleTorus K σ b := by
    rw [← he a b, hab]
  have hx5 : x ^ 5 = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx] at this
  have hab5 : (a, b) ^ 5 = 1 := e.injective (by
    rw [map_pow, hab, map_one]
    exact Subtype.ext hx5)
  have ha5 : a ^ 5 = 1 := congrArg Prod.fst hab5
  have hb5 : b ^ 5 = 1 := congrArg Prod.snd hab5
  set z : Kˣ := trialityFixedUnit K σ b with hz
  have hz5 : z ^ 5 = 1 := by rw [hz, ← map_pow, hb5, map_one]
  have hσa : Units.map σ.toRingHom.toMonoidHom a = a := by
    apply Units.ext
    show σ (a : K) = a
    rw [hσ]
    obtain ⟨m, hm⟩ := hq
    have h1 : 2 ^ f = 5 * m + 1 := by omega
    have ha5' : (a : K) ^ 5 = 1 := by
      have := congrArg Units.val ha5
      simpa using this
    rw [h1, pow_succ, pow_mul, ha5', one_pow, one_mul]
  set A : Kˣ := a ^ 2 * z⁻¹ with hA
  set B : Kˣ := (a * a * a)⁻¹ * z ^ 2 with hB
  have hxdiag : x = rootDiagUnit TwistTag.D4.tag (d4Tuple A A B A) := by
    rw [hxeq, trialityOuter_mul_middle_eq a b]
    simp only [hσa]
    rfl
  have hA5 : A ^ 5 = 1 := by
    rw [hA, mul_pow, inv_pow, ← pow_mul, mul_comm 2 5, pow_mul, ha5, hz5]
    simp
  have hB5 : B ^ 5 = 1 := by
    have h1 : (a * a * a) ^ 5 = 1 := by
      rw [mul_pow, mul_pow, ha5]
      simp
    rw [hB, mul_pow, inv_pow, h1, ← pow_mul, mul_comm 2 5, pow_mul, hz5]
    simp
  have hAB : ¬(A = 1 ∧ B = 1) := by
    rintro ⟨hA1, hB1⟩
    have h1 : x = 1 := by
      rw [hxdiag, hA1, hB1, ← rootDiagUnit_one, ← vec4_one]
    rw [h1, orderOf_one] at hx
    omega
  have hHcomm : ∀ u ∈ graphFixedRootTorus TwistTag.D4 K σ.toRingHom,
      ∀ v ∈ graphFixedRootTorus TwistTag.D4 K σ.toRingHom, u * v = v * u := by
    intro u hu v hv
    obtain ⟨p, hp⟩ := e.surjective ⟨u, hu⟩
    obtain ⟨q, hq'⟩ := e.surjective ⟨v, hv⟩
    have h1 : e (p * q) = e (q * p) := by rw [mul_comm p q]
    rw [map_mul, map_mul, hp, hq'] at h1
    exact congrArg Subtype.val h1
  rw [hxdiag]
  rcases triality_toral_centralizer_cases (K := K) σ (a := d4Tuple A A B A) (A := A) (B := B)
      rfl rfl rfl rfl Nat.prime_five (by norm_num) hA5 hB5 hAB with
    ⟨-, hX⟩ | ⟨v, hv, b', -, -, hDeq, -⟩
  · left
    rw [hX]
    exact hHcomm
  · right
    have hσ1 : ∀ c, σ.toRingHom c = c ^ ((2 ^ f) ^ 1) := fun c => by
      rw [pow_one]
      exact hσ c
    have h4 : 4 ≤ Nat.card (orbitField TwistTag.D4 K σ.toRingHom b') := by
      rw [card_orbitField_D4_orientation Nat.prime_two hf hK (Or.inl rfl) hσ1 b']
      have hpos : 1 ≤ (TwistTag.D4.orbit b').card := TwistTag.D4.card_orbit_pos b'
      calc 4 ≤ 2 ^ f := by omega
        _ ≤ (2 ^ f) ^ (TwistTag.D4.orbit b').card := Nat.le_self_pow (by omega) _
    have h4' : ∃ s : Finset (orbitField TwistTag.D4 K σ.toRingHom b'), s.card = 4 := by
      have : Fintype (orbitField TwistTag.D4 K σ.toRingHom b') := Fintype.ofFinite _
      have hle : 4 ≤ (Finset.univ : Finset (orbitField TwistTag.D4 K σ.toRingHom b')).card := by
        rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
        exact h4
      obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq hle
      exact ⟨s, hs⟩
    obtain ⟨-, hcomm, -, -⟩ := triality_orbitPair_structure σ hσ3 hv b' h4' _ hDeq
    obtain ⟨e'⟩ := nonempty_mulEquiv_graphFixedRootPair_D4 σ hσ3 hv b'
    have : Finite (orbitField TwistTag.D4 K σ.toRingHom b') := Subtype.finite
    obtain ⟨hs, hp⟩ := simple_perfect_of_mulEquiv_SL2 h4 e'
    exact ⟨_, hcomm, hs, hp⟩

theorem oddRad_D4_split {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f))
    (hq : 5 ∣ 2 ^ f - 1) (x : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hx : orderOf x = 5) :
    Odd (Nat.card ↥(solvableRadical ↥(perfectResidual ↥(Subgroup.centralizer {x})))) := by
  classical
  have hx5 : x ^ 5 = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx] at this
  obtain ⟨hsyl, -⟩ := triality_split_prime_toral_Sylow Nat.prime_two hf K hK σ hσ
    Nat.prime_five (by norm_num) hq
  have hP : IsPGroup 5 ↥(Subgroup.zpowers x) := fun y => ⟨1, by
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 y.2
    apply Subtype.ext
    show (y : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ^ 5 ^ 1 = 1
    rw [← hm, pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx5,
      one_zpow]⟩
  obtain ⟨g, hg⟩ := hsyl _ hP
  have hgx := Subgroup.mem_subgroupOf.1
    (hg (Subgroup.mem_map.2 ⟨x, Subgroup.mem_zpowers x, rfl⟩))
  have hgx' : (g : ModGL TwistTag.D4.tag K) * ((x : graphFixedRootGroup TwistTag.D4 K
      σ.toRingHom) : ModGL TwistTag.D4.tag K) * (g : ModGL TwistTag.D4.tag K)⁻¹ ∈
      graphFixedRootTorus TwistTag.D4 K σ.toRingHom := hgx
  have hord : orderOf ((g : ModGL TwistTag.D4.tag K) * ((x : graphFixedRootGroup TwistTag.D4 K
      σ.toRingHom) : ModGL TwistTag.D4.tag K) * (g : ModGL TwistTag.D4.tag K)⁻¹) = 5 := by
    rw [← MulAut.conj_apply, ← MulEquiv.coe_toMonoidHom,
      orderOf_injective _ (MulAut.conj (g : ModGL TwistTag.D4.tag K)).injective,
      Subgroup.orderOf_coe, hx]
  have h1 := card_radical_residual_of_embedding
    (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype Subtype.val_injective x
  rw [Subgroup.range_subtype, Subgroup.coe_subtype] at h1
  have h2 := card_radical_residual_conj (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) g.2
    ((x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) : ModGL TwistTag.D4.tag K)
  rw [h1, ← h2]
  exact odd_card_radical_residual_of_dichotomy _ (dichotomy_D4_split hf K hK σ hσ hq hgx' hord)

end CFSG.RankThree.PartOne.F106
