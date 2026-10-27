module

public import CFSG.RankThree.PartOne.Q1327T.Item7D4W
public import CFSG.RankThree.PartOne.KGD.D4T36Frame
import CFSG.RankThree.Chevalley.SteinbergBTTrialitySplitPrimePlane
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.RankThree.PartOne.Q1327T

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.RankThree.PartOne.KGD CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Lattice
open scoped Matrix Polynomial

set_option linter.unusedSectionVars false

theorem d4T36_frame_canonical {ℓ f : ℕ} [Fact ℓ.Prime] (hf : 1 ≤ f) (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpd : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 + ε * ((ℓ ^ f : ℕ) : ℤ) + 1)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ] :
    ∃ (w : WeylGroup TwistTag.D4.tag) (g0 : ModGL TwistTag.D4.tag L),
      g0 ∈ adjointGroup TwistTag.D4.tag L ∧
        twistHom TwistTag.D4 L (iterateFrobenius L ℓ f) g0 =
          g0 * canonicalRep (coxeterSystem TwistTag.D4.tag) L w ∧
        (triEmb K σ L).range = adjointGroup TwistTag.D4.tag L ⊓
          (twistHom TwistTag.D4 L (iterateFrobenius L ℓ f)).eqLocus (MonoidHom.id _) ∧
        ∀ Q : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom), IsPGroup p Q →
          ∃ c : graphFixedRootGroup TwistTag.D4 K σ.toRingHom, ∀ y ∈ Q,
            g0⁻¹ * triEmb K σ L (c * y * c⁻¹) * g0 ∈ torusGroup TwistTag.D4.tag L := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hq2 : 2 ≤ ℓ ^ f := Nat.one_lt_pow (by omega) hℓ.one_lt
  have hℓq : ℓ ∣ ℓ ^ f := dvd_pow_self ℓ (by omega)
  obtain ⟨w, hw⟩ := d4T36_weyl hε
  set n : ModGL TwistTag.D4.tag L := canonicalRep (coxeterSystem TwistTag.D4.tag) L w with hndef
  have hnM : n ∈ monomialSubgroup TwistTag.D4.tag L := canonicalRep_mem_monomialSubgroup L w
  have hnW : weylQuotientHom TwistTag.D4.tag L ⟨n, hnM⟩ = w :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep w)
  have hnC : n ∈ adjointGroup TwistTag.D4.tag L := monomialSubgroup_le_adjointGroup' hnM
  obtain ⟨g0, hg0C, hg0⟩ := lang_conjugator_D4 (K := K) (ℓ := ℓ) hf L n hnC
  have hT := twistedTorus_D4_eq_map_of_weylImage Fr hnM w hnW (d4T36M ε) hw
  have hrange := triEmb_range hℓ hf hK hσ Fr hFr
  refine ⟨w, g0, hg0C, hg0, hrange, fun Q hQ => ?_⟩
  have hN : d4T36d ε (ℓ ^ f) * d4T36d ε (ℓ ^ f) ≠ 0 := by
    have : 0 < d4T36d ε (ℓ ^ f) := (d4T36d_odd hε (by omega)).pos
    positivity
  have hZcard : Nat.card ((fixedCharTuples (d4T36M ε) Fr).map
      (rootDiagUnitHom TwistTag.D4.tag L)) = d4T36d ε (ℓ ^ f) * d4T36d ε (ℓ ^ f) := by
    rw [Subgroup.card_map_of_injective rootDiagUnit_injective]
    exact d4T36_card hε (by omega) hℓq hFr
  have hCcard := (triality_both_orientations_exact_finite_order ℓ f hℓ hf K hK 1 (Or.inl rfl)
    σ.toRingHom (fun c => by rw [pow_one]; exact hσ c)).1
  have hord : p ^ (Nat.card (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).factorization p =
      p ^ (d4T36d ε (ℓ ^ f) * d4T36d ε (ℓ ^ f)).factorization p := by
    rw [hCcard]
    exact d4T36_ordProj hε hp hp3 hq2 hpd
  obtain ⟨-, -, -, hconj⟩ := sylow_conjugacy_of_subtorus_gen 1 (triEmb K σ L)
    triEmb_injective (twistHom TwistTag.D4 L Fr) n g0 hg0C hg0 hp hp3 hN
    (fun X hX hXC hXF => triEmb_rational hℓ hf hK hσ Fr hFr X hXC hXF)
    ((fixedCharTuples (d4T36M ε) Fr).map (rootDiagUnitHom TwistTag.D4.tag L)) hT.symm.le hZcard
    hord
  obtain ⟨c, hc⟩ := hconj Q hQ
  refine ⟨c, fun y hy => ?_⟩
  have hmem : g0⁻¹ * triEmb K σ L (c * y * c⁻¹) * g0 ∈
      twistedTorusOf n (twistHom TwistTag.D4 L Fr) := by
    rw [hT]
    exact (mem_subtorusImage_iff _ _ _ _).1 (hc y hy)
  exact (mem_twistedTorusOf.1 hmem).1

theorem exists_inv_of_isPGroup_D4_36 {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f)) {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpd : (p : ℤ) ∣ ((2 ^ f : ℕ) : ℤ) ^ 2 + ε * ((2 ^ f : ℕ) : ℤ) + 1)
    {Q : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)} (hQ : IsPGroup p Q) :
    ∃ z : graphFixedRootGroup TwistTag.D4 K σ.toRingHom, ∀ y ∈ Q, z * y * z⁻¹ = y⁻¹ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : CharP K 2 :=
    finite_field_prime_power_characteristic Nat.prime_two (by omega : 1 ≤ 3 * f)
      (by rw [hK, ← pow_mul, mul_comm])
  let L := AlgebraicClosure K
  have : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  obtain ⟨w, g0, hg0C, hg0, hrange, hconj⟩ := d4T36_frame_canonical (ℓ := 2) hf K hK σ hσ hε hp
    hp3 hpd L
  set F := twistHom TwistTag.D4 L (iterateFrobenius L 2 f) with hFdef
  set n₀ : ModGL TwistTag.D4.tag L := canonicalRep (coxeterSystem TwistTag.D4.tag) L d4NegOne
    with hn₀def
  set n : ModGL TwistTag.D4.tag L := canonicalRep (coxeterSystem TwistTag.D4.tag) L w with hndef
  have hFn₀ : F n₀ = n₀ := by
    rw [hFdef, hn₀def, twistHom_canonicalRep, weylTwist_d4NegOne]
  have hnn₀ : n * n₀ = n₀ * n := by
    rw [hndef, hn₀def, ← canonicalRep_mul_charTwo, ← canonicalRep_mul_charTwo,
      d4NegOne_mul_comm]
  have hn₀C : n₀ ∈ adjointGroup TwistTag.D4.tag L :=
    monomialSubgroup_le_adjointGroup' (canonicalRep_mem_monomialSubgroup L d4NegOne)
  have hz'F : F (g0 * n₀ * g0⁻¹) = g0 * n₀ * g0⁻¹ := by
    rw [map_mul, map_mul, map_inv, hg0, hFn₀, mul_inv_rev]
    calc g0 * n * n₀ * (n⁻¹ * g0⁻¹) = g0 * (n * n₀ * n⁻¹) * g0⁻¹ := by group
      _ = g0 * n₀ * g0⁻¹ := by
        rw [hnn₀, mul_assoc n₀ n n⁻¹, mul_inv_cancel, mul_one]
  have hz'mem : g0 * n₀ * g0⁻¹ ∈ (triEmb K σ L).range := by
    rw [hrange]
    exact Subgroup.mem_inf.2 ⟨mul_mem (mul_mem hg0C hn₀C) (inv_mem hg0C), hz'F⟩
  obtain ⟨z, hz⟩ := hz'mem
  obtain ⟨c, hc⟩ := hconj Q hQ
  refine ⟨c⁻¹ * z * c, fun y hy => ?_⟩
  apply triEmb_injective (K := K) (σ := σ) (L := L)
  have hinv : ∀ h ∈ torusGroup TwistTag.D4.tag L, n₀ * h * n₀⁻¹ = h⁻¹ := by
    intro h hh
    obtain ⟨l, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
    exact SteinbergBT.TrialityPlane.canonicalRep_conj_rootDiagUnit_of_neg (w := d4NegOne)
      d4NegOne_smul l
  have hy' := hc y hy
  set x := triEmb K σ L (c * y * c⁻¹) with hx
  have hconjx : g0 * n₀ * g0⁻¹ * x * (g0 * n₀ * g0⁻¹)⁻¹ = x⁻¹ := by
    have h1 := hinv _ hy'
    calc g0 * n₀ * g0⁻¹ * x * (g0 * n₀ * g0⁻¹)⁻¹
        = g0 * (n₀ * (g0⁻¹ * x * g0) * n₀⁻¹) * g0⁻¹ := by group
      _ = g0 * (g0⁻¹ * x * g0)⁻¹ * g0⁻¹ := by rw [h1]
      _ = x⁻¹ := by group
  have hzx : z * (c * y * c⁻¹) * z⁻¹ = (c * y * c⁻¹)⁻¹ := by
    apply triEmb_injective (K := K) (σ := σ) (L := L)
    rw [map_mul, map_mul, map_inv, map_inv, hz]
    exact hconjx
  have e1 : c⁻¹ * z * c * y * (c⁻¹ * z * c)⁻¹ = c⁻¹ * (z * (c * y * c⁻¹) * z⁻¹) * c := by group
  have e2 : c⁻¹ * (c * y * c⁻¹)⁻¹ * c = y⁻¹ := by group
  show triEmb K σ L (c⁻¹ * z * c * y * (c⁻¹ * z * c)⁻¹) = triEmb K σ L y⁻¹
  rw [e1, hzx, e2]

end CFSG.RankThree.PartOne.Q1327T
