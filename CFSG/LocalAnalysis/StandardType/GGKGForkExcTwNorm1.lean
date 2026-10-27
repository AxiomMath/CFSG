module

public import CFSG.LocalAnalysis.StandardType.GGKGForkExcTwCent

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.RootOps CFSG.RankThree.PartOne.KE CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.SeitzGeneration CFSG.Blueprint

theorem ggKGTn_family_data
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    (hp : p.Prime) (hp5 : 5 ≤ p) (F : TwE6Frame K σ n p E)
    (hv : (p ∣ 2 ^ n - 1 ∧ F.v = 1) ∨ (p ∣ 2 ^ n + 1 ∧ ExcIsLongest TwistTag.E6.tag F.v)) :
    ∃ (ι : Type) (a : ι → Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ),
      familyStabilizer a = {1} ∧ familyKernel a = ∅ ∧
        ∀ i, ∃ e ∈ E, rootDiagUnit TwistTag.E6.tag (a i) =
          F.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
            (e : ModGL TwistTag.E6.tag K) * F.g0 := by
  classical
  let L := AlgebraicClosure K
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2 * n)
    (by rw [Fintype.card_eq_nat_card, hK, ← pow_mul, mul_comm])
  haveI : CharP L 2 :=
    charP_of_injective_algebraMap (algebraMap K L).injective 2
  haveI : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  obtain ⟨ζu, hζu⟩ := exists_primitiveRoot_units (L := L) (ℓ := 2)
    (by norm_num) hp (by omega)
  let ζ : L := ζu
  have hζ : IsPrimitiveRoot ζ p := IsPrimitiveRoot.coe_units_iff.2 hζu
  rcases hv with ⟨hpq, hvn⟩ | ⟨hpq, hlong⟩
  · let ι := {b : Fin TwistTag.E6.tag.rank → Lˣ //
        (∀ j, b j ^ p = 1) ∧
          b (⟨0, by decide⟩ : Fin TwistTag.E6.tag.rank) = b ⟨5, by decide⟩ ∧
          b (⟨2, by decide⟩ : Fin TwistTag.E6.tag.rank) = b ⟨4, by decide⟩}
    let a : ι → Fin TwistTag.E6.tag.rank → Lˣ := Subtype.val
    have hall : ∀ b : Fin TwistTag.E6.tag.rank → Lˣ, (∀ j, b j ^ p = 1) →
        b (⟨0, by decide⟩ : Fin TwistTag.E6.tag.rank) = b ⟨5, by decide⟩ →
        b (⟨2, by decide⟩ : Fin TwistTag.E6.tag.rank) = b ⟨4, by decide⟩ →
        ∃ i, a i = b := by
      intro b hb h05 h24
      exact ⟨⟨b, hb, h05, h24⟩, rfl⟩
    refine ⟨ι, a, ?_, ?_, ?_⟩
    · exact ggKGExc_familyStabilizer_phi (ζ := ζ) hp hp5 hζ a hall
    · exact ggKGExc_familyKernel_phi (ζ := ζ) hp hp5 hζ a hall
    · intro i
      exact ggKGTc_exists_conj_of_hact hK hσ hp hp5 F i.property.1
        (ggKGTc_hact_w_one F hvn hpq i.property.1 i.property.2.1 i.property.2.2)
  · let ι := {b : Fin TwistTag.E6.tag.rank → Lˣ // ∀ j, b j ^ p = 1}
    let a : ι → Fin TwistTag.E6.tag.rank → Lˣ := Subtype.val
    have hall : ∀ b : Fin TwistTag.E6.tag.rank → Lˣ, (∀ j, b j ^ p = 1) →
        ∃ i, a i = b := fun b hb => ⟨⟨b, hb⟩, rfl⟩
    refine ⟨ι, a, ?_, ?_, ?_⟩
    · exact ggKGExc_familyStabilizer_allPTorsion (Or.inl rfl) hp (by omega) hζ a hall
    · exact ggKGExc_familyKernel_allPTorsion hp (by omega) hζ a hall
    · intro i
      exact ggKGTc_exists_conj_of_hact hK hσ hp hp5 F i.property
        (ggKGTc_hact_w_w0 F hlong hpq i.property)

theorem ggKGTn_adjoint_inf_centralizer_eq
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    (hp : p.Prime) (hp5 : 5 ≤ p) (F : TwE6Frame K σ n p E)
    (hv : (p ∣ 2 ^ n - 1 ∧ F.v = 1) ∨ (p ∣ 2 ^ n + 1 ∧ ExcIsLongest TwistTag.E6.tag F.v)) :
    adjointGroup TwistTag.E6.tag (AlgebraicClosure K) ⊓
        Subgroup.centralizer {z | ∃ e ∈ E,
          z = F.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
            (e : ModGL TwistTag.E6.tag K) * F.g0} =
      torusGroup TwistTag.E6.tag (AlgebraicClosure K) := by
  classical
  let L := AlgebraicClosure K
  let V : Set (ModGL TwistTag.E6.tag L) :=
    {z | ∃ e ∈ E, z = F.g0⁻¹ * baseChangeGL (algebraMap K L)
      (e : ModGL TwistTag.E6.tag K) * F.g0}
  obtain ⟨ι, a, hstab, hker, hroot⟩ := ggKGTn_family_data hK hσ hp hp5 F hv
  refine le_antisymm ?_ ?_
  · intro g hg
    obtain ⟨hgG, hgC⟩ := Subgroup.mem_inf.1 hg
    have hfam : g ∈ familyCentralizer TwistTag.E6.tag L a := by
      rw [mem_familyCentralizer]
      refine ⟨hgG, fun i => ?_⟩
      obtain ⟨e, he, heq⟩ := hroot i
      have hmem : rootDiagUnit TwistTag.E6.tag (a i) ∈ V := ⟨e, he, heq⟩
      have hc : rootDiagUnit TwistTag.E6.tag (a i) * g = g * rootDiagUnit TwistTag.E6.tag (a i) :=
        hgC _ hmem
      calc rootDiagUnit TwistTag.E6.tag (a i) * g * (rootDiagUnit TwistTag.E6.tag (a i))⁻¹
          = g * rootDiagUnit TwistTag.E6.tag (a i) *
              (rootDiagUnit TwistTag.E6.tag (a i))⁻¹ := by rw [hc]
        _ = g := by group
    exact ggKGEx_familyCentralizer_le_torus a hker hstab hfam
  · intro g hg
    refine Subgroup.mem_inf.2 ⟨torusGroup_le_adjointGroup' hg, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨e, he, rfl⟩ := hz
    have hzH : F.g0⁻¹ * baseChangeGL (algebraMap K L)
        (e : ModGL TwistTag.E6.tag K) * F.g0 ∈ torusGroup TwistTag.E6.tag L :=
      (mem_twistedTorusOf.1 ((F.mem_iff e).1 he).2).1
    exact (mul_comm_of_mem_diagonalGroup (torusGroup_le_diagonalGroup hg)
      (torusGroup_le_diagonalGroup hzH)).symm

end CFSG.StandardType

end
