module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148HRow425G2

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148H

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.Ronan148S
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp (NoThreeCover)
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.PartTwo.Sec11
open scoped MatrixGroups

section G2

open CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof


variable {F : Type} [Field F]

theorem eq_one_of_mem_center_sl2_of_pow_three {B : SL(2, F)}
    (hB : B ∈ Subgroup.center SL(2, F)) (hB3 : B ^ 3 = 1) : B = 1 := by
  obtain ⟨r, hr, hrB⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hB
  rw [Fintype.card_fin] at hr
  have hr3 : r ^ 3 = 1 := by
    have h := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 0) hB3
    simp only [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one,
      Matrix.one_apply_eq] at h
    rw [← hrB, ← map_pow, Matrix.scalar_apply, Matrix.diagonal_apply_eq] at h
    exact h
  have hr1 : r = 1 := by
    have h' : r ^ 3 = r * r ^ 2 := by ring
    rw [hr, mul_one, hr3] at h'
    exact h'.symm
  apply Subtype.ext
  rw [← hrB, hr1, map_one, Matrix.SpecialLinearGroup.coe_one]

theorem false_of_threeB_odd [Finite F] (hchar : ringChar F ≠ 3) (h4 : 4 ≤ Nat.card F)
    {z : adjointGroup .G2 F} (hzM : z ∈ g2LongSL2 F) (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1)
    {J : Subgroup (adjointGroup .G2 F)}
    (hJC : J ≤ Subgroup.centralizer ({z} : Set (adjointGroup .G2 F)))
    (hJq : CFSG.IsQuasisimple J) (hzJ : z ∈ J) : False := by
  obtain ⟨hcomm, -⟩ := g2ThreeBCent_holds F hchar h4 z hzM hz3 hz1
  have hJS : J ≤ g2ShortSL2 F :=
    le_of_commutators_mem hJC (Subgroup.isPerfect_iff.mp hJq.1) hcomm
  have hzS := hJS hzJ
  obtain ⟨e⟩ := nonempty_mulEquiv_g2ShortSL2 (K := F)
  set B := e.symm ⟨z, hzS⟩ with hB
  have heB : e B = ⟨z, hzS⟩ := MulEquiv.apply_symm_apply e _
  have hBc : B ∈ Subgroup.center SL(2, F) := by
    rw [Subgroup.mem_center_iff]
    intro A
    apply e.injective
    rw [map_mul, map_mul, heB]
    exact Subtype.ext (g2Short_commute_g2Long (e A).2 hzM)
  have hB3 : B ^ 3 = 1 := by
    rw [hB, ← map_pow]
    have : (⟨z, hzS⟩ : g2ShortSL2 F) ^ 3 = 1 := Subtype.ext (by
      rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
      exact hz3)
    rw [this, map_one]
  have h1 := eq_one_of_mem_center_sl2_of_pow_three hBc hB3
  apply hz1
  have : (⟨z, hzS⟩ : g2ShortSL2 F) = 1 := by rw [← heB, h1, map_one]
  exact congrArg Subtype.val this

theorem isSLThreePiAt_of_threeA_two [Finite F] {p f : ℕ} [Fact p.Prime]
    (hF : Nat.card F = p ^ f) (hmod : p ^ f % 3 = 2) (hq2 : p ^ f ≠ 2)
    {z : adjointGroup .G2 F} (hzS : z ∈ g2ShortSL2 F) (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1)
    {J : Subgroup (adjointGroup .G2 F)}
    (hJC : J ≤ Subgroup.centralizer ({z} : Set (adjointGroup .G2 F)))
    (hJq : CFSG.IsQuasisimple J)
    (hJs : (J.subgroupOf (Subgroup.centralizer ({z} : Set (adjointGroup .G2 F)))).IsSubnormal) :
    IsSLThreePiAt J (p ^ f) := by
  have : Fintype F := Fintype.ofFinite F
  have hf : f ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hmod
    norm_num at hmod
  have : CharP F p := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hF])
  obtain ⟨L, _, _, _, -, hdeg, -⟩ := exists_quadratic_ext' F
  have : CharP L p := charP_of_injective_algebraMap (algebraMap F L).injective p
  have h3 : 3 ∣ Nat.card F + 1 := by
    rw [hF]
    omega
  obtain ⟨e⟩ := KS11Lie7Proof.nonempty_centralizer_mulEquiv_statedSU hF h3 hdeg hzS hz3 hz1
  have hL : Nat.card L = (p ^ f) ^ 2 := by rw [natCard_quadratic hdeg, hF]
  have hq : ((3 : ℕ), p ^ f) ≠ (3, 2) := fun h => hq2 (Prod.mk.inj h).2
  obtain ⟨hSU, -⟩ := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hL le_rfl hq
  have hCq : CFSG.IsQuasisimple (Subgroup.centralizer ({z} : Set (adjointGroup .G2 F))) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hSU
  have heq := eq_of_le_of_isQuasisimple hJC le_rfl hJs hCq hJq
  exact ⟨L, inferInstance, inferInstance, Or.inr ⟨hL, hmod, ⟨(MulEquiv.subgroupCongr heq).trans e⟩⟩⟩

theorem isSLThreePiAt_of_threeA_one [Finite F] (hmod : Nat.card F % 3 = 1)
    {z : adjointGroup .G2 F} (hzS : z ∈ g2ShortSL2 F) (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1)
    {J : Subgroup (adjointGroup .G2 F)}
    (hJC : J ≤ Subgroup.centralizer ({z} : Set (adjointGroup .G2 F)))
    (hJq : CFSG.IsQuasisimple J)
    (hJs : (J.subgroupOf (Subgroup.centralizer ({z} : Set (adjointGroup .G2 F)))).IsSubnormal) :
    IsSLThreePiAt J (Nat.card F) := by
  have h31 : 3 ∣ Nat.card F - 1 := by omega
  obtain ⟨m, φ, hφinj, hNC, hcomm⟩ := exists_sl3_threeA h31 hzS hz3 hz1
  set e := MulAut.conj m with he'
  obtain ⟨hJ'C, hJ's⟩ := map_le_centralizer_isSubnormal e hJC hJs
  have hez : e z = m * z * m⁻¹ := rfl
  rw [hez] at hJ'C hJ's
  have eJ : J ≃* J.map (e : adjointGroup .G2 F →* adjointGroup .G2 F) :=
    J.equivMapOfInjective _ e.injective
  have hJ'q := CFSG.LocalCores.isQuasisimple_of_mulEquiv eJ hJq
  have hNq : CFSG.IsQuasisimple φ.range := CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (MonoidHom.ofInjective hφinj)
    (CFSG.RankThree.Classical2.isQuasisimple_specialLinearGroup (by norm_num))
  have hJ'N := le_of_commutators_mem hJ'C (Subgroup.isPerfect_iff.mp hJ'q.1) hcomm
  have heq := eq_of_le_of_isQuasisimple hJ'N hNC hJ's hNq hJ'q
  exact ⟨F, inferInstance, inferInstance, Or.inl ⟨rfl, hmod, ⟨eJ.trans
    ((MulEquiv.subgroupCongr heq).trans ((MonoidHom.ofInjective hφinj).symm.trans
      (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F)))⟩⟩⟩

theorem isSLThreePiAt_g2_prime [Finite F] {p : ℕ} [Fact p.Prime] (hp3 : 3 < p)
    (hF : Nat.card F = p) (z : adjointGroup .G2 F) (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1)
    (J : Subgroup (adjointGroup .G2 F))
    (hJC : J ≤ Subgroup.centralizer ({z} : Set (adjointGroup .G2 F)))
    (hJq : CFSG.IsQuasisimple J)
    (hJs : (J.subgroupOf (Subgroup.centralizer ({z} : Set (adjointGroup .G2 F)))).IsSubnormal)
    (hzJ : z ∈ J) : IsSLThreePiAt J p := by
  have : Fintype F := Fintype.ofFinite F
  have : CharP F p := charP_of_card_eq_prime_pow (p := p) (f := 1)
    (by rw [← Nat.card_eq_fintype_card, hF, pow_one])
  have hchar : ringChar F ≠ 3 := by
    rw [ringChar.eq F p]
    omega
  have h4 : 4 ≤ Nat.card F := by omega
  obtain ⟨g, hg⟩ := KS11Lie7Proof.g2ThreeConjSL2_holds F hchar h4 z hz3 hz1
  set e := MulAut.conj g with he'
  obtain ⟨hJ'C, hJ's⟩ := map_le_centralizer_isSubnormal e hJC hJs
  have eJ : J ≃* J.map (e : adjointGroup .G2 F →* adjointGroup .G2 F) :=
    J.equivMapOfInjective _ e.injective
  have hJ'q := CFSG.LocalCores.isQuasisimple_of_mulEquiv eJ hJq
  have hez : e z = g * z * g⁻¹ := rfl
  have hz'3 : e z ^ 3 = 1 := by rw [← map_pow, hz3, map_one]
  have hz'1 : e z ≠ 1 := by
    rw [Ne, map_eq_one_iff _ e.injective]
    exact hz1
  have hz'J : e z ∈ J.map (e : adjointGroup .G2 F →* adjointGroup .G2 F) := ⟨z, hzJ, rfl⟩
  refine isSLThreePiAt_of_mulEquiv eJ ?_
  rcases hg with hS | hM
  · rw [← hez] at hS
    have hp : p % 3 = 1 ∨ p % 3 = 2 := by
      have h3p : ¬ 3 ∣ p := fun h =>
        absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_three (Fact.out : p.Prime)).mp h)
          (by omega)
      omega
    rcases hp with h1 | h2
    · have h := isSLThreePiAt_of_threeA_one (by rw [hF]; exact h1) hS hz'3 hz'1 hJ'C hJ'q hJ's
      rwa [hF] at h
    · have h := isSLThreePiAt_of_threeA_two (p := p) (f := 1) (by rw [hF, pow_one])
        (by rw [pow_one]; exact h2) (by rw [pow_one]; omega) hS hz'3 hz'1 hJ'C hJ'q hJ's
      rwa [pow_one] at h
  · rw [← hez] at hM
    exact (false_of_threeB_odd hchar h4 hM hz'3 hz'1 hJ'C hJ'q hz'J).elim

theorem noThreeCover_adjointQuotient_g2_of_five [Finite F] (h5 : 5 ≤ Nat.card F) :
    NoThreeCover (AdjointQuotient .G2 F) := by
  have hM := (CFSG.LieType.Steinberg.CentralExt.AdjointClosed.g2_hopfMultiplier h5).2
  haveI : Finite (CFSG.Open.griessHopfMultiplier (AdjointQuotient .G2 F)) :=
    Finite.of_subsingleton
  have h1 : Nat.card (CFSG.Open.griessHopfMultiplier (AdjointQuotient .G2 F)) = 1 :=
    Nat.card_eq_one_iff_unique.mpr ⟨hM, ⟨1⟩⟩
  exact Ronan148L.noThreeCover_of_hopf (MulEquiv.refl _) (by rw [h1]; norm_num)

end G2

section Row


theorem rowOf425_g2_prime : ∀ (p : ℕ) [Fact p.Prime], 3 < p → ∀ q : TauCeti.PrimePower,
    q.p = p → q.exponent = 1 → ∀ hq : (TauCeti.LieTypeIndex.G2 q).Valid,
      RowOf425 (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group := by
  intro p _ hp3 q hqp hq1 hq S _ _ _ _ ⟨eSX⟩
  have hp2 : q.p ≠ 2 := by omega
  have h3q : 3 ≤ q.p ^ q.exponent := by
    rw [hq1, pow_one]
    omega
  obtain ⟨F, _, _, hF, ⟨eA⟩⟩ := CFSG.TauCetiBridge.untwistedModel_of_bridge
    CFSG.TauCetiBridge.untwistedBridge_G2 q hq hp2 eSX
  have hFp : Nat.card F = p := by rw [hF, hqp, hq1, pow_one]
  have hp5 : 5 ≤ p := by
    rcases Nat.lt_or_ge p 5 with h | h
    · have h4 : p = 4 := by omega
      exact absurd (h4 ▸ (Fact.out : p.Prime)) (by norm_num)
    · exact h
  refine row425_of_three (eA.trans (adjointQuotientEquivG2 F))
    (NoThreeCover.of_mulEquiv eA (noThreeCover_adjointQuotient_g2_of_five (by rw [hFp]; exact hp5)))
    (p := q.p) (f := q.exponent) ?_ ?_
  · intro X _ ⟨eXS⟩
    exact Or.inl ⟨⟨q.prime_p, q.exponent_pos, rfl, h3q⟩,
      CFSG.TauCetiBridge.untwistedModel_of_bridge CFSG.TauCetiBridge.untwistedBridge_G2 q hq hp2
        (eXS.trans eSX)⟩
  · intro z hz3 hz1 J hJC hJq hJs hzJ
    rw [hqp, hq1, pow_one]
    exact isSLThreePiAt_g2_prime hp3 hFp z hz3 hz1 J hJC hJq hJs hzJ

end Row

end CFSG.RankThree.PartTwo.Sec4.Ronan148H
