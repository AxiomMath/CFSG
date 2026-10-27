module

public import CFSG.RankThree.Chevalley.SteinbergCFOddG2QPlusCentralizers
public import CFSG.RankThree.Chevalley.SteinbergCEG2EvenSplitCentralizers

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ComponentClassification.UnbalancedCatalog CFSG.Timmesfeld.ExceptionalOrders
  CFSG.RankThree.QuadraticSL2 CFSG.RankThree.Classical
open scoped Pointwise commutatorElement

namespace EvenG2

section Matrix

variable {L : Type} [Field L]

@[expose] def evenQuadraticP [CharP L 2] (ω : L) : SL2 L :=
  ⟨!![ω, ω + 1; 1, 1], by
    rw [Matrix.det_fin_two_of, mul_one, mul_one, sub_add_cancel_left, CharTwo.neg_eq]⟩

theorem evenQuadraticP_mul_nSL [CharP L 2] (σ : L ≃+* L) {ω : L} (hσω : σ ω = ω + 1) :
    evenQuadraticP ω * nSL 1 = Matrix.SpecialLinearGroup.map (σ : L →+* L) (evenQuadraticP ω) := by
  have h11 : σ (ω + 1) = ω := by rw [map_add, hσω, map_one, add_assoc, CharTwo.add_self_eq_zero,
    add_zero]
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.map_apply_coe]
  fin_cases i <;> fin_cases j <;>
    simp [evenQuadraticP, nSL, Matrix.mul_apply, Fin.sum_univ_two, hσω, h11, CharTwo.neg_eq]

end Matrix

variable {K K₂ : Type} [Field K] [Finite K] [Field K₂] [Algebra K K₂]

theorem exists_frobenius_eq_add_one [CharP K₂ 2] (hdeg : Module.finrank K K₂ = 2)
    (σ : K₂ ≃+* K₂) (hσ : ∀ c, σ c = c ^ Nat.card K) :
    (∀ c, σ (σ c) = c) ∧ ∃ ω : K₂, σ ω = ω + 1 := by
  obtain ⟨hinv, -⟩ := exists_frobenius_eq_neg hdeg σ hσ
  obtain ⟨-, hord, -⟩ := quadratic_frobenius hdeg σ hσ
  have hne : σ ≠ 1 := fun h => by
    rw [h, orderOf_one] at hord
    exact absurd hord (by norm_num)
  obtain ⟨c, hc⟩ : ∃ c, σ c ≠ c := by
    by_contra h
    push Not at h
    exact hne (RingEquiv.ext fun x => by rw [h x]; rfl)
  set t := c + σ c with ht
  have ht0 : t ≠ 0 := fun h0 => hc (by
    have : σ c = -c := eq_neg_of_add_eq_zero_right h0
    rw [this, CharTwo.neg_eq])
  have hσt : σ t = t := by rw [ht, map_add, hinv, add_comm]
  refine ⟨hinv, c * t⁻¹, ?_⟩
  rw [map_mul, map_inv₀, hσt]
  field_simp
  rw [ht]
  ring_nf
  rw [show c * 2 = 0 by rw [show (2 : K₂) = 0 from CharTwo.two_eq_zero, mul_zero], zero_add]

theorem rootSL2_comap_fixed_eq_of_charTwo [CharP K₂ 2] (hdeg : Module.finrank K K₂ = 2)
    (σ : K₂ ≃+* K₂) (hσ : ∀ c, σ c = c ^ Nat.card K) {g z : ModGL .G2 K₂}
    (hg : g ∈ adjointGroup .G2 K₂)
    (hzdef : z = g * (Units.map (entrywiseHom (σ : K₂ →+* K₂)) g)⁻¹)
    (hz : z ∈ monomialSubgroup .G2 K₂)
    (hw : ∀ v : Fin Tag.G2.rank → ℤ, weylQuotientHom .G2 K₂ ⟨z, hz⟩ • v = -v)
    {α : Fin Tag.G2.rank → ℤ} (hα : IsRoot .G2 α) :
    ∃ P : GL (Fin 2) K₂,
      (rootRankOneGroup .G2 K₂ α ⊓ conjEntrywiseImage K g).comap (rootSL2 .G2 K₂ α) =
        (Matrix.SpecialLinearGroup.map (algebraMap K K₂)).range.map (conjSL P) ∧
      Subgroup.centralizer ((((rootRankOneGroup .G2 K₂ α ⊓ conjEntrywiseImage K g).comap
          (rootSL2 .G2 K₂ α)).map Matrix.SpecialLinearGroup.toGL : Subgroup (GL (Fin 2) K₂)) :
            Set (GL (Fin 2) K₂)) =
        (Matrix.GeneralLinearGroup.scalar (Fin 2)).range := by
  obtain ⟨hfin, -, -⟩ := quadratic_frobenius hdeg σ hσ
  have : Finite K₂ := hfin
  obtain ⟨M, hM⟩ := exists_semilinearConj_rootSL2 hz hw σ hα
  have hΓ := conjEntrywiseImage_eq_fixed σ hσ hg hzdef
  have hinv : ∀ c, σ (σ c) = c := (exists_frobenius_eq_neg hdeg σ hσ).1
  have hinj : Function.Injective (rootSL2 .G2 K₂ α) := rootSL2_injective_of_field α
  have hinvol : ∀ A, semilinearConj M σ (semilinearConj M σ A) = A := fun A => hinj (by
    rw [hM, hM, twistedEntrywise_twistedEntrywise (σ := (σ : K₂ →+* K₂)) hinv hzdef])
  have hfix : (semilinearConj M σ).eqLocus (MonoidHom.id _) =
      (rootRankOneGroup .G2 K₂ α ⊓ conjEntrywiseImage K g).comap (rootSL2 .G2 K₂ α) := by
    ext A
    change semilinearConj M σ A = A ↔
      rootSL2 .G2 K₂ α A ∈ rootRankOneGroup .G2 K₂ α ⊓ conjEntrywiseImage K g
    rw [hΓ]
    constructor
    · intro h
      refine ⟨⟨A, rfl⟩, (exceptional_Lang_root_rank_one_data .G2 K₂ α).2.2.2.2.1 A, ?_⟩
      change twistedEntrywise z (σ : K₂ →+* K₂) (rootSL2 .G2 K₂ α A) = rootSL2 .G2 K₂ α A
      rw [← hM, h]
    · rintro ⟨-, -, h⟩
      exact hinj (by rw [hM]; exact h)
  obtain ⟨P, -, hP, -, hcent⟩ :=
    even_quadratic_semilinear_SL2_fixed_matrix_group K K₂ hdeg σ hσ M hinvol
  refine ⟨P, ?_, ?_⟩
  · rw [← hfix]
    exact hP
  · rw [← hfix]
    exact hcent

theorem isSimpleGroup_of_rootSL2_comap_eq [CharP K 2] (hK4 : 4 ≤ Nat.card K)
    {α : Fin Tag.G2.rank → ℤ}
    {R : Subgroup (ModGL .G2 K₂)} (hR : R ≤ rootRankOneGroup .G2 K₂ α) {P : GL (Fin 2) K₂}
    (hRP : R.comap (rootSL2 .G2 K₂ α) =
      (Matrix.SpecialLinearGroup.map (algebraMap K K₂)).range.map (conjSL P)) :
    IsSimpleGroup R ∧ Group.IsPerfect R ∧ ∃ x y : R, x * y ≠ y * x := by
  have hSLinj : Function.Injective (Matrix.SpecialLinearGroup.map (n := Fin 2)
      (algebraMap K K₂)) := by
    intro A B h
    ext i j
    have h1 := congrArg (fun X : SL2 K₂ => (X : Matrix (Fin 2) (Fin 2) K₂) i j) h
    simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply] at h1
    exact (algebraMap K K₂).injective h1
  have hPinj : Function.Injective (conjSL P) := fun A B h => by
    have h1 := congrArg (conjSL P⁻¹) h
    rwa [← conjSL_mul, ← conjSL_mul, inv_mul_cancel, conjSL_one, conjSL_one] at h1
  have hinj : Function.Injective (rootSL2 .G2 K₂ α) := rootSL2_injective_of_field α
  have hmap : (R.comap (rootSL2 .G2 K₂ α)).map (rootSL2 .G2 K₂ α) = R := by
    rw [Subgroup.map_comap_eq]
    exact inf_of_le_right hR
  let e : SL2 K ≃* R :=
    ((((MonoidHom.ofInjective hSLinj).trans (Subgroup.equivMapOfInjective _ _ hPinj)).trans
      (MulEquiv.subgroupCongr hRP.symm)).trans
        (Subgroup.equivMapOfInjective _ _ hinj)).trans (MulEquiv.subgroupCongr hmap)
  have h4 := exists_finset_card_four hK4
  obtain ⟨-, hsimple, -⟩ :=
    CFSG.LinearGroups.linear_projective_simple (K := K) (n := 2) le_rfl (Or.inr h4)
  have : IsSimpleGroup (SL2 K) :=
    (CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := K)).symm.isSimpleGroup
  have : Group.IsPerfect (SL2 K) := CFSG.LinearGroups.special_linear_dimension_two_perfect h4
  refine ⟨e.symm.isSimpleGroup, Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective,
    e (uSL 1), e (vSL 1), fun h => uSL_mul_vSL_ne (K := K) ?_⟩
  rw [← map_mul, ← map_mul] at h
  exact e.injective h

theorem qplus_prime_element_centralizer_of_charTwo [CharP K 2] {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hpq : p ∣ Nat.card K + 1) (hdeg : Module.finrank K K₂ = 2) (σ : K₂ ≃+* K₂)
    (hσ : ∀ c, σ c = c ^ Nat.card K) {g z : ModGL .G2 K₂} (hg : g ∈ adjointGroup .G2 K₂)
    (hzdef : z = g * (Units.map (entrywiseHom (σ : K₂ →+* K₂)) g)⁻¹)
    (hz : z ∈ monomialSubgroup .G2 K₂)
    (hw : ∀ v : Fin Tag.G2.rank → ℤ, weylQuotientHom .G2 K₂ ⟨z, hz⟩ • v = -v)
    (a : Fin Tag.G2.rank → K₂ˣ) (ha : orderOf (rootDiagUnit .G2 a) = p) :
    (rootCharKernel a = ∅ →
      conjEntrywiseImage K g ⊓ Subgroup.centralizer {rootDiagUnit .G2 a} =
        torusGroup .G2 K₂ ⊓ conjEntrywiseImage K g) ∧
    (rootCharKernel a ≠ ∅ → ∃ α : Fin Tag.G2.rank → ℤ, IsRoot .G2 α ∧
      rootCharKernel a = {α, -α} ∧
      ⁅conjEntrywiseImage K g ⊓ Subgroup.centralizer {rootDiagUnit .G2 a},
          conjEntrywiseImage K g ⊓ Subgroup.centralizer {rootDiagUnit .G2 a}⁆ =
        rootRankOneGroup .G2 K₂ α ⊓ conjEntrywiseImage K g ∧
      (conjEntrywiseImage K g ⊓ Subgroup.centralizer {rootDiagUnit .G2 a}) ⊓
          Subgroup.centralizer ((rootRankOneGroup .G2 K₂ α ⊓ conjEntrywiseImage K g :
            Subgroup (ModGL .G2 K₂)) : Set (ModGL .G2 K₂)) =
        (Subgroup.center (conjEntrywiseImage K g ⊓
          Subgroup.centralizer {rootDiagUnit .G2 a} : Subgroup (ModGL .G2 K₂))).map
          (conjEntrywiseImage K g ⊓ Subgroup.centralizer {rootDiagUnit .G2 a}).subtype ∧
      (Subgroup.center (conjEntrywiseImage K g ⊓
          Subgroup.centralizer {rootDiagUnit .G2 a} : Subgroup (ModGL .G2 K₂))).map
          (conjEntrywiseImage K g ⊓ Subgroup.centralizer {rootDiagUnit .G2 a}).subtype ≤
        torusGroup .G2 K₂) := by
  classical
  obtain ⟨hfin, -, -⟩ := quadratic_frobenius hdeg σ hσ
  have : Finite K₂ := hfin
  have : CharP K₂ 2 := charP_of_injective_algebraMap (algebraMap K K₂).injective 2
  have hq2 := natCard_eq_sq_of_finrank_eq_two hdeg
  have hq1 : 1 ≤ Nat.card K := Nat.card_pos
  have hpq₂ : p ∣ Nat.card K₂ - 1 := by
    refine hpq.trans ⟨Nat.card K - 1, ?_⟩
    rw [hq2]
    zify [hq1, Nat.one_le_pow 2 _ hq1]
    ring
  have hq4 : 4 ≤ Nat.card K := by
    have := Nat.le_of_dvd (Nat.succ_pos _) hpq
    have := five_le_of_prime_of_three_lt hp hp3
    omega
  have hΓ := conjEntrywiseImage_eq_fixed σ hσ hg hzdef
  have hΓC : conjEntrywiseImage K g ≤ adjointGroup .G2 K₂ := by
    rw [hΓ]
    exact inf_le_left
  have hDM : conjEntrywiseImage K g ⊓ Subgroup.centralizer {rootDiagUnit .G2 a} =
      conjEntrywiseImage K g ⊓ toralCentralizer .G2 K₂ a := by
    rw [toralCentralizer, ← inf_assoc, inf_of_le_left hΓC]
  have hcases := toral_centralizer_cases_G2_of_charTwo K₂ hp hp3 hpq₂ a ha
  set D := conjEntrywiseImage K g ⊓ Subgroup.centralizer {rootDiagUnit .G2 a} with hDdef
  constructor
  · intro hker
    rcases hcases with ⟨-, hMH⟩ | ⟨α, -, hα, -⟩
    · rw [hDM, hMH, inf_comm]
    · exact absurd (hα.symm.trans hker) (Set.insert_nonempty _ _).ne_empty
  · intro hker
    rcases hcases with ⟨hker', -⟩ | ⟨α, hαr, hkerα, hMQ, hMset, hMcomm, hMZ, hMZH⟩
    · exact absurd hker' hker
    set M := toralCentralizer .G2 K₂ a with hMdef
    have hL : rootRankOneGroup .G2 K₂ α = rootSubgroup .G2 K₂ α ⊔ rootSubgroup .G2 K₂ (-α) :=
      (exceptional_Lang_root_rank_one_torus_transport .G2 K₂ hαr).1
    rw [← hL] at hMQ hMset hMcomm hMZ
    obtain ⟨P, hPfix, hPcent⟩ :=
      rootSL2_comap_fixed_eq_of_charTwo hdeg σ hσ hg hzdef hz hw hαr
    set R := rootRankOneGroup .G2 K₂ α ⊓ conjEntrywiseImage K g with hRdef
    have hRperf : ⁅R, R⁆ = R := Subgroup.isPerfect_iff.1
      (isSimpleGroup_of_rootSL2_comap_eq hq4 inf_le_left hPfix).2.1
    have hQM : rootRankOneGroup .G2 K₂ α ≤ M := by
      rw [hMQ]
      exact le_sup_right
    have hDle : D ≤ M := by
      rw [hDM]
      exact inf_le_right
    have hRD : R ≤ D := by
      intro r hr
      rw [hDM]
      exact ⟨hr.2, hQM hr.1⟩
    have hcentM : ∀ y ∈ D, (∀ r ∈ R, r * y = y * r) → y ∈ (Subgroup.center M).map M.subtype := by
      intro y hyD hyR
      have hyM := hDle hyD
      have hyset : y ∈ (torusGroup .G2 K₂ : Set (ModGL .G2 K₂)) *
          (rootRankOneGroup .G2 K₂ α : Set (ModGL .G2 K₂)) := by
        rw [← hMset]
        exact hyM
      have hyQ := commute_rootSL2_of_commute_fixed hαr hPcent hyset
        (fun A hA => (hyR _ hA).symm)
      rw [← hMZ]
      refine ⟨hyM, Subgroup.mem_centralizer_iff.2 fun q hq => ?_⟩
      obtain ⟨A, rfl⟩ := MonoidHom.mem_range.1 hq
      exact (hyQ A).symm
    have hcentD : D ⊓ Subgroup.centralizer (R : Set (ModGL .G2 K₂)) =
        (Subgroup.center D).map D.subtype := by
      refine le_antisymm (fun y hy => ?_) ?_
      · obtain ⟨hyD, hyC⟩ := Subgroup.mem_inf.1 hy
        obtain ⟨m, hm, rfl⟩ := hcentM y hyD fun r hr => Subgroup.mem_centralizer_iff.1 hyC r hr
        refine ⟨⟨m, hyD⟩, Subgroup.mem_center_iff.2 fun d => Subtype.ext ?_, rfl⟩
        have h1 := congrArg Subtype.val (Subgroup.mem_center_iff.1 hm ⟨d, hDle d.2⟩)
        exact h1
      · rintro _ ⟨d, hd, rfl⟩
        refine ⟨d.2, Subgroup.mem_centralizer_iff.2 fun r hr => ?_⟩
        exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hd ⟨r, hRD hr⟩)
    have hZH : (Subgroup.center D).map D.subtype ≤ torusGroup .G2 K₂ := by
      rw [← hcentD]
      intro y hy
      obtain ⟨hyD, hyC⟩ := Subgroup.mem_inf.1 hy
      exact hMZH (hcentM y hyD fun r hr => Subgroup.mem_centralizer_iff.1 hyC r hr)
    refine ⟨α, hαr, hkerα, le_antisymm (le_inf ?_ ?_)
      (hRperf.symm.le.trans (Subgroup.commutator_mono hRD hRD)), hcentD, hZH⟩
    · rw [← hMcomm]
      exact Subgroup.commutator_mono hDle hDle
    · exact (commutator_self_le D).trans inf_le_left

end EvenG2

open EvenG2

theorem even_G2_qplus_torus_and_fixed_root_centralizers (K : Type) [Field K] [Finite K]
    [CharP K 2] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpq : p ∣ Nat.card K + 1)
    (K₂ : Type) [Field K₂] [Algebra K K₂] (hdeg : Module.finrank K K₂ = 2) (σ : K₂ ≃+* K₂)
    (hσ : ∀ c, σ c = c ^ Nat.card K) :
    ∃ g z : ModGL .G2 K₂, g ∈ adjointGroup .G2 K₂ ∧ z ∈ adjointGroup .G2 K₂ ∧
      z = g * (Units.map (entrywiseHom (σ : K₂ →+* K₂)) g)⁻¹ ∧
      (∃ hz : z ∈ monomialSubgroup .G2 K₂,
        ∀ v : Fin Tag.G2.rank → ℤ, weylQuotientHom .G2 K₂ ⟨z, hz⟩ • v = -v) ∧
      conjEntrywiseImage K g =
        adjointGroup .G2 K₂ ⊓ (twistedEntrywise z (σ : K₂ →+* K₂)).eqLocus (MonoidHom.id _) ∧
      (∀ y, twistedEntrywise z (σ : K₂ →+* K₂) (twistedEntrywise z (σ : K₂ →+* K₂) y) = y) ∧
      Nonempty ((torusGroup .G2 K₂ ⊓ conjEntrywiseImage K g : Subgroup (ModGL .G2 K₂)) ≃*
        Multiplicative (ZMod (Nat.card K + 1)) × Multiplicative (ZMod (Nat.card K + 1))) ∧
      Odd (Nat.card (torusGroup .G2 K₂ ⊓ conjEntrywiseImage K g : Subgroup (ModGL .G2 K₂))) ∧
      (∃ S : Sylow p (conjEntrywiseImage K g), (S : Subgroup (conjEntrywiseImage K g)) ≤
        (torusGroup .G2 K₂ ⊓ conjEntrywiseImage K g).subgroupOf (conjEntrywiseImage K g)) ∧
      (∃ E : Subgroup (ModGL .G2 K₂), (∀ h, h ∈ E ↔ h ∈ torusGroup .G2 K₂ ∧ h ^ p = 1) ∧
        E ≤ torusGroup .G2 K₂ ⊓ conjEntrywiseImage K g ∧ Nat.card E = p ^ 2 ∧
        (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧ ∀ x ∈ E, x ^ p = 1) ∧
      (∀ α : Fin Tag.G2.rank → ℤ, IsRoot .G2 α → ∃ P : GL (Fin 2) K₂,
        (rootRankOneGroup .G2 K₂ α ⊓ conjEntrywiseImage K g).comap (rootSL2 .G2 K₂ α) =
          (Matrix.SpecialLinearGroup.map (algebraMap K K₂)).range.map (conjSL P) ∧
        IsSimpleGroup
          (rootRankOneGroup .G2 K₂ α ⊓ conjEntrywiseImage K g : Subgroup (ModGL .G2 K₂)) ∧
        Group.IsPerfect
          (rootRankOneGroup .G2 K₂ α ⊓ conjEntrywiseImage K g : Subgroup (ModGL .G2 K₂)) ∧
        ∃ x y : (rootRankOneGroup .G2 K₂ α ⊓ conjEntrywiseImage K g : Subgroup (ModGL .G2 K₂)),
          x * y ≠ y * x) ∧
      (∀ x ∈ torusGroup .G2 K₂ ⊓ conjEntrywiseImage K g,
        ∃! a : Fin Tag.G2.rank → K₂ˣ, rootDiagUnit .G2 a = x) ∧
      ∀ a : Fin Tag.G2.rank → K₂ˣ,
        rootDiagUnit .G2 a ∈ torusGroup .G2 K₂ ⊓ conjEntrywiseImage K g →
        orderOf (rootDiagUnit .G2 a) = p →
        (rootCharKernel a = ∅ →
          conjEntrywiseImage K g ⊓ Subgroup.centralizer {rootDiagUnit .G2 a} =
            torusGroup .G2 K₂ ⊓ conjEntrywiseImage K g) ∧
        (rootCharKernel a ≠ ∅ → ∃ α : Fin Tag.G2.rank → ℤ, IsRoot .G2 α ∧
          rootCharKernel a = {α, -α} ∧
          ⁅conjEntrywiseImage K g ⊓ Subgroup.centralizer {rootDiagUnit .G2 a},
              conjEntrywiseImage K g ⊓ Subgroup.centralizer {rootDiagUnit .G2 a}⁆ =
            rootRankOneGroup .G2 K₂ α ⊓ conjEntrywiseImage K g ∧
          (conjEntrywiseImage K g ⊓ Subgroup.centralizer {rootDiagUnit .G2 a}) ⊓
              Subgroup.centralizer ((rootRankOneGroup .G2 K₂ α ⊓ conjEntrywiseImage K g :
                Subgroup (ModGL .G2 K₂)) : Set (ModGL .G2 K₂)) =
            (Subgroup.center (conjEntrywiseImage K g ⊓
              Subgroup.centralizer {rootDiagUnit .G2 a} : Subgroup (ModGL .G2 K₂))).map
              (conjEntrywiseImage K g ⊓ Subgroup.centralizer {rootDiagUnit .G2 a}).subtype ∧
          (Subgroup.center (conjEntrywiseImage K g ⊓
              Subgroup.centralizer {rootDiagUnit .G2 a} : Subgroup (ModGL .G2 K₂))).map
              (conjEntrywiseImage K g ⊓ Subgroup.centralizer {rootDiagUnit .G2 a}).subtype ≤
            torusGroup .G2 K₂) ∧
        Odd (Nat.card (Subgroup.center (conjEntrywiseImage K g ⊓
          Subgroup.centralizer {rootDiagUnit .G2 a} : Subgroup (ModGL .G2 K₂)))) := by
  classical
  obtain ⟨hfin, -, -⟩ := quadratic_frobenius hdeg σ hσ
  have : Finite K₂ := hfin
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K₂ 2 := charP_of_injective_algebraMap (algebraMap K K₂).injective 2
  have : Finite (Module.End K₂ (RootModule .G2 K₂)) := Module.finite_of_finite K₂
  have hq2 := natCard_eq_sq_of_finrank_eq_two hdeg
  have hq1 : 1 ≤ Nat.card K := Nat.card_pos
  have hdvd₂ : Nat.card K + 1 ∣ Nat.card K₂ - 1 := by
    refine ⟨Nat.card K - 1, ?_⟩
    rw [hq2]
    zify [hq1, Nat.one_le_pow 2 _ hq1]
    ring
  have hq4 : 4 ≤ Nat.card K := by
    have := Nat.le_of_dvd (Nat.succ_pos _) hpq
    have := five_le_of_prime_of_three_lt hp hp3
    omega
  obtain ⟨hinv, ω, hσω⟩ := exists_frobenius_eq_add_one hdeg σ hσ
  have hPn := evenQuadraticP_mul_nSL σ hσω
  have hρC : ∀ (β : Fin Tag.G2.rank → ℤ) (A : SL2 K₂),
      rootSL2 .G2 K₂ β A ∈ adjointGroup .G2 K₂ :=
    fun β A => (exceptional_Lang_root_rank_one_data .G2 K₂ β).2.2.2.2.1 A
  obtain ⟨g, hgdef⟩ : ∃ g : ModGL .G2 K₂, g = rootSL2 .G2 K₂ g2a (evenQuadraticP ω)⁻¹ *
      rootSL2 .G2 K₂ g2v (evenQuadraticP ω)⁻¹ := ⟨_, rfl⟩
  have hg : g ∈ adjointGroup .G2 K₂ := by
    rw [hgdef]
    exact mul_mem (hρC _ _) (hρC _ _)
  obtain ⟨z, hzdef⟩ : ∃ z, z = g * (Units.map (entrywiseHom (σ : K₂ →+* K₂)) g)⁻¹ := ⟨_, rfl⟩
  have hzeq : z = rootWeylSL2 .G2 K₂ g2a 1 * rootWeylSL2 .G2 K₂ g2v 1 := by
    rw [hzdef, hgdef]
    exact rootSL2_pair_mul_entrywise_inv_eq (σ : K₂ →+* K₂) hPn
  obtain ⟨hzN, hw⟩ : ∃ hz : z ∈ monomialSubgroup .G2 K₂,
      ∀ v : Fin Tag.G2.rank → ℤ, weylQuotientHom .G2 K₂ ⟨z, hz⟩ • v = -v := by
    rw [hzeq]
    exact rootWeylSL2_pair_mem_monomial _
  have hzC : z ∈ adjointGroup .G2 K₂ := by
    rw [hzeq]
    exact mul_mem (hρC _ _) (hρC _ _)
  have hΓ := conjEntrywiseImage_eq_fixed σ hσ hg hzdef
  have hT := torusGroup_inf_eq_torusTorsion hzN hw (σ : K₂ →+* K₂) hσ hΓ
  have hHcomm := (triangular_borel_structure.{0, 0} .G2 K₂).1
  have hTΓ : torusGroup .G2 K₂ ⊓ conjEntrywiseImage K g ≤ conjEntrywiseImage K g := inf_le_right
  have hcardΓ : Nat.card (conjEntrywiseImage K g) = CFSG.Open.ordG2 (Nat.card K) := by
    rw [natCard_conjEntrywiseImage, card_adjointGroup_G2]
  have hcardT : Nat.card (torusGroup .G2 K₂ ⊓ conjEntrywiseImage K g : Subgroup (ModGL .G2 K₂)) =
      (Nat.card K + 1) ^ 2 := by
    rw [hT]
    exact natCard_torusTorsion hdvd₂
  have hidx : ¬ p ∣ ((torusGroup .G2 K₂ ⊓ conjEntrywiseImage K g).subgroupOf
      (conjEntrywiseImage K g)).index := by
    refine not_dvd_of_sq_mul_eq_ordG2 hq1 hp hp3 hpq ?_
    rw [← hcardΓ, ← hcardT, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTΓ).toEquiv]
    exact Subgroup.card_mul_index _
  have hTodd : Odd (Nat.card (torusGroup .G2 K₂ ⊓ conjEntrywiseImage K g :
      Subgroup (ModGL .G2 K₂))) := by
    rw [hcardT]
    exact (even_card_of_charTwo (K := K)).add_one.pow
  refine ⟨g, z, hg, hzC, hzdef, ⟨hzN, hw⟩, hΓ,
    twistedEntrywise_twistedEntrywise (σ := (σ : K₂ →+* K₂)) hinv hzdef, ?_, hTodd,
    exists_sylow_le_of_not_dvd_index hidx, ?_, fun α hα => ?_, fun x hx => ?_,
    fun a hadT ha => ?_⟩
  · rw [hT]
    exact nonempty_torusTorsion_mulEquiv hdvd₂
  · have : NeZero p := ⟨hp.ne_zero⟩
    refine ⟨torusTorsion K₂ p, fun h => mem_torusTorsion_iff, ?_, natCard_torusTorsion
      (hpq.trans hdvd₂), fun x hx y hy => hHcomm x (torusTorsion_le_torusGroup p hx) y
        (torusTorsion_le_torusGroup p hy), fun x hx => (mem_torusTorsion_iff.1 hx).2⟩
    rw [hT]
    exact torusTorsion_mono hpq
  · obtain ⟨P, hP, -⟩ := rootSL2_comap_fixed_eq_of_charTwo hdeg σ hσ hg hzdef hzN hw hα
    exact ⟨P, hP, isSimpleGroup_of_rootSL2_comap_eq hq4 inf_le_left hP⟩
  · obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hx.1
    exact ⟨a, rfl, fun b hb => rootDiagUnit_injective hb⟩
  · obtain ⟨h1, h2⟩ := qplus_prime_element_centralizer_of_charTwo hp hp3 hpq hdeg σ hσ hg hzdef
      hzN hw a ha
    refine ⟨h1, h2, ?_⟩
    set D := conjEntrywiseImage K g ⊓ Subgroup.centralizer {rootDiagUnit .G2 a} with hDdef
    have hZT : (Subgroup.center D).map D.subtype ≤
        torusGroup .G2 K₂ ⊓ conjEntrywiseImage K g := by
      by_cases hker : rootCharKernel a = ∅
      · exact (Subgroup.map_subtype_le _).trans (h1 hker).le
      · obtain ⟨-, -, -, -, -, hZH⟩ := h2 hker
        exact le_inf hZH ((Subgroup.map_subtype_le _).trans inf_le_left)
    have hdvd : Nat.card (Subgroup.center D) ∣
        Nat.card (torusGroup .G2 K₂ ⊓ conjEntrywiseImage K g : Subgroup (ModGL .G2 K₂)) := by
      rw [← Subgroup.card_map_of_injective D.subtype_injective]
      exact Subgroup.card_dvd_of_le hZT
    exact Odd.of_dvd_nat hTodd hdvd

end CFSG.RankThree.Chevalley
