module

public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergTrialityHolds

public section

namespace CFSG.OddTranspositions.PartFour.ExtTrialityOrthFour

open CFSG.StandardType CFSG.StandardType.Triality
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.RankThree.PartOne.AUTSL
  CFSG.ComponentClassification.OuterAutomorphisms
open scoped Pointwise

variable {K : Type} [Field K] [Finite K] [CharP K 2]

section Families

private noncomputable abbrev thetaP : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)) :=
  MulAut.congr projEquiv8 (theta : MulAut (Om8 K))

private abbrev families :
    Set (Set (Subgroup (matrixProjectiveDerived (coordinateQuadPlus 4 K)))) :=
  MulAction.orbit (MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)))
    (projectivePointFamily (coordinateQuadPlus 4 K))

private theorem thetaP_pow_three : (thetaP (K := K)) ^ 3 = 1 := by
  rw [thetaP, ← map_pow, theta_cube, map_one]

private theorem thetaP_sq : (thetaP (K := K)) ^ 2 = (thetaP (K := K))⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← pow_succ, thetaP_pow_three])

private theorem mem_families
    {x : Set (Subgroup (matrixProjectiveDerived (coordinateQuadPlus 4 K)))} :
    x ∈ families (K := K) ↔
      ∃ k < 3, x = thetaP (K := K) ^ k • projectivePointFamily (coordinateQuadPlus 4 K) := by
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨k, hk⟩ := exists_pow_smul_pointFamily a
    refine ⟨k % 3, Nat.mod_lt _ (by norm_num), ?_⟩
    change a • _ = _
    rw [hk, ← pow_eq_pow_mod k (thetaP_pow_three (K := K))]
  · rintro ⟨k, -, rfl⟩
    exact MulAction.mem_orbit _ _

private theorem conjAct_smul_family (g : similarityPairs (coordinateQuadPlus 4 K)) :
    MulAut.congr projEquiv8 (conjAct _ g) • projectivePointFamily (coordinateQuadPlus 4 K) =
      projectivePointFamily (coordinateQuadPlus 4 K) := by
  have h := congr_conjAct_mem_image g
  rw [← pointFamilyAut_eq_image] at h
  exact (mem_projectivePointFamilyAut_iff _ _).1 h

private theorem conj_smul_family (w : matrixProjectiveDerived (coordinateQuadPlus 4 K)) :
    MulAut.conj w • projectivePointFamily (coordinateQuadPlus 4 K) =
      projectivePointFamily (coordinateQuadPlus 4 K) := by
  obtain ⟨g, hg⟩ := exists_pair_of_mem_inner (K := K) ⟨projEquiv8.symm w, rfl⟩
  have h := conjAct_smul_family g
  rwa [hg, congr_conj, MulEquiv.apply_symm_apply] at h

private theorem conj_smul_mem_families (w : matrixProjectiveDerived (coordinateQuadPlus 4 K))
    {x : Set (Subgroup (matrixProjectiveDerived (coordinateQuadPlus 4 K)))}
    (hx : x ∈ families (K := K)) : MulAut.conj w • x = x := by
  obtain ⟨k, -, rfl⟩ := mem_families.1 hx
  have e : MulAut.conj w * thetaP (K := K) ^ k =
      thetaP ^ k * MulAut.conj ((thetaP (K := K) ^ k)⁻¹ w) := by
    ext y
    simp [MulAut.conj_apply]
  rw [smul_smul, e, mul_smul, conj_smul_family]

theorem exists_graphHom : ∃ E : MulAut (Om8 K) →* Equiv.Perm (Fin 3),
    inner (Om8 K) ≤ E.ker ∧ E theta ≠ 1 ∧ E (AutOm.plusRefl (K := K) one_le_four) ≠ 1 := by
  classical
  set F := projectivePointFamily (coordinateQuadPlus 4 K) with hF
  set t := thetaP (K := K) with ht
  have h01 : t • F ≠ F := theta_smul_pointFamily_ne
  have h02 : t ^ 2 • F ≠ F := by
    rw [thetaP_sq]
    exact theta_inv_smul_pointFamily_ne
  have h12 : t • F ≠ t ^ 2 • F := by
    intro h
    rw [sq, mul_smul, smul_left_cancel_iff] at h
    exact h01 h.symm
  have hfam : families (K := K) = {F, t • F, t ^ 2 • F} := by
    ext x
    rw [mem_families]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨k, hk, rfl⟩
      interval_cases k
      · exact Or.inl (by rw [pow_zero, one_smul])
      · exact Or.inr (Or.inl (by rw [pow_one]))
      · exact Or.inr (Or.inr rfl)
    · rintro (rfl | rfl | rfl)
      · exact ⟨0, by norm_num, by rw [pow_zero, one_smul]⟩
      · exact ⟨1, by norm_num, by rw [pow_one]⟩
      · exact ⟨2, by norm_num, rfl⟩
  have hcard : (families (K := K)).ncard = 3 :=
    Set.ncard_eq_three.2 ⟨F, t • F, t ^ 2 • F, h01.symm, h02.symm, h12, hfam⟩
  have : Finite ↥(families (K := K)) :=
    (Set.finite_of_ncard_ne_zero (by rw [hcard]; norm_num)).to_subtype
  let e : ↥(families (K := K)) ≃ Fin 3 :=
    Finite.equivFinOfCardEq (by rw [Nat.card_coe_set_eq, hcard])
  let E₀ : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)) →* Equiv.Perm (Fin 3) :=
    (Equiv.permCongrHom e).toMonoidHom.comp
      (MulAction.toPermHom (MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)))
        ↥(families (K := K)))
  have hE₀ : ∀ a, E₀ a = 1 ↔ ∀ x ∈ families (K := K), a • x = x := by
    intro a
    constructor
    · intro h x hx
      have h1 := congrArg (fun p : Equiv.Perm (Fin 3) => e.symm (p (e ⟨x, hx⟩))) h
      simp only [E₀, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Equiv.permCongrHom_coe,
        Equiv.permCongr_apply, MulAction.toPermHom_apply, MulAction.toPerm_apply,
        Equiv.symm_apply_apply, Equiv.Perm.coe_one, id_eq] at h1
      exact congrArg Subtype.val h1
    · intro h
      ext i
      simp only [E₀, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Equiv.permCongrHom_coe,
        Equiv.permCongr_apply, MulAction.toPermHom_apply, MulAction.toPerm_apply,
        Equiv.Perm.coe_one, id_eq]
      have h1 : a • e.symm i = e.symm i :=
        Subtype.ext (by rw [MulAction.orbit.coe_smul]; exact h _ (e.symm i).2)
      rw [h1, Equiv.apply_symm_apply]
  refine ⟨E₀.comp (MulAut.congr projEquiv8).toMonoidHom, ?_, ?_, ?_⟩
  · rintro _ ⟨γ, rfl⟩
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, congr_conj, hE₀]
    exact fun x hx => conj_smul_mem_families _ hx
  · intro h
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hE₀] at h
    exact h01 (h F (MulAction.mem_orbit_self _))
  · intro h
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hE₀] at h
    set r := MulAut.congr projEquiv8 (AutOm.plusRefl (K := K) one_le_four) with hr
    have hrF : r • F = F := by
      obtain ⟨g, hg⟩ := exists_pair_of_mem_plusCompl (K := K) ⟨1, Or.inr (by rw [map_one, mul_one])⟩
      rw [hr, ← hg]
      exact conjAct_smul_family g
    have hrt : r * t = t⁻¹ * r := by
      have h1 := plusRefl_theta_plusRefl (K := K)
      have h2 := AutOm.plusRefl_mul_self (K := K) one_le_four
      have h3 : AutOm.plusRefl (K := K) one_le_four * theta =
          theta⁻¹ * AutOm.plusRefl one_le_four := by
        rw [← h1, mul_assoc, mul_assoc, h2, mul_one]
      rw [hr, ht, thetaP, ← map_mul, h3, map_mul, map_inv]
    have h' := h (t • F) (MulAction.mem_orbit _ _)
    rw [smul_smul, hrt, mul_smul, hrF, ← thetaP_sq] at h'
    exact h12 h'.symm

end Families

section Graph

theorem exists_graph : ∃ (E : MulAut (Om8 K) →* Equiv.Perm (Fin 3))
    (B : Subgroup (MulAut (Om8 K))), B.Normal ∧ inner (Om8 K) ≤ E.ker ∧
      (∀ R : matrixIsometries (coordinateQuadPlus 4 K),
        conjAct _ (matrixIsometryInclusion _ R) ∈ B) ∧
      ∀ x ∈ B, E x = 1 → x ∈ inner (Om8 K) := by
  obtain ⟨E, hEi, hEθ, hEρ⟩ := exists_graphHom (K := K)
  set ρ := AutOm.plusRefl (K := K) one_le_four with hρ
  let π := QuotientGroup.mk' (inner (Om8 K))
  let Eb := QuotientGroup.lift (inner (Om8 K)) E hEi
  have hEb : ∀ x, Eb (π x) = E x := fun x => QuotientGroup.lift_mk' _ hEi x
  have hπ1 : ∀ {x}, x ∈ inner (Om8 K) → π x = 1 := fun hx => (QuotientGroup.eq_one_iff _).2 hx
  set a := π theta with ha
  set b := π ρ with hb
  have ha3 : a ^ 3 = 1 := by rw [ha, ← map_pow, theta_cube, map_one]
  have hb2 : b ^ 2 = 1 := by rw [hb, ← map_pow, sq, hρ, AutOm.plusRefl_mul_self, map_one]
  have hbb : b * b = 1 := by rw [← sq, hb2]
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_left hbb
  have hbab : b * a * b⁻¹ = a⁻¹ := by
    rw [hbinv, ha, hb, ← map_mul, ← map_mul, hρ, plusRefl_theta_plusRefl, map_inv]
  set Bb := Subgroup.zpowers b ⊔ Subgroup.zpowers a with hBb
  have haB : a ∈ Bb := Subgroup.mem_sup_right (Subgroup.mem_zpowers a)
  have hbB : b ∈ Bb := Subgroup.mem_sup_left (Subgroup.mem_zpowers b)
  have hφ : ∀ σ : K ≃+* K,
      π (AutOm.fieldAutP 4 σ) ∈ Subgroup.normalizer (Bb : Set (Outer (Om8 K))) := by
    intro σ
    refine Subgroup.centralizer_le_normalizer _ ?_
    have hle : Bb ≤ Subgroup.centralizer {π (AutOm.fieldAutP 4 σ)} := by
      refine sup_le ((Subgroup.zpowers_le).2 ?_) ((Subgroup.zpowers_le).2 ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff, hb, ← map_mul, ← map_mul, hρ,
          AutOm.plusRefl_mul_fieldAutP]
      · rw [Subgroup.mem_centralizer_singleton_iff, ha, ← map_mul, ← map_mul, theta_fieldAutP]
    rw [Subgroup.mem_centralizer_iff]
    exact fun h hh => Subgroup.mem_centralizer_singleton_iff.1 (hle hh)
  have hnorm : ∀ x : Outer (Om8 K), x ∈ Subgroup.normalizer (Bb : Set (Outer (Om8 K))) := by
    intro x
    obtain ⟨α, rfl⟩ := QuotientGroup.mk'_surjective (inner (Om8 K)) x
    obtain ⟨ι, hι, k, c, hc, rfl⟩ := exists_inner_mul_theta_pow_mul α
    obtain ⟨σ, rfl | rfl⟩ := hc
    · change π (ι * (theta ^ k * AutOm.fieldAutP 4 σ)) ∈ _
      rw [map_mul, hπ1 hι, one_mul, map_mul, map_pow]
      exact mul_mem (pow_mem (Subgroup.le_normalizer haB) k) (hφ σ)
    · change π (ι * (theta ^ k * (ρ * AutOm.fieldAutP 4 σ))) ∈ _
      rw [map_mul, hπ1 hι, one_mul, map_mul, map_pow, map_mul]
      exact mul_mem (pow_mem (Subgroup.le_normalizer haB) k)
        (mul_mem (Subgroup.le_normalizer hbB) (hφ σ))
  have hBbn : Bb.Normal := ⟨fun n hn g => (Subgroup.mem_normalizer_iff.1 (hnorm g) n).1 hn⟩
  have hconj : ∀ k : ℤ, b * a ^ k * b⁻¹ = a ^ (-k) := fun k => by
    rw [← conj_zpow, hbab, inv_zpow']
  have hbN : b ∈ Subgroup.normalizer (Subgroup.zpowers a : Set (Outer (Om8 K))) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
      exact Subgroup.mem_zpowers_iff.2 ⟨-k, (hconj k).symm⟩
    · intro hh
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hh
      refine Subgroup.mem_zpowers_iff.2 ⟨-k, ?_⟩
      calc a ^ (-k) = b * a ^ k * b⁻¹ := (hconj k).symm
        _ = b * (b * h * b⁻¹) * b⁻¹ := by rw [hk]
        _ = (b * b) * h * (b * b)⁻¹ := by group
        _ = h := by rw [hbb, one_mul, inv_one, mul_one]
  have hcoe : (Bb : Set (Outer (Om8 K))) =
      (Subgroup.zpowers b : Set (Outer (Om8 K))) * (Subgroup.zpowers a : Set (Outer (Om8 K))) :=
    Subgroup.coe_mul_of_left_le_normalizer_right _ _ ((Subgroup.zpowers_le).2 hbN)
  have hord_a : orderOf (Eb a) = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime (by rw [← map_pow, ha3, map_one]) (by rw [ha, hEb]; exact hEθ)
  have hord_b : orderOf (Eb b) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [← map_pow, hb2, map_one]) (by rw [hb, hEb]; exact hEρ)
  have hinj : ∀ x ∈ Bb, Eb x = 1 → x = 1 := by
    intro x hx hEx
    have hx' : x ∈ (Bb : Set (Outer (Om8 K))) := hx
    rw [hcoe] at hx'
    obtain ⟨y, hy, z, hz, rfl⟩ := Set.mem_mul.1 hx'
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    rw [map_mul, map_zpow, map_zpow] at hEx
    have hv3 : Eb a ^ 3 = 1 := by rw [← map_pow, ha3, map_one]
    have hu2 : Eb b ^ 2 = 1 := by rw [← map_pow, hb2, map_one]
    have hvk : Eb a ^ k = 1 := by
      have h1 : Eb a ^ k = (Eb b ^ j)⁻¹ := eq_inv_of_mul_eq_one_right hEx
      have hd3 : orderOf (Eb a ^ k) ∣ 3 := orderOf_dvd_of_pow_eq_one (by
        rw [← zpow_natCast, ← zpow_mul, zpow_mul', zpow_natCast, hv3, one_zpow])
      have hd2 : orderOf (Eb a ^ k) ∣ 2 := orderOf_dvd_of_pow_eq_one (by
        rw [h1, inv_pow, ← zpow_natCast, ← zpow_mul, zpow_mul', zpow_natCast, hu2, one_zpow,
          inv_one])
      have h1' : orderOf (Eb a ^ k) = 1 :=
        Nat.dvd_one.1 (by simpa using Nat.dvd_gcd hd3 hd2)
      exact orderOf_eq_one_iff.1 h1'
    have huj : Eb b ^ j = 1 := by rwa [hvk, mul_one] at hEx
    have hak : a ^ k = 1 := by
      have h3 : (3 : ℤ) ∣ k := by
        have := orderOf_dvd_iff_zpow_eq_one.2 hvk
        rwa [hord_a, Nat.cast_ofNat] at this
      exact orderOf_dvd_iff_zpow_eq_one.1
        ((Int.natCast_dvd_natCast.2 (orderOf_dvd_of_pow_eq_one ha3)).trans
          (by exact_mod_cast h3))
    have hbj : b ^ j = 1 := by
      have h2 : (2 : ℤ) ∣ j := by
        have := orderOf_dvd_iff_zpow_eq_one.2 huj
        rwa [hord_b, Nat.cast_ofNat] at this
      exact orderOf_dvd_iff_zpow_eq_one.1
        ((Int.natCast_dvd_natCast.2 (orderOf_dvd_of_pow_eq_one hb2)).trans
          (by exact_mod_cast h2))
    rw [hak, hbj, mul_one]
  have hR : ∀ R : matrixIsometries (coordinateQuadPlus 4 K),
      π (conjAct _ (matrixIsometryInclusion _ R)) ∈ Bb := by
    intro R
    obtain ⟨hnd, hT⟩ := regular_coordinateQuadPlus 4 K (by norm_num)
    have hv0 := AutOm.plusUnitVector_form_ne_zero (K := K) one_le_four
    rcases mem_or_mul_reflMat_mem hnd hT R.2
      (CFSG.SeitzReduction.OmegaPilot.plusUnitVector one_le_four) hv0 with h | h
    · rw [hπ1 (conjAct_inclusion_mem_inner R h)]
      exact one_mem _
    · have hr := reflMat_mem_isometries (Q := coordinateQuadPlus 4 K)
        (CFSG.SeitzReduction.OmegaPilot.plusUnitVector one_le_four) hv0
      have hsplit : R = ⟨R.val * reflMat _ _ hv0, mul_mem R.2 hr⟩ * ⟨reflMat _ _ hv0, hr⟩ := by
        apply Subtype.ext
        change R.val = R.val * reflMat _ _ hv0 * reflMat _ _ hv0
        rw [mul_assoc, reflMat_mul_self, mul_one]
      rw [hsplit, map_mul, map_mul, map_mul, hπ1 (conjAct_inclusion_mem_inner _ h), one_mul]
      exact hbB
  refine ⟨E, Bb.comap π, Subgroup.Normal.comap hBbn π, hEi, hR, ?_⟩
  intro x hx hEx
  exact (QuotientGroup.eq_one_iff x).1 (hinj (π x) hx (by rw [hEb]; exact hEx))

end Graph

end CFSG.OddTranspositions.PartFour.ExtTrialityOrthFour
