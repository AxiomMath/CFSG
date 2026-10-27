module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.CartanCoverTools
public import CFSG.GroupTheory.SylowTwoEquiv
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsC

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open
open CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups

private theorem four_le_sub_of_prime_dvd {m' r : ℕ} (hr : r.Prime) (hm : 5 ≤ m' + 1)
    (hr5 : r ≠ 5) :
    4 ≤ m' - (if r ∣ m' + 1 then 1 else 0) := by
  by_cases hrm : r ∣ m' + 1
  · rw [if_pos hrm]
    have hne5 : m' + 1 ≠ 5 := by
      intro h5
      exact hr5 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_five).mp (h5 ▸ hrm))
    have hm6 : 6 ≤ m' + 1 := by omega
    omega
  · rw [if_neg hrm]
    omega

private theorem isSylowTwoOf_projUnitriangular {F : Type} [Field F] [Finite F] [CharP F 2]
    (m' : ℕ) :
    CFSG.QuasithinUnique.IsSylowTwoOf (LinearFlag.projUnitriangular (m' + 1) F) ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := LinearFlag.exists_sylow_projUnitriangular (K := F) 2 (n := m' + 1) (by omega)
  refine ⟨le_top, ?_, ?_⟩
  · rw [← hP]
    exact P.isPGroup'
  · rw [show ((LinearFlag.projUnitriangular (m' + 1) F).subgroupOf ⊤).index =
      (LinearFlag.projUnitriangular (m' + 1) F).index from Subgroup.relIndex_top_right _, ← hP]
    exact P.not_dvd_index

private theorem torusPSL_range_le_normalizer {F : Type} [Field F] [Finite F] [CharP F 2]
    {r : ℕ} [NeZero r] {ζ : Fˣ} (hζ : ζ ^ r = 1) (m' : ℕ) :
    (CFSG.RankThree.CentralCover.torusPSL ζ hζ m').range ≤
      Subgroup.normalizer (((LinearFlag.projUnitriangular (m' + 1) F).map
        (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
          (m' + 1) F).symm.toMonoidHom : Subgroup (PSL(m' + 1, F))) : Set (PSL(m' + 1, F))) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let eSL : Matrix.ProjectiveSpecialLinearGroup (Fin (m' + 1)) F ≃*
      LinearFlag.projectiveSL (m' + 1) F :=
    CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
      (m' + 1) F
  let ψ : LinearFlag.projectiveSL (m' + 1) F ≃* PSL(m' + 1, F) := eSL.symm
  have htorus_upper : ∀ a, CFSG.RankThree.CentralCover.torusElem ζ hζ a ∈
      LinearFlag.upperTriangular (m' + 1) F := by
    intro a
    refine LinearFlag.mem_upperTriangular.mpr fun i j hij => ?_
    rw [CFSG.RankThree.CentralCover.coe_torusElem, Matrix.diagonal_apply_ne _ (ne_of_gt hij)]
  have hψ_mk : ∀ A : Matrix.SpecialLinearGroup (Fin (m' + 1)) F,
      ψ (LinearFlag.proj (m' + 1) F A) =
        QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin (m' + 1)) F)) A := by
    intro A
    have h1 : eSL (QuotientGroup.mk' (Subgroup.center
          (Matrix.SpecialLinearGroup (Fin (m' + 1)) F)) A) =
        LinearFlag.proj (m' + 1) F A := by
      change QuotientGroup.quotientMulEquivOfEq
        (LinearFlag.scalars_eq_center (m' + 1) F).symm
        (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin (m' + 1)) F)) A) =
          LinearFlag.proj (m' + 1) F A
      simp only [QuotientGroup.coe_mk']
      rw [QuotientGroup.quotientMulEquivOfEq_mk]
      rfl
    show eSL.symm (LinearFlag.proj (m' + 1) F A) = _
    rw [← h1, MulEquiv.symm_apply_apply]
  have hDle : (CFSG.RankThree.CentralCover.torusPSL ζ hζ m').range ≤
      (LinearFlag.projUpperTriangular (m' + 1) F).map ψ.toMonoidHom := by
    rintro d ⟨a, rfl⟩
    refine Subgroup.mem_map.mpr
      ⟨LinearFlag.proj (m' + 1) F (CFSG.RankThree.CentralCover.torusSL ζ hζ m' a), ?_, ?_⟩
    · exact Subgroup.mem_map_of_mem _ (htorus_upper (Multiplicative.toAdd a))
    · change ψ (LinearFlag.proj (m' + 1) F (CFSG.RankThree.CentralCover.torusSL ζ hζ m' a)) =
        (CFSG.RankThree.CentralCover.torusPSL ζ hζ m') a
      rw [hψ_mk]
      rfl
  rw [← Subgroup.map_equiv_normalizer_eq (LinearFlag.projUnitriangular (m' + 1) F) ψ,
    show Subgroup.normalizer (LinearFlag.projUnitriangular (m' + 1) F :
        Set (LinearFlag.projectiveSL (m' + 1) F)) = LinearFlag.projUpperTriangular (m' + 1) F from
      LinearFlag.normalizer_projUnitriangular (K := F) (n := m' + 1) 2]
  exact hDle

theorem k_CartanRankLarge_psl :
    ∀ (K : Type) [Group K] [Finite K] (m f : ℕ),
      CFSG.Open.StatedLieAdmissible .PSL m 2 f → 2 < 2 ^ f →
      CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .PSL m 2 f →
      CFSG.Open.IsQuasisimple K → Odd (Nat.card (Subgroup.center K)) →
      ∀ S : Subgroup K, CFSG.QuasithinUnique.IsSylowTwoOf S ⊤ →
        4 ≤ CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.CS17LieRank .PSL m →
          ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ∣ 2 ^ f - 1 ∧
            3 < CFSG.Open.pRank r (⊤ : Subgroup (TauCeti.Subgroup.normalizerQuotient S)) := by
  intro K _ _ m f hAdm h2f hL _ _ S hS hrank
  have hf2 : 2 ≤ f := by
    by_contra hf
    interval_cases f <;> norm_num at h2f
  have hm5 : 5 ≤ m := by
    have h := hrank
    simp only [CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.CS17LieRank] at h
    omega
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hm' : 1 ≤ m' := by omega
  obtain ⟨F, hFld, hFin, hFcard, ⟨eSL⟩⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hL
  letI := hFld
  letI := hFin
  letI : Fintype F := Fintype.ofFinite F
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := f) (by
    rwa [← Nat.card_eq_fintype_card])
  let ePSL : K ⧸ Subgroup.center K ≃* PSL(m' + 1, F) := eSL.trans
    (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
      (m' + 1) F).symm
  let φ : K →* PSL(m' + 1, F) :=
    ePSL.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  have hφ : Function.Surjective φ :=
    ePSL.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker_eq : φ.ker = Subgroup.center K := by
    rw [MonoidHom.ker_comp_of_injective _ _ ePSL.injective, QuotientGroup.ker_mk']
  have hker : φ.ker ≤ Subgroup.center K := le_of_eq hker_eq
  obtain ⟨r, hr, hr2, hr5, hrdvd⟩ :=
    CFSG.RankThree.PartOne.KFU.exists_odd_prime_dvd_two_pow_sub_one_ne_five hf2
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : NeZero r := ⟨hr.ne_zero⟩
  have hcard_units : r ∣ Nat.card Fˣ := by
    rw [Nat.card_units, hFcard]
    exact hrdvd
  obtain ⟨ζ, hζo⟩ := exists_prime_orderOf_dvd_card' r hcard_units
  have hζ : ζ ^ r = 1 := by rw [← hζo, pow_orderOf_eq_one]
  obtain ⟨hDr, hDcomm, hDcard⟩ :=
    CFSG.RankThree.CentralCover.torusPSL_package (k := F) (p := r) (m := m') (φ := φ)
      hr hr2 hζo hζ hm' hφ hker
  have hk4 : r ^ 4 ≤ Nat.card (CFSG.RankThree.CentralCover.torusPSL ζ hζ m').range :=
    (Nat.pow_le_pow_right hr.pos (four_le_sub_of_prime_dvd hr hm5 hr5)).trans hDcard
  let U : Subgroup (PSL(m' + 1, F)) := (LinearFlag.projUnitriangular (m' + 1) F).map
    (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
      (m' + 1) F).symm.toMonoidHom
  have hU : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤ := by
    have h := CFSG.QuasithinUnique.IsSylowTwoOf.map_mulEquiv
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
        (m' + 1) F).symm (isSylowTwoOf_projUnitriangular (F := F) m')
    simpa [U] using h
  have hmain := le_pRank_normalizerQuotient_of_comap_comm (φ := φ) hφ hker hr hr2
    (D := (CFSG.RankThree.CentralCover.torusPSL ζ hζ m').range) hDr hDcomm hk4
    (U := U) hU (torusPSL_range_le_normalizer (F := F) hζ m') S hS
  exact ⟨r, hr, hr2, hrdvd, by omega⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
