module

public import CFSG.Blueprint.Catalog
public import CFSG.Adapters.QiuzhenLegacy.Compat.G1.DicksonSylowElementary
import CFSG.CharacterTheory.Semidihedral.AllPrimeSL2Sections
import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms
import CFSG.Walter.AStar.Basic
import CFSG.LocalAnalysis.ComponentInitial.LinearCoverDihedral
import CFSG.Adapters.SpecialLinearPerfect

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F09

open CFSG.Blueprint (LieModel)

theorem r95_char_seven_of_section {Q : Type} [Group Q] [Finite Q]
    {p f : ℕ} (hQ : LieModel Q .PSL 2 p f) {E : Subgroup Q} {Qm : Type} [Group Qm]
    (π : E →* Qm) (hπ : Function.Surjective π) (hm : LieModel Qm .PSL 3 2 1) : p = 7 := by
  obtain ⟨⟨hp, -⟩, K, _, _, hK, ⟨eK⟩⟩ := hQ.statedClassicalModel (by decide)
  haveI : Fact p.Prime := ⟨hp⟩
  let e : Q ≃* CFSG.BenderSuzuki.MatrixGroups.PSL2MatrixGroup K :=
    eK.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
  haveI : Finite Qm := Finite.of_surjective π hπ
  haveI : Finite (CFSG.BenderSuzuki.MatrixGroups.PSL2MatrixGroup K) :=
    Finite.of_equiv Q e.toEquiv
  by_cases h2 : p = 2
  ·
    subst h2
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let E' : Subgroup (CFSG.BenderSuzuki.MatrixGroups.PSL2MatrixGroup K) := E.map e.toMonoidHom
    have hE' : CFSG.Walter.HasAbelianSylowTwo ↥E' := fun P =>
      (CFSG.Glauberman.Dickson.h826_sylow_elementary hK E' P).toIsMulCommutative
    let ψ : ↥E' →* Qm :=
      π.comp (Subgroup.equivMapOfInjective E e.toMonoidHom e.injective).symm.toMonoidHom
    have hψ : Function.Surjective ψ := hπ.comp (MulEquiv.surjective _)
    have hQm : CFSG.Walter.HasAbelianSylowTwo Qm :=
      CFSG.Walter.HasAbelianSylowTwo.of_surjective hψ hE'
    obtain ⟨K3, _, _, hc3, ⟨e3⟩⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hm
    haveI := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (by norm_num) hc3
    obtain ⟨m, hm3, S, r, hr, s, hs, -, hro, -, -, hconj⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSL_three_dihedral_sylow
        (k := K3) (by rw [hc3, pow_one])
    have hab := CFSG.Walter.HasAbelianSylowTwo.of_surjective (f := e3.toMonoidHom)
      e3.surjective hQm S
    have hrs : r * s = s * r := congrArg Subtype.val (hab.is_comm.comm ⟨r, hr⟩ ⟨s, hs⟩)
    have hrs' : s⁻¹ * r * s = r := by
      rw [mul_assoc, hrs, ← mul_assoc, inv_mul_cancel, one_mul]
    have hrinv : r = r⁻¹ := by
      rw [hrs'] at hconj
      exact hconj
    have hr2 : r ^ 2 = 1 := by
      have h : r * r = r * r⁻¹ := congrArg (fun x => r * x) hrinv
      rw [mul_inv_cancel] at h
      rw [pow_two]
      exact h
    have hordvd : orderOf r ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hr2
    have hle : 2 ^ (m - 1) ≤ 2 := Nat.le_of_dvd (by norm_num) (hro ▸ hordvd)
    have hge : 4 ≤ 2 ^ (m - 1) := by
      have hm2 : 2 ≤ m - 1 := by omega
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (m - 1) := pow_le_pow_right' (by norm_num : (1 : ℕ) ≤ 2) hm2
    omega
  ·
    have hpodd : Odd p := hp.odd_of_ne_two h2
    have hm7 : LieModel Qm .PSL 2 7 1 :=
      CFSG.LocalAnalysis.ComponentInitial.PSL3_two_PSL2_seven_paired_isomorphism Qm hm
    obtain ⟨⟨-, -⟩, K7, _, _, hK7, ⟨e7'⟩⟩ := hm7.statedClassicalModel (by decide)
    let e7 : Qm ≃* CFSG.BenderSuzuki.MatrixGroups.PSL2MatrixGroup K7 :=
      e7'.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K7).symm
    haveI : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) K7) :=
      CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card K7 (by rw [hK7]; norm_num)
    haveI : Group.IsPerfect (CFSG.BenderSuzuki.MatrixGroups.PSL2MatrixGroup K7) := inferInstance
    haveI : Group.IsPerfect Qm :=
      Group.IsPerfect.ofSurjective (f := e7.symm.toMonoidHom) e7.symm.surjective
    obtain ⟨⟨k, hk, -⟩, -, hPperf, -⟩ := CFSG.perfect_residual_characterization (G := ↥E)
    have hPmap : (CFSG.perfectResidual ↥E).map π = ⊤ := by
      rw [hk, map_derivedSeries_eq hπ, Group.IsPerfect.derivedSeries_eq_top]
    haveI : Group.IsPerfect ↥(CFSG.perfectResidual ↥E) := hPperf
    let ι : ↥E →* CFSG.BenderSuzuki.MatrixGroups.PSL2MatrixGroup K :=
      e.toMonoidHom.comp E.subtype
    let X : Subgroup (CFSG.BenderSuzuki.MatrixGroups.PSL2MatrixGroup K) :=
      (CFSG.perfectResidual ↥E).map ι
    haveI hX : Group.IsPerfect ↥X := Group.IsPerfect.map ι
    let φ : ↥X ≃* ↥(CFSG.perfectResidual ↥E) :=
      (Subgroup.equivMapOfInjective (CFSG.perfectResidual ↥E) ι
        (e.injective.comp E.subtype_injective)).symm
    let π' : ↥X →* CFSG.BenderSuzuki.MatrixGroups.PSL2MatrixGroup K7 :=
      e7.toMonoidHom.comp ((π.comp (CFSG.perfectResidual ↥E).subtype).comp φ.toMonoidHom)
    have hπ' : Function.Surjective π' := by
      intro y
      have hy : e7.symm y ∈ (CFSG.perfectResidual ↥E).map π := by
        rw [hPmap]
        exact Subgroup.mem_top _
      obtain ⟨p, hp, hpy⟩ := Subgroup.mem_map.1 hy
      refine ⟨φ.symm ⟨p, hp⟩, ?_⟩
      have h1 : φ.toMonoidHom (φ.symm ⟨p, hp⟩) = ⟨p, hp⟩ :=
        MulEquiv.apply_symm_apply φ ⟨p, hp⟩
      show e7.toMonoidHom (π ((CFSG.perfectResidual ↥E).subtype
        (φ.toMonoidHom (φ.symm ⟨p, hp⟩)))) = y
      rw [h1]
      show e7.toMonoidHom (π p) = y
      rw [hpy]
      exact MulEquiv.apply_symm_apply e7 y
    obtain ⟨m, hm0, -, hcard⟩ :=
      CFSG.Semidihedral.AllPrime.SL2Sections.psl2_perfect_subgroup_onto_psl2
        (F' := K7) hpodd hK (by rw [hK7]; norm_num) (by rw [hK7]; norm_num) X hX π' hπ'
    have h7 : p ∣ 7 := by
      have := dvd_pow_self p hm0
      rw [← hcard, hK7, pow_one] at this
      exact this
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_seven).1 h7

end CFSG.LocalAnalysis.UniquenessCase.UC22.F09
