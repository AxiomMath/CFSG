module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureFixedPointModelRecognition
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.PerfectOddCoverUnitary
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_10_13
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTwoCoreGrowthLinearOddCover

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.OvergroupHull

open CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open CFSG.ShultStronglyClosedTI.FixedPointModel
open scoped MatrixGroups

theorem unitaryProj_ker_eq_center {k : Type} [Field k] (J : HermitianForm 3 k)
    [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    (hnc : ¬ IsMulCommutative (ProjectiveSpecialUnitaryMatrixGroup J)) :
    (PerfectOddCover.unitaryProj J).ker = Subgroup.center J.specialSubgroup := by
  apply le_antisymm
  · intro A hA
    rw [MonoidHom.mem_ker, ← OneMemClass.coe_eq_one, PerfectOddCover.coe_unitaryProj,
      Matrix.ProjGenLinGroup.mk_eq_one] at hA
    exact Subgroup.mem_center_iff.mpr fun B =>
      Subtype.ext (Subgroup.mem_center_iff.mp hA (B : GL (Fin 3) k))
  · intro A hA
    have hcen : PerfectOddCover.unitaryProj J A ∈
        Subgroup.center (ProjectiveSpecialUnitaryMatrixGroup J) := by
      refine Subgroup.mem_center_iff.mpr fun p => ?_
      obtain ⟨B, rfl⟩ := PerfectOddCover.unitaryProj_surjective J p
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hA B]
    have hbot : Subgroup.center (ProjectiveSpecialUnitaryMatrixGroup J) = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
          (Subgroup.center (ProjectiveSpecialUnitaryMatrixGroup J)) with hb | ht
      · exact hb
      · exact absurd (Subgroup.center_eq_top_iff.mp ht) hnc
    rw [hbot] at hcen
    exact MonoidHom.mem_ker.mpr (Subgroup.mem_bot.mp hcen)

variable {L : Type*} [Group L] [Finite L]

omit [Finite L] in
theorem model_parameter_two_pow {M : Subgroup L} {q i : ℕ}
    (h : IsModelCosetAction L M q i) : ∃ f : ℕ, 2 ≤ f ∧ q = 2 ^ f := by
  rcases h with ⟨-, f, hf, hq, -⟩ | ⟨-, a, ha, hq, -⟩ | ⟨-, f, hf, hq, -⟩
  · exact ⟨f, hf, hq⟩
  · exact ⟨2 * a + 1, by omega, hq⟩
  · exact ⟨f, hf, hq⟩

theorem linear_model_oddCore_eq_bot
    [Group.IsPerfect L]
    (hZ : CFSG.oddCore L ≤ Subgroup.center L) {M : Subgroup L} {q : ℕ}
    (h : IsModelCosetAction L M q 1) :
    CFSG.oddCore L = ⊥ ∧
      ∃ f : ℕ, 2 ≤ f ∧ q = 2 ^ f ∧ Nonempty (L ≃* PSL(2, GaloisField 2 f)) := by
  rcases h with ⟨-, f, hf, hq, e, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
  · let η := e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.oddCore L))
    have hker : η.ker = CFSG.oddCore L := by ext x; simp [η]
    obtain ⟨hbot, iso, -⟩ := TwoCoreGrowth.perfect_linear_odd_cover f hf η
      (e.surjective.comp (QuotientGroup.mk'_surjective _)) (hker ▸ hZ)
      (hker ▸ CFSG.ComponentClassification.OddCore.odd_card L)
    exact ⟨hker ▸ hbot, f, hf, hq, ⟨iso⟩⟩
  · omega
  · omega

theorem suzuki_model_oddCore_eq_bot
    [Group.IsPerfect L]
    (hZ : CFSG.oddCore L ≤ Subgroup.center L) {M : Subgroup L} {q : ℕ}
    (h : IsModelCosetAction L M q 2) :
    CFSG.oddCore L = ⊥ ∧
      ∃ a : ℕ, 1 ≤ a ∧ q = 2 ^ (2 * a + 1) ∧ Nonempty (L ≃* Sz a) := by
  rcases h with ⟨h1, -⟩ | ⟨-, a, ha, hq, ⟨e⟩, -⟩ | ⟨h1, -⟩
  · omega
  · let e' := e.trans (suzukiCoverNativeEquiv a)
    let η := e'.toMonoidHom.comp (QuotientGroup.mk' (CFSG.oddCore L))
    have hker : η.ker = CFSG.oddCore L := by ext x; simp [η]
    obtain ⟨hbot, iso, -⟩ := TwoCoreGrowth.perfect_suzuki_odd_cover a η
      (e'.surjective.comp (QuotientGroup.mk'_surjective _)) (hker ▸ hZ)
      (hker ▸ CFSG.ComponentClassification.OddCore.odd_card L)
    exact ⟨hker ▸ hbot, a, ha, hq, ⟨iso.trans (suzukiCoverNativeEquiv a).symm⟩⟩
  · omega

theorem unitary_model_scalar_cover
    [Group.IsPerfect L]
    (hZ : CFSG.oddCore L ≤ Subgroup.center L) {M : Subgroup L} {q : ℕ}
    (h : IsModelCosetAction L M q 3) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k) (J : HermitianForm 3 k)
      (_ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]),
      Nat.card k = q ^ 2 ∧ Nat.card {x : k // J.conj x = x} = q ∧
      (∀ A : J.specialSubgroup, A ∈ (PerfectOddCover.unitaryProj J).ker ↔
        ∃ c : k, ((A : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) = Matrix.scalar (Fin 3) c ∧
          c ^ (q + 1) = 1 ∧ c ^ 3 = 1) ∧
      (PerfectOddCover.unitaryProj J).ker = Subgroup.center J.specialSubgroup ∧
      ∃ (C : Subgroup J.specialSubgroup) (_ : C.Normal),
        C ≤ (PerfectOddCover.unitaryProj J).ker ∧
        ∃ e : J.specialSubgroup ⧸ C ≃* L,
          ((PerfectOddCover.unitaryProj J).ker.map (QuotientGroup.mk' C)).map e.toMonoidHom =
            CFSG.oddCore L ∧
          Nat.card (CFSG.oddCore L) ∣ Nat.gcd 3 (q + 1) := by
  rcases h with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, f, hf, hq, -, k, _, _, J, hJ, hk, hfix, e, -⟩
  · omega
  · omega
  subst hq
  let η := e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.oddCore L))
  have hker : η.ker = CFSG.oddCore L := by ext x; simp [η]
  obtain ⟨hmem, φ, -, -, -, hφker, hmap, ⟨e', he'⟩, -, -, hdvd, -⟩ :=
    PerfectOddCover.perfect_odd_cover_unitary J f hf hk hfix hJ η
      (e.surjective.comp (QuotientGroup.mk'_surjective _)) (hker ▸ hZ)
      (hker ▸ CFSG.ComponentClassification.OddCore.odd_card L)
  have hconj := CFSG.BenderSuzuki.External.huppert_II_10_4_conj_eq_frobenius J (2 ^ f) hk hfix
  have : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
    CFSG.BenderSuzuki.External.huppert_II_10_13 J (2 ^ f)
      (lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hf)) hk hfix
  have : Group.IsPerfect (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Group.IsPerfect.ofSurjective (f := η) (e.surjective.comp (QuotientGroup.mk'_surjective _))
  obtain ⟨-, -, -, -, -, rho, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    ⟨w, hw, -⟩, -⟩ := UnitaryModel.unitary_three_point_structure J f hf hk hfix hJ
  have : Nontrivial (ProjectiveSpecialUnitaryMatrixGroup J) :=
    nontrivial_of_ne w 1 (fun h1 => by rw [h1, orderOf_one] at hw; omega)
  have hcenter := unitaryProj_ker_eq_center J
    (Group.IsPerfect.not_isMulCommutative (ProjectiveSpecialUnitaryMatrixGroup J))
  refine ⟨k, inferInstance, inferInstance, J, hJ, hk, hfix, fun A => ?_, hcenter, φ.ker,
    inferInstance, hφker, e', ?_, hker ▸ hdvd⟩
  · rw [hmem A]
    refine exists_congr fun c => and_congr_right fun _ => and_congr_left fun _ => ?_
    rw [hconj c, pow_succ, mul_comm]
  · rw [Subgroup.map_map, ← hker, ← hmap]
    congr 1
    ext A
    exact (he' A).1

end CFSG.ShultStronglyClosedTI.OvergroupHull
