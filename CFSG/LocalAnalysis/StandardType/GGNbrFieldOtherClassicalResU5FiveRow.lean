module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalCoreLine
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylUnitaryDvd
public import CFSG.LocalAnalysis.StandardType.GGNbrFrameOneUnitaryLabel
public import CFSG.LinearAlgebra.LinearGroups.UnitaryScalarKernel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggTorusNoLineComp_zero_of_le_three_U5Five {p r : ℕ} (hp : 0 < p) (hr : r ≤ 3) {R : Type}
    [Group R] {I : Set (MulAut R)} (h : GGTorusNoLineComp p r R I) :
    GGTorusNoLineComp p 0 R I := by
  intro L' _ _ ψ hψ hker hperf A hA hAI _ h3 hsc
  exact h L' ψ hψ hker hperf A hA hAI ((Nat.pow_le_pow_right hp hr).trans h3) h3 hsc

section Cover


theorem ggCenterKp_psu_U5Five {n : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) :
    GGCenterKp (fun k => k ∣ 5) (LargeEvenProj (LargeEvenSUGroup (Fin 5) K (2 ^ n))) := by
  intro L' _ _ ψ hψ hker hperf
  obtain ⟨-, hcov⟩ := LineU.unitaryCoverAt hK (d := 5) (by norm_num)
    (fun h => absurd (congrArg Prod.fst h) (by norm_num))
  obtain ⟨φ, hφ⟩ := hcov L' ψ hψ hker hperf
  set Z : Subgroup ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 n K 5) :=
    (LargeEvenScalars (Fin 5) K).subgroupOf (CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 n K 5)
    with hZ
  have hφs : Function.Surjective φ :=
    LineU.surjective_of_cover (LargeEvenProjMk (CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 n K 5))
      (QuotientGroup.mk'_surjective _) ψ hker hperf φ hφ
  have hkerEq : ψ.ker = Z.map φ := by
    ext l
    constructor
    · intro hl
      obtain ⟨s, rfl⟩ := hφs l
      refine ⟨s, ?_, rfl⟩
      have h1 : LargeEvenProjMk (CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 n K 5) s = 1 := by
        rw [← hφ s]
        exact hl
      exact (QuotientGroup.eq_one_iff s).mp h1
    · rintro ⟨s, hs, rfl⟩
      exact (hφ s).trans ((QuotientGroup.eq_one_iff s).mpr hs)
  have hZdvd : Nat.card Z ∣ 5 := by
    have h := (CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hK
      (n := 5) (by norm_num)).2.2
    rw [hZ, h]
    exact Nat.gcd_dvd_left 5 (2 ^ n + 1)
  rw [hkerEq]
  exact (Subgroup.card_map_dvd Z φ).trans hZdvd

theorem largeEvenLabelAll_rowKX_u5Five {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : lab.tag = .twA ∧ lab.rank = 4 ∧ 5 ∣ 2 ^ lab.n + 1 ∧ 5 ∣ lab.n) :
    LargeEvenLabelAll lab fun R _ I _ => (∀ g : R, MulAut.conj g ∈ I) ∧ GGTorusLift 5 0 R ∧
      (IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
        GGTorusNoLineComp 5 0 R I ∧ GGCenterKp (fun k => k ∣ 5) R) := by
  have hrest : LargeEvenLabelAll lab fun R _ I _ =>
      GGTorusLift 5 0 R ∧ GGTorusNoLineComp 5 0 R I ∧ GGCenterKp (fun k => k ∣ 5) R := by
    obtain ⟨t, l, n⟩ := lab
    obtain ⟨ht, hl, hpn, -⟩ := h
    dsimp only at ht hl hpn
    subst ht hl
    have hn : 1 ≤ n := hlab.1
    intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, _, _, hK, hQ'⟩ := hQ
    have : CharP K 2 := (TableBU.unitaryFieldData_of_card hK hn).charP
    have hline := LineU.noInvariantLineSCr_unitary LineU.unitaryUniversalCover hK hn
      (d := 5) (by norm_num) Nat.prime_five hpn (dvd_refl 5) (by omega)
    have hrk : ggUnitaryTorusRank 5 5 = 2 := by decide
    rw [hrk] at hline
    exact ⟨K, inferInstance, inferInstance, hK, hQ',
      TypeA.ggTorusLift_zero
        (two_dvd_card_statedProj_statedSU (d := 5) (f := n) (K := K) (by norm_num)),
      ggTorusNoLineComp_zero_of_le_three_U5Five (by norm_num) (by norm_num)
        (ggTorusNoLineComp_of_ggTorusNoLine
          (ggTorusNoLine_of_noInvariantLineSCr Nat.prime_five hline)),
      ggCenterKp_psu_U5Five hK⟩
  exact (largeEvenLabelAll_and (largeEvenLabelAll_inn_twA hlab h.1) hrest).mono
    fun _ _ _ _ ⟨hi, hl, hn, hk⟩ => ⟨hi, hl, fun _ _ => ⟨hn, hk⟩⟩

end Cover

end CFSG.StandardType

end
