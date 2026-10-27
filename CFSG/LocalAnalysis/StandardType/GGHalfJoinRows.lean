module

public import CFSG.LocalAnalysis.StandardType.GGHalfJoinDefs
public import CFSG.LocalAnalysis.StandardType.GGHalfKnownGroups
public import CFSG.LocalAnalysis.StandardType.GGHalfTorusFrame
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrLabels

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open CFSG.StandardType.GGHalf CFSG.LieType.Universal.SpecialLinear Matrix

theorem GGHalfJoin.typeA_data {m : ℕ} (hm : 3 ≤ m) {G : Type} [Group G] [Finite G]
    {Bs K' : Subgroup G} (hBs : IsElemAbelian 3 Bs) (hinn' : GGInnerDiagOn Bs K')
    (hnorm : Bs ≤ Subgroup.normalizer (K' : Set G))
    (hlab : GGHasLabel ⟨.A, m + 2, 1⟩ (↥K' ⧸ Subgroup.center ↥K')) :
    Subgroup.center ↥K' = ⊥ ∧ ∀ b ∈ Bs, ∃ c ∈ K', ∀ l ∈ K', b * l * b⁻¹ = c * l * c⁻¹ := by
  have hΛ : LargeEvenInLambda2 ⟨.A, m + 2, 1⟩ := by
    dsimp only [LargeEvenInLambda2]; omega
  have hq : CFSG.Assembly.IsQuasisimple ↥K' := isQuasisimple_of_largeEvenMarking hinn'
  have hmod : StatedClassicalModel (↥K' ⧸ Subgroup.center ↥K') .PSL (m + 1 + 1 + 1) 2 1 :=
    statedClassicalModel_of_hasLabel_typeA hΛ hlab
  obtain ⟨φ, hrange, hinj⟩ := GGHalf.exists_slLift_two (m := m) (by omega) hq.1 hmod
  refine ⟨?_, ?_⟩
  · rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    rw [Subgroup.mem_center_iff] at hz
    obtain ⟨a, ha⟩ := show (z : G) ∈ φ.range by rw [hrange]; exact z.2
    have hcomm : ∀ t, a * t = t * a := by
      intro t
      apply hinj
      rw [map_mul, map_mul]
      have hφt : φ t ∈ K' := by rw [← hrange]; exact ⟨t, rfl⟩
      have h := hz ⟨φ t, hφt⟩
      have hval : (z : G) * φ t = φ t * (z : G) := by
        simpa using (congrArg Subtype.val h).symm
      rw [← ha] at hval
      exact hval
    have ha1 : a = 1 := by
      have hmem : a ∈ Subgroup.center (SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2) := by
        rw [Subgroup.mem_center_iff]
        intro t
        exact (hcomm t).symm
      rw [GGHalf.center_eq_bot] at hmem
      exact Subgroup.mem_bot.mp hmem
    apply Subtype.ext
    rw [ha.symm, ha1, map_one]
    rfl
  · intro b hb
    have hd : 3 ≤ m + 1 + 1 + 1 := by omega
    have hdvd : orderOf b ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr (hBs.2 b hb)
    have hodd : Odd (orderOf b) := by
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h <;> rw [h] <;> norm_num
    obtain ⟨a, ha⟩ :=
      GGHalf.exists_inner_action_of_odd_order (d := m + 1 + 1 + 1) hd φ hrange hinj (hnorm hb) hodd
    refine ⟨φ a, ?_, ?_⟩
    · rw [← hrange]; exact ⟨a, rfl⟩
    · intro l hl
      exact ha l hl

end CFSG.StandardType

end
