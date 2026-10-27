module

public import CFSG.RankThree.PartTwo.Sec14.Item148Res9ONProofSub
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.GroupTheory.SteinbergCEThetaQuotientAction

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory

namespace Res9ON

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem inf_theta_le {L K N : Subgroup Γ} (hKL : K ≤ L) [(N.subgroupOf K).Normal]
    (hqN : IsQuasisimple (↥K ⧸ N.subgroupOf K))
    (htcN : Sec4.IsTripleCover (↥K ⧸ N.subgroupOf K) (alternatingGroup (Fin 7))) :
    K ⊓ inSubgroup (aschbacherSolvableCore 3) L ≤ N := by
  set Θ := inSubgroup (aschbacherSolvableCore 3) L with hΘdef
  have hΘ3 : ¬ 3 ∣ Nat.card Θ := by
    rw [hΘdef, inSubgroup, Subgroup.card_map_of_injective L.subtype_injective]
    exact (solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three).2.2.1
  have hLΘ : L ≤ Subgroup.normalizer (Θ : Set Γ) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨y', hy', rfl⟩
      exact ⟨⟨l, hl⟩ * y' * ⟨l, hl⟩⁻¹,
        (inferInstance : (aschbacherSolvableCore 3 ↥L).Normal).conj_mem _ hy' _, rfl⟩
    · intro hy
      obtain ⟨y', hy', hy'eq⟩ := hy
      refine ⟨⟨l, hl⟩⁻¹ * y' * ⟨l, hl⟩, ?_, ?_⟩
      · have := (inferInstance : (aschbacherSolvableCore 3 ↥L).Normal).conj_mem _ hy' ⟨l, hl⟩⁻¹
        simpa using this
      · simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv] at hy'eq ⊢
        rw [hy'eq]
        group
  set T : Subgroup ↥K := (K ⊓ Θ).subgroupOf K with hTdef
  have hTn : T.Normal := by
    rw [hTdef, Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left]
    intro k hk
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hk, hLΘ (hKL hk)⟩
  set q := QuotientGroup.mk' (N.subgroupOf K) with hqdef
  set T' := T.map q with hT'def
  have hT'n : T'.Normal := hTn.map _ (QuotientGroup.mk'_surjective _)
  have hT'3 : ¬ 3 ∣ Nat.card T' := by
    intro h3
    have h1 : Nat.card T' ∣ Nat.card T := Subgroup.card_map_dvd _ _
    have h2 : Nat.card T ∣ Nat.card Θ := by
      rw [hTdef, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv]
      exact Subgroup.card_dvd_of_le inf_le_right
    exact hΘ3 (h3.trans (h1.trans h2))
  have hK7560 : Nat.card (↥K ⧸ N.subgroupOf K) = 7560 := card_of_isTripleCover_a7 htcN
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hqN hT'n with htop | hcen
  · exfalso
    apply hT'3
    rw [htop, Subgroup.card_top, hK7560]
    norm_num
  · have hT'1 : T' = ⊥ := by
      have hdvd : Nat.card T' ∣ 3 := htcN.1 ▸ Subgroup.card_dvd_of_le hcen
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
      · exact Subgroup.eq_bot_of_card_eq _ h
      · exact absurd (by rw [h]) hT'3
    intro x hx
    have hxT : (⟨x, hx.1⟩ : ↥K) ∈ T := hx
    have h1 : q ⟨x, hx.1⟩ ∈ T' := Subgroup.mem_map_of_mem _ hxT
    rw [hT'1, Subgroup.mem_bot, hqdef, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact h1

omit [Finite Γ] in
theorem thetaQuotientAction_mk {A L : Subgroup Γ} (hAL : A ≤ Subgroup.normalizer (L : Set Γ))
    (a : ↥A) (y : ↥L) :
    thetaQuotientAction 3 hAL a (y : ↥L ⧸ aschbacherSolvableCore 3 ↥L) =
      ((⟨(a : Γ) * y * (a : Γ)⁻¹, (hAL a.2 y).mp y.2⟩ : ↥L) :
        ↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
  rfl

omit [Finite Γ] in
theorem mem_center_of_conj_eq_one {X : Type*} [Group X] {x : X} (h : MulAut.conj x = 1) :
    x ∈ Subgroup.center X := by
  refine Subgroup.mem_center_iff.mpr fun y => ?_
  have h1 := congrArg (fun f : MulAut X => f y) h
  simp only [MulAut.conj_apply, MulAut.one_apply] at h1
  calc y * x = x * y * x⁻¹ * x := by rw [h1]
    _ = x * y := by group

omit [Finite Γ] in
theorem conj_eq_one_of_mem_center {X : Type*} [Group X] {x : X} (h : x ∈ Subgroup.center X) :
    MulAut.conj x = 1 := by
  ext y
  rw [MulAut.conj_apply, MulAut.one_apply, ← Subgroup.mem_center_iff.mp h y, mul_assoc,
    mul_inv_cancel, mul_one]

end Res9ON

end CFSG.RankThree.PartTwo.Sec14
