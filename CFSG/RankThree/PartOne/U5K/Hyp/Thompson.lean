module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Foundations.Basic

public section

namespace CFSG.RankThree.PartOne.U5K.Hyp

open CFSG

variable {G : Type} [Group G]

theorem mem_center_map_subtype_iff {J : Subgroup G} {z : G} :
    z ∈ (Subgroup.center ↥J).map J.subtype ↔ z ∈ J ∧ ∀ w ∈ J, w * z = z * w := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a.2, fun w hw => congrArg Subtype.val ((Subgroup.mem_center_iff.1 ha) ⟨w, hw⟩)⟩
  · rintro ⟨hz, hc⟩
    exact ⟨⟨z, hz⟩, Subgroup.mem_center_iff.2 fun w => Subtype.ext (hc w w.2), rfl⟩

theorem mem_elemThompsonCenterTorsion_iff {z : G} :
    z ∈ elemThompsonCenterTorsion G 2 ↔
      (z ∈ elemThompson G 2 ∧ ∀ w ∈ elemThompson G 2, w * z = z * w) ∧ z ^ 2 = 1 := by
  change (z ∈ (Subgroup.center ↥(elemThompson G 2)).map (elemThompson G 2).subtype ∧ z ^ 2 = 1) ↔ _
  rw [mem_center_map_subtype_iff]

theorem elemCenter_eq_of_max [Finite G] {T V : Subgroup G} {n : ℕ} (hVT : V ≤ T)
    (hVc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) (hVs : ∀ x ∈ V, x ^ 2 = 1)
    (hVcard : Nat.card V = 2 ^ n)
    (key : ∀ F : Subgroup G, F ≤ T → (∀ x ∈ F, ∀ y ∈ F, x * y = y * x) →
      (∀ x ∈ F, x ^ 2 = 1) → Nat.card F ≤ 2 ^ n ∧ (Nat.card F = 2 ^ n → F = V)) :
    (elemThompsonCenterTorsion ↥T 2).map T.subtype = V := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set V' : Subgroup ↥T := V.subgroupOf T with hV'
  have hmapV : V'.map T.subtype = V := by
    rw [hV', Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hVT]
  have hcardV' : Nat.card V' = 2 ^ n := by
    rw [← hVcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVT).toEquiv
  have hEA : IsElementaryAbelian 2 V' := by
    refine { toIsMulCommutative := ⟨⟨fun a b => ?_⟩⟩, exponent_dvd_p := ?_ }
    · apply Subtype.ext
      apply Subtype.ext
      show ((a : ↥T) : G) * ((b : ↥T) : G) = ((b : ↥T) : G) * ((a : ↥T) : G)
      exact hVc _ a.2 _ b.2
    · refine Monoid.exponent_dvd_of_forall_pow_eq_one fun a => ?_
      apply Subtype.ext
      apply Subtype.ext
      exact hVs _ a.2
  have key' : ∀ F' : Subgroup ↥T, IsElementaryAbelian 2 F' →
      Nat.card F' ≤ 2 ^ n ∧ (Nat.card F' = 2 ^ n → F' = V') := by
    intro F' hF'
    have hcF : Nat.card (F'.map T.subtype) = Nat.card F' :=
      Subgroup.card_map_of_injective T.subtype_injective
    have hFT : F'.map T.subtype ≤ T := Subgroup.map_subtype_le _
    have hcomm : ∀ x ∈ F'.map T.subtype, ∀ y ∈ F'.map T.subtype, x * y = y * x := by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      exact congrArg (fun z : ↥F' => (((z : ↥F') : ↥T) : G)) (hF'.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    have hsq : ∀ x ∈ F'.map T.subtype, x ^ 2 = 1 := by
      rintro _ ⟨a, ha, rfl⟩
      have := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := F') a ha
      exact congrArg (fun z : ↥T => (z : G)) this
    obtain ⟨h1, h2⟩ := key _ hFT hcomm hsq
    refine ⟨by rw [← hcF]; exact h1, fun hc => ?_⟩
    have := h2 (by rw [hcF, hc])
    rw [← hmapV] at this
    exact Subgroup.map_injective T.subtype_injective this
  have hrank : pRank 2 ↥T = n := by
    apply IsGreatest.csSup_eq
    refine ⟨⟨V', hEA, hcardV'⟩, ?_⟩
    rintro r ⟨F, hF, hFcard⟩
    have := (key' F hF).1
    rw [hFcard] at this
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp this
  have hfam : elemThompsonFamily ↥T 2 = {V'} := by
    ext F
    constructor
    · rintro ⟨hF, hFcard⟩
      rw [hrank] at hFcard
      exact (key' F hF).2 hFcard
    · rintro rfl
      exact ⟨hEA, by rw [hrank, hcardV']⟩
  have hJ : elemThompson ↥T 2 = V' := by
    rw [elemThompson, hfam, sSup_singleton]
  have hCT : elemThompsonCenterTorsion ↥T 2 = V' := by
    ext z
    rw [mem_elemThompsonCenterTorsion_iff, hJ]
    constructor
    · rintro ⟨⟨hz, -⟩, -⟩
      exact hz
    · intro hz
      refine ⟨⟨hz, fun w hw => ?_⟩, ?_⟩
      · apply Subtype.ext
        exact hVc _ hw _ hz
      · apply Subtype.ext
        exact hVs _ hz
  rw [hCT, hmapV]

end CFSG.RankThree.PartOne.U5K.Hyp
