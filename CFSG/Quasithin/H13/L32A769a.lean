module

public import CFSG.Quasithin.H13.L32A764

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

omit [Finite G] in
theorem T_le_centralizer_V1 (T V : Subgroup G) :
    T ≤ Subgroup.centralizer (fsuV1 T V : Set G) := by
  intro t ht
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  have hz' : z ∈ quasithinOmegaOneCenter T := (Subgroup.mem_inf.mp hz).2
  have h1 := (B2F.omegaOneCenter_le_inf_centralizer T hz').2
  exact (Subgroup.mem_centralizer_iff.mp h1 t ht).symm

theorem cent_eq_of_sup_eq (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) (h64 : Remark14_7_64) {W : Subgroup G}
    (hWR : W ≤ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T))
    (hWQ : W ⊔ pCoreOf 2 (hz T V) = pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T))
    (hUW : ⁅fsuU T V, W⁆ ≤ fsuU T V ⊓ W) (hWc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) :
    fsuU T V ⊓ Subgroup.centralizer (W : Set G) = V ⊔ u0 T V ∧
      ⁅fsuU T V, W⁆ ⊔ fsuV1 T V = V ⊔ u0 T V ∧ (fsuU T V ⊓ W) ⊔ fsuV1 T V = V ⊔ u0 T V := by
  have S0 : Setting147 G T L V (hz T V) := ⟨h, h.isHzOne_hz h63⟩
  obtain ⟨-, hR4⟩ := R1_le_kz_sup S0 hF h63 h1222 h1332 h1334
  have hTH : T ≤ hz T V := hF.T_le_H
  have hR1T : pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) ≤ T := pCoreOf_le_of_le h le_sup_right
  have hWT : W ≤ T := hWR.trans hR1T
  have hUeq : fsuU T V = conjClosure V (hz T V) := fsuU_eq_conjClosure_hz hMod h
  have hV1U : fsuV1 T V ≤ fsuU T V := inf_le_left.trans (le_conjClosure V _)
  obtain ⟨s, hsW, hsQ⟩ : ∃ s ∈ W, s ∉ pCoreOf 2 (hz T V) := by
    by_contra hcon
    push Not at hcon
    have hle : W ≤ pCoreOf 2 (hz T V) := fun x hx => hcon x hx
    rw [sup_eq_right.mpr hle] at hWQ
    rw [hWQ, Subgroup.relIndex_self] at hR4
    exact absurd hR4 (by norm_num)
  have h1 : fsuU T V ⊓ Subgroup.centralizer (W : Set G) ≤ V ⊔ u0 T V := by
    rintro u ⟨hu, huc⟩
    refine mem_sup_u0_of_comm_mem h hMod h63 hF h1222 h1332 h1334 (hWR hsW) hsQ hu ?_
    rw [Subgroup.mem_centralizer_iff.mp huc s hsW, mul_inv_cancel_right, mul_inv_cancel]
    exact one_mem _
  have h2 : V ⊔ u0 T V ≤ ⁅fsuU T V, W⁆ ⊔ fsuV1 T V := by
    rw [← (h64 G T L V h).1, ← hWQ]
    refine sup_le (commutator_sup_le ?_ ?_ ?_) le_sup_right
    · exact (hWT.trans hTH).trans hF.H_normalizes_V₁
    · exact (hWT.trans hTH).trans (le_normalizer_pCoreOf 2 _)
    · intro q hq u hu
      have hqC : q ∈ centralizerMod (fsuV1 T V) (hz T V) (conjClosure V (hz T V)) := by
        rw [← hF.pCoreOf_eq_centralizerMod]
        exact hq
      exact hqC.2.2 u (hUeq ▸ hu)
  have h3 : ⁅fsuU T V, W⁆ ⊔ fsuV1 T V ≤ (fsuU T V ⊓ W) ⊔ fsuV1 T V := sup_le_sup_right hUW _
  have h4 : (fsuU T V ⊓ W) ⊔ fsuV1 T V ≤ fsuU T V ⊓ Subgroup.centralizer (W : Set G) := by
    refine sup_le (fun x hx => ⟨hx.1, Subgroup.mem_centralizer_iff.mpr fun y hy =>
      hWc y hy x hx.2⟩) (fun z hz => ⟨hV1U hz, ?_⟩)
    exact Subgroup.mem_centralizer_iff.mpr fun y hy =>
      (Subgroup.mem_centralizer_iff.mp (T_le_centralizer_V1 T V (hWT hy)) z hz).symm
  exact ⟨le_antisymm h1 (h2.trans (h3.trans h4)), le_antisymm (h3.trans (h4.trans h1)) h2,
    le_antisymm (h4.trans h1) (h2.trans h3)⟩

theorem exists_not_mem_union {Q R : Subgroup G} (hQR : Q ≤ R) (h4 : Q.relIndex R = 4) (x : G) :
    ∃ y ∈ R, y ∉ Q ∧ x * y ∉ Q := by
  classical
  by_contra hcon
  push Not at hcon
  have hsub : (R : Set G) ⊆ (Q : Set G) ∪ (x⁻¹ • (Q : Set G)) := by
    intro y hy
    by_cases hyQ : y ∈ Q
    · exact Or.inl hyQ
    · exact Or.inr ⟨x * y, hcon y hy hyQ, by simp [smul_eq_mul]⟩
  have hcardR : Nat.card ↥R = 4 * Nat.card ↥Q := by
    have := Subgroup.relIndex_mul_card Q R
    rw [inf_eq_left.mpr hQR, h4] at this
    omega
  have hle : (R : Set G).ncard ≤ 2 * (Q : Set G).ncard := by
    refine (Set.ncard_le_ncard hsub (Set.toFinite _)).trans ((Set.ncard_union_le _ _).trans ?_)
    rw [Set.ncard_smul_set]
    omega
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, SetLike.coe_sort_coe,
    SetLike.coe_sort_coe, hcardR] at hle
  have hpos : 0 < Nat.card ↥Q := Nat.card_pos
  omega

theorem exists_comm_not_mem (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) {W Z : Subgroup G}
    (hWR : W ≤ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T))
    (hWQ : W ⊔ pCoreOf 2 (hz T V) = pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T))
    (hWc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) (hZW : Z ≤ W) (hZ2 : Nat.card ↥Z = 2) {u : G}
    (hu : u ∈ fsuU T V) (huV : u ∉ V ⊔ u0 T V) : ∃ x ∈ W, u * x * u⁻¹ * x⁻¹ ∉ Z := by
  have S0 : Setting147 G T L V (hz T V) := ⟨h, h.isHzOne_hz h63⟩
  obtain ⟨-, hR4⟩ := R1_le_kz_sup S0 hF h63 h1222 h1332 h1334
  have hQR := pCoreOf_hz_le_R1 h hF
  have hKQ : W ≤ Subgroup.normalizer (pCoreOf 2 (hz T V) : Set G) :=
    (hWR.trans ((pCoreOf_le_of_le h le_sup_right).trans hF.T_le_H)).trans
      (le_normalizer_pCoreOf 2 _)
  have hout : ∀ x ∈ W, x ∉ pCoreOf 2 (hz T V) → u * x * u⁻¹ * x⁻¹ ∉ fsuV1 T V := by
    intro x hx hxQ hc
    apply huV
    refine mem_sup_u0_of_comm_mem h hMod h63 hF h1222 h1332 h1334 (hWR hx) hxQ hu ?_
    have := inv_mem hc
    rwa [show (u * x * u⁻¹ * x⁻¹)⁻¹ = x * u * x⁻¹ * u⁻¹ by group] at this
  have hWmul : ∀ y ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T), ∃ w ∈ W, ∃ q ∈ pCoreOf 2 (hz T V),
      y = w * q := by
    intro y hy
    rw [← hWQ, ← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hKQ] at hy
    obtain ⟨w, hw, q, hq, rfl⟩ := hy
    exact ⟨w, hw, q, hq, rfl⟩
  obtain ⟨y₁, hy₁, hy₁Q, -⟩ := exists_not_mem_union hQR hR4 1
  obtain ⟨x₁, hx₁, q₁, hq₁, rfl⟩ := hWmul y₁ hy₁
  have hx₁Q : x₁ ∉ pCoreOf 2 (hz T V) := fun h' => hy₁Q (mul_mem h' hq₁)
  obtain ⟨y₂, hy₂, hy₂Q, hxy⟩ := exists_not_mem_union hQR hR4 x₁
  obtain ⟨x₂, hx₂, q₂, hq₂, rfl⟩ := hWmul y₂ hy₂
  have hx₂Q : x₂ ∉ pCoreOf 2 (hz T V) := fun h' => hy₂Q (mul_mem h' hq₂)
  have hx₁₂Q : x₁ * x₂ ∉ pCoreOf 2 (hz T V) := fun h' =>
    hxy (by rw [← mul_assoc]; exact mul_mem h' hq₂)
  by_contra hcon
  push Not at hcon
  obtain ⟨z, hz1, hzZ⟩ : ∃ z : G, z ≠ 1 ∧ ∀ y ∈ Z, y = 1 ∨ y = z := by
    obtain ⟨⟨z, hz⟩, hz1, hw⟩ := (Nat.card_eq_two_iff' (1 : ↥Z)).mp hZ2
    refine ⟨z, fun e => hz1 (Subtype.ext e), fun y hy => ?_⟩
    by_cases hy1 : y = 1
    · exact Or.inl hy1
    · right
      exact congrArg Subtype.val (hw ⟨y, hy⟩ (fun e => hy1 (congrArg Subtype.val e)))
  have hV1 : (1 : G) ∈ fsuV1 T V := one_mem _
  have hc1 : u * x₁ * u⁻¹ * x₁⁻¹ = z := by
    rcases hzZ _ (hcon x₁ hx₁) with e | e
    · exact absurd (e ▸ hV1) (hout x₁ hx₁ hx₁Q)
    · exact e
  have hc2 : u * x₂ * u⁻¹ * x₂⁻¹ = z := by
    rcases hzZ _ (hcon x₂ hx₂) with e | e
    · exact absurd (e ▸ hV1) (hout x₂ hx₂ hx₂Q)
    · exact e
  have hzW : z ∈ W := hc1 ▸ hZW (hcon x₁ hx₁)
  have hz2 : z * z = 1 := by
    have h2 : z ^ 2 = 1 := by
      have := orderOf_dvd_natCard (⟨z, (hc1 ▸ hcon x₁ hx₁ : z ∈ Z)⟩ : ↥Z)
      rw [hZ2] at this
      have h' := orderOf_dvd_iff_pow_eq_one.mp this
      simpa using congrArg Subtype.val h'
    rwa [pow_two] at h2
  have hc12 : u * (x₁ * x₂) * u⁻¹ * (x₁ * x₂)⁻¹ = 1 := by
    have e : u * (x₁ * x₂) * u⁻¹ * (x₁ * x₂)⁻¹ =
        (u * x₁ * u⁻¹ * x₁⁻¹) * (x₁ * (u * x₂ * u⁻¹ * x₂⁻¹) * x₁⁻¹) := by group
    rw [e, hc1, hc2, hWc x₁ hx₁ z hzW, mul_inv_cancel_right, hz2]
  exact hout _ (mul_mem hx₁ hx₂) hx₁₂Q (hc12 ▸ hV1)

theorem inf_centralizerMod_eq (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) (h64 : Remark14_7_64) {W Z GW : Subgroup G}
    (hWR : W ≤ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T))
    (hWQ : W ⊔ pCoreOf 2 (hz T V) = pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T))
    (hUW : ⁅fsuU T V, W⁆ ≤ fsuU T V ⊓ W) (hWc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x)
    (hZW : Z ≤ W) (hZ2 : Nat.card ↥Z = 2) (hUG : fsuU T V ≤ GW)
    (hGZ : GW ≤ Subgroup.normalizer (Z : Set G)) :
    fsuU T V ⊓ centralizerMod Z GW W = V ⊔ u0 T V := by
  obtain ⟨hc, -, -⟩ := cent_eq_of_sup_eq h hMod h63 hF h1222 h1332 h1334 h64 hWR hWQ hUW hWc
  apply le_antisymm
  · rintro u ⟨hu, -, -, huc⟩
    by_contra huV
    obtain ⟨x, hx, hxZ⟩ :=
      exists_comm_not_mem h hMod h63 hF h1222 h1332 h1334 hWR hWQ hWc hZW hZ2 hu huV
    exact hxZ (huc x hx)
  · rw [← hc]
    rintro u ⟨hu, huc⟩
    refine ⟨hu, hUG hu, hGZ (hUG hu), fun x hx => ?_⟩
    rw [← Subgroup.mem_centralizer_iff.mp huc x hx, mul_inv_cancel_right, mul_inv_cancel]
    exact one_mem _

end CFSG.Quasithin.H13.L32A
