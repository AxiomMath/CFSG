module

public import CFSG.Quasithin.H13.L32AL2r

public section

namespace CFSG.Quasithin.H13.L32A.L2

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open CFSG.Quasithin.H13.L32A.C

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem mIdx_eq_one {X Y : Subgroup G} (hX : IsPGroup 2 X) (h : Y.relIndex X = 2) :
    mIdx X Y = 1 := by
  have h1 := HypF98.relIndex_eq_two_pow_mIdx (Y := Y) hX
  rw [h] at h1
  have h2 : 2 ^ 1 = 2 ^ mIdx X Y := by rw [pow_one]; exact h1
  exact (Nat.pow_right_injective (le_refl 2) h2).symm

theorem exists_alpha (hF : HypF98 T V L (fsuV1 T V) V (A6.g1 T V))
    (hcase : L2CaseOne G T L V) :
    ∃ (c : G) (t : ↥(A6.g1 T V)),
      Quasithin.conjSub c (conjClosure V (A6.g1 T V)) ≤ pCoreOf 2 (l1 T L V ⊔ T) ∧
      fsuV1 T V ≤ Quasithin.conjSub c (conjClosure V (A6.g1 T V)) ∧
      Quasithin.conjSub c (fsuV1 T V) ≤ conjClosure V (A6.g1 T V) ∧
      Quasithin.conjSub c (fsuV1 T V) ≠ fsuV1 T V ∧
      (F8.DH V (fsuV1 T V) (A6.g1 T V) c).relIndex (conjClosure V (A6.g1 T V)) = 2 ∧
      (t : G) ∈ Quasithin.conjSub c (conjClosure V (A6.g1 T V)) ∧
      (t : G) ∉ pCoreOf 2 (A6.g1 T V) ∧ t * t = 1 := by
  obtain ⟨-, γ, γ', g, s, hcard, hH2, hV1γ, hA1U⟩ := hcase
  have hUγH := hF.Uγ_le_H s
  have hUp : IsPGroup 2 ↥(conjClosure V (A6.g1 T V)) := F7.isPGroup_of_isElemAbelian hF.F911_3
  have hUγp : IsPGroup 2 ↥(F8.Uγ V (A6.g1 T V) (g : G)) :=
    F7.isPGroup_of_isElemAbelian hF.isElemAbelian_Uγ
  have hγ2 : (F8.Dγ V (fsuV1 T V) (A6.g1 T V) (g : G)).relIndex
      (F8.Uγ V (A6.g1 T V) (g : G)) = 2 := by
    rw [hF.Dγ_eq_inf_pCoreOf s, inf_comm, Subgroup.inf_relIndex_right, ← card_modO2Image' hUγH,
      hcard]
  have hm1 := mIdx_eq_one hUγp hγ2
  have hm2 := mIdx_eq_one hUp hH2
  obtain ⟨h, N⟩ := exists_not1471_of_setup hF s (by rw [hm1]; norm_num)
    (le_of_eq (by rw [hm1, hm2]))
  have hhH : (h : G) ∈ A6.g1 T V := N.mem
  have hhU : Quasithin.conjSub (h : G) (conjClosure V (A6.g1 T V)) = conjClosure V (A6.g1 T V) :=
    L32A.conjSub_eq_self_iff.mpr (le_normalizer_conjClosure V (A6.g1 T V) hhH)
  have hhV₁ : Quasithin.conjSub (h : G) (fsuV1 T V) = fsuV1 T V :=
    L32A.conjSub_eq_self_iff.mpr (hF.toHypF91.H_normalizes_V₁ hhH)
  have hc : Quasithin.conjSub ((h : G) * (g : G)) (conjClosure V (A6.g1 T V)) =
      Quasithin.conjSub (h : G) (F8.Uγ V (A6.g1 T V) (g : G)) := by
    rw [Quasithin.conjSub_mul]
    rfl
  obtain ⟨x, hx, hx1⟩ : ∃ x ∈ modO2Image (A6.g1 T V) (F8.Uγ V (A6.g1 T V) (g : G)), x ≠ 1 := by
    by_contra hall
    push Not at hall
    have : modO2Image (A6.g1 T V) (F8.Uγ V (A6.g1 T V) (g : G)) = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      exact Subgroup.mem_bot.mpr (hall y hy)
    rw [this, Subgroup.card_bot] at hcard
    exact absurd hcard (by norm_num)
  obtain ⟨t₀, ht₀U, rfl⟩ := mem_modO2Image'.mp hx
  have ht₀Q : (t₀ : G) ∉ pCoreOf 2 (A6.g1 T V) := by
    intro hq
    apply hx1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, ← pCoreOf_subgroupOf',
      Subgroup.mem_subgroupOf]
    exact hq
  refine ⟨(h : G) * (g : G), ⟨(h : G), hhH⟩ * t₀ * ⟨(h : G), hhH⟩⁻¹, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  ·
    have h1 := N.uα_le hF
    rw [show L₁Of L (fsuV1 T V) = l1 T L V from oTwoRes_eq_oTwoUpper _] at h1
    rw [hc]
    exact h1
  ·
    rw [hc, ← hhV₁]
    exact Quasithin.conjSub_mono _ hV1γ
  ·
    rw [Quasithin.conjSub_mul, ← hhU]
    exact Quasithin.conjSub_mono _ hA1U
  ·
    intro heq
    have hcN : (h : G) * (g : G) ∈ A6.g1 T V := L32A.conjSub_eq_self_iff.mp heq
    apply N.uα_ne hF
    rw [← hc]
    exact L32A.conjSub_eq_self_iff.mpr (le_normalizer_conjClosure V (A6.g1 T V) hcN)
  ·
    have e : F8.DH V (fsuV1 T V) (A6.g1 T V) ((h : G) * (g : G)) =
        Quasithin.conjSub (h : G) (F8.DH V (fsuV1 T V) (A6.g1 T V) (g : G)) := by
      rw [F8.DH, F8.DH, Quasithin.conjSub_centralizerMod, F8.A₁, F8.A₁, F8.Uγ, F8.Uγ,
        Quasithin.conjSub_mul, Quasithin.conjSub_mul, hhU]
    rw [e]
    calc (Quasithin.conjSub (h : G) (F8.DH V (fsuV1 T V) (A6.g1 T V) (g : G))).relIndex
          (conjClosure V (A6.g1 T V)) =
        (Quasithin.conjSub (h : G) (F8.DH V (fsuV1 T V) (A6.g1 T V) (g : G))).relIndex
          (Quasithin.conjSub (h : G) (conjClosure V (A6.g1 T V))) := by rw [hhU]
      _ = (F8.DH V (fsuV1 T V) (A6.g1 T V) (g : G)).relIndex (conjClosure V (A6.g1 T V)) :=
          Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj (h : G)).injective
      _ = 2 := hH2
  ·
    rw [hc]
    exact Quasithin.mul_mem_conjSub ht₀U
  ·
    intro hq
    apply ht₀Q
    have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 (A6.g1 T V)
      ((A6.g1 T V).inv_mem hhH)) _).mp hq
    simpa [mul_assoc] using this
  ·
    have h2 : (t₀ : G) * t₀ = 1 := by
      have := hF.isElemAbelian_Uγ.2 _ ht₀U
      rwa [pow_two] at this
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one]
    calc (h : G) * t₀ * (h : G)⁻¹ * ((h : G) * t₀ * (h : G)⁻¹) =
          (h : G) * ((t₀ : G) * t₀) * (h : G)⁻¹ := by group
      _ = 1 := by rw [h2, mul_one, mul_inv_cancel]

end CFSG.Quasithin.H13.L32A.L2
