module

public import CFSG.Quasithin.Background.E2TwoProofFam
public import CFSG.Quasithin.Background.E2TwoProofY
public import CFSG.Quasithin.Background.E2Hyp

public section

namespace CFSG.Quasithin.Ch3E213M.OS

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin B6 E2P

variable {G : Type} [Group G] {H T M V K : Subgroup G}

theorem subgroupOf_le_normalizer {A B C : Subgroup G}
    (h : A ≤ Subgroup.normalizer (B : Set G)) :
    A.subgroupOf C ≤ Subgroup.normalizer (B.subgroupOf C : Set ↥C) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [Subgroup.mem_subgroupOf] at ha
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
  exact Subgroup.mem_normalizer_iff.mp (h ha) (x : G)

theorem normal_star (hKH : K ≤ H) (hHK : H ≤ Subgroup.normalizer (K : Set G)) :
    (E2.star M H K).Normal := by
  have hn : (K.subgroupOf H).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr hHK
  rw [star_def]
  exact hn.map _ (starMap_surjective M H)

theorem star_le_normalizer (hTV : T ≤ Subgroup.normalizer (V : Set G)) :
    E2.star M H T ≤ Subgroup.normalizer (E2.star M H V : Set (E2.StarQuot M H)) := by
  rw [star_def, star_def]
  exact (Subgroup.map_mono (subgroupOf_le_normalizer hTV)).trans (Subgroup.le_normalizer_map _)

theorem star_sq (hV : ∀ v ∈ V, v * v = 1) : ∀ x ∈ E2.star M H V, x * x = 1 := by
  rintro _ ⟨v, hv, rfl⟩
  rw [← map_mul]
  have : v * v = 1 := Subtype.ext (hV _ (Subgroup.mem_subgroupOf.mp hv))
  rw [this, map_one]

theorem star_comm (hV : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v) :
    ∀ x ∈ E2.star M H V, ∀ y ∈ E2.star M H V, x * y = y * x := by
  rintro _ ⟨v, hv, rfl⟩ _ ⟨w, hw, rfl⟩
  rw [← map_mul, ← map_mul]
  have : v * w = w * v :=
    Subtype.ext (hV _ (Subgroup.mem_subgroupOf.mp hv) _ (Subgroup.mem_subgroupOf.mp hw))
  rw [this]

theorem pCoreOf_subgroupOf_le [Finite G] (hMH : M ≤ H) :
    (pCoreOf 2 M).subgroupOf H ≤ pCoreOf 2 (M.subgroupOf H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    (Subgroup.subgroupOf_mono H (CFSG.LieType.BorelTits.pCoreOf_le 2 M))
    (subgroupOf_le_normalizer (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M)) ?_
  exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).of_equiv
    (Subgroup.subgroupOfEquivOfLe ((CFSG.LieType.BorelTits.pCoreOf_le 2 M).trans hMH)).symm

theorem star_le_pCoreOf [Finite G] (hMH : M ≤ H) (hVM : V ≤ pCoreOf 2 M) :
    E2.star M H V ≤ pCoreOf 2 (E2.star M H M) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [star_def, star_def]
  exact (Subgroup.map_mono ((Subgroup.subgroupOf_mono H hVM).trans
    (pCoreOf_subgroupOf_le hMH))).trans (CFSG.LieType.BorelTits.map_pCoreOf_le _ _)

theorem relIndex_le_card_star [Finite G] (hyp : E2.Hyp28 H T M V) :
    (V ⊓ pCoreOf 2 H).relIndex V ≤ Nat.card (E2.star M H V) := by
  rw [star_def, ← Subgroup.relIndex_ker, ker_starMap,
    Subgroup.relIndex_subgroupOf hyp.le_H, ← Subgroup.inf_relIndex_right (kerIn M H) V]
  have hle : kerIn M H ⊓ V ≤ V ⊓ pCoreOf 2 H := by
    refine le_inf inf_le_right ?_
    exact hyp.minParabolic.le_pCoreOf_of_isPGroup_of_le_kerIn
      ((B6.isPGroup_of_isElemAbelian hyp.elem).to_le inf_le_right) inf_le_left
  exact Subgroup.relIndex_le_of_le_left hle (Subgroup.index_ne_zero_of_finite)

section Abstract

variable {X : Type} [Group X] [Finite X] {K T M : Subgroup X}

omit [Finite X] in
theorem exists_two_pow_mem (hK : K.Normal) (hsup : K ⊔ T = ⊤) (hT : IsPGroup 2 T) (x : X) :
    ∃ j : ℕ, x ^ 2 ^ j ∈ K := by
  obtain ⟨k, hk, t, ht, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer'
    (fun y _ => (Subgroup.normalizer_eq_top_iff.mpr hK).symm ▸ Subgroup.mem_top y)
    (hsup.symm ▸ Subgroup.mem_top x : x ∈ K ⊔ T)
  obtain ⟨j, hj⟩ := hT ⟨t, ht⟩
  refine ⟨j, ?_⟩
  rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, QuotientGroup.mk_mul,
    (QuotientGroup.eq_one_iff k).mpr hk, one_mul, ← QuotientGroup.mk_pow]
  rw [QuotientGroup.eq_one_iff]
  have : t ^ 2 ^ j = 1 := congrArg Subtype.val hj
  rw [this]
  exact K.one_mem

theorem centralizer_eq_bot (hmp : MinParabolic (⊤ : Subgroup X) T M) (hker : kerIn M ⊤ = ⊥)
    (hK : K.Normal) (hZ : Subgroup.center ↥K = ⊥) (hsup : K ⊔ T = ⊤) :
    Subgroup.centralizer (K : Set X) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := Subgroup.centralizer (K : Set X) with hC
  have hCK : ∀ c ∈ C, c ∈ K → c = 1 := fun c hc hcK => by
    have : (⟨c, hcK⟩ : ↥K) ∈ Subgroup.center ↥K := Subgroup.mem_center_iff.mpr fun y =>
      Subtype.ext ((Subgroup.mem_centralizer_iff.mp hc) y y.2)
    rw [hZ] at this
    exact congrArg Subtype.val (Subgroup.mem_bot.mp this)
  have hCn : (⊤ : Subgroup X) ≤ Subgroup.normalizer (C : Set X) := by
    have : C.Normal := Subgroup.normal_centralizer
    rw [Subgroup.normalizer_eq_top_iff.mpr this]
  have hC2 : IsPGroup 2 ↥C := by
    intro c
    obtain ⟨j, hj⟩ := exists_two_pow_mem hK hsup hmp.isSylow.2.1 (c : X)
    refine ⟨j, Subtype.ext ?_⟩
    exact hCK _ (C.pow_mem c.2 _) hj
  have hle : C ≤ pCoreOf 2 ⊤ :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_top hCn hC2
  rw [eq_bot_iff, ← hker]
  exact hle.trans hmp.pCoreOf_le_kerIn

end Abstract

end CFSG.Quasithin.Ch3E213M.OS
