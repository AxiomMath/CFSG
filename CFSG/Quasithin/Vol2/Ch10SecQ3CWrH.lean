module

public import CFSG.Quasithin.Vol2.Ch10SecQ3CI
public import CFSG.Adapters.LinearSmallCatalog
import CFSG.Adapters.StatedClassicalUnitaryOrders
import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.Quasithin.Vol2.Ch10SecQ3CWrA

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

namespace C11AmS

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

theorem eq_bot_of_normal_star {H T X : Subgroup G} (hmin : MinParabolic H T X)
    (C : Subgroup (E2.StarQuot X H)) (hC : C.Normal) (h2 : IsPGroup 2 C) : C = ⊥ := by
  have hker : (QuotientGroup.mk' ((kerIn X H).subgroupOf H)).ker ≤ X.subgroupOf H := by
    rw [QuotientGroup.ker_mk']
    exact fun x hx => Subgroup.mem_subgroupOf.mpr (kerIn_le (Subgroup.mem_subgroupOf.mp hx))
  have hmP := hmin.subgroupOf.map_of_surjective (QuotientGroup.mk'_surjective _) hker
  have hk : kerIn ((X.subgroupOf H).map (QuotientGroup.mk' ((kerIn X H).subgroupOf H))) ⊤ = ⊥ := by
    rw [B6.kerIn_map_top (QuotientGroup.mk'_surjective _) hker, B6.kerIn_subgroupOf_top]
    exact QuotientGroup.map_mk'_self _
  have h1 := hmP.pCore_le_kerIn
  rw [hk] at h1
  exact le_bot_iff.mp ((CFSG.LieType.BorelTits.le_pCore 2 hC h2).trans h1)

theorem isSylowTwoOf_star {H T X : Subgroup G} (hmin : MinParabolic H T X) :
    IsSylowTwoOf (E2.star X H T) ⊤ := by
  have hker : (QuotientGroup.mk' ((kerIn X H).subgroupOf H)).ker ≤ X.subgroupOf H := by
    rw [QuotientGroup.ker_mk']
    exact fun x hx => Subgroup.mem_subgroupOf.mpr (kerIn_le (Subgroup.mem_subgroupOf.mp hx))
  exact (hmin.subgroupOf.map_of_surjective (QuotientGroup.mk'_surjective _) hker).isSylow

theorem exists_borel_elt (hBC : FactBorelCartan) {X H K : Subgroup G} {n : ℕ} (hn : 2 ≤ n)
    (htype : E2.IsBenderOf n ↥(E2.star X H K) ∨ IsPSL 3 2 n ↥(E2.star X H K) ∨
      IsPSp4 2 n ↥(E2.star X H K))
    (hBor : E2.IsBorelIn (E2.star X H K) (E2.star X H (X ⊓ K))) :
    ∃ d ∈ E2.star X H (X ⊓ K), orderOf d = 2 ^ n - 1 := by
  obtain ⟨S, hS, hB⟩ := hBor
  obtain ⟨d, hdN, hdo⟩ := hBC _ n hn htype _ (isSylowTwoOf_top_subgroupOf hS)
  refine ⟨d, ?_, by rw [Subgroup.orderOf_coe]; exact hdo⟩
  rw [hB]
  exact ⟨d.2, coe_mem_normalizer hS.1 hdN⟩

theorem exists_hall_dvd {X H K T B₀ B : Subgroup G} (hT : IsSylowTwoOf T X)
    (hB₀ : Lin2.IsHallTwoPrimeOf B₀ X)
    (hTQ : T ≤ pCoreOf 2 X ⊔ (T ⊓ Subgroup.normalizer (B₀ : Set G)))
    (hB : Lin2.IsHallTwoPrimeOf B X) {d : E2.StarQuot X H} (hd : d ∈ E2.star X H (X ⊓ K))
    (hdo : Odd (orderOf d)) : ∃ b ∈ B, orderOf d ∣ orderOf b := by
  obtain ⟨⟨x, hxH⟩, hx, hxe⟩ := hd
  have hxXK : x ∈ X ⊓ K := hx
  have hdvd : orderOf d ∣ orderOf x := by
    rw [← hxe]
    have h := orderOf_map_dvd (QuotientGroup.mk' ((kerIn X H).subgroupOf H)) (⟨x, hxH⟩ : ↥H)
    rwa [← Subgroup.orderOf_coe] at h
  obtain ⟨a, r, hr, hxar⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
  have hyo : orderOf (x ^ 2 ^ a) = r := by
    rw [orderOf_pow_of_dvd (by positivity) (by rw [hxar]; exact dvd_mul_right _ _), hxar,
      Nat.mul_div_cancel_left _ (by positivity)]
  have hdvr : orderOf d ∣ r := by
    rw [hxar] at hdvd
    exact (Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hdo)).dvd_of_dvd_mul_left hdvd
  obtain ⟨b, hb, hbdvd⟩ := exists_mem_orderOf_dvd hT hB₀ hTQ hB (X.pow_mem hxXK.1 _)
    (by rw [hyo]; exact hr)
  rw [hyo] at hbdvd
  exact ⟨b, hb, hdvr.trans hbdvd⟩

theorem eq_two_of_dvd_nine {n : ℕ} (hn : 2 ≤ n) (h : 2 ^ n - 1 ∣ 9) : n = 2 := by
  have h1 := Nat.le_of_dvd (by norm_num) h
  have h4 : n < 4 := by
    by_contra h4
    have : 2 ^ 4 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  interval_cases n
  · rfl
  · norm_num at h

theorem not_isSz_two {X : Type} [Group X] : ¬ IsSz 2 X := by
  rintro ⟨-, a, ha, K, -, -, hf, -⟩
  omega

theorem nonempty_equiv_aFive {Y : Type} [Group Y]
    (h : IsPSL 2 2 2 Y) : Nonempty (Y ≃* AFive) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  obtain ⟨f⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five K
    (Or.inl (by rw [hK]; norm_num))
  exact ⟨e.trans f⟩

theorem card_of_isPSL_two_two_two {Y : Type} [Group Y] (h : IsPSL 2 2 2 Y) :
    Nat.card Y = 60 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_four h

theorem card_of_isPSU_three_two_two {Y : Type} [Group Y] (h : IsPSU 3 2 2 Y) :
    Nat.card Y = 62400 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_three_four h

end C11AmS

end CFSG.Quasithin.Vol2.Ch10.SecB
