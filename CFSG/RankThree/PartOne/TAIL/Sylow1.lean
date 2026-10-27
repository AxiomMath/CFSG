module

public import CFSG.RankThree.PartOne.TAIL.Orbit
public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.RankThree.PartOne.TAIL

open Subgroup

instance fact_prime_seven : Fact (Nat.Prime 7) := ⟨by decide⟩

theorem pow_le_of_mul_eq {k n m r : ℕ} (hm : ¬ 7 ∣ m) (h : 7 ^ k * r = 7 ^ n * m) : k ≤ n := by
  by_contra hlt
  rw [not_le] at hlt
  apply hm
  have h1 : 7 ^ n * 7 ∣ 7 ^ n * m := by
    rw [← h]
    calc 7 ^ n * 7 = 7 ^ (n + 1) := (pow_succ 7 n).symm
      _ ∣ 7 ^ k := pow_dvd_pow 7 hlt
      _ ∣ 7 ^ k * r := dvd_mul_right _ _
  exact Nat.dvd_of_mul_dvd_mul_left (by positivity) h1

theorem pow_eq_of_mul_eq {k n m r : ℕ} (hm : ¬ 7 ∣ m) (hr : ¬ 7 ∣ r)
    (h : 7 ^ k * r = 7 ^ n * m) : k = n :=
  le_antisymm (pow_le_of_mul_eq hm h) (pow_le_of_mul_eq hr h.symm)

variable {G : Type} [Group G]

structure PData (A B : Subgroup G) (y₀ : G) (P : Subgroup G) : Prop where
  A_le : A ≤ P
  y₀_mem : y₀ ∈ P
  le_Xs : P ≤ Xs A B
  pgroup : IsPGroup 7 P
  idx : ¬ 7 ∣ P.relIndex (Xs A B)

theorem PData.le_normalizer {A B : Subgroup G} {y₀ : G} {P : Subgroup G} (hP : PData A B y₀ P) :
    P ≤ Subgroup.normalizer (A : Set G) :=
  hP.le_Xs.trans Xs_le_normalizer

namespace SchemeHyp

variable [Finite G] {A B : Subgroup G} {c b d y₀ : G} {K M₀ : Subgroup G}
  (h : SchemeHyp G A B c b d y₀ K M₀)

include h

theorem y₀_mem_Xs : y₀ ∈ Xs A B := by
  obtain ⟨β₀, hβ₀B, _, hy⟩ := h.y₀_c
  refine h.mem_Xs_of_moves h.y₀_cB ?_
  have : y₀ * c * y₀⁻¹ * c⁻¹ = β₀ := by
    rw [hy, h.c_comm_B hβ₀B]
    group
  rw [this]
  exact hβ₀B

theorem A_le_centralizer : A ≤ Subgroup.centralizer (A : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact h.A_comm hy hx

theorem A_pgroup : IsPGroup 7 A := IsPGroup.of_card (n := 3) h.A_card

theorem B_pgroup : IsPGroup 7 B := IsPGroup.of_card (n := 2) h.B_card

theorem zpowers_y₀_pgroup : IsPGroup 7 (Subgroup.zpowers y₀) := by
  obtain ⟨k, hk⟩ := h.y₀_ord
  exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])

theorem R_le_Xs : A ⊔ Subgroup.zpowers y₀ ≤ Xs A B :=
  sup_le (h.A_le_centralizer.trans (centralizer_le_Xs h.B_le))
    ((Subgroup.zpowers_le).mpr h.y₀_mem_Xs)

theorem R_pgroup : IsPGroup 7 ↥(A ⊔ Subgroup.zpowers y₀) :=
  h.A_pgroup.to_sup_of_normal_left' h.zpowers_y₀_pgroup
    ((Subgroup.zpowers_le).mpr (Xs_le_normalizer h.y₀_mem_Xs))

theorem exists_P : ∃ P : Subgroup G, PData A B y₀ P := by
  have hR := h.R_le_Xs
  have hR' : IsPGroup 7 ↥((A ⊔ Subgroup.zpowers y₀).subgroupOf (Xs A B)) :=
    h.R_pgroup.comap_subtype
  obtain ⟨S, hS⟩ := hR'.exists_le_sylow
  have hmem : ∀ x : G, x ∈ A ⊔ Subgroup.zpowers y₀ → x ∈ (S : Subgroup ↥(Xs A B)).map (Xs A B).subtype :=
    fun x hx => ⟨⟨x, hR hx⟩, hS (show (⟨x, hR hx⟩ : ↥(Xs A B)) ∈
      (A ⊔ Subgroup.zpowers y₀).subgroupOf (Xs A B) from hx), rfl⟩
  refine ⟨(S : Subgroup ↥(Xs A B)).map (Xs A B).subtype, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · exact fun a ha => hmem a ((le_sup_left : A ≤ A ⊔ Subgroup.zpowers y₀) ha)
  · exact hmem y₀ ((le_sup_right : Subgroup.zpowers y₀ ≤ A ⊔ Subgroup.zpowers y₀)
    (Subgroup.mem_zpowers y₀))
  · exact Subgroup.map_subtype_le _
  · exact S.isPGroup'.map _
  · exact (CFSG.ABGLocalTools.isSylowOf_iff.mp ⟨S, rfl⟩).2.2

theorem not_dvd_relIndex_centralizer :
    ¬ 7 ∣ A.relIndex (Subgroup.centralizer (A : Set G)) := by
  obtain ⟨_, _, hidx⟩ := h.A_sylow_cent
  have hle : Subgroup.centralizer (A : Set G) ≤ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr h.c_mem)
  have := Subgroup.relIndex_mul_relIndex A (Subgroup.centralizer (A : Set G))
    (Subgroup.centralizer ({c} : Set G)) h.A_le_centralizer hle
  intro hd
  exact hidx (this ▸ hd.mul_right _)

variable {P : Subgroup G} (hP : PData A B y₀ P)

include hP

theorem card_P : Nat.card P = 7 ^ 5 := by
  have hX : Nat.card (Xs A B) = Nat.card (Subgroup.centralizer (A : Set G)) * 7 ^ 2 := h.card_Xs
  have hC : A.relIndex (Subgroup.centralizer (A : Set G)) * 7 ^ 3 =
      Nat.card (Subgroup.centralizer (A : Set G)) := by
    have := Subgroup.relIndex_mul_card A (Subgroup.centralizer (A : Set G))
    rwa [inf_eq_left.mpr h.A_le_centralizer, h.A_card] at this
  have hPX : P.relIndex (Xs A B) * Nat.card P = Nat.card (Xs A B) := by
    have := Subgroup.relIndex_mul_card P (Xs A B)
    rwa [inf_eq_left.mpr hP.le_Xs] at this
  obtain ⟨k, hk⟩ := hP.pgroup.exists_card_eq
  rw [hk, hX, ← hC] at hPX
  have e : 7 ^ k * P.relIndex (Xs A B) =
      7 ^ 5 * A.relIndex (Subgroup.centralizer (A : Set G)) := by
    rw [mul_comm, hPX]; ring
  have := pow_eq_of_mul_eq h.not_dvd_relIndex_centralizer hP.idx e
  rw [hk, this]

theorem P_le_normalizer_K : P ≤ Subgroup.normalizer (K : Set G) := by
  intro x hx
  apply h.P_normK x (Xs_le_centralizer (hP.le_Xs hx))
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hP.pgroup) ⟨x, hx⟩
  exact ⟨k, by rwa [Subgroup.orderOf_mk] at hk⟩

theorem P_sylow_normalizer : ¬ 7 ∣ P.relIndex (Subgroup.normalizer (A : Set G)) := by
  obtain ⟨m, hm, hN⟩ := h.card_normalizer_A
  have hPN : P.relIndex (Subgroup.normalizer (A : Set G)) * Nat.card P =
      Nat.card (Subgroup.normalizer (A : Set G)) := by
    have := Subgroup.relIndex_mul_card P (Subgroup.normalizer (A : Set G))
    rwa [inf_eq_left.mpr hP.le_normalizer] at this
  rw [h.card_P hP, hN] at hPN
  have : P.relIndex (Subgroup.normalizer (A : Set G)) = m := by
    apply Nat.eq_of_mul_eq_mul_right (show 0 < 7 ^ 5 by norm_num)
    rw [hPN]; ring
  rw [this]
  exact hm

theorem eps_surj_P : ∀ β ∈ B, ∃ x ∈ P, eps c x = β := by
  intro β hβ
  have hSyl : CFSG.ABGLocalTools.IsSylowOf 7 P (Xs A B) :=
    CFSG.ABGLocalTools.isSylowOf_iff.mpr ⟨hP.le_Xs, hP.pgroup, hP.idx⟩
  obtain ⟨S, hS⟩ := hSyl.exists_sylow_eq_subgroupOf
  have hf : Function.Surjective h.epsHom := h.epsHom_surjective
  have hB7 : IsPGroup 7 ↥B := h.B_pgroup
  have htop : (⊤ : Subgroup ↥B) = (Sylow.mapSurjective hf S : Subgroup ↥B) :=
    (Sylow.mapSurjective hf S).3 (hB7.to_subgroup ⊤) le_top
  have hmem : (⟨β, hβ⟩ : ↥B) ∈ (S : Subgroup ↥(Xs A B)).map h.epsHom := by
    have : (⟨β, hβ⟩ : ↥B) ∈ (⊤ : Subgroup ↥B) := Subgroup.mem_top _
    rw [htop, Sylow.coe_mapSurjective] at this
    exact this
  obtain ⟨x, hxS, hx⟩ := hmem
  rw [hS] at hxS
  refine ⟨(x : G), hxS, ?_⟩
  have := congrArg Subtype.val hx
  rwa [SchemeHyp.epsHom_apply] at this

end SchemeHyp

end CFSG.RankThree.PartOne.TAIL
