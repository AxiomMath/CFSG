module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P2Sec

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.LieType.BorelTits CFSG.Quasithin.C1Pack
  CFSG.Quasithin.S1417

namespace E9P2.Sec

section Sylow

variable {G : Type} [Group G] [Finite G] {T H PQ : Subgroup G} {V : Type} [CommGroup V]
  [Finite V] {β : ↥H →* MulAut V}

namespace BetaData

theorem exists_sylow (hb : BetaData T H PQ β) :
    ∃ P : Subgroup G, P ≤ PQ ∧ Nat.card P = 9 ∧ P ⊓ pCoreOf 2 H = ⊥ := by
  obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 H).exists_card_eq
  have hPQ : Nat.card PQ = 9 * 2 ^ k := by
    have h1 := Subgroup.relIndex_mul_card (pCoreOf 2 H) PQ
    rw [inf_eq_left.mpr hb.QPQ, hb.relIndex_PQ, hk] at h1
    exact h1.symm
  obtain ⟨P₀⟩ := (inferInstance : Nonempty (Sylow 3 ↥PQ))
  have hP₀ : Nat.card ↥(P₀ : Subgroup ↥PQ) = 9 := by
    rw [P₀.card_eq_multiplicity, hPQ,
      Nat.factorization_mul (by norm_num) (by positivity), show (9 : ℕ) = 3 ^ 2 by norm_num,
      Nat.Prime.factorization_pow Nat.prime_three, Nat.Prime.factorization_pow Nat.prime_two]
    simp
  have hP : Nat.card ↥((P₀ : Subgroup ↥PQ).map PQ.subtype) = 9 := by
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective PQ), hP₀]
  refine ⟨_, Subgroup.map_subtype_le _, hP, ?_⟩
  have h1 : Nat.card ↥((P₀ : Subgroup ↥PQ).map PQ.subtype ⊓ pCoreOf 2 H) ∣ 9 :=
    hP ▸ Subgroup.card_dvd_of_le inf_le_left
  have h2 : Nat.card ↥((P₀ : Subgroup ↥PQ).map PQ.subtype ⊓ pCoreOf 2 H) ∣ 2 ^ k :=
    hk ▸ Subgroup.card_dvd_of_le inf_le_right
  have hcop : Nat.Coprime 9 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
  exact Subgroup.card_eq_one.mp (Nat.dvd_one.mp (hcop.gcd_eq_one ▸ Nat.dvd_gcd h1 h2))

omit [Finite G] in
theorem map_sylow_eq (hb : BetaData T H PQ β) {P : Subgroup G} (hPPQ : P ≤ PQ)
    (hP9 : Nat.card P = 9) (hPQ : P ⊓ pCoreOf 2 H = ⊥) :
    (P.subgroupOf H).map β = (PQ.subgroupOf H).map β := by
  have hle : (P.subgroupOf H).map β ≤ (PQ.subgroupOf H).map β :=
    Subgroup.map_mono fun y hy =>
      Subgroup.mem_subgroupOf.mpr (hPPQ (Subgroup.mem_subgroupOf.mp hy))
  have hc : Nat.card ((P.subgroupOf H).map β) = 9 := by
    rw [hb.card_map (hPPQ.trans hb.PQH)]
    have h1 := Subgroup.relIndex_mul_card (pCoreOf 2 H) P
    rw [inf_comm, hPQ, Subgroup.card_bot, mul_one, hP9] at h1
    exact h1
  have : Finite ↥((PQ.subgroupOf H).map β) :=
    Nat.finite_of_card_ne_zero (by rw [hb.str.card_P]; norm_num)
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hb.str.card_P, hc])

theorem exists_P (hb : BetaData T H PQ β) :
    ∃ P : Subgroup G, P ≤ oTwoUpper H ∧ IsElemAbelian 3 P ∧ Nat.card P = 9 ∧
      ∀ h ∈ H, ∃ x ∈ P, ∃ t ∈ T, h = x * t := by
  obtain ⟨P, hPPQ, hP9, hPQ⟩ := hb.exists_sylow
  have hexp : ∀ x ∈ P, x ^ 3 = 1 := fun x hx => by
    have h1 : x ^ 3 ∈ P ⊓ pCoreOf 2 H := ⟨P.pow_mem hx 3, hb.pow_three_PQ (hPPQ hx)⟩
    rwa [hPQ, Subgroup.mem_bot] at h1
  have hcomm : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := fun x hx y hy => by
    have h1 : x * y * x⁻¹ * y⁻¹ ∈ P ⊓ pCoreOf 2 H :=
      ⟨P.mul_mem (P.mul_mem (P.mul_mem hx hy) (P.inv_mem hx)) (P.inv_mem hy),
        hb.comm_PQ (hPPQ hx) (hPPQ hy)⟩
    rw [hPQ, Subgroup.mem_bot] at h1
    exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h1)
  have hodd : P ≤ oTwoUpper H := fun x hx =>
    mem_oTwoUpper_of_odd (hb.PQH (hPPQ hx)) (Odd.of_dvd_nat (by decide : Odd 9)
      (by rw [← hP9]; exact Subgroup.orderOf_dvd_natCard P hx))
  refine ⟨P, hodd, ⟨⟨⟨fun a b => Subtype.ext (hcomm a.1 a.2 b.1 b.2)⟩⟩, hexp⟩, hP9, ?_⟩
  intro h hh
  obtain ⟨a, ha, s, hs, hxas⟩ := hb.str.exists_mul (⟨⟨h, hh⟩, rfl⟩ : β ⟨h, hh⟩ ∈ β.range)
  rw [← hb.map_sylow_eq hPPQ hP9 hPQ] at ha
  obtain ⟨u, hu, rfl⟩ := ha
  obtain ⟨w, hw, rfl⟩ := hs
  have hq : β ((u * w)⁻¹ * ⟨h, hh⟩) = 1 := by
    rw [map_mul, map_inv, map_mul, hxas, inv_mul_cancel]
  have hqQ : ((u : G) * (w : G))⁻¹ * h ∈ pCoreOf 2 H := (hb.beta_eq_one_iff _).mp hq
  refine ⟨(u : G), Subgroup.mem_subgroupOf.mp hu, (w : G) * (((u : G) * (w : G))⁻¹ * h),
    T.mul_mem (Subgroup.mem_subgroupOf.mp hw) (hb.QT hqQ), ?_⟩
  group

end BetaData

end Sylow

end E9P2.Sec

section Main

variable {G : Type} [Group G] [Finite G] {T M H PQ : Subgroup G} {p : ℕ}

theorem e9_exists_P (h35 : Lemma1435) (S : Setting146 G T M) (hred : IsRedCE T M H PQ p)
    (hshape : IsE9Z4Shape T H p) :
    ∃ P : Subgroup G, P ≤ oTwoUpper H ∧ IsElemAbelian 3 P ∧ Nat.card P = 9 ∧
      ∀ h ∈ H, ∃ x ∈ P, ∃ t ∈ T, h = x * t := by
  obtain ⟨V, _, _, β, hb⟩ := E9P2.Sec.exists_betaData h35 S hred hshape
  exact hb.exists_P

end Main

end CFSG.Quasithin
