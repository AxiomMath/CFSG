module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2LocB
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1
  CFSG.QuasithinUnique.Tight CFSG.QuasithinUnique.BenderBranch
  CFSG.ComponentClassification.AschbacherTightEmbedding

namespace S143

namespace InspW2

section Cnt

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} {A : Subgroup G} {t d x : G}

theorem card_rOf_sup_qOf_eq (h : Ctx T M g A t d x) : Nat.card ↥(rOf T M ⊔ qOf T) = 256 := by
  have hRQT : rOf T M ⊔ qOf T ≤ T := rq_le_of_hyp h.c.h1281
  have hmul := Subgroup.relIndex_mul_card (rOf T M ⊔ qOf T) T
  rw [h.c18.a.rq_index, inf_of_le_left hRQT, card_T h] at hmul
  omega

theorem relIndex_rOf_Gw (h : Ctx T M g A t d x) : (Gw d x).relIndex (rOf T M) = 4 := by
  obtain ⟨φ⟩ := h.hR
  have h16 : Nat.card ↥(rOf T M ⊓ Gw d x) = 16 := by
    rw [Nat.card_congr φ.toEquiv, Nat.card_prod]
    have : Nat.card (Multiplicative (ZMod 4)) = 4 := by
      rw [Nat.card_eq_fintype_card]; decide
    rw [this]
  have hmul := Subgroup.relIndex_mul_card (Gw d x) (rOf T M)
  rw [inf_comm, h16, card_rOf h.c] at hmul
  omega

theorem card_Tw_inf_RQ_le (h : Ctx T M g A t d x) :
    Nat.card ↥(Tw T d x ⊓ (rOf T M ⊔ qOf T)) ≤ 64 := by
  have hRQT : rOf T M ⊔ qOf T ≤ T := rq_le_of_hyp h.c.h1281
  have hle : 4 ≤ (Gw d x).relIndex (rOf T M ⊔ qOf T) := by
    rw [← relIndex_rOf_Gw h]
    exact Subgroup.relIndex_le_of_le_right le_sup_left Subgroup.index_ne_zero_of_finite
  have hmul := Subgroup.relIndex_mul_card (Gw d x) (rOf T M ⊔ qOf T)
  rw [card_rOf_sup_qOf_eq h] at hmul
  have heq : Tw T d x ⊓ (rOf T M ⊔ qOf T) = Gw d x ⊓ (rOf T M ⊔ qOf T) := by
    ext y
    simp only [Subgroup.mem_inf]
    exact ⟨fun hy => ⟨hy.1.2, hy.2⟩, fun hy => ⟨⟨hRQT hy.2, hy.1⟩, hy.2⟩⟩
  rw [heq]
  by_contra hcon
  have h65 : 65 ≤ Nat.card ↥(Gw d x ⊓ (rOf T M ⊔ qOf T)) := by omega
  have := Nat.mul_le_mul hle h65
  omega

end Cnt

section Generic

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem card_zpowers_sup {w : G} {S : Subgroup G} (hw2 : w * w = 1) (hw1 : w ≠ 1) (hwS : w ∉ S)
    (hc : ∀ s ∈ S, w * s = s * w) :
    Nat.card ↥(Subgroup.zpowers w ⊔ S) = 2 * Nat.card ↥S := by
  have hord : orderOf w = 2 := orderOf_eq_prime (by rw [pow_two]; exact hw2) hw1
  have hnorm : Subgroup.zpowers w ≤ Subgroup.normalizer (S : Set G) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.centralizer_le_normalizer (S : Set G) (Subgroup.mem_centralizer_iff.2 fun s hs =>
      (hc s hs).symm)
  have hdisj : Disjoint S (Subgroup.zpowers w) := by
    rw [Subgroup.disjoint_def]
    intro y hyS hyw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hyw
    have hk := zpow_mod_orderOf w k
    rw [hord] at hk
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · simp only [Nat.cast_ofNat] at hk
      rw [← hk, h0, zpow_zero]
    · simp only [Nat.cast_ofNat] at hk
      rw [h1, zpow_one] at hk
      exact absurd (hk ▸ hyS) hwS
  rw [sup_comm, CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer S _ hnorm hdisj,
    Nat.card_zpowers, hord, mul_comm]

theorem eq_sup_zpowers_of_card {E S : Subgroup G} {u : G} (hES : E ≤ S) (hu : u ∈ S)
    (hnu : u ∉ E) (hcard : Nat.card ↥S = 2 * Nat.card ↥E) : S = E ⊔ Subgroup.zpowers u := by
  have hXS : E ⊔ Subgroup.zpowers u ≤ S := sup_le hES (Subgroup.zpowers_le.2 hu)
  have hEX : E ≤ E ⊔ Subgroup.zpowers u := le_sup_left
  have huX : u ∈ E ⊔ Subgroup.zpowers u := Subgroup.mem_sup_right (Subgroup.mem_zpowers u)
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hEX
  have hdvd : Nat.card ↥(E ⊔ Subgroup.zpowers u) ∣ Nat.card ↥S := Subgroup.card_dvd_of_le hXS
  have hEpos : 0 < Nat.card ↥E := Nat.card_pos
  rw [hm, hcard, mul_comm 2] at hdvd
  have hm2 : m ∣ 2 := Nat.dvd_of_mul_dvd_mul_left hEpos hdvd
  have hm1 : m ≠ 1 := by
    rintro rfl
    rw [mul_one] at hm
    exact hnu (Subgroup.eq_of_le_of_card_ge hEX (le_of_eq hm) ▸ huX)
  have hm2' : m = 2 := ((Nat.dvd_prime Nat.prime_two).1 hm2).resolve_left hm1
  subst hm2'
  refine (Subgroup.eq_of_le_of_card_ge hXS ?_).symm
  rw [hm, hcard, mul_comm]

end Generic

end InspW2

end S143

end CFSG.Quasithin
