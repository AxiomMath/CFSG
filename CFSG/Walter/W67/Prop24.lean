module

import CFSG.Walter.W67.W1Prop24C
import CFSG.Walter.W67.W1Prop24D
import CFSG.Walter.W67.Prop23
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic
public import CFSG.Walter.W67.Interface
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.Walter.W67

open scoped MatrixGroups

theorem prop_2_4 :
    ∀ (G : Type) [Group G] [Finite G] (h : Hyp G), h.q = 3 →
      (∀ N : Subgroup G, N.Normal → N.index ≠ 2) →
      ∃ L : Subgroup G, L.Normal ∧ L ⊔ CFSG.pPrimeCore 2 G = ⊤ ∧ L ⊓ CFSG.pPrimeCore 2 G = ⊥ ∧
        CFSG.pPrimeCore 2 G ≤ Subgroup.centralizer (L : Set G) ∧
        (∃ K' : Subgroup G, K' ≤ L ⊓ h.H ∧ h.J ∉ K' ∧
          L ⊓ h.H = Subgroup.zpowers h.J ⊔ K' ∧ Nonempty (K' ≃* PSL(2, GaloisField 3 1))) ∧
        ((Nat.card L = 168 ∧ ∀ S : Sylow 2 G, (S : Subgroup G) ≤ L →
            Subgroup.normalizer ((S : Subgroup G) : Set G) ⊓ L = L) ∨
          (Nat.card L = 1512 ∧ (commutator L).index = 3 ∧
            Nonempty (commutator L ≃* PSL(2, GaloisField 2 3)))) := by
  intro G _ _ h hq hidx
  obtain ⟨fr⟩ := Frame.nonempty G h
  set O := CFSG.pPrimeCore 2 G
  by_cases hN : Subgroup.normalizer ((fr.S : Subgroup G) : Set G) = ⊤
  ·
    obtain ⟨hEO, hG, Y, hY, hYcard⟩ := fr.exists_yData_of_normal hq hidx hN
    obtain ⟨hLn, htop, hbot, hOC, hLH⟩ := hY.assembly hq hidx hEO (by rw [hG, hYcard])
    refine ⟨Y ⊔ h.K, hLn, htop, hbot, hOC, ⟨h.K, le_inf le_sup_right h.K_le_H, h.J_not_mem_K,
      hLH, h.nonempty_iso_three hq⟩, Or.inl ⟨by rw [hY.card_sup_K hq, hYcard], fun S' _ => ?_⟩⟩
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := Sylow.unique_of_normal fr.S (Subgroup.normalizer_eq_top_iff.mp hN)
    rw [Subsingleton.elim S' fr.S, hN, top_inf_eq]
  ·
    obtain ⟨hEO, hG, Y, hY, hYcard, hperf, ⟨eY⟩⟩ := fr.exists_yData_of_not_normal hq hidx hN
    obtain ⟨hLn, htop, hbot, hOC, hLH⟩ := hY.assembly hq hidx hEO (by rw [hG, hYcard])
    set L := Y ⊔ h.K
    have hL : Nat.card L = 1512 := by rw [hY.card_sup_K hq, hYcard]
    have hYL : Y ≤ L := le_sup_left
    have := hY.normal
    have hidx3 : (Y.subgroupOf L).index = 3 := by
      have h1 := Subgroup.relIndex_mul_card (H := Y) (K := L)
      rw [inf_eq_left.mpr hYL, hL, hYcard] at h1
      change Y.relIndex L = 3
      omega
    have hcomm : commutator L = Y.subgroupOf L := by
      apply le_antisymm
      · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
        have : IsCyclic (L ⧸ Y.subgroupOf L) :=
          isCyclic_of_prime_card (p := 3) (by rw [← Subgroup.index_eq_card, hidx3])
        have := Abelianization.commutator_subset_ker (QuotientGroup.mk' (Y.subgroupOf L))
        rwa [QuotientGroup.ker_mk'] at this
      · intro y hy
        have hyY : (y : G) ∈ ⁅Y, Y⁆ := by
          rw [← Subgroup.map_subtype_commutator, hperf, ← MonoidHom.range_eq_map,
            Subgroup.range_subtype]
          exact hy
        have hyL : (y : G) ∈ (commutator L).map L.subtype := by
          rw [Subgroup.map_subtype_commutator]
          exact Subgroup.commutator_mono hYL hYL hyY
        obtain ⟨c, hc, hcy⟩ := hyL
        rw [show y = c from Subtype.ext hcy.symm]
        exact hc
    refine ⟨L, hLn, htop, hbot, hOC, ⟨h.K, le_inf le_sup_right h.K_le_H, h.J_not_mem_K,
      hLH, h.nonempty_iso_three hq⟩, Or.inr ⟨hL, by rw [hcomm, hidx3], ⟨?_⟩⟩⟩
    exact ((MulEquiv.subgroupCongr hcomm).trans (Subgroup.subgroupOfEquivOfLe hYL)).trans eY

theorem case_of_q_eq_three :
    ∀ (G : Type) [Group G] [Finite G] (h : Hyp G), h.q = 3 → Case1 h ∨ Case2 h := by
  intro G _ _ h hq
  by_cases hidx : ∃ N : Subgroup G, N.Normal ∧ N.index = 2
  · exact Or.inl (case1_of_sup G h (prop_2_3 G h hidx))
  · right
    push Not at hidx
    obtain ⟨L, hLn, htop, hbot, hOC, ⟨K', hK'L, hJK', hLH, ⟨eK⟩⟩, -⟩ := prop_2_4 G h hq hidx
    set O := CFSG.pPrimeCore 2 G
    have hO : Odd (Nat.card O) := odd_card_pPrimeCore G
    have hidxL : L.index = Nat.card O := by
      have hc : ∀ x ∈ L, ∀ y ∈ O, x * y = y * x := fun x hx y hy =>
        Subgroup.mem_centralizer_iff.mp (hOC hy) x hx
      obtain ⟨h1, -⟩ := card_sup_mul_card_inf_of_commute L O hc
      rw [htop, hbot, Subgroup.card_top, Subgroup.card_bot, mul_one] at h1
      have h2 := L.card_mul_index
      rw [h1] at h2
      exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h2
    have key : ∀ {p f p' f' : ℕ} [Fact p.Prime] [Fact p'.Prime], p = p' → f = f' →
        Nonempty (K' ≃* PSL(2, GaloisField p f)) →
          Nonempty (K' ≃* PSL(2, GaloisField p' f')) := by
      intro p f p' f' _ _ hp hf e
      subst hp hf
      exact e
    refine ⟨L, hLn, hidxL ▸ hO, ⟨1, ?_⟩, ⟨K', hK'L, hJK', hLH,
      key (h.p_eq_three hq).symm (h.f_eq_one hq).symm ⟨eK⟩⟩, ?_⟩
    · rw [eq_top_iff, ← htop]
      exact le_sup_of_le_right (sup_le_sup_left hOC L)
    · rw [hq]
      left
      rfl

end CFSG.Walter.W67
