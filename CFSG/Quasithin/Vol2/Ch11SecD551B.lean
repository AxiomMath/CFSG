module

public import CFSG.Quasithin.Vol2.Ch11SecD551A
public import CFSG.Quasithin.Background.E3Prop
public import CFSG.Quasithin.Vol2.Ch11StatementsD

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem oTwoUpper_sup_eq_of_sylow' {T H : Subgroup G}
    (hT : QuasithinUnique.IsSylowTwoOf T H) : oTwoUpper H ⊔ T = H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJH : oTwoUpper H ⊔ T ≤ H := sup_le (oTwoUpper_le H) hT.1
  refine le_antisymm hJH ?_
  have hodd : ¬ 2 ∣ (oTwoUpper H ⊔ T).relIndex H := fun h2 => hT.2.2 (by
    have := Subgroup.relIndex_mul_relIndex T (oTwoUpper H ⊔ T) H le_sup_right hJH
    change 2 ∣ T.relIndex H
    rw [← this]
    exact Dvd.dvd.mul_left h2 _)
  have hN : ((oTwoUpper H).subgroupOf H).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (le_normalizer_oTwoUpper H)
  have hQ : IsPGroup 2 (↥H ⧸ (oTwoUpper H).subgroupOf H) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H x =>
      obtain ⟨k, hk⟩ := exists_pow_mem_oTwoUpper H x.2
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact hk
  obtain ⟨m, hm⟩ := hQ.exists_card_eq
  have hdvd : (oTwoUpper H ⊔ T).relIndex H ∣ 2 ^ m := by
    rw [← hm, ← Subgroup.index_eq_card]
    exact Subgroup.relIndex_dvd_of_le_left H le_sup_left
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hj0 : j = 0 := by
    by_contra hj0
    exact hodd (hj ▸ dvd_pow_self 2 hj0)
  have h1 : (oTwoUpper H ⊔ T).relIndex H = 1 := by rw [hj, hj0, pow_zero]
  exact Subgroup.relIndex_eq_one.mp h1

theorem two_dvd_card_of_ne_bot {A : Subgroup G} (hA : IsPGroup 2 A) (h1 : A ≠ ⊥) :
    2 ∣ Nat.card A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hA.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact h1 (Subgroup.eq_bot_of_card_eq A (by simpa using hk))
  rw [hk]
  exact dvd_pow_self 2 hk0

theorem ROf_le_T (h : Hyp11 G T L I n) (V₁ : Subgroup G) : ROf T L V₁ ≤ T :=
  pCoreOf_two_le_of_isSylowTwoOf (isSylowTwoOf_of_quasithinIsSylowTwo h.fsu.sylow le_sup_right)

theorem le_M_of_sylow_R₁ (h1102 : Stmt11_0_2) (h1110 : Stmt11_1_0) (h1122 : Stmt11_2_2)
    (h : Hyp11 G T L I n) (hG2 : KindG2 L (fsuV T I) n) {V₁ : Subgroup G}
    (hV₁ : IsVi T L I n 1 V₁) {H₁ : Subgroup G} (hS : IsSylowIn 2 (ROf T L V₁) H₁)
    (hn1 : E1.nParam H₁ = 1) : H₁ ≤ Subgroup.normalizer (L : Set G) := by
  obtain ⟨V₂, hV₂, -⟩ := (h1110 G T L I n h).1 2 (by norm_num) (by norm_num)
  have h22 := h1122 G T L I n (2 * n) V₁ V₂ h hV₁ hV₂ (Or.inl ⟨hG2, rfl⟩)
  have hVel := SecA.isElemAbelian_fsuV h
  have hn := h.one_lt
  have hs : 0 + 1 < E3.sParam hVel := by
    rw [h22.2.2.2.1 hVel]
    omega
  obtain ⟨hW0, hNW0, -⟩ := h22.2.2.2.2.2.1 hG2
  have hC1 := h22.2.2.2.2.2.2 hG2
  have hWR : E3.wClos (fsuV T I) 0 T ≤ ROf T L V₁ :=
    hW0.trans (inf_centralizer_le_ROf h1102 h hV₁)
  have h19 := E3.e3_19 hVel hS (i := 0) hn1 hs
  rw [zero_add, wClos_zero_eq_of_le (ROf_le_T h V₁) hWR] at h19
  rw [← h19]
  exact sup_le (inf_le_right.trans hC1) (inf_le_right.trans hNW0)

end CFSG.Quasithin.Vol2.Ch11.SecD
