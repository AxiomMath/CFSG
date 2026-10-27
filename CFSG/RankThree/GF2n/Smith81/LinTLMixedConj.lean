module

public import CFSG.RankThree.GF2n.Smith81.LinTL
public import CFSG.RankThree.GF2n.Smith81.LinTLPositionConj

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement Matrix

private theorem conj_inv_of_conj {G : Type} [Group G] {V W : Subgroup G} {g : G}
    (h : conjSubgroup g V = W) :
    conjSubgroup g⁻¹ W = V := by
  rw [← h, ← CFSG.RankThree.GF2n.conjSubgroup_mul, inv_mul_cancel,
    CFSG.RankThree.GF2n.conjSubgroup_one]

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {n : ℕ} {V₁ V₂ : Subgroup G}

theorem LinSetup.not_mixed_conj (hc : Ctx M Q Z B) (hS : LinSetup M Q Z B n V₁ V₂)
    (hn : 3 ≤ n) {A : Subgroup G} (hA : Ctx M Q Z A) :
    ¬ ((A ⊔ Z) ⊓ V₁ = Z ∧ (A ⊔ Z) ⊓ V₂ = Z) := by
  have hS2 := hS
  obtain ⟨_, _, _, -, _, -, -, hZV₁, hV₁Q, hZV₂, hV₂Q, -, -, -, -, -, -⟩ := hS2
  obtain ⟨P, hPdef⟩ : ∃ P : Subgroup G,
      P = LB M Q A ⊓ (Subgroup.normalizer (V₁ : Set G) ⊓ Subgroup.normalizer (V₂ : Set G)) :=
    ⟨_, rfl⟩
  have hPmem : ∀ t : G, t ∈ P ↔
      t ∈ LB M Q A ∧ conjSubgroup t V₁ = V₁ ∧
        conjSubgroup t V₂ = V₂ := by
    intro t
    rw [hPdef, Subgroup.mem_inf, Subgroup.mem_inf,
      ← CFSG.RankThree.GF2n.conjSubgroup_eq_self_iff,
      ← CFSG.RankThree.GF2n.conjSubgroup_eq_self_iff]
  have hPLB : P ≤ LB M Q A := fun t ht => ((hPmem t).mp ht).1
  have hPH : P ≤ H0 M Z := fun t ht => hA.LB_le_H0 (hPLB ht)
  have hPn₁ : P ≤ Subgroup.normalizer (V₁ : Set G) := fun t ht =>
    CFSG.RankThree.GF2n.conjSubgroup_eq_self_iff.mp ((hPmem t).mp ht).2.1
  have hPn₂ : P ≤ Subgroup.normalizer (V₂ : Set G) := fun t ht =>
    CFSG.RankThree.GF2n.conjSubgroup_eq_self_iff.mp ((hPmem t).mp ht).2.2
  have hQP : Q ≤ P := fun q hq => (hPmem q).mpr
    ⟨(le_sup_left : Q ≤ LB M Q A) hq,
      CFSG.RankThree.GF2n.conjSubgroup_eq_self_iff.mpr
        (Q_le_normalizer_of_Z_le hc.hyp hZV₁ hV₁Q hq),
      CFSG.RankThree.GF2n.conjSubgroup_eq_self_iff.mpr
        (Q_le_normalizer_of_Z_le hc.hyp hZV₂ hV₂Q hq)⟩
  have hPS : P ≤ Lgen M (LB M Q B) := fun t ht => by
    have htL := (hPmem t).mp ht
    have htt : t * t ∈ Q := by
      have h2 := hA.sq_mem_Q_of_mem_LB htL.1
      rwa [pow_two] at h2
    exact linNonswapStatement_holds G M Q Z B n V₁ V₂ hc hS hn t (hPH ht) htt htL.2.1
  have hswap : ∀ t ∈ LB M Q A, t ∉ P →
      conjSubgroup t V₁ = V₂ ∧ conjSubgroup t V₂ = V₁ := by
    intro t htL htP
    rcases linSwapStatement_holds G M Q Z B n V₁ V₂ hc hS hn t (hA.LB_le_H0 htL) with h | h
    · exact absurd ((hPmem t).mpr ⟨htL, h.1, h.2⟩) htP
    · exact h
  have hcos : ∃ s ∈ LB M Q A, ∀ t ∈ LB M Q A, t ∈ P ∨ s⁻¹ * t ∈ P := by
    by_cases hex : ∃ s ∈ LB M Q A, s ∉ P
    · obtain ⟨s, hsL, hsP⟩ := hex
      refine ⟨s, hsL, fun t htL => ?_⟩
      by_cases htP : t ∈ P
      · exact Or.inl htP
      · right
        obtain ⟨hs1, hs2⟩ := hswap s hsL hsP
        obtain ⟨ht1, ht2⟩ := hswap t htL htP
        refine (hPmem _).mpr ⟨(LB M Q A).mul_mem ((LB M Q A).inv_mem hsL) htL, ?_, ?_⟩
        · rw [CFSG.RankThree.GF2n.conjSubgroup_mul, ht1]
          exact conj_inv_of_conj hs1
        · rw [CFSG.RankThree.GF2n.conjSubgroup_mul, ht2]
          exact conj_inv_of_conj hs2
    · push Not at hex
      exact ⟨1, (LB M Q A).one_mem, fun t htL => Or.inl (hex t htL)⟩
  have hPi : (P.subgroupOf (LB M Q A)).index ≤ 2 := by
    obtain ⟨s, hsL, hcs⟩ := hcos
    let f : Bool → ↥(LB M Q A) ⧸ P.subgroupOf (LB M Q A) := fun b =>
      (QuotientGroup.mk (cond b ⟨s, hsL⟩ 1 : ↥(LB M Q A)) :
        ↥(LB M Q A) ⧸ P.subgroupOf (LB M Q A))
    have hf : Function.Surjective f := by
      intro x
      obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective x
      rcases hcs t t.2 with h | h
      · refine ⟨false, QuotientGroup.eq.mpr ?_⟩
        rw [Subgroup.mem_subgroupOf]
        simpa using h
      · refine ⟨true, QuotientGroup.eq.mpr ?_⟩
        rw [Subgroup.mem_subgroupOf]
        simpa using h
    have hc2 : Nat.card (↥(LB M Q A) ⧸ P.subgroupOf (LB M Q A)) ≤ 2 := by
      refine (Nat.card_le_card_of_surjective f hf).trans (le_of_eq ?_)
      rw [Nat.card_eq_fintype_card, Fintype.card_bool]
    exact hc2
  exact LinSetup.not_mixed_of_index_le_two hc hS hn hA hQP hPLB hPS hPn₁ hPn₂ hPi

theorem LinSetup.conj_le_V (hc : Ctx M Q Z B) (hS : LinSetup M Q Z B n V₁ V₂) (hn : 3 ≤ n)
    {A : Subgroup G} (hA : Ctx M Q Z A) : A ≤ V₁ ∨ A ≤ V₂ := by
  rcases LinSetup.conj_trichotomy hc hS hn hA with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact (LinSetup.not_mixed_conj hc hS hn hA h).elim

theorem lin31FwdStatement_holds : Lin31FwdStatement :=
  lin31FwdStatement_of_conj_position fun _ _ _ _ _ _ _ _ _ _ _ hc hS hn hA =>
    LinSetup.conj_le_V hc hS hn hA

end CFSG.RankThree.GF2n.Smith81
