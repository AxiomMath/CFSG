module

public import CFSG.RankThree.PartOne.CTP.AltRank
public import CFSG.RankThree.PartOne.CTP.OutEmbed
public import CFSG.RankThree.PartOne.CTP.StrongPSolvable
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternating

public section

namespace CFSG.RankThree.PartOne.CTP

open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.ComponentClassification.CatalogueSchreierAlternating
  (alternating_schreier_of_equiv outer_card_dvd_two_of_equiv_outside_six)
open CFSG.ComponentClassification.CatalogueSchreierAlternating.DegreeSix
  (outer_card_le_four_of_equiv)

namespace Alt

theorem le_closure_of_closure_subgroupOf {H : Type*} [Group H] {S E : Subgroup H}
    (h : Subgroup.closure {k : S | ∃ x ∈ E.subgroupOf S, x ≠ 1 ∧ k * x = x * k} = ⊤) :
    S ≤ Subgroup.closure {k : H | ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k} := by
  intro s hs
  have h1 : (⟨s, hs⟩ : S) ∈
      Subgroup.closure {k : S | ∃ x ∈ E.subgroupOf S, x ≠ 1 ∧ k * x = x * k} := by
    rw [h]
    exact Subgroup.mem_top _
  have h2 : S.subtype '' {k : S | ∃ x ∈ E.subgroupOf S, x ≠ 1 ∧ k * x = x * k} ⊆
      {k : H | ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k} := by
    rintro _ ⟨k, ⟨x, hx, hx1, hkx⟩, rfl⟩
    refine ⟨(x : H), Subgroup.mem_subgroupOf.mp hx, ?_, ?_⟩
    · intro h
      exact hx1 (Subtype.ext h)
    · exact congrArg Subtype.val hkx
  have h3 := Subgroup.mem_map_of_mem S.subtype h1
  rw [MonoidHom.map_closure] at h3
  exact Subgroup.closure_mono h2 h3

theorem outer_card_le_four {G : Type*} [Group G] {n : ℕ} (hn5 : 5 ≤ n)
    (e : G ≃* alternatingGroup (Fin n)) : Nat.card (Outer G) ≤ 4 := by
  by_cases h6 : n = 6
  · subst h6
    exact outer_card_le_four_of_equiv e
  · have h := outer_card_dvd_two_of_equiv_outside_six (by omega) e
    exact (Nat.le_of_dvd (by norm_num) h).trans (by norm_num)

end Alt

theorem alt_stronglyPEmbedded {p n : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (hn5 : 5 ≤ n) (hn : n ≤ 12)
    {H : Type} [Group H] [Finite H] (S : Subgroup H) [S.Normal]
    (e : S ≃* alternatingGroup (Fin n)) (hSc : Subgroup.centralizer (S : Set H) = ⊥)
    {Y : Subgroup H} (hY : IsStronglyPEmbedded p Y)
    {E : Subgroup H} (hEY : E ≤ Y) [CFSG.IsElementaryAbelian p E] (hE : Nat.card E = p ^ 2) :
    p = 5 ∧ n = 10 := by
  have hquot : ¬ p ∣ Nat.card (H ⧸ S) := by
    intro hd
    have hpos : 0 < Nat.card (H ⧸ S) := Nat.card_pos
    have h1 := Nat.le_of_dvd hpos hd
    have h2 := card_quotient_le_outer S hSc
    have h3 := Alt.outer_card_le_four hn5 e
    omega
  have hES : E ≤ S :=
    le_of_isPGroup_of_not_dvd_card_quotient (CFSG.IsElementaryAbelian.isPGroup p E) hquot
  let φ : ↥S →* Equiv.Perm (Fin n) := (alternatingGroup (Fin n)).subtype.comp e.toMonoidHom
  have hφ : Function.Injective φ := Subtype.val_injective.comp e.injective
  have hrange : φ.range = alternatingGroup (Fin n) := by
    ext σ
    constructor
    · rintro ⟨s, rfl⟩
      exact (e s).2
    · intro hσ
      exact ⟨e.symm ⟨σ, hσ⟩, by simp [φ]⟩
  have hE₁ : Nat.card (E.subgroupOf S) = p ^ 2 := by
    rw [← hE]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hES).toEquiv
  have hdvd : p ^ 2 ∣ n.factorial := by
    have h1 : Nat.card ((E.subgroupOf S).map φ) = p ^ 2 := by
      rw [Subgroup.card_map_of_injective hφ, hE₁]
    have h2 := Subgroup.card_subgroup_dvd_card ((E.subgroupOf S).map φ)
    rwa [h1, Nat.card_eq_fintype_card (α := Equiv.Perm (Fin n)), Fintype.card_perm,
      Fintype.card_fin] at h2
  obtain ⟨hp, hn10⟩ := Alt.prime_sq_dvd_factorial (Fact.out : p.Prime) hp5 hn hdvd
  refine ⟨hp, ?_⟩
  by_contra hne
  subst hp
  have hpow : ∀ x ∈ E.subgroupOf S, x ^ 5 = 1 := by
    intro x hx
    apply Subtype.ext
    simpa using elemPow_eq_one_of_isElementaryAbelian (A := E) (x : H)
      (Subgroup.mem_subgroupOf.mp hx)
  have hgenS := Alt.closure_centralizers_eq_top (V := Fin n) (by simp; omega) (by simp; omega)
    φ hφ hrange (by rw [hE₁]; norm_num) hpow
  have hsol : Group.IsSolvable (Outer ↥S) := alternating_schreier_of_equiv n hn5 e
  have hsolq : Group.IsSolvable (H ⧸ S) := solvable_quotient_of_outer S hSc
  exact IsStronglyPEmbedded.false_of_generation hY hEY hE
    (Alt.le_closure_of_closure_subgroupOf hgenS) hsolq

end CFSG.RankThree.PartOne.CTP
