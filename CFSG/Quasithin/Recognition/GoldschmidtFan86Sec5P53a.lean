module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P52
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5PCommLt
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5PRev
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5StmtA

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem fan53a_right (F : FanTree Γ G) (h40 : Fan40 F) (ℓ : Line Γ) {z : G} {a b tL tR : ℤ}
    (hz : z ∈ ℓ.ZZ) (hc : ℓ.IsCoreFix z a b tL tR) :
    1 ≤ tR - b ∧ (Fan86.valence Γ (ℓ.vert tR) ≠ 3 → 2 ≤ tR - b) := by
  obtain ⟨hab, hcfix, -, -, -⟩ := hc.core
  have hb := (hc.fix b).1 (hcfix b hab.le le_rfl)
  by_contra hcon
  have h35 : Fan86.valence Γ (ℓ.vert tR) = 3 ∨ Fan86.valence Γ (ℓ.vert tR) = 5 :=
    F.valence _
  have hsmall : tR = b ∨ (tR = b + 1 ∧ Fan86.valence Γ (ℓ.vert tR) = 5) := by
    by_cases h1 : 1 ≤ tR - b
    · right
      have : ¬ (Fan86.valence Γ (ℓ.vert tR) ≠ 3 → 2 ≤ tR - b) := fun h => hcon ⟨h1, h⟩
      push Not at this
      omega
    · left
      omega
  obtain ⟨β, β', hββ', hβ3⟩ : ∃ β β' : V, Γ.Adj β β' ∧ Fan86.valence Γ β ≠ 3 := by
    by_cases h3 : Fan86.valence Γ (ℓ.vert tR) = 3
    · refine ⟨ℓ.vert (tR + 1), ℓ.vert tR, (ℓ.adj tR).symm, ?_⟩
      have h1 : Fan86.valence Γ (ℓ.vert tR) ≠ Fan86.valence Γ (ℓ.vert (tR + 1)) :=
        F.alternating _ _ (ℓ.adj tR)
      omega
    · exact ⟨ℓ.vert tR, ℓ.vert (tR + 1), ℓ.adj tR, h3⟩
  refine F.not_pclosed (ℓ.vert tR) (F.pclosed_of_central fun x hx hxo k hk => ?_)
  have h52 := (fan52 F h40 ℓ z a b tL tR hz hc x hx hxo).1 β β' hββ' hβ3
  have hp := F.valence_isPrime (ℓ.vert tR)
  have hlt : (Subgroup.centralizer ({x} : Set G)).relIndex (nbrStab Γ G (ℓ.vert tR)) <
      Fan86.valence Γ (ℓ.vert tR) := by
    refine lt_of_le_of_lt h52 ?_
    rcases hsmall with h | ⟨h, h5⟩
    · have e1 : {i : ℤ | b ≤ i ∧ i < tR ∧ Fan86.valence Γ (ℓ.vert i) = 3} = ∅ := by
        ext i
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        omega
      have e2 : {i : ℤ | b ≤ i ∧ i < tR ∧ Fan86.valence Γ (ℓ.vert i) ≠ 3} = ∅ := by
        ext i
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        omega
      rw [e1, e2, Set.ncard_empty]
      simp only [mul_zero, pow_zero, mul_one]
      omega
    · have hv : Fan86.valence Γ (ℓ.vert b) = 3 := by
        have h1 : Fan86.valence Γ (ℓ.vert b) ≠ Fan86.valence Γ (ℓ.vert (b + 1)) :=
          F.alternating _ _ (ℓ.adj b)
        have h2 : Fan86.valence Γ (ℓ.vert b) = 3 ∨ Fan86.valence Γ (ℓ.vert b) = 5 := F.valence _
        rw [h] at h5
        omega
      have e1 : {i : ℤ | b ≤ i ∧ i < tR ∧ Fan86.valence Γ (ℓ.vert i) = 3} = {b} := by
        ext i
        simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
        constructor
        · rintro ⟨h1, h2, -⟩
          omega
        · rintro rfl
          exact ⟨le_rfl, by omega, hv⟩
      have e2 : {i : ℤ | b ≤ i ∧ i < tR ∧ Fan86.valence Γ (ℓ.vert i) ≠ 3} = ∅ := by
        ext i
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨h1, h2, h3⟩
        have : i = b := by omega
        subst this
        exact h3 hv
      rw [e1, e2, Set.ncard_empty, Set.ncard_singleton]
      simp only [mul_zero, pow_zero, mul_one, mul_one]
      omega
  have hfin := F.finite_nbrStab (ℓ.vert tR)
  exact comm_of_relIndex_lt hp (by omega) (F.nbrStab_isPGroup _) hxo
    (fun k hk => nbrStab_conj_mem F (MulAction.mem_stabilizer_iff.1 hx) hk)
    (FanTree.relIndex_ne_zero_of_finite _ _) hlt k hk

theorem fan53a (F : FanTree Γ G) : Fan53a F := by
  intro h40 ℓ z a b tL tR hz hc
  obtain ⟨h1, h2⟩ := fan53a_right F h40 ℓ hz hc
  obtain ⟨h3, h4⟩ := fan53a_right F h40 ℓ.rev (Line.ZZ_rev hz) (Line.IsCoreFix.rev hc)
  refine ⟨h1, by omega, h2, fun h => ?_⟩
  have := h4 (by simpa using h)
  omega

end CFSG.Quasithin.Fan86
