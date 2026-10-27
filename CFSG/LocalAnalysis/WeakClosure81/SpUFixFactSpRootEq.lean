module

public import CFSG.LocalAnalysis.WeakClosure81.SpUFixFactSpRoot
public import CFSG.LocalAnalysis.WeakClosure81.SevenKSymplectic
import CFSG.LocalAnalysis.WeakClosure81.W16Gt2KFactsC

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open CFSG.RankThree.PartOne.KCSpFull CFSG.RankThree.Classical
open CFSG.LocalAnalysis.WeakClosure81.SevenK

variable {k : ℕ} {F : Type} [Field F]

theorem exists_eq_spUFixRootSp [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (R : Subgroup ↥(StatedSp k F)) (hR : Nat.card R = 2 ^ n)
    (hRt : ∀ x ∈ R, x ≠ 1 → IsSymplecticTransvectionIn k x) :
    ∃ a : Fin k ⊕ Fin k → F, a ≠ 0 ∧ R = spUFixRootSp a := by
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  ·
    subst hn0
    rw [pow_zero] at hF
    have h1 : 1 < Nat.card F := Finite.one_lt_card
    omega
  ·
    rcases (by omega : n = 1 ∨ 2 ≤ n) with hn1 | hn2
    · subst hn1
      rw [pow_one] at hF hR
      obtain ⟨u, hu, huniqF⟩ := (Nat.card_eq_two_iff' (0 : F)).mp hF
      have h01 : ∀ t : F, t = 0 ∨ t = 1 := by
        intro t
        by_cases ht : t = 0
        · exact Or.inl ht
        · exact Or.inr ((huniqF t ht).trans (huniqF 1 one_ne_zero).symm)
      obtain ⟨r, hr, huniq⟩ := (Nat.card_eq_two_iff' (1 : R)).mp hR
      let x₀ : ↥(StatedSp k F) := (r : ↥(StatedSp k F))
      have hx₀ : x₀ ∈ R := r.2
      have hx₀1 : x₀ ≠ 1 := fun h => hr (Subtype.ext h)
      have huniq' : ∀ x ∈ R, x ≠ 1 → x = x₀ := by
        intro x hx hx1
        have hxR : (⟨x, hx⟩ : R) ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
        exact congrArg Subtype.val (huniq ⟨x, hx⟩ hxR)
      obtain ⟨a, c, ha, hc, heq⟩ := borel86_spn_eq_spTransvection (hRt x₀ hx₀ hx₀1)
      have hc1 : c = 1 := (huniqF c hc).trans (huniqF 1 one_ne_zero).symm
      refine ⟨a, ha, Subgroup.ext fun x => ?_⟩
      rw [mem_spUFixRootSp]
      constructor
      · intro hx
        by_cases hx1 : x = 1
        · exact ⟨0, by rw [hx1, borel86_spn_spTransvection_param_zero]⟩
        · exact ⟨c, by rw [huniq' x hx hx1, heq]⟩
      · rintro ⟨t, rfl⟩
        rcases h01 t with rfl | rfl
        · rw [borel86_spn_spTransvection_param_zero]
          exact R.one_mem
        · rw [← hc1, ← heq]
          exact hx₀
    ·
      obtain ⟨a, ha, hA⟩ := kFacts_sp_rootGroup hF hn2 R hR hRt
      exact ⟨a, ha, Subgroup.ext fun x => by rw [hA x, mem_spUFixRootSp]⟩

end CFSG.LocalAnalysis.WeakClosure81

end
