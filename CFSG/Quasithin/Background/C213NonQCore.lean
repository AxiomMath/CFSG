module

public import CFSG.Quasithin.Background.C41PfKG

public section

namespace CFSG.Quasithin.C213NonQ

open CFSG.Open CFSG.QuasithinUnique

variable {Q : Type} [Group Q] [Finite Q]

omit [Finite Q] in
theorem le_cCompSpan (h39 : A39Statement Q) {L : Subgroup Q} (hL : ⁅L, L⁆ = L) :
    L ≤ cCompSpan (⊤ : Subgroup Q) := by
  rw [h39.1]
  exact le_perfectCore_of_perfect le_top hL

theorem le_normalizer_of_le_cCompSpan {L K : Subgroup Q} (hL : L ≤ cCompSpan (⊤ : Subgroup Q))
    (hK : K ∈ cComp (⊤ : Subgroup Q)) : L ≤ Subgroup.normalizer (K : Set Q) := by
  obtain ⟨hKS, hn⟩ := cComp_normal_span_of_le hK
  have h1 := (Subgroup.normal_subgroupOf_iff_le_normalizer hKS).mp hn
  exact hL.trans h1

theorem exists_commutator_eq {L : Subgroup Q} (hL : ⁅L, L⁆ = L) (hL1 : L ≠ ⊥)
    (hLS : L ≤ cCompSpan (⊤ : Subgroup Q)) :
    ∃ K ∈ cComp (⊤ : Subgroup Q), ⁅K, L⁆ = K := by
  by_contra hcon
  push Not at hcon
  set R := solvRad (⊤ : Subgroup Q) with hR
  have hRle : (⊤ : Subgroup Q) ≤ Subgroup.normalizer (R : Set Q) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_top).mp (solvRad_normal ⊤)
  have hRn : R.Normal :=
    ⟨fun n hn g => (Subgroup.mem_normalizer_iff.mp (hRle (Subgroup.mem_top g)) n).mp hn⟩
  let S : Subgroup Q :=
    { carrier := {x | ∀ l ∈ L, x * l * x⁻¹ * l⁻¹ ∈ R}
      one_mem' := fun l _ => by simp
      mul_mem' := fun {a b} ha hb l hl => by
        have h1 := hRn.conj_mem _ (hb l hl) a
        have h2 := R.mul_mem h1 (ha l hl)
        convert h2 using 1
        group
      inv_mem' := fun {a} ha l hl => by
        have h1 := hRn.conj_mem _ (R.inv_mem (ha l hl)) a⁻¹
        convert h1 using 1
        group }
  have hKS : ∀ K ∈ cComp (⊤ : Subgroup Q), K ≤ S := by
    intro K hK k hk l hl
    rcases cComp_commutator_dichotomy_of_le hK (le_top : L ≤ ⊤) with ⟨h1, -⟩ | h2
    · exact h1 (Subgroup.commutator_mem_commutator hk hl)
    · exfalso
      apply hcon K hK
      rw [h2]
      apply le_antisymm
      · refine conjClosure_le fun x hx z hz => ?_
        exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_of_le_cCompSpan hLS hK hx) z).mp hz
      · exact le_conjClosure K L
  have hSpan : cCompSpan (⊤ : Subgroup Q) ≤ S := sSup_le hKS
  have hLR : L ≤ R := by
    rw [← hL, Subgroup.commutator_le]
    intro a ha b hb
    exact hSpan (hLS ha) b hb
  have hsol : Group.IsSolvable ↥R := solvRad_isSolvable _
  have hLsol : Group.IsSolvable ↥L :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hLR)
      (Subgroup.inclusion_injective hLR)
  exact hL1 (C41Pf.eq_bot_of_perfect_of_isSolvable hL hLsol)

omit [Finite Q] in
theorem le_generalizedFitting_of_isComponent {K : Subgroup Q} (hK : CFSG.IsComponent K) :
    K ≤ CFSG.generalizedFitting Q :=
  (CFSG.LocalCores.component_le_layer hK).trans le_sup_right

end CFSG.Quasithin.C213NonQ
