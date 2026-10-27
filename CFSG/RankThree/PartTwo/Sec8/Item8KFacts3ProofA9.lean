module

public import CFSG.RankThree.PartTwo.Sec8.Item8KFacts3ProofPerfect
public import CFSG.Assembly.Defs

public section

namespace CFSG.RankThree.PartTwo.Sec8.Item8KFacts3

open Equiv Equiv.Perm Subgroup

theorem card_dvd_factorial_of_fixes {α : Type*} [Fintype α] [DecidableEq α]
    {T : Subgroup (Perm α)} (F : Finset α) (hT : ∀ t ∈ T, ∀ x ∉ F, t x = x) :
    Nat.card T ∣ F.card.factorial := by
  have hiff : ∀ t : T, ∀ x, (t : Perm α) x ∈ F ↔ x ∈ F := by
    intro t x
    constructor
    · intro htx
      by_contra hx
      rw [hT t t.2 x hx] at htx
      exact hx htx
    · intro hx
      by_contra htx
      have h1 : (t : Perm α) x = x := (t : Perm α).injective (hT t t.2 _ htx)
      rw [h1] at htx
      exact htx hx
  let ψ : T →* Perm F :=
    { toFun := fun t => (t : Perm α).subtypePerm (hiff t)
      map_one' := by
        ext y
        simp
      map_mul' := fun g h => by
        ext y
        simp only [Subgroup.coe_mul]
        rfl }
  have hinj : Function.Injective ψ := by
    intro g h hgh
    apply Subtype.ext
    ext x
    by_cases hx : x ∈ F
    · have h1 := congrArg (fun σ : Perm F => (σ ⟨x, hx⟩ : α)) hgh
      simpa [ψ] using h1
    · rw [hT g g.2 x hx, hT h h.2 x hx]
  have h1 := Subgroup.card_dvd_of_injective ψ hinj
  rwa [Nat.card_perm, Nat.card_eq_finsetCard] at h1

theorem six_le_of_nine_dvd_factorial : ∀ n ≤ 9, 9 ∣ n.factorial → 6 ≤ n := by
  decide

theorem mem_zpowers_of_perm9 {E S H₁ H₂ : Subgroup (Perm (Fin 9))} {u v : Perm (Fin 9)}
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (hE27 : Nat.card E = 27)
    (hS9 : Nat.card S = 9) (huE : u ∈ E) (hvE : v ∈ E) (huS : u ∉ S) (hvS : v ∉ S)
    (hP₁ : Group.IsPerfect H₁) (hP₂ : Group.IsPerfect H₂) (hSH₁ : S ≤ H₁) (hSH₂ : S ≤ H₂)
    (hH₁ : H₁ ≤ Subgroup.centralizer {u}) (hH₂ : H₂ ≤ Subgroup.centralizer {v}) :
    v ∈ Subgroup.zpowers u := by
  classical
  have hu3 : u ^ 3 = 1 := hE.2 u huE
  have hv3 : v ^ 3 = 1 := hE.2 v hvE
  have hu1 : u ≠ 1 := fun h => huS (h ▸ S.one_mem)
  have hSu : ∀ s ∈ S, ∀ x ∈ u.support, s x = x := fun s hs =>
    fixes_support_of_isPerfect (by simp) hu3 hP₁ hH₁ s (hSH₁ hs)
  have hSv : ∀ s ∈ S, ∀ x ∈ v.support, s x = x := fun s hs =>
    fixes_support_of_isPerfect (by simp) hv3 hP₂ hH₂ s (hSH₂ hs)
  set F : Finset (Fin 9) := Finset.univ.filter (fun x => ∀ s ∈ S, s x = x) with hFdef
  have hmemF : ∀ x, x ∈ F ↔ ∀ s ∈ S, s x = x := fun x => by simp [hFdef]
  have huF : u.support ⊆ F := fun x hx => (hmemF x).2 fun s hs => hSu s hs x hx
  have hvF : v.support ⊆ F := fun x hx => (hmemF x).2 fun s hs => hSv s hs x hx
  have hF3 : F.card ≤ 3 := by
    have h1 := card_dvd_factorial_of_fixes (T := S) Fᶜ fun s hs x hx => by
      rw [Finset.mem_compl, not_not] at hx
      exact (hmemF x).1 hx s hs
    rw [hS9] at h1
    have h2 : Fᶜ.card ≤ 9 := (Finset.card_le_univ _).trans (by simp)
    have h3 := six_le_of_nine_dvd_factorial _ h2 h1
    have h4 := Finset.card_add_card_compl F
    simp only [Fintype.card_fin] at h4
    omega
  set T : Subgroup (Perm (Fin 9)) := Subgroup.closure {u, v} with hTdef
  have hTfix : ∀ t ∈ T, ∀ x ∉ F, t x = x := by
    intro t ht
    induction ht using Subgroup.closure_induction with
    | mem t ht =>
      intro x hx
      rcases ht with rfl | rfl
      · by_contra h
        exact hx (huF (mem_support.mpr h))
      · by_contra h
        exact hx (hvF (mem_support.mpr h))
    | one => exact fun x _ => rfl
    | mul t t' _ _ ht ht' =>
      intro x hx
      rw [Perm.mul_apply, ht' x hx, ht x hx]
    | inv t _ ht =>
      intro x hx
      rw [Perm.inv_eq_iff_eq, ht x hx]
  have hT6 : Nat.card T ∣ 6 :=
    (card_dvd_factorial_of_fixes F hTfix).trans
      ((Nat.factorial_dvd_factorial hF3).trans (by decide))
  have hTE : T ≤ E := by
    rw [hTdef, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact huE
    · exact hvE
  have hT27 : Nat.card T ∣ 27 := by
    rw [← hE27]
    exact Subgroup.card_dvd_of_le hTE
  have hT3 : Nat.card T ≤ 3 := by
    have h1 : Nat.card T ∣ Nat.gcd 6 27 := Nat.dvd_gcd hT6 hT27
    exact Nat.le_of_dvd (by norm_num) (by simpa using h1)
  have huord : orderOf u = 3 := orderOf_eq_prime hu3 hu1
  have hle : Subgroup.zpowers u ≤ T := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.subset_closure (Set.mem_insert u _)
  have heq : Subgroup.zpowers u = T :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, huord]; exact hT3)
  rw [heq]
  exact Subgroup.subset_closure (Set.mem_insert_of_mem u rfl)

end CFSG.RankThree.PartTwo.Sec8.Item8KFacts3
