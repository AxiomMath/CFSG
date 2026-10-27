module

public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22p22nb_exists_complement {p : ℕ} (hp : p.Prime) {E A : Subgroup G}
    (hE : IsElemAbelian p E) (hAE : A ≤ E) (hA : Nat.card A ≤ p) :
    ∃ P : Subgroup G, P ≤ E ∧ P ⊓ A = ⊥ ∧ Nat.card E ≤ p * Nat.card P := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CFSG.IsElementaryAbelian p E := hE.isElementaryAbelian
  obtain ⟨C, hC⟩ := CFSG.IsElementaryAbelian.exists_isCompl p E (A.subgroupOf E)
  have hcard : Nat.card (A.subgroupOf E) * Nat.card C = Nat.card E := by
    refine (isComplement'_of_disjoint_and_mul_eq_univ hC.disjoint ?_).card_mul_card
    rw [← Subgroup.mul_normal, hC.sup_eq_top, Subgroup.coe_top]
  have hAcard : Nat.card (A.subgroupOf E) = Nat.card A :=
    Nat.card_congr (subgroupOfEquivOfLe hAE).toEquiv
  refine ⟨C.map E.subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨c, -, rfl⟩
    exact c.2
  · refine eq_bot_iff.mpr ?_
    rintro _ ⟨⟨c, hcC, rfl⟩, hcA⟩
    have h1 : c = 1 := Subgroup.disjoint_def.mp hC.disjoint (mem_subgroupOf.mpr hcA) hcC
    simp [h1]
  · rw [Subgroup.card_map_of_injective E.subtype_injective, ← hcard, hAcard]
    exact Nat.mul_le_mul_right _ hA

theorem uc22p22nb_card_le_factorial {V P : Subgroup G} (hPV : P ≤ normalizer (V : Set G))
    (hfaith : P ⊓ centralizer (V : Set G) = ⊥) :
    Nat.card P ≤ (Nat.card V - 1).factorial := by
  classical
  have hmem : ∀ x ∈ P, ∀ v : V, x * (v : G) * x⁻¹ ∈ V := fun x hx v =>
    (mem_set_normalizer_iff.mp (hPV hx) v).mp v.2
  let f : P → {v : V // v ≠ 1} → {v : V // v ≠ 1} := fun x v =>
    ⟨⟨x * (v.1 : G) * x⁻¹, hmem x x.2 v.1⟩, fun h => v.2 (by simpa using congrArg Subtype.val h)⟩
  have hf : ∀ x, Function.Injective (f x) := fun x v w h => by
    have h1 := congrArg (fun u : {v : V // v ≠ 1} => ((u.1 : V) : G)) h
    simp only [f] at h1
    exact Subtype.ext (Subtype.ext (by simpa using h1))
  let c : P → Equiv.Perm {v : V // v ≠ 1} := fun x =>
    Equiv.ofBijective (f x) (Finite.injective_iff_bijective.mp (hf x))
  have hc : Function.Injective c := by
    intro x y hxy
    have hxv : ∀ v : {v : V // v ≠ 1}, (x : G) * (v.1 : G) * (x : G)⁻¹ =
        (y : G) * (v.1 : G) * (y : G)⁻¹ := fun v => by
      have h1 := congrArg (fun σ : Equiv.Perm {v : V // v ≠ 1} => (((σ v).1 : V) : G)) hxy
      simpa [c, f] using h1
    have hcent : (y : G)⁻¹ * (x : G) ∈ centralizer (V : Set G) := by
      rw [mem_centralizer_iff]
      intro h hh
      by_cases h1 : h = 1
      · simp [h1]
      · have heq := hxv ⟨⟨h, hh⟩, fun h2 => h1 (by simpa using congrArg Subtype.val h2)⟩
        simp only at heq
        calc h * ((y : G)⁻¹ * (x : G)) = (y : G)⁻¹ * ((y : G) * h * (y : G)⁻¹) * (x : G) := by
              simp [mul_assoc]
          _ = (y : G)⁻¹ * ((x : G) * h * (x : G)⁻¹) * (x : G) := by rw [heq]
          _ = ((y : G)⁻¹ * (x : G)) * h := by simp [mul_assoc]
    have hmem' : (y : G)⁻¹ * (x : G) ∈ P ⊓ centralizer (V : Set G) :=
      ⟨P.mul_mem (P.inv_mem y.2) x.2, hcent⟩
    rw [hfaith, Subgroup.mem_bot] at hmem'
    exact Subtype.ext (inv_mul_eq_one.mp hmem').symm
  have hS : Nat.card {v : V // v ≠ 1} + 1 = Nat.card V := by
    rw [← Finite.card_option]
    exact Nat.card_congr (Equiv.optionSubtypeNe (1 : V))
  calc Nat.card P ≤ Nat.card (Equiv.Perm {v : V // v ≠ 1}) := Nat.card_le_card_of_injective c hc
    _ = (Nat.card {v : V // v ≠ 1}).factorial := Nat.card_perm
    _ = (Nat.card V - 1).factorial := by congr 1; omega

theorem uc22p22nb_false_of_card_le_four {V P : Subgroup G} (hPV : P ≤ normalizer (V : Set G))
    (hfaith : P ⊓ centralizer (V : Set G) = ⊥) (hV4 : Nat.card V ≤ 4) (hP9 : 9 ≤ Nat.card P) :
    False := by
  have h1 := uc22p22nb_card_le_factorial hPV hfaith
  have h2 : (Nat.card V - 1).factorial ≤ (3 : ℕ).factorial := Nat.factorial_le (by omega)
  have h3 : (3 : ℕ).factorial = 6 := rfl
  omega

end CFSG.LocalAnalysis.UniquenessCase.UC22
