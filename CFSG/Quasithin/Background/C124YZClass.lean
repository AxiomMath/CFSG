module

public import CFSG.Quasithin.Background.C124YZCount

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C124.YZ

open CFSG.Quasithin Equiv Equiv.Perm

section Count

variable {m : ℕ} (B : Subgroup (Perm (Fin m)))

theorem prod_two_pow_eq :
    ∏ c : OrbQ B, 2 ^ (Nat.card c.orbit - 1) = 2 ^ (m - Fintype.card (OrbQ B)) := by
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  have h := Finset.sum_tsub_distrib (s := (Finset.univ : Finset (OrbQ B)))
    (f := fun c => Nat.card c.orbit) (g := fun _ => 1) (fun c _ => one_le_card_orbit B c)
  rw [h, sum_card_orbit]
  simp

theorem eq_of_prod_eq {ι : Type*} (s : Finset ι) {f g : ι → ℕ} (hpos : ∀ i ∈ s, 0 < f i)
    (hle : ∀ i ∈ s, f i ≤ g i) (h : ∏ i ∈ s, f i = ∏ i ∈ s, g i) : ∀ i ∈ s, f i = g i := by
  classical
  intro j hj
  by_contra hne
  have hlt : f j < g j := lt_of_le_of_ne (hle j hj) hne
  have e1 := Finset.mul_prod_erase s f hj
  have e2 := Finset.mul_prod_erase s g hj
  have hP : 0 < ∏ i ∈ s.erase j, f i :=
    Finset.prod_pos fun i hi => hpos i (Finset.mem_of_mem_erase hi)
  have hPle : ∏ i ∈ s.erase j, f i ≤ ∏ i ∈ s.erase j, g i :=
    Finset.prod_le_prod fun i hi => hle i (Finset.mem_of_mem_erase hi)
  have : ∏ i ∈ s, f i < ∏ i ∈ s, g i := by
    rw [← e1, ← e2]
    calc f j * ∏ i ∈ s.erase j, f i < g j * ∏ i ∈ s.erase j, f i :=
          Nat.mul_lt_mul_of_pos_right hlt hP
      _ ≤ g j * ∏ i ∈ s.erase j, g i := Nat.mul_le_mul_left _ hPle
  exact absurd h this.ne

def orbitPres : Subgroup (Perm (Fin m)) where
  carrier := {g | ∀ z, (Quotient.mk'' (g z) : OrbQ B) = Quotient.mk'' z}
  one_mem' := fun z => rfl
  mul_mem' := fun {a b} ha hb z => by rw [Perm.mul_apply, ha, hb]
  inv_mem' := fun {a} ha z => by
    have h := ha (a⁻¹ z)
    rw [show a (a⁻¹ z) = z from a.apply_symm_apply z] at h
    exact h.symm

theorem le_orbitPres : B ≤ orbitPres B := by
  intro b hb z
  refine Quotient.eq''.2 ?_
  rw [MulAction.orbitRel_apply]
  exact ⟨⟨b, hb⟩, by simp [Subgroup.smul_def, Perm.smul_def]⟩

theorem card_orbitPres :
    Nat.card (orbitPres B) = ∏ c : OrbQ B, Nat.factorial (Nat.card c.orbit) := by
  classical
  have h := DomMulAct.stabilizer_card (fun z : Fin m => (Quotient.mk'' z : OrbQ B))
  have e1 : Nat.card (orbitPres B) = Fintype.card {g : Perm (Fin m) //
      (fun z : Fin m => (Quotient.mk'' z : OrbQ B)) ∘ g = fun z => Quotient.mk'' z} := by
    rw [← Nat.card_eq_fintype_card]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun g => ?_)
    exact ⟨fun h => funext fun z => h z, fun h z => congrFun h z⟩
  rw [e1, h]
  refine Finset.prod_congr rfl fun c _ => ?_
  congr 1
  rw [← Nat.card_eq_fintype_card]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun a =>
    MulAction.orbitRel.Quotient.mem_orbit.symm)

theorem isSwapGroup_of_card_ge (hsq : ∀ b ∈ B, b * b = 1)
    (hcomm : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hodd : Odd m)
    (h : Nat.card (G6.coreMod m) ≤ Nat.card B * Nat.card (fixAct (G6.coreAct m) B)) :
    IsSwapGroup B := by
  classical
  have h1 := card_le_prod_orbit B hcomm
  have h2 := prod_card_orbit_le B
  have h3 := card_fixAct_core_le B (isPGroup_two_of_sq hsq) hodd
  have h4 := one_le_card_orbQ B hodd
  have h5 := card_orbQ_le B
  rw [card_coreMod hodd.pos] at h
  have hB : 2 ^ (m - Fintype.card (OrbQ B)) ≤ Nat.card B := by
    have : 2 ^ (m - Fintype.card (OrbQ B)) * 2 ^ (Fintype.card (OrbQ B) - 1) ≤
        Nat.card B * 2 ^ (Fintype.card (OrbQ B) - 1) := by
      calc 2 ^ (m - Fintype.card (OrbQ B)) * 2 ^ (Fintype.card (OrbQ B) - 1)
          = 2 ^ (m - 1) := by rw [← pow_add]; congr 1; omega
        _ ≤ Nat.card B * Nat.card (fixAct (G6.coreAct m) B) := h
        _ ≤ Nat.card B * 2 ^ (Fintype.card (OrbQ B) - 1) := Nat.mul_le_mul_left _ h3
    exact Nat.le_of_mul_le_mul_right this (by positivity)
  have hprod : ∏ c : OrbQ B, Nat.card c.orbit = ∏ c : OrbQ B, 2 ^ (Nat.card c.orbit - 1) := by
    rw [prod_two_pow_eq]
    exact le_antisymm h2 (hB.trans h1)
  have hterm := eq_of_prod_eq Finset.univ (fun c _ => one_le_card_orbit B c)
    (fun c _ => nat_le_two_pow_pred (one_le_card_orbit B c)) hprod
  have hle2 : ∀ c : OrbQ B, Nat.card c.orbit ≤ 2 := by
    intro c
    by_contra hc
    have h6 := lt_two_pow_pred (not_le.1 hc)
    have h7 := hterm c (Finset.mem_univ c)
    omega
  have hcardB : Nat.card B = ∏ c : OrbQ B, Nat.card c.orbit :=
    le_antisymm h1 (by rw [hprod, prod_two_pow_eq]; exact hB)
  have hY : Nat.card (orbitPres B) = Nat.card B := by
    rw [card_orbitPres, hcardB]
    refine Finset.prod_congr rfl fun c _ => ?_
    have h8 := one_le_card_orbit B c
    have h9 := hle2 c
    have : Nat.card c.orbit = 1 ∨ Nat.card c.orbit = 2 := by omega
    rcases this with h | h <;> rw [h] <;> decide
  have hBY : B = orbitPres B := Subgroup.eq_of_le_of_card_ge (le_orbitPres B) hY.le
  intro d hd x
  by_cases hdx : d x = x
  · exact Or.inl hdx
  · right
    rw [hBY] at hd ⊢
    intro z
    have hdx' : (Quotient.mk'' (d x) : OrbQ B) = Quotient.mk'' x := hd x
    by_cases hz : z = x
    · subst hz
      rw [swap_apply_left]
      exact hdx'
    · by_cases hz' : z = d x
      · subst hz'
        rw [swap_apply_right]
        exact hdx'.symm
      · rw [swap_apply_of_ne_of_ne hz hz']

end Count

structure ModelFacts (m : ℕ) (Q : Type*) [Group Q] (act : Perm (Fin m) →* MulAut Q) (N : ℕ) where
  pairModel : PairModel m Q act
  index_ge : ∀ B : Subgroup (Perm (Fin m)), (∀ b ∈ B, b * b = 1) →
    (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) → Nat.card B ≤ N → Nat.card B ≤ (fixAct act B).index
  isSwapGroup : ∀ B : Subgroup (Perm (Fin m)), (∀ b ∈ B, b * b = 1) →
    (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) → B ≠ ⊥ → Nat.card B ≤ N →
    (fixAct act B).index ≤ Nat.card B → IsSwapGroup B
  exists_fixed : ∀ H : Subgroup (Perm (Fin m)), IsSwapGroup H → IsPGroup 2 H → Nat.card H ≤ N →
    ∃ c, ∀ d ∈ H, d c = c
  trichotomy : ∀ H : Subgroup (Perm (Fin m)), IsSwapGroup H → IsPGroup 2 H → H ≠ ⊥ →
    Nat.card H ≤ N → ∀ x, (∀ d ∈ H, d x = x) →
      (∃ f₁ f₂ : Fin m, f₁ ≠ x ∧ f₂ ≠ x ∧ f₁ ≠ f₂ ∧ (∀ d ∈ H, d f₁ = f₁) ∧
        ∀ d ∈ H, d f₂ = f₂) ∨ ∀ y, (∀ d ∈ H, d y = y) → y = x

@[expose] noncomputable def modelFactsOdd {m : ℕ} (hodd : Odd m) (N : ℕ) :
    ModelFacts m ↥(G6.coreMod m) (G6.coreAct m) N where
  pairModel := pairModelCore m
  index_ge B hsq hcomm _ := by
    have h := card_mul_card_fixAct_le B hsq hcomm hodd
    have h2 := Subgroup.card_mul_index (fixAct (G6.coreAct m) B)
    have hpos : 0 < Nat.card (fixAct (G6.coreAct m) B) := Nat.card_pos
    rw [← h2] at h
    exact Nat.le_of_mul_le_mul_left (by simpa [mul_comm] using h) hpos
  isSwapGroup B hsq hcomm _ _ hidx := by
    refine isSwapGroup_of_card_ge B hsq hcomm hodd ?_
    have h2 := Subgroup.card_mul_index (fixAct (G6.coreAct m) B)
    rw [← h2, mul_comm (Nat.card B)]
    exact Nat.mul_le_mul_left _ hidx
  exists_fixed H _ hp _ := exists_fixed_of_odd hp (by simpa using hodd)
  trichotomy H _ hp _ _ _ hx := fixed_trichotomy hp (by simpa using hodd) hx

end CFSG.Quasithin.C124.YZ
