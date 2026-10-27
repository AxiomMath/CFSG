module

public import CFSG.Quasithin.EmptyFaithful.SzF53MTab

public section

namespace CFSG.Quasithin.F53.Stellmacher.S29

open Equiv CFSG.Quasithin.F53Mod

private theorem exp_two_orth : ∀ Pf ∈ S5SylF.powerset, (1 : Perm (Fin 5)) ∈ Pf →
    (∀ a ∈ Pf, ∀ b ∈ Pf, a * b ∈ Pf) → (∀ a ∈ Pf, a * a = 1) →
    Pf.card ≤ 4 ∧ Pf.card * (profileFn orth Pf).2.1 ≤ 16 ∧
      (Pf.card = 4 → 4 ≤ (profileFn orth Pf).1) := by
  decide +kernel

private theorem exp_two_nat : ∀ Pf ∈ S5SylF.powerset, (1 : Perm (Fin 5)) ∈ Pf →
    (∀ a ∈ Pf, ∀ b ∈ Pf, a * b ∈ Pf) → (∀ a ∈ Pf, a * a = 1) →
    Pf.card ≤ 4 ∧ Pf.card * (profileFn nat Pf).2.1 ≤ 16 ∧
      (Pf.card = 4 → 4 ≤ (profileFn nat Pf).1) := by
  decide +kernel

private theorem centralizer_comm_orth : ∀ σ ∈ S5SylF,
    (∀ y ∈ spanF (commGensF orth S5SylF Finset.univ), orth.act σ y = y) → σ = 1 := by
  decide +kernel

private theorem centralizer_comm_nat : ∀ σ ∈ S5SylF,
    (∀ y ∈ spanF (commGensF nat S5SylF Finset.univ), nat.act σ y = y) → σ = 1 := by
  decide +kernel

theorem exp_two_profile (M : Model 5) (hM : M = orth ∨ M = nat) {P : Subgroup (Perm (Fin 5))}
    (hP : P ≤ S5Syl) (hsq : ∀ x ∈ P, x * x = 1) :
    Nat.card P ≤ 4 ∧ Nat.card P * Nat.card (fixW M P) ≤ 16 ∧
      (Nat.card P = 4 → 4 ≤ Nat.card (commW M P ⊤)) := by
  classical
  set Pf : Finset (Perm (Fin 5)) := S5SylF.filter (· ∈ P) with hPfdef
  have hPf : ∀ σ, σ ∈ P ↔ σ ∈ Pf := by
    intro σ
    rw [hPfdef, Finset.mem_filter, ← mem_S5Syl_iff]
    exact ⟨fun h => ⟨hP h, h⟩, fun h => h.2⟩
  have hcard : Nat.card P = Pf.card := by
    rw [← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight hPf)
  have hsub : Pf ∈ S5SylF.powerset := Finset.mem_powerset.mpr (Finset.filter_subset _ _)
  have h1 : (1 : Perm (Fin 5)) ∈ Pf := (hPf 1).mp P.one_mem
  have hmul : ∀ a ∈ Pf, ∀ b ∈ Pf, a * b ∈ Pf := fun a ha b hb =>
    (hPf _).mp (P.mul_mem ((hPf a).mpr ha) ((hPf b).mpr hb))
  have hsq' : ∀ a ∈ Pf, a * a = 1 := fun a ha => hsq a ((hPf a).mpr ha)
  rw [hcard]
  rcases hM with rfl | rfl
  · have hprof := profile_eq orth hPf
    have key := exp_two_orth Pf hsub h1 hmul hsq'
    rw [profile, Prod.ext_iff, Prod.ext_iff] at hprof
    rw [← hprof.2.1] at key
    rw [← hprof.1] at key
    simpa [hcard] using key
  · have hprof := profile_eq nat hPf
    have key := exp_two_nat Pf hsub h1 hmul hsq'
    rw [profile, Prod.ext_iff, Prod.ext_iff] at hprof
    rw [← hprof.2.1] at key
    rw [← hprof.1] at key
    simpa [hcard] using key

theorem eq_one_of_fixes_commW_sylow (M : Model 5) (hM : M = orth ∨ M = nat) {σ : Perm (Fin 5)}
    (hσ : σ ∈ S5Syl) (hfix : ∀ y ∈ commW M S5Syl ⊤, M.act σ y = y) : σ = 1 := by
  have hB : ∀ τ, τ ∈ S5Syl ↔ τ ∈ S5SylF := mem_S5Syl_iff
  rcases hM with rfl | rfl
  · have hTop : ∀ u : orth.W, u ∈ (⊤ : Subgroup orth.W) ↔ u ∈ (Finset.univ : Finset orth.W) := by
      intro u; simp
    exact centralizer_comm_orth σ ((mem_S5Syl_iff σ).mp hσ) fun y hy =>
      hfix y ((mem_commW_iff orth hB hTop y).mpr hy)
  · have hTop : ∀ u : nat.W, u ∈ (⊤ : Subgroup nat.W) ↔ u ∈ (Finset.univ : Finset nat.W) := by
      intro u; simp
    exact centralizer_comm_nat σ ((mem_S5Syl_iff σ).mp hσ) fun y hy =>
      hfix y ((mem_commW_iff nat hB hTop y).mpr hy)

end CFSG.Quasithin.F53.Stellmacher.S29
