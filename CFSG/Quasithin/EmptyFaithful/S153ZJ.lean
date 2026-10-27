module

public import CFSG.Quasithin.EmptyFaithful.S153ZI
public import CFSG.Quasithin.EmptyFaithful.S153ZH

public section

namespace CFSG.Quasithin.Z391

open scoped Pointwise

variable {Γ : Type*} [Group Γ] {Q : Type*} [CommGroup Q] [MulDistribMulAction Γ Q]

theorem nB_block [Finite Q] [Finite Γ] (S : Subgroup Q) :
    ∀ (n : ℕ) (A A₁ : Subgroup Γ), (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) → (∀ x ∈ A, x ^ 2 = 1) →
      A₁ ≤ A → rk ↥A = rk ↥A₁ + n → (∀ a ∈ A₁, a • S = S) → (∀ a ∈ A, a • S = S → a ∈ A₁) →
      sSupIndep (Set.range fun t : ↥A => (t : Γ) • S) →
      nB A₁ S + (2 ^ n - 1) * rk ↥S ≤ nB A (⨆ t : ↥A, (t : Γ) • S) ∧
        rk ↥(⨆ t : ↥A, (t : Γ) • S) = 2 ^ n * rk ↥S := by
  intro n
  induction n with
  | zero =>
    intro A A₁ hAc hA2 hA₁A hrk hfix hstab hind
    have hcard : Nat.card ↥A ≤ Nat.card ↥A₁ := by
      rw [rk_eq_log_of_elem hA2, rk_eq_log_of_elem (fun x hx => hA2 x (hA₁A hx))]
      simp [hrk]
    have hA : A₁ = A := Subgroup.eq_of_le_of_card_ge hA₁A hcard
    subst hA
    have hP : (⨆ t : ↥A₁, (t : Γ) • S) = S := by
      refine le_antisymm (iSup_le fun t => (hfix t t.2).le) ?_
      exact le_iSup_of_le ⟨1, A₁.one_mem⟩ (by simp)
    rw [hP]
    simp
  | succ n ih =>
    intro A A₁ hAc hA2 hA₁A hrk hfix hstab hind
    have hne : A₁ ≠ A := by
      intro h
      subst h
      omega
    obtain ⟨a, A', haA, hA₁A', hA'A, haA', hsplit⟩ := exists_index_two_sub hAc hA2 hA₁A hne
    have hAc' : ∀ x ∈ A', ∀ y ∈ A', x * y = y * x := fun x hx y hy => hAc x (hA'A hx) y (hA'A hy)
    have hA2' : ∀ x ∈ A', x ^ 2 = 1 := fun x hx => hA2 x (hA'A hx)
    have hrk' : rk ↥A = rk ↥A' + 1 := rk_index_two haA hAc hA2 hA'A haA' hsplit
    have hrkA' : rk ↥A' = rk ↥A₁ + n := by omega
    set P' : Subgroup Q := ⨆ t : ↥A', (t : Γ) • S with hP'
    have hind' : sSupIndep (Set.range fun t : ↥A' => (t : Γ) • S) := by
      refine hind.mono ?_
      rintro _ ⟨t, rfl⟩
      exact ⟨⟨t, hA'A t.2⟩, rfl⟩
    obtain ⟨ih1, ih2⟩ :=
      ih A' A₁ hAc' hA2' hA₁A' hrkA' hfix (fun x hx hxS => hstab x (hA'A hx) hxS) hind'
    rw [← hP'] at ih1 ih2
    have hPeq : (⨆ t : ↥A, (t : Γ) • S) = P' ⊔ a • P' := by
      refine le_antisymm (iSup_le fun t => ?_) (sup_le ?_ ?_)
      · rcases hsplit (t : Γ) t.2 with h | h
        · exact (le_iSup (fun s : ↥A' => (s : Γ) • S) ⟨t, h⟩).trans le_sup_left
        · refine le_trans ?_ le_sup_right
          have h1 : (a⁻¹ * (t : Γ)) • S ≤ P' :=
            le_iSup (fun s : ↥A' => (s : Γ) • S) ⟨a⁻¹ * (t : Γ), h⟩
          have h2 : a • ((a⁻¹ * (t : Γ)) • S) ≤ a • P' :=
            Subgroup.pointwise_smul_le_pointwise_smul_iff.2 h1
          rwa [smul_smul, mul_inv_cancel_left] at h2
      · exact iSup_le fun t => le_iSup (fun s : ↥A => (s : Γ) • S) ⟨t, hA'A t.2⟩
      · rw [hP', smul_iSup_translate]
        exact iSup_le fun t =>
          le_iSup (fun s : ↥A => (s : Γ) • S) ⟨a * (t : Γ), A.mul_mem haA (hA'A t.2)⟩
    have hinv : XMod.IsInv ↥A' P' := by
      intro b x hx
      have h1 : (b : Γ) • P' ≤ P' := by
        rw [hP', smul_iSup_translate]
        exact iSup_le fun t =>
          le_iSup (fun s : ↥A' => (s : Γ) • S) ⟨(b : Γ) * (t : Γ), A'.mul_mem b.2 t.2⟩
      exact h1 (Subgroup.smul_mem_pointwise_smul _ _ _ hx)
    have hdisj : P' ⊓ a • P' = ⊥ := by
      rw [← disjoint_iff]
      have hY : Set.range (fun t : ↥A' => (t : Γ) • S) ⊆ Set.range (fun t : ↥A => (t : Γ) • S) := by
        rintro _ ⟨t, rfl⟩
        exact ⟨⟨t, hA'A t.2⟩, rfl⟩
      have hZ : Set.range (fun t : ↥A' => (a * (t : Γ)) • S) ⊆
          Set.range (fun t : ↥A => (t : Γ) • S) := by
        rintro _ ⟨t, rfl⟩
        exact ⟨⟨a * (t : Γ), A.mul_mem haA (hA'A t.2)⟩, rfl⟩
      have hYZ : Disjoint (Set.range (fun t : ↥A' => (t : Γ) • S))
          (Set.range (fun t : ↥A' => (a * (t : Γ)) • S)) := by
        rw [Set.disjoint_left]
        rintro _ ⟨t, rfl⟩ ⟨t', ht'⟩
        have h1 : ((a * (t' : Γ))⁻¹ * (t : Γ)) • S = S := by
          rw [mul_smul]
          have : (t : Γ) • S = (a * (t' : Γ)) • S := ht'.symm
          rw [this, inv_smul_smul]
        have h2 : (a * (t' : Γ))⁻¹ * (t : Γ) ∈ A₁ :=
          hstab _ (A.mul_mem (A.inv_mem (A.mul_mem haA (hA'A t'.2))) (hA'A t.2)) h1
        have h3 : (a * (t' : Γ))⁻¹ * (t : Γ) ∈ A' := hA₁A' h2
        apply haA'
        have h4 : a⁻¹ ∈ A' := by
          have := A'.mul_mem (A'.mul_mem t'.2 h3) (A'.inv_mem t.2)
          have e : (t' : Γ) * ((a * (t' : Γ))⁻¹ * (t : Γ)) * (t : Γ)⁻¹ = a⁻¹ := by group
          rwa [e] at this
        simpa using A'.inv_mem h4
      have := disjoint_sSup_of_sSupIndep hind hY hZ hYZ
      rwa [sSup_range, sSup_range, ← smul_iSup_translate] at this
    have hblk := nB_index_two haA (hA2 a haA) hAc hA'A hsplit hinv hdisj
    have hrk2 : rk ↥(P' ⊔ a • P') = 2 * rk ↥P' := by
      have h1 := rk_sup_add_rk_inf P' (a • P')
      rw [hdisj, rk_bot, rk_smul] at h1
      omega
    rw [hPeq, hblk, hrk2]
    have hm : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have e : 2 ^ (n + 1) - 1 = 2 ^ n + (2 ^ n - 1) := by
      rw [pow_succ]
      omega
    refine ⟨?_, ?_⟩
    · rw [e, Nat.add_mul]
      omega
    · rw [ih2, pow_succ]
      ring

end CFSG.Quasithin.Z391
