module

public import CFSG.Quasithin.Vol2.Ch3Sec3CZL32

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.Ins314

open CFSG.Quasithin CFSG.Quasithin.H13.CZL32

@[expose] def zB : L3.Γ := ⟨!![1, 0, 1; 0, 1, 0; 0, 0, 1], by decide⟩

theorem center_check : ∀ g : L3.Γ, (L3.act g e1 = e1 ∧ ∀ v, v ∈ P12 ↔ L3.act g v ∈ P12) →
    ((∀ h : L3.Γ, (L3.act h e1 = e1 ∧ ∀ v, v ∈ P12 ↔ L3.act h v ∈ P12) → g * h = h * g) ↔
      (g = 1 ∨ g = zB)) := by
  decide +kernel

theorem zB_mem : zB ∈ bSub := by
  rw [mem_bSub]
  decide +kernel

theorem mem_center_bSub_iff {g : L3.Γ} (hg : g ∈ bSub) :
    (∀ h ∈ bSub, g * h = h * g) ↔ g = 1 ∨ g = zB :=
  center_check g (mem_bSub.mp hg)

theorem fix_check : ∀ v : L3.Vec, (∀ g : L3.Γ, (L3.act g e1 = e1 ∧
    ∀ w, w ∈ P12 ↔ L3.act g w ∈ P12) → L3.act g v = v) ↔ (v = 0 ∨ v = e1) := by
  decide +kernel

theorem fix_bSub_iff (v : L3.Vec) : (∀ g ∈ bSub, L3.act g v = v) ↔ v = 0 ∨ v = e1 := by
  rw [← fix_check v]
  exact ⟨fun h g hg => h g (mem_bSub.mpr hg), fun h g hg => h g (mem_bSub.mp hg)⟩

theorem fix_zB_iff : ∀ v : L3.Vec, L3.act zB v = v ↔ v ∈ P12 := by
  decide +kernel

theorem card_stabSub_filter : (Finset.univ.filter fun g : L3.Γ =>
    ∀ v, v ∈ P12 ↔ L3.act g v ∈ P12).card = 24 := by
  decide +kernel

theorem card_stabSub : Nat.card (L3.stabSub P12) = 24 := by
  rw [← card_stabSub_filter, ← Fintype.card_coe, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x => by simp [L3.mem_stabSub])

@[expose] def wP : L3.Γ := ⟨!![1, 0, 0; 0, 0, 1; 0, 1, 0], by decide⟩

theorem wP_mem : wP ∈ L3.ptSub e1 := by
  show L3.act wP e1 = e1
  decide +kernel

theorem wP_not_mem : wP ∉ L3.stabSub P12 := by
  rw [L3.mem_stabSub]
  intro h
  have := (h e2).mp (by decide)
  revert this
  decide +kernel

theorem sup_parabolics : L3.ptSub e1 ⊔ L3.stabSub P12 = ⊤ := by
  have h2 : (L3.ptSub e1).relIndex (L3.ptSub e1 ⊔ L3.stabSub P12) *
      Nat.card ↥(L3.ptSub e1) = Nat.card ↥(L3.ptSub e1 ⊔ L3.stabSub P12) := by
    have := Subgroup.relIndex_mul_card (H := L3.ptSub e1) (K := L3.ptSub e1 ⊔ L3.stabSub P12)
    rwa [inf_of_le_left le_sup_left] at this
  rw [card_ptSub] at h2
  have hΓ : Nat.card L3.Γ = 168 := card_L3Γ
  have hne : (L3.ptSub e1).relIndex (L3.ptSub e1 ⊔ L3.stabSub P12) ≠ 1 := by
    intro h
    rw [Subgroup.relIndex_eq_one] at h
    exact wP_not_mem (by
      have hle : L3.stabSub P12 ≤ L3.ptSub e1 := le_sup_right.trans h
      have heq : L3.stabSub P12 = L3.ptSub e1 :=
        Subgroup.eq_of_le_of_card_ge hle (by rw [card_ptSub, card_stabSub])
      rw [heq]
      exact wP_mem)
  have hdvd : Nat.card ↥(L3.ptSub e1 ⊔ L3.stabSub P12) ∣ 168 := by
    rw [← hΓ]
    exact Subgroup.card_subgroup_dvd_card _
  rw [← h2] at hdvd
  obtain ⟨k, hk⟩ := hdvd
  have hk7 : (L3.ptSub e1).relIndex (L3.ptSub e1 ⊔ L3.stabSub P12) * k = 7 := by
    have e : 24 * ((L3.ptSub e1).relIndex (L3.ptSub e1 ⊔ L3.stabSub P12) * k) = 168 := by
      rw [hk]
      ring
    omega
  have h7 : (L3.ptSub e1).relIndex (L3.ptSub e1 ⊔ L3.stabSub P12) = 7 := by
    have hd : (L3.ptSub e1).relIndex (L3.ptSub e1 ⊔ L3.stabSub P12) ∣ 7 := ⟨k, hk7.symm⟩
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp hd with h | h
    · exact absurd h hne
    · exact h
  apply Subgroup.eq_top_of_card_eq
  rw [← h2, h7, hΓ]

@[expose] def c1 : L3.Γ := ⟨!![1, 0, 0; 0, 0, 1; 0, 1, 1], by decide⟩

@[expose] def c2 : L3.Γ := ⟨!![0, 1, 0; 1, 1, 0; 0, 0, 1], by decide⟩

theorem normalizer_bSub_check : ∀ g : L3.Γ, (∀ b : L3.Γ, (L3.act b e1 = e1 ∧
    ∀ v, v ∈ P12 ↔ L3.act b v ∈ P12) → (L3.act (g * b * g⁻¹) e1 = e1 ∧
      ∀ v, v ∈ P12 ↔ L3.act (g * b * g⁻¹) v ∈ P12)) →
    (L3.act g e1 = e1 ∧ ∀ v, v ∈ P12 ↔ L3.act g v ∈ P12) := by
  decide +kernel

theorem mem_bSub_of_normalizes {g : L3.Γ} (hg : ∀ b ∈ bSub, g * b * g⁻¹ ∈ bSub) : g ∈ bSub :=
  mem_bSub.mpr (normalizer_bSub_check g fun b hb => mem_bSub.mp (hg b (mem_bSub.mpr hb)))

theorem cosets1_check : ∀ y : L3.Γ, L3.act y e1 = e1 →
    ∃ j : Fin 3, (L3.act ((c1 ^ (j : ℕ))⁻¹ * y) e1 = e1 ∧
      ∀ v, v ∈ P12 ↔ L3.act ((c1 ^ (j : ℕ))⁻¹ * y) v ∈ P12) := by
  decide +kernel

theorem cosets2_check : ∀ y : L3.Γ, (∀ v, v ∈ P12 ↔ L3.act y v ∈ P12) →
    ∃ j : Fin 3, (L3.act ((c2 ^ (j : ℕ))⁻¹ * y) e1 = e1 ∧
      ∀ v, v ∈ P12 ↔ L3.act ((c2 ^ (j : ℕ))⁻¹ * y) v ∈ P12) := by
  decide +kernel

theorem exists_coset1 {y : L3.Γ} (hy : y ∈ L3.ptSub e1) :
    ∃ j : Fin 3, (c1 ^ (j : ℕ))⁻¹ * y ∈ bSub := by
  obtain ⟨j, hj⟩ := cosets1_check y hy
  exact ⟨j, mem_bSub.mpr hj⟩

theorem exists_coset2 {y : L3.Γ} (hy : y ∈ L3.stabSub P12) :
    ∃ j : Fin 3, (c2 ^ (j : ℕ))⁻¹ * y ∈ bSub := by
  obtain ⟨j, hj⟩ := cosets2_check y hy
  exact ⟨j, mem_bSub.mpr hj⟩

theorem c1_mem : c1 ∈ L3.ptSub e1 := by
  show L3.act c1 e1 = e1
  decide +kernel

theorem c2_mem : c2 ∈ L3.stabSub P12 := by
  rw [L3.mem_stabSub]
  decide +kernel

theorem distinct1_check : ∀ i j : Fin 3, i ≠ j →
    ¬ (L3.act ((c1 ^ (j : ℕ))⁻¹ * c1 ^ (i : ℕ)) e1 = e1 ∧
      ∀ v, v ∈ P12 ↔ L3.act ((c1 ^ (j : ℕ))⁻¹ * c1 ^ (i : ℕ)) v ∈ P12) := by
  decide +kernel

theorem distinct2_check : ∀ i j : Fin 3, i ≠ j →
    ¬ (L3.act ((c2 ^ (j : ℕ))⁻¹ * c2 ^ (i : ℕ)) e1 = e1 ∧
      ∀ v, v ∈ P12 ↔ L3.act ((c2 ^ (j : ℕ))⁻¹ * c2 ^ (i : ℕ)) v ∈ P12) := by
  decide +kernel

end CFSG.Quasithin.H13.Ins314
