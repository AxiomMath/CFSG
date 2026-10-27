module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseModA

public section

namespace CFSG.Quasithin.F53.Stellmacher.S43.Even.E17

open CFSG.Quasithin.F53Mod Equiv

@[expose] def sgA : Perm (Fin 5) := swap 0 4 * swap 0 3 * swap 0 1

@[expose] def sgB : Perm (Fin 5) := swap 1 4 * swap 1 3 * swap 1 2

@[expose] def dd : Perm (Fin 5) := swap 0 1 * swap 1 2

@[expose] def qq : Perm (Fin 5) := swap 0 1 * swap 1 2 * swap 2 3

@[expose] def InY (y : orth.W) : Prop := ∀ b ∈ S5ThatF, orth.act b y = y

instance (y : orth.W) : Decidable (InY y) := by unfold InY; infer_instance

theorem mem_fixW_That_iff (y : orth.W) : y ∈ fixW orth S5That ↔ InY y := by
  rw [mem_fixW]
  exact ⟨fun h b hb => h b ((mem_S5That_iff b).mpr hb),
    fun h b hb => h b ((mem_S5That_iff b).mp hb)⟩

private theorem InY_iff_commTwoF : ∀ w : orth.W, InY w ↔ w ∈ commTwoF := by decide +kernel

theorem commIter_two_eq_fixW_That : F53Mod.commIter orth S5Syl 2 = fixW orth S5That := by
  ext w
  rw [mem_commIter_two_iff, mem_fixW_That_iff, InY_iff_commTwoF]

private theorem swap_of_ThatF : ∀ σ ∈ S5ThatF, σ ≠ 1 → σ ^ 2 = 1 → Perm.sign σ ≠ 1 →
    σ = swap 0 2 ∨ σ = swap 1 3 := by decide +kernel

theorem swap_of_That_idx (σ : Perm (Fin 5)) (hσ : σ ∈ S5That) (h : idx orth σ = 2) :
    σ = swap 0 2 ∨ σ = swap 1 3 := by
  have h1 : σ ≠ 1 := by
    rintro rfl
    have : idx orth 1 = 1 := by
      unfold idx
      rw [Subgroup.index_eq_one, eq_top_iff]
      intro w _
      rw [mem_fixW_zpowers, map_one]
      rfl
    omega
  obtain ⟨-, h2, h3⟩ := (isSwap_iff σ).mp (((transvections σ h1).2).mp h)
  exact swap_of_ThatF σ ((mem_S5That_iff σ).mp hσ) h1 h2 h3

private theorem f17a_A : ∀ y : orth.W, InY y → InY (orth.act sgA y) → y = 1 := by
  decide +kernel

private theorem f17a_B : ∀ y : orth.W, InY y → InY (orth.act sgB y) → y = 1 := by
  decide +kernel

theorem inf_Y_eq (σ : Perm (Fin 5)) (hσ : σ = sgA ∨ σ = sgB) :
    ∀ y ∈ fixW orth S5That, orth.act σ y ∈ fixW orth S5That → y = 1 := by
  intro y hy hσy
  rw [mem_fixW_That_iff] at hy hσy
  rcases hσ with rfl | rfl
  · exact f17a_A y hy hσy
  · exact f17a_B y hy hσy

theorem sgA_moves : (sgA⁻¹ * swap 0 2 * sgA : Perm (Fin 5)) 4 ≠ 4 := by decide +kernel

theorem sgB_moves : (sgB⁻¹ * swap 1 3 * sgB : Perm (Fin 5)) 4 ≠ 4 := by decide +kernel

private theorem f17b_A : ∀ ρ ∈ S5ThatF, sgA⁻¹ * ρ * sgA ∈ S5SylF → ρ = 1 := by decide +kernel

private theorem f17b_B : ∀ ρ ∈ S5ThatF, sgB⁻¹ * ρ * sgB ∈ S5SylF → ρ = 1 := by decide +kernel

theorem That_inf_conj (σ : Perm (Fin 5)) (hσ : σ = sgA ∨ σ = sgB) {ρ : Perm (Fin 5)}
    (hρ : ρ ∈ S5That) (h : σ⁻¹ * ρ * σ ∈ S5Syl) : ρ = 1 := by
  rw [mem_S5That_iff] at hρ
  rw [mem_S5Syl_iff] at h
  rcases hσ with rfl | rfl
  · exact f17b_A ρ hρ h
  · exact f17b_B ρ hρ h

theorem qq_mem : qq ∈ S5Syl := by
  rw [mem_S5Syl_iff]; decide +kernel

private theorem three_classes_aux : ∀ τ ∈ ({swap 0 2, swap 1 3} : Finset (Perm (Fin 5))),
    τ ≠ 1 ∧ qq * τ * qq⁻¹ ≠ 1 ∧ τ⁻¹ * (qq * τ * qq⁻¹) ≠ 1 := by decide +kernel

theorem three_classes {τ : Perm (Fin 5)} (hτ : τ = swap 0 2 ∨ τ = swap 1 3) :
    τ ≠ 1 ∧ qq * τ * qq⁻¹ ≠ 1 ∧ τ⁻¹ * (qq * τ * qq⁻¹) ≠ 1 :=
  three_classes_aux τ (by rcases hτ with rfl | rfl <;> simp)

theorem qq_sq_mem : qq * qq ∈ S5That := by
  rw [mem_S5That_iff]; decide +kernel

theorem S5Syl_eq_closure : S5Syl = Subgroup.closure {qq, swap 0 2} := rfl

@[expose] def InNY (u : nat.W) : Prop := ∀ b ∈ S5ThatF, nat.act b u = u

instance (u : nat.W) : Decidable (InNY u) := by unfold InNY; infer_instance

theorem mem_fixW_nat_That_iff (u : nat.W) : u ∈ fixW nat S5That ↔ InNY u := by
  rw [mem_fixW]
  exact ⟨fun h b hb => h b ((mem_S5That_iff b).mpr hb),
    fun h b hb => h b ((mem_S5That_iff b).mp hb)⟩

private theorem f17c_unique : ∀ u v : nat.W, InNY u → InNY v → u ≠ 1 → v ≠ 1 → u = v := by
  decide +kernel

private theorem f17c_stab : ∀ u : nat.W, InNY u → u ≠ 1 → ∀ σ : Perm (Fin 5),
    nat.act σ u = u → σ ∈ S5SylF := by
  decide +kernel

theorem nat_That_unique {u v : nat.W} (hu : u ∈ fixW nat S5That) (hv : v ∈ fixW nat S5That)
    (hu1 : u ≠ 1) (hv1 : v ≠ 1) : u = v :=
  f17c_unique u v ((mem_fixW_nat_That_iff u).mp hu) ((mem_fixW_nat_That_iff v).mp hv) hu1 hv1

theorem nat_That_stab {u : nat.W} (hu : u ∈ fixW nat S5That) (hu1 : u ≠ 1) {σ : Perm (Fin 5)}
    (hσ : nat.act σ u = u) : σ ∈ S5Syl :=
  (mem_S5Syl_iff σ).mpr (f17c_stab u ((mem_fixW_nat_That_iff u).mp hu) hu1 σ hσ)

private theorem exists_Y_moved_aux : ∃ y : orth.W, InY y ∧ orth.act qq y ≠ y := by
  decide +kernel

theorem exists_Y_moved : ∃ y ∈ fixW orth S5That, orth.act qq y ≠ y := by
  obtain ⟨y, hy, h⟩ := exists_Y_moved_aux
  exact ⟨y, (mem_fixW_That_iff y).mpr hy, h⟩

private theorem qq_sub_aux : ∀ y : orth.W, InY y → orth.act qq y ≠ y →
    orth.act qq y * y⁻¹ ≠ 1 ∧ ∀ σ : Perm (Fin 5), σ 4 = 4 →
      orth.act σ (orth.act qq y * y⁻¹) = orth.act qq y * y⁻¹ := by
  decide +kernel

theorem qq_sub_fixed {y : orth.W} (hy : y ∈ fixW orth S5That) (hq : orth.act qq y ≠ y) :
    orth.act qq y * y⁻¹ ≠ 1 ∧ ∀ σ : Perm (Fin 5), σ 4 = 4 →
      orth.act σ (orth.act qq y * y⁻¹) = orth.act qq y * y⁻¹ :=
  qq_sub_aux y ((mem_fixW_That_iff y).mp hy) hq

theorem dd_four : dd 4 = 4 := by decide +kernel

theorem dd_cube : dd ^ 3 = 1 := by decide +kernel

theorem dd_mem_alt : dd ∈ alternatingGroup (Fin 5) := by
  rw [Perm.mem_alternatingGroup]; decide +kernel

private theorem stab_four_aux : ∀ σ : Perm (Fin 5), σ 4 = 4 →
    σ ∈ S5SylF ∨ dd⁻¹ * σ ∈ S5SylF ∨ dd⁻¹ * dd⁻¹ * σ ∈ S5SylF := by
  decide +kernel

theorem stab_four_cover (σ : Perm (Fin 5)) (hσ : σ 4 = 4) :
    σ ∈ S5Syl ∨ dd⁻¹ * σ ∈ S5Syl ∨ dd⁻¹ * dd⁻¹ * σ ∈ S5Syl := by
  simp only [mem_S5Syl_iff]
  exact stab_four_aux σ hσ

private theorem dd_norm_T_aux : ∀ τ ∈ S5TF, dd⁻¹ * τ * dd ∈ S5TF := by decide +kernel

theorem dd_norm_T {τ : Perm (Fin 5)} (hτ : τ ∈ S5T) : dd⁻¹ * τ * dd ∈ S5T := by
  rw [mem_S5T_iff] at hτ ⊢
  exact dd_norm_T_aux τ hτ

private theorem S5TF_le : ∀ τ ∈ S5TF, τ ∈ S5SylF := by decide +kernel

theorem S5T_le_S5Syl {τ : Perm (Fin 5)} (hτ : τ ∈ S5T) : τ ∈ S5Syl := by
  rw [mem_S5T_iff] at hτ
  rw [mem_S5Syl_iff]
  exact S5TF_le τ hτ

private theorem dd_fix_T_aux : ∀ w : orth.W, (∀ τ ∈ S5TF, orth.act τ w = w) →
    orth.act dd w = w := by
  decide +kernel

theorem dd_fix_T {w : orth.W} (hw : ∀ τ ∈ S5T, orth.act τ w = w) : orth.act dd w = w :=
  dd_fix_T_aux w fun τ hτ => hw τ ((mem_S5T_iff τ).mpr hτ)

@[expose] def coord (v : orth.W) (i : Fin 5) : ℕ :=
  (Multiplicative.toAdd ((v : ↥(G6.coreMod 5)).1) i).val

private theorem section_aux : ∀ c : orth.W, c ≠ 1 → (∀ σ : Perm (Fin 5), σ 4 = 4 →
    orth.act σ c = c) → ∀ v : orth.W,
    ∏ i : Fin 5, (orth.act (swap 4 i) c) ^ coord v i = v := by
  decide +kernel

theorem section_eq {c : orth.W} (hc : c ≠ 1) (hS : ∀ σ : Perm (Fin 5), σ 4 = 4 →
    orth.act σ c = c) (v : orth.W) : ∏ i : Fin 5, (orth.act (swap 4 i) c) ^ coord v i = v :=
  section_aux c hc hS v

set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 1024 in
private theorem swap_facts_a : ∀ t : Perm (Fin 5), t ≠ 1 → t ^ 2 = 1 → Perm.sign t ≠ 1 →
    t 4 ≠ 4 → ∃ y : orth.W, InY y ∧ y ≠ 1 ∧ orth.act t y = y := by
  decide +kernel

private theorem swap_facts_b : ∀ t : Perm (Fin 5), t ≠ 1 → t ^ 2 = 1 → Perm.sign t ≠ 1 →
    t 4 ≠ 4 → ∀ y : orth.W, InY y → y ≠ 1 → orth.act t y = y →
      orth.act t (orth.act qq y) ≠ orth.act qq y := by
  decide +kernel

set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 1024 in
private theorem swap_facts_c : ∀ t : Perm (Fin 5), t ≠ 1 → t ^ 2 = 1 → Perm.sign t ≠ 1 →
    t 4 ≠ 4 → ∀ y y' : orth.W, InY y → InY y' → y ≠ 1 → y' ≠ 1 → orth.act t y = y →
      orth.act t y' = y' → y = y' := by
  decide +kernel

private theorem swap_facts_d : ∀ t : Perm (Fin 5), t ≠ 1 → t ^ 2 = 1 → Perm.sign t ≠ 1 →
    t 4 ≠ 4 → ∀ y₀ : orth.W, InY y₀ → y₀ ≠ 1 → orth.act t y₀ = y₀ → ∀ y : orth.W, InY y →
      y = 1 ∨ y = y₀ ∨ y = orth.act qq y₀ ∨ y = y₀ * orth.act qq y₀ := by
  decide +kernel

theorem swap_facts {t : Perm (Fin 5)} (ht : t.IsSwap) (h4 : t 4 ≠ 4) :
    (∃ y ∈ fixW orth S5That, y ≠ 1 ∧ orth.act t y = y) ∧
    (∀ y ∈ fixW orth S5That, y ≠ 1 → orth.act t y = y →
      orth.act t (orth.act qq y) ≠ orth.act qq y) ∧
    (∀ y ∈ fixW orth S5That, ∀ y' ∈ fixW orth S5That, y ≠ 1 → y' ≠ 1 → orth.act t y = y →
      orth.act t y' = y' → y = y') ∧
    (∀ y₀ ∈ fixW orth S5That, y₀ ≠ 1 → orth.act t y₀ = y₀ → ∀ y ∈ fixW orth S5That,
      y = 1 ∨ y = y₀ ∨ y = orth.act qq y₀ ∨ y = y₀ * orth.act qq y₀) := by
  obtain ⟨h1, h2, h3⟩ := (isSwap_iff t).mp ht
  obtain ⟨y, hy, hy1, hyt⟩ := swap_facts_a t h1 h2 h3 h4
  have hb := swap_facts_b t h1 h2 h3 h4
  have hc := swap_facts_c t h1 h2 h3 h4
  have hd := swap_facts_d t h1 h2 h3 h4
  refine ⟨⟨y, (mem_fixW_That_iff y).mpr hy, hy1, hyt⟩, fun y hy => hb y
    ((mem_fixW_That_iff y).mp hy), fun y hy y' hy' => hc y y' ((mem_fixW_That_iff y).mp hy)
    ((mem_fixW_That_iff y').mp hy'), fun y₀ hy₀ h1 h2 y hy => hd y₀
    ((mem_fixW_That_iff y₀).mp hy₀) h1 h2 y ((mem_fixW_That_iff y).mp hy)⟩

end CFSG.Quasithin.F53.Stellmacher.S43.Even.E17
