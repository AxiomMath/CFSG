module

public import CFSG.Quasithin.Vol2.GoldschmidtEnd1222Basic

public section

namespace CFSG.Quasithin.H13

namespace End1222

open CFSG.Quasithin CFSG.Quasithin.G6

namespace AltDn

variable {n : ℕ}

@[expose] def dpair (n : ℕ) : PermMod n :=
  Multiplicative.ofAdd fun i : Fin n => if i.val < 2 then (1 : ZMod 2) else 0

theorem toAdd_dpair (i : Fin n) :
    Multiplicative.toAdd (dpair n) i = if i.val < 2 then 1 else 0 := rfl

theorem dpair_mem_coreMod (hn : 2 ≤ n) : dpair n ∈ coreMod n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  rw [mem_coreMod, Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp [toAdd_dpair, Fin.val_succ]
  decide

@[expose] def kerSub (n : ℕ) : Subgroup (PermMod n) := Subgroup.zpowers (allOnes n) ⊓ coreMod n

theorem mem_kerSub_iff {x : PermMod n} :
    x ∈ kerSub n ↔ x ∈ coreMod n ∧ ∃ b : ZMod 2, ∀ i, Multiplicative.toAdd x i = b := by
  rw [kerSub, Subgroup.mem_inf, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨⟨k, hk⟩, hc⟩
    refine ⟨hc, (k : ZMod 2), fun i => ?_⟩
    rw [← hk]
    simp [allOnes]
  · rintro ⟨hc, b, hb⟩
    refine ⟨?_, hc⟩
    refine ⟨(b.val : ℤ), ?_⟩
    apply Multiplicative.toAdd.injective
    funext i
    rw [hb i]
    simp [allOnes]

theorem dpair_not_mem_kerSub (hn : 5 ≤ n) : dpair n ∉ kerSub n := by
  rw [mem_kerSub_iff]
  rintro ⟨-, b, hb⟩
  have h0 := hb ⟨0, by omega⟩
  have h2 := hb ⟨2, by omega⟩
  rw [toAdd_dpair] at h0 h2
  simp at h0 h2
  rw [← h0] at h2
  exact absurd h2 (by decide)

theorem toAdd_permAct_mul_inv (σ : Equiv.Perm (Fin n)) (m : PermMod n) (i : Fin n) :
    Multiplicative.toAdd (permAct n σ m * m⁻¹) i =
      Multiplicative.toAdd m (σ⁻¹ i) - Multiplicative.toAdd m i := by
  rw [toAdd_mul, toAdd_inv, Pi.add_apply, Pi.neg_apply, permAct_apply, sub_eq_add_neg]
  rfl

@[expose] def Pres (σ : Equiv.Perm (Fin n)) : Prop := ∀ i : Fin n, (σ i).val < 2 ↔ i.val < 2

theorem Pres.mul {σ τ : Equiv.Perm (Fin n)} (hσ : Pres σ) (hτ : Pres τ) : Pres (σ * τ) :=
  fun i => (hσ (τ i)).trans (hτ i)

theorem pres_swap (a b : Fin n) (h : a.val < 2 ↔ b.val < 2) : Pres (Equiv.swap a b) := by
  intro i
  rw [Equiv.swap_apply_def]
  split_ifs with h1 h2
  · subst h1; exact h.symm
  · subst h2; exact h
  · exact Iff.rfl

theorem permAct_dpair_of_pres {σ : Equiv.Perm (Fin n)} (hσ : Pres σ) :
    permAct n σ (dpair n) = dpair n := by
  apply Multiplicative.toAdd.injective
  funext i
  rw [permAct_apply, toAdd_dpair, toAdd_dpair]
  have h : (σ (σ⁻¹ i)).val < 2 ↔ (σ⁻¹ i).val < 2 := hσ (σ⁻¹ i)
  have h' : i = σ (σ⁻¹ i) := by simp
  rw [← h'] at h
  exact if_congr h.symm rfl rfl

theorem swap_mul_swap_mem {a b c d : Fin n} (hab : a ≠ b) (hcd : c ≠ d) :
    Equiv.swap a b * Equiv.swap c d ∈ alternatingGroup (Fin n) := by
  rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hab,
    Equiv.Perm.sign_swap hcd]
  decide

theorem coord_fixed (hn : 5 ≤ n) (x : Fin n → ZMod 2)
    (h : ∀ σ : Equiv.Perm (Fin n), σ ∈ alternatingGroup (Fin n) → Pres σ →
        ∃ b : ZMod 2, ∀ i, x (σ⁻¹ i) - x i = b) :
    ∃ a b : ZMod 2, ∀ i : Fin n, x i = if i.val < 2 then a else b := by
  have hfix : ∀ σ : Equiv.Perm (Fin n), σ ∈ alternatingGroup (Fin n) → Pres σ →
      ∀ j, σ j = j → ∀ i, x (σ⁻¹ i) = x i := by
    intro σ hσ hp j hj i
    obtain ⟨b, hb⟩ := h σ hσ hp
    have hj' : σ⁻¹ j = j := by
      rw [Equiv.Perm.inv_eq_iff_eq]
      exact hj.symm
    have h1 := hb j
    rw [hj', sub_self] at h1
    have h2 := hb i
    rw [← h1] at h2
    exact sub_eq_zero.1 h2
  obtain ⟨i0, hi0⟩ : ∃ i : Fin n, i.val = 0 := ⟨⟨0, by omega⟩, rfl⟩
  obtain ⟨i1, hi1⟩ : ∃ i : Fin n, i.val = 1 := ⟨⟨1, by omega⟩, rfl⟩
  obtain ⟨i2, hi2⟩ : ∃ i : Fin n, i.val = 2 := ⟨⟨2, by omega⟩, rfl⟩
  obtain ⟨i3, hi3⟩ : ∃ i : Fin n, i.val = 3 := ⟨⟨3, by omega⟩, rfl⟩
  obtain ⟨i4, hi4⟩ : ∃ i : Fin n, i.val = 4 := ⟨⟨4, by omega⟩, rfl⟩
  have hne : ∀ i j : Fin n, i.val ≠ j.val → i ≠ j := fun i j h h' => h (congrArg Fin.val h')
  have hC : ∀ i : Fin n, 3 ≤ i.val → x i = x i2 := by
    intro i hi
    obtain ⟨c, hc3, hci⟩ : ∃ c : Fin n, 3 ≤ c.val ∧ c ≠ i := by
      by_cases hi3 : i.val = 3
      · exact ⟨i4, by omega, hne _ _ (by omega)⟩
      · exact ⟨i3, by omega, hne _ _ (by omega)⟩
    have h2i : i2 ≠ i := hne _ _ (by omega)
    have h2c : i2 ≠ c := hne _ _ (by omega)
    have h0i : i0 ≠ i := hne _ _ (by omega)
    have h0c : i0 ≠ c := hne _ _ (by omega)
    have h02 : i0 ≠ i2 := hne _ _ (by omega)
    have hσ : Equiv.swap i2 i * Equiv.swap i c ∈ alternatingGroup (Fin n) :=
      swap_mul_swap_mem h2i hci.symm
    have hp : Pres (Equiv.swap i2 i * Equiv.swap i c) :=
      (pres_swap _ _ (by omega)).mul (pres_swap _ _ (by omega))
    have hfix0 : (Equiv.swap i2 i * Equiv.swap i c) i0 = i0 := by
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne h0i h0c,
        Equiv.swap_apply_of_ne_of_ne h02 h0i]
    have hmap : (Equiv.swap i2 i * Equiv.swap i c) i2 = i := by
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne h2i h2c, Equiv.swap_apply_left]
    have := hfix _ hσ hp i0 hfix0 i
    rw [Equiv.Perm.inv_eq_iff_eq.2 hmap.symm] at this
    exact this.symm
  have hD : x i0 = x i1 := by
    have h23 : i2 ≠ i3 := hne _ _ (by omega)
    have h01 : i0 ≠ i1 := hne _ _ (by omega)
    have h02 : i0 ≠ i2 := hne _ _ (by omega)
    have h03 : i0 ≠ i3 := hne _ _ (by omega)
    have h42 : i4 ≠ i2 := hne _ _ (by omega)
    have h43 : i4 ≠ i3 := hne _ _ (by omega)
    have h40 : i4 ≠ i0 := hne _ _ (by omega)
    have h41 : i4 ≠ i1 := hne _ _ (by omega)
    have hσ : Equiv.swap i0 i1 * Equiv.swap i2 i3 ∈ alternatingGroup (Fin n) :=
      swap_mul_swap_mem h01 h23
    have hp : Pres (Equiv.swap i0 i1 * Equiv.swap i2 i3) :=
      (pres_swap _ _ (by omega)).mul (pres_swap _ _ (by omega))
    have h4 : (Equiv.swap i0 i1 * Equiv.swap i2 i3) i4 = i4 := by
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne h42 h43,
        Equiv.swap_apply_of_ne_of_ne h40 h41]
    have hmap : (Equiv.swap i0 i1 * Equiv.swap i2 i3) i0 = i1 := by
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne h02 h03, Equiv.swap_apply_left]
    have := hfix _ hσ hp i4 h4 i1
    rw [Equiv.Perm.inv_eq_iff_eq.2 hmap.symm] at this
    exact this
  refine ⟨x i0, x i2, fun i => ?_⟩
  by_cases hi : i.val < 2
  · simp only [hi, ite_true]
    rcases (by omega : i.val = 0 ∨ i.val = 1) with h | h
    · rw [show i = i0 from Fin.ext (by omega)]
    · rw [show i = i1 from Fin.ext (by omega), ← hD]
  · simp only [hi, ite_false]
    rcases (by omega : i.val = 2 ∨ 3 ≤ i.val) with h | h
    · rw [show i = i2 from Fin.ext (by omega)]
    · exact hC i h


theorem fixed_dn (hn : 5 ≤ n) (m : PermMod n) (hm : m ∈ coreMod n)
    (hS : ∀ γ : ↥(alternatingGroup (Fin n)),
      permAct n (γ : Equiv.Perm (Fin n)) (dpair n) = dpair n →
        permAct n (γ : Equiv.Perm (Fin n)) m * m⁻¹ ∈ kerSub n) :
    m ∈ kerSub n ∨ m * (dpair n)⁻¹ ∈ kerSub n := by
  obtain ⟨a, b, hab⟩ := coord_fixed hn (Multiplicative.toAdd m) (fun σ hσ hp => by
    have h1 := hS ⟨σ, hσ⟩ (permAct_dpair_of_pres hp)
    rw [mem_kerSub_iff] at h1
    obtain ⟨-, b, hb⟩ := h1
    exact ⟨b, fun i => by rw [← toAdd_permAct_mul_inv]; exact hb i⟩)
  have hcases : ∀ a b : ZMod 2, a = b ∨ a - 1 = b := by decide
  rcases hcases a b with h | h
  · left
    rw [mem_kerSub_iff]
    refine ⟨hm, b, fun i => ?_⟩
    rw [hab i]
    split_ifs <;> simp [h]
  · right
    rw [mem_kerSub_iff]
    refine ⟨Subgroup.mul_mem _ hm (Subgroup.inv_mem _ (dpair_mem_coreMod (by omega))), b,
      fun i => ?_⟩
    have h1 : Multiplicative.toAdd (m * (dpair n)⁻¹) i =
        Multiplicative.toAdd m i - Multiplicative.toAdd (dpair n) i := by
      rw [toAdd_mul, toAdd_inv, Pi.add_apply, Pi.neg_apply, sub_eq_add_neg]
      rfl
    rw [h1, hab i, toAdd_dpair]
    split_ifs <;> simp [h]

theorem exists_move_of_altDn {W : Type*} [CommGroup W] (hn : 5 ≤ n) {H : Subgroup (MulAut W)}
    {Z : Subgroup W} (hR : (FFModel.altDn n).Realizes H ⊤ Z) (hZ : fixV H = Z) {c : MulAut W}
    (hc : ∀ g ∈ H, c * g = g * c) : ∃ v : W, v ∉ Z ∧ c v * v⁻¹ ∈ Z := by
  obtain ⟨π, hπ⟩ := hR
  refine exists_move_of_realizesVia hπ hZ hc
    {γ : ↥(alternatingGroup (Fin n)) | permAct n (γ : Equiv.Perm (Fin n)) (dpair n) = dpair n}
    (m₀ := dpair n) (dpair_mem_coreMod (by omega)) (dpair_not_mem_kerSub hn) ?_ ?_
  · intro γ hγ
    exact hγ
  · intro m hm hS
    exact fixed_dn hn m hm (fun γ hγ => hS γ hγ)

end AltDn

end End1222

end CFSG.Quasithin.H13
