module

public import CFSG.Quasithin.AppendixH.H14.M24InvolutionClasses
public import CFSG.Quasithin.AppendixH.H14.MathieuOuterInvolutions

public section

namespace CFSG.Quasithin.AppendixH.H14

open CFSG.ASVolI CFSG.ASVolI.ChH CFSG.Quasithin.H.Mathieu CFSG.Monster.Code

theorem isConjIn_symm {G : Subgroup S24} {u v : S24} (h : IsConjIn G u v) : IsConjIn G v u := by
  obtain ⟨g, hg, hgv⟩ := h
  exact ⟨g⁻¹, G.inv_mem hg, by rw [← hgv]; group⟩

theorem isConjIn_trans {G : Subgroup S24} {u v w : S24} (h₁ : IsConjIn G u v)
    (h₂ : IsConjIn G v w) : IsConjIn G u w := by
  obtain ⟨g, hg, hguv⟩ := h₁
  obtain ⟨k, hk, hkvw⟩ := h₂
  refine ⟨k * g, G.mul_mem hk hg, ?_⟩
  rw [mul_inv_rev]
  calc k * g * u * (g⁻¹ * k⁻¹) = k * (g * u * g⁻¹) * k⁻¹ := by group
    _ = k * v * k⁻¹ := by rw [hguv]
    _ = w := hkvw

theorem isConjIn_of_two_classes {G : Subgroup S24} {S : Set S24} (P : S24 → Prop)
    (hP : ∀ g ∈ G, ∀ x, P (g * x * g⁻¹) ↔ P x) {ι₁ ι₂ : S24}
    (hcov : ∀ x ∈ S, IsConjIn G ι₁ x ∨ IsConjIn G ι₂ x) {o : S24} (ho : o ∈ S) (hPo : ¬ P o)
    {x x' : S24} (hx : x ∈ S) (hx' : x' ∈ S) (hPx : P x) (hPx' : P x') : IsConjIn G x x' := by
  have hPconj : ∀ {u v : S24}, IsConjIn G u v → (P u ↔ P v) := by
    rintro u v ⟨g, hg, hguv⟩
    have h := hP g hg u
    rw [hguv] at h
    exact h.symm
  rcases hcov x hx with hx1 | hx2
  · rcases hcov x' hx' with hx'1 | hx'2
    · exact isConjIn_trans (isConjIn_symm hx1) hx'1
    · exfalso
      have hP1 : P ι₁ := (hPconj hx1).2 hPx
      have hP2 : P ι₂ := (hPconj hx'2).2 hPx'
      rcases hcov o ho with ho1 | ho2
      · exact hPo ((hPconj ho1).1 hP1)
      · exact hPo ((hPconj ho2).1 hP2)
  · rcases hcov x' hx' with hx'1 | hx'2
    · exfalso
      have hP1 : P ι₁ := (hPconj hx'1).2 hPx'
      have hP2 : P ι₂ := (hPconj hx2).2 hPx
      rcases hcov o ho with ho1 | ho2
      · exact hPo ((hPconj ho1).1 hP1)
      · exact hPo ((hPconj ho2).1 hP2)
    · exact isConjIn_trans (isConjIn_symm hx2) hx'2

theorem exists_m22Involution :
    ∃ σ ∈ mog22, HasArr σ m22InvolutionArr ∧ orderOf σ = 2 := by
  obtain ⟨σ, hσ, hσa⟩ := exists_of_inAutOK inAutOK_m22InvolutionArr
  have hmem : σ ∈ mog22 :=
    mem_mog22_of_arr hσ hσa outer_arrs_swap_zero_one.2.2.2.2.1
      outer_arrs_swap_zero_one.2.2.2.2.2
  refine ⟨σ, hmem, hσa, ?_⟩
  apply orderOf_eq_prime
  · rw [pow_two]
    ext i
    rw [Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
    rw [hσa (σ i), hσa i]
    exact arr_involutive_m22 (i : ℕ) i.isLt
  · intro h
    have hne : (σ ⟨8, by norm_num⟩ : ℕ) ≠ 8 := by
      rw [hσa]
      decide +kernel
    exact hne (by rw [h]; rfl)

theorem exists_outerFptFree :
    ∃ σ ∈ mog22plus, σ ∉ mog22 ∧ HasArr σ outerFptFreeArr ∧ orderOf σ = 2 ∧ ∀ x, σ x ≠ x := by
  obtain ⟨σ, hσ, hσa⟩ := exists_of_inAutOK inAutOK_outerFptFreeArr
  have hσ0 : σ 0 = 1 := hσa.apply_eq 0 outer_arrs_swap_zero_one.1
  have hσ1 : σ 1 = 0 := hσa.apply_eq 1 outer_arrs_swap_zero_one.2.1
  have hmem : σ ∈ mog22plus := ⟨hσ, Or.inr ⟨hσ0, hσ1⟩⟩
  have hnot : σ ∉ mog22 := by
    intro h
    have h0 : σ 0 = 0 := (mem_stab_iff 0 σ).1 h.1.2
    rw [hσ0] at h0
    exact (by decide +kernel : (1 : Fin 24) ≠ 0) h0
  refine ⟨σ, hmem, hnot, hσa, ?_, ?_⟩
  · apply orderOf_eq_prime
    · rw [pow_two]
      ext i
      rw [Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
      rw [hσa (σ i), hσa i]
      exact arr_involutive_outerFptFree (i : ℕ) i.isLt
    · intro h
      have hne : (σ ⟨0, by norm_num⟩ : ℕ) ≠ 0 := by
        rw [hσa]
        decide +kernel
      exact hne (by rw [h]; rfl)
  · intro x hx
    exact not_fixed_outerFptFree x ((hasArr_fix_iff hσa x).1 hx)

theorem exists_outerOctad :
    ∃ σ ∈ mog22plus, σ ∉ mog22 ∧ HasArr σ outerOctadArr ∧ orderOf σ = 2 ∧
      ∃ x, σ x = x := by
  obtain ⟨σ, hσ, hσa⟩ := exists_of_inAutOK inAutOK_outerOctadArr
  have hσ0 : σ 0 = 1 := hσa.apply_eq 0 outer_arrs_swap_zero_one.2.2.1
  have hσ1 : σ 1 = 0 := hσa.apply_eq 1 outer_arrs_swap_zero_one.2.2.2.1
  have hmem : σ ∈ mog22plus := ⟨hσ, Or.inr ⟨hσ0, hσ1⟩⟩
  have hnot : σ ∉ mog22 := by
    intro h
    have h0 : σ 0 = 0 := (mem_stab_iff 0 σ).1 h.1.2
    rw [hσ0] at h0
    exact (by decide +kernel : (1 : Fin 24) ≠ 0) h0
  refine ⟨σ, hmem, hnot, hσa, ?_, ?_⟩
  · apply orderOf_eq_prime
    · rw [pow_two]
      ext i
      rw [Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
      rw [hσa (σ i), hσa i]
      exact arr_involutive_outerOctad (i : ℕ) i.isLt
    · intro h
      have hne : (σ ⟨0, by norm_num⟩ : ℕ) ≠ 0 := by
        rw [hσa]
        decide +kernel
      exact hne (by rw [h]; rfl)
  · refine ⟨2, ?_⟩
    exact (hasArr_fix_iff hσa 2).2 ((fixed_iff_outerOctad 2).2 (by decide +kernel))

section Certs


theorem outer_fptFree_conj_base {i i' : S24} (hi : i ∈ mog22plus) (hi' : i' ∈ mog22plus)
    (hio : i ∉ mog22) (hio' : i' ∉ mog22) (h2 : orderOf i = 2) (h2' : orderOf i' = 2)
    (hf : ∀ x, i x ≠ x) (hf' : ∀ x, i' x ≠ x) : IsConjIn mog22plus i i' := by
  have hfix : ∀ (g x : S24) (y : Fin 24),
      (g * x * g⁻¹) y = y ↔ x (g⁻¹ y) = g⁻¹ y := by
    intro g x y
    constructor
    · intro h
      have := congrArg (fun t => g⁻¹ t) h
      simpa [Equiv.Perm.mul_apply] using this
    · intro h
      rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, h]
      simp
  have hP : ∀ g ∈ mog22plus, ∀ x,
      (∀ y, (g * x * g⁻¹) y ≠ y) ↔ (∀ y, x y ≠ y) := by
    intro g hg x
    constructor
    · intro h y hy
      exact h (g y) (by
        rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
        have hgy : g⁻¹ (g y) = y := Equiv.Perm.inv_eq_iff_eq.2 rfl
        rw [hgy, hy])
    · intro h y hy
      exact h (g⁻¹ y) ((hfix g x y).1 hy)
  obtain ⟨ι₁, ι₂, hcover⟩ := exists_outer_involution_cover_mog22plus
  obtain ⟨o, ho_plus, ho_not, hoa, ho2, ox, hox⟩ := exists_outerOctad
  have hcov : ∀ x ∈ ({x | x ∈ mog22plus ∧ x ∉ mog22 ∧ orderOf x = 2} : Set S24),
      IsConjIn mog22plus ι₁ x ∨ IsConjIn mog22plus ι₂ x := by
    rintro x ⟨hx1, hx2, hx3⟩
    exact hcover x hx1 hx2 hx3
  exact isConjIn_of_two_classes (G := mog22plus)
    (S := {x | x ∈ mog22plus ∧ x ∉ mog22 ∧ orderOf x = 2})
    (fun x => ∀ y, x y ≠ y) hP (ι₁ := ι₁) (ι₂ := ι₂) hcov
    ⟨ho_plus, ho_not, ho2⟩ (fun h => h ox hox) ⟨hi, hio, h2⟩ ⟨hi', hio', h2'⟩ hf hf'

theorem outer_fixing_conj_base {i i' : S24} (hi : i ∈ mog22plus) (hi' : i' ∈ mog22plus)
    (hio : i ∉ mog22) (hio' : i' ∉ mog22) (h2 : orderOf i = 2) (h2' : orderOf i' = 2)
    (hf : ∃ x, i x = x) (hf' : ∃ x, i' x = x) : IsConjIn mog22plus i i' := by
  have hfix : ∀ (g x : S24) (y : Fin 24),
      (g * x * g⁻¹) y = y ↔ x (g⁻¹ y) = g⁻¹ y := by
    intro g x y
    constructor
    · intro h
      have := congrArg (fun t => g⁻¹ t) h
      simpa [Equiv.Perm.mul_apply] using this
    · intro h
      rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, h]
      simp
  have hP : ∀ g ∈ mog22plus, ∀ x,
      (∃ y, (g * x * g⁻¹) y = y) ↔ ∃ y, x y = y := by
    intro g hg x
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨g⁻¹ y, (hfix g x y).1 hy⟩
    · rintro ⟨y, hy⟩
      refine ⟨g y, (hfix g x (g y)).2 ?_⟩
      have hgy : g⁻¹ (g y) = y := Equiv.Perm.inv_eq_iff_eq.2 rfl
      rw [hgy, hy]
  obtain ⟨ι₁, ι₂, hcover⟩ := exists_outer_involution_cover_mog22plus
  obtain ⟨o, ho_plus, ho_not, hoa, ho2, hoff⟩ := exists_outerFptFree
  have hcov : ∀ x ∈ ({x | x ∈ mog22plus ∧ x ∉ mog22 ∧ orderOf x = 2} : Set S24),
      IsConjIn mog22plus ι₁ x ∨ IsConjIn mog22plus ι₂ x := by
    rintro x ⟨hx1, hx2, hx3⟩
    exact hcover x hx1 hx2 hx3
  exact isConjIn_of_two_classes (G := mog22plus)
    (S := {x | x ∈ mog22plus ∧ x ∉ mog22 ∧ orderOf x = 2})
    (fun x => ∃ y, x y = y) hP (ι₁ := ι₁) (ι₂ := ι₂) hcov
    ⟨ho_plus, ho_not, ho2⟩ (fun h => by obtain ⟨y, hy⟩ := h; exact hoff y hy)
    ⟨hi, hio, h2⟩ ⟨hi', hio', h2'⟩ hf hf'

end Certs

variable {a b : Fin 24} {τ : S24}

private theorem mem_stabPair01_iff (σ : S24) :
    σ ∈ stabPair01 ↔ (σ 0 = 0 ∧ σ 1 = 1) ∨ (σ 0 = 1 ∧ σ 1 = 0) := Iff.rfl

theorem mem_M2ab_iff_conj (hab : a ≠ b) (hτ : τ ∈ AutPerm) (h0 : τ 0 = a) (h1 : τ 1 = b)
    (x : S24) : x ∈ M2ab a b ↔ τ⁻¹ * x * τ ∈ mog22plus := by
  have hA : ∀ y : S24, (τ⁻¹ * y * τ) 0 = τ⁻¹ (y a) := by
    intro y; rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, h0]
  have hB : ∀ y : S24, (τ⁻¹ * y * τ) 1 = τ⁻¹ (y b) := by
    intro y; rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, h1]
  have h0a : ∀ y : Fin 24, τ⁻¹ y = 0 ↔ y = a := by
    intro y
    constructor
    · intro hy
      have := congrArg τ hy
      simpa [h0] using this
    · intro hy
      rw [hy, ← h0]; simp
  have h1b : ∀ y : Fin 24, τ⁻¹ y = 1 ↔ y = b := by
    intro y
    constructor
    · intro hy
      have := congrArg τ hy
      simpa [h1] using this
    · intro hy
      rw [hy, ← h1]; simp
  have hp : ((x a = a ∧ x b = b) ∨ (x a = b ∧ x b = a)) ↔
      (((τ⁻¹ * x * τ) 0 = 0 ∧ (τ⁻¹ * x * τ) 1 = 1) ∨
        ((τ⁻¹ * x * τ) 0 = 1 ∧ (τ⁻¹ * x * τ) 1 = 0)) := by
    rw [hA x, hB x]
    simp only [h0a, h1b]
  have hAut : x ∈ AutPerm ↔ τ⁻¹ * x * τ ∈ AutPerm := by
    constructor
    · intro hx
      exact AutPerm.mul_mem (AutPerm.mul_mem (AutPerm.inv_mem hτ) hx) hτ
    · intro hx
      have hx' : x = τ * (τ⁻¹ * x * τ) * τ⁻¹ := by group
      rw [hx']
      exact AutPerm.mul_mem (AutPerm.mul_mem hτ hx) (AutPerm.inv_mem hτ)
  rw [mem_M2ab_iff a b hab x]
  simp only [M24g]
  constructor
  · rintro ⟨hx, hpair⟩
    refine ⟨hAut.1 hx, ?_⟩
    exact (mem_stabPair01_iff _).2 (hp.1 hpair)
  · rintro ⟨hx, hpair⟩
    exact ⟨hAut.2 hx, hp.2 ((mem_stabPair01_iff _).1 hpair)⟩

theorem mem_M22g_iff_conj (hτ : τ ∈ AutPerm) (h0 : τ 0 = a) (h1 : τ 1 = b) (x : S24) :
    x ∈ M22g a b ↔ τ⁻¹ * x * τ ∈ mog22 := by
  have hA : ∀ y : S24, (τ⁻¹ * y * τ) 0 = τ⁻¹ (y a) := by
    intro y; rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, h0]
  have hB : ∀ y : S24, (τ⁻¹ * y * τ) 1 = τ⁻¹ (y b) := by
    intro y; rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, h1]
  have h0a : ∀ y : Fin 24, τ⁻¹ y = 0 ↔ y = a := by
    intro y
    constructor
    · intro hy
      have := congrArg τ hy
      simpa [h0] using this
    · intro hy
      rw [hy, ← h0]; simp
  have h1b : ∀ y : Fin 24, τ⁻¹ y = 1 ↔ y = b := by
    intro y
    constructor
    · intro hy
      have := congrArg τ hy
      simpa [h1] using this
    · intro hy
      rw [hy, ← h1]; simp
  have hp : (x a = a ∧ x b = b) ↔
      ((τ⁻¹ * x * τ) 0 = 0 ∧ (τ⁻¹ * x * τ) 1 = 1) := by
    rw [hA x, hB x]
    simp only [h0a, h1b]
  have hAut : x ∈ AutPerm ↔ τ⁻¹ * x * τ ∈ AutPerm := by
    constructor
    · intro hx
      exact AutPerm.mul_mem (AutPerm.mul_mem (AutPerm.inv_mem hτ) hx) hτ
    · intro hx
      have hx' : x = τ * (τ⁻¹ * x * τ) * τ⁻¹ := by group
      rw [hx']
      exact AutPerm.mul_mem (AutPerm.mul_mem hτ hx) (AutPerm.inv_mem hτ)
  rw [mem_M22g_iff a b x]
  simp only [M24g]
  constructor
  · rintro ⟨hx, ha, hb⟩
    have hpair := hp.1 ⟨ha, hb⟩
    exact ⟨⟨hAut.1 hx, (mem_stab_iff 0 _).2 hpair.1⟩, (mem_stab_iff 1 _).2 hpair.2⟩
  · rintro ⟨⟨hx, h0'⟩, h1'⟩
    exact ⟨hAut.2 hx, hp.2 ⟨(mem_stab_iff 0 _).1 h0', (mem_stab_iff 1 _).1 h1'⟩⟩

theorem conj_apply_eq_self_iff (τ x : S24) (i : Fin 24) :
    (τ⁻¹ * x * τ) i = i ↔ x (τ i) = τ i := by
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
  constructor
  · intro h
    have := congrArg τ h
    simpa using this
  · intro h
    rw [h]; simp

theorem orderOf_conj_inv_mul (τ x : S24) : orderOf (τ⁻¹ * x * τ) = orderOf x := by
  simpa [MulAut.conj_apply, inv_inv] using MulEquiv.orderOf_eq (MulAut.conj τ⁻¹) x

theorem isConjIn_M2ab_of_conj (hab : a ≠ b) (hτ : τ ∈ AutPerm) (h0 : τ 0 = a) (h1 : τ 1 = b)
    {i i' : S24} (h : IsConjIn mog22plus (τ⁻¹ * i * τ) (τ⁻¹ * i' * τ)) :
    IsConjIn (M2ab a b) i i' := by
  obtain ⟨g, hg, hgconj⟩ := h
  refine ⟨τ * g * τ⁻¹, ?_, ?_⟩
  · rw [mem_M2ab_iff_conj hab hτ h0 h1]
    have hgt : τ⁻¹ * (τ * g * τ⁻¹) * τ = g := by group
    rw [hgt]; exact hg
  · calc τ * g * τ⁻¹ * i * (τ * g * τ⁻¹)⁻¹
        = τ * (g * (τ⁻¹ * i * τ) * g⁻¹) * τ⁻¹ := by group
      _ = τ * (τ⁻¹ * i' * τ) * τ⁻¹ := by rw [hgconj]
      _ = i' := by group

theorem swap_of_mem_M2ab_not_mem_M22g (hab : a ≠ b) {i : S24} (hi : i ∈ M2ab a b)
    (hi' : i ∉ M22g a b) : i a = b ∧ i b = a := by
  rw [mem_M2ab_iff a b hab i] at hi
  rcases hi with ⟨hM, hstab | hswap⟩
  · exfalso
    exact hi' (by
      rw [mem_M22g_iff a b i]
      exact ⟨hM, hstab.1, hstab.2⟩)
  · exact hswap

section Certs2


theorem outer_involution_classes (hab : a ≠ b) :
    (∀ i ∈ M2ab a b, i ∉ M22g a b → orderOf i = 2 →
      ((∀ x : Fin 24, i x ≠ x) ∨
        ∃ O : Finset (Fin 24), IsOctad O ∧ ¬ (a ∈ O ∧ b ∈ O) ∧ ∀ x, x ∈ O ↔ i x = x)) ∧
    (∃ i ∈ M2ab a b, i ∉ M22g a b ∧ orderOf i = 2 ∧ ∀ x : Fin 24, i x ≠ x) ∧
    (∃ i ∈ M2ab a b, i ∉ M22g a b ∧ orderOf i = 2 ∧
      ∃ O : Finset (Fin 24), IsOctad O ∧ ¬ (a ∈ O ∧ b ∈ O) ∧ ∀ x, x ∈ O ↔ i x = x) ∧
    (∀ i ∈ M2ab a b, ∀ i' ∈ M2ab a b, i ∉ M22g a b → i' ∉ M22g a b → orderOf i = 2 →
      orderOf i' = 2 → (∀ x : Fin 24, i x ≠ x) → (∀ x : Fin 24, i' x ≠ x) →
        IsConjIn (M2ab a b) i i') ∧
    (∀ i ∈ M2ab a b, ∀ i' ∈ M2ab a b, i ∉ M22g a b → i' ∉ M22g a b → orderOf i = 2 →
      orderOf i' = 2 →
      (∃ O : Finset (Fin 24), IsOctad O ∧ ¬ (a ∈ O ∧ b ∈ O) ∧ ∀ x, x ∈ O ↔ i x = x) →
      (∃ O : Finset (Fin 24), IsOctad O ∧ ¬ (a ∈ O ∧ b ∈ O) ∧ ∀ x, x ∈ O ↔ i' x = x) →
        IsConjIn (M2ab a b) i i') := by
  obtain ⟨τ, hτ, hτ0, hτ1⟩ := CFSG.Monster.B.TwoA.autPerm_maps_two a b hab
  have hpart1 : ∀ i ∈ M2ab a b, i ∉ M22g a b → orderOf i = 2 →
      ((∀ x : Fin 24, i x ≠ x) ∨
        ∃ O : Finset (Fin 24), IsOctad O ∧ ¬ (a ∈ O ∧ b ∈ O) ∧ ∀ x, x ∈ O ↔ i x = x) := by
    intro i hi hi' hi2
    have hswap := swap_of_mem_M2ab_not_mem_M22g hab hi hi'
    have hiM : i ∈ M24g := ((mem_M2ab_iff a b hab i).1 hi).1
    rcases involution_dichotomy hiM hi2 with ⟨-, -, ⟨O, hO, hOfix⟩, -⟩ | ⟨-, -, hff⟩
    · right
      refine ⟨O, hO, ?_, hOfix⟩
      rintro ⟨haO, hbO⟩
      have hia : i a = a := (hOfix a).1 haO
      rw [hswap.1] at hia
      exact hab hia.symm
    · left
      exact hff
  have hpart2 : ∃ i ∈ M2ab a b, i ∉ M22g a b ∧ orderOf i = 2 ∧
      ∀ x : Fin 24, i x ≠ x := by
    obtain ⟨σ, hσp, hσn, hσa, hσ2, hσff⟩ := exists_outerFptFree
    have hiM : τ * σ * τ⁻¹ ∈ M2ab a b := by
      rw [mem_M2ab_iff_conj hab hτ hτ0 hτ1]
      have h : τ⁻¹ * (τ * σ * τ⁻¹) * τ = σ := by group
      rw [h]; exact hσp
    have hin : τ * σ * τ⁻¹ ∉ M22g a b := by
      intro h
      apply hσn
      have h' := (mem_M22g_iff_conj hτ hτ0 hτ1 (τ * σ * τ⁻¹)).1 h
      have heq : τ⁻¹ * (τ * σ * τ⁻¹) * τ = σ := by group
      rwa [heq] at h'
    have hi2 : orderOf (τ * σ * τ⁻¹) = 2 := by
      have h := orderOf_conj_inv_mul (τ⁻¹) σ
      rw [inv_inv] at h
      rw [h, hσ2]
    have hiff : ∀ x : Fin 24, (τ * σ * τ⁻¹) x ≠ x := by
      intro x hx
      apply hσff (τ⁻¹ x)
      have hx' : ((τ⁻¹)⁻¹ * σ * τ⁻¹) x = x := by simpa [inv_inv] using hx
      exact (conj_apply_eq_self_iff (τ⁻¹) σ x).1 hx'
    exact ⟨τ * σ * τ⁻¹, hiM, hin, hi2, hiff⟩
  have hpart3 : ∃ i ∈ M2ab a b, i ∉ M22g a b ∧ orderOf i = 2 ∧
      ∃ O : Finset (Fin 24), IsOctad O ∧ ¬ (a ∈ O ∧ b ∈ O) ∧ ∀ x, x ∈ O ↔ i x = x := by
    obtain ⟨σ, hσp, hσn, hσa, hσ2, hσfix⟩ := exists_outerOctad
    obtain ⟨x0, hx0⟩ := hσfix
    have hiM : τ * σ * τ⁻¹ ∈ M2ab a b := by
      rw [mem_M2ab_iff_conj hab hτ hτ0 hτ1]
      have h : τ⁻¹ * (τ * σ * τ⁻¹) * τ = σ := by group
      rw [h]; exact hσp
    have hin : τ * σ * τ⁻¹ ∉ M22g a b := by
      intro h
      apply hσn
      have h' := (mem_M22g_iff_conj hτ hτ0 hτ1 (τ * σ * τ⁻¹)).1 h
      have heq : τ⁻¹ * (τ * σ * τ⁻¹) * τ = σ := by group
      rwa [heq] at h'
    have hi2 : orderOf (τ * σ * τ⁻¹) = 2 := by
      have h := orderOf_conj_inv_mul (τ⁻¹) σ
      rw [inv_inv] at h
      rw [h, hσ2]
    have hfix : ∃ y : Fin 24, (τ * σ * τ⁻¹) y = y := by
      refine ⟨τ x0, ?_⟩
      rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
      have hxτ : τ⁻¹ (τ x0) = x0 := Equiv.Perm.inv_eq_iff_eq.2 rfl
      rw [hxτ, hx0]
    rcases hpart1 (τ * σ * τ⁻¹) hiM hin hi2 with hff | hoct
    · obtain ⟨y, hy⟩ := hfix
      exact absurd hy (hff y)
    · exact ⟨τ * σ * τ⁻¹, hiM, hin, hi2, hoct⟩
  have hpart4 : ∀ i ∈ M2ab a b, ∀ i' ∈ M2ab a b, i ∉ M22g a b → i' ∉ M22g a b →
      orderOf i = 2 → orderOf i' = 2 → (∀ x : Fin 24, i x ≠ x) →
      (∀ x : Fin 24, i' x ≠ x) → IsConjIn (M2ab a b) i i' := by
    intro i hi i' hi' hin hin' hi2 hi2' hif hif'
    have hi_plus : τ⁻¹ * i * τ ∈ mog22plus :=
      (mem_M2ab_iff_conj hab hτ hτ0 hτ1 i).1 hi
    have hi'_plus : τ⁻¹ * i' * τ ∈ mog22plus :=
      (mem_M2ab_iff_conj hab hτ hτ0 hτ1 i').1 hi'
    have hi_n22 : τ⁻¹ * i * τ ∉ mog22 := fun h =>
      hin ((mem_M22g_iff_conj hτ hτ0 hτ1 i).2 h)
    have hi'_n22 : τ⁻¹ * i' * τ ∉ mog22 := fun h =>
      hin' ((mem_M22g_iff_conj hτ hτ0 hτ1 i').2 h)
    have hi2c : orderOf (τ⁻¹ * i * τ) = 2 := by rw [orderOf_conj_inv_mul τ i, hi2]
    have hi2c' : orderOf (τ⁻¹ * i' * τ) = 2 := by rw [orderOf_conj_inv_mul τ i', hi2']
    have hiff : ∀ x : Fin 24, (τ⁻¹ * i * τ) x ≠ x :=
      fun x hx => hif (τ x) ((conj_apply_eq_self_iff τ i x).1 hx)
    have hiff' : ∀ x : Fin 24, (τ⁻¹ * i' * τ) x ≠ x :=
      fun x hx => hif' (τ x) ((conj_apply_eq_self_iff τ i' x).1 hx)
    exact isConjIn_M2ab_of_conj hab hτ hτ0 hτ1
      (outer_fptFree_conj_base hi_plus hi'_plus hi_n22 hi'_n22 hi2c hi2c' hiff hiff')
  have hpart5 : ∀ i ∈ M2ab a b, ∀ i' ∈ M2ab a b, i ∉ M22g a b → i' ∉ M22g a b →
      orderOf i = 2 → orderOf i' = 2 →
      (∃ O : Finset (Fin 24), IsOctad O ∧ ¬ (a ∈ O ∧ b ∈ O) ∧ ∀ x, x ∈ O ↔ i x = x) →
      (∃ O : Finset (Fin 24), IsOctad O ∧ ¬ (a ∈ O ∧ b ∈ O) ∧ ∀ x, x ∈ O ↔ i' x = x) →
        IsConjIn (M2ab a b) i i' := by
    intro i hi i' hi' hin hin' hi2 hi2' hOi hOi'
    have hi_plus : τ⁻¹ * i * τ ∈ mog22plus :=
      (mem_M2ab_iff_conj hab hτ hτ0 hτ1 i).1 hi
    have hi'_plus : τ⁻¹ * i' * τ ∈ mog22plus :=
      (mem_M2ab_iff_conj hab hτ hτ0 hτ1 i').1 hi'
    have hi_n22 : τ⁻¹ * i * τ ∉ mog22 := fun h =>
      hin ((mem_M22g_iff_conj hτ hτ0 hτ1 i).2 h)
    have hi'_n22 : τ⁻¹ * i' * τ ∉ mog22 := fun h =>
      hin' ((mem_M22g_iff_conj hτ hτ0 hτ1 i').2 h)
    have hi2c : orderOf (τ⁻¹ * i * τ) = 2 := by rw [orderOf_conj_inv_mul τ i, hi2]
    have hi2c' : orderOf (τ⁻¹ * i' * τ) = 2 := by rw [orderOf_conj_inv_mul τ i', hi2']
    have hfix : ∃ y : Fin 24, (τ⁻¹ * i * τ) y = y := by
      obtain ⟨O, hO, -, hOfix⟩ := hOi
      have hcard : 0 < O.card := by rw [hO.1]; norm_num
      obtain ⟨x, hxO⟩ := Finset.card_pos.1 hcard
      refine ⟨τ⁻¹ x, ?_⟩
      rw [conj_apply_eq_self_iff τ i (τ⁻¹ x)]
      have hxτ : τ (τ⁻¹ x) = x := Equiv.apply_symm_apply τ x
      rw [hxτ]
      exact (hOfix x).1 hxO
    have hfix' : ∃ y : Fin 24, (τ⁻¹ * i' * τ) y = y := by
      obtain ⟨O, hO, -, hOfix⟩ := hOi'
      have hcard : 0 < O.card := by rw [hO.1]; norm_num
      obtain ⟨x, hxO⟩ := Finset.card_pos.1 hcard
      refine ⟨τ⁻¹ x, ?_⟩
      rw [conj_apply_eq_self_iff τ i' (τ⁻¹ x)]
      have hxτ : τ (τ⁻¹ x) = x := Equiv.apply_symm_apply τ x
      rw [hxτ]
      exact (hOfix x).1 hxO
    exact isConjIn_M2ab_of_conj hab hτ hτ0 hτ1
      (outer_fixing_conj_base hi_plus hi'_plus hi_n22 hi'_n22 hi2c hi2c' hfix hfix')
  exact ⟨hpart1, hpart2, hpart3, hpart4, hpart5⟩

end Certs2

end CFSG.Quasithin.AppendixH.H14
