module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupA10Perm
import all CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupA10Perm
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallS10V
public import CFSG.Permutation.AlternatingAutomorphism.ThreeCycle

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6.A10N588

open Equiv Equiv.Perm Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Perm

@[expose] def altA (T : Finset (Fin 10)) : Subgroup A10 := (alternatingGroup.ofSubtype T).range

theorem mem_altA {T : Finset (Fin 10)} {x : A10} :
    x ∈ altA T ↔ (x : Perm (Fin 10)).support ⊆ T :=
  alternatingGroup.mem_range_ofSubtype_iff T x

noncomputable def altAEquiv (T : Finset (Fin 10)) : alternatingGroup ↥T ≃* altA T :=
  MonoidHom.ofInjective alternatingGroup.ofSubtype_injective

theorem isSimpleGroup_altA (T : Finset (Fin 10)) (hT : 5 ≤ T.card) : IsSimpleGroup (altA T) := by
  have : IsSimpleGroup (alternatingGroup ↥T) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_coe]; exact hT)
  exact (altAEquiv T).symm.isSimpleGroup

theorem card_altA (T : Finset (Fin 10)) (hT : 2 ≤ T.card) :
    Nat.card (altA T) = (T.card).factorial / 2 := by
  have : Nontrivial ↥T := Fintype.one_lt_card_iff_nontrivial.mp (by rw [Fintype.card_coe]; omega)
  rw [← Nat.card_congr (altAEquiv T).toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
    Fintype.card_coe]

theorem commute_of_disjoint_support {x y : A10}
    (h : Disjoint (x : Perm (Fin 10)).support (y : Perm (Fin 10)).support) : x * y = y * x := by
  apply Subtype.ext
  exact ((Equiv.Perm.disjoint_iff_disjoint_support.2 h).commute).eq

theorem commute_altA {T T' : Finset (Fin 10)} (hTT : Disjoint T T') {x y : A10}
    (hx : x ∈ altA T) (hy : y ∈ altA T') : x * y = y * x :=
  commute_of_disjoint_support (Finset.disjoint_of_subset_left (mem_altA.1 hx)
    (Finset.disjoint_of_subset_right (mem_altA.1 hy) hTT))

theorem altA_inf_eq_bot {T T' : Finset (Fin 10)} (hTT : Disjoint T T') :
    altA T ⊓ altA T' = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hx, hx'⟩
  rw [mem_bot]
  have h1 := mem_altA.1 hx
  have h2 := mem_altA.1 hx'
  have h3 : (x : Perm (Fin 10)).support = ∅ :=
    Finset.subset_empty.1 (fun y hy => (Finset.disjoint_left.1 hTT (h1 hy) (h2 hy)).elim)
  apply Subtype.ext
  exact Equiv.Perm.support_eq_empty_iff.1 h3

@[expose] def T6 : Finset (Fin 10) := {0, 1, 2, 3, 4, 5}

@[expose] def T5 : Finset (Fin 10) := {5, 6, 7, 8, 9}

@[expose] def T4 : Finset (Fin 10) := {6, 7, 8, 9}

@[expose] def t₀ : A10 := mkA c[0, 1, 2]

@[expose] def t₁ : A10 := mkA c[3, 4, 5]

@[expose] def x₃ : A10 := mkA c[6, 7, 8]

@[expose] def v₁ : A10 := mkA (swap 6 7 * swap 8 9)

@[expose] def v₂ : A10 := mkA (swap 6 8 * swap 7 9)

theorem T6_T4 : Disjoint T6 T4 := by decide
theorem T4_le_T5 : T4 ⊆ T5 := by decide
theorem card_T6 : T6.card = 6 := by decide
theorem card_T5 : T5.card = 5 := by decide
theorem card_T4 : T4.card = 4 := by decide

theorem a₁_mem_T6 : a₁ ∈ altA T6 := mem_altA.2 (by decide +kernel)
theorem t₀_mem_T6 : t₀ ∈ altA T6 := mem_altA.2 (by decide +kernel)
theorem t₁_mem_T6 : t₁ ∈ altA T6 := mem_altA.2 (by decide +kernel)
theorem a₂_mem_T5 : a₂ ∈ altA T5 := mem_altA.2 (by decide +kernel)
theorem x₃_mem_T4 : x₃ ∈ altA T4 := mem_altA.2 (by decide +kernel)
theorem v₁_mem_T4 : v₁ ∈ altA T4 := mem_altA.2 (by decide +kernel)
theorem v₂_mem_T4 : v₂ ∈ altA T4 := mem_altA.2 (by decide +kernel)

theorem t₀_pow : t₀ ^ 3 = 1 := by decide +kernel
theorem t₁_pow : t₁ ^ 3 = 1 := by decide +kernel
theorem t₀_ne : t₀ ≠ 1 := by decide +kernel
theorem t₁_ne : t₁ ≠ 1 := by decide +kernel
theorem t₀₁_comm : t₀ * t₁ = t₁ * t₀ := by decide +kernel
theorem t₁_not_pow : ∀ k : Fin 3, t₀ ^ (k : ℕ) ≠ t₁ := by decide +kernel
theorem x₃_pow : x₃ ^ 3 = 1 := by decide +kernel
theorem x₃_ne : x₃ ≠ 1 := by decide +kernel
theorem t₀_a₂ : t₀ * a₂ = a₂ * t₀ := by decide +kernel
theorem v₁_sq : v₁ ^ 2 = 1 := by decide +kernel
theorem v₂_sq : v₂ ^ 2 = 1 := by decide +kernel
theorem v₁_ne : v₁ ≠ 1 := by decide +kernel
theorem v₁₂_comm : v₁ * v₂ = v₂ * v₁ := by decide +kernel
theorem x₃_v₁ : x₃ * v₁ * x₃⁻¹ = v₁ * v₂ := by decide +kernel
theorem x₃_v₂ : x₃ * v₂ * x₃⁻¹ = v₁ := by decide +kernel

theorem order_three_check : (a₁ * (t₀ * a₁ ^ 2 * t₀⁻¹)) ^ 3 = 1 ∧ a₁ * (t₀ * a₁ ^ 2 * t₀⁻¹) ≠ 1 :=
  ⟨by decide +kernel, by decide +kernel⟩

theorem card_altA_T6 : Nat.card (altA T6) = 360 := by
  rw [card_altA T6 (by rw [card_T6]; norm_num), card_T6]
  decide

theorem card_altA_T4 : Nat.card (altA T4) = 12 := by
  rw [card_altA T4 (by rw [card_T4]; norm_num), card_T4]
  decide

theorem pow_twelve_of_mem_T4 {x : A10} (hx : x ∈ altA T4) : x ^ 12 = 1 := by
  have h : (⟨x, hx⟩ : altA T4) ^ Nat.card (altA T4) = 1 := pow_card_eq_one'
  rw [card_altA_T4] at h
  simpa using congrArg Subtype.val h

noncomputable def altA6Equiv : altA T6 ≃* alternatingGroup (Fin 6) :=
  (altAEquiv T6).symm.trans
    (Equiv.altCongrHom (Fintype.equivFinOfCardEq (by rw [Fintype.card_coe, card_T6])))

theorem mem_altA_T6_iff {σ : A10} : (∀ x ∈ altA T4, x * σ = σ * x) ↔ σ ∈ altA T6 := by
  constructor
  · intro h
    let τ : Perm (Fin 10) := swap 0 1 * swap 2 3 * swap 4 5
    have hτ : τ.support = T6 := by decide +kernel
    have hF : 4 ≤ τ.supportᶜ.card := by rw [hτ]; decide
    let L : Subgroup (Perm (Fin 10)) := (altA T4).map (alternatingGroup (Fin 10)).subtype
    have hL : ∀ l, l ∈ L ↔ l ∈ alternatingGroup (Fin 10) ∧ ∀ x ∈ τ.support, l x = x := by
      intro l
      constructor
      · rintro ⟨y, hy, rfl⟩
        refine ⟨y.2, fun x hx => ?_⟩
        rw [hτ] at hx
        by_contra hne
        have h1 := mem_altA.1 hy (Equiv.Perm.mem_support.2 hne)
        exact Finset.disjoint_left.1 T6_T4 hx h1
      · rintro ⟨hl, hfix⟩
        refine ⟨⟨l, hl⟩, mem_altA.2 fun x hx => ?_, rfl⟩
        by_contra hx4
        have hcov : ∀ y : Fin 10, y ∉ T4 → y ∈ T6 := by decide
        have hx6 : x ∈ τ.support := by
          rw [hτ]
          exact hcov x hx4
        exact Equiv.Perm.mem_support.1 hx (hfix x hx6)
    have hfix := CFSG.ComponentClassification.CatFactsSmall.fix_of_commute_alt hF hL
      (σ := (σ : Perm (Fin 10))) (by
        rintro _ ⟨y, hy, rfl⟩
        exact congrArg Subtype.val (h y hy))
    refine mem_altA.2 fun x hx => ?_
    by_contra hx6
    have : x ∉ τ.support := by rw [hτ]; exact hx6
    exact Equiv.Perm.mem_support.1 hx (hfix x this)
  · intro hσ x hx
    exact commute_altA T6_T4.symm hx hσ

theorem cyc_pow_zero : ∀ k : Fin 5, ((c[0, 1, 2, 3, 4] : Perm (Fin 10)) ^ (k : ℕ)) 0 =
    (⟨k, by omega⟩ : Fin 10) := by
  decide +kernel

theorem cyc_pow_twelve : ∀ k : Fin 5,
    ((c[0, 1, 2, 3, 4] : Perm (Fin 10)) ^ (12 * (k : ℕ))) 0 = 0 → k = 0 := by
  decide +kernel

theorem fix_of_commute_a₁ {σ : A10} (hc : σ * a₁ = a₁ * σ) (h12 : σ ^ 12 = 1) :
    ∀ i : Fin 10, (i : ℕ) < 5 → (σ : Perm (Fin 10)) i = i := by
  set c : Perm (Fin 10) := c[0, 1, 2, 3, 4] with hcdef
  have hc' : (σ : Perm (Fin 10)) * c = c * (σ : Perm (Fin 10)) := congrArg Subtype.val hc
  have h12' : (σ : Perm (Fin 10)) ^ 12 = 1 := by simpa using congrArg Subtype.val h12
  have hcomm : Commute (σ : Perm (Fin 10)) c := hc'
  have h0 : ((σ : Perm (Fin 10)) 0 : ℕ) < 5 := by
    have hmem : (0 : Fin 10) ∈ c.support := by rw [hcdef]; decide
    have := CFSG.ComponentClassification.CatFactsSmall.mem_support_of_commute hc'.symm hmem
    revert this
    rw [hcdef]
    generalize (σ : Perm (Fin 10)) 0 = j
    revert j
    decide
  set k : Fin 5 := ⟨((σ : Perm (Fin 10)) 0 : ℕ), h0⟩ with hk
  have hk0 : (c ^ (k : ℕ)) 0 = (σ : Perm (Fin 10)) 0 := by
    rw [hcdef, cyc_pow_zero k]
  set τ : Perm (Fin 10) := (c ^ (k : ℕ))⁻¹ * (σ : Perm (Fin 10)) with hτ
  have hτ0 : τ 0 = 0 := by
    rw [hτ, Perm.mul_apply, ← hk0]
    simp
  have hτc : Commute τ c := ((Commute.refl c).pow_left (k : ℕ)).inv_left.mul_left hcomm
  have hτfix : ∀ i : Fin 10, (i : ℕ) < 5 → τ i = i := by
    intro i hi
    have hi' : (c ^ (i : ℕ)) 0 = i := by
      have := cyc_pow_zero ⟨i, hi⟩
      rw [hcdef, this]
    have h1 : τ ((c ^ (i : ℕ)) 0) = (c ^ (i : ℕ)) (τ 0) := by
      have := congrArg (fun π : Perm (Fin 10) => π 0) (hτc.pow_right (i : ℕ)).eq
      simpa [Perm.mul_apply] using this
    rw [hi', hτ0, hi'] at h1
    exact h1
  have hσ : (σ : Perm (Fin 10)) = c ^ (k : ℕ) * τ := by rw [hτ, mul_inv_cancel_left]
  have hcτ : Commute (c ^ (k : ℕ)) τ := (hτc.pow_right (k : ℕ)).symm
  have h12a : ((c ^ (k : ℕ)) ^ 12 * τ ^ 12) 0 = 0 := by
    rw [← hcτ.mul_pow, ← hσ, h12']
    rfl
  have hτ12 : (τ ^ 12) 0 = 0 := by
    clear h12a hσ
    induction (12 : ℕ) with
    | zero => rfl
    | succ n ih => rw [pow_succ', Perm.mul_apply, ih, hτ0]
  rw [Perm.mul_apply, hτ12, ← pow_mul, mul_comm] at h12a
  have hk00 : k = 0 := cyc_pow_twelve k (by rw [← hcdef]; exact h12a)
  intro i hi
  rw [hσ, hk00]
  simp only [Fin.val_zero, pow_zero, one_mul]
  exact hτfix i hi

@[expose] def T7 : Finset (Fin 10) := {3, 4, 5, 6, 7, 8, 9}

theorem exists_isThreeCycle_disjoint {σ : Perm (Fin 10)} (hσ : σ.IsThreeCycle) :
    ∃ τ : Perm (Fin 10), τ.IsThreeCycle ∧ τ.support ⊆ T7 ∧ Disjoint σ.support τ.support := by
  classical
  have hcard : 3 ≤ (T7 \ σ.support).card := by
    have h1 := Finset.le_card_sdiff σ.support T7
    have h2 : σ.support.card = 3 := hσ.card_support
    have h3 : T7.card = 7 := by decide
    omega
  obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq hcard
  obtain ⟨τ, hτ, hτs⟩ := CFSG.AlternatingAutomorphism.exists_isThreeCycle_support_eq htc
  refine ⟨τ, hτ, ?_, ?_⟩
  · rw [hτs]
    exact hts.trans Finset.sdiff_subset
  · rw [hτs]
    exact Finset.disjoint_of_subset_right hts Finset.disjoint_sdiff

theorem commute_t₀ {τ : Perm (Fin 10)} (hτ : τ.support ⊆ T7) :
    τ * (t₀ : Perm (Fin 10)) = (t₀ : Perm (Fin 10)) * τ := by
  have hd : Disjoint τ.support (t₀ : Perm (Fin 10)).support := by
    have h1 : (t₀ : Perm (Fin 10)).support = {0, 1, 2} := by decide +kernel
    rw [h1]
    exact Finset.disjoint_of_subset_left hτ (by decide)
  exact ((Equiv.Perm.disjoint_iff_disjoint_support.2 hd).commute).eq

theorem eq_top_of_threeCycles {T : Subgroup A10}
    (hT : ∀ σ : A10, (σ : Perm (Fin 10)).IsThreeCycle → σ ∈ T) : T = ⊤ := by
  have hle : alternatingGroup (Fin 10) ≤ T.map (alternatingGroup (Fin 10)).subtype := by
    have h := Equiv.Perm.closure_three_cycles_eq_alternating (α := Fin 10)
    refine le_trans h.symm.le ?_
    rw [Subgroup.closure_le]
    intro σ hσ
    exact ⟨⟨σ, hσ.mem_alternatingGroup⟩, hT _ hσ, rfl⟩
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, hy, hyx⟩ := hle x.2
  have : y = x := Subtype.ext hyx
  exact this ▸ hy

end CFSG.LocalAnalysis.UniquenessCase.UC6.A10N588
