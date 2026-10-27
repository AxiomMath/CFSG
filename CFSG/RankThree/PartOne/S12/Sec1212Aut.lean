module

public import CFSG.RankThree.PartOne.S12.InputsTable

public section

namespace CFSG.RankThree.PartOne

namespace Sec1212Aut

theorem perm_eq_one_of_card_lt {α : Type*} [Fintype α] [DecidableEq α] {p : ℕ} (hp : p.Prime)
    (σ : Equiv.Perm α) (hσ : σ ^ p = 1) (hα : Fintype.card α < p) : σ = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have h := Equiv.Perm.card_compl_support_modEq (p := p) (n := 1) (σ := σ) (by simpa using hσ)
  have hle : σ.supportᶜ.card ≤ Fintype.card α := Finset.card_le_univ _
  have heq : σ.supportᶜ.card = Fintype.card α :=
    Nat.ModEq.eq_of_lt_of_lt h (lt_of_le_of_lt hle hα) hα
  have huniv : σ.supportᶜ = Finset.univ := Finset.eq_univ_of_card _ heq
  have hsupp : σ.support = ∅ := by
    rw [← Finset.compl_univ, ← huniv, compl_compl]
  exact Equiv.Perm.support_eq_empty_iff.1 hsupp

theorem mulAut_eq_one_of_charSet {W : Type*} [Group W] [Finite W] {p : ℕ} (hp : p.Prime)
    (Q : W → Prop) (hQ : ∀ (σ : MulAut W) (x : W), Q x → Q (σ x))
    (hcard : Nat.card {x : W // Q x} < p)
    (hcl : ∀ g : W, (∀ a, Q a → g * a = a * g) → g ∈ Subgroup.closure {x | Q x})
    (N : ℕ) (hN : Nat.Coprime p N)
    (hexp : ∀ g : W, (∀ a, Q a → g * a = a * g) → g ^ N = 1)
    (σ : MulAut W) (hσ : σ ^ p = 1) : σ = 1 := by
  classical
  have hQiff : ∀ x, Q (σ x) ↔ Q x := fun x =>
    ⟨fun h => by simpa using hQ σ⁻¹ _ h, hQ σ x⟩
  have hfixQ : ∀ x, Q x → σ x = x := by
    have : Fintype {x : W // Q x} := Fintype.ofFinite _
    let τ : Equiv.Perm {x : W // Q x} := (MulAut.toPerm W σ).subtypePerm hQiff
    have hτ : τ ^ p = 1 := by
      have : τ ^ p = ((MulAut.toPerm W σ) ^ p).subtypePerm _ :=
        Equiv.Perm.subtypePerm_pow _ _ _
      rw [this]
      ext x
      simp [← map_pow, hσ]
    have hτ1 : τ = 1 :=
      perm_eq_one_of_card_lt hp τ hτ (by simpa [Nat.card_eq_fintype_card] using hcard)
    intro x hx
    have h1 : τ ⟨x, hx⟩ = ⟨x, hx⟩ := by rw [hτ1]; rfl
    exact congrArg Subtype.val h1
  have hfixcl : ∀ g ∈ Subgroup.closure {x | Q x}, σ g = g := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx => exact hfixQ x hx
    | one => exact map_one σ
    | mul x y _ _ hx hy => rw [map_mul, hx, hy]
    | inv x _ hx => rw [map_inv, hx]
  ext g
  have hcentr : ∀ a, Q a → (g⁻¹ * σ g) * a = a * (g⁻¹ * σ g) := by
    intro a ha
    have hconj : Q (g * a * g⁻¹) := by
      simpa using hQ (MulAut.conj g) a ha
    have h1 : σ (g * a * g⁻¹) = g * a * g⁻¹ := hfixQ _ hconj
    rw [map_mul, map_mul, hfixQ a ha, map_inv] at h1
    calc g⁻¹ * σ g * a = g⁻¹ * (σ g * a * (σ g)⁻¹) * σ g := by group
      _ = g⁻¹ * (g * a * g⁻¹) * σ g := by rw [h1]
      _ = a * (g⁻¹ * σ g) := by group
  have hu : g⁻¹ * σ g ∈ Subgroup.closure {x | Q x} := hcl _ hcentr
  have hiter : ∀ k : ℕ, (σ ^ k) g = g * (g⁻¹ * σ g) ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hfixcl _ hu, pow_succ' _ k,
        ← mul_assoc, mul_inv_cancel_left]
  have hpow : (g⁻¹ * σ g) ^ p = 1 := by
    have h1 := hiter p
    rw [hσ, MulAut.one_apply] at h1
    have h2 : g * (g⁻¹ * σ g) ^ p = g * 1 := by rw [← h1, mul_one]
    exact mul_left_cancel h2
  have hN1 : (g⁻¹ * σ g) ^ N = 1 := hexp _ hcentr
  have hord : orderOf (g⁻¹ * σ g) ∣ Nat.gcd p N :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hpow) (orderOf_dvd_of_pow_eq_one hN1)
  rw [Nat.Coprime.gcd_eq_one hN] at hord
  have h1 : g⁻¹ * σ g = 1 := orderOf_eq_one_iff.1 (Nat.dvd_one.1 hord)
  have : σ g = g := by
    have := congrArg (g * ·) h1
    simpa using this
  simpa using this

theorem coprime_of_five_le {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) {N : ℕ}
    (hN : N = 1 ∨ N = 2 ∨ N = 4 ∨ N = 6 ∨ N = 8) : Nat.Coprime p N := by
  rw [Nat.Prime.coprime_iff_not_dvd hp]
  intro hd
  have hle : p ≤ N := Nat.le_of_dvd (by omega) hd
  have hp8 : p ≤ 8 := by omega
  interval_cases p <;> first | omega | exact absurd hp (by norm_num)

theorem map_pow_eq_one_iff {W : Type*} [Group W] (σ : MulAut W) (x : W) (n : ℕ) :
    (σ x) ^ n = 1 ↔ x ^ n = 1 := by
  rw [← map_pow]
  exact map_eq_one_iff σ σ.injective

@[expose] def QS3 (x : Equiv.Perm (Fin 3)) : Prop := x ≠ 1 ∧ x * x = 1

instance : DecidablePred QS3 := fun x => by unfold QS3; infer_instance

theorem card_QS3 : Nat.card {x : Equiv.Perm (Fin 3) // QS3 x} = 3 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide

theorem centr_QS3 : ∀ g : Equiv.Perm (Fin 3), (∀ a, QS3 a → g * a = a * g) → g = 1 := by
  decide

theorem mulAut_perm_three {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (σ : MulAut (Equiv.Perm (Fin 3))) (hσ : σ ^ p = 1) : σ = 1 := by
  refine mulAut_eq_one_of_charSet hp QS3 ?_ (by rw [card_QS3]; omega) ?_ 1
    (coprime_of_five_le hp h5 (Or.inl rfl)) ?_ σ hσ
  · rintro σ x ⟨h1, h2⟩
    exact ⟨fun h => h1 ((map_eq_one_iff σ σ.injective).1 h), by rw [← map_mul, h2, map_one]⟩
  · intro g hg
    rw [centr_QS3 g hg]
    exact Subgroup.one_mem _
  · intro g hg
    rw [centr_QS3 g hg, pow_one]

theorem r_mem_closure {n : ℕ} [NeZero n] {S : Set (DihedralGroup n)}
    (h : DihedralGroup.r 1 ∈ S) (i : ZMod n) : DihedralGroup.r i ∈ Subgroup.closure S := by
  have : (DihedralGroup.r i : DihedralGroup n) = DihedralGroup.r 1 ^ i.val := by
    rw [DihedralGroup.r_one_pow, ZMod.natCast_zmod_val]
  rw [this]
  exact Subgroup.pow_mem _ (Subgroup.subset_closure h) _

@[expose] def QD6 (x : DihedralGroup 6) : Prop := x ^ 6 = 1 ∧ x ^ 3 ≠ 1 ∧ x ^ 2 ≠ 1

instance : DecidablePred QD6 := fun x => by unfold QD6; infer_instance

theorem card_QD6 : Nat.card {x : DihedralGroup 6 // QD6 x} = 2 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide

theorem centr_QD6 : ∀ g : DihedralGroup 6, (∀ a, QD6 a → g * a = a * g) →
    (∃ i : ZMod 6, g = DihedralGroup.r i) ∧ g ^ 6 = 1 := by
  decide

theorem mulAut_dihedral_six {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (σ : MulAut (DihedralGroup 6)) (hσ : σ ^ p = 1) : σ = 1 := by
  refine mulAut_eq_one_of_charSet hp QD6 ?_ (by rw [card_QD6]; omega) ?_ 6
    (coprime_of_five_le hp h5 (by omega)) ?_ σ hσ
  · rintro σ x ⟨h1, h2, h3⟩
    exact ⟨(map_pow_eq_one_iff σ x 6).2 h1, fun h => h2 ((map_pow_eq_one_iff σ x 3).1 h),
      fun h => h3 ((map_pow_eq_one_iff σ x 2).1 h)⟩
  · intro g hg
    obtain ⟨⟨i, rfl⟩, -⟩ := centr_QD6 g hg
    exact r_mem_closure (by decide : QD6 (DihedralGroup.r 1)) i
  · intro g hg
    exact (centr_QD6 g hg).2

@[expose] def QD8 (x : DihedralGroup 8) : Prop := x ^ 8 = 1 ∧ x ^ 4 ≠ 1

instance : DecidablePred QD8 := fun x => by unfold QD8; infer_instance

theorem card_QD8 : Nat.card {x : DihedralGroup 8 // QD8 x} = 4 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide

theorem centr_QD8 : ∀ g : DihedralGroup 8, (∀ a, QD8 a → g * a = a * g) →
    (∃ i : ZMod 8, g = DihedralGroup.r i) ∧ g ^ 8 = 1 := by
  decide

theorem mulAut_dihedral_eight {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (σ : MulAut (DihedralGroup 8)) (hσ : σ ^ p = 1) : σ = 1 := by
  refine mulAut_eq_one_of_charSet hp QD8 ?_ (by rw [card_QD8]; omega) ?_ 8
    (coprime_of_five_le hp h5 (by omega)) ?_ σ hσ
  · rintro σ x ⟨h1, h2⟩
    exact ⟨(map_pow_eq_one_iff σ x 8).2 h1, fun h => h2 ((map_pow_eq_one_iff σ x 4).1 h)⟩
  · intro g hg
    obtain ⟨⟨i, rfl⟩, -⟩ := centr_QD8 g hg
    exact r_mem_closure (by decide : QD8 (DihedralGroup.r 1)) i
  · intro g hg
    exact (centr_QD8 g hg).2

@[expose] def QD4 (x : DihedralGroup 4) : Prop := x ^ 4 = 1 ∧ x ^ 2 ≠ 1

instance : DecidablePred QD4 := fun x => by unfold QD4; infer_instance

theorem card_QD4 : Nat.card {x : DihedralGroup 4 // QD4 x} = 2 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide

theorem centr_QD4 : ∀ g : DihedralGroup 4, (∀ a, QD4 a → g * a = a * g) →
    (∃ i : ZMod 4, g = DihedralGroup.r i) ∧ g ^ 4 = 1 := by
  decide

theorem mulAut_dihedral_four {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (σ : MulAut (DihedralGroup 4)) (hσ : σ ^ p = 1) : σ = 1 := by
  refine mulAut_eq_one_of_charSet hp QD4 ?_ (by rw [card_QD4]; omega) ?_ 4
    (coprime_of_five_le hp h5 (by omega)) ?_ σ hσ
  · rintro σ x ⟨h1, h2⟩
    exact ⟨(map_pow_eq_one_iff σ x 4).2 h1, fun h => h2 ((map_pow_eq_one_iff σ x 2).1 h)⟩
  · intro g hg
    obtain ⟨⟨i, rfl⟩, -⟩ := centr_QD4 g hg
    exact r_mem_closure (by decide : QD4 (DihedralGroup.r 1)) i
  · intro g hg
    exact (centr_QD4 g hg).2

@[expose] def QS4 (x : Equiv.Perm (Fin 4)) : Prop := x ≠ 1 ∧ x * x = 1 ∧ ∃ y, y * y = x

instance : DecidablePred QS4 := fun x => by unfold QS4; infer_instance

theorem card_QS4 : Nat.card {x : Equiv.Perm (Fin 4) // QS4 x} = 3 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide

theorem centr_QS4 : ∀ g : Equiv.Perm (Fin 4), (∀ a, QS4 a → g * a = a * g) →
    (g = 1 ∨ QS4 g) ∧ g ^ 2 = 1 := by
  decide

theorem mulAut_perm_four {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (σ : MulAut (Equiv.Perm (Fin 4))) (hσ : σ ^ p = 1) : σ = 1 := by
  refine mulAut_eq_one_of_charSet hp QS4 ?_ (by rw [card_QS4]; omega) ?_ 2
    (coprime_of_five_le hp h5 (by omega)) ?_ σ hσ
  · rintro σ x ⟨h1, h2, y, hy⟩
    exact ⟨fun h => h1 ((map_eq_one_iff σ σ.injective).1 h), by rw [← map_mul, h2, map_one],
      σ y, by rw [← map_mul, hy]⟩
  · intro g hg
    rcases (centr_QS4 g hg).1 with rfl | hQ
    · exact Subgroup.one_mem _
    · exact Subgroup.subset_closure hQ
  · intro g hg
    exact (centr_QS4 g hg).2

abbrev W10 := Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)

@[expose] def zW : W10 := (Multiplicative.ofAdd 1, 1)

@[expose] def QW10 (x : W10) : Prop :=
  (x ≠ 1 ∧ x * x = 1 ∧ ∃ y, y * y = x) ∨ (x ≠ 1 ∧ ∀ y, x * y = y * x)

instance : DecidablePred QW10 := fun x => by unfold QW10; infer_instance

theorem card_QW10 : Nat.card {x : W10 // QW10 x} = 4 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide

theorem centr_QW10 : ∀ g : W10, (∀ a, QW10 a → g * a = a * g) →
    (g = 1 ∨ QW10 g ∨ ∃ t, QW10 t ∧ g = zW * t) ∧ g ^ 2 = 1 := by
  decide +kernel

theorem mulAut_z2_perm_four {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (σ : MulAut W10)
    (hσ : σ ^ p = 1) : σ = 1 := by
  refine mulAut_eq_one_of_charSet hp QW10 ?_ (by rw [card_QW10]; omega) ?_ 2
    (coprime_of_five_le hp h5 (by omega)) ?_ σ hσ
  · rintro σ x (⟨h1, h2, y, hy⟩ | ⟨h1, h2⟩)
    · exact Or.inl ⟨fun h => h1 ((map_eq_one_iff σ σ.injective).1 h),
        by rw [← map_mul, h2, map_one], σ y, by rw [← map_mul, hy]⟩
    · refine Or.inr ⟨fun h => h1 ((map_eq_one_iff σ σ.injective).1 h), fun y => ?_⟩
      obtain ⟨y', rfl⟩ := σ.surjective y
      rw [← map_mul, ← map_mul, h2]
  · intro g hg
    rcases (centr_QW10 g hg).1 with rfl | hQ | ⟨t, ht, rfl⟩
    · exact Subgroup.one_mem _
    · exact Subgroup.subset_closure hQ
    · exact Subgroup.mul_mem _ (Subgroup.subset_closure (by decide : QW10 zW))
        (Subgroup.subset_closure ht)
  · intro g hg
    exact (centr_QW10 g hg).2

theorem mulAut_eq_one_of_mulEquiv {Γ W : Type*} [Group Γ] [Group W] (e : Γ ≃* W)
    {p : ℕ} (h : ∀ τ : MulAut W, τ ^ p = 1 → τ = 1) (σ : MulAut Γ) (hσ : σ ^ p = 1) :
    σ = 1 := by
  have h1 : (MulAut.congr e σ) ^ p = 1 := by rw [← map_pow, hσ, map_one]
  exact (map_eq_one_iff (MulAut.congr e) (MulAut.congr e).injective).1 (h _ h1)

end Sec1212Aut

section Row

variable {G : Type} [Group G] {X : Subgroup G} {Γ : Subgroup (MulAut X)} {r : ℕ}

theorem rowWeylIso_mulAut_pow_eq_one (hr1 : 1 ≤ r) (hr10 : r ≤ 10) (hr : RowWeylIso X Γ r)
    {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (σ : MulAut ↥Γ) (hσ : σ ^ p = 1) : σ = 1 := by
  interval_cases r
  · obtain ⟨e⟩ := hr
    exact Sec1212Aut.mulAut_eq_one_of_mulEquiv e
      (fun τ hτ => Sec1212Aut.mulAut_perm_three hp h5 τ hτ) σ hσ
  · obtain ⟨e⟩ := hr
    exact Sec1212Aut.mulAut_eq_one_of_mulEquiv e
      (fun τ hτ => Sec1212Aut.mulAut_dihedral_six hp h5 τ hτ) σ hσ
  · obtain ⟨e⟩ := hr
    exact Sec1212Aut.mulAut_eq_one_of_mulEquiv e
      (fun τ hτ => Sec1212Aut.mulAut_dihedral_six hp h5 τ hτ) σ hσ
  · obtain ⟨e⟩ := hr
    exact Sec1212Aut.mulAut_eq_one_of_mulEquiv e
      (fun τ hτ => Sec1212Aut.mulAut_dihedral_eight hp h5 τ hτ) σ hσ
  · obtain ⟨e⟩ := hr
    exact Sec1212Aut.mulAut_eq_one_of_mulEquiv e
      (fun τ hτ => Sec1212Aut.mulAut_dihedral_four hp h5 τ hτ) σ hσ
  · obtain ⟨e⟩ := hr
    exact Sec1212Aut.mulAut_eq_one_of_mulEquiv e
      (fun τ hτ => Sec1212Aut.mulAut_dihedral_four hp h5 τ hτ) σ hσ
  · obtain ⟨e⟩ := hr
    exact Sec1212Aut.mulAut_eq_one_of_mulEquiv e
      (fun τ hτ => Sec1212Aut.mulAut_dihedral_four hp h5 τ hτ) σ hσ
  · obtain ⟨e⟩ := hr
    exact Sec1212Aut.mulAut_eq_one_of_mulEquiv e
      (fun τ hτ => Sec1212Aut.mulAut_dihedral_four hp h5 τ hτ) σ hσ
  · obtain ⟨e⟩ := hr
    exact Sec1212Aut.mulAut_eq_one_of_mulEquiv e
      (fun τ hτ => Sec1212Aut.mulAut_perm_four hp h5 τ hτ) σ hσ
  · obtain ⟨e⟩ := hr
    exact Sec1212Aut.mulAut_eq_one_of_mulEquiv e
      (fun τ hτ => Sec1212Aut.mulAut_z2_perm_four hp h5 τ hτ) σ hσ

end Row

end CFSG.RankThree.PartOne
