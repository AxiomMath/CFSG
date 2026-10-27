module

public import CFSG.Quasithin.H13.A6Model4
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FactsS6
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.QuasithinUnique.A6Facts

namespace A6Fin

theorem exists_of_mem_pslLit6 {c : List ℕ} (hc : c ∈ Core.pslLit6) :
    ∃ y ∈ alternatingGroup (Fin 6), codeN 6 y = c := by
  obtain ⟨y, hy, hyc⟩ := pslGens6_closure_exists hc
  refine ⟨y, ?_, hyc⟩
  have hle : Subgroup.closure {g | g ∈ pslGens6} ≤ alternatingGroup (Fin 6) := by
    rw [Subgroup.closure_le]
    intro g hg
    exact Equiv.Perm.mem_alternatingGroup.mpr (pslGens6_sign g hg)
  exact hle hy

theorem codeN_mem_pslLit6 {σ : Perm (Fin 6)} (hσ : σ ∈ alternatingGroup (Fin 6)) :
    codeN 6 σ ∈ Core.pslLit6 := by
  classical
  have hcard : (Finset.univ.filter fun y : Perm (Fin 6) => codeN 6 y ∈ Core.pslLit6).card =
      360 := by
    rw [← Core.psl_length6, ← List.toFinset_card_of_nodup Core.psl_nodup6]
    apply Finset.card_bij (fun y _ => codeN 6 y)
    · intro y hy
      exact List.mem_toFinset.mpr (Finset.mem_filter.mp hy).2
    · intro y₁ _ y₂ _ h
      exact codeN_injective h
    · intro c hc
      obtain ⟨y, -, hyc⟩ := exists_of_mem_pslLit6 (List.mem_toFinset.mp hc)
      exact ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hyc ▸ List.mem_toFinset.mp hc⟩, hyc⟩
  by_contra hσS
  have hsub : insert σ (Finset.univ.filter fun y : Perm (Fin 6) => codeN 6 y ∈ Core.pslLit6) ⊆
      (Finset.univ.filter fun y : Perm (Fin 6) => y ∈ alternatingGroup (Fin 6)) := by
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hσ⟩
    · obtain ⟨y', hy', hyc⟩ := exists_of_mem_pslLit6 (Finset.mem_filter.mp hy).2
      rw [codeN_injective hyc] at hy'
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy'⟩
  have h1 := Finset.card_le_card hsub
  have hnot : σ ∉ (Finset.univ.filter fun y : Perm (Fin 6) => codeN 6 y ∈ Core.pslLit6) :=
    fun h => hσS (Finset.mem_filter.mp h).2
  rw [Finset.card_insert_of_notMem hnot, hcard] at h1
  have h2 : (Finset.univ.filter fun y : Perm (Fin 6) => y ∈ alternatingGroup (Fin 6)).card =
      360 := by
    rw [← Fintype.card_subtype]
    exact (card_alternatingGroup (α := Fin 6)).trans (by decide)
  omega

@[expose] def sig0 : Perm (Fin 6) := swap 0 1 * swap 1 2 * (swap 3 4 * swap 4 5)

@[expose] def cyc0 : Perm (Fin 6) := swap 0 1 * swap 1 2

@[expose] def sig0C : List ℕ := [1, 2, 0, 4, 5, 3]

@[expose] def cyc0C : List ℕ := [1, 2, 0, 3, 4, 5]

@[expose] def cpow4 (t : List ℕ) : List ℕ := Core.cmul (Core.cmul t t) (Core.cmul t t)

theorem sig0_code : codeN 6 sig0 = sig0C := by decide +kernel

theorem cyc0_code : codeN 6 cyc0 = cyc0C := by decide +kernel

theorem conj_check : Core.pslLit6.all (fun s => Core.cmul s (Core.cmul s s) != Core.cid6 ||
    s == Core.cid6 || Core.pslLit6.any (fun p => Core.cmul p sig0C == Core.cmul s p) ||
    Core.pslLit6.any (fun p => Core.cmul p cyc0C == Core.cmul s p)) = true := by
  decide +kernel

theorem cent_check : Core.pslLit6.all (fun t => Core.cmul t sig0C != Core.cmul sig0C t ||
    cpow4 t != Core.cid6 || t == Core.cid6) = true := by
  decide +kernel

theorem norm_check : Core.pslLit6.all (fun t => !(Core.cmul t sig0C == Core.cmul sig0C t ||
    Core.cmul t sig0C == Core.cmul (Core.cmul sig0C sig0C) t) || cpow4 t != Core.cid6 ||
    Core.cmul t t == Core.cid6) = true := by
  decide +kernel

theorem pow_check : Core.pslLit6.all (fun t =>
    Core.cmul (cpow4 t) (cpow4 t) != Core.cid6 || cpow4 t == Core.cid6) = true := by
  decide +kernel

theorem conj_pow' {G : Type*} [Group G] (a b : G) (n : ℕ) :
    (a⁻¹ * b * a) ^ n = a⁻¹ * b ^ n * a := by
  have h : (a⁻¹ * b * a⁻¹⁻¹) ^ n = a⁻¹ * b ^ n * a⁻¹⁻¹ := conj_pow
  rwa [inv_inv] at h

theorem act4f_one_eq (σ : Perm (Fin 6)) : act4f σ 1 = 1 := by
  unfold act4f
  rw [map_one]
  exact nrm_of_five 1 (by decide)

theorem codeN_pow4 (τ : Perm (Fin 6)) : codeN 6 (τ ^ 4) = cpow4 (codeN 6 τ) := by
  rw [cpow4, ← codeN_mul, ← codeN_mul]
  congr 1

theorem codeN_eq_cid6_iff (τ : Perm (Fin 6)) : codeN 6 τ = Core.cid6 ↔ τ = 1 := by
  rw [Core.cid6, ← codeN_one]
  exact codeN_injective.eq_iff

theorem pow_four_eq_one {τ : Perm (Fin 6)} (hτ : τ ∈ alternatingGroup (Fin 6))
    (h8 : τ ^ 8 = 1) : τ ^ 4 = 1 := by
  have h := pow_check
  rw [List.all_eq_true] at h
  have h1 := h _ (codeN_mem_pslLit6 hτ)
  rw [← codeN_pow4, ← codeN_mul, show τ ^ 4 * τ ^ 4 = τ ^ 8 by group, h8, codeN_one] at h1
  have e : (List.range 6 != Core.cid6) = false := by simp [Core.cid6]
  rw [e, Bool.false_or, beq_iff_eq, codeN_eq_cid6_iff] at h1
  exact h1

theorem pow_four_eq_one_of_two {τ : Perm (Fin 6)} (hτ : τ ∈ alternatingGroup (Fin 6)) {k : ℕ}
    (hk : τ ^ 2 ^ k = 1) : τ ^ 4 = 1 := by
  apply pow_four_eq_one hτ
  have h1 : orderOf τ ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have h2 : orderOf τ ∣ 720 := by
    have := orderOf_dvd_card (G := Perm (Fin 6)) (x := τ)
    rw [Fintype.card_perm, Fintype.card_fin] at this
    exact this
  obtain ⟨j, hj, hτj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  have hj4 : j ≤ 4 := by
    by_contra hj4
    push Not at hj4
    have h3 : 2 ^ 5 ∣ 720 := (pow_dvd_pow 2 hj4).trans (hτj ▸ h2)
    norm_num at h3
  have h8 : orderOf τ ∣ 2 ^ 4 := hτj ▸ pow_dvd_pow 2 hj4
  by_cases hj3 : j ≤ 3
  · exact orderOf_dvd_iff_pow_eq_one.mp (hτj ▸ (pow_dvd_pow 2 hj3).trans (by norm_num))
  · have hj : j = 4 := by omega
    exfalso
    have h16 : orderOf τ = 16 := by rw [hτj, hj]; norm_num
    have h5 : τ ^ 16 = 1 := by rw [← h16]; exact pow_orderOf_eq_one τ
    have h6 : (τ ^ 2) ^ 8 = 1 := by rw [← pow_mul]; exact h5
    have h7 := pow_four_eq_one (Subgroup.pow_mem _ hτ 2) h6
    have h9 : orderOf τ ∣ 8 := orderOf_dvd_of_pow_eq_one (by rw [← h7, ← pow_mul])
    rw [h16] at h9
    norm_num at h9

theorem conj_cases {σ : Perm (Fin 6)} (hσ : σ ∈ alternatingGroup (Fin 6)) (h3 : σ ^ 3 = 1)
    (h1 : σ ≠ 1) : (∃ π ∈ alternatingGroup (Fin 6), π * sig0 = σ * π) ∨
      ∃ π ∈ alternatingGroup (Fin 6), π * cyc0 = σ * π := by
  have h := conj_check
  rw [List.all_eq_true] at h
  have h2 := h _ (codeN_mem_pslLit6 hσ)
  have e1 : (Core.cmul (codeN 6 σ) (Core.cmul (codeN 6 σ) (codeN 6 σ)) != Core.cid6) = false := by
    rw [← codeN_mul, ← codeN_mul, ← pow_three, h3, codeN_one]
    simp [Core.cid6]
  have e2 : (codeN 6 σ == Core.cid6) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq, codeN_eq_cid6_iff]
    exact h1
  rw [e1, e2, Bool.false_or, Bool.false_or, Bool.or_eq_true, List.any_eq_true,
    List.any_eq_true] at h2
  rcases h2 with ⟨p, hp, hpe⟩ | ⟨p, hp, hpe⟩
  · left
    obtain ⟨π, hπ, rfl⟩ := exists_of_mem_pslLit6 hp
    refine ⟨π, hπ, codeN_injective ?_⟩
    rw [codeN_mul, codeN_mul, sig0_code]
    exact beq_iff_eq.mp hpe
  · right
    obtain ⟨π, hπ, rfl⟩ := exists_of_mem_pslLit6 hp
    refine ⟨π, hπ, codeN_injective ?_⟩
    rw [codeN_mul, codeN_mul, cyc0_code]
    exact beq_iff_eq.mp hpe

theorem eq_one_of_commute_sig0 {τ : Perm (Fin 6)} (hτ : τ ∈ alternatingGroup (Fin 6))
    (hc : τ * sig0 = sig0 * τ) (h4 : τ ^ 4 = 1) : τ = 1 := by
  have h := cent_check
  rw [List.all_eq_true] at h
  have h1 := h _ (codeN_mem_pslLit6 hτ)
  have e1 : (Core.cmul (codeN 6 τ) sig0C != Core.cmul sig0C (codeN 6 τ)) = false := by
    rw [← sig0_code, ← codeN_mul, ← codeN_mul, hc]
    simp
  have e2 : (cpow4 (codeN 6 τ) != Core.cid6) = false := by
    rw [← codeN_pow4, h4, codeN_one]
    simp [Core.cid6]
  rw [e1, e2, Bool.false_or, Bool.false_or, beq_iff_eq, codeN_eq_cid6_iff] at h1
  exact h1

theorem sq_eq_one_of_normalizes_sig0 {τ : Perm (Fin 6)} (hτ : τ ∈ alternatingGroup (Fin 6))
    (hn : τ * sig0 = sig0 * τ ∨ τ * sig0 = sig0 * sig0 * τ) (h4 : τ ^ 4 = 1) : τ ^ 2 = 1 := by
  have h := norm_check
  rw [List.all_eq_true] at h
  have h1 := h _ (codeN_mem_pslLit6 hτ)
  have e1 : (!(Core.cmul (codeN 6 τ) sig0C == Core.cmul sig0C (codeN 6 τ) ||
      Core.cmul (codeN 6 τ) sig0C == Core.cmul (Core.cmul sig0C sig0C) (codeN 6 τ))) = false := by
    rw [← sig0_code, ← codeN_mul, ← codeN_mul, ← codeN_mul, ← codeN_mul]
    rcases hn with hn | hn <;> simp [hn]
  have e2 : (cpow4 (codeN 6 τ) != Core.cid6) = false := by
    rw [← codeN_pow4, h4, codeN_one]
    simp [Core.cid6]
  rw [e1, e2, Bool.false_or, Bool.false_or, beq_iff_eq, ← codeN_mul, codeN_eq_cid6_iff] at h1
  rw [pow_two]
  exact h1

theorem cyc0_fix : act4f cyc0 (dv 3 4) = dv 3 4 ∧ dv 3 4 ≠ 1 := by
  rw [act4f_dv]
  decide +kernel

theorem exists_conj_sig0 {σ : Perm (Fin 6)} (hσ : σ ∈ alternatingGroup (Fin 6)) (h3 : σ ^ 3 = 1)
    (hfix : ∀ w : P6, InW4 w → act4f σ w = w → w = 1) :
    ∃ π ∈ alternatingGroup (Fin 6), π * sig0 = σ * π := by
  have h1 : σ ≠ 1 := by
    rintro rfl
    exact cyc0_fix.2 (hfix _ (dv_mem 3 4) (act4f_one _ (dv_mem 3 4)))
  rcases conj_cases hσ h3 h1 with h | ⟨π, -, hπ⟩
  · exact h
  · exfalso
    have hσ' : σ = π * cyc0 * π⁻¹ := by rw [hπ, mul_inv_cancel_right]
    apply cyc0_fix.2
    have hw := act4f_mem π (dv_mem 3 4)
    have h2 : act4f σ (act4f π (dv 3 4)) = act4f π (dv 3 4) := by
      rw [hσ', act4f_mul, act4f_mul, ← act4f_mul π⁻¹ π, inv_mul_cancel, act4f_one _ (dv_mem 3 4),
        cyc0_fix.1]
    have h4 := hfix _ hw h2
    have h5 : act4f π⁻¹ (act4f π (dv 3 4)) = dv 3 4 := by
      rw [← act4f_mul, inv_mul_cancel, act4f_one _ (dv_mem 3 4)]
    rw [← h5, h4]
    exact act4f_one_eq π⁻¹

theorem eq_one_of_commute {σ τ : Perm (Fin 6)} (hσ : σ ∈ alternatingGroup (Fin 6))
    (h3 : σ ^ 3 = 1) (hfix : ∀ w : P6, InW4 w → act4f σ w = w → w = 1)
    (hτ : τ ∈ alternatingGroup (Fin 6)) (hc : τ * σ = σ * τ) {k : ℕ} (hk : τ ^ 2 ^ k = 1) :
    τ = 1 := by
  obtain ⟨π, hπ, hπσ⟩ := exists_conj_sig0 hσ h3 hfix
  have hσ' : σ = π * sig0 * π⁻¹ := by rw [hπσ, mul_inv_cancel_right]
  have hτ' : π⁻¹ * τ * π ∈ alternatingGroup (Fin 6) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hπ) hτ) hπ
  have h4 : (π⁻¹ * τ * π) ^ 4 = 1 := by
    rw [conj_pow', pow_four_eq_one_of_two hτ hk, mul_one, inv_mul_cancel]
  have hc' : (π⁻¹ * τ * π) * sig0 = sig0 * (π⁻¹ * τ * π) := by
    have e : sig0 = π⁻¹ * σ * π := by rw [hσ']; group
    rw [e]
    calc π⁻¹ * τ * π * (π⁻¹ * σ * π) = π⁻¹ * (τ * σ) * π := by group
      _ = π⁻¹ * (σ * τ) * π := by rw [hc]
      _ = π⁻¹ * σ * π * (π⁻¹ * τ * π) := by group
  have h1 := eq_one_of_commute_sig0 hτ' hc' h4
  calc τ = π * (π⁻¹ * τ * π) * π⁻¹ := by group
    _ = 1 := by rw [h1]; group

theorem sq_eq_one_of_normalizes {σ τ : Perm (Fin 6)} (hσ : σ ∈ alternatingGroup (Fin 6))
    (h3 : σ ^ 3 = 1) (hfix : ∀ w : P6, InW4 w → act4f σ w = w → w = 1)
    (hτ : τ ∈ alternatingGroup (Fin 6)) (hn : τ * σ = σ * τ ∨ τ * σ = σ * σ * τ) {k : ℕ}
    (hk : τ ^ 2 ^ k = 1) : τ ^ 2 = 1 := by
  obtain ⟨π, hπ, hπσ⟩ := exists_conj_sig0 hσ h3 hfix
  have hσ' : σ = π * sig0 * π⁻¹ := by rw [hπσ, mul_inv_cancel_right]
  have hτ' : π⁻¹ * τ * π ∈ alternatingGroup (Fin 6) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hπ) hτ) hπ
  have h4 : (π⁻¹ * τ * π) ^ 4 = 1 := by
    rw [conj_pow', pow_four_eq_one_of_two hτ hk, mul_one, inv_mul_cancel]
  have e : sig0 = π⁻¹ * σ * π := by rw [hσ']; group
  have hn' : (π⁻¹ * τ * π) * sig0 = sig0 * (π⁻¹ * τ * π) ∨
      (π⁻¹ * τ * π) * sig0 = sig0 * sig0 * (π⁻¹ * τ * π) := by
    rw [e]
    rcases hn with hn | hn
    · left
      calc π⁻¹ * τ * π * (π⁻¹ * σ * π) = π⁻¹ * (τ * σ) * π := by group
        _ = π⁻¹ * (σ * τ) * π := by rw [hn]
        _ = π⁻¹ * σ * π * (π⁻¹ * τ * π) := by group
    · right
      calc π⁻¹ * τ * π * (π⁻¹ * σ * π) = π⁻¹ * (τ * σ) * π := by group
        _ = π⁻¹ * (σ * σ * τ) * π := by rw [hn]
        _ = π⁻¹ * σ * π * (π⁻¹ * σ * π) * (π⁻¹ * τ * π) := by group
  have h1 := sq_eq_one_of_normalizes_sig0 hτ' hn' h4
  rw [conj_pow'] at h1
  calc τ ^ 2 = π * (π⁻¹ * τ ^ 2 * π) * π⁻¹ := by group
    _ = 1 := by rw [h1]; group

@[expose] def g1 : Perm (Fin 6) := swap 2 3 * swap 3 4

@[expose] def g2 : Perm (Fin 6) := swap 0 1 * swap 2 3

theorem stab_fix : ∀ w : P6, InW4 w → act4f g1 w = w → act4f g2 w = w → w = 1 ∨ w = dv 0 1 := by
  decide +kernel

@[expose] def piK (k : Fin 6) : Perm (Fin 6) :=
  if k = 2 then swap 1 2 * swap 3 4 else if k = 3 then swap 1 3 * swap 2 4
  else if k = 4 then swap 1 4 * swap 2 3 else if k = 5 then swap 1 5 * swap 2 3 else 1

theorem piK_facts' : ∀ k : Fin 6, k ≠ 0 → Perm.sign (piK k) = 1 ∧ piK k 0 = 0 ∧
    piK k 1 = k := by
  decide

theorem piK_facts (k : Fin 6) (hk : k ≠ 0) : piK k ∈ alternatingGroup (Fin 6) ∧ piK k 0 = 0 ∧
    piK k 1 = k :=
  ⟨Equiv.Perm.mem_alternatingGroup.mpr (piK_facts' k hk).1, (piK_facts' k hk).2⟩

theorem g12_facts' : Perm.sign g1 = 1 ∧ Perm.sign g2 = 1 ∧
    dv (g1 0) (g1 1) = dv 0 1 ∧ dv (g2 0) (g2 1) = dv 0 1 := by
  decide +kernel

theorem g12_facts : g1 ∈ alternatingGroup (Fin 6) ∧ g2 ∈ alternatingGroup (Fin 6) ∧
    dv (g1 0) (g1 1) = dv 0 1 ∧ dv (g2 0) (g2 1) = dv 0 1 :=
  ⟨Equiv.Perm.mem_alternatingGroup.mpr g12_facts'.1,
    Equiv.Perm.mem_alternatingGroup.mpr g12_facts'.2.1, g12_facts'.2.2⟩

@[expose] def dvW (k : Fin 6) : ↥W4 := ⟨dv 0 k, dv_mem 0 k⟩

theorem end_W4 (f : ↥W4 →* ↥W4)
    (hf : ∀ σ ∈ alternatingGroup (Fin 6), ∀ w, f (act4 σ w) = act4 σ (f w)) :
    (∀ w, f w = 1) ∨ (∀ w, f w = w) := by
  obtain ⟨hg1, hg2, hd1, hd2⟩ := g12_facts
  have hfix : ∀ g ∈ alternatingGroup (Fin 6), dv (g 0) (g 1) = dv 0 1 →
      act4 g (f (dvW 1)) = f (dvW 1) := by
    intro g hg hd
    rw [← hf g hg]
    congr 1
    apply Subtype.ext
    rw [act4_coe]
    exact (act4f_dv g 0 1).trans hd
  have h1 : ((f (dvW 1) : ↥W4) : P6) = 1 ∨ ((f (dvW 1) : ↥W4) : P6) = dv 0 1 :=
    stab_fix _ (f (dvW 1)).2 (congrArg Subtype.val (hfix g1 hg1 hd1))
      (congrArg Subtype.val (hfix g2 hg2 hd2))
  have hk : ∀ k : Fin 6, k ≠ 0 → f (dvW k) = act4 (piK k) (f (dvW 1)) := by
    intro k hk0
    obtain ⟨hπ, hπ0, hπ1⟩ := piK_facts k hk0
    rw [← hf _ hπ]
    congr 1
    apply Subtype.ext
    rw [act4_coe]
    show dv 0 k = act4f (piK k) (dv 0 1)
    rw [act4f_dv, hπ0, hπ1]
  have hgen : ∀ w : ↥W4, w = dvW 1 ^ (Multiplicative.toAdd (w : P6) 1).val *
      dvW 2 ^ (Multiplicative.toAdd (w : P6) 2).val *
      dvW 3 ^ (Multiplicative.toAdd (w : P6) 3).val *
      dvW 4 ^ (Multiplicative.toAdd (w : P6) 4).val := fun w =>
    Subtype.ext (eq_prod_dv _ w.2)
  rcases h1 with h1 | h1
  · left
    have h0 : ∀ k : Fin 6, k ≠ 0 → f (dvW k) = 1 := by
      intro k hk0
      have hf1 : f (dvW 1) = 1 := Subtype.ext h1
      rw [hk k hk0, hf1, map_one]
    intro w
    rw [hgen w, map_mul, map_mul, map_mul, map_pow, map_pow, map_pow, map_pow,
      h0 1 (by decide), h0 2 (by decide), h0 3 (by decide), h0 4 (by decide)]
    simp
  · right
    have h0 : ∀ k : Fin 6, k ≠ 0 → f (dvW k) = dvW k := by
      intro k hk0
      have hf1 : f (dvW 1) = dvW 1 := Subtype.ext h1
      rw [hk k hk0, hf1]
      obtain ⟨-, hπ0, hπ1⟩ := piK_facts k hk0
      apply Subtype.ext
      rw [act4_coe]
      show act4f (piK k) (dv 0 1) = dv 0 k
      rw [act4f_dv, hπ0, hπ1]
    intro w
    calc f w = f (dvW 1 ^ (Multiplicative.toAdd (w : P6) 1).val *
        dvW 2 ^ (Multiplicative.toAdd (w : P6) 2).val *
        dvW 3 ^ (Multiplicative.toAdd (w : P6) 3).val *
        dvW 4 ^ (Multiplicative.toAdd (w : P6) 4).val) := congrArg f (hgen w)
      _ = dvW 1 ^ (Multiplicative.toAdd (w : P6) 1).val *
        dvW 2 ^ (Multiplicative.toAdd (w : P6) 2).val *
        dvW 3 ^ (Multiplicative.toAdd (w : P6) 3).val *
        dvW 4 ^ (Multiplicative.toAdd (w : P6) 4).val := by
          rw [map_mul, map_mul, map_mul, map_pow, map_pow, map_pow, map_pow,
            h0 1 (by decide), h0 2 (by decide), h0 3 (by decide), h0 4 (by decide)]
      _ = w := (hgen w).symm

end A6Fin

end CFSG.Quasithin.H13.A6
