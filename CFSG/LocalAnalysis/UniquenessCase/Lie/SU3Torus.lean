module

public import CFSG.LieType.Steinberg.CentralExt.SUThreeOrder

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
  CFSG.LieType.Steinberg CFSG.LieType.BorelTits Subgroup

section Upper

variable {F : Type} [Field F] {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c)

noncomputable abbrev uc22pwsu3X : Subgroup (SU σ 3) := rootGroup σ hσ 3 (Pi.single 0 1)

noncomputable abbrev uc22pwsu3H (σ : F ≃+* F) : Subgroup (SU σ 3) :=
  levelTorus σ (0 : Fin (3 / 2))

noncomputable abbrev uc22pwsu3W (ζ : traceZero σ) : SU σ 3 := levelWeyl hσ ζ (0 : Fin (3 / 2))

theorem uc22pwsu3_mem_X_of_upper {x : SU σ 3} (h00 : mat σ 3 x 0 0 = 1) (h11 : mat σ 3 x 1 1 = 1)
    (h22 : mat σ 3 x 2 2 = 1) (h10 : mat σ 3 x 1 0 = 0) (h20 : mat σ 3 x 2 0 = 0)
    (h21 : mat σ 3 x 2 1 = 0) : x ∈ uc22pwsu3X hσ := by
  have e12 := sum_mat_mul_mat x 1 2
  have e22 := sum_mat_mul_mat x 2 2
  simp [Fin.sum_univ_three, h11, h22, h21] at e12 e22
  rw [uc22pwsu3X, mem_rootGroup_three hσ]
  refine ⟨mat σ 3 x 0 1, mat σ 3 x 0 2, ?_, ?_⟩
  · have hz : mat σ 3 x 1 2 = -σ (mat σ 3 x 0 1) := by linear_combination e12
    rw [hz, map_neg, hσ] at e22
    linear_combination e22
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [h00, h11, h22, h10, h20, h21]
    linear_combination e12

theorem uc22pwsu3_conj_diag_mem {h x : SU σ 3} {d : Fin 3 → F} (hd : ∀ i, d i ≠ 0)
    (hh : mat σ 3 h = diagonal d) (hx : x ∈ uc22pwsu3X hσ) : h * x * h⁻¹ ∈ uc22pwsu3X hσ := by
  have hinv := diagonal_inv_eq hd hh
  obtain ⟨a, b, -, hxm⟩ := (mem_rootGroup_three hσ).1 hx
  have hconj : ∀ i j, mat σ 3 (h * x * h⁻¹) i j = d i * mat σ 3 x i j * (d j)⁻¹ := by
    intro i j
    rw [map_mul, map_mul, hh, hinv, mul_diagonal, diagonal_mul]
  refine uc22pwsu3_mem_X_of_upper hσ ?_ ?_ ?_ ?_ ?_ ?_ <;> rw [hconj] <;> simp [hxm, hd]

theorem uc22pwsu3_levelTorus_le_normalizer :
    uc22pwsu3H σ ≤ normalizer (uc22pwsu3X hσ : Set (SU σ 3)) := by
  have key : ∀ g ∈ uc22pwsu3H σ, ∀ x ∈ uc22pwsu3X hσ, g * x * g⁻¹ ∈ uc22pwsu3X hσ := by
    intro g hg x hx
    obtain ⟨t, ht⟩ := exists_mat_eq_diagonal_of_mem_levelTorus_three hg
    refine uc22pwsu3_conj_diag_mem hσ ?_ ht hx
    have hσt : σ (t : F) ≠ 0 := by simp
    intro i
    fin_cases i <;> simp [hσt]
  intro h hh
  rw [mem_normalizer_iff]
  intro x
  refine ⟨key h hh x, fun hx => ?_⟩
  have := key h⁻¹ (inv_mem hh) _ hx
  simpa [mul_assoc] using this

end Upper

section Char2

variable {F : Type} [Field F] {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c) [CharP F 2]

theorem uc22pwsu3_levelWeyl_sq {ζ : traceZero σ} (hζ : (ζ : F) ≠ 0) :
    uc22pwsu3W hσ ζ ^ 2 = 1 := by
  apply mat_injective (σ := σ) (n := 3)
  rw [map_pow, map_one, pow_two, mat_levelWeyl_three hσ hζ]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, hζ, CharTwo.neg_eq]

@[expose] noncomputable def uc22pwsu3Y (β : F) (hβ : σ β = β) : SU σ 3 :=
  longRootHom σ (i := (0 : Fin 3)) (by decide)
    (Multiplicative.ofAdd ⟨β, by rw [mem_traceZero, hβ]; exact CharTwo.add_self_eq_zero β⟩)

theorem uc22pwsu3_mat_Y (β : F) (hβ : σ β = β) :
    mat σ 3 (uc22pwsu3Y β hβ) = !![1, 0, β; 0, 1, 0; 0, 0, 1] := by
  rw [mat_apply, uc22pwsu3Y, coe_longRootHom]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [longRootMatrix, Matrix.single_apply]

theorem uc22pwsu3Y_mul (β β' : F) (hβ : σ β = β) (hβ' : σ β' = β') (hs : σ (β + β') = β + β') :
    uc22pwsu3Y β hβ * uc22pwsu3Y β' hβ' = uc22pwsu3Y (β + β') hs := by
  apply mat_injective (σ := σ) (n := 3)
  rw [map_mul, uc22pwsu3_mat_Y, uc22pwsu3_mat_Y, uc22pwsu3_mat_Y]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, add_comm]

theorem uc22pwsu3Y_inj {β β' : F} {hβ : σ β = β} {hβ' : σ β' = β'}
    (h : uc22pwsu3Y β hβ = uc22pwsu3Y β' hβ') : β = β' := by
  have := congrArg (fun x => mat σ 3 x 0 2) h
  simpa [uc22pwsu3_mat_Y] using this

theorem uc22pwsu3Y_one : uc22pwsu3Y (σ := σ) 0 (map_zero σ) = 1 := by
  apply mat_injective (σ := σ) (n := 3)
  rw [map_one, uc22pwsu3_mat_Y]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem uc22pwsu3Y_mem (β : F) (hβ : σ β = β) : uc22pwsu3Y β hβ ∈ uc22pwsu3X hσ := by
  refine uc22pwsu3_mem_X_of_upper hσ ?_ ?_ ?_ ?_ ?_ ?_ <;> simp [uc22pwsu3_mat_Y]

theorem uc22pwsu3Y_comm {u : SU σ 3} (hu : u ∈ uc22pwsu3X hσ) (β : F) (hβ : σ β = β) :
    u * uc22pwsu3Y β hβ = uc22pwsu3Y β hβ * u := by
  obtain ⟨a, b, -, hum⟩ := (mem_rootGroup_three hσ).1 hu
  apply mat_injective (σ := σ) (n := 3)
  rw [map_mul, map_mul, hum, uc22pwsu3_mat_Y]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, add_comm]

theorem uc22pwsu3_exists_Y_of_sq {x : SU σ 3} (hx : x ∈ uc22pwsu3X hσ) (hx2 : x * x = 1) :
    ∃ (β : F) (hβ : σ β = β), x = uc22pwsu3Y β hβ := by
  obtain ⟨a, b, hab, hxm⟩ := (mem_rootGroup_three hσ).1 hx
  have h02 := congrFun (congrFun (congrArg (mat σ 3) hx2) 0) 2
  rw [map_mul, map_one, hxm] at h02
  simp [Matrix.mul_apply, Fin.sum_univ_three] at h02
  have ha : a = 0 := by
    have h1 : a * σ a = 0 := by
      linear_combination (-1 : F) * h02 + b * (CharTwo.two_eq_zero (R := F))
    rcases mul_eq_zero.1 h1 with h | h
    · exact h
    · exact (map_eq_zero σ).1 h
  have hb : σ b = b := by
    have : b + σ b = 0 := by simpa [ha] using hab
    linear_combination this - b * (CharTwo.two_eq_zero (R := F))
  refine ⟨b, hb, ?_⟩
  apply mat_injective (σ := σ) (n := 3)
  rw [hxm, uc22pwsu3_mat_Y, ha]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem uc22pwsu3Y_conj {h : SU σ 3} {d : Fin 3 → F} (hd : ∀ i, d i ≠ 0)
    (hh : mat σ 3 h = diagonal d) (β : F) (hβ : σ β = β) (γ : F) (hγ : σ γ = γ)
    (hγβ : γ = d 0 * (d 2)⁻¹ * β) : h * uc22pwsu3Y β hβ * h⁻¹ = uc22pwsu3Y γ hγ := by
  subst hγβ
  have hinv := diagonal_inv_eq hd hh
  apply mat_injective (σ := σ) (n := 3)
  rw [map_mul, map_mul, hh, hinv, uc22pwsu3_mat_Y, uc22pwsu3_mat_Y]
  ext i j
  rw [mul_diagonal, diagonal_mul]
  fin_cases i <;> fin_cases j <;> simp [hd]
  ring

theorem uc22pwsu3_bruhat (hnorm : ∀ x, σ x = x → ∃ a, σ a * a = x)
    (htop : CFSG.LieType.CurtisTits.rankOne (rootGroup σ hσ 3) (0 : Fin (3 / 2)) = ⊤)
    {ζ : traceZero σ} (hζ : (ζ : F) ≠ 0) (g : SU σ 3) :
    (∃ h ∈ uc22pwsu3H σ, ∃ u ∈ uc22pwsu3X hσ, g = h * u) ∨
      ∃ u ∈ uc22pwsu3X hσ, ∃ h ∈ uc22pwsu3H σ, ∃ v ∈ uc22pwsu3X hσ, g = u * uc22pwsu3W hσ ζ * h * v :=
  rankOne_bruhat_last_odd (n := 3) (hσ := hσ) (k := 0) (by decide) (by decide) hζ hnorm g
    (by rw [htop]; trivial)

theorem uc22pwsu3_levelWeyl_not_mem_normalizer {ζ : traceZero σ} (hζ : (ζ : F) ≠ 0) :
    uc22pwsu3W hσ ζ ∉ normalizer (uc22pwsu3X hσ : Set (SU σ 3)) := by
  intro hw
  have h1 := (mem_normalizer_iff.1 hw _).1 (uc22pwsu3Y_mem hσ (σ := σ) 1 (map_one σ))
  set y := uc22pwsu3W hσ ζ * uc22pwsu3Y (σ := σ) 1 (map_one σ) * (uc22pwsu3W hσ ζ)⁻¹ with hy
  obtain ⟨a, b, -, hm⟩ := (mem_rootGroup_three hσ).1 h1
  have e : uc22pwsu3W hσ ζ * uc22pwsu3Y (σ := σ) 1 (map_one σ) = y * uc22pwsu3W hσ ζ := by
    rw [hy]; group
  have e' := congrArg (fun g => mat σ 3 g 2 2) e
  simp only [map_mul] at e'
  rw [hm, uc22pwsu3_mat_Y, mat_levelWeyl_three hσ hζ] at e'
  simp [Matrix.mul_apply, Fin.sum_univ_three, hζ] at e'

theorem uc22pwsu3_normalizer_decomp (hnorm : ∀ x, σ x = x → ∃ a, σ a * a = x)
    (htop : CFSG.LieType.CurtisTits.rankOne (rootGroup σ hσ 3) (0 : Fin (3 / 2)) = ⊤)
    {ζ : traceZero σ} (hζ : (ζ : F) ≠ 0) {g : SU σ 3}
    (hg : g ∈ normalizer (uc22pwsu3X hσ : Set (SU σ 3))) :
    ∃ h ∈ uc22pwsu3H σ, ∃ u ∈ uc22pwsu3X hσ, g = h * u := by
  rcases uc22pwsu3_bruhat hσ hnorm htop hζ g with ⟨h, hh, u, hu, rfl⟩ | ⟨u, hu, h, hh, v, hv, rfl⟩
  · exact ⟨h, hh, u, hu, rfl⟩
  · exfalso
    apply uc22pwsu3_levelWeyl_not_mem_normalizer hσ hζ
    have hN := uc22pwsu3_levelTorus_le_normalizer hσ
    have e : uc22pwsu3W hσ ζ = u⁻¹ * (u * uc22pwsu3W hσ ζ * h * v) * v⁻¹ * h⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem (mul_mem (inv_mem (le_normalizer hu)) hg) (inv_mem (le_normalizer hv)))
      (inv_mem (hN hh))

theorem uc22pwsu3_normalizer_sup_eq_top (hnorm : ∀ x, σ x = x → ∃ a, σ a * a = x)
    (htop : CFSG.LieType.CurtisTits.rankOne (rootGroup σ hσ 3) (0 : Fin (3 / 2)) = ⊤)
    {ζ : traceZero σ} (hζ : (ζ : F) ≠ 0) :
    normalizer (uc22pwsu3X hσ : Set (SU σ 3)) ⊔ zpowers (uc22pwsu3W hσ ζ) = ⊤ := by
  rw [eq_top_iff]
  intro g _
  have hN := uc22pwsu3_levelTorus_le_normalizer hσ
  rcases uc22pwsu3_bruhat hσ hnorm htop hζ g with ⟨h, hh, u, hu, rfl⟩ | ⟨u, hu, h, hh, v, hv, rfl⟩
  · exact mul_mem (mem_sup_left (hN hh)) (mem_sup_left (le_normalizer hu))
  · exact mul_mem (mul_mem (mul_mem (mem_sup_left (le_normalizer hu))
      (mem_sup_right (mem_zpowers _))) (mem_sup_left (hN hh))) (mem_sup_left (le_normalizer hv))

theorem uc22pwsu3_diagonal_fin_three (a b c : F) :
    (diagonal ![a, b, c] : Matrix (Fin 3) (Fin 3) F) = !![a, 0, 0; 0, b, 0; 0, 0, c] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem uc22pwsu3_levelWeyl_conj {ζ : traceZero σ} (hζ : (ζ : F) ≠ 0) {h : SU σ 3} {t : F}
    (ht : t ≠ 0) (hh : mat σ 3 h = diagonal ![t, σ t / t, (σ t)⁻¹]) (hσt : σ t = t) :
    uc22pwsu3W hσ ζ * h * (uc22pwsu3W hσ ζ)⁻¹ = h⁻¹ := by
  have hw : (uc22pwsu3W hσ ζ)⁻¹ = uc22pwsu3W hσ ζ :=
    inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact uc22pwsu3_levelWeyl_sq hσ hζ)
  have hd : ∀ i, (![t, σ t / t, (σ t)⁻¹] : Fin 3 → F) i ≠ 0 := by
    intro i
    fin_cases i <;> simp [ht]
  have hinv := diagonal_inv_eq hd hh
  rw [hw]
  apply mat_injective (σ := σ) (n := 3)
  have hv : (fun s => (![t, σ t / t, (σ t)⁻¹] s)⁻¹) = ![t⁻¹, t / σ t, σ t] := by
    funext s
    fin_cases s <;> simp
  rw [map_mul, map_mul, hinv, hh, mat_levelWeyl_three hσ hζ, hv, hσt, uc22pwsu3_diagonal_fin_three,
    uc22pwsu3_diagonal_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_fin_three, hζ, ht, CharTwo.neg_eq] <;> field_simp

end Char2

section Entry

variable {F : Type} [Field F] {σ : F ≃+* F}

@[expose] noncomputable def uc22pwsu3HEntry (σ : F ≃+* F) : uc22pwsu3H σ →* F where
  toFun h := mat σ 3 h 0 0
  map_one' := by simp
  map_mul' h h' := by
    obtain ⟨t, ht⟩ := exists_mat_eq_diagonal_of_mem_levelTorus_three h.2
    obtain ⟨t', ht'⟩ := exists_mat_eq_diagonal_of_mem_levelTorus_three h'.2
    simp [Subgroup.coe_mul, map_mul, ht, ht']

theorem uc22pwsu3HEntry_injective : Function.Injective (uc22pwsu3HEntry σ) := by
  intro h h' hh
  obtain ⟨t, ht⟩ := exists_mat_eq_diagonal_of_mem_levelTorus_three h.2
  obtain ⟨t', ht'⟩ := exists_mat_eq_diagonal_of_mem_levelTorus_three h'.2
  have hh' : (t : F) = t' := by simpa [uc22pwsu3HEntry, ht, ht'] using hh
  have htt : t = t' := Units.ext hh'
  subst htt
  exact Subtype.ext (mat_injective (σ := σ) (n := 3) (ht.trans ht'.symm))

theorem uc22pwsu3H_cyclic [Finite F] : IsCyclic (uc22pwsu3H σ) :=
  isCyclic_of_subgroup_isDomain (uc22pwsu3HEntry σ) uc22pwsu3HEntry_injective

theorem uc22pwsu3HEntry_ne_zero (h : uc22pwsu3H σ) : uc22pwsu3HEntry σ h ≠ 0 := by
  obtain ⟨t, ht⟩ := exists_mat_eq_diagonal_of_mem_levelTorus_three h.2
  simp [uc22pwsu3HEntry, ht]

theorem uc22pwsu3_mat_pow_entry {h : SU σ 3} (hh : h ∈ uc22pwsu3H σ) (m : ℕ) :
    mat σ 3 (h ^ m) 0 0 = mat σ 3 h 0 0 ^ m := by
  have := map_pow (uc22pwsu3HEntry σ) (⟨h, hh⟩ : uc22pwsu3H σ) m
  simpa [uc22pwsu3HEntry] using this

theorem uc22pwsu3_pow_firstCol {g : SU σ 3} (h10 : mat σ 3 g 1 0 = 0) (h20 : mat σ 3 g 2 0 = 0)
    (m : ℕ) : mat σ 3 (g ^ m) 1 0 = 0 ∧ mat σ 3 (g ^ m) 2 0 = 0 ∧
      mat σ 3 (g ^ m) 0 0 = mat σ 3 g 0 0 ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    obtain ⟨i1, i2, i0⟩ := ih
    rw [pow_succ, map_mul]
    generalize mat σ 3 (g ^ m) = A at i1 i2 i0 ⊢
    refine ⟨?_, ?_, ?_⟩ <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, h10, h20, i1, i2, i0, pow_succ]

theorem uc22pwsu3H_exists_entry [Finite F] (hHcard : Nat.card (uc22pwsu3H σ) = Nat.card Fˣ)
    (s : Fˣ) : ∃ h ∈ uc22pwsu3H σ, mat σ 3 h = diagonal ![(s : F), σ s / s, (σ s)⁻¹] := by
  let φ : uc22pwsu3H σ → Fˣ := fun h =>
    Units.mk0 (uc22pwsu3HEntry σ h) (uc22pwsu3HEntry_ne_zero h)
  have hφ : Function.Injective φ := fun h h' hh =>
    uc22pwsu3HEntry_injective (by simpa [φ] using congrArg (fun u : Fˣ => (u : F)) hh)
  have hsurj : Function.Surjective φ := (hφ.bijective_of_nat_card_le hHcard.ge).2
  obtain ⟨h, hh⟩ := hsurj s
  obtain ⟨t, ht⟩ := exists_mat_eq_diagonal_of_mem_levelTorus_three h.2
  have hts : (t : F) = s := by
    have := congrArg (fun u : Fˣ => (u : F)) hh
    simpa [φ, uc22pwsu3HEntry, ht] using this
  refine ⟨h, h.2, ?_⟩
  rw [ht, hts]

theorem uc22pwsu3_diag_ratio (t : F) : (![t, σ t / t, (σ t)⁻¹] : Fin 3 → F) 0 *
    ((![t, σ t / t, (σ t)⁻¹] : Fin 3 → F) 2)⁻¹ = σ t * t := by
  simp [mul_comm]

end Entry

end CFSG.LocalAnalysis.UniquenessCase.UC22
