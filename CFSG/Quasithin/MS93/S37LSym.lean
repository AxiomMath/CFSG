module

public import CFSG.Quasithin.MS93.MSPRankOne
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.MS93.S37L

open Matrix CFSG.Assembly.LowTwoRank CFSG.Quasithin.MS93 CFSG.Quasithin.MS93.MSP
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFour

variable {F : Type} [Field F]

theorem tau_entry {C : Matrix (Fin 2) (Fin 2) F} (hC : Cᵀ = C) (i j : Fin 2) :
    mat (tau hC) (.inl i) (.inr j) = C i j := by
  rw [mat, coe_tau]
  rfl

noncomputable abbrev q3 (b c d : F) : Sp4 F := tau (sym2_transpose b c d)

theorem q3_mem (b c d : F) : q3 b c d ∈ Q₁ F := tau_mem_Q₁ _

theorem q3_b (b c d : F) : mat (q3 b c d) (.inl 0) (.inr 0) = b := by
  rw [tau_entry]
  rfl

theorem q3_c (b c d : F) : mat (q3 b c d) (.inl 0) (.inr 1) = c := by
  rw [tau_entry]
  rfl

theorem q3_d (b c d : F) : mat (q3 b c d) (.inl 1) (.inr 1) = d := by
  rw [tau_entry]
  rfl

theorem eq_q3 {g : Sp4 F} (hg : g ∈ Q₁ F) :
    g = q3 (mat g (.inl 0) (.inr 0)) (mat g (.inl 0) (.inr 1)) (mat g (.inl 1) (.inr 1)) :=
  eq_of_mem_Q₁ hg (q3_mem _ _ _) (by rw [q3_b]) (by rw [q3_c]) (by rw [q3_d])

theorem q3_mul (b c d b' c' d' : F) : q3 b c d * q3 b' c' d' = q3 (b + b') (c + c') (d + d') :=
  eq_of_mem_Q₁ (mul_mem (q3_mem _ _ _) (q3_mem _ _ _)) (q3_mem _ _ _)
    (by rw [entry_mul_of_mem_Q₁ (q3_mem _ _ _) (q3_mem _ _ _), q3_b, q3_b, q3_b])
    (by rw [entry_mul_of_mem_Q₁ (q3_mem _ _ _) (q3_mem _ _ _), q3_c, q3_c, q3_c])
    (by rw [entry_mul_of_mem_Q₁ (q3_mem _ _ _) (q3_mem _ _ _), q3_d, q3_d, q3_d])

theorem q3_inj {b c d b' c' d' : F} (h : q3 b c d = q3 b' c' d') : b = b' ∧ c = c' ∧ d = d' := by
  refine ⟨?_, ?_, ?_⟩
  · have := congrArg (fun g => mat g (.inl 0) (.inr 0)) h
    simpa only [q3_b] using this
  · have := congrArg (fun g => mat g (.inl 0) (.inr 1)) h
    simpa only [q3_c] using this
  · have := congrArg (fun g => mat g (.inl 1) (.inr 1)) h
    simpa only [q3_d] using this

theorem mem_ln₀_of_fix {g : Sp4 F} (hg : g ∈ Q₁ F)
    (hdet : mat g (.inl 0) (.inr 0) * mat g (.inl 1) (.inr 1) - mat g (.inl 0) (.inr 1) ^ 2 ≠ 0)
    {v : V4 F} (hv : mat g *ᵥ v = v) : v ∈ ln₀ F := by
  rw [mulVec_of_mem_Q₁ hg] at hv
  set b := mat g (.inl 0) (.inr 0)
  set c := mat g (.inl 0) (.inr 1)
  set d := mat g (.inl 1) (.inr 1)
  have h0 := congrFun hv (.inl 0)
  have h1 := congrFun hv (.inl 1)
  simp [e₁, e₂] at h0 h1
  refine mem_ln₀.2 ⟨?_, ?_⟩
  · have : (b * d - c ^ 2) * v (.inr 0) = 0 := by linear_combination d * h0 - c * h1
    exact (mul_eq_zero.1 this).resolve_left hdet
  · have : (b * d - c ^ 2) * v (.inr 1) = 0 := by linear_combination b * h1 - c * h0
    exact (mul_eq_zero.1 this).resolve_left hdet

theorem conj_mem_Q₁ (A : Matrix.SpecialLinearGroup (Fin 2) F) {g : Sp4 F} (hg : g ∈ Q₁ F) :
    levHom₁ A * g * (levHom₁ A)⁻¹ ∈ Q₁ F :=
  (P₁_le_normalizer_Q₁ (lev₁_le_P₁ ⟨A, rfl⟩) g).1 hg

theorem conj_entry (A : Matrix.SpecialLinearGroup (Fin 2) F) {g : Sp4 F} (hg : g ∈ Q₁ F)
    (i j : Fin 2) :
    mat (levHom₁ A * g * (levHom₁ A)⁻¹) (.inl i) (.inr j) =
      (A : Matrix (Fin 2) (Fin 2) F) i 0 * mat g (.inl 0) (.inr 0) *
          (A : Matrix (Fin 2) (Fin 2) F) j 0 +
        (A : Matrix (Fin 2) (Fin 2) F) i 0 * mat g (.inl 0) (.inr 1) *
          (A : Matrix (Fin 2) (Fin 2) F) j 1 +
        (A : Matrix (Fin 2) (Fin 2) F) i 1 * mat g (.inl 0) (.inr 1) *
          (A : Matrix (Fin 2) (Fin 2) F) j 0 +
        (A : Matrix (Fin 2) (Fin 2) F) i 1 * mat g (.inl 1) (.inr 1) *
          (A : Matrix (Fin 2) (Fin 2) F) j 1 := by
  have hsym := entry_symm_of_mem_Q₁ hg
  rw [Q₁_eq_radical] at hg
  obtain ⟨C, hC, rfl⟩ := hg
  rw [levHom₁_conj_tau, tau_entry]
  rw [tau_entry, tau_entry] at hsym
  simp only [tau_entry, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two]
  rw [← hsym]
  ring

section CharTwo

variable [CharP F 2]

theorem conj_up {g : Sp4 F} (hg : g ∈ Q₁ F) (t : F) :
    levHom₁ (sl2Up t) * g * (levHom₁ (sl2Up t))⁻¹ =
      q3 (mat g (.inl 0) (.inr 0) + t ^ 2 * mat g (.inl 1) (.inr 1))
        (mat g (.inl 0) (.inr 1) + t * mat g (.inl 1) (.inr 1)) (mat g (.inl 1) (.inr 1)) := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  refine eq_of_mem_Q₁ (conj_mem_Q₁ _ hg) (q3_mem _ _ _) ?_ ?_ ?_
  · rw [conj_entry _ hg, q3_b]
    simp [sl2Up]
    linear_combination (t * mat g (.inl 0) (.inr 1)) * h2
  · rw [conj_entry _ hg, q3_c]
    simp [sl2Up]
  · rw [conj_entry _ hg, q3_d]
    simp [sl2Up]

theorem conj_low {g : Sp4 F} (hg : g ∈ Q₁ F) (s : F) :
    levHom₁ (sl2Low s) * g * (levHom₁ (sl2Low s))⁻¹ =
      q3 (mat g (.inl 0) (.inr 0)) (s * mat g (.inl 0) (.inr 0) + mat g (.inl 0) (.inr 1))
        (s ^ 2 * mat g (.inl 0) (.inr 0) + mat g (.inl 1) (.inr 1)) := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  refine eq_of_mem_Q₁ (conj_mem_Q₁ _ hg) (q3_mem _ _ _) ?_ ?_ ?_
  · rw [conj_entry _ hg, q3_b]
    simp [sl2Low]
  · rw [conj_entry _ hg, q3_c]
    simp [sl2Low]
    ring
  · rw [conj_entry _ hg, q3_d]
    simp [sl2Low]
    linear_combination (s * mat g (.inl 0) (.inr 1)) * h2

def sl2Sym (a : F) : Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![a, 1 + a; 1 + a, a], by
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    rw [det_fin_two_of]
    linear_combination (-(1 : F) - a) * h2⟩

theorem conj_sym {g : Sp4 F} (hg : g ∈ Q₁ F) (a : F) :
    levHom₁ (sl2Sym a) * g * (levHom₁ (sl2Sym a))⁻¹ =
      q3 (a ^ 2 * mat g (.inl 0) (.inr 0) + (1 + a) ^ 2 * mat g (.inl 1) (.inr 1))
        (a * (1 + a) * (mat g (.inl 0) (.inr 0) + mat g (.inl 1) (.inr 1)) +
          mat g (.inl 0) (.inr 1))
        ((1 + a) ^ 2 * mat g (.inl 0) (.inr 0) + a ^ 2 * mat g (.inl 1) (.inr 1)) := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  refine eq_of_mem_Q₁ (conj_mem_Q₁ _ hg) (q3_mem _ _ _) ?_ ?_ ?_
  · rw [conj_entry _ hg, q3_b]
    simp [sl2Sym]
    linear_combination (a * (1 + a) * mat g (.inl 0) (.inr 1)) * h2
  · rw [conj_entry _ hg, q3_c]
    simp [sl2Sym]
    linear_combination (a * mat g (.inl 0) (.inr 1) + a ^ 2 * mat g (.inl 0) (.inr 1)) * h2
  · rw [conj_entry _ hg, q3_d]
    simp [sl2Sym]
    linear_combination (a * (1 + a) * mat g (.inl 0) (.inr 1)) * h2

end CharTwo

section CharTwoQ3

variable [CharP F 2]

theorem conj_up_q3 (t b c d : F) :
    levHom₁ (sl2Up t) * q3 b c d * (levHom₁ (sl2Up t))⁻¹ = q3 (b + t ^ 2 * d) (c + t * d) d := by
  rw [conj_up (q3_mem _ _ _), q3_b, q3_c, q3_d]

theorem conj_low_q3 (s b c d : F) :
    levHom₁ (sl2Low s) * q3 b c d * (levHom₁ (sl2Low s))⁻¹ =
      q3 b (s * b + c) (s ^ 2 * b + d) := by
  rw [conj_low (q3_mem _ _ _), q3_b, q3_c, q3_d]

theorem conj_sym_q3 (a b c d : F) :
    levHom₁ (sl2Sym a) * q3 b c d * (levHom₁ (sl2Sym a))⁻¹ =
      q3 (a ^ 2 * b + (1 + a) ^ 2 * d) (a * (1 + a) * (b + d) + c)
        ((1 + a) ^ 2 * b + a ^ 2 * d) := by
  rw [conj_sym (q3_mem _ _ _), q3_b, q3_c, q3_d]

omit [CharP F 2] in
theorem q3_zero : q3 (0 : F) 0 0 = 1 :=
  eq_of_mem_Q₁ (q3_mem _ _ _) (one_mem _) (by rw [q3_b, entry_one]) (by rw [q3_c, entry_one])
    (by rw [q3_d, entry_one])

omit [CharP F 2] in
theorem q3_inv (b c d : F) : (q3 b c d)⁻¹ = q3 (-b) (-c) (-d) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [q3_mul, add_neg_cancel, add_neg_cancel, add_neg_cancel, q3_zero]

theorem levHom₁_low_inv (s : F) : (levHom₁ (sl2Low s))⁻¹ = levHom₁ (sl2Low s) := by
  rw [← map_inv]
  congr 1
  refine inv_eq_of_mul_eq_one_right (Subtype.ext ?_)
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2Low, Matrix.mul_apply, Fin.sum_univ_two]
  linear_combination s * h2

theorem levHom₁_up_inv (t : F) : (levHom₁ (sl2Up t))⁻¹ = levHom₁ (sl2Up t) := by
  rw [← map_inv]
  congr 1
  refine inv_eq_of_mul_eq_one_right (Subtype.ext ?_)
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2Up, Matrix.mul_apply, Fin.sum_univ_two]
  linear_combination t * h2

end CharTwoQ3

section Count

variable [Finite F]

theorem sq_lt_card {E : Subgroup (Sp4 F)} (f : F × F → Sp4 F) (hf : Function.Injective f)
    (hfE : ∀ p, f p ∈ E) {x : Sp4 F} (hx : x ∈ E) (hxf : ∀ p, f p ≠ x) :
    Nat.card F ^ 2 < Nat.card E := by
  let g : Option (F × F) → E := fun o => match o with
    | none => ⟨x, hx⟩
    | some p => ⟨f p, hfE p⟩
  have hg : Function.Injective g := by
    rintro (_ | p) (_ | p') h
    · rfl
    · exact absurd (congrArg Subtype.val h).symm (hxf p')
    · exact absurd (congrArg Subtype.val h) (hxf p)
    · exact congrArg some (hf (congrArg Subtype.val h))
  have hle := Nat.card_le_card_of_injective g hg
  have := Fintype.ofFinite F
  rw [Nat.card_eq_fintype_card (α := Option (F × F)), Fintype.card_option, Fintype.card_prod,
    ← sq, ← Nat.card_eq_fintype_card] at hle
  omega

theorem exists_coords {E : Subgroup (Sp4 F)} (hE : Nat.card E = Nat.card F ^ 2)
    (x y : Sp4 F → F) (hxy : ∀ g ∈ E, ∀ g' ∈ E, x g = x g' → y g = y g' → g = g') (a b : F) :
    ∃ g ∈ E, x g = a ∧ y g = b := by
  let φ : E → F × F := fun g => (x g, y g)
  have hφ : Function.Injective φ := fun g g' h =>
    Subtype.ext (hxy g g.2 g' g'.2 (congrArg Prod.fst h) (congrArg Prod.snd h))
  have hbij : Function.Bijective φ :=
    hφ.bijective_of_nat_card_le (by rw [Nat.card_prod, ← sq, hE])
  obtain ⟨g, hg⟩ := hbij.2 (a, b)
  exact ⟨g, g.2, congrArg Prod.fst hg, congrArg Prod.snd hg⟩

theorem exists_sq_eq [CharP F 2] (a : F) : ∃ t : F, t ^ 2 = a := by
  have hinj : Function.Injective (fun t : F => t ^ 2) := fun t t' h => frobenius_inj F 2 h
  obtain ⟨t, ht⟩ := Finite.surjective_of_injective hinj a
  exact ⟨t, ht⟩

end Count

section Root

variable [Finite F] [CharP F 2]

omit [Finite F] [CharP F 2] in
theorem exists_q3 {E : Subgroup (Sp4 F)} (hEQ : E ≤ Q₁ F) {g : Sp4 F} (hg : g ∈ E) :
    ∃ b c d : F, g = q3 b c d := ⟨_, _, _, eq_q3 (hEQ hg)⟩

theorem not_up_and_low (hq : 2 < Nat.card F) {E : Subgroup (Sp4 F)} (hEQ : E ≤ Q₁ F)
    (hE : Nat.card E = Nat.card F ^ 2)
    (hup : ∀ t : F, ∀ g ∈ E, levHom₁ (sl2Up t) * g * (levHom₁ (sl2Up t))⁻¹ ∈ E)
    (hlow : ∀ s : F, ∀ g ∈ E, levHom₁ (sl2Low s) * g * (levHom₁ (sl2Low s))⁻¹ ∈ E) : False := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  by_cases hd : ∃ g ∈ E, mat g (.inl 1) (.inr 1) ≠ 0
  · obtain ⟨g₀, hg₀E, hd₀⟩ := hd
    obtain ⟨b₀, c₀, d₀, rfl⟩ := exists_q3 hEQ hg₀E
    rw [q3_d] at hd₀
    have hu : ∀ t : F, q3 (t ^ 2 * d₀) (t * d₀) 0 ∈ E := by
      intro t
      have h1 := E.mul_mem (hup t _ hg₀E) (E.inv_mem hg₀E)
      rw [conj_up_q3, q3_inv, q3_mul] at h1
      convert h1 using 2 <;> ring
    have hw : ∀ s b' : F, q3 0 (s * b') (s ^ 2 * b') ∈ E := by
      intro s b'
      obtain ⟨t, ht⟩ := exists_sq_eq (b' / d₀)
      have hb' : t ^ 2 * d₀ = b' := by rw [ht, div_mul_cancel₀ _ hd₀]
      have h1 := E.mul_mem (hlow s _ (hu t)) (E.inv_mem (hu t))
      rw [conj_low_q3, q3_inv, q3_mul, hb'] at h1
      convert h1 using 2 <;> ring
    obtain ⟨σ, hσ0, hσ1⟩ := exists_ne_zero_ne_one hq
    have hσσ : σ + σ ^ 2 ≠ 0 := by
      intro h
      have : σ * (1 + σ) = 0 := by linear_combination h
      rcases mul_eq_zero.1 this with h' | h'
      · exact hσ0 h'
      · exact hσ1 (by linear_combination h' - h2)
    have hall : ∀ x y : F, q3 0 x y ∈ E := by
      intro x y
      set b₂ := (x + y) / (σ + σ ^ 2)
      have hb₂ : (σ + σ ^ 2) * b₂ = x + y := by rw [mul_div_cancel₀ _ hσσ]
      have h1 := E.mul_mem (hw 1 (x + σ * b₂)) (hw σ b₂)
      rw [q3_mul] at h1
      convert h1 using 2
      · ring
      · linear_combination -(σ * b₂) * h2
      · linear_combination -hb₂ - x * h2
    refine absurd (sq_lt_card (E := E) (fun p => q3 0 p.1 p.2) (fun p p' h => ?_)
      (fun p => hall p.1 p.2) (hu 1) fun p h => ?_) (by rw [hE]; exact lt_irrefl _)
    · obtain ⟨-, h1, h2'⟩ := q3_inj h
      exact Prod.ext h1 h2'
    · obtain ⟨h1, -, -⟩ := q3_inj h
      exact hd₀ (by simpa using h1.symm)
  · push Not at hd
    obtain ⟨g₁, hg₁E, hb₁, hc₁⟩ := exists_coords hE (fun g => mat g (.inl 0) (.inr 0))
      (fun g => mat g (.inl 0) (.inr 1)) (fun g hg g' hg' h1 h2' =>
        eq_of_mem_Q₁ (hEQ hg) (hEQ hg') h1 h2' (by rw [hd g hg, hd g' hg'])) 1 0
    have h1 := hd _ (hlow 1 g₁ hg₁E)
    rw [conj_low (hEQ hg₁E), q3_d, hb₁, hd g₁ hg₁E] at h1
    simp at h1

end Root

@[expose] def LeviFix (E : Subgroup (Sp4 F)) : Prop :=
  ∃ A : Matrix.SpecialLinearGroup (Fin 2) F, ∃ e ∈ E,
    (∀ v : V4 F, mat e *ᵥ v = v → v ∈ ln₀ F) ∧ levHom₁ A * e * (levHom₁ A)⁻¹ = e ∧
      ∃ e' ∈ E, levHom₁ A * e' * (levHom₁ A)⁻¹ ∉ E

theorem leviFix_of_map (A₀ : Matrix.SpecialLinearGroup (Fin 2) F) {E : Subgroup (Sp4 F)}
    (h : LeviFix (E.map (MulAut.conj (levHom₁ A₀)).toMonoidHom)) : LeviFix E := by
  obtain ⟨A, e, he, hfix, hc, e', he', hn⟩ := h
  set k := levHom₁ A₀ with hk
  rw [mem_map_conj] at he he'
  have hkA : levHom₁ (A₀⁻¹ * A * A₀) = k⁻¹ * levHom₁ A * k := by
    rw [map_mul, map_mul, map_inv]
  refine ⟨A₀⁻¹ * A * A₀, k⁻¹ * e * k, he, fun v hv => ?_, ?_, k⁻¹ * e' * k, he', ?_⟩
  · have hkv : mat e *ᵥ (mat k *ᵥ v) = mat k *ᵥ v := by
      have h1 : mat k *ᵥ (mat (k⁻¹ * e * k) *ᵥ v) = mat k *ᵥ v := by rw [hv]
      rwa [mat_mul_mulVec, mat_mul_mulVec, mat_mulVec_inv] at h1
    have hk' : k⁻¹ ∈ P₁ F := lev₁_le_P₁ ⟨A₀⁻¹, by rw [hk, map_inv]⟩
    have := mulVec_mem_of_mem_stab hk' (hfix _ hkv)
    rwa [mat_inv_mulVec] at this
  · rw [hkA]
    calc k⁻¹ * levHom₁ A * k * (k⁻¹ * e * k) * (k⁻¹ * levHom₁ A * k)⁻¹ =
        k⁻¹ * (levHom₁ A * e * (levHom₁ A)⁻¹) * k := by group
      _ = k⁻¹ * e * k := by rw [hc]
  · rw [hkA]
    intro hmem
    apply hn
    rw [mem_map_conj]
    have e1 : k⁻¹ * (levHom₁ A * e' * (levHom₁ A)⁻¹) * k =
        k⁻¹ * levHom₁ A * k * (k⁻¹ * e' * k) * (k⁻¹ * levHom₁ A * k)⁻¹ := by group
    rw [e1]
    exact hmem

section Main

variable [Finite F] [CharP F 2]

omit [Finite F] [CharP F 2] in
theorem entry_mul_inv_of_mem_Q₁ {g g' : Sp4 F} (hg : g ∈ Q₁ F) (hg' : g' ∈ Q₁ F) (i j : Fin 2) :
    mat (g * g'⁻¹) (.inl i) (.inr j) = mat g (.inl i) (.inr j) - mat g' (.inl i) (.inr j) := by
  rw [entry_mul_of_mem_Q₁ hg (inv_mem hg'), entry_inv_of_mem_Q₁ hg', sub_eq_add_neg]

theorem leviFix_core (hq : 2 < Nat.card F) {E : Subgroup (Sp4 F)} (hEQ : E ≤ Q₁ F)
    (hE : Nat.card E = Nat.card F ^ 2) (h₁ : ∃ b : F, q3 b 0 0 ∉ E)
    (h₂ : ∃ d : F, q3 0 0 d ∉ E) : LeviFix E := by
  have hbd : ∀ (P : Sp4 F → Prop), (∀ g ∈ E, P g → mat g (.inl 0) (.inr 1) = 0) →
      (∀ g ∈ E, ∀ g' ∈ E, mat (g * g'⁻¹) (.inl 0) (.inr 0) = 0 →
        mat (g * g'⁻¹) (.inl 1) (.inr 1) = 0 → P (g * g'⁻¹)) →
      ∀ g ∈ E, ∀ g' ∈ E, mat g (.inl 0) (.inr 0) = mat g' (.inl 0) (.inr 0) →
        mat g (.inl 1) (.inr 1) = mat g' (.inl 1) (.inr 1) → g = g' := by
    intro P hP hP' g hg g' hg' h0 h1
    have hk := E.mul_mem hg (E.inv_mem hg')
    have e0 : mat (g * g'⁻¹) (.inl 0) (.inr 0) = 0 := by
      rw [entry_mul_inv_of_mem_Q₁ (hEQ hg) (hEQ hg'), h0, sub_self]
    have e1 : mat (g * g'⁻¹) (.inl 1) (.inr 1) = 0 := by
      rw [entry_mul_inv_of_mem_Q₁ (hEQ hg) (hEQ hg'), h1, sub_self]
    have ec := hP _ hk (hP' g hg g' hg' e0 e1)
    have h1' : g * g'⁻¹ = 1 := eq_of_mem_Q₁ (hEQ hk) (one_mem _) (by rw [e0, entry_one])
      (by rw [ec, entry_one]) (by rw [e1, entry_one])
    exact mul_inv_eq_one.1 h1'
  have G₁ : ∃ g ∈ E, mat g (.inl 1) (.inr 1) = 0 ∧ mat g (.inl 0) (.inr 1) ≠ 0 := by
    by_contra hn
    push Not at hn
    obtain ⟨b₀, hb₀⟩ := h₁
    obtain ⟨g, hg, hgb, hgd⟩ := exists_coords hE _ _ (hbd (fun g => mat g (.inl 1) (.inr 1) = 0)
      hn fun _ _ _ _ _ h => h) b₀ 0
    refine hb₀ ?_
    have e := eq_q3 (hEQ hg)
    rw [hgb, hgd, hn g hg hgd] at e
    rw [← e]
    exact hg
  have G₂ : ∃ g ∈ E, mat g (.inl 0) (.inr 0) = 0 ∧ mat g (.inl 0) (.inr 1) ≠ 0 := by
    by_contra hn
    push Not at hn
    obtain ⟨d₀, hd₀⟩ := h₂
    obtain ⟨g, hg, hgb, hgd⟩ := exists_coords hE _ _ (hbd (fun g => mat g (.inl 0) (.inr 0) = 0)
      hn fun _ _ _ _ h _ => h) 0 d₀
    refine hd₀ ?_
    have e := eq_q3 (hEQ hg)
    rw [hgb, hgd, hn g hg hgb] at e
    rw [← e]
    exact hg
  by_cases hup : ∀ t : F, ∀ g ∈ E, levHom₁ (sl2Up t) * g * (levHom₁ (sl2Up t))⁻¹ ∈ E
  ·
    have hlow : ¬ ∀ s : F, ∀ g ∈ E, levHom₁ (sl2Low s) * g * (levHom₁ (sl2Low s))⁻¹ ∈ E :=
      fun hlow => not_up_and_low hq hEQ hE hup hlow
    push Not at hlow
    obtain ⟨s, e', he', hn⟩ := hlow
    obtain ⟨g, hg, hgb, hgc⟩ := G₂
    refine ⟨sl2Low s, g, hg, fun v hv => mem_ln₀_of_fix (hEQ hg) ?_ hv, ?_, e', he', hn⟩
    · rw [hgb, zero_mul, zero_sub, neg_ne_zero]
      exact pow_ne_zero 2 hgc
    · rw [eq_q3 (hEQ hg), conj_low_q3, hgb]
      simp
  · push Not at hup
    obtain ⟨t, e', he', hn⟩ := hup
    obtain ⟨g, hg, hgd, hgc⟩ := G₁
    refine ⟨sl2Up t, g, hg, fun v hv => mem_ln₀_of_fix (hEQ hg) ?_ hv, ?_, e', he', hn⟩
    · rw [hgd, mul_zero, zero_sub, neg_ne_zero]
      exact pow_ne_zero 2 hgc
    · rw [eq_q3 (hEQ hg), conj_up_q3, hgd]
      simp

omit [Finite F] [CharP F 2] in
theorem map_conj_le_Q₁ (A₀ : Matrix.SpecialLinearGroup (Fin 2) F) {E : Subgroup (Sp4 F)}
    (hEQ : E ≤ Q₁ F) : E.map (MulAut.conj (levHom₁ A₀)).toMonoidHom ≤ Q₁ F := by
  rintro _ ⟨g, hg, rfl⟩
  exact conj_mem_Q₁ A₀ (hEQ hg)

omit [Finite F] [CharP F 2] in
theorem card_map_conj' (A₀ : Matrix.SpecialLinearGroup (Fin 2) F) (E : Subgroup (Sp4 F)) :
    Nat.card (E.map (MulAut.conj (levHom₁ A₀)).toMonoidHom) = Nat.card E :=
  Subgroup.card_map_of_injective (MulAut.conj _).injective

theorem exists_leviFix (hq : 2 < Nat.card F) {E : Subgroup (Sp4 F)} (hEQ : E ≤ Q₁ F)
    (hE : Nat.card E = Nat.card F ^ 2) : LeviFix E := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  obtain ⟨σ, hσ0, hσ1⟩ := exists_ne_zero_ne_one hq
  have hσσ : σ ≠ σ ^ 2 := by
    intro h
    have : σ * (σ - 1) = 0 := by linear_combination -h
    rcases mul_eq_zero.1 this with h' | h'
    · exact hσ0 h'
    · exact hσ1 (sub_eq_zero.1 h')
  have hlt : ¬ Nat.card F ^ 2 < Nat.card E := by rw [hE]; exact lt_irrefl _
  by_cases P1 : ∀ b : F, q3 b 0 0 ∈ E
  · by_cases P2 : ∀ d : F, q3 0 0 d ∈ E
    ·
      have he : q3 1 0 1 ∈ E := by
        have := E.mul_mem (P1 1) (P2 1)
        rwa [q3_mul, add_zero, zero_add, zero_add] at this
      refine ⟨sl2Sym σ, q3 1 0 1, he, fun v hv => mem_ln₀_of_fix (q3_mem _ _ _) ?_ hv, ?_,
        q3 1 0 0, P1 1, ?_⟩
      · rw [q3_b, q3_c, q3_d]
        norm_num
      · rw [conj_sym_q3]
        congr 1
        · linear_combination (σ ^ 2 + σ) * h2
        · linear_combination (σ * (1 + σ)) * h2
        · linear_combination (σ ^ 2 + σ) * h2
      · rw [conj_sym_q3]
        intro hmem
        refine hlt (sq_lt_card (E := E) (fun p => q3 p.1 0 p.2) (fun p p' h => ?_)
          (fun p => ?_) hmem fun p h => ?_)
        · obtain ⟨h1, -, h3⟩ := q3_inj h
          exact Prod.ext h1 h3
        · have := E.mul_mem (P1 p.1) (P2 p.2)
          rwa [q3_mul, add_zero, zero_add, zero_add] at this
        · obtain ⟨-, h1, -⟩ := q3_inj h
          have h3 : σ * (1 + σ) = 0 := by linear_combination -h1
          rcases mul_eq_zero.1 h3 with h4 | h4
          · exact hσ0 h4
          · exact hσ1 (by linear_combination h4 - h2)
    · by_cases P3 : ∀ x : F, q3 x x x ∈ E
      ·
        have hmem3 : ∀ x y : F, q3 x y y ∈ E := fun x y => by
          have := E.mul_mem (P1 (x + y)) (P3 y)
          rw [q3_mul, zero_add] at this
          convert this using 2
          linear_combination -y * h2
        refine ⟨sl2Low σ, q3 0 1 1, hmem3 0 1, fun v hv => mem_ln₀_of_fix (q3_mem _ _ _) ?_ hv,
          ?_, q3 1 0 0, P1 1, ?_⟩
        · rw [q3_b, q3_c, q3_d]
          norm_num
        · rw [conj_low_q3]
          simp
        · rw [conj_low_q3]
          intro hmem
          refine hlt (sq_lt_card (E := E) (fun p => q3 p.1 p.2 p.2) (fun p p' h => ?_)
            (fun p => hmem3 p.1 p.2) hmem fun p h => ?_)
          · obtain ⟨h1, h3, -⟩ := q3_inj h
            exact Prod.ext h1 h3
          · obtain ⟨-, h1, h3⟩ := q3_inj h
            exact hσσ (by simpa using h1.symm.trans h3)
      ·
        push Not at P2 P3
        set k := levHom₁ (sl2Low (1 : F)) with hk
        have hkinv : k⁻¹ = k := levHom₁_low_inv 1
        have hmem : ∀ x : Sp4 F, x ∈ E.map (MulAut.conj k).toMonoidHom ↔
            k * x * k⁻¹ ∈ E := fun x => by
          rw [mem_map_conj]
          have : k⁻¹ * x * k = k * x * k⁻¹ := by rw [hkinv]
          rw [this]
        refine leviFix_of_map (sl2Low 1) (leviFix_core hq (map_conj_le_Q₁ _ hEQ)
          (by rw [card_map_conj']; exact hE) ?_ ?_)
        · obtain ⟨x, hx⟩ := P3
          refine ⟨x, ?_⟩
          rw [hmem, hk, conj_low_q3]
          simpa using hx
        · obtain ⟨d, hd⟩ := P2
          refine ⟨d, ?_⟩
          rw [hmem, hk, conj_low_q3]
          simpa using hd
  · by_cases P2 : ∀ d : F, q3 0 0 d ∈ E
    · by_cases P3 : ∀ x : F, q3 x x x ∈ E
      ·
        have hmem3 : ∀ x y : F, q3 x x y ∈ E := fun x y => by
          have := E.mul_mem (P2 (x + y)) (P3 x)
          rw [q3_mul, zero_add] at this
          convert this using 2
          linear_combination -x * h2
        refine ⟨sl2Up σ, q3 1 1 0, hmem3 1 0, fun v hv => mem_ln₀_of_fix (q3_mem _ _ _) ?_ hv,
          ?_, q3 0 0 1, P2 1, ?_⟩
        · rw [q3_b, q3_c, q3_d]
          norm_num
        · rw [conj_up_q3]
          simp
        · rw [conj_up_q3]
          intro hmem
          refine hlt (sq_lt_card (E := E) (fun p => q3 p.1 p.1 p.2) (fun p p' h => ?_)
            (fun p => hmem3 p.1 p.2) hmem fun p h => ?_)
          · obtain ⟨h1, -, h3⟩ := q3_inj h
            exact Prod.ext h1 h3
          · obtain ⟨h1, h3, -⟩ := q3_inj h
            exact hσσ (by simpa using h3.symm.trans h1)
      ·
        push Not at P1 P3
        set k := levHom₁ (sl2Up (1 : F)) with hk
        have hkinv : k⁻¹ = k := levHom₁_up_inv 1
        have hmem : ∀ x : Sp4 F, x ∈ E.map (MulAut.conj k).toMonoidHom ↔
            k * x * k⁻¹ ∈ E := fun x => by
          rw [mem_map_conj]
          have : k⁻¹ * x * k = k * x * k⁻¹ := by rw [hkinv]
          rw [this]
        refine leviFix_of_map (sl2Up 1) (leviFix_core hq (map_conj_le_Q₁ _ hEQ)
          (by rw [card_map_conj']; exact hE) ?_ ?_)
        · obtain ⟨b, hb⟩ := P1
          refine ⟨b, ?_⟩
          rw [hmem, hk, conj_up_q3]
          simpa using hb
        · obtain ⟨x, hx⟩ := P3
          refine ⟨x, ?_⟩
          rw [hmem, hk, conj_up_q3]
          simpa using hx
    · push Not at P1 P2
      exact leviFix_core hq hEQ hE P1 P2

end Main

end CFSG.Quasithin.MS93.S37L
