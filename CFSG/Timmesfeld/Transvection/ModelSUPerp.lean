module

public import CFSG.Timmesfeld.Transvection.ModelSUGeometry

public section

namespace CFSG.Timmesfeld.Transvection

namespace ModelRank

open Matrix CFSG.LieType.Universal.Unitary CFSG.Timmesfeld.LieEmbed

variable {F : Type} [Field F] {σ : F ≃+* F} {m : ℕ}

@[expose] def perpPair (σ : F ≃+* F) (a d : Fin m → F) : Submodule F (Fin m → F) where
  carrier := {w | uForm σ a w = 0 ∧ uForm σ d w = 0}
  add_mem' := fun {x y} hx hy => ⟨by rw [uForm_add_right, hx.1, hy.1, add_zero],
    by rw [uForm_add_right, hx.2, hy.2, add_zero]⟩
  zero_mem' := ⟨uForm_zero_right a, uForm_zero_right d⟩
  smul_mem' := fun c x hx => ⟨by rw [uForm_smul_right, hx.1, mul_zero],
    by rw [uForm_smul_right, hx.2, mul_zero]⟩

@[expose] def projPair (σ : F ≃+* F) (a d x : Fin m → F) : Fin m → F :=
  x - uForm σ d x • a - uForm σ a x • d

@[expose] def radVec (σ : F ≃+* F) (a d : Fin m → F) (g : SU σ m) : Fin m → F :=
  projPair σ a d (suMat σ m g *ᵥ d)

@[expose] def levAct (σ : F ≃+* F) (a d : Fin m → F) (g : SU σ m) (w : Fin m → F) :
    Fin m → F :=
  projPair σ a d (suMat σ m g *ᵥ w)

theorem mem_perpPair {a d w : Fin m → F} :
    w ∈ perpPair σ a d ↔ uForm σ a w = 0 ∧ uForm σ d w = 0 := Iff.rfl

theorem uForm_swap_eq_one (hσ : ∀ c, σ (σ c) = c) {a d : Fin m → F} (had : uForm σ a d = 1) :
    uForm σ d a = 1 := by
  rw [← uForm_conj σ hσ, had, map_one]

theorem projPair_mem (hσ : ∀ c, σ (σ c) = c) {a d : Fin m → F} (haa : uForm σ a a = 0)
    (hdd : uForm σ d d = 0) (had : uForm σ a d = 1) (x : Fin m → F) :
    projPair σ a d x ∈ perpPair σ a d := by
  have hda := uForm_swap_eq_one hσ had
  refine ⟨?_, ?_⟩
  · simp only [projPair, uForm_sub_right, uForm_smul_right, haa, had]
    ring
  · simp only [projPair, uForm_sub_right, uForm_smul_right, hdd, hda]
    ring

theorem projPair_of_mem {a d w : Fin m → F} (hw : w ∈ perpPair σ a d) :
    projPair σ a d w = w := by
  rw [projPair, hw.1, hw.2, zero_smul, zero_smul, sub_zero, sub_zero]

theorem projPair_add (a d x y : Fin m → F) :
    projPair σ a d (x + y) = projPair σ a d x + projPair σ a d y := by
  simp only [projPair, uForm_add_right, add_smul]
  abel

theorem projPair_smul (a d : Fin m → F) (c : F) (x : Fin m → F) :
    projPair σ a d (c • x) = c • projPair σ a d x := by
  simp only [projPair, uForm_smul_right, smul_sub, smul_smul]

theorem projPair_a (hσ : ∀ c, σ (σ c) = c) {a d : Fin m → F} (haa : uForm σ a a = 0)
    (had : uForm σ a d = 1) : projPair σ a d a = 0 := by
  have hda := uForm_swap_eq_one hσ had
  simp [projPair, haa, hda]

theorem projPair_d {a d : Fin m → F} (hdd : uForm σ d d = 0) (had : uForm σ a d = 1) :
    projPair σ a d d = 0 := by
  simp [projPair, hdd, had]

theorem projPair_add_smul_a (hσ : ∀ c, σ (σ c) = c) {a d : Fin m → F}
    (haa : uForm σ a a = 0) (had : uForm σ a d = 1) (x : Fin m → F) (c : F) :
    projPair σ a d (x + c • a) = projPair σ a d x := by
  rw [projPair_add, projPair_smul, projPair_a hσ haa had, smul_zero, add_zero]

theorem projPair_add_smul_d {a d : Fin m → F} (hdd : uForm σ d d = 0)
    (had : uForm σ a d = 1) (x : Fin m → F) (c : F) :
    projPair σ a d (x + c • d) = projPair σ a d x := by
  rw [projPair_add, projPair_smul, projPair_d hdd had, smul_zero, add_zero]

end ModelRank

end CFSG.Timmesfeld.Transvection

namespace CFSG.Timmesfeld.Transvection

namespace ModelRank

open Matrix CFSG.LieType.Universal.Unitary CFSG.Timmesfeld.LieEmbed CFSG.Timmesfeld.ARS
open scoped commutatorElement

variable {F : Type} [Field F] {m : ℕ}

structure SUGeomFacts (σ : F ≃+* F) (a d : Fin m → F) : Prop where
  exists_iso : ∃ e ∈ perpPair σ a d, e ≠ 0 ∧ uForm σ e e = 0
  partner : ∀ {e : Fin m → F}, e ∈ perpPair σ a d → e ≠ 0 → uForm σ e e = 0 →
    ∃ f ∈ perpPair σ a d, uForm σ f f = 0 ∧ uForm σ e f = 1
  nonorth : ∀ {w : Fin m → F}, w ∈ perpPair σ a d → w ≠ 0 →
    ∃ e ∈ perpPair σ a d, uForm σ e e = 0 ∧ uForm σ e w ≠ 0
  both : ∀ {e e' : Fin m → F}, e ∈ perpPair σ a d → e' ∈ perpPair σ a d → e ≠ 0 → e' ≠ 0 →
    uForm σ e e = 0 → uForm σ e' e' = 0 →
    ∃ y ∈ perpPair σ a d, uForm σ y y = 0 ∧ uForm σ e y ≠ 0 ∧ uForm σ e' y ≠ 0
  sum : ∀ {w : Fin m → F}, w ∈ perpPair σ a d →
    ∃ e₁ ∈ perpPair σ a d, ∃ e₂ ∈ perpPair σ a d, uForm σ e₁ e₁ = 0 ∧ uForm σ e₂ e₂ = 0 ∧
      w = e₁ + e₂
  kl : ∀ S : AddSubgroup (Fin m → F), (∀ x ∈ S, x ∈ perpPair σ a d) →
    (∀ v ∈ perpPair σ a d, uForm σ v v = 0 → ∀ x ∈ S, uForm σ v x ≠ 0 → ∀ c : F, c • v ∈ S) →
    S = ⊥ ∨ ∀ w ∈ perpPair σ a d, w ∈ S

end ModelRank

end CFSG.Timmesfeld.Transvection

namespace CFSG.Timmesfeld.Transvection

namespace ModelRank

open CFSG.LieType.Universal.Unitary CFSG.Timmesfeld.LieEmbed

variable {F : Type} [Field F] {σ : F ≃+* F} {m : ℕ}

theorem uForm_projPair_of_mem_perpPair (hσ : ∀ c, σ (σ c) = c) {a d e : Fin m → F}
    (he : e ∈ perpPair σ a d) (y : Fin m → F) :
    uForm σ e (projPair σ a d y) = uForm σ e y := by
  rw [projPair, uForm_sub_right, uForm_sub_right, uForm_smul_right, uForm_smul_right,
    uForm_eq_zero_comm hσ he.1, uForm_eq_zero_comm hσ he.2, mul_zero, mul_zero, sub_zero,
    sub_zero]

theorem exists_isotropic_mem_perpPair (hσ : ∀ c, σ (σ c) = c)
    (hnorm : ∀ c, σ c = c → ∃ l, σ l * l = c) (hm : 4 ≤ m) (a d : Fin m → F) :
    ∃ e ∈ perpPair σ a d, e ≠ 0 ∧ uForm σ e e = 0 := by
  obtain ⟨w, hw0, hww, hPw, hQw⟩ := exists_isotropic_perp hσ hnorm
    (P := fun _ : Fin 1 => a) (Q := fun _ : Fin 1 => d) (by omega)
  exact ⟨w, ⟨hPw 0, hQw 0⟩, hw0, hww⟩

theorem exists_isotropic_partner_mem_perpPair (hσ : ∀ c, σ (σ c) = c)
    (htr : ∀ c, σ c = c → ∃ e, e + σ e = c) {a d : Fin m → F} (haa : uForm σ a a = 0)
    (hdd : uForm σ d d = 0) (had : uForm σ a d = 1) {e : Fin m → F}
    (he : e ∈ perpPair σ a d) (he0 : e ≠ 0) (hee : uForm σ e e = 0) :
    ∃ f ∈ perpPair σ a d, uForm σ f f = 0 ∧ uForm σ e f = 1 := by
  obtain ⟨y₀, hy₀⟩ := exists_uForm_eq_one (σ := σ) he0
  have hy : projPair σ a d y₀ ∈ perpPair σ a d := projPair_mem hσ haa hdd had y₀
  have hey : uForm σ e (projPair σ a d y₀) = 1 := by
    rw [uForm_projPair_of_mem_perpPair hσ he, hy₀]
  have hye : uForm σ (projPair σ a d y₀) e = 1 := by rw [← uForm_conj σ hσ, hey, map_one]
  obtain ⟨c, hc⟩ := htr (-uForm σ (projPair σ a d y₀) (projPair σ a d y₀))
    (by rw [map_neg, uForm_conj σ hσ])
  refine ⟨projPair σ a d y₀ + c • e,
    (perpPair σ a d).add_mem hy ((perpPair σ a d).smul_mem c he), ?_, ?_⟩
  · simp only [uForm_add_left, uForm_add_right, uForm_smul_left, uForm_smul_right, hee, hey, hye]
    linear_combination hc
  · rw [uForm_add_right, uForm_smul_right, hee, mul_zero, add_zero, hey]

theorem exists_isotropic_mem_perpPair_uForm_ne_zero [CharP F 2] (hσ : ∀ c, σ (σ c) = c)
    (htr : ∀ c, σ c = c → ∃ e, e + σ e = c) (hnorm : ∀ c, σ c = c → ∃ l, σ l * l = c)
    (hm : 4 ≤ m) {a d : Fin m → F} (haa : uForm σ a a = 0) (hdd : uForm σ d d = 0)
    (had : uForm σ a d = 1) {w : Fin m → F} (hw : w ∈ perpPair σ a d) (hw0 : w ≠ 0) :
    ∃ e ∈ perpPair σ a d, uForm σ e e = 0 ∧ uForm σ e w ≠ 0 := by
  obtain ⟨e₀, he₀, he₀0, he₀e₀⟩ := exists_isotropic_mem_perpPair hσ hnorm hm a d
  obtain ⟨f₀, hf₀, hf₀f₀, he₀f₀⟩ :=
    exists_isotropic_partner_mem_perpPair hσ htr haa hdd had he₀ he₀0 he₀e₀
  by_cases he₀w : uForm σ e₀ w = 0
  swap
  · exact ⟨e₀, he₀, he₀e₀, he₀w⟩
  by_cases hf₀w : uForm σ f₀ w = 0
  swap
  · exact ⟨f₀, hf₀, hf₀f₀, hf₀w⟩
  by_cases hww : uForm σ w w = 0
  · obtain ⟨e, he, hee, hwe⟩ :=
      exists_isotropic_partner_mem_perpPair hσ htr haa hdd had hw hw0 hww
    refine ⟨e, he, hee, ?_⟩
    rw [← uForm_conj σ hσ, hwe, map_one]
    exact one_ne_zero
  have hwe₀ : uForm σ w e₀ = 0 := uForm_eq_zero_comm hσ he₀w
  have hwf₀ : uForm σ w f₀ = 0 := uForm_eq_zero_comm hσ hf₀w
  have hf₀e₀ : uForm σ f₀ e₀ = 1 := by rw [← uForm_conj σ hσ, he₀f₀, map_one]
  obtain ⟨t, ht⟩ := htr (uForm σ w w) (uForm_conj σ hσ w w)
  refine ⟨f₀ + t • e₀ + w, (perpPair σ a d).add_mem ((perpPair σ a d).add_mem hf₀
    ((perpPair σ a d).smul_mem t he₀)) hw, ?_, ?_⟩
  · simp only [uForm_add_left, uForm_add_right, uForm_smul_left, uForm_smul_right, hf₀f₀,
      he₀e₀, he₀f₀, hf₀e₀, he₀w, hf₀w, hwe₀, hwf₀]
    linear_combination ht + CharTwo.add_self_eq_zero (uForm σ w w)
  · simp only [uForm_add_left, uForm_smul_left, hf₀w, he₀w, mul_zero, zero_add]
    exact hww

theorem exists_isotropic_both_mem_perpPair [CharP F 2] (hσ : ∀ c, σ (σ c) = c)
    (htr : ∀ c, σ c = c → ∃ e, e + σ e = c) {a d : Fin m → F} (haa : uForm σ a a = 0)
    (hdd : uForm σ d d = 0) (had : uForm σ a d = 1) {e e' : Fin m → F}
    (he : e ∈ perpPair σ a d) (he' : e' ∈ perpPair σ a d) (he0 : e ≠ 0) (he'0 : e' ≠ 0)
    (hee : uForm σ e e = 0) (he'e' : uForm σ e' e' = 0) :
    ∃ y ∈ perpPair σ a d, uForm σ y y = 0 ∧ uForm σ e y ≠ 0 ∧ uForm σ e' y ≠ 0 := by
  obtain ⟨f, hf, hff, hef⟩ := exists_isotropic_partner_mem_perpPair hσ htr haa hdd had he he0 hee
  by_cases he'f : uForm σ e' f = 0
  swap
  · exact ⟨f, hf, hff, by rw [hef]; exact one_ne_zero, he'f⟩
  obtain ⟨f', hf', hf'f', he'f'⟩ :=
    exists_isotropic_partner_mem_perpPair hσ htr haa hdd had he' he'0 he'e'
  by_cases hef' : uForm σ e f' = 0
  swap
  · exact ⟨f', hf', hf'f', hef', by rw [he'f']; exact one_ne_zero⟩
  have hf'f : uForm σ f' f = σ (uForm σ f f') := (uForm_conj σ hσ f f').symm
  obtain ⟨t, ht0, ht⟩ : ∃ t : F, t ≠ 0 ∧ σ t * σ (uForm σ f f') + t * uForm σ f f' = 0 := by
    by_cases hff' : uForm σ f f' = 0
    · exact ⟨1, one_ne_zero, by rw [hff', map_zero, mul_zero, mul_zero, add_zero]⟩
    · refine ⟨(uForm σ f f')⁻¹, inv_ne_zero hff', ?_⟩
      rw [← map_mul, inv_mul_cancel₀ hff', map_one]
      exact CharTwo.add_self_eq_zero 1
  refine ⟨f + t • f', (perpPair σ a d).add_mem hf ((perpPair σ a d).smul_mem t hf'), ?_, ?_, ?_⟩
  · simp only [uForm_add_left, uForm_add_right, uForm_smul_left, uForm_smul_right, hff, hf'f',
      hf'f]
    linear_combination ht
  · rw [uForm_add_right, uForm_smul_right, hef, hef', mul_zero, add_zero]
    exact one_ne_zero
  · rw [uForm_add_right, uForm_smul_right, he'f, he'f', mul_one, zero_add]
    exact ht0

theorem exists_isotropic_add_mem_perpPair [CharP F 2] (hσ : ∀ c, σ (σ c) = c)
    (htr : ∀ c, σ c = c → ∃ e, e + σ e = c) (hnorm : ∀ c, σ c = c → ∃ l, σ l * l = c)
    (hm : 4 ≤ m) {a d : Fin m → F} (haa : uForm σ a a = 0) (hdd : uForm σ d d = 0)
    (had : uForm σ a d = 1) {w : Fin m → F} (hw : w ∈ perpPair σ a d) :
    ∃ e₁ ∈ perpPair σ a d, ∃ e₂ ∈ perpPair σ a d, uForm σ e₁ e₁ = 0 ∧ uForm σ e₂ e₂ = 0 ∧
      w = e₁ + e₂ := by
  have hu0 : uForm σ (0 : Fin m → F) 0 = 0 := uForm_zero_right 0
  by_cases hww : uForm σ w w = 0
  · exact ⟨w, hw, 0, (perpPair σ a d).zero_mem, hww, hu0, (add_zero w).symm⟩
  have hw0 : w ≠ 0 := by
    rintro rfl
    exact hww hu0
  obtain ⟨e, he, hee, hew⟩ :=
    exists_isotropic_mem_perpPair_uForm_ne_zero hσ htr hnorm hm haa hdd had hw hw0
  have hwe0 : uForm σ w e ≠ 0 := by
    rw [← uForm_conj σ hσ]
    exact (map_ne_zero σ).2 hew
  obtain ⟨c₀, hc₀⟩ := htr (uForm σ w w) (uForm_conj σ hσ w w)
  obtain ⟨c, h1⟩ : ∃ c : F, c * uForm σ w e = c₀ := ⟨c₀ / uForm σ w e, div_mul_cancel₀ c₀ hwe0⟩
  have h2 : σ c * uForm σ e w = σ c₀ := by rw [← uForm_conj σ hσ w e, ← map_mul, h1]
  refine ⟨w + c • e, (perpPair σ a d).add_mem hw ((perpPair σ a d).smul_mem c he),
    c • e, (perpPair σ a d).smul_mem c he, ?_, ?_, ?_⟩
  · simp only [uForm_add_left, uForm_add_right, uForm_smul_left, uForm_smul_right, hee]
    linear_combination h1 + h2 + hc₀ + CharTwo.add_self_eq_zero (uForm σ w w)
  · rw [uForm_smul_left, uForm_smul_right, hee, mul_zero, mul_zero]
  · rw [add_assoc, ← add_smul, CharTwo.add_self_eq_zero, zero_smul, add_zero]

theorem perpPair_addSubgroup_eq_bot_or [CharP F 2] (hσ : ∀ c, σ (σ c) = c)
    (htr : ∀ c, σ c = c → ∃ e, e + σ e = c) (hnorm : ∀ c, σ c = c → ∃ l, σ l * l = c)
    (hm : 4 ≤ m) {a d : Fin m → F} (haa : uForm σ a a = 0) (hdd : uForm σ d d = 0)
    (had : uForm σ a d = 1) (S : AddSubgroup (Fin m → F))
    (hSP : ∀ x ∈ S, x ∈ perpPair σ a d)
    (hS : ∀ v ∈ perpPair σ a d, uForm σ v v = 0 → ∀ x ∈ S, uForm σ v x ≠ 0 → ∀ c : F,
      c • v ∈ S) :
    S = ⊥ ∨ ∀ w ∈ perpPair σ a d, w ∈ S := by
  by_cases hbot : S = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨x₀, hx₀S, hx₀0⟩ : ∃ x₀ ∈ S, x₀ ≠ 0 := by
    by_contra hne
    exact hbot ((AddSubgroup.eq_bot_iff_forall S).2 fun x hx => by
      by_contra hx0
      exact hne ⟨x, hx, hx0⟩)
  have hS1 : ∀ v ∈ perpPair σ a d, uForm σ v v = 0 → ∀ x ∈ S, uForm σ v x ≠ 0 → v ∈ S :=
    fun v hv hvv x hx hvx => by simpa using hS v hv hvv x hx hvx 1
  obtain ⟨y₁, hy₁, hy₁y₁, hy₁x₀⟩ :=
    exists_isotropic_mem_perpPair_uForm_ne_zero hσ htr hnorm hm haa hdd had (hSP x₀ hx₀S) hx₀0
  have hy₁S : y₁ ∈ S := hS1 y₁ hy₁ hy₁y₁ x₀ hx₀S hy₁x₀
  have hy₁0 : y₁ ≠ 0 := by
    rintro rfl
    exact hy₁x₀ (by simp [uForm_eq])
  have hiso : ∀ v ∈ perpPair σ a d, uForm σ v v = 0 → v ∈ S := by
    intro v hv hvv
    by_cases hv0 : v = 0
    · rw [hv0]
      exact S.zero_mem
    obtain ⟨y₂, hy₂, hy₂y₂, hvy₂, hy₁y₂⟩ :=
      exists_isotropic_both_mem_perpPair hσ htr haa hdd had hv hy₁ hv0 hy₁0 hvv hy₁y₁
    have hy₂y₁ : uForm σ y₂ y₁ ≠ 0 := by
      rw [← uForm_conj σ hσ]
      exact (map_ne_zero σ).2 hy₁y₂
    exact hS1 v hv hvv y₂ (hS1 y₂ hy₂ hy₂y₂ y₁ hy₁S hy₂y₁) hvy₂
  intro w hw
  obtain ⟨e₁, he₁, e₂, he₂, he₁e₁, he₂e₂, rfl⟩ :=
    exists_isotropic_add_mem_perpPair hσ htr hnorm hm haa hdd had hw
  exact S.add_mem (hiso e₁ he₁ he₁e₁) (hiso e₂ he₂ he₂e₂)

theorem suGeomFacts_holds [CharP F 2] (hσ : ∀ c, σ (σ c) = c)
    (htr : ∀ c, σ c = c → ∃ e, e + σ e = c) (hnorm : ∀ c, σ c = c → ∃ l, σ l * l = c)
    (hm : 4 ≤ m) {a d : Fin m → F} (haa : uForm σ a a = 0) (hdd : uForm σ d d = 0)
    (had : uForm σ a d = 1) : SUGeomFacts σ a d where
  exists_iso := exists_isotropic_mem_perpPair hσ hnorm hm a d
  partner := exists_isotropic_partner_mem_perpPair hσ htr haa hdd had
  nonorth := exists_isotropic_mem_perpPair_uForm_ne_zero hσ htr hnorm hm haa hdd had
  both := exists_isotropic_both_mem_perpPair hσ htr haa hdd had
  sum := exists_isotropic_add_mem_perpPair hσ htr hnorm hm haa hdd had
  kl := perpPair_addSubgroup_eq_bot_or hσ htr hnorm hm haa hdd had

end ModelRank

end CFSG.Timmesfeld.Transvection
