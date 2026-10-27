module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.Quasithin.ModB

open Matrix

section Det

variable {F : Type} [Field F] {K : Type*} [Group K]

theorem restrict_one_eq (ρ : K →* GL (Fin 3) F) (E : Submodule F (Fin 3 → F))
    (hE : ∀ k : K, ∀ v ∈ E, (ρ k : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈ E) :
    (Matrix.mulVecLin ((ρ 1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)).restrict (hE 1) =
      LinearMap.id := by
  ext v
  simp

theorem restrict_mul_eq (ρ : K →* GL (Fin 3) F) (E : Submodule F (Fin 3 → F))
    (hE : ∀ k : K, ∀ v ∈ E, (ρ k : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈ E) (a b : K) :
    (Matrix.mulVecLin ((ρ (a * b) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)).restrict
            (hE (a * b)) =
      ((Matrix.mulVecLin (ρ a : Matrix (Fin 3) (Fin 3) F)).restrict (hE a)) ∘ₗ
        ((Matrix.mulVecLin (ρ b : Matrix (Fin 3) (Fin 3) F)).restrict (hE b)) := by
  ext v i
  show ((ρ (a * b) : Matrix (Fin 3) (Fin 3) F) *ᵥ (v : Fin 3 → F)) i =
    ((ρ a : Matrix (Fin 3) (Fin 3) F) *ᵥ ((ρ b : Matrix (Fin 3) (Fin 3) F) *ᵥ (v : Fin 3 → F))) i
  rw [map_mul, Units.val_mul, Matrix.mulVec_mulVec]

@[expose] noncomputable def detRestrict (ρ : K →* GL (Fin 3) F) (E : Submodule F (Fin 3 → F))
    (hE : ∀ k : K, ∀ v ∈ E, (ρ k : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈ E) : K →* Fˣ :=
  (({ toFun := fun k => LinearMap.det
        ((Matrix.mulVecLin (ρ k : Matrix (Fin 3) (Fin 3) F)).restrict (hE k))
      map_one' := by rw [restrict_one_eq]; exact LinearMap.det_id
      map_mul' := fun a b => by rw [restrict_mul_eq, LinearMap.det_comp] } : K →* F)).toHomUnits

theorem detRestrict_apply (ρ : K →* GL (Fin 3) F) (E : Submodule F (Fin 3 → F))
    (hE : ∀ k : K, ∀ v ∈ E, (ρ k : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈ E) (k : K) :
    ((detRestrict ρ E hE k : Fˣ) : F) =
      LinearMap.det ((Matrix.mulVecLin (ρ k : Matrix (Fin 3) (Fin 3) F)).restrict (hE k)) := rfl

theorem detRestrict_eq_one (N : Subgroup K) [N.Normal] (hperf : commutator (K ⧸ N) = ⊤)
    (ρ : K →* GL (Fin 3) F) (hN : ∀ n ∈ N, ρ n = 1) (E : Submodule F (Fin 3 → F))
    (hE : ∀ k : K, ∀ v ∈ E, (ρ k : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈ E) (k : K) :
    detRestrict ρ E hE k = 1 := by
  have hcomm : commutator K ≤ (detRestrict ρ E hE).ker :=
    Abelianization.commutator_subset_ker (detRestrict ρ E hE)
  have hNker : ∀ n ∈ N, detRestrict ρ E hE n = 1 := by
    intro n hn
    apply Units.ext
    rw [detRestrict_apply]
    have : (Matrix.mulVecLin ((ρ n : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)).restrict (hE n) =
        LinearMap.id := by
      ext v
      simp [hN n hn]
    rw [this]
    simp
  have hmap : (commutator K).map (QuotientGroup.mk' N) = commutator (K ⧸ N) := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective _
      (QuotientGroup.mk'_surjective N)]
  have hk : (QuotientGroup.mk' N k : K ⧸ N) ∈ (commutator K).map (QuotientGroup.mk' N) := by
    rw [hmap, hperf]
    trivial
  obtain ⟨c, hc, hck⟩ := hk
  have hn : c⁻¹ * k ∈ N := by
    have := hck
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at this
    simpa using this
  have : k = c * (c⁻¹ * k) := by group
  rw [this, map_mul, MonoidHom.mem_ker.mp (hcomm hc), hNker _ hn, one_mul]

end Det

section F4

variable {F : Type} [Field F] [Fintype F]

theorem f4_pow_three (hF : Fintype.card F = 4) {c : F} (hc : c ≠ 0) : c ^ 3 = 1 := by
  have := FiniteField.pow_card_sub_one_eq_one c hc
  rwa [hF] at this

theorem f4_exists_omega (hF : Fintype.card F = 4) : ∃ ω : F, ω ≠ 0 ∧ ω ≠ 1 := by
  classical
  by_contra hcon
  push Not at hcon
  have : Fintype.card F ≤ 2 := by
    have : (Finset.univ : Finset F) ⊆ {0, 1} := fun x _ => by
      by_cases h0 : x = 0
      · simp [h0]
      · simp [hcon x h0]
    calc Fintype.card F = (Finset.univ : Finset F).card := Finset.card_univ.symm
      _ ≤ ({0, 1} : Finset F).card := Finset.card_le_card this
      _ ≤ 2 := Finset.card_le_two
  omega

theorem f4_two_eq_zero (hF : Fintype.card F = 4) : (2 : F) = 0 := by
  have h4 : (4 : F) = 0 := by
    have := card_nsmul_eq_zero (G := F) (x := (1 : F))
    rw [hF] at this
    simpa using this
  have : (2 : F) * 2 = 0 := by rw [← h4]; norm_num
  exact mul_self_eq_zero.mp this

end F4

section Scalar

variable {F : Type} [Field F] [Fintype F]

theorem f4_omega_sq (hF : Fintype.card F = 4) {ω : F} (h0 : ω ≠ 0) (h1 : ω ≠ 1) :
    ω ^ 2 + ω + 1 = 0 := by
  have h3 := f4_pow_three hF h0
  have : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by
    have : (ω - 1) * (ω ^ 2 + ω + 1) = ω ^ 3 - 1 := by ring
    rw [this, h3, sub_self]
  rcases mul_eq_zero.mp this with h | h
  · exact absurd (sub_eq_zero.mp h) h1
  · exact h

end Scalar


section Lemmas

variable {F : Type} [Field F] [Fintype F]

theorem f4_cases (hF : Fintype.card F = 4) {c : F} (h0 : c ≠ 0) (h1 : c ≠ 1) (t : F) :
    t = 0 ∨ t = 1 ∨ t = c ∨ t = c + 1 := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨ht0, ht1, htc, htc1⟩ := hcon
  have h2 : (2 : F) = 0 := f4_two_eq_zero hF
  have hc1 : c + 1 ≠ 0 := by
    intro h
    apply h1
    linear_combination h - h2
  have hc2 : c + 1 ≠ 1 := fun h => h0 (by simpa using h)
  have hc3 : c + 1 ≠ c := fun h => by simp at h
  have hle : ({0, 1, c, c + 1, t} : Finset F).card ≤ Fintype.card F := Finset.card_le_univ _
  rw [hF] at hle
  have : ({0, 1, c, c + 1, t} : Finset F).card = 5 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_insert_of_notMem, Finset.card_singleton] <;>
    simp [h0.symm, h1.symm, hc1.symm, hc2.symm, hc3.symm, ht0.symm, ht1.symm, htc.symm,
      htc1.symm]
  omega


theorem eq_one_of_pow_two_pow (hF : Fintype.card F = 4) {l : F} {k : ℕ} (h : l ^ 2 ^ k = 1) :
    l = 1 := by
  have hl0 : l ≠ 0 := by
    rintro rfl
    simp at h
  have h3 := f4_pow_three hF hl0
  have hd : orderOf l ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h
  have hd3 : orderOf l ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  have hc : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left _ (by norm_num)
  have := Nat.dvd_gcd hd hd3
  rw [hc.gcd_eq_one] at this
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp this)

theorem line_of_card_four (hF : Fintype.card F = 4) (A : AddSubgroup (Fin 3 → F))
    (hA : Nat.card A = 4) {c : F} (hc0 : c ≠ 0) (hc1 : c ≠ 1) (hc : ∀ x ∈ A, c • x ∈ A)
    {a : Fin 3 → F} (ha : a ∈ A) (ha0 : a ≠ 0) : ∀ x : Fin 3 → F, x ∈ A ↔ ∃ t : F, x = t • a := by
  have hsm : ∀ t : F, t • a ∈ A := by
    intro t
    rcases f4_cases hF hc0 hc1 t with rfl | rfl | rfl | rfl
    · simp [A.zero_mem]
    · simpa using ha
    · exact hc a ha
    · rw [add_smul, one_smul]
      exact A.add_mem (hc a ha) ha
  let f : F → A := fun t => ⟨t • a, hsm t⟩
  have hinj : Function.Injective f := fun s t hst =>
    smul_left_injective F ha0 (congrArg Subtype.val hst)
  have hbij : Function.Bijective f :=
    hinj.bijective_of_nat_card_le (by rw [hA, Nat.card_eq_fintype_card, hF])
  intro x
  constructor
  · intro hx
    obtain ⟨t, ht⟩ := hbij.2 ⟨x, hx⟩
    exact ⟨t, (congrArg Subtype.val ht).symm⟩
  · rintro ⟨t, rfl⟩
    exact hsm t

theorem pow_eq_one_dvd_three (hF : Fintype.card F = 4) {μ : F} (h0 : μ ≠ 0) (h1 : μ ≠ 1) {d : ℕ}
    (h : μ ^ d = 1) : 3 ∣ d := by
  have h3 := f4_pow_three hF h0
  have hd : orderOf μ ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  rcases (Nat.dvd_prime Nat.prime_three).1 hd with h' | h'
  · exact absurd (orderOf_eq_one_iff.mp h') h1
  · rw [← h']
    exact orderOf_dvd_of_pow_eq_one h

end Lemmas

section Scalar2

variable {F : Type} [Field F] [Fintype F] {K : Type*} [Group K]

open Module in
theorem scalar_of_central (hF : Fintype.card F = 4) (N : Subgroup K) [N.Normal]
    (hperf : commutator (K ⧸ N) = ⊤) (ρ : K →* GL (Fin 3) F) (hN : ∀ n ∈ N, ρ n = 1)
    (z : K) (hz1 : ρ z ≠ 1) (hz3 : ρ z ^ 3 = 1) (hc : ∀ k, ρ z * ρ k = ρ k * ρ z) :
    ∃ c : F, c ≠ 0 ∧ c ≠ 1 ∧ ∀ v, (ρ z : Matrix (Fin 3) (Fin 3) F) *ᵥ v = c • v := by
  obtain ⟨ω, hω0, hω1⟩ := f4_exists_omega hF
  have hω2 := f4_omega_sq hF hω0 hω1
  have hω3 := f4_pow_three hF hω0
  have h3 : (3 : F) = 1 := by
    have : (3 : F) = 2 + 1 := by norm_num
    rw [this, f4_two_eq_zero hF, zero_add]
  set g : Matrix (Fin 3) (Fin 3) F := (ρ z : Matrix (Fin 3) (Fin 3) F) with hg
  have hg3 : ∀ v, g *ᵥ (g *ᵥ (g *ᵥ v)) = v := by
    intro v
    have : g * g * g = 1 := by
      have := congrArg (fun u : GL (Fin 3) F => (u : Matrix (Fin 3) (Fin 3) F)) hz3
      simpa [pow_succ, hg] using this
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, this, Matrix.one_mulVec]
  let E : F → Submodule F (Fin 3 → F) := fun μ => Module.End.eigenspace (Matrix.mulVecLin g) μ
  have hEmem : ∀ μ v, v ∈ E μ ↔ g *ᵥ v = μ • v := fun μ v => by
    simp [E]
  have hEinv : ∀ μ, ∀ k : K, ∀ v ∈ E μ, (ρ k : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈ E μ := by
    intro μ k v hv
    rw [hEmem] at hv ⊢
    have hcomm : g * (ρ k : Matrix (Fin 3) (Fin 3) F) = (ρ k : Matrix (Fin 3) (Fin 3) F) * g := by
      have := congrArg (fun u : GL (Fin 3) F => (u : Matrix (Fin 3) (Fin 3) F)) (hc k)
      simpa using this
    rw [Matrix.mulVec_mulVec, hcomm, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul]
  have hdet : ∀ μ, μ ^ Module.finrank F (E μ) = 1 := by
    intro μ
    have h1 := detRestrict_eq_one N hperf ρ hN (E μ) (hEinv μ) z
    have h2 : ((detRestrict ρ (E μ) (hEinv μ) z : Fˣ) : F) = 1 := by rw [h1]; rfl
    rw [detRestrict_apply] at h2
    have h3' : (Matrix.mulVecLin (ρ z : Matrix (Fin 3) (Fin 3) F)).restrict (hEinv μ z) =
        μ • LinearMap.id := by
      apply LinearMap.ext
      intro v
      apply Subtype.ext
      show (Matrix.mulVecLin g) (v : Fin 3 → F) = μ • (v : Fin 3 → F)
      rw [Matrix.mulVecLin_apply]
      exact (hEmem μ v).1 v.2
    rw [h3', LinearMap.det_smul, LinearMap.det_id, mul_one] at h2
    exact h2
  have hle : ∀ μ, Module.finrank F (E μ) ≤ 3 := fun μ => by
    have := Submodule.finrank_le (E μ)
    simpa using this
  have hdich : ∀ μ : F, μ ≠ 0 → μ ≠ 1 → E μ = ⊥ ∨ E μ = ⊤ := by
    intro μ h0 h1
    have hd := pow_eq_one_dvd_three hF h0 h1 (hdet μ)
    have hl := hle μ
    have : Module.finrank F (E μ) = 0 ∨ Module.finrank F (E μ) = 3 := by omega
    rcases this with h | h
    · left
      exact Submodule.finrank_eq_zero.mp h
    · right
      apply Submodule.eq_top_of_finrank_eq
      rw [h]
      simp
  have hω'0 : ω ^ 2 ≠ 0 := pow_ne_zero 2 hω0
  have hω'1 : ω ^ 2 ≠ 1 := by
    intro h
    apply hω1
    have : ω = ω ^ 3 / ω ^ 2 := by field_simp
    rw [this, hω3, h]
    simp
  have hcycle : E ω = ⊥ → E (ω ^ 2) = ⊥ → ∀ p q r : Fin 3 → F, g *ᵥ p = q → g *ᵥ q = r →
      g *ᵥ r = p → g *ᵥ p = p := by
    intro hb hb' p q r hpq hqr hrp
    have huω : p + (ω ^ 2) • q + ω • r ∈ E ω := by
      rw [hEmem, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
        hrp, hqr, hpq]
      ext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination (-(q i)) * hω3
    have huω' : p + ω • q + (ω ^ 2) • r ∈ E (ω ^ 2) := by
      rw [hEmem, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
        hrp, hqr, hpq]
      ext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination (-(q i) - ω * r i) * hω3
    rw [hb] at huω
    rw [hb'] at huω'
    have h0 : p + (ω ^ 2) • q + ω • r = 0 := (Submodule.mem_bot F).1 huω
    have h0' : p + ω • q + (ω ^ 2) • r = 0 := (Submodule.mem_bot F).1 huω'
    have hp : p = p + q + r := by
      ext i
      have e1 := congrFun h0 i
      have e2 := congrFun h0' i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e1 e2 ⊢
      linear_combination (-1 : F) * e1 + (-1 : F) * e2 + (p i - q i - r i) * h3 +
        (q i + r i) * hω2
    have hfix : g *ᵥ (p + q + r) = p + q + r := by
      rw [Matrix.mulVec_add, Matrix.mulVec_add, hrp, hqr, hpq]
      abel
    calc g *ᵥ p = g *ᵥ (p + q + r) := congrArg (g *ᵥ ·) hp
      _ = p + q + r := hfix
      _ = p := hp.symm
  rcases hdich ω hω0 hω1 with hb | ht
  · rcases hdich (ω ^ 2) hω'0 hω'1 with hb' | ht'
    · exfalso
      apply hz1
      have key : ∀ v, g *ᵥ v = v := fun v =>
        hcycle hb hb' v (g *ᵥ v) (g *ᵥ (g *ᵥ v)) rfl rfl (hg3 v)
      apply Units.ext
      apply Matrix.toLin'.injective
      exact LinearMap.ext fun v => by simpa [Matrix.toLin'_apply] using key v
    · refine ⟨ω ^ 2, hω'0, hω'1, fun v => ?_⟩
      exact (hEmem _ v).1 (by rw [ht']; trivial)
  · refine ⟨ω, hω0, hω1, fun v => ?_⟩
    exact (hEmem _ v).1 (by rw [ht]; trivial)

end Scalar2



section Unip

variable {F : Type} [Field F] [Fintype F]

theorem eigen_one_of_pgroup (hF : Fintype.card F = 4) {S : Type*} [Group S] (hS : IsPGroup 2 S)
    (ρ : S →* GL (Fin 3) F) {a : Fin 3 → F} (ha : a ≠ 0) (s : S) {l : F}
    (h : (ρ s : Matrix (Fin 3) (Fin 3) F) *ᵥ a = l • a) : l = 1 := by
  obtain ⟨k, hk⟩ := hS s
  have hpow : ∀ n : ℕ, ((ρ s : Matrix (Fin 3) (Fin 3) F) ^ n) *ᵥ a = l ^ n • a := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, ih, smul_smul, pow_succ']
  have h1 : (ρ s : Matrix (Fin 3) (Fin 3) F) ^ 2 ^ k = 1 := by
    have : (ρ s) ^ 2 ^ k = 1 := by rw [← map_pow, hk, map_one]
    have := congrArg (fun u : GL (Fin 3) F => (u : Matrix (Fin 3) (Fin 3) F)) this
    simpa using this
  have := hpow (2 ^ k)
  rw [h1, Matrix.one_mulVec] at this
  have h2 : l ^ 2 ^ k = 1 := by
    have : (1 : F) • a = l ^ 2 ^ k • a := by rw [one_smul]; exact this
    exact (smul_left_injective F ha this).symm
  exact eq_one_of_pow_two_pow hF h2

theorem commute_of_fixing (hF : Fintype.card F = 4) {S : Type*} [Group S] (hS : IsPGroup 2 S)
    (ρ : S →* GL (Fin 3) F) {a₁ a₂ : Fin 3 → F} (hli : LinearIndependent F ![a₁, a₂])
    (h₁ : ∀ s, (ρ s : Matrix (Fin 3) (Fin 3) F) *ᵥ a₁ = a₁)
    (h₂ : ∀ s, (ρ s : Matrix (Fin 3) (Fin 3) F) *ᵥ a₂ = a₂) (s t : S) :
    ρ s * ρ t = ρ t * ρ s := by
  obtain ⟨a₃, hli3⟩ := exists_linearIndependent_cons_of_lt_finrank hli (by simp)
  let b := basisOfLinearIndependentOfCardEqFinrank hli3 (by simp)
  have hb0 : b 0 = a₃ := by simp [b]
  have hb1 : b 1 = a₁ := by simp [b]
  have hb2 : b 2 = a₂ := by simp [b]
  have ha₁ : a₁ ≠ 0 := hli.ne_zero 0
  have hrepr : ∀ x : Fin 3 → F, x = (b.repr x 0) • a₃ + (b.repr x 1) • a₁ + (b.repr x 2) • a₂ := by
    intro x
    conv_lhs => rw [← b.sum_repr x]
    rw [Fin.sum_univ_three, hb0, hb1, hb2]
  let V₂ : Submodule F (Fin 3 → F) := Submodule.span F {a₁, a₂}
  have hform : ∀ u : S, ∀ x : Fin 3 → F, (ρ u : Matrix (Fin 3) (Fin 3) F) *ᵥ x - x =
      (b.repr x 0) • ((ρ u : Matrix (Fin 3) (Fin 3) F) *ᵥ a₃ - a₃) := by
    intro u x
    conv_lhs => rw [hrepr x]
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, h₁ u, h₂ u]
    module
  have hw : ∀ u : S, (ρ u : Matrix (Fin 3) (Fin 3) F) *ᵥ a₃ - a₃ ∈ V₂ := by
    intro u
    set w := (ρ u : Matrix (Fin 3) (Fin 3) F) *ᵥ a₃ - a₃ with hwdef
    by_cases hw0 : w = 0
    · rw [hw0]; exact V₂.zero_mem
    have hgw : (ρ u : Matrix (Fin 3) (Fin 3) F) *ᵥ w = (1 + b.repr w 0) • w := by
      have := hform u w
      rw [← hwdef] at this
      rw [add_smul, one_smul, ← this]
      abel
    have hl := eigen_one_of_pgroup hF hS ρ hw0 u hgw
    have h0 : b.repr w 0 = 0 := by
      have : (1 : F) + b.repr w 0 = 1 + 0 := by rw [hl, add_zero]
      exact add_left_cancel this
    have := hrepr w
    rw [h0, zero_smul, zero_add] at this
    rw [this]
    exact Submodule.mem_span_pair.2 ⟨_, _, rfl⟩
  have hfix : ∀ u : S, ∀ y ∈ V₂, (ρ u : Matrix (Fin 3) (Fin 3) F) *ᵥ y = y := by
    intro u y hy
    obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.1 hy
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, h₁ u, h₂ u]
  have hN : ∀ u : S, ∀ x, (ρ u : Matrix (Fin 3) (Fin 3) F) *ᵥ x - x ∈ V₂ := fun u x => by
    rw [hform u x]
    exact V₂.smul_mem _ (hw u)
  apply Units.ext
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  simp only [Matrix.toLin'_apply, Units.val_mul, ← Matrix.mulVec_mulVec]
  have e1 : (ρ t : Matrix (Fin 3) (Fin 3) F) *ᵥ x = x + ((ρ t : Matrix (Fin 3) (Fin 3) F) *ᵥ x - x) := by
    abel
  have e2 : (ρ s : Matrix (Fin 3) (Fin 3) F) *ᵥ x = x + ((ρ s : Matrix (Fin 3) (Fin 3) F) *ᵥ x - x) := by
    abel
  rw [e1, e2, Matrix.mulVec_add, Matrix.mulVec_add, hfix s _ (hN t x), hfix t _ (hN s x)]
  abel

end Unip

end CFSG.Quasithin.ModB
