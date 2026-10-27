module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148VHeisTorus
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
import CFSG.RankThree.PartTwo.Sec4.Ronan148VElation
import CFSG.RankThree.PartTwo.Sec4.LThreePiTypes

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148V

open Matrix CFSG.RankThree.PartTwo.Sec4 CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ComponentClassification

variable {F : Type} [Field F]

@[expose] def torusSL (m : ℕ) : Subgroup (SpecialLinearGroup (Fin 3) F) where
  carrier := {g | ∃ a b e : Fˣ, a ^ m = 1 ∧ b ^ m = 1 ∧ e ^ m = 1 ∧
    (g : Matrix (Fin 3) (Fin 3) F) = diagonal ![(a : F), b, e]}
  mul_mem' := by
    rintro g g' ⟨a, b, e, ha, hb, he, hg⟩ ⟨a', b', e', ha', hb', he', hg'⟩
    refine ⟨a * a', b * b', e * e', by rw [mul_pow, ha, ha', one_mul],
      by rw [mul_pow, hb, hb', one_mul], by rw [mul_pow, he, he', one_mul], ?_⟩
    rw [Matrix.SpecialLinearGroup.coe_mul, hg, hg', diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i <;> simp
  one_mem' := ⟨1, 1, 1, one_pow _, one_pow _, one_pow _, by
    rw [Matrix.SpecialLinearGroup.coe_one, ← diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp⟩
  inv_mem' := by
    rintro g ⟨a, b, e, ha, hb, he, hg⟩
    refine ⟨a⁻¹, b⁻¹, e⁻¹, by rw [inv_pow, ha, inv_one], by rw [inv_pow, hb, inv_one],
      by rw [inv_pow, he, inv_one], ?_⟩
    have h1 : (g : Matrix (Fin 3) (Fin 3) F) * diagonal ![((a⁻¹ : Fˣ) : F), (b⁻¹ : Fˣ),
        (e⁻¹ : Fˣ)] = 1 := by
      rw [hg, diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext i
      fin_cases i <;> simp
    calc ((g⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
        = ((g⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
          ((g : Matrix (Fin 3) (Fin 3) F) * diagonal ![((a⁻¹ : Fˣ) : F), (b⁻¹ : Fˣ),
            (e⁻¹ : Fˣ)]) := by rw [h1, Matrix.mul_one]
      _ = _ := by
          rw [← Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
            Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul]

theorem mem_torusSL {m : ℕ} {g : SpecialLinearGroup (Fin 3) F} :
    g ∈ torusSL m ↔ ∃ a b e : Fˣ, a ^ m = 1 ∧ b ^ m = 1 ∧ e ^ m = 1 ∧
      (g : Matrix (Fin 3) (Fin 3) F) = diagonal ![(a : F), b, e] :=
  Iff.rfl

@[expose] def diagTorus (m : ℕ) : Subgroup (projectiveSL 3 F) :=
  (torusSL (F := F) m).map (proj 3 F)

theorem not_three_dvd_card_diagTorus [Finite F] {m : ℕ} (hm : Nat.Coprime m 3) :
    ¬ 3 ∣ Nat.card (diagTorus (F := F) m) := by
  intro h3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 3 h3
  obtain ⟨g, ⟨a, b, e, ha, hb, he, hg⟩, hgu⟩ := u.2
  have hgm : g ^ m = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, hg, diagonal_pow, Matrix.SpecialLinearGroup.coe_one,
      ← diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp [← Units.val_pow_eq_pow_val, ha, hb, he]
  have hum : u ^ m = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, ← hgu, ← map_pow, hgm, map_one, Subgroup.coe_one]
  have := orderOf_dvd_of_pow_eq_one hum
  rw [hu] at this
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (Nat.Coprime.symm hm) this

theorem coe_eq_diagUnits {g : SpecialLinearGroup (Fin 3) F} {a b e : Fˣ}
    (hg : (g : Matrix (Fin 3) (Fin 3) F) = diagonal ![(a : F), b, e]) :
    (g : Matrix (Fin 3) (Fin 3) F) =
      ((diagUnits a b e : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
  rw [hg, coe_diagUnits]

theorem conj_diagUnits_eq (w₀ w₁ w₂ a b e : Fˣ) (k : ℕ) :
    (cycThree ^ k * diagUnits w₀ w₁ w₂) * diagUnits a b e *
        (cycThree ^ k * diagUnits w₀ w₁ w₂)⁻¹ =
      cycThree ^ k * diagUnits a b e * (cycThree ^ k)⁻¹ := by
  have hc : diagUnits w₀ w₁ w₂ * diagUnits a b e = diagUnits a b e * diagUnits w₀ w₁ w₂ := by
    rw [diagUnits_mul, diagUnits_mul, mul_comm w₀, mul_comm w₁, mul_comm w₂]
  calc (cycThree ^ k * diagUnits w₀ w₁ w₂) * diagUnits a b e *
        (cycThree ^ k * diagUnits w₀ w₁ w₂)⁻¹
      = cycThree ^ k * (diagUnits w₀ w₁ w₂ * diagUnits a b e) * (diagUnits w₀ w₁ w₂)⁻¹ *
          (cycThree ^ k)⁻¹ := by group
    _ = cycThree ^ k * diagUnits a b e * (cycThree ^ k)⁻¹ := by rw [hc]; group

theorem cycThree_sq_conj_diagUnits (a b e : Fˣ) :
    cycThree ^ 2 * diagUnits a b e * (cycThree ^ 2)⁻¹ = diagUnits b e a := by
  calc cycThree ^ 2 * diagUnits a b e * (cycThree ^ 2)⁻¹ =
      cycThree * (cycThree * diagUnits a b e * cycThree⁻¹) * cycThree⁻¹ := by
        rw [pow_two, _root_.mul_inv_rev]
        group
    _ = diagUnits b e a := by rw [cycThree_conj_diagUnits, cycThree_conj_diagUnits]

theorem slConjugation_mem_torusSL {m k : ℕ} (hk : k < 3) (w₀ w₁ w₂ : Fˣ)
    {g : SpecialLinearGroup (Fin 3) F} (hg : g ∈ torusSL m) :
    CatalogueBHigherLinearAction.slConjugation 3 F (cycThree ^ k * diagUnits w₀ w₁ w₂) g ∈
      torusSL m := by
  obtain ⟨a, b, e, ha, hb, he, hge⟩ := hg
  rw [mem_torusSL, coe_slConjugation, coe_eq_diagUnits hge, ← Units.val_mul, ← Units.val_mul,
    conj_diagUnits_eq]
  interval_cases k
  · exact ⟨a, b, e, ha, hb, he, by rw [pow_zero, one_mul, inv_one, mul_one, coe_diagUnits]⟩
  · exact ⟨e, a, b, he, ha, hb, by rw [pow_one, cycThree_conj_diagUnits, coe_diagUnits]⟩
  · exact ⟨b, e, a, hb, he, ha, by rw [cycThree_sq_conj_diagUnits, coe_diagUnits]⟩

theorem map_mem_torusSL {m : ℕ} (ρ : F ≃+* F) {g : SpecialLinearGroup (Fin 3) F}
    (hg : g ∈ torusSL m) : SpecialLinearGroup.map ρ.toRingHom g ∈ torusSL m := by
  obtain ⟨a, b, e, ha, hb, he, hge⟩ := hg
  refine ⟨Units.map (ρ : F →* F) a, Units.map (ρ : F →* F) b, Units.map (ρ : F →* F) e,
    by rw [← map_pow, ha, map_one], by rw [← map_pow, hb, map_one],
    by rw [← map_pow, he, map_one], ?_⟩
  rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, hge,
    diagonal_map (map_zero _)]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem conjAut_mem_diagTorus {m k : ℕ} (hk : k < 3) (w₀ w₁ w₂ : Fˣ) {u : projectiveSL 3 F}
    (hu : u ∈ diagTorus (F := F) m) :
    conjAut 3 F (cycThree ^ k * diagUnits w₀ w₁ w₂) u ∈ diagTorus (F := F) m := by
  obtain ⟨g, hg, rfl⟩ := hu
  rw [conjAut_proj]
  exact ⟨_, slConjugation_mem_torusSL hk w₀ w₁ w₂ hg, rfl⟩

theorem fieldAut_mem_diagTorus {m : ℕ} (ρ : F ≃+* F) {u : projectiveSL 3 F}
    (hu : u ∈ diagTorus (F := F) m) : fieldAut 3 F ρ u ∈ diagTorus (F := F) m := by
  obtain ⟨g, hg, rfl⟩ := hu
  rw [fieldAut_proj]
  exact ⟨_, map_mem_torusSL ρ hg, rfl⟩

theorem eq_one_of_commute_cycThree_pow {m k : ℕ} (hm : Nat.Coprime m 3) (hk : k = 1 ∨ k = 2)
    {w₀ w₁ w₂ : Fˣ} {M : SpecialLinearGroup (Fin 3) F}
    (hM : (M : Matrix (Fin 3) (Fin 3) F) =
      ((cycThree ^ k * diagUnits w₀ w₁ w₂ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))
    {u : projectiveSL 3 F} (hu : u ∈ diagTorus (F := F) m) (hc : u * proj 3 F M = proj 3 F M * u) :
    u = 1 := by
  obtain ⟨g, ⟨a, b, e, ha, hb, he, hge⟩, rfl⟩ := hu
  obtain ⟨ν, hν0, hν⟩ := exists_smul_of_proj_eq (A := g) (B := M * g * M⁻¹) (by
    rw [map_mul, map_mul, map_inv, ← hc, mul_inv_cancel_right])
  have hconj : ((M * g * M⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      ((cycThree ^ k * diagUnits a b e * (cycThree ^ k)⁻¹ : GL (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) := by
    have hMi : ((M⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        (((cycThree ^ k * diagUnits w₀ w₁ w₂)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
      have h1 : (M : Matrix (Fin 3) (Fin 3) F) *
          (((cycThree ^ k * diagUnits w₀ w₁ w₂)⁻¹ : GL (Fin 3) F) :
            Matrix (Fin 3) (Fin 3) F) = 1 := by
        rw [hM, ← Units.val_mul, mul_inv_cancel, Units.val_one]
      calc ((M⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
          = ((M⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
            ((M : Matrix (Fin 3) (Fin 3) F) *
              (((cycThree ^ k * diagUnits w₀ w₁ w₂)⁻¹ : GL (Fin 3) F) :
                Matrix (Fin 3) (Fin 3) F)) := by rw [h1, Matrix.mul_one]
        _ = _ := by
            rw [← Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
              Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul]
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hM, hMi,
      coe_eq_diagUnits hge, ← Units.val_mul, ← Units.val_mul, conj_diagUnits_eq]
  rw [hconj, coe_eq_diagUnits hge] at hν
  have hent : ∀ i : Fin 3, ((cycThree ^ k * diagUnits a b e * (cycThree ^ k)⁻¹ : GL (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) i i = ν * ((diagUnits a b e : GL (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) i i := fun i => by
    rw [hν]
    rfl
  have hscalar : (a : F) = b ∧ (b : F) = e := by
    rcases hk with rfl | rfl
    · have e0 := hent 0
      have e1 := hent 1
      have e2 := hent 2
      rw [pow_one, cycThree_conj_diagUnits] at e0 e1 e2
      simp only [coe_diagUnits, diagonal_apply_eq, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at e0 e1 e2
      exact eq_of_shift_eq_mul hm (by rw [← Units.val_pow_eq_pow_val, ha, Units.val_one])
        (by rw [← Units.val_pow_eq_pow_val, he, Units.val_one]) e0 e1 e2
    · have e0 := hent 0
      have e1 := hent 1
      have e2 := hent 2
      rw [cycThree_sq_conj_diagUnits] at e0 e1 e2
      simp only [coe_diagUnits, diagonal_apply_eq, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at e0 e1 e2
      obtain ⟨h1, h2⟩ := eq_of_shift_eq_mul (a := (a : F)) (b := (e : F)) (e := (b : F)) hm
        (by rw [← Units.val_pow_eq_pow_val, ha, Units.val_one])
        (by rw [← Units.val_pow_eq_pow_val, hb, Units.val_one]) e0 e2 e1
      exact ⟨h1.trans h2, h2.symm⟩
  obtain ⟨hab, hbe⟩ := hscalar
  have hg1 : (g : Matrix (Fin 3) (Fin 3) F) = (a : F) • (1 : Matrix (Fin 3) (Fin 3) F) := by
    rw [hge]
    ext i j
    by_cases hij : i = j
    · subst hij
      fin_cases i <;> simp [hab, hbe]
    · simp [diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
  exact proj_eq_one_of_eq_smul_one hg1

theorem coe_theta_diag (k : ℕ) (w₀ w₁ w₂ : Fˣ) (ρ : F ≃+* F) {X : SpecialLinearGroup (Fin 3) F}
    {a b e : Fˣ} (hX : (X : Matrix (Fin 3) (Fin 3) F) = diagonal ![(a : F), b, e]) :
    (CatalogueBHigherLinearAction.slConjugation 3 F (cycThree ^ k * diagUnits w₀ w₁ w₂)
        (SpecialLinearGroup.map ρ.toRingHom X) : Matrix (Fin 3) (Fin 3) F) =
      ((cycThree ^ k * diagUnits (Units.map (ρ : F →* F) a) (Units.map (ρ : F →* F) b)
        (Units.map (ρ : F →* F) e) * (cycThree ^ k)⁻¹ : GL (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F) := by
  have hmap : ((SpecialLinearGroup.map ρ.toRingHom X : SpecialLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) = ((diagUnits (Units.map (ρ : F →* F) a)
        (Units.map (ρ : F →* F) b) (Units.map (ρ : F →* F) e) : GL (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F) := by
    rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, hX,
      diagonal_map (map_zero _), coe_diagUnits]
    congr 1
    funext i
    fin_cases i <;> rfl
  rw [coe_slConjugation, hmap, ← Units.val_mul, ← Units.val_mul, conj_diagUnits_eq]

theorem exists_fixed_diagTorus {m k : ℕ} (hm : Nat.Coprime m 3) (hk : k = 1 ∨ k = 2)
    (w₀ w₁ w₂ : Fˣ) (ρ : F ≃+* F) (hρ3 : ∀ x, ρ (ρ (ρ x)) = x) {lam : Fˣ} (hlm : lam ^ m = 1)
    (hρl : ρ lam ≠ lam) :
    ∃ u ∈ diagTorus (F := F) m, u ≠ 1 ∧
      conjAut 3 F (cycThree ^ k * diagUnits w₀ w₁ w₂) (fieldAut 3 F ρ u) = u := by
  set h : GL (Fin 3) F := cycThree ^ k * diagUnits w₀ w₁ w₂ with hh
  set θ : SpecialLinearGroup (Fin 3) F →* SpecialLinearGroup (Fin 3) F :=
    (CatalogueBHigherLinearAction.slConjugation 3 F h).toMonoidHom.comp
      (SpecialLinearGroup.map ρ.toRingHom) with hθ
  have hθapp : ∀ X, θ X = CatalogueBHigherLinearAction.slConjugation 3 F h
      (SpecialLinearGroup.map ρ.toRingHom X) := fun X => rfl
  have hθproj : ∀ X, conjAut 3 F h (fieldAut 3 F ρ (proj 3 F X)) = proj 3 F (θ X) := by
    intro X
    rw [fieldAut_proj, conjAut_proj]
    rfl
  have hk3 : k < 3 := by omega
  have hθT : ∀ X ∈ torusSL (F := F) m, θ X ∈ torusSL m := fun X hX =>
    slConjugation_mem_torusSL hk3 w₀ w₁ w₂ (map_mem_torusSL ρ hX)
  have hdet : (diagonal ![(lam : F), ((lam⁻¹ : Fˣ) : F), 1]).det = 1 := by
    rw [det_diagonal, Fin.prod_univ_three]
    simp
  set t : SpecialLinearGroup (Fin 3) F := ⟨diagonal ![(lam : F), ((lam⁻¹ : Fˣ) : F), 1], hdet⟩
    with ht
  have htT : t ∈ torusSL (F := F) m :=
    ⟨lam, lam⁻¹, 1, hlm, by rw [inv_pow, hlm, inv_one], one_pow _, by simp [ht]⟩
  have hρ0 : ∀ x : F, x ≠ 0 → ρ x ≠ 0 := fun x hx h0 =>
    hx ((map_eq_zero_iff ρ ρ.injective).mp h0)
  have hl0 : (lam : F) ≠ 0 := lam.ne_zero
  set N := t * θ t * θ (θ t) with hN
  have hNT : N ∈ torusSL (F := F) m :=
    mul_mem (mul_mem htT (hθT _ htT)) (hθT _ (hθT _ htT))
  have hc : ∀ (k' : ℕ), k' = 1 ∨ k' = 2 → ∀ X : SpecialLinearGroup (Fin 3) F, ∀ a b e : Fˣ,
      (X : Matrix (Fin 3) (Fin 3) F) = diagonal ![(a : F), b, e] →
      ((CatalogueBHigherLinearAction.slConjugation 3 F (cycThree ^ k' * diagUnits w₀ w₁ w₂)
        (SpecialLinearGroup.map ρ.toRingHom X) : SpecialLinearGroup (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F) =
        if k' = 1 then diagonal ![ρ e, ρ a, ρ b] else diagonal ![ρ b, ρ e, ρ a] := by
    intro k' hk' X a b e hX
    rw [coe_theta_diag k' w₀ w₁ w₂ ρ hX]
    rcases hk' with rfl | rfl
    · rw [if_pos rfl, pow_one, cycThree_conj_diagUnits, coe_diagUnits]
      rfl
    · rw [if_neg (by norm_num), cycThree_sq_conj_diagUnits, coe_diagUnits]
      rfl
  have hcomm : ∀ X Y : SpecialLinearGroup (Fin 3) F, X ∈ torusSL (F := F) m →
      Y ∈ torusSL (F := F) m → X * Y = Y * X := by
    rintro X Y ⟨a, b, e, -, -, -, hX⟩ ⟨a', b', e', -, -, -, hY⟩
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hX, hY,
      diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  have hdiag : ∃ (n₀ n₁ n₂ : F), (N : Matrix (Fin 3) (Fin 3) F) = diagonal ![n₀, n₁, n₂] ∧
      θ (θ (θ t)) = t ∧ ¬ (n₀ = n₁ ∧ n₁ = n₂) := by
    have hinv : ((lam⁻¹ : Fˣ) : F) = (lam : F)⁻¹ := Units.val_inv_eq_inv_val lam
    have hρinv : ∀ x : F, ρ x⁻¹ = (ρ x)⁻¹ := fun x => map_inv₀ ρ x
    rcases hk with rfl | rfl
    ·
      have h1 := hc 1 (Or.inl rfl) t lam lam⁻¹ 1 rfl
      rw [if_pos rfl] at h1
      have h1' : ((θ t : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
          diagonal ![((1 : Fˣ) : F), (Units.map (ρ : F →* F) lam : Fˣ),
            (Units.map (ρ : F →* F) lam⁻¹ : Fˣ)] := by
        rw [hθapp, h1]
        simp
      have h2 := hc 1 (Or.inl rfl) (θ t) 1 (Units.map (ρ : F →* F) lam)
        (Units.map (ρ : F →* F) lam⁻¹) h1'
      rw [if_pos rfl, ← hθapp] at h2
      have h2' : ((θ (θ t) : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
          diagonal ![(Units.map (ρ : F →* F) (Units.map (ρ : F →* F) lam⁻¹) : F),
            ((1 : Fˣ) : F), (Units.map (ρ : F →* F) (Units.map (ρ : F →* F) lam) : F)] := by
        rw [h2]
        simp
      have h3 := hc 1 (Or.inl rfl) (θ (θ t)) _ _ _ h2'
      rw [if_pos rfl, ← hθapp] at h3
      refine ⟨(lam : F) * (ρ (ρ (lam : F)))⁻¹, (lam : F)⁻¹ * ρ lam, (ρ lam)⁻¹ * ρ (ρ lam),
        ?_, ?_, ?_⟩
      · rw [hN, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, h1', h2']
        simp only [ht, diagonal_mul_diagonal]
        congr 1
        funext i
        fin_cases i <;> simp [hinv, hρinv] <;> ring
      · apply Subtype.ext
        rw [h3]
        simp [ht, hρ3, hinv, hρinv]
      · intro hc'
        apply not_const_norm_one ρ hm hl0 (by rw [← Units.val_pow_eq_pow_val, hlm, Units.val_one])
          hρl
        obtain ⟨e1, e2⟩ := hc'
        constructor
        · rw [div_eq_mul_inv, div_eq_mul_inv, e1, mul_comm]
        · rw [div_eq_mul_inv, div_eq_mul_inv, mul_comm, e2, mul_comm]
    ·
      have h1 := hc 2 (Or.inr rfl) t lam lam⁻¹ 1 rfl
      rw [if_neg (by norm_num)] at h1
      have h1' : ((θ t : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
          diagonal ![(Units.map (ρ : F →* F) lam⁻¹ : F), ((1 : Fˣ) : F),
            (Units.map (ρ : F →* F) lam : F)] := by
        rw [hθapp, h1]
        simp
      have h2 := hc 2 (Or.inr rfl) (θ t) _ _ _ h1'
      rw [if_neg (by norm_num), ← hθapp] at h2
      have h2' : ((θ (θ t) : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
          diagonal ![((1 : Fˣ) : F), (Units.map (ρ : F →* F) (Units.map (ρ : F →* F) lam) : F),
            (Units.map (ρ : F →* F) (Units.map (ρ : F →* F) lam⁻¹) : F)] := by
        rw [h2]
        simp
      have h3 := hc 2 (Or.inr rfl) (θ (θ t)) _ _ _ h2'
      rw [if_neg (by norm_num), ← hθapp] at h3
      refine ⟨(lam : F) * (ρ (lam : F))⁻¹, (lam : F)⁻¹ * ρ (ρ lam), ρ lam * (ρ (ρ lam))⁻¹,
        ?_, ?_, ?_⟩
      · rw [hN, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, h1', h2']
        simp only [ht, diagonal_mul_diagonal]
        congr 1
        funext i
        fin_cases i <;> simp [hinv, hρinv] <;> ring
      · apply Subtype.ext
        rw [h3]
        simp [ht, hρ3, hinv, hρinv]
      · intro hc'
        apply not_const_norm_two ρ hm hl0 (by rw [← Units.val_pow_eq_pow_val, hlm, Units.val_one])
          hρl
        obtain ⟨e1, e2⟩ := hc'
        constructor
        · rw [div_eq_mul_inv, div_eq_mul_inv, e1, mul_comm]
        · rw [div_eq_mul_inv, div_eq_mul_inv, mul_comm, e2]
  obtain ⟨n₀, n₁, n₂, hNd, hθ3, hnc⟩ := hdiag
  refine ⟨proj 3 F N, ⟨N, hNT, rfl⟩, ?_, ?_⟩
  · intro h1
    obtain ⟨c, -, hc1⟩ := exists_eq_smul_one_of_mem_scalars (proj_eq_one_iff.mp h1)
    apply hnc
    have e := fun i => congrFun (congrFun (hNd.symm.trans hc1) i) i
    have e0 := e 0
    have e1 := e 1
    have e2 := e 2
    simp at e0 e1 e2
    exact ⟨e0.trans e1.symm, e1.trans e2.symm⟩
  · rw [hθproj]
    congr 1
    rw [hN, map_mul, map_mul, hθ3]
    rw [mul_assoc t, hcomm t (θ t * θ (θ t)) htT (mul_mem (hθT _ htT) (hθT _ (hθT _ htT)))]

end CFSG.RankThree.PartTwo.Sec4.Ronan148V
