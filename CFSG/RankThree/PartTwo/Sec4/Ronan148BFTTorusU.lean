module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148VHeisTorus
public import CFSG.RankThree.PartTwo.Sec4.Ronan148VUnitaryHom

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148B

open Matrix CFSG.RankThree.PartTwo.Sec4 CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartTwo.KFacts
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)

variable {f : ℕ} {F : Type} [Field F]

theorem diagUnits_one : (diagUnits 1 1 1 : GL (Fin 3) F) = 1 := by
  apply Units.ext
  simp only [coe_diagUnits, Units.val_one]
  rw [← diagonal_one]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem diagUnits_inv (a b e : Fˣ) : (diagUnits a b e)⁻¹ = diagUnits a⁻¹ b⁻¹ e⁻¹ := by
  apply inv_eq_of_mul_eq_one_right
  rw [diagUnits_mul, mul_inv_cancel, mul_inv_cancel, mul_inv_cancel, diagUnits_one]

theorem diagUnits_comm (a b e a' b' e' : Fˣ) :
    diagUnits a b e * diagUnits a' b' e' = diagUnits a' b' e' * diagUnits a b e := by
  rw [diagUnits_mul, diagUnits_mul, mul_comm a, mul_comm b, mul_comm e]

theorem glAut_diagUnits (ρ : F ≃+* F) (a b e : Fˣ) :
    glAut ρ (diagUnits a b e) = diagUnits (Units.map (ρ : F →* F) a)
      (Units.map (ρ : F →* F) b) (Units.map (ρ : F →* F) e) := by
  apply Units.ext
  rw [coe_glAut, coe_diagUnits, coe_diagUnits, diagonal_map (map_zero ρ)]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem conj_diagUnits_eq' (w₀ w₁ w₂ a b e : Fˣ) (k : ℕ) :
    (cycThree ^ k * diagUnits w₀ w₁ w₂) * diagUnits a b e *
        (cycThree ^ k * diagUnits w₀ w₁ w₂)⁻¹ =
      cycThree ^ k * diagUnits a b e * (cycThree ^ k)⁻¹ := by
  calc (cycThree ^ k * diagUnits w₀ w₁ w₂) * diagUnits a b e *
        (cycThree ^ k * diagUnits w₀ w₁ w₂)⁻¹
      = cycThree ^ k * (diagUnits w₀ w₁ w₂ * diagUnits a b e) * (diagUnits w₀ w₁ w₂)⁻¹ *
          (cycThree ^ k)⁻¹ := by group
    _ = cycThree ^ k * diagUnits a b e * (cycThree ^ k)⁻¹ := by
        rw [diagUnits_comm]; group

theorem cycThree_sq_conj_diagUnits' (a b e : Fˣ) :
    cycThree ^ 2 * diagUnits a b e * (cycThree ^ 2)⁻¹ = diagUnits b e a := by
  calc cycThree ^ 2 * diagUnits a b e * (cycThree ^ 2)⁻¹ =
      cycThree * (cycThree * diagUnits a b e * cycThree⁻¹) * cycThree⁻¹ := by
        rw [pow_two, _root_.mul_inv_rev]
        group
    _ = diagUnits b e a := by rw [cycThree_conj_diagUnits, cycThree_conj_diagUnits]

theorem exists_cycThree_pow_conj_diagUnits {k : ℕ} (hk : k < 3) (a b e : Fˣ) :
    ∃ a' b' e' : Fˣ, ({a', b', e'} : Set Fˣ) ⊆ {a, b, e} ∧
      cycThree ^ k * diagUnits a b e * (cycThree ^ k)⁻¹ = diagUnits a' b' e' := by
  interval_cases k
  · exact ⟨a, b, e, le_rfl, by rw [pow_zero, one_mul, inv_one, mul_one]⟩
  · refine ⟨e, a, b, ?_, by rw [pow_one, cycThree_conj_diagUnits]⟩
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    tauto
  · refine ⟨b, e, a, ?_, cycThree_sq_conj_diagUnits' a b e⟩
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    tauto

variable (hU : UnitaryFieldData 2 f F)

variable (f F) in
@[expose] def torusSU (m : ℕ) : Subgroup (unitarySU 2 f F 3) where
  carrier := {g | ∃ a b e : Fˣ, a ^ m = 1 ∧ b ^ m = 1 ∧ e ^ m = 1 ∧
    (g : GL (Fin 3) F) = diagUnits a b e}
  mul_mem' := by
    rintro g g' ⟨a, b, e, ha, hb, he, hg⟩ ⟨a', b', e', ha', hb', he', hg'⟩
    exact ⟨a * a', b * b', e * e', by rw [mul_pow, ha, ha', one_mul],
      by rw [mul_pow, hb, hb', one_mul], by rw [mul_pow, he, he', one_mul],
      by rw [Subgroup.coe_mul, hg, hg', diagUnits_mul]⟩
  one_mem' := ⟨1, 1, 1, one_pow _, one_pow _, one_pow _, by rw [Subgroup.coe_one, diagUnits_one]⟩
  inv_mem' := by
    rintro g ⟨a, b, e, ha, hb, he, hg⟩
    exact ⟨a⁻¹, b⁻¹, e⁻¹, by rw [inv_pow, ha, inv_one], by rw [inv_pow, hb, inv_one],
      by rw [inv_pow, he, inv_one], by rw [Subgroup.coe_inv, hg, diagUnits_inv]⟩

theorem mem_torusSU {m : ℕ} {g : unitarySU 2 f F 3} :
    g ∈ torusSU f F m ↔ ∃ a b e : Fˣ, a ^ m = 1 ∧ b ^ m = 1 ∧ e ^ m = 1 ∧
      (g : GL (Fin 3) F) = diagUnits a b e :=
  Iff.rfl

@[expose] def diagTorusU (m : ℕ) : Subgroup (unitaryPSU hU 3) :=
  (torusSU f F m).map (unitaryProj hU 3)

variable {hU}

theorem not_three_dvd_card_diagTorusU {m : ℕ} (hm : Nat.Coprime m 3) :
    ¬ 3 ∣ Nat.card (diagTorusU hU m) := by
  have := hU.finite
  intro h3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 3 h3
  obtain ⟨g, ⟨a, b, e, ha, hb, he, hg⟩, hgu⟩ := u.2
  have hgm : g ^ m = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, hg, Subgroup.coe_one]
    have hpow : ∀ j : ℕ, diagUnits a b e ^ j = diagUnits (a ^ j) (b ^ j) (e ^ j) := by
      intro j
      induction j with
      | zero => rw [pow_zero, pow_zero, pow_zero, pow_zero, diagUnits_one]
      | succ j ih => rw [pow_succ, ih, diagUnits_mul, ← pow_succ, ← pow_succ, ← pow_succ]
    rw [hpow, ha, hb, he, diagUnits_one]
  have hum : u ^ m = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, ← hgu, ← map_pow, hgm, map_one, Subgroup.coe_one]
  have := orderOf_dvd_of_pow_eq_one hum
  rw [hu] at this
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (Nat.Coprime.symm hm) this

theorem suConj_mem_torusSU {m k : ℕ} (hk : k < 3) {w₀ w₁ w₂ : Fˣ}
    (hA : cycThree ^ k * diagUnits w₀ w₁ w₂ ∈ unitaryIsom3 hU) {g : unitarySU 2 f F 3}
    (hg : g ∈ torusSU f F m) : suConj hU ⟨_, hA⟩ g ∈ torusSU f F m := by
  obtain ⟨a, b, e, ha, hb, he, hge⟩ := hg
  rw [mem_torusSU, coe_suConj]
  change ∃ a' b' e' : Fˣ, a' ^ m = 1 ∧ b' ^ m = 1 ∧ e' ^ m = 1 ∧
    (cycThree ^ k * diagUnits w₀ w₁ w₂) * (g : GL (Fin 3) F) *
      (cycThree ^ k * diagUnits w₀ w₁ w₂)⁻¹ = diagUnits a' b' e'
  rw [hge, conj_diagUnits_eq']
  obtain ⟨a', b', e', hsub, heq⟩ := exists_cycThree_pow_conj_diagUnits hk a b e
  have hall : ∀ x ∈ ({a', b', e'} : Set Fˣ), x ^ m = 1 := by
    intro x hx
    rcases hsub hx with rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact he
  exact ⟨a', b', e', hall a' (by simp), hall b' (by simp), hall e' (by simp), heq⟩

theorem suField_mem_torusSU {m : ℕ} (ρ : F ≃+* F) {g : unitarySU 2 f F 3}
    (hg : g ∈ torusSU f F m) : suField hU ρ g ∈ torusSU f F m := by
  obtain ⟨a, b, e, ha, hb, he, hge⟩ := hg
  refine ⟨Units.map (ρ : F →* F) a, Units.map (ρ : F →* F) b, Units.map (ρ : F →* F) e,
    by rw [← map_pow, ha, map_one], by rw [← map_pow, hb, map_one],
    by rw [← map_pow, he, map_one], ?_⟩
  rw [coe_suField, hge, glAut_diagUnits]

theorem psuConj_mem_diagTorusU {m k : ℕ} (hk : k < 3) {w₀ w₁ w₂ : Fˣ}
    (hA : cycThree ^ k * diagUnits w₀ w₁ w₂ ∈ unitaryIsom3 hU) {u : unitaryPSU hU 3}
    (hu : u ∈ diagTorusU hU m) : psuConj hU ⟨_, hA⟩ u ∈ diagTorusU hU m := by
  obtain ⟨g, hg, rfl⟩ := hu
  exact ⟨_, suConj_mem_torusSU hk hA hg, (psuConj_mk _ g).symm⟩

theorem psuField_mem_diagTorusU {m : ℕ} (ρ : F ≃+* F) {u : unitaryPSU hU 3}
    (hu : u ∈ diagTorusU hU m) : psuField hU ρ u ∈ diagTorusU hU m := by
  obtain ⟨g, hg, rfl⟩ := hu
  exact ⟨_, suField_mem_torusSU ρ hg, (psuField_mk _ g).symm⟩

theorem exists_scalar_of_unitaryProj_eq {A B : unitarySU 2 f F 3}
    (h : unitaryProj hU 3 A = unitaryProj hU 3 B) :
    ∃ c : Fˣ, (B : GL (Fin 3) F) = GeneralLinearGroup.scalar (Fin 3) c * A := by
  have h1 : unitaryProj hU 3 (A⁻¹ * B) = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
  obtain ⟨c, -, -, hc⟩ := Ronan148V.exists_scalar_of_unitaryProj_eq_one hU h1
  refine ⟨c, ?_⟩
  rw [Subgroup.coe_mul, Subgroup.coe_inv] at hc
  calc (B : GL (Fin 3) F) = (A : GL (Fin 3) F) * ((A : GL (Fin 3) F)⁻¹ * (B : GL (Fin 3) F)) := by
        group
    _ = (A : GL (Fin 3) F) * GeneralLinearGroup.scalar (Fin 3) c := by rw [hc]
    _ = GeneralLinearGroup.scalar (Fin 3) c * A := (commute_scalar c _).eq

theorem eq_one_of_commute_cycThree_powU {m k : ℕ} (hm : Nat.Coprime m 3) (hk : k = 1 ∨ k = 2)
    {w₀ w₁ w₂ : Fˣ} {M : unitarySU 2 f F 3}
    (hM : (M : GL (Fin 3) F) = cycThree ^ k * diagUnits w₀ w₁ w₂)
    {u : unitaryPSU hU 3} (hu : u ∈ diagTorusU hU m)
    (hc : u * unitaryProj hU 3 M = unitaryProj hU 3 M * u) : u = 1 := by
  obtain ⟨g, ⟨a, b, e, ha, hb, he, hge⟩, rfl⟩ := hu
  obtain ⟨ν, hν⟩ := exists_scalar_of_unitaryProj_eq (hU := hU) (A := g) (B := M * g * M⁻¹)
    (by rw [map_mul, map_mul, map_inv, ← hc, mul_inv_cancel_right])
  have hconj : ((M * g * M⁻¹ : unitarySU 2 f F 3) : GL (Fin 3) F) =
      cycThree ^ k * diagUnits a b e * (cycThree ^ k)⁻¹ := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hM, hge, conj_diagUnits_eq']
  rw [hconj, hge] at hν
  have hent : ∀ i : Fin 3, ((cycThree ^ k * diagUnits a b e * (cycThree ^ k)⁻¹ : GL (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) i i = ν * ((diagUnits a b e : GL (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) i i := fun i => by
    rw [hν, Units.val_mul, GeneralLinearGroup.coe_scalar, scalar_apply, diagonal_mul]
  have hscalar : (a : F) = b ∧ (b : F) = e := by
    rcases hk with rfl | rfl
    · have e0 := hent 0
      have e1 := hent 1
      have e2 := hent 2
      rw [pow_one, cycThree_conj_diagUnits] at e0 e1 e2
      simp only [coe_diagUnits, diagonal_apply_eq, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at e0 e1 e2
      exact Ronan148V.eq_of_shift_eq_mul hm (by rw [← Units.val_pow_eq_pow_val, ha, Units.val_one])
        (by rw [← Units.val_pow_eq_pow_val, he, Units.val_one]) e0 e1 e2
    · have e0 := hent 0
      have e1 := hent 1
      have e2 := hent 2
      rw [cycThree_sq_conj_diagUnits'] at e0 e1 e2
      simp only [coe_diagUnits, diagonal_apply_eq, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at e0 e1 e2
      obtain ⟨h1, h2⟩ :=
        Ronan148V.eq_of_shift_eq_mul (a := (a : F)) (b := (e : F)) (e := (b : F)) hm
        (by rw [← Units.val_pow_eq_pow_val, ha, Units.val_one])
        (by rw [← Units.val_pow_eq_pow_val, hb, Units.val_one]) e0 e2 e1
      exact ⟨h1.trans h2, h2.symm⟩
  obtain ⟨hab, hbe⟩ := hscalar
  apply Ronan148V.unitaryProj_eq_one_of_scalar hU
  refine ⟨a, ?_⟩
  rw [hge]
  apply Units.ext
  rw [GeneralLinearGroup.coe_scalar, coe_diagUnits, scalar_apply]
  congr 1
  funext i
  fin_cases i
  · rfl
  · exact hab
  · exact hab.trans hbe

theorem diagUnits_mem_unitarySU {lam : Fˣ} (hlN : hU.norm (lam : F) = 1) :
    diagUnits lam lam⁻¹ 1 ∈ unitarySU 2 f F 3 := by
  rw [mem_unitarySU_iff hU]
  have hb : hU.bar (lam : F) * lam = 1 := by rw [mul_comm]; exact hlN
  have hbi : hU.bar ((lam⁻¹ : Fˣ) : F) * ((lam⁻¹ : Fˣ) : F) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, ← mul_inv, hb, inv_one]
  refine ⟨?_, ?_⟩
  · rw [coe_diagUnits, det_diagonal, Fin.prod_univ_three]
    simp
  · rw [coe_diagUnits, diagonal_map (map_zero hU.bar), diagonal_transpose, diagonal_mul_diagonal,
      ← diagonal_one]
    congr 1
    funext i
    fin_cases i
    · exact hb
    · exact hbi
    · simp

theorem exists_fixed_diagTorusU {m k : ℕ} (hm : Nat.Coprime m 3) (hk : k = 1 ∨ k = 2)
    {w₀ w₁ w₂ : Fˣ} (hA : cycThree ^ k * diagUnits w₀ w₁ w₂ ∈ unitaryIsom3 hU)
    (ρ : F ≃+* F) (hρ3 : ∀ x, ρ (ρ (ρ x)) = x) {lam : Fˣ} (hlm : lam ^ m = 1)
    (hlN : hU.norm (lam : F) = 1) (hρl : ρ lam ≠ lam) :
    ∃ u ∈ diagTorusU hU m, u ≠ 1 ∧ psuConj hU ⟨_, hA⟩ (psuField hU ρ u) = u := by
  set ρ' : Fˣ →* Fˣ := Units.map (ρ : F →* F) with hρ'
  have hρ'v : ∀ x : Fˣ, ((ρ' x : Fˣ) : F) = ρ (x : F) := fun x => rfl
  set θ : unitarySU 2 f F 3 →* unitarySU 2 f F 3 :=
    (suConj hU ⟨_, hA⟩).toMonoidHom.comp (suField hU ρ).toMonoidHom with hθ
  have hθproj : ∀ X, psuConj hU ⟨_, hA⟩ (psuField hU ρ (unitaryProj hU 3 X)) =
      unitaryProj hU 3 (θ X) := fun X => by
    change psuConj hU ⟨_, hA⟩ (psuField hU ρ (X : unitaryPSU hU 3)) = ((θ X : unitarySU 2 f F 3) :
      unitaryPSU hU 3)
    rw [psuField_mk, psuConj_mk]
    rfl
  have hk3 : k < 3 := by omega
  have hθT : ∀ X ∈ torusSU f F m, θ X ∈ torusSU f F m := fun X hX =>
    suConj_mem_torusSU hk3 hA (suField_mem_torusSU (hU := hU) ρ hX)
  have hθd : ∀ (X : unitarySU 2 f F 3) (a b e : Fˣ), (X : GL (Fin 3) F) = diagUnits a b e →
      ((θ X : unitarySU 2 f F 3) : GL (Fin 3) F) =
        if k = 1 then diagUnits (ρ' e) (ρ' a) (ρ' b) else diagUnits (ρ' b) (ρ' e) (ρ' a) := by
    intro X a b e hX
    change (cycThree ^ k * diagUnits w₀ w₁ w₂) * glAut ρ (X : GL (Fin 3) F) *
      (cycThree ^ k * diagUnits w₀ w₁ w₂)⁻¹ = _
    rw [hX, glAut_diagUnits, conj_diagUnits_eq']
    rcases hk with rfl | rfl
    · rw [if_pos rfl, pow_one, cycThree_conj_diagUnits]
    · rw [if_neg (by norm_num), cycThree_sq_conj_diagUnits']
  set t : unitarySU 2 f F 3 := ⟨_, diagUnits_mem_unitarySU (hU := hU) hlN⟩ with ht
  have htT : t ∈ torusSU f F m :=
    ⟨lam, lam⁻¹, 1, hlm, by rw [inv_pow, hlm, inv_one], one_pow _, rfl⟩
  have hcomm : ∀ X Y : unitarySU 2 f F 3, X ∈ torusSU f F m → Y ∈ torusSU f F m →
      X * Y = Y * X := by
    rintro X Y ⟨a, b, e, -, -, -, hX⟩ ⟨a', b', e', -, -, -, hY⟩
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hX, hY, diagUnits_comm]
  have hρ1 : ρ' 1 = 1 := map_one ρ'
  have hρinv : ∀ x : Fˣ, ρ' x⁻¹ = (ρ' x)⁻¹ := fun x => map_inv ρ' x
  have hρ3' : ∀ x : Fˣ, ρ' (ρ' (ρ' x)) = x := fun x => Units.ext (hρ3 (x : F))
  set N := t * θ t * θ (θ t) with hN
  have hNT : N ∈ torusSU f F m := mul_mem (mul_mem htT (hθT _ htT)) (hθT _ (hθT _ htT))
  obtain ⟨n₀, n₁, n₂, hNd, hθ3, hnc⟩ : ∃ n₀ n₁ n₂ : Fˣ, (N : GL (Fin 3) F) = diagUnits n₀ n₁ n₂ ∧
      θ (θ (θ t)) = t ∧ ¬ ((n₀ : F) = n₁ ∧ (n₁ : F) = n₂) := by
    have hl0 : (lam : F) ≠ 0 := lam.ne_zero
    have hlm' : (lam : F) ^ m = 1 := by rw [← Units.val_pow_eq_pow_val, hlm, Units.val_one]
    rcases hk with rfl | rfl
    · have h1 := hθd t lam lam⁻¹ 1 rfl
      rw [if_pos rfl, hρ1] at h1
      have h2 := hθd (θ t) 1 (ρ' lam) (ρ' lam⁻¹) h1
      rw [if_pos rfl, hρ1] at h2
      have h3 := hθd (θ (θ t)) (ρ' (ρ' lam⁻¹)) 1 (ρ' (ρ' lam)) h2
      rw [if_pos rfl, hρ1, hρ3', hρ3'] at h3
      refine ⟨lam * (ρ' (ρ' lam⁻¹)), lam⁻¹ * ρ' lam, ρ' lam⁻¹ * ρ' (ρ' lam), ?_,
        Subtype.ext h3, ?_⟩
      · rw [hN, Subgroup.coe_mul, Subgroup.coe_mul, h1, h2]
        change diagUnits lam lam⁻¹ 1 * _ * _ = _
        rw [diagUnits_mul, diagUnits_mul]
        simp only [mul_one, one_mul]
      · intro hc'
        apply Ronan148V.not_const_norm_one ρ hm hl0 hlm' hρl
        obtain ⟨e1, e2⟩ := hc'
        simp only [Units.val_mul, hρ'v, Units.val_inv_eq_inv_val, map_inv₀] at e1 e2
        constructor
        · rw [div_eq_mul_inv, div_eq_mul_inv, e1, mul_comm]
        · rw [div_eq_mul_inv, div_eq_mul_inv, mul_comm, e2, mul_comm]
    · have h1 := hθd t lam lam⁻¹ 1 rfl
      rw [if_neg (by norm_num), hρ1] at h1
      have h2 := hθd (θ t) (ρ' lam⁻¹) 1 (ρ' lam) h1
      rw [if_neg (by norm_num), hρ1] at h2
      have h3 := hθd (θ (θ t)) 1 (ρ' (ρ' lam)) (ρ' (ρ' lam⁻¹)) h2
      rw [if_neg (by norm_num), hρ1, hρ3', hρ3'] at h3
      refine ⟨lam * ρ' lam⁻¹, lam⁻¹ * ρ' (ρ' lam), ρ' lam * ρ' (ρ' lam⁻¹), ?_,
        Subtype.ext h3, ?_⟩
      · rw [hN, Subgroup.coe_mul, Subgroup.coe_mul, h1, h2]
        change diagUnits lam lam⁻¹ 1 * _ * _ = _
        rw [diagUnits_mul, diagUnits_mul]
        simp only [mul_one, one_mul]
      · intro hc'
        apply Ronan148V.not_const_norm_two ρ hm hl0 hlm' hρl
        obtain ⟨e1, e2⟩ := hc'
        simp only [Units.val_mul, hρ'v, Units.val_inv_eq_inv_val, map_inv₀] at e1 e2
        constructor
        · rw [div_eq_mul_inv, div_eq_mul_inv, e1, mul_comm]
        · rw [div_eq_mul_inv, div_eq_mul_inv, mul_comm, e2]
  refine ⟨unitaryProj hU 3 N, ⟨N, hNT, rfl⟩, ?_, ?_⟩
  · intro h1
    obtain ⟨c, -, -, hc1⟩ := Ronan148V.exists_scalar_of_unitaryProj_eq_one hU h1
    apply hnc
    rw [hNd] at hc1
    have e := fun i => congrFun (congrFun (congrArg (fun g : GL (Fin 3) F =>
      (g : Matrix (Fin 3) (Fin 3) F)) hc1) i) i
    have e0 := e 0
    have e1 := e 1
    have e2 := e 2
    simp [coe_diagUnits, GeneralLinearGroup.coe_scalar] at e0 e1 e2
    exact ⟨e0.trans e1.symm, e1.trans e2.symm⟩
  · rw [hθproj]
    congr 1
    rw [hN, map_mul, map_mul, hθ3]
    rw [mul_assoc t, hcomm t (θ t * θ (θ t)) htT (mul_mem (hθT _ htT) (hθT _ (hθT _ htT)))]

end CFSG.RankThree.PartTwo.Sec4.Ronan148B
