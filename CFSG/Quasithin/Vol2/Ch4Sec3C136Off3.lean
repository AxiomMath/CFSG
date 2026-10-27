module

public import CFSG.Quasithin.Vol2.Ch4Sec3C136Off2
public import CFSG.Quasithin.Vol2.KGFactL34Uni

public section

namespace CFSG.Quasithin.H13.Ch4

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {F : Type} [Field F]

theorem card_le_of_isPGroup_SL2 [Finite F] [CharP F 2]
    {H : Subgroup (SpecialLinearGroup (Fin 2) F)} (hH : IsPGroup 2 H) :
    Nat.card H ≤ Nat.card F := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := hH.exists_le_sylow
  obtain ⟨P₀, hP₀⟩ := exists_sylow_unitriangular (K := F) 2 (n := 2) (by norm_num)
  have h1 : Nat.card P = Nat.card P₀ := by
    rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
  have h2 : Nat.card P₀ = Nat.card F := by
    have h3 := card_unitriangular (K := F) 2
    rw [← hP₀] at h3
    rw [h3]
    norm_num
  calc Nat.card H ≤ Nat.card P := Subgroup.card_le_of_le hP
    _ = Nat.card P₀ := h1
    _ = Nat.card F := h2

theorem card_le_sq_of_ne_top [Finite F] {C : Submodule F (Fin 3 → F)} (hC : C ≠ ⊤) :
    Nat.card C ≤ Nat.card F ^ 2 := by
  have h1 : Module.finrank F C < 3 := by
    have := Submodule.finrank_lt hC
    rwa [Module.finrank_fin_fun] at this
  rw [Module.natCard_eq_pow_finrank (K := F) (V := ↥C)]
  exact Nat.pow_le_pow_right Nat.card_pos (by omega)

theorem two_le_card_field [Finite F] : 2 ≤ Nat.card F := by
  have := Fintype.ofFinite F
  rw [Nat.card_eq_fintype_card]
  exact Fintype.one_lt_card

section CharTwo

variable [CharP F 2] [Finite F]

omit [Finite F] in
theorem det_eq_one_of_mul_self' {n : ℕ} {A : Matrix (Fin n) (Fin n) F} (h : A * A = 1) :
    A.det = 1 := by
  have h1 := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_one] at h1
  exact eq_one_of_mul_self_eq_one h1

omit [Finite F] in
theorem offDiag_ne_zero_of_mul_self {c : Matrix (Fin 2) (Fin 2) F} (hc : c * c = 1)
    (hc1 : c ≠ 1) : c 0 1 ≠ 0 ∨ c 1 0 ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨h01, h10⟩ := h
  apply hc1
  have e00 := congrFun (congrFun hc 0) 0
  have e11 := congrFun (congrFun hc 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, h01, h10, mul_zero, add_zero, zero_add,
    Matrix.one_apply_eq] at e00 e11
  have h00 := eq_one_of_mul_self_eq_one e00
  have h11 := eq_one_of_mul_self_eq_one e11
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h00, h11, h01, h10]

omit [CharP F 2] [Finite F] in
theorem eq_zero_of_mulVec_eq_zero {P : Matrix (Fin 3) (Fin 3) F} (hP : P * P = 1)
    {x : Fin 3 → F} (hx : P.mulVec x = 0) : x = 0 := by
  have h1 : P.mulVec (P.mulVec x) = x := by rw [Matrix.mulVec_mulVec, hP, Matrix.one_mulVec]
  rw [← h1, hx, Matrix.mulVec_zero]

omit [CharP F 2] [Finite F] in
theorem eq_zero_of_tens_fixed_zero {c : Matrix (Fin 2) (Fin 2) F} {P : Matrix (Fin 3) (Fin 3) F}
    (hP : P * P = 1) (ha : c 0 1 ≠ 0) {v : Fin 2 → Fin 3 → F} (hv : tens c P v = v)
    (hv0 : v 0 = 0) : v = 0 := by
  have h1 := congrFun hv 0
  simp only [tens_apply, Fin.sum_univ_two, hv0, Matrix.mulVec_zero, smul_zero, zero_add] at h1
  have h2 : P.mulVec (v 1) = 0 := (smul_eq_zero.mp h1).resolve_left ha
  funext i
  fin_cases i
  · exact hv0
  · exact eq_zero_of_mulVec_eq_zero hP h2

omit [CharP F 2] [Finite F] in
theorem eq_zero_of_tens_fixed_one {c : Matrix (Fin 2) (Fin 2) F} {P : Matrix (Fin 3) (Fin 3) F}
    (hP : P * P = 1) (ha : c 1 0 ≠ 0) {v : Fin 2 → Fin 3 → F} (hv : tens c P v = v)
    (hv1 : v 1 = 0) : v = 0 := by
  have h1 := congrFun hv 1
  simp only [tens_apply, Fin.sum_univ_two, hv1, Matrix.mulVec_zero, smul_zero, add_zero] at h1
  have h2 : P.mulVec (v 0) = 0 := (smul_eq_zero.mp h1).resolve_left ha
  funext i
  fin_cases i
  · exact eq_zero_of_mulVec_eq_zero hP h2
  · exact hv1

omit [CharP F 2] [Finite F] in
theorem tens_sub (c : Matrix (Fin 2) (Fin 2) F) (P : Matrix (Fin 3) (Fin 3) F)
    (v w : Fin 2 → Fin 3 → F) : tens c P (v - w) = tens c P v - tens c P w := by
  funext i
  simp only [tens_apply, Pi.sub_apply, Matrix.mulVec_sub, smul_sub, Finset.sum_sub_distrib]

omit [CharP F 2] [Finite F] in
theorem dact_eq_self_iff (P : Matrix (Fin 3) (Fin 3) F) (v : Fin 2 → Fin 3 → F) :
    dact P v = v ↔ ∀ i, P.mulVec (v i) = v i := by
  constructor
  · intro h i
    exact congrFun h i
  · intro h
    funext i
    exact h i

omit [Field F] [CharP F 2] [Finite F] in
theorem card_pairs : Nat.card (Fin 2 → Fin 3 → F) = Nat.card F ^ 6 := by
  rw [Nat.card_fun, Nat.card_fun, Nat.card_fin, Nat.card_fin, ← pow_mul]

omit [CharP F 2] [Finite F] in
theorem card_pairs_mem (C : Submodule F (Fin 3 → F)) :
    Nat.card {v : Fin 2 → Fin 3 → F // ∀ i, v i ∈ C} = Nat.card C ^ 2 := by
  rw [Nat.card_congr (Equiv.subtypePiEquivPi (p := fun (_ : Fin 2) (x : Fin 3 → F) => x ∈ C)),
    Nat.card_fun, Nat.card_fin]

theorem card_mul_card_fixPts_le_of_lin {E : Subgroup (Equiv.Perm (Fin 2 → Fin 3 → F))}
    (hadd : E ≤ addPerms F) (hlin : E ≤ linPerms F) (hn : ∀ e ∈ E, NormalizesDact ⇑e)
    (hc : ∀ e ∈ E, ∀ f ∈ E, e * f = f * e) (hinv : ∀ e ∈ E, e * e = 1) :
    Nat.card E ≤ Nat.card F ^ 3 ∧
      Nat.card E * Nat.card (fixPts (E : Set (Equiv.Perm (Fin 2 → Fin 3 → F)))) ≤
        Nat.card F ^ 6 ∧
      (Nat.card E * Nat.card (fixPts (E : Set (Equiv.Perm (Fin 2 → Fin 3 → F)))) =
          Nat.card F ^ 6 →
        E ≤ diagPerms F ∧
          (E = ⊥ ∨ Nat.card (fixPts (E : Set (Equiv.Perm (Fin 2 → Fin 3 → F)))) =
            Nat.card F ^ 4)) := by
  classical
  set q := Nat.card F with hq
  have hq2 : 2 ≤ q := two_le_card_field
  have hnp : ∀ e : ↥E, ∃ cP : Matrix (Fin 2) (Fin 2) F × Matrix (Fin 3) (Fin 3) F,
      cP.1 * cP.1 = 1 ∧ cP.2 * cP.2 = 1 ∧
        ∀ v, (e : Equiv.Perm (Fin 2 → Fin 3 → F)) v = tens cP.1 cP.2 v := by
    intro e
    obtain ⟨c, P, h1, h2, h3⟩ := exists_normalized (hadd e.2) (hlin e.2) (hn e e.2)
      (hn _ (E.inv_mem e.2)) (hinv e e.2)
    exact ⟨(c, P), h1, h2, h3⟩
  choose cP hcP using hnp
  have hrep : ∀ (e : ↥E) v, (e : Equiv.Perm (Fin 2 → Fin 3 → F)) v = tens (cP e).1 (cP e).2 v :=
    fun e => (hcP e).2.2
  have hcomm : ∀ e f : ↥E, (cP e).1 * (cP f).1 = (cP f).1 * (cP e).1 ∧
      (cP e).2 * (cP f).2 = (cP f).2 * (cP e).2 := by
    intro e f
    refine commute_of_commute (hcP e).1 (hcP f).1 (hcP e).2.1 (hcP f).2.1 fun v => ?_
    have h1 : (e : Equiv.Perm (Fin 2 → Fin 3 → F)) ((f : Equiv.Perm (Fin 2 → Fin 3 → F)) v) =
        (f : Equiv.Perm (Fin 2 → Fin 3 → F)) ((e : Equiv.Perm (Fin 2 → Fin 3 → F)) v) :=
      congrArg (fun g : Equiv.Perm (Fin 2 → Fin 3 → F) => g v) (hc e e.2 f f.2)
    rw [hrep f v, hrep e (tens (cP f).1 (cP f).2 v), hrep e v, hrep f (tens (cP e).1 (cP e).2 v),
      tens_tens, tens_tens] at h1
    exact h1
  have hsqm : ∀ {n : ℕ} {a b : Matrix (Fin n) (Fin n) F}, a * a = 1 → b * b = 1 → a * b = b * a →
      (a * b) * (a * b) = 1 := by
    intro n a b ha hb hab
    calc (a * b) * (a * b) = a * (b * a) * b := by simp only [Matrix.mul_assoc]
      _ = a * (a * b) * b := by rw [← hab]
      _ = (a * a) * (b * b) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [ha, hb, Matrix.one_mul]
  have hprod : ∀ e f : ↥E, cP (e * f) = ((cP e).1 * (cP f).1, (cP e).2 * (cP f).2) := by
    intro e f
    have h := normalized_unique (hcP (e * f)).1 (hcP (e * f)).2.1
      (hsqm (hcP e).2.1 (hcP f).2.1 (hcomm e f).2) (fun v => by
        rw [← hrep (e * f) v, ← tens_tens, ← hrep f v, ← hrep e]
        rfl)
    exact Prod.ext h.1 h.2
  have hone : cP 1 = (1, 1) := by
    have h := normalized_unique (hcP 1).1 (hcP 1).2.1 (Matrix.one_mul 1) (fun v => by
      rw [← hrep 1 v, tens_one_one]
      rfl)
    exact Prod.ext h.1 h.2
  let χ : ↥E →* SpecialLinearGroup (Fin 2) F :=
    { toFun := fun e => ⟨(cP e).1, det_eq_one_of_mul_self' (hcP e).1⟩
      map_one' := Subtype.ext (by show (cP 1).1 = 1; rw [hone])
      map_mul' := fun e f => Subtype.ext (by
        show (cP (e * f)).1 = (cP e).1 * (cP f).1
        rw [hprod]) }
  let π : ↥E →* SpecialLinearGroup (Fin 3) F :=
    { toFun := fun e => ⟨(cP e).2, det_eq_one_of_mul_self' (hcP e).2.1⟩
      map_one' := Subtype.ext (by show (cP 1).2 = 1; rw [hone])
      map_mul' := fun e f => Subtype.ext (by
        show (cP (e * f)).2 = (cP e).2 * (cP f).2
        rw [hprod]) }
  have hχapp : ∀ e, ((χ e : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = (cP e).1 :=
    fun _ => rfl
  have hπapp : ∀ e, ((π e : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = (cP e).2 :=
    fun _ => rfl
  have hrange : Nat.card χ.range ≤ q := by
    refine card_le_of_isPGroup_SL2 fun g => ⟨1, ?_⟩
    obtain ⟨_, ⟨e, rfl⟩⟩ := g
    apply Subtype.ext
    show χ e ^ 2 ^ 1 = 1
    rw [pow_one, sq, ← map_mul]
    have h1 : e * e = 1 := Subtype.ext (hinv e e.2)
    rw [h1, map_one]
  set K := χ.ker with hK
  have hcardE : Nat.card E = Nat.card K * Nat.card χ.range := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange χ).toEquiv,
      Subgroup.card_eq_card_quotient_mul_card_subgroup χ.ker, mul_comm]
  have hKmem : ∀ e : ↥E, e ∈ K ↔ (cP e).1 = 1 := by
    intro e
    rw [hK, MonoidHom.mem_ker]
    constructor
    · intro h
      have := congrArg (fun g : SpecialLinearGroup (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F)) h
      exact this
    · intro h
      exact Subtype.ext h
  have hπinj : Function.Injective (π.comp K.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro k hk
    rw [MonoidHom.mem_ker] at hk
    have hk2 : (cP (k : ↥E)).2 = 1 :=
      congrArg (fun g : SpecialLinearGroup (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F)) hk
    have hk1 : (cP (k : ↥E)).1 = 1 := (hKmem k).mp k.2
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    apply Subtype.ext
    refine Equiv.ext fun v => ?_
    show ((k : ↥E) : Equiv.Perm (Fin 2 → Fin 3 → F)) v = v
    rw [hrep, hk1, hk2, tens_one_one]
  set Pim := (π.comp K.subtype).range with hPim
  have hcardPim : Nat.card Pim = Nat.card K :=
    (Nat.card_congr (MonoidHom.ofInjective hπinj).toEquiv).symm
  have hPimle : Nat.card Pim ≤ q ^ 2 := by
    refine KGL34A.card_le_of_elemAb ?_ ?_
    · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
      apply Subtype.ext
      exact (hcomm (x : ↥E) (y : ↥E)).2
    · rintro _ ⟨x, rfl⟩
      apply Subtype.ext
      exact (hcP (x : ↥E)).2.1
  let C₁ : Submodule F (Fin 3 → F) :=
    { carrier := {x | ∀ e : ↥E, e ∈ K → (cP e).2.mulVec x = x}
      add_mem' := fun {x y} hx hy e he => by rw [Matrix.mulVec_add, hx e he, hy e he]
      zero_mem' := fun e _ => Matrix.mulVec_zero _
      smul_mem' := fun μ x hx e he => by rw [Matrix.mulVec_smul, hx e he] }
  have hC₁mem : ∀ x, x ∈ C₁ ↔ ∀ e : ↥E, e ∈ K → (cP e).2.mulVec x = x := fun _ => Iff.rfl
  have hC₁le : Nat.card C₁ ≤ q ^ 3 := by
    calc Nat.card C₁ ≤ Nat.card (Fin 3 → F) := Nat.card_le_card_of_injective _ Subtype.val_injective
      _ = q ^ 3 := by rw [Nat.card_fun, Nat.card_fin]
  have hC₁top : (∃ e : ↥E, e ∈ K ∧ (cP e).2 ≠ 1) → Nat.card C₁ ≤ q ^ 2 := by
    rintro ⟨e, heK, he1⟩
    refine card_le_sq_of_ne_top fun htop => he1 ?_
    apply matrix_eq_of_mulVec_eq
    intro x
    have hx : x ∈ C₁ := by rw [htop]; trivial
    rw [(hC₁mem x).mp hx e heK, Matrix.one_mulVec]
  have hPimtriv : (∀ e : ↥E, e ∈ K → (cP e).2 = 1) → Nat.card K = 1 := by
    intro h
    rw [← hcardPim, Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun a b => ?_⟩, ⟨1⟩⟩
    obtain ⟨_, ⟨x, rfl⟩⟩ := a
    obtain ⟨_, ⟨y, rfl⟩⟩ := b
    apply Subtype.ext
    apply Subtype.ext
    show (cP (x : ↥E)).2 = (cP (y : ↥E)).2
    rw [h x x.2, h y y.2]
  have hPC : Nat.card K * Nat.card C₁ ≤ q ^ 4 := by
    by_cases h : ∃ e : ↥E, e ∈ K ∧ (cP e).2 ≠ 1
    · have h1 := hC₁top h
      rw [← hcardPim]
      calc Nat.card Pim * Nat.card C₁ ≤ q ^ 2 * q ^ 2 := Nat.mul_le_mul hPimle h1
        _ = q ^ 4 := by ring
    · push Not at h
      rw [hPimtriv h, one_mul]
      exact hC₁le.trans (Nat.pow_le_pow_right (by omega) (by norm_num))
  by_cases hdiag : ∀ e : ↥E, (cP e).1 = 1
  ·
    have hKtop : ∀ e : ↥E, e ∈ K := fun e => (hKmem e).mpr (hdiag e)
    have hrange1 : Nat.card χ.range = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      refine ⟨⟨fun a b => ?_⟩, ⟨1⟩⟩
      obtain ⟨_, ⟨x, rfl⟩⟩ := a
      obtain ⟨_, ⟨y, rfl⟩⟩ := b
      apply Subtype.ext
      apply Subtype.ext
      show (cP x).1 = (cP y).1
      rw [hdiag x, hdiag y]
    have hEK : Nat.card E = Nat.card K := by rw [hcardE, hrange1, mul_one]
    have hEdiag : E ≤ diagPerms F := by
      intro e he
      refine ⟨π ⟨e, he⟩, fun v => ?_⟩
      rw [hrep ⟨e, he⟩ v, hdiag ⟨e, he⟩, tens_one]
      rfl
    have hfix : fixPts (E : Set (Equiv.Perm (Fin 2 → Fin 3 → F))) = {v | ∀ i, v i ∈ C₁} := by
      ext v
      constructor
      · intro hv i
        refine (hC₁mem _).mpr fun e _ => ?_
        have h1 := hv e e.2
        rw [hrep, hdiag e, tens_one] at h1
        exact (dact_eq_self_iff _ v).mp h1 i
      · intro hv e he
        rw [hrep ⟨e, he⟩ v, hdiag ⟨e, he⟩, tens_one]
        exact (dact_eq_self_iff _ v).mpr fun i => (hC₁mem _).mp (hv i) ⟨e, he⟩ (hKtop _)
    have hfixcard :
        Nat.card (fixPts (E : Set (Equiv.Perm (Fin 2 → Fin 3 → F)))) = Nat.card C₁ ^ 2 := by
      rw [hfix]
      exact card_pairs_mem C₁
    refine ⟨?_, ?_, fun heq => ⟨hEdiag, ?_⟩⟩
    · rw [hEK, ← hcardPim]
      exact hPimle.trans (Nat.pow_le_pow_right (by omega) (by norm_num))
    · rw [hfixcard, hEK]
      by_cases h : ∃ e : ↥E, e ∈ K ∧ (cP e).2 ≠ 1
      · have h1 := hC₁top h
        rw [← hcardPim]
        calc Nat.card Pim * Nat.card C₁ ^ 2 ≤ q ^ 2 * (q ^ 2) ^ 2 :=
              Nat.mul_le_mul hPimle (Nat.pow_le_pow_left h1 2)
          _ = q ^ 6 := by ring
      · push Not at h
        rw [hPimtriv h, one_mul]
        calc Nat.card C₁ ^ 2 ≤ (q ^ 3) ^ 2 := Nat.pow_le_pow_left hC₁le 2
          _ = q ^ 6 := by ring
    · rw [hfixcard, hEK] at heq
      rw [hfixcard]
      by_cases h : ∃ e : ↥E, e ∈ K ∧ (cP e).2 ≠ 1
      · right
        have h1 := hC₁top h
        rw [← hcardPim] at heq
        have h2 : Nat.card C₁ ^ 2 ≤ q ^ 4 := by
          calc Nat.card C₁ ^ 2 ≤ (q ^ 2) ^ 2 := Nat.pow_le_pow_left h1 2
            _ = q ^ 4 := by ring
        by_contra hne
        have h3 : Nat.card C₁ ^ 2 < q ^ 4 := lt_of_le_of_ne h2 hne
        have h4 : Nat.card Pim * Nat.card C₁ ^ 2 < q ^ 2 * q ^ 4 := by
          calc Nat.card Pim * Nat.card C₁ ^ 2 ≤ q ^ 2 * Nat.card C₁ ^ 2 :=
                Nat.mul_le_mul_right _ hPimle
            _ < q ^ 2 * q ^ 4 := Nat.mul_lt_mul_of_pos_left h3 (by positivity)
        rw [heq] at h4
        have : q ^ 2 * q ^ 4 = q ^ 6 := by ring
        omega
      · left
        push Not at h
        rw [eq_bot_iff]
        intro e he
        rw [Subgroup.mem_bot]
        refine Equiv.ext fun v => ?_
        rw [hrep ⟨e, he⟩ v, hdiag ⟨e, he⟩, h ⟨e, he⟩ (hKtop _), tens_one_one]
        rfl
  ·
    push Not at hdiag
    obtain ⟨e₀, he₀⟩ := hdiag
    set c₀ := (cP e₀).1 with hc₀
    set P₀ := (cP e₀).2 with hP₀
    have hfixmem : ∀ v ∈ fixPts (E : Set (Equiv.Perm (Fin 2 → Fin 3 → F))), tens c₀ P₀ v = v := by
      intro v hv
      rw [← hrep e₀ v]
      exact hv e₀ e₀.2
    have hcoord : ∀ v ∈ fixPts (E : Set (Equiv.Perm (Fin 2 → Fin 3 → F))), ∀ i, v i ∈ C₁ := by
      intro v hv i
      refine (hC₁mem _).mpr fun e he => ?_
      have h1 := hv e e.2
      rw [hrep, (hKmem e).mp he, tens_one] at h1
      exact (dact_eq_self_iff _ v).mp h1 i
    have hfixle : Nat.card (fixPts (E : Set (Equiv.Perm (Fin 2 → Fin 3 → F)))) ≤ Nat.card C₁ := by
      rcases offDiag_ne_zero_of_mul_self (hcP e₀).1 he₀ with h01 | h10
      · refine Nat.card_le_card_of_injective
          (fun v : ↥(fixPts (E : Set (Equiv.Perm (Fin 2 → Fin 3 → F)))) =>
            (⟨v.1 0, hcoord v.1 v.2 0⟩ : ↥C₁))
          fun v w hvw => ?_
        have h1 : v.1 0 = w.1 0 := congrArg Subtype.val hvw
        have h2 : tens c₀ P₀ (v.1 - w.1) = v.1 - w.1 := by
          rw [tens_sub, hfixmem v.1 v.2, hfixmem w.1 w.2]
        have h3 := eq_zero_of_tens_fixed_zero (hcP e₀).2.1 h01 h2 (by
          rw [Pi.sub_apply, h1, sub_self])
        exact Subtype.ext (sub_eq_zero.mp h3)
      · refine Nat.card_le_card_of_injective
          (fun v : ↥(fixPts (E : Set (Equiv.Perm (Fin 2 → Fin 3 → F)))) =>
            (⟨v.1 1, hcoord v.1 v.2 1⟩ : ↥C₁))
          fun v w hvw => ?_
        have h1 : v.1 1 = w.1 1 := congrArg Subtype.val hvw
        have h2 : tens c₀ P₀ (v.1 - w.1) = v.1 - w.1 := by
          rw [tens_sub, hfixmem v.1 v.2, hfixmem w.1 w.2]
        have h3 := eq_zero_of_tens_fixed_one (hcP e₀).2.1 h10 h2 (by
          rw [Pi.sub_apply, h1, sub_self])
        exact Subtype.ext (sub_eq_zero.mp h3)
    have hKle : Nat.card K ≤ q ^ 2 := by rw [← hcardPim]; exact hPimle
    have hEle : Nat.card E ≤ Nat.card K * q := by
      rw [hcardE]
      exact Nat.mul_le_mul_left _ hrange
    have h5 :
        Nat.card E * Nat.card (fixPts (E : Set (Equiv.Perm (Fin 2 → Fin 3 → F)))) ≤ q ^ 5 := by
      calc Nat.card E * Nat.card (fixPts (E : Set (Equiv.Perm (Fin 2 → Fin 3 → F)))) ≤
            (Nat.card K * q) * Nat.card C₁ := Nat.mul_le_mul hEle hfixle
        _ = (Nat.card K * Nat.card C₁) * q := by ring
        _ ≤ q ^ 4 * q := Nat.mul_le_mul_right _ hPC
        _ = q ^ 5 := by ring
    have h56 : q ^ 5 < q ^ 6 := Nat.pow_lt_pow_right (by omega) (by norm_num)
    refine ⟨?_, h5.trans h56.le, fun heq => absurd heq (by omega)⟩
    calc Nat.card E ≤ Nat.card K * q := hEle
      _ ≤ q ^ 2 * q := Nat.mul_le_mul_right _ hKle
      _ = q ^ 3 := by ring

omit [CharP F 2] [Finite F] in
theorem mul_self_eq_one_of_semilinear {e : Equiv.Perm (Fin 2 → Fin 3 → F)} (hinv : e * e = 1)
    {σ : F ≃+* F} (hσ : ∀ (μ : F) v, e (μ • v) = σ μ • e v) : σ * σ = 1 := by
  set w : Fin 2 → Fin 3 → F := fun _ => Pi.single 0 1 with hw
  have hw0 : w ≠ 0 := by
    intro h
    have := congrFun (congrFun h 0) 0
    simp [hw] at this
  have hee : ∀ v, e (e v) = v := fun v => congrArg (fun f : Equiv.Perm _ => f v) hinv
  refine RingEquiv.ext fun μ => ?_
  have h1 : e (e (μ • w)) = μ • w := hee _
  rw [hσ, hσ, hee] at h1
  exact smul_left_injective F hw0 h1

theorem card_mul_card_fixPts_le {E : Subgroup (Equiv.Perm (Fin 2 → Fin 3 → F))}
    (hadd : E ≤ addPerms F) (hn : ∀ e ∈ E, NormalizesDact ⇑e)
    (hc : ∀ e ∈ E, ∀ f ∈ E, e * f = f * e) (hinv : ∀ e ∈ E, e * e = 1) :
    Nat.card E * Nat.card (fixPts (E : Set (Equiv.Perm (Fin 2 → Fin 3 → F)))) ≤
        Nat.card F ^ 6 ∧
      (Nat.card E * Nat.card (fixPts (E : Set (Equiv.Perm (Fin 2 → Fin 3 → F)))) =
          Nat.card F ^ 6 →
        E ≤ diagPerms F ∧
          (E = ⊥ ∨ Nat.card (fixPts (E : Set (Equiv.Perm (Fin 2 → Fin 3 → F)))) =
            Nat.card F ^ 4)) := by
  classical
  set q := Nat.card F with hq
  have hq2 : 2 ≤ q := two_le_card_field
  by_cases hlin : E ≤ linPerms F
  · obtain ⟨-, h2, h3⟩ := card_mul_card_fixPts_le_of_lin hadd hlin hn hc hinv
    exact ⟨h2, h3⟩
  obtain ⟨e₀, he₀E, he₀lin⟩ : ∃ e₀ ∈ E, e₀ ∉ linPerms F := by
    by_contra h
    push Not at h
    exact hlin h
  obtain ⟨σ₀, hσ₀⟩ := exists_semilinear_perm (hadd he₀E) (hn e₀ he₀E) (hn _ (E.inv_mem he₀E))
  have hσ₀1 : σ₀ ≠ 1 := by
    intro h
    apply he₀lin
    intro μ v
    rw [hσ₀, h]
    rfl
  obtain ⟨θ, hθ⟩ : ∃ θ : F, σ₀ θ ≠ θ := by
    by_contra h
    push Not at h
    exact hσ₀1 (RingEquiv.ext h)
  set E₁ := E ⊓ linPerms F with hE₁
  have hhalf := card_fixPts_sq_le (E := E) (E₁ := E₁) le_rfl hadd he₀E hσ₀ hθ
  have hsemi : ∀ e ∈ E, e ∉ linPerms F → e₀ * e ∈ E₁ := by
    intro e he helin
    obtain ⟨σ, hσ⟩ := exists_semilinear_perm (hadd he) (hn e he) (hn _ (E.inv_mem he))
    have hσ1 : σ ≠ 1 := by
      intro h
      apply helin
      intro μ v
      rw [hσ, h]
      rfl
    have hσσ := mul_self_eq_one_of_semilinear (hinv e he) hσ
    have hσ₀σ₀ := mul_self_eq_one_of_semilinear (hinv e₀ he₀E) hσ₀
    have heq : σ = σ₀ := eq_of_mul_self_eq_one hσσ hσ₀σ₀ hσ1 hσ₀1
    refine ⟨E.mul_mem he₀E he, fun μ v => ?_⟩
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hσ, hσ₀, heq]
    have h1 : σ₀ (σ₀ μ) = μ := congrArg (fun ρ : F ≃+* F => ρ μ) hσ₀σ₀
    rw [h1]
  have hE₂ : Nat.card E ≤ Nat.card E₁ * 2 := by
    let f : ↥E → ↥E₁ × Bool := fun e =>
      if h : (e : Equiv.Perm _) ∈ linPerms F then (⟨e, e.2, h⟩, false)
      else (⟨e₀ * e, hsemi e e.2 h⟩, true)
    have hf : Function.Injective f := by
      intro e e' hee
      by_cases h : (e : Equiv.Perm _) ∈ linPerms F <;>
        by_cases h' : (e' : Equiv.Perm _) ∈ linPerms F <;>
        simp only [f, h, h', ↓reduceDIte, Prod.mk.injEq,
          Bool.false_eq_true, Bool.true_eq_false, and_false, and_true] at hee
      · exact Subtype.ext (congrArg (fun x : ↥E₁ => (x : Equiv.Perm (Fin 2 → Fin 3 → F))) hee)
      · exact Subtype.ext (mul_left_cancel
          (congrArg (fun x : ↥E₁ => (x : Equiv.Perm (Fin 2 → Fin 3 → F))) hee))
    have h1 := Nat.card_le_card_of_injective f hf
    rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at h1
  have hE₁add : E₁ ≤ addPerms F := inf_le_left.trans hadd
  have hE₁lin : E₁ ≤ linPerms F := inf_le_right
  obtain ⟨hE₁le, hE₁fix, -⟩ := card_mul_card_fixPts_le_of_lin hE₁add hE₁lin
    (fun e he => hn e he.1) (fun e he f hf => hc e he.1 f hf.1) (fun e he => hinv e he.1)
  set a := Nat.card E
  set b := Nat.card (fixPts (E : Set (Equiv.Perm (Fin 2 → Fin 3 → F))))
  set a₁ := Nat.card E₁
  set b₁ := Nat.card (fixPts (E₁ : Set (Equiv.Perm (Fin 2 → Fin 3 → F))))
  have hsq : (a * b) ^ 2 < (q ^ 6) ^ 2 := by
    have h1 : (a * b) ^ 2 ≤ (a₁ * 2) ^ 2 * b₁ := by
      rw [mul_pow]
      exact Nat.mul_le_mul (Nat.pow_le_pow_left hE₂ 2) hhalf
    have h2 : (a₁ * 2) ^ 2 * b₁ = 4 * a₁ * (a₁ * b₁) := by ring
    have h3 : 4 * a₁ * (a₁ * b₁) ≤ 4 * q ^ 3 * q ^ 6 :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ hE₁le) hE₁fix
    have h4 : 4 * q ^ 3 * q ^ 6 < (q ^ 6) ^ 2 := by
      have h5 : 8 ≤ q ^ 3 := by
        calc 8 = 2 ^ 3 := by norm_num
          _ ≤ q ^ 3 := Nat.pow_le_pow_left hq2 3
      have h6 : (q ^ 6) ^ 2 = q ^ 3 * q ^ 3 * q ^ 6 := by ring
      rw [h6]
      have h7 : 0 < q ^ 6 := by positivity
      have h8 : 4 * q ^ 3 < q ^ 3 * q ^ 3 := by nlinarith
      exact Nat.mul_lt_mul_of_pos_right h8 h7
    rw [h2] at h1
    exact lt_of_le_of_lt (h1.trans h3) h4
  have hlt : a * b < q ^ 6 := by
    by_contra h
    push Not at h
    have := Nat.pow_le_pow_left h 2
    omega
  exact ⟨hlt.le, fun heq => absurd heq hlt.ne⟩

end CharTwo

end CFSG.Quasithin.H13.Ch4
