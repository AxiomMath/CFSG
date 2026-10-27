module

public import CFSG.Quasithin.H13.KGLieTwFrame

public section

namespace CFSG.Quasithin.H13.KGLie

open CFSG.Open CFSG.Quasithin Subgroup
open scoped Matrix

section Det

variable {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F] [CharP F 2]

omit [DecidableEq ι] [CharP F 2] in
theorem twist_apply (a : ℕ) (g X : Matrix ι ι F) (i j : ι) :
    twist a g X i j = ∑ k, ∑ l, g i k * X k l * g j l ^ 2 ^ a := by
  simp only [twist, Matrix.mul_apply, Matrix.transpose_apply, frobPow, Matrix.map_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm]

abbrev unitM (i : ι) : Matrix ι ι F := Matrix.single i i 1

theorem twist_inv_twist {a : ℕ} {g : Matrix.GeneralLinearGroup ι F} {X : Matrix ι ι F} :
    twist a ((g⁻¹ : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F)
      (twist a (g : Matrix ι ι F) X) = X := by
  rw [← twist_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, twist_one]

theorem exists_fixed_of_twData [Finite F] {a : ℕ} (hF : Nat.card F = 2 ^ (2 * a))
    {Γ : Subgroup (Matrix.GeneralLinearGroup ι F)} {U : Subgroup ↥Γ} (hU2 : IsPGroup 2 U)
    {T : Matrix ι ι F → Matrix ι ι F} (hT : TwData a Γ U T) :
    ∃ X, IsHerm a X ∧ T X - X ≠ 0 ∧ ∀ u ∈ U,
      twist a (((u : ↥Γ) : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F) (T X - X) = T X - X := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set imN : Set (Matrix ι ι F) := {Y | ∃ X, IsHerm a X ∧ T X - X = Y} with himN
  have hT0 : T 0 = 0 := by
    have h1 := hT.add 0 0 (isHerm_zero a) (isHerm_zero a)
    rw [add_zero] at h1
    exact add_eq_left.mp h1.symm
  have h0 : (0 : Matrix ι ι F) ∈ imN := ⟨0, isHerm_zero a, by rw [hT0, sub_zero]⟩
  have hadd : ∀ Y Y', Y ∈ imN → Y' ∈ imN → Y + Y' ∈ imN := by
    rintro _ _ ⟨X, hX, rfl⟩ ⟨X', hX', rfl⟩
    refine ⟨X + X', isHerm_add hX hX', ?_⟩
    rw [hT.add X X' hX hX']
    abel
  have hcard : imN.ncard ≤ 4 := hT.card
  have hmem : ∀ u ∈ U, ∀ Y ∈ imN,
      twist a (((u : ↥Γ) : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F) Y ∈ imN := by
    rintro u hu _ ⟨X, hX, rfl⟩
    exact ⟨_, isHerm_twist hF _ hX, by rw [twist_sub, hT.comm u hu X hX]⟩
  have hinj : ∀ (u : ↥Γ) (Y : Matrix ι ι F),
      twist a ((u : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F) Y = 0 → Y = 0 := by
    intro u Y h
    have := congrArg (twist a ((((u : Matrix.GeneralLinearGroup ι F))⁻¹ :
      Matrix.GeneralLinearGroup ι F) : Matrix ι ι F)) h
    rwa [twist_inv_twist, twist_zero] at this
  have h2 : ∀ M : Matrix ι ι F, M + M = 0 := fun M => by
    rw [← two_smul F M, CharTwo.two_eq_zero, zero_smul]
  obtain ⟨X₀, hX₀, hTX₀⟩ := hT.ne
  set Y₀ := T X₀ - X₀ with hY₀
  have hY₀0 : Y₀ ≠ 0 := sub_ne_zero.mpr hTX₀
  have hY₀m : Y₀ ∈ imN := ⟨X₀, hX₀, rfl⟩
  by_cases hfix : ∀ u ∈ U,
      twist a (((u : ↥Γ) : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F) Y₀ = Y₀
  · exact ⟨X₀, hX₀, hY₀0, hfix⟩
  push Not at hfix
  obtain ⟨u₀, hu₀, hY₁⟩ := hfix
  set Y₁ := twist a (((u₀ : ↥Γ) : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F) Y₀ with hY₁d
  have hY₁m : Y₁ ∈ imN := hmem u₀ hu₀ Y₀ hY₀m
  have hY₁0 : Y₁ ≠ 0 := fun h => hY₀0 (hinj _ _ h)
  have hY₂m : Y₀ + Y₁ ∈ imN := hadd _ _ hY₀m hY₁m
  have hY₂0 : Y₀ + Y₁ ≠ 0 := by
    intro h
    apply hY₁
    have := congrArg (· + Y₁) h
    simp only [zero_add, add_assoc, h2, add_zero] at this
    exact this.symm
  have hY₂1 : Y₀ + Y₁ ≠ Y₀ := by
    intro h
    apply hY₁0
    have := congrArg (Y₀ + ·) h
    simpa only [← add_assoc, h2, zero_add] using this
  have hY₂2 : Y₀ + Y₁ ≠ Y₁ := by
    intro h
    apply hY₀0
    have := congrArg (· + Y₁) h
    simpa only [add_assoc, h2, add_zero] using this
  set S3 : Set (Matrix ι ι F) := {Y₀, Y₁, Y₀ + Y₁} with hS3
  have hS3c : S3.ncard = 3 := by
    rw [Set.ncard_eq_three]
    exact ⟨Y₀, Y₁, Y₀ + Y₁, fun h => hY₁ h.symm, hY₂1.symm, hY₂2.symm, rfl⟩
  have hsub : insert 0 S3 ⊆ imN := by
    intro Y hY
    rcases hY with rfl | rfl | rfl | rfl
    · exact h0
    · exact hY₀m
    · exact hY₁m
    · exact hY₂m
  have h0S : (0 : Matrix ι ι F) ∉ S3 := by
    rintro (h | h | h)
    · exact hY₀0 h.symm
    · exact hY₁0 h.symm
    · exact hY₂0 h.symm
  have heq : insert 0 S3 = imN := by
    refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)
    rw [Set.ncard_insert_of_notMem h0S, hS3c]
    exact hcard
  have hS3mem : ∀ Y, Y ∈ S3 ↔ Y ∈ imN ∧ Y ≠ 0 := by
    intro Y
    constructor
    · intro hY
      exact ⟨heq ▸ Set.mem_insert_of_mem 0 hY, fun h => h0S (h ▸ hY)⟩
    · rintro ⟨hY, hY0⟩
      rw [← heq] at hY
      rcases hY with h | h
      · exact absurd h hY0
      · exact h
  let act : MulAction ↥U ↥S3 :=
    { smul := fun u Y => ⟨twist a ((((u : ↥U) : ↥Γ) : Matrix.GeneralLinearGroup ι F) :
          Matrix ι ι F) Y.1, (hS3mem _).2 ⟨hmem u u.2 Y.1 ((hS3mem _).1 Y.2).1,
            fun h => ((hS3mem _).1 Y.2).2 (hinj _ _ h)⟩⟩
      one_smul := fun Y => Subtype.ext (twist_one a Y.1)
      mul_smul := fun u u' Y => Subtype.ext (twist_mul a _ _ Y.1) }
  have hodd : ¬ 2 ∣ Nat.card ↥S3 := by
    rw [Nat.card_coe_set_eq, hS3c]
    norm_num
  obtain ⟨⟨Y, hYS⟩, hYfix⟩ := IsPGroup.nonempty_fixed_point_of_prime_not_dvd_card hU2 ↥S3 hodd
  obtain ⟨⟨X, hX, rfl⟩, hY0⟩ := (hS3mem _).1 hYS
  refine ⟨X, hX, hY0, fun u hu => ?_⟩
  have := congrArg Subtype.val (hYfix ⟨u, hu⟩)
  exact this

omit [Fintype ι] [DecidableEq ι] in
theorem isHerm_sub {a : ℕ} {X Y : Matrix ι ι F} (hX : IsHerm a X) (hY : IsHerm a Y) :
    IsHerm a (X - Y) := by
  have h2 : ∀ M : Matrix ι ι F, -M = M := fun M => by
    rw [neg_eq_iff_add_eq_zero, ← two_smul F M, CharTwo.two_eq_zero, zero_smul]
  rw [sub_eq_add_neg, h2]
  exact isHerm_add hX hY

omit [Fintype ι] [CharP F 2] in
theorem isHerm_unitM (a : ℕ) (i : ι) : IsHerm a (unitM i : Matrix ι ι F) := by
  unfold IsHerm
  ext j k
  simp only [unitM, Matrix.transpose_apply, frobPow, Matrix.map_apply, Matrix.single_apply]
  by_cases h1 : i = j <;> by_cases h2 : i = k <;> simp [h1, h2]

omit [Fintype ι] [DecidableEq ι] [CharP F 2] in
theorem isHerm_diag {a : ℕ} {X : Matrix ι ι F} (hX : IsHerm a X) (i : ι) :
    X i i ^ 2 ^ a = X i i := by
  have := congrFun (congrFun hX i) i
  simpa [frobPow] using this

theorem det_twist {a : ℕ} {g : Matrix ι ι F} (hg : g.det = 1) (X : Matrix ι ι F) :
    (twist a g X).det = X.det := by
  have hσ : (frobPow a g).det = 1 := by
    rw [frobPow_eq_map]
    have := (iterateFrobenius F 2 a).map_det g
    rw [hg, map_one] at this
    exact this.symm
  rw [twist, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hg, hσ, one_mul, mul_one]

omit [CharP F 2] in
theorem det_one_add_unitM {hi lo : ι} (h : hi ≠ lo) (b c : F) :
    (1 + b • unitM lo + c • unitM hi : Matrix ι ι F).det = (1 + c) * (1 + b) := by
  have e : (1 + b • unitM lo + c • unitM hi : Matrix ι ι F) = Matrix.diagonal
      (fun i => (if i = hi then 1 + c else 1) * (if i = lo then 1 + b else 1)) := by
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.single_apply,
      Matrix.diagonal_apply, unitM, smul_eq_mul]
    by_cases hij : i = j
    · subst hij
      by_cases h1 : i = hi
      · subst h1
        simp [h, Ne.symm h]
      · by_cases h2 : i = lo
        · subst h2
          simp [h1, Ne.symm h1]
        · simp [h1, h2, Ne.symm h1, Ne.symm h2]
    · have e1 : ¬ (lo = i ∧ lo = j) := fun h' => hij (h'.1.symm.trans h'.2)
      have e2 : ¬ (hi = i ∧ hi = j) := fun h' => hij (h'.1.symm.trans h'.2)
      simp [hij, e1, e2]
  rw [e, Matrix.det_diagonal, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.prod_ite_eq']
  simp

theorem false_of_twData [Finite F] {a : ℕ} (hF : Nat.card F = 2 ^ (2 * a)) (ha : a = 1 ∨ a = 2)
    {Γ : Subgroup (Matrix.GeneralLinearGroup ι F)}
    (hdet : ∀ γ : ↥Γ, ((γ : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F).det = 1)
    {U : Subgroup ↥Γ} (hU2 : IsPGroup 2 U) {hi lo : ι} (hilo : hi ≠ lo)
    (hRC : ∀ X, IsHerm a X → (∀ u ∈ U,
      twist a (((u : ↥Γ) : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F) X = X) →
      X = X hi hi • unitM hi)
    (hRS : ∀ χ : Matrix ι ι F → F, (∀ X Y, IsHerm a X → IsHerm a Y → χ (X + Y) = χ X + χ Y) →
      (∀ k : F, k ^ 2 ^ a = k → ∀ X, IsHerm a X → χ (k • X) = k * χ X) →
      (∀ u ∈ U, ∀ X, IsHerm a X →
        χ (twist a (((u : ↥Γ) : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F) X) = χ X) →
      χ (unitM hi) = 0 → χ 1 = χ (unitM lo) ∧ (χ (unitM lo) = 0 → ∀ X, IsHerm a X → χ X = 0))
    (w : ↥Γ) (hw1 : twist a ((w : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F) (unitM hi) =
      unitM lo)
    (hw2 : twist a ((w : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F) 1 = 1)
    {T : Matrix ι ι F → Matrix ι ι F} (hT : TwData a Γ U T)
    (hrank : a = 1 → ∀ X, IsHerm a X → T X - X = 0 ∨ T X - X = unitM hi) : False := by
  classical
  have h2M : ∀ M : Matrix ι ι F, M + M = 0 := fun M => by
    rw [← two_smul F M, CharTwo.two_eq_zero, zero_smul]
  have hT0 : T 0 = 0 := by
    have h1 := hT.add 0 0 (isHerm_zero a) (isHerm_zero a)
    rw [add_zero] at h1
    exact add_eq_left.mp h1.symm
  have hTsub : ∀ X Y, IsHerm a X → IsHerm a Y → T (X - Y) = T X - T Y := by
    intro X Y hX hY
    have h1 := hT.add (X - Y) Y (isHerm_sub hX hY) hY
    rw [sub_add_cancel] at h1
    rw [h1]
    abel
  obtain ⟨X₀, hX₀, hY0, hYfix⟩ := exists_fixed_of_twData hF hU2 hT
  have hY₀h : IsHerm a (T X₀ - X₀) := isHerm_sub (hT.herm X₀ hX₀) hX₀
  have hY₀E := hRC _ hY₀h hYfix
  set c₀ := (T X₀ - X₀) hi hi with hc₀
  have hc₀0 : c₀ ≠ 0 := by
    intro h
    apply hY0
    rw [hY₀E, h, zero_smul]
  have hc₀f : c₀ ^ 2 ^ a = c₀ := isHerm_diag hY₀h hi
  have hEfix : ∀ u ∈ U,
      twist a (((u : ↥Γ) : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F) (unitM hi) =
        unitM hi := by
    intro u hu
    have h1 := hYfix u hu
    rw [hY₀E, twist_smul] at h1
    exact smul_right_injective _ hc₀0 h1
  have hN : ∀ X, IsHerm a X → ∃ c : F, T X - X = c • unitM hi := by
    rcases ha with rfl | rfl
    · intro X hX
      rcases hrank rfl X hX with h | h
      · exact ⟨0, by rw [h, zero_smul]⟩
      · exact ⟨1, by rw [h, one_smul]⟩
    · intro X hX
      set imN : Set (Matrix ι ι F) := {Y | ∃ X, IsHerm 2 X ∧ T X - X = Y} with himN
      set A : Set (Matrix ι ι F) := {Y | ∃ k : F, k ^ 2 ^ 2 = k ∧ Y = k • unitM hi} with hA
      have hAsub : A ⊆ imN := by
        rintro _ ⟨k, hk, rfl⟩
        have hk' : (k * c₀⁻¹) ^ 2 ^ 2 = k * c₀⁻¹ := by rw [mul_pow, inv_pow, hk, hc₀f]
        refine ⟨(k * c₀⁻¹) • X₀, isHerm_smul hk' hX₀, ?_⟩
        rw [hT.smul _ hk' X₀ hX₀, ← smul_sub, hY₀E, smul_smul, mul_assoc, inv_mul_cancel₀ hc₀0,
          mul_one]
      have hAcard : 4 ≤ A.ncard := by
        have h3 := card_fixUnits_ge (a := 2) hF
        have hinj : Function.Injective (fun o : Option {k : Fˣ // (k : F) ^ 2 ^ 2 = k} =>
            (⟨match o with
              | none => 0
              | some k => (k.1 : F) • unitM hi, by
                rcases o with _ | k
                · exact ⟨0, by norm_num, by rw [zero_smul]⟩
                · exact ⟨k.1, k.2, rfl⟩⟩ : ↥A)) := by
          have hE : ∀ c : F, (c • unitM hi : Matrix ι ι F) hi hi = c := fun c => by
            simp [unitM]
          rintro (_ | k) (_ | k') h <;> have h' := congrArg (fun Y : ↥A => (Y : Matrix ι ι F)
            hi hi) h <;> simp only [hE, Matrix.zero_apply] at h'
          · rfl
          · exact absurd h'.symm k'.1.ne_zero
          · exact absurd h' k.1.ne_zero
          · exact congrArg some (Subtype.ext (Units.ext h'))
        have h3' : 3 ≤ Nat.card {k : Fˣ // (k : F) ^ 2 ^ 2 = k} := le_trans (by norm_num) h3
        have h4 : 4 ≤ Nat.card {x // x ∈ A} := by
          have := Nat.card_le_card_of_injective _ hinj
          rw [Finite.card_option] at this
          omega
        exact h4
      have hcN : imN.ncard ≤ 4 := hT.card
      have heq : A = imN :=
        Set.eq_of_subset_of_ncard_le hAsub (hcN.trans hAcard) (Set.toFinite _)
      have hmem : T X - X ∈ A := heq ▸ ⟨X, hX, rfl⟩
      obtain ⟨k, -, hk⟩ := hmem
      exact ⟨k, hk⟩
  set χ : Matrix ι ι F → F := fun X => (T X - X) hi hi with hχ
  have hEhi : ∀ c : F, (c • unitM hi : Matrix ι ι F) hi hi = c := fun c => by simp [unitM]
  have hTχ : ∀ X, IsHerm a X → T X - X = χ X • unitM hi := by
    intro X hX
    obtain ⟨c, hc⟩ := hN X hX
    rw [hc, hχ]
    simp only [hc, hEhi]
  have hχadd : ∀ X Y, IsHerm a X → IsHerm a Y → χ (X + Y) = χ X + χ Y := by
    intro X Y hX hY
    simp only [hχ]
    rw [hT.add X Y hX hY, show T X + T Y - (X + Y) = (T X - X) + (T Y - Y) by abel,
      Matrix.add_apply]
  have hχsmul : ∀ k : F, k ^ 2 ^ a = k → ∀ X, IsHerm a X → χ (k • X) = k * χ X := by
    intro k hk X hX
    simp only [hχ]
    rw [hT.smul k hk X hX, ← smul_sub, Matrix.smul_apply, smul_eq_mul]
  have hχU : ∀ u ∈ U, ∀ X, IsHerm a X →
      χ (twist a (((u : ↥Γ) : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F) X) = χ X := by
    intro u hu X hX
    simp only [hχ]
    rw [hT.comm u hu X hX, ← twist_sub, hTχ X hX, twist_smul, hEfix u hu, hEhi]
  have hχE : χ (unitM hi) = 0 := by
    have h1 : T (T X₀ - X₀) - (T X₀ - X₀) = 0 := by
      rw [hTsub _ _ (hT.herm X₀ hX₀) hX₀, hT.invol X₀ hX₀]
      rw [show X₀ - T X₀ - (T X₀ - X₀) = (X₀ - T X₀) + (X₀ - T X₀) by abel, h2M]
    have h2 : χ (T X₀ - X₀) = 0 := by
      simp only [hχ]
      rw [h1, Matrix.zero_apply]
    rw [hY₀E, hχsmul c₀ hc₀f _ (isHerm_unitM a hi)] at h2
    exact (mul_eq_zero.mp h2).resolve_left hc₀0
  obtain ⟨hχ1, hχ0⟩ := hRS χ hχadd hχsmul hχU hχE
  set b := χ 1 with hb
  have hb0 : b ≠ 0 := by
    intro h0
    obtain ⟨X, hX, hTX⟩ := hT.ne
    apply hTX
    have h3 := hχ0 (h0 ▸ hχ1.symm) X hX
    have h4 := hTχ X hX
    rw [h3, zero_smul, sub_eq_zero] at h4
    exact h4
  have hbf : b ^ 2 ^ a = b := isHerm_diag (isHerm_sub (hT.herm 1 (isHerm_one a)) (isHerm_one a)) hi
  have hb3 : b ^ 3 = 1 := by
    rcases ha with rfl | rfl
    · have : b * (b - 1) = 0 := by linear_combination hbf
      have hb1 : b = 1 := sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hb0)
      rw [hb1, one_pow]
    · have : b * (b ^ 3 - 1) = 0 := by linear_combination hbf
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hb0)
  obtain ⟨γ', hγ'⟩ := hT.norm w
  have hT1 : T 1 = 1 + b • unitM hi := by
    rw [← hTχ 1 (isHerm_one a)]
    abel
  have hblo : IsHerm a (b • unitM lo : Matrix ι ι F) := isHerm_smul hbf (isHerm_unitM a lo)
  have h1 := hγ' 1 (isHerm_one a)
  rw [hT1, twist_add, twist_smul, hw1, hw2] at h1
  have h3 : T (1 + b • unitM lo) = 1 + b • unitM lo + (b + b * b) • unitM hi := by
    have h4 := hTχ _ (isHerm_add (isHerm_one a) hblo)
    rw [hχadd 1 _ (isHerm_one a) hblo, hχsmul b hbf _ (isHerm_unitM a lo), ← hχ1, ← hb] at h4
    rw [← h4]
    abel
  rw [h3] at h1
  have hdet1 := congrArg Matrix.det h1
  rw [det_twist (hdet γ'), Matrix.det_one, det_one_add_unitM hilo] at hdet1
  have h2F : (2 : F) = 0 := CharTwo.two_eq_zero
  have : (1 : F) = 0 := by
    linear_combination -hdet1 + hb3 + (1 + b + b ^ 2) * h2F
  exact one_ne_zero this

@[expose] def hermOff (a : ℕ) (i j : ι) (t : F) : Matrix ι ι F :=
  Matrix.single i j t + Matrix.single j i (t ^ 2 ^ a)

abbrev nrm (a : ℕ) (t : F) : F := t * t ^ 2 ^ a

abbrev trc (a : ℕ) (t : F) : F := t + t ^ 2 ^ a

omit [CharP F 2] in
theorem exists_frob_ne [Finite F] {a : ℕ} (ha : 1 ≤ a) (hF : Nat.card F = 2 ^ (2 * a)) :
    ∃ θ : F, θ ^ 2 ^ a ≠ θ := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  refine ⟨g, fun h => ?_⟩
  have hog : orderOf g = 2 ^ (2 * a) - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, hF]
  have hx1 : 1 ≤ 2 ^ a := Nat.one_le_two_pow
  have h1 : g ^ (2 ^ a - 1) = 1 := by
    have hg0 : (g : F) ≠ 0 := g.ne_zero
    have h2 : (g : F) ^ (2 ^ a - 1) * g = 1 * g := by
      rw [← pow_succ, Nat.sub_add_cancel hx1, h, one_mul]
    exact Units.ext (by rw [Units.val_pow_eq_pow_val, mul_right_cancel₀ hg0 h2, Units.val_one])
  have hdvd := orderOf_dvd_of_pow_eq_one h1
  rw [hog] at hdvd
  have h4 : 2 ≤ 2 ^ a := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
  have h3 : 0 < 2 ^ a - 1 := by omega
  have h5 : 2 ^ (2 * a) = 2 ^ a * 2 ^ a := by rw [two_mul, pow_add]
  have h6 : 2 ^ a - 1 < 2 ^ (2 * a) - 1 := by
    rw [h5]
    have : 2 ^ a < 2 ^ a * 2 ^ a := by
      calc 2 ^ a = 2 ^ a * 1 := (mul_one _).symm
        _ < 2 ^ a * 2 ^ a := Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
    omega
  exact absurd (Nat.le_of_dvd h3 hdvd) (not_le.mpr h6)

theorem trc_ne_zero {a : ℕ} {θ : F} (h : θ ^ 2 ^ a ≠ θ) : θ + θ ^ 2 ^ a ≠ 0 := by
  intro h0
  apply h
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  linear_combination h0 - θ * h2

omit [CharP F 2] in
theorem frob_frob [Finite F] {a : ℕ} (hF : Nat.card F = 2 ^ (2 * a)) (t : F) :
    (t ^ 2 ^ a) ^ 2 ^ a = t := by
  have : Fintype F := Fintype.ofFinite F
  rw [← pow_mul, ← pow_add, ← two_mul, ← hF, Nat.card_eq_fintype_card, FiniteField.pow_card]

omit [Fintype ι] in
theorem isHerm_hermOff [Finite F] {a : ℕ} (hF : Nat.card F = 2 ^ (2 * a)) (i j : ι) (t : F) :
    IsHerm a (hermOff a i j t) := by
  unfold IsHerm hermOff
  rw [frobPow_add, frobPow_eq_map, frobPow_eq_map, Matrix.map_single, Matrix.map_single,
    Matrix.transpose_add, Matrix.transpose_single, Matrix.transpose_single, add_comm]
  congr 2
  exact frob_frob hF t

omit [CharP F 2] in
theorem frob_nrm [Finite F] {a : ℕ} (hF : Nat.card F = 2 ^ (2 * a)) (t : F) :
    nrm a t ^ 2 ^ a = nrm a t := by
  rw [nrm, mul_pow, frob_frob hF, mul_comm]

theorem frob_trc [Finite F] {a : ℕ} (hF : Nat.card F = 2 ^ (2 * a)) (t : F) :
    trc a t ^ 2 ^ a = trc a t := by
  rw [trc, add_pow_char_pow, frob_frob hF, add_comm]

omit [CharP F 2] in
theorem card_fix_ge [Finite F] {a : ℕ} (hF : Nat.card F = 2 ^ (2 * a)) :
    2 ^ a ≤ Nat.card {k : F // k ^ 2 ^ a = k} := by
  have h3 := card_fixUnits_ge hF
  have hinj : Function.Injective (fun o : Option {k : Fˣ // (k : F) ^ 2 ^ a = k} =>
      (match o with
        | none => ⟨0, by rw [zero_pow (by positivity)]⟩
        | some k => ⟨(k.1 : F), k.2⟩ : {k : F // k ^ 2 ^ a = k})) := by
    rintro (_ | k) (_ | k') h
    · rfl
    · exact absurd (congrArg Subtype.val h).symm k'.1.ne_zero
    · exact absurd (congrArg Subtype.val h) k.1.ne_zero
    · exact congrArg some (Subtype.ext (Units.ext (congrArg Subtype.val h)))
  have := Nat.card_le_card_of_injective _ hinj
  rw [Finite.card_option] at this
  have h1 : 1 ≤ 2 ^ a := Nat.one_le_two_pow
  omega

theorem card_hermSub_ge [Finite F] {a : ℕ} (hF : Nat.card F = 2 ^ (2 * a)) {i₀ i₁ : ι}
    (h : i₀ ≠ i₁) :
    Nat.card {k : F // k ^ 2 ^ a = k} * Nat.card {k : F // k ^ 2 ^ a = k} * Nat.card F ≤
      Nat.card ↥(hermSub a ι F) := by
  have hE : ∀ i : ι, IsHerm a (unitM i : Matrix ι ι F) := isHerm_unitM a
  set f : {k : F // k ^ 2 ^ a = k} × {k : F // k ^ 2 ^ a = k} × F → ↥(hermSub a ι F) :=
    fun p => ⟨Multiplicative.ofAdd (p.1.1 • unitM i₀ + p.2.1.1 • unitM i₁ +
      hermOff a i₀ i₁ p.2.2), by
        show IsHerm a _
        exact isHerm_add (isHerm_add (isHerm_smul p.1.2 (hE i₀)) (isHerm_smul p.2.1.2 (hE i₁)))
          (isHerm_hermOff hF i₀ i₁ p.2.2)⟩ with hf
  have hfi : Function.Injective f := by
    rintro ⟨x, y, t⟩ ⟨x', y', t'⟩ hxy
    have hm := congrArg (fun z : ↥(hermSub a ι F) =>
      Multiplicative.toAdd (z : Multiplicative (Matrix ι ι F))) hxy
    have e1 := congrFun (congrFun hm i₀) i₀
    have e2 := congrFun (congrFun hm i₁) i₁
    have e3 := congrFun (congrFun hm i₀) i₁
    simp [hf, hermOff, unitM, h, Ne.symm h] at e1 e2 e3
    exact Prod.ext (Subtype.ext e1) (Prod.ext (Subtype.ext e2) e3)
  have := Nat.card_le_card_of_injective f hfi
  rwa [Nat.card_prod, Nat.card_prod, ← mul_assoc] at this

end Det

end CFSG.Quasithin.H13.KGLie
