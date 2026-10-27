module

public import CFSG.Quasithin.Background.SmithB45M22HatData
public import CFSG.Sporadic.Mathieu.M22
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.CharacterTheory.SteinbergBYNortonCriterion
public import CFSG.Open.QuasithinDefs

public section

namespace CFSG.Quasithin.HatM22

open CFSG.CharacterTheory.SteinbergBY CFSG.CharacterTheory.SteinbergBY.FieldFour
open CFSG.Sporadic.Mathieu CFSG.Open CFSG.Blueprint
open scoped Matrix

@[expose] def hatM22N1 : Matrix (Fin 6) (Fin 6) FieldFour := untab hatM22N1Tab

@[expose] def hatM22N2 : Matrix (Fin 6) (Fin 6) FieldFour := untab hatM22N2Tab

@[expose] def hatM22N2Inv : Matrix (Fin 6) (Fin 6) FieldFour := hatM22N2 * hatM22N2 * hatM22N2

theorem hatM22N1_mul_self : hatM22N1 * hatM22N1 = 1 := by decide +kernel

theorem hatM22N2_mul_inv : hatM22N2 * hatM22N2Inv = 1 := by decide +kernel

theorem hatM22N2Inv_mul : hatM22N2Inv * hatM22N2 = 1 := by decide +kernel

@[expose] def hatM22G1 : Matrix.GeneralLinearGroup (Fin 6) FieldFour :=
  ⟨hatM22N1, hatM22N1, hatM22N1_mul_self, hatM22N1_mul_self⟩

@[expose] def hatM22G2 : Matrix.GeneralLinearGroup (Fin 6) FieldFour :=
  ⟨hatM22N2, hatM22N2Inv, hatM22N2_mul_inv, hatM22N2Inv_mul⟩

@[expose] def hatM22Γ₀ : Subgroup (Matrix.GeneralLinearGroup (Fin 6) FieldFour) :=
  Subgroup.closure {hatM22G1, hatM22G2}

theorem hatM22G1_mem : hatM22G1 ∈ hatM22Γ₀ := Subgroup.subset_closure (Set.mem_insert _ _)

theorem hatM22G2_mem : hatM22G2 ∈ hatM22Γ₀ :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

@[expose] def hatM22B (i : Fin 22) : Matrix (Fin 6) (Fin 3) FieldFour := untab hatM22BTab[i]

@[expose] def hatM22L (i : Fin 22) : Matrix (Fin 3) (Fin 6) FieldFour := untab hatM22LTab[i]

@[expose] def hatM22F (i : Fin 22) : Matrix (Fin 3) (Fin 6) FieldFour := untab hatM22FTab[i]

@[expose] def hatM22U (i : Fin 22) : Submodule FieldFour (Fin 6 → FieldFour) :=
  LinearMap.range (Matrix.toLin' (hatM22B i))

theorem hatM22N1_fwd : ∀ i : Fin 22,
    hatM22N1 * hatM22B i = hatM22B (m22gA i) * (hatM22L (m22gA i) * hatM22N1 * hatM22B i) := by
  decide +kernel

theorem hatM22N1_bwd : ∀ i : Fin 22,
    hatM22N1 * hatM22B i * (hatM22L i * hatM22N1 * hatM22B (m22gA i)) = hatM22B (m22gA i) := by
  decide +kernel

theorem hatM22N2_fwd : ∀ i : Fin 22,
    hatM22N2 * hatM22B i = hatM22B (m22gB i) * (hatM22L (m22gB i) * hatM22N2 * hatM22B i) := by
  decide +kernel

theorem hatM22N2_bwd : ∀ i : Fin 22,
    hatM22N2 * hatM22B i * (hatM22L i * hatM22N2Inv * hatM22B (m22gB i)) =
      hatM22B (m22gB i) := by
  decide +kernel

theorem hatM22F_mul_B : ∀ i : Fin 22, hatM22F i * hatM22B i = 0 := by decide +kernel

theorem hatM22F_mul_B_ne : ∀ i j : Fin 22, i ≠ j → hatM22F j * hatM22B i ≠ 0 := by
  decide +kernel

theorem map_range_toLin'_eq {n k : ℕ} {A : Matrix (Fin n) (Fin n) FieldFour}
    {B B' : Matrix (Fin n) (Fin k) FieldFour} {C D : Matrix (Fin k) (Fin k) FieldFour}
    (h1 : A * B = B' * C) (h2 : A * B * D = B') :
    (LinearMap.range (Matrix.toLin' B)).map (Matrix.toLin' A) =
      LinearMap.range (Matrix.toLin' B') := by
  rw [← LinearMap.range_comp, ← Matrix.toLin'_mul]
  apply le_antisymm
  · rw [h1, Matrix.toLin'_mul]
    exact LinearMap.range_comp_le_range _ _
  · conv_lhs => rw [← h2]
    rw [Matrix.toLin'_mul]
    exact LinearMap.range_comp_le_range _ _

theorem range_le_ker_iff {n k m : ℕ} (F : Matrix (Fin m) (Fin n) FieldFour)
    (B : Matrix (Fin n) (Fin k) FieldFour) :
    LinearMap.range (Matrix.toLin' B) ≤ LinearMap.ker (Matrix.toLin' F) ↔ F * B = 0 := by
  rw [LinearMap.range_le_ker_iff, ← Matrix.toLin'_mul, LinearEquiv.map_eq_zero_iff]

theorem hatM22U_le_ker (i : Fin 22) : hatM22U i ≤ LinearMap.ker (Matrix.toLin' (hatM22F i)) :=
  (range_le_ker_iff _ _).2 (hatM22F_mul_B i)

theorem hatM22U_injective : Function.Injective hatM22U := by
  intro i j hij
  by_contra hne
  apply hatM22F_mul_B_ne i j hne
  rw [← range_le_ker_iff]
  rw [show LinearMap.range (Matrix.toLin' (hatM22B i)) = hatM22U i from rfl, hij]
  exact hatM22U_le_ker j

@[expose] def Moves (X : Matrix (Fin 6) (Fin 6) FieldFour) (σ : Equiv.Perm (Fin 22)) : Prop :=
  ∀ i, (hatM22U i).map (Matrix.toLin' X) = hatM22U (σ i)

theorem moves_one : Moves 1 1 := fun i => by
  rw [Matrix.toLin'_one, Submodule.map_id]
  rfl

theorem moves_mul {X Y : Matrix (Fin 6) (Fin 6) FieldFour} {σ τ : Equiv.Perm (Fin 22)}
    (hX : Moves X σ) (hY : Moves Y τ) : Moves (X * Y) (σ * τ) := fun i => by
  rw [Matrix.toLin'_mul, Submodule.map_comp, hY i, hX (τ i)]
  rfl

theorem moves_inv {X Y : Matrix (Fin 6) (Fin 6) FieldFour} {σ : Equiv.Perm (Fin 22)}
    (hYX : Y * X = 1) (hX : Moves X σ) : Moves Y σ⁻¹ := fun i => by
  have h := hX (σ⁻¹ i)
  rw [show σ (σ⁻¹ i) = i from σ.apply_symm_apply i] at h
  rw [← h, ← Submodule.map_comp, ← Matrix.toLin'_mul, hYX, Matrix.toLin'_one, Submodule.map_id]

theorem moves_unique {X : Matrix (Fin 6) (Fin 6) FieldFour} {σ τ : Equiv.Perm (Fin 22)}
    (hσ : Moves X σ) (hτ : Moves X τ) : σ = τ :=
  Equiv.ext fun i => hatM22U_injective ((hσ i).symm.trans (hτ i))

theorem moves_hatM22N1 : Moves hatM22N1 m22gA := fun i =>
  map_range_toLin'_eq (hatM22N1_fwd i) (hatM22N1_bwd i)

theorem moves_hatM22N2 : Moves hatM22N2 m22gB := fun i =>
  map_range_toLin'_eq (hatM22N2_fwd i) (hatM22N2_bwd i)

theorem exists_moves {g : Matrix.GeneralLinearGroup (Fin 6) FieldFour} (hg : g ∈ hatM22Γ₀) :
    ∃ σ, Moves (g : Matrix (Fin 6) (Fin 6) FieldFour) σ := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | hx
    · exact ⟨m22gA, moves_hatM22N1⟩
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact ⟨m22gB, moves_hatM22N2⟩
  | one => exact ⟨1, moves_one⟩
  | mul x y _ _ hx hy =>
    obtain ⟨σ, hσ⟩ := hx
    obtain ⟨τ, hτ⟩ := hy
    exact ⟨σ * τ, by rw [Units.val_mul]; exact moves_mul hσ hτ⟩
  | inv x _ hx =>
    obtain ⟨σ, hσ⟩ := hx
    exact ⟨σ⁻¹, moves_inv (Units.inv_mul x) hσ⟩

@[expose] noncomputable def hatM22Perm (g : ↥hatM22Γ₀) : Equiv.Perm (Fin 22) :=
  Classical.choose (exists_moves g.2)

theorem moves_hatM22Perm (g : ↥hatM22Γ₀) :
    Moves ((g : Matrix.GeneralLinearGroup (Fin 6) FieldFour) : Matrix (Fin 6) (Fin 6) FieldFour)
      (hatM22Perm g) :=
  Classical.choose_spec (exists_moves g.2)

@[expose] noncomputable def hatM22Act : ↥hatM22Γ₀ →* Equiv.Perm (Fin 22) where
  toFun := hatM22Perm
  map_one' := moves_unique (moves_hatM22Perm 1) moves_one
  map_mul' g h := moves_unique (moves_hatM22Perm (g * h))
    (by
      have := moves_mul (moves_hatM22Perm g) (moves_hatM22Perm h)
      simpa only [Subgroup.coe_mul, Units.val_mul] using this)

theorem moves_hatM22Act (g : ↥hatM22Γ₀) :
    Moves ((g : Matrix.GeneralLinearGroup (Fin 6) FieldFour) : Matrix (Fin 6) (Fin 6) FieldFour)
      (hatM22Act g) :=
  moves_hatM22Perm g

theorem hatM22Act_eq {g : ↥hatM22Γ₀} {σ : Equiv.Perm (Fin 22)}
    (h : Moves ((g : Matrix.GeneralLinearGroup (Fin 6) FieldFour) :
      Matrix (Fin 6) (Fin 6) FieldFour) σ) : hatM22Act g = σ :=
  moves_unique (moves_hatM22Act g) h

theorem hatM22Act_g1 : hatM22Act ⟨hatM22G1, hatM22G1_mem⟩ = m22gA :=
  hatM22Act_eq moves_hatM22N1

theorem hatM22Act_g2 : hatM22Act ⟨hatM22G2, hatM22G2_mem⟩ = m22gB :=
  hatM22Act_eq moves_hatM22N2

theorem quasithinM22_eq : quasithinM22 = NativeSporadic.M22 := rfl

theorem range_hatM22Act : hatM22Act.range = quasithinM22 := by
  have htop : Subgroup.closure
      ((Subtype.val : ↥hatM22Γ₀ → Matrix.GeneralLinearGroup (Fin 6) FieldFour) ⁻¹'
        {hatM22G1, hatM22G2}) = ⊤ :=
    Subgroup.closure_closure_coe_preimage
  rw [MonoidHom.range_eq_map, ← htop, MonoidHom.map_closure]
  have himg : hatM22Act '' ((Subtype.val : ↥hatM22Γ₀ →
      Matrix.GeneralLinearGroup (Fin 6) FieldFour) ⁻¹' {hatM22G1, hatM22G2}) =
      {m22gA, m22gB} := by
    ext σ
    constructor
    · rintro ⟨g, hg, rfl⟩
      rcases hg with hg | hg
      · have : g = ⟨hatM22G1, hatM22G1_mem⟩ := Subtype.ext hg
        rw [this, hatM22Act_g1]
        exact Set.mem_insert _ _
      · have : g = ⟨hatM22G2, hatM22G2_mem⟩ := Subtype.ext (Set.mem_singleton_iff.1 hg)
        rw [this, hatM22Act_g2]
        exact Set.mem_insert_of_mem _ rfl
    · rintro (rfl | hσ)
      · exact ⟨⟨hatM22G1, hatM22G1_mem⟩, Set.mem_insert _ _, hatM22Act_g1⟩
      · rw [Set.mem_singleton_iff] at hσ
        subst hσ
        exact ⟨⟨hatM22G2, hatM22G2_mem⟩, Set.mem_insert_of_mem _ rfl, hatM22Act_g2⟩
  rw [himg]
  rfl

theorem hatM22Act_mem (g : ↥hatM22Γ₀) : hatM22Act g ∈ quasithinM22 := by
  rw [← range_hatM22Act]
  exact ⟨g, rfl⟩

@[expose] def hatM22Tgt (a b : Fin 6) : Matrix (Fin 6) (Fin 6) FieldFour :=
  if a = b then Matrix.single a a 1 + Matrix.single 0 0 1 else Matrix.single a b 1

@[expose] def hatM22Comb (P : Vector (Vector (Vector FieldFour 3) 3) 5) :
    Matrix (Fin 6) (Fin 6) FieldFour :=
  (hatM22F 0)ᵀ * untab P[0] * (hatM22B 0)ᵀ + (hatM22F 1)ᵀ * untab P[1] * (hatM22B 1)ᵀ +
    (hatM22F 2)ᵀ * untab P[2] * (hatM22B 2)ᵀ + (hatM22F 3)ᵀ * untab P[3] * (hatM22B 3)ᵀ +
    (hatM22F 4)ᵀ * untab P[4] * (hatM22B 4)ᵀ

theorem hatM22ScalarCert_ok :
    ∀ p ∈ hatM22ScalarCert, hatM22Comb p.2.2 = hatM22Tgt p.1 p.2.1 := by
  decide +kernel

theorem hatM22ScalarCert_keys : ∀ a b : Fin 6, a ≠ b ∨ a ≠ 0 →
    (a, b) ∈ hatM22ScalarCert.map fun p => (p.1, p.2.1) := by
  decide +kernel

theorem hatM22ScalarCert_cover (a b : Fin 6) (h : a ≠ b ∨ a ≠ 0) :
    ∃ P, (a, b, P) ∈ hatM22ScalarCert := by
  obtain ⟨⟨a', b', P⟩, hP, he⟩ := List.mem_map.1 (hatM22ScalarCert_keys a b h)
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact ⟨P, hP⟩

theorem trace_comb_mul {n k : ℕ} (F : Matrix (Fin k) (Fin n) FieldFour)
    (P : Matrix (Fin k) (Fin k) FieldFour) (B : Matrix (Fin n) (Fin k) FieldFour)
    (X : Matrix (Fin n) (Fin n) FieldFour) (h : F * X * B = 0) :
    ((Fᵀ * P * Bᵀ)ᵀ * X).trace = 0 := by
  have e : (Fᵀ * P * Bᵀ)ᵀ * X = B * (Pᵀ * F * X) := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  have e2 : Pᵀ * F * X * B = Pᵀ * (F * X * B) := by simp only [Matrix.mul_assoc]
  rw [e, Matrix.trace_mul_comm, e2, h, Matrix.mul_zero, Matrix.trace_zero]

theorem trace_single_transpose_mul (a b : Fin 6) (X : Matrix (Fin 6) (Fin 6) FieldFour) :
    ((Matrix.single a b (1 : FieldFour))ᵀ * X).trace = X a b := by
  rw [Matrix.transpose_single, Matrix.trace, Finset.sum_eq_single b]
  · simp [Matrix.mul_apply, Matrix.single_apply]
  · intro c _ hc
    simp [Matrix.mul_apply, Ne.symm hc]
  · simp

theorem eq_smul_one_of_fix (X : Matrix (Fin 6) (Fin 6) FieldFour)
    (hX : ∀ i : Fin 22, i.val < 5 → hatM22F i * X * hatM22B i = 0) : X = X 0 0 • 1 := by
  have key : ∀ a b : Fin 6, a ≠ b ∨ a ≠ 0 → ((hatM22Tgt a b)ᵀ * X).trace = 0 := by
    intro a b hab
    obtain ⟨P, hP⟩ := hatM22ScalarCert_cover a b hab
    rw [← hatM22ScalarCert_ok _ hP, hatM22Comb]
    simp only [Matrix.transpose_add, Matrix.add_mul, Matrix.trace_add]
    rw [trace_comb_mul _ _ _ X (hX 0 (by decide)), trace_comb_mul _ _ _ X (hX 1 (by decide)),
      trace_comb_mul _ _ _ X (hX 2 (by decide)), trace_comb_mul _ _ _ X (hX 3 (by decide)),
      trace_comb_mul _ _ _ X (hX 4 (by decide))]
    simp
  refine Matrix.ext fun a b => ?_
  rw [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  by_cases hab : a = b
  · subst hab
    rw [ite_eq_left rfl, mul_one]
    by_cases ha : a = 0
    · rw [ha]
    · have h := key a a (Or.inr ha)
      rw [hatM22Tgt, ite_eq_left rfl, Matrix.transpose_add, Matrix.add_mul, Matrix.trace_add,
        trace_single_transpose_mul, trace_single_transpose_mul] at h
      exact (CharTwo.add_eq_zero (R := FieldFour)).1 h
  · have h := key a b (Or.inl hab)
    rw [hatM22Tgt, ite_eq_right hab, trace_single_transpose_mul] at h
    rw [ite_eq_right hab, mul_zero, h]

theorem hatM22_pow_eleven :
    (hatM22N1 * hatM22N2) ^ 11 = ω • (1 : Matrix (Fin 6) (Fin 6) FieldFour) := by
  decide +kernel

theorem moves_smul_one {c : FieldFour} (hc : c ≠ 0) :
    Moves (c • (1 : Matrix (Fin 6) (Fin 6) FieldFour)) 1 := fun i => by
  apply le_antisymm
  · rintro _ ⟨v, hv, rfl⟩
    rw [Matrix.toLin'_apply, Matrix.smul_mulVec, Matrix.one_mulVec]
    exact Submodule.smul_mem _ c hv
  · intro v hv
    refine ⟨c⁻¹ • v, Submodule.smul_mem _ _ hv, ?_⟩
    rw [Matrix.toLin'_apply, Matrix.smul_mulVec, Matrix.one_mulVec, smul_smul,
      mul_inv_cancel₀ hc, one_smul]

@[expose] def hatM22Omega : Matrix.GeneralLinearGroup (Fin 6) FieldFour :=
  (hatM22G1 * hatM22G2) ^ 11

theorem hatM22Omega_val :
    (hatM22Omega : Matrix (Fin 6) (Fin 6) FieldFour) =
      ω • (1 : Matrix (Fin 6) (Fin 6) FieldFour) := by
  rw [hatM22Omega, Units.val_pow_eq_pow_val, Units.val_mul]
  exact hatM22_pow_eleven

theorem hatM22Omega_mem : hatM22Omega ∈ hatM22Γ₀ :=
  Subgroup.pow_mem _ (Subgroup.mul_mem _ hatM22G1_mem hatM22G2_mem) _

@[expose] def hatM22Z : ↥hatM22Γ₀ := ⟨hatM22Omega, hatM22Omega_mem⟩

theorem hatM22Z_val :
    (((hatM22Z : ↥hatM22Γ₀) : Matrix.GeneralLinearGroup (Fin 6) FieldFour) :
      Matrix (Fin 6) (Fin 6) FieldFour) = ω • 1 :=
  hatM22Omega_val

theorem hatM22Z_sq_val :
    (((hatM22Z ^ 2 : ↥hatM22Γ₀) : Matrix.GeneralLinearGroup (Fin 6) FieldFour) :
      Matrix (Fin 6) (Fin 6) FieldFour) = ω₂ • 1 := by
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hatM22Z_val, smul_pow, one_pow, ω_sq]

theorem hatM22Z_pow_three : hatM22Z ^ 3 = 1 := by
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hatM22Z_val, smul_pow, one_pow]
  have : ω ^ 3 = 1 := by decide
  rw [this, one_smul]
  rfl

theorem mem_ker_hatM22Act_iff (g : ↥hatM22Γ₀) :
    g ∈ hatM22Act.ker ↔ g = 1 ∨ g = hatM22Z ∨ g = hatM22Z ^ 2 := by
  constructor
  · intro hg
    have hmov : Moves ((g : Matrix.GeneralLinearGroup (Fin 6) FieldFour) :
        Matrix (Fin 6) (Fin 6) FieldFour) 1 := by
      have := moves_hatM22Act g
      rwa [MonoidHom.mem_ker.1 hg] at this
    set X : Matrix (Fin 6) (Fin 6) FieldFour :=
      ((g : Matrix.GeneralLinearGroup (Fin 6) FieldFour) : Matrix (Fin 6) (Fin 6) FieldFour)
      with hXdef
    have hfix : ∀ i : Fin 22, i.val < 5 → hatM22F i * X * hatM22B i = 0 := by
      intro i _
      rw [Matrix.mul_assoc, ← range_le_ker_iff, Matrix.toLin'_mul, LinearMap.range_comp]
      have := hmov i
      rw [show hatM22U i = LinearMap.range (Matrix.toLin' (hatM22B i)) from rfl] at this
      rw [this]
      exact hatM22U_le_ker i
    have hX := eq_smul_one_of_fix X hfix
    have hc0 : X 0 0 ≠ 0 := by
      intro h0
      have h1 : X * (((g : Matrix.GeneralLinearGroup (Fin 6) FieldFour)⁻¹ :
          Matrix.GeneralLinearGroup (Fin 6) FieldFour) : Matrix (Fin 6) (Fin 6) FieldFour) = 1 :=
        Units.mul_inv _
      rw [hX, h0, zero_smul, Matrix.zero_mul] at h1
      have h2 := congrFun (congrFun h1 0) 0
      simp at h2
    have hcases : ∀ c : FieldFour, c ≠ 0 → c = 1 ∨ c = ω ∨ c = ω₂ := by decide
    rcases hcases _ hc0 with h | h | h
    · left
      apply Subtype.ext
      apply Units.ext
      show X = 1
      rw [hX, h, one_smul]
    · right; left
      apply Subtype.ext
      apply Units.ext
      show X = _
      rw [hX, h, hatM22Z_val]
    · right; right
      apply Subtype.ext
      apply Units.ext
      show X = _
      rw [hX, h, hatM22Z_sq_val]
  · rintro (rfl | rfl | rfl)
    · exact one_mem _
    · rw [MonoidHom.mem_ker]
      apply hatM22Act_eq
      rw [hatM22Z_val]
      exact moves_smul_one (by decide)
    · rw [MonoidHom.mem_ker]
      apply hatM22Act_eq
      rw [hatM22Z_sq_val]
      exact moves_smul_one (by decide)

end CFSG.Quasithin.HatM22
