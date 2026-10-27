module

public import CFSG.RankThree.PartTwo.Sec21.Item223RankResProofChar

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item223RankResProof

open Matrix

section Eigen

variable {L : Type*} [Field L] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Subgroup (GL ι L)} {b : Module.Basis ι L (ι → L)} {d : GL ι L → ι → L}

theorem repr_mulVec_eigen (hb : ∀ x ∈ E, ∀ a, (x : Matrix ι ι L) *ᵥ b a = d x a • b a)
    {x : GL ι L} (hx : x ∈ E) (v : ι → L) (a : ι) :
    b.repr ((x : Matrix ι ι L) *ᵥ v) a = d x a * b.repr v a := by
  have h : (b.coord a).comp (Matrix.toLin' (x : Matrix ι ι L)) = d x a • b.coord a := by
    refine b.ext fun a' => ?_
    rw [LinearMap.comp_apply, Matrix.toLin'_apply, hb x hx a', LinearMap.smul_apply, map_smul]
    simp only [Module.Basis.coord_apply, Module.Basis.repr_self, smul_eq_mul,
      Finsupp.single_apply]
    split_ifs with haa
    · rw [haa]
    · simp
  have := LinearMap.congr_fun h v
  rwa [LinearMap.comp_apply, Matrix.toLin'_apply, LinearMap.smul_apply, Module.Basis.coord_apply,
    Module.Basis.coord_apply, smul_eq_mul] at this

theorem exists_index_of_eigen (hb : ∀ x ∈ E, ∀ a, (x : Matrix ι ι L) *ᵥ b a = d x a • b a)
    {u : ι → L} (hu : u ≠ 0) {c : GL ι L → L}
    (hc : ∀ x ∈ E, (x : Matrix ι ι L) *ᵥ u = c x • u) : ∃ e, ∀ x ∈ E, d x e = c x := by
  obtain ⟨e, he⟩ : ∃ e, b.repr u e ≠ 0 := by
    by_contra h
    push Not at h
    apply hu
    rw [← b.sum_repr u]
    simp [h]
  refine ⟨e, fun x hx => ?_⟩
  have h1 := repr_mulVec_eigen hb hx u e
  rw [hc x hx, map_smul, Finsupp.smul_apply, smul_eq_mul] at h1
  exact (mul_right_cancel₀ he h1).symm

omit [DecidableEq ι] in
theorem form_mulVec_mulVec' {M x : Matrix ι ι L} (h : xᵀ * M * x = M) (v w : ι → L) :
    (x *ᵥ v) ⬝ᵥ (M *ᵥ (x *ᵥ w)) = v ⬝ᵥ (M *ᵥ w) := by
  rw [← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, h]

theorem form_eq_zero_of_ne (hb : ∀ x ∈ E, ∀ a, (x : Matrix ι ι L) *ᵥ b a = d x a • b a)
    {M : Matrix ι ι L} (hform : ∀ x ∈ E, (x : Matrix ι ι L)ᵀ * M * x = M) {a e : ι}
    (h : ∃ x ∈ E, d x a * d x e ≠ 1) : b a ⬝ᵥ (M *ᵥ b e) = 0 := by
  obtain ⟨x, hx, hne⟩ := h
  have h1 := form_mulVec_mulVec' (hform x hx) (b a) (b e)
  rw [hb x hx a, hb x hx e, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    smul_eq_mul, ← mul_assoc] at h1
  have : (d x a * d x e - 1) * (b a ⬝ᵥ (M *ᵥ b e)) = 0 := by linear_combination h1
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hne)

theorem exists_pair_of_form (hb : ∀ x ∈ E, ∀ a, (x : Matrix ι ι L) *ᵥ b a = d x a • b a)
    {M : Matrix ι ι L} (hM : M.det ≠ 0)
    (hform : ∀ x ∈ E, (x : Matrix ι ι L)ᵀ * M * x = M) (a : ι) :
    ∃ a', b a ⬝ᵥ (M *ᵥ b a') ≠ 0 ∧ ∀ x ∈ E, d x a' = (d x a)⁻¹ := by
  obtain ⟨a', ha'⟩ := Sec4.exists_form_ne_zero hM b (b.ne_zero a)
  refine ⟨a', ha', fun x hx => ?_⟩
  have h1 : d x a * d x a' = 1 := by
    by_contra hne
    exact ha' (form_eq_zero_of_ne hb hform ⟨x, hx, hne⟩)
  exact eq_inv_of_mul_eq_one_right h1

theorem mulVec_mu_eigen (hb : ∀ x ∈ E, ∀ a, (x : Matrix ι ι L) *ᵥ b a = d x a • b a)
    {μ : (ι → L) → (ι → L) → (ι → L)}
    (hμl : ∀ (c : L) v w, μ (c • v) w = c • μ v w) (hμr : ∀ (c : L) v w, μ v (c • w) = c • μ v w)
    (hμE : ∀ x ∈ E, ∀ v w, (x : Matrix ι ι L) *ᵥ μ v w = μ ((x : Matrix ι ι L) *ᵥ v)
      ((x : Matrix ι ι L) *ᵥ w)) {x : GL ι L} (hx : x ∈ E) (a e : ι) :
    (x : Matrix ι ι L) *ᵥ μ (b a) (b e) = (d x a * d x e) • μ (b a) (b e) := by
  rw [hμE x hx, hb x hx a, hb x hx e, hμl, hμr, smul_smul]

theorem card_le_nine_of_eigen [Finite E] (hexp : ∀ x ∈ E, x ^ 3 = 1)
    (hb : ∀ x ∈ E, ∀ a, (x : Matrix ι ι L) *ᵥ b a = d x a • b a)
    (M : Matrix ι ι L) (hM : M.det ≠ 0) (hform : ∀ x ∈ E, (x : Matrix ι ι L)ᵀ * M * x = M)
    (μ : (ι → L) → (ι → L) → (ι → L))
    (hμl : ∀ (c : L) v w, μ (c • v) w = c • μ v w) (hμr : ∀ (c : L) v w, μ v (c • w) = c • μ v w)
    (hμE : ∀ x ∈ E, ∀ v w, (x : Matrix ι ι L) *ᵥ μ v w = μ ((x : Matrix ι ι L) *ᵥ v)
      ((x : Matrix ι ι L) *ᵥ w))
    (κ : L) (hκ : κ ≠ 0)
    (hid : ∀ a c e : ι, (∃ x ∈ E, d x a ≠ 1) → (∀ x ∈ E, d x c = (d x a)⁻¹) →
      b a ⬝ᵥ (M *ᵥ b e) = 0 → b c ⬝ᵥ (M *ᵥ b e) = 0 →
      μ (b a) (μ (b c) (b e)) + μ (b c) (μ (b a) (b e)) = (κ * (b a ⬝ᵥ (M *ᵥ b c))) • b e)
    (hcount : Nat.card {a // ∃ x ∈ E, d x a ≠ 1} ≤ 7) :
    Nat.card E ≤ 9 := by
  classical
  have hd3 : ∀ (x : E) a, d x a ^ 3 = 1 := fun x a => Sec4.eigen_pow_three hb x.2 (hexp x x.2) a
  set χ : ι → E → Lˣ := fun a x => ⟨d x a, d x a ^ 2,
    by rw [← pow_succ', hd3 x a], by rw [← pow_succ, hd3 x a]⟩ with hχdef
  have hχval : ∀ a (x : E), ((χ a x : Lˣ) : L) = d x a := fun _ _ => rfl
  have hχeq : ∀ a e, χ a = χ e ↔ ∀ x ∈ E, d x a = d x e := by
    intro a e
    constructor
    · intro h x hx
      have := congrArg (fun f => ((f ⟨x, hx⟩ : Lˣ) : L)) h
      simpa [hχval] using this
    · intro h
      funext x
      exact Units.ext (h x x.2)
  have hχ1 : ∀ a, χ a = 1 ↔ ∀ x ∈ E, d x a = 1 := by
    intro a
    constructor
    · intro h x hx
      have := congrArg (fun f => ((f ⟨x, hx⟩ : Lˣ) : L)) h
      simpa [hχval] using this
    · intro h
      funext x
      exact Units.ext (h x x.2)
  have hχmul : ∀ a e f, χ f = χ a * χ e ↔ ∀ x ∈ E, d x f = d x a * d x e := by
    intro a e f
    constructor
    · intro h x hx
      have := congrArg (fun g => ((g ⟨x, hx⟩ : Lˣ) : L)) h
      simpa [hχval] using this
    · intro h
      funext x
      exact Units.ext (h x x.2)
  have hχinv : ∀ a f, χ f = (χ a)⁻¹ ↔ ∀ x ∈ E, d x f = (d x a)⁻¹ := by
    intro a f
    constructor
    · intro h x hx
      have := congrArg (fun g => ((g ⟨x, hx⟩ : Lˣ) : L)) h
      simpa [hχval] using this
    · intro h
      funext x
      apply Units.ext
      rw [Pi.inv_apply, Units.val_inv_eq_inv_val]
      exact h x x.2
  have hχinvmul : ∀ a e f, χ f = (χ a)⁻¹ * χ e ↔ ∀ x ∈ E, d x f = (d x a)⁻¹ * d x e := by
    intro a e f
    constructor
    · intro h x hx
      have := congrArg (fun g => ((g ⟨x, hx⟩ : Lˣ) : L)) h
      simpa [hχval] using this
    · intro h
      funext x
      apply Units.ext
      rw [Pi.mul_apply, Pi.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val]
      exact h x x.2
  refine card_le_nine_of_characters χ (fun a x y => Units.ext (Sec4.eigen_mul hb x.2 y.2 a))
    (fun x => Subtype.ext (hexp x x.2)) (fun x hx => ?_) ?_ (fun a => ?_)
    (fun a e ha hea hea' => ?_)
  ·
    apply Subtype.ext
    rw [Subgroup.coe_one]
    refine Sec4.eigen_ext hb x.2 E.one_mem fun a => ?_
    rw [Sec4.eigen_one hb a]
    exact congrArg Units.val (hx a)
  ·
    have e : {a // χ a ≠ 1} ≃ {a // ∃ x ∈ E, d x a ≠ 1} := Equiv.subtypeEquivRight fun a => by
      rw [ne_eq, hχ1]
      push Not
      rfl
    rw [Nat.card_congr e]
    exact hcount
  ·
    obtain ⟨a', -, ha'⟩ := exists_pair_of_form hb hM hform a
    exact ⟨a', (hχinv a a').mpr ha'⟩
  ·
    have ha1 : ∃ x ∈ E, d x a ≠ 1 := by
      by_contra h
      push Not at h
      exact ha ((hχ1 a).mpr h)
    obtain ⟨c, hac, hc⟩ := exists_pair_of_form hb hM hform a
    have hae : b a ⬝ᵥ (M *ᵥ b e) = 0 := by
      refine form_eq_zero_of_ne hb hform ?_
      by_contra h
      push Not at h
      exact hea' ((hχinv a e).mpr fun x hx => eq_inv_of_mul_eq_one_right (h x hx))
    have hce : b c ⬝ᵥ (M *ᵥ b e) = 0 := by
      refine form_eq_zero_of_ne hb hform ?_
      by_contra h
      push Not at h
      apply hea
      refine (hχeq e a).mpr fun x hx => ?_
      have h1 := h x hx
      rw [hc x hx] at h1
      have h0 : d x a ≠ 0 := by
        intro h0
        have := hd3 ⟨x, hx⟩ a
        rw [h0] at this
        norm_num at this
      field_simp at h1
      exact h1
    have hsum := hid a c e ha1 hc hae hce
    have hne : (κ * (b a ⬝ᵥ (M *ᵥ b c))) • b e ≠ 0 :=
      smul_ne_zero (mul_ne_zero hκ hac) (b.ne_zero e)
    have hμ0 : ∀ v, μ v 0 = 0 := fun v => by
      have := hμr 0 v 0
      rwa [zero_smul, zero_smul] at this
    by_cases h1 : μ (b a) (b e) = 0
    · by_cases h2 : μ (b c) (b e) = 0
      · exfalso
        rw [h1, h2, hμ0, hμ0, add_zero] at hsum
        exact hne hsum.symm
      · obtain ⟨e', he'⟩ := exists_index_of_eigen hb h2
          (fun x hx => mulVec_mu_eigen hb hμl hμr hμE hx c e)
        refine ⟨e', Or.inr ((hχinvmul a e e').mpr fun x hx => ?_)⟩
        rw [he' x hx, hc x hx]
    · obtain ⟨e', he'⟩ := exists_index_of_eigen hb h1
        (fun x hx => mulVec_mu_eigen hb hμl hμr hμE hx a e)
      exact ⟨e', Or.inl ((hχmul a e e').mpr he')⟩

end Eigen

end CFSG.RankThree.PartTwo.Sec21.Item223RankResProof
