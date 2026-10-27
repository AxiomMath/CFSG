module

public import CFSG.Timmesfeld.Transvection.ModelRankSp

public section

namespace CFSG.Timmesfeld.Transvection

namespace ModelRank

open Matrix CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Universal.Symplectic
  CFSG.Timmesfeld.ARS CFSG.Timmesfeld.ARS.CaseM

variable {n : ℕ} {F : Type} [Field F]

theorem spForm_mat_mulVec (g : StatedSp n F) (x y : Fin n ⊕ Fin n → F) :
    spForm (SpExtras.mat n F g *ᵥ x) (SpExtras.mat n F g *ᵥ y) = spForm x y := by
  have h := mat_transpose_mul g
  calc spForm (SpExtras.mat n F g *ᵥ x) (SpExtras.mat n F g *ᵥ y)
      = (SpExtras.mat n F g *ᵥ x) ⬝ᵥ (spGram n F *ᵥ (SpExtras.mat n F g *ᵥ y)) := rfl
    _ = x ⬝ᵥ ((SpExtras.mat n F g)ᵀ *ᵥ (spGram n F *ᵥ (SpExtras.mat n F g *ᵥ y))) := by
        rw [Matrix.dotProduct_mulVec x (SpExtras.mat n F g)ᵀ, Matrix.vecMul_transpose]
    _ = x ⬝ᵥ (((SpExtras.mat n F g)ᵀ * spGram n F * SpExtras.mat n F g) *ᵥ y) := by
        rw [Matrix.mul_assoc, ← mulVec_mulVec, ← mulVec_mulVec]
    _ = spForm x y := by rw [h]

theorem mat_inv_mulVec_mat_mulVec (g : StatedSp n F) (v : Fin n ⊕ Fin n → F) :
    SpExtras.mat n F g⁻¹ *ᵥ (SpExtras.mat n F g *ᵥ v) = v := by
  rw [mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one, one_mulVec]

theorem mat_mulVec_mat_inv_mulVec (g : StatedSp n F) (v : Fin n ⊕ Fin n → F) :
    SpExtras.mat n F g *ᵥ (SpExtras.mat n F g⁻¹ *ᵥ v) = v := by
  rw [mulVec_mulVec, ← map_mul, mul_inv_cancel, map_one, one_mulVec]

@[expose] def spLine (a : Fin n ⊕ Fin n → F) : Subgroup (StatedSp n F) where
  carrier := {g | ∃ μ : F, μ ≠ 0 ∧ SpExtras.mat n F g *ᵥ a = μ • a}
  mul_mem' := by
    rintro g h ⟨μ, hμ, hg⟩ ⟨ν, hν, hh⟩
    refine ⟨μ * ν, mul_ne_zero hμ hν, ?_⟩
    rw [map_mul, ← mulVec_mulVec, hh, mulVec_smul, hg, smul_smul, mul_comm]
  one_mem' := ⟨1, one_ne_zero, by rw [map_one, one_mulVec, one_smul]⟩
  inv_mem' := by
    rintro g ⟨μ, hμ, hg⟩
    refine ⟨μ⁻¹, inv_ne_zero hμ, ?_⟩
    have h1 : μ • (SpExtras.mat n F g⁻¹ *ᵥ a) = a := by
      rw [← mulVec_smul, ← hg, mat_inv_mulVec_mat_mulVec]
    exact (eq_inv_smul_iff₀ hμ).2 h1

@[expose] def spRad (a : Fin n ⊕ Fin n → F) : Subgroup (StatedSp n F) where
  carrier := {g | SpExtras.mat n F g *ᵥ a = a ∧
    ∀ u, spForm a u = 0 → ∃ c : F, SpExtras.mat n F g *ᵥ u = u + c • a}
  mul_mem' := by
    rintro g h ⟨hga, hg⟩ ⟨hha, hh⟩
    refine ⟨by rw [map_mul, ← mulVec_mulVec, hha, hga], fun u hu => ?_⟩
    obtain ⟨c, hc⟩ := hh u hu
    obtain ⟨d, hd⟩ := hg u hu
    refine ⟨c + d, ?_⟩
    rw [map_mul, ← mulVec_mulVec, hc, mulVec_add, hd, mulVec_smul, hga, add_smul]
    abel
  one_mem' := ⟨by rw [map_one, one_mulVec],
    fun u _ => ⟨0, by rw [map_one, one_mulVec, zero_smul, add_zero]⟩⟩
  inv_mem' := by
    rintro g ⟨hga, hg⟩
    refine ⟨?_, fun u hu => ?_⟩
    · have := mat_inv_mulVec_mat_mulVec g a
      rwa [hga] at this
    · have hu' : spForm a (SpExtras.mat n F g⁻¹ *ᵥ u) = 0 := by
        have h := spForm_mat_mulVec g a (SpExtras.mat n F g⁻¹ *ᵥ u)
        rw [hga, mat_mulVec_mat_inv_mulVec] at h
        rw [← h]
        exact hu
      obtain ⟨c, hc⟩ := hg _ hu'
      refine ⟨-c, ?_⟩
      rw [mat_mulVec_mat_inv_mulVec] at hc
      rw [neg_smul, ← sub_eq_add_neg]
      exact eq_sub_of_add_eq hc.symm

theorem eq_of_mat_mulVec_eq {g h : StatedSp n F}
    (H : ∀ v, SpExtras.mat n F g *ᵥ v = SpExtras.mat n F h *ᵥ v) : g = h :=
  SpExtras.mat_injective (Matrix.ext_iff_mulVec.2 H)

theorem vec_add_self [CharP F 2] (v : Fin n ⊕ Fin n → F) : v + v = 0 := by
  ext i
  simp [CharTwo.add_self_eq_zero]

theorem IsTransGroup.exists_eq_smul {u v : Fin n ⊕ Fin n → F} {X : Subgroup (StatedSp n F)}
    (hu : IsTransGroup u X) (hv : IsTransGroup v X) (hu0 : u ≠ 0) :
    ∃ μ : F, μ ≠ 0 ∧ u = μ • v := by
  obtain ⟨x, hx⟩ := hu.2 1
  have hxX : x ∈ X := (hu.1 x).2 ⟨1, hx⟩
  obtain ⟨c, hc⟩ := (hv.1 x).1 hxX
  obtain ⟨y, hy⟩ := exists_spForm_ne_zero hu0
  have h1 : SpExtras.mat n F x *ᵥ y = y + (1 * spForm u y) • u := by rw [hx, spTrans_mulVec]
  have h2 : SpExtras.mat n F x *ᵥ y = y + (c * spForm v y) • v := by rw [hc, spTrans_mulVec]
  have h3 : (spForm u y) • u = (c * spForm v y) • v := by
    have := h1.symm.trans h2
    rw [one_mul] at this
    exact add_left_cancel this
  have h4 : u = ((spForm u y)⁻¹ * (c * spForm v y)) • v := by
    rw [← smul_smul, ← h3, smul_smul, inv_mul_cancel₀ hy, one_smul]
  refine ⟨(spForm u y)⁻¹ * (c * spForm v y), ?_, h4⟩
  intro h0
  apply hu0
  rw [h4, h0, zero_smul]

theorem normalizer_eq_spLine {a : Fin n ⊕ Fin n → F} (ha : a ≠ 0) {T : Subgroup (StatedSp n F)}
    (hT : IsTransGroup a T) : Subgroup.normalizer (T : Set (StatedSp n F)) = spLine a := by
  ext g
  rw [Subgroup.mem_normalizer_iff]
  constructor
  · intro hg
    have hconj : conjSub T g = T := by
      ext x
      rw [mem_conjSub]
      have := hg (g⁻¹ * x * g)
      rw [show g * (g⁻¹ * x * g) * g⁻¹ = x by group] at this
      exact this
    have h1 := hT.conjSub g
    rw [hconj] at h1
    exact IsTransGroup.exists_eq_smul h1 hT (mat_mulVec_ne_zero' g ha)
  · rintro ⟨μ, hμ, hga⟩
    have h1 : IsTransGroup a (conjSub T g) :=
      IsTransGroup.of_smul hμ (by rw [← hga]; exact hT.conjSub g)
    have hconj : conjSub T g = T := h1.eq hT
    intro h
    have : g * h * g⁻¹ ∈ conjSub T g ↔ h ∈ T := by
      rw [mem_conjSub, show g⁻¹ * (g * h * g⁻¹) * g = h by group]
    rw [hconj] at this
    exact this.symm

theorem spRad_le_spLine (a : Fin n ⊕ Fin n → F) : spRad a ≤ spLine a := by
  rintro g ⟨hga, -⟩
  exact ⟨1, one_ne_zero, by rw [hga, one_smul]⟩

theorem conj_mem_spRad {a : Fin n ⊕ Fin n → F} {h : StatedSp n F} (hh : h ∈ spLine a)
    {x : StatedSp n F} (hx : x ∈ spRad a) : h * x * h⁻¹ ∈ spRad a := by
  obtain ⟨μ, hμ, hha⟩ := hh
  obtain ⟨hxa, hx⟩ := hx
  have hinv : SpExtras.mat n F h⁻¹ *ᵥ a = μ⁻¹ • a := by
    have h1 : μ • (SpExtras.mat n F h⁻¹ *ᵥ a) = a := by
      rw [← mulVec_smul, ← hha, mat_inv_mulVec_mat_mulVec]
    exact (eq_inv_smul_iff₀ hμ).2 h1
  refine ⟨?_, fun u hu => ?_⟩
  · rw [map_mul, map_mul, ← mulVec_mulVec, ← mulVec_mulVec, hinv, mulVec_smul, hxa, mulVec_smul,
      hha, smul_smul, inv_mul_cancel₀ hμ, one_smul]
  · have hu' : spForm a (SpExtras.mat n F h⁻¹ *ᵥ u) = 0 := by
      have h1 := spForm_mat_mulVec h a (SpExtras.mat n F h⁻¹ *ᵥ u)
      rw [hha, mat_mulVec_mat_inv_mulVec, spForm_smul_left'] at h1
      rw [← h1, hu, mul_zero]
    obtain ⟨c, hc⟩ := hx _ hu'
    refine ⟨c * μ, ?_⟩
    rw [map_mul, map_mul, ← mulVec_mulVec, ← mulVec_mulVec, hc, mulVec_add, mulVec_smul, hha,
      mat_mulVec_mat_inv_mulVec, smul_smul]

theorem le_spRad_of_isTransGroup {a : Fin n ⊕ Fin n → F} {T : Subgroup (StatedSp n F)}
    (hT : IsTransGroup a T) : T ≤ spRad a := by
  intro x hx
  obtain ⟨c, hc⟩ := (hT.1 x).1 hx
  refine ⟨?_, fun u hu => ⟨0, ?_⟩⟩
  · rw [hc, spTrans_mulVec, spForm_self, mul_zero, zero_smul, add_zero]
  · rw [hc, spTrans_mulVec, hu, mul_zero, zero_smul, add_zero]

theorem isPGroup_spRad [CharP F 2] (a : Fin n ⊕ Fin n → F) : IsPGroup 2 (spRad a) := by
  rintro ⟨x, hxa, hx⟩
  refine ⟨2, ?_⟩
  have key : ∀ v, ∃ c : F, SpExtras.mat n F x *ᵥ (SpExtras.mat n F x *ᵥ v) = v + c • a := by
    intro v
    have h0 : spForm a (SpExtras.mat n F x *ᵥ v + v) = 0 := by
      rw [spForm_add_right]
      have := spForm_mat_mulVec x a v
      rw [hxa] at this
      rw [this, CharTwo.add_self_eq_zero]
    obtain ⟨c, hc⟩ := hx _ h0
    refine ⟨c, ?_⟩
    rw [mulVec_add] at hc
    have h2 : SpExtras.mat n F x *ᵥ (SpExtras.mat n F x *ᵥ v) +
        SpExtras.mat n F x *ᵥ v = (v + c • a) + SpExtras.mat n F x *ᵥ v := by
      rw [hc]; abel
    exact add_right_cancel h2
  have h4 : x ^ 4 = 1 := by
    apply eq_of_mat_mulVec_eq
    intro v
    obtain ⟨c, hc⟩ := key v
    have h5 : SpExtras.mat n F (x ^ 4) *ᵥ v = SpExtras.mat n F x *ᵥ (SpExtras.mat n F x *ᵥ
        (SpExtras.mat n F x *ᵥ (SpExtras.mat n F x *ᵥ v))) := by
      rw [map_pow, show (4 : ℕ) = 1 + 1 + 1 + 1 by norm_num, pow_succ, pow_succ, pow_succ, pow_one,
        ← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec]
    rw [h5, map_one, one_mulVec, hc, mulVec_add, mulVec_smul, mulVec_add, mulVec_smul, hc]
    simp only [hxa]
    rw [add_assoc, ← add_smul, CharTwo.add_self_eq_zero, zero_smul, add_zero]
  exact Subtype.ext h4

theorem spRad_le_pCoreOf [CharP F 2] {a : Fin n ⊕ Fin n → F} (ha : a ≠ 0)
    {T : Subgroup (StatedSp n F)} (hT : IsTransGroup a T) :
    spRad a ≤ CFSG.Open.pCoreOf 2 (Subgroup.normalizer (T : Set (StatedSp n F))) := by
  rw [normalizer_eq_spLine ha hT]
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (spRad_le_spLine a) ?_
    (isPGroup_spRad a)
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact conj_mem_spRad hg hx
  · intro hx
    have := conj_mem_spRad (inv_mem hg) hx
    rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at this

theorem two_smul_vec_eq_zero [CharP F 2] (z : Fin n ⊕ Fin n → F) : (2 : F) • z = 0 := by
  rw [CharTwo.two_eq_zero, zero_smul]

theorem mulVec_spTrans_prod [CharP F 2] {a w : Fin n ⊕ Fin n → F} (haw : spForm a w = 0) (l : F)
    (x : Fin n ⊕ Fin n → F) :
    spTrans (a + w) 1 *ᵥ (spTrans w 1 *ᵥ (spTrans a (l + 1) *ᵥ x)) =
      x + spForm a x • w + spForm w x • a + (l * spForm a x) • a := by
  have hwa : spForm w a = 0 := spForm_eq_zero_comm haw
  rw [spTrans_mulVec, spTrans_mulVec, spTrans_mulVec]
  simp only [spForm_add_left, spForm_add_right, spForm_smul_right', spForm_self, haw, hwa,
    mul_zero, add_zero, zero_add, one_mul]
  have h2 := two_smul_vec_eq_zero (spForm a x • a + spForm w x • w)
  linear_combination (norm := module) h2

theorem exists_mem_spRad_mulVec_eq [CharP F 2] {a v v' : Fin n ⊕ Fin n → F}
    (hv : spForm a v = 1) (hv' : spForm a v' = 1) :
    ∃ x ∈ spRad a, SpExtras.mat n F x *ᵥ v = v' := by
  set w := v + v' with hw
  have haw : spForm a w = 0 := by
    rw [hw, spForm_add_right, hv, hv', CharTwo.add_self_eq_zero]
  have hwa : spForm w a = 0 := spForm_eq_zero_comm haw
  obtain ⟨t1, ht1⟩ := exists_mat_eq_spTrans (a + w) (1 : F)
  obtain ⟨t2, ht2⟩ := exists_mat_eq_spTrans w (1 : F)
  obtain ⟨t3, ht3⟩ := exists_mat_eq_spTrans a (spForm w v + 1)
  have hact : ∀ x, SpExtras.mat n F (t1 * t2 * t3) *ᵥ x =
      x + spForm a x • w + spForm w x • a + (spForm w v * spForm a x) • a := by
    intro x
    rw [map_mul, map_mul, ← mulVec_mulVec, ← mulVec_mulVec, ht1, ht2, ht3]
    exact mulVec_spTrans_prod haw _ x
  refine ⟨t1 * t2 * t3, ⟨?_, fun u hu => ⟨spForm w u, ?_⟩⟩, ?_⟩
  · rw [hact, spForm_self, hwa]
    simp
  · rw [hact, hu]
    simp
  · rw [hact, hv, hw, one_smul, mul_one, add_assoc, ← add_assoc v v, vec_add_self, zero_add,
      ← add_smul, CharTwo.add_self_eq_zero, zero_smul, add_zero]

@[expose] def NoTwoPowerStmt (n : ℕ) (F : Type) [Field F] [CharP F 2] : Prop :=
  ∀ {p q : Fin n ⊕ Fin n → F}, spForm p q ≠ 0 → ∀ {c c' : F}, c ≠ 0 → c' ≠ 0 →
    ∀ {g : StatedSp n F}, SpExtras.mat n F g = spTrans p c * spTrans q c' →
      ∀ k : ℕ, g ^ (2 ^ k) ≠ 1

@[expose] def SpCoreStmt (n : ℕ) (F : Type) [Field F] [CharP F 2] : Prop :=
  ∀ {a : Fin n ⊕ Fin n → F}, a ≠ 0 → ∀ {T : Subgroup (StatedSp n F)}, IsTransGroup a T →
    CFSG.Open.pCoreOf 2 (Subgroup.normalizer (T : Set (StatedSp n F))) = spRad a

@[expose] def SpRadCommStmt (n : ℕ) (F : Type) [Field F] [CharP F 2] : Prop :=
  ∀ {a : Fin n ⊕ Fin n → F}, a ≠ 0 → ∀ x ∈ spRad a, ∀ y ∈ spRad a, x * y = y * x

@[expose] def SpMapTransStmt (n : ℕ) (F : Type) [Field F] : Prop :=
  ∀ {a : Fin n ⊕ Fin n → F}, a ≠ 0 → ∀ {T : Subgroup (StatedSp n F)}, IsTransGroup a T →
    ∀ (α : MulAut (StatedSp n F)), (∀ x ∈ T, α x = x) →
      ∀ {v : Fin n ⊕ Fin n → F}, v ≠ 0 → ∀ {X : Subgroup (StatedSp n F)}, IsTransGroup v X →
        ∃ v' : Fin n ⊕ Fin n → F, v' ≠ 0 ∧ IsTransGroup v' (X.map α.toMonoidHom)

@[expose] def SpRigidStmt (n : ℕ) (F : Type) [Field F] [CharP F 2] : Prop :=
  ∀ {a d : Fin n ⊕ Fin n → F}, a ≠ 0 → spForm a d = 1 →
    ∀ {T Td : Subgroup (StatedSp n F)}, IsTransGroup a T → IsTransGroup d Td →
      ∀ (β : MulAut (StatedSp n F)), (∀ x ∈ spRad a, β x = x) →
        Td.map β.toMonoidHom = Td → β = 1

end ModelRank

end CFSG.Timmesfeld.Transvection
