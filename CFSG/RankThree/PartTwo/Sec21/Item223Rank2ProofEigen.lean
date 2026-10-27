module

public import CFSG.RankThree.PartTwo.Sec21.Item223Rank2ProofComb

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item223Rank2Proof

open Matrix

section Block

variable {L : Type*} [Field L] {E : Type*} [Group E]

def IsBlockEigen (β : E →* GL (Fin 8) L) (b : Module.Basis (Fin 8) L (Fin 8 → L))
    (χ : Fin 8 → E → L) : Prop :=
  ∀ x a, ((β x : GL (Fin 8) L) : Matrix (Fin 8) (Fin 8) L) *ᵥ b a = χ a x • b a

theorem exists_block_eigenbasis [IsAlgClosed L] (h3 : (3 : L) ≠ 0)
    (hcomm : ∀ x y : E, x * y = y * x) (hexp : ∀ x : E, x ^ 3 = 1) (β : E →* GL (Fin 8) L) :
    ∃ (b : Module.Basis (Fin 8) L (Fin 8 → L)) (χ : Fin 8 → E → L), IsBlockEigen β b χ := by
  obtain ⟨b, d, hb⟩ := Sec4.exists_common_eigenbasis_pow_three h3 β.range
    (by
      rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
      rw [← map_mul, ← map_mul, hcomm])
    (by
      rintro _ ⟨x, rfl⟩
      rw [← map_pow, hexp, map_one])
  exact ⟨b, fun a x => d (β x) a, fun x a => hb (β x) ⟨x, rfl⟩ a⟩

variable {β : E →* GL (Fin 8) L} {b : Module.Basis (Fin 8) L (Fin 8 → L)} {χ : Fin 8 → E → L}

theorem IsBlockEigen.mul (hb : IsBlockEigen β b χ) (x y : E) (a : Fin 8) :
    χ a (x * y) = χ a x * χ a y := by
  have h1 := hb (x * y) a
  rw [map_mul, Units.val_mul, ← Matrix.mulVec_mulVec, hb y a, Matrix.mulVec_smul, hb x a,
    smul_smul] at h1
  rw [mul_comm]
  exact (smul_left_injective L (b.ne_zero a) h1).symm

theorem IsBlockEigen.one (hb : IsBlockEigen β b χ) (a : Fin 8) : χ a 1 = 1 := by
  have h0 := hb 1 a
  rw [map_one, Units.val_one, Matrix.one_mulVec] at h0
  exact smul_left_injective L (b.ne_zero a) (show χ a 1 • b a = (1 : L) • b a by
    rw [← h0, one_smul])

theorem IsBlockEigen.pow_three (hb : IsBlockEigen β b χ) (hexp : ∀ x : E, x ^ 3 = 1) (x : E)
    (a : Fin 8) : χ a x ^ 3 = 1 := by
  have h := hb.mul (x * x) x a
  rw [hb.mul x x a, ← pow_three', hexp, hb.one] at h
  rw [pow_three']
  exact h.symm

theorem IsBlockEigen.ne_zero (hb : IsBlockEigen β b χ) (hexp : ∀ x : E, x ^ 3 = 1) (x : E)
    (a : Fin 8) : χ a x ≠ 0 := by
  intro h
  have := hb.pow_three hexp x a
  rw [h] at this
  norm_num at this

theorem IsBlockEigen.eq_one (hb : IsBlockEigen β b χ) {x : E} (h : ∀ a, χ a x = 1) :
    β x = 1 := by
  apply Units.ext
  apply Matrix.toLin'.injective
  apply b.ext
  intro a
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, hb x a, h a, one_smul, Units.val_one,
    Matrix.one_mulVec]

theorem IsBlockEigen.repr_mulVec (hb : IsBlockEigen β b χ) (x : E) (v : Fin 8 → L)
    (a : Fin 8) :
    b.repr (((β x : GL (Fin 8) L) : Matrix (Fin 8) (Fin 8) L) *ᵥ v) a = χ a x * b.repr v a := by
  have h : (b.coord a).comp (Matrix.toLin' ((β x : GL (Fin 8) L) : Matrix (Fin 8) (Fin 8) L)) =
      χ a x • b.coord a := by
    refine b.ext fun a' => ?_
    rw [LinearMap.comp_apply, Matrix.toLin'_apply, hb x a', LinearMap.smul_apply, map_smul]
    simp only [Module.Basis.coord_apply, Module.Basis.repr_self, smul_eq_mul,
      Finsupp.single_apply]
    split_ifs with haa
    · rw [haa]
    · simp
  have := LinearMap.congr_fun h v
  rwa [LinearMap.comp_apply, Matrix.toLin'_apply, LinearMap.smul_apply, Module.Basis.coord_apply,
    Module.Basis.coord_apply, smul_eq_mul] at this

theorem IsBlockEigen.exists_index (hb : IsBlockEigen β b χ) {v : Fin 8 → L} (hv : v ≠ 0)
    {c : E → L} (hc : ∀ x, ((β x : GL (Fin 8) L) : Matrix (Fin 8) (Fin 8) L) *ᵥ v = c x • v) :
    ∃ a, χ a = c := by
  obtain ⟨a, ha⟩ : ∃ a, b.repr v a ≠ 0 := by
    by_contra h
    push Not at h
    apply hv
    rw [← b.sum_repr v]
    simp [h]
  refine ⟨a, funext fun x => ?_⟩
  have h1 := hb.repr_mulVec x v a
  rw [hc x, map_smul, Finsupp.smul_apply, smul_eq_mul] at h1
  exact (mul_right_cancel₀ ha h1).symm

theorem IsBlockEigen.exists_pair (hb : IsBlockEigen β b χ) {B : Matrix (Fin 8) (Fin 8) L}
    (hB : B.det ≠ 0)
    (hinv : ∀ x v w, (((β x : GL (Fin 8) L) : Matrix (Fin 8) (Fin 8) L) *ᵥ v) ⬝ᵥ
      (B *ᵥ (((β x : GL (Fin 8) L) : Matrix (Fin 8) (Fin 8) L) *ᵥ w)) = v ⬝ᵥ (B *ᵥ w))
    (a : Fin 8) : ∃ c, (∀ x, χ c x = (χ a x)⁻¹) ∧ b a ⬝ᵥ (B *ᵥ b c) ≠ 0 := by
  obtain ⟨c, hc⟩ := Sec4.exists_form_ne_zero hB b (b.ne_zero a)
  refine ⟨c, fun x => ?_, hc⟩
  have h1 := hinv x (b a) (b c)
  rw [hb x a, hb x c, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    smul_eq_mul, ← mul_assoc] at h1
  have h2 : (χ a x * χ c x - 1) * (b a ⬝ᵥ (B *ᵥ b c)) = 0 := by linear_combination h1
  have h3 : χ a x * χ c x = 1 := by
    have := (mul_eq_zero.mp h2).resolve_right hc
    linear_combination this
  exact eq_inv_of_mul_eq_one_right h3

end Block

theorem pow_eq_of_pow_three {L : Type*} [Field L] {l : L} (hl : l ^ 3 = 1) (q : ℕ) :
    l ^ q = l ^ (q % 3) := by
  conv_lhs => rw [← Nat.div_add_mod q 3, pow_add, pow_mul, hl, one_pow, one_mul]

theorem sq_eq_inv_of_pow_three {L : Type*} [Field L] {l : L} (hl : l ^ 3 = 1) : l ^ 2 = l⁻¹ := by
  have h : l * l ^ 2 = 1 := by rw [← pow_succ', hl]
  exact eq_inv_of_mul_eq_one_right h

theorem pow_pow_eq_self_of_pow_three {L : Type*} [Field L] {l : L} (hl : l ^ 3 = 1) {q : ℕ}
    (hq : ¬ 3 ∣ q) : (l ^ q) ^ q = l := by
  rw [← pow_mul, pow_eq_of_pow_three hl, Nat.mul_mod]
  have : q % 3 = 1 ∨ q % 3 = 2 := by omega
  rcases this with h | h <;> rw [h] <;> norm_num

theorem eq_one_of_pow_eq_one_of_pow_three {L : Type*} [Field L] {l : L} (hl : l ^ 3 = 1)
    {q : ℕ} (hq : ¬ 3 ∣ q) (h : l ^ q = 1) : l = 1 := by
  rw [← pow_pow_eq_self_of_pow_three hl hq, h, one_pow]

theorem pow_eq_or_of_pow_three {L : Type*} [Field L] {l : L} (hl : l ^ 3 = 1) {q : ℕ}
    (hq : ¬ 3 ∣ q) : (q % 3 = 1 ∧ l ^ q = l) ∨ (q % 3 = 2 ∧ l ^ q = l⁻¹) := by
  rw [pow_eq_of_pow_three hl]
  have : q % 3 = 1 ∨ q % 3 = 2 := by omega
  rcases this with h | h
  · exact Or.inl ⟨h, by rw [h, pow_one]⟩
  · exact Or.inr ⟨h, by rw [h, sq_eq_inv_of_pow_three hl]⟩

section Bound

variable {L : Type*} [Field L] {E : Type*} [Group E]

theorem card_le_nine_of_triality [IsAlgClosed L] [Finite E] (h3 : (3 : L) ≠ 0)
    (hcomm : ∀ x y : E, x * y = y * x) (hexp : ∀ x : E, x ^ 3 = 1)
    (β : Fin 3 → E →* GL (Fin 8) L) (hfaith : ∀ x, (∀ j, β j x = 1) → x = 1)
    (B : Matrix (Fin 8) (Fin 8) L) (hB : B.det ≠ 0)
    (μ ν : (Fin 8 → L) → (Fin 8 → L) → (Fin 8 → L))
    (hμl : ∀ (c : L) v s, μ (c • v) s = c • μ v s) (hμr : ∀ (c : L) v s, μ v (c • s) = c • μ v s)
    (hνr : ∀ (c : L) v s, ν v (c • s) = c • ν v s)
    (hμE : ∀ x v s, ((β 2 x : GL (Fin 8) L) : Matrix (Fin 8) (Fin 8) L) *ᵥ μ v s =
      μ (((β 0 x : GL (Fin 8) L) : Matrix (Fin 8) (Fin 8) L) *ᵥ v)
        (((β 1 x : GL (Fin 8) L) : Matrix (Fin 8) (Fin 8) L) *ᵥ s))
    (hνE : ∀ x v u, ((β 1 x : GL (Fin 8) L) : Matrix (Fin 8) (Fin 8) L) *ᵥ ν v u =
      ν (((β 0 x : GL (Fin 8) L) : Matrix (Fin 8) (Fin 8) L) *ᵥ v)
        (((β 2 x : GL (Fin 8) L) : Matrix (Fin 8) (Fin 8) L) *ᵥ u))
    (hcl : ∀ v w s, ν v (μ w s) + ν w (μ v s) = (v ⬝ᵥ (B *ᵥ w)) • s)
    (φ : L →+* L) (q : ℕ) (hq : ¬ 3 ∣ q) (hφ : ∀ c, φ c = c ^ q)
    (σ : Fin 3 → Equiv.Perm (Fin 8))
    (htw : ∀ x j r c, ((β (j + 1) x : GL (Fin 8) L) : Matrix (Fin 8) (Fin 8) L) (σ j r) (σ j c) =
      φ (((β j x : GL (Fin 8) L) : Matrix (Fin 8) (Fin 8) L) r c)) :
    Nat.card E ≤ 9 := by
  classical
  choose b χ hb using fun j => exists_block_eigenbasis h3 hcomm hexp (β j)
  have hne0 : ∀ j a x, χ j a x ≠ 0 := fun j a x => (hb j).ne_zero hexp x a
  have h3χ : ∀ j a x, χ j a x ^ 3 = 1 := fun j a x => (hb j).pow_three hexp x a
  have hBinv : ∀ x v w, (((β 0 x : GL (Fin 8) L) : Matrix (Fin 8) (Fin 8) L) *ᵥ v) ⬝ᵥ
      (B *ᵥ (((β 0 x : GL (Fin 8) L) : Matrix (Fin 8) (Fin 8) L) *ᵥ w)) = v ⬝ᵥ (B *ᵥ w) := by
    intro x v w
    set s := b 1 0 with hs
    have hsx : ((β 1 x : GL (Fin 8) L) : Matrix (Fin 8) (Fin 8) L) *ᵥ s ≠ 0 := by
      rw [hs, hb 1 x 0]
      exact smul_ne_zero (hne0 1 0 x) ((b 1).ne_zero 0)
    have h1 := hcl (((β 0 x : GL (Fin 8) L) : Matrix (Fin 8) (Fin 8) L) *ᵥ v)
      (((β 0 x : GL (Fin 8) L) : Matrix (Fin 8) (Fin 8) L) *ᵥ w)
      (((β 1 x : GL (Fin 8) L) : Matrix (Fin 8) (Fin 8) L) *ᵥ s)
    rw [← hμE, ← hμE, ← hνE, ← hνE, ← Matrix.mulVec_add, hcl, Matrix.mulVec_smul] at h1
    exact (smul_left_injective L hsx h1).symm
  have hpair0 : ∀ a, ∃ c, (∀ x, χ 0 c x = (χ 0 a x)⁻¹) ∧ b 0 a ⬝ᵥ (B *ᵥ b 0 c) ≠ 0 :=
    fun a => (hb 0).exists_pair hB hBinv a
  have htwist : ∀ j a, ∃ a', ∀ x, χ (j + 1) a' x = χ j a x ^ q := by
    intro j a
    set v := b j a with hv
    set w : Fin 8 → L := fun r => φ (v ((σ j).symm r)) with hw
    have hw0 : w ≠ 0 := by
      intro h
      apply (b j).ne_zero a
      funext r
      have := congrFun h (σ j r)
      simp only [hw, Equiv.symm_apply_apply, Pi.zero_apply, map_eq_zero] at this
      exact this
    have heig : ∀ x, ((β (j + 1) x : GL (Fin 8) L) : Matrix (Fin 8) (Fin 8) L) *ᵥ w =
        (χ j a x ^ q) • w := by
      intro x
      funext r
      obtain ⟨r₀, rfl⟩ := (σ j).surjective r
      have hv' := congrFun (hb j x a) r₀
      calc (((β (j + 1) x : GL (Fin 8) L) : Matrix (Fin 8) (Fin 8) L) *ᵥ w) (σ j r₀)
          = ∑ k, ((β (j + 1) x : GL (Fin 8) L) : Matrix (Fin 8) (Fin 8) L) (σ j r₀) k * w k :=
            rfl
        _ = ∑ k, ((β (j + 1) x : GL (Fin 8) L) : Matrix (Fin 8) (Fin 8) L) (σ j r₀) (σ j k) *
              w (σ j k) := (Equiv.sum_comp (σ j) _).symm
        _ = ∑ k, φ (((β j x : GL (Fin 8) L) : Matrix (Fin 8) (Fin 8) L) r₀ k * v k) := by
            simp only [htw, hw, Equiv.symm_apply_apply, map_mul]
        _ = φ ((((β j x : GL (Fin 8) L) : Matrix (Fin 8) (Fin 8) L) *ᵥ v) r₀) := by
            rw [← map_sum]
            rfl
        _ = φ (χ j a x * v r₀) := by rw [hv']; rfl
        _ = ((χ j a x ^ q) • w) (σ j r₀) := by
            simp only [Pi.smul_apply, smul_eq_mul, hw, Equiv.symm_apply_apply, hφ, mul_pow]
    obtain ⟨a', ha'⟩ := (hb (j + 1)).exists_index hw0 heig
    exact ⟨a', fun x => congrFun ha' x⟩
  have h20 : (2 : Fin 3) + 1 = 0 := rfl
  have h01 : (0 : Fin 3) + 1 = 1 := rfl
  have h12 : (1 : Fin 3) + 1 = 2 := rfl
  have hfaith0 : ∀ x, (∀ a, χ 0 a x = 1) → x = 1 := by
    intro x hx
    refine hfaith x fun j => (hb j).eq_one fun a => ?_
    fin_cases j
    · exact hx a
    · show χ 1 a x = 1
      obtain ⟨a₂, ha₂⟩ := htwist 1 a
      rw [h12] at ha₂
      obtain ⟨a₀, ha₀⟩ := htwist 2 a₂
      rw [h20] at ha₀
      have h1 := ha₀ x
      rw [ha₂ x, pow_pow_eq_self_of_pow_three (h3χ 1 a x) hq, hx a₀] at h1
      exact h1.symm
    · show χ 2 a x = 1
      obtain ⟨a₀, ha₀⟩ := htwist 2 a
      rw [h20] at ha₀
      have h1 := ha₀ x
      rw [hx a₀] at h1
      exact eq_one_of_pow_eq_one_of_pow_three (h3χ 2 a x) hq h1.symm
  have hprod0 : ∀ a e, ∃ e', χ 0 e' = χ 0 a * χ 0 e ∨ χ 0 e' = (χ 0 a)⁻¹ * χ 0 e := by
    intro a e
    obtain ⟨c, hc, hac⟩ := hpair0 a
    obtain ⟨e₁, he₁⟩ := htwist 0 e
    rw [h01] at he₁
    set s := b 1 e₁ with hs
    have hsum := hcl (b 0 a) (b 0 c) s
    have hne : (b 0 a ⬝ᵥ (B *ᵥ b 0 c)) • s ≠ 0 := smul_ne_zero hac ((b 1).ne_zero e₁)
    have hν0 : ∀ v, ν v 0 = 0 := fun v => by
      have := hνr 0 v 0
      rwa [zero_smul, zero_smul] at this
    have heig : ∀ a' (x : E), ((β 2 x : GL (Fin 8) L) : Matrix (Fin 8) (Fin 8) L) *ᵥ
        μ (b 0 a') s = (χ 0 a' x * χ 1 e₁ x) • μ (b 0 a') s := by
      intro a' x
      rw [hμE, hb 0 x a', hs, hb 1 x e₁, hμl, hμr, smul_smul]
    have hback : ∀ a', μ (b 0 a') s ≠ 0 → ∃ e', ∀ x, χ 0 e' x = χ 0 a' x ^ q * χ 0 e x := by
      intro a' h
      obtain ⟨e₂, he₂⟩ := (hb 2).exists_index h (heig a')
      obtain ⟨e', he'⟩ := htwist 2 e₂
      rw [h20] at he'
      refine ⟨e', fun x => ?_⟩
      rw [he' x, he₂, mul_pow, he₁ x, pow_pow_eq_self_of_pow_three (h3χ 0 e x) hq]
    by_cases h1 : μ (b 0 a) s = 0
    · by_cases h2 : μ (b 0 c) s = 0
      · exfalso
        rw [h1, h2, hν0, hν0, add_zero] at hsum
        exact hne hsum.symm
      · obtain ⟨e', he'⟩ := hback c h2
        rcases pow_eq_or_of_pow_three (h3χ 0 a 1) hq with ⟨hq1, -⟩ | ⟨hq2, -⟩
        · refine ⟨e', Or.inr (funext fun x => ?_)⟩
          rw [he' x, hc x, Pi.mul_apply, Pi.inv_apply, inv_pow, pow_eq_of_pow_three (h3χ 0 a x),
            hq1, pow_one]
        · refine ⟨e', Or.inl (funext fun x => ?_)⟩
          rw [he' x, hc x, Pi.mul_apply, inv_pow, pow_eq_of_pow_three (h3χ 0 a x), hq2,
            sq_eq_inv_of_pow_three (h3χ 0 a x), inv_inv]
    · obtain ⟨e', he'⟩ := hback a h1
      rcases pow_eq_or_of_pow_three (h3χ 0 a 1) hq with ⟨hq1, -⟩ | ⟨hq2, -⟩
      · refine ⟨e', Or.inl (funext fun x => ?_)⟩
        rw [he' x, Pi.mul_apply, pow_eq_of_pow_three (h3χ 0 a x), hq1, pow_one]
      · refine ⟨e', Or.inr (funext fun x => ?_)⟩
        rw [he' x, Pi.mul_apply, Pi.inv_apply, pow_eq_of_pow_three (h3χ 0 a x), hq2,
          sq_eq_inv_of_pow_three (h3χ 0 a x)]
  have hinv0 : ∀ a, ∃ a', χ 0 a' = (χ 0 a)⁻¹ := fun a => by
    obtain ⟨c, hc, -⟩ := hpair0 a
    exact ⟨c, funext hc⟩
  set χu : Fin 8 → E → Lˣ := fun a x => Units.mk0 (χ 0 a x) (hne0 0 a x) with hχu
  have hχu_val : ∀ a x, ((χu a x : Lˣ) : L) = χ 0 a x := fun _ _ => rfl
  refine card_le_nine_of_characters_eight χu (fun a x y => Units.ext ?_) hexp (fun x hx => ?_)
    ?_ (fun a => ?_) (fun a e _ _ _ => ?_)
  · simp only [hχu_val, Units.val_mul]
    exact (hb 0).mul x y a
  · refine hfaith0 x fun a => ?_
    have := congrArg Units.val (hx a)
    simpa [hχu_val] using this
  · calc Nat.card {a // χu a ≠ 1} ≤ Nat.card (Fin 8) := Finite.card_subtype_le _
      _ = 8 := by simp
  · obtain ⟨a', ha'⟩ := hinv0 a
    refine ⟨a', funext fun x => Units.ext ?_⟩
    rw [hχu_val, Pi.inv_apply, Units.val_inv_eq_inv_val, hχu_val, ha', Pi.inv_apply]
  · obtain ⟨e', he' | he'⟩ := hprod0 a e
    · refine ⟨e', Or.inl (funext fun x => Units.ext ?_)⟩
      rw [hχu_val, Pi.mul_apply, Units.val_mul, hχu_val, hχu_val, he', Pi.mul_apply]
    · refine ⟨e', Or.inr (funext fun x => Units.ext ?_)⟩
      rw [hχu_val, Pi.mul_apply, Units.val_mul, Pi.inv_apply, Units.val_inv_eq_inv_val,
        hχu_val, hχu_val, he', Pi.mul_apply, Pi.inv_apply]

end Bound

end CFSG.RankThree.PartTwo.Sec21.Item223Rank2Proof
