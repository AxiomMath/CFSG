module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiRank

public section

namespace CFSG.RankThree.PartTwo.Sec4.Res417Frame

open Matrix CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K]

theorem exists_mk_mem_of_frame (E : Subgroup (GL (Fin 3) K ⧸ StatedScalars (Fin 3) K))
    (hexp : ∀ x ∈ E, x ^ 3 = 1) {b : Fin 3 → (Fin 3 → K)} (hb : LinearIndependent K b)
    (hd : ∀ y : GL (Fin 3) K, (y : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) ∈ E →
      ∀ i, ∃ c : K, (y : Matrix (Fin 3) (Fin 3) K) *ᵥ b i = c • b i)
    (hE : 9 ≤ Nat.card E) {u v : K} (hu : u ^ 3 = 1) (hv : v ^ 3 = 1) :
    ∃ y : GL (Fin 3) K, (y : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) ∈ E ∧ ∃ l : K,
      (y : Matrix (Fin 3) (Fin 3) K) *ᵥ b 0 = l • b 0 ∧
      (y : Matrix (Fin 3) (Fin 3) K) *ᵥ b 1 = (l * u) • b 1 ∧
      (y : Matrix (Fin 3) (Fin 3) K) *ᵥ b 2 = (l * v) • b 2 := by
  classical
  have hb0 : ∀ i, b i ≠ 0 := fun i => hb.ne_zero i
  have hF : ∀ x : E, ∃ c : Fin 3 → Kˣ, ∀ i,
      ((x.1.out : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ b i = (c i : K) • b i := by
    intro x
    have hx : (x.1.out : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) ∈ E := by
      rw [QuotientGroup.out_eq']
      exact x.2
    choose c hc using hd _ hx
    have hc0 : ∀ i, c i ≠ 0 := by
      intro i h0
      have := hc i
      rw [h0, zero_smul] at this
      have hinj := (Matrix.mulVec_injective_iff_isUnit (A := ((x.1.out : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K))).mpr (x.1.out.isUnit)
      exact hb0 i (hinj (by rw [this, Matrix.mulVec_zero]))
    exact ⟨fun i => Units.mk0 (c i) (hc0 i), fun i => by rw [Units.val_mk0, hc i]⟩
  choose c hc using hF
  have hratio : ∀ x : E, ∀ i, (c x i / c x 0) ^ 3 = 1 := by
    intro x i
    have hx : (x.1.out : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) ∈ E := by
      rw [QuotientGroup.out_eq']
      exact x.2
    obtain ⟨ℓ, hℓ⟩ := pow_three_mem_of_mk (hexp _ hx)
    have hcube : ∀ j, ((c x j : K)) ^ 3 = ℓ := by
      intro j
      have hpow : ∀ n : ℕ, (((x.1.out ^ n : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) *ᵥ b j =
          (c x j : K) ^ n • b j := by
        intro n
        induction n with
        | zero => rw [pow_zero, pow_zero, one_smul, Units.val_one, Matrix.one_mulVec]
        | succ n ih =>
          rw [pow_succ, Units.val_mul, ← Matrix.mulVec_mulVec, hc x j, Matrix.mulVec_smul, ih,
            smul_smul, pow_succ, mul_comm]
      have h1 := hpow 3
      rw [← hℓ, coe_scalar_eq_smul, Matrix.smul_mulVec, Matrix.one_mulVec] at h1
      have h2 : (((c x j : K)) ^ 3 - ℓ) • b j = 0 := by rw [sub_smul, h1, sub_self]
      exact sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right (hb0 j))
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_div_eq_div_val, div_pow, hcube, hcube, div_self
      (Units.ne_zero ℓ), Units.val_one]
  let F : E → rootsOfUnity 3 K × rootsOfUnity 3 K := fun x =>
    (⟨c x 1 / c x 0, (mem_rootsOfUnity 3 _).mpr (hratio x 1)⟩,
      ⟨c x 2 / c x 0, (mem_rootsOfUnity 3 _).mpr (hratio x 2)⟩)
  have hinj : Function.Injective F := by
    intro x x' hxx'
    simp only [F, Prod.mk.injEq, Subtype.mk.injEq] at hxx'
    obtain ⟨h1, h2⟩ := hxx'
    set lam : Kˣ := c x 0 / c x' 0 with hlam
    have key : ∀ {a b a' b' : Kˣ}, a / b = a' / b' → a = b / b' * a' := by
      intro a b a' b' h
      apply Units.ext
      have h' := congrArg Units.val h
      simp only [Units.val_div_eq_div_val] at h'
      rw [Units.val_mul, Units.val_div_eq_div_val]
      have hb := b.ne_zero
      have hb' := b'.ne_zero
      rw [show (a : K) = a' / b' * b by rw [← h', div_mul_cancel₀ _ hb]]
      ring
    have hall : ∀ i, c x i = lam * c x' i := by
      intro i
      fin_cases i
      · show c x 0 = lam * c x' 0
        rw [hlam, div_mul_cancel]
      · exact key h1
      · exact key h2
    have heq : ((x.1.out : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        ((x'.1.out * GeneralLinearGroup.scalar (Fin 3) lam : GL (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K) := by
      apply eq_of_mulVec_eq_of_linearIndependent hb
      intro i
      calc ((x.1.out : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ b i
          = ((lam * c x' i : Kˣ) : K) • b i := by rw [hc x i, hall i]
        _ = ((x'.1.out : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
            (((GeneralLinearGroup.scalar (Fin 3) lam : GL (Fin 3) K) :
              Matrix (Fin 3) (Fin 3) K) *ᵥ b i) := by
            rw [coe_scalar_eq_smul, Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.mulVec_smul,
              hc x' i, smul_smul, Units.val_mul]
        _ = _ := by rw [Matrix.mulVec_mulVec, ← Units.val_mul]
    apply Subtype.ext
    rw [← QuotientGroup.out_eq' x.1, ← QuotientGroup.out_eq' x'.1, Units.ext heq,
      QuotientGroup.mk_mul]
    have : ((GeneralLinearGroup.scalar (Fin 3) lam : GL (Fin 3) K) :
        GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr ⟨lam, rfl⟩
    rw [this, mul_one]
  have hfinE : Finite E := Nat.finite_of_card_ne_zero (by omega)
  have hle : Nat.card E = Nat.card (rootsOfUnity 3 K × rootsOfUnity 3 K) := by
    have h1 := Nat.card_le_card_of_injective F hinj
    have h2 : Nat.card (rootsOfUnity 3 K × rootsOfUnity 3 K) ≤ 9 := by
      rw [Nat.card_prod]
      have : Nat.card (rootsOfUnity 3 K) ≤ 3 := card_rootsOfUnity K 3
      exact (Nat.mul_le_mul this this).trans (by norm_num)
    omega
  have hfin2 : Finite (rootsOfUnity 3 K × rootsOfUnity 3 K) :=
    Nat.finite_of_card_ne_zero (by omega)
  have hbij := (Nat.bijective_iff_injective_and_card F).mpr ⟨hinj, hle⟩
  have hu0 : u ≠ 0 := by
    rintro rfl
    norm_num at hu
  have hv0 : v ≠ 0 := by
    rintro rfl
    norm_num at hv
  obtain ⟨x, hx⟩ := hbij.2 (⟨Units.mk0 u hu0, (mem_rootsOfUnity 3 _).mpr (Units.ext (by
      rw [Units.val_pow_eq_pow_val, Units.val_mk0, hu, Units.val_one]))⟩,
    ⟨Units.mk0 v hv0, (mem_rootsOfUnity 3 _).mpr (Units.ext (by
      rw [Units.val_pow_eq_pow_val, Units.val_mk0, hv, Units.val_one]))⟩)
  simp only [F, Prod.mk.injEq, Subtype.mk.injEq] at hx
  obtain ⟨h1, h2⟩ := hx
  have hc0 := (c x 0).ne_zero
  have e1 : (c x 1 : K) = c x 0 * u := by
    have := congrArg Units.val h1
    rw [Units.val_div_eq_div_val, Units.val_mk0] at this
    rw [← this, mul_div_cancel₀ _ hc0]
  have e2 : (c x 2 : K) = c x 0 * v := by
    have := congrArg Units.val h2
    rw [Units.val_div_eq_div_val, Units.val_mk0] at this
    rw [← this, mul_div_cancel₀ _ hc0]
  refine ⟨x.1.out, ?_, c x 0, hc x 0, ?_, ?_⟩
  · rw [QuotientGroup.out_eq']
    exact x.2
  · rw [hc x 1, e1]
  · rw [hc x 2, e2]

end CFSG.RankThree.PartTwo.Sec4.Res417Frame
