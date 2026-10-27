module

public import CFSG.RankThree.CentralCover.SteinbergBNCoverPairingCore
public import CFSG.RankThree.Classical.SteinbergBJProjectiveSiegelRadical

public section

namespace CFSG.RankThree.GroupTheory

open CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.Assembly.LowTwoRank
open CFSG.RankThree.Classical CFSG.RankThree.CentralCover

variable {K : Type} [Field K] {r : ℕ}

@[expose] def blockSymmMat (B₀ : Matrix (Fin r) (Fin r) K) (b : K) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) K :=
  Matrix.of (Fin.snoc (fun i => Fin.snoc (B₀ i) 0) (Fin.snoc 0 b))

theorem blockSymmMat_castSucc_castSucc (B₀ : Matrix (Fin r) (Fin r) K) (b : K) (i j : Fin r) :
    blockSymmMat B₀ b i.castSucc j.castSucc = B₀ i j := by
  simp [blockSymmMat]

theorem blockSymmMat_castSucc_last (B₀ : Matrix (Fin r) (Fin r) K) (b : K) (i : Fin r) :
    blockSymmMat B₀ b i.castSucc (Fin.last r) = 0 := by
  simp [blockSymmMat]

theorem blockSymmMat_last_castSucc (B₀ : Matrix (Fin r) (Fin r) K) (b : K) (j : Fin r) :
    blockSymmMat B₀ b (Fin.last r) j.castSucc = 0 := by
  simp [blockSymmMat]

theorem blockSymmMat_last_last (B₀ : Matrix (Fin r) (Fin r) K) (b : K) :
    blockSymmMat B₀ b (Fin.last r) (Fin.last r) = b := by
  simp [blockSymmMat]

omit [Field K] in
theorem blockSymmMat_ext {M N : Matrix (Fin (r + 1)) (Fin (r + 1)) K}
    (h1 : ∀ i j : Fin r, M i.castSucc j.castSucc = N i.castSucc j.castSucc)
    (h2 : ∀ i : Fin r, M i.castSucc (Fin.last r) = N i.castSucc (Fin.last r))
    (h3 : ∀ j : Fin r, M (Fin.last r) j.castSucc = N (Fin.last r) j.castSucc)
    (h4 : M (Fin.last r) (Fin.last r) = N (Fin.last r) (Fin.last r)) : M = N := by
  ext i j
  induction i using Fin.lastCases with
  | last => induction j using Fin.lastCases with
    | last => exact h4
    | cast j => exact h3 j
  | cast i => induction j using Fin.lastCases with
    | last => exact h2 i
    | cast j => exact h1 i j

@[expose] def blockSymm (r : ℕ) (K : Type) [Field K] :
    symMatrices r K × K →+ symMatrices (r + 1) K where
  toFun x := ⟨blockSymmMat (x.1 : Matrix (Fin r) (Fin r) K) x.2, by
    rw [mem_symMatrices]
    have hx := x.1.2
    rw [mem_symMatrices] at hx
    refine blockSymmMat_ext (fun i j => ?_) (fun i => ?_) (fun j => ?_) ?_
    · rw [Matrix.transpose_apply, blockSymmMat_castSucc_castSucc, blockSymmMat_castSucc_castSucc]
      exact congrFun (congrFun hx i) j
    · rw [Matrix.transpose_apply, blockSymmMat_last_castSucc, blockSymmMat_castSucc_last]
    · rw [Matrix.transpose_apply, blockSymmMat_castSucc_last, blockSymmMat_last_castSucc]
    · rw [Matrix.transpose_apply]⟩
  map_zero' := by
    apply Subtype.ext
    refine blockSymmMat_ext (fun i j => ?_) (fun i => ?_) (fun j => ?_) ?_ <;>
      simp [blockSymmMat]
  map_add' x y := by
    apply Subtype.ext
    refine blockSymmMat_ext (fun i j => ?_) (fun i => ?_) (fun j => ?_) ?_ <;>
      simp [blockSymmMat]

theorem blockSymm_injective : Function.Injective (blockSymm r K) := by
  rintro ⟨B₀, b⟩ ⟨C₀, c⟩ h
  have h' := congrArg Subtype.val h
  change blockSymmMat (B₀ : Matrix (Fin r) (Fin r) K) b = blockSymmMat (C₀ : Matrix _ _ K) c at h'
  refine Prod.ext (Subtype.ext ?_) ?_
  · ext i j
    have := congrFun (congrFun h' i.castSucc) j.castSucc
    rwa [blockSymmMat_castSucc_castSucc, blockSymmMat_castSucc_castSucc] at this
  · have := congrFun (congrFun h' (Fin.last r)) (Fin.last r)
    rwa [blockSymmMat_last_last, blockSymmMat_last_last] at this

@[expose] def lastSign (r : ℕ) (K : Type) [Field K] : Fin (r + 1) → Kˣ :=
  Fin.snoc (fun _ => -1) 1

theorem lastSign_mul_self (i : Fin (r + 1)) : lastSign r K i * lastSign r K i = 1 := by
  induction i using Fin.lastCases with
  | last => simp [lastSign]
  | cast i => simp [lastSign]

theorem diagonal_lastSign_conj (B₀ : Matrix (Fin r) (Fin r) K) (b : K) :
    Matrix.diagonal (fun i => (lastSign r K i : K)) * blockSymmMat B₀ b *
      Matrix.diagonal (fun i => (lastSign r K i : K)) = blockSymmMat B₀ b := by
  refine blockSymmMat_ext (fun i j => ?_) (fun i => ?_) (fun j => ?_) ?_ <;>
    simp [Matrix.diagonal_mul, Matrix.mul_diagonal, lastSign, blockSymmMat]

theorem symplectic_defining_prime_central_cover_two_local_rank_witness {G : Type*} [Group G]
    [Finite G] (Y : Subgroup G) {p f n : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hn : 2 ≤ n)
    [Finite K] (hK : Nat.card K = p ^ f) (φ : Y →* StatedProj (StatedSp n K))
    (hφ : Function.Surjective φ) (hZ : φ.ker ≤ Subgroup.center Y) :
    ∃ z : G, z ∈ Y ∧ orderOf z = 2 ∧ ∃ V : Subgroup G,
      V ≤ Y ⊓ Subgroup.centralizer ({z} : Set G) ∧ IsElemAbelian p V ∧
        Nat.card V = p ^ (f * (n * (n - 1) / 2 + 1)) ∧
        f * (n * (n - 1) / 2 + 1) ≤ localRank p G := by
  classical
  obtain ⟨r, rfl⟩ : ∃ r, n = r + 1 := ⟨n - 1, by omega⟩
  have hr1 : 1 ≤ r := by omega
  have : Fact p.Prime := ⟨hp⟩
  have := Fintype.ofFinite K
  have : CharP K p :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hK])
  have hp2 : p ≠ 2 := by omega
  obtain ⟨hUel, -, hUcomm⟩ := symplectic_Siegel_root_central_preimage_abelian (n := r + 1)
    hp hp3 hK
  set ψ : Multiplicative (symMatrices r K × K) →* StatedProj (StatedSp (r + 1) K) :=
    (projSiegelHom (r + 1) K).comp (AddMonoidHom.toMultiplicative (blockSymm r K))
  have hψ : Function.Injective ψ :=
    projSiegelHom_injective.comp (Multiplicative.ofAdd.injective.comp
      (blockSymm_injective.comp Multiplicative.toAdd.injective))
  set D := ψ.range
  have hDle : D ≤ projSiegelRadical (r + 1) K := by
    rintro _ ⟨x, rfl⟩
    exact ⟨_, rfl⟩
  have hDcard : Nat.card D = p ^ (f * ((r + 1) * (r + 1 - 1) / 2 + 1)) := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv, Nat.card_congr Multiplicative.toAdd,
      Nat.card_prod, card_symMatrices, hK, ← pow_mul, ← pow_add]
    congr 1
    rw [Nat.add_sub_cancel, mul_comm (r + 1) r]
    ring
  set h : StatedSp (r + 1) K := ⟨torusGL (lastSign r K), torusGL_mem_statedSp _⟩
  set z : StatedProj (StatedSp (r + 1) K) := QuotientGroup.mk h
  have hneg : (-1 : K) ≠ 1 := by
    intro h1
    have h2 : ((2 : ℕ) : K) = 0 := by
      push_cast
      linear_combination -h1
    rw [CharP.cast_eq_zero_iff K p] at h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
  have hz1 : z ≠ 1 := by
    intro h1
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, StatedScalars,
      MonoidHom.mem_range] at h1
    obtain ⟨c, hc⟩ := h1
    have hc' := congrArg (fun g : GL (Fin (r + 1) ⊕ Fin (r + 1)) K =>
      (g : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) K)) hc
    have hε0 : lastSign r K (Fin.castSucc ⟨0, hr1⟩) = -1 := by
      unfold lastSign
      exact Fin.snoc_castSucc _ _ _
    have hεl : lastSign r K (Fin.last r) = 1 := by simp [lastSign]
    have h0 := congrFun (congrFun hc' (Sum.inl (Fin.castSucc ⟨0, hr1⟩)))
      (Sum.inl (Fin.castSucc ⟨0, hr1⟩))
    have hl := congrFun (congrFun hc' (Sum.inl (Fin.last r))) (Sum.inl (Fin.last r))
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq]
      at h0 hl
    change (c : K) = (↑(torusGL (lastSign r K)) :
      Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) K) _ _ at h0
    change (c : K) = (↑(torusGL (lastSign r K)) :
      Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) K) _ _ at hl
    rw [coe_torusGL, Matrix.fromBlocks_apply₁₁, Matrix.diagonal_apply_eq, hε0] at h0
    rw [coe_torusGL, Matrix.fromBlocks_apply₁₁, Matrix.diagonal_apply_eq, hεl] at hl
    rw [h0, Units.val_neg, Units.val_one] at hl
    exact hneg hl
  have hz2 : z ^ 2 = 1 := by
    rw [pow_two, ← QuotientGroup.mk_mul]
    have : h * h = 1 := by
      apply Subtype.ext
      apply Units.ext
      rw [Subgroup.coe_mul, Units.val_mul, coe_torusGL, Matrix.fromBlocks_multiply]
      simp only [Matrix.diagonal_mul_diagonal, Matrix.mul_zero, Matrix.zero_mul, add_zero,
        zero_add, OneMemClass.coe_one, Units.val_one]
      rw [← Matrix.fromBlocks_one]
      congr 1 <;> rw [← Matrix.diagonal_one] <;> congr 1 <;> funext i
      · rw [← Units.val_mul, lastSign_mul_self, Units.val_one]
      · rw [← Units.val_mul, ← mul_inv, lastSign_mul_self, inv_one, Units.val_one]
    rw [this, QuotientGroup.mk_one]
  have hz : orderOf z = 2 := orderOf_eq_prime hz2 hz1
  have hzD : ∀ x ∈ D, Commute z x := by
    rintro _ ⟨x, rfl⟩
    have hcomm : h * siegelSpHom (r + 1) K (Multiplicative.ofAdd (blockSymm r K x.toAdd)) =
        siegelSpHom (r + 1) K (Multiplicative.ofAdd (blockSymm r K x.toAdd)) * h := by
      apply Subtype.ext
      have h1 := torusGL_conj_siegelGL (lastSign r K)
        ((blockSymm r K x.toAdd : symMatrices (r + 1) K) : Matrix (Fin (r + 1)) (Fin (r + 1)) K)
      rw [mul_inv_eq_iff_eq_mul] at h1
      change torusGL (lastSign r K) * siegelGL
          ((blockSymm r K x.toAdd : symMatrices (r + 1) K) : Matrix (Fin (r + 1)) (Fin (r + 1)) K) =
        siegelGL ((blockSymm r K x.toAdd : symMatrices (r + 1) K) :
          Matrix (Fin (r + 1)) (Fin (r + 1)) K) * torusGL (lastSign r K)
      rw [h1]
      congr 2
      exact diagonal_lastSign_conj _ _
    change z * QuotientGroup.mk (siegelSpHom (r + 1) K _) =
      QuotientGroup.mk (siegelSpHom (r + 1) K _) * z
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    exact congrArg _ hcomm
  obtain ⟨u, huY, hu, V, hV, hVel, hVcard, -, -, hrank⟩ :=
    central_cover_involution_witness Y hφ hZ hp hp2 (D := D)
      (fun x hx => hUel.2 x (hDle hx))
      (fun x hx y hy => hUcomm φ hφ hZ x (Subgroup.comap_mono hDle hx) y
        (Subgroup.comap_mono hDle hy))
      (r := f * ((r + 1) * (r + 1 - 1) / 2 + 1)) hDcard.ge hz hzD
  exact ⟨u, huY, hu, V, hV, hVel, hVcard, hrank⟩

end CFSG.RankThree.GroupTheory
