module

public import CFSG.LocalAnalysis.StandardType.GGPGLToralityMatrix

public section

namespace CFSG.StandardType.TypeA.PGLTor

open Matrix

universe u

variable {ι : Type u} [Fintype ι] [DecidableEq ι] {K : Type*} [Field K] {p : ℕ}

section BlockHom

variable {β : Type*} [DecidableEq β]

@[expose] noncomputable def blockHom (w : ι → β) (b : β) (B : Subgroup (GL ι K))
    (hB : ∀ x ∈ B, IsBlockDiag w (x : Matrix ι ι K)) : B →* GL {i // w i = b} K where
  toFun x :=
    ⟨((x : GL ι K) : Matrix ι ι K).toSquareBlock w b,
      ((x⁻¹ : GL ι K) : Matrix ι ι K).toSquareBlock w b, by
        rw [← toSquareBlock_mul_of_isBlockDiag (hB _ x.2), ← Units.val_mul, mul_inv_cancel,
          Units.val_one, toSquareBlock_one], by
        rw [← toSquareBlock_mul_of_isBlockDiag (hB _ (B.inv_mem x.2)), ← Units.val_mul,
          inv_mul_cancel, Units.val_one, toSquareBlock_one]⟩
  map_one' := Units.ext (by
    change ((((1 : B) : GL ι K) : Matrix ι ι K)).toSquareBlock w b = 1
    rw [Subgroup.coe_one, Units.val_one, toSquareBlock_one])
  map_mul' x y := Units.ext (by
    change ((((x * y : B) : GL ι K) : Matrix ι ι K)).toSquareBlock w b =
      (((x : GL ι K) : Matrix ι ι K)).toSquareBlock w b *
        (((y : GL ι K) : Matrix ι ι K)).toSquareBlock w b
    rw [Subgroup.coe_mul, Units.val_mul, toSquareBlock_mul_of_isBlockDiag (hB _ x.2)])

theorem coe_blockHom (w : ι → β) (b : β) (B : Subgroup (GL ι K))
    (hB : ∀ x ∈ B, IsBlockDiag w (x : Matrix ι ι K)) (x : B) :
    ((blockHom w b B hB x : GL {i // w i = b} K) : Matrix {i // w i = b} {i // w i = b} K) =
      ((x : GL ι K) : Matrix ι ι K).toSquareBlock w b :=
  rfl

end BlockHom

section Kernel

theorem mulVec_mem_eigen {t : ι → K} {u β : K} {g : Matrix ι ι K}
    (hgh : diagonal t * g = u • (g * diagonal t)) {v : ι → K} (hv : diagonal t *ᵥ v = β • v) :
    diagonal t *ᵥ (g *ᵥ v) = (u * β) • (g *ᵥ v) := by
  rw [mulVec_mulVec, hgh, smul_mulVec, ← mulVec_mulVec, hv, mulVec_smul, smul_smul]

theorem diagonal_mul_inv_eq {t : ι → K} {u : K} (hu : u ≠ 0) {g g' : Matrix ι ι K}
    (hgg' : g * g' = 1) (hg'g : g' * g = 1) (hgh : diagonal t * g = u • (g * diagonal t)) :
    diagonal t * g' = u⁻¹ • (g' * diagonal t) := by
  have h1 : g' * diagonal t = u • (diagonal t * g') :=
    calc g' * diagonal t = g' * (diagonal t * g) * g' := by
          simp only [Matrix.mul_assoc, hgg', Matrix.mul_one]
      _ = g' * (u • (g * diagonal t)) * g' := by rw [hgh]
      _ = u • (diagonal t * g') := by
          rw [Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc g' g, hg'g, Matrix.one_mul]
  rw [h1, smul_smul, inv_mul_cancel₀ hu, one_smul]

theorem eq_one_of_toSquareBlock_eq_one [NeZero p] {t : ι → K} {u : K} (hu : IsPrimitiveRoot u p)
    (ht : ∀ i, t i ^ p = 1) {α₀ : K} (hα₀ : α₀ ^ p = 1) {g c : GL ι K}
    (hgh : diagonal t * (g : Matrix ι ι K) = u • ((g : Matrix ι ι K) * diagonal t))
    (hcg : (c : Matrix ι ι K) * g = g * c) (hcb : IsBlockDiag t (c : Matrix ι ι K))
    (hc : (c : Matrix ι ι K).toSquareBlock t α₀ = 1) : c = 1 := by
  classical
  have hu0 : u ≠ 0 := hu.ne_zero (NeZero.ne p)
  set g' : Matrix ι ι K := ((g⁻¹ : GL ι K) : Matrix ι ι K) with hg'
  have hgg' : (g : Matrix ι ι K) * g' = 1 := by
    rw [hg', ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hg'g : g' * (g : Matrix ι ι K) = 1 := by
    rw [hg', ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hinv := diagonal_mul_inv_eq hu0 hgg' hg'g hgh
  have h0 : ∀ v : ι → K, diagonal t *ᵥ v = α₀ • v → (c : Matrix ι ι K) *ᵥ v = v := by
    intro v hv
    have hv0 : ∀ j, t j ≠ α₀ → v j = 0 := fun j hj => by
      have h1 := congrFun hv j
      rw [mulVec_diagonal, Pi.smul_apply, smul_eq_mul] at h1
      have h2 : (t j - α₀) * v j = 0 := by rw [sub_mul, h1, sub_self]
      exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hj)
    funext i
    have hterm : ∀ j, (c : Matrix ι ι K) i j * v j = if j = i then v i else 0 := by
      intro j
      by_cases hj : t j = α₀
      · by_cases hi : t i = α₀
        · have h3 := congrFun (congrFun hc ⟨i, hi⟩) ⟨j, hj⟩
          simp only [toSquareBlock_def, of_apply, one_apply, Subtype.mk.injEq] at h3
          rw [h3]
          by_cases hij : i = j
          · subst hij
            simp
          · simp [hij, Ne.symm hij]
        · have hij : t i ≠ t j := by rw [hj]; exact hi
          have hji : j ≠ i := fun h => hi (h ▸ hj)
          rw [hcb i j hij, zero_mul, ite_eq_right hji]
      · rw [hv0 j hj, mul_zero]
        by_cases hji : j = i
        · subst hji
          rw [ite_eq_left rfl, hv0 j hj]
        · rw [ite_eq_right hji]
    rw [mulVec, dotProduct, Finset.sum_congr rfl (fun j _ => hterm j),
      Finset.sum_ite_eq' Finset.univ i (fun _ => v i), ite_eq_left (Finset.mem_univ i)]
  have hk : ∀ k : ℕ, ∀ v : ι → K, diagonal t *ᵥ v = (u ^ k * α₀) • v →
      (c : Matrix ι ι K) *ᵥ v = v := by
    intro k
    induction k with
    | zero =>
      intro v hv
      rw [pow_zero, one_mul] at hv
      exact h0 v hv
    | succ k ih =>
      intro v hv
      have hw : diagonal t *ᵥ (g' *ᵥ v) = (u ^ k * α₀) • (g' *ᵥ v) := by
        rw [mulVec_mem_eigen hinv hv]
        congr 1
        rw [pow_succ]
        field_simp
      have hv' : v = (g : Matrix ι ι K) *ᵥ (g' *ᵥ v) := by
        rw [mulVec_mulVec, hgg', one_mulVec]
      rw [hv', mulVec_mulVec, hcg, ← mulVec_mulVec, ih _ hw]
  have hcol : ∀ j, (c : Matrix ι ι K) *ᵥ Pi.single j 1 = Pi.single j 1 := by
    intro j
    have hα0 : α₀ ≠ 0 := by
      intro h
      rw [h, zero_pow (NeZero.ne p)] at hα₀
      exact zero_ne_one hα₀
    obtain ⟨k, -, hk'⟩ := hu.eq_pow_of_pow_eq_one (ξ := t j * α₀⁻¹)
      (by rw [mul_pow, inv_pow, ht j, hα₀, inv_one, one_mul])
    apply hk k
    rw [hk', mul_assoc, inv_mul_cancel₀ hα0, mul_one, diagonal_mulVec_single, mul_one]
    funext m
    by_cases hm : m = j
    · subst hm
      simp
    · simp [hm]
  apply Units.ext
  ext i j
  have := congrFun (hcol j) i
  rw [mulVec_single_one] at this
  simpa [Matrix.col_apply, Pi.single_apply, one_apply, eq_comm] using this

end Kernel

theorem card_le_of_noncomm [Finite K] (hp : p.Prime) {G : Subgroup (GL ι K)}
    (hG : IsProjElem p G) {h : GL ι K} (hhG : h ∈ G) {t : ι → K}
    (ht : (h : Matrix ι ι K) = diagonal t) (hhp : h ^ p = 1) {g : GL ι K} (hgG : g ∈ G)
    (hgh : g * h ≠ h * g)
    (IH : ∀ (κ : Type u) [Fintype κ] [DecidableEq κ], Fintype.card κ < Fintype.card ι →
      ∀ R : Subgroup (GL κ K), IsProjElem p R →
        p * Nat.card R ≤ p ^ Fintype.card κ * (Nat.card K - 1)) :
    Nat.card G ≤ p ^ (Fintype.card ι / p + 1) * (Nat.card K - 1) := by
  classical
  have hne : Nonempty ι := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    exact hgh (Units.ext (Matrix.ext fun i => isEmptyElim i))
  have := Fact.mk hp
  have : NeZero p := ⟨hp.ne_zero⟩
  set χ := commChar hG hhG with hχ
  set u : Kˣ := χ ⟨g, hgG⟩ with hu
  have hspec : h * g = GeneralLinearGroup.scalar ι u * (g * h) := commChar_spec hG hhG ⟨g, hgG⟩
  have hu1 : u ≠ 1 := by
    intro h1
    rw [h1, map_one, one_mul] at hspec
    exact hgh hspec.symm
  have hup : u ^ p = 1 := commChar_pow_eq_one hG hhG _
  have huK : IsPrimitiveRoot (u : K) p := by
    have h1 : (u : K) ^ p = 1 := by rw [← Units.val_pow_eq_pow_val, hup, Units.val_one]
    have h2 : (u : K) ≠ 1 := fun h => hu1 (Units.ext h)
    exact (orderOf_eq_prime h1 h2) ▸ IsPrimitiveRoot.orderOf (u : K)
  have hghm : diagonal t * (g : Matrix ι ι K) = (u : K) • ((g : Matrix ι ι K) * diagonal t) := by
    have h1 := congrArg (fun A : GL ι K => (A : Matrix ι ι K)) hspec
    simp only [Units.val_mul, GeneralLinearGroup.coe_scalar] at h1
    rw [← ht, h1, scalar_apply, smul_eq_diagonal_mul]
  have htp : ∀ i, t i ^ p = 1 := by
    intro i
    have h1 := congrArg (fun A : GL ι K => (A : Matrix ι ι K) i i) hhp
    simp only [Units.val_pow_eq_pow_val, ht, diagonal_pow, Units.val_one, diagonal_apply_eq,
      one_apply_eq, Pi.pow_apply] at h1
    exact h1
  set C : Subgroup (GL ι K) := χ.ker.map G.subtype with hC
  have hCmem : ∀ x, x ∈ C ↔ x ∈ G ∧ h * x = x * h := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, (commChar_eq_one_iff hG hhG y).mp hy⟩
    · rintro ⟨hxG, hx⟩
      exact ⟨⟨x, hxG⟩, (commChar_eq_one_iff hG hhG ⟨x, hxG⟩).mpr hx, rfl⟩
  have hCcard : Nat.card G ≤ Nat.card C * p := by
    have h1 := Subgroup.card_ker_mul_card_range χ
    have h2 : Nat.card χ.range ≤ p := by
      have h3 : χ.range ≤ rootsOfUnity p K := by
        rintro _ ⟨x, rfl⟩
        exact commChar_pow_eq_one hG hhG x
      exact (Subgroup.card_le_of_le h3).trans (card_rootsOfUnity K p)
    have h3 : Nat.card C = Nat.card χ.ker :=
      Subgroup.card_map_of_injective (Subgroup.subtype_injective G)
    rw [h3, ← h1]
    exact Nat.mul_le_mul_left _ h2
  have hCblock : ∀ x ∈ C, IsBlockDiag t (x : Matrix ι ι K) := by
    intro x hx
    obtain ⟨-, hx2⟩ := (hCmem x).mp hx
    apply isBlockDiag_of_commute_diagonal
    have h1 := congrArg (fun A : GL ι K => (A : Matrix ι ι K)) hx2
    simp only [Units.val_mul] at h1
    rw [← ht]
    exact h1.symm
  obtain ⟨α₀, hα₀mem, hα₀card⟩ := Finset.exists_card_fiber_lt_of_card_lt_mul
    (s := Finset.univ) (t := Polynomial.nthRootsFinset p (1 : K)) (f := t)
    (n := Fintype.card ι / p + 1)
    (by rw [huK.card_nthRootsFinset, Finset.card_univ]; exact Nat.lt_mul_div_succ _ hp.pos)
  have hα₀p : α₀ ^ p = 1 := (Polynomial.mem_nthRootsFinset hp.pos 1).mp hα₀mem
  have hScard : Fintype.card {i // t i = α₀} ≤ Fintype.card ι / p := by
    rw [Fintype.card_subtype]
    omega
  have hSlt : Fintype.card {i // t i = α₀} < Fintype.card ι :=
    hScard.trans_lt (Nat.div_lt_self Fintype.card_pos hp.one_lt)
  set ρ := blockHom t α₀ C hCblock with hρ
  set R := ρ.range with hR
  have hscalC : ∀ v : Kˣ, GeneralLinearGroup.scalar ι v ∈ C := fun v =>
    (hCmem _).mpr ⟨hG.scalar_mem v, (scalar_mul_comm v h).symm⟩
  have hρscal : ∀ v : Kˣ, ρ ⟨GeneralLinearGroup.scalar ι v, hscalC v⟩ =
      GeneralLinearGroup.scalar {i // t i = α₀} v := fun v => Units.ext (by
    rw [hρ, coe_blockHom, GeneralLinearGroup.coe_scalar, GeneralLinearGroup.coe_scalar]
    exact toSquareBlock_scalar t α₀ _)
  have hRproj : IsProjElem p R := by
    refine ⟨fun v => ⟨_, hρscal v⟩, ?_, ?_⟩
    · rintro _ ⟨x, rfl⟩
      obtain ⟨v, hv⟩ := hG.pow_scalar x ((hCmem x).mp x.2).1
      refine ⟨v, ?_⟩
      rw [← map_pow, ← hρscal v]
      congr 1
      exact Subtype.ext (by rw [Subgroup.coe_pow, hv])
    · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
      obtain ⟨v, hv⟩ := hG.comm_scalar x ((hCmem x).mp x.2).1 y ((hCmem y).mp y.2).1
      refine ⟨v, ?_⟩
      rw [← map_mul, ← map_mul, ← hρscal v, ← map_mul]
      congr 1
      exact Subtype.ext (by simp only [Subgroup.coe_mul]; exact hv)
  have hRcard := IH {i // t i = α₀} hSlt R hRproj
  set χg := commChar hG hgG with hχg
  have hCG : ∀ x : C, (x : GL ι K) ∈ G := fun x => ((hCmem x).mp x.2).1
  let F : C → R × rootsOfUnity p K := fun x =>
    (⟨ρ x, x, rfl⟩, ⟨χg ⟨x, hCG x⟩, commChar_pow_eq_one hG hgG _⟩)
  have hinj : Function.Injective F := by
    intro x y hxy
    simp only [F, Prod.mk.injEq] at hxy
    have h1 : ρ x = ρ y := congrArg Subtype.val hxy.1
    have h2 : χg ⟨x, hCG x⟩ = χg ⟨y, hCG y⟩ := congrArg Subtype.val hxy.2
    set c : C := x⁻¹ * y with hcdef
    have hc1 : ρ c = 1 := by rw [hcdef, map_mul, map_inv, h1, inv_mul_cancel]
    have hcG' : (⟨c, hCG c⟩ : G) = (⟨x, hCG x⟩ : G)⁻¹ * ⟨y, hCG y⟩ := Subtype.ext rfl
    have hc2 : χg ⟨c, hCG c⟩ = 1 := by
      rw [hcG', map_mul, map_inv, h2, inv_mul_cancel]
    have hcg : g * c = c * g := (commChar_eq_one_iff hG hgG _).mp hc2
    have hcgm : ((c : GL ι K) : Matrix ι ι K) * (g : Matrix ι ι K) =
        (g : Matrix ι ι K) * ((c : GL ι K) : Matrix ι ι K) := by
      rw [← Units.val_mul, ← Units.val_mul, hcg]
    have hcb : ((c : GL ι K) : Matrix ι ι K).toSquareBlock t α₀ = 1 := by
      have h3 := congrArg (fun A : GL {i // t i = α₀} K =>
        (A : Matrix {i // t i = α₀} {i // t i = α₀} K)) hc1
      simpa only [hρ, coe_blockHom, Units.val_one] using h3
    have hc : (c : GL ι K) = 1 :=
      eq_one_of_toSquareBlock_eq_one huK htp hα₀p hghm hcgm (hCblock c c.2) hcb
    have hc' : c = 1 := Subtype.ext hc
    rw [hcdef, inv_mul_eq_one] at hc'
    exact hc'
  have hCle : Nat.card C ≤ Nat.card R * p := by
    have h1 := Nat.card_le_card_of_injective F hinj
    rw [Nat.card_prod] at h1
    exact h1.trans (Nat.mul_le_mul_left _ (card_rootsOfUnity K p))
  calc Nat.card G ≤ Nat.card C * p := hCcard
    _ ≤ Nat.card R * p * p := Nat.mul_le_mul_right _ hCle
    _ = p * (p * Nat.card R) := by ring
    _ ≤ p * (p ^ Fintype.card {i // t i = α₀} * (Nat.card K - 1)) :=
        Nat.mul_le_mul_left _ hRcard
    _ = p ^ (Fintype.card {i // t i = α₀} + 1) * (Nat.card K - 1) := by ring
    _ ≤ p ^ (Fintype.card ι / p + 1) * (Nat.card K - 1) :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hp.pos (by omega))

end CFSG.StandardType.TypeA.PGLTor
