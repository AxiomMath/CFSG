module

public import CFSG.Quasithin.Background.HSL3Rank
public import CFSG.Quasithin.Background.SmithB51Sp4Desc
public import CFSG.Quasithin.Background.FFC10A

public section

namespace CFSG.Quasithin

namespace B42SL3

open CFSG.Assembly.LowTwoRank CFSG.Quasithin.H CFSG.Quasithin.H.SL3Pair Matrix
open scoped Matrix

section Comm

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
theorem exists_dotProduct_ne_zero {φ : Fin 3 → K} (hφ : φ ≠ 0) :
    ∃ v : Fin 3 → K, φ ⬝ᵥ v ≠ 0 := by
  obtain ⟨j, hj⟩ : ∃ j, φ j ≠ 0 := by
    by_contra h
    push Not at h
    exact hφ (funext h)
  exact ⟨Pi.single j 1, by rwa [dotProduct_single, mul_one]⟩

omit [Finite K] [CharP K 2] in
theorem twisted_sub {a : MulAut (StdMod (Fin 3) K)} {σ : K ≃+* K} {lam : K}
    {φ ψ : Fin 3 → K} (hφ : ∀ v, σ (φ ⬝ᵥ v) * lam = φ ⬝ᵥ toAddMap a v)
    (hψ : ∀ v, σ (ψ ⬝ᵥ v) * lam = ψ ⬝ᵥ toAddMap a v) :
    ∀ v, σ ((φ - ψ) ⬝ᵥ v) * lam = (φ - ψ) ⬝ᵥ toAddMap a v := by
  intro v
  rw [sub_dotProduct, sub_dotProduct, map_sub, sub_mul, hφ, hψ]

omit [Finite K] [CharP K 2] in
theorem eq_zero_of_twisted {a : MulAut (StdMod (Fin 3) K)} {σ : K ≃+* K} {lam κ : K}
    (hκ : σ κ ≠ κ) {χ : Fin 3 → K} (hχ : ∀ v, σ (χ ⬝ᵥ v) * lam = χ ⬝ᵥ toAddMap a v)
    (hκχ : ∀ v, σ ((κ • χ) ⬝ᵥ v) * lam = (κ • χ) ⬝ᵥ toAddMap a v) : χ = 0 := by
  refine eq_zero_of_dotProduct_toAddMap (a := a) fun v => ?_
  have h1 := hκχ v
  rw [smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul, map_mul, mul_assoc, hχ] at h1
  have h2 : (σ κ - κ) * (χ ⬝ᵥ toAddMap a v) = 0 := by linear_combination h1
  exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hκ)

theorem card_le_of_comm_semilinear (E : Subgroup (GL (Fin 3) K)) (hsq : ∀ A ∈ E, A * A = 1)
    (hcomm : ∀ A ∈ E, ∀ B ∈ E, A * B = B * A) {a : MulAut (StdMod (Fin 3) K)} {σ : K ≃+* K}
    (ha : IsSemilinear a σ) (hσ : σ ≠ RingEquiv.refl K)
    (hac : ∀ A ∈ E, ∀ v, toAddMap a ((A : Matrix (Fin 3) (Fin 3) K) *ᵥ v) =
      (A : Matrix (Fin 3) (Fin 3) K) *ᵥ toAddMap a v) :
    Nat.card E ≤ Nat.card K := by
  classical
  by_contra hE
  push Not at hE
  obtain ⟨κ, hκ⟩ := exists_ne_of_ne_refl hσ
  have hq1 : 1 < Nat.card E := lt_of_le_of_lt Nat.card_pos hE
  rcases center_or_axis E hsq hcomm hE with ⟨c, hc, hall⟩ | ⟨ψ, hψ, hall⟩
  ·
    have hall' : ∀ A : E, ∃ φ : Fin 3 → K, φ ⬝ᵥ c = 0 ∧
        ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 + vecMulVec c φ :=
      fun A => hall A A.2
    choose φ hφc hφ using hall'
    have hkey : ∀ (A : E) v, σ (φ A ⬝ᵥ v) • toAddMap a c = (φ A ⬝ᵥ toAddMap a v) • c := by
      intro A v
      refine center_comm ha (fun w => ?_) v
      rw [← hφ A]
      exact hac A A.2 w
    obtain ⟨A₀, hA₀⟩ := exists_ne_one_of_one_lt_card hq1
    have hφ₀ : φ A₀ ≠ 0 := by
      intro h
      apply hA₀
      apply Subtype.ext
      apply Units.ext
      rw [hφ A₀, h, vecMulVec_zero, add_zero]
      rfl
    obtain ⟨v₀, hv₀⟩ := exists_dotProduct_ne_zero hφ₀
    have hσv₀ : σ (φ A₀ ⬝ᵥ v₀) ≠ 0 := (map_ne_zero σ).mpr hv₀
    set lam : K := (σ (φ A₀ ⬝ᵥ v₀))⁻¹ * (φ A₀ ⬝ᵥ toAddMap a v₀) with hlam
    have hac' : toAddMap a c = lam • c := by
      have h1 := hkey A₀ v₀
      rw [hlam, mul_smul, ← h1, smul_smul, inv_mul_cancel₀ hσv₀, one_smul]
    have hlam0 : lam ≠ 0 := by
      intro h0
      rw [h0, zero_smul] at hac'
      exact hc ((toAddMap_eq_zero_iff a).mp hac')
    have hS : ∀ (A : E) v, σ (φ A ⬝ᵥ v) * lam = φ A ⬝ᵥ toAddMap a v := by
      intro A v
      have h1 := hkey A v
      rw [hac', smul_smul] at h1
      exact smul_left_injective K hc h1
    let S := {χ : Fin 3 → K // χ ⬝ᵥ c = 0 ∧ ∀ v, σ (χ ⬝ᵥ v) * lam = χ ⬝ᵥ toAddMap a v}
    have hES : Nat.card E ≤ Nat.card S := by
      refine Nat.card_le_card_of_injective (fun A => (⟨φ A, hφc A, hS A⟩ : S)) ?_
      intro A B h
      have h1 : φ A = φ B := congrArg Subtype.val h
      apply Subtype.ext
      apply Units.ext
      rw [hφ A, hφ B, h1]
    have hSS : Nat.card S ^ 2 ≤ Nat.card K ^ 2 := by
      rw [sq, ← Nat.card_prod, ← card_orth hc]
      refine Nat.card_le_card_of_injective (fun p => ⟨p.1.1 + κ • p.2.1, ?_⟩) ?_
      · rw [dotProduct_comm, add_dotProduct, smul_dotProduct, p.1.2.1, p.2.2.1, smul_zero,
          add_zero]
      · rintro ⟨⟨x, hx₁, hx₂⟩, ⟨y, hy₁, hy₂⟩⟩ ⟨⟨x', hx'₁, hx'₂⟩, ⟨y', hy'₁, hy'₂⟩⟩ h
        have h0 : x + κ • y = x' + κ • y' := congrArg Subtype.val h
        have hyy : y - y' = 0 := by
          refine eq_zero_of_twisted (a := a) (κ := κ) hκ (twisted_sub hy₂ hy'₂) ?_
          have e : κ • (y - y') = x' - x := by
            rw [smul_sub]
            linear_combination (norm := module) h0
          rw [e]
          exact twisted_sub hx'₂ hx₂
        have hy : y = y' := sub_eq_zero.mp hyy
        subst hy
        have hx : x = x' := add_right_cancel h0
        subst hx
        rfl
    have := (Nat.pow_le_pow_iff_left (by norm_num : (2 : ℕ) ≠ 0)).mp hSS
    omega
  ·
    have hall' : ∀ A : E, ∃ w : Fin 3 → K, ψ ⬝ᵥ w = 0 ∧
        ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 + vecMulVec w ψ :=
      fun A => hall A A.2
    choose w hwψ hw using hall'
    obtain ⟨v₀, hv₀⟩ := exists_dotProduct_ne_zero hψ
    have hσv₀ : σ (ψ ⬝ᵥ v₀) ≠ 0 := (map_ne_zero σ).mpr hv₀
    set lam : K := (σ (ψ ⬝ᵥ v₀))⁻¹ * (ψ ⬝ᵥ toAddMap a v₀) with hlam
    have hS : ∀ A : E, toAddMap a (w A) = lam • w A := by
      intro A
      have h1 := axis_comm ha (fun u => by rw [← hw A]; exact hac A A.2 u) v₀
      rw [hlam, mul_smul, ← h1, smul_smul, inv_mul_cancel₀ hσv₀, one_smul]
    have hwinj : Function.Injective w := by
      intro A B h
      apply Subtype.ext
      apply Units.ext
      rw [hw A, hw B, h]
    by_cases hlam0 : lam = 0
    ·
      have hw0 : ∀ A : E, w A = 0 := by
        intro A
        have h1 := hS A
        rw [hlam0, zero_smul] at h1
        exact (toAddMap_eq_zero_iff a).mp h1
      have hsub : Subsingleton E := ⟨fun A B => hwinj (by rw [hw0 A, hw0 B])⟩
      have := Finite.card_le_one_iff_subsingleton.mpr hsub
      omega
    let S := {u : Fin 3 → K // ψ ⬝ᵥ u = 0 ∧ toAddMap a u = lam • u}
    have hES : Nat.card E ≤ Nat.card S :=
      Nat.card_le_card_of_injective (fun A => (⟨w A, hwψ A, hS A⟩ : S))
        (fun A B h => hwinj (congrArg Subtype.val h))
    have hSS : Nat.card S ^ 2 ≤ Nat.card K ^ 2 := by
      rw [sq, ← Nat.card_prod, ← card_orth hψ]
      refine Nat.card_le_card_of_injective (fun p => ⟨p.1.1 + κ • p.2.1, ?_⟩) ?_
      · rw [dotProduct_add, dotProduct_smul, p.1.2.1, p.2.2.1, smul_zero, add_zero]
      · rintro ⟨⟨x, hx₁, hx₂⟩, ⟨y, hy₁, hy₂⟩⟩ ⟨⟨x', hx'₁, hx'₂⟩, ⟨y', hy'₁, hy'₂⟩⟩ h
        have h0 : x + κ • y = x' + κ • y' := congrArg Subtype.val h
        have h1 : toAddMap a (x + κ • y) = toAddMap a (x' + κ • y') := by rw [h0]
        rw [toAddMap_add, toAddMap_add, ha, ha, hx₂, hy₂, hx'₂, hy'₂] at h1
        have h2 : lam • ((σ κ - κ) • (y - y')) = 0 := by
          linear_combination (norm := module) h1 - lam • h0
        rw [smul_eq_zero, smul_eq_zero] at h2
        have hy : y = y' := by
          rcases h2 with h2 | h2 | h2
          · exact absurd h2 hlam0
          · exact absurd (sub_eq_zero.mp h2) hκ
          · exact sub_eq_zero.mp h2
        subst hy
        have hx : x = x' := add_right_cancel h0
        subst hx
        rfl
    have := (Nat.pow_le_pow_iff_left (by norm_num : (2 : ℕ) ≠ 0)).mp hSS
    omega

end Comm

section Normalizer

variable {K : Type} [Field K] [Finite K] [CharP K 2]

@[expose] def linFix (E : Subgroup (MulAut (StdMod (Fin 3) K))) : Submodule K (Fin 3 → K) where
  carrier := {v | ∀ A ∈ linMat E, (A : Matrix (Fin 3) (Fin 3) K) *ᵥ v = v}
  add_mem' := fun {v w} hv hw A hA => by rw [Matrix.mulVec_add, hv A hA, hw A hA]
  zero_mem' := fun A _ => Matrix.mulVec_zero _
  smul_mem' := fun c v hv A hA => by rw [Matrix.mulVec_smul, hv A hA]

theorem card_mul_card_fixV_lt_of_nonlinear {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    {E : Subgroup (MulAut (StdMod (Fin 3) K))} (hEN : E ≤ natNorm (StatedSL 3 K))
    (hE : IsElemAbelian2 E) (hnl : ¬ E ≤ linSub) :
    Nat.card E * Nat.card ↥(fixV E) < Nat.card K ^ 3 := by
  classical
  have hΓ : HasScalarCommutant (StatedSL 3 K) := hasScalarCommutant_statedSL (by norm_num)
  obtain ⟨g, hgE, hgl⟩ : ∃ g ∈ E, g ∉ linSub := by
    by_contra h
    push Not at h
    exact hnl fun x hx => h x hx
  let gN : ↥(natNorm (StatedSL 3 K)) := ⟨g, hEN hgE⟩
  set σ : K ≃+* K := fieldAut hΓ gN with hσdef
  have hgσ : IsSemilinear g σ := isSemilinear_fieldAut hΓ gN
  have hσ : σ ≠ RingEquiv.refl K := by
    intro h
    exact hgl ((fieldHom_eq_one_iff hΓ gN).1 h)
  have hg2 : g * g = 1 := by rw [← pow_two]; exact hE.2 g hgE
  have hq2 : 1 < Nat.card {s : K // σ s = s} := B69.ffOne_lt_card_fix σ
  have hq4 : 4 ≤ Nat.card K := le_trans (by nlinarith) (B69.ffCard_fix_sq_le hσ)
  have hE₀ := card_le_two_mul_card_inf_linSub hΓ hn hK hEN hE.2
  rw [← card_linMat] at hE₀
  have hD := card_le_of_comm_semilinear (linMat E) (linMat_sq hE) (linMat_comm hE) hgσ hσ
    (fun A hA v => by
      have := congrArg (fun h => toAddMap h v) (hE.1 _ hgE _ (matAut_mem_of_mem_linMat hA))
      simpa only [toAddMap_mul, toAddMap_matAut] using this)
  set X := linFix E with hXdef
  have hXinv : ∀ v ∈ X, toAddMap g v ∈ X := by
    intro v hv A hA
    have := congrArg (fun h => toAddMap h v) (hE.1 _ hgE _ (matAut_mem_of_mem_linMat hA))
    simp only [toAddMap_mul, toAddMap_matAut] at this
    rw [← this, hv A hA]
  have hC : Nat.card ↥(fixV E) ≤ Nat.card {v : Fin 3 → K // v ∈ X ∧ toAddMap g v = v} := by
    refine Nat.card_le_card_of_injective
      (fun x => ⟨Multiplicative.toAdd (x : StdMod (Fin 3) K), fun A hA => ?_, ?_⟩) ?_
    · have h1 := x.2 _ (matAut_mem_of_mem_linMat hA)
      have h2 := congrArg Multiplicative.toAdd h1
      rwa [← ofAdd_toAdd (x : StdMod (Fin 3) K)] at h2
    · have h1 := x.2 g hgE
      show Multiplicative.toAdd (g (Multiplicative.ofAdd (Multiplicative.toAdd
        (x : StdMod (Fin 3) K)))) = _
      rw [ofAdd_toAdd, h1]
    · intro x y h
      have h1 : Multiplicative.toAdd (x : StdMod (Fin 3) K) =
          Multiplicative.toAdd (y : StdMod (Fin 3) K) :=
        congrArg (fun p : {v : Fin 3 → K // v ∈ X ∧ toAddMap g v = v} => p.1) h
      exact Subtype.ext (Multiplicative.toAdd.injective h1)
  have hsq := FFC.Sp4Off.card_fix_sq hgσ hσ hg2 X hXinv
  have hX3 : Nat.card X ≤ Nat.card K ^ 3 := by
    have h1 : Nat.card X ≤ Nat.card (Fin 3 → K) :=
      Nat.card_le_card_of_injective (fun x : X => (x : Fin 3 → K)) Subtype.val_injective
    rwa [Nat.card_fun, Nat.card_fin] at h1
  rw [← Nat.pow_lt_pow_iff_left (by norm_num : (2 : ℕ) ≠ 0), mul_pow, ← pow_mul]
  have hCsq : Nat.card ↥(fixV E) ^ 2 ≤ Nat.card X := hsq ▸ Nat.pow_le_pow_left hC 2
  by_cases hD1 : Nat.card (linMat E) = 1
  · have h1 : Nat.card E ≤ 2 := by omega
    have h2 : Nat.card E ^ 2 ≤ 4 := by nlinarith
    have h3 : 4 * Nat.card K ^ 3 < Nat.card K ^ (3 * 2) := by
      have h64 : 64 ≤ Nat.card K ^ 3 := by
        calc 64 = 4 ^ 3 := by norm_num
          _ ≤ Nat.card K ^ 3 := Nat.pow_le_pow_left hq4 3
      rw [show 3 * 2 = 3 + 3 by norm_num, pow_add]
      exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
    calc Nat.card E ^ 2 * Nat.card ↥(fixV E) ^ 2 ≤ 4 * Nat.card X := Nat.mul_le_mul h2 hCsq
      _ ≤ 4 * Nat.card K ^ 3 := Nat.mul_le_mul_left 4 hX3
      _ < Nat.card K ^ (3 * 2) := h3
  ·
    have hD2 : 1 < Nat.card (linMat E) := by
      have := Nat.card_pos (α := linMat E)
      omega
    obtain ⟨A, hA1⟩ := exists_ne_one_of_one_lt_card hD2
    have hXtop : X ≠ ⊤ := by
      intro htop
      apply hA1
      apply Subtype.ext
      apply Units.ext
      refine Matrix.ext_iff_mulVec.mpr fun v => ?_
      have hv : v ∈ X := htop ▸ Submodule.mem_top
      rw [hv A A.2]
      exact (Matrix.one_mulVec v).symm
    have hrk : Module.finrank K X ≤ 2 := by
      have := Submodule.finrank_lt hXtop
      rw [Module.finrank_fin_fun] at this
      omega
    have hX2 : Nat.card X ≤ Nat.card K ^ 2 := by
      rw [Module.natCard_eq_pow_finrank (K := K) (V := X)]
      exact Nat.pow_le_pow_right Nat.card_pos hrk
    have h1 : Nat.card E ≤ 2 * Nat.card K := by omega
    have h2 : Nat.card E ^ 2 ≤ 4 * Nat.card K ^ 2 := by
      calc Nat.card E ^ 2 ≤ (2 * Nat.card K) ^ 2 := Nat.pow_le_pow_left h1 2
        _ = 4 * Nat.card K ^ 2 := by ring
    have h3 : 4 * Nat.card K ^ 2 * Nat.card K ^ 2 < Nat.card K ^ (3 * 2) := by
      have h16 : 16 ≤ Nat.card K ^ 2 := by nlinarith
      have : Nat.card K ^ (3 * 2) = Nat.card K ^ 2 * Nat.card K ^ 2 * Nat.card K ^ 2 := by ring
      rw [this]
      have hpos : 0 < Nat.card K ^ 2 * Nat.card K ^ 2 := by positivity
      nlinarith
    calc Nat.card E ^ 2 * Nat.card ↥(fixV E) ^ 2 ≤ 4 * Nat.card K ^ 2 * Nat.card X :=
          Nat.mul_le_mul h2 hCsq
      _ ≤ 4 * Nat.card K ^ 2 * Nat.card K ^ 2 := Nat.mul_le_mul_left _ hX2
      _ < Nat.card K ^ (3 * 2) := h3

theorem le_natImage_of_offender {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    {E : Subgroup (MulAut (StdMod (Fin 3) K))} (hEN : E ≤ natNorm (StatedSL 3 K))
    (hE : IsElemAbelian2 E)
    (hoff : Nat.card (StdMod (Fin 3) K) ≤ Nat.card E * Nat.card ↥(fixV E)) :
    E ≤ natImage (StatedSL 3 K) := by
  have hlin : E ≤ linSub := by
    by_contra hnl
    have h := card_mul_card_fixV_lt_of_nonlinear hn hK hEN hE hnl
    have h2 : Nat.card (StdMod (Fin 3) K) = Nat.card K ^ 3 := by
      rw [card_stdMod, Fintype.card_fin]
    omega
  intro x hx
  obtain ⟨A, rfl⟩ := exists_matAut_of_mem_linSub (hlin hx)
  have hAA : A * A = 1 := by
    apply matHom_injective
    rw [map_mul, map_one]
    have := hE.2 _ hx
    rwa [pow_two] at this
  have hdet : ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    have h1 : ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det ^ 2 = 1 := by
      rw [sq, ← Matrix.det_mul, ← Units.val_mul, hAA, Units.val_one, Matrix.det_one]
    have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
    have h3 : (((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det - 1) ^ 2 = 0 := by
      linear_combination h1 + (1 - ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det) * h2
    exact sub_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 h3)
  rw [natImage_eq_map]
  exact ⟨A, Subgroup.subset_closure hdet, rfl⟩

end Normalizer

end B42SL3

end CFSG.Quasithin
