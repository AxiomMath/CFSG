module

public import CFSG.Quasithin.Background.FixVZPowersMem
public import CFSG.Quasithin.Background.SmithD37Core

public section

namespace CFSG.Quasithin.SmithD37

open Matrix

variable {U : Type} [CommGroup U] {L₁ L₂ : Subgroup (MulAut U)} {F : Type} [Field F] {d : ℕ}

private theorem sum_vecMulVec_col (X : Matrix (Fin d) (Fin d) F) :
    ∑ i, vecMulVec (fun m => X m i) (Pi.single i 1) = X := by
  ext m n
  simp [Matrix.sum_apply, vecMulVec_apply, Pi.single_apply]

theorem exists_smul_of_comm (Mm : MatModel L₁ L₂ F d)
    (S : Matrix (Fin d) (Fin d) F →+ Matrix (Fin d) (Fin d) F)
    (h₁ : ∀ (l : ↥L₁) X, S ((Mm.R₁ l : Matrix (Fin d) (Fin d) F) * X) =
      (Mm.R₁ l : Matrix (Fin d) (Fin d) F) * S X)
    (h₂ : ∀ (k : ↥L₂) X, S (X * (Mm.R₂ k : Matrix (Fin d) (Fin d) F)ᵀ) =
      S X * (Mm.R₂ k : Matrix (Fin d) (Fin d) F)ᵀ) :
    ∃ c : F, ∀ X, S X = c • X := by
  classical
  have hcol : ∀ i j : Fin d, ∃ c : F, ∀ v : Fin d → F,
      (fun m => S (vecMulVec v (Pi.single i 1)) m j) = c • v := by
    intro i j
    let φ : (Fin d → F) →+ (Fin d → F) :=
      { toFun := fun v m => S (vecMulVec v (Pi.single i 1)) m j
        map_zero' := by ext m; simp
        map_add' := by intro v w; ext m; simp [add_vecMulVec] }
    refine Mm.end₁ φ fun l v => ?_
    ext m
    show S (vecMulVec (_ *ᵥ v) _) m j = _
    rw [← mul_vecMulVec, h₁]
    simp [φ, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  choose c hc using hcol
  set C : Matrix (Fin d) (Fin d) F := Matrix.of c with hC
  have hS : ∀ X, S X = X * C := by
    intro X
    ext m j
    conv_lhs => rw [← sum_vecMulVec_col X]
    rw [map_sum, Matrix.sum_apply]
    have h := fun i => congrFun (hc i j (fun m => X m i)) m
    simp only [Pi.smul_apply, smul_eq_mul] at h
    simp only [h, Matrix.mul_apply, hC, Matrix.of_apply, mul_comm]
  have hcomm : ∀ k : ↥L₂, Cᵀ * (Mm.R₂ k : Matrix (Fin d) (Fin d) F) =
      (Mm.R₂ k : Matrix (Fin d) (Fin d) F) * Cᵀ := by
    intro k
    have h := h₂ k 1
    rw [hS, hS, Matrix.one_mul, Matrix.one_mul] at h
    simpa [Matrix.transpose_mul] using congrArg Matrix.transpose h
  obtain ⟨c₀, hc₀⟩ := Mm.end₂ (Cᵀ).mulVecLin.toAddMonoidHom fun k v => by
    show Cᵀ *ᵥ (_ *ᵥ v) = _ *ᵥ (Cᵀ *ᵥ v)
    rw [Matrix.mulVec_mulVec, hcomm, ← Matrix.mulVec_mulVec]
  have hCt : Cᵀ = c₀ • (1 : Matrix (Fin d) (Fin d) F) := by
    refine Matrix.ext_of_mulVec_single fun i => ?_
    have h := hc₀ (Pi.single i 1)
    simp only [LinearMap.toAddMonoidHom_coe, Matrix.mulVecLin_apply] at h
    rw [h, Matrix.smul_mulVec, Matrix.one_mulVec]
  refine ⟨c₀, fun X => ?_⟩
  have hC' : C = c₀ • (1 : Matrix (Fin d) (Fin d) F) := by
    rw [← Matrix.transpose_transpose C, hCt]
    simp
  rw [hS, hC', Matrix.mul_smul, Matrix.mul_one]

omit [Field F] in
private theorem natCard_matrix [Fintype F] :
    Nat.card (Matrix (Fin d) (Fin d) F) = Nat.card F ^ (d * d) := by
  rw [show Nat.card (Matrix (Fin d) (Fin d) F) = Nat.card (Fin d → Fin d → F) from rfl,
    Nat.card_fun, Nat.card_fun, Nat.card_fin, ← pow_mul]

private theorem natCard_le_pairs : Nat.card {p : Fin d × Fin d // p.1 ≤ p.2} = (d + 1) * d / 2 := by
  rw [← Nat.card_congr Sym2.sortEquiv, Sym2.natCard, Nat.card_fin, Nat.choose_two_right,
    Nat.add_sub_cancel]

theorem natCard_transpose_eq_smul_le [Fintype F] (c : F) :
    Nat.card {Z : Matrix (Fin d) (Fin d) F // Zᵀ = c • Z} ≤ Nat.card F ^ ((d + 1) * d / 2) := by
  let f : {Z : Matrix (Fin d) (Fin d) F // Zᵀ = c • Z} → {p : Fin d × Fin d // p.1 ≤ p.2} → F :=
    fun Z p => Z.1 p.1.1 p.1.2
  have hf : Function.Injective f := by
    rintro ⟨Z, hZ⟩ ⟨Z', hZ'⟩ h
    have h' : ∀ i j, i ≤ j → Z i j = Z' i j := fun i j hij => congrFun h ⟨(i, j), hij⟩
    refine Subtype.ext (Matrix.ext fun i j => ?_)
    rcases le_total i j with hij | hji
    · exact h' i j hij
    · show Z i j = Z' i j
      have h1 := congrFun (congrFun hZ j) i
      have h2 := congrFun (congrFun hZ' j) i
      simp only [Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul] at h1 h2
      rw [h1, h2, h' j i hji]
  have h := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_fun, natCard_le_pairs] at h

theorem natCard_fix_sq_le_of_semilinear [Fintype F]
    (T : Matrix (Fin d) (Fin d) F →+ Matrix (Fin d) (Fin d) F) {c c' : F} (hcc : c ≠ c')
    (h : ∀ X, T (c • X) = c' • T X) :
    Nat.card {X // T X = X} ^ 2 ≤ Nat.card F ^ (d * d) := by
  let f : {X // T X = X} × {X // T X = X} → Matrix (Fin d) (Fin d) F :=
    fun p => p.1.1 + c • p.2.1
  have hf : Function.Injective f := by
    rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ ⟨⟨x', hx'⟩, ⟨y', hy'⟩⟩ hxy
    have h1 : x + c • y = x' + c • y' := hxy
    have h2 : x - x' = c • (y' - y) := by
      rw [smul_sub, sub_eq_sub_iff_add_eq_add, add_comm (c • y') x']
      exact h1
    have h3 : c • (y' - y) = c' • (y' - y) := by
      have e1 : T (x - x') = x - x' := by rw [map_sub, hx, hx']
      have e2 : T (y' - y) = y' - y := by rw [map_sub, hy, hy']
      rw [← h2, ← e1, h2, h, e2]
    have h4 : y' - y = 0 := by
      have h5 : (c - c') • (y' - y) = 0 := by rw [sub_smul, h3, sub_self]
      exact (smul_eq_zero.mp h5).resolve_left (sub_ne_zero.mpr hcc)
    have h6 : y = y' := (sub_eq_zero.mp h4).symm
    subst h6
    have h7 : x = x' := by simpa using h1
    subst h7
    rfl
  have hle := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_prod, ← sq, natCard_matrix] at hle

structure SwapInv (Mm : MatModel L₁ L₂ F d)
    (T : Matrix (Fin d) (Fin d) F →+ Matrix (Fin d) (Fin d) F) where
  φ : ↥L₁ → ↥L₂
  ψ : ↥L₂ → ↥L₁
  invol : ∀ X, T (T X) = X
  ψφ : ∀ l, ψ (φ l) = l
  φψ : ∀ k, φ (ψ k) = k
  left : ∀ (l : ↥L₁) X, T ((Mm.R₁ l : Matrix (Fin d) (Fin d) F) * X) =
    T X * (Mm.R₂ (φ l) : Matrix (Fin d) (Fin d) F)ᵀ
  right : ∀ (k : ↥L₂) X, T (X * (Mm.R₂ k : Matrix (Fin d) (Fin d) F)ᵀ) =
    (Mm.R₁ (ψ k) : Matrix (Fin d) (Fin d) F) * T X

namespace SwapInv

variable {Mm : MatModel L₁ L₂ F d} {T : Matrix (Fin d) (Fin d) F →+ Matrix (Fin d) (Fin d) F}

theorem exists_semilinear (H : SwapInv Mm T) (c : F) :
    ∃ c' : F, ∀ X, T (c • X) = c' • T X := by
  let S : Matrix (Fin d) (Fin d) F →+ Matrix (Fin d) (Fin d) F :=
    { toFun := fun X => T (c • T X)
      map_zero' := by simp
      map_add' := fun X Y => by simp [smul_add] }
  obtain ⟨c', hc'⟩ := exists_smul_of_comm Mm S
    (fun l X => by
      show T (c • T (_ * X)) = _ * T (c • T X)
      rw [H.left, ← Matrix.smul_mul, H.right, H.ψφ])
    (fun k X => by
      show T (c • T (X * _)) = T (c • T X) * _
      rw [H.right, ← Matrix.mul_smul, H.left, H.φψ])
  refine ⟨c', fun X => ?_⟩
  have h := hc' (T X)
  rwa [show S (T X) = T (c • X) by show T (c • T (T X)) = _; rw [H.invol]] at h

theorem exists_intertwiner (H : SwapInv Mm T) (hd : 0 < d)
    (hlin : ∀ (c : F) X, T (c • X) = c • T X) :
    ∃ g : (Fin d → F) →ₗ[F] (Fin d → F), Function.Injective g ∧
      ∀ (l : ↥L₁) v, g ((Mm.R₁ l : Matrix (Fin d) (Fin d) F) *ᵥ v) =
        (Mm.R₂ (H.φ l) : Matrix (Fin d) (Fin d) F) *ᵥ g v := by
  classical
  set e : Fin d → F := Pi.single ⟨0, hd⟩ 1 with he
  have hE : T (vecMulVec e e) ≠ 0 := by
    intro h0
    have h1 := H.invol (vecMulVec e e)
    rw [h0, map_zero] at h1
    have h2 := congrFun (congrFun h1 ⟨0, hd⟩) ⟨0, hd⟩
    simp [e, vecMulVec_apply] at h2
  obtain ⟨j, m₀, hjm⟩ : ∃ j m, T (vecMulVec e e) j m ≠ 0 := by
    by_contra hcon
    refine hE (Matrix.ext fun j m => ?_)
    by_contra h
    exact hcon ⟨j, m, h⟩
  let g : (Fin d → F) →ₗ[F] (Fin d → F) :=
    { toFun := fun v m => T (vecMulVec v e) j m
      map_add' := fun v w => by ext m; simp [add_vecMulVec]
      map_smul' := fun c v => by ext m; simp [smul_vecMulVec, hlin] }
  have hg : ∀ (l : ↥L₁) v, g ((Mm.R₁ l : Matrix (Fin d) (Fin d) F) *ᵥ v) =
      (Mm.R₂ (H.φ l) : Matrix (Fin d) (Fin d) F) *ᵥ g v := by
    intro l v
    ext m
    show T (vecMulVec (_ *ᵥ v) e) j m = _
    rw [← mul_vecMulVec, H.left]
    simp [g, Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]
  refine ⟨g, ?_, hg⟩
  rw [injective_iff_map_eq_zero]
  intro v hv
  let K : AddSubgroup (Fin d → F) := (LinearMap.ker g).toAddSubgroup
  have hK : ∀ (l : ↥L₁), ∀ w ∈ K, (Mm.R₁ l : Matrix (Fin d) (Fin d) F) *ᵥ w ∈ K := by
    intro l w hw
    have hw' : g w = 0 := hw
    show g _ = 0
    rw [hg, hw', Matrix.mulVec_zero]
  rcases Mm.irr₁ K hK with hb | ht
  · have hvK : v ∈ K := hv
    rw [hb] at hvK
    exact hvK
  · exfalso
    have heK : e ∈ K := by rw [ht]; trivial
    have h0 : g e = 0 := heK
    exact hjm (congrFun h0 m₀)

theorem natCard_fix_le_of_linear [Fintype F] (H : SwapInv Mm T) (hd : 0 < d)
    (hlin : ∀ (c : F) X, T (c • X) = c • T X) :
    Nat.card {X // T X = X} ≤ Nat.card F ^ ((d + 1) * d / 2) := by
  classical
  obtain ⟨g, hginj, hg⟩ := H.exists_intertwiner hd hlin
  set A : Matrix (Fin d) (Fin d) F := LinearMap.toMatrix' g with hAdef
  have hA : ∀ v, A *ᵥ v = g v := LinearMap.toMatrix'_mulVec g
  have hAu : IsUnit A := by
    rw [← Matrix.mulVec_injective_iff_isUnit]
    intro v w hvw
    exact hginj (by rw [← hA, ← hA]; exact hvw)
  have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hAu
  have hAR : ∀ l : ↥L₁, A * (Mm.R₁ l : Matrix (Fin d) (Fin d) F) =
      (Mm.R₂ (H.φ l) : Matrix (Fin d) (Fin d) F) * A := by
    intro l
    refine Matrix.ext_of_mulVec_single fun i => ?_
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hA, hA, hg]
  have hinv : ∀ l : ↥L₁, A⁻¹ * (Mm.R₂ (H.φ l) : Matrix (Fin d) (Fin d) F) =
      (Mm.R₁ l : Matrix (Fin d) (Fin d) F) * A⁻¹ := by
    intro l
    calc A⁻¹ * (Mm.R₂ (H.φ l) : Matrix (Fin d) (Fin d) F)
        = A⁻¹ * (Mm.R₂ (H.φ l) : Matrix (Fin d) (Fin d) F) * (A * A⁻¹) := by
          rw [Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]
      _ = A⁻¹ * ((Mm.R₂ (H.φ l) : Matrix (Fin d) (Fin d) F) * A) * A⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = A⁻¹ * (A * (Mm.R₁ l : Matrix (Fin d) (Fin d) F)) * A⁻¹ := by rw [hAR]
      _ = (Mm.R₁ l : Matrix (Fin d) (Fin d) F) * A⁻¹ := by
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul]
  let S : Matrix (Fin d) (Fin d) F →+ Matrix (Fin d) (Fin d) F :=
    { toFun := fun X => A⁻¹ * (T X)ᵀ * Aᵀ
      map_zero' := by simp
      map_add' := fun X Y => by simp [Matrix.mul_add, Matrix.add_mul] }
  obtain ⟨c, hc⟩ := exists_smul_of_comm Mm S
    (fun l X => by
      show A⁻¹ * (T (_ * X))ᵀ * Aᵀ = _ * (A⁻¹ * (T X)ᵀ * Aᵀ)
      rw [H.left, Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc, hinv]
      simp only [Matrix.mul_assoc])
    (fun k X => by
      show A⁻¹ * (T (X * _))ᵀ * Aᵀ = A⁻¹ * (T X)ᵀ * Aᵀ * _
      have h1 : A * (Mm.R₁ (H.ψ k) : Matrix (Fin d) (Fin d) F) =
          (Mm.R₂ k : Matrix (Fin d) (Fin d) F) * A := by rw [hAR, H.φψ]
      have h2 : (Mm.R₁ (H.ψ k) : Matrix (Fin d) (Fin d) F)ᵀ * Aᵀ =
          Aᵀ * (Mm.R₂ k : Matrix (Fin d) (Fin d) F)ᵀ := by
        rw [← Matrix.transpose_mul, h1, Matrix.transpose_mul]
      rw [H.right, Matrix.transpose_mul]
      simp only [Matrix.mul_assoc]
      rw [h2])
  have hfix : ∀ X, T X = X → (A * X)ᵀ = c • (A * X) := by
    intro X hX
    have h1 : A⁻¹ * Xᵀ * Aᵀ = c • X := by
      have h := hc X
      rwa [show S X = A⁻¹ * (T X)ᵀ * Aᵀ from rfl, hX] at h
    calc (A * X)ᵀ = A * (A⁻¹ * Xᵀ * Aᵀ) := by
          rw [Matrix.transpose_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
            Matrix.mul_nonsing_inv _ hdet, Matrix.one_mul]
      _ = c • (A * X) := by rw [h1, Matrix.mul_smul]
  let f : {X // T X = X} → {Z : Matrix (Fin d) (Fin d) F // Zᵀ = c • Z} :=
    fun X => ⟨A * X.1, hfix X.1 X.2⟩
  have hf : Function.Injective f := by
    rintro ⟨X, hX⟩ ⟨Y, hY⟩ h
    have h1 : A * X = A * Y := congrArg Subtype.val h
    have h2 : X = Y := by
      have h3 := congrArg (A⁻¹ * ·) h1
      simpa [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet] using h3
    exact Subtype.ext h2
  exact (Nat.card_le_card_of_injective f hf).trans (natCard_transpose_eq_smul_le c)

private theorem tri_add (d : ℕ) : d * (d - 1) / 2 + (d + 1) * d / 2 = d * d := by
  obtain ⟨k, hk⟩ := Nat.even_mul_pred_self d
  have h1 : (d + 1) * d = d * (d - 1) + 2 * d := by
    rcases d with _ | n
    · simp
    · simp only [Nat.add_sub_cancel]; ring
  have h2 : d * d = d * (d - 1) + d := by
    rcases d with _ | n
    · simp
    · simp only [Nat.add_sub_cancel]; ring
  omega

private theorem tri_le (d : ℕ) : 2 * (d * (d - 1) / 2) + d * d ≤ 2 * (d * d) := by
  have h : d * (d - 1) ≤ d * d := Nat.mul_le_mul_left _ (Nat.sub_le d 1)
  omega

theorem natCard_fix_le [Fintype F] (H : SwapInv Mm T) :
    Nat.card F ^ (d * (d - 1) / 2) * Nat.card {X // T X = X} ≤ Nat.card F ^ (d * d) := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    have h := Finite.card_subtype_le (fun X : Matrix (Fin 0) (Fin 0) F => T X = X)
    rw [natCard_matrix] at h
    simpa using h
  have hF : 0 < Nat.card F := Nat.card_pos
  by_cases hlin : ∀ (c : F) X, T (c • X) = c • T X
  · calc Nat.card F ^ (d * (d - 1) / 2) * Nat.card {X // T X = X}
        ≤ Nat.card F ^ (d * (d - 1) / 2) * Nat.card F ^ ((d + 1) * d / 2) :=
          Nat.mul_le_mul_left _ (H.natCard_fix_le_of_linear hd hlin)
      _ = Nat.card F ^ (d * d) := by rw [← pow_add, tri_add]
  · simp only [not_forall] at hlin
    obtain ⟨c, X, hX⟩ := hlin
    obtain ⟨c', hc'⟩ := H.exists_semilinear c
    have hcc : c ≠ c' := by
      rintro rfl
      exact hX (hc' X)
    have h := natCard_fix_sq_le_of_semilinear T hcc hc'
    rw [← Nat.pow_le_pow_iff_left two_ne_zero]
    calc (Nat.card F ^ (d * (d - 1) / 2) * Nat.card {X // T X = X}) ^ 2
        = Nat.card F ^ (2 * (d * (d - 1) / 2)) * Nat.card {X // T X = X} ^ 2 := by ring
      _ ≤ Nat.card F ^ (2 * (d * (d - 1) / 2)) * Nat.card F ^ (d * d) :=
          Nat.mul_le_mul_left _ h
      _ = Nat.card F ^ (2 * (d * (d - 1) / 2) + d * d) := by rw [pow_add]
      _ ≤ Nat.card F ^ (2 * (d * d)) := Nat.pow_le_pow_right hF (tri_le d)
      _ = (Nat.card F ^ (d * d)) ^ 2 := by ring

end SwapInv

def coordAut (Mm : MatModel L₁ L₂ F d) (t : MulAut U) :
    Matrix (Fin d) (Fin d) F →+ Matrix (Fin d) (Fin d) F where
  toFun X := Multiplicative.toAdd (Mm.β (t (Mm.β.symm (Multiplicative.ofAdd X))))
  map_zero' := by simp
  map_add' X Y := by simp [ofAdd_add]

theorem coordAut_β (Mm : MatModel L₁ L₂ F d) (t : MulAut U) (u : U) :
    coordAut Mm t (Multiplicative.toAdd (Mm.β u)) = Multiplicative.toAdd (Mm.β (t u)) := by
  simp [coordAut]

private theorem conj_mem (t : MulAut U) {L L' : Subgroup (MulAut U)}
    (h : L.map (MulAut.conj t).toMonoidHom = L') (l : ↥L) : t * (l : MulAut U) * t⁻¹ ∈ L' := by
  rw [← h]
  exact ⟨l, l.2, by simp [MulAut.conj_apply]⟩

def swapInvOf (Mm : MatModel L₁ L₂ F d) (t : MulAut U) (ht : t * t = 1)
    (h₁ : L₁.map (MulAut.conj t).toMonoidHom = L₂)
    (h₂ : L₂.map (MulAut.conj t).toMonoidHom = L₁) : SwapInv Mm (coordAut Mm t) where
  φ l := ⟨t * l * t⁻¹, conj_mem t h₁ l⟩
  ψ k := ⟨t * k * t⁻¹, conj_mem t h₂ k⟩
  invol X := by
    have h : ∀ u : U, t (t u) = u := fun u => by rw [← MulAut.mul_apply, ht, MulAut.one_apply]
    simp [coordAut, h]
  ψφ l := Subtype.ext <| by
    show t * (t * (l : MulAut U) * t⁻¹) * t⁻¹ = l
    rw [show t * (t * (l : MulAut U) * t⁻¹) * t⁻¹ = (t * t) * l * (t * t)⁻¹ by group, ht]
    simp
  φψ k := Subtype.ext <| by
    show t * (t * (k : MulAut U) * t⁻¹) * t⁻¹ = k
    rw [show t * (t * (k : MulAut U) * t⁻¹) * t⁻¹ = (t * t) * k * (t * t)⁻¹ by group, ht]
    simp
  left l X := by
    set u := Mm.β.symm (Multiplicative.ofAdd X) with hu
    have h1 : Mm.β.symm (Multiplicative.ofAdd ((Mm.R₁ l : Matrix (Fin d) (Fin d) F) * X)) =
        (l : MulAut U) u := by
      rw [MulEquiv.symm_apply_eq, Mm.act₁, hu, MulEquiv.apply_symm_apply, toAdd_ofAdd]
    have h2 : t ((l : MulAut U) u) =
        ((⟨t * l * t⁻¹, conj_mem t h₁ l⟩ : ↥L₂) : MulAut U) (t u) := by
      simp [MulAut.mul_apply]
    show Multiplicative.toAdd (Mm.β (t (Mm.β.symm (Multiplicative.ofAdd (_ * X))))) =
      Multiplicative.toAdd (Mm.β (t u)) * _
    rw [h1, h2, Mm.act₂]
    rfl
  right k X := by
    set u := Mm.β.symm (Multiplicative.ofAdd X) with hu
    have h1 : Mm.β.symm (Multiplicative.ofAdd (X * (Mm.R₂ k : Matrix (Fin d) (Fin d) F)ᵀ)) =
        (k : MulAut U) u := by
      rw [MulEquiv.symm_apply_eq, Mm.act₂, hu, MulEquiv.apply_symm_apply, toAdd_ofAdd]
    have h2 : t ((k : MulAut U) u) =
        ((⟨t * k * t⁻¹, conj_mem t h₂ k⟩ : ↥L₁) : MulAut U) (t u) := by
      simp [MulAut.mul_apply]
    show Multiplicative.toAdd (Mm.β (t (Mm.β.symm (Multiplicative.ofAdd (X * _))))) =
      _ * Multiplicative.toAdd (Mm.β (t u))
    rw [h1, h2, Mm.act₁]
    rfl

private theorem mem_fixV_zpowers {t : MulAut U} {u : U} :
    u ∈ fixV (Subgroup.zpowers t) ↔ t u = u :=
  CFSG.Quasithin.mem_fixV_zpowers_iff_apply

theorem natCard_fixV_zpowers_eq [Fintype F] (Mm : MatModel L₁ L₂ F d) (t : MulAut U) :
    Nat.card ↥(fixV (Subgroup.zpowers t)) = Nat.card {X // coordAut Mm t X = X} := by
  refine Nat.card_congr (Equiv.subtypeEquiv (Mm.β.toEquiv.trans Multiplicative.toAdd) ?_)
  intro u
  rw [mem_fixV_zpowers]
  show _ ↔ coordAut Mm t (Multiplicative.toAdd (Mm.β u)) = Multiplicative.toAdd (Mm.β u)
  rw [coordAut_β, Multiplicative.toAdd.injective.eq_iff, Mm.β.injective.eq_iff]

theorem card_fixV_swap_le {U : Type} [CommGroup U] [Finite U] {L₁ L₂ : Subgroup (MulAut U)}
    {F : Type} [Field F] [Fintype F] [CharP F 2] {d : ℕ} (Mm : MatModel L₁ L₂ F d)
    (t : MulAut U) (ht : t * t = 1)
    (h₁ : L₁.map (MulAut.conj t).toMonoidHom = L₂)
    (h₂ : L₂.map (MulAut.conj t).toMonoidHom = L₁) :
    Nat.card F ^ (d * (d - 1) / 2) * Nat.card ↥(fixV (Subgroup.zpowers t)) ≤ Nat.card U := by
  rw [natCard_fixV_zpowers_eq Mm t,
    Nat.card_congr (Mm.β.toEquiv.trans Multiplicative.toAdd), natCard_matrix]
  exact (swapInvOf Mm t ht h₁ h₂).natCard_fix_le

end CFSG.Quasithin.SmithD37
