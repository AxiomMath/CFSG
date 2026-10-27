module

public import CFSG.Quasithin.Background.HSL3Pair
public import CFSG.Quasithin.Background.HConj

public section

namespace CFSG.Quasithin

namespace H

namespace SL3Pair

open CFSG.Open CFSG.Assembly.LowTwoRank Matrix
open scoped Matrix

variable {K : Type} [Field K]

@[expose] def pairHom₂ (K : Type) [Field K] :
    MulAut (StdMod (Fin 3) K) × MulAut (StdMod (Fin 3) K) →* MulAut (PairMod K) where
  toFun p := pairAut p.1 p.2
  map_one' := rfl
  map_mul' _ _ := rfl

theorem pairHom₂_apply (p : MulAut (StdMod (Fin 3) K) × MulAut (StdMod (Fin 3) K)) :
    pairHom₂ K p = pairAut p.1 p.2 := rfl

theorem pairAut_injective {a b c d : MulAut (StdMod (Fin 3) K)}
    (h : pairAut a b = pairAut c d) : a = c ∧ b = d := by
  constructor
  · refine MulEquiv.ext fun v => ?_
    have := congrArg (fun z : MulAut (PairMod K) => (z (v, 1)).1) h
    simpa using this
  · refine MulEquiv.ext fun w => ?_
    have := congrArg (fun z : MulAut (PairMod K) => (z (1, w)).2) h
    simpa using this

theorem pairHom₂_injective : Function.Injective (pairHom₂ K) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  obtain ⟨h1, h2⟩ := pairAut_injective h
  exact Prod.ext h1 h2

@[expose] noncomputable def pairSub (K : Type) [Field K] : Subgroup (MulAut (PairMod K)) :=
  (pairHom₂ K).range

theorem pairAut_mem_pairSub (a b : MulAut (StdMod (Fin 3) K)) : pairAut a b ∈ pairSub K :=
  ⟨(a, b), rfl⟩

theorem mem_pairSub_iff {x : MulAut (PairMod K)} :
    x ∈ pairSub K ↔ ∃ a b : MulAut (StdMod (Fin 3) K), x = pairAut a b := by
  constructor
  · rintro ⟨⟨a, b⟩, rfl⟩
    exact ⟨a, b, rfl⟩
  · rintro ⟨a, b, rfl⟩
    exact pairAut_mem_pairSub a b

@[expose] noncomputable def pairEquiv (K : Type) [Field K] :
    (MulAut (StdMod (Fin 3) K) × MulAut (StdMod (Fin 3) K)) ≃* ↥(pairSub K) :=
  MonoidHom.ofInjective pairHom₂_injective

@[expose] noncomputable def fstHom (K : Type) [Field K] :
    ↥(pairSub K) →* MulAut (StdMod (Fin 3) K) :=
  (MonoidHom.fst _ _).comp (pairEquiv K).symm.toMonoidHom

@[expose] noncomputable def sndHom (K : Type) [Field K] :
    ↥(pairSub K) →* MulAut (StdMod (Fin 3) K) :=
  (MonoidHom.snd _ _).comp (pairEquiv K).symm.toMonoidHom

theorem pairEquiv_symm_pairAut (a b : MulAut (StdMod (Fin 3) K)) :
    (pairEquiv K).symm ⟨pairAut a b, pairAut_mem_pairSub a b⟩ = (a, b) := by
  rw [MulEquiv.symm_apply_eq]
  apply Subtype.ext
  rfl

theorem fstHom_pairAut (a b : MulAut (StdMod (Fin 3) K)) :
    fstHom K ⟨pairAut a b, pairAut_mem_pairSub a b⟩ = a := by
  change ((pairEquiv K).symm ⟨pairAut a b, _⟩).1 = a
  rw [pairEquiv_symm_pairAut]

theorem sndHom_pairAut (a b : MulAut (StdMod (Fin 3) K)) :
    sndHom K ⟨pairAut a b, pairAut_mem_pairSub a b⟩ = b := by
  change ((pairEquiv K).symm ⟨pairAut a b, _⟩).2 = b
  rw [pairEquiv_symm_pairAut]

theorem eq_pairAut (x : ↥(pairSub K)) :
    (x : MulAut (PairMod K)) = pairAut (fstHom K x) (sndHom K x) := by
  obtain ⟨_, ⟨a, b⟩, rfl⟩ := x
  change pairAut a b = pairAut (fstHom K ⟨pairAut a b, pairAut_mem_pairSub a b⟩)
    (sndHom K ⟨pairAut a b, pairAut_mem_pairSub a b⟩)
  rw [fstHom_pairAut, sndHom_pairAut]

abbrev pairNorm (K : Type) [Field K] : Subgroup (MulAut (PairMod K)) :=
  Subgroup.normalizer (pairSL K : Set (MulAut (PairMod K)))

theorem pairHom_mem_pairSL {γ : GL (Fin 3) K} (hγ : γ ∈ StatedSL 3 K) : pairHom γ ∈ pairSL K :=
  ⟨γ, hγ, rfl⟩

theorem pairSL_le_pairNorm : pairSL K ≤ pairNorm K := Subgroup.le_normalizer

theorem exists_conj_of_mem_pairNorm {x : MulAut (PairMod K)} (hx : x ∈ pairNorm K)
    {γ : GL (Fin 3) K} (hγ : γ ∈ StatedSL 3 K) :
    ∃ δ ∈ StatedSL 3 K, x * pairHom γ * x⁻¹ = pairHom δ := by
  obtain ⟨δ, hδ, h⟩ := (Subgroup.mem_normalizer_iff.mp hx (pairHom γ)).mp (pairHom_mem_pairSL hγ)
  exact ⟨δ, hδ, h.symm⟩

theorem mem_pairNorm_of {x : MulAut (PairMod K)}
    (h₁ : ∀ γ ∈ StatedSL 3 K, ∃ δ ∈ StatedSL 3 K, x * pairHom γ * x⁻¹ = pairHom δ)
    (h₂ : ∀ γ ∈ StatedSL 3 K, ∃ δ ∈ StatedSL 3 K, x⁻¹ * pairHom γ * x = pairHom δ) :
    x ∈ pairNorm K := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    obtain ⟨δ, hδ, h⟩ := h₁ γ hγ
    exact ⟨δ, hδ, h.symm⟩
  · rintro ⟨δ, hδ, hδy⟩
    obtain ⟨γ, hγ, h⟩ := h₂ δ hδ
    refine ⟨γ, hγ, ?_⟩
    change pairHom γ = y
    rw [← h, hδy]
    group

theorem map_V₁_pairAut (a b : MulAut (StdMod (Fin 3) K)) :
    (V₁ K).map (pairAut a b).toMonoidHom = V₁ K := by
  apply le_antisymm
  · rintro _ ⟨v, hv, rfl⟩
    have hv' : v.2 = 1 := mem_V₁.mp hv
    rw [mem_V₁]
    change b v.2 = 1
    rw [hv', map_one]
  · intro v hv
    have hv' : v.2 = 1 := mem_V₁.mp hv
    refine ⟨(pairAut a b)⁻¹ v, ?_, ?_⟩
    · show (pairAut a b)⁻¹ v ∈ V₁ K
      rw [mem_V₁]
      change b⁻¹ v.2 = 1
      rw [hv', map_one]
    · change pairAut a b ((pairAut a b)⁻¹ v) = v
      exact MulEquiv.apply_symm_apply _ v

theorem fstHom_mem_natNorm [Finite K] {x : ↥(pairSub K)}
    (hx : (x : MulAut (PairMod K)) ∈ pairNorm K) :
    fstHom K x ∈ natNorm (StatedSL 3 K) ∧ sndHom K x ∈ natNorm (StatedSL 3 K) := by
  have h1 : (V₁ K).map (x : MulAut (PairMod K)).toMonoidHom = V₁ K := by
    rw [eq_pairAut x]
    exact map_V₁_pairAut _ _
  obtain ⟨x₁, x₂, hxe, h₁, h₂⟩ := exists_pairAut hx h1
  rw [eq_pairAut x] at hxe
  obtain ⟨e1, e2⟩ := pairAut_injective hxe
  exact ⟨e1 ▸ h₁, e2 ▸ h₂⟩

theorem dualGL_conj (A B : GL (Fin 3) K) :
    dualGL (A * B * A⁻¹) = dualGL A * dualGL B * (dualGL A)⁻¹ := by
  simp only [← dualHom_apply, map_mul, map_inv]

theorem rel_linear {A : GL (Fin 3) K} {x₂ : MulAut (StdMod (Fin 3) K)}
    (hx : pairAut (matAut A) x₂ ∈ pairNorm K) :
    ∃ μ : K, ∀ w, toAddMap x₂ w = μ • ((dualGL A : Matrix (Fin 3) (Fin 3) K) *ᵥ w) := by
  set y := (matAut (dualGL A))⁻¹ * x₂ with hy
  have hcomm : ∀ γ ∈ StatedSL 3 K, ∀ v, toAddMap y ((γ : Matrix (Fin 3) (Fin 3) K) *ᵥ v) =
      (γ : Matrix (Fin 3) (Fin 3) K) *ᵥ toAddMap y v := by
    intro γ hγ v
    obtain ⟨δ, -, h⟩ := exists_conj_of_mem_pairNorm hx (dualGL_mem hγ)
    rw [pairHom_apply, pairHom_apply, pairAut_inv, pairAut_mul, pairAut_mul,
      dualGL_dualGL] at h
    obtain ⟨h1, h2⟩ := pairAut_injective h
    have hδ : δ = A * dualGL γ * A⁻¹ := by
      apply matHom_injective
      rw [matHom_apply, ← h1]
      show matHom A * matHom (dualGL γ) * (matHom A)⁻¹ = matHom (A * dualGL γ * A⁻¹)
      rw [map_mul, map_mul, map_inv]
    have h3 : x₂ * matAut γ * x₂⁻¹ =
        matAut (dualGL A) * matAut γ * (matAut (dualGL A))⁻¹ := by
      rw [h2, hδ, dualGL_conj, dualGL_dualGL]
      show matHom (dualGL A * γ * (dualGL A)⁻¹) =
        matHom (dualGL A) * matHom γ * (matHom (dualGL A))⁻¹
      rw [map_mul, map_mul, map_inv]
    have h4 : y * matAut γ = matAut γ * y := by
      rw [hy]
      have : x₂ * matAut γ = matAut (dualGL A) * matAut γ * (matAut (dualGL A))⁻¹ * x₂ := by
        rw [← h3]
        group
      rw [mul_assoc, this]
      group
    have := congrArg (fun z => toAddMap z v) h4
    simpa only [toAddMap_mul, toAddMap_matAut] using this
  let f : (Fin 3 → K) →+ (Fin 3 → K) :=
    AddMonoidHom.mk' (toAddMap y) (toAddMap_add y)
  obtain ⟨μ, hμ⟩ := hasScalarCommutant_statedSL (K := K) (by norm_num : 2 ≤ 3) f hcomm
  refine ⟨μ, fun w => ?_⟩
  have hx₂ : x₂ = matAut (dualGL A) * y := by rw [hy]; group
  rw [hx₂, toAddMap_mul, toAddMap_matAut]
  change (dualGL A : Matrix (Fin 3) (Fin 3) K) *ᵥ f w = _
  rw [hμ, Matrix.mulVec_smul]

@[expose] def fieldPair (σ : K ≃+* K) : MulAut (PairMod K) :=
  pairAut (fieldMap σ) (fieldMap σ)

@[expose] noncomputable def mapGL (σ : K ≃+* K) (γ : GL (Fin 3) K) : GL (Fin 3) K :=
  Matrix.GeneralLinearGroup.map (σ : K →+* K) γ

theorem coe_mapGL (σ : K ≃+* K) (γ : GL (Fin 3) K) :
    ((mapGL σ γ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (γ : Matrix (Fin 3) (Fin 3) K).map σ :=
  Matrix.GeneralLinearGroup.val_map_apply _ _

theorem mapGL_mem (σ : K ≃+* K) {γ : GL (Fin 3) K} (hγ : γ ∈ StatedSL 3 K) :
    mapGL σ γ ∈ StatedSL 3 K := by
  rw [mem_statedSL_iff] at hγ ⊢
  rw [coe_mapGL]
  have := RingHom.map_det (σ : K →+* K) (γ : Matrix (Fin 3) (Fin 3) K)
  rw [hγ, map_one] at this
  exact this.symm

theorem fieldMap_conj_matAut (σ : K ≃+* K) (γ : GL (Fin 3) K) :
    fieldMap σ * matAut γ * (fieldMap σ)⁻¹ = matAut (mapGL σ γ) :=
  toAddMap_injective fun v => by
    rw [toAddMap_fieldMap_conj, toAddMap_matAut, coe_mapGL]

theorem dualGL_mapGL (σ : K ≃+* K) (γ : GL (Fin 3) K) :
    dualGL (mapGL σ γ) = mapGL σ (dualGL γ) := by
  apply Units.ext
  rw [coe_dualGL, coe_mapGL, coe_dualGL, mapGL, ← map_inv, ← mapGL, coe_mapGL,
    Matrix.transpose_map]

theorem fieldPair_conj (σ : K ≃+* K) (γ : GL (Fin 3) K) :
    fieldPair σ * pairHom γ * (fieldPair σ)⁻¹ = pairHom (mapGL σ γ) := by
  rw [fieldPair, pairHom_apply, pairHom_apply, pairAut_inv, pairAut_mul, pairAut_mul,
    fieldMap_conj_matAut, fieldMap_conj_matAut, dualGL_mapGL]

theorem fieldPair_inv (σ : K ≃+* K) : (fieldPair σ)⁻¹ = fieldPair σ.symm := by
  rw [fieldPair, fieldPair, pairAut_inv, fieldMap_symm]

theorem fieldPair_mem_pairNorm (σ : K ≃+* K) : fieldPair σ ∈ pairNorm K := by
  refine mem_pairNorm_of (fun γ hγ => ⟨mapGL σ γ, mapGL_mem σ hγ, fieldPair_conj σ γ⟩)
    (fun γ hγ => ⟨mapGL σ.symm γ, mapGL_mem σ.symm hγ, ?_⟩)
  have h := fieldPair_conj σ.symm γ
  rw [← fieldPair_inv, inv_inv] at h
  exact h

theorem rel_semilinear {x₁ x₂ : MulAut (StdMod (Fin 3) K)} (hx : pairAut x₁ x₂ ∈ pairNorm K)
    {σ : K ≃+* K} (hσ : IsSemilinear x₁ σ) : IsSemilinear x₂ σ := by
  have h1 : IsSemilinear (x₁ * (fieldMap σ)⁻¹) (RingEquiv.refl K) := by
    have := hσ.mul (isSemilinear_fieldMap (ι := Fin 3) σ).inv
    have e : σ.symm.trans σ = RingEquiv.refl K := by
      ext c
      simp
    rwa [e] at this
  obtain ⟨A, hA⟩ := exists_matAut_of_mem_linSub (show x₁ * (fieldMap σ)⁻¹ ∈ linSub from h1)
  have hmem : pairAut (matAut A) (x₂ * (fieldMap σ)⁻¹) ∈ pairNorm K := by
    have : pairAut (matAut A) (x₂ * (fieldMap σ)⁻¹) = pairAut x₁ x₂ * (fieldPair σ)⁻¹ := by
      rw [fieldPair, pairAut_inv, pairAut_mul, hA]
    rw [this]
    exact Subgroup.mul_mem _ hx (Subgroup.inv_mem _ (fieldPair_mem_pairNorm σ))
  obtain ⟨μ, hμ⟩ := rel_linear hmem
  have key : ∀ u, toAddMap x₂ u =
      μ • ((dualGL A : Matrix (Fin 3) (Fin 3) K) *ᵥ toAddMap (fieldMap σ) u) := by
    intro u
    have := hμ (toAddMap (fieldMap σ) u)
    rwa [toAddMap_mul, toAddMap_apply_inv] at this
  intro c w
  rw [key, key, (isSemilinear_fieldMap (ι := Fin 3) σ) c w, Matrix.mulVec_smul, smul_comm]

@[expose] def swapAut (K : Type) [Field K] : MulAut (PairMod K) := MulEquiv.prodComm

@[simp] theorem swapAut_apply (x : PairMod K) : swapAut K x = (x.2, x.1) := rfl

theorem swapAut_mul_self : swapAut K * swapAut K = 1 := MulEquiv.ext fun _ => rfl

theorem swapAut_inv : (swapAut K)⁻¹ = swapAut K := MulEquiv.ext fun _ => rfl

theorem swapAut_mul_pairAut (a b : MulAut (StdMod (Fin 3) K)) :
    swapAut K * pairAut a b = pairAut b a * swapAut K := MulEquiv.ext fun _ => rfl

theorem swapAut_conj (γ : GL (Fin 3) K) :
    swapAut K * pairHom γ * (swapAut K)⁻¹ = pairHom (dualGL γ) := by
  rw [swapAut_inv, pairHom_apply, pairHom_apply, swapAut_mul_pairAut, mul_assoc,
    swapAut_mul_self, mul_one, dualGL_dualGL]

theorem swapAut_mem_pairNorm : swapAut K ∈ pairNorm K :=
  mem_pairNorm_of (fun γ hγ => ⟨dualGL γ, dualGL_mem hγ, swapAut_conj γ⟩)
    (fun γ hγ => ⟨dualGL γ, dualGL_mem hγ, by
      have := swapAut_conj (K := K) γ
      rw [swapAut_inv] at this ⊢
      exact this⟩)

theorem map_V₂_swapAut : (V₂ K).map (swapAut K).toMonoidHom = V₁ K := by
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    have hv' : v.1 = 1 := mem_V₂.mp hv
    rw [mem_V₁]
    exact hv'
  · intro hx
    rw [mem_V₁] at hx
    exact ⟨(x.2, x.1), mem_V₂.mpr hx, rfl⟩

theorem mem_pairSub_or [Finite K] {x : MulAut (PairMod K)} (hx : x ∈ pairNorm K) :
    x ∈ pairSub K ∨ swapAut K * x ∈ pairSub K := by
  rcases map_V₁_eq_or hx with h | h
  · obtain ⟨x₁, x₂, rfl, -, -⟩ := exists_pairAut hx h
    exact Or.inl (pairAut_mem_pairSub x₁ x₂)
  · right
    have hy : swapAut K * x ∈ pairNorm K := Subgroup.mul_mem _ swapAut_mem_pairNorm hx
    have h1 : (V₁ K).map (swapAut K * x).toMonoidHom = V₁ K := by
      have e : (swapAut K * x).toMonoidHom =
          (swapAut K).toMonoidHom.comp x.toMonoidHom := rfl
      rw [e, ← Subgroup.map_map, h, map_V₂_swapAut]
    obtain ⟨x₁, x₂, he, -, -⟩ := exists_pairAut hy h1
    rw [he]
    exact pairAut_mem_pairSub x₁ x₂

theorem inv_mul_mem_pairSub [Finite K] {x x' : MulAut (PairMod K)} (hx : x ∈ pairNorm K)
    (hx' : x' ∈ pairNorm K) (h : x ∉ pairSub K) (h' : x' ∉ pairSub K) :
    x⁻¹ * x' ∈ pairSub K := by
  have h1 := (mem_pairSub_or hx).resolve_left h
  have h2 := (mem_pairSub_or hx').resolve_left h'
  have : x⁻¹ * x' = (swapAut K * x)⁻¹ * (swapAut K * x') := by
    rw [_root_.mul_inv_rev, swapAut_inv, mul_assoc, ← mul_assoc (swapAut K), swapAut_mul_self,
      one_mul]
  rw [this]
  exact Subgroup.mul_mem _ (Subgroup.inv_mem _ h1) h2

end SL3Pair

end H

end CFSG.Quasithin
