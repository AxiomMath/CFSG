module

public import CFSG.RankThree.GF2n.Stroth80.Sec312Quot
public import CFSG.RankThree.GF2n.Stroth80.Sec310ClPoint

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.Open CFSG.Assembly.LowTwoRank
open scoped Matrix

private theorem orth_good_of_closure {H : Type} [Group H] {k : Set H} {Pm : H → Prop}
    (h1 : Pm 1) (hmul : ∀ x y, Pm x → Pm y → Pm (x * y))
    (hk : ∀ x ∈ k, Pm x ∧ Pm x⁻¹) {x : H} (hx : x ∈ Subgroup.closure k) :
    Pm x ∧ Pm x⁻¹ :=
  Subgroup.closure_induction (p := fun x _ => Pm x ∧ Pm x⁻¹)
    (fun x hx => hk x hx) ⟨h1, by rw [inv_one]; exact h1⟩
    (fun x y _ _ hx hy => ⟨hmul x y hx.1 hy.1, by rw [mul_inv_rev]; exact hmul _ _ hy.2 hx.2⟩)
    (fun x _ hx => ⟨hx.2, by rw [inv_inv]; exact hx.1⟩) hx

private theorem orth_toGL_tv01 {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {W : Submodule K V} (b : Module.Basis (Fin 2) K W) (f : W ≃ₗ[K] W) (c : K)
    (h0 : (f (b 0) : V) = (b 0 : V)) (h1 : (f (b 1) : V) = (b 1 : V) + c • (b 0 : V)) :
    ((b.toGL f : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = Matrix.transvection 0 1 c := by
  have e0 : f (b 0) = b 0 := Subtype.ext h0
  have e1 : f (b 1) = b 1 + c • b 0 := Subtype.ext (by simp [h1])
  ext i j
  rw [toGL_entry]
  fin_cases i <;> fin_cases j <;>
    simp [e0, e1, Module.Basis.repr_self, Matrix.transvection, Matrix.single_apply]

private theorem orth_toGL_tv10 {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {W : Submodule K V} (b : Module.Basis (Fin 2) K W) (f : W ≃ₗ[K] W) (c : K)
    (h0 : (f (b 0) : V) = (b 0 : V) + c • (b 1 : V)) (h1 : (f (b 1) : V) = (b 1 : V)) :
    ((b.toGL f : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = Matrix.transvection 1 0 c := by
  have e0 : f (b 0) = b 0 + c • b 1 := Subtype.ext (by simp [h0])
  have e1 : f (b 1) = b 1 := Subtype.ext h1
  ext i j
  rw [toGL_entry]
  fin_cases i <;> fin_cases j <;>
    simp [e0, e1, Module.Basis.repr_self, Matrix.transvection, Matrix.single_apply]

private theorem orth_exists_dual {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {e₁ e₂ : V} (hind : LinearIndependent K ![e₁, e₂]) (a₁ a₂ : K) :
    ∃ φ : Module.Dual K V, φ e₁ = a₁ ∧ φ e₂ = a₂ := by
  obtain ⟨b, hb0, hb1⟩ : ∃ b : Module.Basis (Fin 2) K (Submodule.span K (Set.range ![e₁, e₂])),
      (b 0 : V) = e₁ ∧ (b 1 : V) = e₂ :=
    ⟨Module.Basis.span hind, Module.Basis.coe_span_apply hind 0,
      Module.Basis.coe_span_apply hind 1⟩
  obtain ⟨φ, hφ⟩ := LinearMap.exists_extend (b.constr K ![a₁, a₂])
  have key : ∀ w : Submodule.span K (Set.range ![e₁, e₂]),
      φ (w : V) = b.constr K ![a₁, a₂] w := by
    intro w
    rw [← hφ]
    rfl
  refine ⟨φ, ?_, ?_⟩
  · rw [← hb0, key, Module.Basis.constr_basis]
    rfl
  · rw [← hb1, key, Module.Basis.constr_basis]
    rfl

private theorem orth_invariant {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {e₁ e₂ : V} (g : V ≃ₗ[K] V)
    (h1 : g e₁ ∈ Submodule.span K (Set.range ![e₁, e₂]))
    (h2 : g e₂ ∈ Submodule.span K (Set.range ![e₁, e₂])) :
    ∀ w ∈ Submodule.span K (Set.range ![e₁, e₂]),
      g w ∈ Submodule.span K (Set.range ![e₁, e₂]) := by
  have hle : Submodule.span K (Set.range ![e₁, e₂]) ≤
      (Submodule.span K (Set.range ![e₁, e₂])).comap (g : V →ₗ[K] V) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact h1
    · exact h2
  intro w hw
  exact hle hw

private theorem orth_pow_four {K V : Type} [Field K] [CharP K 2] [AddCommGroup V] [Module K V]
    (g : V ≃ₗ[K] V) (N : V → V) (hgN : ∀ z, g z = z + N z)
    (hNadd : ∀ a b, N (a + b) = N a + N b) (hcube : ∀ z, N (N (N z)) = 0) :
    ∀ y : V, g (g (g (g y))) = y := by
  have e1 : ∀ z, g (g z) = z + N (N z) := by
    intro z
    have h := Classify.vec_add_self K (N z)
    calc g (g z) = g (z + N z) := by rw [hgN z]
      _ = g z + g (N z) := map_add g _ _
      _ = (z + N z) + (N z + N (N z)) := by rw [hgN z, hgN (N z)]
      _ = z + (N z + N z) + N (N z) := by abel
      _ = z + N (N z) := by rw [h, add_zero]
  have e2 : ∀ z, N (N (z + N (N z))) = N (N z) := by
    intro z
    have hz : N (z + N (N z)) = N z := by rw [hNadd, hcube z, add_zero]
    rw [hz]
  intro y
  calc g (g (g (g y))) = g (g (y + N (N y))) := by rw [e1 y]
    _ = (y + N (N y)) + N (N (y + N (N y))) := e1 _
    _ = (y + N (N y)) + N (N y) := by rw [e2 y]
    _ = y + (N (N y) + N (N y)) := by abel
    _ = y := by rw [Classify.vec_add_self K (N (N y)), add_zero]

theorem orth_quotSat
    {G : Type} [Group G] [Finite G] (L₁ L₂ : Subgroup G)
    {K : Type} [Field K] [Finite K] [CharP K 2] (h4 : 4 ≤ Nat.card K)
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (F : LinearMap.BilinForm K V) (halt : F.IsAlt)
    (e₁ e₂ : V) (hind : LinearIndependent K ![e₁, e₂]) (h12 : F e₁ e₂ = 0)
    (ρ : ↥(L₁ ⊔ L₂) →* (V ≃ₗ[K] V))
    (hρ₁ : ∀ (l : G) (hl : l ∈ L₁),
      ρ ⟨l, Subgroup.mem_sup_left hl⟩ ∈ Classify.pointRadSubgroup F e₁)
    (hρ₂ : ∀ (l : G) (hl : l ∈ L₂),
      ρ ⟨l, Subgroup.mem_sup_right hl⟩ ∈ Classify.pointRadSubgroup F e₂)
    (hf₁ : Classify.ElationFull F
      {g | ∃ (l : G) (hl : l ∈ L₁), ρ ⟨l, Subgroup.mem_sup_left hl⟩ = g} e₁)
    (hf₂ : Classify.ElationFull F
      {g | ∃ (l : G) (hl : l ∈ L₂), ρ ⟨l, Subgroup.mem_sup_right hl⟩ = g} e₂)
    (hker : ∀ s : ↥(L₁ ⊔ L₂), ρ s = 1 → ∃ j : ℕ, (s : G) ^ 2 ^ j = 1) :
    QuotSat (L₁ ⊔ L₂) (inSubgroup (pCore 2) (L₁ ⊔ L₂)) (IsSLModel 2 (Nat.card K)) := by
  set W : Submodule K V := Submodule.span K (Set.range ![e₁, e₂]) with hWdef
  have he₁W : e₁ ∈ W := Submodule.subset_span ⟨0, rfl⟩
  have he₂W : e₂ ∈ W := Submodule.subset_span ⟨1, rfl⟩
  obtain ⟨b, hb0, hb1⟩ : ∃ b : Module.Basis (Fin 2) K W,
      (b 0 : V) = e₁ ∧ (b 1 : V) = e₂ :=
    ⟨Module.Basis.span hind, Module.Basis.coe_span_apply hind 0,
      Module.Basis.coe_span_apply hind 1⟩
  have hF12 : F e₁ e₂ = 0 := h12
  have hF21 : F e₂ e₁ = 0 := by rw [Classify.form_comm halt, h12]
  have hinv1 : ∀ g ∈ Classify.pointRadSubgroup F e₁, ∀ w ∈ W, g w ∈ W := by
    intro g hg
    obtain ⟨-, h2, h3⟩ := Classify.mem_pointRad_iff.mp hg
    obtain ⟨c, hc⟩ := h3 e₂ hF21
    exact orth_invariant (e₁ := e₁) (e₂ := e₂) g (by rw [h2]; exact he₁W)
      (by rw [hc]; exact W.add_mem he₂W (W.smul_mem c he₁W))
  have hinv2 : ∀ g ∈ Classify.pointRadSubgroup F e₂, ∀ w ∈ W, g w ∈ W := by
    intro g hg
    obtain ⟨-, h2, h3⟩ := Classify.mem_pointRad_iff.mp hg
    obtain ⟨c, hc⟩ := h3 e₁ h12
    exact orth_invariant (e₁ := e₁) (e₂ := e₂) g
      (by rw [hc]; exact W.add_mem he₁W (W.smul_mem c he₂W)) (by rw [h2]; exact he₂W)
  obtain ⟨k, hkmem⟩ : ∃ k : Set ↥(L₁ ⊔ L₂),
      ∀ x, x ∈ k ↔ ((x : G) ∈ L₁ ∨ (x : G) ∈ L₂) :=
    ⟨{x | (x : G) ∈ L₁ ∨ (x : G) ∈ L₂}, fun x => Iff.rfl⟩
  have hgen1 : ∀ x : ↥(L₁ ⊔ L₂), (x : G) ∈ L₁ → ρ x ∈ Classify.pointRadSubgroup F e₁ := by
    intro x hx
    simpa using hρ₁ (x : G) hx
  have hgen2 : ∀ x : ↥(L₁ ⊔ L₂), (x : G) ∈ L₂ → ρ x ∈ Classify.pointRadSubgroup F e₂ := by
    intro x hx
    simpa using hρ₂ (x : G) hx
  have hclos : ∀ x : ↥(L₁ ⊔ L₂), x ∈ Subgroup.closure k := by
    intro x
    have hle : L₁ ⊔ L₂ ≤ (Subgroup.closure k).map (L₁ ⊔ L₂).subtype := by
      refine sup_le (fun l hl => Subgroup.mem_map.mpr ⟨⟨l, Subgroup.mem_sup_left hl⟩,
        Subgroup.subset_closure ((hkmem ⟨l, Subgroup.mem_sup_left hl⟩).2 (Or.inl hl)), rfl⟩)
        (fun l hl => Subgroup.mem_map.mpr ⟨⟨l, Subgroup.mem_sup_right hl⟩,
          Subgroup.subset_closure ((hkmem ⟨l, Subgroup.mem_sup_right hl⟩).2 (Or.inr hl)), rfl⟩)
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp (hle x.2)
    have hxy : y = x := Subtype.ext hyx
    rw [← hxy]
    exact hy
  have hone : ∀ w ∈ W, ρ 1 w ∈ W := by
    intro w hw
    rw [map_one]
    simpa using hw
  have hmul1 : ∀ x y : ↥(L₁ ⊔ L₂), (∀ w ∈ W, ρ x w ∈ W) → (∀ w ∈ W, ρ y w ∈ W) →
      ∀ w ∈ W, ρ (x * y) w ∈ W := by
    intro x y hx hy w hw
    rw [map_mul, LinearEquiv.mul_apply]
    exact hx _ (hy w hw)
  have hk1 : ∀ y ∈ k, (∀ w ∈ W, ρ y w ∈ W) ∧ (∀ w ∈ W, ρ y⁻¹ w ∈ W) := by
    intro y hy
    rcases (hkmem y).1 hy with hy1 | hy2
    · have h := hgen1 y hy1
      have h' : ρ y⁻¹ ∈ Classify.pointRadSubgroup F e₁ := by
        rw [map_inv]
        exact (Classify.pointRadSubgroup F e₁).inv_mem h
      exact ⟨hinv1 _ h, hinv1 _ h'⟩
    · have h := hgen2 y hy2
      have h' : ρ y⁻¹ ∈ Classify.pointRadSubgroup F e₂ := by
        rw [map_inv]
        exact (Classify.pointRadSubgroup F e₂).inv_mem h
      exact ⟨hinv2 _ h, hinv2 _ h'⟩
  have hWinv : ∀ x : ↥(L₁ ⊔ L₂), ∀ w ∈ W, ρ x w ∈ W := fun x =>
    (orth_good_of_closure (k := k) (Pm := fun y => ∀ w ∈ W, ρ y w ∈ W) hone hmul1 hk1
      (hclos x)).1
  obtain ⟨Pm2, hPm2⟩ : ∃ P : ↥(L₁ ⊔ L₂) → Prop, ∀ x, P x ↔
      (Classify.IsIsom F (ρ x) ∧ (∀ v, F v e₁ = 0 → F v e₂ = 0 → ρ x v - v ∈ W) ∧
        ((b.toGL (actionOnSubspace ρ W hWinv x) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det
          = 1) :=
    ⟨_, fun x => Iff.rfl⟩
  have hone2 : Pm2 1 := by
    refine (hPm2 1).2 ⟨?_, ?_, ?_⟩
    · intro a c
      simp
    · intro v _ _
      simp
    · simp
  have hmul2 : ∀ x y : ↥(L₁ ⊔ L₂), Pm2 x → Pm2 y → Pm2 (x * y) := by
    intro x y hx hy
    obtain ⟨hx1, hx2, hx3⟩ := (hPm2 x).1 hx
    obtain ⟨hy1, hy2, hy3⟩ := (hPm2 y).1 hy
    refine (hPm2 (x * y)).2 ⟨?_, ?_, ?_⟩
    · intro a c
      rw [map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hx1 (ρ y a) (ρ y c),
        hy1 a c]
    · intro v hv1 hv2
      have h1 : ρ x v - v ∈ W := hx2 v hv1 hv2
      have h2 : ρ y v - v ∈ W := hy2 v hv1 hv2
      have h3 : ρ x (ρ y v - v) ∈ W := hWinv x _ h2
      have key : ρ (x * y) v - v = (ρ x v - v) + ρ x (ρ y v - v) := by
        rw [map_mul, LinearEquiv.mul_apply, map_sub]
        abel
      rw [key]
      exact W.add_mem h1 h3
    · rw [map_mul, map_mul, Units.val_mul, Matrix.det_mul, hx3, hy3, one_mul]
  have gen1 : ∀ x : ↥(L₁ ⊔ L₂), ρ x ∈ Classify.pointRadSubgroup F e₁ → Pm2 x := by
    intro x hx
    obtain ⟨hI, h2, h3⟩ := Classify.mem_pointRad_iff.mp hx
    obtain ⟨c, hc⟩ := h3 e₂ hF21
    refine (hPm2 x).2 ⟨hI, fun v hv1 _ => ?_, ?_⟩
    · obtain ⟨c', hc'⟩ := h3 v hv1
      rw [hc', show v + c' • e₁ - v = c' • e₁ by abel]
      exact W.smul_mem c' he₁W
    · have hM := orth_toGL_tv01 b (actionOnSubspace ρ W hWinv x) c
        (by rw [actionOnSubspace_apply, hb0, h2])
        (by rw [actionOnSubspace_apply, hb0, hb1, hc])
      rw [hM, Matrix.det_transvection_of_ne 0 1 (show (0 : Fin 2) ≠ 1 by decide)]
  have gen2 : ∀ x : ↥(L₁ ⊔ L₂), ρ x ∈ Classify.pointRadSubgroup F e₂ → Pm2 x := by
    intro x hx
    obtain ⟨hI, h2, h3⟩ := Classify.mem_pointRad_iff.mp hx
    obtain ⟨c, hc⟩ := h3 e₁ hF12
    refine (hPm2 x).2 ⟨hI, fun v _ hv2 => ?_, ?_⟩
    · obtain ⟨c', hc'⟩ := h3 v hv2
      rw [hc', show v + c' • e₂ - v = c' • e₂ by abel]
      exact W.smul_mem c' he₂W
    · have hM := orth_toGL_tv10 b (actionOnSubspace ρ W hWinv x) c
        (by rw [actionOnSubspace_apply, hb0, hb1, hc])
        (by rw [actionOnSubspace_apply, hb1, h2])
      rw [hM, Matrix.det_transvection_of_ne 1 0 (show (1 : Fin 2) ≠ 0 by decide)]
  have hk2 : ∀ y ∈ k, Pm2 y ∧ Pm2 y⁻¹ := by
    intro y hy
    rcases (hkmem y).1 hy with hy1 | hy2
    · have h := hgen1 y hy1
      have h' : ρ y⁻¹ ∈ Classify.pointRadSubgroup F e₁ := by
        rw [map_inv]
        exact (Classify.pointRadSubgroup F e₁).inv_mem h
      exact ⟨gen1 y h, gen1 y⁻¹ h'⟩
    · have h := hgen2 y hy2
      have h' : ρ y⁻¹ ∈ Classify.pointRadSubgroup F e₂ := by
        rw [map_inv]
        exact (Classify.pointRadSubgroup F e₂).inv_mem h
      exact ⟨gen2 y h, gen2 y⁻¹ h'⟩
  have hgood2 : ∀ x : ↥(L₁ ⊔ L₂), Pm2 x ∧ Pm2 x⁻¹ := fun x =>
    orth_good_of_closure (k := k) (Pm := Pm2) hone2 hmul2 hk2 (hclos x)
  have hdet : ∀ s : ↥(L₁ ⊔ L₂),
      ((b.toGL (actionOnSubspace ρ W hWinv s) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det
        = 1 :=
    fun s => ((hPm2 s).1 (hgood2 s).1).2.2
  have htrans : ∀ (i j : Fin 2), i ≠ j → ∀ c : K, ∃ s : ↥(L₁ ⊔ L₂),
      ((b.toGL (actionOnSubspace ρ W hWinv s) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
        Matrix.transvection i j c := by
    intro i j hij c
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · obtain ⟨φ, hφ1, hφ2⟩ := orth_exists_dual hind 0 c
      obtain ⟨g, ⟨l, hl, rfl⟩, hg⟩ := hf₁ φ hφ1
      refine ⟨⟨l, Subgroup.mem_sup_left hl⟩, orth_toGL_tv01 b _ c ?_ ?_⟩
      · rw [actionOnSubspace_apply, hb0]
        exact (Classify.mem_pointRad_iff.mp (hρ₁ l hl)).2.1
      · rw [actionOnSubspace_apply, hb0, hb1, hg e₂ hF21, hφ2]
    · obtain ⟨φ, hφ1, hφ2⟩ := orth_exists_dual hind c 0
      obtain ⟨g, ⟨l, hl, rfl⟩, hg⟩ := hf₂ φ hφ2
      refine ⟨⟨l, Subgroup.mem_sup_right hl⟩, orth_toGL_tv10 b _ c ?_ ?_⟩
      · rw [actionOnSubspace_apply, hb0, hb1, hg e₁ hF12, hφ1]
      · rw [actionOnSubspace_apply, hb1]
        exact (Classify.mem_pointRad_iff.mp (hρ₂ l hl)).2.1
    · exact absurd rfl hij
  have hker' : ∀ s : ↥(L₁ ⊔ L₂), b.toGL (actionOnSubspace ρ W hWinv s) = 1 →
      ∃ j : ℕ, s ^ 2 ^ j = 1 := by
    intro s hs
    have hA : actionOnSubspace ρ W hWinv s = 1 := b.toGL.map_eq_one_iff.mp hs
    have hfix : ∀ w ∈ W, ρ s w = w := by
      intro w hw
      have h := congrArg (fun f : W ≃ₗ[K] W => ((f ⟨w, hw⟩ : W) : V)) hA
      simpa [actionOnSubspace_apply] using h
    obtain ⟨hIso, hP3, -⟩ := (hPm2 s).1 (hgood2 s).1
    have hg1 : ρ s e₁ = e₁ := hfix e₁ he₁W
    have hg2 : ρ s e₂ = e₂ := hfix e₂ he₂W
    have hperp : ∀ y : V, F (ρ s y - y) e₁ = 0 ∧ F (ρ s y - y) e₂ = 0 := by
      intro y
      have k1 : F (ρ s y) e₁ = F y e₁ := by
        have h := hIso y e₁
        rwa [hg1] at h
      have k2 : F (ρ s y) e₂ = F y e₂ := by
        have h := hIso y e₂
        rwa [hg2] at h
      exact ⟨by rw [map_sub, LinearMap.sub_apply, k1, sub_self],
        by rw [map_sub, LinearMap.sub_apply, k2, sub_self]⟩
    have hcube : ∀ z : V, ρ s (ρ s (ρ s z - z) - (ρ s z - z)) -
        (ρ s (ρ s z - z) - (ρ s z - z)) = 0 := by
      intro z
      have hmem : ρ s (ρ s z - z) - (ρ s z - z) ∈ W := hP3 _ (hperp z).1 (hperp z).2
      rw [hfix _ hmem, sub_self]
    have hfour : ∀ y : V, ρ s (ρ s (ρ s (ρ s y))) = y :=
      orth_pow_four (ρ s) (fun w => ρ s w - w) (fun z => by simp)
        (fun a c => by simp only [map_add]; abel) hcube
    have hs4 : ρ (s ^ 4) = 1 := by
      apply LinearEquiv.ext
      intro y
      rw [show s ^ 4 = s * s * s * s by simp only [pow_succ, pow_zero, one_mul]]
      simp only [map_mul, LinearEquiv.mul_apply]
      exact hfour y
    obtain ⟨j, hj⟩ := hker (s ^ 4) hs4
    refine ⟨j + 2, ?_⟩
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, show 2 ^ (j + 2) = 4 * 2 ^ j by ring, pow_mul]
    rw [Subgroup.coe_pow] at hj
    exact hj
  exact quotSat_isSLModel_of_restrict (L₁ ⊔ L₂) h4 W (le_refl 2) b ρ hWinv hdet htrans hker'

end CFSG.RankThree.GF2n.Stroth80
