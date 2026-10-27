module

public import CFSG.RankThree.GF2n.Stroth80.Sec312Quot

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.Open CFSG.Open.StatedAPI CFSG.Assembly.LowTwoRank
open scoped Matrix

namespace HS9

section TwoElations

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

@[expose] def moveSub (W : Submodule K V) : Subgroup (V ≃ₗ[K] V) where
  carrier := {g | ∀ v, g v - v ∈ W}
  one_mem' := by
    intro v
    simp
  mul_mem' := by
    intro g h hg hh v
    have hg0 : ∀ w, g w - w ∈ W := hg
    have hh0 : ∀ w, h w - w ∈ W := hh
    have hgW : ∀ w ∈ W, g w ∈ W := fun w hw => by
      simpa using W.add_mem (hg0 w) hw
    have e : (g * h) v - v = g (h v - v) + (g v - v) := by
      rw [LinearEquiv.mul_apply, map_sub]
      abel
    show (g * h) v - v ∈ W
    rw [e]
    exact W.add_mem (hgW _ (hh0 v)) (hg0 v)
  inv_mem' := by
    intro g hg v
    have hg0 : ∀ w, g w - w ∈ W := hg
    have hgv : g (g⁻¹ v) = v := by
      rw [← LinearEquiv.mul_apply, mul_inv_cancel]
      rfl
    have h1 := hg0 (g⁻¹ v)
    rw [hgv] at h1
    have h2 := W.neg_mem h1
    rw [neg_sub] at h2
    exact h2

theorem mem_moveSub_iff {W : Submodule K V} {g : V ≃ₗ[K] V} :
    g ∈ moveSub W ↔ ∀ v, g v - v ∈ W := Iff.rfl

theorem mem_of_sup_pair {G : Type} [Group G] {L₁ L₂ : Subgroup G} (D : Subgroup ↥(L₁ ⊔ L₂))
    (h₁ : ∀ (l : G) (hl : l ∈ L₁), (⟨l, Subgroup.mem_sup_left hl⟩ : ↥(L₁ ⊔ L₂)) ∈ D)
    (h₂ : ∀ (l : G) (hl : l ∈ L₂), (⟨l, Subgroup.mem_sup_right hl⟩ : ↥(L₁ ⊔ L₂)) ∈ D)
    (x : ↥(L₁ ⊔ L₂)) : x ∈ D := by
  have hle : L₁ ⊔ L₂ ≤ D.map (L₁ ⊔ L₂).subtype :=
    sup_le (fun l hl => Subgroup.mem_map.mpr ⟨⟨l, Subgroup.mem_sup_left hl⟩, h₁ l hl, rfl⟩)
      (fun l hl => Subgroup.mem_map.mpr ⟨⟨l, Subgroup.mem_sup_right hl⟩, h₂ l hl, rfl⟩)
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp (hle x.2)
  have hxy : y = x := Subtype.ext hyx
  rwa [← hxy]

private theorem sl2_toGL_tv01 {W : Submodule K V} (b : Module.Basis (Fin 2) K W) (f : W ≃ₗ[K] W)
    (c : K) (h0 : (f (b 0) : V) = (b 0 : V)) (h1 : (f (b 1) : V) = (b 1 : V) + c • (b 0 : V)) :
    ((b.toGL f : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = Matrix.transvection 0 1 c := by
  have e0 : f (b 0) = b 0 := Subtype.ext h0
  have e1 : f (b 1) = b 1 + c • b 0 := Subtype.ext (by simp [h1])
  ext i j
  rw [toGL_entry]
  fin_cases i <;> fin_cases j <;>
    simp [e0, e1, Module.Basis.repr_self, Matrix.transvection, Matrix.single_apply]

private theorem sl2_toGL_tv10 {W : Submodule K V} (b : Module.Basis (Fin 2) K W) (f : W ≃ₗ[K] W)
    (c : K) (h0 : (f (b 0) : V) = (b 0 : V) + c • (b 1 : V)) (h1 : (f (b 1) : V) = (b 1 : V)) :
    ((b.toGL f : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = Matrix.transvection 1 0 c := by
  have e0 : f (b 0) = b 0 + c • b 1 := Subtype.ext (by simp [h0])
  have e1 : f (b 1) = b 1 := Subtype.ext h1
  ext i j
  rw [toGL_entry]
  fin_cases i <;> fin_cases j <;>
    simp [e0, e1, Module.Basis.repr_self, Matrix.transvection, Matrix.single_apply]

private theorem sl2_exists_dual {e₁ e₂ : V} (hind : LinearIndependent K ![e₁, e₂]) (a₁ a₂ : K) :
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

theorem elatPair_quotSat [CharP K 2] {G : Type} [Group G] [Finite G] (L₁ L₂ : Subgroup G)
    [Finite K] (h4 : 4 ≤ Nat.card K) (e₁ e₂ : V) (hind : LinearIndependent K ![e₁, e₂])
    (ρ : ↥(L₁ ⊔ L₂) →* (V ≃ₗ[K] V))
    (hel₁ : ∀ (l : G) (hl : l ∈ L₁), ∃ f : Module.Dual K V, f e₁ = 0 ∧
      ∀ v, ρ ⟨l, Subgroup.mem_sup_left hl⟩ v = v + f v • e₁)
    (hel₂ : ∀ (l : G) (hl : l ∈ L₂), ∃ f : Module.Dual K V, f e₂ = 0 ∧
      ∀ v, ρ ⟨l, Subgroup.mem_sup_right hl⟩ v = v + f v • e₂)
    (hfull₁ : ∀ f : Module.Dual K V, f e₁ = 0 → ∃ (l : G) (hl : l ∈ L₁),
      ∀ v, ρ ⟨l, Subgroup.mem_sup_left hl⟩ v = v + f v • e₁)
    (hfull₂ : ∀ f : Module.Dual K V, f e₂ = 0 → ∃ (l : G) (hl : l ∈ L₂),
      ∀ v, ρ ⟨l, Subgroup.mem_sup_right hl⟩ v = v + f v • e₂)
    (hker : ∀ s : ↥(L₁ ⊔ L₂), ρ s = 1 → ∃ j : ℕ, s ^ 2 ^ j = 1) :
    QuotSat (L₁ ⊔ L₂) (inSubgroup (pCore 2) (L₁ ⊔ L₂)) (IsSLModel 2 (Nat.card K)) := by
  classical
  set W : Submodule K V := Submodule.span K (Set.range ![e₁, e₂]) with hWdef
  have he₁W : e₁ ∈ W := Submodule.subset_span ⟨0, rfl⟩
  have he₂W : e₂ ∈ W := Submodule.subset_span ⟨1, rfl⟩
  obtain ⟨b, hb0, hb1⟩ : ∃ b : Module.Basis (Fin 2) K W, (b 0 : V) = e₁ ∧ (b 1 : V) = e₂ :=
    ⟨Module.Basis.span hind, Module.Basis.coe_span_apply hind 0,
      Module.Basis.coe_span_apply hind 1⟩
  have hmove : ∀ (x : ↥(L₁ ⊔ L₂)) (v : V), ρ x v - v ∈ W := by
    have key := mem_of_sup_pair ((moveSub W).comap ρ)
      (fun l hl => by
        obtain ⟨f, -, hf⟩ := hel₁ l hl
        rw [Subgroup.mem_comap, mem_moveSub_iff]
        intro v
        rw [hf v, add_sub_cancel_left]
        exact W.smul_mem _ he₁W)
      (fun l hl => by
        obtain ⟨f, -, hf⟩ := hel₂ l hl
        rw [Subgroup.mem_comap, mem_moveSub_iff]
        intro v
        rw [hf v, add_sub_cancel_left]
        exact W.smul_mem _ he₂W)
    exact fun x v => (mem_moveSub_iff.mp (Subgroup.mem_comap.mp (key x))) v
  have hW : ∀ (s : ↥(L₁ ⊔ L₂)), ∀ w ∈ W, ρ s w ∈ W := fun s w hw => by
    simpa using W.add_mem (hmove s w) hw
  have hact₁ : ∀ (l : G) (hl : l ∈ L₁), ∃ c : K,
      ρ ⟨l, Subgroup.mem_sup_left hl⟩ e₁ = e₁ ∧
        ρ ⟨l, Subgroup.mem_sup_left hl⟩ e₂ = e₂ + c • e₁ := by
    intro l hl
    obtain ⟨f, hf0, hf⟩ := hel₁ l hl
    exact ⟨f e₂, by rw [hf, hf0, zero_smul, add_zero], hf e₂⟩
  have hact₂ : ∀ (l : G) (hl : l ∈ L₂), ∃ c : K,
      ρ ⟨l, Subgroup.mem_sup_right hl⟩ e₁ = e₁ + c • e₂ ∧
        ρ ⟨l, Subgroup.mem_sup_right hl⟩ e₂ = e₂ := by
    intro l hl
    obtain ⟨f, hf0, hf⟩ := hel₂ l hl
    exact ⟨f e₁, hf e₁, by rw [hf, hf0, zero_smul, add_zero]⟩
  have hdet : ∀ s : ↥(L₁ ⊔ L₂),
      ((b.toGL (actionOnSubspace ρ W hW s) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = 1 := by
    set θ : ↥(L₁ ⊔ L₂) →* GL (Fin 2) K :=
      b.toGL.toMonoidHom.comp (actionOnSubspace ρ W hW) with hθdef
    have hθe : ∀ s, θ s = b.toGL (actionOnSubspace ρ W hW s) := fun s => rfl
    have key := mem_of_sup_pair ((StatedSL 2 K).comap θ)
      (fun l hl => by
        obtain ⟨c, h0, h1⟩ := hact₁ l hl
        rw [Subgroup.mem_comap, hθe]
        apply mem_statedSL_of_det
        rw [sl2_toGL_tv01 b _ c (by rw [actionOnSubspace_apply, hb0, h0])
          (by rw [actionOnSubspace_apply, hb0, hb1, h1]),
          Matrix.det_transvection_of_ne 0 1 (show (0 : Fin 2) ≠ 1 by decide)])
      (fun l hl => by
        obtain ⟨c, h0, h1⟩ := hact₂ l hl
        rw [Subgroup.mem_comap, hθe]
        apply mem_statedSL_of_det
        rw [sl2_toGL_tv10 b _ c (by rw [actionOnSubspace_apply, hb0, hb1, h0])
          (by rw [actionOnSubspace_apply, hb1, h1]),
          Matrix.det_transvection_of_ne 1 0 (show (1 : Fin 2) ≠ 0 by decide)])
    intro s
    have h := det_of_mem_statedSL (Subgroup.mem_comap.mp (key s))
    rwa [hθe] at h
  have htrans : ∀ (i j : Fin 2), i ≠ j → ∀ c : K, ∃ s : ↥(L₁ ⊔ L₂),
      ((b.toGL (actionOnSubspace ρ W hW s) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
        Matrix.transvection i j c := by
    intro i j hij c
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · obtain ⟨φ, hφ1, hφ2⟩ := sl2_exists_dual hind 0 c
      obtain ⟨l, hl, hg⟩ := hfull₁ φ hφ1
      refine ⟨⟨l, Subgroup.mem_sup_left hl⟩, sl2_toGL_tv01 b _ c ?_ ?_⟩
      · rw [actionOnSubspace_apply, hb0, hg, hφ1, zero_smul, add_zero]
      · rw [actionOnSubspace_apply, hb0, hb1, hg, hφ2]
    · obtain ⟨φ, hφ1, hφ2⟩ := sl2_exists_dual hind c 0
      obtain ⟨l, hl, hg⟩ := hfull₂ φ hφ2
      refine ⟨⟨l, Subgroup.mem_sup_right hl⟩, sl2_toGL_tv10 b _ c ?_ ?_⟩
      · rw [actionOnSubspace_apply, hb0, hb1, hg, hφ1]
      · rw [actionOnSubspace_apply, hb1, hg, hφ2, zero_smul, add_zero]
    · exact absurd rfl hij
  have hker' : ∀ s : ↥(L₁ ⊔ L₂), b.toGL (actionOnSubspace ρ W hW s) = 1 →
      ∃ j : ℕ, s ^ 2 ^ j = 1 := by
    intro s hs
    have hA : actionOnSubspace ρ W hW s = 1 := b.toGL.map_eq_one_iff.mp hs
    have hfix : ∀ w ∈ W, ρ s w = w := by
      intro w hw
      have h := congrArg (fun f : W ≃ₗ[K] W => ((f ⟨w, hw⟩ : W) : V)) hA
      simpa [actionOnSubspace_apply] using h
    have hsq : ρ (s * s) = 1 := by
      apply LinearEquiv.ext
      intro y
      rw [map_mul, LinearEquiv.mul_apply]
      have e1 : ρ s (ρ s y) = ρ s (ρ s y - y) + ρ s y := by
        rw [← map_add, sub_add_cancel]
      have e2 : (ρ s y - y) + ρ s y = (ρ s y + ρ s y) - y := by abel
      have e3 : ρ s y + ρ s y = 0 := by
        rw [← two_smul K (ρ s y), CharTwo.two_eq_zero, zero_smul]
      have e4 : -y = y := by
        rw [neg_eq_iff_add_eq_zero, ← two_smul K y, CharTwo.two_eq_zero, zero_smul]
      rw [e1, hfix _ (hmove s y), e2, e3, zero_sub, e4]
      rfl
    obtain ⟨j, hj⟩ := hker (s * s) hsq
    refine ⟨j + 1, ?_⟩
    rw [pow_succ, pow_mul', pow_two]
    exact hj
  exact quotSat_isSLModel_of_restrict (L₁ ⊔ L₂) h4 W (le_refl 2) b ρ hW hdet htrans hker'

end TwoElations

end HS9

end CFSG.RankThree.GF2n.Stroth80
