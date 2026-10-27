module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec95DMPSplit
public import CFSG.RankThree.GF2n.Stroth80.HeringSec95DMPDefs

public section

namespace CFSG.RankThree.GF2n.Stroth80.HS9.MP

open scoped Matrix MatrixGroups
open CFSG.RankThree.GF2n.Stroth80.HS9.M1

section Restrict

variable {K : Type} [Field K] {W : Type} [AddCommGroup W] [Module K W]

@[expose] def s95s_restrict (σ : SL(2, K) →* (W ≃ₗ[K] W)) (N : Submodule K W)
    (hσ : ∀ g, ∀ m ∈ N, σ g m ∈ N) : SL(2, K) →* (↥N ≃ₗ[K] ↥N) where
  toFun g :=
    { toFun := fun m => ⟨σ g m, hσ g m m.2⟩
      map_add' := fun x y => Subtype.ext (map_add _ _ _)
      map_smul' := fun c x => Subtype.ext (map_smul _ _ _)
      invFun := fun m => ⟨σ g⁻¹ m, hσ g⁻¹ m m.2⟩
      left_inv := fun m => Subtype.ext (by
        show σ g⁻¹ (σ g (m : W)) = m
        rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
        rfl)
      right_inv := fun m => Subtype.ext (by
        show σ g (σ g⁻¹ (m : W)) = m
        rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
        rfl) }
  map_one' := LinearEquiv.ext fun m => Subtype.ext (by
    show σ 1 (m : W) = m
    rw [map_one]
    rfl)
  map_mul' := fun g h => LinearEquiv.ext fun m => Subtype.ext (by
    show σ (g * h) (m : W) = σ g (σ h (m : W))
    rw [map_mul]
    rfl)

end Restrict

section Factor

variable {K : Type} [Field K] [Finite K] [CharP K 2] {W : Type} [AddCommGroup W] [Module K W]
  [FiniteDimensional K W]

theorem s95s_factor (hF : SL2FactorStatement) (hK : 4 ≤ Nat.card K)
    (σ : SL(2, K) →* (W ≃ₗ[K] W)) (N X X' : Submodule K W) (hσ : ∀ g, ∀ m ∈ N, σ g m ∈ N)
    (hdisj : ∀ m ∈ N, m ∈ X → m ∈ X' → m = 0)
    (hcodisj : ∀ m ∈ N, ∃ x y, x ∈ N ∧ x ∈ X ∧ y ∈ N ∧ y ∈ X' ∧ m = x + y)
    (hU : ∀ a : K, (∀ m ∈ N, σ (uSL a) m - m ∈ X) ∧ ∀ x ∈ N, x ∈ X → σ (uSL a) x = x)
    (hL : ∀ b : K, (∀ m ∈ N, σ (lSL b) m - m ∈ X') ∧ ∀ x ∈ N, x ∈ X' → σ (lSL b) x = x)
    (hC : ∀ m ∈ N, (∀ g, σ g m = m) → m = 0)
    (Θ : AddSubgroup (W →ₗ[K] (Fin 2 → K)))
    (hΘ : ∀ θ ∈ Θ, ∀ a : K, ∀ m ∈ N, θ (σ (uSL a) m) = uMat a *ᵥ θ m)
    (hsep : ∀ x ∈ N, x ∈ X → (∀ θ ∈ Θ, θ x = 0) → x = 0) :
    ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module K Y) (c : ↥N ≃ₗ[K] (Fin 2 → Y)),
      ∀ (g : SL(2, K)) (m : ↥N), c ⟨σ g m, hσ g m m.2⟩ =
        smulVec (g : Matrix (Fin 2) (Fin 2) K) (c m) := by
  let r : (W →ₗ[K] (Fin 2 → K)) →+ (↥N →ₗ[K] (Fin 2 → K)) :=
    AddMonoidHom.mk' (fun θ => θ ∘ₗ N.subtype) fun θ θ' => LinearMap.add_comp _ _ _
  have hcompl : IsCompl (X.comap N.subtype) (X'.comap N.subtype) := by
    refine ⟨Submodule.disjoint_def.2 fun m h1 h2 => ?_, codisjoint_iff.2 ?_⟩
    · exact Subtype.ext (hdisj m m.2 h1 h2)
    · refine eq_top_iff.2 fun m _ => Submodule.mem_sup.2 ?_
      obtain ⟨x, y, hxN, hxX, hyN, hyX, hm⟩ := hcodisj m m.2
      exact ⟨⟨x, hxN⟩, hxX, ⟨y, hyN⟩, hyX, Subtype.ext hm.symm⟩
  have hΘ' : ∀ θ ∈ Θ.map r, ∀ (a : K) (m : ↥N),
      θ (s95s_restrict σ N hσ (uSL a) m) = uMat a *ᵥ θ m := by
    intro θ hθ a m
    obtain ⟨θ₀, hθ₀, rfl⟩ := AddSubgroup.mem_map.1 hθ
    exact hΘ θ₀ hθ₀ a m m.2
  have hsep' : ∀ x ∈ X.comap N.subtype, (∀ θ ∈ Θ.map r, θ x = 0) → x = 0 := by
    intro x hx h
    exact Subtype.ext (hsep x x.2 hx fun θ hθ => h (r θ) (AddSubgroup.mem_map.2 ⟨θ, hθ, rfl⟩))
  obtain ⟨Y, i1, i2, c, hc⟩ := hF K hK ↥N (s95s_restrict σ N hσ) (X.comap N.subtype)
    (X'.comap N.subtype) hcompl
    (fun a => ⟨fun m => (hU a).1 m m.2, fun x hx => Subtype.ext ((hU a).2 x x.2 hx)⟩)
    (fun b => ⟨fun m => (hL b).1 m m.2, fun x hx => Subtype.ext ((hL b).2 x x.2 hx)⟩)
    (fun m hm => Subtype.ext (hC m m.2 fun g => congrArg Subtype.val (hm g)))
    (Θ.map r) hΘ' hsep'
  exact ⟨Y, i1, i2, c, hc⟩

end Factor

section Move

variable {K : Type} [Field K] [CharP K 2] {W : Type} [AddCommGroup W] [Module K W]

theorem s95s_isCompl_map {p q : Submodule K W} (h : IsCompl p q) (e : W ≃ₗ[K] W) :
    IsCompl (p.map (e : W →ₗ[K] W)) (q.map (e : W →ₗ[K] W)) :=
  (Submodule.orderIsoMapComap e).isCompl h

theorem s95s_move {Act : SL(2, K) × SL(2, K) →* (W ≃ₗ[K] W)} {X : Submodule K W}
    (hS2 : ∀ a a' : K, ∀ x ∈ X, Act (uSL a, uSL a') x = x) {g h : SL(2, K)}
    (hg : (g : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0) (hh : (h : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0)
    (hX : IsCompl X (X.map ((Act (g, h) : W ≃ₗ[K] W) : W →ₗ[K] W))) :
    ∃ g' h' : SL(2, K), (g' : Matrix (Fin 2) (Fin 2) K) 0 0 = 0 ∧
      (g' : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0 ∧ (h' : Matrix (Fin 2) (Fin 2) K) 0 0 = 0 ∧
      (h' : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0 ∧
      IsCompl X (X.map ((Act (g', h') : W ≃ₗ[K] W) : W →ₗ[K] W)) := by
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  set s : K := (g : Matrix (Fin 2) (Fin 2) K) 0 0 / (g : Matrix (Fin 2) (Fin 2) K) 1 0 with hs
  set s' : K := (h : Matrix (Fin 2) (Fin 2) K) 0 0 / (h : Matrix (Fin 2) (Fin 2) K) 1 0 with hs'
  have e00 : ∀ k : SL(2, K), (k : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0 →
      ((uSL ((k : Matrix (Fin 2) (Fin 2) K) 0 0 / (k : Matrix (Fin 2) (Fin 2) K) 1 0) * k :
        SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 0 0 = 0 := by
    intro k hk
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_uSL, uMat, Matrix.mul_apply,
      Fin.sum_univ_two]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
    field_simp
    linear_combination (k : Matrix (Fin 2) (Fin 2) K) 0 0 * h2
  have e10 : ∀ k : SL(2, K), ∀ t : K, ((uSL t * k : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 1 0 =
      (k : Matrix (Fin 2) (Fin 2) K) 1 0 := by
    intro k t
    simp [Matrix.SpecialLinearGroup.coe_mul, coe_uSL, uMat, Matrix.mul_apply, Fin.sum_univ_two]
  refine ⟨uSL s * g, uSL s' * h, e00 g hg, by rw [e10]; exact hg, e00 h hh,
    by rw [e10]; exact hh, ?_⟩
  have e : X.map ((Act (uSL s * g, uSL s' * h) : W ≃ₗ[K] W) : W →ₗ[K] W) =
      (X.map ((Act (g, h) : W ≃ₗ[K] W) : W →ₗ[K] W)).map
        ((Act (uSL s, uSL s') : W ≃ₗ[K] W) : W →ₗ[K] W) := by
    rw [← Submodule.map_comp]
    congr 1
    ext w
    simp only [LinearEquiv.coe_coe, LinearMap.coe_comp, Function.comp_apply]
    rw [← s95s_act_mul]
    simp
  have hfixX : X.map ((Act (uSL s, uSL s') : W ≃ₗ[K] W) : W →ₗ[K] W) = X := by
    ext x
    rw [Submodule.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [hS2 s s' y hy] using hy
    · exact fun hx => ⟨x, hx, hS2 s s' x hx⟩
  rw [e]
  have := s95s_isCompl_map hX (Act (uSL s, uSL s'))
  rwa [hfixX] at this

end Move

end CFSG.RankThree.GF2n.Stroth80.HS9.MP
