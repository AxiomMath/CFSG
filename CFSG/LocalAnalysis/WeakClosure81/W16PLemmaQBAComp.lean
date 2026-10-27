module

public import CFSG.LocalAnalysis.WeakClosure81.W16PLemmaQSz

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open Matrix

private lemma map_zero_of_add {F G : Type} [AddZeroClass F] [Group G] (θ : F → G)
    (hθadd : ∀ v v', θ (v + v') = θ v * θ v') : θ 0 = 1 := by
  have h : θ 0 * 1 = θ 0 * θ 0 := by simpa only [mul_one, add_zero] using hθadd 0 0
  exact (mul_left_cancel h).symm

private lemma map_neg_of_add {F G : Type} [AddGroup F] [Group G] (θ : F → G)
    (hθadd : ∀ v v', θ (v + v') = θ v * θ v') (v : F) : θ (-v) = (θ v)⁻¹ := by
  have h0 : θ 0 = 1 := map_zero_of_add θ hθadd
  have h : θ (-v) * θ v = 1 := by rw [← hθadd (-v) v, neg_add_cancel, h0]
  calc θ (-v) = θ (-v) * 1 := (mul_one _).symm
    _ = θ (-v) * (θ v * (θ v)⁻¹) := by rw [mul_inv_cancel]
    _ = (θ (-v) * θ v) * (θ v)⁻¹ := (mul_assoc _ _ _).symm
    _ = 1 * (θ v)⁻¹ := by rw [h]
    _ = (θ v)⁻¹ := one_mul _

private lemma map_sub_of_add {F G : Type} [AddGroup F] [Group G] (θ : F → G)
    (hθadd : ∀ v v', θ (v + v') = θ v * θ v') (u v : F) :
    θ (u - v) = θ u * (θ v)⁻¹ := by
  rw [sub_eq_add_neg, hθadd, map_neg_of_add θ hθadd]

private lemma invFun_map_mul {F G : Type} [AddGroup F] [Nonempty F] [Group G] (θ : F → G)
    (hθadd : ∀ v v', θ (v + v') = θ v * θ v') (hθinj : Function.Injective θ) (u v : F) :
    Function.invFun θ (θ u * θ v) = u + v := by
  have h1 : θ (Function.invFun θ (θ u * θ v)) = θ u * θ v :=
    Function.invFun_eq ⟨u + v, hθadd u v⟩
  exact hθinj (h1.trans (hθadd u v).symm)

private lemma invFun_map_of_mem {F G : Type} [Nonempty F] [Group G] (θ : F → G) {W : Subgroup G}
    (hθW : Set.range θ = (W : Set G)) (w : G) (hw : w ∈ W) :
    θ (Function.invFun θ w) = w :=
  Function.invFun_eq (by
    change w ∈ Set.range θ
    rw [hθW]
    exact hw)

theorem exists_mem_of_natural_crossedHom {G : Type} [Group G]
    {a : ℕ} (ha : 1 ≤ a) {X W : Subgroup G} (ψ : ↥X →* ↥(Sz a)) (hψs : Function.Surjective ψ)
    (θ : (Fin 4 → GaloisField 2 (2 * a + 1)) → G) (hθadd : ∀ v v', θ (v + v') = θ v * θ v')
    (hθinj : Function.Injective θ) (hθW : Set.range θ = (W : Set G))
    (hθψ : ∀ (x : ↥X) (v : Fin 4 → GaloisField 2 (2 * a + 1)),
      θ ((((ψ x : ↥(Sz a)) : GL (Fin 4) (GaloisField 2 (2 * a + 1))) :
        Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * a + 1))) *ᵥ v) = x * θ v * x⁻¹)
    {V₁ : Subgroup ↥X} (hV₁ : IsElemAbelian 2 (V₁.map ψ))
    (hV₁card : Nat.card (V₁.map ψ) = 2 ^ (2 * a + 1))
    {d : G → G} (hdW : ∀ x ∈ X, d x ∈ W)
    (hd : ∀ x ∈ X, ∀ y ∈ X, d (x * y) = d x * (x * d y * x⁻¹))
    (hdK : ∀ y ∈ ψ.ker, d (y : G) = 1) (hdV : ∀ v ∈ V₁, d (v : G) = 1) :
    ∃ w ∈ W, ∀ x ∈ X, d x = x * w * x⁻¹ * w⁻¹ := by
  classical
  let D : ↥(Sz a) → (Fin 4 → GaloisField 2 (2 * a + 1)) :=
    fun g => Function.invFun θ (d (((Function.surjInv hψs g : ↥X) : G)))
  have hDψ : ∀ x : ↥X, D (ψ x) = Function.invFun θ (d (x : G)) := by
    intro x
    set y : ↥X := Function.surjInv hψs (ψ x) with hy_def
    have hy : ψ y = ψ x := Function.surjInv_eq hψs (ψ x)
    have hk : (y⁻¹ * x : ↥X) ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hy, inv_mul_cancel]
    have hcoe : (y : G) * (((y⁻¹ * x : ↥X) : G)) = (x : G) := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
    have hdx : d (x : G) = d (y : G) := by
      have h := hd (y : G) y.2 (((y⁻¹ * x : ↥X) : G)) ((y⁻¹ * x : ↥X)).2
      rw [hcoe, hdK _ hk] at h
      simpa using h
    dsimp only [D]
    rw [← hy_def, hdx]
  have hDmul : ∀ g g' : ↥(Sz a),
      D (g * g') = D g +
        (((g : GL (Fin 4) (GaloisField 2 (2 * a + 1))) :
          Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * a + 1))) *ᵥ D g') := by
    intro g g'
    set x : ↥X := Function.surjInv hψs g with hx_def
    set x' : ↥X := Function.surjInv hψs g' with hx'_def
    have hx : ψ x = g := Function.surjInv_eq hψs g
    have hx' : ψ x' = g' := Function.surjInv_eq hψs g'
    have hDg : D g = Function.invFun θ (d (x : G)) := by rw [← hx, hDψ x]
    have hDg' : D g' = Function.invFun θ (d (x' : G)) := by rw [← hx', hDψ x']
    have h1 : θ (Function.invFun θ (d (x : G))) = d (x : G) :=
      invFun_map_of_mem θ hθW _ (hdW (x : G) x.2)
    have h1' : θ (Function.invFun θ (d (x' : G))) = d (x' : G) :=
      invFun_map_of_mem θ hθW _ (hdW (x' : G) x'.2)
    have h2 : θ ((((ψ x : ↥(Sz a)) : GL (Fin 4) (GaloisField 2 (2 * a + 1))) :
        Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * a + 1))) *ᵥ
          Function.invFun θ (d (x' : G))) = (x : G) * d (x' : G) * (x : G)⁻¹ := by
      have hh := hθψ x (Function.invFun θ (d (x' : G)))
      rwa [h1'] at hh
    have hcross : Function.invFun θ (d (x : G) * ((x : G) * d (x' : G) * (x : G)⁻¹)) =
        Function.invFun θ (d (x : G)) + ((((ψ x : ↥(Sz a)) :
          GL (Fin 4) (GaloisField 2 (2 * a + 1))) :
          Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * a + 1))) *ᵥ
            Function.invFun θ (d (x' : G))) := by
      have hmul : θ (Function.invFun θ (d (x : G))) *
          θ ((((ψ x : ↥(Sz a)) : GL (Fin 4) (GaloisField 2 (2 * a + 1))) :
            Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * a + 1))) *ᵥ
              Function.invFun θ (d (x' : G))) =
          d (x : G) * ((x : G) * d (x' : G) * (x : G)⁻¹) := by
        rw [h1, h2]
      rw [← hmul]
      exact invFun_map_mul θ hθadd hθinj _ _
    have hgg : D (g * g') =
        Function.invFun θ (d (x : G) * ((x : G) * d (x' : G) * (x : G)⁻¹)) := by
      have hthis : g * g' = ψ (x * x') := by rw [map_mul, hx, hx']
      rw [hthis, hDψ (x * x')]
      congr 1
      rw [Subgroup.coe_mul, hd (x : G) x.2 (x' : G) x'.2]
    rw [hgg, hDg, hDg', ← hx]
    exact hcross
  have hDZ : ∀ z ∈ V₁.map ψ, D z = 0 := by
    intro z hz
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hz
    rw [hDψ v, hdV v hv]
    have h0 : θ 0 = 1 := map_zero_of_add θ hθadd
    rw [← h0]
    exact Function.leftInverse_invFun hθinj 0
  obtain ⟨n, _hnfix, hnsub⟩ := exists_eq_mulVec_sub_of_sz ha hV₁ hV₁card hDmul hDZ
  refine ⟨θ n, ?_, ?_⟩
  · show θ n ∈ (W : Set G)
    rw [← hθW]
    exact ⟨n, rfl⟩
  · intro x hx
    let xX : ↥X := ⟨x, hx⟩
    have key : d x = θ ((((ψ xX : ↥(Sz a)) : GL (Fin 4) (GaloisField 2 (2 * a + 1))) :
        Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * a + 1))) *ᵥ n - n) := by
      rw [← invFun_map_of_mem θ hθW (d x) (hdW x hx), ← hDψ xX]
      exact congrArg θ (hnsub (ψ xX))
    rw [key, map_sub_of_add θ hθadd, hθψ xX n]
    rfl

end CFSG.LocalAnalysis.WeakClosure81

end
