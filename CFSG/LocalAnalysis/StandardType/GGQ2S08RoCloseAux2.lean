module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08RoCloseAux
public import CFSG.LocalAnalysis.StandardType.GGQTwoPairsPrime
public import CFSG.LocalAnalysis.StandardType.GGOneFiveNbr

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly


noncomputable def ggQ2s08r4_basis
    {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
     {N : ℕ} (M : GGQ2LDatum 3 Bs L x) (f : Fin N → M.V)
    (hf : GGQ2S08ROFrame M f) : Module.Basis (Fin N) (ZMod 3) M.V :=
  Module.Basis.mk hf.1 (le_of_eq hf.2.1.symm)

theorem ggQ2s08r4_basis_apply
    {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
     {N : ℕ} (M : GGQ2LDatum 3 Bs L x) (f : Fin N → M.V)
    (hf : GGQ2S08ROFrame M f) (i : Fin N) :
    ggQ2s08r4_basis M f hf i = f i :=
  Module.Basis.mk_apply _ _ _

@[expose] noncomputable def ggQ2s08r4_b
    {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
     {N : ℕ} (M : GGQ2LDatum 3 Bs L x) (f : Fin N → M.V)
    (j : Fin N) : ↥Bs :=
  Additive.toMul (M.model.symm (f j))

theorem ggQ2s08r4_b_model
    {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
     {N : ℕ} (M : GGQ2LDatum 3 Bs L x) (f : Fin N → M.V) (j : Fin N) :
    M.model (Additive.ofMul (ggQ2s08r4_b M f j)) = f j := by
  simp [ggQ2s08r4_b]

theorem ggQ2s08r4_model_x
    {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
     {N : ℕ} (M : GGQ2LDatum 3 Bs L x) (f : Fin N → M.V)
    (hf : GGQ2S08ROFrame M f) :
    M.model (Additive.ofMul ⟨x, M.hx⟩) = ∑ i, f i := by
  simpa only [GGQ2LDatum.xV] using hf.2.2.1

theorem ggQ2s08r4_repr_model_x
    {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
     {N : ℕ} (M : GGQ2LDatum 3 Bs L x) (f : Fin N → M.V)
    (hf : GGQ2S08ROFrame M f) (i : Fin N) :
    (ggQ2s08r4_basis M f hf).repr
      (M.model (Additive.ofMul (⟨x, M.hx⟩ : ↥Bs))) i = (1 : ZMod 3) := by
  rw [ggQ2s08r4_model_x M f hf]
  have hsum : (∑ j, f j) = ∑ j, ggQ2s08r4_basis M f hf j :=
    Finset.sum_congr rfl fun j _ => (ggQ2s08r4_basis_apply M f hf j).symm
  rw [hsum, map_sum, Finsupp.finset_sum_apply]
  simp only [Module.Basis.repr_self, Finsupp.single_apply]
  rw [Finset.sum_ite_eq']
  simp

theorem ggQ2s08r4_singleEquiv_apply
    {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
     {N : ℕ} (M : GGQ2LDatum 3 Bs L x)
    (b : Module.Basis (Fin N) (ZMod 3) M.V) (k : Fin N) (v : M.V) :
    ggQ2s08r4_singleEquiv M b k v = v + (b.repr v k) • b k := by
  have hfun : (ggQ2s08r4_singleEquiv M b k : M.V →ₗ[ZMod 3] M.V) =
      LinearMap.id + (b.coord k).smulRight (b k) := by
    refine Module.Basis.ext b (fun i => ?_)
    change ggQ2s08r4_singleEquiv M b k (b i) =
      (LinearMap.id + (b.coord k).smulRight (b k) : M.V →ₗ[ZMod 3] M.V) (b i)
    simp only [LinearMap.add_apply, LinearMap.id_apply, LinearMap.smulRight_apply,
      Module.Basis.coord_apply, Module.Basis.repr_self]
    by_cases h : i = k
    · rw [h, ggQ2s08r4_singleEquiv_basis_self, Finsupp.single_eq_same]
      rw [one_smul, ← two_smul (ZMod 3) (b k), ← neg_one_smul (ZMod 3) (b k)]
      exact congrArg (fun c : ZMod 3 => c • b k)
        (show (-1 : ZMod 3) = 2 by decide)
    · rw [ggQ2s08r4_singleEquiv_basis_of_ne M b k i h,
        Finsupp.single_eq_of_ne (Ne.symm h)]
      simp
  calc ggQ2s08r4_singleEquiv M b k v
      = (LinearMap.id + (b.coord k).smulRight (b k) : M.V →ₗ[ZMod 3] M.V) v :=
        congrArg (fun (g : M.V →ₗ[ZMod 3] M.V) => g v) hfun
    _ = v + (b.repr v k) • b k := by
        simp only [LinearMap.add_apply, LinearMap.id_apply, LinearMap.smulRight_apply,
          Module.Basis.coord_apply]

theorem ggQ2s08r4_singleEquiv_eq_self
    {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
     {N : ℕ} (M : GGQ2LDatum 3 Bs L x)
    (b : Module.Basis (Fin N) (ZMod 3) M.V) (k : Fin N) {v : M.V}
    (hv : b.repr v k = 0) :
    ggQ2s08r4_singleEquiv M b k v = v := by
  rw [ggQ2s08r4_singleEquiv_apply, hv, zero_smul, add_zero]

theorem ggQ2s08r4_singleSign_mul_prod
     {N : ℕ} (j k : Fin N) :
    (∏ i, ggQ2s08r4_singleSign j i * ggQ2s08r4_singleSign k i) = 1 := by
  rw [Finset.prod_mul_distrib, ggQ2s08r4_singleSign_prod, ggQ2s08r4_singleSign_prod]
  decide

theorem ggQ2s08r4_monoEven_mul_single
    {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
     {N : ℕ} (M : GGQ2LDatum 3 Bs L x) (f : Fin N → M.V)
    (hf : GGQ2S08ROFrame M f) (j k : Fin N) :
    GGQ2S08MonoEven f (ggQ2s08r4_singleEquiv M (ggQ2s08r4_basis M f hf) k *
      ggQ2s08r4_singleEquiv M (ggQ2s08r4_basis M f hf) j) := by
  refine ⟨Equiv.refl (Fin N),
    fun i => ggQ2s08r4_singleSign k i * ggQ2s08r4_singleSign j i,
    fun i => mul_ne_zero (ggQ2s08r4_singleSign_ne_zero k i)
      (ggQ2s08r4_singleSign_ne_zero j i),
    ggQ2s08r4_singleSign_mul_prod k j, fun i => ?_⟩
  rw [LinearEquiv.mul_apply, Equiv.refl_apply, ← ggQ2s08r4_basis_apply M f hf i,
    ggQ2s08r4_singleEquiv_basis, map_smul, ggQ2s08r4_singleEquiv_basis, smul_smul,
    mul_comm (ggQ2s08r4_singleSign j i) (ggQ2s08r4_singleSign k i),
    ggQ2s08r4_basis_apply]

theorem ggQ2s08r4_monoEven_diag
    {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
     {N : ℕ} (M : GGQ2LDatum 3 Bs L x) (f : Fin N → M.V)
    (hf : GGQ2S08ROFrame M f) (s : Fin N → ZMod 3) (hs : ∀ i, s i ≠ 0)
    (hprod : ∏ i, s i = 1) :
    GGQ2S08MonoEven f
      (ggQ2s08r4_diagEquiv M (ggQ2s08r4_basis M f hf) s hs) := by
  refine ⟨Equiv.refl (Fin N), s, hs, hprod, fun i => ?_⟩
  rw [Equiv.refl_apply, ← ggQ2s08r4_basis_apply M f hf i, ggQ2s08r4_diagEquiv_basis]

end CFSG.StandardType

end
