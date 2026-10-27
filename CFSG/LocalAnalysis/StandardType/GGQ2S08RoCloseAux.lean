module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08RoCloseDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoAbsorbPrime

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

noncomputable def ggQ2s08r4_diagLin {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    {N : ℕ} (M : GGQ2LDatum 3 Bs L x) (b : Module.Basis (Fin N) (ZMod 3) M.V)
    (ε : Fin N → ZMod 3) : M.V →ₗ[ZMod 3] M.V :=
  b.constr (ZMod 3) (fun i => ε i • b i)

theorem ggQ2s08r4_diagLin_basis {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    {N : ℕ} (M : GGQ2LDatum 3 Bs L x) (b : Module.Basis (Fin N) (ZMod 3) M.V)
    (ε : Fin N → ZMod 3) (i : Fin N) :
    ggQ2s08r4_diagLin M b ε (b i) = ε i • b i := by
  rw [ggQ2s08r4_diagLin, Module.Basis.constr_basis]

theorem ggQ2s08r4_diagLin_comp {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    {N : ℕ} (M : GGQ2LDatum 3 Bs L x) (b : Module.Basis (Fin N) (ZMod 3) M.V)
    (ε δ : Fin N → ZMod 3) (h : ∀ i, ε i * δ i = 1) :
    (ggQ2s08r4_diagLin M b ε).comp (ggQ2s08r4_diagLin M b δ) = LinearMap.id := by
  refine Module.Basis.ext b ?_
  intro i
  simp only [LinearMap.comp_apply, LinearMap.id_apply]
  rw [ggQ2s08r4_diagLin_basis, map_smul, ggQ2s08r4_diagLin_basis, smul_smul,
    mul_comm (δ i) (ε i), h i, one_smul]

noncomputable def ggQ2s08r4_diagEquiv {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    {N : ℕ} (M : GGQ2LDatum 3 Bs L x) (b : Module.Basis (Fin N) (ZMod 3) M.V)
    (ε : Fin N → ZMod 3) (h : ∀ i, ε i ≠ 0) : M.V ≃ₗ[ZMod 3] M.V :=
  LinearEquiv.ofLinear (ggQ2s08r4_diagLin M b ε) (ggQ2s08r4_diagLin M b (fun i => (ε i)⁻¹))
    (ggQ2s08r4_diagLin_comp M b ε (fun i => (ε i)⁻¹) (by
      intro i; exact mul_inv_cancel₀ (h i)))
    (ggQ2s08r4_diagLin_comp M b (fun i => (ε i)⁻¹) ε (by
      intro i; exact inv_mul_cancel₀ (h i)))

theorem ggQ2s08r4_diagEquiv_basis {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    {N : ℕ} (M : GGQ2LDatum 3 Bs L x) (b : Module.Basis (Fin N) (ZMod 3) M.V)
    (ε : Fin N → ZMod 3) (h : ∀ i, ε i ≠ 0) (i : Fin N) :
    ggQ2s08r4_diagEquiv M b ε h (b i) = ε i • b i := by
  rw [ggQ2s08r4_diagEquiv, LinearEquiv.ofLinear_apply, ggQ2s08r4_diagLin_basis]

noncomputable def ggQ2s08r4_singleSign {N : ℕ} (k : Fin N) : Fin N → ZMod 3 :=
  fun i => if i = k then -1 else 1

theorem ggQ2s08r4_singleSign_ne_zero {N : ℕ} (k : Fin N) (i : Fin N) :
    ggQ2s08r4_singleSign k i ≠ 0 := by
  unfold ggQ2s08r4_singleSign
  split_ifs <;> decide

theorem ggQ2s08r4_singleSign_prod {N : ℕ} (k : Fin N) :
    (∏ i : Fin N, ggQ2s08r4_singleSign k i) = -1 := by
  have h : (∏ i : Fin N, ggQ2s08r4_singleSign k i) =
      ∏ i ∈ (Finset.univ : Finset (Fin N)), (if i = k then (-1 : ZMod 3) else 1) := by
    simp [ggQ2s08r4_singleSign]
  rw [h, Finset.prod_ite_eq']
  simp

noncomputable def ggQ2s08r4_singleEquiv {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    {N : ℕ} (M : GGQ2LDatum 3 Bs L x) (b : Module.Basis (Fin N) (ZMod 3) M.V)
    (k : Fin N) : M.V ≃ₗ[ZMod 3] M.V :=
  ggQ2s08r4_diagEquiv M b (ggQ2s08r4_singleSign k) (ggQ2s08r4_singleSign_ne_zero k)

theorem ggQ2s08r4_singleEquiv_basis {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    {N : ℕ} (M : GGQ2LDatum 3 Bs L x) (b : Module.Basis (Fin N) (ZMod 3) M.V)
    (k i : Fin N) :
    ggQ2s08r4_singleEquiv M b k (b i) = ggQ2s08r4_singleSign k i • b i := by
  rw [ggQ2s08r4_singleEquiv, ggQ2s08r4_diagEquiv_basis]

theorem ggQ2s08r4_singleEquiv_basis_of_ne {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    {N : ℕ} (M : GGQ2LDatum 3 Bs L x) (b : Module.Basis (Fin N) (ZMod 3) M.V)
    (k i : Fin N) (hik : i ≠ k) :
    ggQ2s08r4_singleEquiv M b k (b i) = b i := by
  rw [ggQ2s08r4_singleEquiv_basis]
  simp [ggQ2s08r4_singleSign, hik]

theorem ggQ2s08r4_singleEquiv_basis_self {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    {N : ℕ} (M : GGQ2LDatum 3 Bs L x) (b : Module.Basis (Fin N) (ZMod 3) M.V)
    (k : Fin N) :
    ggQ2s08r4_singleEquiv M b k (b k) = -b k := by
  rw [ggQ2s08r4_singleEquiv_basis]
  simp [ggQ2s08r4_singleSign]
  exact neg_one_smul _ _

theorem ggQ2s08r4_diagLin_involutive {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    {N : ℕ} (M : GGQ2LDatum 3 Bs L x) (b : Module.Basis (Fin N) (ZMod 3) M.V)
    (ε : Fin N → ZMod 3) (hsq : ∀ i, ε i * ε i = 1) :
    (ggQ2s08r4_diagLin M b ε).comp (ggQ2s08r4_diagLin M b ε) = LinearMap.id := by
  refine Module.Basis.ext b ?_
  intro i
  simp only [LinearMap.comp_apply, LinearMap.id_apply]
  rw [ggQ2s08r4_diagLin_basis, map_smul, ggQ2s08r4_diagLin_basis, smul_smul, hsq i, one_smul]

theorem ggQ2s08r4_singleSign_sq {N : ℕ} (k i : Fin N) :
    ggQ2s08r4_singleSign k i * ggQ2s08r4_singleSign k i = 1 := by
  unfold ggQ2s08r4_singleSign
  split_ifs with h
  · have h1 : (-1 : ZMod 3) = 2 := by decide
    rw [h1]
    apply ZMod.val_injective (n := 3)
    rw [ZMod.val_mul]
    decide
  · norm_num

theorem ggQ2s08r4_singleEquiv_involutive {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    {N : ℕ} (M : GGQ2LDatum 3 Bs L x) (b : Module.Basis (Fin N) (ZMod 3) M.V)
    (k : Fin N) :
    ggQ2s08r4_singleEquiv M b k * ggQ2s08r4_singleEquiv M b k = 1 := by
  refine LinearEquiv.ext (R := ZMod 3) (M := M.V) fun v => ?_
  simp only [LinearEquiv.mul_apply, LinearEquiv.refl_apply]
  exact congrArg (fun e : M.V →ₗ[ZMod 3] M.V => e v)
    (ggQ2s08r4_diagLin_involutive M b (ggQ2s08r4_singleSign k)
      (ggQ2s08r4_singleSign_sq k))

end CFSG.StandardType

end
