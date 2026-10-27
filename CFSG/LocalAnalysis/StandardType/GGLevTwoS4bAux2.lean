module

public import CFSG.LocalAnalysis.StandardType.GGLevTwoS4bAux1
public import CFSG.LocalAnalysis.StandardType.GGWeylSimpleSystemsConj

public section

namespace CFSG.StandardType.LevTwo

open CFSG CFSG.Assembly CFSG.LieType.RootSystem LevTwoType
open CFSG.StandardType.S2MathFi1451 CFSG.StandardType.SecFiveRootRefl

attribute [local irreducible] rRefl levTwoS4b_beta levTwoS4b_w levTwoS4b_i levTwoS4b_eL

noncomputable abbrev levTwoS4b_a {G : Type} [Group G] [Finite G] (c : levTwoS4b_Ctx G)
    (k l : c.ιL) : ℤ :=
  coroot c.T.root (levTwoS4b_i c k)
    (weylAction c.T.rootFT (levTwoS4b_w c k)⁻¹
      (weylAction c.T.rootFT (levTwoS4b_w c l) (Pi.single (levTwoS4b_i c l) 1)))

theorem levTwoS4b_a_self {G : Type} [Group G] [Finite G] (c : levTwoS4b_Ctx G) (k : c.ιL) :
    levTwoS4b_a c k k = 2 := by
  rw [levTwoS4b_a, weylAction_inv_apply_apply, coroot_single]
  exact c.T.rootFT.apply_self _

theorem levTwoS4b_beta_ne {G : Type} [Group G] [Finite G] (c : levTwoS4b_Ctx G) {k l : c.ιL}
    (hkl : k ≠ l) :
    rRefl c.T.rootFT (levTwoS4b_beta c k) ≠ rRefl c.T.rootFT (levTwoS4b_beta c l) := by
  intro h
  have h2 : levTwoS4b_eL c (c.ML.simple k) = levTwoS4b_eL c (c.ML.simple l) := by
    apply Subtype.ext
    have hk := levTwoS4b_beta_rho c k
    have hl := levTwoS4b_beta_rho c l
    rw [h] at hk
    exact hk.symm.trans hl
  exact hkl (CoxeterSystem.simple_injective c.ML.toCoxeterSystem
    (by simpa only [CoxeterMatrix.toCoxeterSystem_simple] using (levTwoS4b_eL c).injective h2))

theorem levTwoS4b_w_ne {G : Type} [Group G] [Finite G] (c : levTwoS4b_Ctx G) {k l : c.ιL}
    (hkl : k ≠ l) :
    levTwoS4b_w c k * sg c.T.rootFT (levTwoS4b_i c k) * (levTwoS4b_w c k)⁻¹ ≠
      levTwoS4b_w c l * sg c.T.rootFT (levTwoS4b_i c l) * (levTwoS4b_w c l)⁻¹ := by
  rw [← levTwoS4b_rRefl_eq c k, ← levTwoS4b_rRefl_eq c l]
  exact levTwoS4b_beta_ne c hkl

theorem levTwoS4b_pairing_abstract {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    {R : Matrix ι ι ℤ} (hR : TauCeti.IsFiniteType R)
    {C : Matrix κ κ ℤ} (hC : TauCeti.IsFiniteType C)
    {M : CoxeterMatrix κ} (hcox : coxeterMatrix hC = M)
    {w u : Wg hR} {i j : ι} {k l : κ} (hkl : k ≠ l)
    (hne : w * sg hR i * w⁻¹ ≠ u * sg hR j * u⁻¹)
    (hord : orderOf (w * sg hR i * w⁻¹ * (u * sg hR j * u⁻¹)) = M.M k l) :
    coroot R i (weylAction hR w⁻¹ (weylAction hR u (Pi.single j 1))) *
      coroot R j (weylAction hR u⁻¹ (weylAction hR w (Pi.single i 1))) = C k l * C l k := by
  obtain ⟨hmem, -, hord'⟩ := orderOf_conj_mul_conj hR hne
  have hmemC : C k l * C l k ∈ ({0, 1, 2, 3} : Set ℤ) := hC.apply_mul_apply_mem_of_ne hkl
  have hM : M.M k l = TauCeti.coxeterOrder (C k l * C l k) := by
    rw [← hcox]
    exact TauCeti.coxeterMatrixOfCartanMatrix_apply C hC.apply_self
      (fun i j h => hC.apply_mul_apply_mem_of_ne h) k l
  apply coxeterOrder_injOn hmem hmemC
  rw [← hord', hord, hM]

theorem levTwoS4b_w_order {G : Type} [Group G] [Finite G] (c : levTwoS4b_Ctx G) (k l : c.ιL) :
    orderOf (levTwoS4b_w c k * sg c.T.rootFT (levTwoS4b_i c k) * (levTwoS4b_w c k)⁻¹ *
      (levTwoS4b_w c l * sg c.T.rootFT (levTwoS4b_i c l) * (levTwoS4b_w c l)⁻¹)) =
      c.ML.M k l := by
  have hρk : c.ρ (levTwoS4b_w c k * sg c.T.rootFT (levTwoS4b_i c k) * (levTwoS4b_w c k)⁻¹) =
      Subgroup.inclusion c.hAL (levTwoS4b_eL c (c.ML.simple k)) := by
    rw [← levTwoS4b_rRefl_eq c k]
    apply Subtype.ext
    exact levTwoS4b_beta_rho c k
  have hρl : c.ρ (levTwoS4b_w c l * sg c.T.rootFT (levTwoS4b_i c l) * (levTwoS4b_w c l)⁻¹) =
      Subgroup.inclusion c.hAL (levTwoS4b_eL c (c.ML.simple l)) := by
    rw [← levTwoS4b_rRefl_eq c l]
    apply Subtype.ext
    exact levTwoS4b_beta_rho c l
  have hinc : Function.Injective (Subgroup.inclusion c.hAL) := by
    intro x y h
    exact Subtype.ext (congrArg (fun z : ↥c.A => (z : MulAut ↥c.Bs)) h)
  have h1 : levTwoS4b_w c k * sg c.T.rootFT (levTwoS4b_i c k) * (levTwoS4b_w c k)⁻¹ *
      (levTwoS4b_w c l * sg c.T.rootFT (levTwoS4b_i c l) * (levTwoS4b_w c l)⁻¹) =
      c.ρ.symm (Subgroup.inclusion c.hAL (levTwoS4b_eL c (c.ML.simple k)) *
        Subgroup.inclusion c.hAL (levTwoS4b_eL c (c.ML.simple l))) := by
    apply c.ρ.injective
    rw [MulEquiv.apply_symm_apply, map_mul, hρk, hρl]
  have h2 : Subgroup.inclusion c.hAL (levTwoS4b_eL c (c.ML.simple k)) *
      Subgroup.inclusion c.hAL (levTwoS4b_eL c (c.ML.simple l)) =
      Subgroup.inclusion c.hAL ((levTwoS4b_eL c) (c.ML.simple k * c.ML.simple l)) := by
    rw [← map_mul]
    congr 1
    rw [map_mul]
  have h3 : orderOf ((levTwoS4b_eL c) (c.ML.simple k * c.ML.simple l)) = c.ML.M k l := by
    rw [MulEquiv.orderOf_eq]
    simpa only [CoxeterMatrix.toCoxeterSystem_simple] using
      CoxeterSystem.orderOf_simple_mul_simple c.ML.toCoxeterSystem k l
  have h4 : orderOf (Subgroup.inclusion c.hAL
      ((levTwoS4b_eL c) (c.ML.simple k * c.ML.simple l))) = c.ML.M k l := by
    rw [orderOf_injective (Subgroup.inclusion c.hAL) hinc]
    exact h3
  rw [h1, MulEquiv.orderOf_eq, h2, h4]

theorem levTwoS4b_a_offdiag {G : Type} [Group G] [Finite G] (c : levTwoS4b_Ctx G)
    (C : Matrix c.ιL c.ιL ℤ) (hC : TauCeti.IsFiniteType C)
    (hcox : coxeterMatrix hC = c.ML) (k l : c.ιL) (hkl : k ≠ l) :
    levTwoS4b_a c k l * levTwoS4b_a c l k = C k l * C l k :=
  levTwoS4b_pairing_abstract (R := c.T.root) (C := C) (M := c.ML) (hR := c.T.rootFT)
    (w := levTwoS4b_w c k) (u := levTwoS4b_w c l)
    (i := levTwoS4b_i c k) (j := levTwoS4b_i c l) (k := k) (l := l)
    hC hcox hkl (levTwoS4b_w_ne c hkl) (levTwoS4b_w_order c k l)

theorem levTwoS4b_a_zero_iff {G : Type} [Group G] [Finite G] (c : levTwoS4b_Ctx G) {k l : c.ιL}
    (hkl : k ≠ l) : levTwoS4b_a c k l = 0 ↔ levTwoS4b_a c l k = 0 :=
  (orderOf_conj_mul_conj c.T.rootFT (levTwoS4b_w_ne c hkl)).2.1

end CFSG.StandardType.LevTwo
