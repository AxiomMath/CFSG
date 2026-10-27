module

public import CFSG.LocalAnalysis.StandardType.GGF4B3CoreRep
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelAut
import CFSG.LocalAnalysis.StandardType.GGSecFiveRootRefl
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabel
import CFSG.LocalAnalysis.StandardType.GGF4WeylMat
import CFSG.LocalAnalysis.StandardType.GGF4Rk2Core

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.StandardType.F4Model

private def f4CoordScale : Fin 4 → ℤ := ![2, 2, 1, 1]

private theorem sm_coord : ∀ i k j : Fin 4, (Sm i).toMat k j * f4CoordScale k =
    (if k = j then f4CoordScale k else 0) -
      (if k = i then f4CoordScale j * CartanMatrix.F₄ i j else 0) := by
  decide +kernel

private theorem det_cartanMatrix_F₄ : CartanMatrix.F₄.det = 1 := by
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, CartanMatrix.F₄, Matrix.submatrix,
    Fin.succAbove]

theorem exists_bstar_f4Coords {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {Bs : Subgroup G} (hEl : IsElemAbelian p Bs) (hNT : GGNoTransvection p Bs)
    (hcard : Nat.card ↥Bs ≤ p ^ 4) {A : Subgroup (MulAut ↥Bs)} (hind : A ≤ ggInduced ⊤ Bs)
    (e : CoxeterMatrix.F₄.Group ≃* ↥A)
    (he : ∀ i : Fin 4, GGIsReflection p ((e (CoxeterMatrix.F₄.simple i) : ↥A) : MulAut ↥Bs))
    (R : F4Rep CoxeterMatrix.F₄.Group) (hRs : ∀ i, R.s i = CoxeterMatrix.F₄.simple i) :
    ∃ Ψ : Multiplicative (Fin 4 → ZMod p) ≃* ↥Bs, ∀ (w : CoxeterMatrix.F₄.Group)
      (c : Fin 4 → ZMod p),
      ((e w : ↥A) : MulAut ↥Bs) (Ψ (Multiplicative.ofAdd c)) =
        Ψ (Multiplicative.ofAdd (((R.ρ w).map (Int.castRingHom (ZMod p))).mulVec c)) := by
  classical
  obtain ⟨V, _, _, ⟨ιV⟩⟩ := exists_ggLinData (p := p) hEl
  obtain ⟨h, α, hα, hrefl, hpair⟩ := SecFiveRootRefl.exists_cartan_pairing_of_iso hp2 hNT
    ggIntCartan_F₄ SecFiveRootRefl.entries_F₄ SecFiveRootRefl.cartanTree_F₄ e he
    (fun φ hφ => hind hφ) ιV
  have h2 : (2 : ZMod p) ≠ 0 := zmod_two_ne_zero hp2
  have hli : LinearIndependent (ZMod p) h := by
    refine linearIndependent_of_det_ne_zero h α ?_
    have hm : (Matrix.of fun i j => α i (h j)) =
        CartanMatrix.F₄.map (Int.castRingHom (ZMod p)) := by
      ext i j
      simp [hpair i j]
    rw [hm, show (CartanMatrix.F₄.map (Int.castRingHom (ZMod p))).det =
        Int.castRingHom (ZMod p) CartanMatrix.F₄.det from (RingHom.map_det _ _).symm,
      det_cartanMatrix_F₄, map_one]
    exact one_ne_zero
  have : Finite V := Finite.of_equiv _ ιV.toEquiv
  have : Fintype V := Fintype.ofFinite V
  have : Module.Finite (ZMod p) V := Module.Finite.of_finite
  have hrank : Module.finrank (ZMod p) V = 4 := by
    have hle : 4 ≤ Module.finrank (ZMod p) V := by
      simpa using hli.fintype_card_le_finrank
    have hcardV : Nat.card V = p ^ Module.finrank (ZMod p) V := by
      rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod p) (V := V),
        ZMod.card]
    have hcV : Nat.card V ≤ p ^ 4 := by
      rw [← Nat.card_congr ιV.toEquiv]
      exact hcard
    have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
    rw [hcardV] at hcV
    have := (Nat.pow_le_pow_iff_right hp1).mp hcV
    omega
  let bas : Module.Basis (Fin 4) (ZMod p) V :=
    basisOfLinearIndependentOfCardEqFinrank hli (by rw [hrank, Fintype.card_fin])
  have hbas : ∀ i, bas i = h i := fun i => by simp [bas]
  let δ : Fin 4 → ZMod p := fun j => (f4CoordScale j : ZMod p) * (2 : ZMod p)⁻¹
  have hδ : ∀ j, δ j ≠ 0 := by
    intro j
    refine mul_ne_zero ?_ (inv_ne_zero h2)
    fin_cases j <;> simp [f4CoordScale, h2]
  let bas' : Module.Basis (Fin 4) (ZMod p) V := bas.unitsSMul fun j => Units.mk0 (δ j) (hδ j)
  let Φ : (Fin 4 → ZMod p) ≃ₗ[ZMod p] V := bas'.equivFun.symm
  have hΦ : ∀ c, Φ c = ∑ j, (c j * δ j) • h j := by
    intro c
    simp only [Φ, Module.Basis.equivFun_symm_apply, bas', Module.Basis.unitsSMul_apply, hbas,
      Units.smul_mk0, smul_smul]
  have hΦs : ∀ (j : Fin 4) (a : ZMod p), Φ (Pi.single j a) = (a * δ j) • h j := by
    intro j a
    rw [hΦ, Finset.sum_eq_single j]
    · simp
    · intro k _ hk
      simp [hk]
    · simp
  let S : Fin 4 → Matrix (Fin 4) (Fin 4) (ZMod p) := fun i =>
    (Sm i).toMat.map (Int.castRingHom (ZMod p))
  have hsm : ∀ i k j : Fin 4, (((Sm i).toMat k j : ℤ) : ZMod p) * δ k =
      (if k = j then δ k else 0) -
        (if k = i then δ j * ((CartanMatrix.F₄ i j : ℤ) : ZMod p) else 0) := by
    intro i k j
    have hc : ((((Sm i).toMat k j * f4CoordScale k : ℤ) : ZMod p)) * (2 : ZMod p)⁻¹ =
        (((if k = j then f4CoordScale k else 0) -
          (if k = i then f4CoordScale j * CartanMatrix.F₄ i j else 0) : ℤ) : ZMod p) *
            (2 : ZMod p)⁻¹ := by
      rw [sm_coord i k j]
    simp only [δ]
    split_ifs at hc ⊢ <;> push_cast at hc <;> linear_combination hc
  have hsimple : ∀ (i : Fin 4) (c : Fin 4 → ZMod p),
      ggLin (p := p) ιV ((e (CoxeterMatrix.F₄.simple i) : ↥A) : MulAut ↥Bs) (Φ c) =
        Φ ((S i).mulVec c) := by
    intro i
    have hlin : (ggLin (p := p) ιV ((e (CoxeterMatrix.F₄.simple i) : ↥A) :
        MulAut ↥Bs)).toLinearMap ∘ₗ Φ.toLinearMap = Φ.toLinearMap ∘ₗ Matrix.mulVecLin (S i) := by
      refine LinearMap.pi_ext fun j a => ?_
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Matrix.mulVecLin_apply]
      have hmv : (S i).mulVec (Pi.single j a) = fun k => (S i) k j * a := by
        ext k
        simp [Matrix.mulVec, dotProduct, Pi.single_apply]
      rw [hrefl i, Module.reflection_apply, hΦs, hmv, hΦ]
      simp only [map_smul, smul_eq_mul, hpair]
      have hcoef : ∀ k, ((S i) k j * a) * δ k =
          (if k = j then a * δ j else 0) -
            (if k = i then a * δ j * ((CartanMatrix.F₄ i j : ℤ) : ZMod p) else 0) := by
        intro k
        have hk := hsm i k j
        have hSk : (S i) k j = (((Sm i).toMat k j : ℤ) : ZMod p) := rfl
        rw [hSk]
        by_cases h1 : k = j
        · subst h1
          by_cases h3 : k = i
          · subst h3
            rw [if_pos rfl, if_pos rfl] at hk
            rw [if_pos rfl, if_pos rfl]
            linear_combination a * hk
          · rw [if_pos rfl, if_neg h3] at hk
            rw [if_pos rfl, if_neg h3]
            linear_combination a * hk
        · by_cases h3 : k = i
          · rw [if_neg h1, if_pos h3] at hk
            rw [if_neg h1, if_pos h3]
            linear_combination a * hk
          · rw [if_neg h1, if_neg h3] at hk
            rw [if_neg h1, if_neg h3]
            linear_combination a * hk
      rw [Finset.sum_congr rfl fun k _ => by rw [hcoef k]]
      simp only [sub_smul, Finset.sum_sub_distrib, ite_smul, zero_smul, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
    intro c
    exact LinearMap.congr_fun hlin c
  have hall : ∀ (w : CoxeterMatrix.F₄.Group) (c : Fin 4 → ZMod p),
      ggLin (p := p) ιV ((e w : ↥A) : MulAut ↥Bs) (Φ c) =
        Φ (((R.ρ w).map (Int.castRingHom (ZMod p))).mulVec c) := by
    intro w
    have hw : w ∈ Subgroup.closure (Set.range fun k => R.s (id k)) := by
      rw [show (Set.range fun k => R.s (id k)) = Set.range R.s from rfl, R.gen]
      exact Subgroup.mem_top w
    obtain ⟨l, rfl⟩ := R.exists_word_of_mem_closure id hw
    clear hw
    induction l with
    | nil =>
      intro c
      simp [F4Rep.wd]
    | cons k l ih =>
      intro c
      have hwd : R.wd ((k :: l).map id) = R.s k * R.wd (l.map id) := by simp [F4Rep.wd]
      rw [hwd, map_mul, Subgroup.coe_mul, map_mul, LinearEquiv.mul_apply, ih, hRs k, hsimple,
        map_mul, Matrix.map_mul, ← Matrix.mulVec_mulVec]
      congr 2
      rw [← hRs k, R.hs k]
  let Ψ : Multiplicative (Fin 4 → ZMod p) ≃* ↥Bs :=
    (AddEquiv.toMultiplicative (Φ.toAddEquiv.trans ιV.symm)).trans (MulEquiv.refl _)
  refine ⟨Ψ, fun w c => ?_⟩
  have h1 := hall w c
  rw [ggLin_apply] at h1
  apply_fun (fun v => Additive.toMul (ιV.symm v)) at h1
  simp only [AddEquiv.symm_apply_apply, toMul_ofMul] at h1
  exact h1

end CFSG.StandardType

end
