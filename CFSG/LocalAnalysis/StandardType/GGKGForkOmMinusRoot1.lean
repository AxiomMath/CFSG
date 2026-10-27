module

public import CFSG.LocalAnalysis.StandardType.GGKGForkLayerGen
public import CFSG.LocalAnalysis.StandardType.GGOmegaMinusRootGenWeyl
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySpCoord

public section

namespace CFSG.StandardType

open CFSG.SeitzReduction CFSG.SeitzReduction.SymplecticPilot SpCoord Multiplicative TableBSymp

abbrev ggKGOmM_Idx (m : ℕ) : Type := Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2

private theorem ggKGOmM_exists_ne_zero_col {K : Type} [Field K] {ι : Type} [Fintype ι]
    [DecidableEq ι] (g : GL ι K) (x : ι) : ∃ y, (g : Matrix ι ι K) y x ≠ 0 := by
  by_contra h
  push Not at h
  have h1 := congrFun (congrFun g.inv_mul x) x
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at h1
  simp [h] at h1

private theorem ggKGOmM_weight_eq_of_mul_eq {K : Type} [Field K] {m : ℕ} {t t' : Fin m → Kˣ}
    {g : GL (ggKGOmM_Idx m) K} (h : g * kOmMDiag K m t = kOmMDiag K m t' * g)
    {x y : ggKGOmM_Idx m} (hxy : (g : Matrix (ggKGOmM_Idx m) (ggKGOmM_Idx m) K) y x ≠ 0) :
    kOmMWeight K m t x = kOmMWeight K m t' y := by
  have e := congrArg (fun g : GL (ggKGOmM_Idx m) K =>
    (g : Matrix (ggKGOmM_Idx m) (ggKGOmM_Idx m) K) y x) h
  simp only [Units.val_mul, kOmMDiag_coe, Matrix.mul_diagonal, Matrix.diagonal_mul] at e
  rw [mul_comm (kOmMWeight K m t' y) ((g : Matrix (ggKGOmM_Idx m) (ggKGOmM_Idx m) K) y x)] at e
  exact mul_left_cancel₀ hxy e

theorem ggKGOmM_monomial_tail {K : Type} [Field K] {m p : ℕ} {ζ : Kˣ} (hp : p.Prime)
    (hζ : ζ ^ p = 1) (hζo : orderOf ζ = p) (g : GL (ggKGOmM_Idx m) K)
    (u : MulAut (Fin m → Multiplicative (ZMod p)))
    (hcomm : ∀ f, g * omMinusTorusGL (K := K) (m := m) hζ f =
      omMinusTorusGL (K := K) (m := m) hζ (u f) * g) :
    ∃ (j : Fin m → Fin m) (ε : Fin m → ZMod p), (∀ i, ε i = 1 ∨ ε i = -1) ∧
      ∀ f i, toAdd (u f (j i)) = ε i * toAdd (f i) := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have key : ∀ i : Fin m, ∃ (j : Fin m) (ε : ZMod p), (ε = 1 ∨ ε = -1) ∧
      ∀ f : Fin m → Multiplicative (ZMod p), toAdd (u f j) = ε * toAdd (f i) := by
    intro i
    obtain ⟨y, hy⟩ := ggKGOmM_exists_ne_zero_col g (Sum.inl i)
    have hnot_tail : ∀ jj : Fin 2, y ≠ Sum.inr (Sum.inr jj) := by
      intro jj hyy
      have hw := ggKGOmM_weight_eq_of_mul_eq
        (t := omMinusTorusParam m hζ (Pi.mulSingle i (ofAdd (1 : ZMod p))))
        (t' := omMinusTorusParam m hζ (u (Pi.mulSingle i (ofAdd (1 : ZMod p)))))
        (by rw [← omMinusTorusGL_apply, ← omMinusTorusGL_apply]; exact hcomm _)
        (x := Sum.inl i) (y := Sum.inr (Sum.inr jj)) (by simpa [hyy] using hy)
      rw [kOmMWeight_inl, kOmMWeight_inr_inr, omMinusTorusParam_apply,
        Pi.mulSingle_eq_same] at hw
      have hEq1 : (zmodPowHom hζ (ofAdd (1 : ZMod p)) : Kˣ) = 1 := Units.ext hw
      have h2 := (TableBSymp.zmodPowHom_eq_one_iff hζ hζo).mp hEq1
      have h3 : (1 : ZMod p) = 0 := by
        simpa using congrArg Multiplicative.toAdd h2
      exact SpCoord.coord_zero_ne_one hp h3.symm
    rcases y with i' | i' | jj
    ·
      refine ⟨i', 1, Or.inl rfl, fun f => ?_⟩
      have hw := ggKGOmM_weight_eq_of_mul_eq
        (t := omMinusTorusParam m hζ f)
        (t' := omMinusTorusParam m hζ (u f))
        (by rw [← omMinusTorusGL_apply, ← omMinusTorusGL_apply]; exact hcomm f)
        (x := Sum.inl i) (y := Sum.inl i') hy
      rw [kOmMWeight_inl, kOmMWeight_inl, omMinusTorusParam_apply,
        omMinusTorusParam_apply] at hw
      have hEq : zmodPowHom hζ (f i) = zmodPowHom hζ (u f i') := Units.ext hw
      have h1 : zmodPowHom hζ (f i * (u f i')⁻¹) = 1 := by
        rw [map_mul, map_inv, hEq, mul_inv_cancel]
      have h2 : f i * (u f i')⁻¹ = 1 := (TableBSymp.zmodPowHom_eq_one_iff hζ hζo).mp h1
      have h3 : u f i' = f i := (mul_inv_eq_one.mp h2).symm
      rw [h3, one_mul]
    ·
      refine ⟨i', -1, Or.inr rfl, fun f => ?_⟩
      have hw := ggKGOmM_weight_eq_of_mul_eq
        (t := omMinusTorusParam m hζ f)
        (t' := omMinusTorusParam m hζ (u f))
        (by rw [← omMinusTorusGL_apply, ← omMinusTorusGL_apply]; exact hcomm f)
        (x := Sum.inl i) (y := Sum.inr (Sum.inl i')) hy
      rw [kOmMWeight_inl, kOmMWeight_inr_inl, omMinusTorusParam_apply,
        omMinusTorusParam_apply] at hw
      have hEq : zmodPowHom hζ (f i) = (zmodPowHom hζ (u f i'))⁻¹ := Units.ext hw
      have h1 : zmodPowHom hζ (f i * u f i') = 1 := by
        rw [map_mul, hEq, inv_mul_cancel]
      have h2 : f i * u f i' = 1 := (TableBSymp.zmodPowHom_eq_one_iff hζ hζo).mp h1
      have h3 : u f i' = (f i)⁻¹ :=
        calc u f i' = 1 * u f i' := (one_mul _).symm
          _ = ((f i)⁻¹ * f i) * u f i' := by rw [inv_mul_cancel, one_mul]
          _ = (f i)⁻¹ * (f i * u f i') := by rw [mul_assoc]
          _ = (f i)⁻¹ * 1 := by rw [h2]
          _ = (f i)⁻¹ := mul_one _
      rw [h3, toAdd_inv, neg_one_mul]
    · exact absurd rfl (hnot_tail jj)
  choose j ε hε hrel using key
  exact ⟨j, ε, hε, fun f i => hrel i f⟩

theorem ggKGOmM_isSignedPerm_of_monomial {p m : ℕ} (hp : p.Prime)
    {u : MulAut (Fin m → Multiplicative (ZMod p))} {j : Fin m → Fin m} {ε : Fin m → ZMod p}
    (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (hrel : ∀ f i, toAdd (u f (j i)) = ε i * toAdd (f i)) : SpCoord.IsSignedPerm ⇑u := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hjinj : Function.Injective j := by
    intro i i' hij
    by_contra hne
    have h1 := hrel (Pi.mulSingle i (ofAdd (1 : ZMod p))) i
    have h2 := hrel (Pi.mulSingle i (ofAdd (1 : ZMod p))) i'
    rw [SpCoord.toAdd_mulSingle, if_pos rfl, mul_one] at h1
    rw [SpCoord.toAdd_mulSingle, if_neg (Ne.symm hne), mul_zero] at h2
    rw [hij] at h1
    exact SpCoord.coord_sign_ne_zero hp (hε i) (h1.symm.trans h2)
  have hbij : Function.Bijective j :=
    ⟨hjinj, Finite.injective_iff_surjective.mp hjinj⟩
  refine ⟨Equiv.ofBijective j hbij, ε, hε, fun f i => ?_⟩
  rw [Equiv.ofBijective_apply]
  exact hrel f i

end CFSG.StandardType

end
