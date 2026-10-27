module

public import CFSG.LocalAnalysis.StandardType.GGWitOrthClassR35Aux3
public import CFSG.LocalAnalysis.StandardType.GGWitOrthClassR35E6

public section

namespace CFSG.StandardType.ZS

open Subgroup

theorem owR35_alpha_eq (w a b : Fin 5 → ZMod 3) :
    owR35g_alphaLinP 3 w a b = 2 * ∑ l, w l * (a l * b l) := by
  show 2 * ∑ k, w k * (b k * a k) = 2 * ∑ l, w l * (a l * b l)
  exact congrArg _ (Finset.sum_congr rfl fun k _ => by ring)

theorem owR35_reflFun_eq (w a x : Fin 5 → ZMod 3) (ha : ∑ i, w i * (a i * a i) = 1) :
    owR35_reflFun w a x = owR35g_formP 3 w a x := by
  funext i
  simp only [owR35_reflFun, owR35g_formP, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [ha, div_one]
  simp only [owR35g_alphaLinP, LinearMap.coe_mk, AddHom.coe_mk]

theorem owR35_e6_canon {U : Type} [AddCommGroup U] [Module (ZMod 3) U]
    (Q : QuadraticForm (ZMod 3) U) (e : U ≃ₗ[ZMod 3] (Fin 5 → ZMod 3)) (w : Fin 5 → ZMod 3)
    (he : ∀ v, Q v = ∑ i, w i * (e v i) ^ 2)
    (roots : Fin 6 → Fin 5 → ZMod 3) (ord : Fin 72 → Fin 5 → ZMod 3)
    (par : Fin 72 → Fin 72) (gen : Fin 72 → Fin 6)
    (hQ : ∀ i, (∑ j, w j * (roots i j) ^ 2) = 1)
    (hP : ∀ i j, (2 : ZMod 3) * ∑ l, w l * (roots i l * roots j l) = (CartanMatrix.E 6 i j : ZMod 3))
    (hfirst : ∀ i : Fin 6, ord (Fin.castLE (by norm_num) i) = roots i)
    (hstep : ∀ j : Fin 72, 6 ≤ j.val → owR35_reflFun w (roots (gen j)) (ord (par j)) = ord j)
    (hlt : ∀ j : Fin 72, 6 ≤ j.val → (par j).val < j.val)
    (hcov : ∀ a : Fin 5 → ZMod 3, (∑ i, w i * (a i) ^ 2) = 1 → ∃ j, a = ord j) :
    LinWeyl 3 (Subgroup.closure (ClassRefl 3 Q 1)) := by
  have hnorm : ∀ i, ∑ k, w k * (roots i k * roots i k) = 1 := fun i => by
    simpa only [pow_two] using hQ i
  exact owR35g_e6_canon (p := 3) (by norm_num) (by norm_num) rfl Q e w he roots ord par gen hnorm
    (fun i j => by rw [owR35_alpha_eq]; exact hP i j) hfirst
    (fun j hj => by rw [← owR35_reflFun_eq w _ _ (hnorm (gen j))]; exact (hstep j hj).symm)
    hlt (fun a ha => hcov a (by simpa only [pow_two] using ha))

theorem owR35_e6_canon_1 {U : Type} [AddCommGroup U] [Module (ZMod 3) U]
    (Q : QuadraticForm (ZMod 3) U) (e : U ≃ₗ[ZMod 3] (Fin 5 → ZMod 3))
    (he : ∀ v, Q v = ∑ i, (owR35_wcan 1) i * (e v i) ^ 2) :
    LinWeyl 3 (Subgroup.closure (ClassRefl 3 Q 1)) :=
  owR35_e6_canon Q e (owR35_wcan 1) he owR35_roots1 owR35_ord1 owR35_par1 owR35_gen1
    owR35_hQ1 owR35_hP1 owR35_hfirst1 owR35_hstep1 owR35_hlt1 owR35_hcov1

theorem owR35_e6_canon_3 {U : Type} [AddCommGroup U] [Module (ZMod 3) U]
    (Q : QuadraticForm (ZMod 3) U) (e : U ≃ₗ[ZMod 3] (Fin 5 → ZMod 3))
    (he : ∀ v, Q v = ∑ i, (owR35_wcan 3) i * (e v i) ^ 2) :
    LinWeyl 3 (Subgroup.closure (ClassRefl 3 Q 1)) :=
  owR35_e6_canon Q e (owR35_wcan 3) he owR35_roots3 owR35_ord3 owR35_par3 owR35_gen3
    owR35_hQ3 owR35_hP3 owR35_hfirst3 owR35_hstep3 owR35_hlt3 owR35_hcov3

theorem owR35_e6_canon_5 {U : Type} [AddCommGroup U] [Module (ZMod 3) U]
    (Q : QuadraticForm (ZMod 3) U) (e : U ≃ₗ[ZMod 3] (Fin 5 → ZMod 3))
    (he : ∀ v, Q v = ∑ i, (owR35_wcan 5) i * (e v i) ^ 2) :
    LinWeyl 3 (Subgroup.closure (ClassRefl 3 Q 1)) :=
  owR35_e6_canon Q e (owR35_wcan 5) he owR35_roots5 owR35_ord5 owR35_par5 owR35_gen5
    owR35_hQ5 owR35_hP5 owR35_hfirst5 owR35_hstep5 owR35_hlt5 owR35_hcov5


end CFSG.StandardType.ZS
