module

public import CFSG.RankThree.Chevalley.SteinbergBTEvenTwistedE6SixTorus

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Matrix
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Chevalley (sixTorus_prod_zpow sixTorus_zpow_eq_iff sixTorus_sum_identity)

section Defs

variable {τ : Tag} {K : Type} [Field K] {p : ℕ}

@[expose] def qplusExp (τ : Tag) (v : Fin τ.rank → ZMod p) (l : Fin τ.rank) : ℤ :=
  ∑ j, ((v j).val : ℤ) * τ.cartan j l

@[expose] def qplusTheta (τ : Tag) (ζ : Kˣ) (v : Fin τ.rank → ZMod p) : ModGL τ K :=
  rootDiagUnit τ fun l => ζ ^ qplusExp τ v l

theorem qplusTheta_eq (ζ : Kˣ) (v : Fin τ.rank → ZMod p) :
    qplusTheta τ ζ v = ((List.finRange τ.rank).map fun j => torusElt τ K j (ζ ^ (v j).val)).prod
    := by
  rw [list_prod_torusElt_eq_rootDiagUnit, qplusTheta]
  congr 1
  funext l
  simp only [cartanChar, qplusExp]
  rw [← sixTorus_prod_zpow]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← zpow_natCast, ← _root_.zpow_mul]

theorem qplusTheta_mem (ζ : Kˣ) (v : Fin τ.rank → ZMod p) :
    qplusTheta τ ζ v ∈ adjointGroup τ K := by
  rw [qplusTheta_eq]
  refine list_prod_mem fun x hx => ?_
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
  exact torusElt_mem_adjointGroup j _

end Defs

section Torus

variable {τ : Tag} {K : Type} [Field K] {p : ℕ} [Fact p.Prime]

theorem qplusExp_cast (v : Fin τ.rank → ZMod p) (l : Fin τ.rank) :
    ((qplusExp τ v l : ℤ) : ZMod p) = ∑ j, v j * (τ.cartan j l : ZMod p) := by
  simp only [qplusExp, Int.cast_sum, Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val]

variable {ζ : Kˣ} (hζ : orderOf ζ = p)
include hζ

theorem qplusTheta_add (v w : Fin τ.rank → ZMod p) :
    qplusTheta τ ζ (v + w) = qplusTheta τ ζ v * qplusTheta τ ζ w := by
  rw [qplusTheta, qplusTheta, qplusTheta, ← rootDiagUnit_mul]
  congr 1
  funext l
  rw [Pi.mul_apply, ← _root_.zpow_add, sixTorus_zpow_eq_iff hζ, Int.cast_add, qplusExp_cast,
    qplusExp_cast, qplusExp_cast, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by rw [Pi.add_apply, add_mul]

theorem qplusTheta_zero : qplusTheta τ ζ (0 : Fin τ.rank → ZMod p) = 1 := by
  rw [qplusTheta, ← rootDiagUnit_one]
  congr 1
  funext l
  rw [Pi.one_apply, ← zpow_zero ζ, sixTorus_zpow_eq_iff hζ, qplusExp_cast]
  simp

theorem qplusTheta_eq_one (hτ : τ = .E7 ∨ τ = .E8) (hp3 : 3 < p)
    {v : Fin τ.rank → ZMod p} (h : qplusTheta τ ζ v = 1) : v = 0 := by
  have h1 : (fun l => ζ ^ qplusExp τ v l) = 1 :=
    rootDiagUnit_injective (h.trans rootDiagUnit_one.symm)
  have h3 : v ᵥ* (τ.cartan.map (Int.cast : ℤ → ZMod p)) = 0 := funext fun l => by
    have h2 := congrFun h1 l
    rw [Pi.one_apply, ← zpow_zero ζ, sixTorus_zpow_eq_iff hζ, Int.cast_zero,
      qplusExp_cast] at h2
    simpa [Matrix.vecMul, dotProduct] using h2
  refine Matrix.eq_zero_of_vecMul_eq_zero ?_ h3
  have hdet : (τ.cartan.map (Int.cast : ℤ → ZMod p)).det = ((τ.cartan.det : ℤ) : ZMod p) := by
    have h4 := (Int.castRingHom (ZMod p)).map_det τ.cartan
    rw [RingHom.mapMatrix_apply, Int.coe_castRingHom] at h4
    exact h4.symm
  rw [hdet]
  rcases hτ with rfl | rfl
  · rw [det_cartan_E7, Ne, show (((2 : ℤ)) : ZMod p) = ((2 : ℕ) : ZMod p) by norm_num,
      ZMod.natCast_eq_zero_iff]
    intro h5
    have := Nat.le_of_dvd (by norm_num) h5
    omega
  · rw [det_cartan_E8, Int.cast_one]
    exact one_ne_zero

theorem weylElt_conj_qplusTheta (i : Fin τ.rank) (v : Fin τ.rank → ZMod p) :
    weylElt τ K i 1 * qplusTheta τ ζ v * (weylElt τ K i 1)⁻¹ =
      qplusTheta τ ζ (v - (∑ j, (τ.cartan j i : ZMod p) * v j) • Pi.single i 1) := by
  rw [qplusTheta, weylElt_conj_rootDiagUnit, qplusTheta]
  congr 1
  funext l
  rw [← _root_.zpow_mul, ← _root_.zpow_add, sixTorus_zpow_eq_iff hζ]
  push_cast
  rw [qplusExp_cast, qplusExp_cast, qplusExp_cast]
  exact sixTorus_sum_identity (fun j l => (τ.cartan j l : ZMod p)) v i l

end Torus

end CFSG.RankThree.PartOne.KE
