module

public import CFSG.LocalAnalysis.StandardType.GGTorCNormalizer
public import CFSG.LocalAnalysis.StandardType.GGSpJoinPlaneTorusDefs
public import CFSG.LocalAnalysis.StandardType.GGTBJSympMinusLocalizeAux2

public section

namespace CFSG.StandardType.SympMinus

open CFSG.Open CFSG.Assembly CFSG.StandardType.SpJoin CFSG.StandardType.TorC
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl Multiplicative
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)

theorem sympMinus_component_localize {K : Type} [Field K] [Finite K] [CharP K 2]
    {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K + 1)
    {ζ : Multiplicative (ZMod p) →* Matrix.SpecialLinearGroup (Fin 2) K}
    (hζ : Function.Injective ζ) (hζW : ∀ a, sl2W * ζ a * sl2W⁻¹ = ζ a⁻¹)
    (f₀ : Fin m → Multiplicative (ZMod p)) {J₀ : Subgroup (StatedSp m K)}
    (hJ : CFSG.Assembly.IsComponentOf J₀
      (Subgroup.centralizer ({spPlaneTorus m ζ f₀} : Set (StatedSp m K)))) :
    (∀ j ∈ J₀, ∀ x : Fin m, f₀ x ≠ 1 → ∀ y : Fin m,
      blk (((j : StatedSp m K) : GL (Fin m ⊕ Fin m) K) :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) y x = if y = x then 1 else 0) ∨
    ∃ c : Multiplicative (ZMod p), c ≠ 1 ∧ ∀ j ∈ J₀, ∀ x : Fin m, f₀ x ≠ c → f₀ x ≠ c⁻¹ →
      ∀ y : Fin m,
        blk (((j : StatedSp m K) : GL (Fin m ⊕ Fin m) K) :
          Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) y x = if y = x then 1 else 0 := by
  classical
  have hC : CFSG.Assembly.IsComponentOf J₀
      (⨆ S ∈ sympMinusLocClasses f₀, sympMinusLocMS ζ f₀ S) := by
    rw [sympMinusLoc_iSup_MS hp hp2 hζ f₀]
    exact hJ
  have hc : ∀ S ∈ sympMinusLocClasses f₀, ∀ T ∈ sympMinusLocClasses f₀, S ≠ T →
      ∀ x ∈ sympMinusLocMS ζ f₀ S, ∀ y ∈ sympMinusLocMS ζ f₀ T, Commute x y := by
    intro S hS T hT hST x hx y hy
    apply statedSp_commute
    have hxS : IsSupp (sympMinusLocCoordSet S) (mat m K x) := (Subgroup.mem_inf.mp hx).2
    have hyT : IsSupp (sympMinusLocCoordSet T) (mat m K y) := (Subgroup.mem_inf.mp hy).2
    refine IsSupp.commute hxS hyT ?_
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hS
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp hT
    exact sympMinusLocCoordSet_disjoint (sympMinusLocCls_disjoint hST)
  obtain ⟨S, hSP, hJS⟩ := exists_isComponentOf_block (sympMinusLocClasses f₀)
    (fun S => sympMinusLocMS ζ f₀ S) hc hC
  obtain ⟨x₀, -, hx₀⟩ := Finset.mem_image.mp hSP
  by_cases hx0 : f₀ x₀ = 1
  · left
    intro j hj x hx y
    have hmem : IsSupp (sympMinusLocCoordSet S) (mat m K j) :=
      (Subgroup.mem_inf.mp (hJS.1 hj)).2
    have hxS : x ∉ S := by
      rw [← hx₀]
      intro h
      rcases sympMinusLocCls_mem.mp h with h' | h'
      · exact hx (h'.trans hx0)
      · rw [hx0, inv_one] at h'
        exact hx h'
    exact sympMinusLocBlk_eq_of_isSupp hmem hxS y
  · right
    refine ⟨f₀ x₀, hx0, fun j hj x hx hxi y => ?_⟩
    have hmem : IsSupp (sympMinusLocCoordSet S) (mat m K j) :=
      (Subgroup.mem_inf.mp (hJS.1 hj)).2
    have hxS : x ∉ S := by
      rw [← hx₀]
      intro h
      rcases sympMinusLocCls_mem.mp h with h' | h'
      · exact hx h'
      · exact hxi h'
    exact sympMinusLocBlk_eq_of_isSupp hmem hxS y

end CFSG.StandardType.SympMinus

end
