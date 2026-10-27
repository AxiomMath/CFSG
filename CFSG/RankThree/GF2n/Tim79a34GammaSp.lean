module

public import CFSG.RankThree.GF2n.Tim79a34TwLower

public section

namespace CFSG.RankThree.GF2n.Tim79a.Gamma

open Matrix

theorem exists_statedSp_of_addEquiv {n : ℕ}
    (L : (Fin n ⊕ Fin n → GaloisField 2 1) ≃+ (Fin n ⊕ Fin n → GaloisField 2 1))
    (hL : ∀ v w, CFSG.Timmesfeld.ARS.CaseM.spForm (L v) (L w) =
      CFSG.Timmesfeld.ARS.CaseM.spForm v w) :
    ∃ g : CFSG.Open.StatedSp n (GaloisField 2 1), ∀ v,
      CFSG.LieType.Universal.Symplectic.SpExtras.mat n (GaloisField 2 1) g *ᵥ v = L v := by
  have hsmul : ∀ (c : GaloisField 2 1) (v : Fin n ⊕ Fin n → GaloisField 2 1),
      L (c • v) = c • L v := by
    intro c v
    rcases CFSG.RankThree.GF2n.Tim79a.twl_gf2 c with rfl | rfl
    · simp
    · simp
  obtain ⟨e, he⟩ : ∃ e : (Fin n ⊕ Fin n → GaloisField 2 1) ≃ₗ[GaloisField 2 1]
      (Fin n ⊕ Fin n → GaloisField 2 1), ∀ x, e x = L x :=
    ⟨{ toFun := fun x => L x
       map_add' := fun x y => map_add L x y
       map_smul' := fun c v => hsmul c v
       invFun := fun x => L.symm x
       left_inv := fun x => L.symm_apply_apply x
       right_inv := fun x => L.apply_symm_apply x }, fun x => rfl⟩
  have hMN : LinearMap.toMatrix' e.toLinearMap * LinearMap.toMatrix' e.symm.toLinearMap = 1 := by
    have hcomp : e.toLinearMap.comp e.symm.toLinearMap = LinearMap.id :=
      LinearMap.ext fun x => by simp
    rw [← LinearMap.toMatrix'_comp, hcomp, LinearMap.toMatrix'_id]
  have hNM : LinearMap.toMatrix' e.symm.toLinearMap * LinearMap.toMatrix' e.toLinearMap = 1 := by
    have hcomp : e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id :=
      LinearMap.ext fun x => by simp
    rw [← LinearMap.toMatrix'_comp, hcomp, LinearMap.toMatrix'_id]
  obtain ⟨u, hu1⟩ : ∃ u : GL (Fin n ⊕ Fin n) (GaloisField 2 1),
      (u : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 1)) =
        LinearMap.toMatrix' e.toLinearMap :=
    ⟨Units.mk _ _ hMN hNM, rfl⟩
  have hMv : ∀ x : Fin n ⊕ Fin n → GaloisField 2 1,
      LinearMap.toMatrix' e.toLinearMap *ᵥ x = L x := fun x =>
    (LinearMap.toMatrix'_mulVec e.toLinearMap x).trans (he x)
  have hform : ∀ a b : Fin n ⊕ Fin n → GaloisField 2 1,
      CFSG.ClassicalGroups.Symplectic.spForm n (GaloisField 2 1) a b =
        CFSG.Timmesfeld.ARS.CaseM.spForm a b := fun a b =>
    (CFSG.ClassicalGroups.Symplectic.spForm_apply a b).trans rfl
  have hu : u ∈ CFSG.Open.StatedSp n (GaloisField 2 1) := by
    rw [CFSG.ClassicalGroups.Symplectic.mem_statedSp_iff_forall]
    intro x y
    rw [hu1, hMv, hMv, hform, hform]
    exact hL x y
  refine ⟨⟨u, hu⟩, fun v => ?_⟩
  rw [CFSG.LieType.Universal.Symplectic.SpExtras.mat_apply]
  show (u : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 1)) *ᵥ v = L v
  rw [hu1]
  exact hMv v

end CFSG.RankThree.GF2n.Tim79a.Gamma
