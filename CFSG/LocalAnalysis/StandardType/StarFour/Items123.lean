module

public import CFSG.LocalAnalysis.StandardType.StarFour.ItemsDatum
public import CFSG.LocalAnalysis.StandardType.StarFour.BlockDatum
public import CFSG.LocalAnalysis.StandardType.StarFour.FrameModel
public import CFSG.LocalAnalysis.StandardType.StarFour.FrameNesting

public section

namespace CFSG.StandardType.StarFour

open CFSG.LinearAlgebra.RootGroupSL CFSG.Open

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [Module.Finite F V] {X : Type} [Group X]

theorem items_of_whole {P : Type} [CommGroup P] (η : P →* SpecialLinearGroup F V)
    (fr : SemiFrame F (groupRep η)) (i : Fin fr.r) (hm : 3 ≤ fr.m i)
    (hc : 2 ≤ Module.finrank F (fr.E i)) (ψ : SpecialLinearGroup F V →* X)
    (hψ : Function.Injective ψ) :
    pCoreOf 2 (ψ.range ⊓ Subgroup.normalizer (((fr.blockRoot i (by omega)).map ψ : Subgroup X) :
        Set X)) ⊔ (fr.blockJ0 i (by omega)).map ψ = ψ.range ∧
      GGRootInnerAt ψ.range ((fr.blockRoot i (by omega)).map ψ) ∧
      GGRootNoCentralAt ψ.range ((fr.blockRoot i (by omega)).map ψ) ∧
      (∀ Y : Subgroup X, IsPGroup 2 Y → Y ≤ Subgroup.normalizer (ψ.range : Set X) →
        Y ≤ Subgroup.normalizer (((fr.blockRoot i (by omega)).map ψ : Subgroup X) : Set X) →
        ⁅Y, ψ.range ⊓ Subgroup.normalizer
            (((fr.blockRoot i (by omega)).map ψ : Subgroup X) : Set X)⁆ ≤
          pCoreOf 2 (ψ.range ⊓ Subgroup.normalizer
            (((fr.blockRoot i (by omega)).map ψ : Subgroup X) : Set X)) →
        Y ≤ ψ.range ⊔ Subgroup.centralizer (ψ.range : Set X)) := by
  have hm2 : 2 ≤ fr.m i := by omega
  have hV : 3 * Module.finrank F (fr.E i) ≤ Module.finrank F V := by
    let f : (Fin (fr.m i) → fr.E i) →ₗ[F] V :=
      (fr.Φ.symm : (∀ j, Fin (fr.m j) → fr.E j) →ₗ[F] V) ∘ₗ
        LinearMap.single F (fun j => Fin (fr.m j) → fr.E j) i
    have hf : ∀ u : Fin (fr.m i) → fr.E i, f u = fr.Φ.symm (Pi.single i u) := by
      intro u
      simp only [f, LinearMap.comp_apply, LinearMap.single_apply,
        LinearEquiv.coe_toLinearMap]
    have hinj : Function.Injective f := by
      intro u v huv
      have h : fr.Φ.symm (Pi.single i u) = fr.Φ.symm (Pi.single i v) := by
        rw [← hf u, ← hf v, huv]
      have h' : Pi.single (M := fun j => Fin (fr.m j) → fr.E j) i u =
          Pi.single (M := fun j => Fin (fr.m j) → fr.E j) i v := by
        have hc := congrArg fr.Φ h
        simpa only [LinearEquiv.apply_symm_apply] using hc
      have h2 := congrFun h' i
      simpa only [Pi.single_eq_same] using h2
    have hle := LinearMap.finrank_le_finrank_of_injective hinj
    have hfin : Module.finrank F (Fin (fr.m i) → fr.E i) =
        fr.m i * Module.finrank F (fr.E i) := by
      rw [Module.finrank_pi_fintype]
      simp [Finset.sum_const, nsmul_eq_mul]
    rw [hfin] at hle
    exact (Nat.mul_le_mul_right _ hm).trans hle
  have h1 : ∀ t, fr.blockPi i (fr.idx1 i hm2) (fr.blockIota i (fr.idx0 i hm2) t) = 0 :=
    fun t => fr.blockPi_blockIota_ne i (fr.idx0_ne_idx1 i hm2) t
  have h2 : ∀ t, fr.blockPi i (fr.idx1 i hm2) (fr.blockIota i (fr.idx1 i hm2) t) = t :=
    fun t => fr.blockPi_blockIota_self i (fr.idx1 i hm2) t
  have h3 : ∀ t, fr.blockPi i (fr.idx0 i hm2) (fr.blockIota i (fr.idx0 i hm2) t) = t :=
    fun t => fr.blockPi_blockIota_self i (fr.idx0 i hm2) t
  have h4 : ∀ t, fr.blockPi i (fr.idx0 i hm2) (fr.blockIota i (fr.idx1 i hm2) t) = 0 :=
    fun t => fr.blockPi_blockIota_ne i (fr.idx0_ne_idx1 i hm2).symm t
  have key := items_of_datum (fr.blockIota i (fr.idx0 i hm2))
    (fr.blockIota i (fr.idx1 i hm2)) (fr.blockPi i (fr.idx1 i hm2))
    (fr.blockPi i (fr.idx0 i hm2)) h1 h2 h3 h4 hV (Or.inl hc) ψ hψ
  unfold SemiFrame.blockRoot SemiFrame.blockJ0
  exact key

end CFSG.StandardType.StarFour
