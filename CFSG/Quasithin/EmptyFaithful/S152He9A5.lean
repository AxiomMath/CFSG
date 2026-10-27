module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_6_14
public import Mathlib.LinearAlgebra.Projectivization.Action
public import Mathlib.LinearAlgebra.Projectivization.Cardinality
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.MatrixGroups.PSL2
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Rat.Floor

public section

namespace CFSG.Quasithin.He9

open BenderSuzuki.MatrixGroups ZMod
open scoped LinearAlgebra.Projectivization

theorem nonempty_psl2_gf4_mulEquiv_alternating :
    Nonempty (PSL2MatrixGroup (GaloisField 2 2) ≃* alternatingGroup (Fin 5)) := by
  classical
  let K := GaloisField 2 2
  have hK : Nat.card K = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  have hcenter :=
    BenderSuzuki.External.huppert614_card_center_of_neg_one_eq_one (K := K) (CharTwo.neg_eq 1)
  have hcard := BenderSuzuki.External.huppert614_card_psl_mul_center (K := K)
  rw [hK, hcenter] at hcard
  have hPSL : Nat.card (PSL2MatrixGroup K) = 60 := by
    norm_num at hcard
    exact hcard
  have hP : Nat.card (ℙ K (Fin 2 → K)) = 5 := by
    rw [Projectivization.card_of_finrank_two K (Fin 2 → K) (by simp), hK]
  let : Fintype (ℙ K (Fin 2 → K)) := Fintype.ofFinite _
  let e : ℙ K (Fin 2 → K) ≃ Fin 5 :=
    Fintype.equivFinOfCardEq (by rw [← Nat.card_eq_fintype_card, hP])
  let ψ : PSL2MatrixGroup K →* Equiv.Perm (Fin 5) :=
    e.permCongrHom.toMonoidHom.comp (MulAction.toPermHom (PSL2MatrixGroup K) (ℙ K (Fin 2 → K)))
  have hψ : Function.Injective ψ :=
    e.permCongrHom.injective.comp
      (MulAction.toPerm_injective (α := PSL2MatrixGroup K) (β := ℙ K (Fin 2 → K)))
  have hrange_card : Nat.card ψ.range = 60 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv, hPSL]
  have hindex : ψ.range.index = 2 := by
    have h := ψ.range.card_mul_index
    rw [hrange_card, Nat.card_perm, Nat.card_fin] at h
    simp [Nat.factorial] at h
    omega
  have hrange : ψ.range = alternatingGroup (Fin 5) :=
    Equiv.Perm.eq_alternatingGroup_of_index_eq_two hindex
  exact ⟨(MonoidHom.ofInjective hψ).trans (MulEquiv.subgroupCongr hrange)⟩

end CFSG.Quasithin.He9
