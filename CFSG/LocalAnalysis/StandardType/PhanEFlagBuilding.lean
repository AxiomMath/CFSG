module

public import CFSG.LocalAnalysis.StandardType.PhanEFlagMove
import CFSG.Monster.B.Geometry.ResidueAdj
public import CFSG.LocalAnalysis.StandardType.PhanEFlagCox

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Flag

open Module CFSG.Monster.B.Geometry CFSG.LieType.Chevalley.CosetBuilding
  CFSG.ClassicalInvolution.Phan.PhanE

variable {K : Type} [Field K] {m : ℕ}

@[expose] noncomputable def flagδ (m : ℕ) (E F : FlagK K (m + 1)) : Equiv.Perm (Fin (m + 1)) :=
  (relPos E F)⁻¹

theorem flagδ_self (E : FlagK K (m + 1)) : flagδ m E E = 1 := by
  simp [flagδ, relPos_self]

theorem flagδ_eq_one_iff (E F : FlagK K (m + 1)) : flagδ m E F = 1 ↔ E = F := by
  rw [flagδ, inv_eq_one, relPos_eq_one_iff]

theorem flagδ_symm (E F : FlagK K (m + 1)) : flagδ m F E = (flagδ m E F)⁻¹ := by
  unfold flagδ
  rw [relPos_symm]

private lemma q2cFB_adjSwap_inv (i : Fin m) : (adjSwap i)⁻¹ = adjSwap i := by
  rw [adjSwap]
  exact Equiv.swap_inv _ _

private lemma q2cFB_adjSwap_ne_one (i : Fin m) : adjSwap i ≠ 1 := by
  intro h
  have h' := congrFun (congrArg DFunLike.coe h) i.castSucc
  simp only [adjSwap, Equiv.swap_apply_left, Equiv.Perm.coe_one, id_eq] at h'
  exact absurd (congrArg Fin.val h') (by simp [Fin.val_succ])

private lemma q2cFB_lt_of_invCount_adjSwap_mul {σ : Equiv.Perm (Fin (m + 1))} {i : Fin m}
    (h : invCount (adjSwap i * σ) = invCount σ + 1) :
    σ⁻¹ i.castSucc < σ⁻¹ i.succ := by
  have hne : σ⁻¹ i.castSucc ≠ σ⁻¹ i.succ := by
    intro hh
    have h2 : i.castSucc = i.succ := σ⁻¹.injective hh
    have h3 := congrArg Fin.val h2
    simp only [Fin.val_castSucc, Fin.val_succ] at h3
    omega
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact hlt
  · exfalso
    have := invCount_adjSwap_mul_of_gt σ i hgt
    omega

theorem flagδ_eq_simple_iff (E F : FlagK K (m + 1)) (i : Fin m) :
    flagδ m E F = (symCox m).simple i ↔ E ≠ F ∧ (flagSys K m).adj i E F := by
  have hswap : (relPos E F)⁻¹ = adjSwap i ↔ relPos E F = adjSwap i := by
    constructor
    · intro h
      have := congrArg Inv.inv h
      simpa [q2cFB_adjSwap_inv] using this
    · intro h
      rw [h, q2cFB_adjSwap_inv]
  rw [flagδ, symCox_simple, hswap]
  exact relPos_eq_adjSwap_iff E F i

theorem isWeylDistanceBuilding_flag :
    IsWeylDistanceBuilding (symCox m) (flagδ (K := K) m) := by
  refine ⟨⟨stdFlag K (m + 1)⟩, ?_, ?_, ?_⟩
  · intro x y
    exact flagδ_eq_one_iff x y
  · intro x y z i hyz
    obtain ⟨hne, hadj⟩ := (flagδ_eq_simple_iff y z i).mp hyz
    constructor
    · rcases relPos_adj (E := x) (F := y) (F' := z) hadj with h | h
      · left
        simp only [flagδ]
        rw [h]
      · right
        simp only [flagδ]
        rw [h, mul_inv_rev, q2cFB_adjSwap_inv, symCox_simple]
    · intro hlen
      have hlen' : (symCox m).length ((relPos x y)⁻¹ * adjSwap i) =
          (symCox m).length ((relPos x y)⁻¹) + 1 := by
        simpa only [flagδ, symCox_simple] using hlen
      have h1 : invCount ((relPos x y)⁻¹ * adjSwap i) = invCount ((relPos x y)⁻¹) + 1 := by
        rw [symCox_length, symCox_length] at hlen'
        exact hlen'
      have hcount : invCount (adjSwap i * relPos x y) = invCount (relPos x y) + 1 := by
        calc invCount (adjSwap i * relPos x y)
            = invCount (adjSwap i * relPos x y)⁻¹ := (invCount_inv _).symm
          _ = invCount ((relPos x y)⁻¹ * (adjSwap i)⁻¹) := by rw [mul_inv_rev]
          _ = invCount ((relPos x y)⁻¹ * adjSwap i) := by rw [q2cFB_adjSwap_inv]
          _ = invCount ((relPos x y)⁻¹) + 1 := h1
          _ = invCount (relPos x y) + 1 := by rw [invCount_inv]
      have hlt := q2cFB_lt_of_invCount_adjSwap_mul hcount
      have hpos := hasPos_adj_of_lt (E := x) (F := y) (F' := z) hadj hne
        (hasPos_relPos x y) hlt
      simp only [flagδ]
      rw [(hasPos_iff.mp hpos), mul_inv_rev, q2cFB_adjSwap_inv, symCox_simple]
  · intro x y i
    obtain ⟨z, hadj, hpos⟩ := exists_adj_hasPos (E := x) (F := y) i (hasPos_relPos x y)
    refine ⟨z, ?_, ?_⟩
    · rw [flagδ_eq_simple_iff]
      refine ⟨?_, hadj⟩
      intro heq
      have hz : relPos x z = adjSwap i * relPos x y := hasPos_iff.mp hpos
      have hzy : relPos x z = relPos x y := by rw [heq]
      have hmul : adjSwap i * relPos x y = relPos x y := by rw [← hz, hzy]
      have hone : adjSwap i = 1 := by
        rw [← one_mul (relPos x y)] at hmul
        exact mul_right_cancel hmul
      exact q2cFB_adjSwap_ne_one i hone
    · simp only [flagδ]
      rw [(hasPos_iff.mp hpos), mul_inv_rev, q2cFB_adjSwap_inv, symCox_simple]

theorem flagSys_adj_iff (i : Fin m) (E F : FlagK K (m + 1)) :
    (flagSys K m).adj i E F ↔ flagδ m E F = 1 ∨ flagδ m E F = (symCox m).simple i := by
  constructor
  · intro hadj
    by_cases hEF : E = F
    · left
      rw [← hEF, flagδ_self]
    · right
      exact (flagδ_eq_simple_iff E F i).mpr ⟨hEF, hadj⟩
  · rintro (h | h)
    · rw [(flagδ_eq_one_iff E F).mp h]
      exact (flagSys K m).adj_refl i F
    · exact ((flagδ_eq_simple_iff E F i).mp h).2

theorem residue_flagδ_eq (J : Set (Fin m)) (E : FlagK K (m + 1)) :
    residue (symCox m) (flagδ (K := K) m) J E = (flagSys K m).residue J E := by
  exact (ChamberSystem.residue_eq_of_adj_iff isWeylDistanceBuilding_flag
    (fun i x y => flagSys_adj_iff i x y) J E).symm

theorem length_flagδ_le (E F : FlagK K (m + 1)) :
    (symCox m).length (flagδ m E F) ≤ (m + 1) * m / 2 := by
  rw [flagδ, symCox_length]
  exact invCount_le _

end CFSG.ClassicalInvolution.Phan.PhanE.Flag
