module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1RLevel
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1TorLinLift
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1TorLinMark
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeATransport
import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.SsLin
import CFSG.LocalAnalysis.StandardType.GGOuterInvAtPSLFieldNoneHolds
import CFSG.LinearAlgebra.MatrixPlanes
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearAction

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.StandardType.S2MathAs51642Interfaces
open CFSG.LocalAnalysis.ComponentInitial

theorem q1CentLin_congr_linConjAut {N : ℕ} {K : Type} [Field K] (A : GL (Fin N) K) :
    MulAut.congr (TypeA.recipeEquiv N K) (TableB.linConjAut (Fin N) K A) =
      LinearFlag.conjAut N K A := by
  ext x
  obtain ⟨g, rfl⟩ := LinearFlag.proj_surjective N K x
  set h : ↥(LargeEvenSLGroup (Fin N) K) := (TypeA.slKerEquiv N K).symm g with hh
  have h1 : (TypeA.slKerEquiv N K) h = g := by
    rw [hh, MulEquiv.apply_symm_apply]
  have hx : TypeA.recipeEquiv N K (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K) h) =
      LinearFlag.proj N K g := by
    rw [TypeA.recipeEquiv_mk, h1]
  have hsymm : (TypeA.recipeEquiv N K).symm (LinearFlag.proj N K g) =
      LargeEvenProjMk (LargeEvenSLGroup (Fin N) K) h := by
    rw [MulEquiv.symm_apply_eq]
    exact hx.symm
  have hlin : (TableB.linConjAut (Fin N) K A)
      (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K) h) =
      LargeEvenProjMk (LargeEvenSLGroup (Fin N) K) (MulAut.conjNormal A h) := by
    change (TableB.linConjAut (Fin N) K A)
        (h : LargeEvenProj (LargeEvenSLGroup (Fin N) K)) =
      (MulAut.conjNormal A h : LargeEvenProj (LargeEvenSLGroup (Fin N) K))
    exact TableB.linConjAut_mk A h
  rw [MulAut.congr_apply, MulEquiv.trans_apply, hsymm, MulEquiv.trans_apply, hlin,
    TypeA.recipeEquiv_mk, LinearFlag.conjAut_proj]
  apply congrArg (LinearFlag.proj N K)
  apply Matrix.SpecialLinearGroup.toGL_injective
  have htoGL : Matrix.SpecialLinearGroup.toGL
      ((TypeA.slKerEquiv N K) (MulAut.conjNormal A h)) =
      (MulAut.conjNormal A h : GL (Fin N) K) := by
    apply Units.ext
    exact TypeA.coe_slKerEquiv (MulAut.conjNormal A h)
  have hg : Matrix.SpecialLinearGroup.toGL g = (h : GL (Fin N) K) := by
    rw [← h1]
    rfl
  rw [htoGL, CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation,
    hg, MulAut.conjNormal_apply]

theorem q1CentLin_scalar_of_linConjAut_eq_one {N : ℕ} (hN : 2 ≤ N) {K : Type} [Field K]
    [Finite K] {A : GL (Fin N) K} (h : TableB.linConjAut (Fin N) K A = 1) :
    ∃ c : Kˣ, Matrix.GeneralLinearGroup.scalar (Fin N) c = A := by
  have h1 : LinearFlag.conjAut N K A = 1 := by
    rw [← q1CentLin_congr_linConjAut A, h, map_one]
  exact CFSG.HardMathSupport.Dickson.Sec6.exists_scalar_of_conjAut_eq_one hN h1

theorem q1CentLin_odd_orderOf {N : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (A : GL (Fin N) K) (h : Odd (orderOf (TableB.linConjAut (Fin N) K A))) :
    Odd (orderOf A) := by
  have hord : orderOf (LinearFlag.conjAut N K A) =
      orderOf (TableB.linConjAut (Fin N) K A) := by
    rw [← q1CentLin_congr_linConjAut A]
    exact (MulAut.congr (TypeA.recipeEquiv N K)).orderOf_eq _
  have hodd : Odd (orderOf (LinearFlag.conjAut N K A)) := by
    rw [hord]
    exact h
  exact CFSG.StandardType.psl_odd_orderOf_of_odd_orderOf_conjAut A hodd

theorem q1CentLin_commute {N p : ℕ} (hN : 2 ≤ N) {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hpgcd : ¬ p ∣ Nat.gcd N (Nat.card K - 1)) {g h : GL (Fin N) K}
    (hgp : TableB.linConjAut (Fin N) K g ^ p = 1)
    (hcomm : TableB.linConjAut (Fin N) K h * TableB.linConjAut (Fin N) K g =
      TableB.linConjAut (Fin N) K g * TableB.linConjAut (Fin N) K h) :
    h * g = g * h := by
  have hc : TableB.linConjAut (Fin N) K (h * g * h⁻¹ * g⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
    group
  obtain ⟨z, hz⟩ := q1CentLin_scalar_of_linConjAut_eq_one hN hc
  have hconj : h * g * h⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin N) z * g := by
    rw [hz]
    group
  have hgp' : TableB.linConjAut (Fin N) K (g ^ p) = 1 := by
    rw [map_pow, hgp]
  obtain ⟨b, hb⟩ := q1CentLin_scalar_of_linConjAut_eq_one hN hgp'
  have hzpow : z ^ p = 1 :=
    CFSG.LinearAlgebra.scalar_pow_eq_one_of_conj_eq_scalar hconj hb.symm (by omega)
  have hdet : z ^ N = 1 := by
    have h1 := congrArg Matrix.GeneralLinearGroup.det hconj
    rw [map_mul, map_mul, map_inv, map_mul, Matrix.GeneralLinearGroup.det_scalar,
      Fintype.card_fin] at h1
    have h2 : Matrix.GeneralLinearGroup.det g =
        z ^ N * Matrix.GeneralLinearGroup.det g := by
      calc Matrix.GeneralLinearGroup.det g
          = (Matrix.GeneralLinearGroup.det g * Matrix.GeneralLinearGroup.det h) *
              (Matrix.GeneralLinearGroup.det h)⁻¹ := by group
        _ = (Matrix.GeneralLinearGroup.det h * Matrix.GeneralLinearGroup.det g) *
              (Matrix.GeneralLinearGroup.det h)⁻¹ := by
              rw [mul_comm (Matrix.GeneralLinearGroup.det g)
                (Matrix.GeneralLinearGroup.det h)]
        _ = z ^ N * Matrix.GeneralLinearGroup.det g := h1
    exact mul_right_cancel (by rw [one_mul]; exact h2.symm)
  have hzK : orderOf z ∣ Nat.card K - 1 := by
    rw [← Nat.card_units (α := K)]
    exact orderOf_dvd_of_pow_eq_one pow_card_eq_one'
  have hz1 : orderOf z = 1 := by
    rcases hp.eq_one_or_self_of_dvd (orderOf z)
      (orderOf_dvd_of_pow_eq_one hzpow) with h1 | h1
    · exact h1
    · exfalso
      exact hpgcd (h1 ▸ Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hdet) hzK)
  have hz_eq : z = 1 := orderOf_eq_one_iff.mp hz1
  have hconj1 : h * g * h⁻¹ = g := by
    simpa [hz_eq] using hconj
  calc h * g = h * g * h⁻¹ * h := by group
    _ = g * h := by rw [hconj1]

theorem q1RCenterPrime_lin :
    Q1RToralTransfer (fun _ _ _ => True) (fun p lab => CenterPrimeTo p lab ∧ lab.tag = .A)
      (fun _ _ _ => True) := by
  intro p hp hp2 lab hlab hS
  obtain ⟨t, l, n⟩ := lab
  rcases hS with ⟨hcp, ht⟩
  subst ht
  have hpgcd : ¬ p ∣ Nat.gcd (l + 1) (2 ^ n - 1) := hcp.2
  have hN2 : 2 ≤ l + 1 := by
    have h := hlab
    simp only [LargeEvenInLambda2] at h
    omega
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hq⟩ := hQ
  refine ⟨K, i1, i2, hK, hq, ?_⟩
  intro A hAab hAI _ u huA huord J hJcomp
  have : CharP K 2 := charP_two_of_card hK
  have : IsMulCommutative A := hAab.1
  obtain ⟨g_u, hgu⟩ := TableB.exists_eq_linConjAut (hAI u huA)
  have hlift : ∀ a ∈ A, ∃ g_a : GL (Fin (l + 1)) K,
      a = TableB.linConjAut (Fin (l + 1)) K g_a ∧ g_a * g_u = g_u * g_a := by
    intro a haA
    obtain ⟨g_a, hga⟩ := TableB.exists_eq_linConjAut (hAI a haA)
    refine ⟨g_a, hga, q1CentLin_commute hN2 hp (by rw [hK]; exact hpgcd) ?_ ?_⟩
    · rw [← hgu, ← huord, pow_orderOf_eq_one]
    · rw [← hga, ← hgu]
      exact congrArg Subtype.val (mul_comm' (⟨a, haA⟩ : ↥A) ⟨u, huA⟩)
  rw [hgu] at hJcomp
  obtain ⟨C, hC, hCSL, hJeq⟩ := q1TorLin_component_lift hN2 g_u J hJcomp
  have hgodd : Odd (orderOf g_u) := q1CentLin_odd_orderOf g_u (by
    rw [← hgu, huord]
    exact hp.odd_of_ne_two hp2)
  have hmark := q1TorLin_marking hN2 g_u hgodd C hC hCSL J hJeq
  refine largeEvenMarking_mono (fun labJ R' _ I' F' θJ hprop => ?_) hmark
  refine ⟨trivial, ?_, ?_⟩
  · intro a haA j hj
    obtain ⟨g_a, hga, hcomm⟩ := hlift a haA
    have := (hprop g_a hcomm).1 j hj
    simpa [← hga] using this
  · intro a haA
    obtain ⟨g_a, hga, hcomm⟩ := hlift a haA
    have := (hprop g_a hcomm).2
    simpa [← hga] using this

theorem q1CenterPrimeLinear_holds :
    GGBstarInnerDiagJInputOn (fun p lab => CenterPrimeTo p lab ∧ lab.tag = .A) := by
  refine q1On_of_selectedTransfer
    (q1SelectedTransfer_of_toral (Toral := fun _ _ _ => True)
      (q1ToralActionTransfer_of_rToral q1RCenterPrime_lin) ?_)
  intro G _ _ p B Bs x L D J _ P hP
  exact largeEvenMarking_mono (fun _ _ _ _ _ _ h => ⟨h, fun _ _ _ => trivial⟩) hP

end CFSG.StandardType
