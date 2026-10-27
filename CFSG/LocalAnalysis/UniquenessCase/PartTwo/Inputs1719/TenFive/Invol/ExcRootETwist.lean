module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.ExcTwist
public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.IrrationalRoot

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.LieType.SeitzGeneration.ExcOuterLeOne (exists_adjData_valid_E commutator_xPar_neighbour)
open scoped commutatorElement


theorem isSpecialGood_xPar_single_mul {τ : Tag} (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {K : Type} [Field K] [Finite K] {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) [CharP K p]
    (hK : Nat.card K = p ^ e) (h3 : 3 < p ^ e) {i l : Fin τ.rank}
    (hil : τ.cartan i l = -1) (hli : τ.cartan l i = -1) {w : K → adjointGroup τ K}
    (hw : ∀ s t, w (s + t) = w s * w t)
    (hwl : ∀ s t, Commute (w s) (xPar (rootOperatorFamily τ) (Pi.single l 1) t))
    (hwi : ∀ s t, Commute (w s) (xPar (rootOperatorFamily τ) (Pi.single i 1) t))
    (f : K →+ K) {s : K} (hs : s ≠ 0) :
    orderOf (xPar (rootOperatorFamily τ) (Pi.single i 1) s * w (f s)) = p ∧
      IsSpecialGood p (xPar (rootOperatorFamily τ) (Pi.single i 1) s * w (f s)) := by
  classical
  obtain ⟨D, hD, hτ'⟩ : ∃ D : AdjData τ, D.Valid ∧ NoG2 τ := by
    rcases hτ with rfl | hE
    · exact ⟨_, f4Data_valid, noG2_F4⟩
    · exact exists_adjData_valid_E hE
  obtain ⟨ε, hε, hcomm⟩ := commutator_xPar_neighbour (K := K) (τ := τ) hD hτ' hil hli
  let F := rootOperatorFamily τ
  let xa : K → adjointGroup τ K := fun s => xPar F (Pi.single l 1) s
  let xb : K → adjointGroup τ K := fun s => xPar F (Pi.single i 1) s
  let z : K → adjointGroup τ K :=
    fun s => xPar F (Pi.single l 1 + Pi.single i 1) ((ε : K) * s)
  have hli' : l ≠ i := ne_of_cartan_eq_neg_one hil
  have hδ : IsRoot τ (Pi.single l 1 + Pi.single i 1) := isRoot_single_add_single hil
  have hε0 : (ε : K) ≠ 0 := by rcases hε with rfl | rfl <;> simp
  have hxa : ∀ s t, xa (s + t) = xa s * xa t := fun s t => xPar_add _ s t
  have hxb : ∀ s t, xb (s + t) = xb s * xb t := fun s t => xPar_add _ s t
  have hz : ∀ s t, z (s + t) = z s * z t := by
    intro s t
    dsimp only [z]
    rw [mul_add, xPar_add]
  have hzi : Function.Injective z := by
    intro s t hst
    exact mul_left_cancel₀ hε0 (xPar_injective hδ hst)
  have hab : ∀ s t, ⁅xa s, xb t⁆ = z (s * t) := by
    intro s t
    dsimp only [xa, xb, z]
    simpa [mul_assoc] using hcomm s t
  have hγδa : (Pi.single l 1 + Pi.single i 1 : Fin τ.rank → ℤ) + Pi.single l 1 =
      Pi.single i 1 + (2 : ℤ) • Pi.single l 1 := by
    rw [two_zsmul]
    abel
  have hne_a : ((Pi.single l 1 + Pi.single i 1 : Fin τ.rank → ℤ) + Pi.single l 1) ≠ 0 := by
    intro h0
    have h2 := congrFun h0 l
    rw [hγδa] at h2
    simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply] at h2
    rw [Pi.single_eq_same, Pi.single_eq_of_ne hli'] at h2
    norm_num at h2
  have hn_a : ¬IsRoot τ ((Pi.single l 1 + Pi.single i 1 : Fin τ.rank → ℤ) + Pi.single l 1) := by
    rw [hγδa]
    exact not_isRoot_single_add_two hli
  have hza : ∀ s t, Commute (z s) (xa t) := by
    intro s t
    exact commute_xPar hD hτ' hδ (isRoot_single τ l) hne_a hn_a ((ε : K) * s) t
  have hγδb : (Pi.single l 1 + Pi.single i 1 : Fin τ.rank → ℤ) + Pi.single i 1 =
      Pi.single l 1 + (2 : ℤ) • Pi.single i 1 := by
    rw [two_zsmul]
    abel
  have hne_b : ((Pi.single l 1 + Pi.single i 1 : Fin τ.rank → ℤ) + Pi.single i 1) ≠ 0 := by
    intro h0
    have h2 := congrFun h0 i
    rw [hγδb] at h2
    simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply] at h2
    rw [Pi.single_eq_same, Pi.single_eq_of_ne hli'.symm] at h2
    norm_num at h2
  have hn_b : ¬IsRoot τ ((Pi.single l 1 + Pi.single i 1 : Fin τ.rank → ℤ) + Pi.single i 1) := by
    rw [hγδb]
    exact not_isRoot_single_add_two hil
  have hzb : ∀ s t, Commute (z s) (xb t) := by
    intro s t
    exact commute_xPar hD hτ' hδ (isRoot_single τ i) hne_b hn_b ((ε : K) * s) t
  simpa only [xb] using
    isSpecialGood_mul_of_comm (K := K) (S := adjointGroup τ K) hp hp2 hK h3
      hxa hxb hz hzi hab hza hzb hw hwl hwi f hs

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive
