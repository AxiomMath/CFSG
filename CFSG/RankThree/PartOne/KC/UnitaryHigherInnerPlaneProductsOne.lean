module

public import CFSG.RankThree.PartOne.KC.UnitaryPlaneStatements
public import CFSG.RankThree.PartOne.KC.UnitaryPlaneProductsGlue
public import CFSG.RankThree.PartOne.KC.UnitaryRigidityOne
public import CFSG.RankThree.PartOne.KC.UnitaryHigherInnerPlaneLift
public import CFSG.RankThree.PartOne.KC.UnitaryHigherInnerPlaneCentralization

public section

namespace CFSG.RankThree.PartOne

open Polynomial CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.KCUnitaryExact
  CFSG.RankThree.PartOne.KCUnitaryPlane CFSG.RankThree.PartOne.KCUnitaryGlue
  CFSG.RankThree.PartOne.KCUnitaryOne CFSG.RankThree.PartOne.KCUnitaryFrame

theorem higher_unitary_inner_plane_products_trivial_of_dvd {ℓ f n p : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData ℓ f K) (hp : p.Prime) (hpℓ : p ≠ ℓ) (hn : 3 ≤ n) (hnp : n < p)
    (hne : ¬(n = 3 ∧ ℓ ^ f = 2)) (hpq : p ∣ ℓ ^ f + 1)
    (B : Subgroup (MulAut (primeFormP h (idGram K n)))) (hB : innU h n ≤ B)
    (A : Subgroup (MulAut (primeFormP h (idGram K n)))) (hAH : A ≤ innU h n)
    (hA : IsElementaryAbelian p A) (hAcard : Nat.card A = p ^ 2) :
    autThetaT p B A = ⊥ ∧ ∀ t ∈ A, t ≠ 1 → autPlaneProduct p B A t = ⊥ := by
  have hZp : ∀ c : Kˣ, h.norm (c : K) = 1 → c ^ n = 1 → c ^ p = 1 → c = 1 := by
    intro c _ hcn hcp
    have hcop : Nat.Coprime n p :=
      ((Nat.Prime.coprime_iff_not_dvd hp).mpr (Nat.not_dvd_of_pos_of_lt (by omega) hnp)).symm
    have : c ^ Nat.gcd n p = 1 := pow_gcd_eq_one.mpr ⟨hcn, hcp⟩
    rwa [hcop, pow_one] at this
  obtain ⟨⟨Ahat, hAhat, -⟩, hrest⟩ :=
    higher_unitary_inner_plane_commuting_lift_and_kernel_decomposition h hp hpℓ hn hnp hne A hAH hA
      hAcard
  obtain ⟨-, -, he1, -, -, -, -⟩ := hrest Ahat hAhat
  obtain ⟨-, hq3, b, hbON, hbeig⟩ := he1 ((ordNegQ_eq_one_iff hp).mpr hpq)
  have S : PlaneSetup h n p Ahat := ⟨hn, hne, hp, hpℓ, hZp, hAhat.1, hAhat.2.1⟩
  refine plane_products_trivial_of_lift S hAhat B ?_ ?_
  · intro a haA ha1 x hx hxa hxp
    obtain ⟨hall, -, hlocal, -⟩ :=
      higher_unitary_inner_plane_all_parameter_local_core_centralization h hn hnp hp hpℓ hne B hB A
        Ahat hAhat a haA x hx hxa hxp
    exact ⟨fun i => (hall i).2.2.2.2, hlocal⟩
  · intro β hcent hblock
    exact rigidity_of_orthonormal_eigenbasis S hpq hq3 b hbON
      (fun x hx i => hbeig ⟨x, hx⟩ i) β hcent hblock

end CFSG.RankThree.PartOne
