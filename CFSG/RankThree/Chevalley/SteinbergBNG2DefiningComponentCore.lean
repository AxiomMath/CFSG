module

public import CFSG.RankThree.Chevalley.SteinbergBNComponentLocalCoreReduction
public import CFSG.RankThree.Chevalley.EvenRealThreeCentralizingInvolution
public import CFSG.RankThree.Chevalley.SteinbergCFG2DefiningComponentField
public import CFSG.RankThree.Chevalley.SteinbergCFPrimeFieldG2LocalCores

public section

namespace CFSG.RankThree.Chevalley

open Subgroup CFSG CFSG.RankThree.LocalRank CFSG.RankThree CFSG.RankThree.GroupTheory
open CFSG.LocalAnalysis.ComponentInitial CFSG.Blueprint CFSG.Blueprint.Chevalley
open scoped Pointwise

theorem G2_defining_prime_actual_component_local_core_product_centralizes {X : Type} [Group X]
    [Finite X] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (N : Subgroup X) [N.Normal]
    (hN : ¬p ∣ Nat.card N) (hX : CFSG.Assembly.RankThreeEven.localRank p X ≤ 3)
    {E : Subgroup (X ⧸ N)} (hE : IsElementaryAbelian p E) (hEcard : Nat.card E = p ^ 2)
    {t : X ⧸ N} (ht : t ∈ E) (ht1 : t ≠ 1) {L : Subgroup (X ⧸ N)} (hL : IsComponent L) {f : ℕ}
    (hT : ChevalleyExceptionalModel (L ⧸ center L) .G2 p f)
    (hEL : E ≤ normalizer (L : Set (X ⧸ N)))
    (hSL : inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set (X ⧸ N))) ≤
      normalizer (L : Set (X ⧸ N))) :
    ((⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set (X ⧸ N))), E⁆ ⊔
        thetaT p E : Subgroup (X ⧸ N)) : Set (X ⧸ N)) =
      ((⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set (X ⧸ N))), E⁆ :
        Subgroup (X ⧸ N)) : Set (X ⧸ N)) * (thetaT p E : Set (X ⧸ N)) ∧
      ⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set (X ⧸ N))), E⁆ ⊔
        thetaT p E ≤ normalizer (L : Set (X ⧸ N)) ∧
      ⁅⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set (X ⧸ N))), E⁆, L⁆ = ⊥ ∧
      ⁅thetaT p E, L⁆ = ⊥ ∧
      ⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set (X ⧸ N))), E⁆ ⊔
        thetaT p E ≤ centralizer (L : Set (X ⧸ N)) := by
  set S := inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set (X ⧸ N))) with hS
  have hES : E ≤ normalizer (S : Set (X ⧸ N)) := fun x hx =>
    SteinbergBY.normalizer_le_normalizer_inSubgroup_aschbacherSolvableCore p _
      (le_normalizer (mem_centralizer_singleton_iff.mpr
        (SteinbergBY.mul_comm_of_isMulCommutative hx ht)))
  have hSE : ⁅S, E⁆ ≤ S := le_normalizer_iff_commutator_le_left.mp hES
  have hIS : thetaT p E ≤ S := fun x hx => by
    simp only [thetaT, mem_iInf] at hx
    exact hx t ht ht1
  obtain rfl : f = 1 := G2_defining_prime_actual_component_field_restriction hp hp3 N hN hX L hT
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := exists_mulEquiv_adjointGroup_of_untwisted hT.2
  have hcore : LocalCoreTrivialOn p fun _ : MulAut (adjointGroup .G2 K) => True :=
    localCoreTrivialOn_of_forall hp fun B hB α _ hαp =>
      ((prime_field_G2_order_p_centralizer_local_cores_trivial hp hp3 K
        (by rw [hK, pow_one])).2 B hB α hαp).2
  obtain ⟨hset, hW⟩ := component_local_core_product_centralizes_of_localCoreTrivialOn hp
    (by omega) hE hEcard ht ht1 hL hEL hSL (P := fun _ => True)
    (hcore.of_mulEquiv hp e.symm fun _ _ => trivial) trivial
  exact ⟨hset, sup_le (hSE.trans hSL) (hIS.trans hSL),
    commutator_eq_bot_iff_le_centralizer.mpr (le_sup_left.trans hW),
    commutator_eq_bot_iff_le_centralizer.mpr (le_sup_right.trans hW), hW⟩

end CFSG.RankThree.Chevalley
