module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi24ThreeCoverUpper
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi23Ident
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.RowAssembly
public import Certificates.Certificate291372

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi24Three

open CFSG.CosetTable CFSG.Sporadic.Presentation.Fi24Prime
  CFSG.Sporadic.Recognition.Fi24PrimeMultiplier CFSG.RankThree.PerfectCover CFSG.AGLEmbedding
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster

theorem sq_eq_true :
    (X0.getD sqIdx []).map (fun l => (l.1.val, l.2)) = [(8, true), (8, true)] :=
  Certificates.certificate291372.1

theorem q3_index :
    (genSub {r : FreeGroup (Fin nG) | r ∈ wsQ.map FreeGroup.mk} (subsetOf nG S0)).FiniteIndex ∧
      (genSub {r : FreeGroup (Fin nG) | r ∈ wsQ.map FreeGroup.mk} (subsetOf nG S0)).index ≤
        920808 :=
  Certificates.certificate291372.2.1

theorem q3_ord :
    3 ∣ orderOf (PresentedGroup.mk {r : FreeGroup (Fin nG) | r ∈ wsQ.map FreeGroup.mk}
      (FreeGroup.mk (zetaWord 10))) :=
  Certificates.certificate291372.2.2

theorem three_dvd_card_hopfMultiplier_PG_of_cert :
    3 ∣ Nat.card (hopfMultiplier (PG m0 X0)) :=
  three_dvd_card_hopfMultiplier_PG m0_eq q3_index q3_ord sq_eq_true

theorem three_dvd_card_hopfMultiplier_Fi24Prime :
    3 ∣ Nat.card (hopfMultiplier (CFSG.Blueprint.NativeSporadic.Carrier .Fi24Prime)) := by
  obtain ⟨e⟩ := nonempty_native_equiv
  have h : Nat.card (hopfMultiplier CFSG.Blueprint.NativeSporadic.Fi24prime) =
      Nat.card (hopfMultiplier (PG m0 X0)) :=
    card_hopfMultiplier_eq_of_mulEquiv (X := CFSG.Blueprint.NativeSporadic.Fi24prime)
      (Y := PG m0 X0) e
  have h3 := three_dvd_card_hopfMultiplier_PG_of_cert
  rw [← h] at h3
  exact h3

theorem nativeCell3_Fi24Prime_of_fi23
    (h : KernelTrivialAt (CFSG.Blueprint.NativeSporadic.Carrier .Fi23) 3) :
    PrimaryCentralKernelOrder (CFSG.Blueprint.NativeSporadic.Carrier .Fi24Prime) 3 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .Fi24Prime) =
      1255205709190661721292800 := CFSG.Sporadic.Fi24.card_Fi24prime
  have : Finite (CFSG.Blueprint.NativeSporadic.Carrier .Fi24Prime) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .Fi24Prime) :=
    CFSG.Sporadic.Fi24.isSimpleGroup_Fi24prime
  have : Group.IsPerfect (CFSG.Blueprint.NativeSporadic.Carrier .Fi24Prime) :=
    isPerfect_of_simple_card (X := CFSG.Blueprint.NativeSporadic.Carrier .Fi24Prime) hcard
  refine primaryCentralKernelOrder_of_bounds (p := 3) (k := 1)
    (fun E _ _ _ π hπ hC hpg => ?_) (by simpa using three_dvd_card_hopfMultiplier_Fi24Prime)
  obtain ⟨e⟩ : Nonempty (CFSG.Blueprint.NativeSporadic.Carrier .Fi24Prime ≃* PG m0 X0) :=
    nonempty_native_equiv
  have hk : (e.toMonoidHom.comp π).ker = π.ker := by
    ext x
    simp [MonoidHom.mem_ker]
  have h3 := card_ker_dvd_three_PG m0_eq q3_index sq_eq_true (kernelTrivial_PG10 h)
    (e.toMonoidHom.comp π) (e.surjective.comp hπ) (hk ▸ hC) (hk ▸ hpg)
  rw [hk] at h3
  simpa using h3

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi24Three
