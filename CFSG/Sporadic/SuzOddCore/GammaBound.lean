module

public import Certificates.Certificate2294

public noncomputable section

namespace CFSG.Sporadic.SuzOddCore

open CFSG.Certificates CFSG.Monster.B.Co2

theorem suzGamma_adj_zero
    (i : Fin 22880) : suzGamma.Adj 0 i ↔ i ∈ suzDeltaΩ :=
  Certificates.certificate2294.1 i

theorem gammaStab_orbit
    {s : ℕ} (hs : s < 4) :
    (MulAction.orbit (gammaStab s) (gammaBasePt s)).ncard ≤ gammaBounds s :=
  Certificates.certificate2294.2.1 s hs

theorem gammaStab_four :
    gammaStab 4 = ⊥ :=
  Certificates.certificate2294.2.2

theorem CTUC_Suz_graph_automorphism_order_bound :
    Nat.card (suzGamma ≃g suzGamma) ≤ 896690995200 ∧
    (∀ s < 4, (MulAction.orbit (gammaStab s) (gammaBasePt s)).ncard ≤ gammaBounds s) ∧
    gammaStab 4 = ⊥ ∧
    (∀ (s : ℕ) (σ : suzGamma ≃g suzGamma),
      σ ∈ gammaStab s ↔ ∀ j < s, σ (gammaBasePt j) = gammaBasePt j) ∧
    (∀ s < 4, ((gammaBasePt s : Fin 22880) : ℕ) = s) ∧
    [gammaBounds 0, gammaBounds 1, gammaBounds 2, gammaBounds 3] = [22880, 8505, 1152, 4] := by
  refine ⟨?_, fun s hs => gammaStab_orbit hs, gammaStab_four, fun s σ => mem_gammaStab,
    fun s hs => gammaBasePt_val (by omega), rfl⟩
  have h := card_le_prod_of_stabChain (G := suzGamma ≃g suzGamma) gammaBasePt gammaBounds 4
    (fun s hs => gammaStab_orbit hs) gammaStab_four
  refine h.trans (le_of_eq ?_)
  simp only [Finset.prod_range_succ, Finset.prod_range_zero]
  rfl

end CFSG.Sporadic.SuzOddCore
