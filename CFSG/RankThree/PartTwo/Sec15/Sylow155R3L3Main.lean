module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R3Defs
public import CFSG.RankThree.PartTwo.Sec4.LThreePiDefs
public import CFSG.RankThree.PartTwo.Sec4.Census.Open46
import CFSG.RankThree.PartTwo.KFacts.K72SLPiCField
import CFSG.RankThree.PartTwo.KFacts.KS12SLCenter
import CFSG.RankThree.PartTwo.Sec4.Census.CoverSLThree46
import CFSG.RankThree.PartTwo.Sec15.Sylow155R3L3Abs
import CFSG.RankThree.PartTwo.Sec15.Sylow155R3L3Inner
import CFSG.RankThree.PartTwo.Sec15.Sylow155R3L3Outer

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R3

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4

theorem res3L3TwoModel_holds :
    ∀ (π : Bool) (f : ℕ) (K : Type) [Field K], PiField π 2 f K → ModThree π (2 ^ f) →
      2 < 2 ^ f → ∀ (c g : MulAut (slPi π 3 (2 ^ f) K))
        (V U : Subgroup (MulAut (slPi π 3 (2 ^ f) K))), ¬ Res3Datum c g V U := by
  intro π f K _ hK hq hq2 c g V U h
  rcases KFacts.exists_conj_or_field_of_pow_three_eq_one hK hq2 h.c_pow with
    ⟨y, hy, hcy⟩ | ⟨σ, hσ, H, hH, hcH⟩
  · by_cases hin : c ∈ (MulAut.conj : slPi π 3 (2 ^ f) K →* MulAut (slPi π 3 (2 ^ f) K)).range
    · obtain ⟨j, hj⟩ := hin
      cases π
      · exact false_of_inner_unitary hK hq hq2 h hj
      · exact false_of_inner_linear hK hq h hj
    · exact false_of_semiAct_outer hK hq hq2 h hin hy hcy
  · have hσ3 : σ ^ 3 = 1 := by
      rw [← hσ]
      exact pow_orderOf_eq_one σ
    exact false_of_field_aut_datum hK hq h hσ3 hH hcH

private theorem two_lt_two_pow_of_isoLThreePi {J : Type} [Group J] (hq : IsQuasisimple J)
    {e : ℕ} (he : 1 ≤ e) (hpi : IsoLThreePi (J ⧸ Subgroup.center J) 2 e) : 2 < 2 ^ e := by
  have h2e : 2 ≤ 2 ^ e := Nat.le_self_pow (by omega) 2
  rcases hpi with ⟨h1, -⟩ | ⟨-, ⟨f⟩⟩
  · by_contra hle
    have h2' : 2 ^ e = 2 := by omega
    rw [h2'] at h1
    norm_num at h1
  · by_contra hle
    have he1 : e = 1 := by
      by_contra hne
      have : 2 ^ 2 ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    subst he1
    exact Sec4.Census.false_of_isQuasisimple_projSU_three_two hq f

theorem res3NoDatumL3Two_of (hcov : Sec4.Census.CoverSLThree46) :
    Res3NoDatumL3Two := by
  have hmodel := res3L3TwoModel_holds
  intro J _ _ _ hq e he hiso c g V U hd
  have hX := hcov J hq hd.center_pGroup hd.center_ne 2 e he (Or.inl rfl) hiso
  have hmod : 2 ^ e % 3 = 1 ∨ 2 ^ e % 3 = 2 := hiso.imp (fun h => h.1) (fun h => h.1)
  obtain ⟨π, K, _, hK, hq3, ⟨φ⟩⟩ := KFacts.exists_slPi_of_isSLThreePiAt_two_pow he
    (KFacts.isSLThreePiAt_of_isSLThreeEpsAt he hX hmod hd.center_ne)
  exact hmodel π e K hK hq3 (two_lt_two_pow_of_isoLThreePi hq he hiso) _ _ _ _
    (hd.of_mulEquiv_congr φ)

theorem res3NoDatumL3Two_holds :
    Res3NoDatumL3Two :=
  res3NoDatumL3Two_of Sec4.Census.coverSLThree46

end CFSG.RankThree.PartTwo.Sec15.Sylow155R3
