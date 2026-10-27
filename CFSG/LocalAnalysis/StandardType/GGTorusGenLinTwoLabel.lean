module

public import CFSG.LocalAnalysis.StandardType.GGTorusGenLinTwo
public import CFSG.LocalAnalysis.StandardType.GGTorusGenRTransfer
public import CFSG.LocalAnalysis.StandardType.GGTorusGenSLTransfer
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineL2Cover
public import CFSG.LocalAnalysis.StandardType.GGTableBTwoThreeTorus
public import CFSG.LocalAnalysis.StandardType.GGSlNsRootGenModel
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherConjAutInner

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem largeEvenLabelAll_torusGenTableB_linTwo {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (hrow : GGLinTwoLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusGenTableB p R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨ht, hl, hn, hp3⟩ := hrow
  dsimp only at ht hl hn hp3
  subst ht hn hp3
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, hfield, hfinite, hK, hQ'⟩ := hQ
  refine ⟨K, hfield, hfinite, hK, hQ', ?_⟩
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK2 : Nat.card K = 2 := by simpa using hK
  have : CharP K 2 :=
    charP_of_card_eq_prime_pow (R := K) (p := 2) (f := 1)
      (by rw [← Nat.card_eq_fintype_card]; exact hK)
  have hd : 6 ≤ l + 1 := by omega
  have hd5 : 5 ≤ l + 1 := by omega
  have hI : ∀ φ ∈ Set.range (conjAut (l + 1) K), φ ^ 3 = 1 →
      φ ∈ Set.range
        (MulAut.conj : projectiveSL (l + 1) K →* MulAut (projectiveSL (l + 1) K)) := by
    rintro φ ⟨A, rfl⟩ _
    have hcard_units : Nat.card Kˣ = 1 := by rw [Nat.card_units, hK2]
    have : Subsingleton Kˣ :=
      Finite.card_le_one_iff_subsingleton.mp (by rw [hcard_units])
    have hdet : GeneralLinearGroup.det A = 1 := Subsingleton.elim _ _
    exact conjAut_mem_range_conj_of_det_eq_pow
      (n := l + 1) (A := A) (μ := 1) (by simpa using hdet)
  have hZ : Subgroup.center (projectiveSL (l + 1) K) = ⊥ :=
    SlNsRootGen.center_projectiveSL_eq_bot_charTwo
  have hcp : GGCenterPrime 3 (projectiveSL (l + 1) K) := by
    intro L' _ _ ψ hψ hker hperf
    have hcop := LineL2.ggCenterCoprime_psl_two (K := K) hK2 hd5
    have hcenter : Subgroup.center L' = ψ.ker := by
      refine le_antisymm ?_ hker
      intro z hz
      rw [MonoidHom.mem_ker]
      have hzc : ψ z ∈ Subgroup.center (projectiveSL (l + 1) K) := by
        rw [Subgroup.mem_center_iff]
        intro r
        obtain ⟨l', rfl⟩ := hψ r
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz l']
      rw [hZ, Subgroup.mem_bot] at hzc
      exact hzc
    rw [hcenter]
    exact hcop L' ψ hψ hker hperf
  have hgen : GGTorusGenR 3 ((l + 1) / 2) (projectiveSL (l + 1) K) :=
    ggTorusGenR_linTwo hK2 hd
  have hRk : GGTorusGenTableBRk 3 (projectiveSL (l + 1) K)
      (Set.range (conjAut (l + 1) K)) ((l + 1) / 2 + 1) :=
    ggTorusGenTableBRk_of_torusGenR (r := (l + 1) / 2) hp hI hZ hcp hgen
  have hL : GGTorusLift 3 ((l + 1) / 2) (projectiveSL (l + 1) K) :=
    TwoThree.ggTorusLift_two hK2 hd5
  refine ggTorusGenTableB_of_mulEquiv (R' := projectiveSL (l + 1) K)
    (I' := Set.range (conjAut (l + 1) K)) (TypeA.recipeEquiv (l + 1) K) ?_ ?_
  · intro φ hφ
    exact TypeA.congr_recipeEquiv_mem hφ
  · exact ggTorusGenTableB_of_rk (r := (l + 1) / 2 + 1) hp (by omega)
      (by simpa using hL) hRk

end CFSG.StandardType
