module

public import CFSG.RankThree.PartTwo.Sec20.SimsAsc1412L3Excl
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115OddL3AutClass
import CFSG.ClassicalInvolution.Q3.TL4E3S3GenL3
import CFSG.RankThree.PartTwo.Sec21.Item211Res6ProofGraphConj

public section

namespace CFSG.RankThree.PartTwo.Sec20

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups

theorem inv_transpose_eq_transpose_inv_exc {K : Type} [Field K] (X : SL(3, K)) :
    (X⁻¹).transpose = (X.transpose)⁻¹ := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_inv, Matrix.SpecialLinearGroup.coe_transpose]
  rw [Matrix.adjugate_transpose]

theorem excl1412_projectiveSL3_of_exc {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {t : projectiveSL 3 (GaloisField p 1)} (ht : orderOf t = 2)
    (hinner : Excl1412 (MulAut.conj t)) (hgraph : Excl1412 (dualAut 3 (GaloisField p 1)))
    (β : MulAut (projectiveSL 3 (GaloisField p 1))) (hβ : orderOf β = 2) : Excl1412 β := by
  have hF : Nat.card (GaloisField p 1) = p := by rw [GaloisField.card p 1 one_ne_zero, pow_one]
  have h2 : (2 : GaloisField p 1) ≠ 0 := by
    intro h0
    have := (CharP.cast_eq_zero_iff (GaloisField p 1) p 2).mp (by exact_mod_cast h0)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp this)
  have hodd : Odd (Nat.card (GaloisField p 1)) := by
    rw [hF]
    exact (Fact.out : p.Prime).odd_of_ne_two hp2
  have hβ2 : β * β = 1 := by rw [← sq, ← hβ, pow_orderOf_eq_one]
  rcases CFSG.QuasithinUnique.Ch1.classify_involution hF h2 β hβ2 with ⟨g, hg⟩ | ⟨A, -, hβA⟩
  ·
    have hβs : β = MulAut.conj g⁻¹ := by
      ext x
      rw [hg x, MulAut.conj_apply, inv_inv]
    have hZ := CFSG.RankThree.RegularUnipotent.center_projectiveSL_eq_bot
      (k := GaloisField p 1) (n := 3) le_rfl
    have hs : orderOf g⁻¹ = 2 := by
      refine orderOf_eq_prime ?_ fun h1 => ?_
      · have hc : MulAut.conj (g⁻¹ ^ 2) = 1 := by rw [map_pow, ← hβs, ← hβ, pow_orderOf_eq_one]
        have hmem : g⁻¹ ^ 2 ∈ Subgroup.center (projectiveSL 3 (GaloisField p 1)) := by
          rw [Subgroup.mem_center_iff]
          intro y
          have e := congrArg (fun φ : MulAut (projectiveSL 3 (GaloisField p 1)) => φ y) hc
          simp only [MulAut.conj_apply, MulAut.one_apply] at e
          calc y * g⁻¹ ^ 2 = g⁻¹ ^ 2 * y * (g⁻¹ ^ 2)⁻¹ * g⁻¹ ^ 2 := by rw [e]
            _ = g⁻¹ ^ 2 * y := by group
        rw [hZ, Subgroup.mem_bot] at hmem
        exact hmem
      · rw [h1, map_one] at hβs
        rw [hβs, orderOf_one] at hβ
        exact absurd hβ (by norm_num)
    obtain ⟨k, hk⟩ := CFSG.ClassicalInvolution.Q3.TL4.E3S3Gen.exists_conj_psl3 hodd hs ht
    have hβk : β = MulAut.conj k⁻¹ * MulAut.conj t * (MulAut.conj k⁻¹)⁻¹ := by
      rw [hβs, ← hk]
      simp only [map_mul, map_inv]
      group
    rw [hβk]
    exact hinner.conj _
  ·
    have h1 : fieldAut 3 (GaloisField p 1) 1 = 1 := map_one _
    obtain ⟨k, -, hk⟩ := CFSG.RankThree.PartTwo.Sec21.Item211Res6Proof.exists_graph_conj
      (K := GaloisField p 1) (p := p) hp2 (A := A) (σ := 1) (ρ := 1)
      (by rw [h1, mul_one, mul_one, one_mul]) (m := 0)
      (by rw [h1, mul_one, zpow_zero, ← hβA, sq, hβ2])
    rw [h1, mul_one, one_mul, ← hβA] at hk
    rw [hk]
    exact hgraph.conj _

end CFSG.RankThree.PartTwo.Sec20
