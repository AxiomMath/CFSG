module

public import CFSG.LocalAnalysis.StandardType.GGPhiTwoGenE7D0
public import CFSG.LocalAnalysis.StandardType.GGPhiTwoGenE7TorusDiag
public import CFSG.LocalAnalysis.StandardType.GGPhiTwoRootGenDefs

public section

namespace CFSG.StandardType.PhiTwoRootGen

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley Multiplicative
open CFSG.LieType.SeitzGeneration.ExcHigh CFSG.ComponentClassification.CatLeafProof
open CFSG.StandardType.TableBExc.E6Three

private theorem coprime_pred_of_dvd_succ {p c : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hc : 1 ≤ c)
    (h : p ∣ c + 1) : Nat.Coprime p (c - 1) := by
  rw [Nat.Prime.coprime_iff_not_dvd hp]
  intro h2
  have h3 : p ∣ (c + 1) - (c - 1) := Nat.dvd_sub h h2
  have h4 : (c + 1) - (c - 1) = 2 := by omega
  rw [h4] at h3
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h3)

theorem e7_torus_of_mem_phiTwoA1D6Subgroup
    {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K + 1)
    {g0 : ModGL .E7 (AlgebraicClosure K)} (hg0C : g0 ∈ adjointGroup .E7 (AlgebraicClosure K))
    (hg0D : g0 ∈ phiTwoA1D6Subgroup (AlgebraicClosure K)) {ζ : (AlgebraicClosure K)ˣ}
    (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1)
    {T : Multiplicative (Fin Tag.E7.rank → ZMod p) →* adjointGroup .E7 K}
    (hT : ∀ t : Fin Tag.E7.rank → ZMod p,
      baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((T (ofAdd t) : adjointGroup .E7 K) : ModGL .E7 K) =
        g0 * rootDiagUnit .E7 (TableBExc.E6Three.zetaVec ζ hζ t) * g0⁻¹) :
    (∀ t : Fin Tag.E7.rank → ZMod p, ∑ j, (e7Theta j : ZMod p) * t j = 0 →
      T (ofAdd t) ∈ e7D6Group K) ∧
    (∀ s : ZMod p, T (ofAdd (Pi.single (0 : Fin Tag.E7.rank) s)) ∈ rootPairE7 K e7Theta) ∧
    rootPairE7 K e7Theta ≤ phiTwoComp g0 e7Theta := by
  obtain ⟨a, ha, b, hb, hg0, -⟩ := exists_mul_eq_of_mem_phiTwoA1D6Subgroup
    (by
      intro y
      obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq y (by norm_num : 0 < 2)
      exact ⟨z, by simpa [pow_two] using hz⟩)
    hg0D
  have hcom : ∀ x ∈ rootSpan .E7 (AlgebraicClosure K) e7D6Roots,
      ∀ y ∈ rootSpan .E7 (AlgebraicClosure K) {e7Theta, -e7Theta}, x * y = y * x :=
    fun x hx y hy => (commute_rootSpan_D6_theta hx hy).eq
  have hcop : Nat.Coprime p (Nat.card K - 1) :=
    coprime_pred_of_dvd_succ (Fact.out) hp2 (Nat.card_pos (α := K)) hpq
  have hTpow : ∀ t : Fin Tag.E7.rank → ZMod p, (T (ofAdd t)) ^ p = 1 := by
    intro t
    rw [← map_pow, ← ofAdd_nsmul]
    have h0 : p • t = 0 := by
      funext j
      simp
    rw [h0]
    exact map_one T
  obtain ⟨-, hA, -⟩ := ggPhiTwoD0_structural (K := K)
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    have hd := rootDiagUnit_zetaVec_mem_rootSpan_D6 (L := AlgebraicClosure K) hp2 hζ ht
    refine mem_e7D6Group_of_baseChangeGL_mem_rootSpan hcop (hTpow t) ?_
    rw [hT t, hg0]
    have hbd : b * rootDiagUnit .E7 (zetaVec ζ hζ t) * b⁻¹ = rootDiagUnit .E7 (zetaVec ζ hζ t) := by
      rw [← hcom _ hd b hb]
      group
    have hcalc : a * b * rootDiagUnit .E7 (zetaVec ζ hζ t) * (a * b)⁻¹ =
        a * rootDiagUnit .E7 (zetaVec ζ hζ t) * a⁻¹ := by
      calc a * b * rootDiagUnit .E7 (zetaVec ζ hζ t) * (a * b)⁻¹
          = a * (b * rootDiagUnit .E7 (zetaVec ζ hζ t) * b⁻¹) * a⁻¹ := by group
        _ = a * rootDiagUnit .E7 (zetaVec ζ hζ t) * a⁻¹ := by rw [hbd]
    rw [hcalc]
    exact mul_mem (mul_mem ha hd) (inv_mem ha)
  · intro s
    have hd := rootDiagUnit_zetaVec_single_mem_rootSpan_theta (L := AlgebraicClosure K) hζ s
    refine mem_rootPairE7_of_baseChangeGL_mem_rootSpan hcop (hTpow _) ?_
    rw [hT, hg0]
    have hy : b * rootDiagUnit .E7 (zetaVec ζ hζ (Pi.single (0 : Fin Tag.E7.rank) s)) * b⁻¹ ∈
        rootSpan .E7 (AlgebraicClosure K) {e7Theta, -e7Theta} :=
      mul_mem (mul_mem hb hd) (inv_mem hb)
    have hcalc : a * b * rootDiagUnit .E7 (zetaVec ζ hζ (Pi.single (0 : Fin Tag.E7.rank) s)) *
        (a * b)⁻¹ =
        b * rootDiagUnit .E7 (zetaVec ζ hζ (Pi.single (0 : Fin Tag.E7.rank) s)) * b⁻¹ := by
      calc a * b * rootDiagUnit .E7 (zetaVec ζ hζ (Pi.single (0 : Fin Tag.E7.rank) s)) *
            (a * b)⁻¹
          = a * (b * rootDiagUnit .E7 (zetaVec ζ hζ (Pi.single (0 : Fin Tag.E7.rank) s)) *
              b⁻¹) * a⁻¹ := by group
        _ = b * rootDiagUnit .E7 (zetaVec ζ hζ (Pi.single (0 : Fin Tag.E7.rank) s)) * b⁻¹ := by
          rw [hcom a ha _ hy]
          group
    rw [hcalc]
    exact hy
  · intro x hx
    rw [mem_phiTwoComp_iff]
    have hxK : ((x : adjointGroup .E7 K) : ModGL .E7 K) ∈ rootSpan .E7 K {e7Theta, -e7Theta} := by
      rw [hA]
      exact Subgroup.mem_map_of_mem _ hx
    have hx' := CFSG.RankThree.Classical2.baseChangeGL_mem_rootSpan
      (algebraMap K (AlgebraicClosure K)) hxK
    set x' := baseChangeGL (algebraMap K (AlgebraicClosure K))
      ((x : adjointGroup .E7 K) : ModGL .E7 K)
      with hx'def
    have hax : a * x' = x' * a := hcom a ha x' hx'
    have hcalc : g0⁻¹ * x' * g0 = b⁻¹ * x' * b := by
      rw [hg0]
      have h1 : a⁻¹ * x' * a = x' := by
        rw [mul_assoc, ← hax]
        group
      calc (a * b)⁻¹ * x' * (a * b) = b⁻¹ * (a⁻¹ * x' * a) * b := by group
        _ = b⁻¹ * x' * b := by rw [h1]
    rw [hcalc]
    exact mul_mem (mul_mem (inv_mem hb) hx') hb

end CFSG.StandardType.PhiTwoRootGen

end
