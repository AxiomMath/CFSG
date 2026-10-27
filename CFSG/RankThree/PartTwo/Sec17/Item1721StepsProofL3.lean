module

public import CFSG.RankThree.PartTwo.Sec17.Item1721StepsProofK
import CFSG.RankThree.PartTwo.Sec4.LThreePiHessian
import CFSG.RankThree.PartTwo.Sec13.Item138NMod9
import CFSG.RankThree.PartTwo.KFacts.K72SylowL3
import CFSG.RankThree.PartTwo.Sec13.Item134SylowBarT
public import CFSG.RankThree.PartTwo.Sec17.Item1721StepsProofSW

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec16
open CFSG.Assembly.RankThreeEven (projImage)
open Matrix (ProjGenLinGroup)
open CFSG.ABGLocalTools (IsSylowOf)

namespace Proof1721

theorem not_three_dvd_one_add_sq (k : ℤ) : ¬ (3 : ℤ) ∣ 1 + k * k := by
  intro h
  have h' : ((1 + k * k : ℤ) : ZMod 3) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr h
  push_cast at h'
  generalize (k : ZMod 3) = r at h'
  revert r
  decide

theorem exists_inverting_of_fourier {X : Type} [Group X] [Finite X] {d c f : X}
    (hd3 : d ^ 3 = 1) (hc3 : c ^ 3 = 1) (hdc : d * c = c * d) (hc1 : c ≠ 1)
    (hfd : f * d * f⁻¹ = c⁻¹) (hfc : f * c * f⁻¹ = d) (h27 : ¬ 27 ∣ Nat.card X)
    {E : Subgroup X} (hE9 : Nat.card E = 9) :
    ∃ g ∈ Subgroup.normalizer (E : Set X), ∀ x ∈ E, g * x * g⁻¹ = x⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hd1 : d ≠ 1 := by
    rintro rfl
    apply hc1
    have := congrArg (fun y => f⁻¹ * y * f) hfc
    simpa [mul_assoc] using this
  have hdo : orderOf d = 3 := orderOf_eq_prime hd3 hd1
  have hco : orderOf c = 3 := orderOf_eq_prime hc3 hc1
  have hcd : c ∉ Subgroup.zpowers d := by
    intro hc
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    have h1 : f * d ^ k * f⁻¹ = (d ^ k)⁻¹ ^ k := by rw [← conj_zpow, hfd]
    rw [hfc, ← zpow_neg, ← zpow_mul] at h1
    have h2 : d ^ (1 + k * k) = 1 := by
      calc d ^ (1 + k * k) = d * d ^ (k * k) := by rw [zpow_add, zpow_one]
        _ = d ^ (-k * k) * d ^ (k * k) := by rw [← h1]
        _ = 1 := by rw [← zpow_add, show -k * k + k * k = 0 by ring, zpow_zero]
    have h3 := orderOf_dvd_iff_zpow_eq_one.mpr h2
    rw [hdo] at h3
    exact not_three_dvd_one_add_sq k (by exact_mod_cast h3)
  set E₀ := Subgroup.zpowers d ⊔ Subgroup.zpowers c with hE₀
  have hcN : Subgroup.zpowers c ≤ Subgroup.normalizer (Subgroup.zpowers d : Set X) := by
    refine Subgroup.zpowers_le.mpr (Subgroup.mem_normalizer_fintype fun y hy => ?_)
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [SetLike.mem_coe, ← conj_zpow, show c * d * c⁻¹ = d by rw [← hdc, mul_inv_cancel_right]]
    exact Subgroup.zpow_mem_zpowers d k
  have hdisj : Disjoint (Subgroup.zpowers d) (Subgroup.zpowers c) :=
    disjoint_iff.mpr (inf_zpowers_eq_bot hco hcd)
  have hE₀9 : Nat.card E₀ = 9 := by
    rw [hE₀, CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hcN hdisj,
      Nat.card_zpowers, Nat.card_zpowers, hdo, hco]
  have h27' : ¬ 27 ∣ Nat.card (⊤ : Subgroup X) := by rwa [Subgroup.card_top]
  obtain ⟨m, -, hm⟩ := Item134SylowBarProof.exists_conj_of_isSylowOf
    (isSylowOf_of_card_nine le_top hE₀9 h27') (isSylowOf_of_card_nine le_top hE9 h27')
  set t := f * f with ht
  have htd : t * d * t⁻¹ = d⁻¹ := by
    calc t * d * t⁻¹ = f * (f * d * f⁻¹) * f⁻¹ := by rw [ht]; group
      _ = (f * c * f⁻¹)⁻¹ := by rw [hfd]; group
      _ = d⁻¹ := by rw [hfc]
  have htc : t * c * t⁻¹ = c⁻¹ := by
    calc t * c * t⁻¹ = f * (f * c * f⁻¹) * f⁻¹ := by rw [ht]; group
      _ = c⁻¹ := by rw [hfc, hfd]
  have htE₀ : ∀ y ∈ E₀, t * y * t⁻¹ = y⁻¹ := by
    intro y hy
    obtain ⟨i, j, rfl⟩ := Sec4.exists_zpow_mul_of_mem_sup hdc hy
    have hcomm : Commute (d ^ i) (c ^ j) := Commute.zpow_zpow hdc i j
    calc t * (d ^ i * c ^ j) * t⁻¹ = (t * d * t⁻¹) ^ i * (t * c * t⁻¹) ^ j := by
          rw [conj_zpow, conj_zpow]; group
      _ = (d ^ i * c ^ j)⁻¹ := by
          rw [htd, htc, inv_zpow', inv_zpow', mul_inv_rev, ← zpow_neg, ← zpow_neg]
          exact (Commute.zpow_zpow hdc (-i) (-j)).eq
  refine ⟨m * t * m⁻¹, mem_normalizer_of_conj_eq_inv fun x hx => ?_, fun x hx => ?_⟩ <;>
  · rw [hm] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    change m * t * m⁻¹ * (m * y * m⁻¹) * (m * t * m⁻¹)⁻¹ = (m * y * m⁻¹)⁻¹
    calc m * t * m⁻¹ * (m * y * m⁻¹) * (m * t * m⁻¹)⁻¹ = m * (t * y * t⁻¹) * m⁻¹ := by group
      _ = (m * y * m⁻¹)⁻¹ := by rw [htE₀ y hy]; group

theorem ks1721InvertL3_proof : KS1721InvertL3 := by
  intro X _ _ hX E hE9 _ h27
  obtain ⟨p, e, hp, he, hiso⟩ := hX
  obtain ⟨π, K, _, hK, hq, ⟨φ⟩⟩ := exists_projImage_model he hiso
  have hπ : π = false → CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p e K := fun h => by
    subst h; exact hK.unitary
  have hq' : π = false → Sec4.ModThree false (p ^ e) := fun h => by subst h; exact hq
  obtain ⟨τ, hτ, hτ1⟩ := Sec4.exists_tau hK hq
  have h3 := hK.three_ne_zero hq
  have hs := Sec4.one_add_tau_add_sq hτ hτ1
  set H := Sec4.slPi π 3 (p ^ e) K with hH
  set D : projImage H := Sec4.projOf H ⟨Sec4.diagTau hτ, Sec4.diagTau_mem_slPi hπ hq' hτ⟩
  set C : projImage H := Sec4.projOf H ⟨Sec4.cycThree, Sec4.cycThree_mem_slPi hπ⟩
  set F : projImage H :=
    Sec4.projOf H ⟨Sec4.fourierGL h3 hs, Sec4.fourierGL_mem_slPi hK hq hτ h3 hs⟩
  have hFD : F * D * F⁻¹ = C⁻¹ := Subtype.ext (Sec4.mk_fourier_diagTau hτ h3 hs)
  have hFC : F * C * F⁻¹ = D := Subtype.ext (Sec4.mk_fourier_cycThree hτ h3 hs)
  have hDC : D * C = C * D := Subtype.ext (Sec4.mk_diagTau_cycThree hτ)
  have hC3 : C ^ 3 = 1 := by
    apply Subtype.ext
    change ProjGenLinGroup.mk Sec4.cycThree ^ 3 = 1
    rw [← map_pow, Sec4.cycThree_pow_three, map_one]
  have hC1 : C ≠ 1 := fun h => KFacts.mk_cycThree_ne_one (K := K) (congrArg Subtype.val h)
  have hD3 : D ^ 3 = 1 := by
    rw [← hFC, conj_pow, hC3, mul_one, mul_inv_cancel]
  have hX27 : ¬ 27 ∣ Nat.card X := h27
  refine exists_inverting_of_fourier (d := φ.symm D) (c := φ.symm C) (f := φ.symm F)
    (by rw [← map_pow, hD3, map_one]) (by rw [← map_pow, hC3, map_one])
    (by rw [← map_mul, hDC, map_mul])
    (fun h => hC1 (φ.symm.injective (h.trans φ.symm.map_one.symm)))
    (by rw [← map_inv, ← map_mul, ← map_mul, hFD, map_inv])
    (by rw [← map_inv, ← map_mul, ← map_mul, hFC]) hX27 hE9

end Proof1721

open Proof1721 in
theorem ks1721Invert_proof : KS1721Invert :=
  ks1721Invert_of ks1721InvertL3_proof

end CFSG.RankThree.PartTwo.Sec17
