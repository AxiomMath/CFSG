module

public import CFSG.LocalAnalysis.UniquenessCase.UC6Dict
public import CFSG.LocalAnalysis.UniquenessCase.UC6Syl
public import CFSG.LocalAnalysis.RankThreeUC.StronglyEmbedded

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup CFSG.Open CFSG.ABGLocalTools
open CFSG.Yardstones.Mf4cdcdf2e013 (TheoremCAt)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

theorem inU_of_theoremC {M : Subgroup G} (hM : uniqueFourIsMaxTwoLocal M) (hC : TheoremCAt M)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) {E : Subgroup G} (hEM : E ≤ M)
    (hEel : IsElemAbelian r E) (hEcard : Nat.card E = r ^ 2)
    (hΓ : rankThreeGamma 1 r E ≤ M) : InU M E := by
  refine ⟨hEM, fun g hg => ?_⟩
  have hg' := isMaxTwoLocal_conj hM g
  have hE2 : 2 ≤ Open.pRank r E := le_pRank_of_elemAbelian hr le_rfl hEel hEcard
  have hle : uniqueFourConj g M ≤ M :=
    hC r hr hr2 E hEM (IsElemAbelian.isPGroup hEel) hE2 hΓ _ hg'.1 hg
  exact (hg'.2 M hM.1 hle).symm

theorem normalizer_le_of_inU {M E Q : Subgroup G} (hMself : normalizer (M : Set G) = M)
    (hEU : InU M E) (hEQ : E ≤ centralizer (Q : Set G)) (hQM : centralizer (Q : Set G) ≤ M) :
    normalizer (Q : Set G) ≤ M := by
  intro n hn
  refine ((inU_iff_fixed hMself).1 hEU).2 n fun x hx => hQM ?_
  rw [mem_centralizer_iff]
  intro q hq
  have h1 : n * q * n⁻¹ ∈ Q := (mem_normalizer_iff.1 hn q).1 hq
  have h2 : (n * q * n⁻¹) * x = x * (n * q * n⁻¹) := mem_centralizer_iff.1 (hEQ hx) _ h1
  calc q * (n⁻¹ * x * n) = n⁻¹ * ((n * q * n⁻¹) * x) * n := by group
    _ = n⁻¹ * (x * (n * q * n⁻¹)) * n := by rw [h2]
    _ = (n⁻¹ * x * n) * q := by group

theorem exists_Z_of_not_isStronglyPEmbedded {M : Subgroup G} (hM : uniqueFourIsMaxTwoLocal M)
    (hMtop : M ≠ ⊤) (hC : TheoremCAt M) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) {R E : Subgroup G}
    (hR : IsSylowOf r R M) (hER : E ≤ R ⊓ centralizer (R : Set G)) (hEel : IsElemAbelian r E)
    (hEcard : Nat.card E = r ^ 2) (hΓ : rankThreeGamma 1 r E ≤ M)
    (hns : ¬ IsStronglyPEmbedded r M) :
    ∃ Z : Subgroup G, Z ≤ R ∧ Nat.card Z = r ∧ ¬ centralizer (Z : Set G) ≤ M := by
  haveI : Fact r.Prime := ⟨hr⟩
  by_contra hcon
  push Not at hcon
  have hMself : normalizer (M : Set G) = M := normalizer_eq_of_isMaxTwoLocal hM
  have hEM : E ≤ M := fun x hx => hR.le (hER hx).1
  have hEU : InU M E := inU_of_theoremC hM hC hr hr2 hEM hEel hEcard hΓ
  have hQR : ∀ Q : Subgroup G, Q ≤ R → Q ≠ ⊥ → normalizer (Q : Set G) ≤ M := by
    intro Q hQR hQ1
    have hQp : IsPGroup r Q := hR.isPGroup.to_le hQR
    have hdvd : r ∣ Nat.card Q := hQp.card_eq_or_dvd.resolve_left fun h =>
      hQ1 (Subgroup.card_eq_one.mp h)
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' r hdvd
    have hxQ : (x : G) ∈ Q := x.2
    have hxo : orderOf (x : G) = r := (Subgroup.orderOf_coe x).trans hx
    have hZcard : Nat.card (zpowers (x : G)) = r := by rw [Nat.card_zpowers, hxo]
    have hZR : zpowers (x : G) ≤ R := zpowers_le.2 (hQR hxQ)
    have hCZ : centralizer (zpowers (x : G) : Set G) ≤ M := hcon _ hZR hZcard
    have hCQ : centralizer (Q : Set G) ≤ M := by
      refine le_trans (Subgroup.centralizer_le ?_) hCZ
      exact SetLike.coe_subset_coe.2 (zpowers_le.2 hxQ)
    have hEQ : E ≤ centralizer (Q : Set G) := by
      intro e he
      rw [mem_centralizer_iff]
      intro q hq
      exact mem_centralizer_iff.1 (hER he).2 q (hQR hq)
    exact normalizer_le_of_inU hMself hEU hEQ hCQ
  have hdvdM : r ∣ Nat.card M := by
    have h1 : r ∣ Nat.card E := by
      rw [hEcard]
      exact dvd_pow_self r two_ne_zero
    exact h1.trans (Subgroup.card_dvd_of_le hEM)
  refine hns (CFSG.LocalAnalysis.RankThreeUC.isStronglyPEmbedded_of_normalizer_le hMtop hdvdM ?_)
  intro Q hQ1 hQp hQM
  obtain ⟨k, hkM, hk⟩ := exists_conj_le_of_isSylowOf hR hQM hQp
  have hQ'R : uniqueFourConj k Q ≤ R := fun y hy => by
    rw [mem_uniqueFourConj_iff] at hy
    have := hk _ hy
    simpa [mul_assoc] using this
  have hQ'1 : uniqueFourConj k Q ≠ ⊥ := uniqueFourConj_ne_bot hQ1 k
  have hN := hQR _ hQ'R hQ'1
  intro n hn
  have hn' : k⁻¹ * n * k ∈ normalizer (uniqueFourConj k Q : Set G) := by
    rw [mem_normalizer_iff]
    intro y
    rw [mem_uniqueFourConj_iff, mem_uniqueFourConj_iff]
    have e1 : k * (k⁻¹ * n * k * y * (k⁻¹ * n * k)⁻¹) * k⁻¹ = n * (k * y * k⁻¹) * n⁻¹ := by
      group
    rw [e1]
    exact mem_normalizer_iff.1 hn (k * y * k⁻¹)
  have := hN hn'
  have h2 : n = k * (k⁻¹ * n * k) * k⁻¹ := by group
  rw [h2]
  exact M.mul_mem (M.mul_mem hkM this) (M.inv_mem hkM)

end CFSG.LocalAnalysis.UniquenessCase.UC6
