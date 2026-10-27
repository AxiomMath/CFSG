module

public import CFSG.RankThree.PartTwo.Sec13.F135LastR3Comp
public import CFSG.RankThree.PartTwo.Sec13.F135LastR3Cube
public import CFSG.RankThree.PartTwo.Sec13.F135LastR5Lift

public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open scoped commutatorElement

theorem r3_p_dvd_component {N : Type} [Group N] [Finite N] {p : ℕ} (hp : p.Prime)
    (hno : ∀ A T : Subgroup N, CFSG.Open.IsElemAbelian p A → Nat.card A = p ^ 3 → T ≠ ⊥ →
      IsPGroup 2 T → ¬ A ≤ Subgroup.normalizer (T : Set N))
    {F : Subgroup N} (hF : CFSG.Open.IsElemAbelian p F) (hF3 : Nat.card F = p ^ 3)
    {J : Subgroup N} (hJ : CFSG.IsComponent J) : p ∣ Nat.card J := by
  by_contra hK
  have hFp : IsPGroup p F := IsPGroup.of_card hF3
  have hBp : IsPGroup p (F ⊓ Subgroup.normalizer (J : Set N) : Subgroup N) := hFp.to_inf_left
  have hBN : F ⊓ Subgroup.normalizer (J : Set N) ≤ Subgroup.normalizer (J : Set N) :=
    inf_le_right
  obtain ⟨T, hTsyl, hBT⟩ :=
    CFSG.RankThree.PartTwo.Sec13.F135Last.exists_invariant_sylow_two hp hBp hBN hK
  have hTne : T ≠ ⊥ := r3_sylow_two_ne_bot hJ hTsyl
  have hTJ : T ≤ J := hTsyl.le
  have hT2 : IsPGroup 2 T := hTsyl.isPGroup
  obtain ⟨T', hTT', hT'2, hFT'⟩ := r3_orbit_two hJ hTJ hT2 hBT
  have hT'ne : T' ≠ ⊥ := by
    intro h
    rw [h] at hTT'
    exact hTne (le_bot_iff.mp hTT')
  exact hno F T' hF hF3 hT'ne hT'2 hFT'

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open scoped commutatorElement

theorem r3h_exists_order_mem {N : Type} [Group N] [Finite N] {p : ℕ} (hp : p.Prime)
    {J : Subgroup N} (hd : p ∣ Nat.card J) : ∃ w : N, w ∈ J ∧ orderOf w = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hd
  exact ⟨(x : N), x.2, by rw [Subgroup.orderOf_coe, hx]⟩

theorem r3h_mem_normalizer_of_commute {N : Type} [Group N] {S J K : Subgroup N}
    (hSK : S ≤ K) (hJK : ⁅J, K⁆ = ⊥) {w : N} (hw : w ∈ J) :
    w ∈ Subgroup.normalizer (S : Set N) := by
  have h1 : w ∈ Subgroup.centralizer (K : Set N) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hJK hw
  have h2 : w ∈ Subgroup.centralizer (S : Set N) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hSK) h1
  exact Subgroup.centralizer_le_normalizer (S : Set N) h2

theorem r3_three_components {N : Type} [Group N] [Finite N] {p : ℕ} (hp : p.Prime)
    (hno : ∀ A T : Subgroup N, CFSG.Open.IsElemAbelian p A → Nat.card A = p ^ 3 → T ≠ ⊥ →
      IsPGroup 2 T → ¬ A ≤ Subgroup.normalizer (T : Set N))
    {F : Subgroup N} (hF : CFSG.Open.IsElemAbelian p F) (hF3 : Nat.card F = p ^ 3)
    {Y : Subgroup N} (hY : Nat.card Y = p) (hYc : Y ≤ Subgroup.center N)
    (hmult : ∀ J : Subgroup N, CFSG.IsComponent J → ¬ p ∣ Nat.card (Subgroup.center J))
    {J₀ J₁ J₂ : Subgroup N} (h₀ : CFSG.IsComponent J₀) (h₁ : CFSG.IsComponent J₁)
    (h₂ : CFSG.IsComponent J₂) (h01 : J₀ ≠ J₁) (h02 : J₀ ≠ J₂) (h12 : J₁ ≠ J₂) : False := by
  obtain ⟨w₀, hw₀, ho₀⟩ := r3h_exists_order_mem hp (r3_p_dvd_component hp hno hF hF3 h₀)
  obtain ⟨w₁, hw₁, ho₁⟩ := r3h_exists_order_mem hp (r3_p_dvd_component hp hno hF hF3 h₁)
  obtain ⟨Fh, hFh, hFh3, hFeq⟩ :=
    r3_elem3 hp hY hYc h₀ h₁ h01 (hmult J₀ h₀) (hmult J₁ h₁) hw₀ hw₁ ho₀ ho₁
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S₂, hS₂⟩ := CFSG.ABGLocalTools.exists_isSylowOf 2 J₂
  have hS₂ne : S₂ ≠ ⊥ := r3_sylow_two_ne_bot h₂ hS₂
  have hS₂2 : IsPGroup 2 S₂ := hS₂.isPGroup
  have hc₀ : ⁅J₀, J₂⁆ = ⊥ := (CFSG.LocalCores.distinct_components_commute h₀ h₂).resolve_left h02
  have hc₁ : ⁅J₁, J₂⁆ = ⊥ := (CFSG.LocalCores.distinct_components_commute h₁ h₂).resolve_left h12
  have hYN : Y ≤ Subgroup.normalizer (S₂ : Set N) :=
    (hYc.trans (Subgroup.center_le_centralizer (S₂ : Set N))).trans
      (Subgroup.centralizer_le_normalizer (S₂ : Set N))
  have hnorm : Fh ≤ Subgroup.normalizer (S₂ : Set N) := by
    rw [hFeq]
    exact sup_le (sup_le hYN (Subgroup.zpowers_le.mpr (r3h_mem_normalizer_of_commute hS₂.le hc₀ hw₀)))
      (Subgroup.zpowers_le.mpr (r3h_mem_normalizer_of_commute hS₂.le hc₁ hw₁))
  exact hno Fh S₂ hFh hFh3 hS₂ne hS₂2 hnorm

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open scoped commutatorElement

end CFSG.RankThree.PartTwo.Sec13.F135Last
