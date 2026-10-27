module

public import CFSG.RankThree.PartTwo.Sec14.Notation
import CFSG.RankThree.PartTwo.Sec14.Item14Hyperplanes
import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BGenHypAux
import CFSG.RankThree.PartOne.HNB.Tools
import CFSG.RankThree.GroupTheory.SteinbergBYMinimalCoprimeAction
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeFactorization
import CFSG.Quasithin.Vol2.Ch1Sec3Basic

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R3

open CFSG CFSG.RankThree.PartTwo

variable {G : Type} [Group G] [Finite G]

theorem inf_centralizer_le_frattini_map {U : Subgroup G} {g : G} (hU2 : IsPGroup 2 U)
    (hgU : g ∈ Subgroup.normalizer (U : Set G)) (hodd : Odd (orderOf g))
    (hUU : ⁅U, Subgroup.zpowers g⁆ = U) :
    U ⊓ Subgroup.centralizer ({g} : Set G) ≤ (frattini U).map U.subtype := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z := Subgroup.zpowers g with hZ
  have hZU : Z ≤ Subgroup.normalizer (U : Set G) := Subgroup.zpowers_le.mpr hgU
  haveI : Subgroup.Normalizes Z U := ⟨hZU⟩
  have htop : commutatorAction (A := ↥Z) (G := ↥U) = ⊤ := by
    apply Subgroup.map_injective U.subtype_injective
    rw [commutatorAction_subgroup_conj_map_eq_commutator U Z hZU, hUU, Subgroup.map_top,
      Subgroup.range_subtype]
  have hcop : Nat.Coprime (Nat.card Z) (Nat.card U) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hU2
    rw [hk, hZ, Nat.card_zpowers]
    exact Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hodd)
  letI : MulDistribMulAction ↥Z (↥U ⧸ frattini ↥U) :=
    RankThree.GroupTheory.SteinbergBY.frattiniQuotientAction ↥Z ↥U
  have hbot : fixedPointSubgroup ↥Z (↥U ⧸ frattini ↥U) = ⊥ :=
    RankThree.GroupTheory.SteinbergBY.fixedPointSubgroup_quotient_eq_bot hcop htop (frattini U)
      (RankThree.GroupTheory.SteinbergBY.isInvariant_of_characteristic _)
      (GroupTheory.frattini_elementary_quotient hU2).2.1
  rintro x ⟨hxU, hxg⟩
  have hfix : ((⟨x, hxU⟩ : ↥U) : ↥U ⧸ frattini ↥U) ∈
      fixedPointSubgroup ↥Z (↥U ⧸ frattini ↥U) := by
    rw [FixedPoints.mem_subgroup]
    intro z
    have hz : z • (⟨x, hxU⟩ : ↥U) = ⟨x, hxU⟩ := by
      apply Subtype.ext
      rw [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, mul_inv_eq_iff_eq_mul]
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp z.2
      have hxz : Commute x (g ^ n) :=
        Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.mp hxg) n
      rw [hn] at hxz
      exact hxz.eq.symm
    change ((z • (⟨x, hxU⟩ : ↥U) : ↥U) : ↥U ⧸ frattini ↥U) =
      ((⟨x, hxU⟩ : ↥U) : ↥U ⧸ frattini ↥U)
    rw [hz]
  rw [hbot, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hfix
  exact ⟨⟨x, hxU⟩, hfix, rfl⟩

theorem commutator_le_centralizer_of_hyperplanes {A B₀ V : Subgroup G} {c g : G}
    (hA : CFSG.Assembly.IsElemAbelian 3 A) (hAcard : Nat.card A = 27)
    (hB₀ : Sec14.IsHyperplane A B₀) (hc : c ∈ A) (hcB₀ : c ∉ B₀)
    (hV : IsPGroup 2 V) (hAV : A ≤ Subgroup.normalizer (V : Set G))
    (hgV : g ∈ Subgroup.normalizer (V : Set G)) (hgA : g ∈ Subgroup.centralizer (A : Set G))
    (hodd : Odd (orderOf g))
    (hCV : ∀ B : Subgroup G, Sec14.IsHyperplane A B → B ≠ B₀ →
      V ⊓ Subgroup.centralizer (B : Set G) ≤ Subgroup.centralizer ({g} : Set G)) :
    ⁅V, Subgroup.zpowers g⁆ ≤ Subgroup.centralizer (B₀ : Set G) ∧
      ⁅⁅V, Subgroup.zpowers g⁆, Subgroup.zpowers g⁆ = ⁅V, Subgroup.zpowers g⁆ ∧
      ⁅⁅V, Subgroup.zpowers g⁆, Subgroup.zpowers c⁆ = ⁅V, Subgroup.zpowers g⁆ := by
  classical
  set Z := Subgroup.zpowers g with hZ
  set U := ⁅V, Z⁆ with hU
  have hZV : Z ≤ Subgroup.normalizer (V : Set G) := Subgroup.zpowers_le.mpr hgV
  have hUV : U ≤ V := Subgroup.le_normalizer_iff_commutator_le_left.mp hZV
  have hU2 : IsPGroup 2 U := hV.to_le hUV
  have hcopV : Nat.Coprime (Nat.card Z) (Nat.card V) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hV
    rw [hk, hZ, Nat.card_zpowers]
    exact Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hodd)
  have hsolvV : Group.IsSolvable V := by
    have := hV.isNilpotent
    infer_instance
  have hUU : ⁅U, Z⁆ = U :=
    RankThree.PartOne.HNB.commutator_double_eq_self_of_coprime_solvable Z V hZV hcopV hsolvV
  have hZU : Z ≤ Subgroup.normalizer (U : Set G) := Subgroup.normalizer_commutator_ge_right V Z
  have hAZ : A ≤ Subgroup.normalizer (Z : Set G) := fun a ha =>
    RankThree.PartOne.HNB.mem_normalizer_zpowers_of_commute
      (Subgroup.mem_centralizer_iff.mp hgA a ha)
  have hAU : A ≤ Subgroup.normalizer (U : Set G) := by
    intro a ha
    have h1 := hAV ha
    have h2 := hAZ ha
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at h1 h2 ⊢
    rw [hU, Subgroup.map_commutator, h1, h2]
  have hU3 : Nat.Coprime 3 (Nat.card U) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hU2
    rw [hk]
    exact Nat.Coprime.pow_right k (by decide)
  have hA1 : A ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hAcard
    omega
  have hnongen : ∀ X : Subgroup G, X ≤ U → U ≤ X ⊔ (frattini U).map U.subtype → X = U := by
    intro X hXU h
    refine CFSG.Quasithin.Ch1Sec3.eq_of_sup_frattiniIn_eq hXU (le_antisymm ?_ h)
    exact sup_le hXU (Subgroup.map_subtype_le _)
  have hF := inf_centralizer_le_frattini_map hU2 (hZU (Subgroup.mem_zpowers g)) hodd hUU
  have hHyp : ∀ E, Sec14.IsHyperplane A E → E ≠ B₀ →
      U ⊓ Subgroup.centralizer (E : Set G) ≤ (frattini U).map U.subtype :=
    fun E hE hne x hx => hF ⟨hx.1, hCV E hE hne ⟨hUV hx.1, hx.2⟩⟩
  have h1 : U ≤ Subgroup.centralizer (B₀ : Set G) := by
    have hle : U ≤ (U ⊓ Subgroup.centralizer (B₀ : Set G)) ⊔ (frattini U).map U.subtype :=
      CFSG.LocalAnalysis.GLTheoremA.H301B.le_of_hyperplane_centralizers Nat.prime_three hA hA1
        hAU hU3 fun H hHA hHc => by
          by_cases hHB : H = B₀
          · subst hHB
            exact le_sup_left
          · exact (hHyp H ⟨hHA, by omega⟩ hHB).trans le_sup_right
    have h := hnongen _ inf_le_left hle
    rw [← h]
    exact inf_le_right
  refine ⟨h1, hUU, ?_⟩
  obtain ⟨f, hf, hfh⟩ := Sec14.exists_hyperplanes_thirteen (A := A) ⟨hA, hAcard⟩
  obtain ⟨D, hD, hDne⟩ : ∃ D, Sec14.IsHyperplane A D ∧ D ≠ B₀ := by
    by_cases h0 : f 0 = B₀
    · exact ⟨f 1, hfh 1, fun h => absurd (hf (h.trans h0.symm)) (by decide)⟩
    · exact ⟨f 0, hfh 0, h0⟩
  have hcΦ : U ⊓ Subgroup.centralizer ({c} : Set G) ≤ (frattini U).map U.subtype := by
    intro x hx
    have hxA : x ∈ Subgroup.centralizer (A : Set G) :=
      CFSG.LocalAnalysis.GLTheoremA.H301B.mem_centralizer_of_hyperplane Nat.prime_three hB₀.1
        (by have := hB₀.2; omega) hc hcB₀ (h1 hx.1)
        (Subgroup.mem_centralizer_singleton_iff.mp hx.2).symm
    exact hHyp D hD hDne ⟨hx.1, Subgroup.centralizer_le hD.1 hxA⟩
  have hZc : IsPGroup 3 (Subgroup.zpowers c) :=
    IsPGroup.of_card_dvd_pow (n := 1)
      (by rw [Nat.card_zpowers, pow_one]; exact orderOf_dvd_of_pow_eq_one (hA.2 c hc))
  have hZcU : Subgroup.zpowers c ≤ Subgroup.normalizer (U : Set G) :=
    Subgroup.zpowers_le.mpr (hAU hc)
  have hfac := RankThreeEvenClassification.Helpers.coprime_commutator_centralizer_factorization 3
    Nat.prime_three (Subgroup.zpowers c) U hZc
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hU3) hZcU
  have hcz : Subgroup.centralizer (Subgroup.zpowers c : Set G) ≤
      Subgroup.centralizer ({c} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (Subgroup.mem_zpowers c))
  refine hnongen _ (Subgroup.le_normalizer_iff_commutator_le_left.mp hZcU) ?_
  exact hfac.le.trans (sup_le_sup_left (fun x hx => hcΦ ⟨hx.1, hcz hx.2⟩) _)

end CFSG.RankThree.PartTwo.Sec15.Sylow155R3
