module

public import CFSG.RankThree.PartTwo.Sec14.Wales1411WL3Odd
public import CFSG.RankThree.PartTwo.Sec14.Ronan148QDefs
import CFSG.RankThree.PartTwo.Sec14.Wales1411WRed
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec14.Item148MainProofKType
import CFSG.RankThree.PartTwo.Sec15.Wales154Stage
public import CFSG.RankThree.PartTwo.Sec14.Concl143HJ

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Late
  CFSG.GH74.GLS
open scoped commutatorElement

@[expose] noncomputable def Claim1411HJConfCoreR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L →
      ∀ Y : Subgroup G, Y = delta A (lB A) Y → Y ∈ scriptY A → ¬ Group.IsSolvable ↥Y →
        3 ∣ Nat.card Y →
        (∀ B, IsHyperplane A B → Y ≤ Subgroup.centralizer (B : Set G) → lB A B ≠ ⊥) →
        (∀ Y' ∈ scriptY A, Nat.card Y' < Nat.card Y →
          TransOn A (lB A) (Subgroup.normalizer (A : Set G)) Y') →
        ∀ S ∈ scriptQPiStar A (lB A) Y (piOf 2), ∀ T ∈ scriptQPiStar A (lB A) Y (piOf 2),
          Y ≤ Subgroup.normalizer ((S ⊓ T : Subgroup G) : Set G) →
          (∀ S' ∈ scriptQPiStar A (lB A) Y (piOf 2), ∀ T' ∈ scriptQPiStar A (lB A) Y (piOf 2),
            Nat.card (S ⊓ T : Subgroup G) < Nat.card (S' ⊓ T' : Subgroup G) →
              IsConjIn (Subgroup.normalizer (A : Set G) ⊓ Y) S' T') →
          (∀ a ∈ A, a ≠ 1 → ¬ S ⊓ Subgroup.centralizer {a} ≤ S ⊓ T →
            ¬ T ⊓ Subgroup.centralizer {a} ≤ S ⊓ T → Y ≤ Subgroup.centralizer ({a} : Set G)) →
          ∀ a ∈ A, a ≠ 1 → ¬ S ⊓ Subgroup.centralizer {a} ≤ S ⊓ T →
            ¬ T ⊓ Subgroup.centralizer {a} ≤ S ⊓ T → Subgroup.zpowers a ∉ omegaA A →
            delta A (lB A) (Subgroup.centralizer ({a} : Set G)) ≠
              pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔
                pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) →
            S ⊔ T = Y →
            (∀ e ∈ A, ⁅Y, Subgroup.zpowers e⁆ ≤ pPrimeCoreOf 3 Y → e ∈ Subgroup.zpowers a) →
            IsConjIn (Subgroup.normalizer (A : Set G) ⊓ Y) S T

namespace Wales1411W

variable {G : Type} [Group G] [Finite G]

theorem mem_scriptQ_of_le_delta {A : Subgroup G} {a : G} (h143 : Ronan148Q.Item143QAt A (lB A) a)
    {Y : Subgroup G} (hYΔ : Y ≤ delta A (lB A) (Subgroup.centralizer ({a} : Set G)))
    {Z : Subgroup G} (hZY : Z ≤ Y) (hAZ : A ≤ Subgroup.normalizer (Z : Set G))
    (hZ3 : ¬ 3 ∣ Nat.card Z) : Z ∈ scriptQ A (lB A) := by
  obtain ⟨Q, hQ, hZQ⟩ := exists_le_mem_maxInvariantPiSubgroups
    (H := delta A (lB A) (Subgroup.centralizer ({a} : Set G))) (A := A) (π := piCompl 3)
    ⟨hZY.trans hYΔ, (isPiSubgroup_piCompl_iff Nat.prime_three Z).mpr hZ3, hAZ⟩
  exact mem_scriptQ_of_le (h143 Q hQ).1.1 hZQ hAZ

theorem allPointsHJ_of_hjConf
    (h134 : Item134)
    (h48 : Sec4.Item4_8) {A L : Subgroup G} {c : G} (h : Sec14Std G A c L) {a : G}
    (h143 : Ronan148Q.Item143QAt A (lB A) a)
    (hΔ : delta A (lB A) (Subgroup.centralizer ({a} : Set G)) ≠
      pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔
        pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G))) :
    AllPointsHJ A := by
  obtain ⟨Q, hQ⟩ := maxInvariantPiSubgroups_nonempty
    (delta A (lB A) (Subgroup.centralizer ({a} : Set G))) A (piCompl 3)
  rcases (h143 Q hQ).2 with h1 | ⟨b, d, Lb, hb, hLb, hJ, -⟩
  · exact (hΔ h1).elim
  · exact Wales154.allPointsHJ_of_point h134 h48 h hb hLb hJ

theorem isConjIn_of_trivial_off
    (h142 : Item142AllS14) (hbot : Item145BotS14)
    (hJ2 : ETrans2 Sec4.Sporadic.J2.GJ Sec4.Sporadic.J2.E0)
    {A L : Subgroup G} {c : G} (hR : Sec15R G A c L) (hHJ : AllPointsHJ A)
    {Y : Subgroup G} (hY : Y ∈ scriptY A)
    (hIH : ∀ Y' ∈ scriptY A, Nat.card Y' < Nat.card Y →
      TransOn A (lB A) (Subgroup.normalizer (A : Set G)) Y')
    (hQY : ∀ Z : Subgroup G, Z ≤ Y → A ≤ Subgroup.normalizer (Z : Set G) → ¬ 3 ∣ Nat.card Z →
      Z ∈ scriptQ A (lB A))
    (hBc : ∀ B, IsHyperplane A B → Y ≤ Subgroup.centralizer (B : Set G) → lB A B ≠ ⊥)
    {a : G} (haA : a ∈ A) (ha1 : a ≠ 1) (hYa : Y ≤ Subgroup.centralizer ({a} : Set G))
    {e : G} (heA : e ∈ A) (hea : e ∉ Subgroup.zpowers a)
    (htriv : ⁅Y, Subgroup.zpowers e⁆ ≤ pPrimeCoreOf 3 Y)
    {S T : Subgroup G} (hS : S ∈ scriptQPiStar A (lB A) Y (piOf 2))
    (hT : T ∈ scriptQPiStar A (lB A) Y (piOf 2)) :
    IsConjIn (Subgroup.normalizer (A : Set G) ⊓ Y) S T := by
  have hA : Late.IsE27 A := hR.isE27
  refine isConjIn_of_trivial_mod hA (hbot G A c L hR.toSec14Std) hY.2 hQY heA htriv hS hT ?_
  intro S' T' hS' hT' hY'Y hY'e
  by_cases hY' : S' ⊔ T' = Y
  ·
    have hYe : Y ≤ Subgroup.centralizer ({e} : Set G) := by
      rw [← hY']
      exact hY'e.trans (Subgroup.centralizer_le (by simp [Subgroup.mem_zpowers]))
    set B := Subgroup.closure ({a, e} : Set G) with hBdef
    have hB : IsHyperplane A B :=
      Main148.isHyperplane_closure_pair148 hA haA heA ha1 hea
    have hYB : Y ≤ Subgroup.centralizer (B : Set G) := by
      rw [hBdef, Subgroup.centralizer_closure]
      intro y hy
      rw [Subgroup.mem_centralizer_iff]
      rintro x (rfl | rfl)
      · exact Subgroup.mem_centralizer_iff.mp (hYa hy) x (Set.mem_singleton x)
      · exact Subgroup.mem_centralizer_iff.mp (hYe hy) x (Set.mem_singleton x)
    obtain ⟨b, d, Lb, hc⟩ := exists_isLBConfig_of_lB_ne_bot (hBc B hB hYB)
    obtain ⟨hBeq, hbΩ, hLbset, -, -⟩ := hc
    have hbB : b ∈ B := by
      rw [hBeq]
      exact Subgroup.subset_closure (Set.mem_insert b _)
    have hYb : Y ≤ Subgroup.centralizer ({b} : Set G) :=
      hYB.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hbB))
    have hLb : Lb ∈ lA A b := hLbset ▸ Set.mem_singleton Lb
    obtain ⟨φ⟩ := Wales154.quot_j2_of_allPointsHJ hR.toSec14Std hHJ hbΩ hLb
    rw [hY'] at hS' hT' ⊢
    exact isConjIn_of_j2_point h142 hbot hJ2 hR hbΩ hLb φ hY hIH hYb hS' hT'
  ·
    have hlt : S' ⊔ T' < Y := lt_of_le_of_ne hY'Y hY'
    have hY'𝓨 : S' ⊔ T' ∈ scriptY A :=
      ⟨fun htop => hY.1 (top_le_iff.mp (htop ▸ hY'Y)),
        le_normalizer_sup_of_le hS'.prop.1.1.1.2.2 hT'.prop.1.1.1.2.2⟩
    exact hIH _ hY'𝓨 (Subgroup.card_lt_of_lt hlt) S' hS' T' hT'

end Wales1411W

open Wales1411W in
theorem claim1411NonsolvWPointHJConfR_of_core
    (h142 : Item142AllS14) (hbot : Item145BotS14)
    (hJ2 : ETrans2 Sec4.Sporadic.J2.GJ Sec4.Sporadic.J2.E0) (h143 : Ronan148Q.Item143QS14)
    (h134 : Item134) (h48 : Sec4.Item4_8) (hcore : Claim1411HJConfCoreR) :
    Claim1411NonsolvWPointHJConfR := by
  intro G _ _ A c L hR Y hYΔ hY hs h3 hBc hIH S hS T hT hD hbig hres a haA ha1 haS haT ha hΔ
  have hYa := hres a haA ha1 haS haT
  by_cases hYST : S ⊔ T = Y
  swap
  · exact isConjIn_of_sup_ne hY hIH hS hT hYST
  have h143a : Ronan148Q.Item143QAt A (lB A) a := h143 G A c L hR.toSec14Std a haA ha1 ha
  have hYK : Y ≤ delta A (lB A) (Subgroup.centralizer ({a} : Set G)) := by
    rw [hYΔ]
    exact delta_mono hYa
  have hQY : ∀ Z : Subgroup G, Z ≤ Y → A ≤ Subgroup.normalizer (Z : Set G) →
      ¬ 3 ∣ Nat.card Z → Z ∈ scriptQ A (lB A) :=
    fun Z hZY hAZ hZ3 => mem_scriptQ_of_le_delta h143a hYK hZY hAZ hZ3
  have hHJ : AllPointsHJ A := allPointsHJ_of_hjConf h134 h48 hR.toSec14Std h143a hΔ
  by_cases hker : ∀ e ∈ A, ⁅Y, Subgroup.zpowers e⁆ ≤ pPrimeCoreOf 3 Y → e ∈ Subgroup.zpowers a
  · exact hcore G A c L hR Y hYΔ hY hs h3 hBc hIH S hS T hT hD hbig hres a haA ha1 haS haT ha hΔ
      hYST hker
  · push Not at hker
    obtain ⟨e, heA, htriv, hea⟩ := hker
    exact isConjIn_of_trivial_off h142 hbot hJ2 hR hHJ hY hIH hQY hBc haA ha1 hYa heA hea htriv
      hS hT

end CFSG.RankThree.PartTwo.Sec14
