module

public import CFSG.RankThree.PartTwo.Sec16.Item163U35Conf
import CFSG.RankThree.PartTwo.Sec16.Item163ResProofU35Facts
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.KFacts.KS14HJBasic
import CFSG.Goldschmidt.Steps.G310Basic
import CFSG.RankThree.PartTwo.Sec13.Item136Pair

public section

namespace CFSG.RankThree.PartTwo.Sec16.Proof163U35

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y : Subgroup G}

namespace Conf684

theorem delta_centralizer_eq (h : Conf684 A c L Y) {a : G} (haA : a ∈ A)
    (haz : a ∉ Subgroup.zpowers c) :
    delta A (lB A) (Subgroup.centralizer ({a} : Set G)) =
      pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ xA A := by
  have ha1 : a ≠ 1 := by
    intro h1
    exact haz (h1 ▸ Subgroup.one_mem (Subgroup.zpowers c))
  have hΩ : Subgroup.zpowers a ∉ omegaA A := by
    rw [h.case3.2.2.2.1, Set.mem_singleton_iff]
    exact fun hz => haz (hz ▸ Subgroup.mem_zpowers a)
  set C : Subgroup G := Subgroup.centralizer ({a} : Set G) with hCdef
  obtain ⟨M, hM⟩ := maxInvariantPiSubgroups_nonempty
    (delta A (lB A) C) A (piCompl 3)
  rcases (h.item143 a haA ha1 hΩ M hM).2 with hD | hHJ
  · simpa [hCdef, xA] using hD
  · exfalso
    obtain ⟨b, d, Lb, hbΩ, hLb, ⟨φJ⟩, -, -, -, -, X', hdeltaX, -, -⟩ := hHJ
    obtain ⟨-, hLcard, -, -, -, -, -, -⟩ :=
      CFSG.RankThree.PartTwo.Sec16.Res163U35Facts.facts h.sec15R h.mem_y h.case3
    have hzw : Subgroup.zpowers b = Subgroup.zpowers c := by
      rw [h.case3.2.2.2.1] at hbΩ
      simpa using hbΩ
    have hLbTheta : Lb ∈ thetaComponentsAt 3 c := by
      have hLbc : Lb ∈ lA A c := by
        rwa [CFSG.RankThree.PartTwo.Sec13.lA_congr hzw] at hLb
      exact hLbc.1
    have hLbL : Lb = L :=
      (h.sec15R.chosen136.2 c h.sec15R.zpowers_mem_omegaA L h.sec15R.mem_lA).2 Lb hLbTheta
        (CFSG.RankThree.PartTwo.Sec16.three_dvd_card_of_mem_lA h.sec15R hbΩ hLb)
    subst Lb
    have hdvd : Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L) ∣ Nat.card L :=
      Subgroup.card_quotient_dvd_card _
    have hquot : Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L) = 604800 := by
      rw [Nat.card_congr φJ.toEquiv, CFSG.RankThree.PartTwo.KFacts.KS14.card_nativeJ2]
    rw [hquot, hLcard] at hdvd
    norm_num at hdvd

theorem delta_centralizer_mem_scriptQ (h : Conf684 A c L Y) {a : G} (haA : a ∈ A)
    (haz : a ∉ Subgroup.zpowers c) :
    delta A (lB A) (Subgroup.centralizer ({a} : Set G)) ∈ scriptQ A (lB A) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have ha1 : a ≠ 1 := by
    intro h1
    exact haz (h1 ▸ Subgroup.one_mem (Subgroup.zpowers c))
  have hΩ : Subgroup.zpowers a ∉ omegaA A := by
    rw [h.case3.2.2.2.1, Set.mem_singleton_iff]
    exact fun hz => haz (hz ▸ Subgroup.mem_zpowers a)
  set C : Subgroup G := Subgroup.centralizer ({a} : Set G) with hCdef
  set D : Subgroup G := delta A (lB A) C with hDdef
  have hΔ : D = pPrimeCoreOf 3 C ⊔ xA A := by
    simpa [hDdef, hCdef] using delta_centralizer_eq h haA haz
  have hO3 : IsPiSubgroup (piCompl 3) (pPrimeCoreOf 3 C) :=
    (isPiSubgroup_piCompl_iff Nat.prime_three _).mpr
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 C))
  have hX3 : IsPiSubgroup (piCompl 3) (xA A) :=
    (isPiSubgroup_piCompl_iff Nat.prime_three _).mpr
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
        (coprime_card_pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G))))
  have hXleC : xA A ≤ C :=
    (pPrimeCoreOf_le 3 (Subgroup.centralizer (A : Set G))).trans
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr haA))
  have hXleNO : xA A ≤ Subgroup.normalizer (pPrimeCoreOf 3 C : Set G) :=
    hXleC.trans (le_normalizer_pPrimeCoreOf 3 C)
  have hD3 : IsPiSubgroup (piCompl 3) D := by
    rw [hΔ, sup_comm]
    exact isPiSubgroup_piCompl_sup hX3 hO3 hXleNO
  have hAC : A ≤ C := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    exact (congrArg Subtype.val
      (h.sec15R.toSec13Data.isElemAbelian.1.is_comm.comm ⟨x, hx⟩ ⟨a, haA⟩)).symm
  have hAA : A ≤ Subgroup.centralizer (A : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr h.sec15R.toSec13Data.isElemAbelian.1
  have hAD : A ≤ Subgroup.normalizer (D : Set G) := by
    rw [hΔ]
    exact Sec14.le_normalizer_sup (hAC.trans (le_normalizer_pPrimeCoreOf 3 C))
      (hAA.trans (le_normalizer_pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G))))
  have hmax : D ∈ maxInvariantPiSubgroups D A (piCompl 3) := by
    refine mem_maxInvariantPiSubgroups_iff.mpr ⟨⟨le_rfl, hD3, hAD⟩, ?_⟩
    intro Q hQ hDQ
    exact le_antisymm hQ.1 hDQ
  have hmax' : delta A (lB A) (Subgroup.centralizer ({a} : Set G)) ∈
      maxInvariantPiSubgroups (delta A (lB A) (Subgroup.centralizer ({a} : Set G))) A
        (piCompl 3) := by
    simpa [hDdef, hCdef] using hmax
  exact (h.item143 a haA ha1 hΩ _ hmax').1.1

theorem delta_centralizer_inf_le (h : Conf684 A c L Y) {a : G} (haA : a ∈ A)
    (haz : a ∉ Subgroup.zpowers c) :
    delta A (lB A) (Subgroup.centralizer ({a} : Set G)) ⊓
      Subgroup.centralizer (A : Set G) ≤ xA A := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C : Subgroup G := Subgroup.centralizer ({a} : Set G) with hCdef
  set D : Subgroup G := delta A (lB A) C with hDdef
  have hDmem : D ∈ scriptQ A (lB A) := by
    simpa [hDdef, hCdef] using delta_centralizer_mem_scriptQ h haA haz
  have hD3 : ¬ 3 ∣ Nat.card D :=
    (isPiSubgroup_piCompl_iff Nat.prime_three _).mp hDmem.1.2.1
  have hΔ : D = pPrimeCoreOf 3 C ⊔ xA A := by
    simpa [hDdef, hCdef] using delta_centralizer_eq h haA haz
  have hCAc : Subgroup.centralizer (A : Set G) ≤ C :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr haA)
  have hCD : Subgroup.centralizer (A : Set G) ≤ Subgroup.normalizer (D : Set G) := by
    rw [hΔ]
    exact Sec14.le_normalizer_sup (hCAc.trans (le_normalizer_pPrimeCoreOf 3 C))
      (le_normalizer_pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)))
  have hcop : Nat.Coprime 3 (Nat.card (D ⊓ Subgroup.centralizer (A : Set G) : Subgroup G)) := by
    refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr ?_
    intro h3
    exact hD3 (h3.trans (Subgroup.card_dvd_of_le inf_le_left))
  have hle : D ⊓ Subgroup.centralizer (A : Set G) ≤
      pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) :=
    Sec14.le_pPrimeCoreOf (p := 3) (N := D ⊓ Subgroup.centralizer (A : Set G))
      (X := Subgroup.centralizer (A : Set G)) inf_le_right
      (Late.le_normalizer_inf hCD Subgroup.le_normalizer) hcop
  simpa [hDdef, hCdef, xA] using hle

theorem exists_conj_sylow (h : Conf684 A c L Y) {a : G} (haA : a ∈ A)
    (haz : a ∉ Subgroup.zpowers c) {U P₁ P₂ : Subgroup G}
    (hAU : A ≤ Subgroup.normalizer (U : Set G)) (hP₁2 : IsPGroup 2 P₁)
    (hP₂2 : IsPGroup 2 P₂) (hAP₁ : A ≤ Subgroup.normalizer (P₁ : Set G))
    (hAP₂ : A ≤ Subgroup.normalizer (P₂ : Set G))
    (hP₁ : P₁ ≤ delta A (lB A) (Subgroup.centralizer ({a} : Set G)) ⊓
      Subgroup.normalizer (U : Set G))
    (hP₂ : P₂ ≤ delta A (lB A) (Subgroup.centralizer ({a} : Set G)) ⊓
      Subgroup.normalizer (U : Set G)) :
    ∃ S : Subgroup G, P₁ ≤ S ∧ IsPGroup 2 S ∧ A ≤ Subgroup.normalizer (S : Set G) ∧
      S ≤ delta A (lB A) (Subgroup.centralizer ({a} : Set G)) ⊓
        Subgroup.normalizer (U : Set G) ∧
      ∃ x ∈ xA A ⊓ Subgroup.normalizer (U : Set G),
        P₂ ≤ S.map (MulAut.conj x).toMonoidHom := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set D : Subgroup G := delta A (lB A) (Subgroup.centralizer ({a} : Set G)) with hDdef
  set M : Subgroup G := D ⊓ Subgroup.normalizer (U : Set G) with hMdef
  have hDmem : D ∈ scriptQ A (lB A) := by
    simpa [hDdef] using delta_centralizer_mem_scriptQ h haA haz
  have hD3 : ¬ 3 ∣ Nat.card D :=
    (isPiSubgroup_piCompl_iff Nat.prime_three _).mp hDmem.1.2.1
  have hAM : A ≤ Subgroup.normalizer (M : Set G) := by
    rw [hMdef]
    exact Late.le_normalizer_inf hDmem.1.2.2 (hAU.trans Subgroup.le_normalizer)
  have hM3 : ¬ 3 ∣ Nat.card M := by
    intro h3
    exact hD3 (h3.trans (Subgroup.card_dvd_of_le (by rw [hMdef]; exact inf_le_left)))
  have hA3 : IsPGroup 3 A := fun x =>
    ⟨1, Subtype.ext (by simpa using h.sec15R.toSec13Data.isElemAbelian.2 x x.2)⟩
  obtain ⟨S₁, hS₁, hP₁S₁, hAS₁⟩ :=
    CFSG.Goldschmidt.G310.exists_invariant_sylow_containing (r := 3) (q := 2)
      Nat.prime_three Nat.prime_two hA3 hM3 hAM (by rw [hMdef]; exact hP₁) hP₁2 hAP₁
  obtain ⟨S₂, hS₂, hP₂S₂, hAS₂⟩ :=
    CFSG.Goldschmidt.G310.exists_invariant_sylow_containing (r := 3) (q := 2)
      Nat.prime_three Nat.prime_two hA3 hM3 hAM (by rw [hMdef]; exact hP₂) hP₂2 hAP₂
  obtain ⟨c₀, hc₀, hS₂conj⟩ :=
    CFSG.Goldschmidt.G310.exists_conj_of_invariant_sylows (r := 3) (q := 2)
      Nat.prime_three Nat.prime_two hA3 hM3 hAM hS₁ hS₂ hAS₁ hAS₂
  have hc₀M : c₀ ∈ D ⊓ Subgroup.normalizer (U : Set G) := hMdef ▸ hc₀.1
  have hc₀D : c₀ ∈ D := (Subgroup.mem_inf.mp hc₀M).1
  have hc₀U : c₀ ∈ Subgroup.normalizer (U : Set G) := (Subgroup.mem_inf.mp hc₀M).2
  have hc₀X : c₀ ∈ xA A :=
    delta_centralizer_inf_le h haA haz ⟨hc₀D, hc₀.2⟩
  refine ⟨S₁, hP₁S₁, hS₁.2.1, hAS₁, ?_, c₀, ⟨hc₀X, hc₀U⟩, ?_⟩
  · exact hMdef ▸ hS₁.1
  · rwa [hS₂conj] at hP₂S₂

end Conf684

end CFSG.RankThree.PartTwo.Sec16.Proof163U35
