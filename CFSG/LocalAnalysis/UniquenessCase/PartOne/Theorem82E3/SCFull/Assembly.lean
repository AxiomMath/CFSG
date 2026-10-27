module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoPoints
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.K326Dichotomy
public import CFSG.RankThree.PartTwo.Sec4.Ronan148VSection
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoCentralizerZ
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.SylowThreeWreath
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.SCFull.SolvableResidual
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.SCFull.Factorization
import CFSG.RankThree.PartOne.S12.Equivariance
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerPClosure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.SCFull

open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82 (Ctx812E CaseTwoTransitive)

variable {G : Type} [Group G] [Finite G]

private theorem orderOf_eq_three_of_mem_Z {c : Ctx812E G} (t : CaseTwoTransitive c) {z : G}
    (hz : z ∈ t.Z) (hz1 : z ≠ 1) : orderOf z = 3 := by
  have hdiv : orderOf z ∣ 3 := by
    simpa [t.card_Z] using Subgroup.orderOf_dvd_natCard t.Z hz
  have hne : orderOf z ≠ 1 := fun h => hz1 (orderOf_eq_one_iff.mp h)
  rcases (Nat.dvd_prime Nat.prime_three).mp hdiv with h1 | h3
  · exact absurd h1 hne
  · exact h3

private theorem zpowers_eq_of_mem_Z {c : Ctx812E G} (t : CaseTwoTransitive c) {z : G}
    (hz : z ∈ t.Z) (hz1 : z ≠ 1) : t.Z = Subgroup.zpowers z := by
  have hZ_le : Subgroup.zpowers z ≤ t.Z := Subgroup.zpowers_le.mpr hz
  refine (Subgroup.eq_of_le_of_card_ge hZ_le ?_).symm
  simp [t.card_Z, Nat.card_zpowers, orderOf_eq_three_of_mem_Z t hz hz1]

private theorem centralizer_eq_of_mem_Z {c : Ctx812E G} (t : CaseTwoTransitive c) {z : G}
    (hz : z ∈ t.Z) (hz1 : z ≠ 1) :
    Subgroup.centralizer (t.Z : Set G) = Subgroup.centralizer ({z} : Set G) := by
  rw [zpowers_eq_of_mem_Z t hz hz1, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

private theorem A_le_AA {c : Ctx812E G} (t : CaseTwoTransitive c) (i : Fin 3) :
    t.d.A i ≤ t.d.AA := by
  rw [t.d.AA_def]
  fin_cases i
  · exact le_sup_left.trans le_sup_left
  · exact le_sup_right.trans le_sup_left
  · exact le_sup_right

private theorem orderOf_eq_three_of_mem_A {c : Ctx812E G} (t : CaseTwoTransitive c)
    {i : Fin 3} {a : G} (ha : a ∈ t.d.A i) (ha1 : a ≠ 1) : orderOf a = 3 := by
  have hdiv : orderOf a ∣ 3 := by
    simpa [t.d.card_A i] using Subgroup.orderOf_dvd_natCard (t.d.A i) ha
  have hne : orderOf a ≠ 1 := fun h => ha1 (orderOf_eq_one_iff.mp h)
  rcases (Nat.dvd_prime Nat.prime_three).mp hdiv with h1 | h3
  · exact absurd h1 hne
  · exact h3

private theorem le_centralizer_of_mem_Z_of_central {c : Ctx812E G} (t : CaseTwoTransitive c)
    {z : G} (hz : z ∈ t.Z) (hz1 : z ≠ 1) {x : G}
    (hxP : x ∈ t.P) (hxc : ∀ g ∈ t.P, g * x = x * g) (hx3 : x ^ 3 = 1) :
    Subgroup.centralizer ({z} : Set G) ≤ Subgroup.centralizer ({x} : Set G) := by
  have hZeq : t.Z = Subgroup.zpowers z := zpowers_eq_of_mem_Z t hz hz1
  have hxZ : x ∈ t.Z := t.mem_Z_of_forall_commute hxP hxc hx3
  rw [hZeq] at hxZ
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxZ
  intro y hy
  have hyz : z * y = y * z := (Subgroup.mem_centralizer_iff.mp hy) z (by simp)
  have hcomm : Commute z y := hyz
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  rw [Set.mem_singleton_iff] at hw
  subst w
  rw [← hk]
  exact (hcomm.zpow_left k).eq

private theorem centralizer_axis_le_of_mem_A {c : Ctx812E G} (t : CaseTwoTransitive c)
    (hAxis : ∀ i, normalizer (t.d.A i : Set G) ≤ c.S.M) (i : Fin 3) {a : G}
    (ha : a ∈ t.d.A i) (ha1 : a ≠ 1) :
    Subgroup.centralizer ({a} : Set G) ≤ c.S.M := by
  have hAieq : t.d.A i = Subgroup.zpowers a := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr ha) ?_).symm
    simp [t.d.card_A i, Nat.card_zpowers, orderOf_eq_three_of_mem_A t ha ha1]
  have hcz : Subgroup.centralizer ({a} : Set G) = Subgroup.centralizer (t.d.A i : Set G) := by
    rw [hAieq, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rw [hcz]
  exact (Subgroup.centralizer_le_normalizer (t.d.A i : Set G)).trans (hAxis i)

theorem centralizer_dichotomy_of_mem_Z
    (hK : CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326.K326P2S)
    {c : Ctx812E G} (t : CaseTwoTransitive c)
    (hPG : CFSG.ABGLocalTools.IsSylowOf 3 t.P ⊤)
    (hNA : normalizer (t.d.AA : Set G) ≤ c.S.M)
    (hAxis : ∀ i, normalizer (t.d.A i : Set G) ≤ c.S.M)
    {z : G} (hz : z ∈ t.Z) (hz1 : z ≠ 1) :
    centralizer ({z} : Set G) = (centralizer ({z} : Set G) ⊓ t.d.M) ⊔
        (CFSG.pPrimeCore 3 ↥(centralizer ({z} : Set G))).map
          (centralizer ({z} : Set G)).subtype ∨
      K326Exceptional
        (↥(centralizer ({z} : Set G)) ⧸ CFSG.pPrimeCore 3 ↥(centralizer ({z} : Set G))) := by
  let H : Subgroup G := Subgroup.centralizer ({z} : Set G)
  have hHZ : Subgroup.centralizer (t.Z : Set G) = H := by
    change Subgroup.centralizer (t.Z : Set G) = Subgroup.centralizer ({z} : Set G)
    exact centralizer_eq_of_mem_Z t hz hz1
  have hH : H ≠ ⊤ := by
    rw [← hHZ]
    exact t.centralizer_Z_ne_top
  have hPH : t.P ≤ H := by
    rw [← hHZ]
    exact t.le_centralizer_Z
  obtain ⟨n, hn, -, ⟨e⟩⟩ := t.exists_mulEquiv_zwr
  have hAP : t.d.AA ≤ t.P := t.d.AA_le_S.trans (by rw [t.hdS]; exact inf_le_left)
  have hAab : CFSG.Open.IsElemAbelian 3 t.d.AA := t.d.isElemAbelian_AA
  have hAcard : Nat.card t.d.AA = 27 := t.d.card_AA
  have hcent : ∀ x ∈ t.P, (∀ g ∈ t.P, g * x = x * g) → x ^ 3 = 1 →
      H ≤ Subgroup.centralizer ({x} : Set G) := by
    intro x hxP hxc hx3
    exact le_centralizer_of_mem_Z_of_central t hz hz1 hxP hxc hx3
  obtain ⟨i, a, haAi, haz2⟩ := t.d.exists_axis_not_mem_z2Of hAP hn e
  have haA : a ∈ t.d.AA := A_le_AA t i haAi
  have hone : (1 : G) ∈ CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326.z2Of t.P := by
    change (1 : G) ∈ (Subgroup.upperCentralSeries ↥t.P 2).map t.P.subtype
    exact Subgroup.mem_map_of_mem t.P.subtype (Subgroup.one_mem _)
  have ha1 : a ≠ 1 := fun h => haz2 (h.symm ▸ hone)
  have hCa : Subgroup.centralizer ({a} : Set G) ≤ c.S.M :=
    centralizer_axis_le_of_mem_A t hAxis i haAi ha1
  have hmain := k326_dichotomy_of_E27 hK c.standing.kProper hH hPH hPG hn e hAP hAab hAcard
    hcent haA haz2 hNA hCa
  rcases hmain with hleft | hright
  · left
    have hsup_le : (H ⊓ c.S.M) ⊔ (CFSG.pPrimeCore 3 ↥H).map H.subtype ≤ H :=
      sup_le inf_le_left (Subgroup.map_subtype_le _)
    have hrel :=
      CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_eq_map
        Nat.prime_three H
    have hleft' : H ≤ (H ⊓ c.S.M) ⊔ (CFSG.pPrimeCore 3 ↥H).map H.subtype := by
      simpa [hrel] using hleft
    have heq : H = (H ⊓ c.S.M) ⊔ (CFSG.pPrimeCore 3 ↥H).map H.subtype :=
      le_antisymm hleft' hsup_le
    rw [← t.hdM] at heq
    exact heq
  · right
    exact hright.2

theorem not_three_dvd_card_of_mem_thetaComponentsAt_of_mem_Z
    (hK : CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326.K326P2S)
    {c : Ctx812E G} (t : CaseTwoTransitive c)
    (hPG : CFSG.ABGLocalTools.IsSylowOf 3 t.P ⊤)
    (hNA : normalizer (t.d.AA : Set G) ≤ c.S.M)
    (hAxis : ∀ i, normalizer (t.d.A i : Set G) ≤ c.S.M)
    (hRank : ∀ (T : Type) [Group T] [Finite T] [IsSimpleGroup T], 3 ∣ Nat.card T →
      CFSG.RankThree.PartTwo.Sec4.Ronan148V.IsSec T t.d.M → CFSG.pRank 3 T ≤ 1)
    (hG3 : CFSG.Open.pRank 3 (⊤ : Subgroup G) ≤ 3)
    {z : G} (hz : z ∈ t.Z) (hz1 : z ≠ 1) {L : Subgroup G}
    (hL : L ∈ CFSG.RankThree.thetaComponentsAt 3 z) : ¬ 3 ∣ Nat.card L := by
  let H : Subgroup G := Subgroup.centralizer ({z} : Set G)
  have hZeq : t.Z = Subgroup.zpowers z := zpowers_eq_of_mem_Z t hz hz1
  have hz3 : orderOf z = 3 := orderOf_eq_three_of_mem_Z t hz hz1
  have hHZ : Subgroup.centralizer (t.Z : Set G) = H := by
    change Subgroup.centralizer (t.Z : Set G) = Subgroup.centralizer ({z} : Set G)
    exact centralizer_eq_of_mem_Z t hz hz1
  have hPH : t.P ≤ H := by
    rw [← hHZ]
    exact t.le_centralizer_Z
  have hP : CFSG.ABGLocalTools.IsSylowOf 3 t.P H := hPG.of_le hPH le_top
  have hPz : ∀ w ∈ t.P, (∀ g ∈ t.P, g * w = w * g) → w ^ 3 = 1 → w ∈ Subgroup.zpowers z := by
    intro w hwP hwc hw3
    have hwZ : w ∈ t.Z := t.mem_Z_of_forall_commute hwP hwc hw3
    rw [hZeq] at hwZ
    exact hwZ
  obtain ⟨J, hJ, hLJ⟩ := hL
  rw [← hLJ]
  rw [Subgroup.card_map_of_injective (f := H.subtype) (K := J) (Subgroup.subtype_injective H)]
  have hdich := centralizer_dichotomy_of_mem_Z hK t hPG hNA hAxis hz hz1
  rcases hdich with hfac | hexc
  · exact not_three_dvd_card_of_mem_thetaComponents_of_factorization
      t.d.M hRank hG3 hz3 hP hPz hfac hJ
  · exact not_three_dvd_card_of_mem_thetaComponents_of_card_648 hexc.2.1 hJ

theorem full_support_theta_component_three_prime
    (hK : CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326.K326P2S)
    {c : Ctx812E G} (t : CaseTwoTransitive c)
    (hPG : CFSG.ABGLocalTools.IsSylowOf 3 t.P ⊤)
    (hNA : normalizer (t.d.AA : Set G) ≤ c.S.M)
    (hAxis : ∀ i, normalizer (t.d.A i : Set G) ≤ c.S.M)
    (hRank : ∀ (T : Type) [Group T] [Finite T] [IsSimpleGroup T], 3 ∣ Nat.card T →
      CFSG.RankThree.PartTwo.Sec4.Ronan148V.IsSec T t.d.M → CFSG.pRank 3 T ≤ 1)
    (hG3 : CFSG.Open.pRank 3 (⊤ : Subgroup G) ≤ 3)
    {x : G} (hx : x ∈ t.d.AA) (hx1 : x ≠ 1)
    (hfull : ∀ k l : Fin 3, k ≠ l → x ∉ t.d.A k ⊔ t.d.A l)
    {L : Subgroup G} (hL : L ∈ CFSG.RankThree.thetaComponentsAt 3 x) : ¬ 3 ∣ Nat.card L := by
  have hxij : ∀ i j : Fin 3, x ∉ t.d.A i ⊔ t.d.A j := by
    intro i j hij
    by_cases h : i = j
    · subst j
      obtain ⟨k, hk⟩ : ∃ k : Fin 3, k ≠ i := by
        fin_cases i
        · exact ⟨1, by decide⟩
        · exact ⟨0, by decide⟩
        · exact ⟨0, by decide⟩
      rw [sup_idem] at hij
      exact hfull i k (Ne.symm hk) (Subgroup.mem_sup_left hij)
    · exact hfull i j h hij
  obtain ⟨l, -, hl⟩ := t.exists_conj_mem_Z hx hxij
  have hl1 : l * x * l⁻¹ ≠ 1 := by
    intro h
    have hx1' : x = 1 := by
      calc x = l⁻¹ * (l * x * l⁻¹) * l := by group
        _ = l⁻¹ * 1 * l := by rw [h]
        _ = 1 := by group
    exact hx1 hx1'
  have hconj := CFSG.RankThree.PartOne.conjBy_mem_thetaComponentsAt Nat.prime_three l x hL
  have hcard : Nat.card (CFSG.RankThree.PartOne.conjBy l L) = Nat.card L := by
    simpa [CFSG.RankThree.PartOne.conjBy] using
      Subgroup.card_map_of_injective (f := (MulAut.conj l).toMonoidHom) (K := L)
        (MulAut.conj l).injective
  rw [← hcard]
  exact not_three_dvd_card_of_mem_thetaComponentsAt_of_mem_Z hK t hPG hNA hAxis hRank hG3 hl hl1
    hconj

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.SCFull
