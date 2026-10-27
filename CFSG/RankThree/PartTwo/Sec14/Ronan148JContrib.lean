module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148JTools
public import CFSG.RankThree.PartTwo.Sec14.Ronan148JUniqueD
import CFSG.RankThree.PartTwo.Sec14.Item148ProofYB
import CFSG.RankThree.PartTwo.Sec14.Concrete
import CFSG.RankThree.PartTwo.Sec13.Item13Basic
public import CFSG.RankThree.PartTwo.Sec14.Ronan148JStruct

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148J

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS Ronan148M

variable {G : Type} [Group G] [Finite G] {A Y : Subgroup G} [(ker148 A Y).Normal]

theorem eq_of_img148_eq {E E' : Subgroup G} (hA3 : ∀ a ∈ A, a ^ 3 = 1) (hE : E ≤ A)
    (hE' : E' ≤ A) (h : img148 A Y E = img148 A Y E') : E = E' := by
  have key : ∀ {E E' : Subgroup G}, E ≤ A → E' ≤ A → img148 A Y E ≤ img148 A Y E' → E ≤ E' := by
    intro E E' hE hE' h e he
    have hm : alpha148 A Y e (hE he) ∈ img148 A Y E' :=
      h (mem_img148_iff.mpr ⟨e, Subgroup.mem_sup_right (hE he), he, rfl⟩)
    obtain ⟨e', he'M, he'E, he'eq⟩ := mem_img148_iff.mp hm
    have he'A : e' ∈ A := hE' he'E
    have : e = e' := alpha148_injective hA3 (hE he) he'A (by rw [← he'eq]; rfl)
    rw [this]
    exact he'E
  exact le_antisymm (key hE hE' h.le) (key hE' hE h.ge)

theorem eq_of_img148_le_centralizer (hA : Late.IsE27 A) {Z : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y)}
    (hAZ : ¬ img148 A Y A ≤ Subgroup.centralizer (Z : Set (↥(Y ⊔ A) ⧸ ker148 A Y)))
    {E E' : Subgroup G} (hE : IsHyperplane A E) (hE' : IsHyperplane A E')
    (hEZ : img148 A Y E ≤ Subgroup.centralizer (Z : Set (↥(Y ⊔ A) ⧸ ker148 A Y)))
    (hE'Z : img148 A Y E' ≤ Subgroup.centralizer (Z : Set (↥(Y ⊔ A) ⧸ ker148 A Y))) :
    E = E' := by
  obtain ⟨hEA, -, hmax⟩ := img148_hyperplane_max (Y := Y) hA hE
  obtain ⟨hE'A, -, hmax'⟩ := img148_hyperplane_max (Y := Y) hA hE'
  rcases hmax (img148 A Y E ⊔ img148 A Y E') le_sup_left (sup_le hEA hE'A) with h | h
  · have hle : img148 A Y E' ≤ img148 A Y E := h ▸ le_sup_right
    rcases hmax' (img148 A Y E) hle hEA with h' | h'
    · exact eq_of_img148_eq hA.1.2 hE.1 hE'.1 h'
    · exact absurd (h' ▸ hEZ) hAZ
  · exact absurd (h ▸ sup_le hEZ hE'Z) hAZ

theorem alpha148_mem_centralizer_of_contrib
    (h134 : Item134) (h48 : Sec4.Item4_8) {L : Subgroup G} {c : G} (hS : Sec14Std G A c L)
    {B Lb : Subgroup G} {b d : G} (hB : IsHyperplane A B) (hc : IsLBConfig A B b d Lb)
    (hdA : d ∈ A) {Y1 : Subgroup G} (hY1 : Y1 ≤ Y)
    (h3 : 3 ∣ Nat.card (img148 A Y (deltaZero A (lB A) Y1)))
    (hfix : ∀ e ∈ img148 A Y A,
      e ∉ Subgroup.centralizer ((img148 A Y (deltaZero A (lB A) Y1) : Subgroup _) :
        Set (↥(Y ⊔ A) ⧸ ker148 A Y)) →
      ∀ x ∈ img148 A Y (deltaZero A (lB A) Y1), x * e = e * x →
        Nat.Coprime (orderOf x) 3 → x = 1) :
    alpha148 A Y d hdA ∈ Subgroup.centralizer
      ((img148 A Y (deltaZero A (lB A) Y1) : Subgroup _) : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
  set Z := img148 A Y (deltaZero A (lB A) Y1) with hZ
  have hA : Late.IsE27 A := hS.isE27
  have hAc : IsMulCommutative A := hS.toSec13Data.isElemAbelian.1
  by_contra hdZ
  have hone : ∀ E : Subgroup G, IsHyperplane A E →
      img148 A Y E ≤ Subgroup.centralizer (Z : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) →
      YBOne A (lB A) Y E := by
    intro E hE hEZ
    by_contra hnot
    obtain ⟨b', d', L', hc'⟩ := exists_isLBConfig_of_not_yBOne hAc hE hnot
    have hzz := zpowers_eq_of_isLBConfig h134 h48 hS hB hc hE hc'
    obtain ⟨-, hd'E, -, -, -⟩ := Main148.lbConfig_points hE hA.2 hc'
    have hdE : d ∈ E := (Subgroup.zpowers_le.mpr hd'E) (hzz ▸ Subgroup.mem_zpowers d)
    exact hdZ (hEZ (mem_img148_iff.mpr ⟨d, Subgroup.mem_sup_right hdA, hdE, rfl⟩))
  have hAZ : ¬ img148 A Y A ≤ Subgroup.centralizer (Z : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    fun h => hdZ (h (alpha148_mem_img148 hdA))
  have htriv : ∀ E : Subgroup G, IsHyperplane A E →
      ¬ img148 A Y E ≤ Subgroup.centralizer (Z : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) →
      ∀ R ∈ scriptQZero A (lB A), R ≤ Y1 ⊓ Subgroup.centralizer (E : Set G) →
        img148 A Y R = ⊥ := by
    intro E hE hEZ R hR hRE
    obtain ⟨e, heE, heZ⟩ := Set.not_subset.mp hEZ
    have heA : e ∈ img148 A Y A := img148_mono hE.1 heE
    obtain ⟨hRπ, -, -⟩ := mem_scriptQ_iff.mp hR.1
    have hR3 : ¬ 3 ∣ Nat.card R := (isPiSubgroup_piCompl_iff Nat.prime_three R).mp hRπ
    have hRZ : img148 A Y R ≤ Z := img148_mono (le_deltaZero hR (hRE.trans inf_le_left))
    have hRc : img148 A Y R ≤ Subgroup.centralizer (img148 A Y E : Set _) :=
      img148_le_centralizer (hRE.trans inf_le_right)
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    refine hfix e heA heZ x (hRZ hx) ?_ ?_
    · exact (Subgroup.mem_centralizer_iff.mp (hRc hx) e heE).symm
    · have h1 : orderOf x ∣ Nat.card (img148 A Y R) := Subgroup.orderOf_dvd_natCard _ hx
      exact Nat.Coprime.coprime_dvd_left h1 (coprime_card_img148 hR3).symm
  by_cases hE0 : ∃ E0 : Subgroup G, IsHyperplane A E0 ∧
      img148 A Y E0 ≤ Subgroup.centralizer (Z : Set (↥(Y ⊔ A) ⧸ ker148 A Y))
  · obtain ⟨E0, hE0, hE0Z⟩ := hE0
    have hY0 := hone E0 hE0 hE0Z
    have hle : Z ≤ img148 A Y (pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer (E0 : Set G))) := by
      refine img148_deltaZero_le_of_hyperplanes_of_le hA hY1 fun E hE R hR hRE => ?_
      by_cases hEZ : img148 A Y E ≤ Subgroup.centralizer (Z : Set (↥(Y ⊔ A) ⧸ ker148 A Y))
      · have hEE0 : E = E0 := eq_of_img148_le_centralizer hA hAZ hE hE0 hEZ hE0Z
        subst hEE0
        refine img148_mono ((le_deltaZero hR ?_).trans hY0)
        exact inf_le_inf_right _ hY1 |>.trans' hRE
      · rw [htriv E hE hEZ R hR hRE]
        exact bot_le
    have h3' := (coprime_card_img148 (A := A) (Y := Y)
      (R := pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer (E0 : Set G)))
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 _)))
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp h3'
      (h3.trans (Subgroup.card_dvd_of_le hle))
  · push Not at hE0
    have hbot : Z = ⊥ := by
      rw [eq_bot_iff]
      refine img148_deltaZero_le_of_hyperplanes_of_le hA hY1 fun E hE R hR hRE => ?_
      rw [htriv E hE (hE0 E hE) R hR hRE]
    rw [hbot, Subgroup.card_bot] at h3
    omega

end CFSG.RankThree.PartTwo.Sec14.Ronan148J
