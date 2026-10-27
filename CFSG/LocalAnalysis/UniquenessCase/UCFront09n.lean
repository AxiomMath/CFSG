module

public import CFSG.LocalAnalysis.UniquenessCase.UC6S846b
import CFSG.LocalAnalysis.UniquenessCase.UCFront09i
import CFSG.LocalAnalysis.UniquenessCase.UC1K31
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7SixtyTwoSyl
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ElevenNineFour
import CFSG.GroupTheory.PCore.NormalPCoreOf
import CFSG.GroupTheory.PElementSubgroup
import CFSG.Goldschmidt.Steps.G53Tools
import CFSG.RankThree.PartTwo.KFacts.KS166J2A5Alt5
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.UniquenessCase.UCFront09
import CFSG.LocalAnalysis.UniquenessCase.UCFront09h

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F09

open CFSG.Open Subgroup
open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type} [Group G] [Finite G]

theorem mem_pCoreOf_of_rhoL_eq_one {L : Subgroup G} (hA5 : IsAlt (Bar2 L) 5) {c : G}
    (hcL : c ∈ L) (hc : UC6S846.rhoL L ⟨c, le_normalizer hcL⟩ = 1) : c ∈ pCoreOf 2 L := by
  obtain ⟨φ⟩ := hA5
  have key : ∀ x : Bar2 L, MulAut.conj x = 1 → x = 1 := fun x hx =>
    CFSG.RankThree.PartTwo.KFacts.KS166.eq_one_of_commute_alt5 φ fun y => by
      have h := congrArg (fun f : MulAut (Bar2 L) => f y) hx
      simp only [MulAut.conj_apply, MulAut.one_apply] at h
      calc x * y = x * y * x⁻¹ * x := by group
        _ = y * x := by rw [h]
  have h1 := key _ ((UC6S846.rhoL_inner L c hcL).symm.trans hc)
  exact (CFSG.mem_openPCoreOf_iff ⟨c, hcL⟩).2 ((QuotientGroup.eq_one_iff _).1 h1)

theorem rhoL_pow_three_eq_one {L : Subgroup G} (hA5 : IsAlt (Bar2 L) 5)
    (m : ↥(normalizer (L : Set G))) {k : ℕ} (hm : (m : G) ^ 3 ^ k = 1) :
    UC6S846.rhoL L m ^ 3 = 1 := by
  obtain ⟨φ⟩ := hA5
  have hm' : m ^ 3 ^ k = 1 := Subtype.ext (by simpa using hm)
  have h1 : orderOf (UC6S846.rhoL L m) ∣ 3 ^ k :=
    orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hm', map_one])
  have h2 : orderOf (UC6S846.rhoL L m) ∣ 120 := by
    rw [← CFSG.RankThree.PartTwo.KFacts.KS166.card_mulAut_of_alt5 φ]
    exact orderOf_dvd_natCard _
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 h1
  rw [hj] at h2
  have hj1 : j ≤ 1 := by
    by_contra hj1
    have h9 : 3 ^ 2 ∣ 120 := (pow_dvd_pow 3 (by omega)).trans h2
    norm_num at h9
  have h3 : orderOf (UC6S846.rhoL L m) ∣ 3 := by
    rw [hj]
    exact (pow_dvd_pow 3 hj1).trans (by norm_num)
  exact orderOf_dvd_iff_pow_eq_one.1 h3

theorem isSylowOf_three_of_pRank_le_one {L Y D : Subgroup G}
    (hYN : Y ≤ normalizer (L : Set G)) (hA5 : IsAlt (Bar2 L) 5) (hDL : D ≤ L) (hDY : D ≤ Y)
    (hD : Nat.card D = 3) (h3 : CFSG.Open.pRank 3 (Opp 3 Y) ≤ 1) : IsSylowOf 3 D Y := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD3 : IsPGroup 3 D := IsPGroup.of_card (n := 1) (hD.trans (pow_one 3).symm)
  obtain ⟨P, hP, hDP⟩ : ∃ P : Subgroup G, IsSylowOf 3 P Y ∧ D ≤ P := by
    obtain ⟨Q, hQ⟩ := (hD3.comap_subtype (K := Y)).exists_le_sylow
    exact ⟨(Q : Subgroup Y).map Y.subtype, ⟨Q, rfl⟩, fun y hy => ⟨⟨y, hDY hy⟩, hQ hy, rfl⟩⟩
  have hPW : P ≤ Opp 3 Y :=
    CFSG.le_pElementSubgroup_of_isPGroup Nat.prime_three hP.isPGroup hP.le
  haveI hcyc : IsCyclic P := UCK.K31.isCyclic_of_pRank_le_one Nat.prime_three (by norm_num)
    hP.isPGroup ((CFSG.SectionRank.pRank_mono (by norm_num) hPW).trans h3)
  obtain ⟨⟨g, hgP⟩, hg⟩ := IsCyclic.exists_generator (α := ↥P)
  have hcard : Nat.card P = orderOf g := by
    rw [← orderOf_eq_card_of_forall_mem_zpowers hg, Subgroup.orderOf_mk]
  obtain ⟨k, hk⟩ := hP.isPGroup ⟨g, hgP⟩
  have hgN : g ∈ normalizer (L : Set G) := hYN (hP.le hgP)
  have hρ := rhoL_pow_three_eq_one hA5 ⟨g, hgN⟩ (k := k)
    (by simpa using congrArg Subtype.val hk)
  have hg3 : g ^ 3 = 1 := by
    by_contra hne
    have hDW := CFSG.Goldschmidt.G53.le_of_isCyclic_of_card_eq_prime Nat.prime_three hcyc
      hP.isPGroup hDP hD (zpowers_le.2 (P.pow_mem hgP 3)) (by rwa [Ne, zpowers_eq_bot])
    have hDO : D ≤ pCoreOf 2 L := fun d hd => by
      obtain ⟨j, hj⟩ := mem_zpowers_iff.1 (hDW hd)
      refine mem_pCoreOf_of_rhoL_eq_one hA5 (hDL hd) ?_
      have he : (⟨d, le_normalizer (hDL hd)⟩ : ↥(normalizer (L : Set G))) =
          (⟨g, hgN⟩ ^ 3) ^ j := Subtype.ext (by simpa using hj.symm)
      rw [he, map_zpow, map_pow, hρ, one_zpow]
    obtain ⟨n, hn⟩ := ((UC6S846.isPGroup_pCoreOf L).to_le hDO).exists_card_eq
    have h32 : (3 : ℕ) ∣ 2 ^ n := by rw [← hn, hD]
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h32) (by norm_num)
  have hPD : D = P := Subgroup.eq_of_le_of_card_ge hDP (by
    rw [hD, hcard]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hg3))
  rw [hPD]
  exact hP

theorem isAlt_bar2_opp_of_pRank_le_one {L X Y : Subgroup G} (hYN : Y ≤ normalizer (L : Set G))
    (hA5 : IsAlt (Bar2 L) 5) (hX : Opp 3 X = X) (hXL : X ≤ L) (hcov : L = X ⊔ pCoreOf 2 L)
    (hXY : X ≤ Y) (h3 : CFSG.Open.pRank 3 (Opp 3 Y) ≤ 1) :
    IsAlt (Bar2 (Opp 3 Y)) 5 ∧ Opp 3 Y ≤ L := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨D, hDX, hD⟩ := exists_card_eq_three hXL hcov hA5
  have hWL : Opp 3 Y ≤ L := opp_le_of_isSylowOf
    (isSylowOf_three_of_pRank_le_one hYN hA5 (hDX.trans hXL) (hDX.trans hXY) hD h3)
    fun y hy => (Subgroup.map_mono (hDX.trans hXL)).trans
      (Subgroup.mem_normalizer_iff_map_conj_eq.1 (hYN hy)).le
  have hXW : X ≤ Opp 3 Y := hX.symm.le.trans (closure_mono fun x hx => ⟨hXY hx.1, hx.2⟩)
  exact ⟨isAlt_bar2_of_isAlt_bar2 hWL (le_antisymm (hcov.le.trans (sup_le_sup_right hXW _))
    (sup_le hWL (CFSG.LieType.BorelTits.pCoreOf_le 2 L))) hA5, hWL⟩

theorem pCoreOf_ne_bot_of_le_of_commutator_ne_bot {M X Y : Subgroup G} (hYM : Y ≤ M)
    (hXY : X ≤ Y) (hZ : ⁅pCoreOf 2 M ⊓ centralizer (pCoreOf 2 M : Set G) ⊓ X, X⁆ ≠ ⊥) :
    pCoreOf 2 Y ≠ ⊥ := fun h => zO2_ne_bot hZ (eq_bot_iff.2
  ((inf_le_inf_left _ hXY).trans ((zO2_le_pCoreOf hYM).trans h.le)))

theorem not_isSylowOf_of_mem_calY2_9 (D : Data G) {L X Y S : Subgroup G} (hLM : L ≤ D.M)
    (hLN : D.M ≤ normalizer (L : Set G)) (hUM : UniqueMax D.M (L ⊔ D.T)) (hXL : X ≤ L)
    (hcov : L = X ⊔ pCoreOf 2 L) (hXY : X ≤ Y) (hY : Y ∈ calY2_9 D) (hSY : S ≤ Y) :
    ¬ IsSylowOf 2 S D.M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hS
  obtain ⟨m, hmM, hm⟩ := D.sylowM.exists_mem_conj hS
  have hLY : L ≤ Y := hcov.le.trans (sup_le hXY
    ((CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2 hLM hLN).trans
      ((PartTwo.s16c7_pCoreOf_le_of_isSylowOf hS).trans hSY)))
  have hmap : (L ⊔ D.T).map (MulAut.conj m).toMonoidHom ≤ Y := by
    refine map_le_iff_le_comap.2 (sup_le (fun l hl => mem_comap.2 (hLY ?_))
      fun t ht => mem_comap.2 (hSY ((hm _).2 ?_)))
    · simpa using (mem_normalizer_iff.1 (hLN hmM) l).1 hl
    · simpa [mul_assoc] using ht
  have hU : calMOf ((L ⊔ D.T).map (MulAut.conj m).toMonoidHom) = {D.M} :=
    PartTwo.ElevenNine.uniqueMax_map_conj D hUM hmM
  refine hY.2.1 (Set.eq_singleton_iff_unique_mem.2 ⟨⟨D.maxLocal, hY.1.1⟩, fun N hN => ?_⟩)
  have hN' : N ∈ calMOf ((L ⊔ D.T).map (MulAut.conj m).toMonoidHom) := ⟨hN.1, hmap.trans hN.2⟩
  rw [hU] at hN'
  exact hN'

end CFSG.LocalAnalysis.UniquenessCase.UC22.F09
