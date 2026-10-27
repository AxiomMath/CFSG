module

public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Dev3
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229ZBU3
import CFSG.LocalAnalysis.UniquenessCase.UC22S206c
public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229ZBThin

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem nonabelian_bar2 {M L : Subgroup G} (hL : L ∈ calC M) :
    ∃ x y : Bar2 L, x * y ≠ y * x := by
  by_contra h
  push Not at h
  have htop : Subgroup.center (Bar2 L) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [Subgroup.mem_center_iff]
    intro y
    exact h y x
  haveI : Subsingleton (Bar2 L ⧸ Subgroup.center (Bar2 L)) := by
    rw [htop]
    exact QuotientGroup.subsingleton_quotient_top
  haveI : Nontrivial (Bar2 L ⧸ Subgroup.center (Bar2 L)) := hL.2.2.2.toNontrivial
  obtain ⟨a, b, hab⟩ := (inferInstance : Nontrivial (Bar2 L ⧸ Subgroup.center (Bar2 L)))
  exact hab (Subsingleton.elim a b)

theorem uc22ine229_exists_B₁_three_of_thin (hThin : PartTwo.ThinList13)
    (hOut : RankThreeTheoremC.KFactOutCyclic) {M : Subgroup G} (hK : CFSG.Open.IsKGroup ↥M)
    {Y : Subgroup G} (hY : Y ∈ calC M) (hthin : F08.Thin8 Y)
    (h4 : 4 ≤ CFSG.Open.pRank 3 M) {X : Subgroup G} (hXY : X ≤ Y) {q : ℕ}
    (hq : q.Prime) (hq5 : 5 ≤ q) (hXc : Nat.card X = q) (hrank : CFSG.Open.pRank q M ≤ 3) :
    ∃ B₁ : Subgroup G, B₁ ≤ M ∧ IsElemAbelian 3 B₁ ∧ Nat.card B₁ = 3 ^ 2 ∧
      B₁ ≤ centralizer (X : Set G) ∧ ∀ b ∈ B₁, ∀ y ∈ Y, b * y * b⁻¹ * y⁻¹ ∈ pCoreOf 2 M := by
  have hq2 : q ≠ 2 := by omega
  have hYM : Y ≤ M := hY.1.le
  have hKY : CFSG.Open.IsKGroup (Bar2 Y) := (hK.of_le hYM).quotient (CFSG.pCore 2 ↥Y)
  have hrk : ∀ r : ℕ, r.Prime → r ≠ 2 → CFSG.Open.pRank r (⊤ : Subgroup (Bar2 Y)) ≤ 1 :=
    fun r hr hr2 => (uc22s206c_pRank_le Y hr hr2).trans (hthin r hr hr2)
  have hO2 : CFSG.pCore 2 (Bar2 Y) = ⊥ := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot
  have hs : IsSimpleGroup (Bar2 Y) :=
    (hThin (Bar2 Y) (CFSG.KCore.KGroupNonab.kGroupAllSimple CFSG.Assembly.inCatalog_isoInvariant
      CFSG.Assembly.inCatalog_containsAbelianSimple hKY) hY.2.2 hO2 (fun r hr hr2 => by
        rw [CFSG.SectionRank.pRank_eq_open_pRank_top r (Bar2 Y)]
        exact hrk r hr hr2)).1
  have hnab := nonabelian_bar2 hY
  have hcat : IsCatalogGroup (Bar2 Y) :=
    hKY.isCatalogGroup_of_surjective ⊤ hnab (Subgroup.topEquiv (G := Bar2 Y)).toMonoidHom
      (Subgroup.topEquiv (G := Bar2 Y)).surjective
  have hZ : center (Bar2 Y) = ⊥ := by
    rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hs (center (Bar2 Y)) inferInstance
      with h | h
    · exact h
    · obtain ⟨a, b, hab⟩ := hnab
      exact absurd (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top b) a) hab
  obtain ⟨B₀, hB₀M, hB₀el, hB₀c, hB₀Y⟩ := uc22ine229k_exists_B₀ hY hq hq2 hXY hXc
    (by rw [hZ, Subgroup.card_bot]; exact hq.not_dvd_one)
    (by rw [hZ, Subgroup.card_bot]; exact Nat.prime_three.not_dvd_one) hrank h4
    (fun R hR => uc22ine229_card_le_of_isSimple hOut hs hnab hcat Nat.prime_three (by norm_num)
      (hrk 3 Nat.prime_three (by norm_num)) hR)
    (fun h3 R hR => uc22ine229k_card_le_of_not_dvd_simple hOut hs hnab hcat Nat.prime_three
      (by norm_num) h3 hR)
  exact uc22ine229_exists_copy hYM Nat.prime_three (by norm_num) hq hq2 hB₀M hB₀el hB₀c hB₀Y hXY
    (IsPGroup.of_card (n := 1) (by rw [hXc, pow_one]))

theorem uc22ine229_exists_B₁_three_of_isSU3 (hG : GriessAllModelsStatement)
    (hKA : UCK.U3ThreeRank) {M Y : Subgroup G} (hY : Y ∈ calC M) {n : ℕ}
    (hX : IsSU3 (Bar2 Y) n) (hOp : F10.OpRes 3 M = M) (h4 : 4 ≤ CFSG.Open.pRank 3 M)
    {X : Subgroup G} (hXY : X ≤ Y) {q : ℕ} (hq : q.Prime) (hq5 : 5 ≤ q)
    (hXc : Nat.card X = q) (hZ : ¬ q ∣ Nat.card (center (Bar2 Y)))
    (hrank : CFSG.Open.pRank q M ≤ 3) :
    ∃ B₁ : Subgroup G, B₁ ≤ M ∧ IsElemAbelian 3 B₁ ∧ Nat.card B₁ = 3 ^ 2 ∧
      B₁ ≤ centralizer (X : Set G) ∧ ∀ b ∈ B₁, ∀ y ∈ Y, b * y * b⁻¹ * y⁻¹ ∈ pCoreOf 2 M := by
  have hq2 : q ≠ 2 := by omega
  suffices h : ∃ B₀ : Subgroup G, B₀ ≤ M ∧ IsElemAbelian 3 B₀ ∧ Nat.card B₀ = 3 ^ 2 ∧
      ∀ b ∈ B₀, ∀ y ∈ Y, b * y * b⁻¹ * y⁻¹ ∈ pCoreOf 2 M by
    obtain ⟨B₀, hB₀M, hB₀el, hB₀c, hB₀Y⟩ := h
    exact uc22ine229_exists_copy hY.1.le Nat.prime_three (by norm_num) hq hq2 hB₀M hB₀el hB₀c
      hB₀Y hXY (IsPGroup.of_card (n := 1) (by rw [hXc, pow_one]))
  by_cases hN : M ≤ normalizer (Y : Set G)
  · obtain ⟨B, hBM, hBel, hBc⟩ := UC6S846.exists_elemAbelian_card_of_le_pRank Nat.prime_three h4
    have hR := uc22ine229k_card_map_le_nine hKA hN hX hOp hBM hBel
    obtain ⟨B₀, hB₀B, hB₀el, hB₀c, hB₀Y⟩ := uc22ine229k_exists_kernel hY.1 Nat.prime_three
      (hBM.trans hN) hBel (by rw [hBc]; omega)
    exact ⟨B₀, hB₀B.trans hBM, hB₀el, hB₀c, hB₀Y⟩
  by_cases hn : Even n
  · have hn3 : ¬ 3 ∣ 2 ^ n + 1 := uc22ine229k_not_dvd_two_pow_add_one_of_even hn
    have hZ3 : ¬ 3 ∣ Nat.card (center (Bar2 Y)) := fun h =>
      hn3 ((h.trans (uc22ine229_card_center_dvd hG hX)).trans (Nat.gcd_dvd_right _ _))
    exact uc22ine229k_exists_B₀ hY hq hq2 hXY hXc hZ hZ3 hrank h4
      (fun R hR => uc22ine229k_card_le_of_even hX hn hR)
      (fun h3 R hR => uc22ine229k_card_le_of_even_not_dvd hX hn h3 hR)
  · exact uc22ine229k_exists_conj_nine hY hX
      (uc22ine229k_dvd_two_pow_add_one_of_odd (Nat.not_even_iff_odd.1 hn)) hN

end CFSG.LocalAnalysis.UniquenessCase.UC22
