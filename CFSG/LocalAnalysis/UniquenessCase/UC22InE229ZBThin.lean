module

public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229ZB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs13
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionDefs
import CFSG.LocalAnalysis.RankFourTheoremC.PPointAutRank
import CFSG.LocalAnalysis.RankFourTheoremC.Nongeneration.Planes
import CFSG.LocalAnalysis.UniquenessCase.UC22S206c

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22ine229_card_le_of_isSimple (hOut : RankThreeTheoremC.KFactOutCyclic) {K : Type}
    [Group K] [Finite K] (hs : IsSimpleGroup K) (hnab : ∃ a b : K, a * b ≠ b * a)
    (hcat : IsCatalogGroup K) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hrank : CFSG.Open.pRank p (⊤ : Subgroup K) ≤ 1) {R : Subgroup (MulAut K)}
    (hR : IsElemAbelian p R) : Nat.card R ≤ p ^ 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨T⟩ : Nonempty (Sylow p K) := inferInstance
  have hout := hOut K hs hnab hcat p hp hp2 T
    (RankFourTheoremC.Nongeneration.isCyclic_sylow_of_pRank_le_one hp2 hrank T)
  have hZ : center K = ⊥ := by
    rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal K _ hs (center K) inferInstance with h | h
    · exact h
    · obtain ⟨a, b, hab⟩ := hnab
      exact absurd (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top b) a) hab
  have hmul := RankFourTheoremC.pRank_mulAut_le_add_pRank_outer hp hZ
  obtain ⟨k, hk⟩ := hR.isPGroup.exists_card_eq
  rw [hk]
  exact Nat.pow_le_pow_right hp.pos
    ((CFSG.SectionRank.le_pRank hp.one_lt le_top hR hk).trans (by omega))

private theorem nonabelian_bar2 {M L : Subgroup G} (hL : L ∈ calC M) :
    ∃ x y : Bar2 L, x * y ≠ y * x := by
  by_contra h
  push_neg at h
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

theorem uc22ine229_exists_B₁_of_thin (hThin : PartTwo.ThinList13)
    (hOut : RankThreeTheoremC.KFactOutCyclic) {M : Subgroup G} (hK : CFSG.Open.IsKGroup ↥M)
    {Y : Subgroup G} (hY : Y ∈ calC M) (hthin : F08.Thin8 Y) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (h4 : 4 ≤ CFSG.Open.pRank p M) {X : Subgroup G} (hXY : X ≤ Y) {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (hXc : Nat.card X = q) (hrank : CFSG.Open.pRank q M ≤ 3) :
    ∃ B₁ : Subgroup G, B₁ ≤ M ∧ IsElemAbelian p B₁ ∧ Nat.card B₁ = p ^ 2 ∧
      B₁ ≤ centralizer (X : Set G) ∧ ∀ b ∈ B₁, ∀ y ∈ Y, b * y * b⁻¹ * y⁻¹ ∈ pCoreOf 2 M := by
  have hp2 : p ≠ 2 := by omega
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
  have hZ : ¬ q ∣ Nat.card (center (Bar2 Y)) := by
    have : center (Bar2 Y) = ⊥ := by
      rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hs (center (Bar2 Y)) inferInstance
        with h | h
      · exact h
      · obtain ⟨a, b, hab⟩ := hnab
        exact absurd (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top b) a) hab
    rw [this, Subgroup.card_bot]
    exact hq.not_dvd_one
  obtain ⟨B, hBM, hBel, hBc⟩ := UC6S846.exists_elemAbelian_card_of_le_pRank hp h4
  have hBN := uc22ine229_le_normalizer hY hp hp5 hq hq2 hXY hXc hZ hrank hBM hBel
  obtain ⟨B₀, hB₀B, hB₀el, hB₀c, hB₀Y⟩ := uc22ine229_exists_kernel hY.1 hp hBN hBel hBc
    (uc22ine229_card_le_of_isSimple hOut hs hnab hcat hp hp2 (hrk p hp hp2)
      ((hBel.subgroupOf _).map _))
  exact uc22ine229_exists_copy hYM hp hp2 hq hq2 (hB₀B.trans hBM) hB₀el hB₀c hB₀Y hXY
    (IsPGroup.of_card (n := 1) (by rw [hXc, pow_one]))

end CFSG.LocalAnalysis.UniquenessCase.UC22
