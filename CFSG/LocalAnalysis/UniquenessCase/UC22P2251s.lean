module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S22a
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Bar13
import CFSG.LocalAnalysis.UniquenessCase.UC22P20d
import CFSG.LocalAnalysis.UniquenessCase.UC22Bridge4
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Case1
import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
import CFSG.LocalAnalysis.UniquenessCase.UC22Bridge
import CFSG.Quasithin.H13.QRCThreeFreeRankOneStep
import CFSG.Quasithin.SteinbergBKHigherElementaryThompson
import CFSG.RankThree.PartTwo.Sec4.T444.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

namespace P2251s

theorem bar2_opp_equiv {X : Subgroup G} {p : ℕ} (hpP : p.Prime) {k n : ℕ}
    (e : ↥(Opp p (⊤ : Subgroup (Bar2 X))) ≃* CFSG.Open.StatedSL k (GaloisField 2 n)) :
    Nonempty (Bar2 (Opp p X) ≃* CFSG.Open.StatedSL k (GaloisField 2 n)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hYX : Opp p X ≤ X := PartTwo.s13_Bar13_opp_le p X
  have hXY : X ≤ normalizer (Opp p X : Set G) := by
    have hc := PartTwo.s13_Bar13_opp_conjInv p (M := X) (X := X)
      fun a ha b hb => X.mul_mem (X.mul_mem ha hb) (X.inv_mem ha)
    intro g hg
    refine Subgroup.mem_normalizer_iff.2 fun y => ⟨fun hy => hc g hg y hy, fun hy => ?_⟩
    have h := hc g⁻¹ (X.inv_mem hg) _ hy
    rwa [show g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y by group] at h
  obtain ⟨e₁, -⟩ := uc22p20d_bar2Equiv hYX
    (.step hYX ((Subgroup.normal_subgroupOf_iff_le_normalizer hYX).2 hXY) (.refl X))
  have hbar : ((Opp p X).subgroupOf X).map (QuotientGroup.mk' (CFSG.pCore 2 ↥X)) =
      Opp p (⊤ : Subgroup (Bar2 X)) := by
    have h := PartTwo.s13_barImage_opp hpP (le_refl X)
    rw [PartTwo.s13_barImage_self] at h
    exact h
  exact ⟨(e₁.trans (MulEquiv.subgroupCongr hbar)).trans e⟩

theorem isQuasisimple_of_equiv_statedSL {Q : Type*} [Group Q] {k n : ℕ} (hk : 2 ≤ k)
    (hn : 1 < n) (e : Q ≃* CFSG.Open.StatedSL k (GaloisField 2 n)) : CFSG.IsQuasisimple Q := by
  have hK : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  have h4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  exact CFSG.IsQuasisimple.of_mulEquiv
    (e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL _ _).symm)
    (CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinear_quasisimple _ _ hk
      (Or.inr (by rw [hK]; omega)) (Or.inr (by rw [hK]; omega)))

theorem isComponentOf_mbarImage {M V Y : Subgroup G} (hV : M ≤ normalizer (V : Set G))
    (hYM : Y ≤ M) (hO : CFSG.pCore 2 (MBar M V) = ⊥) (hq : CFSG.IsQuasisimple (Bar2 Y))
    (hsn : CFSG.Open.IsSubnormal (mbarImage M V Y) ⊤) (hne : ¬ Y ≤ centralizer (V : Set G)) :
    IsComponentOf (mbarImage M V Y) ⊤ ∧ ∃ f : Bar2 Y →* ↥(mbarImage M V Y),
      Function.Surjective f ∧ f.ker ≤ center (Bar2 Y) := by
  set φ := uc22br4_phi M V Y hYM with hφ
  have hrange := uc22br4_range_phi M V Y hYM
  have hsnr : φ.range.IsSubnormal := by
    rw [hrange]
    exact CFSG.Open.IsSubnormal.top_iff.1 hsn
  have hφle : CFSG.pCore 2 ↥Y ≤ φ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    have h1 := uc22br4_map_pCore_le_pCore_of_isSubnormal 2 hsnr
    rw [hO] at h1
    have hnorm : ((CFSG.pCore 2 ↥Y).map φ.rangeRestrict).Normal :=
      Subgroup.Normal.map CFSG.pCore_normal _ φ.rangeRestrict_surjective
    have hp : IsPGroup 2 ↥((CFSG.pCore 2 ↥Y).map φ.rangeRestrict) :=
      CFSG.pCore_isPGroup.map φ.rangeRestrict
    have hle2 : (CFSG.pCore 2 ↥Y).map φ.rangeRestrict ≤ CFSG.pCore 2 ↥φ.range :=
      le_sSup ⟨hnorm, hp⟩
    have h3 : φ x ∈ (CFSG.pCore 2 ↥φ.range).map φ.range.subtype :=
      ⟨φ.rangeRestrict x, hle2 (Subgroup.mem_map_of_mem _ hx), rfl⟩
    simpa using h1 h3
  have hne' : φ.range ≠ ⊥ := by
    rw [hrange]
    exact fun h => hne ((uc22br4_mbarImage_eq_bot_iff M V Y hV hYM).1 h)
  have : Nontrivial ↥φ.range := (Subgroup.nontrivial_iff_ne_bot _).2 hne'
  let ψ : Bar2 Y →* ↥φ.range :=
    QuotientGroup.lift (CFSG.pCore 2 ↥Y) φ.rangeRestrict (by rwa [MonoidHom.ker_rangeRestrict])
  have hψ : Function.Surjective ψ := by
    intro y
    obtain ⟨k, hk⟩ := φ.rangeRestrict_surjective y
    exact ⟨QuotientGroup.mk k, by simpa [ψ] using hk⟩
  obtain ⟨a, ha⟩ := exists_ne (1 : ↥φ.range)
  obtain ⟨k, rfl⟩ := hψ a
  have hψ1 : ∃ k, ψ k ≠ 1 := ⟨k, ha⟩
  have hqb := CFSG.LieType.CurtisTits.isQuasisimple_of_surjective hq hψ hψ1
  rw [← hrange] at hsn ⊢
  exact ⟨⟨le_top, hsn, hqb.1.commutator_eq_top, hqb.2.1⟩, ψ, hψ,
    CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hq hψ1⟩

end P2251s

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
