module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosPrimed
import CFSG.LocalAnalysis.StandardType.GGTBJD4FrameAux
import CFSG.LocalAnalysis.StandardType.GGTBJD4Field
import CFSG.LocalAnalysis.StandardType.GGSecFiveJRootCoreOmega
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentBstar
import CFSG.LocalAnalysis.StandardType.GGTableBStdSub
import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitExcCore

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal

theorem ggTBJD4_frame
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg' p B Bs x L D J 𝒦)
    (hL : GGSplitLie p L) {f : ℕ} (ψ : (ggU .POmegaPlus 4 f).K →* G)
    (hadm : StatedLieAdmissible .POmegaPlus 4 2 f)
    (hker : ψ.ker ≤ Subgroup.center (ggU .POmegaPlus 4 f).K) (hrange : ψ.range = L) :
    p.Prime ∧ p ≠ 2 ∧ p ∣ 2 ^ f - 1 ∧
      ∃ ψ' : (ggU .POmegaPlus 4 f).K →* G, Function.Injective ψ' ∧
        ∃ u ∈ ggTorus (ggU .POmegaPlus 4 f).D, u ^ p = 1 ∧ u ≠ 1 ∧
          ∃ J' : Subgroup (ggU .POmegaPlus 4 f).K,
            IsComponentOf J' (Subgroup.centralizer ({u} : Set (ggU .POmegaPlus 4 f).K)) ∧
            J'.map ψ' = J ∧
            Set.ncard {h | h ∈ ggTorus (ggU .POmegaPlus 4 f).D ∧ h ^ p = 1 ∧
              h ∈ Subgroup.centralizer (J' : Set (ggU .POmegaPlus 4 f).K)} ≤ p := by
  obtain ⟨t, n, f₀, ψ₀, hloc, hstd, -⟩ := s2jn_exists_tableBFrame G p B Bs x L D J 𝒦 hcfg hL
  have hp : p.Prime := hloc.1.1
  have hadm₀ := hloc.1.2.2.1
  have h3 := hloc.1.2.2.2
  have hker₀ := hloc.2.1.1
  have hrange₀ : ψ₀.range = L := hloc.2.1.2.1
  obtain ⟨rfl, rfl, rfl⟩ := ggTBJD4_presentation_eq hloc.2.1.2.2.1 ψ₀ hadm₀ hker₀ hrange₀ ψ hadm
    hker hrange
  have := Fact.mk hp
  have hC : GGConfig p B Bs x L D J := hcfg.1.1
  have hS : LargeEvenSStar p B x L := hC.1.2.2.2.2.2.2.1
  have hLc : IsComponentOf L (Subgroup.centralizer ({x} : Set G)) := hS.2.2.2.1
  have hxne : x ≠ 1 := hS.2.2.1
  have hpre := hC.2.2.1
  have hDcard : Nat.card D = p ^ 2 := hpre.2.2.1
  have hDx : x ∈ D := hpre.2.2.2.1
  have hZ := jcoreOm_center 4 f₀ hadm₀ h3
  have hinj : Function.Injective ψ₀ :=
    (MonoidHom.ker_eq_bot_iff ψ₀).mp (le_bot_iff.mp (hker₀.trans hZ.le))
  obtain ⟨y, hyD, -, hDxy, hcent⟩ := ggTBJD4_exists_y hp hDx hxne hpre.2.1 hDcard hLc.1
  have hyBs : y ∈ Bs := hC.2.1.1 (hpre.1 hyD)
  obtain ⟨u, hu, hyu⟩ := jcore_inner_torus (ggU .POmegaPlus 4 f₀).D hinj hstd hyBs
    (jcoreOm_hypVI G p Bs L 4 f₀ ψ₀ hloc y hyBs)
  have hmem : (y, u) ∈ LayerFacts.ggConjPairs ψ₀ :=
    LayerFacts.mem_ggConjPairs.mpr fun z => (hyu z).symm
  have hup : u ^ p = 1 := by
    have hc := pow_mem hmem p
    rw [Prod.pow_mk, hloc.2.2.1.1.2 y hyBs] at hc
    have hc' := LayerFacts.mem_center_of_mem_ggConjPairs_one hinj hc
    rw [hZ] at hc'
    exact Subgroup.mem_bot.mp hc'
  have hu1 : u ≠ 1 := by
    rintro rfl
    refine ggTBJD4_not_isCyclic hp hpre.2.1 hDcard
      (hS.2.2.2.2 D ?_ (IsPGroup.of_card hDcard))
    rw [← hDxy, Subgroup.closure_le]
    rintro g (rfl | rfl)
    · exact Subgroup.mem_centralizer_iff.mpr fun l hl =>
        Subgroup.mem_centralizer_singleton_iff.mp (hLc.1 hl)
    · refine Subgroup.mem_centralizer_iff.mpr fun l hl => ?_
      rw [← hrange₀] at hl
      obtain ⟨z, rfl⟩ := hl
      have e := hyu z
      rw [one_mul, inv_one, mul_one] at e
      nth_rewrite 1 [← e]
      group
  have hJy : IsComponentOf J (L ⊓ Subgroup.centralizer ({y} : Set G)) :=
    hcent ▸ hpre.2.2.2.2.2.1
  subst hrange₀
  rw [ExcNonsplit.range_inf_centralizer_eq_map_centralizer hinj hmem] at hJy
  obtain ⟨hJ', hmap⟩ := isComponentOf_comap_of_injective ψ₀ hinj hJy
  refine ⟨hp, hloc.1.2.1, hloc.2.1.2.2.2, ψ₀, hinj, u, hu, hup, hu1, J.comap ψ₀, hJ', hmap, ?_⟩
  have hBJ : Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D := by
    rw [hpre.2.2.2.2.2.2, ggKGCent_bstar_eq hC hloc hstd]
  refine (ggTBJD4_count hinj hstd hloc.2.2.1.2.2 hBJ hmap).trans ?_
  have hxL : x ∉ ψ₀.range := by
    rintro ⟨z, rfl⟩
    apply hxne
    have hz : z ∈ Subgroup.center (ggU .POmegaPlus 4 f₀).K :=
      Subgroup.mem_center_iff.mpr fun w => hinj (by
        rw [map_mul, map_mul]
        exact Subgroup.mem_centralizer_singleton_iff.mp (hLc.1 ⟨w, rfl⟩))
    rw [hZ, Subgroup.mem_bot] at hz
    rw [hz, map_one]
  exact ggTBJD4_card_inf_le hp hDcard hDx hxL

end CFSG.StandardType

end
