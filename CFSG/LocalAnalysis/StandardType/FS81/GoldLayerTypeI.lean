module

public import CFSG.LocalAnalysis.StandardType.FS81.GoldLayerSetup
import CFSG.Goldschmidt.Steps.G310TypeI
import CFSG.Goldschmidt.Steps.G310TypeID
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Borel
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Lemma83
import CFSG.Walter.Bender1970.S2.Subnormal
import CFSG.Walter.Bender1970.S2.TwoSubgroup
import CFSG.Walter.PSL2Facts

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Goldschmidt
open CFSG.ComponentClassification.AschbacherToolkit.Bender (sylowCenter)

variable {Y : Type} [Group Y] [Finite Y] {S : Sylow 2 Y} {B L : Subgroup Y}

theorem goldLayer_inf_eq_of_typeI
    (D : GoldLayerFacts Y S B) (hL : IsComponentOf L ⊤) (hF : G310.CompFacts B L)
    (hI : IsGoldTypeI L) {P : Sylow 2 Y} (hBP : B ≤ P) :
    (P : Subgroup Y) ⊓ L = (S : Subgroup Y) ⊓ L := by
  have hLn : L.Normal := goldLayer_comp_normal D hL
  have hL' : IsComponentOf L (normalClosureIn ⊤ B) := by
    rw [goldLayer_normalClosureIn_top D.hyp.gen]
    exact hL
  obtain ⟨P₀, Dbar, -, hcl, hBorel, hmap⟩ :=
    G310.typeI_data D.hyp.oddCore D.sstar hL' hI
  obtain ⟨Q₁, hQ₁sub⟩ := G3a.exists_sylow_of_fusionIsSylowIn
    (goldLayer_sylow_inf P hLn)
  have hBQ₁ : (B ⊓ L).subgroupOf L ≤ Q₁ := by
    rw [hQ₁sub]
    intro x hx
    exact ⟨hBP hx.1, hx.2⟩
  have hQ₁P₀ : Q₁ = P₀ := G310.eq_of_le_sylow hL.2.2 hcl hBorel hmap Q₁ hBQ₁
  obtain ⟨Q₂, hQ₂sub⟩ := G3a.exists_sylow_of_fusionIsSylowIn
    (goldLayer_sylow_inf S hLn)
  have hBQ₂ : (B ⊓ L).subgroupOf L ≤ Q₂ := by
    rw [hQ₂sub]
    intro x hx
    exact ⟨D.hyp.le hx.1, hx.2⟩
  have hQ₂P₀ : Q₂ = P₀ := G310.eq_of_le_sylow hL.2.2 hcl hBorel hmap Q₂ hBQ₂
  calc (P : Subgroup Y) ⊓ L = (Q₁ : Subgroup L).map L.subtype := by
        rw [hQ₁sub, Subgroup.map_subgroupOf_eq_of_le inf_le_right]
    _ = (P₀ : Subgroup L).map L.subtype := by rw [hQ₁P₀]
    _ = (Q₂ : Subgroup L).map L.subtype := by rw [← hQ₂P₀]
    _ = (S : Subgroup Y) ⊓ L := by
        rw [hQ₂sub, Subgroup.map_subgroupOf_eq_of_le inf_le_right]

theorem goldLayer_exists_not_le_of_typeI
    (D : GoldLayerFacts Y S B) (hL : IsComponentOf L ⊤)
    (hF : G310.CompFacts B L) (hI : IsGoldTypeI L) :
    ∃ y ∈ L, y ∈ Subgroup.normalizer (((S : Subgroup Y) ⊓ L : Subgroup Y) : Set Y) ∧
      y ∉ (S : Subgroup Y) := by
  have hLn : L.Normal := goldLayer_comp_normal D hL
  have hL' : IsComponentOf L (normalClosureIn ⊤ B) := by
    rw [goldLayer_normalClosureIn_top D.hyp.gen]
    exact hL
  obtain ⟨P₀, Dbar, -, hcl, hBorel, hmap⟩ :=
    G310.typeI_data D.hyp.oddCore D.sstar hL' hI
  let π : L →* L ⧸ Subgroup.center L := QuotientGroup.mk' (Subgroup.center L)
  let Pbar : Sylow 2 (L ⧸ Subgroup.center L) :=
    P₀.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center L))
  have hPbarCoe : (Pbar : Subgroup (L ⧸ Subgroup.center L)) =
      (P₀ : Subgroup L).map π := by
    rw [show Pbar = P₀.mapSurjective (QuotientGroup.mk'_surjective
      (Subgroup.center L)) from rfl, Sylow.coe_mapSurjective]
  have hcenterP : Subgroup.center L ≤ (P₀ : Subgroup L) := by
    have hsup : IsPGroup 2 (Subgroup.center L ⊔ (P₀ : Subgroup L) : Subgroup L) :=
      IsPGroup.to_sup_of_normal_left hF.center P₀.isPGroup'
    have hmax : (Subgroup.center L ⊔ (P₀ : Subgroup L) : Subgroup L) = (P₀ : Subgroup L) :=
      P₀.is_maximal' hsup le_sup_right
    exact le_sup_left.trans (le_of_eq hmax)
  have hP₀comap : (Pbar : Subgroup (L ⧸ Subgroup.center L)).comap π =
      (P₀ : Subgroup L) := by
    rw [hPbarCoe, Subgroup.comap_map_eq_self]
    have hker : π.ker = Subgroup.center L :=
      QuotientGroup.ker_mk' (Subgroup.center L)
    rw [hker]
    exact hcenterP
  have hnormEq : (Subgroup.normalizer
      ((Pbar : Subgroup (L ⧸ Subgroup.center L)) : Set (L ⧸ Subgroup.center L))).comap π =
      Subgroup.normalizer ((P₀ : Subgroup L) : Set L) := by
    rw [Subgroup.comap_normalizer_eq_of_surjective (H :=
      (Pbar : Subgroup (L ⧸ Subgroup.center L))) (f := π)
      (QuotientGroup.mk'_surjective (Subgroup.center L)), hP₀comap]
  have hDne : Dbar ≠ ⊥ := by
    intro hbot
    have hPbot : ((P₀.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center L))) :
        Subgroup (L ⧸ Subgroup.center L)) = ⊥ := by
      have hcomm := hBorel.commutator_eq
      rw [hbot, Subgroup.commutator_bot_right] at hcomm
      exact hcomm.symm
    have hcard : Nat.card (sylowCenter (⊥ : Subgroup (L ⧸ Subgroup.center L))) = 1 := by
      simp [sylowCenter]
    have hfour := hBorel.four
    rw [hPbot, hcard] at hfour
    omega
  have hP₀sub : (P₀ : Subgroup L) = ((S : Subgroup Y) ⊓ L).subgroupOf L := by
    obtain ⟨Q₂, hQ₂sub⟩ := G3a.exists_sylow_of_fusionIsSylowIn
      (goldLayer_sylow_inf S hLn)
    have hBQ₂ : (B ⊓ L).subgroupOf L ≤ Q₂ := by
      rw [hQ₂sub]
      intro x hx
      exact ⟨D.hyp.le hx.1, hx.2⟩
    have hQ₂P₀ : Q₂ = P₀ := G310.eq_of_le_sylow hL.2.2 hcl hBorel hmap Q₂ hBQ₂
    have hQ₂P₀' : (P₀ : Subgroup L) = (Q₂ : Subgroup L) :=
      congrArg (fun Q : Sylow 2 L => (Q : Subgroup L)) hQ₂P₀.symm
    calc (P₀ : Subgroup L) = (Q₂ : Subgroup L) := hQ₂P₀'
      _ = ((S : Subgroup Y) ⊓ L).subgroupOf L := hQ₂sub
  obtain ⟨db, hdbD, hdb1⟩ : ∃ db ∈ Dbar, db ≠ 1 := by
    by_contra h
    push Not at h
    exact hDne (by
      rw [Subgroup.eq_bot_iff_forall]
      exact h)
  obtain ⟨d, hdπ⟩ := QuotientGroup.mk'_surjective (Subgroup.center L) db
  have hdπ' : π d = db := hdπ
  have hdNbar : db ∈ Subgroup.normalizer
      ((Pbar : Subgroup (L ⧸ Subgroup.center L)) : Set (L ⧸ Subgroup.center L)) :=
    hBorel.le hdbD
  have hdNP : d ∈ Subgroup.normalizer ((P₀ : Subgroup L) : Set L) := by
    rw [← hnormEq, Subgroup.mem_comap, hdπ']
    exact hdNbar
  have hdNPsub : d ∈ Subgroup.normalizer
      ((((S : Subgroup Y) ⊓ L).subgroupOf L : Subgroup L) : Set L) := by
    rw [← hP₀sub]
    exact hdNP
  refine ⟨(d : Y), d.2, ?_, ?_⟩
  · have h1 : d ∈ (Subgroup.normalizer
        (((S : Subgroup Y) ⊓ L : Subgroup Y) : Set Y)).subgroupOf L := by
      rw [Subgroup.subgroupOf_normalizer_eq (inf_le_right :
        ((S : Subgroup Y) ⊓ L) ≤ L)]
      exact hdNPsub
    exact h1
  · intro hdS
    have hdP : d ∈ (P₀ : Subgroup L) := by
      rw [hP₀sub]
      exact ⟨hdS, d.2⟩
    have hdbarP : db ∈ (Pbar : Subgroup (L ⧸ Subgroup.center L)) := by
      rw [hPbarCoe, ← hdπ']
      exact Subgroup.mem_map_of_mem π hdP
    have hbot : db ∈ (⊥ : Subgroup (L ⧸ Subgroup.center L)) := by
      rw [← hBorel.inf]
      exact ⟨hdbarP, hdbD⟩
    exact hdb1 (Subgroup.mem_bot.mp hbot)

end CFSG.StandardType.FrameRoute.FS81

end
