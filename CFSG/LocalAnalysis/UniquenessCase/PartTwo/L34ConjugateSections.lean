module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.L34MovingSection
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs16a
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenInfra
public import CFSG.Quasithin.Background.ConjugateSectionAction
public import CFSG.Quasithin.Background.FixVLattice
public import CFSG.Quasithin.Background.D2Basic
public import CFSG.Quasithin.Background.MovingSectionRank
public import CFSG.Blueprint.Catalog
public import CFSG.GroupTheory.IsComponentOfMap
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CenterHopf
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3Close16CoverR119
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21a
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214a
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214b
public import CFSG.Quasithin.Background.F918V3QB1
public import CFSG.Quasithin.Background.G10Local
public import CFSG.Quasithin.Background.HFL3Q
public import CFSG.Quasithin.Background.HTriU3
public import CFSG.Quasithin.Background.SmithB42L2L32
public import CFSG.Quasithin.Background.SmithB42SL3Key
public import CFSG.Quasithin.Background.SmithB45SL3Outer
public import CFSG.Quasithin.Background.SmithB51LnRealB
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Inputs2
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Inputs520
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5115
public import CFSG.Quasithin.Vol2.Ch5Sec1Thm5114
public import CFSG.Quasithin.Vol2.Ch5StatementsDS
public import CFSG.Quasithin.Vol2.Ch6Defs
public import CFSG.Sporadic.Schreier.J4SCommGenBase1

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.ConjugateSection CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22

theorem exists_l34_active_conjugate
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hL34 : IsLn ↥(lBar V₀ V hV L) 3 2)
    (hirr : commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L)
      ∈ irrSet (lBar V₀ V hV L))
    (hdim : E3.mQuot
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L))
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L)
        ⊓ fixV (lBar V₀ V hV L)) = 9) :
    ∃ t ∈ Mbar D.M V₀ V hV,
      t ^ 2 = 1 ∧ t ≠ 1 ∧
      rk ↥(commSub (⊤ : Subgroup (Vtil V₀ V hV)) (Subgroup.zpowers t)) ≤ 3 ∧
      ∃ φ ∈ Mbar D.M V₀ V hV,
        let H0 := (lBar V₀ V hV L).map (MulAut.conj φ).toMonoidHom
        t ∈ Subgroup.normalizer (H0 : Set (MulAut (Vtil V₀ V hV))) ∧
        (∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
          Nat.card F = 4 ∧
          ∃ π : Matrix.SpecialLinearGroup (Fin 3) F →* ↥H0,
            Function.Surjective π ∧
            π.ker = Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F) ∧
            ∃ B : GL (Fin 3) F,
              ∀ g : Matrix.SpecialLinearGroup (Fin 3) F,
                t * (π g : MulAut (Vtil V₀ V hV)) * t⁻¹ =
                  (π (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation
                    3 F B (Matrix.SpecialLinearGroup.map
                      (CFSG.Quasithin.H.SU3.bar 1 : F ≃+* F).toRingHom g)) :
                    MulAut (Vtil V₀ V hV))) ∧
        ∀ σ ∈ Mbar D.M V₀ V hV,
          let Hj := (lBar V₀ V hV L).map (MulAut.conj σ).toMonoidHom
          Hj ≠ H0 →
            t ∈ Subgroup.centralizer (Hj : Set (MulAut (Vtil V₀ V hV))) := by
  classical
  let W := Vtil V₀ V hV
  let A : Subgroup (MulAut W) := Mbar D.M V₀ V hV
  let H : Subgroup (MulAut W) := lBar V₀ V hV L
  let U : Subgroup W := commSub (⊤ : Subgroup W) H
  have hW : ∀ w : W, w ^ 2 = 1 := s15_Infra_vtil_sq_eq_one V₀ V hV
  obtain ⟨t, htA, ht2, htne, hrk, hc⟩ := c.conc
  have hcross : ∀ g ∈ A, g ∉ Subgroup.normalizer (H : Set (MulAut W)) →
      commSub (commSub (⊤ : Subgroup W) H) (H.map (MulAut.conj g).toMonoidHom) = ⊥ :=
    fun g hg hgn => (hc.2.1 g hg hgn).2
  have hnorm : ∀ a ∈ A, t ∈ Subgroup.normalizer
      (H.map (MulAut.conj a).toMonoidHom : Set (MulAut W)) := by
    intro a ha
    by_contra hnot
    have hle := mQuot_le_rk_of_not_mem_normalizer hcross ha htA ht2 hnot
    have hq : E3.mQuot (commSub (⊤ : Subgroup W) (H.map (MulAut.conj a).toMonoidHom))
        (commSub (⊤ : Subgroup W) (H.map (MulAut.conj a).toMonoidHom) ⊓
          fixV (H.map (MulAut.conj a).toMonoidHom)) = 9 := by
      rw [mQuot_commSub_top_inf_fixV_map_conj H a]
      exact hdim
    have h9 : 9 ≤ rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers t)) := by
      rw [← hq]
      exact hle
    exact absurd (h9.trans hrk) (by norm_num)
  have hstab : ∀ a ∈ A,
      t ∈ stabSub (commSub (⊤ : Subgroup W) (H.map (MulAut.conj a).toMonoidHom)) := by
    intro a ha
    have h := CFSG.Quasithin.FixVLat.mem_stabSub_commV_of_mem_normalizer
      (X := H.map (MulAut.conj a).toMonoidHom) (hnorm a ha)
    rwa [commV_eq_commSub] at h
  have hspan : (⨆ X : {X : Subgroup W // X ∈ conjSubs A U}, X.1) = ⊤ := by
    simpa only [iSup_subtype] using hc.1
  obtain ⟨X, u, hu, htu⟩ := exists_not_fixed_of_iSup_eq_top hspan htne
  obtain ⟨φ, hφA, hXeq⟩ := X.2
  have huU : u ∈ U.map φ.toMonoidHom := by
    rw [← hXeq]
    exact hu
  have hu0 : u ∈ commSub (⊤ : Subgroup W) (H.map (MulAut.conj φ).toMonoidHom) := by
    rw [s15_Infra_commSub_top_map_conj H φ]
    exact huU
  have htN0 : t ∈ Subgroup.normalizer
      (H.map (MulAut.conj φ).toMonoidHom : Set (MulAut W)) := hnorm φ hφA
  have hL0 : IsLn ↥(H.map (MulAut.conj φ).toMonoidHom) 3 2 := by
    change CFSG.Blueprint.LieModel ↥(H.map (MulAut.conj φ).toMonoidHom) .PSL 3 2 2
    exact CFSG.Blueprint.LieModel.of_mulEquiv
      (Subgroup.equivMapOfInjective H (MulAut.conj φ).toMonoidHom
        (MulAut.conj φ).injective) hL34
  have hirr0 : commSub (⊤ : Subgroup W) (H.map (MulAut.conj φ).toMonoidHom) ∈
      irrSet (H.map (MulAut.conj φ).toMonoidHom) := by
    have h := map_mem_irrSet_map_conj (H := H) (φ := φ)
      (I := commSub (⊤ : Subgroup W) H) hirr
    rw [← s15_Infra_commSub_top_map_conj H φ] at h
    exact h
  have hdim0 : E3.mQuot (commSub (⊤ : Subgroup W) (H.map (MulAut.conj φ).toMonoidHom))
      (commSub (⊤ : Subgroup W) (H.map (MulAut.conj φ).toMonoidHom) ⊓
        fixV (H.map (MulAut.conj φ).toMonoidHom)) = 9 := by
    rw [mQuot_commSub_top_inf_fixV_map_conj H φ]
    exact hdim
  obtain ⟨hq0, F, hFfield, hFfin, hFchar, hFcard, π, hπsurj, hπker, B, hB⟩ :=
    l34_section_mQuot_eq_three_and_exists_field_action hW hL0 hirr0 hdim0 htN0 ht2
      ⟨u, hu0, htu⟩ hrk
  have hcentral : ∀ σ ∈ A,
      H.map (MulAut.conj σ).toMonoidHom ≠ H.map (MulAut.conj φ).toMonoidHom →
        t ∈ Subgroup.centralizer
          (H.map (MulAut.conj σ).toMonoidHom : Set (MulAut W)) := by
    intro σ hσA hne
    let Hj : Subgroup (MulAut W) := H.map (MulAut.conj σ).toMonoidHom
    have hLj : IsLn ↥Hj 3 2 := by
      change CFSG.Blueprint.LieModel ↥Hj .PSL 3 2 2
      exact CFSG.Blueprint.LieModel.of_mulEquiv
        (Subgroup.equivMapOfInjective H (MulAut.conj σ).toMonoidHom
          (MulAut.conj σ).injective) hL34
    have hirrj : commSub (⊤ : Subgroup W) Hj ∈ irrSet Hj := by
      have h := map_mem_irrSet_map_conj (H := H) (φ := σ)
        (I := commSub (⊤ : Subgroup W) H) hirr
      rw [← s15_Infra_commSub_top_map_conj H σ] at h
      simpa [Hj] using h
    have htNj : t ∈ Subgroup.normalizer (Hj : Set (MulAut W)) := hnorm σ hσA
    have hstab0 : t ∈ stabSub
        (commSub (⊤ : Subgroup W) (H.map (MulAut.conj φ).toMonoidHom)) :=
      hstab φ hφA
    have hstbaj : t ∈ stabSub (commSub (⊤ : Subgroup W) Hj) := hstab σ hσA
    have hle := (commSub_le_fixV_of_conj_ne hcross hφA hσA hne.symm).2
    have hint : commSub (⊤ : Subgroup W) (H.map (MulAut.conj φ).toMonoidHom) ⊓
        commSub (⊤ : Subgroup W) Hj ≤
        commSub (⊤ : Subgroup W) (H.map (MulAut.conj φ).toMonoidHom) ⊓
          fixV (H.map (MulAut.conj φ).toMonoidHom) :=
      le_inf inf_le_left (le_trans inf_le_right hle)
    have hadd := mQuot_commSub_add_le_rk_commSub (W := W) t
      (U1 := commSub (⊤ : Subgroup W) (H.map (MulAut.conj φ).toMonoidHom))
      (U2 := commSub (⊤ : Subgroup W) Hj)
      (Z1 := commSub (⊤ : Subgroup W) (H.map (MulAut.conj φ).toMonoidHom) ⊓
        fixV (H.map (MulAut.conj φ).toMonoidHom))
      (Z2 := commSub (⊤ : Subgroup W) Hj ⊓ fixV Hj)
      hstab0 hstbaj hint
    rw [hq0] at hadd
    have hsum : 3 + E3.mQuot
        (commSub (commSub (⊤ : Subgroup W) Hj) (Subgroup.zpowers t) ⊔
          (commSub (⊤ : Subgroup W) Hj ⊓ fixV Hj))
        (commSub (⊤ : Subgroup W) Hj ⊓ fixV Hj) ≤ 3 :=
      le_trans hadd hrk
    have hqj : E3.mQuot
        (commSub (commSub (⊤ : Subgroup W) Hj) (Subgroup.zpowers t) ⊔
          (commSub (⊤ : Subgroup W) Hj ⊓ fixV Hj))
        (commSub (⊤ : Subgroup W) Hj ⊓ fixV Hj) = 0 := by omega
    exact mem_centralizer_of_l34_section_mQuot_eq_zero hW hLj hirrj htNj hqj
  refine ⟨t, htA, ht2, htne, hrk, φ, hφA, ?_⟩
  dsimp only
  refine ⟨htN0, ⟨F, hFfield, hFfin, hFchar, hFcard, π, hπsurj, hπker, B, hB⟩, ?_⟩
  intro σ hσA
  exact hcentral σ hσA

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
