module

public import CFSG.LocalAnalysis.StandardType.GGQTwoPairsLK
public import CFSG.LocalAnalysis.StandardType.GGQTwoReduction

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggQ2_normalizer_inf_le_of_dvd {G : Type} [Group G] [Finite G] (hLB : GGLBalanceInput)
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hpJ : p ∣ Nat.card J)
    (hHyp : GGCorFiveTwentyHyp p B Bs x L D J) (hAJ : ggAutomizer J Bs ≠ ⊥)
    (hK1 : GGQTwoK1 p B Bs x D J) :
    Subgroup.normalizer (Bs : Set G) ⊓ Subgroup.normalizer (D : Set G) ≤
      Subgroup.normalizer (ggG0 p B x L D J : Set G) := by
  have hDJ : LargeEvenStdSub p B x L D J := hHyp.1.2.2
  have hx_D : x ∈ D := hDJ.1.2.2.2.1
  refine le_normalizer_of_map_conj_le (S := Subgroup.normalizer (Bs : Set G) ⊓
    Subgroup.normalizer (D : Set G)) (H := ggG0 p B x L D J) ?_
  intro g hg
  have hgBs : g ∈ Subgroup.normalizer (Bs : Set G) := hg.1
  have hgD : g ∈ Subgroup.normalizer (D : Set G) := hg.2
  have hLpair : GGStdPair p Bs x L := ggStdPair_L_of_dvd hpJ hHyp hAJ
  have hLpair' : GGStdPair p Bs (g * x * g⁻¹) (L.map (MulAut.conj g).toMonoidHom) :=
    ggStdPair_conj hgBs hLpair
  have hgxD : g * x * g⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.mp hgD x).mp hx_D
  have hLle : L.map (MulAut.conj g).toMonoidHom ≤ ggG0 p B x L D J :=
    ggQ2_stdPair_le_G0_of_dvd hLB hpJ hHyp hAJ hLpair' hgxD
  have hSup : (⨆ (y : G) (K : Subgroup G)
      (_ : LargeEvenSHat p B y K ∧ LargeEvenNeighbor p x y K D J), K).map
        (MulAut.conj g).toMonoidHom ≤ ggG0 p B x L D J := by
    rw [Subgroup.map_iSup]
    refine iSup_le fun y => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun K => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hK => ?_
    have hnbr : GGNbr p B x D J y K := hK
    have hKpair : GGStdPair p Bs y K := ggStdPair_nbr_of_dvd hLB hpJ hHyp hAJ hK1 hnbr
    have hKpair' : GGStdPair p Bs (g * y * g⁻¹) (K.map (MulAut.conj g).toMonoidHom) :=
      ggStdPair_conj hgBs hKpair
    have hyD : y ∈ D := by
      rw [hnbr.2.1]
      exact Subgroup.subset_closure (Set.mem_insert_of_mem x rfl)
    have hgyD : g * y * g⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.mp hgD y).mp hyD
    exact ggQ2_stdPair_le_G0_of_dvd hLB hpJ hHyp hAJ hKpair' hgyD
  unfold ggG0
  rw [Subgroup.map_sup]
  exact sup_le hLle hSup

theorem ggQ2_normalizer_inf_le {G : Type} [Group G] [Finite G] (hLB : GGLBalanceInput)
    (hP : GGStdSubPrimeInput) {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hHyp : GGCorFiveTwentyHyp p B Bs x L D J) (hAJ : ggAutomizer J Bs ≠ ⊥)
    (hK1 : GGQTwoK1 p B Bs x D J) :
    Subgroup.normalizer (Bs : Set G) ⊓ Subgroup.normalizer (D : Set G) ≤
      Subgroup.normalizer (ggG0 p B x L D J : Set G) :=
  ggQ2_normalizer_inf_le_of_dvd hLB (hP G p B x L D J hHyp.1.1 hHyp.1.2.2) hHyp hAJ hK1

theorem ggQ2_lemmaX {G : Type} [Group G] [Finite G] (hLB : GGLBalanceInput)
    (hP : GGStdSubPrimeInput) {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting p B Bs x L D J)
    (hAJ : ggAutomizer J Bs ≠ ⊥) (hK1 : GGQTwoK1 p B Bs x D J)
    (hΓ : ∀ u : ↥Bs, (u : G) ∈ D → u ≠ 1 → GGGammaAt p B Bs x L D J u)
    (hX : GGLemmaXCond p B Bs x D J) :
    Subgroup.normalizer (Bs : Set G) ≤ Subgroup.normalizer (ggG0 p B x L D J : Set G) := by
  have hHyp : GGCorFiveTwentyHyp p B Bs x L D J := hS.1
  have hDJ : LargeEvenStdSub p B x L D J := hHyp.1.2.2
  have hx_D : x ∈ D := hDJ.1.2.2.2.1
  have hxBs : x ∈ Bs := hHyp.1.2.1.1 (hDJ.1.1 hx_D)
  have hRM : ggReflGp p Bs ≤
      ggAutomizer (Subgroup.normalizer (ggG0 p B x L D J : Set G)) Bs :=
    ggQ2r_reflGp_le_M hS hΓ
  refine le_normalizer_of_map_conj_le (S := Subgroup.normalizer (Bs : Set G))
    (H := ggG0 p B x L D J) ?_
  intro g hg
  have hφA : ggConjAut Bs hg ∈ ggAutomizer ⊤ Bs :=
    ggConjAut_mem_ggAutomizer (Subgroup.mem_top g) hg
  have key : ∀ (u : ↥Bs), ((u : G) = x ∨ ∃ (y : G) (K : Subgroup G),
        GGNbr p B x D J y K ∧ (u : G) = y) →
      ∀ (X : Subgroup G), GGStdPair p Bs (u : G) X →
        X.map (MulAut.conj g).toMonoidHom ≤ ggG0 p B x L D J := by
    intro u hlu X hpair
    obtain ⟨r, hrR, w, hwD, hw1, hline⟩ := hX (ggConjAut Bs hg) hφA u hlu
    have hrM : r ∈ ggAutomizer
        (Subgroup.normalizer (ggG0 p B x L D J : Set G)) Bs := hRM hrR
    obtain ⟨m, hmG0, hmB, hmact⟩ := mem_ggAutomizer_iff.mp hrM
    have hmem : (ggConjAut Bs hg) u ∈ Subgroup.zpowers (r w) :=
      hline ▸ Subgroup.mem_zpowers ((ggConjAut Bs hg) u)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hval : (m * (w : G) * m⁻¹) ^ k = g * (u : G) * g⁻¹ := by
      have h := congrArg (fun t : ↥Bs => (t : G)) hk
      simpa [Subgroup.coe_zpow, hmact, ggConjAut_apply] using h
    have hconj : (m⁻¹ * g) * (u : G) * (m⁻¹ * g)⁻¹ ∈ D := by
      have hpow : (m⁻¹ * g) * (u : G) * (m⁻¹ * g)⁻¹ = (w : G) ^ k := by
        calc (m⁻¹ * g) * (u : G) * (m⁻¹ * g)⁻¹
            = m⁻¹ * (g * (u : G) * g⁻¹) * m := by group
          _ = m⁻¹ * ((m * (w : G) * m⁻¹) ^ k) * m := by rw [← hval]
          _ = m⁻¹ * (m * (w : G) ^ k * m⁻¹) * m := by rw [conj_zpow]
          _ = (w : G) ^ k := by group
      rw [hpow]
      exact D.zpow_mem hwD k
    have hg'B : m⁻¹ * g ∈ Subgroup.normalizer (Bs : Set G) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ hmB) hg
    have hpair' : GGStdPair p Bs ((m⁻¹ * g) * (u : G) * (m⁻¹ * g)⁻¹)
        (X.map (MulAut.conj (m⁻¹ * g)).toMonoidHom) :=
      ggStdPair_conj hg'B hpair
    have hle' : X.map (MulAut.conj (m⁻¹ * g)).toMonoidHom ≤ ggG0 p B x L D J :=
      ggQ2_stdPair_le_G0 hLB hP hHyp hAJ hpair' hconj
    have hEq : X.map (MulAut.conj g).toMonoidHom =
        (X.map (MulAut.conj (m⁻¹ * g)).toMonoidHom).map
          (MulAut.conj m).toMonoidHom := by
      rw [map_conj_map_conj, show m * (m⁻¹ * g) = g by group]
    calc X.map (MulAut.conj g).toMonoidHom
        = (X.map (MulAut.conj (m⁻¹ * g)).toMonoidHom).map
            (MulAut.conj m).toMonoidHom := hEq
      _ ≤ (ggG0 p B x L D J).map (MulAut.conj m).toMonoidHom := Subgroup.map_mono hle'
      _ = ggG0 p B x L D J := map_conj_eq_of_mem_normalizer hmG0
  unfold ggG0
  rw [Subgroup.map_sup]
  refine sup_le ?_ ?_
  · exact key ⟨x, hxBs⟩ (Or.inl rfl) L (ggStdPair_L hP hHyp hAJ)
  · rw [Subgroup.map_iSup]
    refine iSup_le fun y => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun K => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hK => ?_
    have hnbr : GGNbr p B x D J y K := hK
    have hyBs : y ∈ Bs := hHyp.1.2.1.1 hnbr.1.2.1
    exact key ⟨y, hyBs⟩ (Or.inr ⟨y, K, hnbr, rfl⟩) K
      (ggStdPair_nbr hLB hP hHyp hAJ hK1 hnbr)

end CFSG.StandardType

end

