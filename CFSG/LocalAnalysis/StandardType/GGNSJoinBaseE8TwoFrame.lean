module

public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRefl
public import CFSG.LocalAnalysis.StandardType.GGTableBExcBasic
public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub
public import Certificates.Certificate1952
import CFSG.LocalAnalysis.StandardType.GGQ2PrimeProp1010
import CFSG.LocalAnalysis.StandardType.GGTableBLinUnitLCx
import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoTorus
import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoTBHalf
import CFSG.LocalAnalysis.StandardType.GGTBTorE8Cover
import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP10Cover
import CFSG.LocalAnalysis.StandardType.FS81.S7NormalizedTwo
import CFSG.LocalAnalysis.StandardType.GGLtBstarOfInner
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpBstar

public noncomputable section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

private theorem inner_of_e8Two_model {G : Type} [Group G] {Bs L : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) {K : Type} [Field K]
    (e : L ≃* adjointGroup .E8 K) (E : Subgroup (adjointGroup .E8 K))
    (hmodel : (ggGamma L hN).range.map (MulAut.congr e).toMonoidHom =
      E.map (MulAut.conj : adjointGroup .E8 K →* MulAut (adjointGroup .E8 K))) :
    ∀ b ∈ Bs, ∃ a : L, ∀ y ∈ L, b⁻¹ * y * b = (a : G)⁻¹ * y * a := by
  intro b hb
  have hbE : (MulAut.congr e) (ggGamma L hN ⟨b⁻¹, inv_mem hb⟩) ∈
      E.map (MulAut.conj : adjointGroup .E8 K →* MulAut (adjointGroup .E8 K)) := by
    rw [← hmodel]
    exact Subgroup.mem_map.mpr
      ⟨ggGamma L hN ⟨b⁻¹, inv_mem hb⟩, ⟨⟨b⁻¹, inv_mem hb⟩, rfl⟩, rfl⟩
  obtain ⟨z, -, hz⟩ := Subgroup.mem_map.mp hbE
  refine ⟨(e.symm z)⁻¹, fun y hy => ?_⟩
  let l : L := ⟨y, hy⟩
  have h := congrArg (fun φ : MulAut (adjointGroup .E8 K) => φ (e l)) hz
  change z * e l * z⁻¹ = e (ggGamma L hN ⟨b⁻¹, inv_mem hb⟩ (e.symm (e l))) at h
  rw [e.symm_apply_apply] at h
  have hL : ggGamma L hN ⟨b⁻¹, inv_mem hb⟩ l = e.symm z * l * (e.symm z)⁻¹ := by
    apply e.injective
    rw [map_mul, map_mul, map_inv, e.apply_symm_apply]
    exact h.symm
  have hG := congrArg Subtype.val hL
  simpa only [ggGamma_coe, Subgroup.coe_mul, Subgroup.coe_inv, inv_inv] using hG

private theorem e8Two_model_of_recipe_marking {G : Type} [Group G] [Finite G]
    {B Bs L D J : Subgroup G} {x : G} (hcfg : GGConfig 3 B Bs x L D J)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    (hperf : commutator L = ⊤)
    (θ : L ⧸ Subgroup.center L ≃* TableBExc.RecipeGroup .E8 K)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hI : ∀ (b : G) (hb : b ∈ Bs),
      ggLAut L θ ⟨b, hN hb⟩ ∈ TableBExc.RecipeID .E8 K) :
    Subgroup.center L = ⊥ ∧ ∃ e : L ≃* adjointGroup .E8 K,
      (∀ l, e l = TableBExc.recipeEquiv .E8 K (ggQuotHom θ l)) ∧
      ∃ E : Subgroup (adjointGroup .E8 K), IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 8 ∧
        (ggGamma L hN).range.map (MulAut.congr e).toMonoidHom =
          E.map (MulAut.conj : adjointGroup .E8 K →* MulAut (adjointGroup .E8 K)) := by
  obtain ⟨hr, h3⟩ := card_range_ggGamma_bstar_ge hcfg hperf θ hN
    (TableBExcTwo.ggTorusLift_E8Two (K := K))
  have hTB : GGTorusTBGroup 3 7 (TableBExc.RecipeGroup .E8 K)
      (TableBExc.RecipeID .E8 K) L (ggQuotHom θ) (ggGamma L hN).range :=
    ggTorusTBGroup_of_marking Nat.prime_three hcfg.2.1.2.1 hcfg.2.1.2.2.2
      hperf θ hN hI hr h3
  obtain ⟨e, he, E, hE, hcard, hSC, hmodel⟩ :=
    exists_e8_model_of_tbGroup (ggQuotHom θ) (ggGamma L hN).range hTB
  have h7 : 3 ^ 7 ≤ Nat.card E := by rw [hcard]; exact hr
  obtain ⟨c, hc⟩ := TableBExcTwoTB.exists_conj_frame_of_card_half_E8 hK hE h7
    (fun g hg hg3 => hSC g (fun z hz => (Subgroup.mem_centralizer_iff.mp hg z hz).symm) hg3)
  have h8 : Nat.card E = 3 ^ 8 := by
    rw [hc, Subgroup.card_map_of_injective (MulAut.conj c).injective]
    exact FrameRoute.FS81.natCard_frameTorusE8 (K := K)
  exact ⟨(FrameRoute.P10a_cover_E8 hK hperf θ).1, e, he, E, hE, h8, hmodel⟩

theorem GGConfig.exists_e8Two_model_of_marking {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs L D J : Subgroup G} {x : G} (hcfg : GGConfig p B Bs x L D J)
    (hmark : GGInnerDiagOnLabel (fun p lab => ggRowP_EE8 p lab ∧ lab.n = 1) p Bs L) :
    p = 3 ∧ Subgroup.center L = ⊥ ∧ ∃ hN : Bs ≤ Subgroup.normalizer (L : Set G),
      ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = 2 ∧
        ∃ (θ : L ⧸ Subgroup.center L ≃* TableBExc.RecipeGroup .E8 K)
          (e : L ≃* adjointGroup .E8 K) (E : Subgroup (adjointGroup .E8 K)),
          (∀ l, e l = TableBExc.recipeEquiv .E8 K (ggQuotHom θ l)) ∧
          IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 8 ∧
          (ggGamma L hN).range.map (MulAut.congr e).toMonoidHom =
            E.map (MulAut.conj : adjointGroup .E8 K →* MulAut (adjointGroup .E8 K)) := by
  classical
  have hpp : p.Prime := hcfg.tableB_facts.1
  obtain ⟨hperf, ⟨t, r, n⟩, -, hraw⟩ := hmark
  cases t
  all_goals
    obtain ⟨R, iR, I, F, hQ⟩ := CFSG.GGQ2Prime.rawDatumLegacy_exists hraw
    obtain ⟨-, -, θ, hP⟩ := hQ
    obtain ⟨⟨⟨htag, hdvd⟩, hn⟩, hN, hBsI⟩ := hP
    dsimp only at htag hdvd hn
    cases htag
    all_goals
      subst n
      have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hpp Nat.prime_three).mp
        (by simpa using hdvd)
      dsimp only [LargeEvenRawDatumLegacy, LargeEvenRecipeChevalley] at hraw
      obtain ⟨K, iK, iFin, hK, hQ⟩ := hraw
      obtain ⟨-, -, θ, hP⟩ := hQ
      obtain ⟨-, hN, hBsI⟩ := hP
      let := iK
      let := iFin
      have hK2 : Nat.card K = 2 := by simpa using hK
      have hchar : CharP K 2 := charP_two_of_card (m := 1) (by simpa using hK)
      let := hchar
      have hI : ∀ (b : G) (hb : b ∈ Bs),
          ggLAut L θ ⟨b, hN hb⟩ ∈ TableBExc.RecipeID .E8 K :=
        fun b hb => ggLAut_mem_of_induces L θ hN hBsI hb
      obtain ⟨hZ, e, he, E, hE, h8, hmodel⟩ :=
        e8Two_model_of_recipe_marking (hp3 ▸ hcfg) hK2 hperf θ hN hI
      exact ⟨hp3, hZ, hN, K, iK, iFin, hchar, hK2, θ, e, E, he, hE, h8, hmodel⟩

private theorem eq_bot_of_isPGroup_two_of_e8Two_model {G : Type} [Group G] [Finite G]
    {Bs L P : Subgroup G} (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    (e : L ≃* adjointGroup .E8 K) (E : Subgroup (adjointGroup .E8 K))
    (hE : IsElemAbelian 3 E) (h8 : Nat.card E = 3 ^ 8)
    (hmodel : (ggGamma L hN).range.map (MulAut.congr e).toMonoidHom =
      E.map (MulAut.conj : adjointGroup .E8 K →* MulAut (adjointGroup .E8 K)))
    (hP : IsPGroup 2 P) (hPL : P ≤ L)
    (hBsP : Bs ≤ Subgroup.normalizer (P : Set G)) : P = ⊥ := by
  classical
  let P' : Subgroup (adjointGroup .E8 K) := (P.subgroupOf L).map e.toMonoidHom
  have hPsub : IsPGroup 2 (P.subgroupOf L) := by
    rw [Subgroup.subgroupOf]
    exact hP.comap_of_injective L.subtype L.subtype_injective
  have hEP : E ≤ Subgroup.normalizer (P' : Set (adjointGroup .E8 K)) := by
    rw [Subgroup.le_normalizer_iff]
    intro z hz v hv
    have hzA : MulAut.conj z ∈ (ggGamma L hN).range.map (MulAut.congr e).toMonoidHom := by
      rw [hmodel]
      exact Subgroup.mem_map.mpr ⟨z, hz, rfl⟩
    obtain ⟨β, hβ, hβeq⟩ := Subgroup.mem_map.mp hzA
    obtain ⟨b, rfl⟩ := hβ
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hv
    have hlP : ggGamma L hN b l ∈ P.subgroupOf L := by
      apply Subgroup.mem_subgroupOf.mpr
      have h := (Subgroup.mem_normalizer_iff.mp (hBsP b.2) (l : G)).mp
        (Subgroup.mem_subgroupOf.mp hl)
      simpa only [ggGamma_coe, inv_inv] using h
    refine Subgroup.mem_map.mpr ⟨ggGamma L hN b l, hlP, ?_⟩
    have h := congrArg (fun φ : MulAut (adjointGroup .E8 K) => φ (e l)) hβeq
    change e (ggGamma L hN b (e.symm (e l))) = z * e l * z⁻¹ at h
    simpa only [MulEquiv.coe_toMonoidHom, e.symm_apply_apply] using h
  have hbot : P' = ⊥ := FrameRoute.FS81.eq_bot_of_isPGroup_two_of_normalized_card_eight
    hK hE h8 (hPsub.map e.toMonoidHom) hEP
  apply le_bot_iff.mp
  intro y hy
  let l : L := ⟨y, hPL hy⟩
  have hmem : e l ∈ P' :=
    Subgroup.mem_map.mpr ⟨l, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  have hl1 : l = 1 := e.injective (by simpa using hmem)
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val hl1)

theorem GGConfig.lt_bstar_of_E8two {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs L D J : Subgroup G} {x : G} (hcfg : GGConfig p B Bs x L D J)
    (hmark : GGInnerDiagOnLabel (fun p lab => ggRowP_EE8 p lab ∧ lab.n = 1) p Bs L) :
    B < Bs := by
  obtain ⟨hp3, hZ, hN, K, iK, iFin, iChar, hK, -, e, E, -, hE, h8, hmodel⟩ :=
    hcfg.exists_e8Two_model_of_marking hmark
  let : Field K := iK
  let : Finite K := iFin
  let : CharP K 2 := iChar
  subst p
  apply hcfg.lt_bstar_of_inner (by rw [hZ]; simp) (inner_of_e8Two_model hN e E hmodel)
  intro U hUL hU hBsU
  rw [eq_bot_of_isPGroup_two_of_e8Two_model hN hK e E hE h8 hmodel hU hUL hBsU]
  exact bot_le

end CFSG.StandardType
