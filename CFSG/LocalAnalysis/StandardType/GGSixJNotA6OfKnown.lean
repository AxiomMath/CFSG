module

public import CFSG.LocalAnalysis.StandardType.GGSixLSixFiveKnownForms
public import CFSG.LocalAnalysis.StandardType.GGSixJNotA6KnownDefs
public import CFSG.LocalAnalysis.StandardType.GGSixOddIndexF4
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticBstar
import CFSG.LocalAnalysis.StandardType.GGTableBTwoThreeSp
import CFSG.LocalAnalysis.StandardType.GGSixJNotA6Step
import CFSG.LocalAnalysis.StandardType.GGSixJNotA6A6Syl
import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenCentJLieKnown
import CFSG.LocalAnalysis.StandardType.GGSixCtxKnownSupply
import CFSG.LocalAnalysis.StandardType.GGOneFiveNormalizer

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

open scoped commutatorElement

theorem center_eq_bot_and_aut_inner_of_model {L : Type} [Group L] [Finite L] {m : ℕ}
    (hm3 : 3 ≤ m) (hLm : LieModel L .PSp m 2 1) :
    Subgroup.center L = ⊥ ∧ ∀ φ : MulAut L, ∃ l : L, φ = MulAut.conj l := by
  obtain ⟨⟨-, -, hk, -⟩, K, _, _, hK, ⟨e⟩⟩ := hLm.statedClassicalModel (by decide)
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two le_rfl hK
  have : NeZero m := ⟨by omega⟩
  have hK2 : Nat.card K = 2 := by simpa using hK
  refine ⟨?_, fun φ => ?_⟩
  · have h := Subgroup.map_center_eq e
    rw [TableBSymp.center_spProj_eq_bot] at h
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h
  · obtain ⟨r, hr⟩ := TwoThree.mem_range_conj_sp hK2 hm3 (MulAut.congr e φ)
    refine ⟨e.symm r, MulEquiv.ext fun j => ?_⟩
    have := congrArg (fun β : MulAut (LargeEvenProj (LargeEvenSpGroup K m)) => e.symm (β (e j))) hr
    simpa [MulAut.conj_apply] using this.symm

@[expose] def GGSixA6InsideF4Known : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ) (G₀ B L D J : Subgroup X) (x : X),
    LieModel (↥G₀ ⧸ Subgroup.center ↥G₀) .F4 n 2 1 →
    Subgroup.center ↥G₀ = ⊥ → B ≤ G₀ → IsElemAbelian 3 B → 3 ^ 4 ≤ Nat.card B →
    L ≤ G₀ → IsComponentOf L (G₀ ⊓ Subgroup.centralizer {x}) → x ≠ 1 →
    (∀ S : Subgroup X, S ≤ G₀ ⊓ Subgroup.centralizer (L : Set X) → IsPGroup 3 S → IsCyclic S) →
    LargeEvenStdSubPre 3 B x L D J → Nonempty (↥J ≃* alternatingGroup (Fin 6)) →
      (∃ D₁ K₁ : Subgroup X, LargeEvenStdSubPre 3 B x L D₁ K₁ ∧ ¬ LargeEvenSmall K₁) ∨
        ∀ U : Subgroup X, U ≤ L → IsPGroup 2 U → B ≤ Subgroup.normalizer (U : Set X) → U = ⊥

section KnownLie

theorem ggSixA6Known_of_red (h : GGSixA6KnownRed) : GGSixA6Known := by
  intro X _ _ t n f ψ p G₀ B₁ D J L x hrange hker hmodel hp hp2 hna hBN hVI hBe hB4 hDB hD hJc
    hxD hx1 hLG hLc hJL hDL hmk hA6
  obtain ⟨hp3, hf1, hty, hZ, hBG, m, hm3, hLm⟩ := h X t n f ψ p G₀ B₁ D J L x hrange hker hmodel
    hp hp2 hna hBN hVI hBe hB4 hDB hD hJc hxD hx1 hLG hLc hJL hDL hmk hA6
  obtain ⟨hZL, hAut⟩ := center_eq_bot_and_aut_inner_of_model hm3 hLm
  exact ⟨hp3, hf1, hty, hZ, hBG, ⟨m, hm3, hLm⟩, hZL, hAut⟩

theorem ggSixA6InsideF4_of_rank (hL : GGF4TwoLocalRankInput) {X : Type} [Group X] [Finite X]
    {n : ℕ} (ψ : (ggU .F4 n 1).K →* X) (G₀ B U : Subgroup X)
    (hadm : StatedLieAdmissible .F4 n 2 1) (hrank : 2 ≤ (ggU .F4 n 1).D.rank)
    (hrange : ψ.range = G₀) (hker : ψ.ker ≤ Subgroup.center (ggU .F4 n 1).K)
    (hperf : commutator ↥G₀ = ⊤) (hlie : LieModel (↥G₀ ⧸ Subgroup.center ↥G₀) .F4 n 2 1)
    (hZ : Subgroup.center ↥G₀ = ⊥) (hBG : B ≤ G₀) (hUG : U ≤ G₀) (hBe : IsElemAbelian 3 B)
    (hB4 : 3 ^ 4 ≤ Nat.card B) (hU2 : IsPGroup 2 U)
    (hBU : B ≤ Subgroup.normalizer (U : Set X)) : U = ⊥ := by
  by_contra hU0
  let ψ' : (ggU .F4 n 1).K →* ↥G₀ := ψ.codRestrict G₀ fun a => hrange ▸ ⟨a, rfl⟩
  have hker' : ψ'.ker = ψ.ker := MonoidHom.ker_codRestrict ψ G₀ _
  have hrange' : ψ'.range = ⊤ := by
    rw [eq_top_iff]
    intro g _
    obtain ⟨a, ha⟩ : (g : X) ∈ ψ.range := hrange ▸ g.2
    exact ⟨a, Subtype.ext ha⟩
  have hperf' : commutator ↥(⊤ : Subgroup ↥G₀) = ⊤ := by
    have : Group.IsPerfect ↥G₀ := Group.isPerfect_def.mpr hperf
    exact Group.isPerfect_def.mp (Group.IsPerfect.ofSurjective
      (f := (Subgroup.topEquiv (G := ↥G₀)).symm.toMonoidHom) (Subgroup.topEquiv.symm.surjective))
  have hlie' : LieModel (↥(⊤ : Subgroup ↥G₀) ⧸ Subgroup.center ↥(⊤ : Subgroup ↥G₀)) .F4 n 2 1 :=
    LieModel.of_mulEquiv (QuotientGroup.congr _ _ (Subgroup.topEquiv (G := ↥G₀)).symm
      (Subgroup.map_center_eq _)) hlie
  have hcfg : GGF4Config n 1 ψ' ⊤ :=
    ⟨hadm, hrank, hrange', hker' ▸ hker, hperf', hlie', by
      rw [Subgroup.coe_top, Subgroup.centralizer_univ, hZ]⟩
  have hU0' : U.subgroupOf G₀ ≠ ⊥ := fun h => hU0 (by
    rw [eq_bot_iff]
    intro u hu
    have h1 : (⟨u, hUG hu⟩ : ↥G₀) ∈ U.subgroupOf G₀ := hu
    rw [h] at h1
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val (Subgroup.mem_bot.mp h1)))
  have h := hL ↥G₀ n 1 ψ' ⊤ hcfg 3 Nat.prime_three (by norm_num) (by norm_num)
    (U.subgroupOf G₀) le_top hU0' (hU2.of_equiv (Subgroup.subgroupOfEquivOfLe hUG).symm)
    (B.subgroupOf G₀) le_top (by
      intro g hg
      rw [Subgroup.mem_normalizer_iff]
      intro u
      have := Subgroup.mem_normalizer_iff.mp (hBU hg) (u : X)
      simpa [Subgroup.mem_subgroupOf] using this) (hBe.subgroupOf G₀)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBG).toEquiv] at h
  omega

@[expose] def GGSixA6InsideF4Psi : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ) (ψ : (ggU .F4 n 1).K →* X)
    (G₀ B L D J : Subgroup X) (x : X),
    StatedLieAdmissible .F4 n 2 1 → 2 ≤ (ggU .F4 n 1).D.rank → ψ.range = G₀ →
    ψ.ker ≤ Subgroup.center (ggU .F4 n 1).K → commutator ↥G₀ = ⊤ →
    LieModel (↥G₀ ⧸ Subgroup.center ↥G₀) .F4 n 2 1 →
    Subgroup.center ↥G₀ = ⊥ → B ≤ G₀ → IsElemAbelian 3 B → 3 ^ 4 ≤ Nat.card B →
    L ≤ G₀ → IsComponentOf L (G₀ ⊓ Subgroup.centralizer {x}) → x ≠ 1 →
    (∀ S : Subgroup X, S ≤ G₀ ⊓ Subgroup.centralizer (L : Set X) → IsPGroup 3 S → IsCyclic S) →
    LargeEvenStdSubPre 3 B x L D J → Nonempty (↥J ≃* alternatingGroup (Fin 6)) →
      (∃ D₁ K₁ : Subgroup X, LargeEvenStdSubPre 3 B x L D₁ K₁ ∧ ¬ LargeEvenSmall K₁) ∨
        ∀ U : Subgroup X, U ≤ L → IsPGroup 2 U → B ≤ Subgroup.normalizer (U : Set X) → U = ⊥

theorem ggSixA6InsideF4Psi_of_rank (hL : GGF4TwoLocalRankInput) : GGSixA6InsideF4Psi :=
  fun X _ _ n ψ G₀ B L D J x hadm hrank hrange hker hperf hlie hZ hBG hBe hB4 hLG _ _ _ _ _ =>
    Or.inr fun U hUL hU2 hBU =>
      ggSixA6InsideF4_of_rank hL ψ G₀ B U hadm hrank hrange hker hperf hlie hZ hBG (hUL.trans hLG)
        hBe hB4 hU2 hBU

theorem ggSixJNotA6Input_of_known_split (hAr : GGSixA6KnownRed) (hSp : GGSixA6InsideSpKnown)
    (hF4 : GGSixA6InsideF4Psi) : GGSixJNotA6Input := by
  have hA := ggSixA6Known_of_red hAr
  intro G _ _ p B Bs x L D J t n f ψ hctx
  refine ⟨fun φ => ?_⟩
  obtain ⟨-, -, ⟨hadm, hrank⟩, ⟨hrange, hker⟩, ⟨hperf, hmodel⟩, ⟨hBsN, hVI⟩, -, -⟩ := hctx.2
  have hBBs : B ≤ Bs := hctx.bstar.1
  have hLc : IsComponentOf L (ggG0 p B x L D J ⊓ Subgroup.centralizer {x}) :=
    hctx.l_isComponentOf_inf
  have hmkL : LargeEvenMarking ↥L (fun lab _ _ _ _ _ => LargeEvenSplit p lab) :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.1) hctx.stdType.1
  have hna : ¬ p ∣ Nat.card (Subgroup.centralizer (ggG0 p B x L D J : Set G)) :=
    not_dvd_card_centralizer_ggG0_of_stdSub hctx.prime hctx.sstar hctx.stdType hctx.stdSub
  obtain ⟨hp3, hf1, hty, hZ0, hBG0, -, hZL, hAut⟩ :=
    hA G t n f ψ p (ggG0 p B x L D J) B D J L x hrange hker hmodel hctx.prime hctx.ne_two hna
      (hBBs.trans hBsN) (fun b hb => hVI b (hBBs hb)) hctx.sstar.1.1 hctx.pow_four_le_card_b
      hctx.stdSub.1.1 hctx.card_d hctx.j_isComponentOf_inf hctx.x_mem_d hctx.sstar.2.2.1
      le_sup_left hLc (hctx.j_le_inf.trans inf_le_left) hctx.not_le_centralizer_L hmkL ⟨φ⟩
  have hBabel : IsElemAbelian p B := hctx.sstar.1.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hctx.sstar.2.2.2.1.1
  have hcyc : ∀ S : Subgroup G, S ≤ Subgroup.centralizer (L : Set G) → IsPGroup p S →
      IsCyclic S := hctx.sstar.2.2.2.2
  have hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S := by
    rw [hp3]
    exact exists_noncyclic_three_group_of_alt_six (hctx.j_le_inf.trans inf_le_left) φ
  have hNL : Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (L : Set G) :=
    fun g hg => mem_normalizer_of_sstar hctx.sstar hnc hg
  obtain ⟨T, hTx, hT2, hBT, hTB⟩ := hctx.stdType.2.1
  obtain ⟨U, hUL, hU2, hBU, hUne⟩ :=
    exists_ne_bot_isPGroup_two_normalized hctx.prime hBabel hctx.sstar.2.1 hctx.sstar.2.2.1 hLx
      hZL hAut hNL (ggSixCtx_normalizer_and_innerDiag_on_L hctx).1 hcyc hTx hT2 hBT hTB
  have hmodel' : LieModel (↥(ggG0 p B x L D J) ⧸ Subgroup.center ↥(ggG0 p B x L D J)) t n 2 1 :=
    hf1 ▸ hmodel
  have hLG : L ≤ ggG0 p B x L D J := le_sup_left
  have hB4 : 3 ^ 4 ≤ Nat.card B := hp3 ▸ hctx.pow_four_le_card_b
  have hB3 : IsElemAbelian 3 B := hp3 ▸ hBabel
  have hcyc3 : ∀ S : Subgroup G, S ≤ ggG0 p B x L D J ⊓ Subgroup.centralizer (L : Set G) →
      IsPGroup 3 S → IsCyclic S := fun S hS hS3 => hcyc S (hS.trans inf_le_right) (hp3 ▸ hS3)
  have hpre : LargeEvenStdSubPre 3 B x L D J := hp3 ▸ hctx.stdSub.1
  have hclose : (∃ D₁ K₁ : Subgroup G, LargeEvenStdSubPre 3 B x L D₁ K₁ ∧ ¬ LargeEvenSmall K₁) →
      False := fun ⟨D₁, K₁, hpre', hns⟩ =>
    hctx.stdSub.2 ⟨hp3, D₁, K₁, hp3 ▸ hpre', hns⟩ (Or.inr ⟨φ⟩)
  rcases hty with ⟨rfl, hn3⟩ | rfl
  ·
    rcases hSp G n (ggG0 p B x L D J) B L D J x hn3 hmodel' hZ0 hBG0 hB3 hB4 hLG hLc
        hctx.sstar.2.2.1 hcyc3 hpre ⟨φ⟩ with h | h
    · exact hclose h
    · exact hUne (h U hUL hU2 hBU)
  ·
    subst hf1
    rcases hF4 G n ψ (ggG0 p B x L D J) B L D J x hadm hrank hrange hker hperf hmodel' hZ0 hBG0
        hB3 hB4 hLG hLc hctx.sstar.2.2.1 hcyc3 hpre ⟨φ⟩ with h | h
    · exact hclose h
    · exact hUne (h U hUL hU2 hBU)

theorem ggSixJNotA6Input_of_known_rank (hAr : GGSixA6KnownRed) (hSp : GGSixA6InsideSpKnown)
    (hL : GGF4TwoLocalRankInput) : GGSixJNotA6Input :=
  ggSixJNotA6Input_of_known_split hAr hSp (ggSixA6InsideF4Psi_of_rank hL)

end KnownLie

end CFSG.StandardType
