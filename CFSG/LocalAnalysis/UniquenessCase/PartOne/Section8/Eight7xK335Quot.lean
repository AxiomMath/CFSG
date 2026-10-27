module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xK335Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore
import CFSG.LocalAnalysis.RankThreeUC.ProofSupport.PrimeFreeGammaContainment.PrimeFreeGammaContainment
import CFSG.LocalAnalysis.UniquenessCase.UC1K327Core
import CFSG.LocalAnalysis.ShultStronglyClosedTI.QuotientStrongClosure
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xK335Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.RankThreeUC.ProofSupport.PrimeFreeGammaContainment
  (le_rankThreeGamma_of_normal_coprime)

private theorem k335qlie_inf_eq_bot {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hL : LieModel ↥L .PSL 3 2 2) (N : Subgroup G) [N.Normal] (hN : ¬ 3 ∣ Nat.card N) :
    L ⊓ N = ⊥ := by
  rcases (k335_simple_L hL).eq_bot_or_eq_top_of_normal (N.subgroupOf L) with hbot | htop
  · have hdisj : Disjoint N L := Subgroup.subgroupOf_eq_bot.mp hbot
    exact disjoint_iff.mp hdisj.symm
  · exfalso
    have hLN : L ≤ N := Subgroup.subgroupOf_eq_top.mp htop
    have hdvd : Nat.card L ∣ Nat.card N := Subgroup.card_dvd_of_le hLN
    rw [k335_card_L hL] at hdvd
    exact hN (dvd_trans (by norm_num : (3 : ℕ) ∣ 20160) hdvd)

theorem k335_quot_lie {G : Type} [Group G] [Finite G] {L P : Subgroup G}
    (hL : LieModel ↥L .PSL 3 2 2) (hP : CFSG.ABGLocalTools.IsSylowOf 3 P L) (N : Subgroup G)
    [N.Normal] (hN : ¬ 3 ∣ Nat.card N) :
    LieModel ↥(L.map (QuotientGroup.mk' N)) .PSL 3 2 2 ∧
      CFSG.ABGLocalTools.IsSylowOf 3 (P.map (QuotientGroup.mk' N))
        (L.map (QuotientGroup.mk' N)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdisj : Disjoint N L := by
    rw [disjoint_iff, inf_comm]
    exact k335qlie_inf_eq_bot hL N hN
  let f : ↥L →* G ⧸ N := (QuotientGroup.mk' N).domRestrict L
  have hfker : f.ker = ⊥ := by
    rw [show f.ker = (QuotientGroup.mk' N).ker.subgroupOf L from
      MonoidHom.ker_domRestrict L (QuotientGroup.mk' N)]
    rw [QuotientGroup.ker_mk']
    exact Subgroup.subgroupOf_eq_bot.mpr hdisj
  have hfinj : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp hfker
  have hfrange : f.range = L.map (QuotientGroup.mk' N) :=
    MonoidHom.domRestrict_range L (QuotientGroup.mk' N)
  let e : ↥L ≃* ↥(L.map (QuotientGroup.mk' N)) :=
    (MonoidHom.ofInjective hfinj).trans (MulEquiv.subgroupCongr hfrange)
  refine ⟨LieModel.of_mulEquiv e hL, ?_⟩
  have hcardP : Nat.card (P.map (QuotientGroup.mk' N)) = Nat.card P := by
    let fP : ↥P →* G ⧸ N := (QuotientGroup.mk' N).domRestrict P
    have hfPker : fP.ker = ⊥ := by
      rw [show fP.ker = (QuotientGroup.mk' N).ker.subgroupOf P from
        MonoidHom.ker_domRestrict P (QuotientGroup.mk' N)]
      rw [QuotientGroup.ker_mk']
      exact Subgroup.subgroupOf_eq_bot.mpr (hdisj.mono_right hP.le)
    have hfPinj : Function.Injective fP := (MonoidHom.ker_eq_bot_iff fP).mp hfPker
    have hfPrange : fP.range = P.map (QuotientGroup.mk' N) :=
      MonoidHom.domRestrict_range P (QuotientGroup.mk' N)
    rw [← hfPrange]
    exact (Nat.card_congr (MonoidHom.ofInjective hfPinj).toEquiv).symm
  have hcardL : Nat.card (L.map (QuotientGroup.mk' N)) = Nat.card L :=
    (Nat.card_congr e.toEquiv).symm
  refine CFSG.ABGLocalTools.isSylowOf_of_card (Subgroup.map_mono hP.le) ?_
  rw [hcardP, hcardL]
  exact hP.card_eq

theorem k335_quot_gamma {G : Type} [Group G] [Finite G] {L P : Subgroup G} (hP : IsPGroup 3 P)
    (hΓ : CFSG.Open.rankThreeGamma 1 3 P ≤ Subgroup.normalizer (L : Set G)) (N : Subgroup G)
    [N.Normal] (hN : ¬ 3 ∣ Nat.card N) :
    CFSG.Open.rankThreeGamma 1 3 (P.map (QuotientGroup.mk' N)) ≤
      Subgroup.normalizer ((L.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcop : Nat.Coprime 3 (Nat.card N) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hN
  change CFSG.Open.GLBCore 3 1 (P.map (QuotientGroup.mk' N)) ≤ _
  rw [← CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC327.GLBCore_map_quotient_eq 3 N P hcop hP]
  exact (Subgroup.map_mono hΓ).trans (Subgroup.le_normalizer_map _)

private theorem k335qcl_isPGroup_zpowers_conj {X : Type*} [Group X] {p : ℕ} {a g : X}
    (ha : IsPGroup p (Subgroup.zpowers a)) :
    IsPGroup p (Subgroup.zpowers (g⁻¹ * a * g)) := by
  have hmap : (Subgroup.zpowers a).map (MulAut.conj g⁻¹).toMonoidHom =
      Subgroup.zpowers (g⁻¹ * a * g) := by
    rw [MonoidHom.map_zpowers]
    congr 1
    change g⁻¹ * a * (g⁻¹)⁻¹ = g⁻¹ * a * g
    rw [inv_inv]
  exact hmap ▸ ha.map (MulAut.conj g⁻¹).toMonoidHom

private theorem k335qcl_conj_into_sylow {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    (S : Sylow p X) (B : Subgroup X) (hSB : (S : Subgroup X) ≤ B) {x : X} (hxB : x ∈ B)
    (hxp : IsPGroup p (Subgroup.zpowers x)) :
    ∃ b ∈ B, b * x * b⁻¹ ∈ (S : Subgroup X) := by
  let xB : B := ⟨x, hxB⟩
  let SB : Sylow p B := S.subtype hSB
  have hxBp : IsPGroup p (Subgroup.zpowers xB) := by
    have hmap : (Subgroup.zpowers xB).map B.subtype = Subgroup.zpowers x :=
      MonoidHom.map_zpowers _ _
    exact hxp.of_equiv
      ((Subgroup.zpowers xB).equivMapOfInjective B.subtype B.subtype_injective |>.trans
        (MulEquiv.subgroupCongr hmap)).symm
  obtain ⟨Q, hQ⟩ := hxBp.exists_le_sylow
  obtain ⟨b, hb⟩ := MulAction.exists_smul_eq B Q SB
  have hbx : (MulAut.conj b) xB ∈ (b • Q : Sylow p B) :=
    Subgroup.mem_map_of_mem (MulAut.conj b).toMonoidHom (hQ (Subgroup.mem_zpowers xB))
  rw [hb] at hbx
  exact ⟨b, b.property, hbx⟩

theorem k335_quot_closed {G : Type} [Group G] [Finite G] {P S : Subgroup G}
    (hS : CFSG.ABGLocalTools.IsSylowOf 3 S ⊤) (hPS : P ≤ S)
    (hSN : S ≤ Subgroup.normalizer (P : Set G)) (hcl : CFSG.Open.fusionStronglyClosed (P : Set G) S)
    (N : Subgroup G) [N.Normal] :
    ∀ a ∈ P.map (QuotientGroup.mk' N), ∀ g : G ⧸ N,
      g⁻¹ * a * g ∈ Subgroup.normalizer ((P.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) :
        Set (G ⧸ N)) → g⁻¹ * a * g ∈ P.map (QuotientGroup.mk' N) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [CFSG.ABGLocalTools.isSylowOf_iff, Subgroup.relIndex_top_right] at hS
  obtain ⟨-, hS3, hidx⟩ := hS
  let T : Sylow 3 G := hS3.toSylow hidx
  let mk' : G →* G ⧸ N := QuotientGroup.mk' N
  let hf : Function.Surjective mk' := QuotientGroup.mk'_surjective N
  let Tbar : Sylow 3 (G ⧸ N) := T.mapSurjective hf
  have : Finite (G ⧸ N) := Finite.of_surjective mk' hf
  have hTbar_coe : (Tbar : Subgroup (G ⧸ N)) = S.map mk' :=
    Sylow.coe_mapSurjective (P := T) hf
  have hsc : CFSG.Open.fusionStronglyClosed (P.map mk' : Set (G ⧸ N))
      (Tbar : Subgroup (G ⧸ N)) :=
    CFSG.ShultStronglyClosedTI.stronglyClosed_map_surjective mk' hf T P hPS hcl
  have hTbar_le : (Tbar : Subgroup (G ⧸ N)) ≤
      Subgroup.normalizer ((P.map mk' : Subgroup (G ⧸ N)) : Set (G ⧸ N)) := by
    rw [hTbar_coe]
    exact (Subgroup.map_mono hSN).trans (Subgroup.le_normalizer_map mk')
  intro a ha g hxK
  have haS : a ∈ (Tbar : Subgroup (G ⧸ N)) := by
    rw [hTbar_coe]
    exact Subgroup.map_mono hPS ha
  have haz : Subgroup.zpowers a ≤ (Tbar : Subgroup (G ⧸ N)) := Subgroup.zpowers_le.mpr haS
  have hap : IsPGroup 3 (Subgroup.zpowers a) :=
    Tbar.isPGroup'.of_injective (Subgroup.inclusion haz) (Subgroup.inclusion_injective haz)
  obtain ⟨b, hbK, hbconj⟩ := k335qcl_conj_into_sylow Tbar
    (Subgroup.normalizer ((P.map mk' : Subgroup (G ⧸ N)) : Set (G ⧸ N))) hTbar_le hxK
    (k335qcl_isPGroup_zpowers_conj (g := g) hap)
  have heq : (g * b⁻¹)⁻¹ * a * (g * b⁻¹) = b * (g⁻¹ * a * g) * b⁻¹ := by group
  have hmemS : (g * b⁻¹)⁻¹ * a * (g * b⁻¹) ∈ (Tbar : Subgroup (G ⧸ N)) := heq ▸ hbconj
  have hmemP : b * (g⁻¹ * a * g) * b⁻¹ ∈ P.map mk' := heq ▸ hsc a ha (g * b⁻¹) hmemS
  exact (Subgroup.mem_normalizer_iff (H := P.map mk').mp hbK (g⁻¹ * a * g)).mpr hmemP

private theorem k335qlie_conj_le_sup {G : Type} [Group G] {L : Subgroup G} (N : Subgroup G)
    [N.Normal]
    (h : Subgroup.normalizer ((L.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) :
      Set (G ⧸ N)) = ⊤) (g : G) : L.map (MulAut.conj g) ≤ L ⊔ N := by
  intro x hx
  obtain ⟨l, hl, rfl⟩ := hx
  have hg : QuotientGroup.mk' N g ∈
      Subgroup.normalizer ((L.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) :
        Set (G ⧸ N)) := by
    rw [h]
    exact Subgroup.mem_top _
  have hmk : QuotientGroup.mk' N (g * l * g⁻¹) ∈ L.map (QuotientGroup.mk' N) := by
    have h1 := (Subgroup.mem_normalizer_iff.mp hg (QuotientGroup.mk' N l)).mp
      (Subgroup.mem_map_of_mem (QuotientGroup.mk' N) hl)
    simpa only [map_mul, map_inv] using h1
  obtain ⟨l', hl', heq⟩ := Subgroup.mem_map.mp hmk
  obtain ⟨z, hz, hz'⟩ := (QuotientGroup.mk'_eq_mk' N).mp heq
  change g * l * g⁻¹ ∈ L ⊔ N
  rw [← hz']
  exact Subgroup.mul_mem_sup hl' hz

theorem k335_normalizer_of_quot {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hL : LieModel ↥L .PSL 3 2 2) (N : Subgroup G) [N.Normal] (hN : ¬ 3 ∣ Nat.card N)
    (hNL : N ≤ Subgroup.normalizer (L : Set G))
    (h : Subgroup.normalizer ((L.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N)) = ⊤) :
    Subgroup.normalizer (L : Set G) = ⊤ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdisjLN : Disjoint L N := by
    rw [disjoint_iff]
    exact k335qlie_inf_eq_bot hL N hN
  have hsupNormal : L ⊔ N ≤ Subgroup.normalizer (L : Set G) :=
    sup_le Subgroup.le_normalizer hNL
  rw [Subgroup.eq_top_iff']
  intro g
  set L' : Subgroup G := L.map (MulAut.conj g) with hL'def
  have hL'le : L' ≤ L ⊔ N := by
    rw [hL'def]
    exact k335qlie_conj_le_sup N h g
  have hL'normal : L' ≤ Subgroup.normalizer (L : Set G) := hL'le.trans hsupNormal
  have hnL' : (L.subgroupOf L').Normal := by
    constructor
    intro n hn x
    have hxN : (x : G) ∈ Subgroup.normalizer (L : Set G) := hL'normal x.2
    have hconj := (Subgroup.mem_normalizer_iff.mp hxN (n : G)).mp hn
    rw [Subgroup.mem_subgroupOf]
    exact hconj
  have : IsSimpleGroup ↥L := k335_simple_L hL
  have hsimpleL' : IsSimpleGroup ↥L' := by
    rw [hL'def]
    exact (Subgroup.equivMapOfInjective L (MulAut.conj g : G →* G)
      (MulAut.conj g).injective).symm.isSimpleGroup
  rcases hsimpleL'.eq_bot_or_eq_top_of_normal (L.subgroupOf L') with hbot | htop
  · exfalso
    have hdisjLL' : Disjoint L L' := Subgroup.subgroupOf_eq_bot.mp hbot
    have hcardL' : Nat.card L' = 20160 := by
      rw [hL'def, ← Nat.card_congr
        (Subgroup.equivMapOfInjective L (MulAut.conj g : G →* G)
          (MulAut.conj g).injective).toEquiv,
        k335_card_L hL]
    have hLL'sup : Nat.card (L ⊔ L' : Subgroup G) = Nat.card L * Nat.card L' :=
      CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer L L' hL'normal hdisjLL'
    have hLNsup : Nat.card (L ⊔ N : Subgroup G) = Nat.card L * Nat.card N :=
      CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer L N hNL hdisjLN
    have hdvd : Nat.card (L ⊔ L' : Subgroup G) ∣ Nat.card (L ⊔ N : Subgroup G) :=
      Subgroup.card_dvd_of_le (sup_le le_sup_left hL'le)
    rw [hLL'sup, hLNsup, k335_card_L hL, hcardL'] at hdvd
    exact hN (dvd_trans (by norm_num : (3 : ℕ) ∣ 20160)
      (Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 20160) hdvd))
  · have hL'leL : L' ≤ L := Subgroup.subgroupOf_eq_top.mp htop
    have hcard_le : Nat.card L ≤ Nat.card L' := by
      rw [hL'def]
      exact le_of_eq (Nat.card_congr
        (Subgroup.equivMapOfInjective L (MulAut.conj g : G →* G)
          (MulAut.conj g).injective).toEquiv)
    have hL'eqL : L' = L := Subgroup.eq_of_le_of_card_ge hL'leL hcard_le
    have hmap : L.map (MulAut.conj g) = L := by
      rw [← hL'def]
      exact hL'eqL
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmap

theorem k335_quot_hyp {G : Type} [Group G] [Finite G] {L P : Subgroup G} (h : K335Hyp G L P)
    (N : Subgroup G) [N.Normal] (hN : ¬ 3 ∣ Nat.card N) :
    K335Hyp (G ⧸ N) (L.map (QuotientGroup.mk' N)) (P.map (QuotientGroup.mk' N)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S, hS, hPS, hSN⟩ := k335_exists_sylow h.sylow.isPGroup h.closed
  have hcl : CFSG.Open.fusionStronglyClosed (P : Set G) S := fun a ha g hg =>
    h.closed a ha g (hSN hg)
  exact ⟨h.kGroup.quotient N, (CFSG.SectionRank.pRank_quotient_eq N hN).trans_le h.rank,
    (k335_quot_lie h.lie h.sylow N hN).1, (k335_quot_lie h.lie h.sylow N hN).2,
    k335_quot_gamma h.sylow.isPGroup h.gamma N hN, k335_quot_closed hS hPS hSN hcl N⟩

theorem K335MinCex.pPrimeCore_eq_bot {G : Type} [Group G] [Finite G] {L P : Subgroup G}
    (h : K335MinCex G L P) : CFSG.pPrimeCore 3 G = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hne
  have : (CFSG.pPrimeCore 3 G).Normal := CFSG.pPrimeCore_normal (p := 3) (G := G)
  have hN : ¬ 3 ∣ Nat.card (CFSG.pPrimeCore 3 G) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1
      (CFSG.pPrimeCore_coprime_card (p := 3) (G := G))
  have hlt : Nat.card (G ⧸ CFSG.pPrimeCore 3 G) < Nat.card G := by
    have h1 : 1 < Nat.card (CFSG.pPrimeCore 3 G) := (Subgroup.one_lt_card_iff_ne_bot _).2 hne
    have h2 : 0 < Nat.card (G ⧸ CFSG.pPrimeCore 3 G) := Nat.card_pos
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pPrimeCore 3 G)]
    nlinarith
  have hq := h.min _ hlt _ _ (k335_quot_hyp h.hyp (CFSG.pPrimeCore 3 G) hN)
  obtain ⟨hE, h9⟩ := k335_sylowL h.hyp.lie h.hyp.sylow
  have hNL : CFSG.pPrimeCore 3 G ≤ Subgroup.normalizer (L : Set G) :=
    (le_rankThreeGamma_of_normal_coprime Nat.prime_three hE (by rw [h9]; norm_num)
      inferInstance hN).trans h.hyp.gamma
  exact h.ne_top (k335_normalizer_of_quot h.hyp.lie _ hN hNL hq)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
