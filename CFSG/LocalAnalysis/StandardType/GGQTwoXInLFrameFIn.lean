module

public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameFDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameFIn2
public import CFSG.RankThree.PartOne.Q1327Z.Block
public import CFSG.LocalAnalysis.StandardType.GGQTwoDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoPairsDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyDichotomy
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRestDefs
public import CFSG.LocalAnalysis.StandardType.GGSixStepOneDefs
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrKappaBase
public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenE6Components
public import CFSG.LocalAnalysis.StandardType.GGRealKGCoverComp
public import CFSG.GroupTheory.CardMapInfKer
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.GroupTheory.InnerCentralizerProjection
public import CFSG.Mathlib.GroupTheory.CoprimeKernelLift

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem eq_one_of_mem_center_of_pow_three {Γ : Type*} [Group Γ] [Finite Γ]
    {H : Subgroup Γ} (h3 : ¬ 3 ∣ Nat.card (Subgroup.centralizer (H : Set Γ)))
    {z : ↥H} (hz : z ∈ Subgroup.center ↥H) (hz3 : z ^ 3 = 1) : z = 1 := by
  have hmem : (z : Γ) ∈ Subgroup.centralizer (H : Set Γ) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨y, hy⟩)
  have hdvd : orderOf z ∣ Nat.card (Subgroup.centralizer (H : Set Γ)) := by
    rw [← Subgroup.orderOf_coe]
    exact Subgroup.orderOf_dvd_natCard _ hmem
  have hdvd3 : orderOf z ∣ 3 := orderOf_dvd_of_pow_eq_one hz3
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd3 with h | h
  · exact orderOf_eq_one_iff.mp h
  · exact absurd (h ▸ hdvd) h3

theorem ggQTwoFRCfg_of_marking {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J) (hI : GGQTwoI1 Bs D J)
    (hxL : x ∈ L) {R : Type} [Group R] {I : Set (MulAut R)}
    (hInn : ∀ φ ∈ I, ∃ r : R, φ = MulAut.conj r)
    (θ : ↥(ggG0 3 B x L D J) ⧸ Subgroup.center ↥(ggG0 3 B x L D J) ≃* R)
    (hperf : commutator ↥(ggG0 3 B x L D J) = ⊤)
    (hBs : ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) :
    Bs ≤ ggG0 3 B x L D J ∧
      GGQTwoFRCfg ((Bs.subgroupOf (ggG0 3 B x L D J)).map (ggMarkHom θ))
        (ggMarkHom θ ⟨x, le_ggG0_left 3 B x L D J hxL⟩)
        ((L.subgroupOf (ggG0 3 B x L D J)).map (ggMarkHom θ))
        ((D.subgroupOf (ggG0 3 B x L D J)).map (ggMarkHom θ))
        ((J.subgroupOf (ggG0 3 B x L D J)).map (ggMarkHom θ)) := by
  let G0 : Subgroup G := ggG0 3 B x L D J
  let π : ↥G0 →* R := ggMarkHom θ
  let xG0 : ↥G0 := ⟨x, le_ggG0_left 3 B x L D J hxL⟩
  let E : Subgroup R := (Bs.subgroupOf G0).map π
  let Lbar : Subgroup R := (L.subgroupOf G0).map π
  let Dbar : Subgroup R := (D.subgroupOf G0).map π
  let Jbar : Subgroup R := (J.subgroupOf G0).map π
  let xbar : R := π xG0
  have hcfg : GGConfig 3 B Bs x L D J := hS.1.1
  have hDJ : LargeEvenStdSub 3 B x L D J := hcfg.2.2
  obtain ⟨hp, hBsElem, hxBs, hLx, h4⟩ := hcfg.tableB_facts
  have hxne : x ≠ 1 := by
    intro h
    have hord := hcfg.orderOf_x
    rw [h, orderOf_one] at hord
    norm_num at hord
  have hSstar : LargeEvenSStar 3 B x L := hcfg.1.2.2.2.2.2.2.1
  have hst : LargeEvenStandardType 3 B x L := hcfg.1.2.2.2.2.2.2.2
  have hLcomp : IsComponentOf L (Subgroup.centralizer ({x} : Set G)) := hSstar.2.2.2.1
  have hBsL : Bs ≤ Subgroup.normalizer (L : Set G) :=
    GGDichotomy.le_normalizer_of_innerDiagOn hS.1.2.2.1.1
  have hBsG0 : Bs ≤ Subgroup.normalizer (G0 : Set G) :=
    GGDichotomy.le_normalizer_of_innerDiagOn hS.1.2.2.2.2
  have h3C : ¬ 3 ∣ Nat.card (Subgroup.centralizer (G0 : Set G)) :=
    not_dvd_card_centralizer_ggG0_of_stdSub hp hSstar hst hDJ
  have h3center : ¬ 3 ∣ Nat.card (Subgroup.center ↥G0) :=
    not_three_dvd_card_center_ggG0 hS
  have hkerπ : π.ker = Subgroup.center ↥G0 := by
    rw [show π = ggQuotHom (L := G0) θ from rfl, ker_ggQuotHom]
  have hπsurj : Function.Surjective π :=
    θ.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center ↥G0))
  have hperfG0 : Group.IsPerfect ↥G0 := ⟨hperf⟩
  have hLG0 : L ≤ G0 := le_ggG0_left 3 B x L D J
  have hDleBs : D ≤ Bs := hDJ.1.1.trans hcfg.2.1.1
  have hBG : Bs ≤ G0 := le_ggG0_of_marking hS hInn θ hperf hBs
  refine ⟨hBG, ?_⟩
  have hdisjBs : (Bs.subgroupOf G0) ⊓ π.ker = ⊥ := by
    ext b
    constructor
    · intro hb
      rw [Subgroup.mem_inf] at hb
      have hbBs : (b : G) ∈ Bs := hb.1
      have hbcenter : b ∈ Subgroup.center ↥G0 := by
        rw [← hkerπ]
        exact hb.2
      have hbC : (b : G) ∈ Subgroup.centralizer (G0 : Set G) := by
        have hmem : (b : G) ∈ (Subgroup.center ↥G0).map G0.subtype := ⟨b, hbcenter, rfl⟩
        rw [CFSG.center_map_subtype_eq_inf_centralizer] at hmem
        exact hmem.2
      have hbot : (b : G) ∈ (⊥ : Subgroup G) := by
        have := Subgroup.mem_inf.mpr ⟨hbBs, hbC⟩
        rwa [bstar_inf_centralizer_ggG0_eq_bot hcfg] at this
      simpa using hbot
    · intro hb
      rw [Subgroup.mem_bot] at hb
      subst hb
      exact Subgroup.mem_inf.mpr ⟨Subgroup.one_mem _, Subgroup.one_mem _⟩
  have hdisjD : (D.subgroupOf G0) ⊓ π.ker = ⊥ := by
    rw [eq_bot_iff]
    intro d hd
    rw [Subgroup.mem_inf] at hd
    have hdBs : d ∈ Bs.subgroupOf G0 :=
      Subgroup.mem_subgroupOf.mpr (hDleBs (Subgroup.mem_subgroupOf.mp hd.1))
    have : d ∈ (Bs.subgroupOf G0) ⊓ π.ker := Subgroup.mem_inf.mpr ⟨hdBs, hd.2⟩
    rwa [hdisjBs] at this
  have hcardE : Nat.card E = Nat.card Bs := by
    have h1 := CFSG.card_map_eq_card_of_inf_ker_eq_bot π (J := Bs.subgroupOf G0) hdisjBs
    have h2 : Nat.card ↥(Bs.subgroupOf G0) = Nat.card ↥Bs :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBG).toEquiv
    rw [h1, h2]
  have hcardD : Nat.card Dbar = 9 := by
    have h1 := CFSG.card_map_eq_card_of_inf_ker_eq_bot π (J := D.subgroupOf G0) hdisjD
    have h2 : Nat.card ↥(D.subgroupOf G0) = Nat.card ↥D :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hDleBs.trans hBG)).toEquiv
    have h3 : Nat.card D = 3 ^ 2 := hDJ.1.2.2.1
    rw [h1, h2, h3]
    norm_num
  have hEelem : IsElemAbelian 3 E :=
    CFSG.Open.IsElemAbelian.map (CFSG.Open.IsElemAbelian.subgroupOf hBsElem G0) π
  have hxG0pow : xG0 ^ 3 = 1 := by
    apply Subtype.ext
    simpa using hBsElem.2 x hxBs
  have hkerp : ∀ z ∈ π.ker, z ^ 3 = 1 → z = 1 := by
    intro z hz hz3
    have hzc : z ∈ Subgroup.center ↥G0 := by
      rw [← hkerπ]
      exact hz
    exact eq_one_of_mem_center_of_pow_three (Γ := G) (H := G0) h3C hzc hz3
  have hker_le_center : π.ker ≤ Subgroup.center ↥G0 := hkerπ.le
  have hLcompMap : IsComponentOf Lbar (Subgroup.centralizer ({xbar} : Set R)) := by
    have hLsub : IsComponentOf (L.subgroupOf G0)
        (Subgroup.centralizer ({xG0} : Set ↥G0)) := by
      have hcentEq : (Subgroup.centralizer ({x} : Set G)).subgroupOf G0 =
          Subgroup.centralizer ({xG0} : Set ↥G0) := by
        ext z
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff,
          Subgroup.mem_centralizer_singleton_iff]
        constructor
        · intro hz
          exact Subtype.ext hz
        · intro hz
          exact congrArg Subtype.val hz
      have h := ggIsComponentOf_subgroupOf_of_le G0 hLG0 hLcomp
      rwa [hcentEq] at h
    have h := RealKGCover.isComponentOf_map_centralizer (p := 3) (φ := π) hπsurj
      hker_le_center hkerp (X := ({xG0} : Set ↥G0)) (fun y hy => by
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact hxG0pow) hLsub
    simpa [Lbar, xbar] using h
  have hmapEq : ((L ⊓ Subgroup.centralizer (D : Set G)).subgroupOf G0).map π =
      Lbar ⊓ Subgroup.centralizer (Dbar : Set R) := by
    apply le_antisymm
    · rintro y ⟨c, hc, rfl⟩
      rw [Subgroup.mem_inf]
      refine ⟨Subgroup.mem_map_of_mem π hc.1, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro z ⟨d, hd, rfl⟩
      have hcd : (c : G) * (d : G) = (d : G) * (c : G) :=
        (Subgroup.mem_centralizer_iff.mp hc.2 (d : G) (Subgroup.mem_subgroupOf.mp hd)).symm
      rw [← map_mul, ← map_mul]
      exact congrArg π (Subtype.ext hcd.symm)
    · rintro y ⟨hyL, hyD⟩
      obtain ⟨l, hlL, rfl⟩ := Subgroup.mem_map.mp hyL
      have hlC : (l : G) ∈ Subgroup.centralizer (D : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro d hd
        have hdG0 : d ∈ G0 := hDleBs.trans hBG hd
        let dG0 : ↥G0 := ⟨d, hdG0⟩
        have hd3 : dG0 ^ 3 = 1 := by
          apply Subtype.ext
          simpa using hDJ.1.2.1.2 d hd
        have hmem : π dG0 ∈ Dbar :=
          Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hd)
        have hcomm : π l * π dG0 = π dG0 * π l :=
          (Subgroup.mem_centralizer_iff.mp hyD (π dG0) hmem).symm
        have hz : l * dG0 * l⁻¹ * dG0⁻¹ ∈ Subgroup.center ↥G0 := by
          rw [← hkerπ]
          apply MonoidHom.mem_ker.mpr
          simp only [map_mul, map_inv]
          rw [hcomm]
          group
        have hconj : l * dG0 * l⁻¹ = dG0 :=
          CFSG.RankThree.PartOne.Q1327Z.commute_of_commutator_mem_center hp h3center hd3 hz
        have hcomm' : l * dG0 = dG0 * l := by
          calc l * dG0 = (l * dG0 * l⁻¹) * l := by group
            _ = dG0 * l := by rw [hconj]
        exact (congrArg Subtype.val hcomm').symm
      exact Subgroup.mem_map.mpr ⟨l, ⟨hlL, hlC⟩, rfl⟩
  have hJleG0 : J ≤ G0 := (hDJ.1.2.2.2.2.2.1.1.trans inf_le_left).trans hLG0
  have hJcomp : IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)) :=
    hDJ.1.2.2.2.2.2.1
  have hJcompMap : IsComponentOf Jbar (Lbar ⊓ Subgroup.centralizer (Dbar : Set R)) := by
    have hJsub : IsComponentOf (J.subgroupOf G0)
        ((L ⊓ Subgroup.centralizer (D : Set G)).subgroupOf G0) :=
      ggIsComponentOf_subgroupOf_of_le G0 hJleG0 hJcomp
    have hmap := CFSG.LocalAnalysis.GLTheoremA.I142N.isComponentOf_map π
      (fun g hg => hkerπ.le (MonoidHom.mem_ker.mpr hg)) (isComponentOf_iff_open.mp hJsub)
    rw [← hmapEq]
    exact isComponentOf_iff_open.mpr hmap
  have hSC : ∀ g ∈ Subgroup.centralizer (E : Set R), g ^ 3 = 1 → g ∈ E := by
    intro g hg hg3
    obtain ⟨g0, hg0⟩ := hπsurj g
    obtain ⟨m, hmπ, hm3⟩ := CFSG.CoprimeKernel.exists_pow_lift (f := π) hp
      (by rwa [hkerπ]) (n := g0) (by rw [hg0]; exact hg3)
    have hmemC : ((g0 ^ m : ↥G0) : G) ∈ Subgroup.centralizer (Bs : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      have hbG0 : b ∈ G0 := hBG hb
      let bG0 : ↥G0 := ⟨b, hbG0⟩
      have hb3 : bG0 ^ 3 = 1 := by
        apply Subtype.ext
        simpa using hBsElem.2 b hb
      have hmemE : π bG0 ∈ E :=
        Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hb)
      have hcomm : π (g0 ^ m) * π bG0 = π bG0 * π (g0 ^ m) := by
        rw [hmπ, hg0]
        exact (Subgroup.mem_centralizer_iff.mp hg (π bG0) hmemE).symm
      have hz : (g0 ^ m) * bG0 * (g0 ^ m)⁻¹ * bG0⁻¹ ∈ Subgroup.center ↥G0 := by
        rw [← hkerπ]
        apply MonoidHom.mem_ker.mpr
        simp only [map_mul, map_inv]
        rw [hcomm]
        group
      have hconj : (g0 ^ m) * bG0 * (g0 ^ m)⁻¹ = bG0 :=
        CFSG.RankThree.PartOne.Q1327Z.commute_of_commutator_mem_center hp h3center hb3 hz
      have hcomm' : (g0 ^ m) * bG0 = bG0 * (g0 ^ m) := by
        calc (g0 ^ m) * bG0 = ((g0 ^ m) * bG0 * (g0 ^ m)⁻¹) * (g0 ^ m) := by group
          _ = bG0 * (g0 ^ m) := by rw [hconj]
      exact (congrArg Subtype.val hcomm').symm
    have hm3' : (((g0 ^ m : ↥G0) : G)) ^ 3 = 1 := by
      simpa using congrArg Subtype.val hm3
    have hmemBs : (g0 ^ m : ↥G0) ∈ Bs.subgroupOf G0 := by
      rw [Subgroup.mem_subgroupOf]
      exact hcfg.2.1.2.2.2 _ hmemC hm3'
    have hgeq : g = π (g0 ^ m) := by rw [hmπ, hg0]
    rw [hgeq]
    exact Subgroup.mem_map_of_mem π hmemBs
  have hxE : xbar ∈ E := Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hxBs)
  have hxnebar : xbar ≠ 1 := by
    intro h
    have hxcenter : xG0 ∈ Subgroup.center ↥G0 := by
      rw [← hkerπ]
      exact MonoidHom.mem_ker.mpr h
    have hxC : (x : G) ∈ Subgroup.centralizer (G0 : Set G) := by
      have hmem : (x : G) ∈ (Subgroup.center ↥G0).map G0.subtype := ⟨xG0, hxcenter, rfl⟩
      rw [CFSG.center_map_subtype_eq_inf_centralizer] at hmem
      exact hmem.2
    have hbot : (x : G) ∈ (⊥ : Subgroup G) := by
      have := Subgroup.mem_inf.mpr ⟨hxBs, hxC⟩
      rwa [bstar_inf_centralizer_ggG0_eq_bot hcfg] at this
    exact hxne (by simpa using hbot)
  have hxLbar : xbar ∈ Lbar :=
    Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hxL)
  have hDE : Dbar ≤ E := by
    rintro y ⟨d, hd, rfl⟩
    exact Subgroup.mem_map_of_mem π
      (Subgroup.mem_subgroupOf.mpr (hDleBs (Subgroup.mem_subgroupOf.mp hd)))
  have hxDbar : xbar ∈ Dbar :=
    Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hDJ.1.2.2.2.1)
  have hEN : E ≤ Subgroup.normalizer (Lbar : Set R) := by
    have h1 : Bs.subgroupOf G0 ≤
        Subgroup.normalizer ((L.subgroupOf G0 : Subgroup ↥G0) : Set ↥G0) := by
      rw [← Subgroup.subgroupOf_normalizer_eq hLG0]
      intro b hb
      exact Subgroup.mem_subgroupOf.mpr (hBsL hb)
    calc E = (Bs.subgroupOf G0).map π := rfl
      _ ≤ (Subgroup.normalizer ((L.subgroupOf G0 : Subgroup ↥G0) : Set ↥G0)).map π :=
        Subgroup.map_mono h1
      _ ≤ Subgroup.normalizer (((L.subgroupOf G0).map π : Subgroup R) : Set R) :=
        Subgroup.le_normalizer_map π
  have hxCL : x ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.mp (hLx hl)
  have hxbarCL : xbar ∈ Subgroup.centralizer (Lbar : Set R) := by
    change π xG0 ∈ Subgroup.centralizer ((L.subgroupOf G0).map π : Set R)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hy
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxCL (l : G) hl)
  have hCL : E ⊓ Subgroup.centralizer (Lbar : Set R) = Subgroup.zpowers xbar := by
    apply le_antisymm
    · intro y hy
      rw [Subgroup.mem_inf] at hy
      obtain ⟨hyE, hyC⟩ := hy
      obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hyE
      have hbBs : (b : G) ∈ Bs := hb
      have hbCL : (b : G) ∈ Subgroup.centralizer (L : Set G) := by
        refine CFSG.mem_centralizer_of_commutator_mem_center (J := L)
          ⟨hLcomp.2.2.1⟩ (hBsL hbBs) ?_
        intro j hj
        have hbG0 : (b : G) ∈ G0 := hBG hbBs
        have hjG0 : j ∈ G0 := hLG0 hj
        have hconj_mem : (b : G) * j * (b : G)⁻¹ ∈ L :=
          (Subgroup.mem_normalizer_iff.mp (hBsL hbBs) j).mp hj
        have hzL : (b : G) * j * (b : G)⁻¹ * j⁻¹ ∈ L :=
          L.mul_mem hconj_mem (L.inv_mem hj)
        have hzG0 : (b : G) * j * (b : G)⁻¹ * j⁻¹ ∈ G0 :=
          G0.mul_mem (G0.mul_mem (G0.mul_mem hbG0 hjG0) (G0.inv_mem hbG0))
            (G0.inv_mem hjG0)
        let zG0 : ↥G0 := ⟨(b : G) * j * (b : G)⁻¹ * j⁻¹, hzG0⟩
        have hzker : π zG0 = 1 := by
          let jG0 : ↥G0 := ⟨j, hjG0⟩
          have hmemπj : π jG0 ∈ Lbar :=
            Subgroup.mem_map_of_mem π (show jG0 ∈ L.subgroupOf G0 from hj)
          have hcomm := Subgroup.mem_centralizer_iff.mp hyC (π jG0) hmemπj
          have hz_eq : zG0 = b * jG0 * b⁻¹ * jG0⁻¹ := rfl
          rw [hz_eq]
          simp only [map_mul, map_inv]
          rw [← hcomm]
          group
        have hzcenter : zG0 ∈ Subgroup.center ↥G0 := by
          rw [← hkerπ]
          exact MonoidHom.mem_ker.mpr hzker
        have hzC : (b : G) * j * (b : G)⁻¹ * j⁻¹ ∈
            Subgroup.centralizer (G0 : Set G) := by
          have hmem : (b : G) * j * (b : G)⁻¹ * j⁻¹ ∈
              (Subgroup.center ↥G0).map G0.subtype := ⟨zG0, hzcenter, rfl⟩
          rw [CFSG.center_map_subtype_eq_inf_centralizer] at hmem
          exact hmem.2
        refine Subgroup.mem_map.mpr ⟨⟨(b : G) * j * (b : G)⁻¹ * j⁻¹, hzL⟩, ?_, rfl⟩
        rw [Subgroup.mem_center_iff]
        intro y
        apply Subtype.ext
        exact Subgroup.mem_centralizer_iff.mp hzC (y : G) (hLG0 y.2)
      have hbzp : (b : G) ∈ Subgroup.zpowers x := by
        have := Subgroup.mem_inf.mpr ⟨hbBs, hbCL⟩
        rwa [hcfg.bstar_inf_centralizer_L] at this
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hbzp
      rw [Subgroup.mem_zpowers_iff]
      refine ⟨k, ?_⟩
      change (π xG0) ^ k = π b
      rw [← map_zpow]
      exact congrArg π (Subtype.ext hk)
    · intro y hy
      rw [Subgroup.mem_zpowers_iff] at hy
      obtain ⟨k, rfl⟩ := hy
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · change (π xG0) ^ k ∈ (Bs.subgroupOf G0).map π
        rw [← map_zpow]
        exact Subgroup.mem_map_of_mem π
          (Subgroup.zpow_mem _ (Subgroup.mem_subgroupOf.mpr hxBs) k)
      · exact Subgroup.zpow_mem _ hxbarCL k
  have hDleCJ : D ≤ Subgroup.centralizer (J : Set G) := by
    rw [hDJ.1.2.2.2.2.2.2]
    exact inf_le_right
  have hBsJ : Bs ≤ Subgroup.normalizer (J : Set G) :=
    GGDichotomy.le_normalizer_stdSub (fun a ha b hb => hBsElem.comm ha hb) hcfg.2.1.1
      hDJ.1 hBsL
  have hCJ : E ⊓ Subgroup.centralizer (Jbar : Set R) = Dbar := by
    apply le_antisymm
    · intro y hy
      rw [Subgroup.mem_inf] at hy
      obtain ⟨hyE, hyC⟩ := hy
      obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hyE
      have hbBs : (b : G) ∈ Bs := hb
      have hbCJ : ∀ j ∈ J, (b : G) * j = j * (b : G) := by
        have hbC : (b : G) ∈ Subgroup.centralizer (J : Set G) := by
          refine CFSG.mem_centralizer_of_commutator_mem_center (J := J)
            ⟨hJcomp.2.2.1⟩ (hBsJ hbBs) ?_
          intro j hj
          have hbG0 : (b : G) ∈ G0 := hBG hbBs
          have hjG0 : j ∈ G0 := hJleG0 hj
          have hconj_mem : (b : G) * j * (b : G)⁻¹ ∈ J :=
            (Subgroup.mem_normalizer_iff.mp (hBsJ hbBs) j).mp hj
          have hzJ : (b : G) * j * (b : G)⁻¹ * j⁻¹ ∈ J :=
            J.mul_mem hconj_mem (J.inv_mem hj)
          have hzG0 : (b : G) * j * (b : G)⁻¹ * j⁻¹ ∈ G0 :=
            G0.mul_mem (G0.mul_mem (G0.mul_mem hbG0 hjG0) (G0.inv_mem hbG0))
              (G0.inv_mem hjG0)
          let zG0 : ↥G0 := ⟨(b : G) * j * (b : G)⁻¹ * j⁻¹, hzG0⟩
          have hzker : π zG0 = 1 := by
            let jG0 : ↥G0 := ⟨j, hjG0⟩
            have hmemπj : π jG0 ∈ Jbar :=
              Subgroup.mem_map_of_mem π (show jG0 ∈ J.subgroupOf G0 from hj)
            have hcomm := Subgroup.mem_centralizer_iff.mp hyC (π jG0) hmemπj
            have hz_eq : zG0 = b * jG0 * b⁻¹ * jG0⁻¹ := rfl
            rw [hz_eq]
            simp only [map_mul, map_inv]
            rw [← hcomm]
            group
          have hzcenter : zG0 ∈ Subgroup.center ↥G0 := by
            rw [← hkerπ]
            exact MonoidHom.mem_ker.mpr hzker
          have hzC : (b : G) * j * (b : G)⁻¹ * j⁻¹ ∈
              Subgroup.centralizer (G0 : Set G) := by
            have hmem : (b : G) * j * (b : G)⁻¹ * j⁻¹ ∈
                (Subgroup.center ↥G0).map G0.subtype := ⟨zG0, hzcenter, rfl⟩
            rw [CFSG.center_map_subtype_eq_inf_centralizer] at hmem
            exact hmem.2
          refine Subgroup.mem_map.mpr ⟨⟨(b : G) * j * (b : G)⁻¹ * j⁻¹, hzJ⟩, ?_, rfl⟩
          rw [Subgroup.mem_center_iff]
          intro y
          apply Subtype.ext
          exact Subgroup.mem_centralizer_iff.mp hzC (y : G) (hJleG0 y.2)
        intro j hj
        exact (Subgroup.mem_centralizer_iff.mp hbC j hj).symm
      have hbD : (b : G) ∈ D := hI b hbBs hbCJ
      exact Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hbD)
    · rintro y ⟨d, hd, rfl⟩
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · exact Subgroup.mem_map_of_mem π
          (Subgroup.mem_subgroupOf.mpr (hDleBs (Subgroup.mem_subgroupOf.mp hd)))
      · rw [Subgroup.mem_centralizer_iff]
        rintro z ⟨j, hj, rfl⟩
        have hdj : (j : G) * (d : G) = (d : G) * (j : G) :=
          Subgroup.mem_centralizer_iff.mp (hDleCJ (Subgroup.mem_subgroupOf.mp hd))
            (j : G) (Subgroup.mem_subgroupOf.mp hj)
        rw [← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext hdj
  change GGQTwoFRCfg E xbar Lbar Dbar Jbar
  exact ⟨hEelem, by rw [hcardE]; exact h4, hSC, hxE, hxnebar, hxLbar, hLcompMap, hEN, hCL,
    hDE, hcardD, hxDbar, hJcompMap, hCJ⟩

end CFSG.StandardType

end
