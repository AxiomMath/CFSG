module

public import CFSG.GroupTheory.ExtraspecialThreeFive
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalRank2
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.CaseOneAbar
public import CFSG.Quasithin.Vol2.GoldschmidtF134J4Local
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPN
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WS6
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.CComponents
import CFSG.HardMathSupport.Solomon.Coordinator.ONCSylow

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
section
open CFSG.Open
open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data IsSpor)
open CFSG.LocalAnalysis.UniquenessCase.UCK (ThreeCover)
open scoped commutatorElement
variable {G : Type} [Group G] [Finite G] {D : Data G}

theorem two_le_pRank_seven_L'
    (c : Ctx82E3 D)
    (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar) :
    2 ≤ CFSG.Open.pRank 7 c.L := by
  classical
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨-, hcenter, ⟨e⟩⟩ := hON
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv
  have hbar : 2 ≤ CFSG.Open.pRank 7 (⊤ : Subgroup c.Lbar) := by
    have hquot : CFSG.Open.pRank 7
        (⊤ : Subgroup (c.Lbar ⧸ Subgroup.center c.Lbar)) =
        CFSG.Open.pRank 7 (⊤ : Subgroup c.Lbar) :=
      CFSG.SectionRank.pRank_quotient_eq (p := 7) (Subgroup.center c.Lbar)
        (by rw [hcenter]; norm_num)
    rw [← hquot]
    exact CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal.rank2_ONan_7
      (A := c.Lbar ⧸ Subgroup.center c.Lbar) (L := ⊤)
      ⟨(Subgroup.topEquiv (G := c.Lbar ⧸ Subgroup.center c.Lbar)).trans (e.trans b)⟩
  rw [← Ctx82E3.pRank_lbar c (p := 7) (by norm_num)]
  exact hbar

@[expose] noncomputable def Lzero (c : Ctx82E3 D) (P : Subgroup G) : Subgroup G :=
  ⨆ (U : Subgroup G) (_ : U ≤ P ⊓ c.L) (_ : ¬ IsCyclic U),
    Subgroup.normalizer (U : Set G) ⊓ c.L

theorem Lzero_le_normalizer_alpha (c : Ctx82E3 D) {P E₀ : Subgroup G}
    (hΓN : ∀ U : Subgroup G, U ≤ P ⊓ c.L → ¬ IsCyclic U →
      Subgroup.normalizer (U : Set G) ≤ Subgroup.normalizer (thetaAlpha 3 E₀ : Set G)) :
    Lzero c P ≤ Subgroup.normalizer (thetaAlpha 3 E₀ : Set G) := by
  refine iSup_le fun U => iSup_le fun hU => iSup_le fun hUc => ?_
  exact inf_le_left.trans (hΓN U hU hUc)

theorem normalizer_le_map_comap_center {H : Type*} [Group H] (Z : Subgroup H) [Z.Normal]
    (hZc : Z ≤ Subgroup.center H) (V : Subgroup (H ⧸ Z)) :
    Subgroup.normalizer (V : Set (H ⧸ Z)) ≤
      (Subgroup.normalizer ((V.comap (QuotientGroup.mk' Z)) : Set H)).map
        (QuotientGroup.mk' Z) := by
  intro x hx
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective Z x
  refine Subgroup.mem_map.mpr ⟨g, ?_, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro u
  constructor
  · intro hu
    rw [Subgroup.mem_comap] at hu ⊢
    exact (Subgroup.mem_normalizer_iff.mp hx (QuotientGroup.mk' Z u)).mp hu
  · intro hu
    rw [Subgroup.mem_comap] at hu ⊢
    exact (Subgroup.mem_normalizer_iff.mp hx (QuotientGroup.mk' Z u)).mpr hu

theorem exists_E27_of_onan
    (c : Ctx82E3 D)
    (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar) (h7 : D.sig = {7})
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hNZ : Subgroup.normalizer ((zSub P c.L : Subgroup G) : Set G) ≤ D.M) :
    ∃ E : Subgroup G, E ≤ P ⊓ c.L ∧ CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 27 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hON' : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar := hON
  obtain ⟨hq, hcenter, hspor⟩ := hON
  have hspor' : IsSpor (c.Lbar ⧸ Subgroup.center c.Lbar) .ONan := hspor
  obtain ⟨eH⟩ := hspor'
  let N : Subgroup ↥c.L := CFSG.Open.pCore 2 ↥c.L
  let π : ↥c.L →* c.Lbar := QuotientGroup.mk' N
  let A : Subgroup G := P ⊓ c.L
  let AL : Subgroup ↥c.L := A.subgroupOf c.L
  have hPL3 : IsPGroup 3 AL := (hP.isPGroup.to_le inf_le_left).comap_subtype
  have hN3 : ¬ 3 ∣ Nat.card N :=
    CFSG.GroupTheory.not_dvd_card_of_isPGroup (p := 2) (q := 3)
      (CFSG.pCore_isPGroup (p := 2) (G := ↥c.L)) Nat.prime_three (by norm_num)
  have hAsyl : CFSG.ABGLocalTools.IsSylowOf 3 A c.L :=
    hP.inf_of_le_normalizer c.hyp81.1 c.le_normalizer_L
  obtain ⟨Q, hQ⟩ := hAsyl.exists_sylow_eq_subgroupOf
  let S : Sylow 3 c.Lbar := Q.mapSurjective (QuotientGroup.mk'_surjective N)
  let SB : Subgroup c.Lbar := (S : Subgroup c.Lbar)
  have hScoe : SB = AL.map π := by
    rw [show SB = (S : Subgroup c.Lbar) from rfl, Sylow.coe_mapSurjective, hQ]
  have hN3 : ¬ 3 ∣ Nat.card N :=
    CFSG.GroupTheory.not_dvd_card_of_isPGroup (p := 2) (q := 3)
      (CFSG.pCore_isPGroup (p := 2) (G := ↥c.L)) Nat.prime_three (by norm_num)
  have hPL3 : IsPGroup 3 AL := (hP.isPGroup.to_le inf_le_left).comap_subtype
  have hInj : Function.Injective (π.comp AL.subtype) :=
    CFSG.GroupTheory.SteinbergBS.injective_mk'_comp_subtype (p := 3) (N := N) hN3 hPL3
  have hHat : CFSG.HardMathSupport.Solomon.LocalBalance.IsHatON c.Lbar := by
    refine ⟨hq.1, hcenter, ?_⟩
    obtain ⟨b⟩ := CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv
    exact ⟨eH.trans b⟩
  obtain ⟨hcardS, hexpS, hcommS, hcentS⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.inputONSylow_holds (X := c.Lbar) hHat S
  have hZS : Nat.card (Subgroup.center ↥SB) = 3 := by
    have hZ3 : IsPGroup 3 (Subgroup.center c.Lbar) :=
      IsPGroup.of_card (n := 1) (by rw [hcenter]; norm_num)
    have hZLeS : Subgroup.center c.Lbar ≤ SB := hZ3.le_sylow_of_normal S
    have hle : (Subgroup.center ↥SB).map SB.subtype ≤ Subgroup.center c.Lbar := by
      rintro z ⟨x, hx, rfl⟩
      exact hcentS x x.2 fun g hg =>
        congrArg Subtype.val (Subgroup.mem_center_iff.mp hx ⟨g, hg⟩)
    have hge : (Subgroup.center c.Lbar).subgroupOf SB ≤ Subgroup.center ↥SB := by
      intro z hz
      rw [Subgroup.mem_center_iff]
      intro w
      apply Subtype.ext
      have hcomm := Subgroup.mem_center_iff.mp (Subgroup.mem_subgroupOf.mp hz) (w : c.Lbar)
      simpa only [Subgroup.coe_mul] using hcomm
    have h1 : Nat.card (Subgroup.center ↥SB) ≤ Nat.card (Subgroup.center c.Lbar) := by
      have h := Subgroup.card_le_of_le hle
      rwa [Subgroup.card_map_of_injective SB.subtype_injective] at h
    have h2 : Nat.card (Subgroup.center c.Lbar) ≤ Nat.card (Subgroup.center ↥SB) := by
      have hcard : Nat.card ((Subgroup.center c.Lbar).subgroupOf SB) =
          Nat.card (Subgroup.center c.Lbar) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZLeS).toEquiv
      rw [← hcard]
      exact Subgroup.card_le_of_le hge
    rw [hcenter] at h1 h2
    omega
  have hcommS' : commutator ↥SB ≤ Subgroup.center ↥SB := by
    change ⁅(⊤ : Subgroup ↥SB), (⊤ : Subgroup ↥SB)⁆ ≤ Subgroup.center ↥SB
    rw [Subgroup.commutator_le]
    intro x _ y _
    rw [Subgroup.mem_center_iff]
    intro z
    apply Subtype.ext
    have hz := Subgroup.mem_center_iff.mp (hcommS x x.2 y y.2) (z : c.Lbar)
    have hcoe : ((⁅x, y⁆ : ↥SB) : c.Lbar) = ⁅(x : c.Lbar), (y : c.Lbar)⁆ :=
      map_commutatorElement SB.subtype x y
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hcoe]
    exact hz
  have hcenter_ne_top : Subgroup.center ↥SB ≠ ⊤ := by
    intro htop
    have h243 : 3 = 243 := by
      rw [← hZS, htop, Subgroup.card_top]
      simpa using hcardS
    norm_num at h243
  have hnotle : ¬ (⊤ : Subgroup ↥SB) ≤ Subgroup.center ↥SB :=
    fun h => hcenter_ne_top (le_antisymm le_top h)
  obtain ⟨a, -, haZ⟩ := SetLike.not_le_iff_exists.mp hnotle
  have hexpS' : ∀ x : ↥SB, x ^ 3 = 1 := by
    intro x
    apply Subtype.ext
    simpa using hexpS x x.2
  obtain ⟨E_S, -, -, hESea, hEScard⟩ :=
    CFSG.GroupTheory.ExtraspecialThreeFive.exists_elemAbelian_27_of_index_le_three
      (R := ↥SB) hcardS hexpS' hZS hcommS' (H := ⊤) (by simp) (by simp) haZ
  let g : ↥AL →* c.Lbar := π.comp AL.subtype
  have hrange : g.range = SB := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, ← hScoe]
  let ψ : ↥AL ≃* ↥SB := (MonoidHom.ofInjective hInj).trans (MulEquiv.subgroupCongr hrange)
  let eAL : ↥A ≃* ↥AL := (Subgroup.subgroupOfEquivOfLe (show A ≤ c.L from inf_le_right)).symm
  let e : ↥A ≃* ↥SB := eAL.trans ψ
  let E_A : Subgroup ↥A := E_S.map e.symm.toMonoidHom
  have hEAea : CFSG.Open.IsElemAbelian 3 E_A :=
    CFSG.SectionRank.isElemAbelian_map hESea e.symm.toMonoidHom
  have hEAcard : Nat.card E_A = 27 := by
    rw [Subgroup.card_map_of_injective e.symm.injective, hEScard]
  refine ⟨E_A.map A.subtype, Subgroup.map_subtype_le E_A, ?_, ?_⟩
  · exact CFSG.SectionRank.isElemAbelian_map hEAea A.subtype
  · rw [Subgroup.card_map_of_injective A.subtype_injective, hEAcard]

theorem L_le_sup_Lzero_pCore
    (hK5 : K5Gen) (c : Ctx82E3 D)
    (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar) (h7 : D.sig = {7})
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hNZ : Subgroup.normalizer ((zSub P c.L : Subgroup G) : Set G) ≤ D.M) :
    c.L ≤ Lzero c P ⊔ (CFSG.Open.pCore 2 ↥c.L).map c.L.subtype := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hON' : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar := hON
  obtain ⟨hq, hcenter, hspor⟩ := hON
  have hspor' : IsSpor (c.Lbar ⧸ Subgroup.center c.Lbar) .ONan := hspor
  obtain ⟨eH⟩ := hspor'
  let N : Subgroup ↥c.L := CFSG.Open.pCore 2 ↥c.L
  let π : ↥c.L →* c.Lbar := QuotientGroup.mk' N
  let A : Subgroup G := P ⊓ c.L
  let AL : Subgroup ↥c.L := A.subgroupOf c.L
  have hPL3 : IsPGroup 3 AL := (hP.isPGroup.to_le inf_le_left).comap_subtype
  have hN3 : ¬ 3 ∣ Nat.card N :=
    CFSG.GroupTheory.not_dvd_card_of_isPGroup (p := 2) (q := 3)
      (CFSG.pCore_isPGroup (p := 2) (G := ↥c.L)) Nat.prime_three (by norm_num)
  have hAsyl : CFSG.ABGLocalTools.IsSylowOf 3 A c.L :=
    hP.inf_of_le_normalizer c.hyp81.1 c.le_normalizer_L
  obtain ⟨Q, hQ⟩ := hAsyl.exists_sylow_eq_subgroupOf
  let S : Sylow 3 c.Lbar := Q.mapSurjective (QuotientGroup.mk'_surjective N)
  let SB : Subgroup c.Lbar := (S : Subgroup c.Lbar)
  have hScoe : SB = AL.map π := by
    rw [show SB = (S : Subgroup c.Lbar) from rfl, Sylow.coe_mapSurjective, hQ]
  have hHat : CFSG.HardMathSupport.Solomon.LocalBalance.IsHatON c.Lbar := by
    refine ⟨hq.1, hcenter, ?_⟩
    obtain ⟨b⟩ := CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv
    exact ⟨eH.trans b⟩
  obtain ⟨hcardS, hexpS, hcommS, hcentS⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.inputONSylow_holds (X := c.Lbar) hHat S
  let Z : Subgroup c.Lbar := Subgroup.center c.Lbar
  have hZcard : Nat.card Z = 3 := hcenter
  have hZ3 : IsPGroup 3 Z := IsPGroup.of_card (n := 1) (by rw [hZcard]; norm_num)
  let πZ : c.Lbar →* c.Lbar ⧸ Z := QuotientGroup.mk' Z
  have hZLeSB : Z ≤ SB := hZ3.le_sylow_of_normal S
  let S' : Sylow 3 (c.Lbar ⧸ Z) := S.mapSurjective (QuotientGroup.mk'_surjective Z)
  let S'B : Subgroup (c.Lbar ⧸ Z) := (S' : Subgroup (c.Lbar ⧸ Z))
  have hS'coe : S'B = SB.map πZ := by
    rw [show S'B = (S' : Subgroup (c.Lbar ⧸ Z)) from rfl, Sylow.coe_mapSurjective]
  have hS'syl : CFSG.ABGLocalTools.IsSylowOf 3 S'B ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    exact ⟨le_top, S'.isPGroup', by simpa using S'.not_dvd_index⟩
  have hgen : (⨆ (V : Subgroup (c.Lbar ⧸ Z)) (_ : V ≤ S'B) (_ : ¬ IsCyclic V),
      Subgroup.normalizer (V : Set (c.Lbar ⧸ Z))) = ⊤ :=
    hK5 (c.Lbar ⧸ Z) hspor S' hS'syl
  let K : Subgroup c.Lbar :=
    ⨆ (V : Subgroup (c.Lbar ⧸ Z)) (_ : V ≤ S'B) (_ : ¬ IsCyclic V),
      Subgroup.normalizer ((V.comap πZ : Subgroup c.Lbar) : Set c.Lbar)
  have hKmap : K.map πZ = ⊤ := by
    apply le_antisymm le_top
    rw [← hgen]
    refine iSup_le fun V => iSup_le fun hV => iSup_le fun hVnc => ?_
    intro x hx
    obtain ⟨g, hg, hgx⟩ := normalizer_le_map_comap_center Z le_rfl V hx
    exact Subgroup.mem_map.mpr ⟨g,
      Subgroup.mem_iSup_of_mem V (Subgroup.mem_iSup_of_mem hV
        (Subgroup.mem_iSup_of_mem hVnc hg)), hgx⟩
  obtain ⟨E, hEA, hEea, hEcard⟩ := exists_E27_of_onan c hON' h7 hP hNZ
  have hEsub : E ≤ c.L := hEA.trans inf_le_right
  let EL : Subgroup ↥c.L := E.subgroupOf c.L
  have hELcard : Nat.card EL = 27 := by
    rw [← hEcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEsub).toEquiv
  have hELleAL : EL ≤ AL := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    exact Subgroup.mem_subgroupOf.mpr (hEA hx)
  have hELdisj : EL ⊓ N = ⊥ := by
    have hPL3' : IsPGroup 3 EL := hPL3.to_le hELleAL
    exact (IsPGroup.disjoint_of_ne 3 2 (by norm_num) EL N hPL3' CFSG.pCore_isPGroup).eq_bot
  have hcardELmap : Nat.card (EL.map π) = 27 := by
    have h := CFSG.Quasithin.F134.J4E9.card_map_mul_card_inf_ker π EL
    rw [show EL ⊓ π.ker = EL ⊓ N from by rw [QuotientGroup.ker_mk'], hELdisj] at h
    rw [hELcard] at h
    simpa using h
  let V0 : Subgroup (c.Lbar ⧸ Z) := (EL.map π).map πZ
  have hV0card : 9 ≤ Nat.card V0 := by
    have h := CFSG.Quasithin.F134.J4E9.card_map_mul_card_inf_ker πZ (EL.map π)
    have hker : (EL.map π) ⊓ πZ.ker ≤ Z := by
      rw [QuotientGroup.ker_mk']
      exact inf_le_right
    have hkcard : Nat.card ↥((EL.map π) ⊓ πZ.ker) ≤ 3 := by
      have h := Subgroup.card_le_of_le hker
      rwa [hZcard] at h
    have hkpos : 1 ≤ Nat.card ↥((EL.map π) ⊓ πZ.ker) := Nat.one_le_iff_ne_zero.mpr Nat.card_pos.ne'
    have hcard : Nat.card V0 * Nat.card ↥((EL.map π) ⊓ πZ.ker) = 27 := by
      rw [← hcardELmap]
      exact h
    have hle : 9 * Nat.card ↥((EL.map π) ⊓ πZ.ker) ≤
        Nat.card V0 * Nat.card ↥((EL.map π) ⊓ πZ.ker) := by
      calc 9 * Nat.card ↥((EL.map π) ⊓ πZ.ker) ≤ 9 * 3 := Nat.mul_le_mul_left 9 hkcard
        _ = 27 := by norm_num
        _ = Nat.card V0 * Nat.card ↥((EL.map π) ⊓ πZ.ker) := hcard.symm
    exact Nat.le_of_mul_le_mul_right hle hkpos
  have hELea : CFSG.Open.IsElemAbelian 3 EL := hEea.comap c.L.subtype_injective
  have hV0ea : CFSG.Open.IsElemAbelian 3 V0 := by
    exact CFSG.SectionRank.isElemAbelian_map
      (CFSG.SectionRank.isElemAbelian_map hELea π) πZ
  have hV0nc : ¬ IsCyclic V0 := by
    intro hcyc
    letI := hcyc
    haveI : Fintype ↥V0 := Fintype.ofFinite _
    have hexp : ∀ x : ↥V0, x ^ 3 = 1 := by
      intro x
      apply Subtype.ext
      simpa using hV0ea.2 x x.2
    have hle := IsCyclic.card_pow_eq_one_le (α := ↥V0) (n := 3) (by norm_num)
    have hall : Finset.univ.filter (fun x : ↥V0 => x ^ 3 = 1) = Finset.univ := by
      ext x
      simp [hexp x]
    rw [hall, Finset.card_univ] at hle
    have h9 : 9 ≤ Fintype.card ↥V0 := by
      simpa [Nat.card_eq_fintype_card] using hV0card
    omega
  have h1 : EL.map π ≤ SB := by
    rw [hScoe]
    exact Subgroup.map_mono hELleAL
  have hV0le : V0 ≤ S'B := by
    change (EL.map π).map πZ ≤ S'B
    rw [hS'coe]
    exact Subgroup.map_mono h1
  have hS'Bnc : ¬ IsCyclic S'B := fun hcyc =>
    hV0nc (isCyclic_of_injective (Subgroup.inclusion hV0le) (Subgroup.inclusion_injective hV0le))
  have hZK : Z ≤ K := by
    intro z hz
    refine Subgroup.mem_iSup_of_mem S'B (Subgroup.mem_iSup_of_mem le_rfl
      (Subgroup.mem_iSup_of_mem hS'Bnc ?_))
    rw [Subgroup.mem_normalizer_iff]
    intro u
    have hzu : z * u * z⁻¹ = u := by
      have hc := Subgroup.mem_center_iff.mp hz u
      calc z * u * z⁻¹ = u * z * z⁻¹ := by rw [hc]
        _ = u := by group
    rw [hzu]
  have hKtop : K = ⊤ := by
    apply le_antisymm le_top
    intro h hh
    have hhmap : πZ h ∈ K.map πZ := by rw [hKmap]; exact Subgroup.mem_top _
    obtain ⟨k, hkK, hkmk⟩ := Subgroup.mem_map.mp hhmap
    have hdiff : h * k⁻¹ ∈ Z := by
      have h1 : πZ (h * k⁻¹) = 1 := by
        rw [map_mul, map_inv, hkmk, mul_inv_cancel]
      exact (QuotientGroup.eq_one_iff (h * k⁻¹)).mp h1
    have hzK : h * k⁻¹ ∈ K := hZK hdiff
    have : h = (h * k⁻¹) * k := by group
    rw [this]
    exact K.mul_mem hzK hkK
  have hKle : K ≤ ((Lzero c P).subgroupOf c.L).map π := by
    refine iSup_le fun V => iSup_le fun hV => iSup_le fun hVnc => ?_
    intro x hx
    let UH : Subgroup c.Lbar := V.comap πZ
    have hZUH : Z ≤ UH := by
      intro z hz
      rw [Subgroup.mem_comap]
      have hz1 : QuotientGroup.mk z = 1 := (QuotientGroup.eq_one_iff z).mpr hz
      change QuotientGroup.mk z ∈ V
      rw [hz1]
      exact V.one_mem
    have hUHleSB : UH ≤ SB := by
      intro u hu
      rw [Subgroup.mem_comap] at hu
      have hmem : πZ u ∈ SB.map πZ := by
        rw [← hS'coe]
        exact hV hu
      obtain ⟨s, hs, hsu⟩ := Subgroup.mem_map.mp hmem
      have husZ : u * s⁻¹ ∈ Z := by
        have h1 : πZ (u * s⁻¹) = 1 := by
          rw [map_mul, map_inv, hsu, mul_inv_cancel]
        exact (QuotientGroup.eq_one_iff (u * s⁻¹)).mp h1
      have hus : u * s⁻¹ ∈ SB := hZLeSB husZ
      have hEq : u = (u * s⁻¹) * s := by group
      rw [hEq]
      exact SB.mul_mem hus hs
    let UL : Subgroup ↥c.L := (UH.comap π) ⊓ AL
    have hULleAL : UL ≤ AL := inf_le_right
    have hULp : IsPGroup 3 UL := hPL3.to_le hULleAL
    have hULmap : UL.map π = UH := by
      apply le_antisymm
      · exact (Subgroup.map_mono inf_le_left).trans (Subgroup.map_comap_le (f := π) (H := UH))
      · intro u hu
        have huSB : u ∈ SB := hUHleSB hu
        have huAL : u ∈ AL.map π := by
          rwa [hScoe] at huSB
        obtain ⟨a, haAL, ha⟩ := Subgroup.mem_map.mp huAL
        refine Subgroup.mem_map.mpr ⟨a, ?_, ha⟩
        refine Subgroup.mem_inf.mpr ⟨?_, haAL⟩
        rw [Subgroup.mem_comap]
        rw [ha]
        exact hu
    have hfr : Subgroup.normalizer (UH : Set c.Lbar) ≤
        (Subgroup.normalizer (UL : Set ↥c.L)).map π := by
      intro y hy
      have hy' : y ∈ Subgroup.normalizer ((UL.map π : Subgroup c.Lbar) : Set c.Lbar) := by
        rwa [hULmap]
      have hcop : Nat.Coprime 3 (Nat.card N) :=
        (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hN3
      obtain ⟨g, hg, hgx⟩ :=
        CFSG.AGLEmbedding.exists_mem_normalizer_mk_eq_of_mem_normalizer
          (p := 3) Nat.prime_three N hcop hULp hy'
      exact Subgroup.mem_map.mpr ⟨g, hg, hgx⟩
    have hULnc : ¬ IsCyclic UL := by
      intro hcyc
      let ψ : ↥UL →* (c.Lbar ⧸ Z) := πZ.comp (π.comp UL.subtype)
      have hψrange : ψ.range = V := by
        rw [MonoidHom.range_comp, MonoidHom.range_comp, Subgroup.range_subtype,
          hULmap]
        change (UH.map πZ) = V
        exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective Z) V
      let ψ' : ↥UL →* ↥V := ψ.codRestrict V (fun y => by
        rw [← hψrange]
        exact ⟨y, rfl⟩)
      have hψ'surj : Function.Surjective ψ' := by
        intro v
        have hv : (v : c.Lbar ⧸ Z) ∈ ψ.range := by rw [hψrange]; exact v.2
        obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp hv
        exact ⟨y, Subtype.ext hy⟩
      exact hVnc (isCyclic_of_surjective ψ' hψ'surj)
    have hNLle : Subgroup.normalizer (UL : Set ↥c.L) ≤ (Lzero c P).subgroupOf c.L := by
      intro g hg
      rw [Subgroup.mem_subgroupOf]
      let UG : Subgroup G := UL.map c.L.subtype
      have hUGle : UG ≤ P ⊓ c.L := by
        intro u hu
        obtain ⟨uL, huL, rfl⟩ := Subgroup.mem_map.mp hu
        exact Subgroup.mem_subgroupOf.mp (hULleAL huL)
      have hUGnc : ¬ IsCyclic UG := by
        intro hcyc
        let eUG : ↥UL ≃* ↥UG :=
          Subgroup.equivMapOfInjective UL c.L.subtype c.L.subtype_injective
        exact hULnc (isCyclic_of_injective eUG.toMonoidHom eUG.injective)
      have hgnorm : (g : G) ∈ Subgroup.normalizer (UG : Set G) := by
        rw [Subgroup.mem_normalizer_iff]
        intro u
        constructor
        · rintro ⟨uL, huL, rfl⟩
          exact Subgroup.mem_map_of_mem c.L.subtype
            ((Subgroup.mem_normalizer_iff.mp hg uL).mp huL)
        · intro hu
          obtain ⟨vL, hvL, hv⟩ := Subgroup.mem_map.mp hu
          have hu_eq : u = (g : G)⁻¹ * c.L.subtype vL * (g : G) := by rw [hv]; group
          rw [hu_eq]
          let w : ↥c.L := (g : ↥c.L)⁻¹ * vL * (g : ↥c.L)
          have hw : w ∈ UL := by
            have hw' := (Subgroup.mem_normalizer_iff.mp
              ((Subgroup.normalizer (UL : Set ↥c.L)).inv_mem hg) vL).mp hvL
            simpa [w, inv_inv] using hw'
          exact Subgroup.mem_map.mpr ⟨w, hw, rfl⟩
      exact Subgroup.mem_iSup_of_mem UG (Subgroup.mem_iSup_of_mem hUGle
        (Subgroup.mem_iSup_of_mem hUGnc ⟨hgnorm, g.2⟩))
    obtain ⟨y, hyNL, hyx⟩ := hfr hx
    exact Subgroup.mem_map.mpr ⟨y, hNLle hyNL, hyx⟩
  have hpiTop : ((Lzero c P).subgroupOf c.L).map π = ⊤ := by
    apply le_antisymm le_top
    rw [← hKtop]
    exact hKle
  intro l hl
  have hmem : π ⟨l, hl⟩ ∈ ((Lzero c P).subgroupOf c.L).map π := by
    rw [hpiTop]
    exact Subgroup.mem_top _
  obtain ⟨x, hxL, hxπ⟩ := Subgroup.mem_map.mp hmem
  have hxG : (x : G) ∈ Lzero c P := Subgroup.mem_subgroupOf.mp hxL
  let k : ↥c.L := ⟨(x : G)⁻¹ * l, c.L.mul_mem (c.L.inv_mem x.2) hl⟩
  have hmemN : k ∈ N := by
    have hk_eq : k = (⟨(x : G)⁻¹, c.L.inv_mem x.2⟩ : ↥c.L) * ⟨l, hl⟩ := by
      apply Subtype.ext
      rfl
    have hinv : (⟨(x : G)⁻¹, c.L.inv_mem x.2⟩ : ↥c.L) = x⁻¹ := by
      apply Subtype.ext
      rfl
    have h1 : π k = 1 := by
      rw [hk_eq, map_mul, hinv, map_inv, hxπ, inv_mul_cancel]
    exact (QuotientGroup.eq_one_iff k).mp h1
  have hLzero_le : Lzero c P ≤ c.L := by
    refine iSup_le fun U => iSup_le fun _ => iSup_le fun _ => inf_le_right
  have hxk : x * k = (⟨l, hl⟩ : ↥c.L) := by
    apply Subtype.ext
    show (x : G) * ((x : G)⁻¹ * l) = l
    group
  have hmemL : (⟨l, hl⟩ : ↥c.L) ∈ (Lzero c P).subgroupOf c.L ⊔ N :=
    (Subgroup.mem_sup_of_normal_right
      (s := (Lzero c P).subgroupOf c.L) (t := N)).mpr ⟨x, hxL, k, hmemN, hxk⟩
  have hmap := Subgroup.mem_map_of_mem c.L.subtype hmemL
  have hmap_eq : ((Lzero c P).subgroupOf c.L ⊔ N).map c.L.subtype =
      Lzero c P ⊔ (CFSG.Open.pCore 2 ↥c.L).map c.L.subtype := by
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hLzero_le]
  rwa [hmap_eq] at hmap

theorem pCore_le_Lzero
    (c : Ctx82E3 D)
    (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar) (h7 : D.sig = {7})
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hNZ : Subgroup.normalizer ((zSub P c.L : Subgroup G) : Set G) ≤ D.M) :
    (CFSG.Open.pCore 2 ↥c.L).map c.L.subtype ≤ Lzero c P := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let N : Subgroup ↥c.L := CFSG.Open.pCore 2 ↥c.L
  obtain ⟨E, hEA, hEea, hEcard⟩ := exists_E27_of_onan c hON h7 hP hNZ
  have hEsub : E ≤ c.L := hEA.trans inf_le_right
  let EL : Subgroup ↥c.L := E.subgroupOf c.L
  have hELea : CFSG.Open.IsElemAbelian 3 EL := hEea.comap c.L.subtype_injective
  have hELcard : Nat.card EL = 27 := by
    rw [← hEcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEsub).toEquiv
  haveI : IsElementaryAbelian 3 ↥EL :=
    { is_comm := hELea.1.is_comm
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
        Subtype.ext (hELea.2 x x.2) }
  haveI : Nontrivial ↥EL :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hELcard]; norm_num)
  have hN3 : ¬ 3 ∣ Nat.card ↥N :=
    CFSG.GroupTheory.not_dvd_card_of_isPGroup (p := 2) (q := 3)
      (CFSG.pCore_isPGroup (p := 2) (G := ↥c.L)) Nat.prime_three (by norm_num)
  have hgen : (⨆ (B : Subgroup ↥EL) (_ : B.index = 3),
      fixedPointSubgroup B ↥N) = ⊤ :=
    CFSG.SolvableHall.coprime_hyperplane_generation (p := 3) (A := ↥EL) (H := ↥N) hN3
  have htop : (⊤ : Subgroup ↥N).map (c.L.subtype.comp N.subtype) =
      N.map c.L.subtype := by
    rw [Subgroup.map_top, MonoidHom.range_comp, Subgroup.range_subtype]
  have hNsup : N.map c.L.subtype =
      ⨆ (B : Subgroup ↥EL) (_ : B.index = 3),
        (fixedPointSubgroup B ↥N).map (c.L.subtype.comp N.subtype) := by
    calc N.map c.L.subtype = (⊤ : Subgroup ↥N).map (c.L.subtype.comp N.subtype) :=
          htop.symm
      _ = ((⨆ (B : Subgroup ↥EL) (_ : B.index = 3),
            fixedPointSubgroup B ↥N)).map (c.L.subtype.comp N.subtype) := by rw [hgen]
      _ = ⨆ (B : Subgroup ↥EL) (_ : B.index = 3),
            (fixedPointSubgroup B ↥N).map (c.L.subtype.comp N.subtype) := by
          rw [Subgroup.map_iSup]
          simp_rw [Subgroup.map_iSup]
  rw [hNsup]
  refine iSup_le fun B => iSup_le fun hBindex => ?_
  have hBcard : Nat.card B = 9 := by
    have h := B.card_mul_index
    rw [hBindex, hELcard] at h
    omega
  have hBmapcard : Nat.card (B.map EL.subtype) = 9 := by
    rw [Subgroup.card_map_of_injective EL.subtype_injective, hBcard]
  have hBmapea : CFSG.Open.IsElemAbelian 3 (B.map EL.subtype) :=
    hELea.mono (Subgroup.map_subtype_le B)
  have hBnc : ¬ IsCyclic (B.map EL.subtype) := by
    intro hcyc
    letI := hcyc
    haveI : Fintype ↥(B.map EL.subtype) := Fintype.ofFinite _
    have hexp : ∀ x : ↥(B.map EL.subtype), x ^ 3 = 1 := by
      intro x
      apply Subtype.ext
      simpa using hBmapea.2 x x.2
    have hle := IsCyclic.card_pow_eq_one_le (α := ↥(B.map EL.subtype)) (n := 3) (by norm_num)
    have hall : Finset.univ.filter (fun x : ↥(B.map EL.subtype) => x ^ 3 = 1) = Finset.univ := by
      ext x
      simp [hexp x]
    rw [hall, Finset.card_univ] at hle
    have h9 : 9 ≤ Fintype.card ↥(B.map EL.subtype) := by
      rw [← Nat.card_eq_fintype_card]
      exact hBmapcard.ge
    omega
  let BG : Subgroup G := (B.map EL.subtype).map c.L.subtype
  have hBGnc : ¬ IsCyclic BG := by
    intro hcyc
    let eB : ↥(B.map EL.subtype) ≃* ↥BG :=
      Subgroup.equivMapOfInjective (B.map EL.subtype) c.L.subtype c.L.subtype_injective
    exact hBnc (isCyclic_of_injective eB.toMonoidHom eB.injective)
  have hBGle : BG ≤ P ⊓ c.L := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
    have hzE : (z : G) ∈ E := Subgroup.mem_subgroupOf.mp z.2
    exact hEA hzE
  intro q hq
  obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hq
  have hqN : (b : ↥c.L) ∈ N := b.2
  have hcentral : c.L.subtype (N.subtype b) ∈ Subgroup.centralizer (BG : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨y1, hy1, rfl⟩ := Subgroup.mem_map.mp hy
    obtain ⟨y2, hy2, rfl⟩ := Subgroup.mem_map.mp hy1
    have hsmEL : ((y2 : ↥EL) • b : ↥N) = b := by
      simpa using hb ⟨y2, hy2⟩
    have hsm := congrArg (fun x : ↥N => (x : ↥c.L)) hsmEL
    rw [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe (A := EL) (K := N)] at hsm
    have hcommG : (y2 : G) * (b : G) = (b : G) * (y2 : G) := by
      have h := congrArg (fun x : ↥c.L => (x : G)) hsm
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_subtype] at h
      calc (y2 : G) * (b : G) = ((y2 : G) * (b : G) * (y2 : G)⁻¹) * (y2 : G) := by group
        _ = (b : G) * (y2 : G) := by rw [h]
    exact hcommG
  refine Subgroup.mem_iSup_of_mem BG (Subgroup.mem_iSup_of_mem hBGle
    (Subgroup.mem_iSup_of_mem hBGnc ?_))
  exact Subgroup.mem_inf.mpr
    ⟨Subgroup.centralizer_le_normalizer (BG : Set G) hcentral, (N.subtype b).2⟩

theorem L_le_normalizer_alpha'
    (hK5 : K5Gen) (c : Ctx82E3 D)
    (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar) (h7 : D.sig = {7})
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hNZ : Subgroup.normalizer ((zSub P c.L : Subgroup G) : Set G) ≤ D.M)
    {E₀ : Subgroup G} (hE₀P : E₀ ≤ P)
    (hΓN : ∀ U : Subgroup G, U ≤ P ⊓ c.L → ¬ IsCyclic U →
      Subgroup.normalizer (U : Set G) ≤ Subgroup.normalizer (thetaAlpha 3 E₀ : Set G)) :
    c.L ≤ Subgroup.normalizer (thetaAlpha 3 E₀ : Set G) := by
  have hL0 : Lzero c P ≤ Subgroup.normalizer (thetaAlpha 3 E₀ : Set G) :=
    Lzero_le_normalizer_alpha c hΓN
  have hO : (CFSG.Open.pCore 2 ↥c.L).map c.L.subtype ≤ Lzero c P :=
    pCore_le_Lzero c hON h7 hP hNZ
  have hL : c.L ≤ Lzero c P ⊔ (CFSG.Open.pCore 2 ↥c.L).map c.L.subtype :=
    L_le_sup_Lzero_pCore hK5 c hON h7 hP hNZ
  exact hL.trans (sup_le hL0 (hO.trans hL0))

end
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
section
open CFSG.Open
open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data IsSpor)
open CFSG.LocalAnalysis.UniquenessCase.UCK (ThreeCover)
variable {G : Type} [Group G] [Finite G] {D : Data G}

theorem normalizer_alpha_le_M'
    (hK5 : K5Gen) (hKF7 : UC22.KF7Use D)
    (c : Ctx82E3 D)
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar) (h7 : D.sig = {7})
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hNZ : Subgroup.normalizer ((zSub P c.L : Subgroup G) : Set G) ≤ D.M)
    {E₀ : Subgroup G} (hE₀P : E₀ ≤ P) (hαne : thetaAlpha 3 E₀ ≠ ⊥)
    (hαsolv : Group.IsSolvable ↥(thetaAlpha 3 E₀))
    (hα3 : Nat.Coprime 3 (Nat.card ↥(thetaAlpha 3 E₀)))
    (hΓN : ∀ U : Subgroup G, U ≤ P → ¬ IsCyclic U →
      Subgroup.normalizer (U : Set G) ≤ Subgroup.normalizer (thetaAlpha 3 E₀ : Set G)) :
    Subgroup.normalizer (thetaAlpha 3 E₀ : Set G) ≤ D.M := by
  have hHne := normalizer_alpha_ne_top D.standing.simple D.standing.nonab hαne hαsolv
  have hL := L_le_normalizer_alpha' hK5 c hON h7 hP hNZ hE₀P
    (fun U hU => hΓN U (hU.trans inf_le_left))
  have hrankL : 2 ≤ CFSG.Open.pRank 7 c.L := two_le_pRank_seven_L' c hON
  exact normalizer_alpha_le_M_of_L_le hKF7 c h7 hHne hL hrankL

end
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
