module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A11Coords
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.CaseOneSp6Plane
public import CFSG.LocalAnalysis.UniquenessCase.UC1K326Setup
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A11Mult
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.CaseOneYLemma
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.CaseOnePElementCentral
import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.A6.I1435.AltCase
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811CoordsSigned
import CFSG.LocalAnalysis.SectionRank.AmbientRank
import CFSG.LocalAnalysis.SectionRank.GroupRankTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data IsAlt)
open CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326 (ZWr)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82 (K2)

variable {G : Type} [Group G] [Finite G] {D : Data G}

private theorem factorization_card_a11 :
    (Nat.card (alternatingGroup (Fin 11))).factorization 3 = 4 := by
  obtain ⟨m, hm, hc⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.A6.I1435.card_alt_eq (n := 11)
      (by norm_num) (by norm_num)
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero 3)
  rw [hc, show (81 : ℕ) = 3 ^ 4 by norm_num,
    Nat.factorization_mul (pow_ne_zero 4 (by norm_num)) hm0,
    Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_three,
    Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd hm, add_zero]

namespace Ctx82E3

theorem center_lbar_eq_bot_of_a11 (c : Ctx82E3 D)
    (h811 : CFSG.Yardstones.Mf4cdcdf2e013.QuasisimpleModOTwo c.L)
    (hA : IsAlt (c.Lbar ⧸ Subgroup.center c.Lbar) 11) : Subgroup.center c.Lbar = ⊥ :=
  kMult_A11 c.Lbar (c.isQuasisimple_lbar h811) (Subgroup.center c.Lbar) le_rfl hA
    (c.odd_card_center_lbar)

theorem nonempty_mulEquiv_a11 (c : Ctx82E3 D)
    (h811 : CFSG.Yardstones.Mf4cdcdf2e013.QuasisimpleModOTwo c.L)
    (hA : IsAlt (c.Lbar ⧸ Subgroup.center c.Lbar) 11) :
    Nonempty (c.Lbar ≃* alternatingGroup (Fin 11)) := by
  have hZ : Subgroup.center c.Lbar = ⊥ := center_lbar_eq_bot_of_a11 c h811 hA
  exact ⟨(QuotientGroup.quotientBot (G := c.Lbar)).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq (G := c.Lbar) hZ.symm).trans hA.some)⟩

theorem nonempty_case811Sylow_of_a11 (c : Ctx82E3 D)
    (h811 : CFSG.Yardstones.Mf4cdcdf2e013.QuasisimpleModOTwo c.L) (hK2 : K2)
    (hA : IsAlt (c.Lbar ⧸ Subgroup.center c.Lbar) 11) : Nonempty (Case811Sylow c) := by
  classical
  have hZ : Subgroup.center c.Lbar = ⊥ := center_lbar_eq_bot_of_a11 c h811 hA
  have hZ3 : ¬ 3 ∣ Nat.card (Subgroup.center c.Lbar) := by
    rw [hZ, Subgroup.card_bot]
    norm_num
  have hON : ¬ CFSG.LocalAnalysis.UniquenessCase.UCK.ThreeCover
      (fun Y _ => CFSG.LocalAnalysis.UniquenessCase.UC22.IsSpor Y .ONan) c.Lbar := by
    rintro ⟨-, hZcard, -⟩
    exact hZ3 (by rw [hZcard])
  have h227 : ¬ CFSG.Blueprint.LieModel (c.Lbar ⧸ Subgroup.center c.Lbar) .PSL 2 3 3 := by
    intro hLie
    obtain ⟨e⟩ := hA
    have h81 : 81 ∣ Nat.card (c.Lbar ⧸ Subgroup.center c.Lbar) := by
      rw [Nat.card_congr e.toEquiv]
      obtain ⟨m, -, hc⟩ :=
        CFSG.LocalAnalysis.RankThreeTheoremC.A6.I1435.card_alt_eq (n := 11)
          (by norm_num) (by norm_num)
      rw [hc]
      exact dvd_mul_right 81 m
    have h2 : Nat.card (c.Lbar ⧸ Subgroup.center c.Lbar) = 9828 := by
      rw [CFSG.GH74.card_of_lieModel_PSL (by norm_num) hLie]
      norm_num [CFSG.Open.ordA]
    rw [h2] at h81
    norm_num at h81
  have hPL : ∀ P : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 P D.M → P ≤ c.L :=
    fun P hP => Ctx82E3.le_L_of_K2 c h811 hK2 hZ3 hON h227 hP
  obtain ⟨e⟩ := nonempty_mulEquiv_a11 c h811 hA
  exact exists_case811Sylow c
    (fun P => existsUnique_elemAbelian_card_27_of_mulEquiv_a11 e P)
    (fun A hAab hAcard x hx =>
      exists_conj_mem_of_elemAbelian_card_27_of_mulEquiv_a11 e hAab hAcard hx)
    hPL

end Ctx82E3

namespace Case811Sylow

variable {c : Ctx82E3 D}

theorem SignedLift.exists_c₀_eq_of_isSignedCoords (h : Case811Sylow c)
    {c₀ : Multiplicative (Fin 3 → ZMod 3) →* c.Lbar}
    (hc₀ : Theorem82.IsSignedCoords h.Abar c₀) :
    ∃ s : SignedLift h, s.c₀ = c₀ := by
  obtain ⟨a, ha_range, ha_apply, hXinj, ha_memA⟩ := h.exists_coords_lift hc₀.2.1
  have ha_inj : Function.Injective a := by
    intro u v huv
    apply hc₀.1
    rw [← ha_apply u, ← ha_apply v, huv]
  refine ⟨⟨c₀, a, hc₀, ha_range, ha_apply, hXinj, ha_inj, ha_memA, fun v hv => ?_⟩, rfl⟩
  have h3 : (Multiplicative.ofAdd v : Multiplicative (Fin 3 → ZMod 3)) ^ 3 = 1 := by
    rw [← ofAdd_nsmul]
    have hzero : (3 : ℕ) • v = 0 := by
      funext i
      rw [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul]
      have h30 : (↑(3 : ℕ) : ZMod 3) = 0 := by rfl
      rw [h30, zero_mul]
    rw [hzero, ofAdd_zero]
  have hne : (Multiplicative.ofAdd v : Multiplicative (Fin 3 → ZMod 3)) ≠ 1 :=
    fun hone => hv (ofAdd_eq_one.mp hone)
  rw [Subgroup.orderOf_coe, orderOf_injective a ha_inj, orderOf_eq_prime h3 hne]

theorem exists_signedLift_of_a11 (h : Case811Sylow c) (e : c.Lbar ≃* alternatingGroup (Fin 11)) :
    ∃ (s : SignedLift h) (g : alternatingGroup (Fin 11)),
      ∀ v, e (s.c₀ v) = g * a11Coords v * g⁻¹ := by
  classical
  let E : Subgroup (alternatingGroup (Fin 11)) := h.Abar.map e.toMonoidHom
  have hE : CFSG.Open.IsElemAbelian 3 E := h.isElemAbelian_Abar.map e.toMonoidHom
  have hE27 : Nat.card E = 27 := by
    rw [Subgroup.card_map_of_injective e.injective, h.card_Abar]
  obtain ⟨g, hg⟩ := exists_conj_eq_a11A0 hE hE27
  let c₀ : Multiplicative (Fin 3 → ZMod 3) →* c.Lbar :=
    e.symm.toMonoidHom.comp ((MulAut.conj g).toMonoidHom.comp a11Coords)
  have hcoords : Theorem82.IsSignedCoords h.Abar c₀ := by
    have h1 := (Theorem82.IsSignedCoords.conj isSignedCoords_a11Coords g).map_mulEquiv e.symm
    have hEeq : E.map e.symm.toMonoidHom = h.Abar := by
      calc E.map e.symm.toMonoidHom
          = (h.Abar.map e.toMonoidHom).map e.symm.toMonoidHom := rfl
        _ = h.Abar.map (e.symm.toMonoidHom.comp e.toMonoidHom) := Subgroup.map_map ..
        _ = h.Abar.map (MonoidHom.id c.Lbar) := by
            congr 1
            ext x
            simp
        _ = h.Abar := Subgroup.map_id ..
    rw [← hg] at h1
    rwa [hEeq] at h1
  obtain ⟨s, hs⟩ := SignedLift.exists_c₀_eq_of_isSignedCoords h hcoords
  refine ⟨s, g, fun v => ?_⟩
  rw [hs]
  dsimp [c₀]
  rw [MulEquiv.apply_symm_apply]

theorem exists_five_of_a11 (h : Case811Sylow c) (e : c.Lbar ≃* alternatingGroup (Fin 11))
    (h5 : 5 ∈ D.sig) :
    ∃ y ∈ D.M ⊓ Subgroup.centralizer (h.A : Set G), orderOf y = 5 ∧ y ∉ c.L := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  refine h.exists_mem_centralizer_A_not_mem_L h5 ?_ ?_ ?_
  · exact h.mem_centralizer_of_isPGroup_of_prime (p := 5) Nat.prime_five
      (by norm_num) (by norm_num) (by norm_num)
  · have h1 : CFSG.Open.pRank 5 (⊤ : Subgroup c.Lbar) =
        CFSG.pRank 5 ↥(⊤ : Subgroup c.Lbar) :=
      (CFSG.SectionRank.pRank_coe_eq_openPRank 5 (⊤ : Subgroup c.Lbar)).symm
    have h2 : CFSG.pRank 5 ↥(⊤ : Subgroup c.Lbar) =
        CFSG.pRank 5 ↥(⊤ : Subgroup (alternatingGroup (Fin 11))) :=
      CFSG.pRank_congr_of_mulEquiv
        ((Subgroup.topEquiv (G := c.Lbar)).trans
          (e.trans (Subgroup.topEquiv (G := alternatingGroup (Fin 11))).symm)) 5
    have h3 : CFSG.pRank 5 ↥(⊤ : Subgroup (alternatingGroup (Fin 11))) =
        CFSG.Open.pRank 5 (⊤ : Subgroup (alternatingGroup (Fin 11))) :=
      CFSG.SectionRank.pRank_coe_eq_openPRank 5 _
    rw [← Ctx82E3.pRank_lbar c (p := 5) (by norm_num), h1, h2, h3]
    exact pRank_five_a11_le_two
  · intro h5dvd
    apply not_five_dvd_card_centralizer_of_elemAbelian_a11
      (E := h.Abar.map e.toMonoidHom) (h.isElemAbelian_Abar.map e.toMonoidHom)
    · rw [Subgroup.card_map_of_injective e.injective, h.card_Abar]
    · have hmap := CFSG.Glauberman.map_centralizer_eq_of_equiv e h.Abar
      have hcard : Nat.card (Subgroup.centralizer (h.Abar : Set c.Lbar)) =
          Nat.card (Subgroup.centralizer ((h.Abar.map e.toMonoidHom :
            Subgroup (alternatingGroup (Fin 11))) :
              Set (alternatingGroup (Fin 11)))) := by
        rw [← hmap, Subgroup.card_map_of_injective e.injective]
      rwa [← hcard]

private theorem factorization_card_L_of_a11 {c : Ctx82E3 D}
    (e : c.Lbar ≃* alternatingGroup (Fin 11)) :
    (Nat.card ↥c.L).factorization 3 = 4 := by
  let O : Subgroup ↥c.L := CFSG.Open.pCore 2 ↥c.L
  have hN3 : ¬ 3 ∣ Nat.card O :=
    CFSG.GroupTheory.not_dvd_card_of_isPGroup (p := 2) (q := 3)
      (CFSG.pCore_isPGroup (p := 2) (G := ↥c.L)) Nat.prime_three (by norm_num)
  have hfacLbar : (Nat.card c.Lbar).factorization 3 = 4 := by
    rw [Nat.card_congr e.toEquiv]
    exact factorization_card_a11
  have hcardL : Nat.card ↥c.L = Nat.card c.Lbar * Nat.card O :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup O
  rw [hcardL, Nat.factorization_mul (Nat.card_pos.ne') (Nat.card_pos.ne'),
    Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hN3, add_zero, hfacLbar]

theorem nonempty_zwr_of_a11 (h : Case811Sylow c) (e : c.Lbar ≃* alternatingGroup (Fin 11)) :
    Nonempty (↥h.P ≃* ZWr 1) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let O : Subgroup ↥c.L := CFSG.Open.pCore 2 ↥c.L
  let π : ↥c.L →* c.Lbar := QuotientGroup.mk' O
  have hN3 : ¬ 3 ∣ Nat.card O :=
    CFSG.GroupTheory.not_dvd_card_of_isPGroup (p := 2) (q := 3)
      (CFSG.pCore_isPGroup (p := 2) (G := ↥c.L)) Nat.prime_three (by norm_num)
  have hPLsyl : CFSG.ABGLocalTools.IsSylowOf 3 h.P c.L :=
    h.sylow.of_le h.P_le_L c.hyp81.1
  have hPcard81 : Nat.card h.P = 81 := by
    rw [hPLsyl.card_eq, factorization_card_L_of_a11 e]
    norm_num
  let PX : Subgroup c.Lbar := (h.P.subgroupOf c.L).map π
  have hPL3 : IsPGroup 3 (h.P.subgroupOf c.L) := h.sylow.isPGroup.comap_subtype
  have hinj : Function.Injective (π.comp (h.P.subgroupOf c.L).subtype) :=
    CFSG.GroupTheory.SteinbergBS.injective_mk'_comp_subtype (p := 3) (N := O) hN3 hPL3
  have hrange : (π.comp (h.P.subgroupOf c.L).subtype).range = PX := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  let ψ : ↥(h.P.subgroupOf c.L) ≃* ↥PX :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  have hPXcard : Nat.card PX = 81 := by
    rw [← hPcard81]
    exact (Nat.card_congr ψ.symm.toEquiv).trans
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.P_le_L).toEquiv)
  let PE : Subgroup (alternatingGroup (Fin 11)) := PX.map e.toMonoidHom
  have hPEcard : Nat.card PE = 81 := by
    rw [Subgroup.card_map_of_injective e.injective, hPXcard]
  have hfac11 : (Nat.card (alternatingGroup (Fin 11))).factorization 3 = 4 :=
    factorization_card_a11
  let S : Sylow 3 (alternatingGroup (Fin 11)) :=
    Sylow.ofCard PE (by rw [hPEcard, hfac11]; norm_num)
  have hScoe : (S : Subgroup (alternatingGroup (Fin 11))) = PE := Sylow.coe_ofCard PE _
  obtain ⟨eW⟩ := CFSG.LocalAnalysis.RankThreeTheoremC.A6.I1435.sylow_alt_W3
    (n := 11) (by norm_num) (by norm_num) S
  exact ⟨(Subgroup.subgroupOfEquivOfLe h.P_le_L).symm.trans
    (ψ.trans ((Subgroup.equivMapOfInjective PX e.toMonoidHom e.injective).trans
      ((MulEquiv.subgroupCongr hScoe.symm).trans eW)))⟩

namespace SignedLift

variable {h : Case811Sylow c} (s : SignedLift h)

theorem five_dvd_card_inf_centralizer_pt_of_a11 (e : c.Lbar ≃* alternatingGroup (Fin 11))
    {g : alternatingGroup (Fin 11)} (hs : ∀ v, e (s.c₀ v) = g * a11Coords v * g⁻¹)
    {v : Fin 3 → ZMod 3} (hz : ∃ i, v i = 0) :
    5 ∣ Nat.card (c.L ⊓ Subgroup.centralizer (Subgroup.zpowers (s.pt v) : Set G) :
      Subgroup G) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hB : IsPGroup 3 (Subgroup.zpowers (s.pt v)) :=
    (CFSG.Open.isElemAbelian_zpowers (s.pt_pow_three v)).isPGroup
  have hBL : Subgroup.zpowers (s.pt v) ≤ c.L :=
    Subgroup.zpowers_le.mpr (s.pt_mem_L v)
  rw [Ctx82E3.dvd_card_centralizer_lbar_iff c (q := 3) (by norm_num) (p := 5) (by norm_num)
    hBL hB]
  rw [s.lbar_image_zpowers_pt v, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  let a : alternatingGroup (Fin 11) := a11Coords (Multiplicative.ofAdd v)
  have hs' : e (s.c₀ (Multiplicative.ofAdd v)) = g * a * g⁻¹ := hs _
  have hcard1 : Nat.card (Subgroup.centralizer
      ({s.c₀ (Multiplicative.ofAdd v)} : Set c.Lbar)) =
      Nat.card (Subgroup.centralizer
        ({e (s.c₀ (Multiplicative.ofAdd v))} : Set (alternatingGroup (Fin 11)))) := by
    have h1 := CFSG.Glauberman.map_centralizer_eq_of_equiv e
      (Subgroup.zpowers (s.c₀ (Multiplicative.ofAdd v)))
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure,
      MonoidHom.map_closure, Set.image_singleton, Subgroup.centralizer_closure] at h1
    change Subgroup.map e.toMonoidHom
      (Subgroup.centralizer {s.c₀ (Multiplicative.ofAdd v)}) =
      Subgroup.centralizer {e (s.c₀ (Multiplicative.ofAdd v))} at h1
    rw [← h1, Subgroup.card_map_of_injective e.injective]
  have hcard2 : Nat.card (Subgroup.centralizer
      ({g * a * g⁻¹} : Set (alternatingGroup (Fin 11)))) =
      Nat.card (Subgroup.centralizer ({a} : Set (alternatingGroup (Fin 11)))) := by
    have h1 := CFSG.Glauberman.map_centralizer_eq_of_equiv (MulAut.conj g)
      (Subgroup.zpowers a)
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure,
      MonoidHom.map_closure, Set.image_singleton, Subgroup.centralizer_closure] at h1
    change Subgroup.map (MulAut.conj g).toMonoidHom (Subgroup.centralizer {a}) =
      Subgroup.centralizer {g * a * g⁻¹} at h1
    rw [← h1, Subgroup.card_map_of_injective (MulAut.conj g).injective]
  rw [hcard1, hs', hcard2]
  exact five_dvd_card_centralizer_a11Coords hz

end SignedLift

end Case811Sylow

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
