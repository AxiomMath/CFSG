module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K326Setup
import CFSG.LocalAnalysis.UniquenessCase.UC1K326Wreath
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoPairs
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoNormalizerA
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoFixedEnd
import CFSG.LocalAnalysis.UniquenessCase.UC1K327Core
import CFSG.GroupTheory.SteinbergBSQuotientLifting
import CFSG.GroupTheory.PCore.PrimeSetCore
import CFSG.LocalAnalysis.GLTheoremB.ComponentTools
import CFSG.LocalAnalysis.GLTheoremB.SchreierTools

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open Subgroup

namespace CaseTwoTransitive

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {c : Ctx812E G} (t : CaseTwoTransitive c)

theorem k326_hypotheses {p : ℕ} (hp : p ∈ c.sig)
    (hN : t.PairNormalizerLe p)
    {H : Subgroup G} (hHtop : H ≠ ⊤) (hPH : t.P ≤ H)
    (hcent : ∀ x ∈ t.P, (∀ g ∈ t.P, g * x = x * g) → x ^ 3 = 1 →
      H ≤ Subgroup.centralizer ({x} : Set G))
    {n : ℕ} (hn : 1 ≤ n) (e : ↥t.P ≃* CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326.ZWr n) :
    CFSG.Open.IsKGroup (↥H ⧸ CFSG.pPrimeCore 3 ↥H) ∧
      CFSG.pPrimeCore 3 (↥H ⧸ CFSG.pPrimeCore 3 ↥H) = ⊥ ∧
      CFSG.ABGLocalTools.IsSylowOf 3
        ((t.P.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H))) ⊤ ∧
      Nonempty (↥((t.P.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H))) ≃*
        CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326.ZWr n) ∧
      CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326.OmegaCentral
        ((t.P.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H))) ∧
      ∃ a : ↥H ⧸ CFSG.pPrimeCore 3 ↥H,
        a ∈ CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326.jOf
          ((t.P.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H))) ∧
        a ∉ CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326.z2Of
          ((t.P.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H))) ∧
        Subgroup.normalizer (CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326.jOf
            ((t.P.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H))) : Set _) ⊔
          Subgroup.centralizer ({a} : Set (↥H ⧸ CFSG.pPrimeCore 3 ↥H)) ≤
          ((H ⊓ c.S.M).subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H)) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let O : Subgroup ↥H := CFSG.pPrimeCore 3 ↥H
  let X := ↥H ⧸ O
  let π : ↥H →* X := QuotientGroup.mk' O
  let PX : Subgroup X := (t.P.subgroupOf H).map π
  let MX : Subgroup X := ((H ⊓ c.S.M).subgroupOf H).map π
  have hSP : t.d.S ≤ t.P := by
    rw [t.hdS]
    exact inf_le_left
  have hAAleH : t.d.AA ≤ H := (t.d.AA_le_S.trans hSP).trans hPH
  have hA0P : t.d.A 0 ≤ t.P := (t.d.A_le_S 0).trans hSP
  have hKH : CFSG.Open.IsKGroup ↥H :=
    CFSG.LocalAnalysis.GLTheoremB.isKGroup_of_isKProper c.standing.kProper hHtop
  have hKX : CFSG.Open.IsKGroup X :=
    CFSG.LocalAnalysis.GLTheoremB.isKGroup_quotient' hKH O
  have hcore : CFSG.pPrimeCore 3 X = ⊥ := CFSG.pPrimeCore_quotient_eq_bot Nat.prime_three
  have hOcop : Nat.Coprime 3 (Nat.card O) := CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥H)
  have hOnotdvd : ¬ 3 ∣ Nat.card O :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hOcop
  have hPsylH : CFSG.ABGLocalTools.IsSylowOf 3 t.P H :=
    (t.isSylowOf_top hp hN).of_le hPH le_top
  have hPsylHtop : CFSG.ABGLocalTools.IsSylowOf 3 (t.P.subgroupOf H) ⊤ := by
    refine (CFSG.ABGLocalTools.isSylowOf_map_subtype_iff (K := H)).mp ?_
    simpa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPH,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype] using hPsylH
  have hPXsyl : CFSG.ABGLocalTools.IsSylowOf 3 PX ⊤ := by
    have h := CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC327.isSylowOf_map π hPsylHtop
    simpa [PX, Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective O)] using h
  have hPH3 : IsPGroup 3 (t.P.subgroupOf H) :=
    (t.isSylowOf_top hp hN).isPGroup.comap_subtype
  have hinj : Function.Injective (π.comp (t.P.subgroupOf H).subtype) :=
    CFSG.GroupTheory.SteinbergBS.injective_mk'_comp_subtype (p := 3) (N := O)
      hOnotdvd hPH3
  haveI : Nontrivial ↥(t.d.A 0) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [t.d.card_A 0]; norm_num)
  obtain ⟨a₀, ha₀ne⟩ := exists_ne (1 : ↥(t.d.A 0))
  let a₀G : G := a₀
  have ha₀A0 : a₀G ∈ t.d.A 0 := a₀.2
  have ha₀neG : a₀G ≠ 1 := fun h => ha₀ne (Subtype.ext h)
  have ha₀P : a₀G ∈ t.P := hA0P ha₀A0
  have ha₀AA : a₀G ∈ t.d.AA :=
    (show t.d.A 0 ≤ t.d.AA from le_sup_left.trans le_sup_left) ha₀A0
  have ha₀3 : a₀G ^ 3 = 1 := ((t.d.mem_A_iff 0).mp ha₀A0).2
  let w : ↥t.P := ⟨a₀G, ha₀P⟩
  let f : ↥(t.P.subgroupOf H) →* X := π.comp (t.P.subgroupOf H).subtype
  have hrange : f.range = PX := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  let ψ : ↥(t.P.subgroupOf H) ≃* ↥PX :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  let θ : ↥t.P ≃* ↥(t.P.subgroupOf H) := (Subgroup.subgroupOfEquivOfLe hPH).symm
  let φ : ↥t.P ≃* ↥PX := θ.trans ψ
  have hφ_apply : ∀ x : ↥t.P, (φ x : X) = π ⟨(x : G), hPH x.2⟩ := by
    intro x
    rfl
  let a : X := (φ w : X)
  let ePX : ↥PX ≃* CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326.ZWr n := φ.symm.trans e
  have hOmegacent : CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326.OmegaCentral PX := by
    intro z hzcent hz3
    let wz : ↥t.P := φ.symm z
    have hwzcent : wz ∈ Subgroup.center ↥t.P := by
      have h := Subgroup.mem_map_of_mem (φ.symm.toMonoidHom) hzcent
      have hmap : Subgroup.map (φ.symm.toMonoidHom) (Subgroup.center ↥PX) =
          Subgroup.center ↥t.P := Subgroup.map_center_eq φ.symm
      rwa [hmap] at h
    have hwz3 : wz ^ 3 = 1 := by
      have h := congrArg (φ.symm) hz3
      simpa [wz, map_pow] using h
    have hHcent : H ≤ Subgroup.centralizer ({(wz : G)} : Set G) :=
      hcent (wz : G) wz.2 (fun g hg => by
        have h := Subgroup.mem_center_iff.mp hwzcent ⟨g, hg⟩
        exact congrArg Subtype.val h) (by simpa using congrArg Subtype.val hwz3)
    refine Subgroup.mem_center_iff.mpr fun y => ?_
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective O y
    have hzw : (φ wz : X) = (z : X) :=
      congrArg Subtype.val (MulEquiv.apply_symm_apply φ z)
    rw [← hzw, hφ_apply wz, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    simpa [Subgroup.coe_mul] using
      (Subgroup.mem_centralizer_iff.mp (hHcent h.2) (wz : G) (by simp)).symm
  have hdisj : t.d.A 0 ⊓ (t.d.A 1 ⊔ t.d.A 2) = ⊥ := by
    have hcomm : ∀ x ∈ t.d.A 0, ∀ y ∈ t.d.A 1 ⊔ t.d.A 2, x * y = y * x := by
      intro x hx y hy
      exact t.d.S_commute x y (t.d.A_le_S 0 hx) ((sup_le (t.d.A_le_S 1) (t.d.A_le_S 2)) hy)
    obtain ⟨hcard, -⟩ :=
      CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (t.d.A 0)
        (t.d.A 1 ⊔ t.d.A 2) hcomm
    have hsup : t.d.A 0 ⊔ (t.d.A 1 ⊔ t.d.A 2) = t.d.AA := by
      rw [t.d.AA_def, ← sup_assoc]
    have h12 : Nat.card ↥(t.d.A 1 ⊔ t.d.A 2) = 9 := by
      rw [t.d.card_A_sup_A (by decide)]
      norm_num
    have h0 : Nat.card ↥(t.d.A 0) = 3 := t.d.card_A 0
    rw [hsup, t.d.card_AA, h0, h12] at hcard
    norm_num at hcard
    exact Subgroup.eq_bot_of_card_eq _ hcard
  have hnotZ2 : w ∉ Subgroup.upperCentralSeries ↥t.P 2 := by
    intro hwZ
    have hcommZ : ⁅w, ⟨t.y, t.hyP⟩⁆ ∈ Subgroup.center ↥t.P := by
      have h := (Subgroup.mem_upperCentralSeries_succ_iff (n := 1)).mp hwZ ⟨t.y, t.hyP⟩
      rwa [Subgroup.upperCentralSeries_one] at h
    let a₁ : G := t.y * a₀G * t.y⁻¹
    let a₂ : G := t.y * a₁ * t.y⁻¹
    have ha₁A1 : a₁ ∈ t.d.A 1 := by
      have h : a₁ ∈ (t.d.A 0).map (MulAut.conj t.y).toMonoidHom :=
        Subgroup.mem_map_of_mem _ ha₀A0
      rwa [t.map_conj_A 0, show (0 : Fin 3) + 1 = 1 from by decide] at h
    have ha₂A2 : a₂ ∈ t.d.A 2 := by
      have h : a₂ ∈ (t.d.A 1).map (MulAut.conj t.y).toMonoidHom :=
        Subgroup.mem_map_of_mem _ ha₁A1
      rwa [t.map_conj_A 1, show (1 : Fin 3) + 1 = 2 from by decide] at h
    have hval : ((⁅w, ⟨t.y, t.hyP⟩⁆ : ↥t.P) : G) = a₀G * a₁⁻¹ := by
      simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv, w, a₁]
      group
    have hcentG : ∀ g ∈ t.P, g * (a₀G * a₁⁻¹) = (a₀G * a₁⁻¹) * g := by
      intro g hg
      have h := Subgroup.mem_center_iff.mp hcommZ ⟨g, hg⟩
      calc
        g * (a₀G * a₁⁻¹) = g * ((⁅w, ⟨t.y, t.hyP⟩⁆ : ↥t.P) : G) := by rw [hval]
        _ = ((⟨g, hg⟩ * ⁅w, ⟨t.y, t.hyP⟩⁆ : ↥t.P) : G) := rfl
        _ = ((⁅w, ⟨t.y, t.hyP⟩⁆ * ⟨g, hg⟩ : ↥t.P) : G) := by rw [h]
        _ = ((⁅w, ⟨t.y, t.hyP⟩⁆ : ↥t.P) : G) * g := rfl
        _ = (a₀G * a₁⁻¹) * g := by rw [hval]
    have hconj : t.y * (a₀G * a₁⁻¹) * t.y⁻¹ = a₀G * a₁⁻¹ := by
      rw [hcentG t.y t.hyP, mul_assoc, mul_inv_cancel, mul_one]
    have hconj2 : t.y * (a₀G * a₁⁻¹) * t.y⁻¹ = a₁ * a₂⁻¹ := by
      simp only [a₁, a₂, mul_inv_rev]
      group
    have heq : a₁ * a₂⁻¹ = a₀G * a₁⁻¹ := hconj2 ▸ hconj
    have ha₀eq : a₀G = a₁ * a₂⁻¹ * a₁ := by
      rw [heq]
      group
    have hmem : a₀G ∈ t.d.A 1 ⊔ t.d.A 2 := by
      rw [ha₀eq]
      exact (t.d.A 1 ⊔ t.d.A 2).mul_mem
        ((t.d.A 1 ⊔ t.d.A 2).mul_mem (Subgroup.mem_sup_left ha₁A1)
          (Subgroup.inv_mem _ (Subgroup.mem_sup_right ha₂A2)))
        (Subgroup.mem_sup_left ha₁A1)
    have hbot : a₀G ∈ (t.d.A 0 ⊓ (t.d.A 1 ⊔ t.d.A 2) : Subgroup G) := ⟨ha₀A0, hmem⟩
    rw [hdisj] at hbot
    exact ha₀neG (Subgroup.mem_bot.mp hbot)
  let AAH : Subgroup ↥H := t.d.AA.subgroupOf H
  let AAX : Subgroup X := AAH.map π
  have hAAH_elem : CFSG.Open.IsElemAbelian 3 AAH :=
    t.d.isElemAbelian_AA.subgroupOf H
  have hinjAA : Function.Injective (π.comp AAH.subtype) := by
    intro x y hxy
    have hxP : (x : ↥H) ∈ t.P.subgroupOf H := by
      rw [Subgroup.mem_subgroupOf]
      exact (t.d.AA_le_S.trans hSP) (by
        have := x.2
        rwa [Subgroup.mem_subgroupOf] at this)
    have hyP : (y : ↥H) ∈ t.P.subgroupOf H := by
      rw [Subgroup.mem_subgroupOf]
      exact (t.d.AA_le_S.trans hSP) (by
        have := y.2
        rwa [Subgroup.mem_subgroupOf] at this)
    have h := hinj (show (π.comp (t.P.subgroupOf H).subtype)
        ⟨(x : ↥H), hxP⟩ = (π.comp (t.P.subgroupOf H).subtype)
        ⟨(y : ↥H), hyP⟩ from hxy)
    exact Subtype.ext (congrArg (fun z : ↥(t.P.subgroupOf H) => (z : ↥H)) h)
  have hAAX_elem : CFSG.Open.IsElemAbelian 3 AAX := hAAH_elem.map π
  have hAAX_card : Nat.card AAX = 27 := by
    have hrangeAA : (π.comp AAH.subtype).range = AAX := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← hrangeAA, ← Nat.card_congr (MonoidHom.ofInjective hinjAA).toEquiv, ← t.d.card_AA]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAAleH).toEquiv
  have hAAX_le_PX : AAX ≤ PX := by
    apply Subgroup.map_mono
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact (t.d.AA_le_S.trans hSP) hx
  let AAP : Subgroup ↥PX := AAX.subgroupOf PX
  have hAAP_elem : CFSG.Open.IsElemAbelian 3 AAP := hAAX_elem.subgroupOf PX
  have hAAP_card : Nat.card AAP = 27 := by
    change Nat.card ↥(AAX.subgroupOf PX) = 27
    rw [← hAAX_card]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAAX_le_PX).toEquiv
  obtain ⟨AP, hET, -, -, huniq, -⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326.zwr_unique_E27 hn ePX
  have hAAP_eq : AAP = AP := huniq AAP hAAP_elem hAAP_card
  have hAPmap : AP.map PX.subtype = AAX := by
    rw [← hAAP_eq, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hAAX_le_PX]
  have hjOf_eq : CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326.jOf PX = AAX := by
    change (CFSG.elemThompson ↥PX 3).map PX.subtype = AAX
    rw [hET, hAPmap]
  have ha_mem : a ∈ CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326.jOf PX := by
    rw [hjOf_eq]
    have hmem : (⟨a₀G, hPH ha₀P⟩ : ↥H) ∈ AAH := by
      rw [Subgroup.mem_subgroupOf]
      exact ha₀AA
    have hpi : π ⟨a₀G, hPH ha₀P⟩ ∈ AAX := Subgroup.mem_map_of_mem π hmem
    rwa [← hφ_apply w] at hpi
  have ha_notin : a ∉ CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326.z2Of PX := by
    intro ha
    rw [CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326.z2Of] at ha
    obtain ⟨z, hzZ, hza⟩ := Subgroup.mem_map.mp ha
    have hz_eq : z = φ w := Subtype.ext hza
    have hwZ : φ w ∈ Subgroup.upperCentralSeries ↥PX 2 := hz_eq ▸ hzZ
    have hwZP : w ∈ Subgroup.upperCentralSeries ↥t.P 2 := by
      have hcomp : w ∈ Subgroup.comap (φ : ↥t.P →* ↥PX)
          (Subgroup.upperCentralSeries ↥PX 2) := Subgroup.mem_comap.mpr hwZ
      rwa [Subgroup.comap_upperCentralSeries φ 2] at hcomp
    exact hnotZ2 hwZP
  have hN_le : Subgroup.normalizer
      (CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326.jOf PX : Set X) ≤ MX := by
    intro x hx
    rw [hjOf_eq] at hx
    have hnorm := CFSG.GroupTheory.normal_coprime_quotient_normalizer (p := 3) O hOnotdvd
      AAH hAAH_elem.isPGroup
    rw [← hnorm] at hx
    obtain ⟨h, hh, hxh⟩ := Subgroup.mem_map.mp hx
    have hAAHmap : AAH.map H.subtype = t.d.AA := by
      change (t.d.AA.subgroupOf H).map H.subtype = t.d.AA
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hAAleH]
    have hG : (h : G) ∈ Subgroup.normalizer (t.d.AA : Set G) := by
      have hhmap : AAH.map (MulAut.conj h).toMonoidHom = AAH :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp hh
      have hcomp : H.subtype.comp (MulAut.conj h).toMonoidHom =
          (MulAut.conj (h : G)).toMonoidHom.comp H.subtype := by
        ext y
        simp [MulAut.conj_apply, mul_assoc]
      have hGmap : t.d.AA.map (MulAut.conj (h : G)).toMonoidHom = t.d.AA := by
        calc
          t.d.AA.map (MulAut.conj (h : G)).toMonoidHom
              = (AAH.map H.subtype).map (MulAut.conj (h : G)).toMonoidHom := by
                  rw [hAAHmap]
          _ = AAH.map ((MulAut.conj (h : G)).toMonoidHom.comp H.subtype) := by
                  rw [Subgroup.map_map]
          _ = AAH.map (H.subtype.comp (MulAut.conj h).toMonoidHom) := by rw [hcomp]
          _ = (AAH.map (MulAut.conj h).toMonoidHom).map H.subtype := by
                  rw [Subgroup.map_map]
          _ = AAH.map H.subtype := by rw [hhmap]
          _ = t.d.AA := hAAHmap
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hGmap
    have hhM : h ∈ (H ⊓ c.S.M).subgroupOf H := by
      rw [Subgroup.mem_subgroupOf]
      exact ⟨h.2, normalizer_AA_le t hp hN hG⟩
    have := Subgroup.mem_map_of_mem π hhM
    rwa [hxh] at this
  have hC_le : Subgroup.centralizer ({a} : Set X) ≤ MX := by
    let x : ↥H := ⟨a₀G, hPH ha₀P⟩
    have hx3 : x ^ 3 = 1 := Subtype.ext (by simpa using ha₀3)
    let Q : Subgroup ↥H := Subgroup.zpowers x
    have hQ3 : IsPGroup 3 Q := (CFSG.Open.isElemAbelian_zpowers (p := 3) hx3).isPGroup
    have hQmap : Q.map π = Subgroup.zpowers a := by
      change (Subgroup.zpowers x).map π = Subgroup.zpowers a
      rw [MonoidHom.map_zpowers]
      congr 1
    have hcz : Subgroup.centralizer ({a} : Set X) =
        Subgroup.centralizer (Subgroup.zpowers a : Set X) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    intro y hy
    rw [hcz] at hy
    rw [← hQmap,
      CFSG.GroupTheory.SteinbergBS.centralizer_map_mk'_eq (p := 3) (N := O)
        hOnotdvd hQ3] at hy
    obtain ⟨h, hh, hhy⟩ := Subgroup.mem_map.mp hy
    have hcentH : (h : G) ∈ Subgroup.centralizer (Subgroup.zpowers a₀G : Set G) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact congrArg Subtype.val
        ((Subgroup.mem_centralizer_iff.mp hh) x (Subgroup.mem_zpowers x))
    have hY : Subgroup.zpowers a₀G ≤ t.d.A 0 ⊔ t.d.A 1 :=
      Subgroup.zpowers_le.mpr (Subgroup.mem_sup_left ha₀A0)
    have hY1 : Subgroup.zpowers a₀G ≠ ⊥ := Subgroup.zpowers_ne_bot.mpr ha₀neG
    have hNle := hN.normalizer_le (i := 0) (j := 1) (by decide) hY hY1
    have hhM : h ∈ (H ⊓ c.S.M).subgroupOf H := by
      rw [Subgroup.mem_subgroupOf]
      exact ⟨h.2, hNle (Subgroup.centralizer_le_normalizer _ hcentH)⟩
    have := Subgroup.mem_map_of_mem π hhM
    rwa [hhy] at this
  have hle : Subgroup.normalizer
      (CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326.jOf PX : Set X) ⊔
      Subgroup.centralizer ({a} : Set X) ≤ MX := sup_le hN_le hC_le
  exact ⟨hKX, hcore, hPXsyl, ⟨ePX⟩, hOmegacent, a, ha_mem, ha_notin, hle⟩

end CaseTwoTransitive

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
