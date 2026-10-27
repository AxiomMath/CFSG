module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.CaseOne
public import CFSG.LocalAnalysis.UniquenessCase.UC1K326S
import CFSG.LocalAnalysis.UniquenessCase.UC1K326Wreath
import CFSG.LocalAnalysis.UniquenessCase.UC1K327Core
import CFSG.GroupTheory.SteinbergBSQuotientLifting
import CFSG.GroupTheory.PCore.PrimeSetCore
import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
import CFSG.LocalAnalysis.GLTheoremB.ComponentTools

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)
open CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326 (K326P2S ZWr z2Of jOf OmegaCentral)

variable {G : Type} [Group G] [Finite G] {D : Data G}

@[expose] def K326Exceptional (X : Type) [Group X] : Prop :=
  Nat.card (CFSG.pCore 3 X) = 27 ∧ Nat.card (CFSG.GH74.GLS.oPrimeResidual 3 X) = 648 ∧
    CFSG.pCore 3 X ≤ CFSG.GH74.GLS.oPrimeResidual 3 X

private theorem map_pPrimeCore_le_relPPrimeCore (H : Subgroup G) :
    (CFSG.pPrimeCore 3 ↥H).map H.subtype ≤ CFSG.Open.relPPrimeCore 3 H := by
  refine le_sSup ⟨?_, ?_, ?_⟩
  · rintro _ ⟨y, -, rfl⟩
    exact y.2
  · show (Subgroup.comap H.subtype ((CFSG.pPrimeCore 3 ↥H).map H.subtype)).Normal
    rw [Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
    infer_instance
  · rw [Subgroup.card_map_of_injective H.subtype_injective]
    exact CFSG.pPrimeCore_coprime_card

theorem k326_dichotomy_of_E27 (hK : K326P2S) (hKG : CFSG.Open.IsKProper G)
    {M P A H : Subgroup G} (hH : H ≠ ⊤) (hPH : P ≤ H)
    (hPG : CFSG.ABGLocalTools.IsSylowOf 3 P ⊤) {n : ℕ} (hn : 1 ≤ n) (e : ↥P ≃* ZWr n)
    (hAP : A ≤ P) (hAab : CFSG.Open.IsElemAbelian 3 A) (hAcard : Nat.card A = 27)
    (hcent : ∀ x ∈ P, (∀ g ∈ P, g * x = x * g) → x ^ 3 = 1 →
      H ≤ Subgroup.centralizer ({x} : Set G))
    {a : G} (haA : a ∈ A) (haZ : a ∉ z2Of P)
    (hNA : Subgroup.normalizer (A : Set G) ≤ M)
    (hCa : Subgroup.centralizer ({a} : Set G) ≤ M) :
    H ≤ (H ⊓ M) ⊔ CFSG.Open.relPPrimeCore 3 H ∨
      (n = 1 ∧ K326Exceptional (↥H ⧸ CFSG.pPrimeCore 3 ↥H)) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let O : Subgroup ↥H := CFSG.pPrimeCore 3 ↥H
  let X := ↥H ⧸ O
  let π : ↥H →* X := QuotientGroup.mk' O
  let PX : Subgroup X := (P.subgroupOf H).map π
  let MX : Subgroup X := ((H ⊓ M).subgroupOf H).map π
  have haP : a ∈ P := hAP haA
  have ha3 : a ^ 3 = 1 := hAab.2 a haA
  have hKH : CFSG.Open.IsKGroup ↥H :=
    CFSG.LocalAnalysis.GLTheoremB.isKGroup_of_isKProper hKG hH
  have hKX : CFSG.Open.IsKGroup X :=
    CFSG.LocalAnalysis.GLTheoremB.isKGroup_quotient' hKH O
  have hcore : CFSG.pPrimeCore 3 X = ⊥ := CFSG.pPrimeCore_quotient_eq_bot Nat.prime_three
  have hOcop : Nat.Coprime 3 (Nat.card O) := CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥H)
  have hOnotdvd : ¬ 3 ∣ Nat.card O :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hOcop
  have hPsylH : CFSG.ABGLocalTools.IsSylowOf 3 P H := hPG.of_le hPH le_top
  have hPsylHtop : CFSG.ABGLocalTools.IsSylowOf 3 (P.subgroupOf H) ⊤ := by
    refine (CFSG.ABGLocalTools.isSylowOf_map_subtype_iff (K := H)).mp ?_
    simpa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPH,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype] using hPsylH
  have hPXsyl : CFSG.ABGLocalTools.IsSylowOf 3 PX ⊤ := by
    have h := CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC327.isSylowOf_map π hPsylHtop
    simpa [PX, Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective O)] using h
  have hPH3 : IsPGroup 3 (P.subgroupOf H) := hPG.isPGroup.comap_subtype
  have hinj : Function.Injective (π.comp (P.subgroupOf H).subtype) :=
    CFSG.GroupTheory.SteinbergBS.injective_mk'_comp_subtype (p := 3) (N := O)
      hOnotdvd hPH3
  let w : ↥P := ⟨a, haP⟩
  let f : ↥(P.subgroupOf H) →* X := π.comp (P.subgroupOf H).subtype
  have hrange : f.range = PX := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  let ψ : ↥(P.subgroupOf H) ≃* ↥PX :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  let θ : ↥P ≃* ↥(P.subgroupOf H) := (Subgroup.subgroupOfEquivOfLe hPH).symm
  let φ : ↥P ≃* ↥PX := θ.trans ψ
  have hφ_apply : ∀ x : ↥P, (φ x : X) = π ⟨(x : G), hPH x.2⟩ := by
    intro x
    rfl
  let a' : X := (φ w : X)
  let ePX : ↥PX ≃* ZWr n := φ.symm.trans e

  have hOmegacent : OmegaCentral PX := by
    intro z hzcent hz3
    let wz : ↥P := φ.symm z
    have hwzcent : wz ∈ Subgroup.center ↥P := by
      have h := Subgroup.mem_map_of_mem (φ.symm.toMonoidHom) hzcent
      have hmap : Subgroup.map (φ.symm.toMonoidHom) (Subgroup.center ↥PX) =
          Subgroup.center ↥P := Subgroup.map_center_eq φ.symm
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
  let AH : Subgroup ↥H := A.subgroupOf H
  let AX : Subgroup X := AH.map π
  have hAleH : A ≤ H := hAP.trans hPH
  have hAH_elem : CFSG.Open.IsElemAbelian 3 AH := hAab.subgroupOf H
  have hinjA : Function.Injective (π.comp AH.subtype) := by
    intro x y hxy
    have hxP : (x : ↥H) ∈ P.subgroupOf H := by
      rw [Subgroup.mem_subgroupOf]
      exact hAP (by
        have := x.2
        rwa [Subgroup.mem_subgroupOf] at this)
    have hyP : (y : ↥H) ∈ P.subgroupOf H := by
      rw [Subgroup.mem_subgroupOf]
      exact hAP (by
        have := y.2
        rwa [Subgroup.mem_subgroupOf] at this)
    have h := hinj (show (π.comp (P.subgroupOf H).subtype)
        ⟨(x : ↥H), hxP⟩ = (π.comp (P.subgroupOf H).subtype)
        ⟨(y : ↥H), hyP⟩ from hxy)
    exact Subtype.ext (congrArg (fun z : ↥(P.subgroupOf H) => (z : ↥H)) h)
  have hAX_elem : CFSG.Open.IsElemAbelian 3 AX := hAH_elem.map π
  have hAX_card : Nat.card AX = 27 := by
    have hrangeA : (π.comp AH.subtype).range = AX := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← hrangeA, ← Nat.card_congr (MonoidHom.ofInjective hinjA).toEquiv, ← hAcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAleH).toEquiv
  have hAX_le_PX : AX ≤ PX := by
    apply Subgroup.map_mono
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hAP hx
  let AQ : Subgroup ↥PX := AX.subgroupOf PX
  have hAQ_elem : CFSG.Open.IsElemAbelian 3 AQ := hAX_elem.subgroupOf PX
  have hAQ_card : Nat.card AQ = 27 := by
    change Nat.card ↥(AX.subgroupOf PX) = 27
    rw [← hAX_card]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAX_le_PX).toEquiv
  obtain ⟨AP, hET, -, -, huniq, -⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326.zwr_unique_E27 hn ePX
  have hAQ_eq : AQ = AP := huniq AQ hAQ_elem hAQ_card
  have hAPmap : AP.map PX.subtype = AX := by
    rw [← hAQ_eq, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hAX_le_PX]
  have hjOf_eq : jOf PX = AX := by
    change (CFSG.elemThompson ↥PX 3).map PX.subtype = AX
    rw [hET, hAPmap]
  have ha_mem : a' ∈ jOf PX := by
    rw [hjOf_eq]
    have hmem : (⟨a, hPH haP⟩ : ↥H) ∈ AH := by
      rw [Subgroup.mem_subgroupOf]
      exact haA
    have hpi : π ⟨a, hPH haP⟩ ∈ AX := Subgroup.mem_map_of_mem π hmem
    rwa [← hφ_apply w] at hpi
  have ha_notin : a' ∉ z2Of PX := by
    intro ha
    rw [z2Of] at ha
    obtain ⟨z, hzZ, hza⟩ := Subgroup.mem_map.mp ha
    have hz_eq : z = φ w := Subtype.ext hza
    have hwZ : φ w ∈ Subgroup.upperCentralSeries ↥PX 2 := hz_eq ▸ hzZ
    have hwZP : w ∈ Subgroup.upperCentralSeries ↥P 2 := by
      have hcomp : w ∈ Subgroup.comap (φ : ↥P →* ↥PX)
          (Subgroup.upperCentralSeries ↥PX 2) := Subgroup.mem_comap.mpr hwZ
      rwa [Subgroup.comap_upperCentralSeries φ 2] at hcomp
    exact haZ (Subgroup.mem_map_of_mem P.subtype hwZP)
  have hN_le : Subgroup.normalizer (jOf PX : Set X) ≤ MX := by
    intro x hx
    rw [hjOf_eq] at hx
    have hnorm := CFSG.GroupTheory.normal_coprime_quotient_normalizer (p := 3) O hOnotdvd
      AH hAH_elem.isPGroup
    rw [← hnorm] at hx
    obtain ⟨h, hh, hxh⟩ := Subgroup.mem_map.mp hx
    have hAHmap : AH.map H.subtype = A := by
      change (A.subgroupOf H).map H.subtype = A
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hAleH]
    have hG : (h : G) ∈ Subgroup.normalizer (A : Set G) := by
      have hhmap : AH.map (MulAut.conj h).toMonoidHom = AH :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp hh
      have hcomp : H.subtype.comp (MulAut.conj h).toMonoidHom =
          (MulAut.conj (h : G)).toMonoidHom.comp H.subtype := by
        ext y
        simp [MulAut.conj_apply, mul_assoc]
      have hGmap : A.map (MulAut.conj (h : G)).toMonoidHom = A := by
        calc
          A.map (MulAut.conj (h : G)).toMonoidHom
              = (AH.map H.subtype).map (MulAut.conj (h : G)).toMonoidHom := by
                  rw [hAHmap]
          _ = AH.map ((MulAut.conj (h : G)).toMonoidHom.comp H.subtype) := by
                  rw [Subgroup.map_map]
          _ = AH.map (H.subtype.comp (MulAut.conj h).toMonoidHom) := by rw [hcomp]
          _ = (AH.map (MulAut.conj h).toMonoidHom).map H.subtype := by
                  rw [Subgroup.map_map]
          _ = AH.map H.subtype := by rw [hhmap]
          _ = A := hAHmap
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hGmap
    have hhM : h ∈ (H ⊓ M).subgroupOf H := by
      rw [Subgroup.mem_subgroupOf]
      exact ⟨h.2, hNA hG⟩
    have := Subgroup.mem_map_of_mem π hhM
    rwa [hxh] at this
  have hC_le : Subgroup.centralizer ({a'} : Set X) ≤ MX := by
    let x : ↥H := ⟨a, hPH haP⟩
    have hx3 : x ^ 3 = 1 := Subtype.ext (by simpa using ha3)
    let Q : Subgroup ↥H := Subgroup.zpowers x
    have hQ3 : IsPGroup 3 Q := (CFSG.Open.isElemAbelian_zpowers (p := 3) hx3).isPGroup
    have hQmap : Q.map π = Subgroup.zpowers a' := by
      change (Subgroup.zpowers x).map π = Subgroup.zpowers a'
      rw [MonoidHom.map_zpowers]
      congr 1
    have hcz : Subgroup.centralizer ({a'} : Set X) =
        Subgroup.centralizer (Subgroup.zpowers a' : Set X) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    intro y hy
    rw [hcz] at hy
    rw [← hQmap,
      CFSG.GroupTheory.SteinbergBS.centralizer_map_mk'_eq (p := 3) (N := O)
        hOnotdvd hQ3] at hy
    obtain ⟨h, hh, hhy⟩ := Subgroup.mem_map.mp hy
    have hcentH : (h : G) ∈ Subgroup.centralizer ({a} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact congrArg Subtype.val
        ((Subgroup.mem_centralizer_iff.mp hh) x (Subgroup.mem_zpowers x))
    have hhM : h ∈ (H ⊓ M).subgroupOf H := by
      rw [Subgroup.mem_subgroupOf]
      exact ⟨h.2, hCa hcentH⟩
    have := Subgroup.mem_map_of_mem π hhM
    rwa [hhy] at this
  have hle : Subgroup.normalizer (jOf PX : Set X) ⊔ Subgroup.centralizer ({a'} : Set X) ≤ MX :=
    sup_le hN_le hC_le
  rcases hK X hKX hcore n hn PX hPXsyl ⟨ePX⟩ hOmegacent MX a' ha_mem ha_notin hle with
    hMX | ⟨hn1, hc27, hr648, hle'⟩
  · left
    intro x hx
    have hmem : π ⟨x, hx⟩ ∈ MX := by
      rw [hMX]
      exact Subgroup.mem_top _
    obtain ⟨m, hm, hmx⟩ := Subgroup.mem_map.mp hmem
    have hm' : (m : G) ∈ H ⊓ M := Subgroup.mem_subgroupOf.mp hm
    have hker : m⁻¹ * ⟨x, hx⟩ ∈ O := QuotientGroup.eq.mp hmx
    have hxO : ((m⁻¹ * ⟨x, hx⟩ : ↥H) : G) ∈ CFSG.Open.relPPrimeCore 3 H :=
      map_pPrimeCore_le_relPPrimeCore H (Subgroup.mem_map_of_mem H.subtype hker)
    have hxeq : x = (m : G) * ((m⁻¹ * ⟨x, hx⟩ : ↥H) : G) := by simp
    rw [hxeq]
    exact Subgroup.mul_mem_sup hm' hxO
  · exact Or.inr ⟨hn1, hc27, hr648, hle'⟩

private theorem center_eq_bot_of_simple_nonab (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) : Subgroup.center G = ⊥ := by
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    have ha : a ∈ Subgroup.center G := by rw [h]; exact Subgroup.mem_top a
    exact hab (Subgroup.mem_center_iff.mp ha b).symm

namespace Case811Sylow

theorem k326_dichotomy {c : Ctx82E3 D} (h : Case811Sylow c)
    (hK : K326P2S) {n : ℕ} (hn : 1 ≤ n) (e : ↥h.P ≃* ZWr n)
    (hPG : CFSG.ABGLocalTools.IsSylowOf 3 h.P ⊤)
    (hNA : Subgroup.normalizer (h.A : Set G) ≤ D.M)
    {a : G} (haA : a ∈ h.A) (haZ : a ∉ z2Of h.P)
    (hCa : Subgroup.centralizer ({a} : Set G) ≤ D.M)
    {H : Subgroup G} (hH : H ≠ ⊤) (hPH : h.P ≤ H)
    (hcent : ∀ x ∈ h.P, (∀ g ∈ h.P, g * x = x * g) → x ^ 3 = 1 →
      H ≤ Subgroup.centralizer ({x} : Set G)) :
    H ≤ (H ⊓ D.M) ⊔ CFSG.Open.relPPrimeCore 3 H ∨
      (n = 1 ∧ K326Exceptional (↥H ⧸ CFSG.pPrimeCore 3 ↥H)) :=
  k326_dichotomy_of_E27 hK c.kProper hH hPH hPG hn e h.A_le h.elemAbelian h.card_A hcent
    haA haZ hNA hCa

theorem k326_dichotomy_omega {c : Ctx82E3 D} (h : Case811Sylow c)
    (hK : K326P2S) {n : ℕ} (hn : 1 ≤ n) (e : ↥h.P ≃* ZWr n)
    (hPG : CFSG.ABGLocalTools.IsSylowOf 3 h.P ⊤)
    (hNA : Subgroup.normalizer (h.A : Set G) ≤ D.M)
    {a : G} (haA : a ∈ h.A) (haZ : a ∉ z2Of h.P)
    (hCa : Subgroup.centralizer ({a} : Set G) ≤ D.M)
    {B : Subgroup G} (hB1 : B ≠ ⊥) (hBc : ∀ x ∈ B, ∀ g ∈ h.P, g * x = x * g)
    (hBΩ : ∀ x ∈ h.P, (∀ g ∈ h.P, g * x = x * g) → x ^ 3 = 1 → x ∈ B) :
    Subgroup.centralizer (B : Set G) ≤
        (Subgroup.centralizer (B : Set G) ⊓ D.M) ⊔
          CFSG.Open.relPPrimeCore 3 (Subgroup.centralizer (B : Set G)) ∨
      (n = 1 ∧ K326Exceptional (↥(Subgroup.centralizer (B : Set G)) ⧸
        CFSG.pPrimeCore 3 ↥(Subgroup.centralizer (B : Set G)))) := by
  refine h.k326_dichotomy hK hn e hPG hNA haA haZ hCa ?_ ?_ ?_
  · intro htop
    apply hB1
    rw [eq_bot_iff]
    intro b hb
    have hz : b ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hg : g ∈ Subgroup.centralizer (B : Set G) := by rw [htop]; exact Subgroup.mem_top g
      exact (Subgroup.mem_centralizer_iff.mp hg b hb).symm
    rw [center_eq_bot_of_simple_nonab D.standing.simple D.standing.nonab] at hz
    exact hz
  · intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (hBc x hx g hg).symm
  · intro x hx hxc hx3
    refine Subgroup.centralizer_le (fun y hy => ?_)
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact hBΩ x hx hxc hx3

end Case811Sylow

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
