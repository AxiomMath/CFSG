module

public import CFSG.Quasithin.Background.C24PfD
public import CFSG.Quasithin.Background.B2FactorizationOffender
public import CFSG.Quasithin.Background.B2FactorizationBaumannAux
public import CFSG.Quasithin.Background.A4V
public import CFSG.Quasithin.Background.B1More13A
public import CFSG.Quasithin.Background.E1Defs
public import CFSG.Quasithin.Background.G2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique
open scoped commutatorElement

namespace C24Pf

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isKGroupCat_autI {H V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hHN : H ≤ Subgroup.normalizer (V : Set G)) (hH : CFSG.SectionRank.IsKGroupCat ↥H) :
    CFSG.SectionRank.IsKGroupCat ↥(autI hV H) := by
  have h1 : CFSG.SectionRank.IsKGroupCat (↥H ⧸ (convHom hV H hHN).ker) :=
    CFSG.SectionRank.IsKGroupCat.quotient hH _
  have h2 : CFSG.SectionRank.IsKGroupCat ↥(convHom hV H hHN).range :=
    CFSG.SectionRank.IsKGroupCat.of_mulEquiv h1
      (QuotientGroup.quotientKerEquivRange (convHom hV H hHN)).symm
  exact CFSG.SectionRank.IsKGroupCat.of_mulEquiv h2
    (MulEquiv.subgroupCongr (range_convHom hV H hHN).symm)

omit [Finite G] in
theorem isComponent_autI {H V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hHN : H ≤ Subgroup.normalizer (V : Set G)) (hL : L ∈ cComp H)
    (hLq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    (hOV : pCoreOf 2 L ≤ Subgroup.centralizer (V : Set G))
    (hLV : ¬ L ≤ Subgroup.centralizer (V : Set G)) :
    CFSG.IsComponent ((autI hV L).subgroupOf (autI hV H)) := by
  have hLH : L ≤ H := le_of_mem_cComp hL
  have hLN : L ≤ Subgroup.normalizer (V : Set G) := hLH.trans hHN
  have hAH : autI hV L ≤ autI hV H := autI_mono hV hLH
  set ψ₀ : ↥L →* ↥(autI hV L) :=
    (MulEquiv.subgroupCongr (range_convHom hV L hLN)).toMonoidHom.comp
      (convHom hV L hLN).rangeRestrict with hψ₀
  have hψ₀s : Function.Surjective ψ₀ :=
    (MulEquiv.subgroupCongr (range_convHom hV L hLN)).surjective.comp
      (convHom hV L hLN).rangeRestrict_surjective
  have hker₀ : ∀ x : ↥L, ψ₀ x = 1 ↔ (x : G) ∈ Subgroup.centralizer (V : Set G) := by
    intro x
    have h1 : ψ₀ x = 1 ↔ convHom hV L hLN x = 1 := by
      rw [hψ₀, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, map_eq_one_iff _
        (MulEquiv.injective _), ← Subtype.coe_inj, MonoidHom.coe_rangeRestrict]
      rfl
    rw [h1, ← MonoidHom.mem_ker, ker_convHom, Subgroup.mem_subgroupOf]
    exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
  have hpk : CFSG.pCore 2 ↥L ≤ ψ₀.ker := by
    intro x hx
    rw [MonoidHom.mem_ker, hker₀]
    exact hOV ⟨x, hx, rfl⟩
  set ψ : (↥L ⧸ CFSG.pCore 2 ↥L) →* ↥(autI hV L) := QuotientGroup.lift _ ψ₀ hpk with hψ
  have hψs : Function.Surjective ψ := by
    intro y
    obtain ⟨x, rfl⟩ := hψ₀s y
    exact ⟨QuotientGroup.mk x, rfl⟩
  have hψk : ψ.ker ≤ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hLq (MonoidHom.normal_ker ψ) with h | h
    · exfalso
      apply hLV
      intro l hl
      have h1 : (QuotientGroup.mk (⟨l, hl⟩ : ↥L) : ↥L ⧸ CFSG.pCore 2 ↥L) ∈ ψ.ker := by
        rw [h]; trivial
      rw [MonoidHom.mem_ker, hψ, QuotientGroup.lift_mk] at h1
      exact (hker₀ ⟨l, hl⟩).mp h1
    · exact h
  have hq : CFSG.IsQuasisimple ↥(autI hV L) :=
    CFSG.LocalCores.isQuasisimple_of_surjective hLq ψ hψs hψk
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hAH).symm hq, ?_⟩
  set χ : ↥H →* ↥(autI hV H) :=
    (MulEquiv.subgroupCongr (range_convHom hV H hHN)).toMonoidHom.comp
      (convHom hV H hHN).rangeRestrict with hχ
  have hχs : Function.Surjective χ :=
    (MulEquiv.subgroupCongr (range_convHom hV H hHN)).surjective.comp
      (convHom hV H hHN).rangeRestrict_surjective
  have hmap : (L.subgroupOf H).map χ = (autI hV L).subgroupOf (autI hV H) := by
    ext φ
    rw [Subgroup.mem_map, Subgroup.mem_subgroupOf, mem_autI]
    constructor
    · rintro ⟨h, hh, rfl⟩
      refine ⟨⟨h, hHN h.2⟩, Subgroup.mem_subgroupOf.mp hh, ?_⟩
      rfl
    · rintro ⟨g, hg, hgφ⟩
      refine ⟨⟨g, hLH hg⟩, Subgroup.mem_subgroupOf.mpr hg, Subtype.ext ?_⟩
      rw [← hgφ]
      rfl
  rw [← hmap]
  exact (B113.subgroupOf_isSubnormal (subnormal_of_mem_cComp hL)).map hχs

omit [Finite G] in
theorem le_centralizer_of_autI_eq {H V L K : Subgroup G} (hV : IsElemAbelian 2 V)
    (hHN : H ≤ Subgroup.normalizer (V : Set G)) (hLH : L ≤ H) (hKH : K ≤ H)
    (hLp : ⁅L, L⁆ = L) (hc : ⁅L, K⁆ ≤ Subgroup.centralizer (V : Set G))
    (he : autI hV L = autI hV K) : L ≤ Subgroup.centralizer (V : Set G) := by
  set C := Subgroup.centralizer (V : Set G) with hC
  have hCn : ∀ h ∈ H, ∀ c ∈ C, h * c * h⁻¹ ∈ C := by
    intro h hh c hc'
    exact (Subgroup.mem_normalizer_iff.mp
      (B2F.normalizer_le_normalizer_centralizer V (hHN hh)) c).mp hc'
  rw [← hLp, Subgroup.commutator_le]
  intro l₁ hl₁ l₂ hl₂
  obtain ⟨k, hk, hlk⟩ := exists_mul_inv_mem_centralizer hV hLH hHN he hl₂
  have e : ⁅l₁, l₂⁆ = ⁅l₁, l₂ * k⁻¹⁆ * ((l₂ * k⁻¹) * ⁅l₁, k⁆ * (l₂ * k⁻¹)⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [e]
  refine C.mul_mem ?_ ?_
  · rw [commutatorElement_def]
    refine C.mul_mem ?_ (C.inv_mem hlk)
    exact hCn l₁ (hLH hl₁) _ hlk
  · exact hCn _ (H.mul_mem (hLH hl₂) (H.inv_mem (hKH hk))) _
      (hc (Subgroup.commutator_mem_commutator hl₁ hk))

theorem thompsonJ_le_normalizer (h82 : Asc82Thm2) {H R L : Subgroup G} (hHs : IsSQTKIn H)
    (hRH : R ≤ H) (hQR : pCoreOf 2 H ≤ R) (hL : L ∈ cComp H)
    (hLq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    (hLV : ¬ L ≤ Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 H) : Set G))
    (hconj : ∀ r ∈ R, r ∉ Subgroup.normalizer (L : Set G) →
      ⁅L, conjByElt r L⁆ ≤ pCoreOf 2 H) :
    thompsonJ R ≤ Subgroup.normalizer (L : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := pCoreOf 2 H with hQ
  set V := omegaOneCenterOf Q with hVdef
  have hV : IsElemAbelian 2 V := B2F.isElemAbelian_omegaOneCenterOf Q
  have hVQ : V ≤ Q := omegaOneCenterOf_le Q
  have hQH : Q ≤ H := pCoreOf_le 2 H
  have hHN : H ≤ Subgroup.normalizer (V : Set G) :=
    (le_normalizer_pCoreOf 2 H).trans (normalizer_le_normalizer_omegaOneCenterOf Q)
  have hRN : R ≤ Subgroup.normalizer (V : Set G) := hRH.trans hHN
  have hVR : V ≤ R := hVQ.trans hQR
  have hLH : L ≤ H := le_of_mem_cComp hL
  have hQC : Q ≤ Subgroup.centralizer (V : Set G) := by
    intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact (Subgroup.mem_centralizer_iff.mp
      ((A4.omegaOneCenterOf_le_centerOf Q hv).2) q hq).symm
  have hOL : pCoreOf 2 L ≤ Subgroup.centralizer (V : Set G) :=
    (A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hL)).trans hQC
  have hcomp := isComponent_autI hV hHN hL hLq hOL hLV
  have hK := isKGroupCat_autI hV hHN hHs.2
  refine iSup₂_le fun A hA => ?_
  intro a ha
  by_contra haN
  have haR : a ∈ R := hA.1 ha
  have haL : convI hV ⟨a, hRN haR⟩ ∈ Subgroup.normalizer ((autI hV L : Subgroup _) : Set _) := by
    by_cases hAC : A ≤ Subgroup.centralizer (V : Set G)
    · have h1 : convI hV ⟨a, hRN haR⟩ = 1 := (convI_eq_one_iff hV _).mpr (hAC ha)
      rw [h1]
      exact Subgroup.one_mem _
    · have hoff : IsFFStarOffender (autI hV R) (autI hV A) :=
        offenderImages_isFFStarOffender hV hVR hRN ⟨A, ⟨hA, hAC⟩, rfl⟩
      have hoff' := isFFStarOffender_mono (autI_mono hV hRH) hoff
      exact h82 (IntMod V hV) (fun v => IntMod.sq_eq_one (hV := hV) v) _ _ _ hK hoff'
        (autI_mono hV hLH) hcomp (convI_mem_autI hV ha (hRN haR))
  have he : autI hV (cjSub a L) = autI hV L := by
    rw [← autI_cjSub hV (hRN haR) L]
    exact (Subgroup.mem_normalizer_iff_map_conj_eq.mp haL)
  have hc := hconj a haR haN
  have hLa : cjSub a L ≤ H := by
    rintro _ ⟨l, hl, rfl⟩
    exact H.mul_mem (H.mul_mem (hRH haR) (hLH hl)) (H.inv_mem (hRH haR))
  exact hLV (le_centralizer_of_autI_eq hV hHN hLH hLa (perfect_of_mem_cComp hL)
    (hc.trans hQC) he.symm)

end C24Pf

end CFSG.Quasithin
