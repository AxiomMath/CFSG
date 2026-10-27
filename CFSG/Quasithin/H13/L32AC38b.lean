module

public import CFSG.Quasithin.Vol2.Ch10SecQ4H4
public import CFSG.Quasithin.EmptyFaithful.S153EB6D
public import CFSG.CharacterTheory.Semidihedral.Principal.FreeSixCharacterDefectFourSupport
public import CFSG.Quasithin.Background.F9Tilde
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.H13.L32ASetting

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Quasithin.Vol2.Ch10.SecF.C10E4

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

theorem isTwoReducedIn_tilde (hF : HypF98 T V L (fsuV1 T V) V H) :
    IsTwoReducedIn (tildeOf (fsuV1 T V) H) (tildeOf (fsuV1 T V) (conjClosure V H)) := by
  have h91 := hF.toHypF91
  have hHN : H ≤ Subgroup.normalizer (fsuV1 T V : Set G) := h91.H_normalizes_V₁
  have hUH : conjClosure V H ≤ H := h91.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 H)
  have hV1 : fsuV1 T V ≤ H ⊓ pCoreOf 2 H :=
    le_inf (h91.V₁_le_pCoreOf.trans (pCoreOf_le 2 H)) h91.V₁_le_pCoreOf
  have hcent := h91.tilde_inf_centralizer_pCoreOf (le_refl H)
  refine ⟨secImg_mono hUH, HypF91.tilde_le_normalizer le_rfl, h91.isElemAbelian_tilde, ?_⟩
  intro D hDH hHD hD2
  set N := Subgroup.normalizer (fsuV1 T V : Set G) with hN
  let D' : Subgroup G := (D.comap (secMk N (fsuV1 T V))).map N.subtype ⊓ H
  have hmem : ∀ x (hx : x ∈ H), x ∈ D' ↔ secMk N (fsuV1 T V) ⟨x, hHN hx⟩ ∈ D := by
    intro x hx
    constructor
    · rintro ⟨⟨y, hy, rfl⟩, -⟩
      exact hy
    · intro h
      exact ⟨⟨⟨x, hHN hx⟩, h, rfl⟩, hx⟩
  have hQ : ∀ x (hx : x ∈ H), secMk N (fsuV1 T V) ⟨x, hHN hx⟩ ∈
      Subgroup.centralizer (tildeOf (fsuV1 T V) (conjClosure V H) :
        Set (SecQuot N (fsuV1 T V))) → x ∈ pCoreOf 2 H := by
    intro x hx hc
    have h1 : secMk N (fsuV1 T V) ⟨x, hHN hx⟩ ∈ tildeOf (fsuV1 T V) (H ⊓ pCoreOf 2 H) := by
      rw [← hcent]
      exact ⟨secMk_mem_secImg hx, hc⟩
    exact ((secMk_mem_secImg_iff hV1).mp h1).2
  have hD'H : D' ≤ H := inf_le_right
  have hHD' : H ≤ Subgroup.normalizer (D' : Set G) := by
    intro h hh
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    have hxH : x ∈ H := hx.2
    have hm : h * x * h⁻¹ ∈ H := H.mul_mem (H.mul_mem hh hxH) (H.inv_mem hh)
    refine (hmem _ hm).mpr ?_
    have h1 := (hmem x hxH).mp hx
    have h2 : secMk N (fsuV1 T V) ⟨h, hHN hh⟩ ∈ tildeOf (fsuV1 T V) H := secMk_mem_secImg hh
    have h3 := (Subgroup.mem_normalizer_iff.mp (hHD h2) _).mp h1
    have e : (⟨h * x * h⁻¹, hHN hm⟩ : ↥N) = ⟨h, hHN hh⟩ * ⟨x, hHN hxH⟩ * ⟨h, hHN hh⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv]
    exact h3
  have hD'p : IsPGroup 2 ↥D' := by
    rintro ⟨x, hx⟩
    have hxH : x ∈ H := hx.2
    obtain ⟨k, hk⟩ := hD2 _ ((hmem x hxH).mp hx)
    have hkH : x ^ 2 ^ k ∈ H := H.pow_mem hxH _
    have e : (secMk N (fsuV1 T V) ⟨x, hHN hxH⟩) ^ 2 ^ k =
        secMk N (fsuV1 T V) ⟨x ^ 2 ^ k, hHN hkH⟩ := by
      rw [← map_pow]
      rfl
    rw [e] at hk
    obtain ⟨m, hm⟩ := (pCoreOf_isPGroup 2 H) ⟨_, hQ _ hkH hk⟩
    refine ⟨k + m, Subtype.ext ?_⟩
    have := congrArg Subtype.val hm
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at this ⊢
    rw [pow_add, pow_mul]
    exact this
  have hD'Q : D' ≤ pCoreOf 2 H := le_pCoreOf_of_le_normalizer 2 hD'H hHD' hD'p
  intro d hd
  obtain ⟨x, hxH, rfl⟩ := mem_secImg.mp (hDH hd)
  have hx' : (x : G) ∈ D' := (hmem x hxH).mpr hd
  have h1 : secMk N (fsuV1 T V) x ∈ tildeOf (fsuV1 T V) (H ⊓ pCoreOf 2 H) :=
    secMk_mem_secImg ⟨hxH, hD'Q hx'⟩
  rw [← hcent] at h1
  exact h1.2

omit [Finite G] in
theorem tilde_transvection {b c : G} (hbN : b ∈ Subgroup.normalizer (fsuV1 T V : Set G))
    (hcN : c ∈ Subgroup.normalizer (fsuV1 T V : Set G))
    (htr : ∀ u ∈ conjClosure V H, b * u * b⁻¹ = u ∨ b * u * b⁻¹ = u * c) :
    ∀ x ∈ tildeOf (fsuV1 T V) (conjClosure V H),
      secMk (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V) ⟨b, hbN⟩ * x *
          (secMk (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V) ⟨b, hbN⟩)⁻¹ = x ∨
        secMk (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V) ⟨b, hbN⟩ * x *
            (secMk (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V) ⟨b, hbN⟩)⁻¹ =
          x * secMk (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V) ⟨c, hcN⟩ := by
  intro x hx
  obtain ⟨u, hu, rfl⟩ := mem_secImg.mp hx
  rw [← map_inv, ← map_mul, ← map_mul, ← map_mul]
  rcases htr u hu with h | h
  · left
    congr 1
    exact Subtype.ext h
  · right
    congr 1
    exact Subtype.ext h

theorem isSQTKCat_H (S : Setting147 G T L V H) : CFSG.SectionRank.IsSQTKCat ↥H := by
  have := S.hyp.fsu.simple
  exact (QuasithinUnique.qtkeCore_of_cat S.hyp.fsu.nonabelian S.hyp.fsu.qtke).1 H S.hz.1.2

theorem hyp61_tilde (hF : HypF98 T V L (fsuV1 T V) V H) (hsq : CFSG.SectionRank.IsSQTKCat ↥H)
    {b c : G} (hbH : b ∈ H) (hbQ : b ∉ pCoreOf 2 H) (hcU : c ∈ conjClosure V H)
    (hcV : c ∉ fsuV1 T V)
    (htr : ∀ u ∈ conjClosure V H, b * u * b⁻¹ = u ∨ b * u * b⁻¹ = u * c)
    (hbN : b ∈ Subgroup.normalizer (fsuV1 T V : Set G))
    (hcN : c ∈ Subgroup.normalizer (fsuV1 T V : Set G))
    (hUe : IsElemAbelian 2 (conjClosure (Subgroup.zpowers
      (secMk (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V) ⟨c, hcN⟩))
        (tildeOf (fsuV1 T V) H))) :
    G64.Hyp61 (autI hUe (tildeOf (fsuV1 T V) H))
      (transvI hUe (secMk_mem_secImg (x := ⟨b, hbN⟩) hbH)) := by
  have h91 := hF.toHypF91
  have hR := isTwoReducedIn_tilde hF
  have htH := secMk_mem_secImg (A := Subgroup.normalizer (fsuV1 T V : Set G)) (B := fsuV1 T V)
    (x := ⟨b, hbN⟩) hbH
  have hv : secMk (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V) ⟨c, hcN⟩ ∈
      tildeOf (fsuV1 T V) (conjClosure V H) := secMk_mem_secImg hcU
  have hv1 : secMk (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V) ⟨c, hcN⟩ ≠ 1 :=
    fun h => hcV (secMk_eq_one_iff.mp h)
  have htr' := tilde_transvection hbN hcN htr
  have htC : secMk (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V) ⟨b, hbN⟩ ∉
      Subgroup.centralizer (tildeOf (fsuV1 T V) (conjClosure V H) :
        Set (SecQuot (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V))) := by
    intro hc
    have hV1 : fsuV1 T V ≤ H ⊓ pCoreOf 2 H :=
      le_inf (h91.V₁_le_pCoreOf.trans (pCoreOf_le 2 H)) h91.V₁_le_pCoreOf
    have h1 : secMk (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V) ⟨b, hbN⟩ ∈
        tildeOf (fsuV1 T V) (H ⊓ pCoreOf 2 H) := by
      rw [← h91.tilde_inf_centralizer_pCoreOf (le_refl H)]
      exact ⟨htH, hc⟩
    exact hbQ ((secMk_mem_secImg_iff hV1).mp h1).2
  have hHN : H ≤ Subgroup.normalizer (fsuV1 T V : Set G) := h91.H_normalizes_V₁
  have hK : tildeOf (fsuV1 T V) H ≤ Subgroup.normalizer
      (conjClosure (Subgroup.zpowers
        (secMk (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V) ⟨c, hcN⟩))
          (tildeOf (fsuV1 T V) H) : Set (SecQuot (Subgroup.normalizer (fsuV1 T V : Set G))
            (fsuV1 T V))) := le_normalizer_conjClosure _ _
  let tl : ↥H →* ↥(tildeOf (fsuV1 T V) H) :=
    ((secMk (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V)).comp
      (Subgroup.inclusion hHN)).codRestrict _ fun h => secMk_mem_secImg h.2
  have htl : Function.Surjective tl := by
    rintro ⟨x, hx⟩
    obtain ⟨y, hyH, hyx⟩ := mem_secImg.mp hx
    exact ⟨⟨y, hyH⟩, Subtype.ext hyx⟩
  let φ : ↥H →* ↥(convHom hUe (tildeOf (fsuV1 T V) H) hK).range :=
    (convHom hUe (tildeOf (fsuV1 T V) H) hK).rangeRestrict.comp tl
  have hφ : Function.Surjective φ :=
    (MonoidHom.rangeRestrict_surjective _).comp htl
  have hHq : G64.IsQuotientOfSQTKCat ↥H :=
    ⟨↥H, inferInstance, inferInstance, ⊥, inferInstance, hsq, ⟨(QuotientGroup.quotientBot).symm⟩⟩
  exact {
    pCore_eq_bot := pCoreOf_autI_conjClosure hUe hR htH hv hv1 htr' htC
    quotient_sqtk := by
      rw [← range_convHom hUe (tildeOf (fsuV1 T V) H) hK]
      exact S153EB6.isQuotientOfSQTKCat_of_surjective (le_refl H) hHq φ hφ
    mem := transvI_mem hUe htH
    ne_one := transvI_ne_one hUe hR htH hv htr' htC
    sq_eq_one := transvI_sq hUe hR.2.1 hv hv1 htr' htH
    card_comm_le := by
      rw [card_commV_transvI hUe hR htH hv hv1 htr' htC]
      norm_num
    span := iSup_map_commV_transvI hUe hR htH hv hv1 htr' htC }

end CFSG.Quasithin.H13.L32A.C
