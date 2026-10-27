module

public import CFSG.Quasithin.EmptyFaithful.S153E52B
public import CFSG.Quasithin.EmptyFaithful.S153E52In

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace S153E

section Four

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem tildeT_le_normalizer_tildeV (cx : Ctx15350 T Mc M V₁ V₂ t) :
    tildeOf (quasithinOmegaOneCenter T) T ≤
      Subgroup.normalizer (tildeOf (quasithinOmegaOneCenter T) (VZ T M) : Set _) := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := mem_secImg.1 hy
  exact secMk_mem_normalizer_secImg (cx.hF.T_normalizes_V hx)

theorem exists_central_Vstar (cx : Ctx15350 T Mc M V₁ V₂ t) (h1 : ¬ VZ T M ≤ pCoreOf 2 Mc) :
    ∃ a ∈ autOn (tildeOf (quasithinOmegaOneCenter T) (VZ T M))
        (tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc)), a ≠ 1 ∧
      ∀ x ∈ autOn (tildeOf (quasithinOmegaOneCenter T) T)
        (tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc)), x * a = a * x := by
  have hT2 : IsPGroup 2 ↥(autOn (tildeOf (quasithinOmegaOneCenter T) T)
      (tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc))) := (isSylowTwoOf_HStar_T cx).2.1
  have hVT : autOn (tildeOf (quasithinOmegaOneCenter T) (VZ T M))
        (tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc)) ≤
      autOn (tildeOf (quasithinOmegaOneCenter T) T)
        (tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc)) :=
    A4.autOn_mono (secImg_mono cx.hF.V_le_T)
  have hV1 : autOn (tildeOf (quasithinOmegaOneCenter T) (VZ T M))
      (tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc)) ≠ ⊥ := by
    intro hbot
    have hcard := HypF91.card_autOn_tilde cx.hF (B := VZ T M) cx.hF.V_le_H
    rw [hbot, Subgroup.card_bot] at hcard
    apply h1
    have := Subgroup.relIndex_eq_one.mp hcard.symm
    exact fun v hv => (this hv).2
  have hn : autOn (tildeOf (quasithinOmegaOneCenter T) T)
        (tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc)) ≤
      Subgroup.normalizer (autOn (tildeOf (quasithinOmegaOneCenter T) (VZ T M))
        (tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc)) : Set _) :=
    autOn_le_normalizer_autOn (HypF91.tilde_le_normalizer (hBH := cx.hF.T_le_H))
      (HypF91.tilde_le_normalizer (hBH := cx.hF.V_le_H)) (tildeT_le_normalizer_tildeV cx)
  obtain ⟨z, hz, hz1, hzc⟩ := exists_ne_one_mem_center_of_normalized hT2 hVT hV1 hn
  exact ⟨z, hz, hz1, hzc⟩

theorem card_tildeU_eq_four (i52 : Input15352) (cx : Ctx15350 T Mc M V₁ V₂ t)
    (h1 : ¬ VZ T M ≤ pCoreOf 2 Mc) (hZS : ZS153 T M V₁ = VZ T M ⊓ UH153 T M V₁ Mc) :
    Nat.card ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc)) = 4 := by
  let _ : CommGroup ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc)) :=
    commGroupOfElemAbelian cx.hF.isElemAbelian_tilde
  obtain ⟨a, haV, ha1, hcent⟩ := exists_central_Vstar cx h1
  have hexp : ∀ v : ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc)), v ^ 2 = 1 :=
    fun v => Subtype.ext (by simpa using cx.hF.isElemAbelian_tilde.2 v v.2)
  have haH : a ∈ HStar153 T M V₁ Mc :=
    A4.autOn_mono (secImg_mono cx.hF.V_le_H) haV
  have ha2 : a ^ 2 = 1 := by
    obtain ⟨s, hsV, rfl⟩ := mem_autOn_iff.1 haV
    obtain ⟨x, hxV, hx⟩ := mem_secImg.1 hsV
    rw [← map_pow]
    have hs2 : s ^ 2 = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, ← hx, ← map_pow]
      have : x ^ 2 = 1 := Subtype.ext (by simpa using cx.c.hyp.elemAbelian.2 x hxV)
      rw [this, map_one]
      rfl
    rw [hs2, map_one]
  have hle : commV (Subgroup.zpowers a) ≤ tildeZS T M V₁ Mc := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨g, hg, w, rfl⟩
    have hgV : g ∈ autOn (tildeOf (quasithinOmegaOneCenter T) (VZ T M))
        (tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc)) :=
      (Subgroup.zpowers_le.2 haV) hg
    exact Vstar_comm_mem cx hZS hgV w
  have hne : commV (Subgroup.zpowers a) ≠ ⊥ := by
    intro hbot
    apply ha1
    ext w
    have hw : a w * w⁻¹ ∈ commV (Subgroup.zpowers a) :=
      Subgroup.subset_closure ⟨a, Subgroup.mem_zpowers a, w, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hw
    have := mul_inv_eq_one.mp hw
    simpa using this
  have hcommV : commV (Subgroup.zpowers a) = tildeZS T M V₁ Mc := by
    have h2 := card_tildeZS cx
    have h3 : 1 < Nat.card ↥(commV (Subgroup.zpowers a)) := (Subgroup.one_lt_card_iff_ne_bot _).2 hne
    have h4 := Subgroup.card_le_of_le hle
    exact Subgroup.eq_of_le_of_card_ge hle (by omega)
  have hcard : Nat.card ↥(commV (Subgroup.zpowers a)) = 2 := by
    rw [hcommV]
    exact card_tildeZS cx
  have hyp : G64.Hyp61 (HStar153 T M V₁ Mc) a :=
    { pCore_eq_bot := pCoreOf_HStar_eq_bot cx
      quotient_sqtk := isQuotientOfSQTKCat_HStar cx
      mem := haH
      ne_one := ha1
      sq_eq_one := ha2
      card_comm_le := by rw [hcard]; norm_num
      span := by rw [hcommV]; exact span_tildeZS cx }
  have hT : ∃ T' : Subgroup (MulAut ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc))),
      IsSylowTwoOf T' (HStar153 T M V₁ Mc) ∧ a ∈ T' ∧ ∀ x ∈ T', x * a = a * x :=
    ⟨_, isSylowTwoOf_HStar_T cx, A4.autOn_mono (secImg_mono cx.hF.V_le_T) haV, hcent⟩
  refine i52 _ hexp (HStar153 T M V₁ Mc) a hyp hcard hT ?_
  intro g hg hg3
  by_contra hfix
  push Not at hfix
  rw [← range_rhoU cx] at hg
  obtain ⟨h, rfl⟩ := MonoidHom.mem_range.1 hg
  have hZSN : ZS153 T M V₁ ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
    (ZS_le_U cx).trans ((U_le_T cx).trans ((T_le_Mc cx).trans (Mc_le_normalizer_Z cx)))
  have hhN : (h : G) ∈ Subgroup.normalizer (ZS153 T M V₁ : Set G) := by
    have hhZ := Mc_le_normalizer_Z cx h.2
    have hconj : ∀ z ∈ ZS153 T M V₁, (h : G) * z * (h : G)⁻¹ ∈ ZS153 T M V₁ := by
      intro z hz
      have hzN := hZSN hz
      have hw : (⟨tmk (quasithinOmegaOneCenter T) ⟨z, hzN⟩, secMk_mem_secImg (x := ⟨z, hzN⟩) (ZS_le_U cx hz)⟩ :
          ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc))) ∈
          commV (Subgroup.zpowers a) := by
        rw [hcommV]
        exact secMk_mem_secImg (x := ⟨z, hzN⟩) hz
      have hval := congrArg Subtype.val (hfix _ hw)
      rw [rhoU_apply_val cx h] at hval
      have hprod : (⟨(h : G) * z * (h : G)⁻¹, Subgroup.mul_mem _ (Subgroup.mul_mem _ hhZ hzN)
          (Subgroup.inv_mem _ hhZ)⟩ : ↥(Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))) =
          ⟨h, hhZ⟩ * ⟨z, hzN⟩ * ⟨h, hhZ⟩⁻¹ := Subtype.ext rfl
      have hval' : tmk (quasithinOmegaOneCenter T) (⟨(h : G) * z * (h : G)⁻¹, Subgroup.mul_mem _ (Subgroup.mul_mem _ hhZ hzN)
          (Subgroup.inv_mem _ hhZ)⟩ : ↥(Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))) =
          tmk (quasithinOmegaOneCenter T) ⟨z, hzN⟩ := by
        rw [hprod, map_mul, map_mul, map_inv]
        exact hval
      have hmem := secMk_eq_secMk_iff.1 hval'
      have hmem' : ((h : G) * z * (h : G)⁻¹)⁻¹ * z ∈ quasithinOmegaOneCenter T := hmem
      have e : (h : G) * z * (h : G)⁻¹ = z * (((h : G) * z * (h : G)⁻¹)⁻¹ * z)⁻¹ := by group
      rw [e]
      exact Subgroup.mul_mem _ hz (Z_le_ZS cx (Subgroup.inv_mem _ hmem'))
    have hle : cjSub (h : G) (ZS153 T M V₁) ≤ ZS153 T M V₁ := by
      intro x hx
      have hz := mem_cjSub.1 hx
      have := hconj _ hz
      simpa [mul_assoc] using this
    rw [B2F.mem_normalizer_iff_cjSub_eq]
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_cjSub])
  have hdvd1 : orderOf (rhoU cx h) ∣ orderOf (h : G) := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_map_dvd (rhoU cx) h
  have hdvd2 : orderOf (h : G) ∣ Nat.card ↥(Subgroup.normalizer (ZS153 T M V₁ : Set G)) := by
    have := orderOf_dvd_natCard (⟨(h : G), hhN⟩ : ↥(Subgroup.normalizer (ZS153 T M V₁ : Set G)))
    rwa [Subgroup.orderOf_mk] at this
  have h3 : ¬ 3 ∣ Nat.card ↥(Subgroup.normalizer (ZS153 T M V₁ : Set G)) := cx.r49.threePrime_N
  exact h3 (hg3 ▸ hdvd1.trans hdvd2)

end Four

end S153E

end CFSG.Quasithin
