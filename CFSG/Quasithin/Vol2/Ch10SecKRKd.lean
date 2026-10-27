module

public import CFSG.Quasithin.H13.LocDblCComp
public import CFSG.Quasithin.Background.F9Comp
public import CFSG.Quasithin.Vol2.Ch10SecKRKb

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.KRK

open CFSG.Open CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {Γ : Type} [Group Γ] [Finite Γ]

namespace K1Hyp

variable {H R J L V₁ : Subgroup Γ} (h : K1Hyp H R J L V₁)
include h

theorem mem_normalizer_J {r : Γ} (hr : r ∈ R) (hrc : r ∈ Subgroup.centralizer (L : Set Γ)) :
    r ∈ Subgroup.normalizer (J : Set Γ) := by
  have hJ' : conjSub r J ∈ cComp H := conjSub_mem_cComp_of_mem h.comp (h.syl.1 hr)
  have hLJ' : L ≤ conjSub r J := fun l hl => by
    refine ⟨l, h.le hl, ?_⟩
    have hc := Subgroup.mem_centralizer_iff.mp hrc l hl
    show r * l * r⁻¹ = l
    rw [← hc, mul_inv_cancel_right]
  have hn : J ≤ Subgroup.normalizer (conjSub r J : Set Γ) :=
    LocDbl.le_normalizer_of_mem_cComp hJ' h.comp
  have hN : ((conjSub r J).subgroupOf J).Normal := ⟨fun n hn' g => by
    rw [Subgroup.mem_subgroupOf] at hn' ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hn g.2) n).mp hn'⟩
  rcases CFSG.LocalCores.quasisimple_normal_subgroups h.quasi hN with ht | hc
  · have hle : J ≤ conjSub r J := fun x hx => by
      have : (⟨x, hx⟩ : ↥J) ∈ (conjSub r J).subgroupOf J := by rw [ht]; trivial
      exact this
    have heq : J = conjSub r J := by
      by_contra hne
      exact hJ'.2.2.2 J (lt_of_le_of_ne hle hne) (ne_bot_of_mem_cComp h.comp)
        (perfect_of_mem_cComp h.comp) (subnormal_of_mem_cComp h.comp)
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq.symm
  · exfalso
    exact h.not_le_center ((Subgroup.comap_mono hLJ').trans hc)

@[expose] noncomputable def alpha {r : Γ} (hr : r ∈ Subgroup.normalizer (J : Set Γ)) :
    MulAut (QJ J) :=
  descendHom (conjHom J ⟨r, hr⟩)

omit [Finite Γ] h in
theorem alpha_mk {r : Γ} (hr : r ∈ Subgroup.normalizer (J : Set Γ)) (x : ↥J) :
    alpha hr (piJ J x) = piJ J (conjHom J ⟨r, hr⟩ x) := rfl

omit [Finite Γ] h in
theorem alpha_fix_B {r : Γ} (hr : r ∈ Subgroup.normalizer (J : Set Γ))
    (hrc : r ∈ Subgroup.centralizer (L : Set Γ)) : ∀ b ∈ imJ J L, alpha hr b = b := by
  rintro _ ⟨l, hl, rfl⟩
  rw [alpha_mk]
  congr 1
  apply Subtype.ext
  rw [coe_conjHom_apply]
  have hc := Subgroup.mem_centralizer_iff.mp hrc (l : Γ) (Subgroup.mem_subgroupOf.mp hl)
  show r * l * r⁻¹ = l
  rw [← hc, mul_inv_cancel_right]

omit [Finite Γ] h in
theorem alpha_T {r : Γ} (hr : r ∈ Subgroup.normalizer (J : Set Γ)) (hrR : r ∈ R) :
    ∀ t ∈ imJ J R, alpha hr t ∈ imJ J R := by
  rintro _ ⟨s, hs, rfl⟩
  rw [alpha_mk]
  refine ⟨conjHom J ⟨r, hr⟩ s, ?_, rfl⟩
  show conjHom J ⟨r, hr⟩ s ∈ R.subgroupOf J
  rw [Subgroup.mem_subgroupOf, coe_conjHom_apply]
  exact R.mul_mem (R.mul_mem hrR (Subgroup.mem_subgroupOf.mp hs)) (R.inv_mem hrR)

theorem alpha_pow {r : Γ} (hr : r ∈ Subgroup.normalizer (J : Set Γ)) (hrR : r ∈ R) :
    ∃ k : ℕ, alpha hr ^ 2 ^ k = 1 := by
  obtain ⟨k, hk⟩ := h.syl.2.1 ⟨r, hrR⟩
  refine ⟨k, ?_⟩
  have hk' : (⟨r, hr⟩ : ↥(Subgroup.normalizer (J : Set Γ))) ^ 2 ^ k = 1 :=
    Subtype.ext (by simpa using congrArg Subtype.val hk)
  rw [alpha, ← map_pow, ← map_pow, hk', map_one, map_one]

omit h in
theorem mem_centralizer_of_alpha_eq_one (h' : K1Hyp H R J L V₁) {r : Γ}
    (hr : r ∈ Subgroup.normalizer (J : Set Γ)) (hα : alpha hr = 1) :
    r ∈ Subgroup.centralizer (J : Set Γ) := by
  have hcen : ∀ x : ↥J, (⟨r * x * r⁻¹ * (x : Γ)⁻¹, J.mul_mem
      ((Subgroup.mem_normalizer_iff.mp hr x).mp x.2) (J.inv_mem x.2)⟩ : ↥J) ∈
      Subgroup.center ↥J := by
    intro x
    have h1 : piJ J (conjHom J ⟨r, hr⟩ x) = piJ J x := by
      rw [← alpha_mk, hα, MulAut.one_apply]
    have h2 : (conjHom J ⟨r, hr⟩ x)⁻¹ * x ∈ Subgroup.center ↥J :=
      h'.pCore_le_center ((QuotientGroup.eq).mp h1)
    have h3 := Subgroup.inv_mem _ h2
    have h4 : ((conjHom J ⟨r, hr⟩ x)⁻¹ * x)⁻¹ = x * ((conjHom J ⟨r, hr⟩ x)⁻¹ * x)⁻¹ * x⁻¹ :=
      (Subgroup.mem_center_iff.mp h3 x).symm ▸ by group
    convert h3 using 1
    rw [h4]
    apply Subtype.ext
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv, coe_conjHom_apply]
    group
  have hperf : ⁅J, J⁆ = J := perfect_of_mem_cComp h'.comp
  have key := commute_of_conj_mul_inv_mem_center hperf hr (fun x hx y hy => by
    have := Subgroup.mem_center_iff.mp (hcen ⟨x, hx⟩) ⟨y, hy⟩
    exact (congrArg Subtype.val this).symm)
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  exact (key x hx).symm

noncomputable def centerEquiv : QJ J ⧸ Subgroup.center (QJ J) ≃* ↥J ⧸ Subgroup.center ↥J :=
  (QuotientGroup.quotientMulEquivOfEq
      (CFSG.LocalCores.quasisimple_central_quotient h.quasi _ h.pCore_le_center).2.2).trans
    (QuotientGroup.quotientQuotientEquivQuotient _ _ h.pCore_le_center)

end K1Hyp

end CFSG.Quasithin.Vol2.Ch10.SecC.KRK
