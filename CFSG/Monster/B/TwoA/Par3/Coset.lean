
module

public import CFSG.Monster.B.TwoA.Par3.CosetBase

public import CFSG.Monster.B.TwoA.Base.RankThreePar

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Par3

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.Lifts CFSG.Monster.VisQuot
  CFSG.Monster.ScalarKernel CFSG.Monster.B.Co2 CFSG.Monster.B.TwoA.Sp8 CFSG.Monster.B.TwoA.Par2
  CFSG.Monster.VisCert

theorem good_alpha23K :
    Good alpha23K := by
  rw [Good, sig_eq_decW, alpha23K, wAct_alpha_decW,
    show Native.actD 22 (genQuotMatrix 23) 6144 = 6144 by decide +kernel, two_add_self]
  exact Uplane.zero_mem

theorem NU_good
    {k : Kstab v0} (hk : k ∈ NU) : Good k := by
  have hw : wAct v0 k wFr ∈ Uplane := hk _ wFr_mem_Uplane
  rcases (mem_Uplane_iff _).1 hw with h | h | h | h
  · exact absurd h (wAct_ne_zero k wFr_ne_zero)
  · exact good_of_mem_NUw ⟨hk, mem_Mfr_of_fix h⟩
  ·
    set g := alpha23K * sgnK
    have hg : wAct v0 g wFr = sW := by
      rw [wAct_mul, Module.End.mul_apply, alpha23K_wFr, map_add, sgnK_wFr, sgnK_sW, ← add_assoc,
        two_add_self, zero_add]
    have hgN : g ∈ NU := NU.mul_mem alpha23K_mem_NU sgnK_mem_NU
    have hm : k * g⁻¹ ∈ NU ⊓ Mfr := by
      refine ⟨NU.mul_mem hk (NU.inv_mem hgN), mem_Mfr_of_fix ?_⟩
      rw [wAct_mul, Module.End.mul_apply, h, ← hg, wAct_inv_apply]
    have e : k = (k * g⁻¹) * alpha23K * sgnK := by
      rw [mul_assoc (k * g⁻¹), inv_mul_cancel_right]
    rw [e]
    exact good_mul (good_mul (good_of_mem_NUw hm) good_alpha23K alpha23K_mem_NU)
      (good_of_mem_NUw sgnK_mem_NUw) sgnK_mem_NU
  ·
    have hm : k * alpha23K⁻¹ ∈ NU ⊓ Mfr := by
      refine ⟨NU.mul_mem hk (NU.inv_mem alpha23K_mem_NU), mem_Mfr_of_fix ?_⟩
      rw [wAct_mul, Module.End.mul_apply, h, ← alpha23K_wFr, wAct_inv_apply]
    have e : k = (k * alpha23K⁻¹) * alpha23K := by rw [inv_mul_cancel_right]
    rw [e]
    exact good_mul (good_of_mem_NUw hm) good_alpha23K alpha23K_mem_NU

theorem NU_le_wSetStab_U4 :
    NU ≤ wSetStab U4 := by
  intro k hk x hx
  rcases (mem_U4_iff x).1 hx with h | h
  · exact Submodule.mem_sup_left (hk _ h)
  · have e : x = (x + sig) + sig := by rw [add_assoc, two_add_self, add_zero]
    have hs : wAct v0 k sig ∈ U4 := by
      have e' : wAct v0 k sig = (wAct v0 k sig + sig) + sig := by
        rw [add_assoc, two_add_self, add_zero]
      rw [e']
      exact U4.add_mem (Submodule.mem_sup_left (NU_good hk)) sig_mem_U4
    rw [e, map_add]
    exact U4.add_mem (Submodule.mem_sup_left (hk _ h)) hs

theorem H3_le_normalizer_E4 :
    H3 ≤ Subgroup.normalizer (E4 : Set Dfull) := by
  intro h hh
  have hJ : h ∈ Jhat := H3_le_Jhat hh
  rw [E4, mem_normalizer_EU_iff hJ]
  have h1 : (⟨h, hJ⟩ : Jhat) ∈ H3.subgroupOf Jhat := hh
  rw [H3_subgroupOf_eq, Subgroup.mem_comap] at h1
  exact NU_le_wSetStab_U4 h1

theorem K3_le_normalizer_E4 :
    K3 ≤ Subgroup.normalizer (E4 : Set Dfull) := by
  intro k hk
  rw [K3_eq_closure] at hk
  refine (Subgroup.closure_le _).2 ?_ hk
  rintro _ (rfl | h)
  · exact tauhat_mem_normalizer_E4
  · exact H3_le_normalizer_E4 h

theorem conj_cQ_mem_cE3
    {k : Dfull} (hk : k ∈ K3) : k * cQ * k⁻¹ ∈ cE3 := by
  refine mem_cE3_of_mem_E4 (conj_mem_of_normalizer (K3_le_normalizer_E4 hk) cQ_mem_E4) ?_
  intro h
  apply cQ_not_mem_E3
  have := conj_mem_of_normalizer (K3.inv_mem hk) h
  rwa [inv_inv, show k⁻¹ * (k * cQ * k⁻¹) * k = cQ by group] at this

theorem conj_mem_cE3
    {k : Dfull} (hk : k ∈ K3) {d : Dfull} (hd : d ∈ cE3) :
    k * d * k⁻¹ ∈ cE3 := by
  obtain ⟨e, he, rfl⟩ := hd
  obtain ⟨e', he', h'⟩ := conj_cQ_mem_cE3 hk
  refine ⟨e' * (k * e * k⁻¹), E3.mul_mem he' (conj_mem_of_normalizer hk he), ?_⟩
  rw [← mul_assoc, h']
  group

theorem exists_R3_translate
    {t : Dfull} (ht : t ∈ E3) : ∃ r ∈ R3, r * cQ * r⁻¹ = cQ * t := by
  by_cases ht1 : t = 1
  · exact ⟨1, R3.one_mem, by rw [ht1, one_mul, inv_one, mul_one]⟩
  obtain ⟨g, hg, hgt⟩ := exists_K3_conj_xhat ht ht1
  obtain ⟨e, he, hec⟩ := exists_R3_xhat
  obtain ⟨t₁, ht₁, h₁⟩ := conj_cQ_mem_cE3 (K3.inv_mem hg)
  rw [inv_inv] at h₁
  have heC : e ∈ C3 := R3_le_C3 he
  have het : e * t₁ * e⁻¹ = t₁ := by
    rw [(Subgroup.mem_centralizer_iff.1 heC t₁ ht₁).symm, mul_inv_cancel_right]
  have hxt : xhat * t₁ = t₁ * xhat :=
    Subgroup.mem_centralizer_iff.1 (E3_le_C3 ht₁) xhat xhat_mem_E3
  refine ⟨g * e * g⁻¹, conj_mem_R3 hg he, ?_⟩
  calc g * e * g⁻¹ * cQ * (g * e * g⁻¹)⁻¹ = g * (e * (g⁻¹ * cQ * g) * e⁻¹) * g⁻¹ := by group
    _ = g * ((e * cQ * e⁻¹) * (e * t₁ * e⁻¹)) * g⁻¹ := by rw [← h₁]; group
    _ = g * (cQ * (xhat * t₁)) * g⁻¹ := by rw [hec, het]; group
    _ = (g * (cQ * t₁) * g⁻¹) * (g * xhat * g⁻¹) := by rw [hxt]; group
    _ = cQ * t := by rw [h₁, hgt]; group

theorem K3_class_eq :
    {d : Dfull | ∃ k ∈ K3, k * cQ * k⁻¹ = d} = cE3 := by
  ext d
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact conj_cQ_mem_cE3 hk
  · rintro ⟨t, ht, rfl⟩
    obtain ⟨r, hr, hrc⟩ := exists_R3_translate ht
    exact ⟨r, R3_le_K3 hr, hrc⟩

theorem cE3_R3_transitive
    {x y : Dfull} (hx : x ∈ cE3) (hy : y ∈ cE3) :
    ∃ r ∈ R3, r * x * r⁻¹ = y := by
  obtain ⟨t, ht, rfl⟩ := hx
  obtain ⟨t', ht', rfl⟩ := hy
  obtain ⟨r, hr, hrc⟩ := exists_R3_translate ht
  obtain ⟨r', hr', hrc'⟩ := exists_R3_translate ht'
  refine ⟨r' * r⁻¹, R3.mul_mem hr' (R3.inv_mem hr), ?_⟩
  rw [← hrc, ← hrc']
  group

end CFSG.Monster.B.TwoA.Par3
