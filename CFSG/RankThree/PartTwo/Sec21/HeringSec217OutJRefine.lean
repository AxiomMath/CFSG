module

public import CFSG.RankThree.PartTwo.Sec21.HeringSec217OutJ
public import CFSG.RankThree.PartTwo.Sec21.HeringSec217OutSteps

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open Subgroup CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec21 CFSG.Blueprint
open scoped commutatorElement

section Refine

variable {G : Type} [Group G] [Finite G] {A E U : Subgroup G} {c : G} {L : Subgroup G}


set_option linter.unusedSectionVars false

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem CoverOut.A_le_normalizer_component (h45 : Sec4.Item4_5) (h : CoverOut A E U c L) {a : G}
    (hfr : Frame217 E c L a) {d : G} (hd : Subgroup.zpowers d = dGroup a c ⊓ L) {J : Subgroup G}
    (hJ : J ∈ thetaComponentsAt 3 d) (hIJ : iCore L a ≤ J) :
    A ≤ Subgroup.normalizer (J : Set G) := by
  obtain ⟨⟨e⟩, hIA, hIcen, hIcomm, hcardAI, hAC⟩ := h.iCore_structure h45 hfr
  obtain ⟨l, hlA, ⟨i, hai⟩, hl1, hl3, hlnc, hDeq, hDL, hDA, hDE⟩ := h.dgroup_decomp h45 hfr
  have hdDL : d ∈ dGroup a c ⊓ L := hd ▸ Subgroup.mem_zpowers d
  have hdA : d ∈ A := hDA hdDL.1
  have hab := isElemAbelian_iff.1 h.isElemAbelian_A
  have hIperf : ⁅iCore L a, iCore L a⁆ = iCore L a := perfect_of_equiv_alt6 _ e
  have hIs : ¬ Group.IsSolvable ↥(iCore L a) := not_isSolvable_of_equiv_alt6 e
  have hqnd : ∀ q : G, q * d = d * q →
      q ∈ Subgroup.normalizer ((Subgroup.zpowers d : Subgroup G) : Set G) := by
    intro q hq
    have hqC : q ∈ Subgroup.centralizer ((Subgroup.zpowers d : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      exact ((show Commute d q from hq.symm).zpow_left k).eq
    exact Subgroup.centralizer_le_normalizer ((Subgroup.zpowers d : Subgroup G) : Set G) hqC
  intro q hq
  have hJ' := CFSG.RankThree.PartOne.Sec12TwoAssembly.conj_mem_thetaComponentsAt
    Nat.prime_three (hqnd q (hab.1 q hq d hdA)) hJ
  have hIJ2 : iCore L a ≤ J ⊓ J.map (MulAut.conj q).toMonoidHom := by
    intro x hx
    refine ⟨hIJ hx, ⟨q⁻¹ * x * q, hIJ ?_, ?_⟩⟩
    swap
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem (hIA q hq)) x).1 hx
    simpa using this
  have heq := eq_of_perfect_le_inf_thetaComponentsAt hJ hJ' hIJ2 hIperf hIs
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact heq.symm

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem CoverOut.A_inf_thetaQuot_eq (h45 : Sec4.Item4_5) (h : CoverOut A E U c L) {a : G}
    (hfr : Frame217 E c L a) {d : G} (hd : Subgroup.zpowers d = dGroup a c ⊓ L) {J : Subgroup G}
    (hJ : J ∈ thetaComponentsAt 3 d) (hIJ : iCore L a ≤ J)
    (hcQ : c ∉ Sec4.thetaQuotCentralizer J) :
    A ⊓ Sec4.thetaQuotCentralizer J = Subgroup.zpowers d := by
  obtain ⟨⟨e⟩, hIA, hIcen, hIcomm, hcardAI, hAC⟩ := h.iCore_structure h45 hfr
  obtain ⟨l, hlA, ⟨i, hai⟩, hl1, hl3, hlnc, hDeq, hDL, hDA, hDE⟩ := h.dgroup_decomp h45 hfr
  obtain ⟨hd1, hfrd⟩ := h.frame_of_zpowers_eq_inf h45 hfr hd
  have hdDL : d ∈ dGroup a c ⊓ L := hd ▸ Subgroup.mem_zpowers d
  have hdl : d ∈ Subgroup.zpowers (l : G) := hDL ▸ hdDL
  have hld : (l : G) ∈ Subgroup.zpowers d := mem_zpowers_of_mem_zpowers hl3 hd1 hdl
  have hDeq' : dGroup a c = Subgroup.zpowers d ⊔ Subgroup.zpowers c := by
    rw [hDeq]
    congr 1
    exact le_antisymm (Subgroup.zpowers_le.2 hld) (Subgroup.zpowers_le.2 hdl)
  have hab := isElemAbelian_iff.1 h.isElemAbelian_A
  have hdA : d ∈ A := hDA hdDL.1
  have hJC : J ≤ Subgroup.centralizer ({d} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hJ
  have hdQ : d ∈ Sec4.thetaQuotCentralizer J := by
    refine Sec6.mem_thetaQuotCentralizer_iff.2 ⟨?_, fun l' hl' => ?_⟩
    · have hdC : d ∈ Subgroup.centralizer (J : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        exact Subgroup.mem_centralizer_singleton_iff.1 (hJC hx)
      exact Subgroup.centralizer_le_normalizer (J : Set G) hdC
    · have hl'd : l' * d = d * l' := Subgroup.mem_centralizer_singleton_iff.1 (hJC hl')
      have : d * l' * d⁻¹ = l' := by rw [← hl'd]; group
      rw [this, inv_mul_cancel]
      exact Subgroup.one_mem _
  apply le_antisymm
  · rintro q ⟨hqA, hqQ⟩
    have hqC : q ∈ Subgroup.centralizer ((iCore L a : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have h1 := (Sec6.mem_thetaQuotCentralizer_iff.1 hqQ).2 x (hIJ hx)
      have h2 : x⁻¹ * (q * x * q⁻¹) ∈ iCore L a :=
        (iCore L a).mul_mem ((iCore L a).inv_mem hx)
          ((Subgroup.mem_normalizer_iff.1 (hIA q hqA) x).1 hx)
      have h3 : x⁻¹ * (q * x * q⁻¹) ∈
          iCore L a ⊓ inSubgroup (aschbacherSolvableCore 3) J := ⟨h2, h1⟩
      rw [inf_theta_eq_bot_of_A6 hIJ e, Subgroup.mem_bot] at h3
      have h4 : x = q * x * q⁻¹ := inv_mul_eq_one.1 h3
      calc x * q = (q * x * q⁻¹) * q := by rw [← h4]
        _ = q * x := by group
    have hqD : q ∈ dGroup a c := by
      rw [← hAC]
      exact ⟨hqA, hqC⟩
    rw [hDeq'] at hqD
    have hcomm' : ∀ x ∈ Subgroup.zpowers d, ∀ y ∈ Subgroup.zpowers c, x * y = y * x := by
      intro x hx y hy
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      exact ((show Commute d c from hab.1 d hdA c h.c_mem_A).zpow_zpow j k).eq
    obtain ⟨p, hp, r, hr, hpr⟩ := (mem_sup_of_commute hcomm').1 hqD
    have hrQ : r ∈ Sec4.thetaQuotCentralizer J := by
      have hpQ : p ∈ Sec4.thetaQuotCentralizer J := by
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hp
        exact Subgroup.zpow_mem _ hdQ j
      have := Subgroup.mul_mem _ (Subgroup.inv_mem _ hpQ) hqQ
      rw [← hpr] at this
      simpa using this
    have hr1 : r = 1 := by
      by_contra hr1
      apply hcQ
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hr
      have hk3 : ¬ (3 : ℤ) ∣ k := by
        intro hk3
        apply hr1
        obtain ⟨m, rfl⟩ := hk3
        rw [zpow_mul]
        have h3z : c ^ (3 : ℤ) = 1 := by exact_mod_cast h.c_cubed
        rw [h3z, one_zpow]
      have hc : c = (c ^ k) ^ (k : ℤ) := by
        rw [← zpow_mul]
        have h12 : k % 3 = 1 ∨ k % 3 = 2 := by omega
        have hmod : c ^ (k * k) = c ^ ((k * k) % 3) := by
          have := zpow_mod_orderOf c (k * k)
          rw [orderOf_eq_prime h.c_cubed h.c_ne_one] at this
          exact_mod_cast this.symm
        have hkk : (k * k) % 3 = 1 := by
          rcases h12 with h1 | h2
          · simp [Int.mul_emod, h1]
          · simp [Int.mul_emod, h2]
        rw [hmod, hkk, zpow_one]
      rw [hc]
      exact Subgroup.zpow_mem _ hrQ k
    rw [hr1, mul_one] at hpr
    rw [← hpr]
    exact hp
  · exact le_inf (Subgroup.zpowers_le.2 hdA) (Subgroup.zpowers_le.2 hdQ)

theorem sec217OutJCentral_of (h45 : Sec4.Item4_5) (hJ : Sec217OutJ) : Sec217OutJCentral := by
  intro G _ _ A E U c L a h hfr d hd htr J hJd hIJ
  by_contra hcQ
  exact hJ G A E U c L a h hfr d hd htr J hJd hIJ
    (h.A_le_normalizer_component h45 hfr hd hJd hIJ)
    (h.A_inf_thetaQuot_eq h45 hfr hd hJd hIJ hcQ)

end Refine

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
