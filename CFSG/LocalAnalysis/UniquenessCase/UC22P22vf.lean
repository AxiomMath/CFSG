module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22f
public import CFSG.LocalAnalysis.UniquenessCase.UC6R2
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
import CFSG.LocalAnalysis.UniquenessCase.UC22P21a
import CFSG.LocalAnalysis.UniquenessCase.UC22P22uh

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22p22vf_gamma_le (D : Data G) (Ch : Choice2011 G) (h77 : F07.R77Eq D)
    (hsp : ∀ p ∈ D.sig1, CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M) (h8 : S22_8 D Ch)
    (hne : D.sig.Nonempty) (hrk : ∀ p ∈ D.sig, 3 ≤ CFSG.Open.pRank p D.M)
    (h1930 : H1930 D) (c : Ctx22b D Ch) (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (Q : Subgroup G)
    (hQM : Q ≤ D.M) (hQq : IsPGroup q ↥Q) (hexp : ∀ x ∈ Q, x ^ q = 1) (hcl : ⁅⁅Q, Q⁆, Q⁆ = ⊥)
    (hnc : ¬ IsCyclic ↥Q) (hn : (barImage D.M Q).Normal) : rankThreeGamma 1 q Q ≤ D.M :=
  gam2210_of D Ch h77 hsp h8 hne hrk h1930 c q hq hq2 Q hQM hQq hexp hcl hnc hn

theorem uc22p22vf_rank_bridge (D : Data G) (Ch : Choice2011 G) (h8 : S22_8 D Ch)
    (hSg : UC6S846.SigmaStd D) (h1930 : H1930 D) (c : Ctx22b D Ch) {q : ℕ}
    (hqB : q ∈ piSet c.B0) : ¬ 4 ≤ CFSG.Open.pRank q D.M := by
  intro h4
  obtain ⟨hqp, hqd⟩ := hqB
  have hodd : Odd (Nat.card c.B0) :=
    uc22p22f_odd_card_B ({ c.toCtx21 with B := c.B0, hB := c.hB0, hle := le_rfl } : Ctx21 D Ch)
  have hq2 : q ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hqd)
  have hσ : q ∈ D.sig := hSg.four_mem q hqp hq2 h4
  exact uc22p22f_not_dvd_card_B D Ch h8 hSg.sig1_sp h1930
    { c with B := c.B0, hB := c.hB0, hle := le_rfl } hσ hqd

private theorem uc22p22vf_mem_zpowers_two {z x : G} (hz2 : z ^ 2 = 1) (hx : x ∈ Subgroup.zpowers z) :
    x = 1 ∨ x = z := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  have h2 : z ^ (2 : ℤ) = 1 := by simpa using hz2
  obtain ⟨m, hm | hm⟩ := Int.even_or_odd' k
  · left
    rw [hm, zpow_mul, h2, one_zpow]
  · right
    rw [hm, zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]

private theorem uc22p22vf_mem_normalizer_zpowers {b e : G} (h : e * b = b * e) :
    e ∈ Subgroup.normalizer ((Subgroup.zpowers b : Subgroup G) : Set G) := by
  have hcen : e ∈ Subgroup.centralizer ((Subgroup.zpowers b : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    have hc : Commute b e := h.symm
    exact (hc.zpow_left k).eq
  exact Subgroup.centralizer_le_normalizer _ hcen

private theorem uc22p22vf_pCoreOf_conj {K : Subgroup G} {h w : G} (hh : h ∈ K)
    (hw : w ∈ pCoreOf 2 K) : h * w * h⁻¹ ∈ pCoreOf 2 K := by
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hw
  have hchar := Subgroup.characteristic_iff_map_le.mp
    (CFSG.pCore_characteristic (p := 2) (G := ↥K))
  have hx' : (MulAut.conj (⟨h, hh⟩ : ↥K)) x ∈ CFSG.pCore 2 ↥K :=
    hchar (MulAut.conj (⟨h, hh⟩ : ↥K)) (Subgroup.mem_map_of_mem _ hx)
  exact Subgroup.mem_map.2 ⟨_, hx', rfl⟩

private theorem uc22p22vf_conj_mem {M : Subgroup G} {b h w : G}
    (hhM : h ∈ M) (hh : h ∈ Subgroup.normalizer ((Subgroup.zpowers b : Subgroup G) : Set G))
    (hw : w ∈ pCoreOf 2 M ⊓ Subgroup.centralizer ({b} : Set G)) :
    h * w * h⁻¹ ∈ pCoreOf 2 M ⊓ Subgroup.centralizer ({b} : Set G) := by
  obtain ⟨hwO, hwC⟩ := Subgroup.mem_inf.1 hw
  refine Subgroup.mem_inf.2 ⟨uc22p22vf_pCoreOf_conj hhM hwO, ?_⟩
  rw [Subgroup.mem_centralizer_iff] at hwC ⊢
  intro y hy
  have hy' : y = b := hy
  subst hy'
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1
    ((Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer _).inv_mem hh) y).1 (Subgroup.mem_zpowers y))
  have hk' : h⁻¹ * y * h = y ^ k := by simpa using hk.symm
  have hwk : w * y ^ k = y ^ k * w := by
    have hc : Commute y w := (hwC y rfl : y * w = w * y)
    exact (hc.zpow_left k).symm.eq
  have hR1 : y * h = h * y ^ k := by
    rw [← hk']
    group
  have hR2 : h⁻¹ * y = y ^ k * h⁻¹ := by
    rw [← hk']
    group
  calc y * (h * w * h⁻¹) = (y * h) * w * h⁻¹ := by group
    _ = (h * y ^ k) * w * h⁻¹ := by rw [hR1]
    _ = h * (y ^ k * w) * h⁻¹ := by group
    _ = h * (w * y ^ k) * h⁻¹ := by rw [hwk]
    _ = h * w * (y ^ k * h⁻¹) := by group
    _ = h * w * (h⁻¹ * y) := by rw [hR2]
    _ = h * w * h⁻¹ * y := by group

theorem uc22p22vf_cyclic_cent (D : Data G) (Ch : Choice2011 G) (h1930 : H1930 D) (_hV : S22_V D Ch)
    (h8 : S22_8 D Ch) (h63 : UC6.R6_3 D) (h67 : UC6.R6_7 D) (_hSg : UC6S846.SigmaStd D)
    (c : Ctx22b D Ch) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {Q : Subgroup G} (hQM : Q ≤ D.M)
    (hQq : IsPGroup q ↥Q) (hGam : rankThreeGamma 1 q Q ≤ D.M) {b : G} (hb : b ∈ c.B0)
    (hb1 : b ≠ 1) : IsCyclic ↥(Q ⊓ centralizer ({b} : Set G)) := by
  classical
  by_contra hnc
  set A : Subgroup G := Q ⊓ centralizer ({b} : Set G) with hA
  have hAQ : A ≤ Q := inf_le_left
  have hAp : IsPGroup q ↥A := hQq.to_le hAQ
  obtain ⟨E, hEA, hEel, hEcard⟩ := uc22p22u_exists_elemAbelian_sq hq hq2 hAp hnc
  have hEQ : E ≤ Q := hEA.trans hAQ
  have hEM : E ≤ D.M := hEQ.trans hQM
  have hΓE : rankThreeGamma 1 q E ≤ D.M := by
    refine le_trans (sSup_le_sSup ?_) hGam
    rintro N ⟨R, hRE, hR, rfl⟩
    exact ⟨R, hRE.trans hEQ, hR, rfl⟩
  have hU : calMOf E = {D.M} := h63 q hq hq2 E hEM hEel hEcard hΓE
  have hEb : ∀ e ∈ E, e * b = b * e := fun e he =>
    (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 (hEA he)).2 b rfl).symm
  set H : Subgroup G := Subgroup.normalizer ((Subgroup.zpowers b : Subgroup G) : Set G) with hH
  have hEH : E ≤ H := fun e he => uc22p22vf_mem_normalizer_zpowers (hEb e he)
  have hHtop : H ≠ ⊤ := by
    intro htop
    haveI hnorm : (Subgroup.zpowers b).Normal := Subgroup.normalizer_eq_top_iff.1 htop
    rcases D.standing.simple.eq_bot_or_eq_top_of_normal (Subgroup.zpowers b) with h | h
    · exact hb1 (Subgroup.zpowers_eq_bot.1 h)
    · obtain ⟨x, y, hxy⟩ := D.standing.nonab
      have hx : x ∈ Subgroup.zpowers b := h ▸ Subgroup.mem_top x
      have hy : y ∈ Subgroup.zpowers b := h ▸ Subgroup.mem_top y
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      exact hxy (Commute.zpow_zpow_self b i j).eq
  have hHnM : ¬ H ≤ D.M :=
    s21_2 D Ch h1930 ({ c.toCtx21 with B := c.B0, hB := c.hB0, hle := le_rfl } : Ctx21 D Ch)
      (Subgroup.zpowers b) (Subgroup.zpowers_le.2 hb)
  obtain ⟨z, hzV, hz1, hzZ, hz2⟩ := uc22p22f_exists_z c
  have hzO : z ∈ pCoreOf 2 D.M := uc22p22f_V_le_pCoreOf c hzV
  have hL0Z : c.L0 ≤ centralizer (D.Z : Set G) := c.hLge.trans (CFSG.Open.IsSubnormal.le c.hL.2)
  have hbZ : b ∈ centralizer (D.Z : Set G) := hL0Z (c.hB0.1 hb)
  have hzb : z * b = b * z := Subgroup.mem_centralizer_iff.1 hbZ z hzZ
  have hzW : z ∈ pCoreOf 2 D.M ⊓ centralizer ({b} : Set G) :=
    Subgroup.mem_inf.2 ⟨hzO, Subgroup.mem_centralizer_iff.2 fun y hy => by
      have hy' : y = b := hy
      subst hy'
      exact hzb.symm⟩
  have hWK : (pCoreOf 2 D.M ⊓ centralizer ({b} : Set G)) ≤ H ⊓ D.M := by
    intro w hw
    obtain ⟨hwO, hwC⟩ := Subgroup.mem_inf.1 hw
    refine Subgroup.mem_inf.2 ⟨uc22p22vf_mem_normalizer_zpowers ?_, Subgroup.map_subtype_le _ hwO⟩
    exact (Subgroup.mem_centralizer_iff.1 hwC b rfl).symm
  have hWnorm : H ⊓ D.M ≤ Subgroup.normalizer ((pCoreOf 2 D.M ⊓ centralizer ({b} : Set G) :
      Subgroup G) : Set G) := by
    intro k hk
    obtain ⟨hkH, hkM⟩ := Subgroup.mem_inf.1 hk
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => uc22p22vf_conj_mem hkM hkH hx, fun hx => ?_⟩
    have := uc22p22vf_conj_mem (Subgroup.inv_mem _ hkM) ((Subgroup.normalizer _).inv_mem hkH) hx
    simpa [mul_assoc] using this
  have hW2 : IsPGroup 2 ↥(pCoreOf 2 D.M ⊓ centralizer ({b} : Set G)) :=
    (D.sylowM.isPGroup.to_le (uc22p22f_pCoreOf_le_T D)).to_le inf_le_left
  have hzK : z ∈ pCoreOf 2 (H ⊓ D.M) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hWK hWnorm hW2 hzW
  have hpc : pCoreOf 2 (H ⊓ D.M) ≠ ⊥ := fun h => hz1 (by simpa [h] using hzK)
  obtain ⟨-, t, ht2, hpceq, -⟩ := h67 (h8 h1930 c).subset q hq hq2 E hEM hEel hEcard hΓE H hEH
    hHtop hpc hHnM
  have ht2' : t ^ 2 = 1 := by
    rw [← ht2]
    exact pow_orderOf_eq_one t
  have hzt : z ∈ Subgroup.zpowers t := hpceq ▸ hzK
  have hztz : z = t := (uc22p22vf_mem_zpowers_two ht2' hzt).resolve_left hz1
  subst hztz
  have hEz : E ≤ centralizer ({z} : Set G) := by
    intro e he
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    have heK : e ∈ H ⊓ D.M := Subgroup.mem_inf.2 ⟨hEH he, hEM he⟩
    have hconj : e * z * e⁻¹ ∈ pCoreOf 2 (H ⊓ D.M) := uc22p22vf_pCoreOf_conj heK hzK
    rw [hpceq] at hconj
    rcases uc22p22vf_mem_zpowers_two ht2' hconj with h | h
    · exact absurd (by simpa using h) hz1
    · calc z * e = (e * z * e⁻¹) * e := by rw [h]
        _ = e * z := by group
  have hH2 : IsTwoLocal (centralizer ({z} : Set G)) := uc22p22f_isTwoLocal_centralizer hz1 hz2
  obtain ⟨N, hN, hHN⟩ := uc22p22f_exists_maxTwoLocal_ge hH2
  have hNmem : N ∈ calMOf E := ⟨hN, hEz.trans hHN⟩
  rw [hU] at hNmem
  have hNM : N = D.M := hNmem
  have hHM : centralizer ({z} : Set G) ≤ D.M := hNM ▸ hHN
  exact c.hC ((Subgroup.centralizer_le (Set.singleton_subset_iff.2 hzZ)).trans hHM)

end CFSG.LocalAnalysis.UniquenessCase.UC22
