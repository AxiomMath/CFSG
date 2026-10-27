module

public import CFSG.RankThree.GF2n.Stroth80.Sec7TailTIHyp79
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailTIFitting
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailTIGen
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailNormLB
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailBarConj
public import CFSG.RankThree.GF2n.Stroth80.Tim81Stroth.VBasic

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

@[expose] def InvAbelian (hc : Ctx M Q Z B) (t : G) (Z0 : Subgroup G) : Prop :=
  ∀ A : Subgroup G, Z0 ≤ A → A ≤ hc.CN t →
    (∀ r ∈ Rt M (LB M Q B) t, conjSubgroup r A = A) → A ≠ hc.CN t →
    ∀ x ∈ A, ∀ y ∈ A, ⁅x, y⁆ ∈ Q

@[expose] def Step7HypSub'Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (n : ℕ) (t : G), Sec7Hyp hc n t →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    IsMaxAbNormalMod (NormH0 M Z Z0) Z0 Q →
    (∀ g ∈ M, ∀ u ∈ Z0, u ∉ Q → g * u * g⁻¹ ∈ Z0 → g ∈ Subgroup.normalizer (Z0 : Set G)) →
    generalizedFitting ↥(bar M Q (NormH0 M Z Z0)) =
      (bar M Q (hc.CN t)).subgroupOf (bar M Q (NormH0 M Z Z0)) →
    InvAbelian hc t Z0 →
    (∃ g ∈ M, conjSubgroup g Z0 ≤ hc.CN t ∧ conjSubgroup g Z0 ≠ Z0) →
    SubConfigHyp79 M Q Z (hc.CN t)

theorem step7HypSub_of_parts (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hZt : Sec7ZtStatement) (hZcard : Sec7ZCardStatement) (hZc : Sec7CentreMpStatement) :
    Step7HypSub'Statement := by
  intro G _ _ M Q Z B _ hc n t hs Z0 hZ0 hMA hTI hF hInv hex
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre ht hZ0
  have hZ0M : Z0 ≤ M := hc.centre_le_M t hZ0
  have hH0M : H0 M Z ≤ M := fun x hx => hx.1
  have hQH : Q ≤ H0 M Z := hc.Q_le_H0'
  have hZ0H0 : Z0 ≤ H0 M Z := hZ0.le.trans (hc.Rt_le_H0 t)
  have hQCN : Q ≤ hc.CN t := hc.Q_le_CN' ht
  have hCNR : hc.CN t ≤ Rt M (LB M Q B) t := fun x hx => (Ctx.mem_CN.mp hx).1
  have hCNH0 : hc.CN t ≤ H0 M Z := hCNR.trans (hc.Rt_le_H0 t)
  haveI hN' : (Q.subgroupOf (H0 M Z)).Normal := normal_subgroupOf_of_le hQH hH0M
  have hconf := hc.tiConfig hs hZ0 hZt hZcard (sec7_CN_pgroup_bar h34 h311a hc hs) hMA hTI hF
  have hinj := embBar_injective hH0M hQH
  have hrange := embBar_range hH0M hQH
  have hconf' := hconf.comap (embBar M Q hH0M hQH) hinj hrange
  rw [comap_embBar_bar hH0M hQH hZ0H0, comap_embBar_bar hH0M hQH hCNH0] at hconf'
  refine ⟨hN', pCore_hat_eq_bot hc, ?_⟩
  have hcen : cen (bar (H0 M Z) Q (hc.CN t)) = bar (H0 M Z) Q Z0 := hconf'.cenIn_N_eq
  rw [hcen]
  have hq4 : 4 ≤ Nat.card ↥(bar (H0 M Z) Q Z0) := by
    have h4 := four_le_card_bar_Z0 hc hs hZcard hZ0
    rw [← map_embBar_bar hH0M hQH hZ0H0, Subgroup.card_map_of_injective hinj] at h4
    exact h4
  have hsq := sq_eq_one_hat hc hs hZc hZ0
  have hne := ne_hat hc hs hZcard hZ0

  obtain ⟨g, hg, hgN, hgne⟩ := hex
  obtain ⟨hb, hbS, hbN, hbV⟩ := exists_Hconj_of_conj hc hs hZ0 hconf hg hgN hgne
  have hex' := exists_hat_conj hQH hH0M (V := bar M Q Z0) (N := bar M Q (hc.CN t))
    (bar_mono' hZ0H0) (bar_mono' hCNH0) ⟨hb, hbS, hbN, hbV⟩
  rw [comap_embBar_bar hH0M hQH hZ0H0, comap_embBar_bar hH0M hQH hCNH0] at hex'
  have hnormR : ∀ ρ ∈ Rt M (LB M Q B) t, ∀ y ∈ Q, ρ * y * ρ⁻¹ ∈ Q := fun ρ hρ y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (hc.Rt_le_M t hρ)) y).mp hy
  have hInv' : ∀ A : Subgroup (↥(H0 M Z) ⧸ Q.subgroupOf (H0 M Z)),
      bar (H0 M Z) Q Z0 ≤ A → A ≤ bar (H0 M Z) Q (hc.CN t) →
      (∀ k ∈ NormIn ⊤ (bar (H0 M Z) Q Z0), k ∈ Subgroup.normalizer (A : Set _)) →
      A ≠ bar (H0 M Z) Q (hc.CN t) → ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := by
    intro A hVA hAN hAinv hANe x hx y hy
    obtain ⟨A', hQA', hA'H0, hbarA⟩ := exists_pre (M := H0 M Z) hQH A
    have hZ0A : Z0 ≤ A' := by
      intro u hu
      have h1 : QuotientGroup.mk' (Q.subgroupOf (H0 M Z)) ⟨u, hZ0H0 hu⟩ ∈ A :=
        hVA (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hu))
      rw [← hbarA] at h1
      exact (mk_mem_bar_iff_sec4 hQA' _).mp h1
    have hA'N : A' ≤ hc.CN t := by
      intro u hu
      have h1 : QuotientGroup.mk' (Q.subgroupOf (H0 M Z)) ⟨u, hA'H0 hu⟩ ∈
          bar (H0 M Z) Q (hc.CN t) :=
        hAN (hbarA ▸ Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hu))
      exact (mk_mem_bar_iff_sec4 hQCN _).mp h1
    have hA'ne : A' ≠ hc.CN t := fun h => hANe (by rw [← hbarA, h])
    have hRinv : ∀ r ∈ Rt M (LB M Q B) t, conjSubgroup r A' = A' := by
      intro r hr
      have hrH0 : r ∈ H0 M Z := hc.Rt_le_H0 t hr
      have hrZ0 : r ∈ Subgroup.normalizer (Z0 : Set G) := IsCentrePre.mem_normalizer hZ0 hnormR hr
      have h1 := mk_mem_normalizer_bar_of_normalizer (M := H0 M Z) hQZ0 ⟨r, hrH0⟩ hrZ0
      have h2 := hAinv _ (mem_NormIn.mpr ⟨Subgroup.mem_top _, h1⟩)
      rw [← hbarA] at h2
      exact conjSubgroup_eq_self_iff.mpr
        (mem_normalizer_of_mk_mem_normalizer_bar (M := H0 M Z) hQA' hA'H0 ⟨r, hrH0⟩ h2)
    have hab := hInv A' hZ0A hA'N hRinv hA'ne
    obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp (hbarA ▸ hx)
    obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.mp (hbarA ▸ hy)
    exact step716_mk_mul_comm (hab _ (Subgroup.mem_subgroupOf.mp hx') _
      (Subgroup.mem_subgroupOf.mp hy'))
  have hgen := hconf'.gen_of_inv hex' hInv'
  have hKmap : (Subgroup.normalizer ((bar (H0 M Z) Q Z0 : Subgroup _) : Set _)).map
      (embBar M Q hH0M hQH) = bar M Q (NormH0 M Z Z0) := by
    have hVr : bar M Q Z0 ≤ (embBar M Q hH0M hQH).range := by
      rw [hrange]; exact bar_mono' hZ0H0
    rw [bar_NormH0_eq hc hQZ0 hZ0M]
    ext z
    constructor
    · rintro ⟨k, hk, rfl⟩
      have hk' : k ∈ Subgroup.normalizer ((((bar M Q Z0).comap (embBar M Q hH0M hQH) :
          Subgroup _)) : Set _) := by
        rw [comap_embBar_bar hH0M hQH hZ0H0]; exact hk
      refine mem_NormIn.mpr ⟨?_, (TIConfig.normalizer_comap_iff hVr k).mp hk'⟩
      rw [← hrange]; exact ⟨k, rfl⟩
    · intro hz
      obtain ⟨hzH, hzN⟩ := mem_NormIn.mp hz
      rw [← hrange] at hzH
      obtain ⟨k, rfl⟩ := hzH
      refine ⟨k, ?_, rfl⟩
      have := (TIConfig.normalizer_comap_iff hVr k).mpr hzN
      rwa [comap_embBar_bar hH0M hQH hZ0H0] at this
  have hfit1 := generalizedFitting_comap_eq (embBar M Q hH0M hQH) hinj hKmap hF
  rw [comap_embBar_bar hH0M hQH hCNH0] at hfit1
  have hfit2 := pCore_normalizer_eq hconf'
  exact hyp79_of_tiConfig hconf' hq4 hsq hne hgen (hfit1.trans hfit2.symm)

end CFSG.RankThree.GF2n.Stroth80
