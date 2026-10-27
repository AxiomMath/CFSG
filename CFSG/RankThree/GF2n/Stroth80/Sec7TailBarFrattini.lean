module

public import CFSG.RankThree.GF2n.Stroth80.Sec7TailBarConj
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailTIConfigC

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal]

theorem exists_H_conj_of_frattini {X : Type*} [Group X] {H V : Subgroup X}
    (hf : ∀ g : X, ∃ k ∈ Subgroup.normalizer (V : Set X), ∃ y ∈ H, g = k * y) (g : X) :
    ∃ h ∈ H, conjSubgroup g V = conjSubgroup h V := by
  obtain ⟨k, hk, y, hy, hgky⟩ := hf g⁻¹
  refine ⟨y⁻¹, H.inv_mem hy, ?_⟩
  have e : g = y⁻¹ * k⁻¹ := by
    have : g = (g⁻¹)⁻¹ := (inv_inv g).symm
    rw [this, hgky]; group
  rw [e, ← CFSG.CGT.Timmesfeld75.conjSubgroup_conjSubgroup,
    CFSG.RankThree.GF2n.conjSubgroup_eq_self_iff.mpr ((Subgroup.normalizer _).inv_mem hk)]

@[expose] def CentTwoInV (hc : Ctx M Q Z B) (t : G) (Z0 : Subgroup G) : Prop :=
  ∀ k ∈ bar M Q (NormH0 M Z Z0), IsPGroup 2 (Subgroup.zpowers k) →
    (∀ n ∈ bar M Q (hc.CN t), k * n = n * k) → k ∈ bar M Q Z0

theorem Ctx.tiConfigC (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hZt : Sec7ZtStatement) (hZcard : Sec7ZCardStatement)
    (hN2 : IsPGroup 2 ↥(bar M Q (hc.CN t)))
    (hTI : ∀ g ∈ M, ∀ u ∈ Z0, u ∉ Q → g * u * g⁻¹ ∈ Z0 →
      g ∈ Subgroup.normalizer (Z0 : Set G))
    (hC : CentTwoInV hc t Z0) :
    TIConfigC (bar M Q (H0 M Z)) (bar M Q Z0) (bar M Q (hc.CN t)) := by
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre ht hZ0
  have hZ0M : Z0 ≤ M := hc.centre_le_M t hZ0
  have hQH : Q ≤ H0 M Z := hc.Q_le_H0'
  have hZ0H0 : Z0 ≤ H0 M Z := hZ0.le.trans (hc.Rt_le_H0 t)
  have hZ0N : Z0 ≤ hc.CN t := sec7ctr_Z0_le_CN hc hs hZ0
  have hNR : hc.CN t ≤ Rt M (LB M Q B) t := fun x hx => (Ctx.mem_CN.mp hx).1
  have hnormR : ∀ ρ ∈ Rt M (LB M Q B) t, ∀ y ∈ Q, ρ * y * ρ⁻¹ ∈ Q := fun ρ hρ y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (hc.Rt_le_M t hρ)) y).mp hy
  have hRK : Rt M (LB M Q B) t ≤ NormH0 M Z Z0 := fun ρ hρ =>
    Subgroup.mem_inf.mpr ⟨hc.Rt_le_H0 t hρ, IsCentrePre.mem_normalizer hZ0 hnormR hρ⟩
  have hNK : hc.CN t ≤ NormH0 M Z Z0 := hNR.trans hRK
  have hQN : Q ≤ NormH0 M Z Z0 := fun q hq =>
    Subgroup.mem_inf.mpr ⟨hQH hq, Subgroup.le_normalizer (hQZ0 hq)⟩
  have hKbar := bar_NormH0_eq hc hQZ0 hZ0M
  refine
    { V_le := bar_mono' hZ0H0
      V_ne_bot := ?_
      V_le_N := bar_mono' hZ0N
      ti := ?_
      N_le := ?_
      N_normal := ?_
      N_pgroup := hN2
      cent2 := ?_ }
  · obtain ⟨s, hsZ, hsQ⟩ := sec7_exists_Z0_not_Q hZcard hc hs hZ0
    intro hbot
    have hmem : QuotientGroup.mk' (Q.subgroupOf M) ⟨s, hZ0M hsZ⟩ ∈ bar M Q Z0 :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hsZ)
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hsQ (Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp hmem))
  · intro g x hx hx1 hgx
    obtain ⟨g', rfl⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) g
    obtain ⟨x', rfl⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) x
    have hx'Z : (x' : G) ∈ Z0 := (mk_mem_bar_iff_sec4 hQZ0 x').mp hx
    have hx'Q : (x' : G) ∉ Q := fun h => hx1 ((QuotientGroup.eq_one_iff x').mpr h)
    rw [← map_inv, ← map_mul, ← map_mul, mk_mem_bar_iff_sec4 hQZ0] at hgx
    exact mk_mem_normalizer_bar_of_normalizer hQZ0 g' (hTI g' g'.2 x' hx'Z hx'Q hgx)
  · rw [← hKbar]
    exact bar_mono' hNK
  · intro k hk
    rw [← hKbar] at hk
    obtain ⟨k', rfl⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) k
    have hk' : (k' : G) ∈ NormH0 M Z Z0 := (mk_mem_bar_iff_sec4 hQN k').mp hk
    have hcn := sec7_conj_CN_eq hZt hZcard hc hs hZ0 hk'
    exact mk_mem_normalizer_bar_of_normalizer (hc.Q_le_CN' ht) k'
      (conjSubgroup_eq_self_iff.mp hcn)
  · intro k hk hk2 hkc
    rw [← hKbar] at hk
    exact hC k hk hk2 hkc

theorem Ctx.sylow_of_cent2 (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hZt : Sec7ZtStatement) (hZcard : Sec7ZCardStatement)
    (hN2 : IsPGroup 2 ↥(bar M Q (hc.CN t)))
    (hTI : ∀ g ∈ M, ∀ u ∈ Z0, u ∉ Q → g * u * g⁻¹ ∈ Z0 →
      g ∈ Subgroup.normalizer (Z0 : Set G))
    (hC : CentTwoInV hc t Z0) {S : Subgroup (Mbar M Q)}
    (hSK : S ≤ bar M Q (NormH0 M Z Z0)) (hSp : IsPGroup 2 S)
    (hS : ∀ T : Subgroup (Mbar M Q), T ≤ bar M Q (NormH0 M Z Z0) → IsPGroup 2 T → S ≤ T →
      T = S) :
    ∀ T : Subgroup (Mbar M Q), T ≤ bar M Q (H0 M Z) → IsPGroup 2 T → S ≤ T → T = S := by
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre ht hZ0
  have hZ0M : Z0 ≤ M := hc.centre_le_M t hZ0
  have hconf := hc.tiConfigC hs hZ0 hZt hZcard hN2 hTI hC
  have hKbar := bar_NormH0_eq hc hQZ0 hZ0M
  rw [hKbar] at hSK hS
  exact hconf.sylow_of_maximal hSK hSp hS

theorem Ctx.exists_H0_conj (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hZt : Sec7ZtStatement) (hZcard : Sec7ZCardStatement)
    (hN2 : IsPGroup 2 ↥(bar M Q (hc.CN t)))
    (hTI : ∀ g ∈ M, ∀ u ∈ Z0, u ∉ Q → g * u * g⁻¹ ∈ Z0 →
      g ∈ Subgroup.normalizer (Z0 : Set G))
    (hC : CentTwoInV hc t Z0) {g : G} (hg : g ∈ M) :
    ∃ h ∈ H0 M Z, conjSubgroup g Z0 = conjSubgroup h Z0 := by
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre ht hZ0
  have hZ0M : Z0 ≤ M := hc.centre_le_M t hZ0
  have hQM : Q ≤ M := hc.hyp.Q_normal.1
  have hQH : Q ≤ H0 M Z := hc.Q_le_H0'
  have hH0M : H0 M Z ≤ M := fun x hx => hx.1
  have hconf := hc.tiConfigC hs hZ0 hZt hZcard hN2 hTI hC
  haveI hnormH := hc.normal_bar_H0
  have hHn : ∀ x : Mbar M Q, x ∈ Subgroup.normalizer
      ((bar M Q (H0 M Z) : Subgroup (Mbar M Q)) : Set (Mbar M Q)) := fun x => by
    rw [Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top x
  obtain ⟨hb, hbH, hbeq⟩ := exists_H_conj_of_frattini
    (hconf.frattini_conj hHn) (QuotientGroup.mk' (Q.subgroupOf M) ⟨g, hg⟩)
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) hb
  have hhH : (h : G) ∈ H0 M Z := (mk_mem_bar_iff_sec4 hQH h).mp hbH
  refine ⟨h, hhH, ?_⟩
  rw [conjSubgroup_bar hQZ0 hQM ⟨g, hg⟩, conjSubgroup_bar hQZ0 hQM h] at hbeq
  exact bar_injective_of_ge (Q_le_conjSubgroup hQZ0 hQM ⟨g, hg⟩)
    (Q_le_conjSubgroup hQZ0 hQM h) (conj_le_M hZ0M hg) (conj_le_M hZ0M h.2) hbeq

end CFSG.RankThree.GF2n.Stroth80
