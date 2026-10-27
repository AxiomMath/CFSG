module

public import CFSG.RankThree.GF2n.Stroth80.Sec7TailBarDict
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailBarEmb
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailTIFrattini
public import CFSG.RankThree.GF2n.Stroth80.Tim81Stroth.O2Hbar

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal]

theorem bar_injective_of_ge {S T : Subgroup G} (hQS : Q ≤ S) (hQT : Q ≤ T) (hSM : S ≤ M)
    (hTM : T ≤ M) (h : bar M Q S = bar M Q T) : S = T := by
  ext x
  constructor
  · intro hx
    have h1 := (mk_mem_bar_iff_sec4 hQS ⟨x, hSM hx⟩).mpr hx
    rw [h] at h1
    exact (mk_mem_bar_iff_sec4 hQT _).mp h1
  · intro hx
    have h1 := (mk_mem_bar_iff_sec4 hQT ⟨x, hTM hx⟩).mpr hx
    rw [← h] at h1
    exact (mk_mem_bar_iff_sec4 hQS _).mp h1

theorem Q_le_conjSubgroup {S : Subgroup G} (hQS : Q ≤ S) (hQM : Q ≤ M) (g : M) :
    Q ≤ conjSubgroup (g : G) S := by
  intro y hy
  rw [mem_conjSubgroup]
  have h1 : (g⁻¹ : M) * ⟨y, hQM hy⟩ * (g⁻¹ : M)⁻¹ ∈ Q.subgroupOf M :=
    Subgroup.Normal.conj_mem inferInstance _ (Subgroup.mem_subgroupOf.mpr hy) g⁻¹
  exact hQS (by simpa using Subgroup.mem_subgroupOf.mp h1)

theorem conjSubgroup_bar {S : Subgroup G} (hQS : Q ≤ S) (hQM : Q ≤ M) (g : M) :
    conjSubgroup (QuotientGroup.mk' (Q.subgroupOf M) g) (bar M Q S) =
      bar M Q (conjSubgroup (g : G) S) := by
  have hQc := Q_le_conjSubgroup hQS hQM g
  ext z
  obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) z
  rw [mem_conjSubgroup, ← map_inv, ← map_mul, ← map_mul, mk_mem_bar_iff_sec4 hQS,
    mk_mem_bar_iff_sec4 hQc, mem_conjSubgroup]
  simp [mul_assoc]

theorem pCore_hat_eq_bot (hc : Ctx M Q Z B) [(Q.subgroupOf (H0 M Z)).Normal] :
    pCore 2 (↥(H0 M Z) ⧸ Q.subgroupOf (H0 M Z)) = ⊥ := by
  have hH0M : H0 M Z ≤ M := fun x hx => hx.1
  have hQH : Q ≤ H0 M Z := hc.Q_le_H0'
  have hinj := embBar_injective hH0M hQH
  have hrange := embBar_range hH0M hQH
  let iso : (↥(H0 M Z) ⧸ Q.subgroupOf (H0 M Z)) ≃* ↥(bar M Q (H0 M Z)) :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  have h := CFSG.pCore_map_iso 2 iso
  rw [pCore_two_bar_H0_eq_bot hc] at h
  exact (Subgroup.map_eq_bot_iff_of_injective _ iso.injective).mp h

theorem sq_eq_one_hat (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t)
    (hZc : Sec7CentreMpStatement) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) [(Q.subgroupOf (H0 M Z)).Normal] :
    ∀ x ∈ bar (H0 M Z) Q Z0, x ^ 2 = 1 := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  have hyZ : (y : G) ∈ Z0 := Subgroup.mem_subgroupOf.mp hy
  have hyL : (y : G) ∈ LB M Q B := (hZc G M Q Z B hc n t hs Z0 hZ0 _ hyZ).1
  have hsq : (y : G) ^ 2 ∈ Q := hc.sq_mem_Q_of_mem_LB hyL
  rw [← map_pow]
  exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr (by simpa using hsq))

theorem ne_hat (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t)
    (hZcard : Sec7ZCardStatement) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) [(Q.subgroupOf (H0 M Z)).Normal] :
    bar (H0 M Z) Q (hc.CN t) ≠ bar (H0 M Z) Q Z0 := by
  intro h
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre ht hZ0
  have hQCN : Q ≤ hc.CN t := hc.Q_le_CN' ht
  have hZ0H0 : Z0 ≤ H0 M Z := hZ0.le.trans (hc.Rt_le_H0 t)
  have hCNR : hc.CN t ≤ Rt M (LB M Q B) t := fun x hx => (Ctx.mem_CN.mp hx).1
  have hCNH0 : hc.CN t ≤ H0 M Z := hCNR.trans (hc.Rt_le_H0 t)
  have heq := bar_injective_of_ge (M := H0 M Z) hQCN hQZ0 hCNH0 hZ0H0 h
  have hlarge := hs.large
  have hcard := hZcard G M Q Z B hc n t hs Z0 hZ0
  rw [heq] at hlarge
  omega

theorem exists_Hconj_of_conj (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hconf : TIConfig (bar M Q (H0 M Z)) (bar M Q Z0) (bar M Q (hc.CN t)))
    {g : G} (hg : g ∈ M) (h1 : conjSubgroup g Z0 ≤ hc.CN t) (h2 : conjSubgroup g Z0 ≠ Z0) :
    ∃ h ∈ bar M Q (H0 M Z), conjSubgroup h (bar M Q Z0) ≤ bar M Q (hc.CN t) ∧
      conjSubgroup h (bar M Q Z0) ≠ bar M Q Z0 := by
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre ht hZ0
  have hZ0M : Z0 ≤ M := hc.centre_le_M t hZ0
  have hQM : Q ≤ M := hc.hyp.Q_normal.1
  haveI hnormH := hc.normal_bar_H0
  have hHn : ∀ x : Mbar M Q, x ∈ Subgroup.normalizer
      ((bar M Q (H0 M Z) : Subgroup (Mbar M Q)) : Set (Mbar M Q)) := fun x => by
    rw [Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top x
  set gb : Mbar M Q := QuotientGroup.mk' (Q.subgroupOf M) ⟨g, hg⟩ with hgb
  obtain ⟨k, hk, y, hy, hgky⟩ := hconf.frattini_conj hHn gb⁻¹
  have hconj : conjSubgroup gb (bar M Q Z0) = conjSubgroup y⁻¹ (bar M Q Z0) := by
    have e : gb = y⁻¹ * k⁻¹ := by
      have : gb = (gb⁻¹)⁻¹ := (inv_inv gb).symm
      rw [this, hgky]; group
    rw [e, ← CFSG.CGT.Timmesfeld75.conjSubgroup_conjSubgroup,
      CFSG.RankThree.GF2n.conjSubgroup_eq_self_iff.mpr ((Subgroup.normalizer _).inv_mem hk)]
  have hcb : conjSubgroup gb (bar M Q Z0) = bar M Q (conjSubgroup g Z0) :=
    conjSubgroup_bar hQZ0 hQM ⟨g, hg⟩
  refine ⟨y⁻¹, (bar M Q (H0 M Z)).inv_mem hy, ?_, ?_⟩
  · rw [← hconj, hcb]
    exact bar_mono' h1
  · intro hEq
    rw [← hconj, hcb] at hEq
    have hQc : Q ≤ conjSubgroup g Z0 := Q_le_conjSubgroup hQZ0 hQM ⟨g, hg⟩
    exact h2 (bar_injective_of_ge hQc hQZ0 (conj_le_M hZ0M hg) hZ0M hEq)

theorem conjSubgroup_comap {X Y : Type*} [Group X] [Group Y] (e : Y →* X) (g : Y)
    (S : Subgroup X) : conjSubgroup g (S.comap e) = (conjSubgroup (e g) S).comap e := by
  ext x
  simp only [mem_conjSubgroup, Subgroup.mem_comap, map_mul, map_inv]

theorem exists_hat_conj {S : Subgroup G} (hQS : Q ≤ S) (hSM : S ≤ M)
    [(Q.subgroupOf S).Normal] {V N : Subgroup (Mbar M Q)}
    (hV : V ≤ bar M Q S) (hN : N ≤ bar M Q S)
    (h : ∃ h ∈ bar M Q S, conjSubgroup h V ≤ N ∧ conjSubgroup h V ≠ V) :
    ∃ g' : (↥S ⧸ Q.subgroupOf S), conjSubgroup g' (V.comap (embBar M Q hSM hQS)) ≤
        N.comap (embBar M Q hSM hQS) ∧
      conjSubgroup g' (V.comap (embBar M Q hSM hQS)) ≠ V.comap (embBar M Q hSM hQS) := by
  obtain ⟨hb, hbS, hbN, hbV⟩ := h
  have hrange := embBar_range hSM hQS
  obtain ⟨g', hg'⟩ : hb ∈ (embBar M Q hSM hQS).range := by rw [hrange]; exact hbS
  refine ⟨g', ?_, ?_⟩
  · rw [conjSubgroup_comap, hg']
    exact Subgroup.comap_mono hbN
  · intro hEq
    rw [conjSubgroup_comap, hg'] at hEq
    apply hbV
    ext z
    constructor
    · intro hz
      have hzS : z ∈ bar M Q S := by
        have hmem : z ∈ conjSubgroup hb V := hz
        rw [mem_conjSubgroup] at hmem
        have h1 : hb⁻¹ * z * hb ∈ bar M Q S :=
          hV hmem
        have : z = hb * (hb⁻¹ * z * hb) * hb⁻¹ := by group
        rw [this]
        exact (bar M Q S).mul_mem ((bar M Q S).mul_mem hbS h1) ((bar M Q S).inv_mem hbS)
      obtain ⟨x, hx⟩ : z ∈ (embBar M Q hSM hQS).range := by rw [hrange]; exact hzS
      have : x ∈ (conjSubgroup hb V).comap (embBar M Q hSM hQS) := by
        rw [Subgroup.mem_comap, hx]; exact hz
      rw [hEq, Subgroup.mem_comap, hx] at this
      exact this
    · intro hz
      have hzS : z ∈ bar M Q S := hV hz
      obtain ⟨x, hx⟩ : z ∈ (embBar M Q hSM hQS).range := by rw [hrange]; exact hzS
      have : x ∈ (V.comap (embBar M Q hSM hQS)) := by rw [Subgroup.mem_comap, hx]; exact hz
      rw [← hEq, Subgroup.mem_comap, hx] at this
      exact this

end CFSG.RankThree.GF2n.Stroth80
