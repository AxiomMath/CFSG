module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3EOmega
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3KGap

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3E

open GoldAmL3

open scoped commutatorElement

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {z : D} {V : Subgroup D}

namespace Ctx

omit [Finite D] in
theorem comm_KK_normal (_c : Ctx A B z V) {x n : D} (hx : x ∈ B) (hn : n ∈ ⁅Ksub A B, Ksub A B⁆) :
    x * n * x⁻¹ ∈ ⁅Ksub A B, Ksub A B⁆ := by
  have hK : conjSub x (Ksub A B) = Ksub A B :=
    conjSub_eq_of_mem_normalizer (le_normalizer_coreIn _ _ hx)
  have hN : conjSub x ⁅Ksub A B, Ksub A B⁆ = ⁅Ksub A B, Ksub A B⁆ := by
    unfold conjSub
    rw [Subgroup.map_commutator]
    unfold conjSub at hK
    rw [hK]
  have hmem : x ∈ Subgroup.normalizer ((⁅Ksub A B, Ksub A B⁆ : Subgroup D) : Set D) :=
    mem_normalizer_of_conjSub_eq hN
  exact (Subgroup.mem_normalizer_iff.mp hmem n).mp hn

end Ctx

namespace Gen

variable {c : Ctx A B z V} (g : Gen c)

include g in
theorem comm_mem_zpowers {m : D} (hm : m ∈ Msub A B V) (hP : ∀ q ∈ pCoreOf 2 A, ⁅m, q⁆ ∈ V) :
    ∀ q ∈ pCoreOf 2 A, ⁅m, q⁆ ∈ Subgroup.zpowers z := by
  intro q hq
  obtain ⟨w, hw, k, hk, rfl⟩ := g.exists_mul_of_mem_Q hq
  have hwQ := c.W_le_Q hw
  have hkQ := c.K_le_Q hk
  have hmK : m ∈ Ksub A B := c.M_le_K hm
  have h1 : ⁅m, w⁆ = 1 := comm_eq_one_iff.mpr ((c.mem_M_iff.mp hm).2 w hw).symm
  have h2 : ⁅m, w * k⁆ = ⁅m, k⁆ := by
    rw [comm_mul_right, h1, one_mul]
    exact c.conj_V (hP k hkQ) hwQ
  rw [h2]
  let N₂ : Subgroup D := conjClosure V B ⊓ ⁅Ksub A B, Ksub A B⁆
  have hN₂V : N₂ ≤ V := by
    intro n hn
    have hnM : n ∈ Msub A B V := by
      have : ⁅Ksub A B, Ksub A B⁆ ≤ Msub A B V :=
        Subgroup.commutator_le.mpr fun x hx y hy => c.comm_K_K_M hx hy
      exact this hn.2
    exact g.U_inf_M_le_V hn.1 hnM
  have hN₂B : ∀ x ∈ B, ∀ n ∈ N₂, x * n * x⁻¹ ∈ N₂ := fun x hx n hn =>
    ⟨conjClosure_conj_mem hx hn.1, c.comm_KK_normal hx hn.2⟩
  have hmem : ⁅m, k⁆ ∈ N₂ :=
    ⟨le_conjClosure V B (hP k hkQ), Subgroup.commutator_mem_commutator hmK hk⟩
  exact c.le_zpowers_of_normal hN₂V hN₂B hmem

include g in
theorem centerQ_of_Z2 {m : D} (hm : m ∈ Msub A B V) (hP : ∀ q ∈ pCoreOf 2 A, ⁅m, q⁆ ∈ V) :
    m ∈ centerOf (pCoreOf 2 A) := by
  have hmQ : m ∈ pCoreOf 2 A := (c.mem_M_iff.mp hm).1
  refine ⟨hmQ, Subgroup.mem_centralizer_iff.mpr fun q hq => ?_⟩
  have hm' : g.a⁻¹ * m * g.a⁻¹⁻¹ ∈ Msub A B V := c.M_normal (A.inv_mem g.a_mem) hm
  have hP' : ∀ q' ∈ pCoreOf 2 A, ⁅g.a⁻¹ * m * g.a⁻¹⁻¹, q'⁆ ∈ V := by
    intro q' hq'
    have e := conj_comm g.a⁻¹ m (g.a * q' * g.a⁻¹)
    have hq'' : g.a * q' * g.a⁻¹ ∈ pCoreOf 2 A := pCoreOf_conj_mem g.a_mem hq'
    have e2 : g.a⁻¹ * (g.a * q' * g.a⁻¹) * g.a⁻¹⁻¹ = q' := by group
    rw [e2] at e
    rw [← e]
    exact c.V_normal (A.inv_mem g.a_mem) (hP _ hq'')
  have hs := g.comm_mem_zpowers hm hP q hq
  have hq₂ : g.a⁻¹ * q * g.a⁻¹⁻¹ ∈ pCoreOf 2 A := pCoreOf_conj_mem (A.inv_mem g.a_mem) hq
  have hs' := g.comm_mem_zpowers hm' hP' _ hq₂
  have e := conj_comm g.a⁻¹ m q
  rw [← e] at hs'
  have hs1 : ⁅m, q⁆ = 1 := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hs
    rcases zpow_eq_one_or_self c.hyp.natural.z_sq k with h | h
    · rw [← hk, h]
    · exfalso
      rw [← hk, h] at hs'
      have hz₂ : g.a⁻¹ * z * g.a ∈ Subgroup.zpowers z := by simpa using hs'
      rw [g.ainv_conj_z] at hz₂
      have hz₂' : g.z₂ ∈ Subgroup.zpowers z := hz₂
      obtain ⟨k', hk'⟩ := Subgroup.mem_zpowers_iff.mp hz₂'
      rcases zpow_eq_one_or_self c.hyp.natural.z_sq k' with h5 | h5
      · rw [h5] at hk'; exact g.z₂_ne_one hk'.symm
      · rw [h5] at hk'; exact g.z₂_ne_z hk'.symm
  exact (comm_eq_one_iff.mp hs1).symm

include g in
theorem M_le_V : Msub A B V ≤ V := by
  by_contra hM
  have hVQ : V ≤ pCoreOf 2 A := fun v hv => c.U_le_Q (le_conjClosure V B hv)
  have hMQ : Msub A B V ≤ pCoreOf 2 A := fun m hm => (c.mem_M_iff.mp hm).1
  let Vq : Subgroup ↥(pCoreOf 2 A) := V.subgroupOf (pCoreOf 2 A)
  have hVqN : Vq.Normal := by
    refine ⟨fun n hn x => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := c.conj_V hn x.2
    simpa using this.symm ▸ hn
  have hnil : Group.IsNilpotent (↥(pCoreOf 2 A) ⧸ Vq) :=
    ((pCoreOf_isPGroup 2 A).to_quotient Vq).isNilpotent
  have hMN : ((Msub A B V).subgroupOf (pCoreOf 2 A)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMQ).mpr
      ((pCoreOf_le 2 A).trans c.M_le_normalizer)
  let H : Subgroup (↥(pCoreOf 2 A) ⧸ Vq) :=
    ((Msub A B V).subgroupOf (pCoreOf 2 A)).map (QuotientGroup.mk' Vq)
  have hHN : H.Normal := hMN.map _ (QuotientGroup.mk'_surjective Vq)
  obtain ⟨m₀, hm₀M, hm₀V⟩ : ∃ m ∈ Msub A B V, m ∉ V := by
    by_contra hcon
    push Not at hcon
    exact hM fun m hm => hcon m hm
  have hHne : H ≠ ⊥ := by
    intro hbot
    have hmem : QuotientGroup.mk' Vq ⟨m₀, hMQ hm₀M⟩ ∈ H :=
      Subgroup.mem_map_of_mem _ (by rw [Subgroup.mem_subgroupOf]; exact hm₀M)
    rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf] at hmem
    exact hm₀V hmem
  have hne := Group.IsNilpotent.inf_center_ne_bot_of_normal hHne
  obtain ⟨⟨x, hxH, hxZ⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  obtain ⟨⟨m, hmQ⟩, hmM, rfl⟩ := Subgroup.mem_map.mp hxH
  rw [Subgroup.mem_subgroupOf] at hmM
  have hP : ∀ q' ∈ pCoreOf 2 A, ⁅m, q'⁆ ∈ V := by
    intro q' hq'
    have hc := Subgroup.mem_center_iff.mp hxZ (QuotientGroup.mk' Vq ⟨q', hq'⟩)
    rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq, Subgroup.mem_subgroupOf] at hc
    have hv : (q' * m)⁻¹ * (m * q') ∈ V := by simpa using hc
    have hqm : q' * m ∈ pCoreOf 2 A := (pCoreOf 2 A).mul_mem hq' hmQ
    have e : ⁅m, q'⁆ = (q' * m) * ((q' * m)⁻¹ * (m * q')) * (q' * m)⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e, c.conj_V hv hqm]
    exact hv
  have hmV : m ∈ V := g.centerQ_le_V (g.centerQ_of_Z2 hmM hP)
  apply hx1
  apply Subtype.ext
  show QuotientGroup.mk' Vq ⟨m, hmQ⟩ = 1
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  exact hmV

end Gen

universe u

theorem b3IntersectionInputThree_holds : GoldAmL3K.B3IntersectionInputThree.{u} := by
  intro D _ _ A B z V h hb
  have hU := h.card_conjClosure_eq_eight_of_critDist_eq_three hb
  have c : Ctx A B z V := ⟨h, hU, hb⟩
  obtain ⟨g⟩ := c.nonempty_gen
  exact ⟨g.a, g.a_mem, fun q hq => g.M_le_V (g.inf_conjSub_le_M hq)⟩

end GoldAmL3E

end F6

end CFSG.Quasithin
