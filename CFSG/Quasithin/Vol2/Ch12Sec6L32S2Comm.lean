module

public import CFSG.Quasithin.Vol2.Ch12Sec6L32S2Defs
public import CFSG.Quasithin.Vol2.Ch12Sec6L33g

public section

namespace CFSG.Quasithin.H13.L1232S2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits S126 S126P S126L1a
  S126L24 F126 L1232 Equiv CFSG.Quasithin.H13.L1233

variable {G : Type} [Group G] [Finite G]

section Comm

variable {T L V H K : Subgroup G} [IsMulCommutative ↥V]

theorem tilde_commutator_eq_of_L1 (F : Frame126 T L V) (h918 : HypF918 T V L F.V1 F.V5 H K)
    (hL1 : ∀ l ∈ Li L F.V1, ∀ hl : l ∈ H,
      (QuotientGroup.mk ⟨l, hl⟩ : S126.HStar H) ∈ S126.star H (conjClosure K T)) :
    tildeOf F.V1 ⁅conjClosure F.V5 H, conjClosure K T⁆ = tildeOf F.V1 (conjClosure F.V5 H) := by
  have h := h918.toHypF98.toHypF91
  have hUN : conjClosure F.V5 H ≤ N1 F.V1 :=
    h.conjClosure_Vp_le_pCoreOf.trans ((pCoreOf_le 2 H).trans (le_N1 h))
  have hVN : F.V5 ≤ N1 F.V1 := (le_conjClosure F.V5 H).trans hUN
  have hK₀H : conjClosure K T ≤ H := h918.K₀_le_H
  have hHV₁ : H ≤ Subgroup.normalizer (F.V1 : Set G) := le_N1 h
  have hCU : ⁅conjClosure F.V5 H, conjClosure K T⁆ ≤ conjClosure F.V5 H :=
    commutator_le_conjClosure le_rfl hK₀H
  have hCN : H ≤
      Subgroup.normalizer ((⁅conjClosure F.V5 H, conjClosure K T⁆ : Subgroup G) : Set G) :=
    fun x hx =>
      mem_normalizer_commutator (le_normalizer_conjClosure F.V5 H hx) (h918.K₀_normal hx)
  have hkey : ∀ l ∈ Li L F.V1, ∀ v ∈ F.V5,
      l * v * l⁻¹ * v⁻¹ ∈ ⁅conjClosure F.V5 H, conjClosure K T⁆ ⊔ F.V1 := by
    intro l hl v hv
    have hlH : l ∈ H := h.L₁T_le_H (Subgroup.mem_sup_left hl)
    obtain ⟨⟨k, hkH⟩, hkK, hke⟩ := hL1 l hl hlH
    have hq := mem_pCoreOf_of_mk_eq hke
    set q := k⁻¹ * l with hqd
    have hvU : v ∈ conjClosure F.V5 H := le_conjClosure F.V5 H hv
    have hz : q * v * q⁻¹ * v⁻¹ ∈ F.V1 := by
      have := F.V1.inv_mem (h.commutator_conjClosure_le v hvU q hq)
      have e : (v * q * v⁻¹ * q⁻¹)⁻¹ = q * v * q⁻¹ * v⁻¹ := by group
      rwa [e] at this
    have hkz : k * (q * v * q⁻¹ * v⁻¹) * k⁻¹ = q * v * q⁻¹ * v⁻¹ := by
      have := Subgroup.mem_centralizer_iff.1 (h.H_le_centralizer hkH) _ hz
      rw [← this, mul_inv_cancel_right]
    have hc : k * v * k⁻¹ * v⁻¹ ∈ ⁅conjClosure F.V5 H, conjClosure K T⁆ := by
      rw [Subgroup.commutator_comm]
      have := Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.1 hkK) hvU
      rwa [commutatorElement_def] at this
    have e : l * v * l⁻¹ * v⁻¹ = (k * (q * v * q⁻¹ * v⁻¹) * k⁻¹) * (k * v * k⁻¹ * v⁻¹) := by
      rw [hqd]
      group
    rw [e, hkz]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hz) (Subgroup.mem_sup_left hc)
  have hW'N : Li L F.V1 ⊔ T ≤ Subgroup.normalizer
      ((F.V5 ⊓ (⁅conjClosure F.V5 H, conjClosure K T⁆ ⊔ F.V1) : Subgroup G) : Set G) :=
    fun g hg => mem_normalizer_inf (h.L₁T_normalizes_Vp hg)
      (mem_normalizer_sup (hCN (h.L₁T_le_H hg)) (hHV₁ (h.L₁T_le_H hg)))
  rcases h.irred _ (le_inf h.V₁_le_Vp le_sup_right) inf_le_left hW'N with hW | hW
  ·
    exfalso
    obtain ⟨l, hlL1, hlV, hl⟩ := S126L1b.exists_mem_L1 F aP_mem aP_pow_three aP_block
    have hA : ActEq aP 1 := by
      refine actEq_of_conj F hlV (Subgroup.one_mem _) hl (ActsAs.one F) fun v hv => ?_
      have hl5 : l * v * l⁻¹ ∈ F.V5 :=
        (Subgroup.mem_normalizer_iff.1 (h.L₁T_normalizes_Vp (Subgroup.mem_sup_left hlL1)) v).1 hv
      have h1 : l * v * l⁻¹ * v⁻¹ ∈ F.V1 := by
        rw [← hW]
        exact ⟨F.V5.mul_mem hl5 (F.V5.inv_mem hv), hkey l hlL1 v hv⟩
      have hvV : v ∈ V := h.Vp_le_V hv
      have key : ∀ a ∈ V, a * v⁻¹ ∈ F.V1 → a⁻¹ * (1 * v * 1⁻¹) ∈ F.V1 := fun a haV ha => by
        have e : a⁻¹ * (1 * v * 1⁻¹) = (a * v⁻¹)⁻¹ := by
          rw [one_mul, inv_one, mul_one, mul_inv_rev, inv_inv]
          exact S126L1b.comm_of_mem (V.inv_mem haV) hvV
        rw [e]
        exact F.V1.inv_mem ha
      exact key _ (h.Vp_le_V hl5) h1
    have := indep_ab (i := 1) (j := 0) (by simpa using hA)
    exact absurd this.1 (by decide)
  ·
    have hVS : ∀ w : ↥(UT F.V1 F.V5 H), (w : SecQuot (N1 F.V1) F.V1) ∈ tildeOf F.V1 F.V5 →
        w ∈ (tildeOf F.V1 ⁅conjClosure F.V5 H, conjClosure K T⁆).subgroupOf (UT F.V1 F.V5 H) := by
      intro w hw
      rw [Subgroup.mem_subgroupOf]
      obtain ⟨⟨v, hvN⟩, hv5, hvw⟩ := mem_secImg.1 hw
      have hv' : v ∈ F.V5 ⊓ (⁅conjClosure F.V5 H, conjClosure K T⁆ ⊔ F.V1) := by
        rw [hW]
        exact hv5
      have hv : v ∈ ⁅conjClosure F.V5 H, conjClosure K T⁆ ⊔ F.V1 := hv'.2
      rw [← hvw]
      have hsup : tildeOf F.V1 (⁅conjClosure F.V5 H, conjClosure K T⁆ ⊔ F.V1) =
          tildeOf F.V1 ⁅conjClosure F.V5 H, conjClosure K T⁆ := by
        have e1 : tildeOf F.V1 (⁅conjClosure F.V5 H, conjClosure K T⁆ ⊔ F.V1) =
            tildeOf F.V1 ⁅conjClosure F.V5 H, conjClosure K T⁆ ⊔ tildeOf F.V1 F.V1 := by
          show ((⁅conjClosure F.V5 H, conjClosure K T⁆ ⊔ F.V1).subgroupOf (N1 F.V1)).map
            (secMk (N1 F.V1) F.V1) = _
          rw [Subgroup.subgroupOf_sup (hCU.trans hUN) Subgroup.le_normalizer, Subgroup.map_sup]
          rfl
        rw [e1, tildeOf_eq_bot_of_le le_rfl, sup_bot_eq]
      rw [← hsup]
      exact secMk_mem_secImg hv
    have hinv : ∀ x : ↥H, ∀ s ∈ (tildeOf F.V1 ⁅conjClosure F.V5 H, conjClosure K T⁆).subgroupOf
        (UT F.V1 F.V5 H), thetaH h x s ∈
          (tildeOf F.V1 ⁅conjClosure F.V5 H, conjClosure K T⁆).subgroupOf (UT F.V1 F.V5 H) := by
      intro x s hs
      rw [Subgroup.mem_subgroupOf] at hs ⊢
      obtain ⟨⟨c, hcN⟩, hcC, hcs⟩ := mem_secImg.1 hs
      rw [thetaH_apply, ← hcs, thetaH_apply_secMk]
      exact secMk_mem_secImg ((Subgroup.mem_normalizer_iff.1 (hCN x.2) c).1 hcC)
    have htop := eq_top_of_le h _ hVS hinv
    apply le_antisymm (secImg_mono hCU)
    intro y hy
    have : (⟨y, hy⟩ : ↥(UT F.V1 F.V5 H)) ∈
        (tildeOf F.V1 ⁅conjClosure F.V5 H, conjClosure K T⁆).subgroupOf (UT F.V1 F.V5 H) := by
      rw [htop]
      exact Subgroup.mem_top _
    exact this

end Comm

theorem leafComm_holds : LeafComm := by
  intro G _ _ T L V _ F H K h hL1
  exact tilde_commutator_eq_of_L1 F h hL1

end CFSG.Quasithin.H13.L1232S2
