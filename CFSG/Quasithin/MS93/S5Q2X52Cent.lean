module

public import CFSG.Quasithin.MS93.S5Q2X52Sp
public import CFSG.Quasithin.MS93.S5Q2X52Coc
public import CFSG.Quasithin.MS93.S33XMain
public import CFSG.Quasithin.MS93.S5BStmt

public noncomputable section

namespace CFSG.Quasithin.MS93.S5Q2.X52

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {F : Type} [Field F] [Fintype F]
  {a : ↥M →* ↥(StatedSp 2 F)}

section Odd

variable (h : PUHyp M T L) (hd : S5.IsSp4Data M T L 1 F a)

include h hd in
theorem relIndex_centralizer_eq {K : Subgroup G} (hKM : K ≤ M)
    (hodd : ¬ S5.imSp a K ≤ commutator (MSP.Sp4 F)) :
    (Subgroup.centralizer (K : Set G)).relIndex (Zq M L) =
      (Subgroup.centralizer (M : Set G)).relIndex (Zq M L) := by
  obtain ⟨g, hg, hgc⟩ := IsConcreteLE.not_le_iff_exists.1 hodd
  obtain ⟨⟨j, hjM⟩, hjK, rfl⟩ := hg
  have he := inf_centralizer_eq_of_not_mem h hd hKM (Subgroup.mem_subgroupOf.1 hjK) hgc
  rw [← Subgroup.inf_relIndex_right, inf_comm, he, inf_comm, Subgroup.inf_relIndex_right]

omit [Fintype F] in
theorem two_le_relIndex_centralizer (hC : ¬ Zq M L ≤ Subgroup.centralizer (M : Set G)) :
    2 ≤ (Subgroup.centralizer (M : Set G)).relIndex (Zq M L) := by
  have h1 : (Subgroup.centralizer (M : Set G)).relIndex (Zq M L) ≠ 1 := fun h1 =>
    hC (Subgroup.relIndex_eq_one.1 h1)
  have h0 : (Subgroup.centralizer (M : Set G)).relIndex (Zq M L) ≠ 0 :=
    Subgroup.index_ne_zero_of_finite
  omega

include h hd in
theorem card_commutator_eq :
    Nat.card ↥⁅Zq M L, M⁆ = (Subgroup.centralizer (M : Set G)).relIndex (Zq M L) := by
  have hNF : Nat.card F = 2 := by rw [Nat.card_eq_fintype_card, hd.2.1, pow_one]
  set v : MSP.V4 F := Pi.single (Sum.inl 0) 1 with hv
  have hv0 : v ≠ 0 := fun h0 => one_ne_zero (congrFun h0 (Sum.inl 0) |>.symm.trans
    (by simp [hv]) |>.symm)
  obtain ⟨σ, hσ⟩ := hd.2.2.1 (MSP.transv v 1)
  have hσo : a σ ∉ commutator (MSP.Sp4 F) := by
    rw [hσ]
    exact MSP.transv_not_mem_commutator_of_card_two hNF hv0 1 one_ne_zero
  have hZn : M ≤ Subgroup.normalizer (Zq M L : Set G) := le_normalizer_Zq h.le_normalizer
  have hσZ : ∀ c ∈ Zq M L, (σ : G) * c * (σ : G)⁻¹ * c⁻¹ ∈ Zq M L := fun c hc =>
    mul_mem ((Subgroup.mem_normalizer_iff.1 (hZn σ.2) c).1 hc) (inv_mem hc)
  let f : ↥(Zq M L) →* ↥(Zq M L) :=
    { toFun := fun c => ⟨(σ : G) * c * (σ : G)⁻¹ * (c : G)⁻¹, hσZ c c.2⟩
      map_one' := by ext; simp
      map_mul' := fun c₁ c₂ => by
        ext
        simp only [Subgroup.coe_mul, MulMemClass.mk_mul_mk]
        have h1 : (σ : G) * c₂ * (σ : G)⁻¹ ∈ Zq M L :=
          (Subgroup.mem_normalizer_iff.1 (hZn σ.2) _).1 c₂.2
        have hc : (c₁ : G)⁻¹ * ((σ : G) * c₂ * (σ : G)⁻¹ * (c₂ : G)⁻¹) =
            ((σ : G) * c₂ * (σ : G)⁻¹ * (c₂ : G)⁻¹) * (c₁ : G)⁻¹ :=
          S5Q2.mul_comm_of_mem_Xq (inv_mem c₁.2).1 (hσZ _ c₂.2).1
        calc (σ : G) * (c₁ * c₂) * (σ : G)⁻¹ * ((c₁ : G) * c₂)⁻¹
            = (σ : G) * c₁ * (σ : G)⁻¹ *
                (((σ : G) * c₂ * (σ : G)⁻¹ * (c₂ : G)⁻¹) * (c₁ : G)⁻¹) := by group
          _ = (σ : G) * c₁ * (σ : G)⁻¹ *
                ((c₁ : G)⁻¹ * ((σ : G) * c₂ * (σ : G)⁻¹ * (c₂ : G)⁻¹)) := by rw [hc]
          _ = _ := by group }
  have hker : f.ker = (Subgroup.centralizer (M : Set G)).subgroupOf (Zq M L) := by
    ext c
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    have he := inf_centralizer_eq_of_not_mem h hd (J := Subgroup.zpowers (σ : G))
      (Subgroup.zpowers_le.2 σ.2) (Subgroup.mem_zpowers _) hσo
    constructor
    · intro h1
      have h2 : (σ : G) * c * (σ : G)⁻¹ * (c : G)⁻¹ = 1 := congrArg Subtype.val h1
      have h3 : (c : G) ∈ Subgroup.centralizer (Subgroup.zpowers (σ : G) : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
        have hcomm : Commute (σ : G) c := by
          rw [Commute, SemiconjBy]
          calc (σ : G) * c = (σ : G) * c * (σ : G)⁻¹ * (c : G)⁻¹ * (c * σ) := by group
            _ = c * σ := by rw [h2, one_mul]
        exact (hcomm.zpow_left n).eq
      have h4 : (c : G) ∈ Zq M L ⊓ Subgroup.centralizer (Subgroup.zpowers (σ : G) : Set G) :=
        ⟨c.2, h3⟩
      rw [he] at h4
      exact h4.2
    · intro h1
      apply Subtype.ext
      show (σ : G) * c * (σ : G)⁻¹ * (c : G)⁻¹ = 1
      rw [Subgroup.mem_centralizer_iff.1 h1 σ σ.2, mul_inv_cancel_right, mul_inv_cancel]
  have hrange : (f.range).map (Zq M L).subtype = ⁅Zq M L, M⁆ := by
    apply le_antisymm
    · rintro _ ⟨_, ⟨c, rfl⟩, rfl⟩
      show (σ : G) * c * (σ : G)⁻¹ * (c : G)⁻¹ ∈ ⁅Zq M L, M⁆
      have := Subgroup.commutator_mem_commutator c.2 σ.2
      rw [commutatorElement_def] at this
      have e : (σ : G) * c * (σ : G)⁻¹ * (c : G)⁻¹ =
          ((c : G) * σ * (c : G)⁻¹ * (σ : G)⁻¹)⁻¹ := by group
      rw [e]
      exact inv_mem this
    · rw [Subgroup.commutator_le]
      intro c hc m hm
      by_cases hmc : a ⟨m, hm⟩ ∈ commutator (MSP.Sp4 F)
      · have hmc' : m * c = c * m := commute_of_mem_commutator h hd hmc hc
        have e : ⁅c, m⁆ = 1 := by
          rw [commutatorElement_def, ← hmc']
          group
        rw [e]
        exact one_mem _
      · have he := conj_eq_of_not_mem h hd hmc hσo (inv_mem hc)
        simp only at he
        refine ⟨f ⟨c⁻¹, inv_mem hc⟩, ⟨_, rfl⟩, ?_⟩
        show (σ : G) * c⁻¹ * (σ : G)⁻¹ * (c⁻¹)⁻¹ = ⁅c, m⁆
        have hcomm : (σ : G) * c⁻¹ * (σ : G)⁻¹ * c = c * ((σ : G) * c⁻¹ * (σ : G)⁻¹) :=
          (S5Q2.mul_comm_of_mem_Xq hc.1
            ((Subgroup.mem_normalizer_iff.1 (hZn σ.2) _).1 (inv_mem hc)).1).symm
        rw [inv_inv, hcomm, ← he, commutatorElement_def]
        group
  have h1 := Subgroup.index_ker f
  rw [hker] at h1
  rw [Subgroup.relIndex, h1, ← hrange]
  exact Subgroup.card_map_of_injective (Zq M L).subtype_injective

end Odd

section Count

variable (h : PUHyp M T L) (hd : S5.IsSp4Data M T L 1 F a)
  (hC : ¬ Zq M L ≤ Subgroup.centralizer (M : Set G)) {K : Subgroup G} (hKM : K ≤ M)
  (hE2 : IsPGroup 2 (S5.imSp a K))
  (hq : MSP.commSp (S5.imSp a K) ≤ MSP.fixSp (S5.imSp a K)) (hE1 : S5.imSp a K ≠ ⊥)
include h hd hC hKM hE2 hq hE1

theorem card_le_relIndex_of_not_le :
    Nat.card (S5.imSp a K) ≤ (Subgroup.centralizer (K : Set G)).relIndex (Xq M) ∧
      ((MSP.IsLine (MSP.fixSp (S5.imSp a K)) ∧
          S5.imSp a K = MSP.qLine (MSP.fixSp (S5.imSp a K)) ⊓ commutator (MSP.Sp4 F)) ∨
        (MSP.IsLine (MSP.fixSp (S5.imSp a K)) ∧
          S5.imSp a K = MSP.qLine (MSP.fixSp (S5.imSp a K)) ∧
          4 * (Subgroup.centralizer (M : Set G)).relIndex (Zq M L) ≤
            (Subgroup.centralizer (K : Set G)).relIndex (Xq M)) ∨
        2 * Nat.card (S5.imSp a K) ≤ (Subgroup.centralizer (K : Set G)).relIndex (Xq M)) := by
  have hF : Fintype.card F = 2 := by simpa using hd.card_eq
  have hNF : Nat.card F = 2 := by rw [Nat.card_eq_fintype_card, hF]
  have hV : Nat.card (MSP.V4 F) = 16 := by rw [MSP.card_V4, hNF]; norm_num
  have : CharP F 2 := hd.charP
  obtain ⟨nv⟩ := hd.nonempty_natVec
  set E := S5.imSp a K with hE
  set c := (Subgroup.centralizer (K : Set G)).relIndex (Zq M L) with hc
  set n := (Subgroup.centralizer (K : Set G)).relIndex (Xq M) with hn
  set r := Nat.card (Set.range (phiK h nv hKM)) with hr
  set f := Nat.card (MSP.fixSp E) with hf
  have hc1 : 1 ≤ c := Nat.one_le_iff_ne_zero.2 Subgroup.index_ne_zero_of_finite
  have hcnt : c * r ≤ n := relIndex_mul_card_range_le h nv hKM
  have hr1 : 16 ≤ f * r := hV ▸ card_le_card_fixSp_mul_card_range h nv hKM
  have hf0 : 0 < f := Nat.card_pos
  have hrn : r ≤ n := le_trans (Nat.le_mul_of_pos_left r hc1) hcnt
  rcases quad_shape hNF hE2 hq hE1 with ⟨hl, hT1⟩ | ⟨hl, hT2⟩ | ⟨hEc, hT3⟩ | ⟨hEo, hT4⟩
  · have hcard : Nat.card E = 4 := by rw [hT1]; exact MSP.card_qLine_inf_commutator hNF hl
    have hf4 : f = 4 := card_eq_four_of_isLine hNF hl
    rw [hf4] at hr1
    refine ⟨by omega, Or.inl ⟨hl, hT1⟩⟩
  · have hcard : Nat.card E = 8 := by rw [hT2, MSP.card_qLine hl, hNF]; norm_num
    have hf4 : f = 4 := card_eq_four_of_isLine hNF hl
    have hodd : ¬ E ≤ commutator (MSP.Sp4 F) := by
      rw [hT2]
      exact MSP.qLine_not_le_commutator hNF hl
    have hcM := relIndex_centralizer_eq h hd hKM hodd
    have hc2 := two_le_relIndex_centralizer hC
    rw [← hcM] at hc2 ⊢
    rw [hf4] at hr1
    have h4 : 4 * c ≤ n := le_trans (by nlinarith) hcnt
    refine ⟨by omega, Or.inr (Or.inl ⟨hl, hT2, h4⟩)⟩
  · have h1 : 2 * Nat.card E ≤ r := by
      have : f * (2 * Nat.card E) ≤ f * r := by nlinarith
      exact Nat.le_of_mul_le_mul_left this hf0
    exact ⟨by omega, Or.inr (Or.inr (by omega))⟩
  · have hc2 : 2 ≤ c := by
      rw [hc, relIndex_centralizer_eq h hd hKM hEo]
      exact two_le_relIndex_centralizer hC
    have h1 : Nat.card E ≤ r := by
      have : f * Nat.card E ≤ f * r := by nlinarith
      exact Nat.le_of_mul_le_mul_left this hf0
    have h2 : 2 * r ≤ n := le_trans (Nat.mul_le_mul_right r hc2) hcnt
    exact ⟨by omega, Or.inr (Or.inr (by omega))⟩

theorem two_mul_card_le_relIndex (hXL : ⁅Xq M, L⁆ ≤ Uq M T L)
    (hne : Xq M ≠ Uq M T L ⊔ Zq M L) :
    2 * Nat.card (S5.imSp a K) ≤ (Subgroup.centralizer (K : Set G)).relIndex (Xq M) := by
  have hF : Fintype.card F = 2 := by simpa using hd.card_eq
  have hNF : Nat.card F = 2 := by rw [Nat.card_eq_fintype_card, hF]
  have hV : Nat.card (MSP.V4 F) = 16 := by rw [MSP.card_V4, hNF]; norm_num
  have : CharP F 2 := hd.charP
  obtain ⟨nv⟩ := hd.nonempty_natVec
  obtain ⟨x, hx, hxN⟩ := exists_mem_xFix_not_mem h hXL hne
  obtain ⟨B, m₀, hB, hform⟩ := exists_cform_of_mem_xFix hd h nv hx hxN
  have hφ := S5.cocSp_mul hd h nv hx.1 hx.2
  set E := S5.imSp a K with hE
  set c := (Subgroup.centralizer (K : Set G)).relIndex (Zq M L) with hc
  set n := (Subgroup.centralizer (K : Set G)).relIndex (Xq M) with hn
  set r := Nat.card (Set.range (phiK h nv hKM)) with hr
  set f := Nat.card (MSP.fixSp E) with hf
  have hc1 : 1 ≤ c := Nat.one_le_iff_ne_zero.2 Subgroup.index_ne_zero_of_finite
  have hcnt : c * r ≤ n := relIndex_mul_card_range_le h nv hKM
  have hr1 : 16 ≤ f * r := hV ▸ card_le_card_fixSp_mul_card_range h nv hKM
  have hf0 : 0 < f := Nat.card_pos
  have hrn : r ≤ n := le_trans (Nat.le_mul_of_pos_left r hc1) hcnt
  have hnc : (E = MSP.qLine (MSP.fixSp E) ⊓ commutator (MSP.Sp4 F) ∨
      E = MSP.qLine (MSP.fixSp E)) → MSP.IsLine (MSP.fixSp E) → 32 ≤ f * r := by
    intro hsh hl
    have key := two_mul_card_le_card_fixSp_mul_card_range h nv hKM hx fun v => by
      obtain ⟨g, hg, hgv⟩ := not_cob_of_shape hF hφ hB hform hl hsh v
      obtain ⟨⟨m, hmM⟩, hmK, rfl⟩ := hg
      rw [S5.cocSp_a hd h nv hx.1 hx.2 hmM] at hgv
      exact ⟨⟨m, Subgroup.mem_subgroupOf.1 hmK⟩, hgv⟩
    rw [hV] at key
    exact key
  rcases quad_shape hNF hE2 hq hE1 with ⟨hl, hT1⟩ | ⟨hl, hT2⟩ | ⟨hEc, hT3⟩ | ⟨hEo, hT4⟩
  · have hcard : Nat.card E = 4 := by rw [hT1]; exact MSP.card_qLine_inf_commutator hNF hl
    have hf4 : f = 4 := card_eq_four_of_isLine hNF hl
    have h32 := hnc (Or.inl hT1) hl
    rw [hf4] at h32
    omega
  · have hcard : Nat.card E = 8 := by rw [hT2, MSP.card_qLine hl, hNF]; norm_num
    have hf4 : f = 4 := card_eq_four_of_isLine hNF hl
    have hodd : ¬ E ≤ commutator (MSP.Sp4 F) := by
      rw [hT2]
      exact MSP.qLine_not_le_commutator hNF hl
    have hc2 : 2 ≤ c := by
      rw [hc, relIndex_centralizer_eq h hd hKM hodd]
      exact two_le_relIndex_centralizer hC
    have h32 := hnc (Or.inr hT2) hl
    rw [hf4] at h32
    have h2 : 2 * r ≤ n := le_trans (Nat.mul_le_mul_right r hc2) hcnt
    omega
  · have h1 : 2 * Nat.card E ≤ r := by
      have : f * (2 * Nat.card E) ≤ f * r := by nlinarith
      exact Nat.le_of_mul_le_mul_left this hf0
    omega
  · have hc2 : 2 ≤ c := by
      rw [hc, relIndex_centralizer_eq h hd hKM hEo]
      exact two_le_relIndex_centralizer hC
    have h1 : Nat.card E ≤ r := by
      have : f * Nat.card E ≤ f * r := by nlinarith
      exact Nat.le_of_mul_le_mul_left this hf0
    have h2 : 2 * r ≤ n := le_trans (Nat.mul_le_mul_right r hc2) hcnt
    omega

end Count

section Amalgam

variable (h : PUHyp M T L)

theorem crit_facts {β : Vtx (puAmalgam h.le)} (hc : IsCritical _ (baseA _) β) :
    XM (puAmalgam h.le) β ≤ stab _ (baseA _) ∧ IsPGroup 2 (XM (puAmalgam h.le) β) ∧
      XM (puAmalgam h.le) (baseA _) ≤ stab _ β ∧ ¬ XM (puAmalgam h.le) β ≤ Qv _ (baseA _) := by
  have h20 := h.hyp20
  have hb := h.critDist_pos
  have hC := h.centHyp
  have hle := xm_le_qv_geo_one _ h20 hb hC hc
  have hadj := adj_geo_one_of_isCritical _ hb hc
  have hc' := ms22_iii _ h20 hb hC hc
  refine ⟨hle.trans (qv_le_stab_of_adj _ hadj.symm),
    (isPGroup_qv _ h20 ((isMVtx_iff_of_adj _ hadj).1 (isMVtx_baseA _))).to_le hle,
    (xm_le_qv_geo_one _ h20 hb hC hc').trans
      (qv_le_stab_of_adj _ (adj_geo_one_of_isCritical _ hb hc').symm),
    fun hle' => hc'.2.2 ((zm_le_xm _ h20 hb (hc.isMVtx_right _ h20)).trans hle')⟩

theorem crit_image {k : ℕ} (hd : S5.IsSp4Data M T L k F a) {β : Vtx (puAmalgam h.le)}
    (hc : IsCritical _ (baseA _) β) :
    IsPGroup 2 (S5.imSp a (S33.pre h.le (XM _ β))) ∧
      MSP.commSp (S5.imSp a (S33.pre h.le (XM _ β))) ≤
        MSP.fixSp (S5.imSp a (S33.pre h.le (XM _ β))) ∧
      S5.imSp a (S33.pre h.le (XM _ β)) ≠ ⊥ ∧
      (Subgroup.centralizer (S33.pre h.le (XM _ β) : Set G)).relIndex (Xq M) ≤
        (Qv _ β).relIndex (XM (puAmalgam h.le) (baseA _)) ∧
      (Qv _ (baseA _)).relIndex (XM (puAmalgam h.le) β) =
        Nat.card (S5.imSp a (S33.pre h.le (XM _ β))) := by
  obtain ⟨hXs, hX2, hXα, hXQ⟩ := crit_facts h hc
  have hvim : S5.vIm h.le a (XM _ β) = S5.imSp a (S33.pre h.le (XM _ β)) :=
    S33.vIm_eq_map_pre h a _
  have hcard := S33.relIndex_qv_baseA_eq_card h hd hXs hX2
  rw [hvim] at hcard
  have hXM : XM (puAmalgam h.le) β ≤ imM h.le M := by rwa [← puAmalgam.stab_baseA]
  refine ⟨hvim ▸ S33.isPGroup_vIm h hX2, ?_, fun hbot => hXQ ?_, ?_, hcard⟩
  · have hnatM : IsSumOfNaturalModulesVia M (Uq M T L) (Uq M T L ⊓ Zq M L) a false 1 := by
      have := hd.2.2.2
      rwa [← h.Uq_inf_Zq] at this
    obtain ⟨-, -, β', hβ', hβker, hβα⟩ := id hnatM
    have hAβ := S33.isCoordAct_of_natSp hβα
    refine S33.commSp_le_fixSp_of_quadratic h le_rfl hβ' hβker hAβ (S33.pre_le h.le _) ?_ ?_
    · intro x hx y hy
      obtain ⟨m, hm, rfl⟩ := (S33.mem_pre_iff' h.le).1 hx
      obtain ⟨m', hm', rfl⟩ := (S33.mem_pre_iff' h.le).1 hy
      have hc := (isMulCommutative_subgroup_iff.mp (isElemAbelian_xm _ β).1) _ hm _ hm'
      have : m * m' = m' * m :=
        (puAmalgam h.le).ofA_injective (by rw [map_mul, map_mul]; exact hc)
      exact congrArg Subtype.val this
    · rw [Subgroup.commutator_le]
      intro u hu e he
      obtain ⟨m, hm, rfl⟩ := (S33.mem_pre_iff' h.le).1 he
      have huM : u ∈ M := (Xq_le M) (h.Uq_le_Xq hu)
      have huX : (puAmalgam h.le).ofA ⟨u, huM⟩ ∈ XM (puAmalgam h.le) (baseA _) := by
        rw [puAmalgam.xm_baseA, h.normalCoreIn_eq]
        exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 (h.Uq_le_Xq hu))
      have hn := stab_le_normalizer_xm _ β (hXα huX)
      have hcM : ⁅u, (m : G)⁆ ∈ M := by
        rw [commutatorElement_def]
        exact M.mul_mem (M.mul_mem (M.mul_mem huM m.2) (M.inv_mem huM)) (M.inv_mem m.2)
      refine (S33.mem_pre_iff' h.le).2 ⟨⟨⁅u, (m : G)⁆, hcM⟩, ?_, rfl⟩
      have e : (⟨⁅u, (m : G)⁆, hcM⟩ : ↥M) = ⟨u, huM⟩ * m * (⟨u, huM⟩ : ↥M)⁻¹ * m⁻¹ :=
        Subtype.ext (commutatorElement_def _ _)
      rw [e, map_mul, map_mul, map_mul, map_inv, map_inv]
      exact mul_mem ((Subgroup.mem_normalizer_iff.1 hn _).1 hm) (inv_mem hm)
  · rw [hbot, Subgroup.card_bot] at hcard
    exact Subgroup.relIndex_eq_one.1 hcard
  · have e : (Subgroup.centralizer (S33.pre h.le (XM _ β) : Set G)).relIndex (Xq M) =
        (Subgroup.centralizer (XM (puAmalgam h.le) β : Set _)).relIndex
          (XM (puAmalgam h.le) (baseA _)) := by
      rw [puAmalgam.xm_baseA, h.normalCoreIn_eq,
        ← S33.relIndex_centralizer_imM h.le (Xq_le M) (S33.pre_le h.le _), S33.imM_pre h.le hXM]
    rw [e]
    have : Finite ↥(XM (puAmalgam h.le) (baseA _)) := by
      rw [puAmalgam.xm_baseA]
      exact S33.finite_imM_of_finite h.le _
    exact Subgroup.relIndex_le_of_le_left (qv_le_centralizer_xm _ β)
      Subgroup.index_ne_zero_of_finite

theorem exists_partner {α' : Vtx (puAmalgam h.le)} (hc : IsCritical _ (baseA _) α') :
    ∃ μ, IsCritical (puAmalgam h.le) (baseA _) μ ∧
      (Qv _ α').relIndex (XM (puAmalgam h.le) (baseA _)) =
        (Qv _ (baseA _)).relIndex (XM (puAmalgam h.le) μ) ∧
      (Qv _ μ).relIndex (XM (puAmalgam h.le) (baseA _)) =
        (Qv _ (baseA _)).relIndex (XM (puAmalgam h.le) α') := by
  have h20 := h.hyp20
  have hb := h.critDist_pos
  have hC := h.centHyp
  obtain ⟨g, hgα, -, hμ, -⟩ := S33.exists_conj_of_isCritical _ h20 hb hc
  have hgμ : g • (g⁻¹ • baseA (puAmalgam h.le)) = baseA (puAmalgam h.le) := smul_inv_smul g _
  have hconj : ∀ H K : Subgroup (puAmalgam h.le).Universal,
      (H.map (MulAut.conj g).toMonoidHom).relIndex (K.map (MulAut.conj g).toMonoidHom) =
        H.relIndex K := fun H K =>
    Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective
  refine ⟨g⁻¹ • baseA _, ms22_iii _ h20 hb hC hμ, ?_, ?_⟩
  · rw [← hconj (Qv _ (baseA _)) (XM _ (g⁻¹ • baseA _)), ← qv_smul, ← xm_smul, hgα, hgμ]
  · rw [← hconj (Qv _ (g⁻¹ • baseA _)) (XM _ (baseA _)), ← qv_smul, ← xm_smul, hgμ, hgα]

end Amalgam

section Main

theorem zq_le_centralizer_of_ne (h : PUHyp M T L) (hd : S5.IsSp4Data M T L 1 F a)
    (hXL : ⁅Xq M, L⁆ ≤ Uq M T L)
    (hne : Xq M ≠ Uq M T L ⊔ Zq M L) : Zq M L ≤ Subgroup.centralizer (M : Set G) := by
  by_contra hC
  obtain ⟨α', hc, -⟩ := exists_isCritical_geo _ h.hyp20 h.critDist_pos (isMVtx_baseA _)
    (adj_baseA_baseB (puAmalgam h.le))
  obtain ⟨μ, hcμ, e2, e3⟩ := exists_partner h hc
  obtain ⟨hE2, hq, hE1, hidx, hcard⟩ := crit_image h hd hc
  obtain ⟨hE2', hq', hE1', hidx', hcard'⟩ := crit_image h hd hcμ
  have h1 := two_mul_card_le_relIndex h hd hC (S33.pre_le h.le _) hE2 hq hE1 hXL hne
  have h2 := two_mul_card_le_relIndex h hd hC (S33.pre_le h.le _) hE2' hq' hE1' hXL hne
  have hpos : 0 < Nat.card (S5.imSp a (S33.pre h.le (XM (puAmalgam h.le) μ))) := Nat.card_pos
  omega

theorem shape_of_not_le (h : PUHyp M T L) (hd : S5.IsSp4Data M T L 1 F a)
    (hC : ¬ Zq M L ≤ Subgroup.centralizer (M : Set G)) {α' : Vtx (puAmalgam h.le)}
    (hc : IsCritical _ (baseA _) α') :
    (Qv _ α').relIndex (XM (puAmalgam h.le) (baseA _)) = Nat.card (S5.vIm h.le a (XM _ α')) ∧
      ∃ l, MSP.IsLine l ∧
        ((S5.vIm h.le a (XM _ α') = MSP.qLine l ⊓ commutator (MSP.Sp4 F) ∧
            S5.vIm h.le a (ZM _ α') = S5.vIm h.le a (XM _ α')) ∨
          (S5.vIm h.le a (XM _ α') = MSP.qLine l ∧ Nat.card ↥⁅Zq M L, M⁆ = 2)) := by
  have hNF : Nat.card F = 2 := by
    rw [Nat.card_eq_fintype_card]
    simpa using hd.card_eq
  obtain ⟨μ, hcμ, e2, e3⟩ := exists_partner h hc
  obtain ⟨hE2, hq, hE1, hidx, hcard⟩ := crit_image h hd hc
  obtain ⟨hE2', hq', hE1', hidx', hcard'⟩ := crit_image h hd hcμ
  obtain ⟨h1, hsh⟩ := card_le_relIndex_of_not_le h hd hC (S33.pre_le h.le _) hE2 hq hE1
  obtain ⟨h2, -⟩ := card_le_relIndex_of_not_le h hd hC (S33.pre_le h.le _) hE2' hq' hE1'
  have hv : S5.vIm h.le a (XM _ α') = S5.imSp a (S33.pre h.le (XM (puAmalgam h.le) α')) :=
    S33.vIm_eq_map_pre h a _
  have hpos : 0 < Nat.card (S5.imSp a (S33.pre h.le (XM (puAmalgam h.le) α'))) := Nat.card_pos
  have hc2 := two_le_relIndex_centralizer hC
  refine ⟨by rw [hv]; omega, ?_⟩
  rw [hv]
  rcases hsh with ⟨hl, hT⟩ | ⟨hl, hT, h4⟩ | h3
  · refine ⟨_, hl, Or.inl ⟨hT, ?_⟩⟩
    obtain ⟨hXs, hX2, -, -⟩ := crit_facts h hc
    have hZX : ZM (puAmalgam h.le) α' ≤ XM _ α' :=
      zm_le_xm _ h.hyp20 h.critDist_pos (hc.isMVtx_right _ h.hyp20)
    have hZle : S5.vIm h.le a (ZM _ α') ≤ S5.vIm h.le a (XM _ α') :=
      Subgroup.map_mono (Subgroup.comap_mono hZX)
    rw [hv] at hZle
    have hcard4 : Nat.card (S5.imSp a (S33.pre h.le (XM (puAmalgam h.le) α'))) = 4 := by
      rw [hT]
      exact MSP.card_qLine_inf_commutator hNF hl
    rcases S33.shape_of_sp4Data h hd hc with ⟨-, -, p, hp, hpZ⟩ | ⟨-, h4Z, -⟩
    · exfalso
      refine MSP.xPoint_not_le_commutator hNF hp ?_
      rw [← hpZ]
      exact hZle.trans (hT ▸ inf_le_right)
    · refine Subgroup.eq_of_le_of_card_ge hZle ?_
      rw [hcard4, ← S33.relIndex_qv_baseA_eq_card h hd (hZX.trans hXs) (hX2.to_le hZX)]
      simpa using h4Z
  · refine ⟨_, hl, Or.inr ⟨hT, ?_⟩⟩
    have hcard8 : Nat.card (S5.imSp a (S33.pre h.le (XM (puAmalgam h.le) α'))) = 8 := by
      rw [hT, MSP.card_qLine hl, hNF]
      norm_num
    rw [card_commutator_eq h hd]
    omega
  · omega

theorem vIm_qv_baseB_ne_qPoint (h : PUHyp M T L) (hd : S5.IsSp4Data M T L 1 F a)
    (hC : ¬ Zq M L ≤ Subgroup.centralizer (M : Set G)) {p : Submodule F (MSP.V4 F)}
    (hp : MSP.IsPoint p) : S5.vIm h.le a (Qv _ (baseB (puAmalgam h.le))) ≠ MSP.qPoint p := by
  have hNF : Nat.card F = 2 := by
    rw [Nat.card_eq_fintype_card]
    simpa using hd.card_eq
  intro heq
  obtain ⟨α', hc, hgeo⟩ := exists_isCritical_geo _ h.hyp20 h.critDist_pos (isMVtx_baseA _)
    (adj_baseA_baseB (puAmalgam h.le))
  have hXQ : XM (puAmalgam h.le) α' ≤ Qv _ (baseB _) :=
    hgeo ▸ xm_le_qv_geo_one _ h.hyp20 h.critDist_pos h.centHyp hc
  have hle : S5.vIm h.le a (XM _ α') ≤ MSP.qPoint p :=
    heq ▸ Subgroup.map_mono (Subgroup.comap_mono hXQ)
  obtain ⟨-, l, hl, hsh⟩ := shape_of_not_le h hd hC hc
  rcases hsh with ⟨hT, -⟩ | ⟨hT, -⟩
  · exact qLine_inf_commutator_not_le_qPoint hNF hl hp (hT ▸ hle)
  · exact qLine_not_le_qPoint hl hp (hT ▸ hle)

end Main

end CFSG.Quasithin.MS93.S5Q2.X52

namespace CFSG.Quasithin.MS93.S5Q2

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

@[expose] def Q2CentUC : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L),
    PUMin M T L → 2 < critDist (puAmalgam h.le) →
    ∀ (F : Type) (_ : Field F) (_ : Fintype F) (a : ↥M →* ↥(StatedSp 2 F)),
      S5.IsSp4Data M T L 1 F a → Xq M = Uq M T L ⊔ Zq M L →
      (∀ p : Submodule F (MSP.V4 F), MSP.IsPoint p →
        S5.vIm h.le a (Qv _ (baseB (puAmalgam h.le))) ≠ MSP.qPoint p) →
      (∀ α' : Vtx (puAmalgam h.le), IsCritical _ (baseA _) α' →
        (Qv _ α').relIndex (XM (puAmalgam h.le) (baseA _)) =
            Nat.card (S5.vIm h.le a (XM _ α')) ∧
          ∃ l : Submodule F (MSP.V4 F), MSP.IsLine l ∧
            ((S5.vIm h.le a (XM _ α') = MSP.qLine l ⊓ commutator (MSP.Sp4 F) ∧
                S5.vIm h.le a (ZM _ α') = S5.vIm h.le a (XM _ α')) ∨
              (S5.vIm h.le a (XM _ α') = MSP.qLine l ∧ Nat.card ↥⁅Zq M L, M⁆ = 2))) →
      Zq M L ≤ Subgroup.centralizer (M : Set G)

theorem q2Cent_of_q2CentUC (h32 : S32) (H : Q2CentUC) : S5B.Q2Cent := by
  intro G _ _ M T L h hmin hb F _ _ a hd
  by_cases hXU : Xq M = Uq M T L ⊔ Zq M L
  · by_contra hC
    exact hC (H G M T L h hmin hb F _ _ a hd hXU
      (fun p hp => X52.vIm_qv_baseB_ne_qPoint h hd hC hp)
      fun α' hc => X52.shape_of_not_le h hd hC hc)
  · exact X52.zq_le_centralizer_of_ne h hd (h32 G M T L h).2.1 hXU

end CFSG.Quasithin.MS93.S5Q2
