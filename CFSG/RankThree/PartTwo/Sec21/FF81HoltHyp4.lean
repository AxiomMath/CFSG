module

public import CFSG.RankThree.PartTwo.Sec21.FF81Defs
import CFSG.RankThree.PartTwo.Sec21.FF81Step0
import CFSG.RankThree.PartTwo.Sec21.FF81KFacts
import CFSG.RankThree.PartTwo.Sec21.FF81Fusion
import CFSG.RankThree.PartTwo.Sec21.FF81Prop51
import CFSG.RankThree.PartTwo.Sec21.FF81J
import CFSG.LocalAnalysis.StandardType.GGSixFusion
import CFSG.ClassicalGroups.Symplectic.Simple
import CFSG.Timmesfeld.Orders.Classical
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition84Residual

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79

section Helpers

variable {G : Type} [Group G] [Finite G]

theorem cen_conj (y x : G) : Cen (y * x * y⁻¹) = conjBy y (Cen x) := by
  ext z
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  simp only [MulEquiv.symm_apply_eq, MulAut.conj_symm_apply, MulAut.conj_apply]
  constructor
  · intro h
    calc y⁻¹ * z * y * x = y⁻¹ * (z * (y * x * y⁻¹)) * y := by group
      _ = y⁻¹ * ((y * x * y⁻¹) * z) * y := by rw [h]
      _ = x * (y⁻¹ * z * y) := by group
  · intro h
    calc z * (y * x * y⁻¹) = y * ((y⁻¹ * z * y) * x) * y⁻¹ := by group
      _ = y * (x * (y⁻¹ * z * y)) * y⁻¹ := by rw [h]
      _ = y * x * y⁻¹ * z := by group

theorem cen_le_cen_of_mem_zpowers {u x : G} (hx : x ∈ Subgroup.zpowers u) : Cen u ≤ Cen x := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  intro z hz
  rw [Subgroup.mem_centralizer_singleton_iff] at hz ⊢
  exact (Commute.zpow_right hz k).eq

theorem inSubgroup_conj_mem {H : Subgroup G} {K : Subgroup H} (hK : K.Normal) {g o : G}
    (hg : g ∈ H) (ho : o ∈ K.map H.subtype) : g * o * g⁻¹ ∈ K.map H.subtype := by
  obtain ⟨o', ho', rfl⟩ := ho
  exact ⟨⟨g, hg⟩ * o' * ⟨g, hg⟩⁻¹, hK.conj_mem o' ho' ⟨g, hg⟩, by simp⟩

theorem exists_conjBy_le_sylow {p : ℕ} [Fact p.Prime] {H A : Subgroup G} (hAH : A ≤ H)
    (hA : IsPGroup p A) (Q : Sylow p H) :
    ∃ c ∈ H, conjBy c A ≤ (Q : Subgroup H).map H.subtype := by
  obtain ⟨Q₁, hQ₁⟩ := (hA.comap_of_injective H.subtype Subtype.coe_injective).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H Q₁ Q
  refine ⟨g, g.2, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hx' : (⟨x, hAH hx⟩ : H) ∈ (Q₁ : Subgroup H) := hQ₁ (Subgroup.mem_comap.mpr hx)
  have : MulAut.conj g • (⟨x, hAH hx⟩ : H) ∈ (Q : Subgroup H) := by
    rw [← hg, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ hx'
  exact ⟨_, this, rfl⟩

theorem exists_isSylowOf_le {p : ℕ} [Fact p.Prime] {Y R : Subgroup G} (hRY : R ≤ Y)
    (hR : IsPGroup p R) : ∃ Q : Subgroup G, IsSylowOf p Q Y ∧ R ≤ Q := by
  obtain ⟨Q, hQ⟩ := (hR.comap_of_injective Y.subtype Subtype.coe_injective).exists_le_sylow
  refine ⟨(Q : Subgroup Y).map Y.subtype, ⟨Subgroup.map_subtype_le _, Q.isPGroup'.map _, ?_⟩,
    fun x hx => ⟨⟨x, hRY hx⟩, hQ (Subgroup.mem_comap.mpr hx), rfl⟩⟩
  show Nat.Coprime p ((((Q : Subgroup Y).map Y.subtype).subgroupOf Y).index)
  rw [show ((Q : Subgroup Y).map Y.subtype).subgroupOf Y = Q from
    Subgroup.comap_map_eq_self_of_injective Subtype.coe_injective _]
  exact (Nat.Prime.coprime_iff_not_dvd Fact.out).mpr Q.not_dvd_index

theorem exists_conjBy_eq_of_unique {Y H A₁ A₂ : Subgroup G}
    (hS1 : ∀ Q : Subgroup G, IsSylowOf 3 Q Y → ∀ B₁ B₂ : Subgroup G, B₁ ≤ Q → B₂ ≤ Q →
      IsElemAb 3 4 B₁ → IsElemAb 3 4 B₂ → B₁ = B₂)
    (hHY : H ≤ Y) (h₁ : A₁ ≤ H) (h₂ : A₂ ≤ H) (e₁ : IsElemAb 3 4 A₁) (e₂ : IsElemAb 3 4 A₂) :
    ∃ c ∈ H, conjBy c A₁ = A₂ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q, hQ⟩ := ((IsPGroup.of_card e₂.2).comap_of_injective H.subtype
    Subtype.coe_injective).exists_le_sylow
  obtain ⟨c, hc, hcA⟩ := exists_conjBy_le_sylow h₁ (IsPGroup.of_card e₁.2) Q
  have h₂R : A₂ ≤ (Q : Subgroup H).map H.subtype := fun x hx =>
    ⟨⟨x, h₂ hx⟩, hQ (Subgroup.mem_comap.mpr hx), rfl⟩
  obtain ⟨Q', hQ', hRQ'⟩ := exists_isSylowOf_le ((Subgroup.map_subtype_le _).trans hHY)
    (Q.isPGroup'.map H.subtype)
  exact ⟨c, hc, hS1 Q' hQ' _ _ (hcA.trans hRQ') (h₂R.trans hRQ') (isElemAb_conjBy e₁ c) e₂⟩

theorem conj_commute {a u v : G} (h : u * v = v * u) :
    a * u * a⁻¹ * (a * v * a⁻¹) = a * v * a⁻¹ * (a * u * a⁻¹) := by
  calc a * u * a⁻¹ * (a * v * a⁻¹) = a * (u * v) * a⁻¹ := by group
    _ = a * (v * u) * a⁻¹ := by rw [h]
    _ = a * v * a⁻¹ * (a * u * a⁻¹) := by group

end Helpers

section Basis

variable {G : Type} [Group G] [Finite G] {b : G} {L B : Subgroup G} {b₁ b₂ b₃ : G}

theorem FF81Basis.card_L (hB : FF81Basis b L B b₁ b₂ b₃) : Nat.card L = 1451520 := by
  rw [(CFSG.Timmesfeld.card_statedClassicalModel_two hB.hyp.model).2.2.1 rfl]
  norm_num [CFSG.Open.ordBC, Finset.prod_Icc_succ_top]

theorem FF81Basis.cen_eq_sup (hB : FF81Basis b L B b₁ b₂ b₃) (h0 : Opp 3 (Cen b) = ⊥) :
    Cen b = Subgroup.zpowers b ⊔ L := by
  refine le_antisymm (fun x hx => ?_) (sup_le (Subgroup.zpowers_le.mpr
    (Subgroup.mem_centralizer_singleton_iff.mpr rfl)) hB.hyp.hLC)
  obtain ⟨l, hlL, hl⟩ := kf_sp62Out G L hB.hyp.model x (hB.hyp.hLN hx)
  have hdL : l⁻¹ * x ∈ CenS L := Subgroup.mem_centralizer_iff.mpr fun y hy => by
    have := hl y hy
    calc y * (l⁻¹ * x) = l⁻¹ * (l * y * l⁻¹) * x := by group
      _ = l⁻¹ * (x * y * x⁻¹) * x := by rw [this]
      _ = l⁻¹ * x * y := by group
  have hdb : l⁻¹ * x ∈ Cen b := (Cen b).mul_mem ((Cen b).inv_mem (hB.hyp.hLC hlL)) hx
  have hd : l⁻¹ * x ∈ Subgroup.zpowers b := by
    rw [← hB.cen_inf_cenS_eq h0]; exact ⟨hdb, hdL⟩
  have : x = l * (l⁻¹ * x) := by group
  rw [this]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hlL) (Subgroup.mem_sup_left hd)

theorem FF81Basis.card_cen (hB : FF81Basis b L B b₁ b₂ b₃) (h0 : Opp 3 (Cen b) = ⊥) :
    Nat.card (Cen b) = 2 ^ 9 * 3 ^ 5 * 5 * 7 := by
  have hN : Subgroup.zpowers b ≤ Subgroup.normalizer (L : Set G) :=
    Subgroup.zpowers_le.mpr (hB.hyp.hLN (Subgroup.mem_centralizer_singleton_iff.mpr rfl))
  have e := card_sup_mul_card_inf _ _ hN
  have hbL : Subgroup.zpowers b ≤ CenS L := Subgroup.zpowers_le.mpr
    (Subgroup.mem_centralizer_iff.mpr fun y hy =>
      Subgroup.mem_centralizer_singleton_iff.mp (hB.hyp.hLC hy))
  have hinf : Subgroup.zpowers b ⊓ L = ⊥ := by
    refine eq_bot_iff.mpr fun x hx => ?_
    rw [← hB.inf_cenS_self]; exact ⟨hx.2, hbL hx.1⟩
  rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, hB.hyp.ord, hB.card_L,
    ← hB.cen_eq_sup h0] at e
  rw [e]; norm_num

variable {t₀ : G}

theorem FF81Sec4.mem_conjLines (h4 : FF81Sec4 b L B b₁ b₂ b₃ t₀) :
    Subgroup.zpowers b₁ ∈ ConjLines B b ∧ Subgroup.zpowers b₂ ∈ ConjLines B b ∧
      Subgroup.zpowers b₃ ∈ ConjLines B b := by
  rw [h4.caseI.2]; simp

theorem orderOf_of_mem_conjLines (hb : orderOf b = 3) {x : G}
    (hx : Subgroup.zpowers x ∈ ConjLines B b) : orderOf x = 3 := by
  obtain ⟨-, g, hg⟩ := hx
  rw [← Nat.card_zpowers, ← hg, Subgroup.card_map_of_injective (MulAut.conj g).injective,
    Nat.card_zpowers, hb]

end Basis

theorem ff81_holtHyp4 : FF81_holtHyp4 := by
  intro hSp G _ _ b L B b₁ b₂ b₃ t₀ h4 h42 h43 h44 hYm h411
  obtain ⟨-, hBY, hNY, hfusY⟩ := h411
  have hB := h4.basis
  set Y := Y4 b₃ t₀ with hYdef
  obtain ⟨hS1, -, hS3, hS4, hS5, hS6, hS7⟩ := hSp G Y hYm
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hB4 := hB.mono.1
  obtain ⟨hbB, hb1B, hb2B, hb3B⟩ := hB.mem
  have hb3 := hB.hyp.ord
  have hcomm := comm_of_isElemAb hB4
  have ht₀2 : t₀ * t₀ = 1 := by
    have := pow_orderOf_eq_one t₀
    rwa [h4.ht₀, sq] at this
  have ht₀inv : t₀⁻¹ = t₀ := inv_eq_of_mul_eq_one_right ht₀2
  have hLt : L ≤ Cen t₀ := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp h4.ht₀L x hx)
  have hCtY : Cen t₀ ≤ Y := by
    show Cen t₀ ≤ Cen t₀ ⊔ OUpp 2 (Cen b₃); exact le_sup_left
  have hLY : L ≤ Y := hLt.trans hCtY
  have hbY : b ∈ Y := hBY hbB
  have hCb := hB.cen_eq_sup h44
  have hCbY : Cen b ≤ Y := by rw [hCb]; exact sup_le (Subgroup.zpowers_le.mpr hbY) hLY
  have hCbcard := hB.card_cen h44
  have hconj : ∀ x : G, Subgroup.zpowers x ∈ ConjLines B b →
      Cen x ≤ Y ∧ Nat.card ↥(Y ⊓ Cen x) = 2 ^ 9 * 3 ^ 5 * 5 * 7 := by
    intro x hx
    obtain ⟨hxB, g, hg⟩ := hx
    have hgb : g * b * g⁻¹ ∈ Subgroup.zpowers x := by
      rw [← hg]; exact ⟨b, Subgroup.mem_zpowers b, rfl⟩
    have hxg : x ∈ Subgroup.zpowers (g * b * g⁻¹) := by
      have : x ∈ conjBy g (Subgroup.zpowers b) := by rw [hg]; exact Subgroup.mem_zpowers x
      obtain ⟨w, hw, rfl⟩ := this
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simp [map_zpow]⟩
    obtain ⟨y, hy, hyb⟩ := hfusY b hbY hb3 g (hBY (hxB hgb))
    have hCx : Cen x = conjBy y (Cen b) := by
      rw [← cen_conj, hyb]
      exact le_antisymm (cen_le_cen_of_mem_zpowers hgb) (cen_le_cen_of_mem_zpowers hxg)
    have hle : Cen x ≤ Y := by
      rw [hCx]; rintro _ ⟨w, hw, rfl⟩
      exact Y.mul_mem (Y.mul_mem hy (hCbY hw)) (Y.inv_mem hy)
    refine ⟨hle, ?_⟩
    rw [inf_of_le_right hle, hCx, Subgroup.card_map_of_injective (MulAut.conj y).injective,
      hCbcard]
  obtain ⟨hl1, hl2, hl3⟩ := h4.mem_conjLines
  obtain ⟨-, hC2⟩ := hconj b₂ hl2
  obtain ⟨hC3Y, hC3⟩ := hconj b₃ hl3
  have ho1 := orderOf_of_mem_conjLines hb3 hl1
  have ho2 := orderOf_of_mem_conjLines hb3 hl2
  have ho3 := orderOf_of_mem_conjLines hb3 hl3
  have h23 : b₃ ∉ Subgroup.zpowers b₂ := by
    intro h
    have hle : Subgroup.closure ({b₁, b₂, b₃} : Set G) ≤
        Subgroup.zpowers b₁ ⊔ Subgroup.zpowers b₂ := by
      refine (Subgroup.closure_le _).mpr ?_
      intro z hz
      rcases hz with rfl | rfl | rfl
      · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
      · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
      · exact Subgroup.mem_sup_right h
    have hN : Subgroup.zpowers b₁ ≤ Subgroup.normalizer (Subgroup.zpowers b₂ : Set G) :=
      Subgroup.zpowers_le.mpr (mem_normalizer_of_comm hcomm (Subgroup.zpowers_le.mpr hb2B) hb1B)
    have e := card_sup_mul_card_inf _ _ hN
    rw [Nat.card_zpowers, Nat.card_zpowers, ho1, ho2] at e
    have h1 := Subgroup.card_le_of_le hle
    rw [hB.elem.2] at h1
    have h2 : 0 < Nat.card ↥(Subgroup.zpowers b₁ ⊓ Subgroup.zpowers b₂) := Nat.card_pos
    nlinarith
  have hβL : b₂ * b₃ ∈ L := L.mul_mem hB.hb₂ hB.hb₃
  have hβY : b₂ * b₃ ∈ Y := hLY hβL
  have hβ3 : orderOf (b₂ * b₃) = 3 := by
    have p2 : b₂ ^ 3 = 1 := ho2 ▸ pow_orderOf_eq_one b₂
    have p3 : b₃ ^ 3 = 1 := ho3 ▸ pow_orderOf_eq_one b₃
    refine orderOf_eq_prime ?_ ?_
    · rw [(show Commute b₂ b₃ from hcomm b₂ hb2B b₃ hb3B).mul_pow, p2, p3, one_mul]
    · intro h1
      apply h23
      rw [eq_inv_of_mul_eq_one_right h1]
      exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _)
  have hβcard : Nat.card ↥(Y ⊓ Cen (b₂ * b₃)) = 2 ^ 5 * 3 ^ 4 * 5 :=
    hS3 B hBY hB4 b₂ hb2B b₃ hb3B hC2 hC3 h23
  have ht₀β : t₀ ∈ Cen (b₂ * b₃) := Subgroup.mem_centralizer_singleton_iff.mpr
    (Subgroup.mem_centralizer_singleton_iff.mp (hLt hβL)).symm
  set T := Op 2 (Cen t₀) with hT
  have hTn : ∀ g ∈ Cen t₀, ∀ s ∈ T, g * s * g⁻¹ ∈ T := fun g hg s hs =>
    inSubgroup_conj_mem (CFSG.pCore_normal (p := 2) (G := ↥(Cen t₀))) hg hs
  have hTcard : Nat.card T = 2 ^ 7 := h43.2.1.2
  have hTle : T ≤ Cen t₀ := Subgroup.map_subtype_le _
  have hTL : T ⊓ L = ⊥ := by
    haveI : IsSimpleGroup L :=
      CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp L 3 2 1
        hB.hyp.model
    haveI hn : ((T ⊓ L).subgroupOf L).Normal := ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact ⟨hTn g (hLt g.2) n hn.1, L.mul_mem (L.mul_mem g.2 hn.2) (L.inv_mem g.2)⟩⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((T ⊓ L).subgroupOf L) with h | h
    · refine eq_bot_iff.mpr fun x hx => ?_
      have : (⟨x, hx.2⟩ : L) ∈ (T ⊓ L).subgroupOf L := Subgroup.mem_subgroupOf.mpr hx
      rw [h, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
    · exfalso
      have hLT : L ≤ T := fun x hx => by
        have : (⟨x, hx⟩ : L) ∈ (T ⊓ L).subgroupOf L := by rw [h]; exact Subgroup.mem_top _
        exact (Subgroup.mem_subgroupOf.mp this).1
      have := Subgroup.card_dvd_of_le hLT
      rw [hB.card_L, hTcard] at this
      norm_num at this
  have hLN : L ≤ Subgroup.normalizer (T : Set G) := fun l hl =>
    Subgroup.mem_normalizer_iff.mpr fun s => ⟨fun hs => hTn l (hLt hl) s hs, fun hs => by
      have := hTn l⁻¹ ((Cen t₀).inv_mem (hLt hl)) _ hs
      rwa [show l⁻¹ * (l * s * l⁻¹) * l⁻¹⁻¹ = s by group] at this⟩
  have hCt : L ⊔ T = Cen t₀ := by
    refine le_antisymm (sup_le hLt hTle) fun x hx => ?_
    have hx' : x ∈ setMul T L := by rw [h43.1]; exact hx
    obtain ⟨s, hs, l, hl, rfl⟩ := hx'
    exact (L ⊔ T).mul_mem (Subgroup.mem_sup_right hs) (Subgroup.mem_sup_left hl)
  have hCtcard : Nat.card (Cen t₀) = 2 ^ 16 * 2835 := by
    have e := card_sup_mul_card_inf L T hLN
    rw [inf_comm, hTL, Subgroup.card_bot, mul_one, hCt, hB.card_L, hTcard] at e
    rw [e]; norm_num
  have hA2 : ∀ x ∈ Cen t₀, orderOf x = 3 → ∃ c ∈ Cen t₀, c * x * c⁻¹ ∈ L := by
    intro x hx hx3
    have hx' : x ∈ setMul T L := by rw [h43.1]; exact hx
    obtain ⟨s, hs, l, hl, rfl⟩ := hx'
    have hl3T : l ^ 3 ∈ T := by
      have key : ∀ a z : G, (a * z) ^ 3 = a * (z * a * z⁻¹) * (z ^ 2 * a * (z ^ 2)⁻¹) * z ^ 3 := by
        intro a z; simp only [pow_three, pow_two]; group
      have e := key s⁻¹ (s * l)
      rw [show s⁻¹ * (s * l) = l by group] at e
      have hx3' : (s * l) ^ 3 = 1 := hx3 ▸ pow_orderOf_eq_one _
      rw [e, hx3', mul_one]
      exact T.mul_mem (T.mul_mem (T.inv_mem hs) (hTn _ hx _ (T.inv_mem hs)))
        (hTn _ ((Cen t₀).pow_mem hx 2) _ (T.inv_mem hs))
    have hl3 : l ^ 3 = 1 := by
      have : l ^ 3 ∈ T ⊓ L := ⟨hl3T, L.pow_mem hl 3⟩
      rwa [hTL, Subgroup.mem_bot] at this
    have hl1 : l ≠ 1 := by
      rintro rfl
      rw [mul_one] at hx3
      have := orderOf_dvd_natCard (⟨s, hs⟩ : T)
      rw [Subgroup.orderOf_mk, hx3, hTcard] at this
      norm_num at this
    have hlo : orderOf l = 3 := orderOf_eq_prime hl3 hl1
    have hNH : Subgroup.zpowers (s * l) ≤ Subgroup.normalizer (T : Set G) :=
      Subgroup.zpowers_le.mpr (Subgroup.mem_normalizer_iff.mpr fun w =>
        ⟨fun hw => hTn _ hx w hw, fun hw => by
          have := hTn _ ((Cen t₀).inv_mem hx) _ hw
          rwa [show (s * l)⁻¹ * (s * l * w * (s * l)⁻¹) * (s * l)⁻¹⁻¹ = w by group] at this⟩)
    have hinf : Subgroup.zpowers (s * l) ⊓ T = ⊥ := Subgroup.inf_eq_bot_of_coprime (by
      rw [Nat.card_zpowers, hx3, hTcard]; norm_num)
    have hHcard : Nat.card ↥(Subgroup.zpowers (s * l) ⊔ T) = 2 ^ 7 * 3 := by
      have e := card_sup_mul_card_inf _ _ hNH
      rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, hx3, hTcard] at e
      rw [e]; ring
    have hlH : Subgroup.zpowers l ≤ Subgroup.zpowers (s * l) ⊔ T := by
      refine Subgroup.zpowers_le.mpr ?_
      have h' : s⁻¹ * (s * l) ∈ Subgroup.zpowers (s * l) ⊔ T :=
        Subgroup.mul_mem _ (Subgroup.mem_sup_right (T.inv_mem hs))
          (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
      rwa [show s⁻¹ * (s * l) = l by group] at h'
    obtain ⟨Q, hQ⟩ := ((IsPGroup.of_card (n := 1) (show Nat.card (Subgroup.zpowers l) = 3 ^ 1 by
      rw [Nat.card_zpowers, hlo]; rfl)).comap_of_injective
        (Subgroup.zpowers (s * l) ⊔ T).subtype Subtype.coe_injective).exists_le_sylow
    have hQcard : Nat.card ((Q : Subgroup _).map (Subgroup.zpowers (s * l) ⊔ T).subtype) = 3 := by
      rw [Subgroup.card_map_of_injective (Subgroup.zpowers (s * l) ⊔ T).subtype_injective,
        Q.card_eq_multiplicity, hHcard, Nat.factorization_mul (by norm_num) (by norm_num),
        Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 2 ^ 7),
        Nat.Prime.factorization_self Nat.prime_three]
      norm_num
    have hQl : (Q : Subgroup _).map (Subgroup.zpowers (s * l) ⊔ T).subtype =
        Subgroup.zpowers l := by
      symm
      refine Subgroup.eq_of_le_of_card_ge
        (fun z hz => ⟨⟨z, hlH hz⟩, hQ (Subgroup.mem_comap.mpr hz), rfl⟩) ?_
      rw [hQcard, Nat.card_zpowers, hlo]
    obtain ⟨c, hc, hcx⟩ := exists_conjBy_le_sylow
      (le_sup_left : Subgroup.zpowers (s * l) ≤ Subgroup.zpowers (s * l) ⊔ T)
      (IsPGroup.of_card (n := 1) (show Nat.card (Subgroup.zpowers (s * l)) = 3 ^ 1 by
        rw [Nat.card_zpowers, hx3]; rfl)) Q
    refine ⟨c, (sup_le (Subgroup.zpowers_le.mpr hx) hTle) hc, ?_⟩
    rw [hQl] at hcx
    exact (Subgroup.zpowers_le.mpr hl) (hcx ⟨s * l, Subgroup.mem_zpowers _, rfl⟩)
  set E := Subgroup.closure ({b₂, b₃} : Set G) with hE
  have hA4 : ∀ n ∈ Nor E, n ∈ Y := by
    intro n hn
    have hEB : E ≤ B := (Subgroup.closure_le _).mpr (by
      intro z hz; rcases hz with rfl | rfl; exacts [hb2B, hb3B])
    have hBC : B ≤ CenS E := fun z hz =>
      Subgroup.mem_centralizer_iff.mpr fun h hh => hcomm h (hEB hh) z hz
    have hb3E : b₃ ∈ E := Subgroup.subset_closure (Set.mem_insert_of_mem b₂ (Set.mem_singleton b₃))
    have hCEY : CenS E ≤ Y := fun z hz => hC3Y (Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hz b₃ hb3E).symm)
    have hnC := CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer E hn
    have hnB : conjBy n B ≤ CenS E := by
      rintro _ ⟨z, hz, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp hnC z).mp (hBC hz)
    obtain ⟨c, hc, hcB⟩ := exists_conjBy_eq_of_unique hS1 hCEY hnB hBC (isElemAb_conjBy hB4 n) hB4
    have hcn : c * n ∈ Nor B := Subgroup.mem_normalizer_fintype fun z hz => by
      rw [← hcB]
      refine ⟨n * z * n⁻¹, ⟨z, hz, rfl⟩, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    have : n = c⁻¹ * (c * n) := by group
    rw [this]
    exact Y.mul_mem (Y.inv_mem (hCEY hc)) (hNY hcn)
  have hA5 : ∀ τ ∈ Y, orderOf τ = 2 → ∀ g : G, g * τ * g⁻¹ = t₀ →
      ∃ y ∈ Y, y * τ * y⁻¹ = t₀ := by
    intro τ hτY hτ2 g hg
    obtain ⟨y, hy, hyβ⟩ := hS4 τ hτY hτ2 (b₂ * b₃) hβY hβ3 hβcard
    have hτ'β : y⁻¹ * τ * y ∈ Cen (b₂ * b₃) := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hyβ ⊢
      calc y⁻¹ * τ * y * (b₂ * b₃) = y⁻¹ * (τ * (y * (b₂ * b₃) * y⁻¹)) * y := by group
        _ = y⁻¹ * ((y * (b₂ * b₃) * y⁻¹) * τ) * y := by rw [hyβ]
        _ = b₂ * b₃ * (y⁻¹ * τ * y) := by group
    have hg' : (g * y) * (y⁻¹ * τ * y) * (g * y)⁻¹ = t₀ := by rw [← hg]; group
    have hxC : (g * y) * (b₂ * b₃) * (g * y)⁻¹ ∈ Cen t₀ := by
      rw [Subgroup.mem_centralizer_singleton_iff, ← hg']
      exact conj_commute (Subgroup.mem_centralizer_singleton_iff.mp hτ'β).symm
    have hx3 : orderOf ((g * y) * (b₂ * b₃) * (g * y)⁻¹) = 3 := by
      rw [show (g * y) * (b₂ * b₃) * (g * y)⁻¹ = MulAut.conj (g * y) (b₂ * b₃) from rfl,
        MulEquiv.orderOf_eq]
      exact hβ3
    obtain ⟨c, hc, hcL⟩ := hA2 _ hxC hx3
    have e : (c * (g * y)) * (b₂ * b₃) * (c * (g * y))⁻¹ =
        c * ((g * y) * (b₂ * b₃) * (g * y)⁻¹) * c⁻¹ := by group
    have hx'L : (c * (g * y)) * (b₂ * b₃) * (c * (g * y))⁻¹ ∈ L := by rw [e]; exact hcL
    obtain ⟨y₁, hy₁, hy₁β⟩ := hfusY _ hβY hβ3 _ (hLY hx'L)
    have hsup : Subgroup.zpowers b ⊔ L = Y ⊓ Cen b := by rw [inf_of_le_right hCbY, hCb]
    obtain ⟨k, hk, hkβ⟩ := hS5 b hbY hb3 L hLY hsup hB.hyp.model (b₂ * b₃) hβL _ hx'L hβ3
      ⟨y₁, hy₁, hy₁β⟩
    obtain ⟨h, hh⟩ : ∃ h : G, h = k⁻¹ * (c * (g * y)) := ⟨_, rfl⟩
    have hhβ : h ∈ Cen (b₂ * b₃) := by
      have e : h * (b₂ * b₃) * h⁻¹ = b₂ * b₃ := by
        rw [hh, show k⁻¹ * (c * (g * y)) * (b₂ * b₃) * (k⁻¹ * (c * (g * y)))⁻¹ =
          k⁻¹ * ((c * (g * y)) * (b₂ * b₃) * (c * (g * y))⁻¹) * k by group, ← hkβ]
        group
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc h * (b₂ * b₃) = h * (b₂ * b₃) * h⁻¹ * h := by group
        _ = b₂ * b₃ * h := by rw [e]
    have hhτ : h * (y⁻¹ * τ * y) * h⁻¹ = t₀ := by
      have hct : c * t₀ * c⁻¹ = t₀ := by
        rw [Subgroup.mem_centralizer_singleton_iff.mp hc, mul_inv_cancel_right]
      have hkt : k⁻¹ * t₀ * k = t₀ := by
        rw [Subgroup.mem_centralizer_singleton_iff.mp ((Cen t₀).inv_mem (hLt hk)),
          inv_mul_cancel_right]
      rw [hh]
      calc k⁻¹ * (c * (g * y)) * (y⁻¹ * τ * y) * (k⁻¹ * (c * (g * y)))⁻¹ =
          k⁻¹ * (c * ((g * y) * (y⁻¹ * τ * y) * (g * y)⁻¹) * c⁻¹) * k := by group
        _ = t₀ := by rw [hg', hct, hkt]
    obtain ⟨-, hdec⟩ := h42 _ (Set.mem_insert _ _)
    have hh' : h ∈ setMul (Opp 3 (Cen (b₂ * b₃))) (Cen (b₂ * b₃) ⊓ Nor E) := by
      rw [hdec]; exact hhβ
    obtain ⟨o, ho, n, hn, rfl⟩ := hh'
    have hnY : n ∈ Y := hA4 n hn.2
    have hτ''Y : n * (y⁻¹ * τ * y) * n⁻¹ ∈ Y :=
      Y.mul_mem (Y.mul_mem hnY (Y.mul_mem (Y.mul_mem (Y.inv_mem hy) hτY) hy)) (Y.inv_mem hnY)
    have hτ'' : n * (y⁻¹ * τ * y) * n⁻¹ = o⁻¹ * t₀ * o := by rw [← hhτ]; group
    have hON := CFSG.pPrimeCore_normal (p := 3) (G := ↥(Cen (b₂ * b₃)))
    have hu : n * (y⁻¹ * τ * y) * n⁻¹ * t₀ ∈ Opp 3 (Cen (b₂ * b₃)) := by
      rw [hτ'', show o⁻¹ * t₀ * o * t₀ = o⁻¹ * (t₀ * o * t₀⁻¹) by rw [ht₀inv]; group]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ ho) (inSubgroup_conj_mem hON ht₀β ho)
    have huY : n * (y⁻¹ * τ * y) * n⁻¹ * t₀ ∈ Y :=
      Y.mul_mem hτ''Y (hCtY (Subgroup.mem_centralizer_singleton_iff.mpr rfl))
    have hR := hS6 (b₂ * b₃) hβY hβ3 (Opp 3 (Cen (b₂ * b₃)) ⊓ Y)
      (fun z hz => ⟨hz.2, Subgroup.map_subtype_le _ hz.1⟩)
      (fun z hz => Subgroup.mem_normalizer_fintype fun w hw =>
        ⟨inSubgroup_conj_mem hON hz.2 hw.1, Y.mul_mem (Y.mul_mem hz.1 hw.2) (Y.inv_mem hz.1)⟩)
      (Nat.Coprime.coprime_dvd_left (Subgroup.card_dvd_of_le inf_le_left) (by
        rw [Opp, CFSG.inSubgroup, Subgroup.card_map_of_injective (Cen (b₂ * b₃)).subtype_injective]
        exact (CFSG.pPrimeCore_coprime_card (p := 3)).symm))
    have hu1 : n * (y⁻¹ * τ * y) * n⁻¹ * t₀ = 1 := by
      have : n * (y⁻¹ * τ * y) * n⁻¹ * t₀ ∈ Opp 3 (Cen (b₂ * b₃)) ⊓ Y := ⟨hu, huY⟩
      rwa [hR, Subgroup.mem_bot] at this
    have hfin : n * (y⁻¹ * τ * y) * n⁻¹ = t₀ := by
      have := eq_inv_of_mul_eq_one_left hu1
      rwa [ht₀inv] at this
    refine ⟨n * y⁻¹, Y.mul_mem hnY (Y.inv_mem hy), ?_⟩
    rw [← hfin]; group
  refine ⟨?_, ?_⟩
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨P⟩ : Nonempty (Sylow 2 (Cen t₀)) := inferInstance
    set S := (P : Subgroup (Cen t₀)).map (Cen t₀).subtype with hS
    have hSC : S ≤ Cen t₀ := Subgroup.map_subtype_le _
    have hSY : S ≤ Y := hSC.trans hCtY
    have ht₀S : t₀ ∈ S := by
      obtain ⟨t₀', ht₀'⟩ : ∃ t : Cen t₀, (t : G) = t₀ :=
        ⟨⟨t₀, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩, rfl⟩
      haveI hK : (Subgroup.zpowers t₀').Normal := ⟨fun z hz g => by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
        have hgc : Commute g t₀' := Subtype.ext (by
          rw [Subgroup.coe_mul, Subgroup.coe_mul, ht₀']
          exact Subgroup.mem_centralizer_singleton_iff.mp g.2)
        rw [(hgc.zpow_right k).eq, mul_inv_cancel_right]; exact hz⟩
      have hKp : IsPGroup 2 (Subgroup.zpowers t₀') := IsPGroup.of_card (n := 1) (by
        rw [Nat.card_zpowers, ← Subgroup.orderOf_coe, ht₀', h4.ht₀]; rfl)
      exact ⟨t₀', hKp.le_sylow_of_normal P (Subgroup.mem_zpowers t₀'), ht₀'⟩
    have hScard : Nat.card S = 2 ^ 16 := by
      rw [hS, Subgroup.card_map_of_injective (Cen t₀).subtype_injective, P.card_eq_multiplicity,
        hCtcard, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
        Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 2835)]
    have hYcard : Nat.card Y = 2 ^ 16 * 722925 := by
      rw [(CFSG.Timmesfeld.card_statedClassicalModel_two hYm).2.2.1 rfl]
      norm_num [CFSG.Open.ordBC, Finset.prod_Icc_succ_top]
    have hSsyl : IsSylowOf 2 S Y := by
      refine ⟨hSY, P.isPGroup'.map _, ?_⟩
      have e := Subgroup.relIndex_mul_card S Y
      rw [inf_of_le_left hSY, hScard, hYcard] at e
      have : S.relIndex Y = 722925 := by omega
      rw [this]; norm_num
    have hNS : Subgroup.normalizer (S : Set G) ≤ Cen t₀ := by
      intro g hg
      have hz₂S : g * t₀ * g⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp hg t₀).mp ht₀S
      have hcen : ∀ u ∈ S, t₀ * u = u * t₀ := fun u hu =>
        (Subgroup.mem_centralizer_singleton_iff.mp (hSC hu)).symm
      have hcen2 : ∀ u ∈ S, g * t₀ * g⁻¹ * u = u * (g * t₀ * g⁻¹) := by
        intro u hu
        have hv : g⁻¹ * u * g ∈ S :=
          (Subgroup.mem_normalizer_iff.mp hg (g⁻¹ * u * g)).mpr
            (by rwa [show g * (g⁻¹ * u * g) * g⁻¹ = u by group])
        have := hcen _ hv
        calc g * t₀ * g⁻¹ * u = g * (t₀ * (g⁻¹ * u * g)) * g⁻¹ := by group
          _ = g * ((g⁻¹ * u * g) * t₀) * g⁻¹ := by rw [this]
          _ = u * (g * t₀ * g⁻¹) := by group
      have hz2 : orderOf (g * t₀ * g⁻¹) = 2 := by
        rw [show g * t₀ * g⁻¹ = MulAut.conj g t₀ from rfl, MulEquiv.orderOf_eq]; exact h4.ht₀
      obtain ⟨y, hy, hyz⟩ := hA5 _ (hSY hz₂S) hz2 g⁻¹ (by group)
      have := hS7 S hSsyl t₀ ht₀S _ hz₂S hcen hcen2 ⟨y⁻¹, Y.inv_mem hy, by
        calc y⁻¹ * t₀ * y⁻¹⁻¹ = y⁻¹ * (y * (g * t₀ * g⁻¹) * y⁻¹) * y⁻¹⁻¹ := by rw [hyz]
          _ = g * t₀ * g⁻¹ := by group⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc g * t₀ = g * t₀ * g⁻¹ * g := by group
        _ = t₀ * g := by rw [← this]
    obtain ⟨Tsyl, hTsyl⟩ := CFSG.StandardType.exists_sylow_eq_map_of_normalizer_le P hNS
    exact ⟨Tsyl, by rw [hTsyl]; exact ht₀S, by rw [hTsyl]; exact hSC⟩
  · refine ⟨((1 : G) : G ⧸ Y), ?_, ?_⟩
    · show t₀ • ((1 : G) : G ⧸ Y) = ((1 : G) : G ⧸ Y)
      rw [MulAction.Quotient.smul_coe, smul_eq_mul, QuotientGroup.eq]
      simpa using hCtY (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
    · intro q hq
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq] at hq
      have hτY : g⁻¹ * t₀ * g ∈ Y := by rwa [mul_inv_rev, ht₀inv] at hq
      have hτ2 : orderOf (g⁻¹ * t₀ * g) = 2 := by
        rw [show g⁻¹ * t₀ * g = MulAut.conj g⁻¹ t₀ by simp [MulAut.conj_apply],
          MulEquiv.orderOf_eq]
        exact h4.ht₀
      obtain ⟨y, hy, hyτ⟩ := hA5 _ hτY hτ2 g (by group)
      have hyg : y * g⁻¹ ∈ Cen t₀ := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc y * g⁻¹ * t₀ = y * (g⁻¹ * t₀ * g) * y⁻¹ * (y * g⁻¹) := by group
          _ = t₀ * (y * g⁻¹) := by rw [hyτ]
      have hgY : g ∈ Y := by
        have : g = (y * g⁻¹)⁻¹ * y := by group
        rw [this]; exact Y.mul_mem (Y.inv_mem (hCtY hyg)) hy
      show (g : G ⧸ Y) = ((1 : G) : G ⧸ Y)
      rw [QuotientGroup.eq]; simpa using hgY

end CFSG.RankThree.PartTwo.Sec21.FF81
