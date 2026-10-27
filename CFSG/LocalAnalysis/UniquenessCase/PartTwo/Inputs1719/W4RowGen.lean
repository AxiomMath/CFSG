module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowFstarLift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowRank
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.X1 CFSG.QuasithinUnique.Setup.Family

variable {W : Type} [CommGroup W] [Finite W]

omit [Finite W] in
theorem redHom_ne_one_of_o2Trivial {L : Subgroup (MulAut W)} (hO2 : O2Trivial L) {S : Type}
    [Group S] (e : CQ L ≃* S) {t : MulAut W} (htL : t ∈ L) (hto : orderOf t = 2) :
    redHom L e ⟨t, htL⟩ ≠ 1 := by
  intro h
  rw [redHom_eq_one_iff] at h
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hto
    norm_num at hto
  have hzpow : (Subgroup.zpowers t).subgroupOf L = Subgroup.zpowers (⟨t, htL⟩ : ↥L) := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, Subtype.ext hk⟩
    · rintro ⟨k, hk⟩
      exact ⟨k, congrArg Subtype.val hk⟩
  have hP2 : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hto]; norm_num)
  have hPbot := hO2 (Subgroup.zpowers t) (Subgroup.zpowers_le.2 htL) (by
    rw [hzpow]
    exact Subgroup.normal_of_le_center (Subgroup.zpowers_le.2 h)) hP2
  have hmem : t ∈ (⊥ : Subgroup (MulAut W)) := by
    rw [← hPbot]
    exact Subgroup.mem_zpowers t
  exact ht1 (Subgroup.mem_bot.1 hmem)

theorem le_rkIdx_of_gen (hW : ∀ w : W, w * w = 1) {L : Subgroup (MulAut W)} (hO2 : O2Trivial L)
    {S : Type} [Group S] (e : CQ L ≃* S) {k p ρ : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hρ : k * ρ < orderOf (2 : ZMod p) + k)
    (hgen : ∀ B : Subgroup S, (∀ x ∈ B, x * x = 1) → B ≠ ⊥ → ∃ cs : List S, cs.length = k ∧
      ∃ x ∈ Subgroup.closure (X1.conjSet cs (B : Set S)), orderOf x = p)
    {t : MulAut W} (htL : t ∈ L) (hto : orderOf t = 2) :
    ρ ≤ rkIdx (fixV (Subgroup.zpowers t)) := by
  have hEL : Subgroup.zpowers t ≤ L := Subgroup.zpowers_le.2 htL
  have ht2 : t ^ 2 = 1 := by
    rw [← hto]
    exact pow_orderOf_eq_one t
  have hEel : IsElemAbelian2 (Subgroup.zpowers t) := isElemAbelian2_of_sq_eq_one fun a ha => by
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ht2, one_zpow]
  have hne : imgSub L (Subgroup.zpowers t) hEL e ≠ ⊥ := by
    intro h
    have hmem : redHom L e (Subgroup.inclusion hEL ⟨t, Subgroup.mem_zpowers t⟩) ∈
        imgSub L (Subgroup.zpowers t) hEL e := mem_imgSub.2 ⟨_, rfl⟩
    rw [h, Subgroup.mem_bot] at hmem
    exact redHom_ne_one_of_o2Trivial hO2 e htL hto hmem
  obtain ⟨cs, hcs, hx⟩ := hgen _ (imgSub_sq hEel) hne
  have h := two_pow_le_of_inner_gen hW hEL e hp2 ⟨cs, hcs, hx⟩
  obtain ⟨m, hm⟩ := index_fixV_eq_two_pow hW (Subgroup.zpowers t)
  have h2 := two_pow_le_of_pow_le ⟨m, hm⟩ h hρ
  rw [hm] at h2
  have hρm : ρ ≤ m := (Nat.pow_le_pow_iff_right (by norm_num)).1 h2
  rwa [rkIdx, hm, padicValNat.prime_pow]

theorem le_rk_of_gen (hW : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)} {S : Type} [Group S]
    (e : CQ L ≃* S) {k p ρ : ℕ} [Fact p.Prime] (hk : 0 < k) (hp2 : p ≠ 2)
    (hpS : p ∣ Nat.card S) (hρ : k * ρ < orderOf (2 : ZMod p) + k) : ρ ≤ rk W := by
  have hW' : ∀ w : W, w * w = 1 := fun w => by rw [← sq]; exact hW w
  have hcard : Nat.card W = 2 ^ rk W :=
    card_eq_two_pow_of_isPGroup (isPGroup_two_of_sq_eq_one hW)
  have hle := two_pow_le_card_of_dvd hW' e hp2 hpS
  rw [hcard] at hle
  have hord : orderOf (2 : ZMod p) ≤ rk W := (Nat.pow_le_pow_iff_right (by norm_num)).1 hle
  have hρd : ρ ≤ orderOf (2 : ZMod p) := by
    by_contra hcon
    push Not at hcon
    nlinarith
  omega

theorem le_mParam_of_gen (hW : ∀ w : W, w ^ 2 = 1) {Y L : Subgroup (MulAut W)} (hO2 : O2Trivial L)
    (hYL : ∀ t ∈ Y, orderOf t = 2 → t ∈ L) {S : Type} [Group S] (e : CQ L ≃* S) {k p ρ : ℕ}
    [Fact p.Prime] (hk : 0 < k) (hp2 : p ≠ 2) (hpS : p ∣ Nat.card S)
    (hρ : k * ρ < orderOf (2 : ZMod p) + k)
    (hgen : ∀ B : Subgroup S, (∀ x ∈ B, x * x = 1) → B ≠ ⊥ → ∃ cs : List S, cs.length = k ∧
      ∃ x ∈ Subgroup.closure (X1.conjSet cs (B : Set S)), orderOf x = p) :
    ρ ≤ E3.mParam Y := by
  have hW' : ∀ w : W, w * w = 1 := fun w => by rw [← sq]; exact hW w
  unfold E3.mParam
  by_cases hEven : Even (Nat.card Y)
  · rw [if_pos hEven]
    refine le_csInf ?_ ?_
    · obtain ⟨t, hto⟩ :=
        exists_prime_orderOf_dvd_card' (G := ↥Y) 2 (even_iff_two_dvd.1 hEven)
      exact ⟨_, (t : MulAut W), t.2, by rwa [Subgroup.orderOf_coe], rfl⟩
    · rintro n ⟨t, htY, hto, rfl⟩
      exact le_rkIdx_of_gen hW' hO2 e hp2 hρ hgen (hYL t htY hto) hto
  · rw [if_neg hEven]
    exact le_rk_of_gen hW e hk hp2 hpS hρ

theorem mem_of_actS_inner_of_fstar {Y L : Subgroup (MulAut W)} (hLY : L ≤ Y) (hF : Fstar Y = L)
    (hperf : Group.IsPerfect ↥L) (hY : Y ≤ Subgroup.normalizer (L : Set (MulAut W)))
    {S : Type} [Group S] (e : CQ L ≃* S) {b : MulAut W} (hbY : b ∈ Y)
    (hin : actS hY e ⟨b, Subgroup.mem_sup_right hbY⟩ ∈ (MulAut.conj : S →* MulAut S).range) :
    b ∈ L := by
  obtain ⟨s, hs⟩ := hin
  obtain ⟨l, rfl⟩ := redHom_surjective L e s
  have h1 := actS_of_mem hY e l
  set l' : ↥(L ⊔ Y) := ⟨(l : MulAut W), Subgroup.mem_sup_left l.2⟩ with hl'
  set b' : ↥(L ⊔ Y) := ⟨b, Subgroup.mem_sup_right hbY⟩ with hb'
  have h2 : actS hY e (l'⁻¹ * b') = 1 := by
    rw [map_mul, map_inv, h1, ← hs]
    simp
  have h3 : actionOnCQ (le_sup_left : L ≤ L ⊔ Y) (normal_sup_of_le_normalizer hY)
      (l'⁻¹ * b') = 1 := by
    have := h2
    rw [actS_apply] at this
    exact (MulAut.congr e).injective (by rw [this, map_one])
  have h4 := (actionOnCQ_eq_one_iff (le_sup_left : L ≤ L ⊔ Y) (normal_sup_of_le_normalizer hY)
    hperf (l'⁻¹ * b')).1 h3
  have hxY : ((l'⁻¹ * b' : ↥(L ⊔ Y)) : MulAut W) ∈ Y := by
    simp only [hl', hb', Subgroup.coe_mul, Subgroup.coe_inv]
    exact Y.mul_mem (Y.inv_mem (hLY l.2)) hbY
  have h5 : ((l'⁻¹ * b' : ↥(L ⊔ Y)) : MulAut W) ∈ L :=
    mem_of_mem_centralizer_of_fstar_eq hLY hF hxY h4
  have h6 : b = (l : MulAut W) * ((l'⁻¹ * b' : ↥(L ⊔ Y)) : MulAut W) := by
    simp [hl', hb']
  rw [h6]
  exact L.mul_mem l.2 h5

theorem two_pow_le_index_sq_of_outer (hW : ∀ w : W, w * w = 1) {Y L : Subgroup (MulAut W)}
    (hLY : L ≤ Y) (hF : Fstar Y = L) (hperf : Group.IsPerfect ↥L)
    (hY : Y ≤ Subgroup.normalizer (L : Set (MulAut W))) {S : Type} [Group S] [Finite S]
    (e : CQ L ≃* S) (hcent : Subgroup.center S = ⊥)
    (hcard2 : Nat.card (MulAut S) ≤ 2 * Nat.card S) {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2)
    (hD : ∀ ψ : MulAut S, ψ ∉ (MulAut.conj : S →* MulAut S).range → ψ * ψ = 1 →
      ∃ α : MulAut S, orderOf (ψ * (α * ψ * α⁻¹)) = q)
    {t : MulAut W} (htY : t ∈ Y) (htL : t ∉ L) (ht2 : t * t = 1) :
    2 ^ orderOf (2 : ZMod q) ≤ (fixV (Subgroup.zpowers t)).index ^ 2 := by
  set t' : ↥(L ⊔ Y) := ⟨t, Subgroup.mem_sup_right htY⟩ with ht'
  have hto : actS hY e t' ∉ (MulAut.conj : S →* MulAut S).range := fun h =>
    htL (mem_of_actS_inner_of_fstar hLY hF hperf hY e htY h)
  have ht'2 : actS hY e t' * actS hY e t' = 1 := by
    rw [← map_mul]
    have : t' * t' = 1 := Subtype.ext ht2
    rw [this, map_one]
  obtain ⟨α, hα⟩ := hD _ hto ht'2
  have hαr : α ∈ (actS hY e).range := by
    by_cases hαi : α ∈ (MulAut.conj : S →* MulAut S).range
    · obtain ⟨s, rfl⟩ := hαi
      exact conj_mem_range_actS hY e s
    · have h1 := inner_of_outer_mul hcent hcard2 hto hαi
      have h2 : (actS hY e t')⁻¹ * α ∈ (actS hY e).range := by
        obtain ⟨s, hs⟩ := h1
        rw [← hs]
        exact conj_mem_range_actS hY e s
      have : α = actS hY e t' * ((actS hY e t')⁻¹ * α) := by group
      rw [this]
      exact (actS hY e).range.mul_mem ⟨t', rfl⟩ h2
  have hdisp := two_pow_le_index_pow_of_mem hW (G := L ⊔ Y) (actS hY e)
    (B := Subgroup.zpowers t) [1, α]
    (by
      intro c hc
      rcases List.mem_cons.1 hc with rfl | hc
      · exact (actS hY e).range.one_mem
      · simp only [List.mem_singleton] at hc
        rw [hc]
        exact hαr) hq2 hα (by
      refine Subgroup.mul_mem _
        (Subgroup.subset_closure ⟨1, by simp, t', Subgroup.mem_zpowers t, by simp⟩)
        (Subgroup.subset_closure ⟨α, by simp, t', Subgroup.mem_zpowers t, rfl⟩))
  simpa using hdisp

theorem le_mParam_of_gen_out2 (hW : ∀ w : W, w ^ 2 = 1) {Y L : Subgroup (MulAut W)} (hLY : L ≤ Y)
    (hLn : (L.subgroupOf Y).Normal) (hF : Fstar Y = L) (hq : IsQuasisimple ↥L)
    (hO2 : O2Trivial L) {S : Type} [Group S] [Finite S] (e : CQ L ≃* S)
    (hcent : Subgroup.center S = ⊥) (hcard2 : Nat.card (MulAut S) ≤ 2 * Nat.card S)
    {k p q ρ : ℕ} [Fact p.Prime] [Fact q.Prime] (hk : 0 < k) (hp2 : p ≠ 2) (hq2 : q ≠ 2)
    (hpS : p ∣ Nat.card S) (hρ : k * ρ < orderOf (2 : ZMod p) + k)
    (hρq : 2 * ρ < orderOf (2 : ZMod q) + 2)
    (hgen : ∀ B : Subgroup S, (∀ x ∈ B, x * x = 1) → B ≠ ⊥ → ∃ cs : List S, cs.length = k ∧
      ∃ x ∈ Subgroup.closure (X1.conjSet cs (B : Set S)), orderOf x = p)
    (hD : ∀ ψ : MulAut S, ψ ∉ (MulAut.conj : S →* MulAut S).range → ψ * ψ = 1 →
      ∃ α : MulAut S, orderOf (ψ * (α * ψ * α⁻¹)) = q) :
    ρ ≤ E3.mParam Y := by
  have hW' : ∀ w : W, w * w = 1 := fun w => by rw [← sq]; exact hW w
  have hY : Y ≤ Subgroup.normalizer (L : Set (MulAut W)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLY).1 hLn
  unfold E3.mParam
  by_cases hEven : Even (Nat.card Y)
  · rw [if_pos hEven]
    refine le_csInf ?_ ?_
    · obtain ⟨t, hto⟩ :=
        exists_prime_orderOf_dvd_card' (G := ↥Y) 2 (even_iff_two_dvd.1 hEven)
      exact ⟨_, (t : MulAut W), t.2, by rwa [Subgroup.orderOf_coe], rfl⟩
    · rintro n ⟨t, htY, hto, rfl⟩
      by_cases htL : t ∈ L
      · exact le_rkIdx_of_gen hW' hO2 e hp2 hρ hgen htL hto
      · have ht2 : t * t = 1 := by
          rw [← sq, ← hto]
          exact pow_orderOf_eq_one t
        have h := two_pow_le_index_sq_of_outer hW' hLY hF hq.1 hY e hcent hcard2 hq2 hD htY htL
          ht2
        obtain ⟨m, hm⟩ := index_fixV_eq_two_pow hW' (Subgroup.zpowers t)
        have h2 := two_pow_le_of_pow_le ⟨m, hm⟩ h hρq
        rw [hm] at h2
        have hρm : ρ ≤ m := (Nat.pow_le_pow_iff_right (by norm_num)).1 h2
        rwa [rkIdx, hm, padicValNat.prime_pow]
  · rw [if_neg hEven]
    exact le_rk_of_gen hW e hk hp2 hpS hρ

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row
