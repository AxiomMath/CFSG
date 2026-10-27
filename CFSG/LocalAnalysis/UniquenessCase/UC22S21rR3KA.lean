module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8101UBar
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Cong
import CFSG.LocalAnalysis.UniquenessCase.UC22OddPRank
import CFSG.LocalAnalysis.UniquenessCase.UC1K31
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.InnerTorusFacts
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsThirtyEightOq

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem uc22r3k_symm {M L K : Subgroup G} (hne : K ≠ L) (hset : conjSetOf M L = {L, K})
    {n : ℕ} (hS : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n) :
    (conjSetOf M L).ncard = 2 ∧ (conjSetOf M K).ncard = 2 ∧
      (IsL2 (Bar2 K) n ∨ IsSz (Bar2 K) n) ∧ Nat.card K = Nat.card L := by
  have hmem : K ∈ conjSetOf M L := by rw [hset]; simp
  have hc2 : (conjSetOf M L).ncard = 2 := by rw [hset]; exact Set.ncard_pair hne.symm
  refine ⟨hc2, by rw [uc22p2214_conjSetOf_eq hmem]; exact hc2, uc22s21ru4e_shape_conj hmem hS,
    ?_⟩
  obtain ⟨g, -, rfl⟩ := hmem
  exact Subgroup.card_map_of_injective (MulAut.conj g).injective

private theorem uc22r3k_le_normalizer {M Y R : Subgroup G} (hcY : (conjSetOf M Y).ncard = 2)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hR : CFSG.ABGLocalTools.IsSylowOf r R M) :
    barImage M R ≤ normalizer (barImage M Y : Set (Bar2 M)) := by
  intro y hy
  obtain ⟨m, hm, rfl⟩ := uc22p21c_mem_barImage.1 hy
  refine uc22ine229_mk_mem_normalizer (uc22p2214_mem_normalizer_of_odd hcY m.2 ?_)
  obtain ⟨k, hk⟩ := hR.isPGroup ⟨m, hm⟩
  have h1 : orderOf (m : G) ∣ r ^ k := by
    rw [← Subgroup.orderOf_mk (m : G) hm]
    exact orderOf_dvd_of_pow_eq_one hk
  exact (hr.odd_of_ne_two hr2).pow.of_dvd_nat h1

private theorem uc22r3k_inner_part {M Y R : Subgroup G}
    (hY : Y ∈ calC M) (hcY : (conjSetOf M Y).ncard = 2) {n : ℕ}
    (hSY : IsL2 (Bar2 Y) n ∨ IsSz (Bar2 Y) n) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hrn : ¬ r ∣ n) (hR : CFSG.ABGLocalTools.IsSylowOf r R M) {β : Bar2 M}
    (hβ : β ∈ barImage M R) :
    ∃ x ∈ barImage M R ⊓ barImage M Y, ∀ f ∈ barImage M Y, β * f * β⁻¹ = x * f * x⁻¹ := by
  have : Fact r.Prime := ⟨hr⟩
  refine u81_inner_mem (u4x_isSylowOf_barImage hR) (uc22r3k_le_normalizer hcY hr hr2 hR)
    (u4x_center_eq_bot hY hSY) (fun α hα => ?_) hβ
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (u4x_isSylowOf_barImage hR).isPGroup
  have hcop : Nat.Coprime (Nat.card ↥(barImage M R)) n := by
    rw [hk]
    exact Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hr).2 hrn)
  exact mem_inner_of_pow_eq_one_of_coprime_card_outer hα
    (Nat.Coprime.coprime_dvd_right (u81_card_outer_dvd (u4x_shape_barImage hY hSY)) hcop)

theorem uc22r3k_decomp {M L K : Subgroup G} (hL : L ∈ calC M)
    (hK : K ∈ calC M) (hne : K ≠ L) (hset : conjSetOf M L = {L, K}) {n : ℕ}
    (hS : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hrn : ¬ r ∣ n) {R : Subgroup G} (hR : CFSG.ABGLocalTools.IsSylowOf r R M) {β : Bar2 M}
    (hβ : β ∈ barImage M R) :
    ∃ x₀ ∈ barImage M R ⊓ barImage M L, ∃ x₁ ∈ barImage M R ⊓ barImage M K,
      ∃ c ∈ barImage M R ⊓ centralizer
        ((barImage M L ⊔ barImage M K : Subgroup (Bar2 M)) : Set (Bar2 M)),
      β = x₀ * x₁ * c := by
  obtain ⟨hc2, hcK, hSK, -⟩ := uc22r3k_symm hne hset hS
  obtain ⟨hcomm, -⟩ := u4x_bar_structure hL hK hne hset hS
  obtain ⟨x₀, hx₀, h₀⟩ := uc22r3k_inner_part hL hc2 hS hr hr2 hrn hR hβ
  obtain ⟨x₁, hx₁, h₁⟩ := uc22r3k_inner_part hK hcK hSK hr hr2 hrn hR hβ
  have hc : Commute β (x₀ * x₁) :=
    (u4x_commute_of_conj hx₀.2 h₀).mul_right (u4x_commute_of_conj hx₁.2 h₁)
  have hm : β * (x₀ * x₁)⁻¹ ∈ barImage M R :=
    Subgroup.mul_mem _ hβ (Subgroup.inv_mem _ (Subgroup.mul_mem _ hx₀.1 hx₁.1))
  refine ⟨x₀, hx₀, x₁, hx₁, _, ⟨hm, u4x_mul_inv_mem_centralizer hcomm hx₀.2 hx₁.2 h₀ h₁⟩, ?_⟩
  rw [← mul_assoc, ← hc.eq, mul_inv_cancel_right]

private theorem uc22r3k_exists_orderOf_inf {M Y R : Subgroup G} (hY : Y ∈ calC M)
    (hcY : (conjSetOf M Y).ncard = 2) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hrY : r ∣ Nat.card Y) (hR : CFSG.ABGLocalTools.IsSylowOf r R M) :
    ∃ x ∈ barImage M R ⊓ barImage M Y, orderOf x = r := by
  have : Fact r.Prime := ⟨hr⟩
  have hRN : R ≤ normalizer (Y : Set G) := fun g hg => by
    obtain ⟨k, hk⟩ := hR.isPGroup ⟨g, hg⟩
    have hg3 : g ^ r ^ k = 1 := congrArg Subtype.val hk
    exact uc22p2214_mem_normalizer_of_odd hcY (hR.le hg)
      ((hr.odd_of_ne_two hr2).pow.of_dvd_nat (orderOf_dvd_of_pow_eq_one hg3))
  have hRY := (hR.of_le (le_inf hR.le hRN) inf_le_left).inf_of_le_normalizer
    (le_inf hY.1.le Subgroup.le_normalizer) inf_le_right
  have hne : R ⊓ Y ≠ ⊥ := by
    intro hbot
    have hv : 1 ≤ (Nat.card Y).factorization r :=
      (Nat.Prime.dvd_iff_one_le_factorization hr Nat.card_pos.ne').1 hrY
    have hc := hRY.card_eq
    rw [hbot, Subgroup.card_bot] at hc
    have h1 : r ^ 1 ≤ r ^ (Nat.card Y).factorization r := Nat.pow_le_pow_right hr.pos hv
    rw [pow_one] at h1
    exact lt_irrefl 1 (lt_of_lt_of_le hr.one_lt (h1.trans hc.symm.le))
  obtain ⟨a, ha, hao, -⟩ := CFSG.AGLEmbeddingD2.exists_orderOf_eq_mem_centralizer_of_le_normalizer
    hr hR.isPGroup inf_le_left ((le_inf Subgroup.le_normalizer hRN).trans
      Subgroup.inf_normalizer_le_normalizer_inf) hne
  have haM : a ∈ M := hR.le ha.1
  exact ⟨_, ⟨uc22p21c_mem_barImage.2 ⟨⟨a, haM⟩, ha.1, rfl⟩,
    uc22p21c_mem_barImage.2 ⟨⟨a, haM⟩, ha.2, rfl⟩⟩, orderOf_bar_eq_of_prime haM hr hr2 hao⟩

private theorem uc22r3k_isCyclic_inf {M Y R : Subgroup G} (hY : Y ∈ calC M) {n : ℕ}
    (hSY : IsL2 (Bar2 Y) n ∨ IsSz (Bar2 Y) n) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hR : CFSG.ABGLocalTools.IsSylowOf r R M) : IsCyclic ↥(barImage M R ⊓ barImage M Y) := by
  have : Fact r.Prime := ⟨hr⟩
  refine UCK.K31.isCyclic_of_pRank_le_one hr hr2
    (u4x_isSylowOf_barImage hR).isPGroup.to_inf_left ?_
  refine (CFSG.SectionRank.pRank_mono hr.one_lt inf_le_right).trans ?_
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (barImage M Y)]
  exact pRank_le_one_of_isL2_or_isSz (u4x_shape_barImage hY hSY) hr hr2

private theorem uc22r3k_le_pRank {M L K : Subgroup G} (hL : L ∈ calC M) (hK : K ∈ calC M)
    (hne : K ≠ L) (hset : conjSetOf M L = {L, K}) {n : ℕ}
    (hS : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hrL : r ∣ Nat.card L) {R : Subgroup G} (hR : CFSG.ABGLocalTools.IsSylowOf r R M)
    {E : Subgroup (Bar2 M)}
    (hE : E ≤ barImage M R ⊓ centralizer
      ((barImage M L ⊔ barImage M K : Subgroup (Bar2 M)) : Set (Bar2 M)))
    (hEel : IsElemAbelian r E) {j : ℕ} (hj : Nat.card E = r ^ j) :
    2 + j ≤ CFSG.Open.pRank r M := by
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨hc2, hcK, -, hKL⟩ := uc22r3k_symm hne hset hS
  obtain ⟨hcomm, hinf, -, -, -, -, hXC⟩ := u4x_bar_structure hL hK hne hset hS
  obtain ⟨x₀, hx₀, hx₀o⟩ := uc22r3k_exists_orderOf_inf hL hc2 hr hr2 hrL hR
  obtain ⟨x₁, hx₁, hx₁o⟩ := uc22r3k_exists_orderOf_inf hK hcK hr hr2 (hKL ▸ hrL) hR
  have h := u81_le_pRank hcomm hinf hXC (zpowers_le.2 hx₀.2) (zpowers_le.2 hx₁.2)
    (by rw [Nat.card_zpowers, hx₀o]) (by rw [Nat.card_zpowers, hx₁o]) (hE.trans inf_le_right)
    hEel hj
  rwa [pRank_bar2_eq_of_odd hr hr2] at h

theorem uc22r3k_comm {M L K : Subgroup G} (hL : L ∈ calC M)
    (hK : K ∈ calC M) (hne : K ≠ L) (hset : conjSetOf M L = {L, K}) {n : ℕ}
    (hS : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hrn : ¬ r ∣ n) (hrL : r ∣ Nat.card L) (hr3 : CFSG.Open.pRank r M ≤ 3) {R : Subgroup G}
    (hR : CFSG.ABGLocalTools.IsSylowOf r R M) : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x := by
  have : Fact r.Prime := ⟨hr⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hSK, -⟩ := uc22r3k_symm hne hset hS
  have hS' := u4x_isSylowOf_barImage hR
  have : IsCyclic ↥(barImage M R ⊓ centralizer
      ((barImage M L ⊔ barImage M K : Subgroup (Bar2 M)) : Set (Bar2 M))) := by
    refine UCK.K31.isCyclic_of_pRank_le_one hr hr2 hS'.isPGroup.to_inf_left
      (CFSG.SectionRank.pRank_le hr.one_lt fun E hE hEel => ?_)
    obtain ⟨j, hj⟩ := IsPGroup.iff_card.1 (hS'.isPGroup.to_le (hE.trans inf_le_left))
    have h := uc22r3k_le_pRank hL hK hne hset hS hr hr2 hrL hR hE hEel hj
    rw [hj]
    exact Nat.pow_le_pow_right hr.pos (by omega)
  have := uc22r3k_isCyclic_inf hL hS hr hr2 hR
  have := uc22r3k_isCyclic_inf hK hSK hr hr2 hR
  obtain ⟨hcomm, -⟩ := u4x_bar_structure hL hK hne hset hS
  have hC : ∀ {a b : Bar2 M}, a ∈ barImage M L ⊔ barImage M K →
      b ∈ centralizer ((barImage M L ⊔ barImage M K : Subgroup (Bar2 M)) : Set (Bar2 M)) →
      Commute a b := fun ha hb => Subgroup.mem_centralizer_iff.1 hb _ ha
  have hbar : ∀ β ∈ barImage M R, ∀ γ ∈ barImage M R, Commute β γ := by
    intro β hβ γ hγ
    obtain ⟨x₀, hx₀, x₁, hx₁, c, hc, rfl⟩ := uc22r3k_decomp hL hK hne hset hS hr hr2 hrn hR hβ
    obtain ⟨y₀, hy₀, y₁, hy₁, d, hd, rfl⟩ := uc22r3k_decomp hL hK hne hset hS hr hr2 hrn hR hγ
    have a00 : Commute x₀ y₀ := congrArg Subtype.val
      (mul_comm' (⟨x₀, hx₀⟩ : ↥(barImage M R ⊓ barImage M L)) ⟨y₀, hy₀⟩)
    have a01 : Commute x₀ y₁ := hcomm x₀ hx₀.2 y₁ hy₁.2
    have a10 : Commute x₁ y₀ := (hcomm y₀ hy₀.2 x₁ hx₁.2).symm
    have a11 : Commute x₁ y₁ := congrArg Subtype.val
      (mul_comm' (⟨x₁, hx₁⟩ : ↥(barImage M R ⊓ barImage M K)) ⟨y₁, hy₁⟩)
    have a20 : Commute c y₀ := (hC (mem_sup_left hy₀.2) hc.2).symm
    have a21 : Commute c y₁ := (hC (mem_sup_right hy₁.2) hc.2).symm
    have a22 : Commute c d :=
      congrArg Subtype.val (mul_comm' (⟨c, hc⟩ : ↥(barImage M R ⊓ centralizer _)) ⟨d, hd⟩)
    exact (((a00.mul_right a01).mul_right (hC (mem_sup_left hx₀.2) hd.2)).mul_left
      ((a10.mul_right a11).mul_right (hC (mem_sup_right hx₁.2) hd.2))).mul_left
      ((a20.mul_right a21).mul_right a22)
  intro x hx y hy
  have hxM := hR.le hx
  have hyM := hR.le hy
  have hπ : uc22p21cPi M (⟨x, hxM⟩ * ⟨y, hyM⟩ * (⟨y, hyM⟩ * ⟨x, hxM⟩)⁻¹) = 1 := by
    simp only [map_mul, map_inv]
    rw [(hbar _ (uc22p21c_mem_barImage.2 ⟨_, hx, rfl⟩) _
      (uc22p21c_mem_barImage.2 ⟨_, hy, rfl⟩)).eq, mul_inv_cancel]
  have hmemR : (⟨x, hxM⟩ * ⟨y, hyM⟩ * (⟨y, hyM⟩ * ⟨x, hxM⟩)⁻¹ : ↥M) ∈ R.subgroupOf M := by
    rw [Subgroup.mem_subgroupOf]
    exact R.mul_mem (R.mul_mem hx hy) (R.inv_mem (R.mul_mem hy hx))
  have h1 := Subgroup.disjoint_def.1 (IsPGroup.disjoint_of_ne _ _ hr2 _ _
    hR.isPGroup.comap_subtype CFSG.pCore_isPGroup) hmemR ((QuotientGroup.eq_one_iff _).1 hπ)
  have h2 := congrArg Subtype.val h1
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one] at h2
  exact mul_inv_eq_one.1 h2

theorem uc22r3k_exists_omega {M L K : Subgroup G}
    (hL : L ∈ calC M) (hK : K ∈ calC M) (hne : K ≠ L) (hset : conjSetOf M L = {L, K}) {n : ℕ}
    (hS : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hrn : ¬ r ∣ n) (hrL : r ∣ Nat.card L) (hr3 : CFSG.Open.pRank r M ≤ 3) {R : Subgroup G}
    (hR : CFSG.ABGLocalTools.IsSylowOf r R M) :
    ∃ B : Subgroup G, B ≤ R ∧ R ≤ centralizer (B : Set G) ∧ IsElemAbelian r B ∧
      ∀ x ∈ R, x ^ r = 1 → x ∈ B := by
  have hc := uc22r3k_comm hL hK hne hset hS hr hr2 hrn hrL hr3 hR
  have hBR : closure {x | x ∈ R ∧ x ^ r = 1} ≤ R := (closure_le _).2 fun x hx => hx.1
  refine ⟨_, hBR, fun y hy => mem_centralizer_iff.2 fun x hx => hc x (hBR hx) y hy, ?_,
    fun x hx hx1 => subset_closure ⟨hx, hx1⟩⟩
  exact IsElemAbelian.closure_of_commute (fun a ha b hb => hc a ha.1 b hb.1) fun a ha => ha.2

theorem uc22r3k_inf_centralizer_eq_bot {M L K : Subgroup G} (hL : L ∈ calC M) (hK : K ∈ calC M)
    (hne : K ≠ L) (hset : conjSetOf M L = {L, K}) {n : ℕ}
    (hS : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hrL : r ∣ Nat.card L) (hr3 : ¬ 3 ≤ CFSG.Open.pRank r M) {R : Subgroup G}
    (hR : CFSG.ABGLocalTools.IsSylowOf r R M) :
    barImage M R ⊓ centralizer
      ((barImage M L ⊔ barImage M K : Subgroup (Bar2 M)) : Set (Bar2 M)) = ⊥ := by
  have : Fact r.Prime := ⟨hr⟩
  set H := barImage M R ⊓ centralizer
    ((barImage M L ⊔ barImage M K : Subgroup (Bar2 M)) : Set (Bar2 M))
  by_contra hne'
  have hP : IsPGroup r H := (u4x_isSylowOf_barImage hR).isPGroup.to_inf_left
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hP
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hne' (Subgroup.eq_bot_of_card_eq _ (by rw [hk, pow_zero]))
  obtain ⟨c, hco⟩ := exists_prime_orderOf_dvd_card' (G := ↥H) r
    (by rw [hk]; exact dvd_pow_self r hk0)
  have hcc : Nat.card (zpowers (c : Bar2 M)) = r := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hco]
  have h := uc22r3k_le_pRank hL hK hne hset hS hr hr2 hrL hR (zpowers_le.2 c.2)
    (CFSG.GroupTheory.isElemAbelian_of_card_prime hcc) (j := 1) (by rw [hcc, pow_one])
  omega

theorem uc22r3k_barImage_le_sup {M L K : Subgroup G}
    (hL : L ∈ calC M) (hK : K ∈ calC M) (hne : K ≠ L) (hset : conjSetOf M L = {L, K}) {n : ℕ}
    (hS : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hrn : ¬ r ∣ n) (hrL : r ∣ Nat.card L) (hr3 : ¬ 3 ≤ CFSG.Open.pRank r M) {R : Subgroup G}
    (hR : CFSG.ABGLocalTools.IsSylowOf r R M) : barImage M R ≤ barImage M L ⊔ barImage M K := by
  intro β hβ
  obtain ⟨x₀, hx₀, x₁, hx₁, c, hc, rfl⟩ := uc22r3k_decomp hL hK hne hset hS hr hr2 hrn hR hβ
  rw [uc22r3k_inf_centralizer_eq_bot hL hK hne hset hS hr hr2 hrL hr3 hR] at hc
  rw [Subgroup.mem_bot.1 hc, mul_one]
  exact mul_mem (mem_sup_left hx₀.2) (mem_sup_right hx₁.2)

end CFSG.LocalAnalysis.UniquenessCase.UC22
