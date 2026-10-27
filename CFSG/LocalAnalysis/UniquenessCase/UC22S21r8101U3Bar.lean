module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rU4PA
import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8101UBar
import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8100Res2
import CFSG.LocalAnalysis.UniquenessCase.UC22P20v
import CFSG.LocalAnalysis.UniquenessCase.UC22P22ry
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Cong
import CFSG.LocalAnalysis.UniquenessCase.UC22OddPRank
import CFSG.LocalAnalysis.UniquenessCase.UC1K31
import CFSG.LocalAnalysis.UniquenessCase.UC6S898b
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.InnerTorusFacts
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsThirtyEightOq
import CFSG.RankThree.PartOne.Q1327S.Arith

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem u4p_eq_five_or_eleven_le {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hev : Even n)
    (hpd : p ∣ 2 ^ n + 1) : p = 5 ∨ 11 ≤ p := by
  have h3 : p ≠ 3 := by
    rintro rfl
    exact UC6S898.not_three_dvd_two_pow_add_one_of_even hev hpd
  have h7 : p ≠ 7 := CFSG.RankThree.PartOne.Q1327S.ne_seven_of_dvd_two_pow_add_one hpd
  have h2 := hp.two_le
  rcases lt_or_ge p 11 with h11 | h11
  · left
    interval_cases p <;> first | rfl | omega | exact absurd hp (by norm_num)
  · exact Or.inr h11

namespace U4P

variable {D : Data G} {L K : Subgroup G} {n p : ℕ}

theorem prime_p (u : U4P D L K n p) : p.Prime := (D.sig_prime p u.hσ).1

theorem p_ne_two (u : U4P D L K n p) : p ≠ 2 := (D.sig_prime p u.hσ).2

theorem p_dvd_n (u : U4P D L K n p) : p ∣ n := by
  obtain ⟨k, -, hn⟩ := u.hk
  rw [hn]
  exact dvd_mul_left p _

theorem not_sq_dvd_n (u : U4P D L K n p) : ¬ p ^ 2 ∣ n := by
  obtain ⟨k, -, hn⟩ := u.hk
  rw [hn, sq]
  intro h
  have h1 : p ∣ 2 ^ k := Nat.dvd_of_mul_dvd_mul_right u.prime_p.pos h
  exact u.p_ne_two ((Nat.prime_dvd_prime_iff_eq u.prime_p Nat.prime_two).1
    (u.prime_p.dvd_of_dvd_pow h1))

theorem p_dvd_card (u : U4P D L K n p) : p ∣ Nat.card (Bar2 L) := by
  have e : (2 ^ n) ^ 2 - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by rw [← Nat.sq_sub_sq, one_pow]
  rw [uc22p22r_L2_card u.hL2, e]
  exact ((uc22r8100b_dvd_of_modEq u.hcong).mul_right _).mul_left _

theorem p_eq_five_or_eleven_le (u : U4P D L K n p) : p = 5 ∨ 11 ≤ p := by
  have hev : Even n := by
    obtain ⟨k, hk, hn⟩ := u.hk
    rw [hn]
    exact (Nat.even_pow.2 ⟨even_two, hk.ne'⟩).mul_right p
  exact u4p_eq_five_or_eleven_le u.prime_p u.p_ne_two hev (uc22r8100b_dvd_of_modEq u.hcong)

theorem r_ne_two (u : U4P D L K n p) {r : ℕ} (hr : r.Prime) (hrp : r ∣ 2 ^ p - 1) : r ≠ 2 :=
  uc22p20v_ne_two_of_dvd_sub_one u.prime_p.one_lt.le hr hrp

theorem not_dvd_n (u : U4P D L K n p) {r : ℕ} (hr : r.Prime) (hrp : r ∣ 2 ^ p - 1) : ¬ r ∣ n := by
  obtain ⟨k, -, hn⟩ := u.hk
  rw [hn]
  intro h
  rcases (Nat.Prime.dvd_mul hr).1 h with h | h
  · exact u.r_ne_two hr hrp ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h))
  · obtain rfl := (Nat.prime_dvd_prime_iff_eq hr u.prime_p).1 h
    exact UC6S898.not_dvd_two_pow_sub_one_self hr hrp

theorem r_dvd_two_pow (u : U4P D L K n p) {r : ℕ} (hrp : r ∣ 2 ^ p - 1) : r ∣ 2 ^ n - 1 :=
  hrp.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 u.p_dvd_n)

theorem isL2_barImage (u : U4P D L K n p) : IsL2 ↥(barImage D.M L) n := by
  obtain ⟨e, -⟩ := uc22p22l_barImage_equiv u.hL
  exact CFSG.Blueprint.LieModel.of_mulEquiv e u.hL2

theorem isMulCommutative_outer (u : U4P D L K n p) :
    IsMulCommutative (CFSG.ComponentClassification.OuterAutomorphisms.Outer
      ↥(barImage D.M L)) := by
  haveI := P22y.isCyclic_outer_of_isL2Ev (IsL2.isL2Ev u.isL2_barImage)
  infer_instance

theorem u81_le_normalizer (u : U4P D L K n p) {r : ℕ} (hr : r.Prime) (hrp : r ∣ 2 ^ p - 1)
    {R : Subgroup G} (hR : CFSG.ABGLocalTools.IsSylowOf r R D.M) :
    barImage D.M R ≤ normalizer (barImage D.M L : Set (Bar2 D.M)) := by
  intro y hy
  obtain ⟨m, hm, rfl⟩ := uc22p21c_mem_barImage.1 hy
  refine uc22ine229_mk_mem_normalizer (uc22p2214_mem_normalizer_of_odd u.hc2 m.2 ?_)
  obtain ⟨k, hk⟩ := hR.isPGroup ⟨m, hm⟩
  have h1 : orderOf (m : G) ∣ r ^ k := by
    rw [← Subgroup.orderOf_mk (m : G) hm]
    exact orderOf_dvd_of_pow_eq_one hk
  exact (hr.odd_of_ne_two (u.r_ne_two hr hrp)).pow.of_dvd_nat h1

theorem u81_inner (u : U4P D L K n p) {r : ℕ} (hr : r.Prime) (hrp : r ∣ 2 ^ p - 1)
    {R : Subgroup G} (hR : CFSG.ABGLocalTools.IsSylowOf r R D.M) (α : MulAut ↥(barImage D.M L))
    (hα : α ^ Nat.card ↥(barImage D.M R) = 1) :
    α ∈ (MulAut.conj : ↥(barImage D.M L) →* MulAut ↥(barImage D.M L)).range := by
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (u4x_isSylowOf_barImage hR).isPGroup
  have hcop : Nat.Coprime (Nat.card ↥(barImage D.M R)) n := by
    rw [hk]
    exact Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hr).2 (u.not_dvd_n hr hrp))
  exact mem_inner_of_pow_eq_one_of_coprime_card_outer hα
    (Nat.Coprime.coprime_dvd_right (card_outer_dvd_of_isL2 u.isL2_barImage) hcop)

theorem u81_inner_part (u : U4P D L K n p) {r : ℕ} (hr : r.Prime) (hrp : r ∣ 2 ^ p - 1)
    {R : Subgroup G} (hR : CFSG.ABGLocalTools.IsSylowOf r R D.M) {β : Bar2 D.M}
    (hβ : β ∈ barImage D.M R) :
    ∃ x ∈ barImage D.M R ⊓ barImage D.M L, ∀ f ∈ barImage D.M L, β * f * β⁻¹ = x * f * x⁻¹ := by
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨-, -, h₀, -⟩ := u4x_bar_structure u.hL u.hK u.hne u.hset u.shape
  exact u81_inner_mem (u4x_isSylowOf_barImage hR) (u.u81_le_normalizer hr hrp hR) h₀
    (u.u81_inner hr hrp hR) hβ

theorem u81_decomp (u : U4P D L K n p) {r : ℕ} (hr : r.Prime) (hrp : r ∣ 2 ^ p - 1)
    {R : Subgroup G} (hR : CFSG.ABGLocalTools.IsSylowOf r R D.M) {β : Bar2 D.M}
    (hβ : β ∈ barImage D.M R) :
    ∃ x₀ ∈ barImage D.M R ⊓ barImage D.M L, ∃ x₁ ∈ barImage D.M R ⊓ barImage D.M K,
      ∃ c ∈ barImage D.M R ⊓ centralizer
        ((barImage D.M L ⊔ barImage D.M K : Subgroup (Bar2 D.M)) : Set (Bar2 D.M)),
      β = x₀ * x₁ * c := by
  obtain ⟨hcomm, -⟩ := u4x_bar_structure u.hL u.hK u.hne u.hset u.shape
  obtain ⟨x₀, hx₀, h₀⟩ := u.u81_inner_part hr hrp hR hβ
  obtain ⟨x₁, hx₁, h₁⟩ := u.symm.u81_inner_part hr hrp hR hβ
  have hc : Commute β (x₀ * x₁) :=
    (u4x_commute_of_conj hx₀.2 h₀).mul_right (u4x_commute_of_conj hx₁.2 h₁)
  have hm : β * (x₀ * x₁)⁻¹ ∈ barImage D.M R :=
    Subgroup.mul_mem _ hβ (Subgroup.inv_mem _ (Subgroup.mul_mem _ hx₀.1 hx₁.1))
  refine ⟨x₀, hx₀, x₁, hx₁, _, ⟨hm, u4x_mul_inv_mem_centralizer hcomm hx₀.2 hx₁.2 h₀ h₁⟩, ?_⟩
  rw [← mul_assoc, ← hc.eq, mul_inv_cancel_right]

theorem u81_exists_mem_inf (u : U4P D L K n p) {r : ℕ} (hr : r.Prime) (hrp : r ∣ 2 ^ p - 1)
    {R : Subgroup G} (hR : CFSG.ABGLocalTools.IsSylowOf r R D.M) :
    ∃ a ∈ R ⊓ L, orderOf a = r := by
  have hr2 := u.r_ne_two hr hrp
  haveI : Fact r.Prime := ⟨hr⟩
  have hRN : R ≤ normalizer (L : Set G) := fun g hg => by
    obtain ⟨k, hk⟩ := hR.isPGroup ⟨g, hg⟩
    have hg3 : g ^ r ^ k = 1 := congrArg Subtype.val hk
    exact uc22p2214_mem_normalizer_of_odd u.hc2 (hR.le hg)
      ((hr.odd_of_ne_two hr2).pow.of_dvd_nat (orderOf_dvd_of_pow_eq_one hg3))
  have hRL := (hR.of_le (le_inf hR.le hRN) inf_le_left).inf_of_le_normalizer
    (le_inf u.hL.1.le Subgroup.le_normalizer) inf_le_right
  have hne : R ⊓ L ≠ ⊥ := by
    intro hbot
    have hv : 1 ≤ (Nat.card L).factorization r :=
      (Nat.Prime.dvd_iff_one_le_factorization hr Nat.card_pos.ne').1
        (u.dvd_card_of_dvd (u.r_dvd_two_pow hrp))
    have hc := hRL.card_eq
    rw [hbot, Subgroup.card_bot] at hc
    have h1 : r ^ 1 ≤ r ^ (Nat.card L).factorization r := Nat.pow_le_pow_right hr.pos hv
    rw [pow_one] at h1
    exact lt_irrefl 1 (lt_of_lt_of_le hr.one_lt (h1.trans hc.symm.le))
  obtain ⟨a, ha, hao, -⟩ := CFSG.AGLEmbeddingD2.exists_orderOf_eq_mem_centralizer_of_le_normalizer
    hr hR.isPGroup inf_le_left ((le_inf Subgroup.le_normalizer hRN).trans
      Subgroup.inf_normalizer_le_normalizer_inf) hne
  exact ⟨a, ha, hao⟩

theorem u81_exists_orderOf_inf (u : U4P D L K n p) {r : ℕ} (hr : r.Prime) (hrp : r ∣ 2 ^ p - 1)
    {R : Subgroup G} (hR : CFSG.ABGLocalTools.IsSylowOf r R D.M) :
    ∃ x ∈ barImage D.M R ⊓ barImage D.M L, orderOf x = r := by
  obtain ⟨a, ha, hao⟩ := u.u81_exists_mem_inf hr hrp hR
  have haM : a ∈ D.M := hR.le ha.1
  exact ⟨_, ⟨uc22p21c_mem_barImage.2 ⟨⟨a, haM⟩, ha.1, rfl⟩,
    uc22p21c_mem_barImage.2 ⟨⟨a, haM⟩, ha.2, rfl⟩⟩,
    orderOf_bar_eq_of_prime haM hr (u.r_ne_two hr hrp) hao⟩

theorem u81_isCyclic_inf (u : U4P D L K n p) {r : ℕ} (hr : r.Prime) (hrp : r ∣ 2 ^ p - 1)
    {R : Subgroup G} (hR : CFSG.ABGLocalTools.IsSylowOf r R D.M) :
    IsCyclic ↥(barImage D.M R ⊓ barImage D.M L) := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hr2 := u.r_ne_two hr hrp
  refine UCK.K31.isCyclic_of_pRank_le_one hr hr2
    (u4x_isSylowOf_barImage hR).isPGroup.to_inf_left ?_
  refine (CFSG.SectionRank.pRank_mono hr.one_lt inf_le_right).trans ?_
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (barImage D.M L)]
  exact pRank_le_one_of_isL2_or_isSz (Or.inl u.isL2_barImage) hr hr2

theorem u81_isCyclic (u : U4P D L K n p) {r : ℕ} (hr : r.Prime) (hrp : r ∣ 2 ^ p - 1)
    (hr3 : CFSG.Open.pRank r D.M ≤ 3) {R : Subgroup G}
    (hR : CFSG.ABGLocalTools.IsSylowOf r R D.M) :
    IsCyclic ↥(barImage D.M R ⊓ centralizer
      ((barImage D.M L ⊔ barImage D.M K : Subgroup (Bar2 D.M)) : Set (Bar2 D.M))) := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hr2 := u.r_ne_two hr hrp
  have hS := u4x_isSylowOf_barImage hR
  obtain ⟨hcomm, hinf, -, -, -, -, hXC⟩ := u4x_bar_structure u.hL u.hK u.hne u.hset u.shape
  obtain ⟨x₀, hx₀, hx₀o⟩ := u.u81_exists_orderOf_inf hr hrp hR
  obtain ⟨x₁, hx₁, hx₁o⟩ := u.symm.u81_exists_orderOf_inf hr hrp hR
  refine UCK.K31.isCyclic_of_pRank_le_one hr hr2 hS.isPGroup.to_inf_left
    (CFSG.SectionRank.pRank_le hr.one_lt fun E hE hEel => ?_)
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.1 (hS.isPGroup.to_le (hE.trans inf_le_left))
  have h := u81_le_pRank hcomm hinf hXC (zpowers_le.2 hx₀.2) (zpowers_le.2 hx₁.2)
    (by rw [Nat.card_zpowers, hx₀o]) (by rw [Nat.card_zpowers, hx₁o]) (hE.trans inf_le_right)
    hEel hj
  rw [pRank_bar2_eq_of_odd hr hr2] at h
  rw [hj]
  exact Nat.pow_le_pow_right hr.pos (by omega)

theorem u81_comm (u : U4P D L K n p) {r : ℕ} (hr : r.Prime) (hrp : r ∣ 2 ^ p - 1)
    (hr3 : CFSG.Open.pRank r D.M ≤ 3) {R : Subgroup G}
    (hR : CFSG.ABGLocalTools.IsSylowOf r R D.M) :
    ∀ x ∈ R, ∀ y ∈ R, x * y = y * x := by
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hr2 := u.r_ne_two hr hrp
  haveI := u.u81_isCyclic hr hrp hr3 hR
  haveI := u.u81_isCyclic_inf hr hrp hR
  haveI := u.symm.u81_isCyclic_inf hr hrp hR
  obtain ⟨hcomm, -⟩ := u4x_bar_structure u.hL u.hK u.hne u.hset u.shape
  have hC : ∀ {a b : Bar2 D.M}, a ∈ barImage D.M L ⊔ barImage D.M K →
      b ∈ centralizer ((barImage D.M L ⊔ barImage D.M K : Subgroup (Bar2 D.M)) : Set (Bar2 D.M)) →
      Commute a b := fun ha hb => Subgroup.mem_centralizer_iff.1 hb _ ha
  have hbar : ∀ β ∈ barImage D.M R, ∀ γ ∈ barImage D.M R, Commute β γ := by
    intro β hβ γ hγ
    obtain ⟨x₀, hx₀, x₁, hx₁, c, hc, rfl⟩ := u.u81_decomp hr hrp hR hβ
    obtain ⟨y₀, hy₀, y₁, hy₁, d, hd, rfl⟩ := u.u81_decomp hr hrp hR hγ
    have a00 : Commute x₀ y₀ := congrArg Subtype.val
      (mul_comm' (⟨x₀, hx₀⟩ : ↥(barImage D.M R ⊓ barImage D.M L)) ⟨y₀, hy₀⟩)
    have a01 : Commute x₀ y₁ := hcomm x₀ hx₀.2 y₁ hy₁.2
    have a10 : Commute x₁ y₀ := (hcomm y₀ hy₀.2 x₁ hx₁.2).symm
    have a11 : Commute x₁ y₁ := congrArg Subtype.val
      (mul_comm' (⟨x₁, hx₁⟩ : ↥(barImage D.M R ⊓ barImage D.M K)) ⟨y₁, hy₁⟩)
    have a20 : Commute c y₀ := (hC (mem_sup_left hy₀.2) hc.2).symm
    have a21 : Commute c y₁ := (hC (mem_sup_right hy₁.2) hc.2).symm
    have a22 : Commute c d :=
      congrArg Subtype.val (mul_comm' (⟨c, hc⟩ : ↥(barImage D.M R ⊓ centralizer _)) ⟨d, hd⟩)
    exact (((a00.mul_right a01).mul_right (hC (mem_sup_left hx₀.2) hd.2)).mul_left
      ((a10.mul_right a11).mul_right (hC (mem_sup_right hx₁.2) hd.2))).mul_left
      ((a20.mul_right a21).mul_right a22)
  intro x hx y hy
  have hxM := hR.le hx
  have hyM := hR.le hy
  have hπ : uc22p21cPi D.M (⟨x, hxM⟩ * ⟨y, hyM⟩ * (⟨y, hyM⟩ * ⟨x, hxM⟩)⁻¹) = 1 := by
    simp only [map_mul, map_inv]
    rw [(hbar _ (uc22p21c_mem_barImage.2 ⟨_, hx, rfl⟩) _
      (uc22p21c_mem_barImage.2 ⟨_, hy, rfl⟩)).eq, mul_inv_cancel]
  have hmemR : (⟨x, hxM⟩ * ⟨y, hyM⟩ * (⟨y, hyM⟩ * ⟨x, hxM⟩)⁻¹ : ↥D.M) ∈ R.subgroupOf D.M := by
    rw [Subgroup.mem_subgroupOf]
    exact R.mul_mem (R.mul_mem hx hy) (R.inv_mem (R.mul_mem hy hx))
  have h1 := Subgroup.disjoint_def.1 (IsPGroup.disjoint_of_ne _ _ hr2 _ _
    hR.isPGroup.comap_subtype CFSG.pCore_isPGroup) hmemR ((QuotientGroup.eq_one_iff _).1 hπ)
  have h2 := congrArg Subtype.val h1
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one] at h2
  exact mul_inv_eq_one.1 h2

end U4P

end CFSG.LocalAnalysis.UniquenessCase.UC22
