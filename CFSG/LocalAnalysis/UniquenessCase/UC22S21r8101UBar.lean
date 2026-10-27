module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rU4XD
import CFSG.LocalAnalysis.UniquenessCase.UC22S21rU4XI
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Cong
import CFSG.LocalAnalysis.UniquenessCase.UC22OddPRank
import CFSG.LocalAnalysis.UniquenessCase.UC1K31
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.InnerTorusFacts
import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
import CFSG.Adapters.StatedClassicalSmallOrders
import CFSG.GroupTheory.SupCommute

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

section Generic

variable {Q : Type} [Group Q] [Finite Q]

theorem u81_card_outer_dvd {X : Type} [Group X] [Finite X] {n : ℕ}
    (hX : IsL2 X n ∨ IsSz X n) :
    Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer X) ∣ n := by
  rcases hX with h | h
  · exact card_outer_dvd_of_isL2 h
  · obtain ⟨-, -, a, ha, K, _, _, rfl, hK, ⟨e⟩⟩ := CFSG.Blueprint.LieModel.suzukiModel h
    rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]
    exact (CFSG.LieType.Suzuki.suzukiGroup_outer_isCyclic_card_dvd ha hK).2

theorem u81_inner_mem {S F : Subgroup Q} {r : ℕ} [Fact r.Prime]
    (hS : CFSG.ABGLocalTools.IsSylowOf r S ⊤) (hSN : S ≤ normalizer (F : Set Q))
    (hZ : center ↥F = ⊥)
    (hinn : ∀ α : MulAut ↥F, α ^ Nat.card S = 1 → α ∈ (MulAut.conj : ↥F →* MulAut ↥F).range)
    {β : Q} (hβ : β ∈ S) : ∃ x ∈ S ⊓ F, ∀ f ∈ F, β * f * β⁻¹ = x * f * x⁻¹ := by
  have hr : r.Prime := Fact.out
  have hβq : β ^ Nat.card S = 1 := congrArg Subtype.val (pow_card_eq_one' (x := (⟨β, hβ⟩ : ↥S)))
  obtain ⟨x, hxF, hxq, hconj⟩ := u4x_inner_part hZ hinn (hSN hβ) hβq
  have hP : CFSG.ABGLocalTools.IsSylowOf r (S ⊓ F) F :=
    (hS.of_le hSN le_top).inf_of_le_normalizer Subgroup.le_normalizer le_rfl
  have hxN : zpowers x ≤ normalizer ((S ⊓ F : Subgroup Q) : Set Q) := by
    refine zpowers_le.2 (Subgroup.mem_normalizer_fintype fun s hs => ?_)
    rw [← hconj s hs.2]
    exact ⟨S.mul_mem (S.mul_mem hβ hs.1) (S.inv_mem hβ),
      (Subgroup.mem_normalizer_iff.1 (hSN hβ) s).1 hs.2⟩
  have hxp : IsPGroup r (zpowers x) := by
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 hS.isPGroup
    rw [hm] at hxq
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hr).1 (orderOf_dvd_of_pow_eq_one hxq)
    exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  have heq : S ⊓ F ⊔ zpowers x = S ⊓ F := hP.eq_of_le le_sup_left
    (sup_le hP.le (zpowers_le.2 hxF)) (hP.isPGroup.to_sup_of_normal_left' hxp hxN)
  refine ⟨x, ?_, hconj⟩
  rw [← heq]
  exact mem_sup_right (mem_zpowers x)

theorem u81_card_eq_of_isSylowOf {P F : Subgroup Q} {r : ℕ} [Fact r.Prime]
    (hP : CFSG.ABGLocalTools.IsSylowOf r P F) (h1 : r ∣ Nat.card F) (h2 : ¬ r ^ 2 ∣ Nat.card F) :
    Nat.card P = r := by
  have hr : r.Prime := Fact.out
  have hF : Nat.card F ≠ 0 := Nat.card_pos.ne'
  have a := (hr.dvd_iff_one_le_factorization hF).1 h1
  have b : (Nat.card F).factorization r < 2 :=
    not_le.1 fun h => h2 ((hr.pow_dvd_iff_le_factorization hF).2 h)
  rw [hP.card_eq, show (Nat.card F).factorization r = 1 by omega, pow_one]

theorem u81_le_pRank {F₀ F₁ P₀ P₁ E : Subgroup Q} {r j : ℕ} [Fact r.Prime]
    (hcomm : ∀ x ∈ F₀, ∀ y ∈ F₁, x * y = y * x) (hinf : F₀ ⊓ F₁ = ⊥)
    (hXC : (F₀ ⊔ F₁) ⊓ centralizer ((F₀ ⊔ F₁ : Subgroup Q) : Set Q) = ⊥)
    (h₀ : P₀ ≤ F₀) (h₁ : P₁ ≤ F₁) (hc₀ : Nat.card P₀ = r) (hc₁ : Nat.card P₁ = r)
    (hE : E ≤ centralizer ((F₀ ⊔ F₁ : Subgroup Q) : Set Q)) (hEel : IsElemAbelian r E)
    (hEc : Nat.card E = r ^ j) : 2 + j ≤ CFSG.Open.pRank r (⊤ : Subgroup Q) := by
  have hr : r.Prime := Fact.out
  have hc : ∀ a ∈ P₀, ∀ b ∈ P₁, Commute a b := fun a ha b hb => hcomm a (h₀ ha) b (h₁ hb)
  have hd : P₀ ⊓ P₁ = ⊥ := eq_bot_iff.2 fun x hx => by
    rw [← hinf]
    exact ⟨h₀ hx.1, h₁ hx.2⟩
  have hX : P₀ ⊔ P₁ ≤ F₀ ⊔ F₁ := sup_le_sup h₀ h₁
  have hc' : ∀ a ∈ P₀ ⊔ P₁, ∀ b ∈ E, Commute a b := fun a ha b hb =>
    Subgroup.mem_centralizer_iff.1 (hE hb) a (hX ha)
  have hd' : (P₀ ⊔ P₁) ⊓ E = ⊥ := eq_bot_iff.2 fun x hx => by
    rw [← hXC]
    exact ⟨hX hx.1, hE hx.2⟩
  have hel : IsElemAbelian r (P₀ ⊔ P₁ ⊔ E) :=
    ((CFSG.GroupTheory.isElemAbelian_of_card_prime hc₀).sup_of_commute
      (CFSG.GroupTheory.isElemAbelian_of_card_prime hc₁) hc).sup_of_commute hEel hc'
  refine CFSG.SectionRank.le_pRank hr.one_lt le_top hel ?_
  rw [CFSG.card_sup_eq_mul_of_commute _ _ hc' hd', CFSG.card_sup_eq_mul_of_commute _ _ hc hd,
    hc₀, hc₁, hEc]
  ring

end Generic

theorem u81_dvd_card {X : Type} [Group X] {n : ℕ}
    (h : (n = 3 ∧ IsL2 X n) ∨ (n = 5 ∧ IsSz X n)) :
    2 ^ n - 1 ∣ Nat.card X ∧ ¬ (2 ^ n - 1) ^ 2 ∣ Nat.card X := by
  rcases h with ⟨rfl, h⟩ | ⟨rfl, h⟩
  · rw [CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_two
      (CFSG.Blueprint.LieModel.statedClassicalModel h (by decide))]
    norm_num
  · rw [CFSG.LocalAnalysis.EvenBN.GMSK.card_of_lieModel_twistedB2 h]
    norm_num

namespace U4X

variable {D : Data G} {L K : Subgroup G} {n : ℕ}

theorem u81_le_normalizer (u : U4X D L K n) {R : Subgroup G}
    (hR : CFSG.ABGLocalTools.IsSylowOf (2 ^ n - 1) R D.M) :
    barImage D.M R ≤ normalizer (barImage D.M L : Set (Bar2 D.M)) := by
  intro y hy
  obtain ⟨m, hm, rfl⟩ := uc22p21c_mem_barImage.1 hy
  refine uc22ine229_mk_mem_normalizer (uc22p2214_mem_normalizer_of_odd u.hc2 m.2 ?_)
  obtain ⟨k, hk⟩ := hR.isPGroup ⟨m, hm⟩
  have h1 : orderOf (m : G) ∣ (2 ^ n - 1) ^ k := by
    rw [← Subgroup.orderOf_mk (m : G) hm]
    exact orderOf_dvd_of_pow_eq_one hk
  exact (u.prime_r.odd_of_ne_two u.r_ne_two).pow.of_dvd_nat h1

theorem u81_inner (u : U4X D L K n) {R : Subgroup G}
    (hR : CFSG.ABGLocalTools.IsSylowOf (2 ^ n - 1) R D.M) (α : MulAut ↥(barImage D.M L))
    (hα : α ^ Nat.card ↥(barImage D.M R) = 1) :
    α ∈ (MulAut.conj : ↥(barImage D.M L) →* MulAut ↥(barImage D.M L)).range := by
  haveI : Fact (2 ^ n - 1).Prime := ⟨u.prime_r⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (u4x_isSylowOf_barImage hR).isPGroup
  have hrn : 2 ^ n - 1 ≠ n := by rcases u.hLS with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> norm_num
  have hcop : Nat.Coprime (Nat.card ↥(barImage D.M R)) n := by
    rw [hk]
    exact Nat.Coprime.pow_left k ((Nat.coprime_primes u.prime_r u.prime_n).2 hrn)
  exact mem_inner_of_pow_eq_one_of_coprime_card_outer hα
    (Nat.Coprime.coprime_dvd_right (u81_card_outer_dvd (u4x_shape_barImage u.hL u.shape)) hcop)

theorem u81_inner_part (u : U4X D L K n) {R : Subgroup G}
    (hR : CFSG.ABGLocalTools.IsSylowOf (2 ^ n - 1) R D.M) {β : Bar2 D.M}
    (hβ : β ∈ barImage D.M R) :
    ∃ x ∈ barImage D.M R ⊓ barImage D.M L, ∀ f ∈ barImage D.M L, β * f * β⁻¹ = x * f * x⁻¹ := by
  haveI : Fact (2 ^ n - 1).Prime := ⟨u.prime_r⟩
  obtain ⟨-, -, h₀, -⟩ := u4x_bar_structure u.hL u.hK u.hne u.hset u.shape
  exact u81_inner_mem (u4x_isSylowOf_barImage hR) (u.u81_le_normalizer hR) h₀ (u.u81_inner hR) hβ

theorem u81_decomp (u : U4X D L K n) {R : Subgroup G}
    (hR : CFSG.ABGLocalTools.IsSylowOf (2 ^ n - 1) R D.M) {β : Bar2 D.M}
    (hβ : β ∈ barImage D.M R) :
    ∃ x₀ ∈ barImage D.M R ⊓ barImage D.M L, ∃ x₁ ∈ barImage D.M R ⊓ barImage D.M K,
      ∃ c ∈ barImage D.M R ⊓ centralizer
        ((barImage D.M L ⊔ barImage D.M K : Subgroup (Bar2 D.M)) : Set (Bar2 D.M)),
      β = x₀ * x₁ * c := by
  obtain ⟨hcomm, -⟩ := u4x_bar_structure u.hL u.hK u.hne u.hset u.shape
  obtain ⟨x₀, hx₀, h₀⟩ := u.u81_inner_part hR hβ
  obtain ⟨x₁, hx₁, h₁⟩ := u.symm.u81_inner_part hR hβ
  have hc : Commute β (x₀ * x₁) :=
    (u4x_commute_of_conj hx₀.2 h₀).mul_right (u4x_commute_of_conj hx₁.2 h₁)
  have hm : β * (x₀ * x₁)⁻¹ ∈ barImage D.M R :=
    Subgroup.mul_mem _ hβ (Subgroup.inv_mem _ (Subgroup.mul_mem _ hx₀.1 hx₁.1))
  refine ⟨x₀, hx₀, x₁, hx₁, _, ⟨hm, u4x_mul_inv_mem_centralizer hcomm hx₀.2 hx₁.2 h₀ h₁⟩, ?_⟩
  rw [← mul_assoc, ← hc.eq, mul_inv_cancel_right]

theorem u81_card_inf (u : U4X D L K n) {R : Subgroup G}
    (hR : CFSG.ABGLocalTools.IsSylowOf (2 ^ n - 1) R D.M) :
    Nat.card ↥(barImage D.M R ⊓ barImage D.M L) = 2 ^ n - 1 := by
  haveI : Fact (2 ^ n - 1).Prime := ⟨u.prime_r⟩
  obtain ⟨e, -⟩ := uc22p22l_barImage_equiv u.hL
  obtain ⟨h1, h2⟩ := u81_dvd_card u.hLS
  rw [Nat.card_congr e.toEquiv] at h1 h2
  exact u81_card_eq_of_isSylowOf (((u4x_isSylowOf_barImage hR).of_le (u.u81_le_normalizer hR)
    le_top).inf_of_le_normalizer Subgroup.le_normalizer le_rfl) h1 h2

theorem u81_isCyclic (u : U4X D L K n)
    (hr3 : CFSG.Open.pRank (2 ^ n - 1) D.M ≤ 3) {R : Subgroup G}
    (hR : CFSG.ABGLocalTools.IsSylowOf (2 ^ n - 1) R D.M) :
    IsCyclic ↥(barImage D.M R ⊓ centralizer
      ((barImage D.M L ⊔ barImage D.M K : Subgroup (Bar2 D.M)) : Set (Bar2 D.M))) := by
  haveI : Fact (2 ^ n - 1).Prime := ⟨u.prime_r⟩
  have hr := u.prime_r
  have hS := u4x_isSylowOf_barImage hR
  obtain ⟨hcomm, hinf, -, -, -, -, hXC⟩ := u4x_bar_structure u.hL u.hK u.hne u.hset u.shape
  refine UCK.K31.isCyclic_of_pRank_le_one hr u.r_ne_two hS.isPGroup.to_inf_left
    (CFSG.SectionRank.pRank_le hr.one_lt fun E hE hEel => ?_)
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.1 (hS.isPGroup.to_le (hE.trans inf_le_left))
  have h := u81_le_pRank hcomm hinf hXC inf_le_right inf_le_right (u.u81_card_inf hR)
    (u.symm.u81_card_inf hR) (hE.trans inf_le_right) hEel hj
  rw [pRank_bar2_eq_of_odd hr u.r_ne_two] at h
  rw [hj]
  exact Nat.pow_le_pow_right hr.pos (by omega)

theorem u81_comm (u : U4X D L K n)
    (hr3 : CFSG.Open.pRank (2 ^ n - 1) D.M ≤ 3) {R : Subgroup G}
    (hR : CFSG.ABGLocalTools.IsSylowOf (2 ^ n - 1) R D.M) :
    ∀ x ∈ R, ∀ y ∈ R, x * y = y * x := by
  haveI : Fact (2 ^ n - 1).Prime := ⟨u.prime_r⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := u.u81_isCyclic hr3 hR
  obtain ⟨hcomm, -⟩ := u4x_bar_structure u.hL u.hK u.hne u.hset u.shape
  have h₀ := CFSG.GroupTheory.isElemAbelian_of_card_prime (u.u81_card_inf hR)
  have h₁ := CFSG.GroupTheory.isElemAbelian_of_card_prime (u.symm.u81_card_inf hR)
  have hC : ∀ {a b : Bar2 D.M}, a ∈ barImage D.M L ⊔ barImage D.M K →
      b ∈ centralizer ((barImage D.M L ⊔ barImage D.M K : Subgroup (Bar2 D.M)) : Set (Bar2 D.M)) →
      Commute a b := fun ha hb => Subgroup.mem_centralizer_iff.1 hb _ ha
  have hbar : ∀ β ∈ barImage D.M R, ∀ γ ∈ barImage D.M R, Commute β γ := by
    intro β hβ γ hγ
    obtain ⟨x₀, hx₀, x₁, hx₁, c, hc, rfl⟩ := u.u81_decomp hR hβ
    obtain ⟨y₀, hy₀, y₁, hy₁, d, hd, rfl⟩ := u.u81_decomp hR hγ
    have a00 : Commute x₀ y₀ := h₀.comm hx₀ hy₀
    have a01 : Commute x₀ y₁ := hcomm x₀ hx₀.2 y₁ hy₁.2
    have a10 : Commute x₁ y₀ := (hcomm y₀ hy₀.2 x₁ hx₁.2).symm
    have a11 : Commute x₁ y₁ := h₁.comm hx₁ hy₁
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
  have h1 := Subgroup.disjoint_def.1 (IsPGroup.disjoint_of_ne _ _ u.r_ne_two _ _
    hR.isPGroup.comap_subtype CFSG.pCore_isPGroup) hmemR ((QuotientGroup.eq_one_iff _).1 hπ)
  have h2 := congrArg Subtype.val h1
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one] at h2
  exact mul_inv_eq_one.1 h2

end U4X

end CFSG.LocalAnalysis.UniquenessCase.UC22
