module

public import CFSG.RankThree.PartTwo.Sec4.Item424ProofField
import CFSG.RankThree.PartTwo.KFacts.K71Lift
import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

namespace Item424Proof

variable {G : Type} [Group G] [Finite G]

theorem mem_thetaQuotCentralizer_iff_eq_one {L : Subgroup G} {x : G} :
    x ∈ thetaQuotCentralizer L ↔ ∃ hx : x ∈ Subgroup.normalizer (L : Set G),
      thetaQuotMulAut L (compAction L ⟨x, hx⟩) = 1 := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

theorem mem_theta_of_mem_thetaQuotCentralizer {L : Subgroup G}
    (hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥) {x : G} (hxL : x ∈ L)
    (hx : x ∈ thetaQuotCentralizer L) : x ∈ inSubgroup (aschbacherSolvableCore 3) L := by
  obtain ⟨hxN, h1⟩ := mem_thetaQuotCentralizer_iff_eq_one.mp hx
  rw [KFacts.thetaQuotMulAut_compAction_of_mem hxL hxN] at h1
  have hc : (QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨x, hxL⟩) ∈
      Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) := by
    rw [Subgroup.mem_center_iff]
    intro y
    have := congrArg (fun φ : MulAut (L ⧸ aschbacherSolvableCore 3 L) => φ y) h1
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc y * QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨x, hxL⟩ =
        (QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨x, hxL⟩ * y *
          (QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨x, hxL⟩)⁻¹) *
            QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨x, hxL⟩ := by rw [this]
      _ = _ := by group
  rw [hZ, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hc
  exact ⟨_, hc, rfl⟩

end Item424Proof

open Item424Proof

namespace Config424

variable {G : Type} [Group G] [Finite G] {A L : Subgroup G} {a c : G} {K : Subgroup G}

theorem exists_c₀_of_inner (h45 : Item4_5) (h : Config424 G A L a c K)
    (hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥)
    (hinner : ¬ InducesOuterTheta c L) :
    ∃ c₀ ∈ A, c₀ ∈ L ∧ ∃ i : ℤ, c = c₀ * a ^ i := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAN := h.le_normalizer h45
  have hcN : c ∈ Subgroup.normalizer (L : Set G) := hAN h.c_mem
  set T := thetaQuotCentralizer L with hT
  set θL := inSubgroup (aschbacherSolvableCore 3) L with hθL
  set τ := thetaQuotMulAut L (compAction L ⟨c, hcN⟩) with hτ
  have hτinn : τ ∈ (MulAut.conj : L ⧸ aschbacherSolvableCore 3 L →* _).range := by
    by_contra hn
    exact hinner ⟨hcN, hn⟩
  obtain ⟨xb, hxb⟩ := hτinn
  obtain ⟨ℓ, rfl⟩ := QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 L) xb
  have key : ∀ (y : G) (hy : y ∈ L), y⁻¹ * c ∈ T ↔
      thetaQuotMulAut L (compAction L ⟨y, Subgroup.le_normalizer hy⟩) = τ := by
    intro y hy
    have hyN : y ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hy
    have hyc : y⁻¹ * c ∈ Subgroup.normalizer (L : Set G) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ hyN) hcN
    have e : (⟨y⁻¹ * c, hyc⟩ : Subgroup.normalizer (L : Set G)) = ⟨y, hyN⟩⁻¹ * ⟨c, hcN⟩ :=
      rfl
    rw [mem_thetaQuotCentralizer_iff_eq_one]
    constructor
    · rintro ⟨_, h1⟩
      rw [e, map_mul, map_mul, map_inv, map_inv] at h1
      exact (inv_mul_eq_one.mp h1).symm.trans rfl |>.symm
    · intro h1
      refine ⟨hyc, ?_⟩
      rw [e, map_mul, map_mul, map_inv, map_inv, h1, inv_mul_cancel]
  have hℓ : (ℓ : G)⁻¹ * c ∈ T := by
    rw [key ℓ ℓ.2, KFacts.thetaQuotMulAut_compAction_of_mem ℓ.2]
    exact hxb
  let α : A →* MulAut G := MulAut.conj.comp A.subtype
  have hθ3 : ¬ 3 ∣ Nat.card θL := not_three_dvd_card_theta L
  have hcoset : ∀ x : G, (ℓ : G)⁻¹ * x ∈ θL → x ∈ L ∧ x⁻¹ * c ∈ T := by
    intro x hx
    have hxL : x ∈ L := by
      have := L.mul_mem ℓ.2 (Sec6.theta_le L hx)
      simpa using this
    refine ⟨hxL, ?_⟩
    have e : x⁻¹ * c = ((ℓ : G)⁻¹ * x)⁻¹ * ((ℓ : G)⁻¹ * c) := by group
    rw [e]
    exact T.mul_mem (T.inv_mem (Sec6.theta_le_thetaQuotCentralizer L hx)) hℓ
  have hcoset' : ∀ x : G, x ∈ L → x⁻¹ * c ∈ T → (ℓ : G)⁻¹ * x ∈ θL := by
    intro x hxL hx
    refine mem_theta_of_mem_thetaQuotCentralizer hZ (L.mul_mem (L.inv_mem ℓ.2) hxL) ?_
    have e : (ℓ : G)⁻¹ * x = ((ℓ : G)⁻¹ * c) * (x⁻¹ * c)⁻¹ := by group
    rw [e]
    exact T.mul_mem hℓ (T.inv_mem hx)
  obtain ⟨y, hyℓ, hyfix⟩ := (CFSG.Semidihedral.Principal.coprime_invariant_coset_fixed 3
    h.isPGroup α θL hθ3 ℓ).2 (by
      intro b x hx
      obtain ⟨hxL, hxc⟩ := hcoset x hx
      have hbN : (b : G) ∈ Subgroup.normalizer (L : Set G) := hAN b.2
      refine hcoset' _ ?_ ?_
      · exact (Subgroup.mem_normalizer_iff.mp hbN x).mp hxL
      · have hbc : (b : G) * c = c * b := h.comm b b.2 c h.c_mem
        have e : ((b : G) * x * (b : G)⁻¹)⁻¹ * c = (b : G) * (x⁻¹ * c) * (b : G)⁻¹ := by
          calc ((b : G) * x * (b : G)⁻¹)⁻¹ * c = (b : G) * x⁻¹ * ((b : G)⁻¹ * c) := by group
            _ = (b : G) * x⁻¹ * (c * (b : G)⁻¹) := by
                rw [show (b : G)⁻¹ * c = c * (b : G)⁻¹ by
                  calc (b : G)⁻¹ * c = (b : G)⁻¹ * (c * b) * (b : G)⁻¹ := by group
                    _ = (b : G)⁻¹ * (b * c) * (b : G)⁻¹ := by rw [hbc]
                    _ = c * (b : G)⁻¹ := by group]
            _ = (b : G) * (x⁻¹ * c) * (b : G)⁻¹ := by group
        show ((b : G) * x * (b : G)⁻¹)⁻¹ * c ∈ T
        rw [e]
        exact Sec6.conj_mem_thetaQuotCentralizer hxc hbN)
  obtain ⟨hyL, hyc⟩ := hcoset y hyℓ
  have hyA : ∀ b ∈ A, b * y = y * b := by
    intro b hb
    have := hyfix ⟨b, hb⟩
    change b * y * b⁻¹ = y at this
    calc b * y = (b * y * b⁻¹) * b := by group
      _ = y * b := by rw [this]
  have hyc' : y * c = c * y := (hyA c h.c_mem).symm
  have hy3 : y ^ 3 ∈ θL := by
    refine mem_theta_of_mem_thetaQuotCentralizer hZ (L.pow_mem hyL 3) ?_
    have e : (y⁻¹ * c) ^ 3 = (y ^ 3)⁻¹ := by
      rw [(Commute.inv_left (show Commute y c from hyc')).mul_pow, inv_pow,
        h.pow_three c h.c_mem, mul_one]
    have := T.pow_mem hyc 3
    rw [e] at this
    exact inv_inv (y ^ 3) ▸ T.inv_mem this
  set k := orderOf (y ^ 3) with hk
  have hk3 : ¬ 3 ∣ k := fun h3 => hθ3 (h3.trans (Subgroup.orderOf_dvd_natCard θL hy3))
  have hkk : (k * k) % 3 = 1 := by
    have : k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases this with h1 | h1 <;> simp [Nat.mul_mod, h1]
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : G, c₀ = y ^ (k * k) := ⟨_, rfl⟩
  have hc₀3 : c₀ ^ 3 = 1 := by
    rw [hc₀, ← pow_mul, show k * k * 3 = 3 * k * k by ring, pow_mul, pow_mul, hk,
      pow_orderOf_eq_one, one_pow]
  have hc₀A : c₀ ∈ A := mem_of_maximal_of_commute h.maximal hc₀3 fun b hb => by
    rw [hc₀]
    exact (Commute.pow_right (show Commute b y from hyA b hb) _).eq
  have hc₀L : c₀ ∈ L := by rw [hc₀]; exact L.pow_mem hyL _
  have hc₀c : c₀⁻¹ * c ∈ T := by
    obtain ⟨m, hm⟩ : ∃ m, k * k = 3 * m + 1 := ⟨k * k / 3, by omega⟩
    have e : (y⁻¹ * c) ^ (k * k) = c₀⁻¹ * c := by
      rw [(Commute.inv_left (show Commute y c from hyc')).mul_pow, inv_pow, ← hc₀, hm,
        pow_succ, pow_mul, h.pow_three c h.c_mem, one_pow, one_mul]
    rw [← e]
    exact T.pow_mem hyc _
  have hc₀cA : c₀⁻¹ * c ∈ A ⊓ T := ⟨A.mul_mem (A.inv_mem hc₀A) h.c_mem, hc₀c⟩
  rw [h.inf_thetaQuotCentralizer hAN] at hc₀cA
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hc₀cA
  exact ⟨c₀, hc₀A, hc₀L, i, by rw [hi]; group⟩

theorem inner_structure (h45 : Item4_5) (h : Config424 G A L a c K)
    (hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥)
    (hinner : ¬ InducesOuterTheta c L) :
    ∃ c₀ d : G, ∃ i : ℤ, c = c₀ * a ^ i ∧ A ⊓ K = Subgroup.zpowers d ∧ orderOf d = 3 ∧
      c₀ ∈ A ∧ c₀ ∈ L ∧ c₀ ≠ 1 ∧ d ∉ Subgroup.zpowers c₀ ∧
      A ⊓ L = Subgroup.closure {c₀, d} ∧ Nat.card (Subgroup.closure ({c₀, d} : Set G)) = 9 ∧
      A = Subgroup.closure {a, c₀, d} := by
  obtain ⟨c₀, hc₀A, hc₀L, i, hci⟩ := h.exists_c₀_of_inner h45 hZ hinner
  obtain ⟨d, hdK, hd3, hdB, hA⟩ := h.exists_d h45
  have hdAK : d ∈ A ⊓ K := by rw [hdK]; exact Subgroup.mem_zpowers d
  have hdA : d ∈ A := hdAK.1
  have hdL : d ∈ L := h.K_le_L hdAK.2
  have hc₀B : c₀ ∈ Subgroup.closure ({a, c} : Set G) := by
    have e : c₀ = c * a ^ (-i) := by rw [hci]; group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
      (Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp)) _)
  have hc₀1 : c₀ ≠ 1 := by
    intro h1
    apply h.c_not_mem
    rw [hci, h1, one_mul]
    exact Subgroup.zpow_mem_zpowers a i
  have hdc₀ : d ∉ Subgroup.zpowers c₀ := fun hd =>
    hdB ((Subgroup.zpowers_le.mpr hc₀B) hd)
  have h9 := card_closure_pair_eq_nine h.isElemAbelian h.card_eq hc₀A hdA hc₀1 hdc₀
  have hDle : Subgroup.closure ({c₀, d} : Set G) ≤ A ⊓ L := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact ⟨hc₀A, hc₀L⟩
    · exact ⟨hdA, hdL⟩
  have haL : a ∉ L := fun haL => h.a_ne_one
    (h.eq_one_of_mem_zpowers_a_of_mem_L hZ (Subgroup.mem_zpowers a) haL)
  have hAL : A ⊓ L = Subgroup.closure {c₀, d} := by
    have hdvd : Nat.card (A ⊓ L : Subgroup G) ∣ 27 :=
      h.card_eq ▸ Subgroup.card_dvd_of_le inf_le_left
    have h9d : 9 ∣ Nat.card (A ⊓ L : Subgroup G) := h9 ▸ Subgroup.card_dvd_of_le hDle
    have hne : Nat.card (A ⊓ L : Subgroup G) ≠ 27 := by
      intro h27
      apply haL
      have heq : A ⊓ L = A := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h27, h.card_eq])
      have haAL : a ∈ A ⊓ L := by rw [heq]; exact h.a_mem
      exact haAL.2
    have hc : Nat.card (A ⊓ L : Subgroup G) = 9 := by
      have : Nat.card (A ⊓ L : Subgroup G) ∈ Nat.divisors 27 :=
        Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
      have hd : Nat.divisors 27 = {1, 3, 9, 27} := by decide
      rw [hd] at this
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      omega
    exact (Subgroup.eq_of_le_of_card_ge hDle (by rw [hc, h9])).symm
  have hac₀ : Subgroup.closure ({a, c₀} : Set G) = Subgroup.closure {a, c} := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      intro x hx
      rcases hx with rfl | rfl
      · exact Subgroup.subset_closure (by simp)
      · exact hc₀B
    · rw [Subgroup.closure_le]
      intro x hx
      rcases hx with rfl | rfl
      · exact Subgroup.subset_closure (by simp)
      · rw [hci]
        exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
          (Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp)) _)
  have hA' : A = Subgroup.closure {a, c₀, d} :=
    eq_closure_triple h.card_eq h.a_mem hc₀A hdA (hac₀ ▸ h.card_closure_pair) (hac₀ ▸ hdB)
  exact ⟨c₀, d, i, hci, hdK, hd3, hc₀A, hc₀L, hc₀1, hdc₀, hAL, h9, hA'⟩

end Config424

end CFSG.RankThree.PartTwo.Sec4
