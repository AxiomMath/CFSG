module

public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.RankThree.PartOne.S12.Sec1511Y1
public import CFSG.RankThree.PartOne.S12.Sec1511Y2W

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory

namespace Sec1511

@[expose] def KF1511A : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec15Hyp G p A c L E → Sec12Facts G p A c L E → Outcome152Five p E A (lieGenerated p E) →
    p = 5 → KAHyp p E (lieNormalizer p E) A

@[expose] def KFEI : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec15Hyp G p A c L E → Sec12Facts G p A c L E → Outcome152 p E A (lieGenerated p E) →
    ¬ Outcome152Five p E A (lieGenerated p E) → E ≤ lieGenerated p E

section Basic

variable {G : Type} [Group G] [Finite G]

theorem rank_le_three {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
    (h : Sec12Hyp G p A c L E) : ∀ F : Subgroup G, IsElementaryAbelian p ↥F →
      (∃ S : Subgroup G, S ≠ ⊥ ∧ IsPGroup 2 ↥S ∧ F ≤ Subgroup.normalizer (S : Set G)) →
        Nat.card ↥F ≤ p ^ 3 := by
  intro F hF ⟨S, hS1, hS2, hFS⟩
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := (IsElementaryAbelian.isPGroup p ↥F).exists_card_eq
  have hH : CFSG.Assembly.IsTwoLocal (Subgroup.normalizer (S : Set G)) := ⟨S, hS1, hS2, rfl⟩
  have h1 : k ≤ CFSG.Assembly.pRank p (Subgroup.normalizer (S : Set G)) :=
    CFSG.SectionRank.le_pRank hp.one_lt hFS
      ⟨hF.toIsMulCommutative, fun x hx => elemPow_eq_one_of_isElementaryAbelian (p := p) (A := F) x hx⟩
      hk
  have h2 : CFSG.Assembly.pRank p (Subgroup.normalizer (S : Set G)) ≤ CFSG.Assembly.evenRank G :=
    CFSG.RankThreeEvenClassification.Helpers.pRank_le_evenRank p hp
      (by have := h.three_lt; omega) _ hH
  rw [h.evenRank_eq] at h2
  rw [hk]
  exact Nat.pow_le_pow_right hp.pos (h1.trans h2)

theorem ne_top_of_two_local [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a) {Y : Subgroup G}
    (hY : ∃ S : Subgroup G, S ≠ ⊥ ∧ IsPGroup 2 ↥S ∧ Y ≤ Subgroup.normalizer (S : Set G)) :
    Y ≠ ⊤ := by
  obtain ⟨S, hS1, hS2, hYS⟩ := hY
  intro hYtop
  rw [hYtop, top_le_iff, Subgroup.normalizer_eq_top_iff] at hYS
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal S with h | h
  · exact hS1 h
  · have hG : IsPGroup 2 G := by
      subst h
      exact hS2.of_equiv Subgroup.topEquiv
    have : Group.IsNilpotent G := hG.isNilpotent
    have hsolv : Group.IsSolvable G := inferInstance
    obtain ⟨a, b, hab⟩ := hnab
    exact hab (IsSimpleGroup.comm_iff_isSolvable.2 hsolv a b)

omit [Finite G] in
theorem weyl154_perm_four {p : ℕ} {A E I : Subgroup G} (hEA : E = A) (hout : Outcome152 p E A I)
    {W₀ : Subgroup (MulAut ↥E)} (hW : Weyl154 p E W₀) :
    Nonempty (↥W₀ ≃* Equiv.Perm (Fin 4)) := by
  rcases hW.2.2.1 with h4 | ⟨⟨e⟩⟩
  · exact h4
  · exfalso
    have h4c : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm]
      simp [Nat.factorial]
    have h48 : Nat.card (Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)) = 48 := by
      rw [Nat.card_prod, h4c]
      have : Nat.card (Multiplicative (ZMod 2)) = 2 := by
        rw [Nat.card_eq_fintype_card]; decide
      rw [this]
    have hdvd : Nat.card ↥(reflectionGroup p E) ∣ 48 := by
      rcases hout with h1 | h2 | h3 | h4' | h5
      · obtain ⟨f, -, -, -, ⟨e'⟩, -, -⟩ := h1
        rw [Nat.card_congr e'.toEquiv, h4c]; norm_num
      · obtain ⟨f, -, -, -, ⟨e'⟩, -, -⟩ := h2
        rw [Nat.card_congr e'.toEquiv, h48]
      · obtain ⟨f, -, -, -, ⟨e'⟩, -, -⟩ := h3
        rw [Nat.card_congr e'.toEquiv, h48]
      · obtain ⟨f, -, -, -, ⟨e'⟩, -, -⟩ := h4'
        rw [Nat.card_congr e'.toEquiv, h48]
      · obtain ⟨f, -, -, -, -, -, hne, -⟩ := h5
        exact absurd hEA hne
    have h1 : Nat.card ↥W₀ ∣ Nat.card ↥(reflectionGroup p E) := Subgroup.card_dvd_of_le hW.2.1
    have h2 := h1.trans hdvd
    have h5 : Nat.card ↥W₀ = 120 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm]
      simp [Nat.factorial]
    rw [h5] at h2
    omega

omit [Finite G] in
theorem weyl154_hord6 {p : ℕ} {E : Subgroup G} {W₀ : Subgroup (MulAut ↥E)} (hW : Weyl154 p E W₀) :
    ∀ u ∈ W₀, orderOf u ≤ 6 := by
  have hS45 : Nonempty (↥W₀ ≃* Equiv.Perm (Fin 4)) ∨ Nonempty (↥W₀ ≃* Equiv.Perm (Fin 5)) := by
    obtain ⟨-, -, h, -, -, -⟩ := hW
    exact h
  rcases hS45 with h4 | h5
  · obtain ⟨e⟩ := h4
    exact fun u hu => (hord_perm4 e u hu).trans (by norm_num)
  · obtain ⟨e⟩ := h5
    exact hord_perm5 e

theorem centralizes_of_pPower_gen {p : ℕ} (hp : p.Prime) {E : Subgroup G}
    (hEexp : ∀ e ∈ E, e ^ p = 1) (hE1 : ∃ e ∈ E, e ≠ 1) {W₀ : Subgroup (MulAut ↥E)}
    (hW : Weyl154 p E W₀) {M₁ : ℕ} (hord : ∀ u ∈ W₀, orderOf u ≤ M₁) (hM₁ : M₁ < p) {g : G}
    (hg : g ∈ Subgroup.normalizer (E : Set G)) {k : ℕ} (hgk : g ^ (p ^ k) = 1) :
    ∀ e ∈ E, g * e = e * g := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set φ : MulAut ↥E := E.normalizerMonoidHom ⟨g, hg⟩ with hφ
  have hφW : φ ∈ torusWeyl E := ⟨⟨g, hg⟩, rfl⟩
  obtain ⟨z, u, hzW, huW, hφzu, hzc, kz, hkz⟩ := weyl_decomp hW φ hφW
  have hz1 : z ^ (p - 1) = 1 := scalar_pow_eq_one hp hEexp hE1 hkz
  have hW0le : W₀ ≤ torusWeyl E := by
    obtain ⟨-, -, -, hsup, -, -⟩ := hW
    exact hsup ▸ le_sup_right
  have huz : z * u = u * z := hzc u (hW0le huW)
  set m := orderOf u with hm
  have hm1 : 1 ≤ m := orderOf_pos u
  have hmp : m < p := (hord u huW).trans_lt hM₁
  set L := Nat.lcm (p - 1) m with hL
  have hu1 : u ^ L = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one]
    exact Nat.dvd_lcm_right _ _
  have hz1' : z ^ L = 1 := by
    obtain ⟨t, ht⟩ := Nat.dvd_lcm_left (p - 1) m
    rw [← hL] at ht
    rw [ht, pow_mul, hz1, one_pow]
  have hφL : φ ^ L = 1 := by
    rw [hφzu, (Commute.mul_pow (show Commute z u from huz) L), hz1', hu1, one_mul]
  have hφk : φ ^ (p ^ k) = 1 := by
    rw [hφ, ← map_pow]
    have : (⟨g, hg⟩ : ↥(Subgroup.normalizer (E : Set G))) ^ (p ^ k) = 1 := Subtype.ext hgk
    rw [this, map_one]
  have hpL : ¬ p ∣ L := by
    intro hdvd
    have h1 : p ∣ (p - 1) * m := hdvd.trans (Nat.lcm_dvd_mul _ _)
    rcases (Nat.Prime.dvd_mul hp).1 h1 with h2 | h2
    · have := Nat.le_of_dvd (by have := hp.two_le; omega) h2
      omega
    · have := Nat.le_of_dvd hm1 h2
      omega
  have hcop : Nat.Coprime (p ^ k) L :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2 hpL)
  have hφ1 : φ = 1 := by
    have := pow_gcd_eq_one.2 ⟨hφk, hφL⟩
    rwa [Nat.Coprime.gcd_eq_one hcop, pow_one] at this
  have hker : (⟨g, hg⟩ : ↥(Subgroup.normalizer (E : Set G))) ∈ E.normalizerMonoidHom.ker := hφ1
  rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at hker
  intro e he
  exact ((Subgroup.mem_centralizer_iff.1 hker) e he).symm

omit [Finite G] in
theorem omegaHyp_of_centralizes {p : ℕ} {E : Subgroup G}
    (hEel : IsElementaryAbelian p ↥E)
    (hmax : ∀ F : Subgroup G, IsElementaryAbelian p ↥F → E ≤ F → F = E)
    (hc : ∀ g ∈ Subgroup.normalizer (E : Set G), ∀ k : ℕ, g ^ (p ^ k) = 1 →
      ∀ e ∈ E, g * e = e * g) : OmegaHyp p E := by
  intro Q hEQ hQW hQp
  have hEexp : ∀ e ∈ E, e ^ p = 1 := fun e he =>
    elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) e he
  apply le_antisymm
  · refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨hxQ, hxp⟩
    have hxcomm : ∀ e ∈ E, x * e = e * x := hc x (hQW hxQ) 1 (by rwa [pow_one])
    have hzx : IsElementaryAbelian p ↥(Subgroup.zpowers x) :=
      IsElementaryAbelian.zpowers_of_pow_eq_one hxp
    have hF : IsElementaryAbelian p ↥(E ⊔ Subgroup.zpowers x) := by
      have := hEel
      have := hzx
      refine IsElementaryAbelian.sup_of_le_centralizer (E := E) (C := Subgroup.zpowers x) ?_
      intro y hy
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      exact (Commute.zpow_left (show Commute x e from hxcomm e he) j).eq.symm
    have heq := hmax _ hF le_sup_left
    have : x ∈ E ⊔ Subgroup.zpowers x := Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
    rwa [heq] at this
  · intro e he
    exact Subgroup.subset_closure ⟨hEQ he, hEexp e he⟩

end Basic

end Sec1511

end CFSG.RankThree.PartOne
