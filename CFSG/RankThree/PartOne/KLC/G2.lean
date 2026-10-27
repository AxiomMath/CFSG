module

public import CFSG.RankThree.PartOne.KLC.Vacuity
public import CFSG.RankThree.PartOne.S11c.Sec66G2Sub
public import CFSG.RankThree.PartOne.S11d.LieCentralizerTags
public import CFSG.RankThree.PartOne.KLC.PRankTwo
public import CFSG.RankThree.Chevalley.SteinbergBIE7ThreeA1
public import CFSG.RankThree.SubgroupLists.CentralizerPerfect

public section

namespace CFSG.RankThree.PartOne.KLC

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.Chevalley CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.Sec66T
open scoped MatrixGroups

section RankTwo

variable {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] in
theorem eq_one_of_forall_commute_sl2 {b : SL2 K} (hb : ∀ A : SL2 K, b * A = A * b) : b = 1 := by
  have hcent : b ∈ Subgroup.center (SL2 K) := Subgroup.mem_center_iff.2 fun g => (hb g).symm
  obtain ⟨r, hr, hrb⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hcent
  have hr2 : r ^ 2 = 1 := by simpa using hr
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hr1 : r = 1 := by
    have h0 : (r - 1) ^ 2 = 0 := by linear_combination hr2 + (1 - r) * h2
    exact sub_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h0)
  subst hr1
  apply Subtype.ext
  rw [← hrb]
  simp

theorem two_le_pRank_of_orth_roots {β γ : Fin τ.rank → ℤ}
    (hcomm : ∀ A B : SL2 K, Commute (rootSL2 τ K β A) (rootSL2 τ K γ B))
    {p : ℕ} (hp : p.Prime) (hdvd : p ∣ Nat.card K ^ 2 - 1) {G : Type*} [Group G] [Finite G]
    (e : G ≃* adjointGroup τ K) : 2 ≤ CFSG.pRank p G := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hcard : p ∣ Nat.card (SL2 K) := by
    rw [CFSG.RankThree.SubgroupLists.card_sl2_field]
    exact Dvd.dvd.mul_left hdvd _
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' p hcard
  have hap : a ^ p = 1 := by
    rw [← ha]
    exact pow_orderOf_eq_one a
  have hadj : ∀ (r : Fin τ.rank → ℤ) (A : SL2 K), rootSL2 τ K r A ∈ adjointGroup τ K := fun r A =>
    (exceptional_Lang_root_rank_one_data τ K r).2.2.2.2.1 A
  have hinjβ := rootSL2_injective_of_field (τ := τ) (K := K) β
  have hinjγ := rootSL2_injective_of_field (τ := τ) (K := K) γ
  set u₁ : adjointGroup τ K := ⟨rootSL2 τ K β a, hadj β a⟩ with hu₁
  set u₂ : adjointGroup τ K := ⟨rootSL2 τ K γ a, hadj γ a⟩ with hu₂
  have hu₁p : u₁ ^ p = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, hu₁, ← map_pow, hap, map_one]
    rfl)
  have hu₂p : u₂ ^ p = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, hu₂, ← map_pow, hap, map_one]
    rfl)
  have hu₁₂ : Commute u₁ u₂ := Subtype.ext (hcomm a a).eq
  refine two_le_pRank_of_two_commuting hp (e₁ := e.symm u₁) (e₂ := e.symm u₂) (hu₁₂.map e.symm.toMonoidHom)
    (by rw [← map_pow, hu₁p, map_one]) (by rw [← map_pow, hu₂p, map_one]) ?_
  intro i j hij
  have h1 : u₁ ^ i * u₂ ^ j = 1 := by
    apply e.symm.injective
    rw [map_mul, map_zpow, map_zpow, hij, map_one]
  have h2 : rootSL2 τ K β (a ^ i) * rootSL2 τ K γ (a ^ j) = 1 := by
    have := congrArg Subtype.val h1
    simpa [hu₁, hu₂, map_zpow] using this
  have hβγ : rootSL2 τ K β (a ^ i) = (rootSL2 τ K γ (a ^ j))⁻¹ := eq_inv_of_mul_eq_one_left h2
  have hγβ : rootSL2 τ K γ (a ^ j) = (rootSL2 τ K β (a ^ i))⁻¹ := eq_inv_of_mul_eq_one_right h2
  have hai : a ^ i = 1 := by
    refine eq_one_of_forall_commute_sl2 fun A => hinjβ ?_
    rw [map_mul, map_mul, hβγ]
    exact ((hcomm A (a ^ j)).inv_right).symm.eq
  have haj : a ^ j = 1 := by
    refine eq_one_of_forall_commute_sl2 fun B => hinjγ ?_
    rw [map_mul, map_mul, hγβ]
    exact ((hcomm (a ^ i) B).inv_left).eq
  rw [← ha]
  exact ⟨(orderOf_dvd_iff_zpow_eq_one).2 hai, (orderOf_dvd_iff_zpow_eq_one).2 haj⟩

end RankTwo

section Roots

@[expose] def g2OrthBeta : Fin Tag.G2.rank → ℤ := ![0, 1]

@[expose] def g2OrthGamma : Fin Tag.G2.rank → ℤ := ![2, 3]

theorem g2Orth_isRoot : IsRoot Tag.G2 g2OrthBeta ∧ IsRoot Tag.G2 g2OrthGamma := by
  rw [isRoot_iff_mem_artifactRoots, isRoot_iff_mem_artifactRoots]
  unfold g2OrthBeta g2OrthGamma
  decide +kernel

theorem g2Orth_orth : iform g2OrthBeta g2OrthGamma = 0 := by
  unfold g2OrthBeta g2OrthGamma
  decide +kernel

theorem g2Orth_not_isRoot :
    ¬ IsRoot Tag.G2 (g2OrthBeta + g2OrthGamma) ∧ ¬ IsRoot Tag.G2 (g2OrthBeta - g2OrthGamma) := by
  have h : List.ofFn (g2OrthBeta + g2OrthGamma) ∉ Tag.G2.artifactRoots ∧
      List.ofFn (g2OrthBeta - g2OrthGamma) ∉ Tag.G2.artifactRoots := by
    unfold g2OrthBeta g2OrthGamma
    decide +kernel
  exact ⟨fun hv => h.1 (isRoot_iff_mem_artifactRoots.1 hv),
    fun hv => h.2 (isRoot_iff_mem_artifactRoots.1 hv)⟩

theorem g2Orth_commute {K : Type} [Field K] (A B : SL2 K) :
    Commute (rootSL2 Tag.G2 K g2OrthBeta A) (rootSL2 Tag.G2 K g2OrthGamma B) :=
  rootSL2_commute_of_orth g2Orth_isRoot.1 g2Orth_isRoot.2 g2Orth_orth g2Orth_not_isRoot.1
    g2Orth_not_isRoot.2 A B

end Roots

section Main

theorem dvd_sub_one_or_dvd_add_one {p Q : ℕ} (hp : p.Prime) (hQ : 1 ≤ Q) (h : p ∣ Q ^ 2 - 1) :
    p ∣ Q - 1 ∨ p ∣ Q + 1 := by
  obtain ⟨q, rfl⟩ : ∃ q, Q = q + 1 := ⟨Q - 1, by omega⟩
  have e : (q + 1) ^ 2 - 1 = (q + 1 - 1) * (q + 1 + 1) := by
    rw [Nat.add_sub_cancel, Nat.sub_eq_iff_eq_add (Nat.one_le_pow _ _ (by omega))]
    ring
  rw [e] at h
  exact (Nat.Prime.dvd_mul hp).1 h

theorem not_dvd_two_pow {p m : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) : ¬ p ∣ 2 ^ m := by
  intro h
  have h2 : p ∣ 2 := hp.dvd_of_dvd_pow h
  have := Nat.le_of_dvd (by norm_num) h2
  omega

theorem lieGoodComponentFixT_G2 :
    LieGoodComponentFixT .G2 := by
  intro T _ _ p hp hp5 hLR hpr n f₀ hf₀ hM α hαp hαinn hLRA hX x hxp hx1 hαx y hy2 hy1 hxy
  exfalso
  obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := exists_adjoint_equiv untwistedTag_G2 hM
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype K := Fintype.ofFinite K
  have hchar : CharP K 2 :=
    charP_of_card_eq_prime_pow (f := p * f₀) (by rw [← Nat.card_eq_fintype_card]; exact hKcard)
  have h0 : ¬ p ∣ Nat.card K := by
    rw [hKcard]
    exact not_dvd_two_pow hp hp5
  have hK1 : 1 ≤ Nat.card K := Nat.card_pos
  by_cases h12 : p ∣ Nat.card K ^ 2 - 1
  · have h2 := two_le_pRank_of_orth_roots (τ := Tag.G2) (K := K) g2Orth_commute hp h12 e
    omega
  · have h1 : ¬ p ∣ Nat.card K - 1 := fun h => h12 (by
      obtain ⟨c, hc⟩ := h
      refine ⟨c * (Nat.card K + 1), ?_⟩
      have : Nat.card K ^ 2 - 1 = (Nat.card K - 1) * (Nat.card K + 1) := by
        obtain ⟨q, hq⟩ : ∃ q, Nat.card K = q + 1 := ⟨Nat.card K - 1, by omega⟩
        rw [hq, Nat.add_sub_cancel, Nat.sub_eq_iff_eq_add (Nat.one_le_pow _ _ (by omega))]
        ring
      rw [this, hc]
      ring)
    have h2 : ¬ p ∣ Nat.card K + 1 := fun h => h12 (by
      obtain ⟨c, hc⟩ := h
      refine ⟨c * (Nat.card K - 1), ?_⟩
      have : Nat.card K ^ 2 - 1 = (Nat.card K - 1) * (Nat.card K + 1) := by
        obtain ⟨q, hq⟩ : ∃ q, Nat.card K = q + 1 := ⟨Nat.card K - 1, by omega⟩
        rw [hq, Nat.add_sub_cancel, Nat.sub_eq_iff_eq_add (Nat.one_le_pow _ _ (by omega))]
        ring
      rw [this, hc]
      ring)
    have hx' : orderOf (e x) = p := by
      rw [MulEquiv.orderOf_eq]
      exact orderOf_eq_prime hxp hx1
    have hy2' : (e y) ^ 2 = 1 := by rw [← map_pow, hy2, map_one]
    have hy1' : (e y : ModGL Tag.G2 K) ≠ 1 := fun h =>
      hy1 (e.injective (Subtype.ext (by simpa using h)))
    have hxy' : ((e x : adjointGroup Tag.G2 K) : ModGL Tag.G2 K) * (e y : ModGL Tag.G2 K) =
        (e y : ModGL Tag.G2 K) * (e x : ModGL Tag.G2 K) := by
      have := congrArg (fun z => (e z : ModGL Tag.G2 K)) hxy
      simpa [map_mul] using this
    exact no_commuting_of_not_dvd_parabolic (τ := Tag.G2) (K := K) (e x).2 (e y).2
      (by rw [Subgroup.orderOf_coe]; exact hx') (by simpa using congrArg Subtype.val hy2')
      hy1' hxy' (fun J hJ => g2Sub_not_dvd_card_parabolic hp h0 h1 h2 hJ)

end Main

end CFSG.RankThree.PartOne.KLC
