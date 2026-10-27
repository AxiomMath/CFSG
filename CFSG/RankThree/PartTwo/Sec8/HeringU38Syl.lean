module

import CFSG.RankThree.PartTwo.KFacts.K72List
import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofLink
import CFSG.RankThree.PartTwo.Sec11.Item113
import CFSG.RankThree.PartTwo.Sec8.Item87Res2Proof418
import CFSG.RankThree.GroupTheory.SteinbergBYHyperplaneResidual
public import CFSG.RankThree.PartTwo.Sec8.HeringU38Comm

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 (thetaQuotMulAut compAction InducesOuterTheta)
open scoped commutatorElement

@[expose] def u38Two {Ū : Type*} [Group Ū] (α : MulAut Ū) : Subgroup Ū :=
  Subgroup.closure {y | y ∈ u38Fix α ∧ ∃ k : ℕ, y ^ 2 ^ k = 1}

@[expose] def U38P3Model : Prop :=
  ∀ (Ū : Type) [Group Ū] [Finite Ū], IsUnitaryTwo Ū 3 →
    ∀ α β : MulAut Ū, α ^ 3 = 1 → β ^ 3 = 1 → α * β = β * α → ¬ KFacts.IsInnerAut α →
      Nat.card (u38Fix α) = 216 → (∃ u ∈ u38Fix α, u ^ 4 = 1 ∧ u ^ 2 ≠ 1) →
      β ≠ 1 → 7 ∣ Nat.card (u38Fix β) →
      ∀ x : Ū, x ≠ 1 → x ^ 3 = 1 → α x = x → β x = x →
        x ∈ (perfectResidual (u38Fix β)).map (u38Fix β).subtype →
        x ∈ u38Two α ∧ ∀ z ∈ u38Two α, (∃ j : ℕ, z ^ 3 ^ j = 1) →
          z ∈ Subgroup.closure {y | ∃ g ∈ u38Two α, y = g * x * g⁻¹}

variable {G : Type} [Group G] [Finite G]

theorem exists_two_element_lift {X Y : Type*} [Group X] [Group Y] [Finite X] (φ : X →* Y) {x : X}
    {k : ℕ} (hz : (φ x) ^ 2 ^ k = 1) :
    ∃ y : X, (∃ e : ℕ, y ^ 2 ^ e = 1) ∧ φ y = φ x ∧ ∃ u : ℕ, y = x ^ u := by
  obtain ⟨e, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
  have hcop : Nat.Coprime m (2 ^ k) := Nat.Coprime.pow_right k hm.coprime_two_right
  let u := (Nat.chineseRemainder hcop 0 1 : ℕ)
  have hu0 : u ≡ 0 [MOD m] := (Nat.chineseRemainder hcop 0 1).2.1
  have hu1 : u ≡ 1 [MOD 2 ^ k] := (Nat.chineseRemainder hcop 0 1).2.2
  refine ⟨x ^ u, ⟨e, ?_⟩, ?_, u, rfl⟩
  · obtain ⟨u₀, hu₀⟩ := (Nat.modEq_zero_iff_dvd.mp hu0)
    rw [← pow_mul, hu₀, show m * u₀ * 2 ^ e = (2 ^ e * m) * u₀ by ring, pow_mul, ← hn,
      pow_orderOf_eq_one, one_pow]
  · rw [map_pow, pow_eq_pow_mod u hz, hu1]
    by_cases hk : k = 0
    · subst hk
      simp only [pow_zero, pow_one] at hz
      simp [hz]
    · have : 1 % 2 ^ k = 1 := Nat.mod_eq_of_lt (Nat.one_lt_two_pow hk)
      rw [this, pow_one]

theorem imageModTheta_sec8I_eq {L : Subgroup G} {a : G}
    (haN : a ∈ Subgroup.normalizer (L : Set G)) (ha3 : a ^ 3 = 1)
    (hU : IsUnitaryTwo (L ⧸ aschbacherSolvableCore 3 L) 3) :
    imageModTheta L (sec8I L a) = u38Two (thetaQuotMulAut L (compAction L ⟨a, haN⟩)) := by
  classical
  set θ := aschbacherSolvableCore 3 L with hθ
  set q : L →* L ⧸ θ := QuotientGroup.mk' θ with hq
  have hIdef : sec8I L a = Subgroup.closure
      {y | y ∈ L ⊓ Subgroup.centralizer {a} ∧ ∃ k : ℕ, y ^ 2 ^ k = 1} := by
    simp only [sec8I, hU, ↓reduceIte]
  have hMeq := barCentralizer_eq_u38Fix haN
  have himg := KFacts.imageModTheta_centralizer_eq haN ⟨1, by rw [pow_one]; exact ha3⟩
  apply le_antisymm
  · rintro _ ⟨i, hi, rfl⟩
    have hi' : (i : G) ∈ sec8I L a := Subgroup.mem_subgroupOf.mp hi
    rw [hIdef] at hi'
    have key : ∀ g ∈ Subgroup.closure
        {y | y ∈ L ⊓ Subgroup.centralizer ({a} : Set G) ∧ ∃ k : ℕ, y ^ 2 ^ k = 1},
        ∃ hgL : g ∈ L, q ⟨g, hgL⟩ ∈ u38Two (thetaQuotMulAut L (compAction L ⟨a, haN⟩)) := by
      intro g hg
      induction hg using Subgroup.closure_induction with
      | mem y hy =>
        obtain ⟨hyC, k, hk⟩ := hy
        have hyL : y ∈ L := (Subgroup.mem_inf.mp hyC).1
        refine ⟨hyL, Subgroup.subset_closure ⟨?_, k, ?_⟩⟩
        · rw [← hMeq, ← himg]
          exact ⟨⟨y, hyL⟩, Subgroup.mem_subgroupOf.mpr hyC, rfl⟩
        · rw [← map_pow]
          have : (⟨y, hyL⟩ : L) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk)
          rw [this, map_one]
      | one =>
        refine ⟨Subgroup.one_mem _, ?_⟩
        have : (⟨1, Subgroup.one_mem L⟩ : L) = 1 := rfl
        rw [this, map_one]
        exact Subgroup.one_mem _
      | mul x y _ _ hx hy =>
        obtain ⟨hxL, hx⟩ := hx
        obtain ⟨hyL, hy⟩ := hy
        refine ⟨Subgroup.mul_mem _ hxL hyL, ?_⟩
        have : q ⟨x * y, Subgroup.mul_mem _ hxL hyL⟩ = q ⟨x, hxL⟩ * q ⟨y, hyL⟩ := by
          rw [← map_mul]
          rfl
        rw [this]
        exact Subgroup.mul_mem _ hx hy
      | inv x _ hx =>
        obtain ⟨hxL, hx⟩ := hx
        refine ⟨Subgroup.inv_mem _ hxL, ?_⟩
        have : q ⟨x⁻¹, Subgroup.inv_mem _ hxL⟩ = (q ⟨x, hxL⟩)⁻¹ := by
          rw [← map_inv]
          rfl
        rw [this]
        exact Subgroup.inv_mem _ hx
    obtain ⟨hiL, h⟩ := key (i : G) hi'
    exact h
  · rw [u38Two, Subgroup.closure_le]
    rintro z ⟨hzF, k, hk⟩
    have hzM : z ∈ barCentralizer (Subgroup.zpowers a) L := by rw [hMeq]; exact hzF
    rw [← himg] at hzM
    obtain ⟨x, hx, rfl⟩ := hzM
    obtain ⟨y, ⟨e, hye⟩, hyq, u, hyu⟩ := exists_two_element_lift q (x := x) hk
    have hxC : (x : G) ∈ L ⊓ Subgroup.centralizer ({a} : Set G) := Subgroup.mem_subgroupOf.mp hx
    have hyC : (y : G) ∈ L ⊓ Subgroup.centralizer ({a} : Set G) := by
      rw [hyu]
      simpa using Subgroup.pow_mem _ hxC u
    have hyI : (y : G) ∈ sec8I L a := by
      rw [hIdef]
      exact Subgroup.subset_closure ⟨hyC, e, by simpa using congrArg Subtype.val hye⟩
    exact ⟨y, Subgroup.mem_subgroupOf.mpr hyI, hyq⟩

theorem coprime_three_of_mem_theta {L : Subgroup G} {d : G}
    (hd : d ∈ (aschbacherSolvableCore 3 L).map L.subtype) : Nat.Coprime (orderOf d) 3 := by
  have h3 : ¬ 3 ∣ Nat.card ((aschbacherSolvableCore 3 L).map L.subtype) := by
    rw [Subgroup.card_map_of_injective L.subtype_injective]
    exact KFacts.not_three_dvd_card_aschbacherSolvableCore L
  have h1 : orderOf d ∣ Nat.card ((aschbacherSolvableCore 3 L).map L.subtype) := by
    have := orderOf_dvd_natCard (⟨d, hd⟩ : (aschbacherSolvableCore 3 L).map L.subtype)
    rwa [← Subgroup.orderOf_coe] at this
  exact Nat.Coprime.coprime_dvd_left h1
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3).symm

theorem mem_of_three_pow_mem {I Y : Subgroup G}
    (h : ∀ g ∈ I, (∃ j : ℕ, g ^ 3 ^ j = 1) → g ∈ Y) :
    ∀ i ∈ I, (∃ j : ℕ, i ^ 3 ^ j ∈ Y) → i ∈ Y := by
  rintro i hi ⟨j, hj⟩
  obtain ⟨e, m', hm', hm⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos i).ne' 3
    (by norm_num)
  have hcop : Nat.Coprime (3 ^ e) m' :=
    Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hm')
  have hzm : (i ^ 3 ^ e) ^ m' = 1 := by
    rw [← pow_mul, ← hm, pow_orderOf_eq_one]
  have hz : i ^ 3 ^ e ∈ Y := by
    rcases le_or_gt j e with hje | hje
    · have : i ^ 3 ^ e = (i ^ 3 ^ j) ^ 3 ^ (e - j) := by
        rw [← pow_mul, ← pow_add, Nat.add_sub_cancel' hje]
      rw [this]
      exact Subgroup.pow_mem _ hj _
    · have hcz : Nat.Coprime (3 ^ (j - e)) (orderOf (i ^ 3 ^ e)) :=
        Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hzm)
          (Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hm'))
      obtain ⟨w, hw⟩ := exists_pow_eq_self_of_coprime hcz
      have : (i ^ 3 ^ e) ^ 3 ^ (j - e) = i ^ 3 ^ j := by
        rw [← pow_mul, ← pow_add, Nat.add_sub_cancel' hje.le]
      rw [← hw, this]
      exact Subgroup.pow_mem _ hj _
  have hw : i ^ m' ∈ Y := by
    refine h _ (Subgroup.pow_mem _ hi _) ⟨e, ?_⟩
    rw [← pow_mul, mul_comm, ← hm, pow_orderOf_eq_one]
  obtain ⟨s, t, hst⟩ := Nat.isCoprime_iff_coprime.mpr hcop
  have hi' : i = (i ^ 3 ^ e) ^ s * (i ^ m') ^ t := by
    calc i = i ^ (1 : ℤ) := (zpow_one i).symm
      _ = i ^ (s * ((3 ^ e : ℕ) : ℤ) + t * (m' : ℤ)) := by rw [hst]
      _ = (i ^ 3 ^ e) ^ s * (i ^ m') ^ t := by
        rw [zpow_add, mul_comm s, mul_comm t, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]
  rw [hi']
  exact Subgroup.mul_mem _ (Subgroup.zpow_mem _ hz s) (Subgroup.zpow_mem _ hw t)


theorem u38_three_elt_mem
    (h45 : Sec4.Item4_5) (hP : U38P3Model)
    {A : Subgroup G} {c : G} {L : Subgroup G} {a b : G} {X : Subgroup G} {n : ℕ}
    (h : Sec8Pair G A c L a b X n) (hU : IsUnitaryTwo (L ⧸ aschbacherSolvableCore 3 L) 3)
    {Y : Subgroup G} (hJY : sec8J X a ≤ Y) (hIY : sec8I L a ≤ Subgroup.normalizer (Y : Set G)) :
    ∀ g ∈ sec8I L a, (∃ j : ℕ, g ^ 3 ^ j = 1) → g ∈ Y := by
  classical
  obtain ⟨haN, hbN, ha3, hb3, hab, haL, hCa, hu4, hβ1, h7, hθodd⟩ := u38_pair_data h45 h hU
  have hG := h.toTheoremFourHyp
  have hAab := h.mem_partTwoF.1
  have hAc : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hAab.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hbA : b ∈ A := h.isGammaIndex.1
  have hb1 : b ≠ 1 := h.isGammaIndex.2.1
  have hAp : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by simpa using hAab.2 g g.2)⟩
  have hAb : A ≤ Subgroup.centralizer ({b} : Set G) := fun u hu =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hAc u hu b hbA)
  have hXb : X ∈ thetaComponentsAt 3 b := h.pairRel.2.2.1
  have hAX : A ≤ Subgroup.normalizer (X : Set G) :=
    Sec11.le_normalizer_of_isPGroup_of_le_centralizer h45 hG hb3 hb1 hAp hAb X hXb
  have haX : a ∈ Subgroup.normalizer (X : Set G) := hAX h.a_mem
  obtain rfl := u38_n_eq_one h hU
  set θ := aschbacherSolvableCore 3 L with hθ
  set q : L →* L ⧸ θ := QuotientGroup.mk' θ with hq
  set K : Subgroup G := inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G))
    with hK
  have hKLb : K ≤ L ⊓ Subgroup.centralizer ({b} : Set G) := Item87Proof.residual_le _
  have hKL : K ≤ L := hKLb.trans inf_le_left
  have hKX : K ≤ X := h.pairRel.2.2.2.1
  have haK : a ∈ Subgroup.normalizer (K : Set G) := by
    have haC : a ∈ Subgroup.normalizer (Subgroup.centralizer ({b} : Set G) : Set G) :=
      Subgroup.le_normalizer (Subgroup.mem_centralizer_singleton_iff.mpr hab)
    have haLb : a ∈ Subgroup.normalizer
        ((L ⊓ Subgroup.centralizer {b} : Subgroup G) : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      rw [Subgroup.mem_inf, Subgroup.mem_inf, (Subgroup.mem_normalizer_iff.mp haN y),
        (Subgroup.mem_normalizer_iff.mp haC y)]
    exact GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_perfectResidual
      _ haLb
  have h3K : 3 ∣ Nat.card K := by
    have h504 := u38_K_card h hU
    have h1 : Nat.card (imageModTheta L K) ∣ Nat.card (K.subgroupOf L) :=
      Subgroup.card_map_dvd (H := K.subgroupOf L) (QuotientGroup.mk' θ)
    rw [h504, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKL).toEquiv] at h1
    exact (by norm_num : 3 ∣ 504).trans h1
  obtain ⟨x, ⟨hxK, hxCa⟩, hxord⟩ := KFacts.exists_mem_centralizer_orderOf_eq
    (Item87Res2Proof.isPGroup_zpowers_of_pow_three ha3) (Subgroup.zpowers_le.mpr haK) h3K
  have hxa : x ∈ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (Subgroup.mem_zpowers a)) hxCa
  have hx3 : x ^ 3 = 1 := by rw [← hxord]; exact pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hxord
    norm_num at hxord
  have hxb : x ∈ Subgroup.centralizer ({b} : Set G) := (Subgroup.mem_inf.mp (hKLb hxK)).2
  have hxJ : x ∈ sec8J X a := by
    have hRF : Item8KFacts2Proof.ResidualFacts (barCentralizer (Subgroup.zpowers a) X) := by
      rcases h.centralizer_of_unitary ⟨3, hU⟩ with hG2 | hSp
      · exact Item8KFacts2Proof.residualFacts_of_isoGTwoEven le_rfl hG2
      · obtain ⟨e⟩ := hSp
        exact Item8KFacts2Proof.ResidualFacts.of_mulEquiv e
          (Item8KFacts2Proof.residualFacts_projSp le_rfl)
    exact Item8KFacts2Proof.mem_inSubgroup_perfectResidual_of_pow_three haX ha3 hRF.1
      (hKX hxK) hxa hx3
  have hxY : x ∈ Y := hJY hxJ
  have hxL : x ∈ L := hKL hxK
  set α := thetaQuotMulAut L (compAction L ⟨a, haN⟩) with hα
  set β := thetaQuotMulAut L (compAction L ⟨b, hbN⟩) with hβ
  set xb : L ⧸ θ := q ⟨x, hxL⟩ with hxbdef
  have hαx : α xb = xb := by
    have h1 := Sec4.thetaQuotMulAut_mk (compAction L ⟨a, haN⟩) ⟨x, hxL⟩
    have h2 : compAction L ⟨a, haN⟩ ⟨x, hxL⟩ = ⟨x, hxL⟩ := by
      refine Subtype.ext ?_
      have := Subgroup.mem_centralizer_singleton_iff.mp hxa
      show a * x * a⁻¹ = x
      rw [← this, mul_inv_cancel_right]
    rw [h2] at h1
    exact h1
  have hβx : β xb = xb := by
    have h1 := Sec4.thetaQuotMulAut_mk (compAction L ⟨b, hbN⟩) ⟨x, hxL⟩
    have h2 : compAction L ⟨b, hbN⟩ ⟨x, hxL⟩ = ⟨x, hxL⟩ := by
      refine Subtype.ext ?_
      have := Subgroup.mem_centralizer_singleton_iff.mp hxb
      show b * x * b⁻¹ = x
      rw [← this, mul_inv_cancel_right]
    rw [h2] at h1
    exact h1
  have hxb3 : xb ^ 3 = 1 := by
    rw [hxbdef, ← map_pow]
    have : (⟨x, hxL⟩ : L) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
    rw [this, map_one]
  have hxb1 : xb ≠ 1 := by
    intro h1
    have hxθ : (⟨x, hxL⟩ : L) ∈ θ := (QuotientGroup.eq_one_iff _).mp h1
    have := KFacts.eq_one_of_mem_aschbacherSolvableCore_of_pow hxθ (j := 1)
      (by simpa using (Subtype.ext (by simpa using hx3) : (⟨x, hxL⟩ : L) ^ 3 = 1))
    exact hx1 (by simpa using congrArg Subtype.val this)
  have hxKbar : xb ∈ (perfectResidual (u38Fix β)).map (u38Fix β).subtype := by
    have h1 : xb ∈ imageModTheta L K := ⟨⟨x, hxL⟩, Subgroup.mem_subgroupOf.mpr hxK, rfl⟩
    rw [hK, KFacts.imageModTheta_perfectResidual_centralizer_eq hbN ⟨1, by rw [pow_one]; exact hb3⟩,
      barCentralizer_eq_u38Fix hbN] at h1
    exact h1
  obtain ⟨hxTwo, hP3⟩ := hP (L ⧸ aschbacherSolvableCore 3 L) hU α β
    (u38_pow_eq_one haN ha3) (u38_pow_eq_one hbN hb3) (u38_mul_comm haN hbN hab)
    (by obtain ⟨hx, hnot⟩ := haL; exact fun hin => hnot hin)
    (by rw [← barCentralizer_eq_u38Fix haN]; exact hCa)
    (by
      obtain ⟨u, hu, h4, h2⟩ := hu4
      exact ⟨u, by rwa [barCentralizer_eq_u38Fix haN] at hu, h4, h2⟩)
    hβ1 (by rw [← barCentralizer_eq_u38Fix hbN]; exact h7) xb hxb1 hxb3 hαx hβx hxKbar
  set I : Subgroup G := sec8I L a with hI
  have hIC : I ≤ L ⊓ Subgroup.centralizer ({a} : Set G) := Item812Res7.sec8I_le L a
  have hIL : I ≤ L := hIC.trans inf_le_left
  have hIeq : imageModTheta L I = u38Two α := imageModTheta_sec8I_eq haN ha3 hU
  have hxbI : xb ∈ imageModTheta L I := by rw [hIeq]; exact hxTwo
  obtain ⟨i, hi, hiq⟩ := hxbI
  have hiI : (i : G) ∈ I := Subgroup.mem_subgroupOf.mp hi
  have hθ' : i⁻¹ * (⟨x, hxL⟩ : L) ∈ θ := by
    have h1 : (i : L ⧸ θ) = ((⟨x, hxL⟩ : L) : L ⧸ θ) := hiq
    exact QuotientGroup.eq.mp h1
  have hθ'G : (i : G)⁻¹ * x ∈ θ.map L.subtype := ⟨i⁻¹ * ⟨x, hxL⟩, hθ', rfl⟩
  have hdC : (i : G)⁻¹ * x ∈ L ⊓ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (hIC hiI)) (Subgroup.mem_inf.mpr ⟨hxL, hxa⟩)
  have hxI : x ∈ I := by
    refine HeringU38.mem_of_mul_coprime (θ := (i : G)⁻¹ * x) (n := (i : G))
      (Item812Res7.mem_normalizer_sec8I (Subgroup.le_normalizer hdC)) hiI ?_ (by group)
    rw [hxord]
    exact coprime_three_of_mem_theta hθ'G
  set W : Subgroup G := I ⊓ Y with hW
  have hxW : x ∈ W := Subgroup.mem_inf.mpr ⟨hxI, hxY⟩
  have hWN : ∀ d ∈ I, d ∈ Subgroup.normalizer (W : Set G) := by
    intro d hd
    rw [Subgroup.mem_normalizer_iff]
    intro z
    simp only [hW, Subgroup.mem_inf]
    rw [Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hd) z,
      Subgroup.mem_normalizer_iff.mp (hIY hd) z]
  have hclos : Subgroup.closure {y | ∃ g ∈ u38Two α, y = g * xb * g⁻¹} ≤ imageModTheta L W := by
    rw [Subgroup.closure_le]
    rintro y ⟨g, hg, rfl⟩
    rw [← hIeq] at hg
    obtain ⟨l, hl, rfl⟩ := hg
    have hlI : (l : G) ∈ I := Subgroup.mem_subgroupOf.mp hl
    have hconj : (l : G) * x * (l : G)⁻¹ ∈ W :=
      Subgroup.mem_inf.mpr ⟨by
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hlI hxI) (Subgroup.inv_mem _ hlI),
        (Subgroup.mem_normalizer_iff.mp (hIY hlI) x).mp hxY⟩
    refine ⟨l * ⟨x, hxL⟩ * l⁻¹, Subgroup.mem_subgroupOf.mpr hconj, ?_⟩
    show q (l * ⟨x, hxL⟩ * l⁻¹) = _
    rw [map_mul, map_mul, map_inv]
  intro g hg ⟨j, hj⟩
  have hgL : g ∈ L := hIL hg
  have hgbar : q ⟨g, hgL⟩ ∈ u38Two α := by
    rw [← hIeq]
    exact ⟨⟨g, hgL⟩, Subgroup.mem_subgroupOf.mpr hg, rfl⟩
  have hgbar3 : (q ⟨g, hgL⟩) ^ 3 ^ j = 1 := by
    rw [← map_pow]
    have : (⟨g, hgL⟩ : L) ^ 3 ^ j = 1 := Subtype.ext (by simpa using hj)
    rw [this, map_one]
  obtain ⟨w, hwW, hwq⟩ := hclos (hP3 _ hgbar ⟨j, hgbar3⟩)
  have hwG : (w : G) ∈ W := Subgroup.mem_subgroupOf.mp hwW
  have hdθ : w⁻¹ * (⟨g, hgL⟩ : L) ∈ θ := QuotientGroup.eq.mp hwq
  have hdθG : (w : G)⁻¹ * g ∈ θ.map L.subtype := ⟨w⁻¹ * ⟨g, hgL⟩, hdθ, rfl⟩
  have hdI : (w : G)⁻¹ * g ∈ I :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_inf.mp hwG).1) hg
  have hgW : g ∈ W := by
    refine HeringU38.mem_of_mul_coprime (θ := (w : G)⁻¹ * g) (n := (w : G)) (hWN _ hdI) hwG ?_
      (by group)
    have h2 : orderOf g ∣ 3 ^ j := orderOf_dvd_of_pow_eq_one hj
    exact Nat.Coprime.coprime_dvd_right h2
      (Nat.Coprime.pow_right _ (coprime_three_of_mem_theta hdθG))
  exact (Subgroup.mem_inf.mp hgW).2

end CFSG.RankThree.PartTwo.Sec8
