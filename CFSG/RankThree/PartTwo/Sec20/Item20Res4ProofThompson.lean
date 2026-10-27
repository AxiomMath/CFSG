module

public import CFSG.RankThree.PartTwo.Sec3.TwoOfThreeNormal

public section

namespace CFSG.RankThree.PartTwo.Sec20.Res4

open Subgroup CFSG.RankThree.PartTwo.Sec3

theorem pRank_congr {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (p : ℕ) [Fact p.Prime] :
    CFSG.pRank p X = CFSG.pRank p Y := by
  unfold CFSG.pRank
  congr 1
  ext r
  constructor
  · rintro ⟨B, hB, hcard⟩
    have := hB
    exact ⟨B.map e.toMonoidHom, CFSG.IsElementaryAbelian.map (p := p) (A := B) e.toMonoidHom,
      by rw [Subgroup.card_map_of_injective e.injective, hcard]⟩
  · rintro ⟨B, hB, hcard⟩
    have := hB
    exact ⟨B.map e.symm.toMonoidHom,
      CFSG.IsElementaryAbelian.map (p := p) (A := B) e.symm.toMonoidHom,
      by rw [Subgroup.card_map_of_injective e.symm.injective, hcard]⟩

variable {G : Type*} [Group G]

theorem exists_mem_famG_zero [Finite G] (T : Subgroup G) : ∃ A, A ∈ famG T 0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set s := {r : ℕ | ∃ B : Subgroup T, CFSG.IsElementaryAbelian 2 B ∧ Nat.card B = 2 ^ r}
    with hs
  have hbdd : BddAbove s := by
    refine ⟨Nat.card T, fun r ⟨B, _, hB⟩ => ?_⟩
    have h1 : 2 ^ r ≤ Nat.card T := hB ▸ Subgroup.card_le_card_group B
    exact (Nat.lt_two_pow_self).le.trans h1
  have hne : s.Nonempty := by
    refine ⟨0, (⊥ : Subgroup G).subgroupOf T,
      isElementaryAbelian_of_isElemTwo (T := T) (A := ⊥) ⟨fun a ha b hb => ?_, fun a ha => ?_⟩,
      ?_⟩
    · rw [Subgroup.mem_bot] at ha hb
      rw [ha, hb]
    · rw [Subgroup.mem_bot] at ha
      rw [ha, one_mul]
    · rw [pow_zero, Subgroup.bot_subgroupOf, Subgroup.card_bot]
  obtain ⟨B, hB, hcard⟩ := Nat.sSup_mem hne hbdd
  refine ⟨B.map T.subtype, Subgroup.map_subtype_le B, isElemTwo_map_of_isElementaryAbelian hB, ?_⟩
  rw [Subgroup.card_map_of_injective T.subtype_injective, hcard, Nat.sub_zero]
  rfl

theorem jG_zero_eq_of_le [Finite G] {S T : Subgroup G} (hST : S ≤ T) (hJ : jG T 0 ≤ S) :
    jG S 0 = jG T 0 := by
  obtain ⟨A₀, hA₀⟩ := exists_mem_famG_zero T
  obtain ⟨A₁, hA₁⟩ := exists_mem_famG_zero S
  have h1 : CFSG.pRank 2 T ≤ CFSG.pRank 2 S := by
    have := card_le_two_pow_pRank ((le_jG hA₀).trans hJ) hA₀.2.1
    rw [hA₀.2.2, Nat.sub_zero] at this
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp this
  have h2 : CFSG.pRank 2 S ≤ CFSG.pRank 2 T := by
    have := card_le_two_pow_pRank (hA₁.1.trans hST) hA₁.2.1
    rw [hA₁.2.2, Nat.sub_zero] at this
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp this
  have hr : CFSG.pRank 2 S = CFSG.pRank 2 T := le_antisymm h2 h1
  have hfam : famG S 0 = famG T 0 := by
    ext A
    constructor
    · rintro ⟨hAS, hA2, hAc⟩
      exact ⟨hAS.trans hST, hA2, by rw [hAc, hr]⟩
    · intro hA
      exact ⟨(le_jG hA).trans hJ, hA.2.1, by rw [hA.2.2, hr]⟩
  rw [jG, jG, hfam]

theorem inf_centralizer_ne_bot [Finite G] {S W : Subgroup G} (hS : IsPGroup 2 S) (hWS : W ≤ S)
    (hn : S ≤ normalizer (W : Set G)) (hW : W ≠ ⊥) : W ⊓ centralizer (S : Set G) ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent S := hS.isNilpotent
  have hN : (W.subgroupOf S).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hn
  have hne : W.subgroupOf S ≠ ⊥ := by
    intro h
    apply hW
    rw [← Subgroup.map_subgroupOf_eq_of_le hWS, h, Subgroup.map_bot]
  obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  have hyC : (y : G) ∈ centralizer (S : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hy.2 ⟨t, ht⟩)
  intro h
  have hmem : (y : G) ∈ W ⊓ centralizer (S : Set G) := ⟨hy.1, hyC⟩
  rw [h, Subgroup.mem_bot] at hmem
  exact hy1 (Subtype.ext (Subtype.ext hmem))

section Abstract

variable [Finite G]

theorem le_pCore_of_mem_famG_of_htr (T : Sylow 2 G) (B : Sylow 3 G)
    (hB9 : Nat.card (B : Subgroup G) = 9)
    (hTB : ∀ g : G, ∃ t ∈ (T : Subgroup G), ∃ b ∈ (B : Subgroup G), g = t * b)
    (hBc : ∀ a ∈ (B : Subgroup G), ∀ b ∈ (B : Subgroup G), a * b = b * a)
    (hB3 : ∀ b ∈ (B : Subgroup G), b ^ 3 = 1)
    (htr : ∀ d ∈ (B : Subgroup G), ∀ d' ∈ (B : Subgroup G), d ≠ 1 → d' ≠ 1 →
      ∃ n ∈ normalizer ((B : Subgroup G) : Set G), n * d * n⁻¹ = d')
    (hV : ∃ b ∈ (B : Subgroup G), ∃ v ∈ omegaG (CFSG.pCore 2 G), b * v * b⁻¹ ≠ v)
    {A : Subgroup G} (hA : A ∈ famG (T : Subgroup G) 0) :
    A ≤ CFSG.pCore 2 G := by
  set Q := CFSG.pCore 2 G with hQdef
  have hQ2 : IsPGroup 2 Q := pCore_two_isPGroup
  set V := omegaG Q with hVdef
  have hVn : V.Normal := omegaG_normal CFSG.pCore_normal
  have hVQ : V ≤ Q := omegaG_le Q
  have hVel : IsElemTwo V := isElemTwo_omegaG Q
  have hQV : Q ≤ centralizer (V : Set G) := by
    intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact hv.2.1 q hq
  have hAT : A ≤ (T : Subgroup G) := hA.1
  have hk4 := relIndex_le_four T B hB9 hTB hBc hB3 hAT hA.2.1.2 hA.2.1.1
  have hkdvd : Q.relIndex A ∣ 2 ^ (CFSG.pRank 2 (T : Subgroup G) - 0) :=
    hA.2.2 ▸ Subgroup.relIndex_dvd_card Q A
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hkdvd
  have hstd := relIndex_centralizer_le_of_famG (hVQ.trans (pCore_two_le_sylow T)) hVel hA
  have hcv : (centralizer (V : Set G)).relIndex A ≤ Q.relIndex A :=
    Subgroup.relIndex_le_of_le_left hQV (relIndex_ne_zero_of_finite _ _)
  have hjle : j ≤ 2 := by
    rw [hj] at hk4
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp (hk4.trans (by norm_num))
  have hcentA : ∀ t ∈ A, (centralizer ({t} : Set G)).relIndex V ≤
      (centralizer (A : Set G)).relIndex V := fun t ht =>
    Subgroup.relIndex_le_of_le_left (Subgroup.centralizer_le (by simpa using ht))
      (relIndex_ne_zero_of_finite _ _)
  interval_cases j
  · rw [pow_zero] at hj
    exact Subgroup.relIndex_eq_one.mp hj
  · exfalso
    obtain ⟨t, htA, htQ⟩ : ∃ t ∈ A, t ∉ Q := by
      by_contra h
      push Not at h
      rw [Subgroup.relIndex_eq_one.mpr h] at hj
      norm_num at hj
    obtain ⟨d, hdB, hd1, htd⟩ := exists_inv_mod_of_mul_self_mem T B hB9 hTB hBc hB3 (hAT htA)
      htQ (by rw [hA.2.1.2 t htA]; exact Q.one_mem)
    have h8 := eight_le_relIndex_centralizer hQ2 hBc hB3 hB9 htr hdB hd1 htd V hVn hVQ
      hVel.1 hVel.2 hV
    have := (h8.trans (hcentA t htA)).trans hstd
    rw [hj] at hcv
    have : 8 ≤ 2 ^ 0 * 2 := this.trans (Nat.mul_le_mul_left _ hcv)
    omega
  · exfalso
    obtain ⟨⟨z, hzA, hz⟩, -⟩ := exists_of_relIndex_eq_four T B hB9 hTB hBc hB3 hAT
      hA.2.1.2 hA.2.1.1 hj
    have h16 := sixteen_le_relIndex_centralizer hQ2 hBc hB3 hB9 htr hz V hVn hVQ hVel.1 hVel.2
      hV
    have := (h16.trans (hcentA z hzA)).trans hstd
    rw [hj] at hcv
    have : 16 ≤ 2 ^ 0 * 4 := this.trans (Nat.mul_le_mul_left _ hcv)
    omega

end Abstract

section Transfer

variable [Finite G]

omit [Finite G] in
theorem card_sup_eq_mul {T B : Subgroup G} (hTB : ∀ g ∈ T ⊔ B, ∃ t ∈ T, ∃ b ∈ B, g = t * b)
    (hbot : T ⊓ B = ⊥) : Nat.card ↥(T ⊔ B) = Nat.card T * Nat.card B := by
  let μ : ↥T × ↥B → ↥(T ⊔ B) := fun p =>
    ⟨(p.1 : G) * p.2, Subgroup.mul_mem _ (Subgroup.mem_sup_left p.1.2)
      (Subgroup.mem_sup_right p.2.2)⟩
  have hμ : Function.Bijective μ := by
    refine ⟨?_, fun g => ?_⟩
    · rintro ⟨t, b⟩ ⟨t', b'⟩ h
      have h' : (t : G) * b = t' * b' := congrArg Subtype.val h
      have hmem : (t' : G)⁻¹ * t = b' * (b : G)⁻¹ := by
        calc (t' : G)⁻¹ * t = (t' : G)⁻¹ * (t * b) * (b : G)⁻¹ := by group
          _ = (t' : G)⁻¹ * (t' * b') * (b : G)⁻¹ := by rw [h']
          _ = b' * (b : G)⁻¹ := by group
      have hb : (t' : G)⁻¹ * t ∈ T ⊓ B :=
        ⟨T.mul_mem (T.inv_mem t'.2) t.2, hmem ▸ B.mul_mem b'.2 (B.inv_mem b.2)⟩
      rw [hbot, Subgroup.mem_bot] at hb
      have htt : t = t' := Subtype.ext (by
        have := mul_eq_one_iff_eq_inv.mp hb
        exact (inv_injective this).symm)
      have hbb : b = b' := Subtype.ext (by
        rw [hb] at hmem
        exact (mul_inv_eq_one.mp hmem.symm).symm)
      rw [htt, hbb]
    · obtain ⟨t, ht, b, hb, hg⟩ := hTB g g.2
      exact ⟨(⟨t, ht⟩, ⟨b, hb⟩), Subtype.ext hg.symm⟩
  rw [← Nat.card_prod]
  exact (Nat.card_congr (Equiv.ofBijective μ hμ)).symm

theorem le_pCoreOf_of_mem_famG {T B : Subgroup G} (hT2 : IsPGroup 2 T)
    (hB9 : Nat.card B = 9) (hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hB3 : ∀ b ∈ B, b ^ 3 = 1)
    (hTB : ∀ g ∈ T ⊔ B, ∃ t ∈ T, ∃ b ∈ B, g = t * b)
    (htr : ∀ d ∈ B, ∀ d' ∈ B, d ≠ 1 → d' ≠ 1 →
      ∃ t ∈ T, t ∈ normalizer (B : Set G) ∧ t * d * t⁻¹ = d')
    (hV : ∃ b ∈ B, ∃ v ∈ omegaG (CFSG.Open.pCoreOf 2 (T ⊔ B)), b * v * b⁻¹ ≠ v)
    {A : Subgroup G} (hA : A ∈ famG T 0) : A ≤ CFSG.Open.pCoreOf 2 (T ⊔ B) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set H := T ⊔ B with hHdef
  have hTH : T ≤ H := le_sup_left
  have hBH : B ≤ H := le_sup_right
  obtain ⟨k, hk⟩ := hT2.exists_card_eq
  have hbot : T ⊓ B = ⊥ := by
    apply disjoint_iff.mp
    apply Subgroup.disjoint_of_coprime_natCard
    rw [hB9, hk]
    exact Nat.Coprime.pow_left k (by norm_num)
  have hcard : Nat.card H = 2 ^ k * 3 ^ 2 := by
    rw [card_sup_eq_mul hTB hbot, hk, hB9]
    norm_num
  have hf2 : (Nat.card H).factorization 2 = k := by
    rw [hcard, Nat.factorization_mul (by positivity) (by positivity), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd fun h =>
        absurd (Nat.prime_two.dvd_of_dvd_pow h) (by norm_num), add_zero]
  have hf3 : (Nat.card H).factorization 3 = 2 := by
    rw [hcard, Nat.factorization_mul (by positivity) (by positivity), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd fun h =>
        absurd (Nat.prime_three.dvd_of_dvd_pow h) (by norm_num), zero_add]
  obtain ⟨TS, hTS⟩ := (CFSG.ABGLocalTools.isSylowOf_of_card hTH
    (by rw [hk, hf2])).exists_sylow_eq_subgroupOf
  obtain ⟨BS, hBS⟩ := (CFSG.ABGLocalTools.isSylowOf_of_card hBH
    (by rw [hB9, hf3]; norm_num)).exists_sylow_eq_subgroupOf
  have hB9' : Nat.card (BS : Subgroup H) = 9 := by
    rw [hBS, ← hB9]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBH).toEquiv
  have hTB' : ∀ g : H, ∃ t ∈ (TS : Subgroup H), ∃ b ∈ (BS : Subgroup H), g = t * b := by
    intro g
    obtain ⟨t, ht, b, hb, hg⟩ := hTB g g.2
    refine ⟨⟨t, hTH ht⟩, by rw [hTS]; exact ht, ⟨b, hBH hb⟩, by rw [hBS]; exact hb, ?_⟩
    exact Subtype.ext hg
  have hBc' : ∀ a ∈ (BS : Subgroup H), ∀ b ∈ (BS : Subgroup H), a * b = b * a := by
    intro a ha b hb
    rw [hBS, Subgroup.mem_subgroupOf] at ha hb
    exact Subtype.ext (hBc _ ha _ hb)
  have hB3' : ∀ b ∈ (BS : Subgroup H), b ^ 3 = 1 := by
    intro b hb
    rw [hBS, Subgroup.mem_subgroupOf] at hb
    exact Subtype.ext (by rw [Subgroup.coe_pow]; exact hB3 _ hb)
  have htr' : ∀ d ∈ (BS : Subgroup H), ∀ d' ∈ (BS : Subgroup H), d ≠ 1 → d' ≠ 1 →
      ∃ n ∈ normalizer ((BS : Subgroup H) : Set H), n * d * n⁻¹ = d' := by
    intro d hd d' hd' hd1 hd'1
    rw [hBS, Subgroup.mem_subgroupOf] at hd hd'
    obtain ⟨t, ht, htB, htd⟩ := htr _ hd _ hd' (fun h => hd1 (Subtype.ext h))
      (fun h => hd'1 (Subtype.ext h))
    refine ⟨⟨t, hTH ht⟩, ?_, Subtype.ext htd⟩
    rw [hBS, Subgroup.mem_normalizer_iff]
    intro x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_normalizer_iff.mp htB x
  have hO : CFSG.Open.pCoreOf 2 H = (CFSG.pCore 2 H).map H.subtype := by
    rfl
  have hV' : ∃ b ∈ (BS : Subgroup H), ∃ v ∈ omegaG (CFSG.pCore 2 H), b * v * b⁻¹ ≠ v := by
    obtain ⟨b, hb, v, ⟨hvO, hvc, hv2⟩, hbv⟩ := hV
    rw [hO] at hvO hvc
    obtain ⟨v', hv'O, rfl⟩ := hvO
    refine ⟨⟨b, hBH hb⟩, by rw [hBS]; exact hb, v', ⟨hv'O, fun x hx => ?_, ?_⟩, ?_⟩
    · exact Subtype.ext (hvc _ ⟨x, hx, rfl⟩)
    · exact Subtype.ext hv2
    · intro h
      exact hbv (congrArg Subtype.val h)
  have hA' : A.subgroupOf H ∈ famG (TS : Subgroup H) 0 := by
    obtain ⟨hAT, hA2, hAc⟩ := hA
    refine ⟨?_, ⟨fun a ha b hb => Subtype.ext (hA2.1 _ ha _ hb), fun a ha => Subtype.ext
      (hA2.2 _ ha)⟩, ?_⟩
    · rw [hTS]
      exact Subgroup.subgroupOf_mono H hAT
    · have hAH : A ≤ H := hAT.trans hTH
      have hr : CFSG.pRank 2 ↥(TS : Subgroup H) = CFSG.pRank 2 ↥T := by
        rw [hTS]
        exact pRank_congr (Subgroup.subgroupOfEquivOfLe hTH) 2
      rw [hr, ← hAc]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAH).toEquiv
  have hle := le_pCore_of_mem_famG_of_htr TS BS hB9' hTB' hBc' hB3' htr' hV' hA'
  intro a ha
  rw [hO]
  exact ⟨⟨a, (hA.1.trans hTH) ha⟩, hle ha, rfl⟩

end Transfer

end CFSG.RankThree.PartTwo.Sec20.Res4
