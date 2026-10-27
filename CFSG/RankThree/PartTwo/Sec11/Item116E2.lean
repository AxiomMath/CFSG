module

public import CFSG.RankThree.PartTwo.Sec11.Item116E2Pure
public import CFSG.RankThree.PartTwo.Sec11.Item116Holes
public import CFSG.RankThree.PartTwo.Sec11.Item116H3Rank
import CFSG.RankThree.PartTwo.Sec6.Item68

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

section Data

theorem pCore_quotient_pCore (Y : Type*) [Group Y] (p : ℕ) :
    CFSG.pCore p (Y ⧸ CFSG.pCore p Y) = ⊥ := by
  set N := CFSG.pCore p Y with hN
  haveI : N.Normal := BaerSuzuki.Helpers.pCore_normal p
  set M := CFSG.pCore p (Y ⧸ N) with hM
  have hMn : M.Normal := BaerSuzuki.Helpers.pCore_normal p
  have hMp : IsPGroup p M := BaerSuzuki.Helpers.pCore_isPGroup p
  have hNp : IsPGroup p N := BaerSuzuki.Helpers.pCore_isPGroup p
  have hM' : IsPGroup p (M.comap (QuotientGroup.mk' N)) := by
    intro y
    obtain ⟨k, hk⟩ := hMp ⟨QuotientGroup.mk' N y, y.2⟩
    have h1 : (QuotientGroup.mk' N (y : Y)) ^ p ^ k = 1 := congrArg Subtype.val hk
    have h2 : (y : Y) ^ p ^ k ∈ N := by
      have h3 : QuotientGroup.mk' N ((y : Y) ^ p ^ k) = 1 := by
        rw [map_pow]
        exact h1
      exact (QuotientGroup.eq_one_iff _).mp h3
    obtain ⟨j, hj⟩ := hNp ⟨_, h2⟩
    refine ⟨k + j, Subtype.ext ?_⟩
    have := congrArg Subtype.val hj
    simpa [pow_add, pow_mul] using this
  have hle : M.comap (QuotientGroup.mk' N) ≤ N :=
    BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup (hMn.comap _) hM'
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N x
  have hy : y ∈ M.comap (QuotientGroup.mk' N) := hx
  have := hle hy
  simpa [QuotientGroup.eq_one_iff] using this

theorem pCore_eq_bot_of_not_dvd (X : Type*) [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    (h : ¬ p ∣ Nat.card X) : CFSG.pCore p X = ⊥ := by
  obtain ⟨k, hk⟩ := (BaerSuzuki.Helpers.pCore_isPGroup (G := X) p).exists_card_eq
  have hdvd : Nat.card (CFSG.pCore p X) ∣ Nat.card X := Subgroup.card_subgroup_dvd_card _
  rcases k with _ | k
  · rw [pow_zero] at hk
    exact Subgroup.eq_bot_of_card_eq _ hk
  · exact absurd (dvd_trans (hk ▸ dvd_pow_self p (Nat.succ_ne_zero k)) hdvd) h

end Data

section Main

variable {G : Type} [Group G] [Finite G]

theorem commutator_twoFitting_le_pCore_of_double
    (hB : KFacts.BlackburnRankTwo) (hLin : KFacts.NoDoubleComponentGL) {a : G}
    (hloc : ∀ p : ℕ, p.Prime → 3 < p → CFSG.Assembly.RankThreeEven.localRank p G < 3)
    (hO2 : inSubgroup (CFSG.pCore 2) (thetaCent a) ≠ ⊥)
    {K : Subgroup G} (hKC : K ≤ Subgroup.centralizer ({a} : Set G)) (hKperf : ⁅K, K⁆ = K)
    {n : G}
    (hn : n ∈ Subgroup.normalizer ((Subgroup.centralizer ({a} : Set G) : Subgroup G) : Set G))
    (hKKn : ⁅K, K.map (MulAut.conj n).toMonoidHom⁆ ≤ thetaCent a) :
    ⁅K, inSubgroup twoFitting (thetaCent a)⁆ ≤ inSubgroup (CFSG.pCore 2) (thetaCent a) := by
  classical
  set θ := thetaCent a with hθ
  haveI hNc : (CFSG.pCore 2 ↥θ).Characteristic := BaerSuzuki.Helpers.pCore_characteristic 2
  haveI hNn : (CFSG.pCore 2 ↥θ).Normal := BaerSuzuki.Helpers.pCore_normal 2
  set N := CFSG.pCore 2 ↥θ with hN
  have hCθ : Subgroup.normalizer ((Subgroup.centralizer ({a} : Set G) : Subgroup G) : Set G) ≤
      Subgroup.normalizer (θ : Set G) := Sec6.normalizer_le_normalizer_theta _
  have hKΓ : K ≤ Subgroup.normalizer (θ : Set G) := hKC.trans (Subgroup.le_normalizer.trans hCθ)
  have hθΓ : θ ≤ Subgroup.normalizer (θ : Set G) := Subgroup.le_normalizer
  have hnΓ : n ∈ Subgroup.normalizer (θ : Set G) := hCθ hn
  set Γ := Subgroup.normalizer (θ : Set G) with hΓ
  let φ : Γ →* MulAut (↥θ ⧸ N) :=
    (SectionRank.Ccomm.autQuotient N).comp θ.normalizerMonoidHom
  have hθs : Group.IsSolvable ↥θ := isSolvable_inSubgroup_theta _
  have hXs : Group.IsSolvable (↥θ ⧸ N) :=
    Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective N)
  have hθ3 : ¬ 3 ∣ Nat.card θ := not_three_dvd_card_inSubgroup_theta _
  have hlow : ∀ p : ℕ, p.Prime → p < 5 → CFSG.pCore p (↥θ ⧸ N) = ⊥ := by
    intro p hp hp5
    haveI : Fact p.Prime := ⟨hp⟩
    have h23 : p = 2 ∨ p = 3 := by
      have h2 := hp.two_le
      have h234 : p = 2 ∨ p = 3 ∨ p = 4 := by omega
      rcases h234 with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · subst h
        exact absurd hp (by norm_num)
    rcases h23 with rfl | rfl
    · exact pCore_quotient_pCore ↥θ 2
    · refine pCore_eq_bot_of_not_dvd _ ?_
      intro h3
      exact hθ3 (h3.trans (Subgroup.card_quotient_dvd_card N))
  have hNev : Even (Nat.card N) := by
    have hN0 : N ≠ ⊥ := fun h => hO2 (by
      rw [show inSubgroup (CFSG.pCore 2) θ = N.map θ.subtype from rfl, h, Subgroup.map_bot])
    obtain ⟨k, hk⟩ := (BaerSuzuki.Helpers.pCore_isPGroup (G := ↥θ) 2).exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hN0 (Subgroup.eq_bot_of_card_eq _ (by simpa using hk))
    exact hk ▸ (Nat.even_pow' hk0).mpr even_two
  have h3gen : ∀ (r : ℕ) [Fact r.Prime], 5 ≤ r → ∀ P : Subgroup (↥θ ⧸ N), IsPGroup r P →
      ∃ s : Finset P, s.card ≤ 3 ∧ Subgroup.closure (s : Set P) = ⊤ := by
    intro r _ hr5 P hP
    exact Item116PRank.exists_three_generators_of_even_normal hB hr5
      (hloc r Fact.out (by omega)) θ N hNev P hP
  let KΓ : Subgroup Γ := K.subgroupOf Γ
  let TΓ : Subgroup Γ := θ.subgroupOf Γ
  haveI hTΓn : TΓ.Normal := Subgroup.normal_in_normalizer
  let nΓ : Γ := ⟨n, hnΓ⟩
  have hKΓperf : ⁅KΓ, KΓ⁆ = KΓ := by
    apply Subgroup.map_injective Γ.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hKΓ, hKperf]
  have hTinn : ∀ t ∈ TΓ, ∃ x : ↥θ ⧸ N, ∀ y, φ t y = x * y * x⁻¹ := by
    intro t ht
    have htθ : (t : G) ∈ θ := ht
    refine ⟨((⟨(t : G), htθ⟩ : ↥θ) : ↥θ ⧸ N), fun y => ?_⟩
    obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective y
    have h1 : θ.normalizerMonoidHom t y' = ⟨(t : G), htθ⟩ * y' * ⟨(t : G), htθ⟩⁻¹ := by
      apply Subtype.ext
      simp [Subgroup.normalizerMonoidHom_apply_apply_coe]
    show SectionRank.Ccomm.autQuotient N (θ.normalizerMonoidHom t) (y' : ↥θ ⧸ N) = _
    rw [SectionRank.Ccomm.autQuotient_mk, h1]
    rfl
  have hKT : ⁅KΓ, KΓ.map (MulAut.conj nΓ).toMonoidHom⁆ ≤ TΓ := by
    rw [← Subgroup.map_le_map_iff_of_injective Γ.subtype_injective, Subgroup.map_commutator,
      Subgroup.map_subgroupOf_eq_of_le hKΓ, Subgroup.map_subgroupOf_eq_of_le hθΓ]
    have hmap : (KΓ.map (MulAut.conj nΓ).toMonoidHom).map Γ.subtype =
        K.map (MulAut.conj n).toMonoidHom := by
      rw [Subgroup.map_map, ← Subgroup.map_subgroupOf_eq_of_le hKΓ, Subgroup.map_map]
      congr 1
    rw [hmap]
    exact hKKn
  have hX3 : ¬ 3 ∣ Nat.card (↥θ ⧸ N) := fun h3 => hθ3 (h3.trans (Subgroup.card_quotient_dvd_card N))
  have key := fitting_fixed_of_ndc hLin hXs hX3 hlow h3gen φ KΓ TΓ nΓ hKΓperf hTinn hKT
  rw [Subgroup.commutator_le]
  intro k hk v hv
  obtain ⟨v', hv', rfl⟩ := hv
  have hkΓ : k ∈ Γ := hKΓ hk
  have hkK : (⟨k, hkΓ⟩ : Γ) ∈ KΓ := hk
  have hfix := key ⟨k, hkΓ⟩ hkK (QuotientGroup.mk' N v') hv'
  have h1 : SectionRank.Ccomm.autQuotient N (θ.normalizerMonoidHom ⟨k, hkΓ⟩) (v' : ↥θ ⧸ N) =
      (v' : ↥θ ⧸ N) := hfix
  rw [SectionRank.Ccomm.autQuotient_mk, QuotientGroup.eq_iff_div_mem] at h1
  refine ⟨_, h1, ?_⟩
  simp [Subgroup.normalizerMonoidHom_apply_apply_coe, commutatorElement_def, div_eq_mul_inv]

end Main

section Residue

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G} {d : G}

theorem kfAt_of_pCore_ne_bot (hB : KFacts.BlackburnRankTwo) (hLin : KFacts.NoDoubleComponentGL)
    (hP2b : Item116P2b) (h : ResidueConfig G A c L a R Y d) (hT : A ∉ partTwoT G)
    (hR1 : ResidueR1 G A c a d)
    (hO2 : inSubgroup (CFSG.pCore 2) (inSubgroup (aschbacherSolvableCore 3)
      (Subgroup.centralizer ({a} : Set G))) ≠ ⊥) : KFAt L a := by
  have hs := h.toSec11Std hT
  obtain ⟨-, hD8, n, hnW, hnc, hnd, hna⟩ := hR1
  have hAe := h.mem_partTwoF.1
  have hexp : ∀ u ∈ A, u ^ 3 = 1 := hAe.2
  have haA := h.a_mem
  have hna' : n * a * n⁻¹ ∈ Subgroup.zpowers a := by
    rw [hna]
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers a)
  have hna1 : n * a * n⁻¹ ≠ 1 := fun h1 => h.a_ne_one (by
    calc a = n⁻¹ * (n * a * n⁻¹) * n := by group
      _ = 1 := by rw [h1]; group)
  have hnC : n ∈ Subgroup.normalizer
      ((Subgroup.centralizer ({a} : Set G) : Subgroup G) : Set G) := by
    refine GroupTheory.SteinbergBY.mem_normalizer_of_map_conj_eq ?_
    rw [map_centralizer_singleton, MulAut.conj_apply]
    exact TheoremO.centralizer_eq_of_zpowers_eq
      (TheoremO.zpowers_eq_of_mem_of_ne_one (hexp a haA) hna' hna1)
  have hYn : Y.map (MulAut.conj n).toMonoidHom ≠ Y :=
    hP2b G A c L a R Y hs d h.inf_eq_zpowers h.normalizer_le h.isIrreducibleOn h.isSylowOf_top
      h.not_mem_zpowers hD8 n hnW hnc hnd hna
  have hYnL : Y.map (MulAut.conj n).toMonoidHom ∈ thetaComponentsAt 3 a := by
    have h1 := map_mem_thetaComponentsAt (MulAut.conj n) h.mem_thetaComponentsAt_Y
    rwa [MulAut.conj_apply, TheoremO.thetaComponentsAt_eq_of_zpowers_eq
      (TheoremO.zpowers_eq_of_mem_of_ne_one (hexp a haA) hna' hna1)] at h1
  have hKKn : ⁅sec11K L a, (sec11K L a).map (MulAut.conj n).toMonoidHom⁆ ≤ thetaCent a :=
    (Subgroup.commutator_mono h.sec11K_le (Subgroup.map_mono h.sec11K_le)).trans
      (Sec6.commutator_le_theta_of_ne_mem_thetaComponentsAt h.mem_thetaComponentsAt_Y hYnL
        hYn.symm)
  have hKC : sec11K L a ≤ Subgroup.centralizer ({a} : Set G) :=
    (Subgroup.map_subtype_le _).trans inf_le_right
  have hKperf : ⁅sec11K L a, sec11K L a⁆ = sec11K L a :=
    Subgroup.isPerfect_iff.mp (Sec6.isPerfect_inSubgroup_perfectResidual _)
  exact commutator_twoFitting_le_pCore_of_double hB hLin
    (fun p hp h3 => h.localRank_lt p hp h3) hO2 hKC hKperf hnC hKKn

end Residue

end CFSG.RankThree.PartTwo.Sec11

end
