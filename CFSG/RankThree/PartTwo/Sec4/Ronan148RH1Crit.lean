module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1Transfer

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148R

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429 CFSG.RankThree.PartTwo.Sec4.RonanK429H
open CFSG.RankThree.PartTwo.Sec4.Ronan148S
open scoped commutatorElement

section Type5

variable {X : Type} [Group X] [Finite X]

theorem center_le_pCore_two_of_isA5Type [Group.IsPerfect X] (hT : IsA5Type (X ⧸ CFSG.pCore 2 X)) :
    Subgroup.center X ≤ CFSG.pCore 2 X := by
  haveI := hT.isSimpleGroup
  have hZ : Subgroup.center (X ⧸ CFSG.pCore 2 X) = ⊥ :=
    center_eq_bot_of_isSimpleGroup_of_isPerfect
  intro z hz
  have hz' : (QuotientGroup.mk' (CFSG.pCore 2 X) z) ∈ Subgroup.center (X ⧸ CFSG.pCore 2 X) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 X) g
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hz g)]
  rw [hZ, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hz'
  exact hz'

theorem not_mem_pCore_two_of_orderOf {x : X} (hx : orderOf x = 3) : x ∉ CFSG.pCore 2 X := by
  intro hmem
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 X)) ⟨x, hmem⟩
  have hk' : x ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have h3 : 3 ∣ 2 ^ k := hx ▸ orderOf_dvd_of_pow_eq_one hk'
  have h2 : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
  have h1 : 3 ∣ 1 := by
    rw [← Nat.Coprime.gcd_eq_one h2]
    exact Nat.dvd_gcd dvd_rfl h3
  omega

theorem not_isA5Type_of_simple [IsSimpleGroup X] (hna : ∃ a b : X, a * b ≠ b * a)
    (h60 : Nat.card X ≠ 60) : ¬ IsA5Type (X ⧸ CFSG.pCore 2 X) := by
  intro hT
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases (inferInstance : (CFSG.pCore 2 X).Normal).eq_bot_or_eq_top with h | h
  · apply h60
    rw [← hT.card]
    exact (Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq h).trans
      QuotientGroup.quotientBot).toEquiv).symm
  · obtain ⟨a, b, hab⟩ := hna
    have h2 : IsPGroup 2 X := by
      intro g
      obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 X))
        ⟨g, h ▸ Subgroup.mem_top g⟩
      exact ⟨k, congrArg Subtype.val hk⟩
    haveI : Nontrivial X := ⟨⟨a * b, b * a, hab⟩⟩
    haveI := h2.center_nontrivial
    have hc : Subgroup.center X = ⊤ := by
      rcases (inferInstance : (Subgroup.center X).Normal).eq_bot_or_eq_top with hc | hc
      · exfalso
        have hnt : Nontrivial (Subgroup.center X) := inferInstance
        rw [hc] at hnt
        exact not_nontrivial _ hnt
      · exact hc
    have ha : a ∈ Subgroup.center X := hc ▸ Subgroup.mem_top a
    exact hab (Subgroup.mem_center_iff.mp ha b).symm

theorem not_dvd_sixty_mul_two_pow {n : ℕ} (hn : Nat.Coprime n 2) (h : ¬ n ∣ 60) (a : ℕ) :
    ¬ n ∣ 60 * 2 ^ a :=
  fun hd => h ((Nat.Coprime.pow_right a hn).dvd_of_dvd_mul_right hd)

end Type5

section Criteria

variable {S : Type} [Group S] [Finite S]

theorem good427_of_le_simple {C E : Subgroup S} (hEC : E ≤ C) [hEs : IsSimpleGroup E]
    (hna : ∃ a b : E, a * b ≠ b * a) (h60 : Nat.card E ≠ 60)
    (hle : ∀ K : Subgroup S, K ≤ C → Group.IsPerfect K → K ≤ E) : Good427 C := by
  intro K hKC hKq hKs hT
  haveI : Group.IsPerfect K := hKq.1
  have hnt : Nontrivial K := CFSG.LocalCores.isQuasisimple_nontrivial hKq
  have hKE : K ≤ E := hle K hKC inferInstance
  have hsE : (K.subgroupOf E).IsSubnormal := isSubnormal_subgroupOf_of_le hEC hKE hKs
  rcases hsE.eq_bot_or_top_of_isSimpleGroup hEs with hbot | htop
  · rw [Subgroup.subgroupOf_eq_bot] at hbot
    have hK0 : K = ⊥ := by
      rw [eq_bot_iff]
      intro k hk
      exact Subgroup.mem_bot.mpr (Subgroup.disjoint_def.mp hbot hk (hKE hk))
    exact (Subgroup.nontrivial_iff_ne_bot K).mp hnt hK0
  · have hKeq : K = E := le_antisymm hKE (Subgroup.subgroupOf_eq_top.mp htop)
    subst hKeq
    exact not_isA5Type_of_simple hna h60 hT

theorem good427_of_derived_le_simple {C E : Subgroup S} (hEC : E ≤ C) [IsSimpleGroup E]
    (hna : ∃ a b : E, a * b ≠ b * a) (h60 : Nat.card E ≠ 60) (hder : ⁅C, C⁆ ≤ E) :
    Good427 C :=
  good427_of_le_simple hEC hna h60 fun K hKC _ => by
    have h := Subgroup.commutator_mono hKC hKC
    rw [Subgroup.commutator_eq_self (H := K)] at h
    exact h.trans hder

theorem good427_of_simpleNormal' {C L : Subgroup S} (hLC : L ≤ C)
    (hLn : ∀ g ∈ C, ∀ l ∈ L, g * l * g⁻¹ ∈ L) [hLs : IsSimpleGroup L]
    (hLna : ∃ a b : L, a * b ≠ b * a) (h60 : Nat.card L ≠ 60)
    (hcent : ∀ g ∈ C, (∀ l ∈ L, l * g = g * l) → g ^ 3 = 1) : Good427 C := by
  intro K hKC hKq hKs hT
  haveI : Group.IsPerfect K := hKq.1
  haveI : Nontrivial K := CFSG.LocalCores.isQuasisimple_nontrivial hKq
  have hL'n : (L.subgroupOf C).Normal := normal_subgroupOf_of_forall_conj' hLn
  have hK'c : IsComponent (K.subgroupOf C) :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKC).symm hKq, hKs⟩
  rcases CFSG.LocalCores.component_normal_subgroup hK'c hL'n with hle | hcomm
  · have hKL : K ≤ L := fun k hk => hle (show (⟨k, hKC hk⟩ : C) ∈ K.subgroupOf C from hk)
    have hsL : (K.subgroupOf L).IsSubnormal := isSubnormal_subgroupOf_of_le hLC hKL hKs
    rcases hsL.eq_bot_or_top_of_isSimpleGroup hLs with hbot | htop
    · rw [Subgroup.subgroupOf_eq_bot] at hbot
      have hK0 : K = ⊥ := by
        rw [eq_bot_iff]
        intro k hk
        exact Subgroup.mem_bot.mpr (Subgroup.disjoint_def.mp hbot hk (hKL hk))
      exact (Subgroup.nontrivial_iff_ne_bot K).mp inferInstance hK0
    · have hKeq : K = L := le_antisymm hKL (Subgroup.subgroupOf_eq_top.mp htop)
      subst hKeq
      exact not_isA5Type_of_simple hLna h60 hT
  · have hk3 : ∀ k ∈ K, k ^ 3 = 1 := by
      intro k hk
      apply hcent k (hKC hk)
      intro l hl
      have hmem : ⁅(⟨k, hKC hk⟩ : C), (⟨l, hLC hl⟩ : C)⁆ ∈ ⁅K.subgroupOf C, L.subgroupOf C⁆ :=
        Subgroup.commutator_mem_commutator (show (⟨k, hKC hk⟩ : C) ∈ K.subgroupOf C from hk)
          (show (⟨l, hLC hl⟩ : C) ∈ L.subgroupOf C from hl)
      rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
      exact (congrArg Subtype.val hmem).symm
    have hK3 : IsPGroup 3 K := isPGroup_three_of_pow_three hk3
    haveI := hK3.isNilpotent
    exact Group.IsPerfect.not_isSolvable K inferInstance

theorem good427_of_central_of_not_nine_dvd {C : Subgroup S} {y : S} (hyC : y ∈ C)
    (hyc : ∀ c ∈ C, c * y = y * c) (hy : orderOf y = 3) (h9 : ¬ 9 ∣ Nat.card C) :
    Good427 C := by
  intro K hKC hKq _ hT
  haveI : Group.IsPerfect K := hKq.1
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_cases hyK : y ∈ K
  ·
    have hyZ : (⟨y, hyK⟩ : K) ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hyc g (hKC g.2))
    have hyO := center_le_pCore_two_of_isA5Type hT hyZ
    exact not_mem_pCore_two_of_orderOf (by rw [Subgroup.orderOf_mk]; exact hy) hyO
  ·
    have hcomm : ∀ a ∈ K, ∀ b ∈ Subgroup.zpowers y, a * b = b * a := by
      intro a ha b hb
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      exact ((Commute.zpow_right (show Commute a y from hyc a (hKC ha)) k)).eq
    have hinf : K ⊓ Subgroup.zpowers y = ⊥ := by
      have hd : Nat.card (K ⊓ Subgroup.zpowers y : Subgroup S) ∣ 3 := by
        rw [← hy, ← Nat.card_zpowers]
        exact Subgroup.card_dvd_of_le inf_le_right
      rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h3
      · exact Subgroup.card_eq_one.mp h1
      · exfalso
        have hle : Subgroup.zpowers y ≤ K := by
          have heq : K ⊓ Subgroup.zpowers y = Subgroup.zpowers y :=
            Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h3, Nat.card_zpowers, hy])
          exact heq ▸ inf_le_left
        exact hyK (hle (Subgroup.mem_zpowers y))
    have hcard := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute K (Subgroup.zpowers y)
      hcomm).1
    rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, hy] at hcard
    have hle : K ⊔ Subgroup.zpowers y ≤ C := sup_le hKC ((Subgroup.zpowers_le).mpr hyC)
    obtain ⟨a, ha⟩ := exists_card_eq_sixty_mul hT
    apply h9
    refine Dvd.dvd.trans ?_ (Subgroup.card_dvd_of_le hle)
    rw [hcard, ha]
    exact ⟨20 * 2 ^ a, by ring⟩

theorem good427_of_five {C H : Subgroup S} (h25 : ¬ 25 ∣ Nat.card C)
    (hH : H ≤ Subgroup.closure {f : S | f ∈ C ∧ f ^ 5 = 1})
    (hH60 : ∀ a : ℕ, ¬ Nat.card H ∣ 60 * 2 ^ a) : Good427 C := by
  intro K hKC hKq hKs hT
  haveI : Group.IsPerfect K := hKq.1
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨a, ha⟩ := exists_card_eq_sixty_mul hT
  set K' : Subgroup C := K.subgroupOf C with hK'def
  have eK : K' ≃* K := Subgroup.subgroupOfEquivOfLe hKC
  have hK'card : Nat.card K' = 60 * 2 ^ a := (Nat.card_congr eK.toEquiv).trans ha
  have hK'c : IsComponent K' :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv eK.symm hKq, hKs⟩
  have hTK' : IsA5Type (K' ⧸ CFSG.pCore 2 K') := isA5Type_quot_congr eK hT
  haveI : Group.IsPerfect K' := hK'c.1.1
  have h2inf : ∀ c : C, ⁅K', K'.map (MulAut.conj c).toMonoidHom⁆ = ⊥ →
      IsPGroup 2 (K' ⊓ K'.map (MulAut.conj c).toMonoidHom : Subgroup C) := by
    intro c hc x
    have hxK : (x : C) ∈ K' := x.2.1
    have hxZ : (⟨x, hxK⟩ : K') ∈ Subgroup.center K' := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hmem : ⁅(g : C), (x : C)⁆ ∈ ⁅K', K'.map (MulAut.conj c).toMonoidHom⁆ :=
        Subgroup.commutator_mem_commutator g.2 x.2.2
      rw [hc, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
      exact Subtype.ext hmem
    have hxO := center_le_pCore_two_of_isA5Type hTK' hxZ
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 K')) ⟨_, hxO⟩
    refine ⟨k, Subtype.ext ?_⟩
    have := congrArg (fun z : CFSG.pCore 2 K' => ((z : K') : C)) hk
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    simpa using this
  have hnorm : K'.Normal := by
    refine ⟨fun k hk c => ?_⟩
    have hconj : IsComponent (K'.map (MulAut.conj c).toMonoidHom) := by
      have e2 : K' ≃* K'.map (MulAut.conj c).toMonoidHom :=
        K'.equivMapOfInjective _ (MulAut.conj c).injective
      refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e2 hK'c.1, ?_⟩
      have := hK'c.2.map (f := (MulAut.conj c).toMonoidHom) (MulAut.conj c).surjective
      simpa using this
    rcases CFSG.LocalCores.distinct_components_commute hK'c hconj with heq | hcomm
    · have : c * k * c⁻¹ ∈ K'.map (MulAut.conj c).toMonoidHom := ⟨k, hk, rfl⟩
      rwa [← heq] at this
    · exfalso
      have hc2 := h2inf c hcomm
      obtain ⟨m, hm⟩ := hc2.exists_card_eq
      have hcm : ∀ x ∈ K', ∀ y ∈ K'.map (MulAut.conj c).toMonoidHom, x * y = y * x := by
        intro x hx y hy
        have hmem : ⁅x, y⁆ ∈ ⁅K', K'.map (MulAut.conj c).toMonoidHom⁆ :=
          Subgroup.commutator_mem_commutator hx hy
        rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
        exact hmem
      have hcard := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute K'
        (K'.map (MulAut.conj c).toMonoidHom) hcm).1
      rw [hm, Subgroup.card_map_of_injective (MulAut.conj c).injective, hK'card] at hcard
      have h25' : 25 ∣ Nat.card (K' ⊔ K'.map (MulAut.conj c).toMonoidHom : Subgroup C) * 2 ^ m := by
        rw [hcard]
        exact ⟨144 * 2 ^ a * 2 ^ a, by ring⟩
      have h25'' : 25 ∣ Nat.card (K' ⊔ K'.map (MulAut.conj c).toMonoidHom : Subgroup C) :=
        (Nat.Coprime.pow_right m (by norm_num : Nat.Coprime 25 2)).dvd_of_dvd_mul_right h25'
      apply h25
      exact h25''.trans (Subgroup.card_subgroup_dvd_card _)
  have hidx5 : ¬ 5 ∣ Nat.card (C ⧸ K') := by
    intro h5
    apply h25
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup K', hK'card]
    obtain ⟨t, ht⟩ := h5
    rw [ht]
    exact ⟨t * 12 * 2 ^ a, by ring⟩
  have hfK : ∀ f ∈ {f : S | f ∈ C ∧ f ^ 5 = 1}, f ∈ K := by
    rintro f ⟨hfC, hf5⟩
    have hq : (QuotientGroup.mk' K' (⟨f, hfC⟩ : C)) ^ 5 = 1 := by
      rw [← map_pow]
      have : (⟨f, hfC⟩ : C) ^ 5 = 1 := Subtype.ext (by simpa using hf5)
      rw [this, map_one]
    have hdvd : orderOf (QuotientGroup.mk' K' (⟨f, hfC⟩ : C)) ∣ 5 := orderOf_dvd_of_pow_eq_one hq
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hdvd with h1 | h5
    · rw [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact h1
    · exfalso
      apply hidx5
      rw [← h5]
      exact orderOf_dvd_natCard _
  have hHK : H ≤ K := hH.trans ((Subgroup.closure_le K).mpr hfK)
  apply hH60 a
  rw [← ha]
  exact Subgroup.card_dvd_of_le hHK

theorem good427_of_pConstrained {C : Subgroup S}
    (h : CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PConstrainedShape 3 C) : Good427 C := by
  obtain ⟨R, hRC, hn, hp, hc⟩ := h
  exact good427_of_selfCentralizing' hRC hn hp (fun x hx => hc ⟨hx.2, hx.1⟩)

theorem forall_good427_of_mulEquiv {T T' : Type} [Group T] [Group T'] (e : T ≃* T')
    (h : ∀ x : T', orderOf x = 3 → Good427 (Subgroup.centralizer ({x} : Set T'))) :
    ∀ x : T, orderOf x = 3 → Good427 (Subgroup.centralizer ({x} : Set T)) := fun x hx =>
  Good427.of_mulEquiv_centralizer e (h (e x) (by rwa [MulEquiv.orderOf_eq]))

theorem good427_of_isExtOf {C : Subgroup S} {Y B : Type*} [Group Y] [Group B]
    (h : Sec4.IsExtOf C Y B) (hY : IsSimpleGroup Y) (hB : Group.IsSolvable B)
    (hn : ∀ a : ℕ, ¬ Nat.card Y ∣ 60 * 2 ^ a) : Good427 C := by
  obtain ⟨N, hN, ⟨eN⟩, ⟨eQ⟩⟩ := h
  set ρ : C →* Y := eQ.toMonoidHom.comp (QuotientGroup.mk' N) with hρdef
  have hρ : Function.Surjective ρ := eQ.surjective.comp (QuotientGroup.mk'_surjective N)
  have hker : ρ.ker = N := by
    ext x
    simp [hρdef, QuotientGroup.eq_one_iff]
  have hsolvN : Group.IsSolvable N :=
    solvable_of_surjective (f := eN.symm.toMonoidHom) eN.symm.surjective
  have hsolv : Group.IsSolvable ρ.ker :=
    solvable_of_surjective (f := (MulEquiv.subgroupCongr hker).symm.toMonoidHom)
      (MulEquiv.subgroupCongr hker).symm.surjective
  intro K hKC hKq hKs hT
  have hcomp : CFSG.IsComponent (K.subgroupOf C) :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKC).symm hKq, hKs⟩
  have htop := CFSG.Sporadic.SmallOddCore.map_eq_top_of_isComponent ρ hρ hsolv hY hcomp
  obtain ⟨a, ha⟩ := exists_card_eq_sixty_mul hT
  apply hn a
  have h1 : Nat.card Y = Nat.card ((K.subgroupOf C).map ρ) := by rw [htop, Subgroup.card_top]
  rw [h1, ← ha, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKC).toEquiv]
  exact Subgroup.card_map_dvd (K.subgroupOf C) ρ

theorem not_dvd_sixty_of_nine_dvd {m : ℕ} (h9 : 9 ∣ m) (a : ℕ) : ¬ m ∣ 60 * 2 ^ a :=
  fun hd => not_dvd_sixty_mul_two_pow (n := 9) (by norm_num) (by norm_num) a (h9.trans hd)

theorem good427_of_not_five_dvd {C : Subgroup S} (h5 : ¬ 5 ∣ Nat.card C) : Good427 C :=
  good427_of_card_dvd dvd_rfl fun h => h5 (Dvd.dvd.trans ⟨12, by norm_num⟩ h)

end Criteria

section Rows

theorem NoCfgS427.of_mulEquiv {S T : Type} [Group S] [Group T] (e : S ≃* T) (h : NoCfgS427 T) :
    NoCfgS427 S := by
  intro σ h3 h1
  have h3' : MulAut.congr e σ ^ 3 = 1 := by rw [← map_pow, h3, map_one]
  have h1' : MulAut.congr e σ ≠ 1 := fun h' =>
    h1 ((MulAut.congr e).injective (h'.trans (map_one _).symm))
  have hg := h _ h3' h1'
  rw [autFix_congr] at hg
  exact Good427.of_map e.toMonoidHom e.injective hg

theorem simple_nonab_of_mulEquiv' {S T : Type} [Group S] [Group T] (e : T ≃* S)
    (hs : IsSimpleGroup S) (hna : ∃ a b : S, a * b ≠ b * a) :
    IsSimpleGroup T ∧ ∃ a b : T, a * b ≠ b * a := by
  haveI := hs
  refine ⟨e.isSimpleGroup, ?_⟩
  obtain ⟨a, b, hab⟩ := hna
  refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
  have := congrArg e h
  simpa using this

theorem rowOf427_of_noCfgS
    {X : Type} [Group X]
    (h : ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      Nonempty (S ≃* X) → NoCfgS427 S ∧ NoONS427 S) : RowOf427 X := by
  intro S _ _ hs hna ⟨eSX⟩
  refine row427_of_noCfg' fun S' _ _ ⟨e'⟩ => ?_
  obtain ⟨hs', hna'⟩ := simple_nonab_of_mulEquiv' e' hs hna
  exact h S' hs' hna' ⟨e'.trans eSX⟩

theorem rowOf427_spor
    {s : TauCeti.SporadicName}
    (hb : Nonempty (Blueprint.NativeSporadic.Carrier s ≃* Spor s))
    (h : ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      Nonempty (S ≃* Blueprint.NativeSporadic.Carrier s) → NoCfgS427 S ∧ NoONS427 S) :
    RowOf427 (Spor s) :=
  rowOf427_of_noCfgS fun S _ _ hs hna ⟨e⟩ => by
    obtain ⟨b⟩ := hb
    exact h S hs hna ⟨e.trans b.symm⟩

end Rows

end CFSG.RankThree.PartTwo.Sec4.Ronan148R

end
