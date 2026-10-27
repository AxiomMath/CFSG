module

public import CFSG.Quasithin.EmptyFaithful.R3c10Elim

public section

namespace CFSG.Quasithin.R3c10

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.Blueprint
open scoped commutatorElement

section Rank

variable {G : Type} [Group G] [Finite G]

theorem exists_nine_of_pRank_two {H : Subgroup G} (hr : CFSG.Open.pRank 3 H = 2) :
    ∃ E : Subgroup G, E ≤ H ∧ IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  classical
  set s : Set ℕ := {k | ∃ E : Subgroup G, E ≤ H ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ k} with hs
  have hr' : sSup s = 2 := hr
  have hbdd : BddAbove s := by
    refine ⟨Nat.card G, fun k hk => ?_⟩
    obtain ⟨E, -, -, hE⟩ := hk
    have h1 : Nat.card E ≤ Nat.card G :=
      Nat.card_le_card_of_injective E.subtype E.subtype_injective
    have h2 : k < 3 ^ k := Nat.lt_pow_self (by norm_num)
    omega
  have hne : s.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h] at hr'
    simp at hr'
  have hmem : 2 ∈ s := hr' ▸ Nat.sSup_mem hne hbdd
  obtain ⟨E, hEL, hE, hcard⟩ := hmem
  exact ⟨E, hEL, hE, by simpa using hcard⟩

theorem borel_threeGroup_isCyclic {L Q E : Subgroup G}
    (hZ : centerOf L = pCoreOf 2 L) (hQ : IsSylowTwoOf Q L)
    (hB : fusionIsBenderGroup (↥L ⧸ Subgroup.center ↥L)) (hEL : E ≤ L)
    (hEN : E ≤ Subgroup.normalizer (Q : Set G)) (hE3 : IsPGroup 3 E) : IsCyclic E := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPL : Q ≤ L := hQ.1
  have hZP : ∀ z ∈ Subgroup.center ↥L, (z : G) ∈ Q := center_le_of_isSylowTwoOf hZ hQ
  obtain ⟨Tsyl, hT, hTcomap, hNcomap⟩ := exists_quotSylow hZ hQ
  set Z : Subgroup ↥L := Subgroup.center ↥L with hZdef
  set π : ↥L →* ↥L ⧸ Z := QuotientGroup.mk' Z with hπ
  have hker : π.ker = Z := QuotientGroup.ker_mk' Z
  obtain ⟨D, hD⟩ := CFSG.Goldschmidt.G3a.exists_borelSetup hB Tsyl
  set T : Subgroup (↥L ⧸ Z) := (Tsyl : Subgroup (↥L ⧸ Z)) with hTdef
  set N : Subgroup (↥L ⧸ Z) := Subgroup.normalizer (T : Set (↥L ⧸ Z)) with hN
  have hTN : (T.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer Subgroup.le_normalizer).mpr le_rfl
  have hmemN : ∀ e : ↥E, π (Subgroup.inclusion hEL e) ∈ N := by
    intro e
    have h1 : Subgroup.inclusion hEL e ∈ Subgroup.normalizer ((Q.subgroupOf L : Subgroup ↥L) : Set ↥L) :=
      (SBc2.mem_normalizer_subgroupOf_iff hPL _).mpr (hEN e.2)
    rw [← hNcomap] at h1
    exact h1
  let f₁ : ↥E →* ↥N := (π.comp (Subgroup.inclusion hEL)).codRestrict N hmemN
  let g : ↥E →* ↥N ⧸ T.subgroupOf N := (QuotientGroup.mk' (T.subgroupOf N)).comp f₁
  have hcyc : IsCyclic (↥N ⧸ T.subgroupOf N) := by
    have : IsCyclic ↥D := hD.cyc
    let h₁ : ↥D →* ↥N ⧸ T.subgroupOf N :=
      (QuotientGroup.mk' (T.subgroupOf N)).comp (Subgroup.inclusion hD.le)
    have hsurj : Function.Surjective h₁ := by
      intro y
      obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective _ y
      obtain ⟨t, ht, d, hd, hnd⟩ := hD.exists_mul n.2
      refine ⟨⟨d, hd⟩, ?_⟩
      show QuotientGroup.mk (Subgroup.inclusion hD.le ⟨d, hd⟩) = QuotientGroup.mk n
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      have hdN : d ∈ N := hD.le hd
      have h2 : d⁻¹ * t * d ∈ T := by
        have := (Subgroup.mem_normalizer_iff.mp (N.inv_mem hdN) t).mp ht
        rwa [inv_inv] at this
      have e : (((Subgroup.inclusion hD.le ⟨d, hd⟩)⁻¹ * n : ↥N) : ↥L ⧸ Z) = d⁻¹ * t * d := by
        have : (n : ↥L ⧸ Z) = t * d := hnd
        simp [this, mul_assoc]
      rw [e]
      exact h2
    exact isCyclic_of_surjective h₁ hsurj
  have hginj : Function.Injective g := by
    rw [injective_iff_map_eq_one]
    intro e he
    have h0 : f₁ e ∈ T.subgroupOf N := (QuotientGroup.eq_one_iff _).mp he
    have h1 : π (Subgroup.inclusion hEL e) ∈ T := Subgroup.mem_subgroupOf.mp h0
    obtain ⟨a, ha⟩ := (IsPGroup.iff_orderOf.mp hE3) e
    have hpow : (π (Subgroup.inclusion hEL e)) ^ 3 ^ a = 1 := by
      have : e ^ 3 ^ a = 1 := by rw [← ha]; exact pow_orderOf_eq_one e
      rw [← map_pow, ← map_pow, this, map_one, map_one]
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp Tsyl.isPGroup')
      (⟨π (Subgroup.inclusion hEL e), h1⟩ : ↥T)
    have hk' : orderOf (π (Subgroup.inclusion hEL e)) = 2 ^ k := by
      rw [← hk]
      exact Subgroup.orderOf_coe (⟨π (Subgroup.inclusion hEL e), h1⟩ : ↥T)
    have hdvd : 2 ^ k ∣ 3 ^ a := by
      rw [← hk']
      exact orderOf_dvd_of_pow_eq_one hpow
    have hk1 : 2 ^ k = 1 :=
      (Nat.Coprime.pow k a (by norm_num : Nat.Coprime 2 3)).eq_one_of_dvd hdvd
    have hx1 : π (Subgroup.inclusion hEL e) = 1 := by
      rw [← orderOf_eq_one_iff, hk', hk1]
    have hmemZ : Subgroup.inclusion hEL e ∈ Z := by
      rw [← hker]
      exact hx1
    have hQe : (e : G) ∈ Q := hZP _ hmemZ
    obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp hQ.2.1) (⟨(e : G), hQe⟩ : ↥Q)
    have hj' : orderOf (e : G) = 2 ^ j := by
      rw [← hj]
      exact Subgroup.orderOf_coe (⟨(e : G), hQe⟩ : ↥Q)
    have ha' : orderOf (e : G) = 3 ^ a := by
      rw [← ha]
      exact Subgroup.orderOf_coe e
    have hj1 : 2 ^ j = 1 := by
      have : 2 ^ j ∣ 3 ^ a := by rw [← hj', ha']
      exact (Nat.Coprime.pow j a (by norm_num : Nat.Coprime 2 3)).eq_one_of_dvd this
    have : orderOf (e : G) = 1 := by rw [hj', hj1]
    rw [orderOf_eq_one_iff] at this
    exact Subtype.ext this
  exact isCyclic_of_injective g hginj

end Rank

section Context

variable {G : Type} [Group G] [Finite G]

theorem bender_cl {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}
    (c : CtxComp2 T Mc M V₁ V₂ Yp I L t) (hN : I ≤ Subgroup.normalizer (L : Set G))
    (hYL : Yp ≤ L) (hB : fusionIsBenderGroup (↥L ⧸ Subgroup.center ↥L)) : False := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.hyp
  have hLc : L ∈ cComp I := c.c33.mem
  have hLI : L ≤ I := le_of_mem_cComp hLc
  have hSM : Sgp153 T V₁ ≤ M := inf_le_left.trans hh.hyp.T_le
  have hSI : Sgp153 T V₁ ≤ I := le_sup_right.trans c.inH.1.1
  have hYpM : Yp ≤ M := hh.Yp_le_Y153.trans (Y153_le Mc M)
  have hSL : Sgp153 T V₁ ≤ Subgroup.normalizer (L : Set G) := fun s hs => hN (hSI hs)
  have hZ : centerOf L = CFSG.Open.pCoreOf 2 L := c.c33.center_eq
  have hSyl : IsSylowTwoOf (Sgp153 T V₁) I := c.facts.sylow
  have hQsyl : IsSylowTwoOf (Sgp153 T V₁ ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal (A4.isSylowTwoOf_mono hSyl (le_inf hSyl.1 hSL) inf_le_left)
      (le_inf hLI Subgroup.le_normalizer) inf_le_right
  set Q : Subgroup G := Sgp153 T V₁ ⊓ L with hQdef
  have hYQ : Yp ≤ Subgroup.normalizer (Q : Set G) := by
    rcases le_normalizer_or_le_of_bender hZ hQsyl hB (le_sup_right : Q ≤ Yp ⊔ Q)
        (sup_le hYL (inf_le_right : Q ≤ L)) with h | h
    · exact le_sup_left.trans h
    · exact (c.c33.not_le (h.trans (sup_le hYpM (inf_le_left.trans hSM)))).elim
  obtain ⟨E, hEY, hE, hE9⟩ := exists_nine_of_pRank_two c.rank
  have hE3 : IsPGroup 3 E := IsPGroup.of_card (n := 2) (by simpa using hE9)
  have hcyc := borel_threeGroup_isCyclic hZ hQsyl hB (hEY.trans hYL) (hEY.trans hYQ) hE3
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥E)
  have hg3 : g ^ 3 = 1 := Subtype.ext (hE.2 (g : G) g.2)
  have h1 : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one hg3
  rw [hg, hE9] at h1
  omega

end Context

section Cases

@[expose] def Lemma115LieHighTwo (X : Type) [Group X] : Prop :=
  (((∃ f : ℕ, (2 ≤ f ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSL 3 2 f) ∨
      (2 ≤ f ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSp 2 2 f) ∨
      (2 ≤ f ∧ ChevalleyExceptionalModel X .G2 2 f) ∨
      (1 ≤ f ∧ ChevalleyExceptionalModel X .trialityD4 2 f) ∨
      (Odd f ∧ 3 ≤ f ∧ ReeTitsModel X .twistedF4 2 f)) ∨
    ReeTitsModel X .Tits 2 1) ∨
    (∃ n : ℕ, (n = 4 ∨ n = 5) ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSL n 2 1)) ∨
  Nonempty (X ≃* alternatingGroup (Fin 6)) ∨ CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSU 3 3 1

theorem lemma115LieHigh_cases {X : Type} [Group X] (h : Lemma115LieHigh X) :
    Lemma115LieHighTwo X ∨ CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSL 3 2 1 := by
  rcases h with (((⟨f, hfam⟩ | hTits) | hL45) | ⟨⟨e⟩⟩ | hU33)
  · rcases hfam with ⟨hf, hm⟩ | ⟨hf, hm⟩ | ⟨hf, hm⟩ | ⟨hf, hm⟩ | ⟨hodd, hf, hm⟩
    · by_cases hf1 : f = 1
      · subst hf1
        exact Or.inr hm
      · exact Or.inl (Or.inl (Or.inl (Or.inl ⟨f, Or.inl ⟨by omega, hm⟩⟩)))
    · exact Or.inl (Or.inl (Or.inl (Or.inl ⟨f, Or.inr (Or.inl ⟨hf, hm⟩)⟩)))
    · exact Or.inl (Or.inl (Or.inl (Or.inl ⟨f, Or.inr (Or.inr (Or.inl ⟨hf, hm⟩))⟩)))
    · exact Or.inl (Or.inl (Or.inl (Or.inl ⟨f, Or.inr (Or.inr (Or.inr (Or.inl ⟨hf, hm⟩)))⟩)))
    · exact Or.inl (Or.inl (Or.inl (Or.inl ⟨f, Or.inr (Or.inr (Or.inr (Or.inr ⟨hodd, hf, hm⟩)))⟩)))
  · exact Or.inl (Or.inl (Or.inl (Or.inr hTits)))
  · exact Or.inl (Or.inl (Or.inr hL45))
  · exact Or.inl (Or.inr (Or.inl ⟨e⟩))
  · exact Or.inl (Or.inr (Or.inr hU33))

end Cases

section Main

@[expose] def Input15335CloseLieHigh : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    CtxComp2 T Mc M V₁ V₂ Yp I L t →
      (∀ K : Subgroup G, IsHPlus Yp (Sgp153 T V₁) M K → K ≤ I → K = I) →
        I ≤ Subgroup.normalizer (L : Set G) → I = L ⊔ Sgp153 T V₁ → Yp ≤ L →
          Lemma115LieHighTwo (↥L ⧸ Subgroup.center ↥L) → False

theorem input15335CloseLie_of_high (kH : Input15335CloseLieHigh) :
    Input15335CloseLie := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c hmin hN hIeq hYL hlie
  rcases lemma115LieCharTwo_cases hlie with hHigh | ⟨f, hf, h⟩ | ⟨f, hf, h⟩ | ⟨f, -, -, hm⟩
  · rcases lemma115LieHigh_cases hHigh with hH2 | hL32
    · exact kH G T Mc M V₁ V₂ Yp I L t c hmin hN hIeq hYL hH2
    ·
      exfalso
      have h9 : 9 ∣ Nat.card ↥Yp := R3c8.nine_dvd_card_of_pRank_two c.rank
      have h9L : 9 ∣ Nat.card ↥L := h9.trans (Subgroup.card_dvd_of_le hYL)
      obtain ⟨-, -, -, -, hcard⟩ := R3c6.psl3Data hL32
      have h168 : Nat.card (↥L ⧸ Subgroup.center ↥L) = 168 := by
        norm_num at hcard
        omega
      have hcardL := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥L)
      obtain ⟨a, ha⟩ := (R3c3.isPGroup_two_center c.c33.center_eq).exists_card_eq
      rw [hcardL, h168, ha] at h9L
      have hcop : Nat.Coprime 9 (2 ^ a) := Nat.Coprime.pow_right a (by norm_num)
      have : 9 ∣ 168 := hcop.dvd_of_dvd_mul_right h9L
      omega
  · exact bender_cl c hN hYL (A5.C25.fusionIsBenderGroup_of_isPSL h)
  · exact bender_cl c hN hYL (K1.fusionIsBenderGroup_of_stated_psu_three hf h)
  · exact c.c34.not_Sz ⟨f, hm⟩

end Main

end CFSG.Quasithin.R3c10
