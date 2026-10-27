module

public import CFSG.Quasithin.EmptyFaithful.E22NParam

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Vol2.Ch11.SecB

namespace E2

variable {Γ : Type} [Group Γ]

@[expose] def E22NParamWCases (H T M K : Subgroup Γ) : Prop :=
  let Ks := star M H K
  let MKs := star M H (M ⊓ K)
  let TKs := star M H (T ⊓ K)
  let Ts := star M H T
  let Q := pCoreOf 2 H
  let ZTK := TKs ⊓ Subgroup.centralizer (TKs : Set (StarQuot M H))
  (kerIn M H = Q → (∃ t ∈ T, cjSub t K ≠ K ∧ M = (M ⊓ K) ⊔ cjSub t (M ⊓ K) ⊔ T) →
    ∀ p : ℕ, p.Prime → (p % 8 = 1 ∨ p % 8 = 7) → IsPSL 2 p 1 ↥Ks →
      MKs = Ks ⊓ Subgroup.centralizer (ZTK : Set (StarQuot M H)) → 8 < autCard Ts Ks →
      E1.nParam H = 1) ∧
  (T ≤ Subgroup.normalizer (K : Set Γ) →
    (∀ x : Γ, x ∈ kerIn M H ↔ x ∈ K ⊔ Q ∧ ∀ y ∈ K ⊔ Q, x * y * x⁻¹ * y⁻¹ ∈ Q) →
    (∀ n : ℕ, 1 ≤ n → (IsPSL 3 2 n ↥Ks ∨ IsSp4Prime n ↥Ks) → IsDiagramNontrivial Ts Ks TKs →
        IsBorelIn Ks MKs → n = 1 → E1.nParam H ≤ 1) ∧
      (∀ p e : ℕ, p.Prime → 3 < p → (e = 1 ∨ e = 2) → (p ^ e % 8 = 1 ∨ p ^ e % 8 = 7) →
        IsPSL 2 p e ↥Ks → MKs = Ks ⊓ Subgroup.centralizer (ZTK : Set (StarQuot M H)) →
        8 < autCard Ts Ks → E1.nParam H = 1) ∧
      (∀ p : ℕ, p.Prime → p ≠ 2 →
        ((p % 4 = 1 ∧ IsPSU 3 p 1 ↥Ks) ∨ (p % 4 = 3 ∧ IsPSL 3 p 1 ↥Ks ∧ InducesOuter Ts Ks)) →
        MKs = Ks ⊓ Subgroup.centralizer (ZTK : Set (StarQuot M H)) → E1.nParam H = 1))

@[expose] def E22NParamW : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (H T M K : Subgroup Γ), MinParabolic H T M → SQTKGroup ↥H →
    ¬ Group.IsSolvable ↥H → K ∈ cComp H → H = K ⊔ T →
    CFSG.Open.IsQuasisimple (↥K ⧸ CFSG.Open.pCore 2 ↥K) → E22CasesNoN H T M K →
    SQTKGroup (StarQuot M H) → E22NParamWCases H T M K

@[expose] def E22StatementW : Prop :=
  E22StatementNoN ∧ E22NParamW

theorem E22StatementW.toNoN (h : E22StatementW) : E22StatementNoN :=
  h.1

theorem E22StatementW.toNParam (h : E22StatementW) : E22NParamW :=
  h.2

theorem e22NParamWCases_of_e22NParamCases {H T M K : Subgroup Γ} (h : E22NParamCases H T M K) :
    E22NParamWCases H T M K := by
  dsimp only [E22NParamCases] at h
  dsimp only [E22NParamWCases]
  refine ⟨fun hJ ht p hp hp8 hK hMK haut => (h.1 hJ ht).2 p hp hp8 hK hMK haut,
    fun hTK hJ => ?_⟩
  obtain ⟨-, hb, hc, hd⟩ := h.2 hTK hJ
  refine ⟨fun n hn hty hD hB hn1 => ?_, hc, hd⟩
  have := (hb n hn hty hD hB).1
  subst hn1
  simpa using this

theorem E22StatementC.toW (h : E22StatementC) : E22StatementW :=
  ⟨h.toNoN, fun Γ _ _ H T M K hmin hSQ hns hKc hHK hq hc hSQs =>
    e22NParamWCases_of_e22NParamCases (h.toNParam Γ H T M K hmin hSQ hns hKc hHK hq hc hSQs)⟩

@[expose] def E22CasesW (H T M K : Subgroup Γ) : Prop :=
  let Ks := star M H K
  let MKs := star M H (M ⊓ K)
  let TKs := star M H (T ⊓ K)
  let Ts := star M H T
  let Q := pCoreOf 2 H
  let ZTK := TKs ⊓ Subgroup.centralizer (TKs : Set (StarQuot M H))
  (kerIn M H = Q ∧ ∃ t ∈ T, cjSub t K ≠ K ∧ M = (M ⊓ K) ⊔ cjSub t (M ⊓ K) ⊔ T ∧
    ((∃ n : ℕ, 2 ≤ n ∧ (IsPSL 2 2 n ↥Ks ∨ IsSz n ↥Ks) ∧ IsBorelIn Ks MKs) ∨
      (∃ p : ℕ, p.Prime ∧ (p % 8 = 1 ∨ p % 8 = 7) ∧ IsPSL 2 p 1 ↥Ks ∧
        MKs = Ks ⊓ Subgroup.centralizer (ZTK : Set (StarQuot M H)) ∧ 8 < autCard Ts Ks ∧
        E1.nParam H = 1))) ∨
  (T ≤ Subgroup.normalizer (K : Set Γ) ∧
    (∀ x : Γ, x ∈ kerIn M H ↔ x ∈ K ⊔ Q ∧ ∀ y ∈ K ⊔ Q, x * y * x⁻¹ * y⁻¹ ∈ Q) ∧
    ((∃ n : ℕ, IsBenderOf n ↥Ks ∧ IsBorelIn Ks MKs) ∨
      (∃ n : ℕ, 1 ≤ n ∧ (IsPSL 3 2 n ↥Ks ∨ IsSp4Prime n ↥Ks) ∧ IsDiagramNontrivial Ts Ks TKs ∧
        IsBorelIn Ks MKs ∧ (n = 1 → E1.nParam H ≤ 1)) ∨
      (∃ p e : ℕ, p.Prime ∧ 3 < p ∧ (e = 1 ∨ e = 2) ∧ (p ^ e % 8 = 1 ∨ p ^ e % 8 = 7) ∧
        IsPSL 2 p e ↥Ks ∧ MKs = Ks ⊓ Subgroup.centralizer (ZTK : Set (StarQuot M H)) ∧
        8 < autCard Ts Ks ∧ E1.nParam H = 1) ∨
      (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧
        ((p % 4 = 1 ∧ IsPSU 3 p 1 ↥Ks) ∨ (p % 4 = 3 ∧ IsPSL 3 p 1 ↥Ks ∧ InducesOuter Ts Ks)) ∧
        MKs = Ks ⊓ Subgroup.centralizer (ZTK : Set (StarQuot M H)) ∧ E1.nParam H = 1)))

theorem e22CasesW_of_noN {H T M K : Subgroup Γ} (hc : E22CasesNoN H T M K)
    (hn : E22NParamWCases H T M K) : E22CasesW H T M K := by
  dsimp only [E22CasesNoN] at hc
  dsimp only [E22NParamWCases] at hn
  dsimp only [E22CasesW]
  rcases hc with ⟨hJ, t, ht, hne, hM, h1⟩ | ⟨hTK, hJ, h2⟩
  · refine Or.inl ⟨hJ, t, ht, hne, hM, ?_⟩
    rcases h1 with ⟨n, hn2, hty, hB⟩ | ⟨p, hp, hp8, hK, hMK, haut⟩
    · exact Or.inl ⟨n, hn2, hty, hB⟩
    · exact Or.inr ⟨p, hp, hp8, hK, hMK, haut,
        hn.1 hJ ⟨t, ht, hne, hM⟩ p hp hp8 hK hMK haut⟩
  · obtain ⟨hb, hc', hd⟩ := hn.2 hTK hJ
    refine Or.inr ⟨hTK, hJ, ?_⟩
    rcases h2 with ⟨n, hBen, hB⟩ | ⟨n, h1n, hty, hD, hB⟩ |
        ⟨p, e, hp, hp3, he, hpe, hK, hMK, haut⟩ | ⟨p, hp, hp2, hK, hMK⟩
    · exact Or.inl ⟨n, hBen, hB⟩
    · exact Or.inr (Or.inl ⟨n, h1n, hty, hD, hB, hb n h1n hty hD hB⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨p, e, hp, hp3, he, hpe, hK, hMK, haut,
        hc' p e hp hp3 he hpe hK hMK haut⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨p, hp, hp2, hK, hMK, hd p hp hp2 hK hMK⟩))

end E2

namespace E2.E22StatementW

theorem exists_cases (h : E2.E22StatementW) {G : Type} [Group G] [Finite G]
    {H T M : Subgroup G} (hmin : MinParabolic H T M) (hSQ : SQTKGroup ↥H)
    (hns : ¬ Group.IsSolvable ↥H) :
    (∃ K : Subgroup G, K ∈ cComp H ∧ H = K ⊔ T ∧
      CFSG.Open.IsQuasisimple (↥K ⧸ CFSG.Open.pCore 2 ↥K) ∧ E2.E22CasesW H T M K) ∧
    SQTKGroup (E2.StarQuot M H) := by
  obtain ⟨⟨K, hKc, hHK, hq, hc⟩, hSQs⟩ := h.toNoN G H T M hmin hSQ hns
  exact ⟨⟨K, hKc, hHK, hq,
    E2.e22CasesW_of_noN hc (h.toNParam G H T M K hmin hSQ hns hKc hHK hq hc hSQs)⟩, hSQs⟩

end E2.E22StatementW

namespace E2.E22N

@[expose] def E114One : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Subgroup G), SQTKGroup G →
    IsSimpleGroup (ASInputs.FStar G) → quasithinIsSylowTwo T →
    CFSG.generalizedFitting G ⊔ T = ⊤ →
      TypeOne (ASInputs.FStar G) → E1.nParam (⊤ : Subgroup G) ≤ 1

theorem e114One_of_e114 (h : ASInputs.AS_E_1_14) : E114One := by
  intro G _ _ T hSQ hFs hT hFT hty
  obtain ⟨h1, -, -, -, -, -, h6, h7⟩ := h G T hSQ hFs hT hFT
  rcases hty with hh | hh | ⟨p, f, hp, hp2, h5, hh⟩ | ⟨s, p, hp, hp2, hh⟩
  · exact (h1 1 le_rfl (Or.inr (Or.inr (Or.inr (Or.inl hh))))).le
  · exact (h1 1 le_rfl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr ⟨rfl, hh⟩))))))).le
  · exact (h6 p f hp hp2 h5 hh).le
  · exact (h7 s p hp hp2 hh).le

theorem nParam_sup_le_one_of_one (h114 : E114One) {X : Type} [Group X] [Finite X]
    [IsSimpleGroup X] (hnab : ∃ a b : X, a * b ≠ b * a) (hSQ : SQTKGroup X) (hT : TypeOne X)
    {B : Subgroup (MulAut X)} (hB : IsPGroup 2 B)
    (hBI : IsSylowIn 2 (B ⊓ (MulAut.conj : X →* MulAut X).range)
      (MulAut.conj : X →* MulAut X).range) :
    E1.nParam ((MulAut.conj : X →* MulAut X).range ⊔ B) ≤ 1 := by
  set I := (MulAut.conj : X →* MulAut X).range with hI
  set Z := I ⊔ B with hZdef
  have hIn : I.Normal := normal_range_conj X
  have hSQI : SQTKGroup ↥I :=
    sqtkGroup_of_mulEquiv (rangeConjEquiv (center_eq_bot_of_nonabelian' hnab)).symm hSQ
  have hSQZ : SQTKGroup ↥Z := InternalSec.sqtkGroup_of_two_pow le_sup_left
    (fun y _ k hk => hIn.conj_mem k hk y) (pow_mem_of_mem_sup hB) hSQI
  set e := generalizedFittingEquiv hnab B with he
  have hFs : IsSimpleGroup (ASInputs.FStar ↥Z) := e.isSimpleGroup
  have hFT : TypeOne (ASInputs.FStar ↥Z) := TypeOne.of_mulEquiv e hT
  have key : E1.nParam (⊤ : Subgroup ↥Z) ≤ 1 :=
    h114 ↥Z (B.subgroupOf Z) hSQZ hFs (isSylowTwo_sup hB hBI)
      (generalizedFitting_sup_sup hnab B) hFT
  rw [E1.nParam_subgroupOf]
  exact key

theorem e22NParamW_of (h111 : E111ForQn (fun X _ => TypeOne X) 1) (h114 : E114One) :
    E2.E22NParamW := by
  intro Γ _ _ H T M K hmin hSQ hns hKc hHK hq hcases hSQs
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (E2.StarQuot M H) := E2P.finite_starQuot M H
  have hTH : T ≤ H := hmin.isSylow.1
  have hT2 : IsPGroup 2 T := hmin.isSylow.2.1
  have hKH : K ≤ H := le_of_mem_cComp hKc
  have hJs : Group.IsSolvable ↥(kerIn M H) := isSolvable_kerIn_of_e22CasesNoN hcases
  have hO2T : oTwoUpper H ⊔ T = H := C1Pack12.oTwoUpper_sup_eq_of_sylow hmin.isSylow
  have hge1 := E22A.one_le_nParam hmin
  set Ks := E2.star M H K with hKs
  set π := QuotientGroup.mk' ((kerIn M H).subgroupOf H) with hπ
  have hKp : Group.IsPerfect ↥K := A36A.isPerfect_of_mem_cComp hKc
  have hnab : IsSimpleGroup ↥Ks → ∃ a b : ↥Ks, a * b ≠ b * a := fun hsimp => by
    have : Nontrivial ↥Ks := hsimp.toNontrivial
    exact nonabelian_of_perfect_surjective
      ((π.subgroupMap (K.subgroupOf H)).comp (Subgroup.subgroupOfEquivOfLe hKH).symm.toMonoidHom)
      ((π.subgroupMap_surjective _).comp (Subgroup.subgroupOfEquivOfLe hKH).symm.surjective)
  have hSQK : SQTKGroup ↥Ks := sqtkGroup_subgroup hSQs Ks
  have hOne : TypeOne ↥Ks → E1.nParam H = 1 := by
    intro hty
    refine le_antisymm ?_ hge1
    have h := nParam_le_of_star (Q := fun X _ => TypeOne X) typeOne_isoInv h111
      hTH hT2 hKc hHK hJs hty.isSimpleGroup hty
      (fun X _ _ _ hnabX ⟨e⟩ B hB hBI => by
        have hSQX : SQTKGroup X := sqtkGroup_of_mulEquiv e hSQK
        simpa using nParam_sup_le_one_of_one h114 hnabX hSQX (TypeOne.of_mulEquiv e hty) hB hBI)
      hTH
    rw [sup_comm, hO2T] at h
    simpa using h
  dsimp only [E2.E22NParamWCases]
  refine ⟨fun _ _ p hp hp8 hK _ _ => hOne ?_, fun hTK _ =>
    ⟨fun n hn1 hty _ _ hn => ?_, fun p e hp hp3 he hpe8 hK _ _ => hOne ?_,
      fun p hp hp2 hK _ => hOne ?_⟩⟩
  ·
    have h1 := hp.one_lt
    have hp2 : p ≠ 2 := by omega
    have h5 : 5 < p ^ 1 := by rw [pow_one]; omega
    exact Or.inr (Or.inr (Or.inl ⟨p, 1, hp, hp2, h5, hK⟩))
  ·
    subst hn
    refine (hOne ?_).le
    rcases hty with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (by simpa [IsSp4Prime] using h))
  ·
    have h5 : 5 ≤ p ^ e := by
      rcases he with rfl | rfl
      · rw [pow_one] at hpe8 ⊢; omega
      · nlinarith
    refine Or.inr (Or.inr (Or.inl ⟨p, e, hp, by omega, ?_, hK⟩))
    generalize p ^ e = q at h5 hpe8 ⊢
    omega
  ·
    rcases hK with ⟨-, hK⟩ | ⟨-, hK, -⟩
    · exact Or.inr (Or.inr (Or.inr ⟨false, p, hp, hp2, hK⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨true, p, hp, hp2, hK⟩))

end E2.E22N

end CFSG.Quasithin
