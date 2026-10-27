module

public import CFSG.Quasithin.Vol2.Ch11SecBE22NParam

public section

namespace CFSG.Quasithin.E2

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Vol2.Ch11.SecB

namespace E22N

@[expose] def TypeOneOdd (Y : Type) [Group Y] : Prop :=
  (∃ p e : ℕ, p.Prime ∧ p ≠ 2 ∧ 5 < p ^ e ∧ IsPSL 2 p e Y) ∨
    ∃ (s : Bool) (p : ℕ), p.Prime ∧ p ≠ 2 ∧ IsPSLEps3 s p 1 Y

theorem TypeOneOdd.of_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y')
    (h : TypeOneOdd Y') : TypeOneOdd Y := by
  rcases h with ⟨p, f, hp, hp2, h5, h⟩ | ⟨s, p, hp, hp2, h⟩
  · exact Or.inl ⟨p, f, hp, hp2, h5, CFSG.SectionRank.statedClassicalModel_of_mulEquiv e h⟩
  · refine Or.inr ⟨s, p, hp, hp2, ?_⟩
    cases s with
    | true => exact CFSG.SectionRank.statedClassicalModel_of_mulEquiv e h
    | false => exact CFSG.SectionRank.statedClassicalModel_of_mulEquiv e h

theorem TypeOne.cases {Y : Type} [Group Y] (h : TypeOne Y) : TypeLie 1 Y ∨ TypeOneOdd Y := by
  rcases h with h | h | h | h
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, h⟩)))))
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

theorem typeOne_isoInv : IsoInv (fun X _ => TypeOne X) := by
  intro A B _ _ e h
  exact TypeOne.of_mulEquiv e h

@[expose] def TypeK : GrpPred := fun X _ => (∃ n : ℕ, TypeLie n X) ∨ TypeOne X

theorem typeK_isoInv : IsoInv TypeK := by
  intro A B _ _ e h
  rcases h with ⟨n, hn⟩ | h
  · exact Or.inl ⟨n, TypeLie.of_mulEquiv e hn⟩
  · exact Or.inr (TypeOne.of_mulEquiv e h)

@[expose] def E111ForQn (Q : GrpPred) (n : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], ASInputs.E111Hyp G n → SecAll G Q →
    E1.nParam (⊤ : Subgroup G) ≤ (n : ℕ∞)

@[expose] def E111ForQ (Q : GrpPred) : Prop := ∀ n : ℕ, 1 ≤ n → E111ForQn Q n

@[expose] def E111ForK : Prop := E111ForQ TypeK

theorem e111ForQ_of_e111 (Q : GrpPred) (h : ASInputs.AS_E_1_11) : E111ForQ Q :=
  fun n hn G _ _ hH _ => h G n hn hH

theorem e111ForK_of_e111 (h : ASInputs.AS_E_1_11) : E111ForK := e111ForQ_of_e111 TypeK h

variable {G : Type} [Group G] [Finite G]

theorem nParam_le_of_star {Q : GrpPred} {n : ℕ} (hQ : IsoInv Q) (h111 : E111ForQn Q n)
    {H T M K R : Subgroup G} (hTH : T ≤ H) (hT2 : IsPGroup 2 T) (hKc : K ∈ cComp H)
    (hHK : H = K ⊔ T) (hJs : Group.IsSolvable ↥(kerIn M H))
    (hKs : IsSimpleGroup ↥(E2.star M H K)) (hKK : Q ↥(E2.star M H K))
    (hP : ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
      Nonempty (X ≃* ↥(E2.star M H K)) → ∀ B : Subgroup (MulAut X), IsPGroup 2 B →
      IsSylowIn 2 (B ⊓ (MulAut.conj : X →* MulAut X).range)
        (MulAut.conj : X →* MulAut X).range →
      E1.nParam ((MulAut.conj : X →* MulAut X).range ⊔ B) ≤ n)
    (hRH : R ≤ H) : E1.nParam (R ⊔ oTwoUpper H) ≤ n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y := R ⊔ oTwoUpper H with hYdef
  have hYH : Y ≤ H := sup_le hRH (oTwoUpper_le H)
  have hKH : K ≤ H := by rw [hHK]; exact le_sup_left
  set J' := (kerIn M H).subgroupOf H with hJ'
  set π : ↥H →* E2.StarQuot M H := QuotientGroup.mk' J' with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective J'
  set Ks : Subgroup (E2.StarQuot M H) := (K.subgroupOf H).map π with hKsdef
  have hKs' : IsSimpleGroup ↥Ks := hKs
  have hKp : Group.IsPerfect ↥K := A36A.isPerfect_of_mem_cComp hKc
  have hKab : ∃ a b : ↥Ks, a * b ≠ b * a :=
    nonabelian_of_perfect_surjective
      ((π.subgroupMap (K.subgroupOf H)).comp (Subgroup.subgroupOfEquivOfLe hKH).symm.toMonoidHom)
      ((π.subgroupMap_surjective _).comp (Subgroup.subgroupOfEquivOfLe hKH).symm.surjective)
  have hKsn : Ks.IsSubnormal := by
    have h1 := A4.subnormal_comap H.subtype hKc.2.2.1
    have h2 : H.comap H.subtype = ⊤ := Subgroup.subgroupOf_self H
    rw [h2] at h1
    exact (isSubnormal_of_open h1 Subgroup.IsSubnormal.top).map hπs
  set Ts : Subgroup (E2.StarQuot M H) := (T.subgroupOf H).map π with hTsdef
  have hTs : IsPGroup 2 ↥Ts := (hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTH).symm).map π
  have hKT : Ks ⊔ Ts = ⊤ := by
    have h1 : K.subgroupOf H ⊔ T.subgroupOf H = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hKH hTH, ← hHK, Subgroup.subgroupOf_self]
    rw [hKsdef, hTsdef, ← Subgroup.map_sup, h1, Subgroup.map_top_of_surjective π hπs]
  set Os : Subgroup (E2.StarQuot M H) := ((oTwoUpper H).subgroupOf H).map π with hOsdef
  have hOn : Os.Normal := by
    have : ((oTwoUpper H).subgroupOf H).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (oTwoUpper_le H)).mpr
        (le_normalizer_oTwoUpper H)
    exact this.map π hπs
  have hKO : Ks ≤ Os := Subgroup.map_mono fun x hx =>
    B1Red.perfect_le_oTwoUpper' hKH hKp (Subgroup.mem_subgroupOf.mp hx)
  set f : ↥Y →* E2.StarQuot M H := π.comp (Subgroup.inclusion hYH) with hf
  have hOY : Os ≤ f.range := by
    rintro _ ⟨o, ho, rfl⟩
    exact ⟨⟨o, le_sup_right (a := R) (Subgroup.mem_subgroupOf.mp ho)⟩, rfl⟩
  set P : GrpPred := fun (X : Type) [Group X] => Nonempty (X ≃* ↥Ks) with hPdef
  have hPi : IsoInv P := by
    intro A B _ _ e h
    obtain ⟨e'⟩ := h
    exact ⟨e.trans e'⟩
  have hsecY' : SecAll ↥f.range P :=
    secAll_of_simple_subnormal hPi hKs' hKab hKsn ⟨MulEquiv.refl _⟩ hTs hKT hOn hKO hOY
  have hker : Group.IsSolvable ↥f.rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    let j : ↥f.ker →* ↥(kerIn M H) :=
      { toFun := fun y => ⟨((y : ↥Y) : G), by
          have hy : π (Subgroup.inclusion hYH (y : ↥Y)) = 1 := y.2
          rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hJ',
            Subgroup.mem_subgroupOf] at hy
          exact hy⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    refine Group.isSolvable_of_isSolvable_injective (f := j) fun a b hab => ?_
    apply Subtype.ext
    apply Subtype.ext
    simpa [j] using congrArg Subtype.val hab
  have hsecY : SecAll ↥Y P :=
    secAll_of_surjective hPi f.rangeRestrict f.rangeRestrict_surjective hker hsecY'
  have hE : ASInputs.E111Hyp ↥Y n := by
    intro H₁ K₁ _ _ hsn hsimple hnab B hB hBI
    have hsn' : H₁.IsSubnormal := isSubnormal_of_open hsn Subgroup.IsSubnormal.top
    obtain ⟨e⟩ := hsecY H₁ (K₁.subgroupOf H₁) hsn' hsimple hnab
    exact hP _ hnab ⟨e⟩ B hB hBI
  have hSecK : SecAll ↥Y Q := by
    intro H₁ N₁ _ hsn hsimple hnab
    obtain ⟨e⟩ := hsecY H₁ N₁ hsn hsimple hnab
    exact hQ _ _ e hKK
  have := h111 ↥Y hE hSecK
  rw [E1.nParam_subgroupOf]
  simpa using this

@[expose] def E114ForE22 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Subgroup G), SQTKGroup G →
    IsSimpleGroup (ASInputs.FStar G) → quasithinIsSylowTwo T →
    CFSG.generalizedFitting G ⊔ T = ⊤ →
      (∀ n : ℕ, 1 ≤ n → TypeLie n (ASInputs.FStar G) → E1.nParam (⊤ : Subgroup G) = n) ∧
      (TypeOneOdd (ASInputs.FStar G) → E1.nParam (⊤ : Subgroup G) ≤ 1)

theorem e114ForE22_of_e114 (h : ASInputs.AS_E_1_14) : E114ForE22 := by
  intro G _ _ T hSQ hFs hT hFT
  obtain ⟨h1, -, -, -, -, -, h6, h7⟩ := h G T hSQ hFs hT hFT
  refine ⟨fun n hn hty => h1 n hn ?_, ?_⟩
  · rcases hty with h | h | h | h | h | ⟨hn1, h⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr ⟨hn1, h⟩)))))
  · rintro (⟨p, f, hp, hp2, h5, hh⟩ | ⟨s, p, hp, hp2, hh⟩)
    · exact (h6 p f hp hp2 h5 hh).le
    · exact (h7 s p hp hp2 hh).le

theorem nParam_sup_eq_of_typeLie (h114 : E114ForE22) {n : ℕ} (hn : 1 ≤ n)
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X] (hnab : ∃ a b : X, a * b ≠ b * a)
    (hSQ : SQTKGroup X) (hT : TypeLie n X) {B : Subgroup (MulAut X)} (hB : IsPGroup 2 B)
    (hBI : IsSylowIn 2 (B ⊓ (MulAut.conj : X →* MulAut X).range)
      (MulAut.conj : X →* MulAut X).range) :
    E1.nParam ((MulAut.conj : X →* MulAut X).range ⊔ B) = n := by
  set I := (MulAut.conj : X →* MulAut X).range with hI
  set Z := I ⊔ B with hZdef
  have hIn : I.Normal := normal_range_conj X
  have hSQI : SQTKGroup ↥I :=
    sqtkGroup_of_mulEquiv (rangeConjEquiv (center_eq_bot_of_nonabelian' hnab)).symm hSQ
  have hSQZ : SQTKGroup ↥Z := InternalSec.sqtkGroup_of_two_pow le_sup_left
    (fun y _ k hk => hIn.conj_mem k hk y) (pow_mem_of_mem_sup hB) hSQI
  set e := generalizedFittingEquiv hnab B with he
  have hFs : IsSimpleGroup (ASInputs.FStar ↥Z) := e.isSimpleGroup
  have hFT : TypeLie n (ASInputs.FStar ↥Z) := TypeLie.of_mulEquiv e hT
  have key : E1.nParam (⊤ : Subgroup ↥Z) = n :=
    (h114 ↥Z (B.subgroupOf Z) hSQZ hFs (isSylowTwo_sup hB hBI)
      (generalizedFitting_sup_sup hnab B)).1 n hn hFT
  rw [E1.nParam_subgroupOf, key]

theorem nParam_sup_le_one (h114 : E114ForE22) {X : Type} [Group X] [Finite X]
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
  have h := h114 ↥Z (B.subgroupOf Z) hSQZ hFs (isSylowTwo_sup hB hBI)
    (generalizedFitting_sup_sup hnab B)
  have key : E1.nParam (⊤ : Subgroup ↥Z) ≤ 1 := by
    rcases TypeOne.cases hFT with h1 | h1
    · exact (h.1 1 le_rfl h1).le
    · exact h.2 h1
  rw [E1.nParam_subgroupOf]
  exact key


theorem e22NParamC_of (h111 : E111ForK) (h114 : E114ForE22) :
    E22NParamC := by
  intro Γ _ _ H T M K hmin hSQ hns hKc hHK hq hcases hSQs
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (StarQuot M H) := E2P.finite_starQuot M H
  have hTH : T ≤ H := hmin.isSylow.1
  have hT2 : IsPGroup 2 T := hmin.isSylow.2.1
  have hKH : K ≤ H := le_of_mem_cComp hKc
  have hJs : Group.IsSolvable ↥(kerIn M H) := isSolvable_kerIn_of_e22CasesNoN hcases
  have hO2T : oTwoUpper H ⊔ T = H := C1Pack12.oTwoUpper_sup_eq_of_sylow hmin.isSylow
  have hge1 := E22A.one_le_nParam hmin
  set Ks := star M H K with hKs
  set π := QuotientGroup.mk' ((kerIn M H).subgroupOf H) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hKp : Group.IsPerfect ↥K := A36A.isPerfect_of_mem_cComp hKc
  have hnab : IsSimpleGroup ↥Ks → ∃ a b : ↥Ks, a * b ≠ b * a := fun hsimp => by
    have : Nontrivial ↥Ks := hsimp.toNontrivial
    exact nonabelian_of_perfect_surjective
      ((π.subgroupMap (K.subgroupOf H)).comp (Subgroup.subgroupOfEquivOfLe hKH).symm.toMonoidHom)
      ((π.subgroupMap_surjective _).comp (Subgroup.subgroupOfEquivOfLe hKH).symm.surjective)
  have hSQK : SQTKGroup ↥Ks := sqtkGroup_subgroup hSQs Ks
  have hbound : ∀ n : ℕ, 1 ≤ n → IsSimpleGroup ↥Ks → TypeK ↥Ks →
      (∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
        Nonempty (X ≃* ↥Ks) → ∀ B : Subgroup (MulAut X), IsPGroup 2 B →
        IsSylowIn 2 (B ⊓ (MulAut.conj : X →* MulAut X).range)
          (MulAut.conj : X →* MulAut X).range →
        E1.nParam ((MulAut.conj : X →* MulAut X).range ⊔ B) ≤ n) → E1.nParam H ≤ n := by
    intro n hn hsimp hKK hP
    have h := nParam_le_of_star typeK_isoInv (h111 n hn) hTH hT2 hKc hHK hJs hsimp hKK hP hTH
    rwa [sup_comm, hO2T] at h
  have hLie : ∀ n : ℕ, 1 ≤ n → TypeLie n ↥Ks → E1.nParam H ≤ n := by
    intro n hn hty
    refine hbound n hn hty.isSimpleGroup (Or.inl ⟨n, hty⟩) fun X _ _ _ hnabX ⟨e⟩ B hB hBI => ?_
    have hSQX : SQTKGroup X := sqtkGroup_of_mulEquiv e hSQK
    exact (nParam_sup_eq_of_typeLie h114 hn hnabX hSQX (TypeLie.of_mulEquiv e hty) hB hBI).le
  have hOne : TypeOne ↥Ks → E1.nParam H = 1 := by
    intro hty
    refine le_antisymm ?_ hge1
    have h := hbound 1 le_rfl hty.isSimpleGroup (Or.inr hty) fun X _ _ _ hnabX ⟨e⟩ B hB hBI => by
      have hSQX : SQTKGroup X := sqtkGroup_of_mulEquiv e hSQK
      simpa using nParam_sup_le_one h114 hnabX hSQX (TypeOne.of_mulEquiv e hty) hB hBI
    simpa using h
  have hStar : T ≤ Subgroup.normalizer (K : Set Γ) → ∀ n : ℕ, 1 ≤ n → TypeLie n ↥Ks →
      E1.nParam (⊤ : Subgroup (StarQuot M H)) = n := by
    intro hTK n hn hty
    have hsimp := hty.isSimpleGroup
    have hF := E22A.generalizedFitting_star hmin hKc hHK hTK hJs hsimp (hnab hsimp)
    set Ts := (T.subgroupOf H).map π with hTs
    have hTsS : IsSylowTwoOf Ts π.range := E2P.isSylowTwoOf_map_hom hmin.isSylow π
    rw [MonoidHom.range_eq_top.mpr hπs] at hTsS
    have hqs : quasithinIsSylowTwo Ts :=
      ⟨hTsS.2.1, fun h => hTsS.2.2 (by
        show 2 ∣ Ts.relIndex ⊤
        rw [Subgroup.relIndex_top_right]
        exact h)⟩
    have hKT : CFSG.generalizedFitting (StarQuot M H) ⊔ Ts = ⊤ := by
      rw [hF]
      have h1 : K.subgroupOf H ⊔ T.subgroupOf H = ⊤ := by
        rw [← Subgroup.subgroupOf_sup hKH hTH, ← hHK, Subgroup.subgroupOf_self]
      rw [star, hTs, ← Subgroup.map_sup, h1, Subgroup.map_top_of_surjective π hπs]
    have eF : ASInputs.FStar (StarQuot M H) ≃* ↥Ks := MulEquiv.subgroupCongr hF
    have hFs : IsSimpleGroup (ASInputs.FStar (StarQuot M H)) := eF.isSimpleGroup
    exact (h114 (StarQuot M H) Ts hSQs hFs hqs hKT).1 n hn (TypeLie.of_mulEquiv eF hty)
  dsimp only [E22NParamCases]
  refine ⟨fun _ _ => ⟨fun n hn2 hty _ => hLie n (by omega) ?_, fun p hp hp8 hK _ _ => hOne ?_⟩,
    fun hTK _ => ⟨fun n hBen _ => ?_, fun n hn1 hty _ _ => ?_,
      fun p e hp hp3 he hpe8 hK _ _ => hOne ?_, fun p hp hp2 hK _ => hOne ?_⟩⟩
  ·
    rcases hty with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  ·
    have h1 := hp.one_lt
    have hp2 : p ≠ 2 := by omega
    have h5 : 5 < p ^ 1 := by rw [pow_one]; omega
    exact Or.inr (Or.inr (Or.inl ⟨p, 1, hp, hp2, h5, hK⟩))
  ·
    have hT' : TypeLie n ↥Ks := by
      rcases hBen.2 with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
    exact ⟨hLie n (by have := hBen.1; omega) hT', hStar hTK n (by have := hBen.1; omega) hT'⟩
  ·
    have hT' : TypeLie n ↥Ks := by
      rcases hty with h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · rw [IsSp4Prime] at h
        split_ifs at h with h1
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h1, h⟩))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    exact ⟨hLie n hn1 hT', hStar hTK n hn1 hT'⟩
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

theorem e22StatementC_of_e114 (hNoN : E22StatementNoN) (h111 : E111ForK)
    (h114 : E114ForE22) : E22StatementC :=
  ⟨hNoN, e22NParamC_of h111 h114⟩

end E22N

end CFSG.Quasithin.E2
