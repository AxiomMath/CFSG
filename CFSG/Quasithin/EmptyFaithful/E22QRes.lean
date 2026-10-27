module

public import CFSG.Quasithin.EmptyFaithful.E22QOne
public import CFSG.Quasithin.EmptyFaithful.E22PRes
public import CFSG.Quasithin.EmptyFaithful.E22NE111

public section

namespace CFSG.Quasithin.E2.E22N

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Vol2.Ch11.SecB

variable {G : Type} [Group G] [Finite G]

theorem nParam_le_of_starC {Q : GrpPred} {C : (Y : Type) → [Group Y] → Prop} {n : ℕ}
    (hQ : IsoInv Q)
    (h111 : ∀ (Y : Type) [Group Y] [Finite Y], ASInputs.E111Hyp Y n → SecAll Y Q → C Y →
      E1.nParam (⊤ : Subgroup Y) ≤ (n : ℕ∞))
    {H T M K R : Subgroup G} (hTH : T ≤ H) (hT2 : IsPGroup 2 T) (hKc : K ∈ cComp H)
    (hHK : H = K ⊔ T) (hJs : Group.IsSolvable ↥(kerIn M H))
    (hKs : IsSimpleGroup ↥(E2.star M H K)) (hKK : Q ↥(E2.star M H K))
    (hP : ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
      Nonempty (X ≃* ↥(E2.star M H K)) → ∀ B : Subgroup (MulAut X), IsPGroup 2 B →
      IsSylowIn 2 (B ⊓ (MulAut.conj : X →* MulAut X).range)
        (MulAut.conj : X →* MulAut X).range →
      E1.nParam ((MulAut.conj : X →* MulAut X).range ⊔ B) ≤ n)
    (hRH : R ≤ H) (hC : C ↥(R ⊔ oTwoUpper H)) : E1.nParam (R ⊔ oTwoUpper H) ≤ n := by
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
  have := h111 ↥Y hE hSecK hC
  rw [E1.nParam_subgroupOf]
  simpa using this


theorem solvSimpSolv_of_star {H T M K R : Subgroup G} (hTH : T ≤ H) (hT2 : IsPGroup 2 T)
    (hKc : K ∈ cComp H) (hHK : H = K ⊔ T) (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hJs : Group.IsSolvable ↥(kerIn M H)) (hKs : IsSimpleGroup ↥(E2.star M H K))
    (hRH : R ≤ H) : SolvSimpSolv ↥(R ⊔ oTwoUpper H) := by
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
  have hHnorm : H ≤ Subgroup.normalizer (K : Set G) := by
    rw [hHK]
    exact sup_le Subgroup.le_normalizer hTK
  have hKHn : (K.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr hHnorm
  have hKsn : Ks.Normal := hKHn.map π hπs
  set Ts : Subgroup (E2.StarQuot M H) := (T.subgroupOf H).map π with hTsdef
  have hTs : IsPGroup 2 ↥Ts := (hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTH).symm).map π
  have hKT : Ks ⊔ Ts = ⊤ := by
    have h1 : K.subgroupOf H ⊔ T.subgroupOf H = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hKH hTH, ← hHK, Subgroup.subgroupOf_self]
    rw [hKsdef, hTsdef, ← Subgroup.map_sup, h1, Subgroup.map_top_of_surjective π hπs]
  set Os : Subgroup (E2.StarQuot M H) := ((oTwoUpper H).subgroupOf H).map π with hOsdef
  have hKO : Ks ≤ Os := Subgroup.map_mono fun x hx =>
    B1Red.perfect_le_oTwoUpper' hKH hKp (Subgroup.mem_subgroupOf.mp hx)
  set f : ↥Y →* E2.StarQuot M H := π.comp (Subgroup.inclusion hYH) with hf
  have hOY : Os ≤ f.range := by
    rintro _ ⟨o, ho, rfl⟩
    exact ⟨⟨o, le_sup_right (a := R) (Subgroup.mem_subgroupOf.mp ho)⟩, rfl⟩
  have hker : Group.IsSolvable ↥f.ker := by
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
  have hqsolv : Group.IsSolvable (E2.StarQuot M H ⧸ Ks) := by
    have h2q : IsPGroup 2 (E2.StarQuot M H ⧸ Ks) := by
      intro q
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Ks q
      obtain ⟨e, he⟩ := pow_mem_of_mem_sup_normal hTs x (hKT ▸ Subgroup.mem_top x)
      exact ⟨e, (QuotientGroup.eq_one_iff _).mpr he⟩
    have := h2q.isNilpotent
    infer_instance
  exact solvSimpSolv_of_hom f hker Ks hKs' (hKO.trans hOY) (exists_derivedSeries_le_of_solvable Ks)

theorem isoInv_isPSL_two (p : ℕ) : IsoInv (fun (X : Type) [Group X] => IsPSL 2 p 1 X) := by
  intro A B _ _ e h
  exact CFSG.SectionRank.statedClassicalModel_of_mulEquiv e h

@[expose] def E111CoreMultiL2 : Prop :=
  ∀ p : ℕ, p.Prime → (p % 8 = 1 ∨ p % 8 = 7) →
    E111CoreMultiQn (fun X _ => IsPSL 2 p 1 X) 1

theorem e22NParamW_of_L2 (h111 : E111CoreMultiL2)
    (h114 : E114OneResNoA6) : E2.E22NParamW := by
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
  have h114' : E114OneRes := e114OneRes_of_noA6 h114
  have hP : TypeOneRes ↥Ks → ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X],
      (∃ a b : X, a * b ≠ b * a) → Nonempty (X ≃* ↥Ks) → ∀ B : Subgroup (MulAut X),
      IsPGroup 2 B → IsSylowIn 2 (B ⊓ (MulAut.conj : X →* MulAut X).range)
        (MulAut.conj : X →* MulAut X).range →
      E1.nParam ((MulAut.conj : X →* MulAut X).range ⊔ B) ≤ ((1 : ℕ) : ℕ∞) :=
    fun hty X _ _ _ hnabX ⟨e⟩ B hB hBI => by
      have hSQX : SQTKGroup X := sqtkGroup_of_mulEquiv e hSQK
      simpa using nParam_sup_le_one_of_res h114' hnabX hSQX (TypeOneRes.of_mulEquiv e hty) hB hBI
  have hfin : E1.nParam (T ⊔ oTwoUpper H) ≤ 1 → E1.nParam H = 1 :=
    fun h => by
      refine le_antisymm ?_ hge1
      rw [sup_comm, hO2T] at h
      simpa using h
  have hOneN : T ≤ Subgroup.normalizer (K : Set Γ) → TypeOneRes ↥Ks → E1.nParam H = 1 := by
    intro hTK hty
    refine hfin ?_
    have h := nParam_le_of_starC (Q := fun X _ => TypeOne X) (C := SolvSimpSolv)
      typeOne_isoInv (fun Y _ _ hH hK hC => e111ForQnC_sss typeOne_isoInv le_rfl Y hH hK hC)
      hTH hT2 hKc hHK hJs hty.toTypeOne.isSimpleGroup hty.toTypeOne (hP hty) hTH
      (solvSimpSolv_of_star hTH hT2 hKc hHK hTK hJs hty.toTypeOne.isSimpleGroup hTH)
    exact_mod_cast h
  have hOneM : ∀ p : ℕ, p.Prime → (p % 8 = 1 ∨ p % 8 = 7) → IsPSL 2 p 1 ↥Ks →
      E1.nParam H = 1 := by
    intro p hp hp8 hK
    have h1 := hp.two_le
    have hty : TypeOneRes ↥Ks :=
      Or.inr (Or.inr (Or.inl ⟨p, 1, hp, by omega, Or.inl rfl, by simpa using hp8, hK⟩))
    refine hfin ?_
    have h := nParam_le_of_star (Q := fun X _ => IsPSL 2 p 1 X) (isoInv_isPSL_two p)
      (e111ForQn_of_core (isoInv_isPSL_two p) le_rfl (h111 p hp hp8))
      hTH hT2 hKc hHK hJs hty.toTypeOne.isSimpleGroup hK (hP hty) hTH
    exact_mod_cast h
  dsimp only [E2.E22NParamWCases]
  refine ⟨fun _ _ p hp hp8 hK _ _ => hOneM p hp hp8 hK, fun hTK _ =>
    ⟨fun n hn1 hty _ _ hn => ?_, fun p e hp hp3 he hpe8 hK _ _ => hOneN hTK ?_,
      fun p hp hp2 hK _ => hOneN hTK ?_⟩⟩
  ·
    subst hn
    refine (hOneN hTK ?_).le
    rcases hty with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (by simpa [IsSp4Prime] using h))
  ·
    exact Or.inr (Or.inr (Or.inl ⟨p, e, hp, hp3, he, hpe8, hK⟩))
  ·
    rcases hK with ⟨h4, hK⟩ | ⟨h4, hK, -⟩
    · exact Or.inr (Or.inr (Or.inr ⟨false, p, hp, hp2, by simp, fun _ => h4, hK⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨true, p, hp, hp2, fun _ => h4, by simp, hK⟩))

end CFSG.Quasithin.E2.E22N
