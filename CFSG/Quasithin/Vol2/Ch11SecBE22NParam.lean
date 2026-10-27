module

public import CFSG.Quasithin.Vol2.Ch11SecBNPCaseL
public import CFSG.Quasithin.Background.E2TwoProofY
public import CFSG.Quasithin.Background.C1PackS15212A
public import CFSG.Quasithin.Vol2.Ch11SecBNPCasesC
public import CFSG.Quasithin.Vol2.Ch11SecBNPLie
public import CFSG.Quasithin.Vol2.Ch11SecBTCStar

public section

namespace CFSG.Quasithin.E2

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Vol2.Ch11.SecB

namespace E22A

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem one_le_nParam {H T M : Subgroup Γ} (hmin : MinParabolic H T M) : 1 ≤ E1.nParam H := by
  have heven : ¬ Odd (Nat.card H) := by
    intro hodd
    have hT1 : T = ⊥ := E1.eq_bot_of_isSylowIn_odd
      ⟨hmin.isSylow.1, hmin.isSylow.2.1, hmin.isSylow.2.2⟩ hodd
    apply hmin.not_normal
    rw [hT1, show Subgroup.normalizer ((⊥ : Subgroup Γ) : Set Γ) = ⊤ from
      Subgroup.normalizer_eq_top_iff.mpr inferInstance]
    exact le_top
  unfold E1.nParam
  split_ifs
  exact le_iInf₂ fun i hi => by exact_mod_cast hi.1

theorem generalizedFitting_star {H T M K : Subgroup Γ} (hmin : MinParabolic H T M)
    (hKc : K ∈ cComp H) (hHK : H = K ⊔ T) (hTK : T ≤ Subgroup.normalizer (K : Set Γ))
    (hJs : Group.IsSolvable ↥(kerIn M H)) (hKs : IsSimpleGroup ↥(star M H K))
    (hnab : ∃ a b : ↥(star M H K), a * b ≠ b * a) :
    CFSG.generalizedFitting (StarQuot M H) = star M H K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (StarQuot M H) := E2P.finite_starQuot M H
  set π := QuotientGroup.mk' ((kerIn M H).subgroupOf H) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hKH : K ≤ H := le_of_mem_cComp hKc
  have hTH : T ≤ H := hmin.isSylow.1
  have hT2 : IsPGroup 2 T := hmin.isSylow.2.1
  have hMH : M ≤ H := hmin.maximal.1.le
  have hns : ¬ Group.IsSolvable ↥H := fun hsol => not_isSolvable_of_mem_cComp hKc
    (Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hKH)
      (Subgroup.inclusion_injective hKH))
  have hRJ := solvRad_le_kerIn hmin.uniqueMax hT2 hns
  have hcomp := isComponent_star hMH hJs hRJ hKc
  have hHN : H ≤ Subgroup.normalizer (K : Set Γ) := hHK ▸ sup_le Subgroup.le_normalizer hTK
  have hKn : (K.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr hHN
  have hKsn : (star M H K).Normal := hKn.map π hπs
  set Ts := (T.subgroupOf H).map π with hTs
  have hTs2 : IsPGroup 2 ↥Ts :=
    (hT2.comap_of_injective H.subtype H.subtype_injective).map π
  have hKT : star M H K ⊔ Ts = ⊤ := by
    have h1 : K.subgroupOf H ⊔ T.subgroupOf H = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hKH hTH, ← hHK, Subgroup.subgroupOf_self]
    rw [star, hTs, ← Subgroup.map_sup, h1, Subgroup.map_top_of_surjective π hπs]
  set C := Subgroup.centralizer ((star M H K : Subgroup (StarQuot M H)) : Set (StarQuot M H))
    with hC
  have hZ : Subgroup.center ↥(star M H K) = ⊥ := center_eq_bot_of_nonabelian' hnab
  have hCK : ∀ c ∈ C, c ∈ star M H K → c = 1 := by
    intro c hc hcK
    have : (⟨c, hcK⟩ : ↥(star M H K)) ∈ Subgroup.center ↥(star M H K) := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hc) y y.2)
    rw [hZ, Subgroup.mem_bot] at this
    exact congrArg Subtype.val this
  have hC2 : IsPGroup 2 ↥C := by
    intro c
    obtain ⟨e, he⟩ := pow_mem_of_mem_sup_normal hTs2 (c : StarQuot M H)
      (hKT ▸ Subgroup.mem_top _)
    refine ⟨e, Subtype.ext ?_⟩
    simpa using hCK _ (C.pow_mem c.2 _) he
  have hCO : C ≤ CFSG.Open.pCore 2 (StarQuot M H) :=
    CFSG.LieType.BorelTits.le_pCore 2 inferInstance hC2
  have hO : CFSG.Open.pCore 2 (StarQuot M H) = ⊥ := by
    have h1 := (E2P.minParabolic_star hmin).pCore_le_kerIn
    rwa [E2P.kerIn_star, le_bot_iff] at h1
  have hCb : C = ⊥ := le_bot_iff.mp (hO ▸ hCO)
  exact generalizedFitting_eq_of_component _ hcomp hCb

end E22A

theorem e22NParamC_of (h1111 : ASInputs.AS_E_1_11) (h1114 : ASInputs.AS_E_1_14) :
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
  have hbound : ∀ n : ℕ, 1 ≤ n → IsSimpleGroup ↥Ks →
      (∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
        Nonempty (X ≃* ↥Ks) → ∀ B : Subgroup (MulAut X), IsPGroup 2 B →
        IsSylowIn 2 (B ⊓ (MulAut.conj : X →* MulAut X).range)
          (MulAut.conj : X →* MulAut X).range →
        E1.nParam ((MulAut.conj : X →* MulAut X).range ⊔ B) ≤ n) → E1.nParam H ≤ n := by
    intro n hn hsimp hP
    have h := nParam_le_of_star h1111 hn hTH hT2 hKc hHK hJs hsimp hP hTH
    rwa [sup_comm, hO2T] at h
  have hLie : ∀ n : ℕ, 1 ≤ n → TypeLie n ↥Ks → E1.nParam H ≤ n := by
    intro n hn hty
    refine hbound n hn hty.isSimpleGroup fun X _ _ _ hnabX ⟨e⟩ B hB hBI => ?_
    have hSQX : SQTKGroup X := sqtkGroup_of_mulEquiv e hSQK
    exact (nParam_sup_eq_of_typeLie h1114 hn hnabX hSQX (TypeLie.of_mulEquiv e hty) hB hBI).le
  have hOne : TypeOne ↥Ks → E1.nParam H = 1 := by
    intro hty
    refine le_antisymm ?_ hge1
    have h := hbound 1 le_rfl hty.isSimpleGroup fun X _ _ _ hnabX ⟨e⟩ B hB hBI => by
      have hSQX : SQTKGroup X := sqtkGroup_of_mulEquiv e hSQK
      simpa using nParam_sup_le_one (e114TypeOne_of_e114 h1114) hnabX hSQX
        (TypeOne.of_mulEquiv e hty) hB hBI
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
    obtain ⟨h1, -⟩ := h1114 (StarQuot M H) Ts hSQs hFs hqs hKT
    refine h1 n hn ?_
    rcases TypeLie.of_mulEquiv eF hty with h | h | h | h | h | ⟨hn1, h⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr ⟨hn1, h⟩)))))
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

theorem e22StatementC_of (hNoN : E22StatementNoN) (h1111 : ASInputs.AS_E_1_11)
    (h1114 : ASInputs.AS_E_1_14) : E22StatementC :=
  ⟨hNoN, e22NParamC_of h1111 h1114⟩

end CFSG.Quasithin.E2
