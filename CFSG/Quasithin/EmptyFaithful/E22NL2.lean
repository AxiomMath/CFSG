module

public import CFSG.Quasithin.EmptyFaithful.E111RFacts
public import CFSG.Quasithin.EmptyFaithful.E22QRes
public import CFSG.Quasithin.Vol2.Ch11SecU1E22R
public import CFSG.Quasithin.Vol2.Ch11SecU1Wire
public import CFSG.Quasithin.EmptyFaithful.E111RMain
public import CFSG.Quasithin.Vol2.Ch11SecBNPMainS
public import CFSG.Quasithin.Vol2.Ch11SecU1Cases

public section

namespace CFSG.Quasithin.E2.E22N

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Vol2.Ch11.SecB

theorem e22NParamC_ofRL2 (hL2 : E111CoreMultiL2) (h114 : Vol2.Ch11.SecE3.E114ForE22R) :
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
  have hLieP : ∀ n : ℕ, 1 ≤ n → TypeLie n ↥Ks → ∀ (X : Type) [Group X] [Finite X]
      [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) → Nonempty (X ≃* ↥Ks) →
      ∀ B : Subgroup (MulAut X), IsPGroup 2 B →
      IsSylowIn 2 (B ⊓ (MulAut.conj : X →* MulAut X).range) (MulAut.conj : X →* MulAut X).range →
      E1.nParam ((MulAut.conj : X →* MulAut X).range ⊔ B) ≤ n :=
    fun n hn hty X _ _ _ hnabX ⟨e⟩ B hB hBI =>
      (nParam_sup_eq_of_typeLieR h114 hn hnabX (sqtkGroup_of_mulEquiv e hSQK)
        (TypeLie.of_mulEquiv e hty) hB hBI).le
  have hOneP : TypeOneRes ↥Ks → ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X],
      (∃ a b : X, a * b ≠ b * a) → Nonempty (X ≃* ↥Ks) →
      ∀ B : Subgroup (MulAut X), IsPGroup 2 B →
      IsSylowIn 2 (B ⊓ (MulAut.conj : X →* MulAut X).range) (MulAut.conj : X →* MulAut X).range →
      E1.nParam ((MulAut.conj : X →* MulAut X).range ⊔ B) ≤ ((1 : ℕ) : ℕ∞) :=
    fun hty X _ _ _ hnabX ⟨e⟩ B hB hBI => by
      simpa using nParam_sup_le_one_of_res (e114OneRes_of_e114ForE22R h114) hnabX
        (sqtkGroup_of_mulEquiv e hSQK) (TypeOneRes.of_mulEquiv e hty) hB hBI
  have hboundN : T ≤ Subgroup.normalizer (K : Set Γ) → ∀ n : ℕ, 1 ≤ n → IsSimpleGroup ↥Ks →
      TypeK ↥Ks → (∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X],
        (∃ a b : X, a * b ≠ b * a) → Nonempty (X ≃* ↥Ks) → ∀ B : Subgroup (MulAut X),
        IsPGroup 2 B → IsSylowIn 2 (B ⊓ (MulAut.conj : X →* MulAut X).range)
          (MulAut.conj : X →* MulAut X).range →
        E1.nParam ((MulAut.conj : X →* MulAut X).range ⊔ B) ≤ n) → E1.nParam H ≤ n := by
    intro hTK n hn hsimp hKK hP
    have h := nParam_le_of_starC (Q := TypeK) (C := SolvSimpSolv) typeK_isoInv
      (fun Y _ _ hH hK hC => e111ForQnC_sss typeK_isoInv hn Y hH hK hC)
      hTH hT2 hKc hHK hJs hsimp hKK hP hTH
      (solvSimpSolv_of_star hTH hT2 hKc hHK hTK hJs hsimp hTH)
    rwa [sup_comm, hO2T] at h
  have hbound1a : ∀ n : ℕ, 1 ≤ n → IsSimpleGroup ↥Ks → AutRankLe n ↥Ks →
      (∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X],
        (∃ a b : X, a * b ≠ b * a) → Nonempty (X ≃* ↥Ks) → ∀ B : Subgroup (MulAut X),
        IsPGroup 2 B → IsSylowIn 2 (B ⊓ (MulAut.conj : X →* MulAut X).range)
          (MulAut.conj : X →* MulAut X).range →
        E1.nParam ((MulAut.conj : X →* MulAut X).range ⊔ B) ≤ n) → E1.nParam H ≤ n := by
    intro n hn hsimp hKK hP
    have h := nParam_le_of_star (autRankLe_isoInv n) (e111ForQn_autRankLe hn)
      hTH hT2 hKc hHK hJs hsimp hKK hP hTH
    rwa [sup_comm, hO2T] at h
  have hbound1b : ∀ p : ℕ, p.Prime → (p % 8 = 1 ∨ p % 8 = 7) → IsPSL 2 p 1 ↥Ks →
      TypeOneRes ↥Ks → E1.nParam H = 1 := by
    intro p hp hp8 hK hty
    refine le_antisymm ?_ hge1
    have h := nParam_le_of_star (Q := fun X _ => IsPSL 2 p 1 X) (isoInv_isPSL_two p)
      (e111ForQn_of_core (isoInv_isPSL_two p) le_rfl (hL2 p hp hp8))
      hTH hT2 hKc hHK hJs hty.toTypeOne.isSimpleGroup hK (hOneP hty) hTH
    rw [sup_comm, hO2T] at h
    exact_mod_cast h
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
  refine ⟨fun _ _ => ⟨fun n hn2 hty _ => ?_, fun p hp hp8 hK _ _ => ?_⟩,
    fun hTK _ => ⟨fun n hBen _ => ?_, fun n hn1 hty _ _ => ?_,
      fun p e hp hp3 he hpe8 hK _ _ => ?_, fun p hp hp2 hK _ => ?_⟩⟩
  ·
    have hT' : TypeLie n ↥Ks := by
      rcases hty with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    have hsimp := hT'.isSimpleGroup
    have hKK : AutRankLe n ↥Ks := by
      rcases hty with h | h
      · exact autRankLe_of_isPSL22 (hnab hsimp) h
      · exact autRankLe_of_isSz (hnab hsimp) h
    exact hbound1a n (by omega) hsimp hKK (hLieP n (by omega) hT')
  ·
    have h2 := hp.two_le
    exact hbound1b p hp hp8 hK
      (Or.inr (Or.inr (Or.inl ⟨p, 1, hp, by omega, Or.inl rfl, by simpa using hp8, hK⟩)))
  ·
    have hT' : TypeLie n ↥Ks := by
      rcases hBen.2 with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
    have hn : 1 ≤ n := by have := hBen.1; omega
    exact ⟨hboundN hTK n hn hT'.isSimpleGroup (Or.inl ⟨n, hT'⟩) (hLieP n hn hT'),
      hStar hTK n hn hT'⟩
  ·
    have hT' : TypeLie n ↥Ks := by
      rcases hty with h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · rw [IsSp4Prime] at h
        split_ifs at h with h1
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h1, h⟩))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    exact ⟨hboundN hTK n hn1 hT'.isSimpleGroup (Or.inl ⟨n, hT'⟩) (hLieP n hn1 hT'),
      hStar hTK n hn1 hT'⟩
  ·
    have hty : TypeOneRes ↥Ks := Or.inr (Or.inr (Or.inl ⟨p, e, hp, hp3, he, hpe8, hK⟩))
    refine le_antisymm ?_ hge1
    have h := hboundN hTK 1 le_rfl hty.toTypeOne.isSimpleGroup (Or.inr hty.toTypeOne)
      (hOneP hty)
    exact_mod_cast h
  ·
    have hty : TypeOneRes ↥Ks := by
      rcases hK with ⟨h4, hK⟩ | ⟨h4, hK, -⟩
      · exact Or.inr (Or.inr (Or.inr ⟨false, p, hp, hp2, by simp, fun _ => h4, hK⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨true, p, hp, hp2, fun _ => h4, by simp, hK⟩))
    refine le_antisymm ?_ hge1
    have h := hboundN hTK 1 le_rfl hty.toTypeOne.isSimpleGroup (Or.inr hty.toTypeOne)
      (hOneP hty)
    exact_mod_cast h

theorem e22StatementC_ofRL2 (hNoN : E22StatementNoN) (hL2 : E111CoreMultiL2)
    (h114 : Vol2.Ch11.SecE3.E114ForE22R) : E22StatementC :=
  ⟨hNoN, e22NParamC_ofRL2 hL2 h114⟩

theorem nParam_le_one_of_noLieL2 (hL2 : E111CoreMultiL2) (h1114 : E114OneRes)
    {G : Type} [Group G] [Finite G] {H T M K R : Subgroup G} (hTH : T ≤ H) (hT2 : IsPGroup 2 T)
    (hKc : K ∈ cComp H) (hHK : H = K ⊔ T) (hcases : E2.E22CasesNoN H T M K)
    (hlie : ¬ E2.E22LieCases H T M K) (hSQs : SQTKGroup (E2.StarQuot M H)) (hRH : R ≤ H) :
    E1.nParam (R ⊔ oTwoUpper H) ≤ 1 := by
  have hTy := (typeOneRes_or_lieCases hcases).resolve_right hlie
  have hJs := isSolvable_kerIn_of_e22CasesNoN hcases
  have hSQK : SQTKGroup ↥(E2.star M H K) := sqtkGroup_subgroup hSQs _
  have hsimp := hTy.toTypeOne.isSimpleGroup
  have hP : ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X],
      (∃ a b : X, a * b ≠ b * a) → Nonempty (X ≃* ↥(E2.star M H K)) →
      ∀ B : Subgroup (MulAut X), IsPGroup 2 B →
      IsSylowIn 2 (B ⊓ (MulAut.conj : X →* MulAut X).range) (MulAut.conj : X →* MulAut X).range →
      E1.nParam ((MulAut.conj : X →* MulAut X).range ⊔ B) ≤ ((1 : ℕ) : ℕ∞) :=
    fun X _ _ _ hnabX ⟨e⟩ B hB hBI => by
      simpa using nParam_sup_le_one_of_res h1114 hnabX (sqtkGroup_of_mulEquiv e hSQK)
        (TypeOneRes.of_mulEquiv e hTy) hB hBI
  by_cases hTK : T ≤ Subgroup.normalizer (K : Set G)
  · have h := nParam_le_of_starC (Q := fun X _ => TypeOne X) (C := SolvSimpSolv) typeOne_isoInv
      (fun Y _ _ hH hK hC => e111ForQnC_sss typeOne_isoInv le_rfl Y hH hK hC)
      hTH hT2 hKc hHK hJs hsimp hTy.toTypeOne hP hRH
      (solvSimpSolv_of_star hTH hT2 hKc hHK hTK hJs hsimp hRH)
    exact_mod_cast h
  · obtain ⟨p, hp, hp8, hKp⟩ : ∃ p : ℕ, p.Prime ∧ (p % 8 = 1 ∨ p % 8 = 7) ∧
        IsPSL 2 p 1 ↥(E2.star M H K) := by
      have hc := hcases
      dsimp only [E2.E22CasesNoN] at hc
      rcases hc with ⟨hJ, t, ht, hne, hM, ⟨n, hn2, hty, hB⟩ | ⟨p, hp, hp8, hK, -, -⟩⟩ |
          ⟨hTK', -⟩
      · exact absurd (Or.inl ⟨hJ, t, ht, hne, hM, n, hn2, hty, hB⟩) hlie
      · exact ⟨p, hp, hp8, hK⟩
      · exact absurd hTK' hTK
    have h := nParam_le_of_star (Q := fun X _ => IsPSL 2 p 1 X) (isoInv_isPSL_two p)
      (e111ForQn_of_core (isoInv_isPSL_two p) le_rfl (hL2 p hp hp8))
      hTH hT2 hKc hHK hJs hsimp hKp hP hRH
    exact_mod_cast h

theorem asP778NParamS_ofResL2 (hL2 : E111CoreMultiL2) (h1114 : E114OneRes)
    (hE22 : E2.E22StatementNoN) : AS_p778_nParamS :=
  asP778NParamS_of_bound hE22 fun _ _ _ _ _ _ _ _ hTH hT2 hKc hHK hcases hlie hSQs hRH =>
    nParam_le_one_of_noLieL2 hL2 h1114 hTH hT2 hKc hHK hcases hlie hSQs hRH

theorem asP778NParamS_ofRestL2
    (hL2 : E111CoreMultiL2)
    (h1114 : E114OneResRest) (hE22 : E2.E22StatementNoN) : AS_p778_nParamS :=
  asP778NParamS_ofResL2 hL2 (e114OneRes_of_rest h1114) hE22

end CFSG.Quasithin.E2.E22N
