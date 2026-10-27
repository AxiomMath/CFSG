module

public import CFSG.Quasithin.EmptyFaithful.E22PA6

public section

namespace CFSG.Quasithin.E2.E22N

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Vol2.Ch11.SecB

@[expose] def TypeOneRes (Y : Type) [Group Y] : Prop :=
  IsPSL 3 2 1 Y ∨ IsAlt 6 Y ∨
    (∃ p e : ℕ, p.Prime ∧ 3 < p ∧ (e = 1 ∨ e = 2) ∧ (p ^ e % 8 = 1 ∨ p ^ e % 8 = 7) ∧
      IsPSL 2 p e Y) ∨
    ∃ (s : Bool) (p : ℕ), p.Prime ∧ p ≠ 2 ∧ (s = true → p % 4 = 3) ∧ (s = false → p % 4 = 1) ∧
      IsPSLEps3 s p 1 Y

theorem TypeOneRes.of_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y')
    (h : TypeOneRes Y') : TypeOneRes Y := by
  rcases h with h | h | ⟨p, f, hp, hp3, hf, hpf, h⟩ | ⟨s, p, hp, hp2, h4, h4', h⟩
  · exact Or.inl (CFSG.SectionRank.statedClassicalModel_of_mulEquiv e h)
  · obtain ⟨e'⟩ : Nonempty (Y' ≃* alternatingGroup (Fin 6)) := h
    exact Or.inr (Or.inl ⟨e.trans e'⟩)
  · exact Or.inr (Or.inr (Or.inl
      ⟨p, f, hp, hp3, hf, hpf, CFSG.SectionRank.statedClassicalModel_of_mulEquiv e h⟩))
  · refine Or.inr (Or.inr (Or.inr ⟨s, p, hp, hp2, h4, h4', ?_⟩))
    cases s with
    | true => exact CFSG.SectionRank.statedClassicalModel_of_mulEquiv e h
    | false => exact CFSG.SectionRank.statedClassicalModel_of_mulEquiv e h

theorem TypeOneRes.toTypeOne {Y : Type} [Group Y] (h : TypeOneRes Y) : TypeOne Y := by
  rcases h with h | h | ⟨p, f, hp, hp3, hf, hpf, h⟩ | ⟨s, p, hp, hp2, -, -, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · refine Or.inr (Or.inr (Or.inl ⟨p, f, hp, by omega, ?_, h⟩))
    have h2 := hp.two_le
    rcases hf with rfl | rfl
    · rw [pow_one] at hpf ⊢
      omega
    · nlinarith
  · exact Or.inr (Or.inr (Or.inr ⟨s, p, hp, hp2, h⟩))

@[expose] def E114OneRes : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Subgroup G), SQTKGroup G →
    IsSimpleGroup (ASInputs.FStar G) → quasithinIsSylowTwo T →
    CFSG.generalizedFitting G ⊔ T = ⊤ →
      TypeOneRes (ASInputs.FStar G) → E1.nParam (⊤ : Subgroup G) ≤ 1

theorem e114OneRes_of_e114One (h : E114One) : E114OneRes :=
  fun G _ _ T hSQ hFs hT hFT hty => h G T hSQ hFs hT hFT hty.toTypeOne

theorem nParam_sup_le_one_of_res (h114 : E114OneRes) {X : Type} [Group X] [Finite X]
    [IsSimpleGroup X] (hnab : ∃ a b : X, a * b ≠ b * a) (hSQ : SQTKGroup X)
    (hT : TypeOneRes X) {B : Subgroup (MulAut X)} (hB : IsPGroup 2 B)
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
  have hFT : TypeOneRes (ASInputs.FStar ↥Z) := TypeOneRes.of_mulEquiv e hT
  have key : E1.nParam (⊤ : Subgroup ↥Z) ≤ 1 :=
    h114 ↥Z (B.subgroupOf Z) hSQZ hFs (isSylowTwo_sup hB hBI)
      (generalizedFitting_sup_sup hnab B) hFT
  rw [E1.nParam_subgroupOf]
  exact key

theorem e22NParamW_of_res (h111 : E111ForQn (fun X _ => TypeOne X) 1) (h114 : E114OneRes) :
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
  have hOne : TypeOneRes ↥Ks → E1.nParam H = 1 := by
    intro hty
    refine le_antisymm ?_ hge1
    have h := nParam_le_of_star (Q := fun X _ => TypeOne X) typeOne_isoInv h111
      hTH hT2 hKc hHK hJs hty.toTypeOne.isSimpleGroup hty.toTypeOne
      (fun X _ _ _ hnabX ⟨e⟩ B hB hBI => by
        have hSQX : SQTKGroup X := sqtkGroup_of_mulEquiv e hSQK
        simpa using nParam_sup_le_one_of_res h114 hnabX hSQX (TypeOneRes.of_mulEquiv e hty) hB
          hBI)
      hTH
    rw [sup_comm, hO2T] at h
    simpa using h
  dsimp only [E2.E22NParamWCases]
  refine ⟨fun _ _ p hp hp8 hK _ _ => hOne ?_, fun hTK _ =>
    ⟨fun n hn1 hty _ _ hn => ?_, fun p e hp hp3 he hpe8 hK _ _ => hOne ?_,
      fun p hp hp2 hK _ => hOne ?_⟩⟩
  ·
    have h1 := hp.two_le
    exact Or.inr (Or.inr (Or.inl ⟨p, 1, hp, by omega, Or.inl rfl, by simpa using hp8, hK⟩))
  ·
    subst hn
    refine (hOne ?_).le
    rcases hty with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (by simpa [IsSp4Prime] using h))
  ·
    exact Or.inr (Or.inr (Or.inl ⟨p, e, hp, hp3, he, hpe8, hK⟩))
  ·
    rcases hK with ⟨h4, hK⟩ | ⟨h4, hK, -⟩
    · exact Or.inr (Or.inr (Or.inr ⟨false, p, hp, hp2, by simp, fun _ => h4, hK⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨true, p, hp, hp2, fun _ => h4, by simp, hK⟩))

@[expose] def TypeOneResNoA6 (Y : Type) [Group Y] : Prop :=
  IsPSL 3 2 1 Y ∨
    (∃ p e : ℕ, p.Prime ∧ 3 < p ∧ (e = 1 ∨ e = 2) ∧ (p ^ e % 8 = 1 ∨ p ^ e % 8 = 7) ∧
      IsPSL 2 p e Y) ∨
    ∃ (s : Bool) (p : ℕ), p.Prime ∧ p ≠ 2 ∧ (s = true → p % 4 = 3) ∧ (s = false → p % 4 = 1) ∧
      IsPSLEps3 s p 1 Y

@[expose] def E114OneResNoA6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Subgroup G), SQTKGroup G →
    IsSimpleGroup (ASInputs.FStar G) → quasithinIsSylowTwo T →
    CFSG.generalizedFitting G ⊔ T = ⊤ →
      TypeOneResNoA6 (ASInputs.FStar G) → E1.nParam (⊤ : Subgroup G) ≤ 1

theorem e114OneRes_of_noA6 (h : E114OneResNoA6) : E114OneRes := by
  intro G _ _ T hSQ hFs hT hFT hty
  rcases hty with h1 | h6 | h2 | h3
  · exact h G T hSQ hFs hT hFT (Or.inl h1)
  · exact nParam_le_one_of_alt6 h6
  · exact h G T hSQ hFs hT hFT (Or.inr (Or.inl h2))
  · exact h G T hSQ hFs hT hFT (Or.inr (Or.inr h3))

theorem e22NParamW_of_resNoA6
    (h111 : E111ForQn (fun X _ => TypeOne X) 1) (h114 : E114OneResNoA6) : E2.E22NParamW :=
  e22NParamW_of_res h111 (e114OneRes_of_noA6 h114)

end CFSG.Quasithin.E2.E22N
