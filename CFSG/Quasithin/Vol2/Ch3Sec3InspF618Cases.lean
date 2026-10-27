module

public import CFSG.Quasithin.Vol2.Ch3Sec3InspF618Tools
public import CFSG.Quasithin.EmptyFaithful.Gold14610F618StructCase3
public import CFSG.Quasithin.EmptyFaithful.Gold14610F618StructSym
public import CFSG.Quasithin.EmptyFaithful.Gold14610F618StructPGL
public import CFSG.Quasithin.EmptyFaithful.Gold14610F618StructFieldExt
public import CFSG.Quasithin.EmptyFaithful.Gold14610F618StructM12
public import Certificates.Kernel.J4Count.FixCE
public import CFSG.Quasithin.EmptyFaithful.S14610Top
public import CFSG.Quasithin.EmptyFaithful.S14610Q1
public import CFSG.Quasithin.EmptyFaithful.Gold14610F618StructSimple
public import CFSG.Quasithin.Background.C1PackS1531Top
public import CFSG.Quasithin.EmptyFaithful.S146R2
public import CFSG.Quasithin.EmptyFaithful.S146ThreeB
public import CFSG.Quasithin.EmptyFaithful.S146G4
public import CFSG.Quasithin.EmptyFaithful.S152Y15
public import CFSG.Quasithin.EmptyFaithful.T1531Final
public import CFSG.Quasithin.EmptyFaithful.S152Y19
public import CFSG.Quasithin.EmptyFaithful.S143Pre
public import Certificates.Kernel.J4Count.FixCPairBase1
public import CFSG.Quasithin.Background.A3Structure314Defs
public import CFSG.Quasithin.EmptyFaithful.S152UGen
public import CFSG.Quasithin.Vol2.Ch3Sec3InspF618
public import CFSG.Quasithin.Background.D2
public import CFSG.Quasithin.Background.D2Cyclic
public import CFSG.Quasithin.Background.E3
public import CFSG.Quasithin.EmptyFaithful.S14110
public import CFSG.Quasithin.Background.B216Quotient
public import CFSG.Quasithin.EmptyFaithful.S146R3
public import CFSG.ClassicalGroups
public import CFSG.Quasithin.Background.F9G2
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.Quasithin.Recognition.ModelBridges
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Lean.Data.Json
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Units
public import Mathlib.Data.Fintype.CardEmbedding
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Tactic.Abel

public section

namespace CFSG.Quasithin.F6.InspRest

open CFSG.QuasithinUnique CFSG.GorensteinWalter CFSG.Assembly.LowTwoRank
open scoped commutatorElement

@[expose] def TypeL2One (W : Type) [Group W] : Prop :=
  ∃ p : ℕ, p.Prime ∧ (p % 24 = 11 ∨ p % 24 = 13) ∧ IsL2 p 1 W

@[expose] def TypeSix (W : Type) [Group W] : Prop :=
  Nonempty (W ≃* ↥(alternatingGroup (Fin 6))) ∨
    ∃ p e : ℕ, p.Prime ∧ 1 ≤ e ∧ e ≤ 2 ∧ (p ^ e % 16 = 7 ∨ p ^ e % 16 = 9) ∧ IsL2 p e W

@[expose] def TypeSeven (W : Type) [Group W] : Prop :=
  Nonempty (W ≃* ↥(alternatingGroup (Fin 7)))

@[expose] def TypeEight (W : Type) [Group W] : Prop :=
  Nonempty (W ≃* ↥(alternatingGroup (Fin 6))) ∨
    ∃ p : ℕ, p.Prime ∧ (p % 8 = 3 ∨ p % 8 = 5) ∧ IsL2 p 2 W

@[expose] def TypeNine (W : Type) [Group W] : Prop :=
  Nonempty (W ≃* ↥(alternatingGroup (Fin 7))) ∨
    ∃ p : ℕ, p.Prime ∧ (p % 24 = 5 ∨ p % 24 = 19) ∧ IsL2 p 2 W

@[expose] def TypeTen (W : Type) [Group W] : Prop :=
  ∃ p : ℕ, (p % 8 = 3 ∨ p % 8 = 5) ∧ IsSLEps3 p W

section Iso

variable {A B : Type} [Group A] [Group B]

theorem isL2_of_mulEquiv (e : A ≃* B) {p f : ℕ} (h : IsL2 p f B) : IsL2 p f A :=
  CFSG.SectionRank.statedClassicalModel_of_mulEquiv e h

theorem isSLEps3_of_mulEquiv (e : A ≃* B) {p : ℕ} (h : IsSLEps3 p B) : IsSLEps3 p A := by
  obtain ⟨hp, K, _, _, hK⟩ := h
  refine ⟨hp, K, inferInstance, inferInstance, ?_⟩
  rcases hK with ⟨h1, h2, hf | hf⟩ | ⟨h1, h2, hf | hf⟩
  · obtain ⟨f⟩ := hf
    exact Or.inl ⟨h1, h2, Or.inl ⟨e.trans f⟩⟩
  · obtain ⟨f⟩ := hf
    exact Or.inl ⟨h1, h2, Or.inr ⟨e.trans f⟩⟩
  · obtain ⟨f⟩ := hf
    exact Or.inr ⟨h1, h2, Or.inl ⟨e.trans f⟩⟩
  · obtain ⟨f⟩ := hf
    exact Or.inr ⟨h1, h2, Or.inr ⟨e.trans f⟩⟩

theorem typeL2One_of_mulEquiv (e : A ≃* B) (h : TypeL2One B) : TypeL2One A := by
  obtain ⟨p, hp, hp24, hL⟩ := h
  exact ⟨p, hp, hp24, isL2_of_mulEquiv e hL⟩

theorem typeSix_of_mulEquiv (e : A ≃* B) (h : TypeSix B) : TypeSix A := by
  rcases h with hf | ⟨p, k, hp, hk1, hk2, h16, hL⟩
  · obtain ⟨f⟩ := hf
    exact Or.inl ⟨e.trans f⟩
  · exact Or.inr ⟨p, k, hp, hk1, hk2, h16, isL2_of_mulEquiv e hL⟩

theorem typeSeven_of_mulEquiv (e : A ≃* B) (h : TypeSeven B) : TypeSeven A := by
  obtain ⟨f⟩ := h
  exact ⟨e.trans f⟩

theorem typeEight_of_mulEquiv (e : A ≃* B) (h : TypeEight B) : TypeEight A := by
  rcases h with hf | ⟨p, hp, hp8, hL⟩
  · obtain ⟨f⟩ := hf
    exact Or.inl ⟨e.trans f⟩
  · exact Or.inr ⟨p, hp, hp8, isL2_of_mulEquiv e hL⟩

theorem typeNine_of_mulEquiv (e : A ≃* B) (h : TypeNine B) : TypeNine A := by
  rcases h with hf | ⟨p, hp, hp24, hL⟩
  · obtain ⟨f⟩ := hf
    exact Or.inl ⟨e.trans f⟩
  · exact Or.inr ⟨p, hp, hp24, isL2_of_mulEquiv e hL⟩

theorem typeTen_of_mulEquiv (e : A ≃* B) (h : TypeTen B) : TypeTen A := by
  obtain ⟨p, hp8, hS⟩ := h
  exact ⟨p, hp8, isSLEps3_of_mulEquiv e hS⟩

theorem isM12_of_mulEquiv (e : A ≃* B) (h : IsM12 B) : IsM12 A := by
  obtain ⟨f⟩ := h
  exact ⟨e.trans f⟩

end Iso

theorem isSimpleGroup_alt_seven : IsSimpleGroup ↥(alternatingGroup (Fin 7)) :=
  alternatingGroup.isSimpleGroup (by simp)

theorem exists_noncomm_alt_seven : ∃ a b : ↥(alternatingGroup (Fin 7)), a * b ≠ b * a := by
  have := isSimpleGroup_alt_seven
  refine CFSG.Quasithin.A314.exists_noncomm_of_simple this ?_
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  norm_num [Nat.factorial]

theorem exists_noncomm_m12 :
    ∃ a b : CFSG.Blueprint.NativeSporadic.M12, a * b ≠ b * a := by
  have hs := CFSG.Sporadic.Mathieu.fam_m12_simplicity.2.2
  have := CFSG.Sporadic.Mathieu.fam_m12_simplicity.1
  refine CFSG.Quasithin.A314.exists_noncomm_of_simple hs ?_
  rw [CFSG.Sporadic.Mathieu.card_M12]
  norm_num

variable {D : Type} [Group D]

theorem sqWitness_of_index_two_of_simple {P : ∀ (W : Type) [Group W], Prop}
    (hP : ∀ {A B : Type} [Group A] [Group B], (A ≃* B) → P B → P A) {N : Subgroup D} [N.Normal]
    (hidx : N.index = 2) [IsSimpleGroup ↥N] (hnc : ∃ a b : ↥N, a * b ≠ b * a) (hPN : P ↥N) :
    SqWitness D P :=
  sqWitness_of_index_two hidx (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc).1
    (hP (quotientCenterEquivOfSimple hnc) hPN)

variable {H₁ H₂ : Subgroup D}

theorem sqWitness_caseFour (h : IsF618CaseFour H₁ H₂) : SqWitness D TypeL2One := by
  obtain ⟨⟨p, hp, hp24, hL⟩, -⟩ := h
  have : IsSimpleGroup D := (CFSG.LieType.Simplicity.fam_PSL_simplicity D 2 p 1 hL).2
  exact sqWitness_top_of_simple typeL2One_of_mulEquiv
    (exists_noncomm_of_isL2 hp (by omega) le_rfl (by rw [pow_one]; omega) hL) ⟨p, hp, hp24, hL⟩

theorem sqWitness_caseFive (h : IsF618CaseFive H₁ H₂) : SqWitness D TypeL2One := by
  obtain ⟨⟨q, hq, hq24, K, _, _, hK, ⟨e⟩⟩, -⟩ := h
  refine SqWitness.of_mulEquiv typeL2One_of_mulEquiv (e.trans (Gold14610.Struct.pglEquiv K)) ?_
  have hodd : IsOddPrimePower (Nat.card K) :=
    ⟨q, 1, hq, by rw [Nat.odd_iff]; omega, le_rfl, by rw [hK, pow_one]⟩
  set Kb : Subgroup (PGL2 K) :=
    (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range with hKb
  have hidx : Kb.index = 2 := pgl2_psl2Range_index_eq_two K hodd
  have : Kb.Normal := Subgroup.normal_of_index_eq_two hidx
  have hL2 : IsL2 q 1 ↥Kb := by
    refine ⟨⟨hq, le_rfl, le_rfl, ?_, ?_⟩, K, inferInstance, inferInstance, by rw [hK, pow_one],
      ⟨(psl2EquivToPGLRange K).symm.trans
        (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K)⟩⟩
    · rw [pow_one]; intro h; simp at h; omega
    · rw [pow_one]; intro h; simp at h; omega
  have : IsSimpleGroup ↥Kb := (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 2 q 1 hL2).2
  exact sqWitness_of_index_two_of_simple typeL2One_of_mulEquiv hidx
    (exists_noncomm_of_isL2 hq (by omega) le_rfl (by rw [pow_one]; omega) hL2) ⟨q, hq, hq24, hL2⟩

theorem sqWitness_caseSix (h : IsF618CaseSix H₁ H₂) : SqWitness D TypeSix := by
  rcases h.1 with hA | ⟨p, e, hp, he1, he2, h16, hL⟩
  · exact sqWitness_top typeSix_of_mulEquiv (Gold14610.Struct.isQuasisimple_of_isHatAlt hA)
      (Or.inl hA.2.2)
  · have : IsSimpleGroup D := (CFSG.LieType.Simplicity.fam_PSL_simplicity D 2 p e hL).2
    have hp2 : p ≠ 2 := by
      rintro rfl
      rcases (show e = 1 ∨ e = 2 by omega) with rfl | rfl <;> norm_num at h16
    exact sqWitness_top_of_simple typeSix_of_mulEquiv
      (exists_noncomm_of_isL2 hp hp2 he1 (by omega) hL) (Or.inr ⟨p, e, hp, he1, he2, h16, hL⟩)

theorem sqWitness_caseSeven (h : IsF618CaseSeven H₁ H₂) : SqWitness D TypeSeven := by
  rcases h.1 with he | hA
  · obtain ⟨e⟩ := he
    have := isSimpleGroup_alt_seven
    have : IsSimpleGroup D := e.isSimpleGroup
    have hnc : ∃ a b : D, a * b ≠ b * a := by
      obtain ⟨a, b, hab⟩ := exists_noncomm_alt_seven
      exact ⟨e.symm a, e.symm b, fun hc => hab (by simpa using congrArg e hc)⟩
    exact sqWitness_top_of_simple typeSeven_of_mulEquiv hnc ⟨e⟩
  · exact sqWitness_top typeSeven_of_mulEquiv (Gold14610.Struct.isQuasisimple_of_isHatAlt hA)
      hA.2.2

theorem sqWitness_of_isHatSym {n : ℕ} {P : ∀ (W : Type) [Group W], Prop}
    (hPA : ∀ (W : Type) [Group W], Nonempty (W ≃* ↥(alternatingGroup (Fin n))) → P W)
    (h : IsHatSym n D) : SqWitness D P := by
  obtain ⟨φ, -, -, hA⟩ := h
  refine ⟨(alternatingGroup (Fin n)).comap φ, inferInstance, fun x => ?_,
    Gold14610.Struct.isQuasisimple_of_isHatAlt hA, hPA _ hA.2.2⟩
  rw [Subgroup.mem_comap, map_pow]
  exact Gold14610.Struct.sq_mem_alternatingGroup _

theorem sqWitness_of_isL2FieldExtCat {p : ℕ} (hp8 : p % 8 = 3 ∨ p % 8 = 5)
    {P : ∀ (W : Type) [Group W], Prop}
    (hP : ∀ {A B : Type} [Group A] [Group B], (A ≃* B) → P B → P A)
    (hPL : ∀ (W : Type) [Group W], IsL2 p 2 W → P W) (h : IsL2FieldExtCat p D) :
    SqWitness D P := by
  obtain ⟨hp, K, _, _, hK, ⟨e⟩⟩ := h
  refine SqWitness.of_mulEquiv hP e ?_
  have hpodd : Odd p := by rw [Nat.odd_iff]; omega
  have hp3 : 3 ≤ p := by omega
  have hodd : IsOddPrimePower (Nat.card K) := ⟨p, 2, hp, hpodd, by norm_num, hK⟩
  have hK3 : 3 < Nat.card K := by rw [hK]; nlinarith
  have hLn : (pGammaL2PSLRange K).Normal := pGammaL2PSLRange_normal K hodd hK3
  have hLS : pGammaL2PSLRange K ≤ PSigmaL2 K := le_sup_left
  have hσ2 : ∀ σ : K ≃+* K, σ ^ 2 = 1 := fun σ => by
    have := CFSG.Semidihedral.SemilinearOuterQuotient.fieldAut_card K hp hK
    rw [← this]
    exact pow_card_eq_one'
  set M : Subgroup ↥(PSigmaL2 K) := (pGammaL2PSLRange K).subgroupOf (PSigmaL2 K) with hM
  have hL2 : IsL2 p 2 ↥M := by
    refine ⟨⟨hp, by norm_num, le_rfl, ?_, ?_⟩, K, inferInstance, inferInstance, hK,
      ⟨(Subgroup.subgroupOfEquivOfLe hLS).trans ((pGammaL2PSLRangeEquiv K).symm.trans
        (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K))⟩⟩
    · intro h; simp at h; nlinarith
    · intro h; simp at h; nlinarith
  have : IsSimpleGroup ↥M := (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 2 p 2 hL2).2
  have hnc := exists_noncomm_of_isL2 hp (by omega) (by norm_num) (by nlinarith) hL2
  refine ⟨M, inferInstance, fun x => ?_, (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc).1,
    hP (quotientCenterEquivOfSimple hnc) (hPL _ hL2)⟩
  rw [hM, Subgroup.mem_subgroupOf, Subgroup.coe_pow]
  obtain ⟨n, hn, r, hr, hnr⟩ := Subgroup.mem_sup_of_normal_left.1 x.2
  obtain ⟨σ, rfl⟩ := hr
  rw [← hnr]
  have hr2 : (SemidirectProduct.inr σ : PGammaL2 K) * SemidirectProduct.inr σ = 1 := by
    rw [← map_mul, ← sq, hσ2, map_one]
  have e2 : (n * SemidirectProduct.inr σ) * (n * SemidirectProduct.inr σ) =
      n * (SemidirectProduct.inr σ * n * (SemidirectProduct.inr σ)⁻¹) *
        ((SemidirectProduct.inr σ : PGammaL2 K) * SemidirectProduct.inr σ) := by group
  rw [sq, e2, hr2, mul_one]
  exact Subgroup.mul_mem _ hn (hLn.conj_mem n hn _)

theorem sqWitness_caseEight (h : IsF618CaseEightCat H₁ H₂) : SqWitness D TypeEight := by
  rcases h.1 with hS | ⟨p, hp, hp8, hF⟩
  · exact sqWitness_of_isHatSym (fun _ _ hA => Or.inl hA) hS
  · exact sqWitness_of_isL2FieldExtCat hp8 typeEight_of_mulEquiv
      (fun _ _ hL => Or.inr ⟨p, hp, hp8, hL⟩) hF

theorem sqWitness_caseNine (h : IsF618CaseNineCat H₁ H₂) : SqWitness D TypeNine := by
  rcases h.1 with he | hS | ⟨p, hp, hp24, hF⟩
  · obtain ⟨e⟩ := he
    refine SqWitness.of_mulEquiv typeNine_of_mulEquiv e ?_
    have := isSimpleGroup_alt_seven
    have hnc := exists_noncomm_alt_seven
    exact ⟨alternatingGroup (Fin 7), inferInstance,
      fun x => Gold14610.Struct.sq_mem_alternatingGroup x,
      (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc).1,
      typeNine_of_mulEquiv (quotientCenterEquivOfSimple hnc) (Or.inl ⟨MulEquiv.refl _⟩)⟩
  · exact sqWitness_of_isHatSym (fun _ _ hA => Or.inl hA) hS
  · exact sqWitness_of_isL2FieldExtCat (by omega) typeNine_of_mulEquiv
      (fun _ _ hL => Or.inr ⟨p, hp, hp24, hL⟩) hF

theorem sqWitness_caseTen (h : IsF618CaseTen H₁ H₂) : SqWitness D TypeTen := by
  obtain ⟨⟨p, hp8, hS⟩, -⟩ := h
  obtain ⟨hq, hS'⟩ := isQuasisimple_and_isSLEps3 (by omega) hS
  exact sqWitness_top typeTen_of_mulEquiv hq ⟨p, hp8, hS'⟩

theorem sqWitness_caseEleven (h : IsF618CaseEleven H₁ H₂) : SqWitness D TypeTen := by
  obtain ⟨⟨p, hp8, hS⟩, -⟩ := h
  obtain ⟨Kq, hidx, hKq⟩ := Gold14610.Struct.exists_index_two_sub_isSLEps3 hS
  have : Kq.Normal := Subgroup.normal_of_index_eq_two hidx
  obtain ⟨hq, hS'⟩ := isQuasisimple_and_isSLEps3 (by omega) hKq
  exact sqWitness_of_index_two hidx hq ⟨p, hp8, hS'⟩

theorem sqWitness_caseTwelve (h : IsF618CaseTwelve H₁ H₂) :
    SqWitness D IsM12 := by
  obtain ⟨⟨e⟩, -⟩ := h
  have := CFSG.Sporadic.Mathieu.fam_m12_simplicity.2.2
  have : IsSimpleGroup D := e.isSimpleGroup
  have hnc : ∃ a b : D, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := exists_noncomm_m12
    exact ⟨e.symm a, e.symm b, fun hc => hab (by simpa using congrArg e hc)⟩
  exact sqWitness_top_of_simple isM12_of_mulEquiv hnc ⟨e⟩

theorem sqWitness_caseThirteen
    (h : IsF618CaseThirteen H₁ H₂) : SqWitness D IsM12 := by
  obtain ⟨⟨e⟩, -⟩ := h
  refine SqWitness.of_mulEquiv isM12_of_mulEquiv e ?_
  have := CFSG.Sporadic.Mathieu.fam_m12_simplicity.2.2
  have hinj : Function.Injective (MulAut.conj :
      CFSG.Blueprint.NativeSporadic.M12 →* MulAut CFSG.Blueprint.NativeSporadic.M12) :=
    Gold14610.Struct.conjHom_injective_of_center_eq_bot
      CFSG.ComponentClassification.M12Cover.m12_center
  let eI : CFSG.Blueprint.NativeSporadic.M12 ≃*
      ↥(CFSG.ComponentClassification.OuterAutomorphisms.inner
        CFSG.Blueprint.NativeSporadic.M12) :=
    MonoidHom.ofInjective hinj
  have hidx : (CFSG.ComponentClassification.OuterAutomorphisms.inner
      CFSG.Blueprint.NativeSporadic.M12).index = 2 :=
    CFSG.ComponentClassification.M12Cover.card_outer
  have : (CFSG.ComponentClassification.OuterAutomorphisms.inner
      CFSG.Blueprint.NativeSporadic.M12).Normal := Subgroup.normal_of_index_eq_two hidx
  have : IsSimpleGroup ↥(CFSG.ComponentClassification.OuterAutomorphisms.inner
      CFSG.Blueprint.NativeSporadic.M12) := eI.symm.isSimpleGroup
  have hnc : ∃ a b : ↥(CFSG.ComponentClassification.OuterAutomorphisms.inner
      CFSG.Blueprint.NativeSporadic.M12), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := exists_noncomm_m12
    exact ⟨eI a, eI b, fun hc => hab (by simpa using congrArg eI.symm hc)⟩
  exact sqWitness_of_index_two_of_simple isM12_of_mulEquiv hidx hnc ⟨eI.symm⟩

variable [Finite D]

omit [Finite D] in
theorem commutator_sup_le {K Z : Subgroup D} (hcomm : ∀ k ∈ K, ∀ z ∈ Z, k * z = z * k)
    (hZ : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a) : ⁅K ⊔ Z, K ⊔ Z⁆ ≤ K := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  obtain ⟨k₁, hk₁, z₁, hz₁, rfl⟩ := Gold14610.Struct.exists_mul_of_mem_sup_of_comm hcomm hx
  obtain ⟨k₂, hk₂, z₂, hz₂, rfl⟩ := Gold14610.Struct.exists_mul_of_mem_sup_of_comm hcomm hy
  have h1 : z₁ * k₂ = k₂ * z₁ := (hcomm k₂ hk₂ z₁ hz₁).symm
  have h2 : z₁ * z₂ = z₂ * z₁ := hZ z₁ hz₁ z₂ hz₂
  have h3 : z₂ * k₁⁻¹ = k₁⁻¹ * z₂ := (hcomm k₁⁻¹ (K.inv_mem hk₁) z₂ hz₂).symm
  have e : ⁅k₁ * z₁, k₂ * z₂⁆ = ⁅k₁, k₂⁆ := by
    rw [commutatorElement_def, commutatorElement_def]
    calc k₁ * z₁ * (k₂ * z₂) * (k₁ * z₁)⁻¹ * (k₂ * z₂)⁻¹
        = k₁ * (z₁ * k₂) * z₂ * z₁⁻¹ * k₁⁻¹ * z₂⁻¹ * k₂⁻¹ := by group
      _ = k₁ * k₂ * (z₁ * z₂) * z₁⁻¹ * k₁⁻¹ * z₂⁻¹ * k₂⁻¹ := by rw [h1]; group
      _ = k₁ * k₂ * (z₂ * k₁⁻¹) * z₂⁻¹ * k₂⁻¹ := by rw [h2]; group
      _ = k₁ * k₂ * k₁⁻¹ * k₂⁻¹ := by rw [h3]; group
  rw [e, commutatorElement_def]
  exact K.mul_mem (K.mul_mem (K.mul_mem hk₁ hk₂) (K.inv_mem hk₁)) (K.inv_mem hk₂)

theorem spec_caseThree (h : IsF618CaseThree H₁ H₂) :
    CFSG.IsQuasisimple ↥(perfectCore (⊤ : Subgroup D)) ∧
      TypeL2One (↥(perfectCore (⊤ : Subgroup D)) ⧸
        Subgroup.center ↥(perfectCore (⊤ : Subgroup D))) := by
  obtain ⟨p, K, Z, hp, hp24, hL, hZ3, hKZ, -, hcomm, -⟩ := h
  set L := twoResidual (⊤ : Subgroup D) with hLdef
  have hLn : L.Normal :=
    Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp (le_normalizer_twoResidual ⊤))
  have h2 : IsPGroup 2 (D ⧸ L) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H x =>
      obtain ⟨k, hk⟩ := twoResidual_isTwoQuotient (⊤ : Subgroup D) x trivial
      exact ⟨k, by rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]; exact hk⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent (D ⧸ L) := h2.isNilpotent
  have hZc : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have : IsCyclic ↥Z := isCyclic_of_prime_card hZ3
    intro a ha b hb
    exact congrArg Subtype.val ((IsCyclic.commGroup (α := ↥Z)).mul_comm ⟨a, ha⟩ ⟨b, hb⟩)
  have : IsSimpleGroup ↥K := (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 2 p 1 hL).2
  have hnc := exists_noncomm_of_isL2 hp (by omega) le_rfl (by rw [pow_one]; omega) hL
  have hq := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc).1
  have hKp : ⁅K, K⁆ = K := commutator_eq_self_of_isQuasisimple hq
  have hKL : K ≤ L := hKZ ▸ le_sup_left
  have hcore : perfectCore (⊤ : Subgroup D) = K := by
    have h1 : perfectCore (⊤ : Subgroup D) ≤ perfectCore L :=
      le_perfectCore_of_perfect (perfectCore_top_le_of_isSolvable L) (perfectCore_perfect _)
    have h2 : perfectCore L ≤ K := by
      refine (le_perfectCore_of_perfect ?_ (perfectCore_perfect L)).trans
        (perfectCore_eq_self_of_perfect hKp).le
      calc perfectCore L = ⁅perfectCore L, perfectCore L⁆ := (perfectCore_perfect L).symm
        _ ≤ ⁅L, L⁆ := Subgroup.commutator_mono (perfectCore_le L) (perfectCore_le L)
        _ ≤ K := by rw [← hKZ]; exact commutator_sup_le hcomm hZc
    exact le_antisymm (h1.trans h2) (le_perfectCore_of_perfect le_top hKp)
  let e : ↥(perfectCore (⊤ : Subgroup D)) ≃* ↥K := MulEquiv.subgroupCongr hcore
  exact ⟨isQuasisimple_of_mulEquiv e hq, typeL2One_of_mulEquiv
    ((centralQuotientCongr e).trans (quotientCenterEquivOfSimple hnc)) ⟨p, hp, hp24, hL⟩⟩

end CFSG.Quasithin.F6.InspRest
