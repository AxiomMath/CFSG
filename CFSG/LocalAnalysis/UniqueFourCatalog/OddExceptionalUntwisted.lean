module

public import CFSG.Yardstones.Mf4cdcdf2e013.Definitions
public import CFSG.LocalAnalysis.RankThreeEvenClassification.InvolutionLocal
public import CFSG.RankThree.PartTwo.Census.Criteria
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QX7S

public section

namespace CFSG.LocalAnalysis.UniqueFourCatalog

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Open
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4)
open CFSG.LieType.Steinberg.Adjoint CFSG.LieType.HighestRoot
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


theorem ringChar_ne_two_of_odd_card_untwisted (K : Type) [Field K] [Finite K]
    (hodd : Odd (Nat.card K)) : ringChar K ≠ 2 := by
  let _ : Fintype K := Fintype.ofFinite K
  intro h2
  have heven : Fintype.card K % 2 = 0 :=
    (FiniteField.even_card_iff_char_two (F := K)).mp h2
  have hodd' : Odd (Fintype.card K) := by
    simpa [Nat.card_eq_fintype_card] using hodd
  exact hodd'.not_two_dvd_nat (Nat.dvd_of_mod_eq_zero heven)

theorem isComponentOf_top_map_equiv {H N : Type} [Group H] [Group N] (e : H ≃* N)
    {S : Subgroup H} (hS : IsComponentOf S ⊤) : IsComponentOf (S.map e.toMonoidHom) ⊤ := by
  have htop : (⊤ : Subgroup H).map e.toMonoidHom = ⊤ := by
    ext x
    constructor
    · intro _
      exact Subgroup.mem_top x
    · intro _
      exact ⟨e.symm x, Subgroup.mem_top _, e.apply_symm_apply x⟩
  refine ⟨le_top, ?_,
    CFSG.ComponentClassification.Components.quasisimple_of_equiv
      (S.equivMapOfInjective e.toMonoidHom e.injective).symm hS.2.2⟩
  have hrel := CFSG.ComponentClassification.Components.chain_map e.toMonoidHom hS.2.1
  rwa [htop] at hrel

theorem hasInvolutionComponent_of_open_component {G : Type} [Group G] (t : G) (ht1 : t ≠ 1)
    (ht2 : t ^ 2 = 1) (L : Subgroup ↥(Subgroup.centralizer ({t} : Set G)))
    (hL : IsComponentOf L ⊤) : HasInvolutionComponent G := by
  refine ⟨t, L.map (Subgroup.centralizer ({t} : Set G)).subtype, ht1, ht2, ?_⟩
  refine ⟨Subgroup.map_subtype_le L, ?_,
    CFSG.ComponentClassification.Components.quasisimple_of_equiv
      (L.equivMapOfInjective (Subgroup.centralizer ({t} : Set G)).subtype
        (Subgroup.centralizer ({t} : Set G)).subtype_injective).symm hL.2.2⟩
  have hrel := CFSG.ComponentClassification.Components.chain_map
    (Subgroup.centralizer ({t} : Set G)).subtype hL.2.1
  have htopMap : (⊤ : Subgroup ↥(Subgroup.centralizer ({t} : Set G))).map
      (Subgroup.centralizer ({t} : Set G)).subtype = Subgroup.centralizer ({t} : Set G) := by
    ext element
    constructor
    · rintro ⟨member, _, rfl⟩
      exact member.property
    · intro hmem
      exact ⟨⟨element, hmem⟩, Subgroup.mem_top _, rfl⟩
  rwa [htopMap] at hrel

theorem mem_kernelRoots_signTuple_single {τ : Tag} {K : Type} [Field K] (hK2 : ringChar K ≠ 2)
    (i j : Fin τ.rank) (hj : Even (τ.cartan i j)) :
    (Pi.single j 1 : Fin τ.rank → ℤ) ∈
      kernelRoots (maskChar (signTupleBits (signTuple τ K i))) := by
  rw [← rootCharKernel_eq_kernelRoots hK2 (signTuple_eq_one_or_eq_neg_one i)]
  refine (mem_rootCharKernel_signTuple hK2 i _).2 ⟨isRoot_single τ j, ?_⟩
  simpa [Pi.single_apply, mul_ite] using hj

theorem two_lt_ncard_signClass {τ : Tag} {K : Type} [Field K] (i : Fin τ.rank) {j k : Fin τ.rank}
    (hα : (Pi.single j 1 : Fin τ.rank → ℤ) ∈
      kernelRoots (maskChar (signTupleBits (signTuple τ K i))))
    (hε : (Pi.single k 1 : Fin τ.rank → ℤ) ∈
      kernelRoots (maskChar (signTupleBits (signTuple τ K i))))
    (hjk : j ≠ k) (hiform : iform (Pi.single k 1 : Fin τ.rank → ℤ) (Pi.single j 1) ≠ 0) :
    2 < (componentRoots (maskChar (signTupleBits (signTuple τ K i)))
      (⟦⟨Pi.single j 1, hα⟩⟧ :
        KernelComponent (maskChar (signTupleBits (signTuple τ K i))))).ncard := by
  have hroot : IsRoot τ (Pi.single j 1 : Fin τ.rank → ℤ) := isRoot_single τ j
  have hnα : -(Pi.single j 1 : Fin τ.rank → ℤ) ∈
      kernelRoots (maskChar (signTupleBits (signTuple τ K i))) :=
    ⟨IsRoot.neg hroot, chi_neg hα.2⟩
  have hfin : (componentRoots (maskChar (signTupleBits (signTuple τ K i)))
      (⟦⟨Pi.single j 1, hα⟩⟧ :
        KernelComponent (maskChar (signTupleBits (signTuple τ K i))))).Finite :=
    (finite_setOf_isRoot τ).subset fun β ⟨h, _⟩ => h.1
  have hne2 : (Pi.single k 1 : Fin τ.rank → ℤ) ≠ Pi.single j 1 := by
    intro h
    have := congrFun h k
    simp [Pi.single_apply, hjk.symm] at this
  have hne3 : (Pi.single k 1 : Fin τ.rank → ℤ) ≠ -Pi.single j 1 := by
    intro h
    have := congrFun h k
    simp [Pi.single_apply, hjk.symm] at this
  exact (Set.two_lt_ncard_iff hfin).2 ⟨Pi.single j 1, -Pi.single j 1, Pi.single k 1,
    ⟨hα, rfl⟩, ⟨hnα, mk_eq_of_iform_ne_zero (iform_neg_self_ne_zero hroot)⟩,
    ⟨hε, mk_eq_of_iform_ne_zero hiform⟩, ne_neg_of_isRoot hroot, Ne.symm hne2, Ne.symm hne3⟩

theorem map_centralizer_involution_eq {τ : Tag} {K : Type} [Field K] {c : Fin τ.rank → Kˣ}
    (hdA : rootDiagUnit τ c ∈ adjointGroup τ K) :
    (Subgroup.centralizer ({(⟨rootDiagUnit τ c, hdA⟩ : adjointGroup τ K)} :
      Set (adjointGroup τ K))).map (adjointGroup τ K).subtype = toralCentralizer τ K c := by
  ext x
  constructor
  · rintro ⟨g, hg, rfl⟩
    rw [toralCentralizer, Subgroup.mem_inf]
    refine ⟨g.2, ?_⟩
    have hgC := congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hg)
    exact Subgroup.mem_centralizer_singleton_iff.2 hgC
  · intro hx
    rw [toralCentralizer, Subgroup.mem_inf] at hx
    have hxC := Subgroup.mem_centralizer_singleton_iff.1 hx.2
    exact ⟨⟨x, hx.1⟩, Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext hxC), rfl⟩

theorem hasInvolutionComponent_of_toral {τ : Tag} {K : Type} [Field K] {c : Fin τ.rank → Kˣ}
    (hc : ∀ l, c l = 1 ∨ c l = -1) (hK2 : ringChar K ≠ 2)
    (hdA : rootDiagUnit τ c ∈ adjointGroup τ K)
    (ht1 : (⟨rootDiagUnit τ c, hdA⟩ : adjointGroup τ K) ≠ 1)
    (ht2 : (⟨rootDiagUnit τ c, hdA⟩ : adjointGroup τ K) ^ 2 = 1)
    (ψ : KernelComponent (maskChar (signTupleBits c)))
    (hψ : 2 < (componentRoots (maskChar (signTupleBits c)) ψ).ncard) :
    HasInvolutionComponent ↥(adjointGroup τ K) := by
  have hH := CFSG.ComponentClassification.HarrisLit.T1.P51Q.isComponent_componentRootSpan_toral_of_ncard
    hK2 hc ψ hψ
  have hX := (CFSG.isComponent_iff_open _).1 hH
  let Cc := Subgroup.centralizer
    ({(⟨rootDiagUnit τ c, hdA⟩ : adjointGroup τ K)} : Set (adjointGroup τ K))
  let e : ↥Cc ≃* ↥(toralCentralizer τ K c) :=
    (Cc.equivMapOfInjective (adjointGroup τ K).subtype (adjointGroup τ K).subtype_injective).trans
      (MulEquiv.subgroupCongr (map_centralizer_involution_eq hdA))
  exact hasInvolutionComponent_of_open_component _ ht1 ht2 _
    (isComponentOf_top_map_equiv e.symm hX)

theorem untwisted_node_data {τ : Tag} (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    ∃ i j k m : Fin τ.rank, Even (τ.cartan i j) ∧ Even (τ.cartan i k) ∧ j ≠ k ∧
      iform (Pi.single k 1 : Fin τ.rank → ℤ) (Pi.single j 1) ≠ 0 ∧ Odd (τ.cartan i m) := by
  rcases hτ with rfl | rfl | rfl | rfl
  · exact ⟨⟨3, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, by decide, by decide,
      by decide, by decide, by decide⟩
  · exact ⟨⟨5, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨4, by decide⟩, by decide, by decide,
      by decide, by decide, by decide⟩
  · exact ⟨⟨6, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨5, by decide⟩, by decide, by decide,
      by decide, by decide, by decide⟩
  · exact ⟨⟨7, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨6, by decide⟩, by decide, by decide,
      by decide, by decide, by decide⟩

theorem hasInvolutionComponent_adjointGroup_exceptional {τ : CFSG.Blueprint.Chevalley.Tag}
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type} [Field K] [Finite K]
    (hK : ringChar K ≠ 2) : HasInvolutionComponent ↥(adjointGroup τ K) := by
  obtain ⟨i, j, k, m, hj, hk, hjk, hform, hm⟩ := untwisted_node_data hτ
  have hc : ∀ l, signTuple τ K i l = 1 ∨ signTuple τ K i l = -1 :=
    signTuple_eq_one_or_eq_neg_one i
  have hdA : rootDiagUnit τ (signTuple τ K i) ∈ adjointGroup τ K := by
    rw [← torusElt_neg_one_eq i]
    exact torusElt_mem_adjointGroup i (-1)
  have hne : signTuple τ K i ≠ 1 := by
    intro h
    have h1 := congrFun h m
    simp only [signTuple, Pi.one_apply] at h1
    rw [hm.neg_one_zpow] at h1
    exact absurd (congrArg Units.val h1) (by simpa using Ring.neg_one_ne_one_of_char_ne_two hK)
  have ht1 : (⟨rootDiagUnit τ (signTuple τ K i), hdA⟩ : adjointGroup τ K) ≠ 1 := by
    intro h
    have h' : rootDiagUnit τ (signTuple τ K i) = 1 := congrArg Subtype.val h
    rw [← rootDiagUnit_one (τ := τ) (K := K)] at h'
    exact hne (rootDiagUnit_injective h')
  have ht2 : (⟨rootDiagUnit τ (signTuple τ K i), hdA⟩ : adjointGroup τ K) ^ 2 = 1 := by
    refine Subtype.ext ?_
    have hsq : signTuple τ K i * signTuple τ K i = 1 := by
      funext l
      rcases hc l with h | h <;> simp [h]
    change rootDiagUnit τ (signTuple τ K i) ^ 2 = 1
    rw [pow_two, ← rootDiagUnit_mul, hsq, rootDiagUnit_one]
  have hα := mem_kernelRoots_signTuple_single hK i j hj
  have hε := mem_kernelRoots_signTuple_single hK i k hk
  exact hasInvolutionComponent_of_toral hc hK hdA ht1 ht2 _
    (two_lt_ncard_signClass i hα hε hjk hform)

theorem not_isCharTwoType_of_untwistedChevalleyModel_odd
    {τ : CFSG.Blueprint.Chevalley.Tag} (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {q : ℕ}
    (hq : Odd q) {H : Type} [Group H] (h : CFSG.Blueprint.UntwistedChevalleyModel H τ q) :
    ¬ CFSG.Open.IsCharTwoType H := by
  obtain ⟨K, hKfield, hKfin, hKcard, ⟨e⟩⟩ := h
  intro hchar
  have hK : ringChar K ≠ 2 := ringChar_ne_two_of_odd_card_untwisted K (by rw [hKcard]; exact hq)
  have hQ : CFSG.Open.IsCharTwoType (CFSG.Blueprint.AdjointQuotient τ K) :=
    CFSG.RankThree.PartTwo.Census.isCharTwoType_of_mulEquiv e hchar
  let qiso : CFSG.Blueprint.AdjointQuotient τ K ≃* ↥(adjointGroup τ K) :=
    (QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans QuotientGroup.quotientBot
  have hA : CFSG.Open.IsCharTwoType ↥(adjointGroup τ K) :=
    CFSG.RankThree.PartTwo.Census.isCharTwoType_of_mulEquiv qiso hQ
  haveI : Finite (ModGL τ K) := finite_modGL
  haveI : Finite ↥(adjointGroup τ K) := inferInstance
  exact CFSG.RankThreeEvenClassification.Helpers.charTwoType_no_involution_component hA
    (hasInvolutionComponent_adjointGroup_exceptional hτ hK)

theorem false_of_untwistedExceptional_odd {G : Type} [Group G] [Finite G]
    (hS : CFSG.Yardstones.Mf4cdcdf2e013.Standing4 G) {t : CFSG.Open.StatedLieTag}
    (ht : t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8) {p f : ℕ} (hp : p ≠ 2)
    (h : CFSG.Blueprint.ChevalleyExceptionalModel G t p f) : False := by
  obtain ⟨hadm, hmatch⟩ := h
  have hodd : Odd (p ^ f) := ((hadm.1).odd_of_ne_two hp).pow
  rcases ht with rfl | rfl | rfl | rfl
  · exact not_isCharTwoType_of_untwistedChevalleyModel_odd (Or.inl rfl) hodd hmatch hS.charTwo
  · exact not_isCharTwoType_of_untwistedChevalleyModel_odd (Or.inr (Or.inl rfl)) hodd hmatch
      hS.charTwo
  · exact not_isCharTwoType_of_untwistedChevalleyModel_odd (Or.inr (Or.inr (Or.inl rfl))) hodd
      hmatch hS.charTwo
  · exact not_isCharTwoType_of_untwistedChevalleyModel_odd (Or.inr (Or.inr (Or.inr rfl))) hodd
      hmatch hS.charTwo

end CFSG.LocalAnalysis.UniqueFourCatalog
