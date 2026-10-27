module

public import CFSG.LocalAnalysis.StandardType.GGFamSplitFrameRange
public import CFSG.LocalAnalysis.StandardType.GGFamUnitaryFrameRange
public import CFSG.LocalAnalysis.StandardType.GGFamInnerCover
public import CFSG.LocalAnalysis.StandardType.GGFamTameRangeSpan

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.LieType.Steinberg.Adjoint
  CFSG.ClassicalInvolution.WeakCT CFSG.Timmesfeld CFSG.Assembly.LowTwoRank
  CFSG.RankThree.Classical2
open scoped MatrixGroups commutatorElement

private theorem famTypeACover_twistKindM_eq_inner_of_compRank_eq_one
    {τ : Tag} {M : Type*} [CommGroup M]
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} (i : KernelComponent χ)
    (h1 : compRank (componentRoots χ i) = 1) :
    twistKindM ρ χ i = .inner := by
  classical
  by_cases hin : twistInner (componentRoots χ i)
      ((ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength ρ (componentRoots χ i)])
  · unfold twistKindM
    rw [if_pos hin]
  · unfold twistKindM
    rw [if_neg hin, if_neg (by rintro (⟨h, _⟩ | ⟨h, _⟩) <;> omega),
      if_neg (fun h => by omega), if_neg (fun h => by omega)]

theorem fam_exists_slCover_rankOne
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀)
    {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (hρ : ∀ γ ∈ kernelRoots χ, S.ρ γ ∈ kernelRoots χ) (i : KernelComponent χ)
    (h1 : compRank (componentRoots χ i) = 1)
    (hn : (componentRoots χ i).ncard = 2)
    (hQS : CFSG.IsQuasisimple (rationalComponentM S.ρ S.Γ χ i)) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (f : ℕ),
      1 ≤ f ∧ Nat.card K = ringChar L ^ f ∧
      ringChar L ^ f = S.D.q ^ componentOrbitLength S.ρ (componentRoots χ i) ∧
      ringChar K = ringChar L ∧ 4 ≤ Nat.card K ∧
      ∃ g : SL(2, K) →* ↥(rationalComponentM S.ρ S.Γ χ i),
        Function.Surjective g ∧ g.ker ≤ Subgroup.center SL(2, K) := by
  classical
  obtain ⟨β, hβ, hΨ⟩ := fam_exists_pair_of_rank_one i hn
  obtain ⟨hs0, hs, hmin⟩ := fam_componentOrbitLength_spec S hρ i
  set s := componentOrbitLength S.ρ (componentRoots χ i) with hsdef
  have : NeZero s := ⟨hs0.ne'⟩
  have hinner : twistInner (componentRoots χ i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[s]) :=
    fam_twistInner_of_twistKind_eq_inner
      CFSG.HardMathSupport.Timmesfeld.RootAut.rootAutIsWeyl_holds S hρ i
      (famTypeACover_twistKindM_eq_inner_of_compRank_eq_one (ρ := S.ρ) i h1)
  obtain ⟨σ, z, hσ, hnorm, hz⟩ := fam_exists_untwist S hρ i hs0 hinner
  obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : CharP L r := hchar
  have hrL : ringChar L = r := ringChar.eq L r
  have hσ' : ∀ c, σ c = c ^ (r ^ (e * s)) := fun c => by rw [hσ, hq, ← pow_mul]
  obtain ⟨hfinK, hKcard⟩ := finite_card_fixSubfield (L := L) (r := r) (n := e * s)
    (Nat.mul_pos he hs0) σ hσ'
  have hsL : ∃ u : Lˣ, u ^ 2 ≠ 1 :=
    CFSG.HardMathSupport.Dickson.Sec6.Up34Exc.exists_unit_sq_ne_one_alg
  obtain ⟨f, hf1, hker, hf2⟩ :=
    fam_rationalComponent_eq_range_componentRootSpan S hρ i hs hmin σ z hnorm hz hsL
  have hC : componentRootSpan (fixSubfield σ) χ i =
      (rootSL2 τ (fixSubfield σ) β).range := by
    rw [CFSG.RankThree.Chevalley.range_rootSL2_of_isRoot hβ]
    show rootSpan τ (fixSubfield σ) (componentRoots χ i) = _
    rw [hΨ]
    simp only [rootSpan, iSup_insert, iSup_singleton]
  let eSL : SL(2, ↥(fixSubfield σ)) ≃*
      ↥(componentRootSpan (fixSubfield σ) χ i) :=
    (MonoidHom.ofInjective (CFSG.RankThree.Chevalley.rootSL2_injective_of_field
      (K := ↥(fixSubfield σ)) β)).trans (MulEquiv.subgroupCongr hC.symm)
  have hker' := ker_comp_mulEquiv_le_center eSL f hker
  by_cases hQ4 : 4 ≤ r ^ (e * s)
  · obtain ⟨t, ht⟩ := exists_unit_sq_ne_one (L := L) σ hσ' (Nat.mul_pos he hs0) hQ4
    have hperfC := isPerfect_componentRootSpan_of_sq_ne_one (K := fixSubfield σ)
      (χ := χ) ht i
    have hRf : f.range = rationalComponentM S.ρ S.Γ χ i :=
      le_antisymm (hf2 (Subgroup.isPerfect_iff.1 hperfC)) hf1
    let g : SL(2, ↥(fixSubfield σ)) →* ↥(rationalComponentM S.ρ S.Γ χ i) :=
      (f.comp eSL.toMonoidHom).codRestrict _ (fun c => by
        rw [← hRf]
        exact ⟨eSL c, rfl⟩)
    have hgsurj : Function.Surjective g := by
      rintro ⟨x, hx⟩
      obtain ⟨c, hc⟩ : x ∈ f.range := hRf ▸ hx
      obtain ⟨c', rfl⟩ := eSL.surjective c
      exact ⟨c', Subtype.ext hc⟩
    have hgker : g.ker ≤ Subgroup.center SL(2, ↥(fixSubfield σ)) := by
      intro c hc
      apply hker'
      rw [MonoidHom.mem_ker] at hc ⊢
      exact congrArg Subtype.val hc
    rw [hrL]
    refine ⟨↥(fixSubfield σ), inferInstance, hfinK, e * s, Nat.mul_pos he hs0, hKcard,
      ?_, ?_, ?_, g, hgsurj, hgker⟩
    · rw [pow_mul, ← hq]
    · exact (ringChar_subfield' _).trans hrL
    · rw [hKcard]
      exact hQ4
  · exfalso
    have hKle : Nat.card (fixSubfield σ) ≤ 3 := by rw [hKcard]; omega
    haveI : Group.IsSolvable SL(2, ↥(fixSubfield σ)) :=
      isSolvable_specialLinear_two_of_card_le_three hKle
    haveI : Group.IsSolvable ↥(componentRootSpan (fixSubfield σ) χ i) :=
      Group.isSolvable_of_isSolvable_injective (f := eSL.symm.toMonoidHom) eSL.symm.injective
    haveI : Group.IsSolvable ↥f.range :=
      Group.isSolvable_of_surjective (f := f.rangeRestrict) f.rangeRestrict_surjective
    haveI : Group.IsSolvable ↥(rationalComponentM S.ρ S.Γ χ i) :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hf1)
    exact CFSG.HardMathSupport.Solomon.Coordinator.LieComp.not_isSolvable_of_isQuasisimple
      hQS inferInstance

theorem fam_exists_slCover_splitFrame
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀)
    {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (hρ : ∀ γ ∈ kernelRoots χ, S.ρ γ ∈ kernelRoots χ) (i : KernelComponent χ) {ν : ℕ}
    (hν : 3 ≤ ν) {ψ : SL(ν, L) →* ModGL τ L} {σ : Fin ν → Fin ν → Fin τ.rank → ℤ}
    (hψ : IsSLFrame ψ σ) (hΨ : componentRoots χ i = frameRoots σ)
    (π : Equiv.Perm (Fin ν))
    (hπ : ∀ a b, a ≠ b → (S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
      (componentRoots χ i)] (σ a b) = σ (π a) (π b)) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (f : ℕ),
      1 ≤ f ∧ Nat.card K = ringChar L ^ f ∧
      ringChar L ^ f = S.D.q ^ componentOrbitLength S.ρ (componentRoots χ i) ∧
      ringChar K = ringChar L ∧
      ∃ g : SL(ν, K) →* ↥(rationalComponentM S.ρ S.Γ χ i),
        Function.Surjective g ∧ g.ker ≤ Subgroup.center SL(ν, K) := by
  classical
  obtain ⟨hs0, -, -⟩ := fam_componentOrbitLength_spec S hρ i
  obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : CharP L r := hchar
  set s := componentOrbitLength S.ρ (componentRoots χ i) with hsdef
  have hrL : ringChar L = r := ringChar.eq L r
  obtain ⟨σQ, hσc, f, hf1, hfker, hf2⟩ := fam_split_exists_hom S hρ i hν hψ hΨ π hπ
    hr hchar he hq
  obtain ⟨hfinK, hKcard⟩ := finite_card_fixSubfield (L := L) (r := r) (n := e * s)
    (Nat.mul_pos he hs0) σQ hσc
  have hperf : Group.IsPerfect SL(ν, ↥(fixSubfield σQ)) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect hν
  have hRf : f.range = rationalComponentM S.ρ S.Γ χ i :=
    le_antisymm (hf2 hperf) hf1
  let g : SL(ν, ↥(fixSubfield σQ)) →* ↥(rationalComponentM S.ρ S.Γ χ i) :=
    f.codRestrict _ (fun c => hRf ▸ ⟨c, rfl⟩)
  have hgsurj : Function.Surjective g := by
    rintro ⟨x, hx⟩
    obtain ⟨c, hc⟩ : x ∈ f.range := hRf ▸ hx
    exact ⟨c, Subtype.ext hc⟩
  have hgker : g.ker ≤ Subgroup.center SL(ν, ↥(fixSubfield σQ)) := by
    intro c hc
    apply hfker
    rw [MonoidHom.mem_ker] at hc ⊢
    exact congrArg Subtype.val hc
  rw [hrL]
  refine ⟨↥(fixSubfield σQ), inferInstance, hfinK, e * s, Nat.mul_pos he hs0, hKcard,
    ?_, ?_, g, hgsurj, hgker⟩
  · rw [pow_mul, ← hq]
  · exact (ringChar_subfield' _).trans hrL

theorem fam_not_unitaryFrame_three_two
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀)
    {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (hρ : ∀ γ ∈ kernelRoots χ, S.ρ γ ∈ kernelRoots χ) (i : KernelComponent χ) {ν : ℕ}
    (hν : 3 ≤ ν) {ψ : SL(ν, L) →* ModGL τ L} {σ : Fin ν → Fin ν → Fin τ.rank → ℤ}
    (hψ : IsSLFrame ψ σ) (hΨ : componentRoots χ i = frameRoots σ)
    (π : Equiv.Perm (Fin ν))
    (hπ : ∀ a b, a ≠ b → (S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
      (componentRoots χ i)] (σ a b) = σ (π b) (π a))
    {r e : ℕ} (hr : r.Prime) (hchar : CharP L r) (he : 0 < e) (hq : S.D.q = r ^ e)
    (hQS : CFSG.IsQuasisimple (rationalComponentM S.ρ S.Γ χ i)) :
    (ν, r ^ (e * componentOrbitLength S.ρ (componentRoots χ i))) ≠ (3, 2) := by
  classical
  obtain ⟨hs0, -, -⟩ := fam_componentOrbitLength_spec S hρ i
  set s := componentOrbitLength S.ρ (componentRoots χ i) with hsdef
  have hes : 0 < e * s := Nat.mul_pos he hs0
  intro h32
  obtain ⟨σQ, hσc, f, hf1, -, -⟩ := fam_two_suN_exists_hom S hρ i hν hψ hΨ π hπ
    hr hchar he hq
  obtain ⟨hfin, -, hc216⟩ := stdUnitary_fixSubgroup (ν := ν) hr hes σQ hσc hν
  have hcard := hc216 h32
  haveI := hfin
  haveI := Fintype.ofFinite
    ↥(CFSG.RankThree.Classical2.fixSubgroup (stdUnitaryEquiv (ν := ν) σQ))
  haveI : Group.IsSolvable
      ↥(CFSG.RankThree.Classical2.fixSubgroup (stdUnitaryEquiv (ν := ν) σQ)) :=
    CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
      (p := 2) (q := 3) (a := 3) (b := 3) Nat.prime_two Nat.prime_three (by norm_num)
      (by rw [← Nat.card_eq_fintype_card, hcard]; norm_num)
  haveI : Group.IsSolvable ↥f.range :=
    Group.isSolvable_of_surjective (f := f.rangeRestrict) f.rangeRestrict_surjective
  haveI : Group.IsSolvable ↥(rationalComponentM S.ρ S.Γ χ i) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hf1)
  exact CFSG.HardMathSupport.Solomon.Coordinator.LieComp.not_isSolvable_of_isQuasisimple
    hQS inferInstance

theorem fam_exists_suCover_unitaryFrame
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀)
    {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (hρ : ∀ γ ∈ kernelRoots χ, S.ρ γ ∈ kernelRoots χ) (i : KernelComponent χ) {ν : ℕ}
    (hν : 3 ≤ ν) {ψ : SL(ν, L) →* ModGL τ L} {σ : Fin ν → Fin ν → Fin τ.rank → ℤ}
    (hψ : IsSLFrame ψ σ) (hΨ : componentRoots χ i = frameRoots σ)
    (π : Equiv.Perm (Fin ν))
    (hπ : ∀ a b, a ≠ b → (S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
      (componentRoots χ i)] (σ a b) = σ (π b) (π a))
    (hQS : CFSG.IsQuasisimple (rationalComponentM S.ρ S.Γ χ i)) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (f : ℕ),
      1 ≤ f ∧ Nat.card K = (ringChar L ^ f) ^ 2 ∧
      ringChar L ^ f = S.D.q ^ componentOrbitLength S.ρ (componentRoots χ i) ∧
      ringChar K = ringChar L ∧ (ν, ringChar L ^ f) ≠ (3, 2) ∧
      ∃ g : ↥(StatedSU ν (ringChar L ^ f) K) →* ↥(rationalComponentM S.ρ S.Γ χ i),
        Function.Surjective g ∧
          g.ker ≤ Subgroup.center ↥(StatedSU ν (ringChar L ^ f) K) := by
  classical
  obtain ⟨hs0, -, -⟩ := fam_componentOrbitLength_spec S hρ i
  obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : CharP L r := hchar
  set s := componentOrbitLength S.ρ (componentRoots χ i) with hsdef
  have hes : 0 < e * s := Nat.mul_pos he hs0
  have hrL : ringChar L = r := ringChar.eq L r
  have h32r : (ν, r ^ (e * s)) ≠ (3, 2) :=
    fam_not_unitaryFrame_three_two S hρ i hν hψ hΨ π hπ hr hchar he hq hQS
  obtain ⟨σQ, hσc, f, hf1, hfker, hf2⟩ := fam_two_suN_exists_hom S hρ i hν hψ hΨ π hπ
    hr hchar he hq
  obtain ⟨hfin, hqsC, -⟩ := stdUnitary_fixSubgroup (ν := ν) hr hes σQ hσc hν
  have hCperf : Group.IsPerfect
      ↥(CFSG.RankThree.Classical2.fixSubgroup (stdUnitaryEquiv (ν := ν) σQ)) :=
    (hqsC h32r).1
  have hRf : f.range = rationalComponentM S.ρ S.Γ χ i :=
    le_antisymm (hf2 hCperf) hf1
  let g : ↥(CFSG.RankThree.Classical2.fixSubgroup (stdUnitaryEquiv (ν := ν) σQ)) →*
      ↥(rationalComponentM S.ρ S.Γ χ i) :=
    f.codRestrict _ (fun c => hRf ▸ ⟨c, rfl⟩)
  have hgker : g.ker ≤ Subgroup.center
      ↥(CFSG.RankThree.Classical2.fixSubgroup (stdUnitaryEquiv (ν := ν) σQ)) := by
    intro c hc
    apply hfker
    rw [MonoidHom.mem_ker] at hc ⊢
    exact congrArg Subtype.val hc
  obtain ⟨F, hFcard, ⟨eC⟩⟩ :=
    CFSG.HardMathSupport.Dickson.Sec6.Up34Exc.two_suN_exists_equiv hr hes σQ hσc hν
  haveI : Finite ↥F := Nat.finite_of_card_ne_zero (by
    rw [hFcard]
    exact (pow_pos (pow_pos hr.pos _) 2).ne')
  let g' : ↥(StatedSU ν (r ^ (e * s)) F) →*
      ↥(rationalComponentM S.ρ S.Γ χ i) := g.comp eC.toMonoidHom
  have hg'surj : Function.Surjective g' := by
    rintro ⟨x, hx⟩
    obtain ⟨c, hc⟩ : x ∈ f.range := hRf ▸ hx
    obtain ⟨c', rfl⟩ := eC.surjective c
    exact ⟨c', Subtype.ext hc⟩
  have hg'ker : g'.ker ≤ Subgroup.center ↥(StatedSU ν (r ^ (e * s)) F) :=
    ker_comp_mulEquiv_le_center eC g hgker
  have hring : ringChar ↥F = ringChar L := ringChar_subfield' _
  rw [hrL]
  refine ⟨↥F, inferInstance, inferInstance, e * s, Nat.mul_pos he hs0, hFcard,
    ?_, ?_, ?_, g', hg'surj, hg'ker⟩
  · rw [pow_mul, ← hq]
  · exact hring.trans hrL
  · exact h32r

end CFSG.StandardType.TableCRes