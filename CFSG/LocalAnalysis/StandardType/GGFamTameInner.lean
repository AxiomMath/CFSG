module

public import CFSG.LocalAnalysis.StandardType.GGFamTameRangeSpan
public import CFSG.LocalAnalysis.StandardType.GGFamTameLang
public import CFSG.LocalAnalysis.StandardType.GGFamTameOrbit
public import CFSG.LocalAnalysis.StandardType.GGFamTameTransfer
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4ULang
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcTamePrime
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcTame.SmallField
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerF4Root
public import CFSG.HardMathSupport.Timmesfeld.RootAut.Main
public import CFSG.LocalAnalysis.StandardType.GGFamTameInnerAux
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcLang

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.RootAut
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped commutatorElement

private theorem famInner_four_le
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (hρ : ∀ γ ∈ kernelRoots χ, S.ρ γ ∈ kernelRoots χ) (i : KernelComponent χ)
    (hkind : twistKindM S.ρ χ i = .inner)
    (hQ : 4 ≤ S.D.q ^ componentOrbitLength S.ρ (componentRoots χ i)) :
    CFSG.IsQuasisimple (rationalComponentM S.ρ S.Γ χ i) := by
  classical
  obtain ⟨hs0, hs, hmin⟩ := fam_componentOrbitLength_spec S hρ i
  set s := componentOrbitLength S.ρ (componentRoots χ i) with hsdef
  haveI : NeZero s := ⟨hs0.ne'⟩
  have hinner := fam_twistInner_of_twistKind_eq_inner rootAutIsWeyl_holds S hρ i hkind
  obtain ⟨σ, z, hσ, hnorm, hz⟩ := fam_exists_untwist S hρ i hs0 hinner
  obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : CharP L r := hchar
  have hσ' : ∀ c, σ c = c ^ (r ^ (e * s)) := fun c => by rw [hσ, hq, ← pow_mul]
  have hQ' : 4 ≤ r ^ (e * s) := by rw [pow_mul, ← hq]; exact hQ
  obtain ⟨t, ht⟩ := exists_unit_sq_ne_one (L := L) σ hσ' (Nat.mul_pos he hs0) hQ'
  have hsL : ∃ u : Lˣ, u ^ 2 ≠ 1 := by
    refine ⟨Units.map (fixSubfield σ).subtype.toMonoidHom t, fun h => ht ?_⟩
    apply Units.ext
    apply Subtype.ext
    simpa using congrArg (fun x : Lˣ => (x : L)) h
  have hperfC := isPerfect_componentRootSpan_of_sq_ne_one (K := fixSubfield σ) (χ := χ) ht i
  have hQS := isQuasisimple_componentRootSpan_of_sq_ne_one (K := fixSubfield σ) (χ := χ) ht i
  obtain ⟨f, hf1, hker, hf2⟩ :=
    fam_rationalComponent_eq_range_componentRootSpan S hρ i hs hmin σ z hnorm hz hsL
  rw [le_antisymm hf1 (hf2 (Subgroup.isPerfect_iff.1 hperfC))]
  exact isQuasisimple_range_of_ker_le_center hQS f hker

private theorem famInner_small_tame
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ} (S : LangSetup τ L p₀)
    {M : Type} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (hp : p.Prime) (hρ : ∀ γ ∈ kernelRoots χ, S.ρ γ ∈ kernelRoots χ) (i : KernelComponent χ)
    (hkind : twistKindM S.ρ χ i = .inner) (hp5 : τ = .G2 → 5 ≤ p)
    (hχp : ∀ γ, IsRoot τ γ → χ (Multiplicative.ofAdd γ) ^ p = 1)
    (hχ1 : ∃ γ, IsRoot τ γ ∧ χ (Multiplicative.ofAdd γ) ≠ 1)
    (hQ : S.D.q ^ componentOrbitLength S.ρ (componentRoots χ i) < 4) :
    CFSG.IsQuasisimple (rationalComponentM S.ρ S.Γ χ i) ∨
      (Group.IsSolvable (rationalComponentM S.ρ S.Γ χ i) ∧
        ∀ α ∈ componentRoots χ i, ∀ δ ∈ componentRoots χ i, δ = α ∨ δ = -α) := by
  classical
  obtain ⟨hs0, hs, hmin⟩ := fam_componentOrbitLength_spec S hρ i
  set s := componentOrbitLength S.ρ (componentRoots χ i) with hsdef
  haveI : NeZero s := ⟨hs0.ne'⟩
  have hinner := fam_twistInner_of_twistKind_eq_inner rootAutIsWeyl_holds S hρ i hkind
  obtain ⟨σ, z, hσ, hnorm, hz⟩ := fam_exists_untwist S hρ i hs0 hinner
  obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : CharP L r := hchar
  have hσ' : ∀ c, σ c = c ^ (r ^ (e * s)) := fun c => by rw [hσ, hq, ← pow_mul]
  have hQ' : r ^ (e * s) < 4 := by rw [pow_mul, ← hq]; exact hQ
  obtain ⟨hfinset, hcardset⟩ := ncard_pow_eq_self (L := L) r (e * s) (Nat.mul_pos he hs0)
  have hset : (fixSubfield σ : Set L) = {c : L | c ^ (r ^ (e * s)) = c} := by
    ext c
    show c ∈ fixSubfield σ ↔ _
    rw [mem_fixSubfield, hσ']
    rfl
  have hfinK : Finite (fixSubfield σ) := by
    have h1 : (fixSubfield σ : Set L).Finite := by rw [hset]; exact hfinset
    exact h1.to_subtype
  haveI : Finite (fixSubfield σ) := hfinK
  have hKcard : Nat.card (fixSubfield σ) = r ^ (e * s) := by
    have h1 : Nat.card (fixSubfield σ) = (fixSubfield σ : Set L).ncard :=
      Nat.card_coe_set_eq (fixSubfield σ : Set L)
    rw [h1, hset, hcardset]
  have hKle : Nat.card (fixSubfield σ) ≤ 3 := by rw [hKcard]; omega
  have hsL : ∃ u : Lˣ, u ^ 2 ≠ 1 := by
    obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset ({0, 1, -1} : Finset L)
    have hc0 : c ≠ 0 := fun h => hc (by simp [h])
    refine ⟨Units.mk0 c hc0, fun h => hc ?_⟩
    have h2 : c ^ 2 = 1 := by simpa using congrArg (fun x : Lˣ => (x : L)) h
    have h3 : (c - 1) * (c + 1) = 0 := by linear_combination h2
    rcases mul_eq_zero.1 h3 with h | h
    · simp [sub_eq_zero.1 h]
    · simp [eq_neg_of_add_eq_zero_left h]
  set C := componentRootSpan (fixSubfield σ) χ i with hCdef
  obtain ⟨f₁, hf₁1, -, -⟩ :=
    fam_rationalComponent_eq_range_componentRootSpan S hρ i hs hmin σ z hnorm hz hsL
  by_cases hrank : ∀ α ∈ componentRoots χ i, ∀ δ ∈ componentRoots χ i, δ = α ∨ δ = -α
  · refine Or.inr ⟨?_, hrank⟩
    have : Group.IsSolvable ↥C := isSolvable_componentRootSpan_of_rank_one hKle i hrank
    have : Group.IsSolvable ↥f₁.range := Group.isSolvable_of_surjective f₁.rangeRestrict_surjective
    exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hf₁1)
      (Subgroup.inclusion_injective hf₁1)
  obtain ⟨hDQ, hD⟩ := smallFieldInner_quasisimple_of_not_rankOne (K := fixSubfield σ) (χ := χ)
    i hp hp5 hχp hχ1 hKle hrank
  refine Or.inl ?_
  have hY : ∀ g g' : ModGL τ L, g ∈ rootSpan τ L (componentRoots χ i) →
      g' ∈ rootSpan τ L (componentRoots χ i) →
      frobGL σ g * g⁻¹ ∈ (famOrbitFamily S hρ i hs hmin).Z →
      frobGL σ g' * g'⁻¹ ∈ (famOrbitFamily S hρ i hs hmin).Z →
      ⁅g, g'⁆ ∈ (⁅C, C⁆).map (baseChangeGL (fixSubfield σ).subtype) := by
    intro g g' hg hg' hgZ hgZ'
    rcases hD with hD2 | hDC
    · have hF : ∀ d : L, σ d = d → d ≠ 0 → d = 1 := by
        intro d hd hd0
        let : Fintype (fixSubfield σ) := Fintype.ofFinite _
        have hcard : Fintype.card (fixSubfield σ) = 2 := by
          rw [← Nat.card_eq_fintype_card]; exact hD2
        have hdK : d ∈ fixSubfield σ := hd
        have h1 := FiniteField.pow_card_sub_one_eq_one (⟨d, hdK⟩ : fixSubfield σ)
          (fun h => hd0 (congrArg Subtype.val h))
        rw [hcard] at h1
        simpa using congrArg Subtype.val h1
      have := famInner_orbit_commutator_mem_commutator_CQ S hρ i hs hmin σ hsL hF hg hg' hgZ hgZ'
      rwa [CQ_eq_map, ← Subgroup.map_commutator] at this
    · have := famRangeSpan_orbit_commutator_mem_CQ S hρ i hs hmin σ hsL hg hg' hgZ hgZ'
      rwa [CQ_eq_map, ← hDC] at this
  obtain ⟨f, hf1, hker, hf2⟩ := famRangeSpan_rationalComponent_eq_rangeT S hρ i hs hmin σ z hnorm hz
    ⁅C, C⁆ (Subgroup.commutator_le_self _ |>.trans le_rfl) hY
  have hperfD : ⁅⁅C, C⁆, ⁅C, C⁆⁆ = ⁅C, C⁆ := Subgroup.isPerfect_iff.1 hDQ.1
  rw [le_antisymm hf1 (hf2 hperfD)]
  exact isQuasisimple_range_of_ker_le_center hDQ f hker

theorem langFamTame_inner
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p₀ p : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime) (hp2 : p ≠ 2) {ι : Type}
    {a : ι → Fin τ.rank → Lˣ} (hT : ∀ u, rootDiagUnit τ (a u) ∈ S.D.torus)
    (hap : ∀ u j, a u j ^ p = 1) (h1 : ∃ u, rootDiagUnit τ (a u) ≠ 1)
    (i : KernelComponent (famCharHom a))
    (hk : twistKindM S.ρ (famCharHom a) i = .inner) :
    CFSG.IsQuasisimple (rationalComponentM S.ρ S.Γ (famCharHom a) i) ∨
      Group.IsSolvable (rationalComponentM S.ρ S.Γ (famCharHom a) i) := by
  have hρ : ∀ γ ∈ kernelRoots (famCharHom a), S.ρ γ ∈ kernelRoots (famCharHom a) :=
    fun γ hγ => rho_mem_kernelRoots_famChar S a hT hγ
  have hχp : ∀ γ, IsRoot τ γ → (famCharHom a) (Multiplicative.ofAdd γ) ^ p = 1 := by
    intro γ _
    funext u
    exact show rootChar (a u) γ ^ p = 1 from rootChar_pow_eq_one_of_forall (hap u) γ
  have hχ1 : ∃ γ, IsRoot τ γ ∧ (famCharHom a) (Multiplicative.ofAdd γ) ≠ 1 := by
    obtain ⟨u, hu⟩ := h1
    obtain ⟨γ, hγ, hne⟩ := exists_rootChar_ne_one hu
    exact ⟨γ, hγ, fun h => hne (show rootChar (a u) γ = 1 from congrFun h u)⟩
  have hp5 : τ = .G2 → 5 ≤ p := by
    rintro rfl
    rcases hτ with h | h | h <;> exact absurd h (by decide)
  by_cases hQ : 4 ≤ S.D.q ^ componentOrbitLength S.ρ (componentRoots (famCharHom a) i)
  · exact Or.inl (famInner_four_le S hρ i hk hQ)
  · exact (famInner_small_tame S hp hρ i hk hp5 hχp hχ1 (not_le.1 hQ)).imp_right And.left

theorem langFamTame_inner_of_hp5
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p₀ p : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime) (hp5 : τ = .G2 → 5 ≤ p) {ι : Type}
    {a : ι → Fin τ.rank → Lˣ} (hT : ∀ u, rootDiagUnit τ (a u) ∈ S.D.torus)
    (hap : ∀ u j, a u j ^ p = 1) (h1 : ∃ u, rootDiagUnit τ (a u) ≠ 1)
    (i : KernelComponent (famCharHom a))
    (hk : twistKindM S.ρ (famCharHom a) i = .inner) :
    CFSG.IsQuasisimple (rationalComponentM S.ρ S.Γ (famCharHom a) i) ∨
      Group.IsSolvable (rationalComponentM S.ρ S.Γ (famCharHom a) i) := by
  have hρ : ∀ γ ∈ kernelRoots (famCharHom a), S.ρ γ ∈ kernelRoots (famCharHom a) :=
    fun γ hγ => rho_mem_kernelRoots_famChar S a hT hγ
  have hχp : ∀ γ, IsRoot τ γ → (famCharHom a) (Multiplicative.ofAdd γ) ^ p = 1 := by
    intro γ _
    funext u
    exact show rootChar (a u) γ ^ p = 1 from rootChar_pow_eq_one_of_forall (hap u) γ
  have hχ1 : ∃ γ, IsRoot τ γ ∧ (famCharHom a) (Multiplicative.ofAdd γ) ≠ 1 := by
    obtain ⟨u, hu⟩ := h1
    obtain ⟨γ, hγ, hne⟩ := exists_rootChar_ne_one hu
    exact ⟨γ, hγ, fun h => hne (show rootChar (a u) γ = 1 from congrFun h u)⟩
  by_cases hQ : 4 ≤ S.D.q ^ componentOrbitLength S.ρ (componentRoots (famCharHom a) i)
  · exact Or.inl (famInner_four_le S hρ i hk hQ)
  · exact (famInner_small_tame S hp hρ i hk hp5 hχp hχ1 (not_le.1 hQ)).imp_right And.left

theorem langFamTame_inner_isQuasisimple
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p₀ p : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime) {ι : Type}
    {a : ι → Fin τ.rank → Lˣ} (hT : ∀ u, rootDiagUnit τ (a u) ∈ S.D.torus)
    (hap : ∀ u j, a u j ^ p = 1) (h1 : ∃ u, rootDiagUnit τ (a u) ≠ 1)
    (i : KernelComponent (famCharHom a))
    (hk : twistKindM S.ρ (famCharHom a) i = .inner)
    (hbig : 4 ≤ S.D.q ^ componentOrbitLength S.ρ (componentRoots (famCharHom a) i) ∨
      ¬ ∀ α ∈ componentRoots (famCharHom a) i, ∀ δ ∈ componentRoots (famCharHom a) i,
        δ = α ∨ δ = -α) :
    CFSG.IsQuasisimple (rationalComponentM S.ρ S.Γ (famCharHom a) i) := by
  have hρ : ∀ γ ∈ kernelRoots (famCharHom a), S.ρ γ ∈ kernelRoots (famCharHom a) :=
    fun γ hγ => rho_mem_kernelRoots_famChar S a hT hγ
  have hχp : ∀ γ, IsRoot τ γ → (famCharHom a) (Multiplicative.ofAdd γ) ^ p = 1 := by
    intro γ _
    funext u
    exact show rootChar (a u) γ ^ p = 1 from rootChar_pow_eq_one_of_forall (hap u) γ
  have hχ1 : ∃ γ, IsRoot τ γ ∧ (famCharHom a) (Multiplicative.ofAdd γ) ≠ 1 := by
    obtain ⟨u, hu⟩ := h1
    obtain ⟨γ, hγ, hne⟩ := exists_rootChar_ne_one hu
    exact ⟨γ, hγ, fun h => hne (show rootChar (a u) γ = 1 from congrFun h u)⟩
  have hp5 : τ = .G2 → 5 ≤ p := by
    rintro rfl
    rcases hτ with h | h | h <;> exact absurd h (by decide)
  by_cases hQ : 4 ≤ S.D.q ^ componentOrbitLength S.ρ (componentRoots (famCharHom a) i)
  · exact famInner_four_le S hρ i hk hQ
  · have hQlt : S.D.q ^ componentOrbitLength S.ρ (componentRoots (famCharHom a) i) < 4 :=
      not_le.1 hQ
    rcases famInner_small_tame S hp hρ i hk hp5 hχp hχ1 hQlt with h | ⟨-, hrank⟩
    · exact h
    · rcases hbig with hbig | hbig
      · exact absurd hbig hQ
      · exact absurd hrank hbig

end CFSG.StandardType.TableCRes
