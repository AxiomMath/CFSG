module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPD4Rank4All
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.G2LongFrame
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUAll
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SRTLargeReeComp
public import CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridgeHolds
public import CFSG.LocalAnalysis.StandardType.ChevTwoLieModel
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434RemTitsLocal
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs1415
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Open Subgroup
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open scoped commutatorElement

@[expose] def NoA6Comp {S : Type} [Group S] (β : MulAut S) : Prop :=
  ∀ K : Subgroup S, IsComponentOf K (fixSubgroup β) →
    IsEmpty ((↥K ⧸ center ↥K) ≃* alternatingGroup (Fin 6))

theorem center_map_mulEquiv_k324 {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    (center G).map (e : G →* H) = center H := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_center_iff]
    intro z
    obtain ⟨w, rfl⟩ := e.surjective z
    change e w * e x = e x * e w
    rw [← map_mul, ← map_mul, (mem_center_iff.1 hx w)]
  · intro hy
    refine ⟨e.symm y, mem_center_iff.2 fun z => ?_, by simp⟩
    apply e.injective
    change e (z * e.symm y) = e (e.symm y * z)
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, mem_center_iff.1 hy (e z)]

noncomputable def centralQuotientCongr {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    G ⧸ center G ≃* H ⧸ center H :=
  QuotientGroup.congr _ _ e (center_map_mulEquiv_k324 e)

theorem NoA6Comp.of_congr {S G : Type} [Group S] [Group G] (e : S ≃* G) {β : MulAut S}
    (h : NoA6Comp (MulAut.congr e β)) : NoA6Comp β := by
  intro K hK
  have hfix : fixSubgroup (MulAut.congr e β) = (fixSubgroup β).map (e : S →* G) := by
    ext x
    rw [mem_fixSubgroup]
    refine Iff.trans ?_ (Subgroup.mem_map_equiv (f := e)).symm
    rw [mem_fixSubgroup]
    show e (β (e.symm x)) = x ↔ β (e.symm x) = e.symm x
    exact e.eq_symm_apply.symm
  have hK' : IsComponentOf (K.map (e : S →* G)) (fixSubgroup (MulAut.congr e β)) := by
    rw [hfix]
    exact CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map e hK
  refine ⟨fun f => (h _ hK').false ?_⟩
  exact (centralQuotientCongr (K.equivMapOfInjective (e : S →* G) e.injective)).symm.trans f

theorem isQuasisimple_of_simple_k324 {D : Type*} [Group D] [IsSimpleGroup D]
    (hnab : ∃ a b : D, a * b ≠ b * a) : CFSG.Open.IsQuasisimple D ∧ center D = ⊥ := by
  have hc : center D = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center D) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      apply hab
      have ha : a ∈ center D := by rw [h]; exact Subgroup.mem_top a
      exact ((Subgroup.mem_center_iff.mp ha) b).symm
  have hcomm : commutator D = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator D) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      apply hab
      have hmem : ⁅a, b⁆ ∈ commutator D :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h, Subgroup.mem_bot, commutatorElement_def, mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
        at hmem
      exact hmem
    · exact h
  let e : D ⧸ center D ≃* D :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
  exact ⟨⟨hcomm, e.isSimpleGroup⟩, hc⟩

theorem false_of_noA6Comp {S : Type} [Group S] {s : S} (h : NoA6Comp (MulAut.conj s))
    {Y : Subgroup S} (hYC : Y ≤ centralizer ({s} : Set S))
    (hYn : (Y.subgroupOf (centralizer ({s} : Set S))).Normal) (hY : UC22.IsAlt ↥Y 6) : False := by
  obtain ⟨φ⟩ := hY
  haveI : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  haveI hYs : IsSimpleGroup ↥Y := φ.isSimpleGroup
  have hnab : ∃ a b : ↥Y, a * b ≠ b * a := by
    refine ⟨φ.symm ⟨Equiv.swap 0 1 * Equiv.swap 0 2, by
        rw [Equiv.Perm.mem_alternatingGroup]; decide⟩,
      φ.symm ⟨Equiv.swap 0 1 * Equiv.swap 0 3, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩,
      fun h => ?_⟩
    rw [← map_mul, ← map_mul] at h
    exact absurd (φ.symm.injective h) (by decide)
  obtain ⟨hq, hZ⟩ := isQuasisimple_of_simple_k324 hnab
  have hfix : fixSubgroup (MulAut.conj s) = centralizer ({s} : Set S) :=
    CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs1415.fixSubgroup_conj s
  have hcomp : IsComponentOf Y (fixSubgroup (MulAut.conj s)) := by
    rw [hfix]
    exact ⟨hYC, IsSubnormal.step hYC hYn (IsSubnormal.refl _), hq⟩
  let e : ↥Y ⧸ center ↥Y ≃* ↥Y :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  exact (h Y hcomp).false (e.trans φ)

section TypeA


variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
  {a : Fin τ.rank → Lˣ}

theorem rationalLieType_of_typeA_prime {p : ℕ} (hp : p.Prime) (hT : rootDiagUnit τ a ∈ S.D.torus)
    (hap : ∀ i, a i ^ p = 1) (h1 : rootDiagUnit τ a ≠ 1) (hℓ3 : ringChar L ≠ 3)
    (i : KernelComponent (rootCharHom a))
    (hA : 1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1))
    (hQS : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    RationalLieType (ringChar L) (rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  classical
  have hℓp : ringChar L ≠ p := ringChar_ne_of_pow_eq_one hp hap h1
  by_cases hr1 : compRank (componentRoots (rootCharHom a) i) = 1
  · exact rationalLieType_of_rankOne S hT i hr1 (by rw [hA.2, hr1]) hℓ3 hQS
  · have h2 : 2 ≤ compRank (componentRoots (rootCharHom a) i) := by omega
    have hTp := rootDiagUnit_pow_eq_one_of_forall hap
    have hpL : ((p : ℕ) : L) ≠ 0 := natCast_ne_zero_of_ringChar_ne hp hℓp
    obtain ⟨ν, ψ, σ, κ, hν, hψ, hκ, hnorm, hΨ⟩ := exists_frame_of_typeA_tag_T_of_prime
      g2LongA2Frame_proved S hp hpL hTp i h2 hA.2
    obtain ⟨hs0, hs, -⟩ := outer_componentOrbitLength_spec S hT i
    set s := componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) with hsdef
    have hmaps : ∀ x y, x ≠ y → (S.ρ : (Fin τ.rank → ℤ) → _)^[s] (σ x y) ∈ frameRoots σ := by
      intro x y hxy
      have h1 : σ x y ∈ componentRoots (rootCharHom a) i := by
        rw [hΨ]
        exact ⟨x, y, hxy, rfl⟩
      have h2 : (S.ρ : (Fin τ.rank → ℤ) → _)^[s] (σ x y) ∈
          (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' componentRoots (rootCharHom a) i := ⟨_, h1, rfl⟩
      rw [hs, hΨ] at h2
      exact h2
    have hneg : ∀ (n : ℕ) (γ : Fin τ.rank → ℤ),
        (S.ρ : (Fin τ.rank → ℤ) → _)^[n] (-γ) = -(S.ρ : (Fin τ.rank → ℤ) → _)^[n] γ := by
      intro n
      induction n with
      | zero => exact fun γ => rfl
      | succ n ih =>
        intro γ
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, S.frob.neg_eq]
    rcases hψ.aut_cases hν hκ hnorm ((S.ρ : (Fin τ.rank → ℤ) → _)^[s]) hmaps (hneg s)
        (iform_rho_iterate S s) with ⟨π, hπ⟩ | ⟨π, hπ⟩
    · exact rationalLieType_of_split_frame S hT i hν hψ hΨ π hπ hℓ3
    · exact rationalLieType_of_unitary_frame S hT i hν hψ hΨ π hπ hQS

end TypeA

section G2D4


variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
  {a : Fin τ.rank → Lˣ}

theorem rationalLieType_G2_D4 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hτ : τ = .G2 ∨ τ = .D4)
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ i, a i ^ p = 1) (h1 : rootDiagUnit τ a ≠ 1)
    (hℓ3 : ringChar L ≠ 3) (i : KernelComponent (rootCharHom a))
    (hq : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    RationalLieType (ringChar L) (rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  classical
  have hℓp : ringChar L ≠ p := ringChar_ne_of_pow_eq_one hp hap h1
  have hpL : ((p : ℕ) : L) ≠ 0 := natCast_ne_zero_of_ringChar_ne hp hℓp
  have hTp := rootDiagUnit_pow_eq_one_of_forall hap
  by_cases hA : 1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)
  · exact rationalLieType_of_typeA_prime S hp hT hap h1 hℓ3 i hA hq
  rcases hτ with rfl | rfl
  · exact (false_of_g2Class_nonAP hp S hpL hTp h1 i hA).elim
  by_cases hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.D4.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])
  · exact rationalLieType_of_inner_nonA_D4 S hp hpL hT hTp i hA hinner
  · obtain ⟨v, μ, x, c, -, hc, -, hlen, hroots, hrank, hncard⟩ :=
      exists_cand_of_class kacD4 facts_D4 d4_tree d4_adj d4_check d4_lt d4_card S hp hpL hTp i
    have hshape := d4_shape c hc hlen
    rw [← hncard, ← hrank] at hshape
    rcases hshape with hA' | hD'
    · exact (hA hA').elim
    · exact excRationalLieTypesOuterDP_proved hp _ L p₀ S a hT hap h1 i hD' hinner hq

end G2D4

section LangSetup


variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
  {a : Fin τ.rank → Lˣ}

theorem noA6Comp_of_langSetup {p : ℕ} (hp : p.Prime) {C : Type} [Group C] [Finite C]
    (ι : C →* ModGL τ L) (hι : Function.Injective ι) (hrange : ι.range = S.Γ) (β : MulAut C)
    (hβ : ∀ c, ι (β c) = rootDiagUnit τ a * ι c * (rootDiagUnit τ a)⁻¹)
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ i, a i ^ p = 1) (h1 : rootDiagUnit τ a ≠ 1)
    (hTame : ∀ i : KernelComponent (rootCharHom a),
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) ∨
        Group.IsSolvable (rationalComponent S.ρ S.Γ (rootCharHom a) i))
    (hRL : ∀ i : KernelComponent (rootCharHom a),
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) →
        RationalLieType (ringChar L) (rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    NoA6Comp β := by
  intro K hK
  obtain ⟨i, hq, hKR⟩ := components_of_langSetup S hp ι hι hrange β hβ hT hap h1 hTame hK
  have hR := (hRL i hq).2
  let eK : ↥K ≃* ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
    (K.equivMapOfInjective ι hι).trans (MulEquiv.subgroupCongr hKR)
  exact ⟨fun f => hR.false ((centralQuotientCongr eK).symm.trans f)⟩

end LangSetup

section Catalogue


theorem noA6Comp_G2 {S : Type} [Group S] [Finite S] (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.G2 q).Valid) (hq3 : q.p ≠ 3) (hq5 : q.p ≠ 5)
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group) {s : S} (hso : orderOf s = 5) :
    NoA6Comp (MulAut.conj s) := by
  classical
  obtain ⟨K, _, hKfin, hK, hKchar, ⟨eK⟩⟩ :=
    CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup
      CFSG.TauCetiBridge.Even.chevalleyBridgesAll.g2 q hv
  let e' : S ≃* ↥(adjointGroup Tag.G2 K) := e.trans eK
  refine NoA6Comp.of_congr e' ?_
  rw [congr_conj_exc]
  set x := e' s with hx
  have hxo : orderOf x = 5 := by rw [hx, MulEquiv.orderOf_eq, hso]
  set h : ModGL Tag.G2 K := (x : ModGL Tag.G2 K) with hh
  have hp1 : h ^ 5 = 1 := by
    rw [hh, ← Subgroup.coe_pow, ← hxo, pow_orderOf_eq_one, Subgroup.coe_one]
  have hh1 : h ≠ 1 := by
    intro h1
    have : x = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hxo
    omega
  have hβ : ∀ c, ((MulAut.conj x) c : ModGL Tag.G2 K) = h * c * h⁻¹ := fun c => by
    simp [hh, MulAut.conj_apply]
  have hhL := baseChange_mem_adjointGroup_of_mem_inndiag
    (CFSG.StandardType.RecipeExcLang.adjointGroup_le_inndiagGroup x.2)
  have hℓ : ringChar K = q.p := ringChar.eq K q.p
  have hpK : ¬ 5 ∣ Nat.card K := by
    rw [hK]
    exact CFSG.LieType.SeitzGeneration.not_dvd_card_of_ne Nat.prime_five (Ne.symm hq5)
  have hG2K : 3 ≤ Nat.card K := by
    rw [hK]
    exact (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
      ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  have hperf : commutator ↥(adjointGroup Tag.G2 K) = ⊤ :=
    (CFSG.LieType.Steinberg.Adjoint.isPerfect_g2_of_three_le_card K hG2K).commutator_eq_top
  have hmon : MonomialToralAt Tag.G2 5 :=
    monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five (by simp) Nat.prime_five
      (by norm_num)
  obtain ⟨S', a, ι, -, -, hT, hap, h1, hinj, hrange, hconj⟩ :=
    exists_langSetup_of_inner_untw (Or.inl rfl) Nat.prime_five hpK (Or.inl le_rfl) hmon hperf
      (MulAut.conj x) h hhL hβ hp1 hh1
  have hAC : ringChar (AlgebraicClosure K) ≠ 3 := by
    rw [ringChar_algebraicClosure, hℓ]
    exact hq3
  exact noA6Comp_of_langSetup S' Nat.prime_five ι hinj hrange _ hconj hT hap h1
    (langSetup_hTame S' hT hap h1)
    (fun i hq =>
      rationalLieType_G2_D4 S' Nat.prime_five (by norm_num) (Or.inl rfl) hT hap h1 hAC i hq)

theorem noA6Comp_triD4 {S : Type} [Group S] [Finite S] (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid) (hq3 : q.p ≠ 3) (hq5 : q.p ≠ 5)
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group) {s : S} (hso : orderOf s = 5) :
    NoA6Comp (MulAut.conj s) := by
  classical
  obtain ⟨K, _, _, σ, hK, hσ, -, ⟨eK⟩⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_catEquiv_trialityD4 q hv
  let e' : S ≃* ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := e.trans eK
  refine NoA6Comp.of_congr e' ?_
  rw [congr_conj_exc]
  set x := e' s with hx
  have hxo : orderOf x = 5 := by rw [hx, MulEquiv.orderOf_eq, hso]
  have hxp : x ^ 5 = 1 := by rw [← hxo]; exact pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hxo
    omega
  have hAC : ringChar (AlgebraicClosure K) = q.p := by
    rw [ringChar_algebraicClosure]
    exact ringChar_eq_of_card_eq_pow (n := q.exponent * 3) q.prime_p
      (by have := q.exponent_pos; omega) (by rw [hK, ← pow_mul])
  have hmon : MonomialToralAt Tag.D4 5 :=
    monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five (by simp) Nat.prime_five
      (by norm_num)
  obtain ⟨p₀, hp₀, hp₀ℓ, hq₀⟩ :=
    exists_setup_prime q.prime_p q.exponent_pos Nat.prime_five (by norm_num) (Ne.symm hq5)
  obtain ⟨S', a, ι, -, -, hT, hap, h1, hinj, hrange, hconj⟩ :=
    exists_langSetup_of_inner_triD4_of_prime q.prime_p q.exponent_pos hK σ hσ Nat.prime_five
      (Ne.symm hq5) hp₀ hp₀ℓ hq₀ hmon x hxp hx1
  have hAC3 : ringChar (AlgebraicClosure K) ≠ 3 := by rw [hAC]; exact hq3
  exact noA6Comp_of_langSetup S' Nat.prime_five ι hinj hrange _ hconj hT hap h1
    (langSetup_hTame_of_prime S' Nat.prime_five
      (natCast_ne_zero_algebraicClosure_of_ne q.prime_p Nat.prime_five hK (Ne.symm hq5))
      (fun h => absurd h (by decide)) hT hap h1)
    (fun i hq =>
      rationalLieType_G2_D4 S' Nat.prime_five (by norm_num) (Or.inr rfl) hT hap h1 hAC3 i hq)

end Catalogue

theorem isQuasisimple_root_of_simple_k324 {D : Type*} [Group D] [IsSimpleGroup D]
    (hnab : ∃ a b : D, a * b ≠ b * a) : CFSG.IsQuasisimple D := by
  obtain ⟨⟨hcomm, hsimp⟩, hc⟩ := isQuasisimple_of_simple_k324 hnab
  let e : D ⧸ center D ≃* D :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
  obtain ⟨a, b, hab⟩ := hnab
  exact ⟨⟨hcomm⟩, hsimp, e.symm a, e.symm b,
    fun h => hab (e.symm.injective (by rw [map_mul, map_mul, h]))⟩

theorem map_normal_centralizer_k324 {S T : Type} [Group S] [Group T] (e : S ≃* T) {s : S}
    {Y : Subgroup S} (hYC : Y ≤ centralizer ({s} : Set S))
    (hYn : (Y.subgroupOf (centralizer ({s} : Set S))).Normal) :
    Y.map (e : S →* T) ≤ centralizer ({e s} : Set T) ∧
      ∀ c ∈ centralizer ({e s} : Set T), ∀ y ∈ Y.map (e : S →* T),
        c * y * c⁻¹ ∈ Y.map (e : S →* T) := by
  have hcs : ∀ c₀ : S, e c₀ ∈ centralizer ({e s} : Set T) → c₀ ∈ centralizer ({s} : Set S) := by
    intro c₀ hc
    rw [mem_centralizer_singleton_iff] at hc ⊢
    apply e.injective
    rw [map_mul, map_mul]
    exact hc
  refine ⟨?_, ?_⟩
  · rintro _ ⟨y₀, hy₀, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have h := mem_centralizer_singleton_iff.1 (hYC hy₀)
    change e y₀ * e s = e s * e y₀
    rw [← map_mul, ← map_mul, h]
  · rintro c hc _ ⟨y₀, hy₀, rfl⟩
    obtain ⟨c₀, rfl⟩ := e.surjective c
    have hc₀ := hcs c₀ hc
    have h1 : (⟨c₀, hc₀⟩ : ↥(centralizer ({s} : Set S))) * ⟨y₀, hYC hy₀⟩ *
        (⟨c₀, hc₀⟩ : ↥(centralizer ({s} : Set S)))⁻¹ ∈ Y.subgroupOf (centralizer ({s} : Set S)) :=
      hYn.conj_mem _ (show (⟨y₀, hYC hy₀⟩ : ↥(centralizer ({s} : Set S))) ∈
        Y.subgroupOf (centralizer ({s} : Set S)) from hy₀) _
    refine ⟨c₀ * y₀ * c₀⁻¹, h1, ?_⟩
    change e (c₀ * y₀ * c₀⁻¹) = e c₀ * e y₀ * (e c₀)⁻¹
    rw [map_mul, map_mul, map_inv]

section ReeF4


theorem false_of_reeF4 {S : Type} [Group S] [Finite S] (m : ℕ)
    (hv : (TauCeti.LieTypeIndex.reeF4 m).Valid)
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨.reeF4 m, hv⟩).Group) {s : S} (hso : orderOf s = 5)
    {Y : Subgroup S} (hYC : Y ≤ centralizer ({s} : Set S))
    (hYn : (Y.subgroupOf (centralizer ({s} : Set S))).Normal) (hY : UC22.IsAlt ↥Y 6) : False := by
  have hR := CFSG.HardMathSupport.Timmesfeld.DefChar.lot_reeTitsModel_twistedF4_of_index m hv e
  obtain ⟨-, a, ha, -, K, _, _, _, hK, ⟨e2⟩⟩ :=
    CFSG.RankThree.PartTwo.Sec4.exists_mulEquiv_reeGamma hR
  have hxo : orderOf (e2 s) = 5 := by rw [MulEquiv.orderOf_eq]; exact hso
  obtain ⟨N, -, -, hcomp, -, hNs⟩ :=
    largeRee_component_chev ha hK Nat.prime_five (by norm_num) _ hxo
  obtain ⟨φ⟩ := hY
  haveI : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  set Y' := Y.map e2.toMonoidHom with hY'
  let eY : ↥Y ≃* ↥Y' := Y.equivMapOfInjective e2.toMonoidHom e2.injective
  haveI : IsSimpleGroup ↥Y' := (eY.symm.trans φ).isSimpleGroup
  have hnab : ∃ a b : ↥Y', a * b ≠ b * a := by
    refine ⟨(eY.symm.trans φ).symm ⟨Equiv.swap 0 1 * Equiv.swap 0 2, by
        rw [Equiv.Perm.mem_alternatingGroup]; decide⟩,
      (eY.symm.trans φ).symm ⟨Equiv.swap 0 1 * Equiv.swap 0 3, by
        rw [Equiv.Perm.mem_alternatingGroup]; decide⟩, fun h => ?_⟩
    rw [← map_mul, ← map_mul] at h
    exact absurd ((eY.symm.trans φ).symm.injective h) (by decide)
  obtain ⟨hY'C, hY'n⟩ := map_normal_centralizer_k324 e2 hYC hYn
  have hsn : (Y'.subgroupOf (centralizer ({e2 s} : Set _))).Normal :=
    ⟨fun n hn g => by
      rw [mem_subgroupOf] at hn ⊢
      exact hY'n g g.2 n hn⟩
  have hY'comp : CFSG.RankThree.PartOne.IsComponentOf (centralizer ({e2 s} : Set _)) Y' :=
    ⟨hY'C, isQuasisimple_root_of_simple_k324 hnab, hsn.isSubnormal⟩
  have hYN := hcomp Y' hY'comp
  have hN1 : N ≠ ⊥ := by
    rw [← hYN]
    exact (Subgroup.nontrivial_iff_ne_bot Y').1 inferInstance
  obtain ⟨-, -, hnA6⟩ := hNs hN1
  exact (hnA6 lieOrderBridge_holds).false
    ((MulEquiv.subgroupCongr hYN).symm.trans (eY.symm.trans φ))

end ReeF4

section Tits


theorem false_of_tits {S : Type} [Group S] [Finite S] (hv : TauCeti.LieTypeIndex.tits.Valid)
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨.tits, hv⟩).Group) {s : S} (hso : orderOf s = 5)
    {Y : Subgroup S} (hYC : Y ≤ centralizer ({s} : Set S)) (hY : UC22.IsAlt ↥Y 6) : False := by
  obtain ⟨f⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv S 2 1
    (CFSG.StandardType.ChevTwo.reeTitsModel_of_tits hv e)
  obtain ⟨φ⟩ := hY
  have hY360 : Nat.card Y = 360 := by
    rw [Nat.card_congr φ.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    decide
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥Y) 3 (by rw [hY360]; norm_num)
  have hyo : orderOf (y : S) = 3 := by rw [Subgroup.orderOf_coe]; exact hy
  have hys : (y : S) * s = s * y := (mem_centralizer_singleton_iff.1 (hYC y.2))
  refine CFSG.RankThree.PartTwo.Sec4.Item434RemTits.mul_ne_mul_of_orderOf (x := f y) (y := f s)
    (by rw [MulEquiv.orderOf_eq]; exact hyo) (Or.inl rfl)
    (by rw [MulEquiv.orderOf_eq]; exact hso) ?_
  rw [← map_mul, ← map_mul, hys]

end Tits

end CFSG.LocalAnalysis.UniquenessCase.UCK
