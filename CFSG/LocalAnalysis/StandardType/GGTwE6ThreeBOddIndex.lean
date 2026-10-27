module

public import CFSG.LocalAnalysis.StandardType.GGTwE6D4GammaLayer
public import CFSG.LocalAnalysis.StandardType.GGLayerNotExcThreeAtTwoE6D4
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleField
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleLang
public import CFSG.LieType.HighestRoot.CentToralPGroup
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem16A8Cnt
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotLeviYSplit
public import CFSG.RankThree.PartOne.KE.ConjRootSpan
public import CFSG.LieType.HighestRoot.CentTrialityMain
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoOddLieDefs
public import CFSG.Quasithin.Background.G64SymCase

public section

namespace CFSG.StandardType.TwE6ThreeB

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartOne.KE (d4Nodes)
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

theorem exists_odd_pow_eq_one_of_mem_torusGroup_of_periodic
    {τ : Tag} {L : Type} [Field L] [CharP L 2]
    (hAlg : ∀ c : L, ∃ n, 0 < n ∧ c ^ (2 ^ n) = c) {t : ModGL τ L}
    (ht : t ∈ torusGroup τ L) : ∃ N, Odd N ∧ t ^ N = 1 := by
  classical
  have hd : t ∈ diagonalGroup := torusGroup_le_diagonalGroup ht
  choose c hc using exists_apply_single_of_mem_diagonalGroup hd
  choose n hn hpow using fun b => hAlg (c b : L)
  haveI : Fintype (Label τ) := Fintype.ofFinite _
  set M := ∏ b, n b with hMdef
  have hM : 0 < M := Finset.prod_pos fun b _ => hn b
  have key : ∀ b, (c b : L) ^ (2 ^ M) = c b := by
    intro b
    obtain ⟨m, hm⟩ : n b ∣ M := Finset.dvd_prod_of_mem _ (Finset.mem_univ b)
    rw [hm]
    clear hm
    induction m with
    | zero => simp
    | succ m ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, hpow b]
  have key1 : ∀ b, (c b : L) ^ (2 ^ M - 1) = 1 := by
    intro b
    have h := key b
    rw [← Nat.sub_add_cancel (Nat.one_le_two_pow (n := M)), pow_succ] at h
    exact mul_right_cancel₀ (c b).ne_zero (h.trans (one_mul _).symm)
  refine ⟨2 ^ M - 1, ?_, ?_⟩
  · obtain ⟨k, hk⟩ : ∃ k, 2 ^ M = 2 * k ∧ 1 ≤ k :=
      ⟨2 ^ (M - 1), by rw [← pow_succ']; congr 1; omega, Nat.one_le_two_pow⟩
    exact ⟨k - 1, by omega⟩
  · refine Units.ext (end_ext_single fun b => ?_)
    have hp : ∀ N : ℕ, ((t ^ N : ModGL τ L) : Module.End L (RootModule τ L))
        (Finsupp.single b 1) = ((c b : L) ^ N) • Finsupp.single b 1 := by
      intro N
      induction N with
      | zero => simp
      | succ N ih =>
        rw [pow_succ, Units.val_mul, Module.End.mul_apply, hc, map_smul, ih, smul_smul, pow_succ,
          mul_comm]
    rw [hp, key1, one_smul, Units.val_one, Module.End.one_apply]

theorem mem_rootSpan_of_mem_toralCentralizer_of_two_pow
    {τ : Tag} {L : Type} [Field L]
    [CharP L 2] (hAlg : ∀ c : L, ∃ n, 0 < n ∧ c ^ (2 ^ n) = c) {a : Fin τ.rank → Lˣ}
    (ha : ∀ i, a i ^ 3 = 1) {x : ModGL τ L} (hx : x ∈ toralCentralizer τ L a) {k : ℕ}
    (hxk : x ^ (2 ^ k) = 1) : x ∈ rootSpan τ L (kernelRoots (rootCharHom a)) := by
  have hxR : x ∈ toralRootGroup τ L a :=
    CFSG.LieType.HighestRoot.mem_toralRootGroup_of_pow_eq_one Nat.prime_three ha hx
      (Nat.Coprime.pow_left _ (by decide)) hxk
  show x ∈ rootSpan τ L (rootCharKernel a)
  have hT := CFSG.Quasithin.SmithCurtis.Chev.torusGroup_le_normalizer_rootSpan (K := L)
    (S := rootCharKernel a) fun _ hα => hα.1
  have hx' : x ∈ ((torusGroup τ L ⊔ rootSpan τ L (rootCharKernel a) : Subgroup (ModGL τ L)) :
      Set (ModGL τ L)) := hxR
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hT] at hx'
  obtain ⟨t, ht, s, hs, rfl⟩ := hx'
  obtain ⟨s', hs', h⟩ := CFSG.Quasithin.H13.Lem16A8.exists_pow_mul_eq (hT ht) hs (2 ^ k)
  rw [h] at hxk
  have htp : t ^ (2 ^ k) ∈ rootSpan τ L (rootCharKernel a) := by
    rw [eq_inv_of_mul_eq_one_left hxk]
    exact inv_mem hs'
  obtain ⟨N, hNodd, hN⟩ := exists_odd_pow_eq_one_of_mem_torusGroup_of_periodic hAlg ht
  have hcop : Nat.Coprime (2 ^ k) (orderOf t) :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hN)
      (Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hNodd))
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  have htS : t ∈ rootSpan τ L (rootCharKernel a) := by
    rw [← hm]
    exact pow_mem htp m
  exact mul_mem htS hs

theorem mem_CQ_of_frobGL_eq_self
    {τ : Tag} {L : Type} [Field L] {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} (i : KernelComponent χ) (σ : L ≃+* L)
    (hσ : ∀ c, σ c = c → c ≠ 0 → c = 1) {y : ModGL τ L}
    (hy : y ∈ rootSpan τ L (componentRoots χ i)) (hfix : frobGL σ y = y) : y ∈ CQ σ i := by
  have hy' : y ∈ unionRootSpan L χ ({i} : Set (KernelComponent χ)) := by
    show y ∈ rootSpan τ L (unionRoots χ ({i} : Set (KernelComponent χ)))
    rw [unionRoots_singleton]; exact hy
  obtain ⟨t, ht, x, hx, rfl, htf⟩ :=
    exists_decomp (σ := σ) hy' (one_mem _) (by rw [hfix, one_mul])
  have hdiag : t ∈ diagonalGroup := torusGroup_le_diagonalGroup ht.2
  have ht1 : t = 1 := by
    refine Units.ext (end_ext_single fun b => ?_)
    obtain ⟨c, hc⟩ := exists_apply_single_of_mem_diagonalGroup hdiag b
    have h2 : ((frobGL σ t : ModGL τ L) : Module.End L (RootModule τ L)) (Finsupp.single b 1) =
        (σ c : L) • Finsupp.single b 1 := by
      show entrywise σ.toRingHom (t : Module.End L (RootModule τ L)) (Finsupp.single b 1) = _
      rw [entrywise_single, hc]
      ext l
      by_cases hl : b = l
      · subst hl; simp
      · simp [Finsupp.single_eq_of_ne hl]
    rw [htf, one_mul, hc] at h2
    have hcσ : σ (c : L) = c := by
      have := congrArg (fun v => v b) h2
      simpa using this.symm
    have h1 : (c : L) = 1 := hσ _ hcσ c.ne_zero
    rw [hc, h1, one_smul]
    rfl
  rw [ht1, one_mul]
  exact hx

theorem exists_rootSpan_inf_model_eq_map_CQ
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
    {p₀ : ℕ} (S : LangSetup τ L p₀) (hq : S.D.q = 2) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[1])) :
    ∃ (σ : L ≃+* L) (z : ModGL τ L), (∀ c, σ c = c ^ 2) ∧
      rootSpan τ L (componentRoots (rootCharHom a) i) ⊓ S.D.model =
        (CQ σ i).map (MulAut.conj z).toMonoidHom := by
  obtain ⟨σ, z, hσ, hnorm, hz⟩ := exists_untwistT S hT i one_pos hinner
  have hσ2 : ∀ c, σ c = c ^ 2 := fun c => by rw [hσ, hq, pow_one]
  refine ⟨σ, z, hσ2, ?_⟩
  have hσF : ∀ c : L, σ c = c → c ≠ 0 → c = 1 := by
    intro c hc h0
    rw [hσ2, sq] at hc
    exact mul_left_cancel₀ h0 (hc.trans (mul_one c).symm)
  have hstep : ∀ g, iterHom S.D.step 1 g = S.D.step g := fun _ => rfl
  ext y
  constructor
  · rintro ⟨hyU, hyM⟩
    have hy : z * (z⁻¹ * y * z) * z⁻¹ = y := by group
    have hg : z⁻¹ * y * z ∈ rootSpan τ L (componentRoots (rootCharHom a) i) :=
      (hnorm i _).2 (by rw [hy]; exact hyU)
    refine ⟨z⁻¹ * y * z, mem_CQ_of_frobGL_eq_self i σ hσF hg ?_, ?_⟩
    · have h1 := hz _ hg
      rw [hy, hstep] at h1
      have hfix : S.D.step y = y := hyM.2
      rw [hfix] at h1
      calc frobGL σ (z⁻¹ * y * z) = z⁻¹ * (z * frobGL σ (z⁻¹ * y * z) * z⁻¹) * z := by group
        _ = z⁻¹ * y * z := by rw [← h1]
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact hy
  · rintro ⟨g, hg, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have hgU : g ∈ rootSpan τ L (componentRoots (rootCharHom a) i) := CQ_le_rootSpan σ i hg
    have hU : z * g * z⁻¹ ∈ rootSpan τ L (componentRoots (rootCharHom a) i) := (hnorm i g).1 hgU
    refine ⟨hU, (iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α :
      rootSpan τ L _ ≤ adjointGroup τ L) hU, ?_⟩
    have h1 := hz g hgU
    rw [hstep, frobGL_eq_self_of_mem_CQ σ i hg] at h1
    exact h1

theorem isSimpleGroup_CQ_d4
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {a : Fin Tag.E6.rank → Lˣ}
    (i : KernelComponent (rootCharHom a)) (σ : L ≃+* L) (hσ : ∀ c, σ c = c ^ 2)
    (v : WeylGroup Tag.E6)
    (hv : componentRoots (rootCharHom a) i =
      (fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6)) :
    IsSimpleGroup (CQ σ i) ∧ Group.IsPerfect (CQ σ i) ∧ LieModel (CQ σ i) .POmegaPlus 4 2 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hfin, hcard⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.finite_card_fixSubfield (r := 2) (n := 1)
      one_pos σ (fun c => by rw [hσ, pow_one])
  haveI : Finite (fixSubfield σ) := hfin
  haveI : CharP (fixSubfield σ) 2 :=
    (RingHom.charP_iff (fixSubfield σ).subtype (fixSubfield σ).subtype.injective 2).mpr ‹CharP L 2›
  have hCQ := CQ_eq_map (i := i) σ
  let e1 : componentRootSpan (fixSubfield σ) (rootCharHom a) i ≃* CQ σ i :=
    (Subgroup.equivMapOfInjective _ _ (baseChangeGL_injective (fixSubfield σ).subtype)).trans
      (MulEquiv.subgroupCongr hCQ.symm)
  have hset : (CFSG.LieType.Chevalley.C2E6Std.setD : Set (Fin Tag.E6.rank)) = d4Nodes Tag.E6 := by
    ext j
    change j ∈ ({1, 2, 3, 4} : Set (Fin 6)) ↔ 1 ≤ j.val ∧ j.val ≤ 4
    fin_cases j <;> simp
  have hd4 : CFSG.SeitzReduction.TwistedE6Pilot.d4Levi (fixSubfield σ) =
      rootSpan Tag.E6 (fixSubfield σ) (parabolicRoots Tag.E6 (d4Nodes Tag.E6)) := by
    show subsystemGroup Tag.E6 (fixSubfield σ)
      (CFSG.LieType.Chevalley.C2E6Std.setD : Set (Fin Tag.E6.rank)) = _
    rw [hset]
    exact subsystemGroup_eq_rootSpan _
  have h2 : componentRootSpan (fixSubfield σ) (rootCharHom a) i =
      (CFSG.SeitzReduction.TwistedE6Pilot.d4Levi (fixSubfield σ)).map
        (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) (fixSubfield σ) v)).toMonoidHom := by
    show rootSpan Tag.E6 (fixSubfield σ) (componentRoots (rootCharHom a) i) = _
    rw [hv, ← CFSG.RankThree.PartOne.KE.map_conj_rootSpan v (fun γ hγ => hγ.1), hd4]
  let e2 : CFSG.SeitzReduction.TwistedE6Pilot.d4Levi (fixSubfield σ) ≃*
      componentRootSpan (fixSubfield σ) (rootCharHom a) i :=
    (Subgroup.equivMapOfInjective _ _ (MulAut.conj _).injective).trans
      (MulEquiv.subgroupCongr h2.symm)
  let e := e2.trans e1
  haveI := CFSG.SeitzReduction.TwistedE6Pilot.isSimpleGroup_d4Levi (K := fixSubfield σ)
  haveI := CFSG.SeitzReduction.TwistedE6Pilot.isPerfect_d4Levi (K := fixSubfield σ)
  exact ⟨e.symm.isSimpleGroup, Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective,
    LieModel.of_mulEquiv e
    (CFSG.SeitzReduction.TwistedE6Pilot.lieModel_d4Levi (K := fixSubfield σ) le_rfl
      (by rw [hcard, pow_one]))⟩

theorem twE6_threeB_rationalComponent_of_twistInner
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p₀ : ℕ} (S : LangSetup Tag.E6 L p₀) (hq : S.D.q = 2) (hAlg : S.IsAlgebraic)
    {a : Fin Tag.E6.rank → Lˣ} (hap : ∀ i, a i ^ 3 = 1) (h1 : rootDiagUnit Tag.E6 a ≠ 1)
    (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus)
    (hall : (kernelRoots (rootCharHom a)).ncard = 24)
    (hinK : twistInner (kernelRoots (rootCharHom a))
      ((S.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[1]))
    (i : KernelComponent (rootCharHom a)) :
    rationalComponent S.ρ S.Γ (rootCharHom a) i =
        rootSpan Tag.E6 L (kernelRoots (rootCharHom a)) ⊓ S.D.model ∧
      IsSimpleGroup (rationalComponent S.ρ S.Γ (rootCharHom a) i) ∧
      LieModel (rationalComponent S.ρ S.Γ (rootCharHom a) i) .POmegaPlus 4 2 1 ∧
      Subgroup.center (rationalComponent S.ρ S.Γ (rootCharHom a) i) = ⊥ ∧
      (∀ x ∈ S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.E6 a}, ∀ k : ℕ, x ^ (2 ^ k) = 1 →
        x ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i) ∧
      Odd ((rationalComponent S.ρ S.Γ (rootCharHom a) i).subgroupOf
        (S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.E6 a})).index := by
  classical
  have h3 : ((3 : ℕ) : L) ≠ 0 := by
    rw [show ((3 : ℕ) : L) = 1 + 2 by norm_num, CharTwo.two_eq_zero, add_zero]
    exact one_ne_zero
  have hceq : componentRoots (rootCharHom a) i = kernelRoots (rootCharHom a) :=
    d4t2_class_eq_kernel h3 hap hall i
  have hker := rho_mem_kernelRoots_of_mem_torus S hT
  have hρmem : ∀ γ ∈ componentRoots (rootCharHom a) i,
      S.ρ γ ∈ componentRoots (rootCharHom a) i := by
    intro γ hγ
    rw [hceq] at hγ ⊢
    exact hker γ hγ
  obtain ⟨hrank, hc⟩ := d4t2_class_of_card h3 hap hall i
  have hin1 : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[1]) := by
    rw [hceq]; exact hinK
  obtain ⟨v, hv, -⟩ :=
    CFSG.StandardType.ExcThreeAtTwo.exists_pinned_d4Class_E6 S hT hap h1 i hrank hc
  obtain ⟨σ, z, hσ, hY⟩ := exists_rootSpan_inf_model_eq_map_CQ S hq hT i hin1
  obtain ⟨hsimp, hperf, hlie⟩ := isSimpleGroup_CQ_d4 i σ hσ v hv
  set Y := rootSpan Tag.E6 L (componentRoots (rootCharHom a) i) ⊓ S.D.model with hYdef
  let eY : CQ σ i ≃* Y :=
    (Subgroup.equivMapOfInjective _ _ (MulAut.conj z).injective).trans
      (MulEquiv.subgroupCongr hY.symm)
  haveI : IsSimpleGroup Y := eY.symm.isSimpleGroup
  have hperfY : Group.IsPerfect Y :=
    Group.IsPerfect.ofSurjective (f := eY.toMonoidHom) eY.surjective
  have hYY : ⁅Y, Y⁆ = Y := Subgroup.isPerfect_iff.mp hperfY
  have hΓM : S.Γ ≤ S.D.model := Subgroup.commutator_le.mpr fun g hg h hh => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hg hh) (inv_mem hg)) (inv_mem hh)
  have hYΓ : Y ≤ S.Γ := by
    rw [← hYY]
    exact Subgroup.commutator_mono inf_le_right inf_le_right
  have hrr : rationalRoots S.ρ (rootCharHom a) i = componentRoots (rootCharHom a) i := by
    ext γ
    constructor
    · rintro ⟨k, δ, hδ, rfl⟩
      induction k with
      | zero => exact hδ
      | succ k ih => rw [Function.iterate_succ_apply']; exact hρmem _ ih
    · exact fun h => ⟨0, γ, h, rfl⟩
  have hspan : rationalSpan S.ρ S.Γ (rootCharHom a) i = Y := by
    show rootSpan Tag.E6 L (rationalRoots S.ρ (rootCharHom a) i) ⊓ S.Γ = Y
    rw [hrr]
    exact le_antisymm (inf_le_inf_left _ hΓM) fun y hy => ⟨hy.1, hYΓ hy⟩
  have hR : rationalComponent S.ρ S.Γ (rootCharHom a) i = Y := by
    show ⁅rationalSpan S.ρ S.Γ (rootCharHom a) i, rationalSpan S.ρ S.Γ (rootCharHom a) i⁆ = Y
    rw [hspan, hYY]
  have hAlg' : ∀ c : L, ∃ n, 0 < n ∧ c ^ (2 ^ n) = c := fun c => by
    obtain ⟨n, hn, h⟩ := hAlg c
    exact ⟨n, hn, by rwa [hq] at h⟩
  have htwo : ∀ x ∈ S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.E6 a}, ∀ k : ℕ,
      x ^ (2 ^ k) = 1 → x ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i := by
    intro x hx k hxk
    have hxM := hΓM hx.1
    have hxC : x ∈ toralCentralizer Tag.E6 L a := ⟨hxM.1, hx.2⟩
    have hxU := mem_rootSpan_of_mem_toralCentralizer_of_two_pow hAlg' hap hxC hxk
    rw [hR]
    exact ⟨by rw [hceq]; exact hxU, hxM⟩
  have hcenter : Subgroup.center Y = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Y) with h | h
    · exact h
    · exfalso
      have hbot : ⁅(⊤ : Subgroup Y), (⊤ : Subgroup Y)⁆ = (⊥ : Subgroup Y) := by
        refine (Subgroup.commutator_le.mpr fun g _ g' _ => ?_).antisymm bot_le
        have hg : g ∈ Subgroup.center Y := h ▸ Subgroup.mem_top g
        rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
        exact (Subgroup.mem_center_iff.mp hg g').symm
      have htop := hperfY.commutator_eq_top
      rw [commutator_def] at htop
      rw [htop] at hbot
      exact bot_ne_top hbot.symm
  refine ⟨by rw [hR, hYdef, hceq], by rw [hR]; infer_instance,
    by rw [hR]; exact LieModel.of_mulEquiv eY hlie, by rw [hR]; exact hcenter, htwo, ?_⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite S.D.model := S.finite
  haveI : Finite (S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.E6 a} :
      Subgroup (ModGL Tag.E6 L)) :=
    Finite.of_injective (Subgroup.inclusion (inf_le_left.trans hΓM))
      (Subgroup.inclusion_injective _)
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2
    (S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.E6 a} : Subgroup (ModGL Tag.E6 L))))
  have hPle : (P : Subgroup _) ≤ (rationalComponent S.ρ S.Γ (rootCharHom a) i).subgroupOf
      (S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.E6 a}) := by
    intro g hg
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨g, hg⟩
    have hk' : ((g : ModGL Tag.E6 L)) ^ (2 ^ k) = 1 := by
      have := congrArg Subtype.val (congrArg Subtype.val hk)
      simpa using this
    exact Subgroup.mem_subgroupOf.mpr (htwo g g.2 k hk')
  have hnd := P.not_dvd_index
  exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp fun h =>
    hnd (h.trans (Subgroup.index_dvd_of_le hPle)))

end CFSG.StandardType.TwE6ThreeB

end
