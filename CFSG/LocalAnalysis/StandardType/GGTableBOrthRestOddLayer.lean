module

public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestOddCount
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthogonalEndNode
public import CFSG.RankThree.PartOne.KC.OrthogonalDerivedInLayer
public import CFSG.RankThree.PartOne.KC.OrthogonalFixedDerived
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusTenBasic
public import CFSG.RankThree.PartOne.S11d.OrthCyclic
public import CFSG.GroupTheory.WeirSylow.OrthogonalModels
public import CFSG.ClassicalGroups.Orthogonal.Simple
public import CFSG.RankThree.PartOne.KC.OrthogonalInnerPlane
public import CFSG.RankThree.PartOne.S11d.LieCentralizerBlock
public import CFSG.RankThree.PartOne.S11d.LieCentralizerOrth
public import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic
public import CFSG.RankThree.Theta.ThreeComponentOrbitCover

public section

namespace CFSG.StandardType

namespace OrthRestOdd

open Module Polynomial CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.Classical2

section Primary

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]

theorem fixedSpace_eq_lit (x : V ≃ₗ[K] V) :
    fixedSpace x = CFSG.RankThree.PartOne.LIT.fixedSpace x := by
  ext v
  rw [mem_fixedSpace, CFSG.RankThree.PartOne.LIT.mem_fixedSpace]

theorem aeval_apply_of_fixed {x : V ≃ₗ[K] V} (f : K[X]) {v : V} (hv : x v = v) :
    aeval x.toLinearMap f v = f.eval 1 • v := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg => rw [map_add, LinearMap.add_apply, hf, hg, eval_add, add_smul]
  | monomial n c =>
    have hpow : ∀ k : ℕ, (x.toLinearMap ^ k) v = v := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih => rw [pow_succ, Module.End.mul_apply, LinearEquiv.coe_toLinearMap, hv, ih]
    rw [aeval_monomial, Module.End.mul_apply, hpow, eval_monomial, one_pow, mul_one,
      Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply]

theorem aeval_mem_commSpace {x : V ≃ₗ[K] V} (f : K[X]) {v : V}
    (hv : v ∈ CFSG.RankThree.PartOne.LIT.commSpace x) :
    aeval x.toLinearMap f v ∈ CFSG.RankThree.PartOne.LIT.commSpace x := by
  obtain ⟨y, rfl⟩ := CFSG.RankThree.PartOne.LIT.mem_commSpace.mp hv
  refine CFSG.RankThree.PartOne.LIT.mem_commSpace.mpr ⟨aeval x.toLinearMap f y, ?_⟩
  have hc : Commute x.toLinearMap (aeval x.toLinearMap f) :=
    commute_aeval (Commute.refl x.toLinearMap) f
  have h1 := LinearMap.congr_fun hc.eq y
  simp only [Module.End.mul_apply, LinearEquiv.coe_toLinearMap] at h1
  rw [map_sub, ← h1]

variable [FiniteDimensional K V]

theorem eval_one_ne_zero {x : V ≃ₗ[K] V} {h : K[X]} (hh : h ∈ primaryFactors x.toLinearMap)
    (hne : h ≠ X - 1) : h.eval 1 ≠ 0 := by
  obtain ⟨u, w, huw⟩ := isCoprime_of_irreducible_monic_ne irreducible_X_sub_one
    (irreducible_of_mem_primaryFactors hh) (monic_X_sub_one) (monic_of_mem_primaryFactors hh)
    (Ne.symm hne)
  intro h0
  have := congrArg (eval 1) huw
  simp only [eval_add, eval_mul, eval_sub, eval_X, eval_one, sub_self, mul_zero, h0,
    zero_add] at this
  exact zero_ne_one this

variable {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

theorem primaryComponent_le_commSpace (hx : OddOrderIsometry Q p x) {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) (hne : h ≠ X - 1) :
    primaryComponent x.toLinearMap h ≤ CFSG.RankThree.PartOne.LIT.commSpace x := by
  intro v hv
  have hc := CFSG.RankThree.PartOne.LIT.isCompl_fixedSpace_commSpace hx.cast_ne_zero
    hx.pow_eq_one
  have hvs : v ∈ CFSG.RankThree.PartOne.LIT.fixedSpace x ⊔
      CFSG.RankThree.PartOne.LIT.commSpace x := by rw [hc.sup_eq_top]; trivial
  obtain ⟨v₀, hv₀, v₁, hv₁, rfl⟩ := Submodule.mem_sup.mp hvs
  have hfix := CFSG.RankThree.PartOne.LIT.mem_fixedSpace.mp hv₀
  have h0 : aeval x.toLinearMap h (v₀ + v₁) = 0 := mem_primaryComponent.mp hv
  rw [map_add, aeval_apply_of_fixed h hfix] at h0
  have hmem : h.eval 1 • v₀ ∈ CFSG.RankThree.PartOne.LIT.fixedSpace x ⊓
      CFSG.RankThree.PartOne.LIT.commSpace x := by
    refine ⟨Submodule.smul_mem _ _ hv₀, ?_⟩
    rw [eq_neg_of_add_eq_zero_left h0]
    exact Submodule.neg_mem _ (aeval_mem_commSpace h hv₁)
  rw [hc.inf_eq_bot, Submodule.mem_bot] at hmem
  have hv₀0 : v₀ = 0 := (smul_eq_zero.mp hmem).resolve_left (eval_one_ne_zero hh hne)
  rw [hv₀0, zero_add]
  exact hv₁

theorem two_le_natDegree (hx : OddOrderIsometry Q p x) (hK1 : ∀ c : K, c ^ p = 1 → c = 1)
    {h : K[X]} (hh : h ∈ primaryFactors x.toLinearMap) (hne : h ≠ X - 1) : 2 ≤ h.natDegree := by
  have hirr := irreducible_of_mem_primaryFactors hh
  by_contra hlt
  have hdeg : h.degree = 1 := by
    have h1 : 0 < h.natDegree := Irreducible.natDegree_pos hirr
    rw [Polynomial.degree_eq_natDegree hirr.ne_zero]
    norm_cast
    omega
  obtain ⟨c, hc⟩ := Polynomial.exists_root_of_degree_eq_one hdeg
  have hdvd : h ∣ X ^ p - 1 :=
    (mem_primaryFactors.mp hh).2.2.trans (minpoly.dvd K _ hx.aeval_X_pow_sub_one)
  have hc' : (X ^ p - 1 : K[X]).IsRoot c := Polynomial.IsRoot.dvd hc hdvd
  have hcp : c ^ p = 1 := by
    have := hc'.eq_zero
    simp only [eval_sub, eval_pow, eval_X, eval_one] at this
    exact sub_eq_zero.mp this
  apply eval_one_ne_zero hh hne
  rw [← hK1 c hcp]
  exact hc.eq_zero

theorem primaryMultiplicity_eq_one (hx : OddOrderIsometry Q p x)
    (hK1 : ∀ c : K, c ^ p = 1 → c = 1)
    (h2 : finrank K (CFSG.RankThree.PartOne.LIT.commSpace x) = 2) {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) (hne : h ≠ X - 1) :
    primaryMultiplicity x.toLinearMap h = 1 := by
  have : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  have hdim : finrank K (primaryComponent x.toLinearMap h) =
      h.natDegree * primaryMultiplicity x.toLinearMap h := finrank_primaryComponent x.toLinearMap h
  have hle := Submodule.finrank_mono (primaryComponent_le_commSpace hx hh hne)
  have hpos : 1 ≤ finrank K (primaryComponent x.toLinearMap h) :=
    Submodule.one_le_finrank_iff.mpr (primaryComponent_ne_bot hx.squarefree_minpoly hh)
  have hdeg := two_le_natDegree hx hK1 hh hne
  obtain ⟨m, hm⟩ : ∃ m, primaryMultiplicity x.toLinearMap h = m := ⟨_, rfl⟩
  rw [hm] at hdim ⊢
  rw [h2] at hle
  rw [hdim] at hle hpos
  rcases Nat.lt_or_ge m 2 with hm2 | hm2
  · rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0, mul_zero] at hpos
      omega
    · omega
  · have : 2 * 2 ≤ h.natDegree * m := Nat.mul_le_mul hdeg hm2
    omega

theorem specialProduct_eq_bot (hx : OddOrderIsometry Q p x) (hK1 : ∀ c : K, c ^ p = 1 → c = 1)
    (h2 : finrank K (CFSG.RankThree.PartOne.LIT.commSpace x) = 2) {Rep : Finset K[X]}
    (hRep : IsOrbitRepresentatives x Rep) : specialProduct Q x Rep = ⊥ := by
  refine eq_bot_iff.mpr (iSup₂_le fun h hh => iSup_le fun hne => ?_)
  have hh' := hRep.1 hh
  have : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh'⟩
  rw [hx.specialBlock_eq_bot_of_finrank_eq_one hh' (primaryMultiplicity_eq_one hx hK1 h2 hh' hne)]

theorem commutator_mem_supportedFixedDerived (hx : OddOrderIsometry Q p x)
    (hK1 : ∀ c : K, c ^ p = 1 → c = 1)
    (h2 : finrank K (CFSG.RankThree.PartOne.LIT.commSpace x) = 2) {g h : V ≃ₗ[K] V}
    (hg : g ∈ isometryCentralizer Q x) (hh : h ∈ isometryCentralizer Q x) :
    g * h * g⁻¹ * h⁻¹ ∈ supportedFixedDerived Q x := by
  obtain ⟨Rep, hRep⟩ := hx.exists_orbitRepresentatives
  have hmem : g * h * g⁻¹ * h⁻¹ ∈ ⁅isometryCentralizer Q x, isometryCentralizer Q x⁆ := by
    rw [← commutatorElement_def]
    exact Subgroup.commutator_mem_commutator hg hh
  obtain ⟨f, hf, j, hj, hjf⟩ := hx.exists_decomposition_of_mem_commutator hRep hmem
  rw [specialProduct_eq_bot hx hK1 h2 hRep, Subgroup.mem_bot] at hj
  rw [hjf, hj, one_mul]
  exact hf

end Primary

section Fixed

variable {K : Type} [Field K] [Finite K] [CharP K 2] {W : Type} [AddCommGroup W] [Module K W]
  [FiniteDimensional K W]

omit [Finite K] [FiniteDimensional K W] in
theorem polar_self_eq_zero (R : QuadraticForm K W) (w : W) : QuadraticMap.polar R w w = 0 := by
  rw [QuadraticMap.polar_self, two_smul, CharTwo.add_self_eq_zero]

omit [Finite K] in
theorem even_finrank_of_regular (R : QuadraticForm K W)
    (hR : (QuadraticMap.polarBilin R).Nondegenerate) : Even (finrank K W) :=
  LinearMap.BilinForm.IsAlt.even_finrank (B := QuadraticMap.polarBilin R)
    (fun w => by rw [QuadraticMap.polarBilin_apply_apply]; exact polar_self_eq_zero R w) hR

theorem exists_totallySingular_three (R : QuadraticForm K W)
    (hR : (QuadraticMap.polarBilin R).Nondegenerate) (hW : 8 ≤ finrank K W) :
    ∃ T : Submodule K W, finrank K T = 3 ∧ ∀ u ∈ T, R u = 0 := by
  obtain ⟨k, hk⟩ := even_finrank_of_regular R hR
  have hdim : finrank K W = 2 * k := by omega
  rcases CFSG.GroupTheory.WeirSylow.exists_isometry_quadPlus_or_quadMinus R hR (n := k)
      (by omega) hdim with he | ⟨b, c, hirr, he⟩
  · obtain ⟨e⟩ := he
    obtain ⟨-, T, hT3, hT0⟩ := CFSG.ClassicalGroups.Orthogonal.regular_quadPlus (K := K)
      (n := k) (by omega)
    refine ⟨T.map e.symm.toLinearEquiv.toLinearMap, ?_, ?_⟩
    · rw [LinearEquiv.finrank_map_eq, hT3]
    · rintro _ ⟨y, hy, rfl⟩
      change R (e.symm y) = 0
      rw [QuadraticMap.IsometryEquiv.map_app]
      exact hT0 y hy
  · obtain ⟨e⟩ := he
    obtain ⟨-, T, hT3, hT0⟩ := CFSG.ClassicalGroups.Orthogonal.regular_quadMinus (K := K)
      (n := k) (by omega) hirr
    refine ⟨T.map e.symm.toLinearEquiv.toLinearMap, ?_, ?_⟩
    · rw [LinearEquiv.finrank_map_eq, hT3]
    · rintro _ ⟨y, hy, rfl⟩
      change R (e.symm y) = 0
      rw [QuadraticMap.IsometryEquiv.map_app]
      exact hT0 y hy

omit [Finite K] [FiniteDimensional K W] in
theorem scalars_subgroupOf_orthDerived_eq_bot (R : QuadraticForm K W)
    (hR : (QuadraticMap.polarBilin R).Nondegenerate) [Nontrivial W] :
    (CFSG.ClassicalGroups.Orthogonal.scalars K W).subgroupOf (orthDerived R) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro g hg
  obtain ⟨c, hc⟩ :=
    CFSG.ClassicalGroups.Orthogonal.mem_scalars.mp (Subgroup.mem_subgroupOf.mp hg)
  have hgO := CFSG.RankThree.PartOne.KCOrthogonal.orthDerived_le_orthogonalGroup g.2
  obtain ⟨w, hw⟩ : ∃ w : W, R w ≠ 0 := by
    by_contra hall
    push Not at hall
    obtain ⟨v, hv⟩ := exists_ne (0 : W)
    apply hv
    refine hR.1 v fun u => ?_
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, hall, hall, hall, sub_zero,
      sub_zero]
  have h1 := (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hgO) w
  rw [hc, QuadraticMap.map_smul, smul_eq_mul] at h1
  have hc2 : c * c = 1 := by
    have := mul_right_cancel₀ hw (h1.trans (one_mul _).symm)
    exact this
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h3 : (c - 1) ^ 2 = 0 := by linear_combination hc2 - (c - 1) * h2
  have hc1 : c = 1 := sub_eq_zero.mp ((pow_eq_zero_iff (n := 2) (by norm_num)).mp h3)
  apply Subtype.ext
  refine LinearEquiv.ext fun v => ?_
  rw [hc, hc1, one_smul]
  rfl

theorem orthDerived_facts (R : QuadraticForm K W) (hR : (QuadraticMap.polarBilin R).Nondegenerate)
    (hW : 6 ≤ finrank K W) :
    CFSG.IsQuasisimple (orthDerived R) ∧ Subgroup.center (orthDerived R) = ⊥ ∧
      ∀ g ∈ TauCeti.QuadraticMap.orthogonalGroup R, ∀ n : ℕ, Odd n → g ^ n = 1 →
        g ∈ orthDerived R := by
  have : Nontrivial W := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  by_cases hT : ∃ T : Submodule K W, finrank K T = 3 ∧ ∀ u ∈ T, R u = 0
  · obtain ⟨-, hcenter, -⟩ :=
      CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hR hT
    refine ⟨isQuasisimple_orthDerived hR hT, ?_, fun g hg n hn hgn =>
      CFSG.RankThree.PartOne.mem_orthDerived_of_pow_eq_one hR hT hn hg hgn⟩
    rw [hcenter, scalars_subgroupOf_orthDerived_eq_bot R hR]
  · push Not at hT
    obtain ⟨k, hk⟩ := even_finrank_of_regular R hR
    have h6 : finrank K W = 6 := by
      by_contra h6
      obtain ⟨T, hT3, hT0⟩ := exists_totallySingular_three R hR (by omega)
      obtain ⟨u, hu, hu0⟩ := hT T hT3
      exact hu0 (hT0 u hu)
    obtain ⟨hq, hc⟩ := CFSG.SeitzReduction.OmegaPilot.isQuasisimple_orthDerived_of_six hR h6 hT
    refine ⟨hq, hc, fun g hg n hn hgn => ?_⟩
    exact CFSG.SeitzReduction.OmegaPilot.omegaGroup_le_orthDerived_of_six hR h6 hT
      (CFSG.RankThree.PartOne.mem_omegaGroup_of_pow_eq_one hR hn hg hgn)

end Fixed

section EndNode

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

omit [Finite K] in
theorem natCast_ne_zero_of_odd {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : (p : K) ≠ 0 := by
  intro h
  have := (CharP.cast_eq_zero_iff K 2 p).mp h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp this).symm

theorem mem_zpowers_of_fixes (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {A : Subgroup (orthDerived Q)}
    (hA : CFSG.Assembly.IsElemAbelian p A) {t : orthDerived Q} (htA : t ∈ A) (ht1 : t ≠ 1)
    (ht2 : finrank K (CFSG.RankThree.PartOne.LIT.commSpace (t : V ≃ₗ[K] V)) = 2)
    {s : orthDerived Q} (hs : s ∈ A)
    (hsfix : ∀ w ∈ CFSG.RankThree.PartOne.LIT.fixedSpace (t : V ≃ₗ[K] V), (s : V ≃ₗ[K] V) w = w) :
    s ∈ Subgroup.zpowers t := by
  classical
  have hpK : (p : K) ≠ 0 := natCast_ne_zero_of_odd hp hp2
  set x : V ≃ₗ[K] V := ↑t with hxdef
  set F := CFSG.RankThree.PartOne.LIT.fixedSpace x with hF
  let E₀ : Subgroup (V ≃ₗ[K] V) :=
    A.map (orthDerived Q).subtype ⊓ fixingSubgroup (V ≃ₗ[K] V) (F : Set V)
  have hmemE : ∀ {g : V ≃ₗ[K] V}, g ∈ E₀ ↔ g ∈ A.map (orthDerived Q).subtype ∧ ∀ w ∈ F, g w = w :=
    fun {g} => by rw [Subgroup.mem_inf, mem_fixingSubgroup_iff]; rfl
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have hE : IsoGroup (QuadraticMap.polarBilin Q) p E₀ :=
    { sep := hQ.1
      alt := fun v => by rw [QuadraticMap.polarBilin_apply_apply]; exact polar_self_eq_zero Q v
      comm := by
        intro g hg h hh
        obtain ⟨⟨a, ha, rfl⟩, -⟩ := hmemE.mp hg
        obtain ⟨⟨b, hb, rfl⟩, -⟩ := hmemE.mp hh
        exact congrArg Subtype.val (TableB.IsElemAbelian.comm hA ha hb)
      pow := by
        intro g hg
        obtain ⟨⟨a, ha, rfl⟩, -⟩ := hmemE.mp hg
        rw [← map_pow, hA.2 a ha, map_one]
      pres := by
        intro g hg u w
        obtain ⟨⟨a, ha, rfl⟩, -⟩ := hmemE.mp hg
        rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polarBilin_apply_apply]
        exact TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup
          (CFSG.RankThree.PartOne.KCOrthogonal.orthDerived_le_orthogonalGroup a.2) u w }
  have hxE : x ∈ E₀ := hmemE.mpr ⟨⟨t, htA, rfl⟩, fun w hw =>
    CFSG.RankThree.PartOne.LIT.mem_fixedSpace.mp hw⟩
  have hsE : (s : V ≃ₗ[K] V) ∈ E₀ := hmemE.mpr ⟨⟨s, hs, rfl⟩, hsfix⟩
  have hc := hE.isCompl hpK hxE
  have hEW := hE.resComm hpK hxE
  have hcardW := hEW.card_le hp hpK
  rw [ht2] at hcardW
  have hinj : Function.Injective (resHom E₀ _ (hE.comm_inv hxE)) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    have hv : v ∈ F ⊔ CFSG.RankThree.PartOne.LIT.commSpace x := by rw [hc.sup_eq_top]; trivial
    obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hv
    have hgu := (hmemE.mp g.2).2 u hu
    have hgw : (g : V ≃ₗ[K] V) w = w := congrArg Subtype.val (LinearEquiv.congr_fun hg ⟨w, hw⟩)
    simp only [map_add, hgu, hgw, OneMemClass.coe_one]
    rfl
  have hcard : Nat.card E₀ ≤ p := by
    have := Nat.card_le_card_of_injective (resHom E₀ _ (hE.comm_inv hxE)).rangeRestrict
      ((resHom E₀ _ (hE.comm_inv hxE)).rangeRestrict_injective_iff.mpr hinj)
    simpa using this.trans hcardW
  have : Fact p.Prime := ⟨hp⟩
  have hx1 : x ≠ 1 := fun h => ht1 (Subtype.ext h)
  have hxp : x ^ p = 1 := by
    rw [hxdef, ← Subgroup.coe_pow, hA.2 t htA]
    rfl
  have hzp : Subgroup.zpowers x = E₀ := by
    refine Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr hxE) ?_
    rw [Nat.card_zpowers, orderOf_eq_prime hxp hx1]
    exact hcard
  rw [← hzp] at hsE
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hsE
  refine Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext ?_⟩
  rw [Subgroup.coe_zpow, ← hk]

theorem isEndNode_of_commSpace_two (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hV : 8 ≤ finrank K V) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK1 : ∀ c : K, c ^ p = 1 → c = 1) {A : Subgroup (orthDerived Q)}
    (hA : CFSG.Assembly.IsElemAbelian p A) {t : orthDerived Q} (htA : t ∈ A) (ht1 : t ≠ 1)
    (ht2 : finrank K (CFSG.RankThree.PartOne.LIT.commSpace (t : V ≃ₗ[K] V)) = 2) :
    TableBOrth.IsEndNode A t := by
  classical
  have hpK : (p : K) ≠ 0 := natCast_ne_zero_of_odd hp hp2
  set x : V ≃ₗ[K] V := ↑t with hxdef
  have hxp : x ^ p = 1 := by
    rw [hxdef, ← Subgroup.coe_pow, hA.2 t htA]
    rfl
  have hxO : x ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    CFSG.RankThree.PartOne.KCOrthogonal.orthDerived_le_orthogonalGroup t.2
  have hx : OddOrderIsometry Q p x := ⟨hxO, hxp, hpK, fun v hv => hQ.1 v fun w => by
    rw [QuadraticMap.polarBilin_apply_apply]; exact hv w⟩
  have hc := CFSG.RankThree.PartOne.LIT.isCompl_fixedSpace_commSpace hpK hxp
  have hsum := Submodule.finrank_add_eq_of_isCompl hc
  have hW6 : 6 ≤ finrank K (fixedSpace x) := by rw [fixedSpace_eq_lit]; omega
  obtain ⟨hq, hcenter, hodd⟩ := orthDerived_facts (Q.comp (fixedSpace x).subtype)
    hx.polarBilin_fixed_nondegenerate hW6
  set D₀ := supportedFixedDerived Q x with hD₀
  have hD₀Ω : D₀ ≤ orthDerived Q := hx.supportedFixedDerived_le_orthDerived
  set D : Subgroup (orthDerived Q) := D₀.subgroupOf (orthDerived Q) with hD
  have hmemC : ∀ y : orthDerived Q,
      y ∈ Subgroup.centralizer ({t} : Set (orthDerived Q)) ↔
        (y : V ≃ₗ[K] V) ∈ isometryCentralizer Q x := by
    intro y
    rw [Subgroup.mem_centralizer_singleton_iff, isometryCentralizer, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      exact ⟨CFSG.RankThree.PartOne.KCOrthogonal.orthDerived_le_orthogonalGroup y.2,
        congrArg Subtype.val h⟩
    · rintro ⟨-, h⟩
      exact Subtype.ext h
  have hDH : D ≤ Subgroup.centralizer ({t} : Set (orthDerived Q)) := by
    intro y hy
    rw [hmemC]
    exact supportedFixedDerived_le_isometryCentralizer (Subgroup.mem_subgroupOf.mp hy)
  have hcomm : ∀ g ∈ Subgroup.centralizer ({t} : Set (orthDerived Q)),
      ∀ h ∈ Subgroup.centralizer ({t} : Set (orthDerived Q)), g * h * g⁻¹ * h⁻¹ ∈ D := by
    intro g hg h hh
    rw [hD, Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact commutator_mem_supportedFixedDerived hx hK1 ht2 ((hmemC g).mp hg) ((hmemC h).mp hh)
  have hDq : CFSG.IsQuasisimple D := by
    have e1 : D ≃* D₀ := Subgroup.subgroupOfEquivOfLe hD₀Ω
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (e1.trans (supportedFixedDerivedEquiv hx)).symm hq
  obtain ⟨hlay, hcompD⟩ := TableBSymp.largeEvenLayer_eq_of_commutator_mem hDH hcomm hDq
  refine ⟨htA, ht1, ?_, ?_⟩
  · rw [hlay]
    exact hcompD
  · intro s hs
    rw [hlay]
    constructor
    · intro hsD
      have hsC : (s : V ≃ₗ[K] V) ∈ isometryCentralizer Q x := by
        rw [← hmemC, Subgroup.mem_centralizer_singleton_iff]
        exact TableB.IsElemAbelian.comm hA hs htA
      set r := isometryRestrictFixed Q x ⟨_, hsC⟩ with hr
      have hrO := isometryRestrictFixed_mem_orthogonalGroup (Q := Q) ⟨_, hsC⟩
      have hrp : r ^ p = 1 := by
        rw [hr, ← map_pow]
        have hsp : (s : V ≃ₗ[K] V) ^ p = 1 := by
          rw [← Subgroup.coe_pow, hA.2 s hs]
          rfl
        have : (⟨_, hsC⟩ : isometryCentralizer Q x) ^ p = 1 :=
          Subtype.ext (by rw [Subgroup.coe_pow]; exact hsp)
        rw [this, map_one]
      have hrΩ := hodd r hrO p (hp.odd_of_ne_two hp2) hrp
      have hrc : (⟨r, hrΩ⟩ : orthDerived (Q.comp (fixedSpace x).subtype)) ∈
          Subgroup.center (orthDerived (Q.comp (fixedSpace x).subtype)) := by
        rw [Subgroup.mem_center_iff]
        intro ω
        obtain ⟨g, hg⟩ := restrictFixed_surjective hx ω
          (CFSG.RankThree.PartOne.KCOrthogonal.orthDerived_le_orthogonalGroup ω.2)
        have hgD : g.1 ∈ D₀ := mem_supportedFixedDerived.mpr ⟨g.2, by rw [hg]; exact ω.2⟩
        have hgs := hsD ⟨g.1, hD₀Ω hgD⟩ (Subgroup.mem_subgroupOf.mpr hgD)
        apply Subtype.ext
        refine LinearEquiv.ext fun w => Subtype.ext ?_
        simp only [Subgroup.coe_mul, LinearEquiv.mul_apply]
        rw [← hg, coe_restrictFixed, hr, coe_isometryRestrictFixed, coe_isometryRestrictFixed,
          coe_restrictFixed]
        exact (LinearEquiv.congr_fun (congrArg Subtype.val hgs) (w : V)).symm
      rw [hcenter, Subgroup.mem_bot] at hrc
      have hr1 : r = 1 := congrArg Subtype.val hrc
      refine mem_zpowers_of_fixes hQ hp hp2 hA htA ht1 ht2 hs fun w hw => ?_
      rw [← fixedSpace_eq_lit] at hw
      have := congrArg Subtype.val (LinearEquiv.congr_fun hr1 ⟨w, hw⟩)
      rw [coe_isometryRestrictFixed] at this
      exact this
    · intro hsz j hj
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hsz
      have hjt := Subgroup.mem_centralizer_singleton_iff.mp (hDH hj)
      exact (Commute.zpow_left hjt.symm k).eq

end EndNode

end OrthRestOdd

end CFSG.StandardType
