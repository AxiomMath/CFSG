module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRuleSpFinI
public import CFSG.RankThree.PartOne.KC.OrthogonalNormPlanePrimary
public import CFSG.RankThree.PartOne.KC.OrthogonalNormPlaneFactors

public section

namespace CFSG.StandardType.SpFin

open Module Polynomial CFSG.RankThree.Classical CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCSpFull
  CFSG.RankThree.PartOne.KCUnitary CFSG.LocalAnalysis.ComponentInitial
  CFSG.StandardType.TwoThree CFSG.Assembly TableB
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.Open (StatedSp)

section Poly

variable {K : Type} [Field K] [CharP K 2]

@[expose] noncomputable def h3 (K : Type) [Field K] : K[X] := X ^ 2 + X + 1

theorem h3_monic : (h3 K).Monic := by
  unfold h3
  monicity!

theorem h3_natDegree : (h3 K).natDegree = 2 := by
  unfold h3
  compute_degree!

theorem h3_irreducible (hK : Nat.card K = 2) [Finite K] : Irreducible (h3 K) := by
  refine irreducible_of_degree_le_three_of_not_isRoot (by rw [h3_natDegree]; simp) ?_
  intro a ha
  have h11 : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
  rcases eq_zero_or_eq_one_of_card hK a with rfl | rfl
  · simp [h3, IsRoot] at ha
  · simp [h3, IsRoot, h11] at ha

theorem h3_ne_X_sub_one : h3 K ≠ X - 1 := by
  intro h
  have := congrArg natDegree h
  rw [h3_natDegree] at this
  have h2 : (X - 1 : K[X]).natDegree = 1 := by compute_degree!
  omega

theorem h3_reciprocal : KCOrthogonal.reciprocalPolynomial (h3 K) = h3 K := by
  have h0 : (h3 K).coeff 0 = 1 := by simp [h3]
  unfold KCOrthogonal.reciprocalPolynomial
  rw [h0, inv_one, map_one, one_mul]
  unfold Polynomial.reverse
  rw [h3_natDegree]
  unfold h3
  rw [reflect_add, reflect_add, reflect_one]
  have e1 : reflect 2 ((X : K[X]) ^ 2) = 1 := by
    rw [reflect_monomial, revAt_le (le_refl 2)]
    simp
  have e2 : reflect 2 (X : K[X]) = X := by
    have := reflect_monomial (R := K) 2 1
    rw [pow_one, revAt_le (by norm_num : 1 ≤ 2)] at this
    simpa using this
  rw [e1, e2]
  ring

theorem aeval_h3 {V : Type*} [AddCommGroup V] [Module K V] (A : Module.End K V) :
    aeval A (h3 K) = A ^ 2 + A + 1 := by
  simp [h3]

end Poly

section Prim

variable {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ}

theorem primaryComponent_h3 (hK : Nat.card K = 2) {x : StatedSp m K} (hx3 : x ^ 3 = 1) :
    primaryComponent (spEnd x) (h3 K) = LinearMap.range (spEnd x - 1) := by
  apply le_antisymm
  · intro w hw
    obtain ⟨w', hw'⟩ := exists_sub_one_apply_eq_of_mem_primaryComponent (spEnd x)
      (h3_irreducible hK) h3_monic h3_ne_X_sub_one hw
    exact ⟨w', hw'⟩
  · rintro _ ⟨u, rfl⟩
    rw [mem_primaryComponent, aeval_h3]
    have hx3' : spEnd x ^ 3 = 1 := spEnd_pow hx3
    have hA3 : ∀ v, spEnd x (spEnd x (spEnd x v)) = v := fun v => by
      have := congrArg (fun f => f v) hx3'
      simpa [pow_succ, Module.End.mul_apply] using this
    simp only [LinearMap.add_apply, pow_two, Module.End.mul_apply, Module.End.one_apply,
      LinearMap.sub_apply, map_sub]
    rw [hA3 u]
    abel

theorem h3_mem_primaryFactors (hK : Nat.card K = 2) {x : StatedSp m K} (hx3 : x ^ 3 = 1)
    (hx1 : x ≠ 1) : h3 K ∈ primaryFactors (spEnd x) :=
  KCOrthogonal.mem_primaryFactors_of_primaryComponent_ne_bot (h3_irreducible hK) h3_monic (by
    rw [primaryComponent_h3 hK hx3]
    exact rng_ne_bot (x₀ := spLin m K x)
      (fun h => hx1 (spLin_injective (h.trans (map_one _).symm))))

theorem primaryComponent_eq_bot_of_ne (hK : Nat.card K = 2) {x : StatedSp m K} (hx3 : x ^ 3 = 1)
    (hx1 : x ≠ 1) (blocks : SpPrimaryBlocks 2 1 3 x (proj m K x)) {k : Polynomial K}
    (hk : k ∈ primaryFactors (spEnd x)) (hk1 : k ≠ Polynomial.X - 1) (hk3 : k ≠ h3 K) :
    primaryComponent (spEnd x) k = ⊥ := by
  classical
  have hh3 := h3_mem_primaryFactors hK hx3 hx1
  have hdisj : Disjoint (primaryComponent (spEnd x) k) (primaryComponent (spEnd x) (h3 K)) :=
    blocks.isInternal.submodule_iSupIndep.pairwiseDisjoint
      (show (⟨k, hk⟩ : primaryFactors (spEnd x)) ≠ ⟨h3 K, hh3⟩ from fun h =>
        hk3 (congrArg Subtype.val h))
  refine hdisj.eq_bot_of_le fun w hw => ?_
  rw [primaryComponent_h3 hK hx3]
  obtain ⟨w', hw'⟩ := exists_sub_one_apply_eq_of_mem_primaryComponent (spEnd x)
    (irreducible_of_mem_primaryFactors hk) (monic_of_mem_primaryFactors hk) hk1 hw
  exact ⟨w', hw'⟩

end Prim

section Pull

variable {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ}

open CFSG.RankThree.PartOne.KCSpIsotypic in
theorem spPull_isQuasisimple_of_four_le {x : StatedSp m K}
    (blocks : SpPrimaryBlocks 2 1 3 x (proj m K x)) {h : primaryFactors (spEnd x)}
    (hne : (h : Polynomial K) ≠ Polynomial.X - 1)
    (hself : KCOrthogonal.reciprocalPolynomial (h : Polynomial K) = h)
    (hm : 4 ≤ primaryMultiplicity (spEnd x) (h : Polynomial K)) :
    CFSG.IsQuasisimple (spPull x (h : Polynomial K)) := by
  have hS := blocks.selfDual h hne hself
  obtain ⟨d, -, hpd, σ, -, -, -, -, -, hE, -, Hf, hHf, hHfl, -, -, φ, hφ⟩ := hS.exists_half
  have hO : ({(h : Polynomial K), KCOrthogonal.reciprocalPolynomial (h : Polynomial K)} :
      Set (Polynomial K)) = {(h : Polynomial K)} := by
    rw [hself, Set.pair_eq_singleton]
  have hφ' : ∀ (g : orbitFactor (spForm m K) (spLin m K x) (h : Polynomial K))
      (v : Fin m ⊕ Fin m → K) (hv : v ∈ primaryComponent (spEnd x) (h : Polynomial K)),
      blockApply ((((spOrbitEquiv x hO).trans φ) g : sesqUnitaryGroup Hf) :
        blockGL (spEnd x) (h : Polynomial K)) v hv =
        ((g : LinearMap.GeneralLinearGroup K (Fin m ⊕ Fin m → K)) :
          Module.End K (Fin m ⊕ Fin m → K)) v := by
    intro g v hv
    rw [MulEquiv.trans_apply]
    have := hφ (spOrbitEquiv x hO g) v hv
    rw [this, spEnd_orbitEquiv]
  let ι : sesqUnitaryGroup Hf →* blockGL (spEnd x) (h : Polynomial K) :=
    (sesqUnitaryGroup Hf).subtype
  have hspec := specialBlock_eq_kerImage (B := spForm m K) ((spOrbitEquiv x hO).trans φ) ι hφ'
  let D : sesqUnitaryGroup Hf →* (AdjoinRoot (h : Polynomial K))ˣ :=
    (blockGLDet (spEnd x) (h : Polynomial K)).comp ι
  have hker : D.ker = (sesqSpecialUnitaryGroup Hf).subgroupOf (sesqUnitaryGroup Hf) := by
    ext δ
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_sesqSpecialUnitaryGroup]
    constructor
    · intro hδ
      refine ⟨δ.2, ?_⟩
      have := congrArg Units.val hδ
      simpa [D, ι, blockGLDet] using this
    · rintro ⟨-, hδ⟩
      apply Units.ext
      simpa [D, ι, blockGLDet] using hδ
  have hm' : 4 ≤ Module.finrank (AdjoinRoot (h : Polynomial K))
      (primaryComponent (spEnd x) (h : Polynomial K)) := hm
  have hquasi : CFSG.IsQuasisimple D.ker := by
    rw [hker]
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe (sesqSpecialUnitaryGroup_le Hf)).symm
      (CFSG.RankThree.PartOne.KCUnitary.isQuasisimple_sesqSpecialUnitaryGroup_of_two_le hE hHf
        hHfl (by omega) ⟨fun h2 => by omega, fun h3 => by omega⟩)
  obtain ⟨e⟩ := nonempty_kerImage_mulEquiv (orbitFactor (spForm m K) (spLin m K x)
    (h : Polynomial K)) ((spOrbitEquiv x hO).trans φ) D
  have hsb : CFSG.IsQuasisimple (specialBlock (spForm m K) (spLin m K x) (h : Polynomial K)) := by
    rw [hspec]
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hquasi
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (comapSpLinEquiv _ (fun _ hg => spLin_mem_sesq_of_mem_specialBlock hg)).symm hsb

end Pull

section Pull2

variable {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ}

open CFSG.RankThree.PartOne.KCSpIsotypic

theorem card_adjoinRoot_h3 (hK : Nat.card K = 2) : Nat.card (AdjoinRoot (h3 K)) = 4 := by
  haveI : Fact (Irreducible (h3 K)) := ⟨h3_irreducible hK⟩
  haveI : Module.Finite K (AdjoinRoot (h3 K)) := (AdjoinRoot.powerBasis h3_monic.ne_zero).finite
  have h1 : finrank K (AdjoinRoot (h3 K)) = 2 := by
    rw [(AdjoinRoot.powerBasis h3_monic.ne_zero).finrank, AdjoinRoot.powerBasis_dim, h3_natDegree]
  rw [Module.natCard_eq_pow_finrank (K := K), hK, h1]
  norm_num

theorem pull_fix_ker (hK : Nat.card K = 2) {x q : StatedSp m K}
    (blocks : SpPrimaryBlocks 2 1 3 x (proj m K x)) (hq : q ∈ spPull x (h3 K)) :
    ∀ v ∈ LinearMap.ker (spEnd x - 1), spEnd q v = v := by
  intro v hv
  by_cases hv0 : v = 0
  · rw [hv0, map_zero]
  have hVp : primaryComponent (spEnd x) (Polynomial.X - 1) = LinearMap.ker (spEnd x - 1) :=
    blocks.fixed_eq
  have hmem : (Polynomial.X - 1 : Polynomial K) ∈ primaryFactors (spEnd x) :=
    KCOrthogonal.mem_primaryFactors_of_primaryComponent_ne_bot irreducible_X_sub_one
      monic_X_sub_one (fun hbot => hv0 (by
        have : v ∈ primaryComponent (spEnd x) (Polynomial.X - 1) := hVp ▸ hv
        rw [hbot, Submodule.mem_bot] at this
        exact this))
  have hq' : spLin m K q ∈ specialBlock (spForm m K) (spLin m K x) (h3 K) := hq
  have hq'' := specialBlock_le_orbitFactor hq'
  rw [orbitFactor_spForm, h3_reciprocal, Set.pair_eq_singleton] at hq''
  exact hq''.2 (Polynomial.X - 1) hmem
    (fun h => h3_ne_X_sub_one (Set.mem_singleton_iff.mp h).symm) v (hVp ▸ hv)

theorem commute_of_fix_pull (hK : Nat.card K = 2) {x b q : StatedSp m K} (hx3 : x ^ 3 = 1)
    (blocks : SpPrimaryBlocks 2 1 3 x (proj m K x)) (hbx : b * x = x * b)
    (hb : ∀ w ∈ LinearMap.range (spEnd x - 1), spEnd b w = w) (hq : q ∈ spPull x (h3 K)) :
    b * q = q * b := by
  have hqx : q * x = x * q :=
    Subgroup.mem_centralizer_singleton_iff.mp (spPull_le_centralizer x _ hq)
  have hxq : spEnd x * spEnd q = spEnd q * spEnd x := (spEnd_comm_iff.mp hqx).symm
  have hxb : spEnd x * spEnd b = spEnd b * spEnd x := (spEnd_comm_iff.mp hbx).symm
  have hx3' : spEnd x ^ 3 = 1 := spEnd_pow hx3
  apply spEnd_injective
  rw [spEnd_mul, spEnd_mul]
  apply LinearMap.ext
  intro v
  obtain ⟨v₁, hv₁, w, hw, rfl⟩ := CFSG.RankThree.PartOne.OddIso.exists_fix_add_range (p := 3)
    ⟨1, by norm_num⟩ hx3' v
  obtain ⟨u, rfl⟩ := hw
  have hbv₁ : spEnd b v₁ ∈ LinearMap.ker (spEnd x - 1) := by
    rw [LinearMap.mem_ker, sub_one_apply_comm hxb, LinearMap.mem_ker.mp hv₁, map_zero]
  have hqw : spEnd q ((spEnd x - 1) u) ∈ LinearMap.range (spEnd x - 1) :=
    ⟨spEnd q u, by rw [sub_one_apply_comm hxq]⟩
  simp only [Module.End.mul_apply, map_add]
  rw [pull_fix_ker hK blocks hq v₁ hv₁, hb _ (LinearMap.mem_range_self _ u),
    pull_fix_ker hK blocks hq _ hbv₁, hb _ hqw]

theorem card_le_three_mul_inf_pull (hK : Nat.card K = 2) {Ã : Subgroup (StatedSp m K)}
    (hÃ : IsElemAbelian 3 Ã) {x : StatedSp m K} (hx : x ∈ Ã) (hx1 : x ≠ 1)
    (blocks : SpPrimaryBlocks 2 1 3 x (proj m K x))
    (hfix : ∀ b ∈ Ã, ∀ u ∈ LinearMap.ker (spEnd x - 1), spEnd b u = u) :
    Nat.card Ã ≤ 3 * Nat.card (Ã ⊓ spPull x (h3 K) : Subgroup (StatedSp m K)) := by
  classical
  haveI := finite_statedSp_group (K := K) (m := m)
  have hx3 : x ^ 3 = 1 := hÃ.2 x hx
  let ε : Ã →* gl_centralizer (spLin m K x) :=
    { toFun := fun b => ⟨spLin m K b, mem_gl_centralizer.mpr
        (spEnd_comm_iff.mp (TableB.IsElemAbelian.comm hÃ b.2 hx))⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun a b => Subtype.ext (map_mul _ _ _) }
  let δ : Ã →* (AdjoinRoot (h3 K))ˣ := (blockDetHom (spLin m K x) (h3 K)).comp ε
  have hker : ∀ b : Ã, δ b = 1 → (b : StatedSp m K) ∈ spPull x (h3 K) := by
    intro b hb
    show spLin m K b ∈ specialBlock (spForm m K) (spLin m K x) (h3 K)
    rw [mem_specialBlock]
    refine ⟨?_, (ε b).2, hb⟩
    rw [orbitFactor_spForm, h3_reciprocal, Set.pair_eq_singleton]
    refine ⟨mem_unitaryCentralizer.mpr ⟨spLin_mem _, mem_gl_centralizer.mp (ε b).2⟩, ?_⟩
    intro k hk hkn v hv
    by_cases hk1 : k = Polynomial.X - 1
    · subst hk1
      exact hfix b b.2 v (blocks.fixed_eq ▸ hv)
    · have hbot := primaryComponent_eq_bot_of_ne hK hx3 hx1 blocks hk hk1
        (fun h => hkn (h ▸ Set.mem_singleton _))
      rw [hbot, Submodule.mem_bot] at hv
      rw [hv, map_zero]
  have hrange : Nat.card δ.range ≤ 3 := by
    haveI : Fact (Irreducible (h3 K)) := ⟨h3_irreducible hK⟩
    haveI : Module.Finite K (AdjoinRoot (h3 K)) := (AdjoinRoot.powerBasis h3_monic.ne_zero).finite
    haveI : Finite (AdjoinRoot (h3 K)) := Module.finite_of_finite K
    have h1 : Nat.card δ.range ≤ Nat.card (AdjoinRoot (h3 K))ˣ :=
      Subgroup.card_le_card_group δ.range
    rw [Nat.card_units, card_adjoinRoot_h3 hK] at h1
    omega
  have hcardA : Nat.card δ.ker * Nat.card δ.range = Nat.card Ã :=
    Subgroup.card_ker_mul_card_range δ
  have hle : δ.ker.map Ã.subtype ≤ (Ã ⊓ spPull x (h3 K) : Subgroup (StatedSp m K)) := by
    rintro _ ⟨b, hb, rfl⟩
    exact ⟨b.2, hker b hb⟩
  have hkc : Nat.card δ.ker ≤ Nat.card (Ã ⊓ spPull x (h3 K) : Subgroup (StatedSp m K)) := by
    calc Nat.card δ.ker = Nat.card (δ.ker.map Ã.subtype) :=
          Nat.card_congr (δ.ker.equivMapOfInjective Ã.subtype Ã.subtype_injective).toEquiv
      _ ≤ _ := Subgroup.card_le_of_le hle
  calc Nat.card Ã = Nat.card δ.ker * Nat.card δ.range := hcardA.symm
    _ ≤ Nat.card (Ã ⊓ spPull x (h3 K) : Subgroup (StatedSp m K)) * 3 := Nat.mul_le_mul hkc hrange
    _ = 3 * Nat.card (Ã ⊓ spPull x (h3 K) : Subgroup (StatedSp m K)) := mul_comm _ _

end Pull2

section CoreII

variable {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ}

theorem coreII (hK : Nat.card K = 2) (hm : 5 ≤ m) {Ã : Subgroup (StatedSp m K)}
    (hÃ : IsElemAbelian 3 Ã) (hcard : 3 ^ (m - 1) ≤ Nat.card Ã)
    {T : Submodule K (Fin m ⊕ Fin m → K)} (hT0 : T ≠ ⊥)
    (hTiso : ∀ u ∈ T, ∀ v ∈ T, spForm m K u v = 0)
    (hTÃ : ∀ a ∈ Ã, ∀ t ∈ T, spEnd a t ∈ T) {x : StatedSp m K} (hx : x ∈ Ã) (hx1 : x ≠ 1)
    (blocks : SpPrimaryBlocks 2 1 3 x (proj m K x)) (hd : spFixedDim x ≤ 2) :
    ∃ Q : Subgroup (StatedSp m K), CFSG.IsQuasisimple Q ∧
      Q ≤ Subgroup.centralizer ({x} : Set (StatedSp m K)) ∧
      (∀ c ∈ Subgroup.centralizer ({x} : Set (StatedSp m K)), ∀ q ∈ Q, c * q * c⁻¹ ∈ Q) ∧
      ((∃ b ∈ Ã, b ∉ Subgroup.zpowers x ∧ ∀ q ∈ Q, b * q = q * b) ∨
        3 ^ 3 ≤ Nat.card (Ã ⊓ Q : Subgroup (StatedSp m K))) := by
  classical
  haveI := finite_statedSp_group (K := K) (m := m)
  haveI := finite_units_end (K := K) (V := Fin m ⊕ Fin m → K)
  have hx3 : x ^ 3 = 1 := hÃ.2 x hx
  set Xg : Subgroup (Module.End K (Fin m ⊕ Fin m → K))ˣ := Ã.map (spLin m K) with hXg
  have hXiso := isoSetup_map hÃ
  have hx₀ : spLin m K x ∈ Xg := ⟨x, hx, rfl⟩
  have hx₁ : spLin m K x ≠ 1 := fun h => hx1 (spLin_injective (h.trans (map_one _).symm))
  have hcardX : 3 ^ (m - 1) ≤ Nat.card Xg := by
    rw [hXg, ← Nat.card_congr (Ã.equivMapOfInjective (spLin m K) spLin_injective).toEquiv]
    exact hcard
  have hTX : ∀ g ∈ Xg, ∀ t ∈ T, (g : Module.End K (Fin m ⊕ Fin m → K)) t ∈ T := by
    rintro _ ⟨a, ha, rfl⟩ t ht
    exact hTÃ a ha t ht
  have hx3' : (spLin m K x) ^ 3 = 1 := by rw [← map_pow, hx3, map_one]
  have hsum : finrank K (LinearMap.ker (spEnd x - 1)) + finrank K (LinearMap.range (spEnd x - 1)) =
      2 * m := by
    have h := Submodule.finrank_add_eq_of_isCompl (isCompl_fix_rng hx3')
    rw [finrank_spSpace m] at h
    exact h
  have hfix : finrank K (LinearMap.ker (spEnd x - 1)) = spFixedDim x := by
    rw [← blocks.fixed_eq]
    rfl
  have hbx : ∀ b ∈ Ã, b * x = x * b := fun b hb => TableB.IsElemAbelian.comm hÃ hb hx
  have hh3 := h3_mem_primaryFactors hK hx3 hx1
  have hmult : 4 ≤ primaryMultiplicity (spEnd x) (h3 K) := by
    haveI : Fact (Irreducible (h3 K)) := ⟨h3_irreducible hK⟩
    have h1 := finrank_primaryComponent (spEnd x) (h3 K)
    rw [h3_natDegree] at h1
    have h1' : finrank K (primaryComponent (spEnd x) (h3 K)) =
        finrank K (LinearMap.range (spEnd x - 1)) := by rw [primaryComponent_h3 hK hx3]
    have h2 : primaryMultiplicity (spEnd x) (h3 K) =
        finrank (AdjoinRoot (h3 K)) (primaryComponent (spEnd x) (h3 K)) := rfl
    omega
  have hQq := spPull_isQuasisimple_of_four_le (h := ⟨h3 K, hh3⟩) blocks h3_ne_X_sub_one
    h3_reciprocal hmult
  refine ⟨spPull x (h3 K), hQq, spPull_le_centralizer x _, spPull_normalized x _, ?_⟩
  by_cases hb : ∃ b ∈ Ã, b ∉ Subgroup.zpowers x ∧ ∀ w ∈ LinearMap.range (spEnd x - 1),
      spEnd b w = w
  · obtain ⟨b, hbÃ, hbz, hbf⟩ := hb
    exact Or.inl ⟨b, hbÃ, hbz, fun q hq => commute_of_fix_pull hK hx3 blocks (hbx b hbÃ) hbf hq⟩
  · right
    have hXm : ∀ g ∈ Xg, g ∈ fixG (LinearMap.range (spEnd x - 1)) → g = 1 := by
      rintro _ ⟨b, hbÃ, rfl⟩ hgf
      have hbz : b ∈ Subgroup.zpowers x := by
        by_contra hn
        exact hb ⟨b, hbÃ, hn, fun w hw => hgf w hw⟩
      by_contra hg1
      have hb3 : spLin m K b ^ 3 = 1 := by rw [← map_pow, hÃ.2 b hbÃ, map_one]
      have hgz : spLin m K b ∈ Subgroup.zpowers (spLin m K x) := by
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hbz
        exact Subgroup.mem_zpowers_iff.mpr ⟨k, by rw [← map_zpow, hk]⟩
      have heq : Subgroup.zpowers (spLin m K b) = Subgroup.zpowers (spLin m K x) :=
        Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hgz) (by
          rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime hx3' hx₁,
            orderOf_eq_prime hb3 hg1])
      have hxm : spLin m K x ∈ fixG (LinearMap.range (spEnd x - 1)) :=
        (Subgroup.zpowers_le.mpr hgf) (heq ▸ Subgroup.mem_zpowers (spLin m K x))
      have hbot : LinearMap.range (spEnd x - 1) = ⊥ := by
        rw [eq_bot_iff]
        intro w hw
        exact (Submodule.mem_bot K).mpr (OddIso.eq_zero_of_fixed_range (p := 3) ⟨1, by norm_num⟩
          (by rw [← Units.val_pow_eq_pow_val, hx3', Units.val_one]) hw (hxm w hw))
      exact rng_ne_bot hx₁ hbot
    obtain ⟨-, hall⟩ := lemII hK spForm_nondegenerate spForm_isAlt.isRefl hXiso hx₀ hx₁ (n := m)
      (by omega) (finrank_spSpace m) hcardX hT0 hTiso hTX hXm
    have hfixVp : ∀ b ∈ Ã, ∀ u ∈ LinearMap.ker (spEnd x - 1), spEnd b u = u :=
      fun b hb u hu => hall (spLin m K b) ⟨b, hb, rfl⟩ u hu
    have h3le := card_le_three_mul_inf_pull hK hÃ hx hx1 blocks hfixVp
    have h4 : 3 ^ (m - 2) ≤ Nat.card (Ã ⊓ spPull x (h3 K) : Subgroup (StatedSp m K)) := by
      have h5 : 3 * 3 ^ (m - 2) ≤ 3 * Nat.card (Ã ⊓ spPull x (h3 K) : Subgroup (StatedSp m K)) := by
        calc 3 * 3 ^ (m - 2) = 3 ^ (m - 1) := by
              rw [← pow_succ']
              congr 1
              omega
          _ ≤ Nat.card Ã := hcard
          _ ≤ _ := h3le
      exact Nat.le_of_mul_le_mul_left h5 (by norm_num)
    exact (Nat.pow_le_pow_right (by norm_num) (by omega : 3 ≤ m - 2)).trans h4

end CoreII

end CFSG.StandardType.SpFin
