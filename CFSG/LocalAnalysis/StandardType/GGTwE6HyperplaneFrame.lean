module

public import CFSG.LocalAnalysis.StandardType.GGTwE6ReflectionRadical
public import CFSG.LocalAnalysis.StandardType.GGTwE6FixedComponent
public import CFSG.LocalAnalysis.StandardType.GGTwE6HyperplaneTypes
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeNonToralFpf
public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeA2BlockTwoCore
public import CFSG.LocalAnalysis.StandardType.GGTwE6FixedA2SL3
public import CFSG.Quasithin.Vol2.KGFactC31RuRef

public noncomputable section

namespace CFSG.StandardType.TwE6HyperplaneFrame

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.TableBExc.Three
  CFSG.StandardType.TableBExc.E6Three CFSG.StandardType.E6NonToralThree
  CFSG.StandardType.E6ThreeEnd

section CharacterKernel


theorem rootChar_pow_three_of_commute {L : Type} [Field L] {x : ModGL .E6 L}
    (hx : x ∈ monomialSubgroup .E6 L) {b : Fin Tag.E6.rank → Lˣ}
    (hbx : rootDiagUnit .E6 b * x = x * rootDiagUnit .E6 b) {α : Fin Tag.E6.rank → ℤ}
    (hα : α + weylQuotientHom .E6 L ⟨x, hx⟩ • α +
      weylQuotientHom .E6 L ⟨x, hx⟩ • weylQuotientHom .E6 L ⟨x, hx⟩ • α = 0) :
    rootChar b α ^ 3 = 1 := by
  set w := weylQuotientHom .E6 L ⟨x, hx⟩ with hw
  have hconj : x * rootDiagUnit .E6 b * x⁻¹ = rootDiagUnit .E6 (weylTuple w b) := by
    have h := conj_rootDiagUnit_of_mem_monoHat (x := ⟨x, monomial_le_monoHat hx⟩) b
    rw [psiHat_of_mem_monomial hx] at h
    exact h
  have h1 : x * rootDiagUnit .E6 b * x⁻¹ = rootDiagUnit .E6 b := by
    rw [← hbx]
    group
  have hwt : weylTuple w b = b := rootDiagUnit_injective (hconj.symm.trans h1)
  have hfix : ∀ u, rootChar b (w • u) = rootChar b u := fun u => by
    have h := rootChar_weylTuple w b (w • u)
    rw [hwt, inv_smul_smul] at h
    exact h
  have h2 : rootChar b (w • w • α) = rootChar b α := (hfix (w • α)).trans (hfix α)
  have hsum := congrArg (rootChar b) hα
  rw [rootChar_add, rootChar_add, hfix α, h2, rootChar_zero] at hsum
  rw [pow_three, ← mul_assoc]
  exact hsum

theorem finiteIndex_rootChar_kernel {L : Type} [Field L] [IsAlgClosed L] (hL : ringChar L ≠ 3)
    {E : Subgroup (ModGL .E6 L)} [Finite E] (hEM : E ≤ monomialSubgroup .E6 L)
    (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ 4) (hET : ¬ E ≤ torusGroup .E6 L)
    (hAS : ∀ e (he : e ∈ E), weylQuotientHom .E6 L ⟨e, hEM he⟩ ∈ modelHomE6.range)
    (hAg : ∀ e (he : e ∈ E) i, weylQuotientHom .E6 L ⟨e, hEM he⟩ ≠ gE6 i)
    {x : ModGL .E6 L} (hxE : x ∈ E) {α : Fin Tag.E6.rank → ℤ} (hα : IsRoot .E6 α)
    (hαw : α + weylQuotientHom .E6 L ⟨x, hEM hxE⟩ • α +
      weylQuotientHom .E6 L ⟨x, hEM hxE⟩ • weylQuotientHom .E6 L ⟨x, hEM hxE⟩ • α = 0) :
    ((torusGroup .E6 L ⊓ Subgroup.centralizer (E : Set (ModGL .E6 L)) ⊓
        Subgroup.centralizer ({rootSL2 .E6 L α (uSL 1)} : Set (ModGL .E6 L))).subgroupOf
      (adjointGroup .E6 L ⊓ Subgroup.centralizer (E : Set (ModGL .E6 L)))).FiniteIndex := by
  classical
  set Z := adjointGroup .E6 L ⊓ Subgroup.centralizer (E : Set (ModGL .E6 L)) with hZdef
  set M := torusGroup .E6 L ⊓ Subgroup.centralizer (E : Set (ModGL .E6 L)) ⊓
    Subgroup.centralizer ({rootSL2 .E6 L α (uSL 1)} : Set (ModGL .E6 L)) with hMdef
  have hdec : ∀ z : Z, ∃ e ∈ E, ∃ b : Fin Tag.E6.rank → Lˣ,
      (∀ e' ∈ E, rootDiagUnit .E6 b * e' = e' * rootDiagUnit .E6 b) ∧
        (z : ModGL .E6 L) = e * rootDiagUnit .E6 b := by
    intro z
    obtain ⟨e, he, t, ht, htE, hzt⟩ := exists_mul_torus_of_commute hL hEM hE hcard hET hAS hAg
      z.2.1 (fun e' he' => (Subgroup.mem_centralizer_iff.mp z.2.2 e' he').symm)
    obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
    exact ⟨e, he, b, htE, hzt⟩
  choose e he b hbE hzb using hdec
  have hcube : ∀ z : Z, rootChar (b z) α ∈ rootsOfUnity 3 L := fun z => by
    rw [mem_rootsOfUnity]
    exact rootChar_pow_three_of_commute (hEM hxE) (hbE z x hxE) hαw
  have key : ∀ z₁ z₂ : Z, e z₁ = e z₂ → rootChar (b z₁) α = rootChar (b z₂) α →
      (QuotientGroup.mk z₁ : Z ⧸ M.subgroupOf Z) = QuotientGroup.mk z₂ := by
    intro z₁ z₂ he12 hb12
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have hprod : ((z₁⁻¹ * z₂ : Z) : ModGL .E6 L) = rootDiagUnit .E6 ((b z₁)⁻¹ * b z₂) := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hzb z₁, hzb z₂, he12,
        CFSG.LieType.Chevalley.rootDiagUnit_mul, ← CFSG.LieType.Chevalley.rootDiagUnit_inv]
      group
    have hchar : rootChar ((b z₁)⁻¹ * b z₂) α = 1 := by
      have h : rootChar ((b z₁)⁻¹ * b z₂) α = (rootChar (b z₁) α)⁻¹ * rootChar (b z₂) α := by
        simp only [rootChar, Pi.mul_apply, Pi.inv_apply, mul_zpow, inv_zpow,
          Finset.prod_mul_distrib, Finset.prod_inv_distrib]
      rw [h, hb12, inv_mul_cancel]
    have hcE : ∀ e' ∈ E, e' * ((z₁⁻¹ * z₂ : Z) : ModGL .E6 L) =
        ((z₁⁻¹ * z₂ : Z) : ModGL .E6 L) * e' := by
      intro e' he'
      rw [Subgroup.coe_mul, Subgroup.coe_inv]
      have h₁ : Commute e' (z₁ : ModGL .E6 L) := Subgroup.mem_centralizer_iff.mp z₁.2.2 e' he'
      have h₂ : Commute e' (z₂ : ModGL .E6 L) := Subgroup.mem_centralizer_iff.mp z₂.2.2 e' he'
      exact (h₁.inv_right.mul_right h₂).eq
    have hmem : rootDiagUnit .E6 ((b z₁)⁻¹ * b z₂) ∈ M := by
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2
        ⟨CFSG.LieType.Chevalley.rootDiagUnit_mem_torusGroup _, ?_⟩, ?_⟩
      · rw [Subgroup.mem_centralizer_iff, ← hprod]
        exact hcE
      · rw [Subgroup.mem_centralizer_iff]
        intro r hr
        rw [Set.mem_singleton_iff.mp hr]
        exact ((TwE6FixedA2Type.rootDiagUnit_commute_rootSL2_iff _ hα).2 hchar).symm
    rw [hprod]
    exact hmem
  let f : E × rootsOfUnity 3 L → Z ⧸ M.subgroupOf Z := fun p =>
    if hp : ∃ z : Z, e z = p.1 ∧ rootChar (b z) α = p.2 then QuotientGroup.mk (Classical.choose hp)
    else QuotientGroup.mk 1
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective q
    have hp : ∃ z' : Z, e z' = (⟨e z, he z⟩ : E) ∧
        rootChar (b z') α = (⟨rootChar (b z) α, hcube z⟩ : rootsOfUnity 3 L) := ⟨z, rfl, rfl⟩
    refine ⟨(⟨e z, he z⟩, ⟨rootChar (b z) α, hcube z⟩), ?_⟩
    change (if hp : ∃ z' : Z, e z' = (⟨e z, he z⟩ : E) ∧
        rootChar (b z') α = (⟨rootChar (b z) α, hcube z⟩ : rootsOfUnity 3 L) then
          QuotientGroup.mk (Classical.choose hp) else QuotientGroup.mk 1) = _
    rw [dif_pos hp]
    exact key _ _ (Classical.choose_spec hp).1 (Classical.choose_spec hp).2
  have : Finite (Z ⧸ M.subgroupOf Z) := Finite.of_surjective f hf
  exact Subgroup.finiteIndex_of_finite_quotient

theorem rootChar_eq_one_of_mem_connected_centralizer {L : Type} [Field L] [IsAlgClosed L]
    (hL : ringChar L ≠ 3) {E : Subgroup (ModGL .E6 L)} [Finite E]
    (hEM : E ≤ monomialSubgroup .E6 L) (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ 4)
    (hET : ¬ E ≤ torusGroup .E6 L)
    (hAS : ∀ e (he : e ∈ E), weylQuotientHom .E6 L ⟨e, hEM he⟩ ∈ modelHomE6.range)
    (hAg : ∀ e (he : e ∈ E) i, weylQuotientHom .E6 L ⟨e, hEM he⟩ ≠ gE6 i)
    {x : ModGL .E6 L} (hxE : x ∈ E) {α : Fin Tag.E6.rank → ℤ} (hα : IsRoot .E6 α)
    (hαw : α + weylQuotientHom .E6 L ⟨x, hEM hxE⟩ • α +
      weylQuotientHom .E6 L ⟨x, hEM hxE⟩ • weylQuotientHom .E6 L ⟨x, hEM hxE⟩ • α = 0)
    {t : ModGL .E6 L} (ht : t ∈ closedIdentityComponent
      (adjointGroup .E6 L ⊓ Subgroup.centralizer (E : Set (ModGL .E6 L)))) :
    ∃ b, t = rootDiagUnit .E6 b ∧ rootChar b α = 1 := by
  have := finiteIndex_rootChar_kernel hL hEM hE hcard hET hAS hAg hxE hα hαw
  have hM := isPointClosed_inf (isPointClosed_inf (isPointClosed_torusGroup (τ := Tag.E6) (k := L))
    (isPointClosed_centralizer (E : Set (ModGL .E6 L))))
    (isPointClosed_centralizer ({rootSL2 .E6 L α (uSL 1)} : Set (ModGL .E6 L)))
  obtain ⟨⟨htT, -⟩, htr⟩ := closedIdentityComponent_le_of_isPointClosed_finiteIndex hM ht
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup htT
  exact ⟨b, rfl, (TwE6FixedA2Type.rootDiagUnit_commute_rootSL2_iff b hα).1
    (Subgroup.mem_centralizer_iff.mp htr _ rfl).symm⟩

theorem closedIdentityComponent_eq_bot_of_weyl_norm_zero
    {L : Type} [Field L] [IsAlgClosed L] (hL : ringChar L ≠ 3)
    {E : Subgroup (ModGL .E6 L)} [Finite E]
    (hEM : E ≤ monomialSubgroup .E6 L) (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ 4)
    (hET : ¬ E ≤ torusGroup .E6 L)
    (hAS : ∀ e (he : e ∈ E), weylQuotientHom .E6 L ⟨e, hEM he⟩ ∈ modelHomE6.range)
    (hAg : ∀ e (he : e ∈ E) i, weylQuotientHom .E6 L ⟨e, hEM he⟩ ≠ gE6 i)
    {x : ModGL .E6 L} (hxE : x ∈ E)
    (hN : ∀ i : Fin Tag.E6.rank,
      (Pi.single i 1 : Fin Tag.E6.rank → ℤ) +
        weylQuotientHom .E6 L ⟨x, hEM hxE⟩ • (Pi.single i 1 : Fin Tag.E6.rank → ℤ) +
        weylQuotientHom .E6 L ⟨x, hEM hxE⟩ •
          (weylQuotientHom .E6 L ⟨x, hEM hxE⟩ • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) = 0) :
    closedIdentityComponent (adjointGroup .E6 L ⊓
      Subgroup.centralizer (E : Set (ModGL .E6 L))) = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro t ht
  have hall : ∀ i : Fin Tag.E6.rank, ∃ b, t = rootDiagUnit .E6 b ∧
      rootChar b (Pi.single i 1) = 1 := fun i =>
    rootChar_eq_one_of_mem_connected_centralizer hL hEM hE hcard hET hAS hAg hxE
      (isRoot_single .E6 i) (hN i) ht
  obtain ⟨b, hb, -⟩ := hall 0
  have hb1 : b = 1 := by
    funext i
    obtain ⟨b', hb', h'⟩ := hall i
    have hbb : b = b' := rootDiagUnit_injective (hb.symm.trans hb')
    rw [← hbb] at h'
    have hs := rootChar_nsmul_single b i 1
    rw [one_nsmul, pow_one] at hs
    rw [Pi.one_apply, ← hs, h']
  rw [hb, hb1, CFSG.LieType.Chevalley.rootDiagUnit_one]
  exact Subgroup.one_mem _

end CharacterKernel

section CFrame

open CFSG.StandardType.TwE6HyperplaneTypes


theorem exists_conj_weylImage_zpowers_c {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    (halg : letI := ZMod.algebra L 2; Algebra.IsAlgebraic (ZMod 2) L)
    {E : Subgroup (ModGL .E6 L)} [Finite E] (hEG : E ≤ adjointGroup .E6 L)
    (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ 4)
    (hnt : ¬ CFSG.StandardType.SCFourCover.E6AdToral E) {e : ModGL .E6 L} (he1 : e ≠ 1)
    (heS : e ∈ closedIdentityComponent
      (adjointGroup .E6 L ⊓ Subgroup.centralizer (E : Set (ModGL .E6 L)))) :
    ∃ y₀ ∈ adjointGroup .E6 L,
      ∃ hEM : E.map (MulAut.conj y₀).toMonoidHom ≤ monomialSubgroup .E6 L,
        (∀ e' (he' : e' ∈ E.map (MulAut.conj y₀).toMonoidHom),
          weylQuotientHom .E6 L ⟨e', hEM he'⟩ ∈ Subgroup.zpowers cE6) ∧
        ∃ x, ∃ hx : x ∈ E.map (MulAut.conj y₀).toMonoidHom,
          weylQuotientHom .E6 L ⟨x, hEM hx⟩ = cE6 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL3 : ringChar L ≠ 3 := by rw [ringChar.eq L 2]; decide
  obtain ⟨g, hgG, hEM₁, hreg⟩ := exists_conj_regular (by decide : (2 : ℕ) ≠ 3) halg hEG
    (Set.toFinite (E : Set (ModGL .E6 L))) hE
  set E₁ := E.map (MulAut.conj g).toMonoidHom with hE₁def
  have hE₁ : IsElemAbelian 3 E₁ := hE.map _
  have hcard₁ : Nat.card E₁ = 3 ^ 4 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hcard
  have : Finite E₁ :=
    Finite.of_surjective _ ((MulAut.conj g).toMonoidHom.subgroupMap_surjective E)
  have hET₁ : ¬ E₁ ≤ torusGroup .E6 L := by
    intro h
    apply hnt
    refine (CFSG.StandardType.SCFourCover.e6AdToral_map_conj hgG E).mp
      ⟨1, one_mem _, fun e he => ?_⟩
    simpa using h he
  have hAS₁ : ∀ e (he : e ∈ E₁), weylQuotientHom .E6 L ⟨e, hEM₁ he⟩ ∈ modelHomE6.range :=
    fun e he => (hreg e he).1
  have hAg₁ : ∀ e (he : e ∈ E₁) i, weylQuotientHom .E6 L ⟨e, hEM₁ he⟩ ≠ gE6 i :=
    fun e he => (hreg e he).2
  have he₁S : g * e * g⁻¹ ∈ closedIdentityComponent
      (adjointGroup .E6 L ⊓ Subgroup.centralizer (E₁ : Set (ModGL .E6 L))) := by
    rw [← map_adjoint_centralizer_conj E hgG, closedIdentityComponent_map_conj]
    exact ⟨e, heS, rfl⟩
  have he₁1 : g * e * g⁻¹ ≠ 1 := by
    intro h
    apply he1
    calc e = g⁻¹ * (g * e * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  have hnofpf : ∀ x (hx : x ∈ E₁) (v : Fin 3 → ZMod 3), (∀ i, v i ≠ 0) →
      weylQuotientHom .E6 L ⟨x, hEM₁ hx⟩ ≠
        modelHomE6 (SemidirectProduct.inl (Multiplicative.ofAdd v)) := by
    intro x hx v hv hw
    apply he₁1
    have hS := closedIdentityComponent_eq_bot_of_weyl_norm_zero
      hL3 hEM₁ hE₁ hcard₁ hET₁ hAS₁ hAg₁ hx (fun i => by
        rw [hw, modelHomE6_eq_wordProd]
        simp only [CFSG.StandardType.TableBExc.wordProd_smul]
        exact fpf_cubic v hv i)
    simpa only [hS, Subgroup.mem_bot] using he₁S
  obtain ⟨x₁, hx₁, hx₁T⟩ : ∃ x ∈ E₁, x ∉ torusGroup .E6 L := by
    by_contra h
    push Not at h
    exact hET₁ h
  have hker : ∀ y (hy : y ∈ monomialSubgroup .E6 L), weylQuotientHom .E6 L ⟨y, hy⟩ = 1 →
      y ∈ torusGroup .E6 L := by
    intro y hy h
    have h' : (⟨y, hy⟩ : monomialSubgroup .E6 L) ∈ (weylQuotientHom .E6 L).ker := h
    rw [CFSG.StandardType.TableBExc.weylQuotientHom_surjective_ker.2,
      Subgroup.mem_subgroupOf] at h'
    exact h'
  set w₁ := weylQuotientHom .E6 L ⟨x₁, hEM₁ hx₁⟩ with hw₁
  have hw₁1 : w₁ ≠ 1 := fun h => hx₁T (hker _ _ h)
  have hpow : ∀ y (hy : y ∈ E₁) (m : ℕ), weylQuotientHom .E6 L ⟨y, hEM₁ hy⟩ ^ m =
      weylQuotientHom .E6 L ⟨y ^ m, hEM₁ (pow_mem hy m)⟩ := by
    intro y hy m
    rw [← map_pow]
    rfl
  have hw₁3 : w₁ ^ 3 = 1 := by
    rw [hw₁, hpow x₁ hx₁ 3]
    have h3 : (⟨x₁ ^ 3, hEM₁ (pow_mem hx₁ 3)⟩ : monomialSubgroup .E6 L) = 1 :=
      Subtype.ext (hE₁.2 x₁ hx₁)
    rw [h3, map_one]
  obtain ⟨m₁, hm₁⟩ : w₁ ∈ modelHomE6.range := hAS₁ x₁ hx₁
  set v := Multiplicative.toAdd m₁.left with hv
  set j := Multiplicative.toAdd m₁.right with hj
  have hw₁word : w₁ = (coxeterSystem .E6).wordProd (modelWordE6 v j) := by
    rw [← hm₁, modelHomE6_eq_wordProd]
  have hmj0 : j = 0 → m₁ = SemidirectProduct.inl (Multiplicative.ofAdd v) := by
    intro hj0
    refine SemidirectProduct.ext ?_ ?_
    · rw [SemidirectProduct.left_inl, hv, ofAdd_toAdd]
    · rw [SemidirectProduct.right_inl, ← ofAdd_toAdd m₁.right, ← hj, hj0, ofAdd_zero]
  have hc1 : j = 0 ∨ v 0 + v 1 + v 2 = 0 := by
    by_contra hcon
    obtain ⟨i, hi⟩ := modelElt_cube_ne v j hcon
    apply hi
    rw [← CFSG.StandardType.TableBExc.wordProd_smul, CFSG.StandardType.TableBExc.wordProd_replicate,
      ← hw₁word, hw₁3, one_smul]
  have hc2 : ¬ (v = 0 ∧ j = 0) := by
    rintro ⟨hv0, hj0⟩
    apply hw₁1
    rw [← hm₁, hmj0 hj0, hv0, ofAdd_zero, map_one, map_one]
  have hc3 : ∀ i : Fin 3, ¬ (j = 0 ∧ (v = Pi.single i 1 ∨ v = Pi.single i 2)) := by
    rintro i ⟨hj0, hvi | hvi⟩
    · apply hAg₁ x₁ hx₁ i
      change w₁ = gE6 i
      rw [← hm₁, hmj0 hj0, hvi]
      change modelHom isModel_E6 _ = _
      rw [modelHom_inl, modelN_single, ZMod.val_one, pow_one]
    · apply hAg₁ (x₁ ^ 2) (pow_mem hx₁ 2) i
      rw [← hpow x₁ hx₁ 2, ← hw₁]
      have hg : w₁ = gE6 i ^ 2 := by
        rw [← hm₁, hmj0 hj0, hvi]
        change modelHom isModel_E6 _ = _
        rw [modelHom_inl, modelN_single]
        rfl
      rw [hg, ← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, gE6_pow_three, one_mul, pow_one]
  obtain ⟨hj0, hvne⟩ | hconjw := modelElt_cases v j hc1 hc2 hc3
  · exact absurd (by show w₁ = _; rw [← hm₁, hmj0 hj0]) (hnofpf x₁ hx₁ v hvne)
  set V := (coxeterSystem .E6).wordProd (conjWordE6 v j) with hV
  have hVw : V * w₁ * V⁻¹ = cE6 := by
    rw [mul_inv_eq_iff_eq_mul]
    refine CFSG.LieType.Chevalley.ext_single fun i => ?_
    rw [hV, hw₁word, cE6, ← CoxeterSystem.wordProd_append, ← CoxeterSystem.wordProd_append,
      CFSG.StandardType.TableBExc.wordProd_smul, CFSG.StandardType.TableBExc.wordProd_smul]
    exact hconjw i
  set A₁ : Subgroup (WeylGroup .E6) :=
    (E₁.subgroupOf (monomialSubgroup .E6 L)).map (weylQuotientHom .E6 L) with hA₁def
  have hmemA : ∀ y (hy : y ∈ E₁), weylQuotientHom .E6 L ⟨y, hEM₁ hy⟩ ∈ A₁ := fun y hy =>
    ⟨⟨y, hEM₁ hy⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
  have hA₁mem : ∀ a ∈ A₁, ∃ y, ∃ hy : y ∈ E₁, weylQuotientHom .E6 L ⟨y, hEM₁ hy⟩ = a := by
    rintro a ⟨⟨y, hyN⟩, hy, rfl⟩
    exact ⟨y, Subgroup.mem_subgroupOf.mp hy, rfl⟩
  have hA₁eq : A₁ = Subgroup.zpowers w₁ := by
    have hle : Subgroup.zpowers w₁ ≤ A₁ := (Subgroup.zpowers_le).mpr (hmemA x₁ hx₁)
    have hcw : Nat.card (Subgroup.zpowers w₁) = 3 := by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime hw₁3 hw₁1
    have hdvd : Nat.card A₁ ∣ 3 ^ 4 := by
      have h := Subgroup.card_map_dvd (E₁.subgroupOf (monomialSubgroup .E6 L))
        (weylQuotientHom .E6 L)
      have hK : Nat.card (E₁.subgroupOf (monomialSubgroup .E6 L)) = 3 ^ 4 := by
        rw [← hcard₁]
        exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEM₁).toEquiv
      rwa [hK] at h
    have h3dvd : 3 ∣ Nat.card A₁ := hcw ▸ Subgroup.card_dvd_of_le hle
    by_contra hne
    have hne3 : Nat.card A₁ ≠ 3 := by
      intro h3
      apply hne
      have : Finite A₁ := Nat.finite_of_card_ne_zero (by rw [h3]; norm_num)
      exact (Subgroup.eq_of_le_of_card_ge hle (by rw [h3, hcw])).symm
    have h9 : 9 ≤ Nat.card A₁ := by
      obtain ⟨k, hk4, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
      have hk1 : 1 ≤ k := by
        rcases Nat.eq_zero_or_pos k with rfl | h
        · rw [hk, pow_zero] at h3dvd
          exact absurd h3dvd (by norm_num)
        · exact h
      have hk2 : 2 ≤ k := by
        rcases eq_or_lt_of_le hk1 with h | h
        · exact absurd (by rw [hk, ← h, pow_one]) hne3
        · exact h
      calc 9 = 3 ^ 2 := by norm_num
        _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
        _ = Nat.card A₁ := hk.symm
    have hAS : A₁ ≤ modelHomE6.range := by
      intro a ha
      obtain ⟨y, hy, rfl⟩ := hA₁mem a ha
      exact hAS₁ y hy
    have hg : ∀ i, gE6 i ∉ A₁ := by
      intro i hi
      obtain ⟨y, hy, hyi⟩ := hA₁mem _ hi
      exact hAg₁ y hy i hyi
    obtain ⟨v', hv', hv'A⟩ := exists_inl_mem A₁ hAS
      ((hE₁.subgroupOf (monomialSubgroup .E6 L)).map (weylQuotientHom .E6 L)) hg h9
    obtain ⟨y, hy, hyv⟩ := hA₁mem _ hv'A
    exact hnofpf y hy (Multiplicative.toAdd v') hv' (by rw [hyv, ofAdd_toAdd])
  set n := canonicalRep (coxeterSystem .E6) L V with hn
  have hnG : n ∈ adjointGroup .E6 L := canonicalRep_mem_adjointGroup (cs := coxeterSystem .E6) L V
  have hnN : n ∈ monomialSubgroup .E6 L := canonicalRep_mem_monomialSubgroup L V
  have hρn : weylQuotientHom .E6 L ⟨n, hnN⟩ = V := weylQuotientHom_eq (mapsRootLines_canonicalRep V)
  have hmem2 : ∀ e', e' ∈ E.map (MulAut.conj (n * g)).toMonoidHom ↔ ∃ y ∈ E₁, e' = n * y * n⁻¹ := by
    intro e'
    constructor
    · rintro ⟨e₀, he₀, rfl⟩
      refine ⟨g * e₀ * g⁻¹, ⟨e₀, he₀, rfl⟩, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    · rintro ⟨y, ⟨e₀, he₀, rfl⟩, rfl⟩
      refine ⟨e₀, he₀, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  have hEM : E.map (MulAut.conj (n * g)).toMonoidHom ≤ monomialSubgroup .E6 L := by
    intro e' he'
    obtain ⟨y, hy, rfl⟩ := (hmem2 e').1 he'
    exact mul_mem (mul_mem hnN (hEM₁ hy)) (inv_mem hnN)
  have hρconj : ∀ y (hy : y ∈ E₁) (h' : n * y * n⁻¹ ∈ monomialSubgroup .E6 L),
      weylQuotientHom .E6 L ⟨n * y * n⁻¹, h'⟩ = V * weylQuotientHom .E6 L ⟨y, hEM₁ hy⟩ * V⁻¹ := by
    intro y hy h'
    have e1 : (⟨n * y * n⁻¹, h'⟩ : monomialSubgroup .E6 L) =
        ⟨n, hnN⟩ * ⟨y, hEM₁ hy⟩ * (⟨n, hnN⟩ : monomialSubgroup .E6 L)⁻¹ := rfl
    rw [e1, map_mul, map_mul, map_inv, hρn]
  refine ⟨n * g, mul_mem hnG hgG, hEM, ?_, n * x₁ * n⁻¹, (hmem2 _).2 ⟨x₁, hx₁, rfl⟩, ?_⟩
  · intro e' he'
    obtain ⟨y, hy, rfl⟩ := (hmem2 e').1 he'
    rw [hρconj y hy]
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hA₁eq ▸ hmemA y hy)
    rw [← hm, ← MulAut.conj_apply, map_zpow, MulAut.conj_apply, hVw]
    exact Subgroup.zpow_mem_zpowers cE6 m
  · rw [hρconj x₁ hx₁, ← hw₁, hVw]

theorem conj_rootDiagUnit_zetaVec {L : Type} [Field L] {x : ModGL .E6 L}
    (hx : x ∈ monomialSubgroup .E6 L) {ζ : Lˣ} (hζ : ζ ^ 3 = 1) (v : Fin Tag.E6.rank → ZMod 3) :
    x * rootDiagUnit .E6 (zetaVec ζ hζ v) * x⁻¹ =
      rootDiagUnit .E6 (zetaVec ζ hζ (adAct .E6 3 (weylQuotientHom .E6 L ⟨x, hx⟩) v)) := by
  have h := conj_rootDiagUnit_of_mem_monoHat (x := ⟨x, monomial_le_monoHat hx⟩) (zetaVec ζ hζ v)
  rw [psiHat_of_mem_monomial hx, weylTuple_zetaVec] at h
  exact h

theorem adAct_zpow_eq_self {w : WeylGroup .E6} {v : Fin Tag.E6.rank → ZMod 3}
    (h : adAct .E6 3 w v = v) (m : ℤ) : adAct .E6 3 (w ^ m) v = v := by
  have hinv : adAct .E6 3 w⁻¹ v = v := by
    conv_lhs => rw [← h]
    rw [← adAct_mul, inv_mul_cancel, adAct_one]
  induction m using Int.induction_on with
  | zero => rw [zpow_zero, adAct_one]
  | succ m ih => rw [zpow_add_one, adAct_mul, h, ih]
  | pred m ih => rw [zpow_sub_one, adAct_mul, hinv, ih]

open scoped Pointwise in
theorem exists_mul_zpow_of_mem_sup_zpowers {G : Type*} [Group G] {H : Subgroup G} {g : G}
    (hc : ∀ h ∈ H, h * g = g * h) {x : G} (hx : x ∈ H ⊔ Subgroup.zpowers g) :
    ∃ h ∈ H, ∃ m : ℤ, x = h * g ^ m := by
  have hgN : g ∈ Subgroup.normalizer (H : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · intro hn
      rw [← hc n hn, mul_inv_cancel_right]
      exact hn
    · intro hn
      have h1 := hc _ hn
      have h2 : n = g * n * g⁻¹ := by
        calc n = g⁻¹ * (g * n * g⁻¹ * g) := by group
          _ = g⁻¹ * (g * (g * n * g⁻¹)) := by rw [h1]
          _ = g * n * g⁻¹ := by group
      rw [h2]
      exact hn
  have hx' : x ∈ ((H : Set G) * (Subgroup.zpowers g : Set G)) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left H (Subgroup.zpowers g)
      ((Subgroup.zpowers_le).mpr hgN)]
    exact hx
  obtain ⟨h, hh, t, ht, rfl⟩ := Set.mem_mul.mp hx'
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht
  exact ⟨h, hh, m, rfl⟩

theorem exists_hyperplane_frame_of_zpowers_c {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {E : Subgroup (ModGL .E6 L)} [Finite E] (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ 4)
    (hnt : ¬ CFSG.StandardType.SCFourCover.E6AdToral E)
    {Hh : Subgroup (ModGL .E6 L)} {e : ModGL .E6 L} (hsplit : E = Hh ⊔ Subgroup.zpowers e)
    (heH : e ∉ Hh)
    (heS : e ∈ closedIdentityComponent
      (adjointGroup .E6 L ⊓ Subgroup.centralizer (E : Set (ModGL .E6 L))))
    {y₀ : ModGL .E6 L} (hy₀ : y₀ ∈ adjointGroup .E6 L)
    (hEM : E.map (MulAut.conj y₀).toMonoidHom ≤ monomialSubgroup .E6 L)
    (hEc : ∀ e' (he' : e' ∈ E.map (MulAut.conj y₀).toMonoidHom),
      weylQuotientHom .E6 L ⟨e', hEM he'⟩ ∈ Subgroup.zpowers cE6)
    {x₂ : ModGL .E6 L} (hx₂ : x₂ ∈ E.map (MulAut.conj y₀).toMonoidHom)
    (hx₂c : weylQuotientHom .E6 L ⟨x₂, hEM hx₂⟩ = cE6) :
    ∃ x : ModGL .E6 L, ∃ hxM : x ∈ monomialSubgroup .E6 L,
      weylQuotientHom .E6 L ⟨x, hxM⟩ = cE6 ∧ x ^ 3 = 1 ∧
      ∃ ζ : Lˣ, ∃ _hζo : orderOf ζ = 3, ∃ hζ : ζ ^ 3 = 1, ∃ k y : Fin 3 → ZMod 3,
        (∀ α ∈ rootFinset .E6, α + cAct α + cAct (cAct α) = 0 → dotZ3 α (combC y) = 0) ∧
        ∑ i, k i * y i = 1 ∧
        Hh.map (MulAut.conj y₀).toMonoidHom = Subgroup.closure
          ((fun v => rootDiagUnit .E6 (zetaVec ζ hζ v)) ''
            {v | ∃ x', ∑ i, k i * x' i = 0 ∧ v = combC x'} ∪ {x}) ∧
        y₀ * e * y₀⁻¹ = rootDiagUnit .E6 (zetaVec ζ hζ (combC y)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL3 : ringChar L ≠ 3 := by rw [ringChar.eq L 2]; decide
  have h30 : (3 : L) ≠ 0 := by
    have h2 : (2 : L) = 0 := by exact_mod_cast CharP.cast_eq_zero L 2
    rw [show (3 : L) = 2 + 1 by norm_num, h2, zero_add]
    exact one_ne_zero
  obtain ⟨ζ, hζ, hζo⟩ := CFSG.HardMathSupport.Lang.E6Descent.TwistedDiag.exists_cube_root
    (Ω := L) h30
  set E₂ := E.map (MulAut.conj y₀).toMonoidHom with hE₂def
  set Ĥ := Hh.map (MulAut.conj y₀).toMonoidHom with hĤdef
  set e₂ := y₀ * e * y₀⁻¹ with he₂def
  have hE₂ : IsElemAbelian 3 E₂ := hE.map _
  have hcard₂ : Nat.card E₂ = 3 ^ 4 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj y₀).injective]
    exact hcard
  have : Finite E₂ :=
    Finite.of_surjective _ ((MulAut.conj y₀).toMonoidHom.subgroupMap_surjective E)
  have hET₂ : ¬ E₂ ≤ torusGroup .E6 L := by
    intro h
    apply hnt
    refine (CFSG.StandardType.SCFourCover.e6AdToral_map_conj hy₀ E).mp
      ⟨1, one_mem _, fun e he => ?_⟩
    simpa using h he
  have hcR : cE6 ∈ modelHomE6.range := ⟨⟨1, Multiplicative.ofAdd 1⟩, modelHomE6_c⟩
  have hcg : ∀ (m : ℤ) (i : Fin 3), cE6 ^ m ≠ gE6 i := cE6_zpow_ne_gE6
  have hc1 : cE6 ≠ 1 := cE6_ne_one
  have hAS₂ : ∀ e' (he' : e' ∈ E₂), weylQuotientHom .E6 L ⟨e', hEM he'⟩ ∈ modelHomE6.range :=
    fun e' he' => (Subgroup.zpowers_le.mpr hcR) (hEc e' he')
  have hAg₂ : ∀ e' (he' : e' ∈ E₂) i, weylQuotientHom .E6 L ⟨e', hEM he'⟩ ≠ gE6 i := by
    intro e' he' i h
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hEc e' he')
    exact hcg m i (hm.trans h)
  have hker : ∀ z (hz : z ∈ monomialSubgroup .E6 L), weylQuotientHom .E6 L ⟨z, hz⟩ = 1 →
      z ∈ torusGroup .E6 L := by
    intro z hz h
    have h' : (⟨z, hz⟩ : monomialSubgroup .E6 L) ∈ (weylQuotientHom .E6 L).ker := h
    rw [CFSG.StandardType.TableBExc.weylQuotientHom_surjective_ker.2,
      Subgroup.mem_subgroupOf] at h'
    exact h'
  have he₂S : e₂ ∈ closedIdentityComponent
      (adjointGroup .E6 L ⊓ Subgroup.centralizer (E₂ : Set (ModGL .E6 L))) := by
    rw [← map_adjoint_centralizer_conj E hy₀, closedIdentityComponent_map_conj]
    exact ⟨e, heS, rfl⟩
  have heE : e ∈ E := by
    rw [hsplit]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers e)
  have he₂E : e₂ ∈ E₂ := ⟨e, heE, rfl⟩
  have hsplit₂ : E₂ = Ĥ ⊔ Subgroup.zpowers e₂ := by
    rw [hE₂def, hsplit, Subgroup.map_sup, MonoidHom.map_zpowers]
    rfl
  have he₂Ĥ : e₂ ∉ Ĥ := by
    rintro ⟨h, hh, hhe⟩
    apply heH
    have : h = e := (MulAut.conj y₀).injective hhe
    exact this ▸ hh
  have hĤE₂ : Ĥ ≤ E₂ := by
    rw [hsplit₂]
    exact le_sup_left
  have hfix : ∀ v, rootDiagUnit .E6 (zetaVec ζ hζ v) ∈ E₂ → adWord .E6 3 wordE6C v = v := by
    intro v hv
    have h1 := conj_rootDiagUnit_zetaVec (hEM hx₂) hζ v
    rw [hx₂c, (hE₂.comm hx₂ hv), mul_inv_cancel_right] at h1
    have h2 := zetaVec_injective hζo hζ (rootDiagUnit_injective h1.symm)
    rw [adWord_eq_adAct]
    exact h2
  have he₂T : e₂ ∈ torusGroup .E6 L :=
    connected_centralizer_le_torus_of_regular hL3 hEM hE₂ hcard₂ hET₂ hAS₂ hAg₂ he₂S
  obtain ⟨u, hu⟩ := NoOffTwE6Three.exists_zetaVec_eq_of_mem_torusGroup_pow_three hζ hζo he₂T
    (hE₂.2 e₂ he₂E)
  obtain ⟨y, rfl⟩ := exists_combC_of_adWord u (hfix u (hu ▸ he₂E))
  have huR : ∀ α ∈ rootFinset .E6, α + cAct α + cAct (cAct α) = 0 →
      dotZ3 α (combC y) = 0 := by
    intro α hα hαc
    obtain ⟨b, hb, hbα⟩ := rootChar_eq_one_of_mem_connected_centralizer hL3 hEM hE₂ hcard₂ hET₂
      hAS₂ hAg₂ hx₂ (mem_rootFinset.mp hα) (by rw [hx₂c, cE6_smul, cE6_smul]; exact hαc) he₂S
    have hbz : b = zetaVec ζ hζ (combC y) := rootDiagUnit_injective (hb.symm.trans hu)
    rw [hbz, NoOffE8Five.rootChar_zetaVec] at hbα
    have h1 : Multiplicative.ofAdd (∑ j, ((α j : ℤ) : ZMod 3) * combC y j) = 1 :=
      (CFSG.RankThree.CentralCover.zmodPowHom_injective hζo hζ) (by rw [hbα, map_one])
    exact congrArg Multiplicative.toAdd h1
  set H := expE ζ hζ Ĥ with hHdef
  have huH : combC y ∉ H := by
    intro h
    apply he₂Ĥ
    rw [hu]
    exact h
  let Dh : Multiplicative (Fin Tag.E6.rank → ZMod 3) →* ModGL .E6 L :=
    { toFun := fun x => rootDiagUnit .E6 (zetaVec ζ hζ (Multiplicative.toAdd x))
      map_one' := by
        have e : zetaVec ζ hζ (0 : Fin Tag.E6.rank → ZMod 3) = 1 := by
          funext i
          change CFSG.RankThree.CentralCover.zmodPowHom ζ hζ (.ofAdd 0) = 1
          rw [ofAdd_zero, map_one]
        change rootDiagUnit .E6 (zetaVec ζ hζ 0) = 1
        rw [e, CFSG.LieType.Chevalley.rootDiagUnit_one]
      map_mul' := fun x x' => by
        have e : zetaVec ζ hζ (Multiplicative.toAdd (x * x')) =
            zetaVec ζ hζ (Multiplicative.toAdd x) * zetaVec ζ hζ (Multiplicative.toAdd x') := by
          funext i
          change CFSG.RankThree.CentralCover.zmodPowHom ζ hζ
              (.ofAdd (Multiplicative.toAdd x i + Multiplicative.toAdd x' i)) =
            CFSG.RankThree.CentralCover.zmodPowHom ζ hζ (.ofAdd (Multiplicative.toAdd x i)) *
              CFSG.RankThree.CentralCover.zmodPowHom ζ hζ (.ofAdd (Multiplicative.toAdd x' i))
          rw [ofAdd_add, map_mul]
        change rootDiagUnit .E6 (zetaVec ζ hζ (Multiplicative.toAdd (x * x'))) = _
        rw [e, CFSG.LieType.Chevalley.rootDiagUnit_mul] }
  have hDh : ∀ v, Dh (Multiplicative.ofAdd v) = rootDiagUnit .E6 (zetaVec ζ hζ v) := fun v => rfl
  have hEA : ∀ w, w ∈ Subgroup.zpowers cE6 ↔
      ∃ e', ∃ he' : e' ∈ E₂, weylQuotientHom .E6 L ⟨e', hEM he'⟩ = w := by
    intro w
    constructor
    · intro hw
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      refine ⟨x₂ ^ m, zpow_mem hx₂ m, ?_⟩
      rw [← hx₂c, ← map_zpow]
      rfl
    · rintro ⟨e', he', rfl⟩
      exact hEc e' he'
  have hDE : ∀ v, adWord .E6 3 wordE6C v = v → rootDiagUnit .E6 (zetaVec ζ hζ v) ∈ E₂ := by
    intro v hv
    refine rootDiagUnit_zetaVec_mem hζo hζ hEM hE₂ hcard₂.ge hEA (Subgroup.zpowers_le.mpr hcR)
      ?_ ?_ ?_
    · intro h
      apply hc1
      have h' := Subgroup.mem_zpowers cE6
      rw [h, Subgroup.mem_bot] at h'
      exact h'
    · intro i h
      have h' : gE6 i ∈ Subgroup.zpowers cE6 := h ▸ Subgroup.mem_zpowers (gE6 i)
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp h'
      exact hcg m i hm
    · intro a ha
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      rw [adWord_eq_adAct] at hv
      exact adAct_zpow_eq_self hv m
  have hspan : ∀ v, adWord .E6 3 wordE6C v = v → ∃ j : ZMod 3, v - j • combC y ∈ H := by
    intro v hv
    have hvE := hDE v hv
    rw [hsplit₂] at hvE
    obtain ⟨h, hh, m, hhm⟩ := exists_mul_zpow_of_mem_sup_zpowers
      (fun h hh => hE₂.comm (hĤE₂ hh) he₂E) hvE
    refine ⟨(m : ZMod 3), ?_⟩
    change rootDiagUnit .E6 (zetaVec ζ hζ (v - (m : ZMod 3) • combC y)) ∈ Ĥ
    rw [Int.cast_smul_eq_zsmul, ← hDh, ofAdd_sub, map_div, ofAdd_zsmul, map_zpow, hDh, hDh, hhm,
      ← hu, mul_div_cancel_right]
    exact hh
  obtain ⟨k, hky, hkH⟩ := exists_planeKey H huH hspan
  obtain ⟨h₀, hh₀, hh₀T⟩ : ∃ h ∈ Ĥ, h ∉ torusGroup .E6 L := by
    by_contra hcon
    push Not at hcon
    apply hET₂
    rw [hsplit₂, sup_le_iff]
    exact ⟨hcon, (Subgroup.zpowers_le).mpr he₂T⟩
  obtain ⟨m₀, hm₀⟩ := Subgroup.mem_zpowers_iff.mp (hEc h₀ (hĤE₂ hh₀))
  have hm₀3 : m₀ % 3 ≠ 0 := by
    intro h
    apply hh₀T
    refine hker h₀ (hEM (hĤE₂ hh₀)) ?_
    rw [← hm₀, zpow_eq_zpow_emod' m₀ cE6_pow_three]
    norm_num [h]
  set x₃ := h₀ ^ m₀ with hx₃def
  have hx₃Ĥ : x₃ ∈ Ĥ := zpow_mem hh₀ m₀
  have hx₃M : x₃ ∈ monomialSubgroup .E6 L := hEM (hĤE₂ hx₃Ĥ)
  have hx₃c : weylQuotientHom .E6 L ⟨x₃, hx₃M⟩ = cE6 := by
    have h1 : weylQuotientHom .E6 L ⟨x₃, hx₃M⟩ =
        (weylQuotientHom .E6 L ⟨h₀, hEM (hĤE₂ hh₀)⟩) ^ m₀ := by
      rw [← map_zpow]
      rfl
    rw [h1, ← hm₀, ← zpow_mul, zpow_eq_zpow_emod' _ cE6_pow_three]
    have hr : m₀ % 3 = 1 ∨ m₀ % 3 = 2 := by omega
    have h2 : m₀ * m₀ % ((3 : ℕ) : ℤ) = 1 := by
      rw [Int.mul_emod]
      rcases hr with hr | hr <;> norm_num [hr]
    rw [h2, zpow_one]
  have hx₃3 : x₃ ^ 3 = 1 := hE₂.2 x₃ (hĤE₂ hx₃Ĥ)
  have hHgen : Ĥ = Subgroup.closure ((fun v => rootDiagUnit .E6 (zetaVec ζ hζ v)) ''
      {v | ∃ x', ∑ i, k i * x' i = 0 ∧ v = combC x'} ∪ {x₃}) := by
    apply le_antisymm
    · intro h hh
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hEc h (hĤE₂ hh))
      have htĤ : h * x₃ ^ (-m) ∈ Ĥ := mul_mem hh (zpow_mem hx₃Ĥ _)
      have htT : h * x₃ ^ (-m) ∈ torusGroup .E6 L := by
        refine hker _ (hEM (hĤE₂ htĤ)) ?_
        have h1 : weylQuotientHom .E6 L ⟨h * x₃ ^ (-m), hEM (hĤE₂ htĤ)⟩ =
            weylQuotientHom .E6 L ⟨h, hEM (hĤE₂ hh)⟩ * (weylQuotientHom .E6 L ⟨x₃, hx₃M⟩) ^ (-m) := by
          rw [← map_zpow, ← map_mul]
          rfl
        rw [h1, hx₃c, ← hm, ← zpow_add, add_neg_cancel, zpow_zero]
      obtain ⟨v, hv⟩ := NoOffTwE6Three.exists_zetaVec_eq_of_mem_torusGroup_pow_three hζ hζo htT
        (hE₂.2 _ (hĤE₂ htĤ))
      obtain ⟨x', rfl⟩ := exists_combC_of_adWord v (hfix v (hv ▸ hĤE₂ htĤ))
      have hx' : ∑ i, k i * x' i = 0 := (hkH x').1 (by
        change rootDiagUnit .E6 (zetaVec ζ hζ (combC x')) ∈ Ĥ
        rw [← hv]
        exact htĤ)
      have hh' : h = (h * x₃ ^ (-m)) * x₃ ^ m := by group
      rw [hh', hv]
      exact mul_mem (Subgroup.subset_closure
          (Set.mem_union_left _ ⟨combC x', ⟨x', hx', rfl⟩, rfl⟩))
        (zpow_mem (Subgroup.subset_closure (Set.mem_union_right _ (Set.mem_singleton x₃))) m)
    · rw [Subgroup.closure_le]
      rintro z (⟨v, ⟨x', hx', rfl⟩, rfl⟩ | hz)
      · exact (hkH x').2 hx'
      · rw [Set.mem_singleton_iff.mp hz]
        exact hx₃Ĥ
  exact ⟨x₃, hx₃M, hx₃c, hx₃3, ζ, hζo, hζ, k, y, huR, hky, hHgen, hu⟩

end CFrame

section Jgeom

open CFSG.StandardType.TwE6HyperplaneTypes CFSG.HardMathSupport.Lang.E6Descent
  CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.ComponentClassification.CatalogueBPrimeJoin


theorem isQuasisimple_jgeom_of_nonToral {Ω : Type} [Field Ω] {Fr : Ω →+* Ω}
    {Hh : Subgroup (ModGL Tag.E6 Ω)}
    [Finite ↥(closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))) ⊓ TwistedDiag.Rgrp Ω Fr)]
    {n : ℕ} (hn : 3 ≤ n) {k : Type} [Field k] [Finite k] [Algebra k Ω] [IsAlgClosure k Ω]
    (hk : Nat.card k = (2 ^ n) ^ 2) (hFr : ∀ c, Fr c = c ^ 2 ^ n)
    (hHF : Hh ≤ TwistedDiag.Rgrp Ω Fr)
    {E : Subgroup (ModGL .E6 Ω)} [Finite E] (hEG : E ≤ adjointGroup .E6 Ω)
    (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ 4)
    (hnt : ¬ CFSG.StandardType.SCFourCover.E6AdToral E)
    {e g : ModGL Tag.E6 Ω} (hsplit : E = Hh ⊔ Subgroup.zpowers e) (heH : e ∉ Hh)
    (heS : e ∈ closedIdentityComponent
      (adjointGroup .E6 Ω ⊓ Subgroup.centralizer (E : Set (ModGL .E6 Ω))))
    (heK : e ∈ closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))))
    (heF : e ∈ TwistedDiag.Rgrp Ω Fr)
    (hgK : g ∈ closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))))
    (hgF : g ∈ TwistedDiag.Rgrp Ω Fr) {t : ℕ} (hg2 : g ^ (2 ^ t) = 1)
    (hinv : g * e * g⁻¹ = e⁻¹) :
    CFSG.IsQuasisimple ((primeResidual 2 ↥(closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))) ⊓ TwistedDiag.Rgrp Ω Fr)).map
        (closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
          Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))) ⊓ TwistedDiag.Rgrp Ω Fr).subtype) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype k := Fintype.ofFinite k
  have : CharP k 2 := charP_of_card_eq_prime_pow (f := 2 * n)
    (by rw [← Nat.card_eq_fintype_card, hk, ← pow_mul, mul_comm])
  have : CharP Ω 2 := charP_of_injective_algebraMap (algebraMap k Ω).injective 2
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  have halg : letI := ZMod.algebra Ω 2; Algebra.IsAlgebraic (ZMod 2) Ω :=
    CFSG.RankThree.PartOne.KE.isAlgebraic_zmod_of_isAlgClosure (k := k)
  have he1 : e ≠ 1 := fun h => heH (h ▸ one_mem Hh)
  have heE : e ∈ E := by
    rw [hsplit]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers e)
  have he3 : e ^ 3 = 1 := hE.2 e heE
  obtain ⟨y₀, hy₀, hEM, hEc, x₂, hx₂, hx₂c⟩ :=
    exists_conj_weylImage_zpowers_c halg hEG hE hcard hnt he1 heS
  obtain ⟨x, hxM, hxc, hx3, ζ, hζo, hζ, kk, y, huR, hky, hHgen, hey⟩ :=
    exists_hyperplane_frame_of_zpowers_c hE hcard hnt hsplit heH heS hy₀ hEM hEc hx₂ hx₂c
  have heT : y₀ * e * y₀⁻¹ ∈ torusGroup .E6 Ω := by
    rw [hey]
    exact CFSG.LieType.Chevalley.rootDiagUnit_mem_torusGroup _
  set Hs : Set (Fin Tag.E6.rank → ZMod 3) := {v | ∃ x', ∑ i, kk i * x' i = 0 ∧ v = combC x'}
    with hHs
  have hsig : ∀ α, (∀ v ∈ Hs, NoOffTwE6Three.pairFormE6 α v = 0) ↔ sigmaTest kk α := by
    intro α
    constructor
    · intro h x' hx'
      exact h _ ⟨x', hx', rfl⟩
    · rintro h v ⟨x', hx', rfl⟩
      exact h x' hx'
  have hz : ∀ v α, rootChar (zetaVec ζ hζ v) α = 1 ↔ NoOffTwE6Three.pairFormE6 α v = 0 := by
    intro v α
    rw [NoOffE8Five.rootChar_zetaVec]
    constructor
    · intro h
      have h1 : Multiplicative.ofAdd (∑ j, ((α j : ℤ) : ZMod 3) * v j) = 1 :=
        (CFSG.RankThree.CentralCover.zmodPowHom_injective hζo hζ) (by rw [h, map_one])
      simpa [NoOffTwE6Three.pairFormE6] using congrArg Multiplicative.toAdd h1
    · intro h
      rw [show (∑ j, ((α j : ℤ) : ZMod 3) * v j) = 0 by simpa [NoOffTwE6Three.pairFormE6] using h, ofAdd_zero,
        map_one]
  rcases planeTypes_c kk ⟨y, huR, hky⟩ with hempty | ⟨β, hβF, hβS, ho1, ho2, ho3, ℓ, hℓ, hℓ1⟩ |
    hfix
  ·
    exfalso
    set H' := Hh.map (MulAut.conj y₀).toMonoidHom with hH'
    let a : Hs → Fin Tag.E6.rank → Ωˣ := fun v => zetaVec ζ hζ (v : Fin Tag.E6.rank → ZMod 3)
    have ha : ∀ i, rootDiagUnit .E6 (a i) ∈ H' := fun i => by
      rw [hHgen]
      exact Subgroup.subset_closure (Set.mem_union_left _ ⟨i.1, i.2, rfl⟩)
    have hkerA : familyKernel a = ∅ := by
      ext α
      simp only [familyKernel, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro hα hall
      apply hempty α (mem_rootFinset.mpr hα)
      rw [← hsig]
      intro v hv
      exact (hz v α).1 (hall ⟨v, hv⟩)
    have hfam : familyGroup (K := Ω) a = torusGroup .E6 Ω := by
      rw [familyGroup, hkerA]
      simp only [rootSpan, Set.mem_empty_iff_false, iSup_false, iSup_bot, sup_bot_eq]
    have hKT : ∀ z, z ∈ closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
        Subgroup.centralizer (H' : Set (ModGL Tag.E6 Ω))) → z ∈ torusGroup .E6 Ω := by
      intro z hz'
      have h := closedIdentityComponent_le_familyGroup_inf_centralizer a ha hz'
      rw [hfam] at h
      exact h.1
    have hgT := hKT _ ((TwE6FixedComponent.conj_mem_closedIdentityComponent_iff hy₀ g).2 hgK)
    have heT' := hKT _ ((TwE6FixedComponent.conj_mem_closedIdentityComponent_iff hy₀ e).2 heK)
    obtain ⟨bg, hbg⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hgT
    obtain ⟨be, hbe⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup heT'
    have hcomm : (y₀ * g * y₀⁻¹) * (y₀ * e * y₀⁻¹) = (y₀ * e * y₀⁻¹) * (y₀ * g * y₀⁻¹) := by
      rw [hbg, hbe, ← CFSG.LieType.Chevalley.rootDiagUnit_mul,
        ← CFSG.LieType.Chevalley.rootDiagUnit_mul, mul_comm]
    have hge : g * e = e * g := by
      have h := congrArg (fun v => y₀⁻¹ * v * y₀) hcomm
      rw [show y₀⁻¹ * (y₀ * g * y₀⁻¹ * (y₀ * e * y₀⁻¹)) * y₀ = g * e by group,
        show y₀⁻¹ * (y₀ * e * y₀⁻¹ * (y₀ * g * y₀⁻¹)) * y₀ = e * g by group] at h
      exact h
    have hee : e = e⁻¹ := by rw [← hinv, hge, mul_inv_cancel_right]
    apply he1
    have h2 : e ^ 2 = 1 := by
      rw [sq]
      nth_rewrite 2 [hee]
      exact mul_inv_cancel e
    calc e = e ^ 3 * (e ^ 2)⁻¹ := by group
      _ = 1 := by rw [he3, h2]; group
  ·
    have hβr : IsRoot .E6 β := mem_rootFinset.mp (Finset.mem_filter.mp hβF).1
    have hcβ : IsRoot .E6 (cAct β) := by
      rw [← cE6_smul]
      exact CFSG.LieType.Chevalley.IsRoot.smul hβr cE6
    have hccβ : IsRoot .E6 (cAct (cAct β)) := by
      rw [← cE6_smul]
      exact CFSG.LieType.Chevalley.IsRoot.smul hcβ cE6
    refine TwE6FixedComponent.isQuasisimple_jgeom_of_monomial_orbit hn hk hFr hHF hy₀ hxM hx3
      hζo hζ (H := Hs) hHgen hβr ?_ ?_ (ℓ₁ := Sum.inr ⟨ℓ, mem_rootFinset.mp hℓ⟩) ?_ heK heF he1 he3
      hgK hgF hg2 hinv heT
    · simp only [hxc, cE6_smul]
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
          Matrix.tail_cons, ne_eq, not_true_eq_false] at hij ⊢
      · exact ho1
      · exact ho2
      · exact (iform_comm _ _).trans ho1
      · exact ho3
      · exact (iform_comm _ _).trans ho2
      · exact (iform_comm _ _).trans ho3
    · simp only [hxc, cE6_smul]
      intro α
      rw [hsig]
      simp only [CFSG.RankThree.PartOne.KE.threeRootSet, Set.mem_insert_iff,
        Set.mem_singleton_iff]
      constructor
      · rintro ⟨hα, hs⟩
        exact (hβS α (mem_rootFinset.mpr hα)).1 hs
      · intro hα
        have hr : IsRoot .E6 α := by
          rcases hα with rfl | rfl | rfl | rfl | rfl | rfl
          exacts [hβr, CFSG.LieType.Chevalley.IsRoot.neg hβr, hcβ,
            CFSG.LieType.Chevalley.IsRoot.neg hcβ, hccβ, CFSG.LieType.Chevalley.IsRoot.neg hccβ]
        exact ⟨hr, (hβS α (mem_rootFinset.mpr hr)).2 hα⟩
    · simp only [hxc, cE6_smul, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      exact hℓ1
  ·
    have hk0 : ∀ x' : Fin 3 → ZMod 3, ∑ i, kk i * x' i = 0 ↔ x' 0 = 0 := by
      intro x'
      rcases hfix with rfl | rfl
      · simp [Fin.sum_univ_three]
      · simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, zero_mul, add_zero]
        generalize x' 0 = c
        revert c
        decide
    have hy0 : y 0 ≠ 0 := by
      intro h0
      have h := hky
      rcases hfix with rfl | rfl <;>
        simp [Fin.sum_univ_three, h0] at h
    have hHgen' : Hh.map (MulAut.conj y₀).toMonoidHom = Subgroup.closure
        ((fun v => rootDiagUnit .E6 (zetaVec ζ hζ v)) ''
          {v | ∃ x', x' 0 = 0 ∧ v = combC x'} ∪ {x}) := by
      rw [hHgen]
      congr 3
      ext v
      simp only [Set.mem_setOf_eq, hHs, hk0]
    rcases TwE6FixedA2Type.isQuasisimple_jgeom_or_centralizes_fixedA2 hn hk hFr hHF hy₀ hxM hxc
        hζo hζ hHgen' heK heF he1 he3 hgK hgF hg2 hinv hey with hq | hcent
    · exact hq
    · exact TwE6FixedA2SL3.isQuasisimple_jgeom_of_centralizes_fixedA2 hn hk hFr hHF hy₀ hζo hζ
        hHgen' hcent heK heF he1 he3 hgK hgF hg2 hinv hy0 hey

end Jgeom

section OriginalActors

open CFSG.StandardType.TwE6HyperplaneTypes CFSG.HardMathSupport.Lang.E6Descent
  CFSG.ComponentClassification.CatalogueBPrimeJoin SCFourCover NoOffTwE6Three
  CFSG.HardMathSupport.Timmesfeld.CrossChar


variable {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2)
  (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n) {Ω : Type} [Field Ω] [Algebra K Ω]
  [IsAlgClosure K Ω] (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ n)
  (ε : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) ≃* TwE6Delta.RecipeR K n)
  (hε : ∀ x : MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
    MulAut.congr ε x ∈ TwE6Delta.RecipeI K n ↔ x ∈ (RecipeExcLang.twConj K σ).range)

theorem isQuasisimple_jgeom_of_tableB
    (hn3 : 3 ≤ n) {L' : Type} [Group L'] [Finite L']
    {ψ : L' →* TwE6Delta.RecipeR K n} {A : Subgroup (MulAut L')}
    (hTB : GGTorusTBGroup 3 4 (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n) L' ψ A)
    (hnt : ¬ E6AdToral (rgrpModel hn hK σ hσ Fr hFr ε (TypeA.inducedSub ψ A)))
    {g : L'} (hg : MulAut.conj g ∈ Subgroup.normalizer (A : Set (MulAut L')))
    (hφ : GGIsReflection 3 (ggConjAut A hg)) {m : ℕ} (hg2 : g ^ (2 ^ m) = 1) :
    let γ := recipeActorModelEquiv hn hK σ hσ Fr hFr ε hε hTB.1 hTB.2.1 hTB.2.2.1 hTB.2.2.2.2.1
    let Hh := ((ggConjAut A hg).toMonoidHom.eqLocus (MonoidHom.id A)).map
      ((rgrpModel hn hK σ hσ Fr hFr ε (TypeA.inducedSub ψ A)).subtype.comp γ.toMonoidHom)
    let Kc := closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω)))
    let KF := Kc ⊓ TwistedDiag.Rgrp Ω Fr
    CFSG.IsQuasisimple ((primeResidual 2 ↥KF).map KF.subtype) := by
  intro γ Hh Kc KF
  classical
  have : CharP K 2 := CFSG.StandardType.charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  have : CharP Ω 2 := charP_of_injective_algebraMap (algebraMap K Ω).injective 2
  have hA := hTB.2.2.2.1
  have : Finite (MulAut L') := Finite.of_injective (fun a : MulAut L' => (a : L' → L'))
    (fun _ _ h => MulEquiv.ext (congrFun h))
  have : Finite A := inferInstance
  have hcardA : Nat.card A = 3 ^ 4 := le_antisymm
    (card_le_four_of_not_e6AdToral_rgrpModel_of_cover hn hK σ hσ Fr hFr ε hε
      hTB.1 hTB.2.1 hTB.2.2.1 hTB.2.2.2.1 hTB.2.2.2.2.1 hnt) hTB.2.2.2.2.2.1
  have hcardE : Nat.card (rgrpModel hn hK σ hσ Fr hFr ε (TypeA.inducedSub ψ A)) = 3 ^ 4 := by
    rw [card_rgrpModel hn hK σ hσ Fr hFr ε hε (inducedSub_subset hTB.1 hTB.2.2.2.2.1),
      TypeA.card_inducedSub hTB.1 hTB.2.1 hTB.2.2.1
        (fun a ha => (hTB.2.2.2.2.1 a ha).imp fun _ h => h.2), hcardA]
  have : Finite (rgrpModel hn hK σ hσ Fr hFr ε (TypeA.inducedSub ψ A)) :=
    Nat.finite_of_card_ne_zero (hcardE ▸ (by norm_num : 3 ^ 4 ≠ 0))
  have hEG : rgrpModel hn hK σ hσ Fr hFr ε (TypeA.inducedSub ψ A) ≤ adjointGroup .E6 Ω :=
    fun x hx => ((TwistedDiag.mem_Rgrp _).mp
    (rgrpModel_le_Rgrp hn hK σ hσ Fr hFr ε _ hx)).1
  have hE := isElemAbelian_rgrpModel hn hK σ hσ Fr hFr ε
    (TypeA.isElemAbelian_inducedSub hTB.1 hTB.2.2.2.1)
  have hHh : rgrpModel hn hK σ hσ Fr hFr ε (TypeA.inducedSub ψ
      (((ggConjAut A hg).toMonoidHom.eqLocus (MonoidHom.id A)).map A.subtype)) = Hh :=
    rgrpModel_fixedHyperplane_eq hn hK σ hσ Fr hFr ε hε hTB.1 hTB.2.1 hTB.2.2.1 hTB.2.2.2.2.1
  obtain ⟨e, he1, heinv⟩ := hφ.exists_inverted_ne_one Nat.prime_three
  have hgK := given_two_realizer_mem_connected_hyperplane hn hK σ hσ Fr hFr ε hε
    hTB.1 hTB.2.1 hTB.2.2.1 hTB.2.2.2.2.1 hA hφ hg rfl m hg2
  rw [hHh] at hgK
  have heK := negative_recipe_actor_mem_connected_hyperplane_of_reflection
    hn hK σ hσ Fr hFr ε hε hTB.1 hTB.2.1 hTB.2.2.1 hTB.2.2.2.2.1 hA hφ hg rfl heinv
  rw [hHh] at heK
  have heS := negative_mem_full_connected_centralizer_of_actual_reflection_of_connected
    hn hK σ hσ Fr hFr ε hε hTB hnt hg rfl hφ he1 heinv
  have hsplit0 := rgrpModel_eq_fixedHyperplane_sup_negative hn hK σ hσ Fr hFr ε hε
    hTB.1 hTB.2.1 hTB.2.2.1 hTB.2.2.2.2.1 hA hφ he1 heinv
  rw [hHh] at hsplit0
  have hsplit : rgrpModel hn hK σ hσ Fr hFr ε (TypeA.inducedSub ψ A) =
      Hh ⊔ Subgroup.zpowers (γ e : ModGL .E6 Ω) := hsplit0
  have he3 : e ^ 3 = 1 := Subtype.ext (hA.2 e e.2)
  have heH : (γ e : ModGL .E6 Ω) ∉ Hh := by
    rintro ⟨a, ha, hae⟩
    have hae' : a = e := γ.injective (Subtype.ext hae)
    have hfix : ggConjAut A hg e = e := by
      rw [← hae']
      exact ha
    apply he1
    have hee : e = e⁻¹ := by rw [← heinv, hfix]
    have h2 : e ^ 2 = 1 := by
      rw [sq]
      nth_rewrite 2 [hee]
      exact mul_inv_cancel e
    calc e = e ^ 3 * (e ^ 2)⁻¹ := by group
      _ = 1 := by rw [he3, h2]; group
  have hHF : Hh ≤ TwistedDiag.Rgrp Ω Fr := by
    rintro _ ⟨a, -, rfl⟩
    exact rgrpModel_le_Rgrp hn hK σ hσ Fr hFr ε _ (γ a).2
  have heF : (γ e : ModGL .E6 Ω) ∈ TwistedDiag.Rgrp Ω Fr :=
    rgrpModel_le_Rgrp hn hK σ hσ Fr hFr ε _ (γ e).2
  set g0 : ModGL Tag.E6 Ω := recipeMatrixHom σ ε (ψ := ψ) g with hg0
  have hg0F : g0 ∈ TwistedDiag.Rgrp Ω Fr := by
    let r := twInndiagEquivRgrp hn hK σ hσ Fr hFr
      ⟨ε.symm (ψ g), RecipeExcLang.graphFixedRootGroup_le_twInndiag σ (ε.symm (ψ g)).2⟩
    have hr : r.1 = g0 := (twInndiagEquivRgrp_apply hn hK σ hσ Fr hFr _).trans
      (recipeMatrixHom_apply σ ε (ψ := ψ) g).symm
    exact hr ▸ r.2
  have hg0order : orderOf g0 = 2 := by
    rw [hg0]
    exact orderOf_recipeMatrixHom_of_two_element_reflection hn hK σ hσ Fr hFr ε hε
      hTB hnt hg hφ hg2
  have hg02 : g0 ^ (2 ^ 1) = 1 := by
    simpa [hg0order] using pow_orderOf_eq_one g0
  have hinv : g0 * (γ e : ModGL .E6 Ω) * g0⁻¹ = (γ e : ModGL .E6 Ω)⁻¹ := by
    rw [← recipeActorModelEquiv_conj hn hK σ hσ Fr hFr ε hε hTB.1 hTB.2.1 hTB.2.2.1
      hTB.2.2.2.2.1 hg e, heinv, map_inv, Subgroup.coe_inv]
  have hfin : Finite (TwistedDiag.Rgrp Ω Fr) :=
    (CFSG.RankThree.Classical2.twisted_E6_full_rational_fixed_group_order Nat.prime_two hn K hK σ.toRingHom hσ Ω Fr hFr).1
  have : Finite KF := Finite.of_injective (Subgroup.inclusion (inf_le_right : KF ≤ _))
    (Subgroup.inclusion_injective _)
  exact isQuasisimple_jgeom_of_nonToral hn3 (k := K) hK hFr hHF hEG hE hcardE hnt hsplit heH
    heS heK heF hgK hg0F hg02 hinv

end OriginalActors

end CFSG.StandardType.TwE6HyperplaneFrame

end
