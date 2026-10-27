module

public import CFSG.LocalAnalysis.StandardType.GGTwE6SCFourModel
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeAEndModel
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUDefs
public import CFSG.LieType.Chevalley.TwistedE6NormalFormActors
import CFSG.LocalAnalysis.StandardType.GGTwE6SCFourInverter
import CFSG.LocalAnalysis.StandardType.GGTwE6SCFourCoroot
import CFSG.LocalAnalysis.StandardType.GGTwE6SCFourCover
import CFSG.LocalAnalysis.StandardType.GGTwE6SCFourRetype
import CFSG.LocalAnalysis.GLTheoremA.CatA.T156GTwE6Fix
import CFSG.HardMathSupport.Malle.E27Lie.ExcCross.TwE6Core

public section

namespace CFSG.StandardType.KG87B

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Lang.E6Descent
  CFSG.RankThree.Classical2 CFSG.StandardType.NoOffTwE6Three CFSG.RankThree.PartOne.KE
  CFSG.StandardType.SCFourCover

private theorem twistE6_twistE6
    {Ω : Type} [Field Ω] (Fr₀ : Ω →+* Ω) (y : ModGL Tag.E6 Ω) :
    twistE6 Ω Fr₀ (twistE6 Ω Fr₀ y) = Units.map (entrywiseHom (Fr₀.comp Fr₀)) y := by
  have hP : diagramMap TwistTag.E6 Ω * diagramMap TwistTag.E6 Ω = 1 := by
    rw [← sq]
    exact diagramMap_pow_order TwistTag.E6 Ω
  have key : ∀ z : ModGL TwistTag.E6.tag Ω,
      twistHom TwistTag.E6 Ω Fr₀ (twistHom TwistTag.E6 Ω Fr₀ z) =
        Units.map (entrywiseHom (Fr₀.comp Fr₀)) z := fun z => by
    rw [twistHom_apply, twistHom_apply, map_mul, map_mul, map_inv,
      units_map_entrywiseHom_diagramMap, units_map_entrywiseHom_comp]
    calc diagramMap TwistTag.E6 Ω * (diagramMap TwistTag.E6 Ω *
          Units.map (entrywiseHom (Fr₀.comp Fr₀)) z * (diagramMap TwistTag.E6 Ω)⁻¹) *
            (diagramMap TwistTag.E6 Ω)⁻¹ =
          diagramMap TwistTag.E6 Ω * diagramMap TwistTag.E6 Ω *
            Units.map (entrywiseHom (Fr₀.comp Fr₀)) z *
              ((diagramMap TwistTag.E6 Ω)⁻¹ * (diagramMap TwistTag.E6 Ω)⁻¹) := by
          simp only [mul_assoc]
      _ = Units.map (entrywiseHom (Fr₀.comp Fr₀)) z := by
          rw [← mul_inv_rev, hP, inv_one, one_mul, mul_one]
  exact key y

private theorem twistE6_units_map_entrywiseHom {Ω : Type} [Field Ω] {Fr₀ Fr : Ω →+* Ω}
    (h : Fr₀.comp (Fr₀.comp Fr₀) = Fr) (y : ModGL Tag.E6 Ω) :
    twistE6 Ω Fr₀ (Units.map (entrywiseHom (Fr₀.comp Fr₀)) y) = twistE6 Ω Fr y := by
  have key : ∀ z : ModGL TwistTag.E6.tag Ω,
      twistHom TwistTag.E6 Ω Fr₀ (Units.map (entrywiseHom (Fr₀.comp Fr₀)) z) =
        twistHom TwistTag.E6 Ω Fr z := fun z => by
    rw [twistHom_apply, twistHom_apply, units_map_entrywiseHom_comp, h]
  exact key y

private theorem mem_Cgrp_of_mul_self
    {n : ℕ} (hn : 1 ≤ n) {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ 2 ^ n) {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ n) (h3 : 3 ∣ 2 ^ n + 1) {x : ModGL Tag.E6 Ω}
    (hx : x ∈ TwistedDiag.Rgrp Ω Fr) (hx2 : x * x = 1) :
    x ∈ TwistedDiag.Cgrp K σ.toRingHom Ω := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hCn, hCi, -⟩ :=
    TwistedDiag.cgrp_facts (ℓ := 2) (f := n) hn K hK σ.toRingHom hσ h3 Ω Fr hFr
  have := hCn
  have h1 := Subgroup.pow_index_mem
    ((TwistedDiag.Cgrp K σ.toRingHom Ω).subgroupOf (TwistedDiag.Rgrp Ω Fr)) ⟨x, hx⟩
  have hidx : ((TwistedDiag.Cgrp K σ.toRingHom Ω).subgroupOf
      (TwistedDiag.Rgrp Ω Fr)).index = 3 := hCi
  rw [hidx] at h1
  have h : x ^ 3 ∈ TwistedDiag.Cgrp K σ.toRingHom Ω := Subgroup.mem_subgroupOf.1 h1
  rwa [show x ^ 3 = x by rw [pow_succ, pow_two, hx2, one_mul]] at h

private theorem conj_weylElt_mem_Rgrp
    {Ω : Type} [Field Ω]
    (Fr₀ : Ω →+* Ω) {g0 : ModGL Tag.E6 Ω} (hg0 : g0 ∈ adjointGroup Tag.E6 Ω)
    (hgn : g0⁻¹ * twistE6 Ω Fr₀ g0 = TwistedDiag.n0 Ω) (i : Fin Tag.E6.rank) :
    g0 * weylElt Tag.E6 Ω i 1 * g0⁻¹ ∈ TwistedDiag.Rgrp Ω Fr₀ := by
  refine (TwistedDiag.mem_thetaFixed_iff_conj Fr₀ hg0 hgn _).1
    ⟨weylElt_mem_adjointGroup (τ := Tag.E6) i 1, ?_⟩
  change TwistedDiag.theta Fr₀ (weylElt Tag.E6 Ω i 1) = weylElt Tag.E6 Ω i 1
  rw [TwistedDiag.theta_apply]
  exact CFSG.HardMathSupport.Malle.E27Lie.ExcCross.weylElt_twistFixed6 (L := Ω) Fr₀
    (fun u => twE6W0_smul u) i

private theorem conj_torusElt_mem_Rgrp
    {Ω : Type} [Field Ω]
    [IsAlgClosed Ω] {d : ℕ} (Fr₀ : Ω →+* Ω) (hFr₀ : ∀ c, Fr₀ c = c ^ 2 ^ d)
    (h3 : 3 ∣ 2 ^ d + 1) {g0 : ModGL Tag.E6 Ω} (hg0 : g0 ∈ adjointGroup Tag.E6 Ω)
    (hgn : g0⁻¹ * twistE6 Ω Fr₀ g0 = TwistedDiag.n0 Ω) {ζ : Ωˣ} (hζ : ζ ^ 3 = 1)
    (i : Fin Tag.E6.rank) : g0 * torusElt Tag.E6 Ω i ζ * g0⁻¹ ∈ TwistedDiag.Rgrp Ω Fr₀ := by
  have hb : ∀ j, (fun j => ζ ^ Tag.E6.cartan i j) j ^ 3 = 1 := fun j => by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hζ, one_zpow]
  rw [torusElt_eq_rootDiagUnit]
  exact TwE6DD2.conj_cubeTorus_le_Rgrp Fr₀ hFr₀ h3 hg0 hgn
    ⟨_, TwE6DD2.rootDiagUnit_mem_cubeTorus hb, rfl⟩

private theorem rgrpRecipeAut_apply_eq
    {n : ℕ} (hn : 1 ≤ n) {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ 2 ^ n) {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ n)
    (ε : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) ≃* TwE6Delta.RecipeR K n)
    (r : ↥(TwistedDiag.Rgrp Ω Fr)) {c c' : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)}
    (h : (r : ModGL Tag.E6 Ω) * baseChangeGL (τ := Tag.E6) (algebraMap K Ω) c.1 *
      (r : ModGL Tag.E6 Ω)⁻¹ = baseChangeGL (τ := Tag.E6) (algebraMap K Ω) c'.1) :
    rgrpRecipeAut hn hK σ hσ Fr hFr ε r (ε c) = ε c' := by
  rw [rgrpRecipeAut_apply]
  congr 1
  refine Subtype.ext (baseChangeGL_injective (τ := Tag.E6) (algebraMap K Ω) ?_)
  rw [← h]
  have key : ∀ a b : ModGL TwistTag.E6.tag K,
      baseChangeGL (τ := TwistTag.E6.tag) (algebraMap K Ω) (a * b * a⁻¹) =
        baseChangeGL (τ := TwistTag.E6.tag) (algebraMap K Ω) a *
          baseChangeGL (τ := TwistTag.E6.tag) (algebraMap K Ω) b *
            (baseChangeGL (τ := TwistTag.E6.tag) (algebraMap K Ω) a)⁻¹ := fun a b => by
    rw [map_mul, map_mul, map_inv]
  obtain ⟨w, rfl⟩ := (twInndiagEquivRgrp hn hK σ hσ Fr hFr).surjective r
  rw [rgrpConjAut_apply_baseChange, RecipeExcLang.coe_twConj]
  exact key w.1 c.1

private theorem mem_rgrpModel_of_inverts
    {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n) {Ω : Type} [Field Ω] [Algebra K Ω]
    [IsAlgClosure K Ω] (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ n)
    (ε : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) ≃* TwE6Delta.RecipeR K n)
    (hε : ∀ x : MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
      MulAut.congr ε x ∈ TwE6Delta.RecipeI K n ↔ x ∈ (RecipeExcLang.twConj K σ).range)
    (h3 : 3 ∣ 2 ^ n + 1) {L' : Type} [Group L'] {ψ : L' →* TwE6Delta.RecipeR K n}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    {A A₀ : Subgroup (MulAut L')}
    (hA₀ : ∀ a, a ∈ A₀ ↔ a ∈ A ∧ ∃ φ ∈ TwE6Delta.RecipeI K n, ∀ l, φ (ψ l) = ψ (a l))
    {β : MulAut (TwE6Delta.RecipeR K n)} {b : MulAut L'} (hb : ∀ l, β (ψ l) = ψ (b l))
    (hAb : ∀ a ∈ A, ∃ a₀ ∈ A₀, ∃ j : ℕ, a = a₀ * b ^ j) (hSC : GGTorusSelfCent 3 A)
    {u t : ModGL Tag.E6 Ω} (huR : u ∈ TwistedDiag.Rgrp Ω Fr) (htR : t ∈ TwistedDiag.Rgrp Ω Fr)
    (hu3 : u ^ 3 = 1) (ht2 : t * t = 1) (htu : t * u * t⁻¹ = u⁻¹)
    (hβu : ∀ c : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
      baseChangeGL (τ := Tag.E6) (algebraMap K Ω) c.1 = u → β (ε c) = ε c)
    (hβt : ∀ c : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
      baseChangeGL (τ := Tag.E6) (algebraMap K Ω) c.1 = t → β (ε c) = ε c)
    (hmodel : ∀ x ∈ rgrpModel hn hK σ hσ Fr hFr ε (TypeA.inducedSub ψ A₀),
      x * u = u * x ∧ ∃ k : ℕ, x * t * x⁻¹ = t * u ^ k) :
    u ∈ rgrpModel hn hK σ hσ Fr hFr ε (TypeA.inducedSub ψ A₀) := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have htC := mem_Cgrp_of_mul_self hn hK σ hσ Fr hFr h3 htR ht2
  have htuC := mem_Cgrp_of_mul_self hn hK σ hσ Fr hFr h3 (mul_mem htR huR) (by
    rw [show t * u * (t * u) = t * u * t⁻¹ * u by rw [htinv, mul_assoc (t * u)], htu,
      inv_mul_cancel])
  have huC : u ∈ TwistedDiag.Cgrp K σ.toRingHom Ω := by
    have h := mul_mem (inv_mem htC) htuC
    rwa [inv_mul_cancel_left] at h
  obtain ⟨cu, hcu, rfl⟩ := huC
  obtain ⟨ct, hct, rfl⟩ := htC
  set Cu : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) := ⟨cu, hcu⟩
  set Ct : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) := ⟨ct, hct⟩
  have hι : ∀ {c c' : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)},
      baseChangeGL (τ := Tag.E6) (algebraMap K Ω) c.1 =
        baseChangeGL (τ := Tag.E6) (algebraMap K Ω) c'.1 → ε c = ε c' := fun h =>
    congrArg ε (Subtype.ext (baseChangeGL_injective (τ := Tag.E6) (algebraMap K Ω) h))
  have hmul : ∀ c₁ c₂ : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
      baseChangeGL (τ := Tag.E6) (algebraMap K Ω) (c₁ * c₂).1 =
        baseChangeGL (τ := Tag.E6) (algebraMap K Ω) c₁.1 *
          baseChangeGL (τ := Tag.E6) (algebraMap K Ω) c₂.1 := fun c₁ c₂ => by
    rw [Subgroup.coe_mul]
    exact map_mul (baseChangeGL (τ := TwistTag.E6.tag) (algebraMap K Ω)) _ _
  have hinv : ∀ c : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
      baseChangeGL (τ := Tag.E6) (algebraMap K Ω) c⁻¹.1 =
        (baseChangeGL (τ := Tag.E6) (algebraMap K Ω) c.1)⁻¹ := fun c => by
    rw [Subgroup.coe_inv]
    exact map_inv (baseChangeGL (τ := TwistTag.E6.tag) (algebraMap K Ω)) _
  have hpow : ∀ (c : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) (m : ℕ),
      baseChangeGL (τ := Tag.E6) (algebraMap K Ω) (c ^ m).1 =
        baseChangeGL (τ := Tag.E6) (algebraMap K Ω) c.1 ^ m := fun c m => by
    rw [Subgroup.coe_pow]
    exact map_pow (baseChangeGL (τ := TwistTag.E6.tag) (algebraMap K Ω)) _ _
  have hU3 : ε Cu ^ 3 = 1 := by
    rw [← map_pow, ← map_one ε]
    refine hι ?_
    rw [hpow]
    refine hu3.trans ?_
    rw [Subgroup.coe_one]
    exact (map_one (baseChangeGL (τ := TwistTag.E6.tag) (algebraMap K Ω))).symm
  have hTU : ε Ct * ε Cu * (ε Ct)⁻¹ = (ε Cu)⁻¹ := by
    rw [← map_mul, ← map_inv, ← map_mul, ← map_inv]
    refine hι ?_
    rw [hmul, hmul, hinv, hinv]
    exact htu
  have hβpow : ∀ (j : ℕ) (m : TwE6Delta.RecipeR K n), β m = m → (β ^ j) m = m := by
    intro j m hm
    induction j with
    | zero => rfl
    | succ j ih => rw [pow_succ, MulAut.mul_apply, hm, ih]
  obtain ⟨a, ha, hconj⟩ := exists_induces_conj_of_inverts hψ hker hSC hU3 hTU fun a ha => by
    obtain ⟨a₀, ha₀, j, rfl⟩ := hAb a ha
    obtain ⟨-, φ, hφI, hφ⟩ := (hA₀ a₀).1 ha₀
    obtain ⟨r, rfl⟩ := (mem_range_rgrpRecipeAut hn hK σ hσ Fr hFr ε hε φ).2 hφI
    obtain ⟨hcomm, k, hk⟩ := hmodel r ((mem_rgrpModel hn hK σ hσ Fr hFr ε).2
      ⟨r.2, TypeA.mem_inducedSub.2 ⟨a₀, ha₀, hφ⟩⟩)
    have h1 : rgrpRecipeAut hn hK σ hσ Fr hFr ε r (ε Cu) = ε Cu :=
      rgrpRecipeAut_apply_eq hn hK σ hσ Fr hFr ε r (by
        rw [mul_inv_eq_iff_eq_mul]
        exact hcomm)
    have h2 : rgrpRecipeAut hn hK σ hσ Fr hFr ε r (ε Ct) = ε Ct * ε Cu ^ (k : ℤ) := by
      rw [zpow_natCast, ← map_pow, ← map_mul]
      refine rgrpRecipeAut_apply_eq hn hK σ hσ Fr hFr ε r ?_
      rw [hmul, hpow]
      exact hk
    refine ⟨rgrpRecipeAut hn hK σ hσ Fr hFr ε r * β ^ j, fun l => ?_, ?_, k, ?_⟩
    · rw [MulAut.mul_apply, TypeA.induced_pow ψ hb j l, hφ, MulAut.mul_apply]
    · rw [MulAut.mul_apply, hβpow j _ (hβu Cu rfl), h1]
    · rw [MulAut.mul_apply, hβpow j _ (hβt Ct rfl), h2]
  have hφu : ∀ l, rgrpRecipeAut hn hK σ hσ Fr hFr ε ⟨_, huR⟩ (ψ l) = ψ (a l) := fun l => by
    rw [← hconj l]
    obtain ⟨c, hc⟩ := ε.surjective (ψ l)
    rw [← hc, MulAut.conj_apply, ← map_mul, ← map_inv, ← map_mul]
    refine rgrpRecipeAut_apply_eq hn hK σ hσ Fr hFr ε _ ?_
    rw [hmul, hmul, hinv]
  have haA₀ : a ∈ A₀ := (hA₀ a).2 ⟨ha, _,
    (mem_range_rgrpRecipeAut hn hK σ hσ Fr hFr ε hε _).1 ⟨_, rfl⟩, hφu⟩
  exact (mem_rgrpModel hn hK σ hσ Fr hFr ε).2 ⟨huR, TypeA.mem_inducedSub.2 ⟨a, haA₀, hφu⟩⟩

theorem not_e6AdToral_rgrpModel_field
    {d n : ℕ} (hd : 1 ≤ d) (hnd : n = 3 * d) (h3 : 3 ∣ 2 ^ d + 1) (hn : 1 ≤ n)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ 2 ^ n) {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ n)
    (ε : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) ≃* TwE6Delta.RecipeR K n)
    (hε : ∀ x : MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
      MulAut.congr ε x ∈ TwE6Delta.RecipeI K n ↔ x ∈ (RecipeExcLang.twConj K σ).range)
    {κ : K ≃+* K} (hκ : orderOf κ = 3) {L' : Type} [Group L']
    {ψ : L' →* TwE6Delta.RecipeR K n} (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A A₀ : Subgroup (MulAut L')} (hA : IsElemAbelian 3 A)
    (hA₀ : ∀ a, a ∈ A₀ ↔ a ∈ A ∧ ∃ φ ∈ TwE6Delta.RecipeI K n, ∀ l, φ (ψ l) = ψ (a l))
    (hcard : Nat.card A₀ = 3 ^ 4) {b : MulAut L'} (hbA : b ∈ A)
    (hb : ∀ l, MulAut.congr ε (fieldActor σ κ) (ψ l) = ψ (b l))
    (hAb : ∀ a ∈ A, ∃ a₀ ∈ A₀, ∃ j : ℕ, a = a₀ * b ^ j) (hSC : GGTorusSelfCent 3 A) :
    ¬ E6AdToral (rgrpModel hn hK σ hσ Fr hFr ε (TypeA.inducedSub ψ A₀)) := by
  intro htor
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := n * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, pow_mul])
  have : CharP Ω 2 := charP_of_injective_algebraMap (algebraMap K Ω).injective 2
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have hA₀A : ∀ a ∈ A₀, a ∈ A := fun a ha => ((hA₀ a).1 ha).1
  have hAI₀ : ∀ a ∈ A₀, ∃ φ ∈ TwE6Delta.RecipeI K n, ∀ l, φ (ψ l) = ψ (a l) :=
    fun a ha => ((hA₀ a).1 ha).2
  have h3n : 3 ∣ 2 ^ n + 1 := by
    refine h3.trans ?_
    have h := Odd.nat_add_dvd_pow_add_pow (2 ^ d) 1 (by decide : Odd 3)
    rwa [one_pow, ← pow_mul, mul_comm, ← hnd] at h
  have hq3 : 3 ≤ 2 ^ n :=
    le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) (show 2 ≤ n by omega))
  have hK6 : Nat.card K = 2 ^ (6 * d) := by
    rw [hK, hnd, ← pow_mul]
    ring_nf
  obtain ⟨κ₁, hκ₁⟩ : ∃ κ₁ : K ≃+* K, ∀ c, κ₁ c = c ^ 2 ^ (2 * d) :=
    ⟨iterateFrobeniusEquiv K 2 (2 * d), fun c => by
      rw [iterateFrobeniusEquiv_apply, iterateFrobenius_def]⟩
  have hκ₁3 : κ₁ ^ 3 = 1 := by
    have h : ∀ (m : ℕ) (c : K), (κ₁ ^ m) c = c ^ (2 ^ (2 * d)) ^ m := by
      intro m
      induction m with
      | zero => intro c; simp
      | succ m ih =>
        intro c
        rw [pow_succ, RingAut.mul_apply, ih, hκ₁, ← pow_mul, pow_succ']
    refine RingEquiv.ext fun c => ?_
    rw [h, ← pow_mul, show 2 * d * 3 = 6 * d by ring, ← hK6, Nat.card_eq_fintype_card,
      FiniteField.pow_card]
    rfl
  have hκ₁ne : κ₁ ≠ 1 := by
    intro h
    obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := Kˣ)
    have hγo : orderOf γ = 2 ^ (6 * d) - 1 := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hγ, Nat.card_units, hK6]
    have h1 : γ ^ 2 ^ (2 * d) = γ := Units.ext (by
      rw [Units.val_pow_eq_pow_val]
      exact (hκ₁ γ).symm.trans (RingEquiv.ext_iff.mp h γ))
    have h2 : γ ^ (2 ^ (2 * d) - 1) = 1 := by
      refine mul_right_cancel (b := γ) ?_
      rw [← pow_succ, Nat.sub_add_cancel Nat.one_le_two_pow, one_mul, h1]
    have h3 : orderOf γ ∣ 2 ^ (2 * d) - 1 := orderOf_dvd_of_pow_eq_one h2
    rw [hγo] at h3
    have h5 : 2 ^ (2 * d) < 2 ^ (6 * d) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    have h6 : 1 < 2 ^ (2 * d) := Nat.one_lt_two_pow (by omega)
    have h4 := Nat.le_of_dvd (by omega) h3
    generalize 2 ^ (2 * d) = x at h4 h5 h6
    generalize 2 ^ (6 * d) = y at h4 h5
    omega
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hκ₁o : orderOf κ₁ = 3 := orderOf_eq_prime hκ₁3 hκ₁ne
  have : IsCyclic (K ≃+* K) := CFSG.LocalAnalysis.GLTheoremA.FP.isCyclic_ringEquiv K
  have : Finite (K ≃+* K) :=
    Finite.of_injective (fun g : K ≃+* K => (g : K → K)) DFunLike.coe_injective
  have hzp : Subgroup.zpowers κ = Subgroup.zpowers κ₁ := by
    rw [IsCyclic.subgroup_eq_iff_card_eq, Nat.card_zpowers, Nat.card_zpowers, hκ, hκ₁o]
  obtain ⟨Fr₀, hFr₀⟩ : ∃ Fr₀ : Ω →+* Ω, ∀ c, Fr₀ c = c ^ 2 ^ d :=
    ⟨iterateFrobenius Ω 2 d, fun c => iterateFrobenius_def 2 d c⟩
  have hFr3 : Fr₀.comp (Fr₀.comp Fr₀) = Fr := RingHom.ext fun c => by
    rw [RingHom.comp_apply, RingHom.comp_apply, hFr₀, hFr₀, hFr₀, hFr, ← pow_mul, ← pow_mul,
      ← pow_add, ← pow_add, hnd]
    ring_nf
  have hκΩ : (Fr₀.comp Fr₀).comp (algebraMap K Ω) = (algebraMap K Ω).comp κ₁.toRingHom :=
    RingHom.ext fun c => by
      rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply, hFr₀, hFr₀,
        RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, hκ₁, map_pow, ← pow_mul, ← pow_add,
        two_mul]
  have hentry : ∀ g : ModGL TwistTag.E6.tag K,
      baseChangeGL (algebraMap K Ω) (Units.map (entrywiseHom κ₁.toRingHom) g) =
        Units.map (entrywiseHom (Fr₀.comp Fr₀)) (baseChangeGL (algebraMap K Ω) g) := fun g => by
    rw [units_map_entrywiseHom_eq_baseChangeGL, units_map_entrywiseHom_eq_baseChangeGL,
      baseChangeGL_baseChangeGL, baseChangeGL_baseChangeGL, hκΩ]
  have hle : ∀ y ∈ TwistedDiag.Rgrp Ω Fr₀, y ∈ TwistedDiag.Rgrp Ω Fr := by
    intro y hy
    obtain ⟨hyG, hyF⟩ := (TwistedDiag.mem_Rgrp Fr₀).1 hy
    refine (TwistedDiag.mem_Rgrp Fr).2 ⟨hyG, ?_⟩
    rw [← twistE6_units_map_entrywiseHom hFr3, ← twistE6_twistE6, hyF, hyF, hyF]
  have hmem0 : ∀ y ∈ TwistedDiag.Rgrp Ω Fr, Units.map (entrywiseHom (Fr₀.comp Fr₀)) y = y →
      y ∈ TwistedDiag.Rgrp Ω Fr₀ := by
    intro y hy hy2
    obtain ⟨hyG, hyF⟩ := (TwistedDiag.mem_Rgrp Fr).1 hy
    refine (TwistedDiag.mem_Rgrp Fr₀).2 ⟨hyG, ?_⟩
    calc twistE6 Ω Fr₀ y = twistE6 Ω Fr₀ (Units.map (entrywiseHom (Fr₀.comp Fr₀)) y) := by
          rw [hy2]
      _ = y := by rw [twistE6_units_map_entrywiseHom hFr3, hyF]
  have hfix0 : ∀ y ∈ TwistedDiag.Rgrp Ω Fr₀, Units.map (entrywiseHom (Fr₀.comp Fr₀)) y = y := by
    intro y hy
    obtain ⟨-, hyF⟩ := (TwistedDiag.mem_Rgrp Fr₀).1 hy
    rw [← twistE6_twistE6, hyF, hyF]
  have hβfix : ∀ c : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
      baseChangeGL (τ := Tag.E6) (algebraMap K Ω) c.1 ∈ TwistedDiag.Rgrp Ω Fr₀ →
        MulAut.congr ε (fieldActor σ κ) (ε c) = ε c := by
    intro c hc
    have h1 : fieldActorHom σ κ₁ ∈ MulAction.stabilizer
        (MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) c := by
      refine MulAction.mem_stabilizer_iff.2 (Subtype.ext
        (baseChangeGL_injective (algebraMap K Ω) ?_))
      change baseChangeGL (algebraMap K Ω) (fieldActor σ κ₁ c : ModGL TwistTag.E6.tag K) = _
      rw [coe_fieldActor, hentry]
      exact hfix0 _ hc
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 (hzp ▸ Subgroup.mem_zpowers κ)
    have h2 : fieldActor σ κ c = c := by
      rw [← hi, ← fieldActorHom_apply, map_zpow]
      exact MulAction.mem_stabilizer_iff.1 (Subgroup.zpow_mem _ h1 i)
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply, h2]
  have hcardH : Nat.card (rgrpModel hn hK σ hσ Fr hFr ε (TypeA.inducedSub ψ A₀)) = 3 ^ 4 := by
    rw [card_rgrpModel hn hK σ hσ Fr hFr ε hε (inducedSub_subset hψ hAI₀),
      TypeA.card_inducedSub hψ hker hperf fun a ha => (hAI₀ a ha).imp fun _ hφ => hφ.2, hcard]
  have : Finite (rgrpModel hn hK σ hσ Fr hFr ε (TypeA.inducedSub ψ A₀)) :=
    Nat.finite_of_card_ne_zero (by rw [hcardH]; norm_num)
  have hX3 : ∀ x ∈ rgrpModel hn hK σ hσ Fr hFr ε (TypeA.inducedSub ψ A₀), x ^ 3 = 1 := by
    intro x hx
    obtain ⟨hxR, hxA⟩ := (mem_rgrpModel hn hK σ hσ Fr hFr ε).1 hx
    obtain ⟨a, ha, hφ⟩ := TypeA.mem_inducedSub.1 hxA
    have h1 : (⟨x, hxR⟩ : ↥(TwistedDiag.Rgrp Ω Fr)) ^ 3 = 1 :=
      rgrpRecipeAut_injective hn hK σ hσ Fr hFr ε (by
        rw [map_pow, map_one]
        refine TypeA.induced_unique ψ hψ (TypeA.induced_pow ψ hφ 3) fun l => ?_
        rw [hA.2 a (hA₀A a ha)]
        rfl)
    have h := congrArg Subtype.val h1
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at h
  have hXR0 : rgrpModel hn hK σ hσ Fr hFr ε (TypeA.inducedSub ψ A₀) ≤
      TwistedDiag.Rgrp Ω Fr₀ := by
    intro x hx
    obtain ⟨hxR, hxA⟩ := (mem_rgrpModel hn hK σ hσ Fr hFr ε).1 hx
    obtain ⟨a, ha, hφ⟩ := TypeA.mem_inducedSub.1 hxA
    have hab : a * b = b * a := CFSG.Open.IsElemAbelian.comm hA (hA₀A a ha) hbA
    have hcomm : rgrpRecipeAut hn hK σ hσ Fr hFr ε ⟨x, hxR⟩ * MulAut.congr ε (fieldActor σ κ) =
        MulAut.congr ε (fieldActor σ κ) * rgrpRecipeAut hn hK σ hσ Fr hFr ε ⟨x, hxR⟩ := by
      refine TypeA.induced_unique ψ hψ (a := a * b) (fun l => ?_) (fun l => ?_)
      · rw [MulAut.mul_apply, MulAut.mul_apply, hb, hφ]
      · rw [hab, MulAut.mul_apply, MulAut.mul_apply, hφ, hb]
    obtain ⟨w, hw⟩ := (twInndiagEquivRgrp hn hK σ hσ Fr hFr).surjective ⟨x, hxR⟩
    have hc : RecipeExcLang.twConj K σ w * fieldActor σ κ =
        fieldActor σ κ * RecipeExcLang.twConj K σ w := by
      rw [← rgrpConjAut_apply_baseChange hn hK σ hσ Fr hFr w, hw]
      apply (MulAut.congr ε).injective
      rw [map_mul, map_mul]
      exact hcomm
    have hc₁ : RecipeExcLang.twConj K σ w * fieldActor σ κ₁ =
        fieldActor σ κ₁ * RecipeExcLang.twConj K σ w := by
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (hzp.symm ▸ Subgroup.mem_zpowers κ₁)
      rw [← hj, ← fieldActorHom_apply, map_zpow]
      exact (Commute.zpow_right hc j).eq
    have hwκ := CFSG.LocalAnalysis.GLTheoremA.T156.twE6_entrywise_eq_of_commute hn hK hσ hq3 κ₁
      w hc₁
    have hxw : baseChangeGL (algebraMap K Ω) (w : ModGL TwistTag.E6.tag K) = x :=
      (twInndiagEquivRgrp_apply hn hK σ hσ Fr hFr w).symm.trans (congrArg Subtype.val hw)
    have h := hentry w
    rw [hwκ, hxw] at h
    exact hmem0 x hxR h.symm
  obtain ⟨g1, hg1, hgn, hX⟩ := exists_typeW0_of_e6AdLangToral hd Fr₀ hFr₀ h3 hX3
    (by rw [hcardH]; norm_num) (e6AdLangToral_of_toral hd Fr₀ hFr₀ hXR0 htor)
  have h30 : (3 : Ω) ≠ 0 := by
    have h2 : (2 : Ω) = 0 := CharP.cast_eq_zero Ω 2
    rw [show (3 : Ω) = 1 by linear_combination h2]
    exact one_ne_zero
  obtain ⟨ζ, -, hζ⟩ := TwistedDiag.exists_cube_root (Ω := Ω) h30
  have hζ3 : ζ ^ 3 = 1 := hζ ▸ pow_orderOf_eq_one ζ
  have hmem : ∀ i, g1 * torusElt Tag.E6 Ω i ζ * g1⁻¹ ∈
      rgrpModel hn hK σ hσ Fr hFr ε (TypeA.inducedSub ψ A₀) := by
    intro i
    have hu0 := conj_torusElt_mem_Rgrp Fr₀ hFr₀ h3 hg1 hgn hζ3 i
    have ht0 := conj_weylElt_mem_Rgrp Fr₀ hg1 hgn i
    obtain ⟨hu3, ht2, htu⟩ := inverts_conj_torusElt (CharP.cast_eq_zero Ω 2) g1 hζ3 i
    refine mem_rgrpModel_of_inverts hn hK σ hσ Fr hFr ε hε h3n hψ hker hA₀ hb hAb hSC
      (hle _ hu0) (hle _ ht0) hu3 ht2 htu (fun c hc => hβfix c (by rw [hc]; exact hu0))
      (fun c hc => hβfix c (by rw [hc]; exact ht0)) fun x hx => ?_
    obtain ⟨b', hb', rfl, -⟩ :=
      exists_rootDiagUnit_of_mem_langTorus (v := twE6W0) (hX x hx) (hX3 x hx)
    exact conj_rootDiagUnit_conj_weylElt g1 hb' hζ i
  have h5 := three_pow_five_le_card_of_conj_torusElt_mem hζ hmem
  rw [hcardH] at h5
  norm_num at h5

end CFSG.StandardType.KG87B

end
