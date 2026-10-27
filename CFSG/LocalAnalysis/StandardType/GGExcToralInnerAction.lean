module

public import CFSG.LocalAnalysis.StandardType.GGExcElemToralLangStep
public import CFSG.LocalAnalysis.StandardType.GGTBWNormFrame
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfMaxToral
public import CFSG.LocalAnalysis.StandardType.GGTableBExcRank
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitExcPlusE7
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneHeightRigidityAut
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwE7Model
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwE8Model
public import CFSG.RankThree.PartOne.Q1327T.Item7D4W
public import CFSG.RankThree.PartOne.KE.CTLang
public import CFSG.RankThree.Chevalley.SteinbergCAF4SplitPrimeTorus
public import CFSG.LieType.AlgebraicGroups.ToralTwistPinning
public import CFSG.LieType.AlgebraicGroups.ToralTwistSemilinearDatum
public import CFSG.LieType.Chevalley.OddDiagramFrobeniusFixedDerived
public import CFSG.LieType.Chevalley.CLSOddE7RationalDerivedIndex
public import CFSG.LieType.Chevalley.OddF4CosetDescent
public import CFSG.LieType.SeitzGeneration.ExcHighThree.Killed

public noncomputable section

namespace CFSG.StandardType.ExcToralInner

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.StandardType.TableBExc

theorem exists_orderOf_eq_three (K : Type) [Field K] [CharP K 2] :
    ∃ ζ : (AlgebraicClosure K)ˣ, orderOf ζ = 3 := by
  have h3 : ((3 : ℕ) : K) ≠ 0 := by
    have h2 : ((2 : ℕ) : K) = 0 := CharP.cast_eq_zero K 2
    have h32 : ((3 : ℕ) : K) = ((2 : ℕ) : K) + 1 := by push_cast; ring
    rw [h32, h2, zero_add]
    exact one_ne_zero
  haveI : NeZero ((3 : ℕ) : K) := ⟨h3⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.prim (M := AlgebraicClosure K) (n := 3)
  refine ⟨(hz.isUnit (by norm_num)).unit, ?_⟩
  rw [← orderOf_units, IsUnit.unit_spec, ← hz.eq_orderOf]

theorem exists_units_map_eq_pow_three {L : Type} [Field L] {ζ : Lˣ} (hζo : orderOf ζ = 3)
    (σ : L →+* L) :
    ∃ m : ℕ, (m = 1 ∨ m = 2) ∧ ∀ c : Lˣ, c ^ 3 = 1 → Units.map σ.toMonoidHom c = c ^ m := by
  have hζ : ζ ^ 3 = 1 := hζo ▸ pow_orderOf_eq_one ζ
  have h1 : (Units.map σ.toMonoidHom ζ) ^ 3 = 1 := by rw [← map_pow, hζ, map_one]
  obtain ⟨m₀, hm₀⟩ := CFSG.RankThree.Chevalley.exists_pow_val_eq_of_pow_eq_one hζo h1
  have hlt : m₀.val < 3 := ZMod.val_lt m₀
  have hne : m₀.val ≠ 0 := by
    intro h0
    have hσ : Units.map σ.toMonoidHom ζ = 1 := by rw [← hm₀, h0, pow_zero]
    have hζ1 : ζ = 1 := by
      apply Units.ext
      have h : σ (ζ : L) = σ 1 := by
        have h' := congrArg Units.val hσ
        rw [Units.val_one] at h'
        rw [map_one]
        exact h'
      exact σ.injective h
    rw [hζ1, orderOf_one] at hζo
    exact absurd hζo (by norm_num)
  refine ⟨m₀.val, by omega, fun c hc => ?_⟩
  obtain ⟨j, rfl⟩ := CFSG.RankThree.Chevalley.exists_pow_val_eq_of_pow_eq_one hζo hc
  rw [map_pow, ← hm₀, ← pow_mul, ← pow_mul, mul_comm]


theorem exists_smul_eq_neg_E7_E8 {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) :
    ∃ w₀ : WeylGroup τ, ∀ v : Fin τ.rank → ℤ, w₀ • v = -v := by
  rcases hτ with rfl | rfl
  · exact ⟨e7Neg, e7Neg_smul⟩
  · exact ⟨e8Neg, e8Neg_smul⟩

theorem mul_comm_of_smul_eq_neg {τ : Tag} {w₀ : WeylGroup τ}
    (hw₀ : ∀ v : Fin τ.rank → ℤ, w₀ • v = -v) (u : WeylGroup τ) : u * w₀ = w₀ * u := by
  apply eq_of_smul_eq_smul (α := Fin τ.rank → ℤ)
  intro v
  rw [mul_smul, mul_smul, hw₀, hw₀, smul_neg]

theorem canonicalRep_conj_rootDiagUnit_of_smul_eq_neg {τ : Tag} {L : Type} [Field L]
    {w₀ : WeylGroup τ} (hw₀ : ∀ v : Fin τ.rank → ℤ, w₀ • v = -v) (b : Fin τ.rank → Lˣ) :
    canonicalRep (coxeterSystem τ) L w₀ * rootDiagUnit τ b *
      (canonicalRep (coxeterSystem τ) L w₀)⁻¹ = (rootDiagUnit τ b)⁻¹ := by
  have h := (rootDiagUnit_eq_conj_canonicalRep_iff b⁻¹ b w₀).2 fun v => by
    rw [hw₀]
    simp only [rootChar, Pi.inv_apply, Pi.neg_apply, inv_zpow', neg_neg]
  rw [← h]
  exact (rootDiagUnitHom τ L).map_inv b

theorem canonicalRep_mul_comm_of_smul_eq_neg {τ : Tag} {R : Type} [CommRing R] [CharP R 2]
    {w₀ : WeylGroup τ} (hw₀ : ∀ v : Fin τ.rank → ℤ, w₀ • v = -v) (v w : WeylGroup τ) :
    canonicalRep (coxeterSystem τ) R v * canonicalRep (coxeterSystem τ) R w *
        canonicalRep (coxeterSystem τ) R w₀ =
      canonicalRep (coxeterSystem τ) R w₀ *
        (canonicalRep (coxeterSystem τ) R v * canonicalRep (coxeterSystem τ) R w) := by
  rw [← CFSG.RankThree.PartOne.Q1327T.canonicalRep_mul_charTwo v w,
    ← CFSG.RankThree.PartOne.Q1327T.canonicalRep_mul_charTwo,
    ← CFSG.RankThree.PartOne.Q1327T.canonicalRep_mul_charTwo, mul_comm_of_smul_eq_neg hw₀]

theorem finite_fixed_le_map_adjointGroup_E7_E8 {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) {K : Type}
    [Field K] [Finite K] [CharP K 2] (Fr : AlgebraicClosure K →+* AlgebraicClosure K)
    (hFr : ∀ c, Fr c = c ^ Nat.card K) (X : Subgroup (ModGL τ (AlgebraicClosure K))) [Finite X]
    (hXC : X ≤ adjointGroup τ (AlgebraicClosure K))
    (hXF : ∀ x ∈ X, Units.map (entrywiseHom Fr) x = x) :
    X ≤ (adjointGroup τ K).map (baseChangeGL (algebraMap K (AlgebraicClosure K))) := by
  rcases hτ with rfl | rfl
  · exact finite_fixed_le_map_adjointGroup_E7 Fr hFr X hXC hXF
  · exact Subgroup.relIndex_eq_one.1 (Nat.dvd_one.1
      (CFSG.RankThree.PartOne.KE.finite_fixed_subgroup_rational_perfect (τ := .E8) (K := K)
        (L := AlgebraicClosure K) 1 (Or.inr (Or.inr ⟨rfl, rfl⟩)) Fr hFr X hXC hXF).1)

theorem exists_rational_of_frob_fixed {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) {K : Type} [Field K]
    [Finite K] [CharP K 2] [Fact (Nat.Prime 2)] [CharP (AlgebraicClosure K) 2] {f : ℕ}
    (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) {y : ModGL τ (AlgebraicClosure K)}
    (hy : y ∈ adjointGroup τ (AlgebraicClosure K))
    (hF : entrywiseFrobGL τ (AlgebraicClosure K) 2 f y = y) :
    ∃ r ∈ adjointGroup τ K, baseChangeGL (algebraMap K (AlgebraicClosure K)) r = y := by
  let X : Subgroup (ModGL τ (AlgebraicClosure K)) :=
    adjointGroup τ (AlgebraicClosure K) ⊓
      (entrywiseFrobGL τ (AlgebraicClosure K) 2 f).eqLocus (MonoidHom.id _)
  haveI : Finite X := Set.Finite.to_subtype
    ((finite_setOf_entrywiseFrobGL_eq (τ := τ) (k := AlgebraicClosure K) 2 hf).subset
      fun g hg => (Subgroup.mem_inf.1 hg).2)
  have hFr : ∀ c : AlgebraicClosure K,
      iterateFrobenius (AlgebraicClosure K) 2 f c = c ^ Nat.card K := fun c => by
    rw [iterateFrobenius_def, hK]
  obtain ⟨r, hr, hry⟩ := finite_fixed_le_map_adjointGroup_E7_E8 hτ
    (iterateFrobenius (AlgebraicClosure K) 2 f) hFr X inf_le_left
    (fun x hx => (Subgroup.mem_inf.1 hx).2) (Subgroup.mem_inf.2 ⟨hy, hF⟩)
  exact ⟨r, hr, hry⟩

theorem exists_conj_eq_of_toral {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) {K : Type} [Field K]
    [Finite K] [CharP K 2] (E : Subgroup (adjointGroup τ K)) (hE : IsElemAbelian 3 E)
    (hT : ExcFramesHalf.IsToralSubgroup τ (AlgebraicClosure K)
      (E.map ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp
        (adjointGroup τ K).subtype)))
    (β : MulAut (adjointGroup τ K)) :
    ∃ r : adjointGroup τ K, ∀ x ∈ E, β x = r * x * r⁻¹ := by
  classical
  obtain ⟨w₀, hw₀⟩ := exists_smul_eq_neg_E7_E8 hτ
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  let : Fintype K := Fintype.ofFinite K
  obtain ⟨f, _, hKf⟩ := FiniteField.card K 2
  have hf : 1 ≤ (f : ℕ) := f.pos
  have hK : Nat.card K = 2 ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hKf]
  have hFbc : ∀ y : ModGL τ (AlgebraicClosure K),
      entrywiseFrobGL τ (AlgebraicClosure K) 2 f y =
        baseChangeGL (iterateFrobenius (AlgebraicClosure K) 2 f) y := fun y =>
    units_map_entrywiseHom_eq_baseChangeGL _ y
  have hbcinj : Function.Injective
      (baseChangeGL (τ := τ) (algebraMap K (AlgebraicClosure K))) :=
    baseChangeGL_injective (algebraMap K (AlgebraicClosure K))
  obtain ⟨g, hg, hgT⟩ := hT
  have hmemT : ∀ x : E, g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      ((x : adjointGroup τ K) : ModGL τ K) * g ∈ torusGroup τ (AlgebraicClosure K) :=
    fun x => hgT _ (Subgroup.mem_map_of_mem _ x.2)
  choose a ha using fun x : E =>
    CFSG.LieType.SeitzGeneration.ExcHighThree.exists_rootDiagUnit_of_mem_torusGroup (hmemT x)
  have hgx : ∀ x : E, g * rootDiagUnit τ (a x) * g⁻¹ =
      baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((x : adjointGroup τ K) : ModGL τ K) := by
    intro x
    rw [ha x]
    group
  have hexp : ∀ (x : E) j, a x j ^ 3 = 1 := by
    intro x
    have hpow : rootDiagUnit τ (a x ^ 3) = rootDiagUnit τ 1 := by
      rw [show rootDiagUnit τ (a x ^ 3) = rootDiagUnit τ (a x) ^ 3 from
        (rootDiagUnitHom τ (AlgebraicClosure K)).map_pow (a x) 3, ha x, rootDiagUnit_one,
        show g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
            ((x : adjointGroup τ K) : ModGL τ K) * g =
          (MulAut.conj g⁻¹) (baseChangeGL (algebraMap K (AlgebraicClosure K))
            ((x : adjointGroup τ K) : ModGL τ K)) by
          simp only [MulAut.conj_apply, inv_inv],
        ← map_pow, ← map_pow, ← Subgroup.coe_pow, hE.2 x x.2, OneMemClass.coe_one, map_one, map_one]
    exact fun j => congrFun (CFSG.LieType.Chevalley.rootDiagUnit_injective hpow) j
  obtain ⟨w, hw⟩ : ∃ w : WeylGroup τ, ∀ (x : E) v,
      rootChar (a x) (w • v) = rootChar (a x) v ^ 2 ^ (f : ℕ) := by
    rcases Nat.even_or_odd (f : ℕ) with ⟨k, hk⟩ | ⟨k, hk⟩
    · have hmod : 2 ^ (f : ℕ) % 3 = 1 := by
        rw [hk, ← two_mul, pow_mul, Nat.pow_mod]
        norm_num
      obtain ⟨m, hm⟩ : ∃ m, 2 ^ (f : ℕ) = 3 * m + 1 :=
        ⟨2 ^ (f : ℕ) / 3, by have := Nat.div_add_mod (2 ^ (f : ℕ)) 3; omega⟩
      refine ⟨1, fun x v => ?_⟩
      rw [one_smul, hm, pow_succ, pow_mul, rootChar_pow_eq_one (a x) (hexp x) v, one_pow,
        one_mul]
    · have hmod : 2 ^ (f : ℕ) % 3 = 2 := by
        rw [hk, pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
        norm_num
      obtain ⟨m, hm⟩ : ∃ m, 2 ^ (f : ℕ) + 1 = 3 * m :=
        ⟨2 ^ (f : ℕ) / 3 + 1, by have := Nat.div_add_mod (2 ^ (f : ℕ)) 3; omega⟩
      refine ⟨w₀, fun x v => ?_⟩
      have hneg : rootChar (a x) (-v) = (rootChar (a x) v)⁻¹ := by
        simp only [rootChar, Pi.neg_apply, zpow_neg, Finset.prod_inv_distrib]
      rw [hw₀, hneg]
      refine (eq_inv_of_mul_eq_one_left ?_).symm
      rw [← pow_succ, hm, pow_mul, rootChar_pow_eq_one (a x) (hexp x) v, one_pow]
  have hcop : Nat.Coprime 3 (2 ^ (f : ℕ)) := Nat.Coprime.pow_right _ (by norm_num)
  have hFix : ∀ y : ModGL τ K, entrywiseFrobGL τ (AlgebraicClosure K) 2 f
      (baseChangeGL (algebraMap K (AlgebraicClosure K)) y) =
        baseChangeGL (algebraMap K (AlgebraicClosure K)) y := by
    intro y
    have hcomp : (iterateFrobenius (AlgebraicClosure K) 2 (f : ℕ)).comp
        (algebraMap K (AlgebraicClosure K)) = algebraMap K (AlgebraicClosure K) := by
      apply RingHom.ext
      intro t
      change iterateFrobenius (AlgebraicClosure K) 2 f (algebraMap K (AlgebraicClosure K) t) =
        algebraMap K (AlgebraicClosure K) t
      rw [iterateFrobenius_def, ← map_pow, ← hKf]
      exact congrArg (algebraMap K (AlgebraicClosure K)) (FiniteField.pow_card t)
    rw [hFbc, baseChangeGL_baseChangeGL, hcomp]
  obtain ⟨v, -, g₁, hg₁, hFg₁, hg₁x⟩ := ExcElemToral.exists_lang_conj_of_family_twisted_stab 2 hf
    a hcop hexp hw hg fun x => by rw [hgx]; exact hFix _
  obtain ⟨n, hn⟩ : ∃ n : ModGL τ (AlgebraicClosure K),
      n = canonicalRep (coxeterSystem τ) (AlgebraicClosure K) v *
        canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w := ⟨_, rfl⟩
  rw [← hn] at hFg₁
  have hg₁φ : ∀ x : E, g₁ * rootDiagUnit τ (a x) * g₁⁻¹ =
      baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((x : adjointGroup τ K) : ModGL τ K) :=
    fun x => (hg₁x x).trans (hgx x)
  obtain ⟨n₀, hn₀⟩ : ∃ n₀ : ModGL τ (AlgebraicClosure K),
      n₀ = canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w₀ := ⟨_, rfl⟩
  have hn₀G : n₀ ∈ adjointGroup τ (AlgebraicClosure K) := by
    rw [hn₀]
    exact canonicalRep_mem_adjointGroup _ (AlgebraicClosure K) _
  have hFn₀ : entrywiseFrobGL τ (AlgebraicClosure K) 2 f n₀ = n₀ := by
    rw [hFbc, hn₀]
    exact baseChangeGL_canonicalRep _ w₀
  have hcomm : n * n₀ = n₀ * n := by
    rw [hn, hn₀]
    exact canonicalRep_mul_comm_of_smul_eq_neg hw₀ v w
  have hy₁ : g₁ * n₀ * g₁⁻¹ ∈ adjointGroup τ (AlgebraicClosure K) :=
    mul_mem (mul_mem hg₁ hn₀G) (inv_mem hg₁)
  have hFy₁ : entrywiseFrobGL τ (AlgebraicClosure K) 2 f (g₁ * n₀ * g₁⁻¹) =
      g₁ * n₀ * g₁⁻¹ := by
    rw [map_mul, map_mul, map_inv, hFg₁, hFn₀]
    calc g₁ * n * n₀ * (g₁ * n)⁻¹ = g₁ * (n * n₀) * n⁻¹ * g₁⁻¹ := by group
      _ = g₁ * n₀ * g₁⁻¹ := by rw [hcomm]; group
  obtain ⟨r₁, hr₁, hr₁y⟩ := exists_rational_of_frob_fixed hτ hf hK hy₁ hFy₁
  have hinv : ∀ x : E, r₁ * ((x : adjointGroup τ K) : ModGL τ K) * r₁⁻¹ =
      ((x : adjointGroup τ K) : ModGL τ K)⁻¹ := by
    intro x
    apply hbcinj
    rw [map_mul, map_mul, map_inv, map_inv, hr₁y, ← hg₁φ x]
    calc g₁ * n₀ * g₁⁻¹ * (g₁ * rootDiagUnit τ (a x) * g₁⁻¹) * (g₁ * n₀ * g₁⁻¹)⁻¹ =
        g₁ * (n₀ * rootDiagUnit τ (a x) * n₀⁻¹) * g₁⁻¹ := by group
      _ = (g₁ * rootDiagUnit τ (a x) * g₁⁻¹)⁻¹ := by
        rw [hn₀, canonicalRep_conj_rootDiagUnit_of_smul_eq_neg hw₀]
        group
  have hfield : ∀ δ : K ≃+* K, ∃ r ∈ adjointGroup τ K, ∀ x : E,
      Units.map (entrywiseHom δ.toRingHom) ((x : adjointGroup τ K) : ModGL τ K) =
        r * ((x : adjointGroup τ K) : ModGL τ K) * r⁻¹ := by
    intro δ
    obtain ⟨δ', hδι⟩ : ∃ δ' : AlgebraicClosure K ≃+* AlgebraicClosure K, ∀ c : K,
        δ' (algebraMap K (AlgebraicClosure K) c) = algebraMap K (AlgebraicClosure K) (δ c) :=
      ⟨IsAlgClosure.equivOfEquiv (AlgebraicClosure K) (AlgebraicClosure K) δ,
        IsAlgClosure.equivOfEquiv_algebraMap (AlgebraicClosure K) (AlgebraicClosure K) δ⟩
    have hDφ : ∀ y : ModGL τ K,
        baseChangeGL δ'.toRingHom (baseChangeGL (algebraMap K (AlgebraicClosure K)) y) =
          baseChangeGL (algebraMap K (AlgebraicClosure K)) (baseChangeGL δ.toRingHom y) := by
      intro y
      have hc : δ'.toRingHom.comp (algebraMap K (AlgebraicClosure K)) =
          (algebraMap K (AlgebraicClosure K)).comp δ.toRingHom := RingHom.ext fun c => hδι c
      rw [baseChangeGL_baseChangeGL, baseChangeGL_baseChangeGL, hc]
    have hDF : ∀ y : ModGL τ (AlgebraicClosure K),
        baseChangeGL δ'.toRingHom (entrywiseFrobGL τ (AlgebraicClosure K) 2 f y) =
          entrywiseFrobGL τ (AlgebraicClosure K) 2 f (baseChangeGL δ'.toRingHom y) := by
      intro y
      have hc : δ'.toRingHom.comp (iterateFrobenius (AlgebraicClosure K) 2 f) =
          (iterateFrobenius (AlgebraicClosure K) 2 f).comp δ'.toRingHom :=
        RingHom.ext fun c => by simp only [RingHom.comp_apply, iterateFrobenius_def, map_pow]
      rw [hFbc, hFbc, baseChangeGL_baseChangeGL, baseChangeGL_baseChangeGL, hc]
    have hDn : baseChangeGL δ'.toRingHom n = n := by
      rw [hn, map_mul, baseChangeGL_canonicalRep, baseChangeGL_canonicalRep]
    obtain ⟨ζ, hζ⟩ := exists_orderOf_eq_three K
    obtain ⟨m, hm12, hm⟩ := exists_units_map_eq_pow_three hζ δ'.toRingHom
    have hDd : ∀ x : E, baseChangeGL δ'.toRingHom (rootDiagUnit τ (a x)) =
        rootDiagUnit τ (a x) ^ m := by
      intro x
      rw [baseChangeGL_rootDiagUnit, show rootDiagUnit τ (a x) ^ m =
        rootDiagUnit τ (a x ^ m) from
          ((rootDiagUnitHom τ (AlgebraicClosure K)).map_pow (a x) m).symm]
      congr 1
      funext j
      exact hm (a x j) (hexp x j)
    have hy₂ : baseChangeGL δ'.toRingHom g₁ * g₁⁻¹ ∈ adjointGroup τ (AlgebraicClosure K) :=
      mul_mem (baseChangeGL_mem_adjointGroup _ hg₁) (inv_mem hg₁)
    have hFy₂ : entrywiseFrobGL τ (AlgebraicClosure K) 2 f
        (baseChangeGL δ'.toRingHom g₁ * g₁⁻¹) = baseChangeGL δ'.toRingHom g₁ * g₁⁻¹ := by
      rw [map_mul, map_inv, ← hDF, hFg₁, map_mul, hDn]
      group
    obtain ⟨r₂, hr₂, hr₂y⟩ := exists_rational_of_frob_fixed hτ hf hK hy₂ hFy₂
    have hδx : ∀ x : E, Units.map (entrywiseHom δ.toRingHom)
        ((x : adjointGroup τ K) : ModGL τ K) =
          r₂ * ((x : adjointGroup τ K) : ModGL τ K) ^ m * r₂⁻¹ := by
      intro x
      rw [units_map_entrywiseHom_eq_baseChangeGL]
      apply hbcinj
      rw [← hDφ, map_mul, map_mul, map_inv, map_pow, hr₂y, ← hg₁φ x, map_mul, map_mul, map_inv,
        hDd x, conj_pow]
      group
    rcases hm12 with rfl | rfl
    · exact ⟨r₂, hr₂, fun x => by rw [hδx x, pow_one]⟩
    · refine ⟨r₂ * r₁, mul_mem hr₂ hr₁, fun x => ?_⟩
      have hx3 : ((x : adjointGroup τ K) : ModGL τ K) ^ 3 = 1 := by
        rw [← Subgroup.coe_pow, hE.2 x x.2, OneMemClass.coe_one]
      have hx2 : ((x : adjointGroup τ K) : ModGL τ K) ^ 2 =
          ((x : adjointGroup τ K) : ModGL τ K)⁻¹ :=
        eq_inv_of_mul_eq_one_left (by rw [← pow_succ, hx3])
      rw [hδx x, hx2, ← hinv x]
      group
  obtain ⟨g', hg', a', -, δ, -, hβx⟩ := CFSG.SeitzReduction.mem_diagonalFieldActors_E7_E8 hτ β
  obtain ⟨r₀, hr₀, hr₀x⟩ := hfield δ
  have hda : rootDiagUnit τ a' ∈ adjointGroup τ K :=
    torusGroup_le_adjointGroup (full_of_E7_E8 hτ a')
  refine ⟨⟨g' * rootDiagUnit τ a' * r₀, mul_mem (mul_mem hg' hda) hr₀⟩, fun x hx => ?_⟩
  apply Subtype.ext
  rw [hβx x, show Units.map (entrywiseHom δ.toRingHom)
      ((x : adjointGroup τ K) : ModGL τ K) =
    r₀ * ((x : adjointGroup τ K) : ModGL τ K) * r₀⁻¹ from hr₀x ⟨x, hx⟩]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  group

theorem ggWNormConcl_of_toral {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) {K : Type} [Field K] [Finite K]
    [CharP K 2] [Fact (Nat.Prime 3)] {L : Type} [Group L] [Finite L] (A : Subgroup (MulAut L))
    (e : L ≃* adjointGroup τ K) (E : Subgroup (adjointGroup τ K))
    (hE : IsElemAbelian 3 E) (hAE : A.map (MulAut.congr e).toMonoidHom = E.map MulAut.conj)
    (hT : ExcFramesHalf.IsToralSubgroup τ (AlgebraicClosure K)
      (E.map ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp
        (adjointGroup τ K).subtype)))
    {Λ' V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥A ≃+ V) (φ : Λ' → MulAut ↥A) (h : Λ' → V) (α : Λ' → Module.Dual (ZMod 3) V)
    (hgen : ggAutomizer (MulAut.conj : L →* MulAut L).range A = Subgroup.closure (Set.range φ))
    {s : MulAut ↥A} (hs : s ∈ ggInduced (⊤ : Subgroup (MulAut L)) A) :
    GGWNormConcl ι φ h α s := by
  let Λ0 : adjointGroup τ K →* MulAut L :=
    (MulAut.congr e.symm).toMonoidHom.comp MulAut.conj
  have hΛψ : ∀ l, Λ0 (e l) = MulAut.conj l := by
    intro l
    ext x
    simp [Λ0, MulAut.congr_apply, MulAut.conj_apply]
  have hEA : E.map Λ0 = A := by
    have hcomp : (MulAut.congr e.symm).toMonoidHom.comp (MulAut.congr e).toMonoidHom =
        MonoidHom.id (MulAut L) := by
      ext a x
      simp [MulAut.congr_apply, MulEquiv.trans_apply]
    change E.map ((MulAut.congr e.symm).toMonoidHom.comp MulAut.conj) = A
    rw [← Subgroup.map_map, ← hAE, Subgroup.map_map, hcomp, Subgroup.map_id]
  have hker : e.toMonoidHom.ker ≤ Subgroup.center L := by
    intro l hl
    rw [MonoidHom.mem_ker] at hl
    rw [show l = 1 from e.injective (hl.trans (map_one e).symm)]
    exact one_mem _
  exact ggWNormConcl_of_centralCover_innerAction e.toMonoidHom e.surjective hker
    center_adjointGroup_eq_bot Λ0 hΛψ E A hEA (fun β => exists_conj_eq_of_toral hτ E hE hT β)
    ι φ h α hgen hs

end CFSG.StandardType.ExcToralInner
