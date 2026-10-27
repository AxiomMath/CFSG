module

public import CFSG.LocalAnalysis.StandardType.GGTorusE7Lang
public import CFSG.LocalAnalysis.StandardType.GGLieCoreToralInd
public import CFSG.LocalAnalysis.StandardType.GGExcElemToralLangStep
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwE7Model

public noncomputable section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.C14Lattice
  CFSG.RankThree.PartOne.KE CFSG.RankThree.E6 CFSG.LieType.SeitzGeneration
  CFSG.HardMathSupport.Timmesfeld.CrossChar


theorem exists_langTorus_E7_plus {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ Nat.card K + 1)
    (E : Subgroup (adjointGroup .E7 K)) (hE : IsElemAbelian p E) :
    ∃ Fr : AlgebraicClosure K →+* AlgebraicClosure K, (∀ c, Fr c = c ^ Nat.card K) ∧
      ∃ g0 ∈ adjointGroup .E7 (AlgebraicClosure K),
        Units.map (entrywiseHom Fr) g0 =
          g0 * canonicalRep (coxeterSystem .E7) (AlgebraicClosure K) e7Neg ∧
        ∀ x ∈ E, baseChangeGL (algebraMap K (AlgebraicClosure K))
            ((x : adjointGroup .E7 K) : ModGL .E7 K) ∈
          (twistedTorusOf (canonicalRep (coxeterSystem .E7) (AlgebraicClosure K) e7Neg)
            (Units.map (entrywiseHom Fr))).map (MulAut.conj g0).toMonoidHom := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  let L := AlgebraicClosure K
  let : Fintype K := Fintype.ofFinite K
  let : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective _
  let ι : K →+* L := algebraMap K L
  let φ : adjointGroup .E7 K →* ModGL .E7 L :=
    (baseChangeGL ι).comp (adjointGroup .E7 K).subtype
  let A := E.map φ
  have hA : A ≤ adjointGroup .E7 L := by
    rintro _ ⟨x, hx, rfl⟩
    exact CFSG.LieType.Chevalley.baseChangeGL_mem_adjointGroup (f := ι) x.2
  have hAe : CFSG.Open.IsElemAbelian p A := TableB.isElemAbelian_map hE φ
  have hsur : Function.Surjective (fun x : E =>
      (⟨φ (x : adjointGroup .E7 K), Subgroup.mem_map_of_mem φ x.2⟩ : A)) := by
    rintro ⟨y, ⟨x, hx, rfl⟩⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  let : Finite A := Finite.of_surjective _ hsur
  have halg := isAlgebraic_zmod_algebraicClosure_of_finite K 2
  obtain ⟨g, hg, hgt⟩ := LieCore.isToralSubgroup_of_nonTorsion hp hp2 (fun _ => hp3)
    (by intro h; cases h) (Ne.symm hp2) halg hA (inferInstance : Finite A) hAe
  have htor : ∀ x : E, g⁻¹ * φ (x : adjointGroup .E7 K) * g ∈ torusGroup .E7 L :=
    fun x => hgt _ (Subgroup.mem_map_of_mem φ x.2)
  choose a ha using fun x : E => exists_rootDiagUnit_eq_of_mem_torusGroup (htor x)
  have hexp : ∀ (x : E) j, a x j ^ p = 1 := by
    intro x
    have hpow : rootDiagUnit .E7 (a x ^ p) = rootDiagUnit .E7 1 := by
      rw [show rootDiagUnit .E7 (a x ^ p) = rootDiagUnit .E7 (a x) ^ p from
        (rootDiagUnitHom .E7 L).map_pow (a x) p, ← ha x, rootDiagUnit_one]
      change (g⁻¹ * φ (x : adjointGroup .E7 K) * g) ^ p = 1
      rw [show g⁻¹ * φ (x : adjointGroup .E7 K) * g =
        (MulAut.conj g⁻¹) (φ (x : adjointGroup .E7 K)) by simp only [MulAut.conj_apply, inv_inv],
        ← map_pow, ← map_pow, hE.2 x x.2, map_one, map_one]
    exact fun j => congrFun (CFSG.LieType.Chevalley.rootDiagUnit_injective hpow) j
  obtain ⟨f, _, hKf⟩ := FiniteField.card K 2
  have hf : 1 ≤ (f : ℕ) := f.pos
  have hK : Nat.card K = 2 ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hKf]
  have hw : ∀ (x : E) v, rootChar (a x) (e7Neg • v) = rootChar (a x) v ^ 2 ^ (f : ℕ) := by
    intro x v
    rw [e7Neg_smul]
    have hneg : rootChar (a x) (-v) = (rootChar (a x) v)⁻¹ := by
      simp only [rootChar, Pi.neg_apply, zpow_neg, Finset.prod_inv_distrib]
    rw [hneg, ← hK]
    refine (eq_inv_of_mul_eq_one_left ?_).symm
    obtain ⟨k, hk⟩ := hpq
    rw [← pow_succ, hk, pow_mul, rootChar_pow_eq_one (a x) (hexp x) v, one_pow]
  have hcop : Nat.Coprime p (2 ^ (f : ℕ)) :=
    Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  have hcent : familyCentralizer .E7 L a = familyGroup (K := L) a :=
    familyCentralizer_eq_familyGroup_of_nonTorsion hp hp2 (fun _ => hp3)
      (by intro h; cases h) a hexp
  have hFix : ∀ y : ModGL .E7 K, entrywiseFrobGL .E7 L 2 f (baseChangeGL ι y) =
      baseChangeGL ι y := by
    intro y
    have hcomp : (iterateFrobenius L 2 (f : ℕ)).comp ι = ι := by
      apply RingHom.ext
      intro t
      change iterateFrobenius L 2 f (ι t) = ι t
      rw [iterateFrobenius_def, ← map_pow, ← hKf]
      exact congrArg ι (FiniteField.pow_card t)
    rw [entrywiseFrobGL, CFSG.LieType.Chevalley.units_map_entrywiseHom_eq_baseChangeGL,
      CFSG.LieType.Chevalley.baseChangeGL_baseChangeGL, hcomp]
  have hgx : ∀ x : E, g * rootDiagUnit .E7 (a x) * g⁻¹ = φ (x : adjointGroup .E7 K) := by
    intro x
    rw [← ha x]
    group
  obtain ⟨g₁, hg₁, hFg₁, hg₁x⟩ := ExcElemToral.exists_lang_conj_of_family_twisted 2 hf a hcop
    hexp hw hcent hg (fun x => by rw [hgx]; exact hFix (x : ModGL .E7 K))
  let Fr : L →+* L := iterateFrobenius L 2 f
  have hFr : ∀ t, Fr t = t ^ Nat.card K := fun t => by
    rw [show Fr t = t ^ 2 ^ (f : ℕ) from rfl, ← hK]
  refine ⟨Fr, hFr, g₁, hg₁, hFg₁, fun x hx => ?_⟩
  let xE : E := ⟨x, hx⟩
  refine ⟨rootDiagUnit .E7 (a xE), ⟨rootDiagUnit_mem_torusGroup _, ?_⟩, ?_⟩
  · have h := rootDiagUnit_eq_conj_frob 2 (hw xE)
    exact h.symm
  · change g₁ * rootDiagUnit .E7 (a xE) * g₁⁻¹ = φ x
    rw [hg₁x xE, hgx xE]

theorem langFrameData_E7_plus {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    [Fact p.Prime] (hp5 : 5 ≤ p) (hpq : p ∣ Nat.card K + 1)
    (E : Subgroup (adjointGroup .E7 K)) (hE : IsElemAbelian p E)
    (hSC : ∀ x ∈ Subgroup.centralizer (E : Set (adjointGroup .E7 K)), x ^ p = 1 → x ∈ E) :
    Irred937.LangFrameData .E7 p K E := by
  obtain ⟨Fr, hFr, g0, hg0C, hg0, hEin⟩ := exists_langTorus_E7_plus Fact.out hp5 hpq E hE
  refine Irred937.langFrameData_of_langTorus (Or.inl rfl) (by omega) K hpq E hE hSC e7Neg Fr hFr
    g0 hg0C hg0 hEin ?_
  have hM : weylMatrix e7Neg = -1 := by
    ext i j
    rw [weylMatrix_apply, e7Neg_smul, Pi.neg_apply, Matrix.neg_apply, Matrix.one_apply,
      Pi.single_apply]
  rw [hM]
  ext i j
  simp [modMat, Matrix.one_apply]

theorem exists_e7_scalar_frame_of_sc {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp5 : 5 ≤ p)
    (hq : p ∣ Nat.card K + 1) (E : Subgroup (adjointGroup .E7 K))
    (hE : CFSG.Assembly.IsElemAbelian p E)
    (hSC : ∀ g : adjointGroup .E7 K, (∀ x ∈ E, g * x = x * g) → g ^ p = 1 → g ∈ E) :
    ∃ (F : ExcFrame .E7 K p E) (Fr : AlgebraicClosure K →+* AlgebraicClosure K)
      (ζ : (AlgebraicClosure K)ˣ) (hζ : ζ ^ p = 1)
      (ι : Multiplicative (Fin Tag.E7.rank → ZMod p) →* adjointGroup .E7 K)
      (n : Fin Tag.E7.rank → adjointGroup .E7 K),
      (∀ c, Fr c = c ^ Nat.card K) ∧
      (∀ x, F.D.Φ x = Units.map (entrywiseHom Fr) x) ∧
      (∀ u : Fin Tag.E7.rank → ℤ, F.w • u = -u) ∧
      orderOf ζ = p ∧ Function.Injective ι ∧ ι.range = E ∧
      (∀ s : Fin Tag.E7.rank → ZMod p,
        baseChangeGL (algebraMap K (AlgebraicClosure K))
            (ι (Multiplicative.ofAdd s) : ModGL .E7 K) =
          F.D.g0 * ExcFrames.frameDiag ζ hζ s * F.D.g0⁻¹) ∧
      (∀ k, baseChangeGL (algebraMap K (AlgebraicClosure K)) (n k : ModGL .E7 K) =
        F.D.g0 * canonicalRep (coxeterSystem .E7) (AlgebraicClosure K) (simple .E7 k) * F.D.g0⁻¹) ∧
      (∀ k s, n k * ι (Multiplicative.ofAdd s) * (n k)⁻¹ =
        ι (Multiplicative.ofAdd (TableBExc.torusAct .E7 p (simple .E7 k) s))) ∧
      (∀ g ∈ Subgroup.normalizer (E : Set (adjointGroup .E7 K)),
        ∃ v : WeylGroup .E7, ∀ s,
          g * ι (Multiplicative.ofAdd s) * g⁻¹ =
            ι (Multiplicative.ofAdd (TableBExc.torusAct .E7 p v s))) := by
  have : Fact (Nat.Prime p) := ⟨hp⟩
  exact exists_e7_scalar_frame_of_langFrame hp (by omega) hq E hE hSC
    (langFrameData_E7_plus hp5 hq E hE
      (fun g hg hgp => hSC g (fun x hx => (Subgroup.mem_centralizer_iff.mp hg x hx).symm) hgp))

end CFSG.StandardType
