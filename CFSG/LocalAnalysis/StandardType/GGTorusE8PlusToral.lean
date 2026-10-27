module

public import CFSG.LocalAnalysis.StandardType.GGTorusE8Scalar
public import CFSG.LocalAnalysis.StandardType.GGExcElemToralLangStep
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwE8Model

public noncomputable section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.RankThree.PartOne.KE CFSG.RankThree.E6
  CFSG.LieType.SeitzGeneration CFSG.HardMathSupport.Timmesfeld.CrossChar


theorem exists_langTorus_E8_plus_of_family {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K + 1)
    (E : Subgroup (adjointGroup .E8 K)) (hE : IsElemAbelian p E)
    {g : ModGL .E8 (AlgebraicClosure K)} (hg : g ∈ adjointGroup .E8 (AlgebraicClosure K))
    (a : E → Fin Tag.E8.rank → (AlgebraicClosure K)ˣ)
    (ha : ∀ x : E, rootDiagUnit .E8 (a x) =
      g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((x : adjointGroup .E8 K) : ModGL .E8 K) * g)
    (hcent : familyCentralizer .E8 (AlgebraicClosure K) a =
      familyGroup (K := AlgebraicClosure K) a) :
    ∃ Fr : AlgebraicClosure K →+* AlgebraicClosure K, (∀ c, Fr c = c ^ Nat.card K) ∧
      ∃ g0 ∈ adjointGroup .E8 (AlgebraicClosure K),
        Units.map (entrywiseHom Fr) g0 =
          g0 * canonicalRep (coxeterSystem .E8) (AlgebraicClosure K) e8Neg ∧
        ∀ x ∈ E, baseChangeGL (algebraMap K (AlgebraicClosure K))
            ((x : adjointGroup .E8 K) : ModGL .E8 K) ∈
          (twistedTorusOf (canonicalRep (coxeterSystem .E8) (AlgebraicClosure K) e8Neg)
            (Units.map (entrywiseHom Fr))).map (MulAut.conj g0).toMonoidHom := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fact p.Prime := ⟨hp⟩
  let L := AlgebraicClosure K
  let : Fintype K := Fintype.ofFinite K
  let : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective _
  let ι : K →+* L := algebraMap K L
  let φ : adjointGroup .E8 K →* ModGL .E8 L :=
    (baseChangeGL ι).comp (adjointGroup .E8 K).subtype
  have hexp : ∀ (x : E) j, a x j ^ p = 1 := by
    intro x
    have hpow : rootDiagUnit .E8 (a x ^ p) = rootDiagUnit .E8 1 := by
      rw [show rootDiagUnit .E8 (a x ^ p) = rootDiagUnit .E8 (a x) ^ p from
        (rootDiagUnitHom .E8 L).map_pow (a x) p, ha x, rootDiagUnit_one]
      change (g⁻¹ * φ (x : adjointGroup .E8 K) * g) ^ p = 1
      rw [show g⁻¹ * φ (x : adjointGroup .E8 K) * g =
        (MulAut.conj g⁻¹) (φ (x : adjointGroup .E8 K)) by simp only [MulAut.conj_apply, inv_inv],
        ← map_pow, ← map_pow, hE.2 x x.2, map_one, map_one]
    exact fun j => congrFun (CFSG.LieType.Chevalley.rootDiagUnit_injective hpow) j
  obtain ⟨f, _, hKf⟩ := FiniteField.card K 2
  have hf : 1 ≤ (f : ℕ) := f.pos
  have hK : Nat.card K = 2 ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hKf]
  have hw : ∀ (x : E) v, rootChar (a x) (e8Neg • v) = rootChar (a x) v ^ 2 ^ (f : ℕ) := by
    intro x v
    rw [e8Neg_smul]
    have hneg : rootChar (a x) (-v) = (rootChar (a x) v)⁻¹ := by
      simp only [rootChar, Pi.neg_apply, zpow_neg, Finset.prod_inv_distrib]
    rw [hneg, ← hK]
    refine (eq_inv_of_mul_eq_one_left ?_).symm
    obtain ⟨k, hk⟩ := hpq
    rw [← pow_succ, hk, pow_mul, rootChar_pow_eq_one (a x) (hexp x) v, one_pow]
  have hcop : Nat.Coprime p (2 ^ (f : ℕ)) :=
    Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  have hFix : ∀ y : ModGL .E8 K, entrywiseFrobGL .E8 L 2 f (baseChangeGL ι y) =
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
  have hgx : ∀ x : E, g * rootDiagUnit .E8 (a x) * g⁻¹ = φ (x : adjointGroup .E8 K) := by
    intro x
    rw [ha x]
    group
    rfl
  obtain ⟨g₁, hg₁, hFg₁, hg₁x⟩ := ExcElemToral.exists_lang_conj_of_family_twisted 2 hf a hcop
    hexp hw hcent hg (fun x => by rw [hgx]; exact hFix (x : ModGL .E8 K))
  let Fr : L →+* L := iterateFrobenius L 2 f
  have hFr : ∀ t, Fr t = t ^ Nat.card K := fun t => by
    rw [show Fr t = t ^ 2 ^ (f : ℕ) from rfl, ← hK]
  refine ⟨Fr, hFr, g₁, hg₁, hFg₁, fun x hx => ?_⟩
  let xE : E := ⟨x, hx⟩
  refine ⟨rootDiagUnit .E8 (a xE), ⟨rootDiagUnit_mem_torusGroup _, ?_⟩, ?_⟩
  · have h := rootDiagUnit_eq_conj_frob 2 (hw xE)
    exact h.symm
  · change g₁ * rootDiagUnit .E8 (a xE) * g₁⁻¹ = φ x
    rw [hg₁x xE, hgx xE]

theorem langFrameData_E8_plus_of_family {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K + 1)
    (E : Subgroup (adjointGroup .E8 K)) (hE : IsElemAbelian p E)
    (hSC : ∀ x ∈ Subgroup.centralizer (E : Set (adjointGroup .E8 K)), x ^ p = 1 → x ∈ E)
    {g : ModGL .E8 (AlgebraicClosure K)} (hg : g ∈ adjointGroup .E8 (AlgebraicClosure K))
    (a : E → Fin Tag.E8.rank → (AlgebraicClosure K)ˣ)
    (ha : ∀ x : E, rootDiagUnit .E8 (a x) =
      g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((x : adjointGroup .E8 K) : ModGL .E8 K) * g)
    (hcent : familyCentralizer .E8 (AlgebraicClosure K) a =
      familyGroup (K := AlgebraicClosure K) a) :
    Irred937.LangFrameData .E8 p K E := by
  obtain ⟨Fr, hFr, g0, hg0C, hg0, hEin⟩ :=
    exists_langTorus_E8_plus_of_family Fact.out hp2 hpq E hE hg a ha hcent
  refine Irred937.langFrameData_of_langTorus (Or.inr rfl) hp2 K hpq E hE hSC e8Neg Fr hFr
    g0 hg0C hg0 hEin ?_
  have hM : weylMatrix e8Neg = -1 := by
    ext i j
    rw [weylMatrix_apply, e8Neg_smul, Pi.neg_apply, Matrix.neg_apply, Matrix.one_apply,
      Pi.single_apply]
  rw [hM]
  ext i j
  simp [modMat, Matrix.one_apply]

theorem exists_e8_scalar_frame_of_family {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (hq : p ∣ Nat.card K + 1) (E : Subgroup (adjointGroup .E8 K))
    (hE : CFSG.Assembly.IsElemAbelian p E)
    (hSC : ∀ g : adjointGroup .E8 K, (∀ x ∈ E, g * x = x * g) → g ^ p = 1 → g ∈ E)
    {g : ModGL .E8 (AlgebraicClosure K)} (hg : g ∈ adjointGroup .E8 (AlgebraicClosure K))
    (a : E → Fin Tag.E8.rank → (AlgebraicClosure K)ˣ)
    (ha : ∀ x : E, rootDiagUnit .E8 (a x) =
      g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((x : adjointGroup .E8 K) : ModGL .E8 K) * g)
    (hcent : familyCentralizer .E8 (AlgebraicClosure K) a =
      familyGroup (K := AlgebraicClosure K) a) :
    ∃ (F : ExcFrame .E8 K p E) (Fr : AlgebraicClosure K →+* AlgebraicClosure K)
      (ζ : (AlgebraicClosure K)ˣ) (hζ : ζ ^ p = 1)
      (ι : Multiplicative (Fin Tag.E8.rank → ZMod p) →* adjointGroup .E8 K)
      (n : Fin Tag.E8.rank → adjointGroup .E8 K),
      (∀ c, Fr c = c ^ Nat.card K) ∧
      (∀ x, F.D.Φ x = Units.map (entrywiseHom Fr) x) ∧
      (∀ u : Fin Tag.E8.rank → ℤ, F.w • u = -u) ∧
      orderOf ζ = p ∧ Function.Injective ι ∧ ι.range = E ∧
      (∀ s : Fin Tag.E8.rank → ZMod p,
        baseChangeGL (algebraMap K (AlgebraicClosure K))
            (ι (Multiplicative.ofAdd s) : ModGL .E8 K) =
          F.D.g0 * ExcFrames.frameDiag ζ hζ s * F.D.g0⁻¹) ∧
      (∀ k, baseChangeGL (algebraMap K (AlgebraicClosure K)) (n k : ModGL .E8 K) =
        F.D.g0 * canonicalRep (coxeterSystem .E8) (AlgebraicClosure K) (simple .E8 k) * F.D.g0⁻¹) ∧
      (∀ k s, n k * ι (Multiplicative.ofAdd s) * (n k)⁻¹ =
        ι (Multiplicative.ofAdd (TableBExc.torusAct .E8 p (simple .E8 k) s))) ∧
      (∀ g ∈ Subgroup.normalizer (E : Set (adjointGroup .E8 K)),
        ∃ v : WeylGroup .E8, ∀ s,
          g * ι (Multiplicative.ofAdd s) * g⁻¹ =
            ι (Multiplicative.ofAdd (TableBExc.torusAct .E8 p v s))) := by
  have : Fact (Nat.Prime p) := ⟨hp⟩
  exact E8ScalarTorus.exists_frame_of_langFrameData hp hp2 hq E hE hSC
    (langFrameData_E8_plus_of_family hp2 hq E hE
      (fun x hx hxp => hSC x (fun y hy => (Subgroup.mem_centralizer_iff.mp hx y hy).symm) hxp)
      hg a ha hcent)

end CFSG.StandardType

end
