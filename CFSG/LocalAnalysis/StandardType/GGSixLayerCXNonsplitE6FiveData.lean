module

public import CFSG.RankThree.PartOne.KE.A1E6Five
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitE6FiveEmbed
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitComponentEmbed
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGeneralLinearSmall
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LieType.Ree.LargeReeSylowOpposition
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.Chevalley.SteinbergBNNoninnerComponentNodes
public import CFSG.RankThree.Chevalley.SteinbergCFOddE7E8NoninnerComponent
public import CFSG.RankThree.Lattice.SteinbergBIOrbitQuotFull
public import CFSG.RankThree.PartOne.KE.Basic
public import CFSG.RankThree.PartOne.KE.NativeCyclicMain
public import CFSG.RankThree.PartOne.S8.Statements
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7

public noncomputable section

namespace CFSG.StandardType.E6Nonsplit

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
open CFSG.RankThree.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Lattice
open CFSG.RankThree.Chevalley (exhaustionPhi)
open CFSG.RankThree.PartOne.KE
open CFSG.Assembly (IsComponentOf)
open Matrix CFSG.RankThree.QuadraticSL2 CFSG.RankThree.Classical
open scoped Matrix Polynomial MatrixGroups

section SL2

variable {K L : Type} [Field K] [Field L] [Algebra K L]

theorem nonempty_mulEquiv_sl2_conj_range (P : GL (Fin 2) L) :
    Nonempty (SL(2, K) ≃* ↥((SpecialLinearGroup.map (algebraMap K L)).range.map (conjSL P))) := by
  have hSLinj : Function.Injective (SpecialLinearGroup.map (n := Fin 2) (algebraMap K L)) := by
    intro A B h
    ext i j
    have h1 := congrArg (fun X : SL(2, L) => (X : Matrix (Fin 2) (Fin 2) L) i j) h
    simp only [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply] at h1
    exact (algebraMap K L).injective h1
  have hPinj : Function.Injective (conjSL P) := fun A B h => by
    have h1 := congrArg (conjSL P⁻¹) h
    rwa [← conjSL_mul, ← conjSL_mul, inv_mul_cancel, conjSL_one, conjSL_one] at h1
  exact ⟨(MonoidHom.ofInjective hSLinj).trans (Subgroup.equivMapOfInjective _ _ hPinj)⟩

end SL2

theorem isSolvable_SL_two_of_card_lt_four {E : Type} [Field E] [Finite E]
    (h : Nat.card E < 4) : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) E) := by
  have hcard : Nat.card E = 2 ∨ Nat.card E = 3 := by
    have h2 : 1 < Nat.card E := Finite.one_lt_card
    omega
  have : Group.IsSolvable (Matrix.GeneralLinearGroup (Fin 2) E) :=
    CFSG.ComponentClassification.CatalogueBGeneralLinear.generalLinear_two_small_solvable E hcard
  exact Group.isSolvable_of_isSolvable_injective
    (f := (Matrix.SpecialLinearGroup.toGL : Matrix.SpecialLinearGroup (Fin 2) E →* _))
    Matrix.SpecialLinearGroup.toGL_injective

theorem a1_untwisted_structure
    (τ : Tag) (d : ℕ)
    (hτ : (τ = .E6 ∧ d = 3) ∨ (τ = .E7 ∧ d = 2) ∨ (τ = .E8 ∧ d = 1))
    (K : Type) [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ] (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L]
    [CharP L ℓ] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hordW : ¬ p ∣ Nat.card (WeylGroup τ))
    (n : ModGL τ L) (hnC : n ∈ adjointGroup τ L) {θ : Fin τ.rank → ℤ} (hθ : IsRoot τ θ)
    (hZcyc : IsCyclic (subtorusA1 n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) θ))
    {N : ℕ} (hN : N ≠ 0)
    (hZcard : Nat.card (subtorusA1 n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) θ) = N)
    (hord : p ^ (Nat.card (adjointGroup τ K)).factorization p = p ^ N.factorization p)
    (hkerZ : ∀ a : Fin τ.rank → Lˣ,
      rootDiagUnit τ a ∈ subtorusA1 n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) θ →
      orderOf (rootDiagUnit τ a) = p → rootCharKernel a ⊆ {θ, -θ}) :
    ∀ (S : Subgroup (SL2 L)) [Finite S],
      (∀ B : SL2 L, n * Units.map (entrywiseHom (iterateFrobenius L ℓ f))
          (rootSL2 τ L θ B) * n⁻¹ = rootSL2 τ L θ B ↔ B ∈ S) →
      Subgroup.centralizer ((S.map Matrix.SpecialLinearGroup.toGL :
        Subgroup (GL (Fin 2) L)) : Set (GL (Fin 2) L)) =
          (Matrix.GeneralLinearGroup.scalar (Fin 2)).range →
      ∀ x : adjointGroup τ K, orderOf x = p →
        (CFSG.IsQuasisimple S →
          ∃ (ψ : ↥(Subgroup.centralizer ({x} : Set (adjointGroup τ K))) →* ModGL τ L)
            (P Z : Subgroup (ModGL τ L)),
            Function.Injective ψ ∧ Nonempty (↥S ≃* ↥P) ∧ P ≤ ψ.range ∧
            (∀ d : ↥(Subgroup.centralizer ({x} : Set (adjointGroup τ K))), ∀ u ∈ P,
              ψ d * u * (ψ d)⁻¹ ∈ P) ∧
            (∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a) ∧
            (∀ d : ↥(Subgroup.centralizer ({x} : Set (adjointGroup τ K))),
              (∀ u ∈ P, ψ d * u = u * ψ d) → ψ d ∈ Z)) ∧
        (Group.IsSolvable S →
          Group.IsSolvable ↥(Subgroup.centralizer ({x} : Set (adjointGroup τ K)))) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype K := Fintype.ofFinite K
  have : Finite (ModGL τ K) := finite_modGL
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact iterateFrobenius_def ℓ f c
  obtain ⟨g0, hg0C, hg0⟩ := lang_conjugator_gen τ K hf L n hnC
  let ι : adjointGroup τ K →* ModGL τ L :=
    (baseChangeGL (algebraMap K L)).comp (adjointGroup τ K).subtype
  have hrange : ι.range = (adjointGroup τ K).map (baseChangeGL (algebraMap K L)) := by
    change ((baseChangeGL (algebraMap K L)).comp (adjointGroup τ K).subtype).range = _
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hι : Function.Injective ι :=
    (baseChangeGL_injective _).comp (Subgroup.subtype_injective _)
  have hιC : ∀ y, ι y ∈ adjointGroup τ L := fun y => baseChangeGL_mem_adjointGroup _ y.2
  have hcomp : Fr.comp (algebraMap K L) = algebraMap K L := RingHom.ext fun c => by
    change Fr (algebraMap K L c) = algebraMap K L c
    rw [hFr, ← map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hιΦ : ∀ y, Units.map (entrywiseHom Fr) (ι y) = ι y := fun y => by
    have e : Units.map (entrywiseHom Fr) (ι y) = baseChangeGL Fr (ι y) := Units.ext rfl
    rw [e]
    change baseChangeGL Fr (baseChangeGL (algebraMap K L) (y : ModGL τ K)) =
      baseChangeGL (algebraMap K L) (y : ModGL τ K)
    rw [baseChangeGL_baseChangeGL, hcomp]
  have hrat3 : ∀ (X : Subgroup (ModGL τ L)) [Finite X], X ≤ adjointGroup τ L →
      (∀ x ∈ X, Units.map (entrywiseHom Fr) x = x) → ι.range.relIndex X ∣ d ∧
        (∀ p : ℕ, p.Prime → 3 < p → ∀ P : Subgroup (ModGL τ L), P ≤ X → IsPGroup p P →
          P ≤ ι.range) ∧
        ∀ P : Subgroup (ModGL τ L), P ≤ X → ⁅P, P⁆ = P → P ≤ ι.range := by
    intro X _ hXC hXF
    rw [hrange]
    have : Algebra.IsAlgebraic K L := inferInstance
    exact finite_fixed_subgroup_rational_perfect d hτ Fr hFr X hXC hXF
  have hrat2 : ∀ (X : Subgroup (ModGL τ L)) [Finite X], X ≤ adjointGroup τ L →
      (∀ x ∈ X, Units.map (entrywiseHom Fr) x = x) → ι.range.relIndex X ∣ d ∧
        ∀ p : ℕ, p.Prime → 3 < p → ∀ P : Subgroup (ModGL τ L), P ≤ X → IsPGroup p P →
          P ≤ ι.range := fun X _ hXC hXF => by
    have h := hrat3 X hXC hXF
    exact ⟨h.1, h.2.1⟩
  have hZle : subtorusA1 n (Units.map (entrywiseHom Fr)) θ ≤
      twistedTorusOf n (Units.map (entrywiseHom Fr)) := subtorusA1_le_twistedTorusOf _ _ _
  obtain ⟨-, -, -, -, hpcyc, hconj⟩ := sylow_conjugacy_of_subtorus d ι hι
    (Units.map (entrywiseHom Fr)) n g0 hg0C hg0 hp hp3 hN hrat2 _ hZle hZcyc hZcard hord
  intro S _ hS1 hS3
  exact a1_centralizer_structure ι hι hιC (Units.map (entrywiseHom Fr)) hιΦ n g0 hg0C hg0
    (fun P hP hPC hPF hPp => (hrat3 P hPC hPF).2.2 P le_rfl hPp) hp hordW hθ (hZ := hZcyc) hconj
    hkerZ S hS1 hS3

theorem E6_five_structure
    (K : Type) [Field K] [Finite K] {ℓ f :
    ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime) (hp5 : 5 < p)
    (hpf : (p : ℤ) ∣ (exhaustionPhi 5).eval (Nat.card K : ℤ)) :
    ∀ x : adjointGroup .E6 K, orderOf x = p → ∀ X : Subgroup (adjointGroup .E6 K),
      IsComponentOf X (Subgroup.centralizer ({x} : Set (adjointGroup .E6 K))) →
        4 ≤ Nat.card K ∧ Nonempty (SL(2, K) ≃* ↥X) := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have : Fintype K := Fintype.ofFinite K
  have : CharP K ℓ := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    hℓ hf hK
  let L := AlgebraicClosure K
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hpf' : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 4 + (Nat.card K : ℤ) ^ 3 + (Nat.card K : ℤ) ^ 2 +
      (Nat.card K : ℤ) + 1 := by simpa [exhaustionPhi] using hpf
  obtain ⟨hp7, hpq, hord5⟩ := CTE6.e6Five_data hp hp5 hpf'
  have hordW : ¬ p ∣ Nat.card (WeylGroup .E6) := not_dvd_card_weylGroup_E hp hp7 (Or.inl rfl)
  have hΦ5 : ((Nat.card K : ℕ) : ZMod p) ^ 4 + ((Nat.card K : ℕ) : ZMod p) ^ 3 +
      ((Nat.card K : ℕ) : ZMod p) ^ 2 + ((Nat.card K : ℕ) : ZMod p) + 1 = 0 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd ((Nat.card K : ℤ) ^ 4 + (Nat.card K : ℤ) ^ 3 +
      (Nat.card K : ℤ) ^ 2 + (Nat.card K : ℤ) + 1) p).2 hpf'
    simpa using this
  set w : WeylGroup .E6 := (coxeterSystem .E6).wordProd [0, 2, 3, 4] with hwdef
  have hw : ∀ u, w • u = e6O5W *ᵥ u := wordProd_smul_eq_wordMat_mulVec .E6 [0, 2, 3, 4]
  set n : ModGL .E6 L := canonicalRep (coxeterSystem .E6) L w with hndef
  have hnC : n ∈ adjointGroup .E6 L := canonicalRep_mem_adjointGroup (coxeterSystem .E6) L w
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact iterateFrobenius_def ℓ f c
  have hℓq : ℓ ∣ Nat.card K := by
    rw [hK]
    exact dvd_pow_self _ (by omega)
  have hθroot : IsRoot .E6 e6O5Theta := E6_order_five_lattice_and_exact_A1_prime_root_kernel.1
  set J : Set (Fin Tag.E6.rank) := {i | i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4} with hJ
  have hJorth : ∀ i ∈ J, CFSG.LieType.Steinberg.Adjoint.iform
      (Pi.single i 1 : Fin Tag.E6.rank → ℤ) e6O5Theta = 0 := by
    intro i hi
    rcases hi with rfl | rfl | rfl | rfl <;> decide +kernel
  have hwJ : w ∈ parabolicWeylGroup .E6 J := by
    refine wordProd_mem_parabolicWeylGroup (fun i hi => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    exact hi
  have hsl : ∀ j : Fin Tag.E6.rank, Tag.E6.symmetrizer j j = 1 := by decide
  have hn : n ∈ Subgroup.centralizer (rootRankOneGroup .E6 L e6O5Theta : Set (ModGL .E6 L)) :=
    canonicalRep_mem_centralizer_rootRankOneGroup hsl hθroot hJorth hwJ
  have hT : twistedTorusOf n (Units.map (entrywiseHom Fr)) =
      (fixedCharTuples e6O5W Fr).map (rootDiagUnitHom .E6 L) := by
    rw [← twistedFixedTuples_eq_fixedCharTuples hw Fr]
    exact twistedTorus_eq_map_twistedFixedTuples w Fr
  have hZeq := subtorusA1_eq_map_fixedBlockTuples hT hθroot
  have hinj0 : Function.Injective (rootDiagUnitHom .E6 L) := rootDiagUnit_injective
  have hne : e6FiveBlock.P.eval (Nat.card K : ℤ) ≠ 0 := by
    have h1 : (1 : ℤ) < (Nat.card K : ℤ) ^ 5 := by
      have : (2 : ℤ) ≤ Nat.card K := by exact_mod_cast hq2
      calc (1 : ℤ) < 2 := by norm_num
        _ ≤ 2 ^ 5 := by norm_num
        _ ≤ (Nat.card K : ℤ) ^ 5 := pow_le_pow_left₀ (by norm_num) this 5
    show (Polynomial.X ^ 5 - Polynomial.C 1 : ℤ[X]).eval (Nat.card K : ℤ) ≠ 0
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
    omega
  obtain ⟨hcycB, hcardB⟩ := e6FiveBlock.isCyclic_and_card Fr hFr hℓ hℓq hne
  have hZcyc : IsCyclic (subtorusA1 n (Units.map (entrywiseHom Fr)) e6O5Theta) := by
    rw [hZeq]
    exact (Subgroup.equivMapOfInjective _ (rootDiagUnitHom .E6 L) hinj0).isCyclic.1 hcycB
  have hZcard : Nat.card (subtorusA1 n (Units.map (entrywiseHom Fr)) e6O5Theta) =
      Nat.card K ^ 5 - 1 := by
    rw [hZeq, Subgroup.card_map_of_injective hinj0, hcardB]
    show ((Polynomial.X ^ 5 - Polynomial.C 1 : ℤ[X]).eval (Nat.card K : ℤ)).natAbs = _
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
    have h1 : 1 ≤ Nat.card K ^ 5 := Nat.one_le_pow _ _ (by omega)
    have e : ((Nat.card K : ℤ) ^ 5 - 1) = ((Nat.card K ^ 5 - 1 : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub h1]
      ring
    rw [e, Int.natAbs_natCast]
  have hN : Nat.card K ^ 5 - 1 ≠ 0 := by
    have : 1 < Nat.card K ^ 5 := Nat.one_lt_pow (by norm_num) (by omega)
    omega
  have hord : p ^ (Nat.card (adjointGroup .E6 K)).factorization p =
      p ^ (Nat.card K ^ 5 - 1).factorization p := by
    have h1 : 1 ≤ Nat.card K ^ 5 := Nat.one_le_pow _ _ (by omega)
    exact ordProj_card_adjointGroup_E6 hp (by omega) hpq hord5 (d₀ := 5) (by decide) (by decide)
      hN (R := 1) (by push_cast [Nat.cast_sub h1]; ring) (by
        intro h
        exact hp.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) h))
  have hz : ∀ z : Fin Tag.E6.rank → ZMod p, z ≠ 0 →
      (e6O5W.map (Int.cast : ℤ → ZMod p))ᵀ *ᵥ z = ((Nat.card K : ℕ) : ZMod p) • z →
        {α | IsRoot .E6 α ∧ pair α z = 0} = {e6O5Theta, -e6O5Theta} := fun z hz0 hzM =>
    E6_order_five_lattice_and_exact_A1_prime_root_kernel.2.2.2.2.2.2.2.2 p hp hp5
      ((Nat.card K : ℕ) : ZMod p) hΦ5 z hz0 hzM
  have hkerZ : ∀ a : Fin Tag.E6.rank → Lˣ,
      rootDiagUnit .E6 a ∈ subtorusA1 n (Units.map (entrywiseHom Fr)) e6O5Theta →
      orderOf (rootDiagUnit .E6 a) = p → rootCharKernel a ⊆ {e6O5Theta, -e6O5Theta} := by
    intro a ha hap
    rw [hZeq] at ha
    obtain ⟨a', ha', haa'⟩ := ha
    have : a' = a := hinj0 haa'
    subst this
    exact (A1BlockData.rootCharKernel_eq Fr hFr hp hz ha'.1
      (pow_eq_one_of_orderOf_rootDiagUnit hap) (ne_one_of_orderOf_rootDiagUnit hp hap)).le
  have hS := a1_untwisted_structure .E6 3 (Or.inl ⟨rfl, rfl⟩) K hf hK L hp (by omega)
    hordW n hnC hθroot hZcyc hN hZcard hord hkerZ
  obtain ⟨e0⟩ := nonempty_mulEquiv_sl2_conj_range (K := K) (L := L) (1 : GL (Fin 2) L)
  haveI hSfin : Finite ↥((SpecialLinearGroup.map (algebraMap K L)).range.map
      (conjSL (1 : GL (Fin 2) L))) := Finite.of_equiv _ e0.toEquiv
  have hSx := hS _ (a1_typeI_action Fr hFr hn) (sl2_conj_range_centralizer (K := K) 1)
  have : Finite (ModGL .E6 K) := finite_modGL
  intro x hx X hX
  by_cases hK4 : 4 ≤ Nat.card K
  · obtain ⟨-, hSq⟩ := sl2_conj_range_quasisimple (L := L) hK4 (1 : GL (Fin 2) L)
    obtain ⟨ψ, P, Z, hψ, ⟨hPe⟩, hPψ, hnorm, hZ, hcent⟩ := (hSx x hx).1 hSq
    obtain ⟨e1⟩ := ExcNonsplit.nonempty_mulEquiv_of_isComponentOf_centralizer ψ hψ hPe hSq hPψ
      hnorm hZ hcent hX
    exact ⟨hK4, ⟨e0.trans e1⟩⟩
  · exfalso
    have hsolSL : Group.IsSolvable SL(2, K) := isSolvable_SL_two_of_card_lt_four (not_le.1 hK4)
    haveI : Group.IsSolvable ↥((SpecialLinearGroup.map (algebraMap K L)).range.map
        (conjSL (1 : GL (Fin 2) L))) :=
      Group.isSolvable_of_isSolvable_injective (f := e0.symm.toMonoidHom) e0.symm.injective
    haveI := (hSx x hx).2 inferInstance
    exact ExcNonsplit.not_isComponentOf_of_isSolvable hX

end CFSG.StandardType.E6Nonsplit
