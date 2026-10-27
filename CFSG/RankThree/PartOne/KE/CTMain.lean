module

public import CFSG.RankThree.PartOne.KE.CTAbstract
public import CFSG.RankThree.PartOne.KE.CTLangData
public import CFSG.RankThree.PartOne.KE.CTTorus
public import CFSG.RankThree.PartOne.KE.F4Regular
public import CFSG.RankThree.Chevalley.G2F4FiniteFieldFixedMatrices

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Chevalley (G2_F4_exact_finite_field_fixed_root_matrices)
open scoped Matrix Polynomial

section Torus

variable {τ : Tag} {L : Type} [Field L]

theorem twistedTorus_eq_map_twistedFixedTuples [IsAlgClosed L] (w : WeylGroup τ) (Fr : L →+* L) :
    twistedTorus (canonicalRep (coxeterSystem τ) L w) Fr =
      (twistedFixedTuples w Fr).map (rootDiagUnitHom τ L) := by
  ext x
  constructor
  · intro hx
    obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (mem_twistedTorus.1 hx).1
    exact ⟨a, mem_twistedFixedTuples_iff_conj.2 (mem_twistedTorus.1 hx).2, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact mem_twistedTorus.2 ⟨rootDiagUnit_mem_torusGroup a, mem_twistedFixedTuples_iff_conj.1 ha⟩

theorem pow_eq_one_of_orderOf_rootDiagUnit {a : Fin τ.rank → Lˣ} {p : ℕ}
    (hxp : orderOf (rootDiagUnit τ a) = p) : ∀ i, a i ^ p = 1 := by
  have h1 : rootDiagUnit τ (a ^ p) = 1 := by
    have hpow : rootDiagUnit τ a ^ p = rootDiagUnit τ (a ^ p) :=
      ((rootDiagUnitHom τ L).map_pow a p).symm
    rw [← hpow, ← hxp]
    exact pow_orderOf_eq_one _
  have h2 : a ^ p = 1 := rootDiagUnit_injective (h1.trans rootDiagUnit_one.symm)
  intro i
  exact congrFun h2 i

theorem ne_one_of_orderOf_rootDiagUnit {a : Fin τ.rank → Lˣ} {p : ℕ} (hp : p.Prime)
    (hxp : orderOf (rootDiagUnit τ a) = p) : a ≠ 1 := by
  rintro rfl
  rw [rootDiagUnit_one, orderOf_one] at hxp
  exact hp.one_lt.ne hxp

end Torus

theorem cyclic_sylow_untwisted (τ : Tag) (d : ℕ) (K : Type) [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p)
    (hrat : ∀ (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] (Fr : L →+* L),
      (∀ c, Fr c = c ^ Nat.card K) → ∀ (X : Subgroup (ModGL τ L)) [Finite X],
        X ≤ adjointGroup τ L → (∀ x ∈ X, Units.map (entrywiseHom Fr) x = x) →
        ((adjointGroup τ K).map (baseChangeGL (algebraMap K L))).relIndex X ∣ d ∧
          ∀ p' : ℕ, p'.Prime → 3 < p' → ∀ P : Subgroup (ModGL τ L), P ≤ X → IsPGroup p' P →
            P ≤ (adjointGroup τ K).map (baseChangeGL (algebraMap K L)))
    (hcent : ∀ (M' : Type) [Field M'] [Finite M'], p ∣ Nat.card M'ˣ → ∀ {x : ModGL τ M'},
      x ∈ torusGroup τ M' → orderOf x = p →
      (∀ a : Fin τ.rank → M'ˣ, x = rootDiagUnit τ a →
        ∀ α : Fin τ.rank → ℤ, IsRoot τ α → rootChar a α ≠ 1) →
      adjointGroup τ M' ⊓ Subgroup.centralizer {x} = torusGroup τ M')
    (M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ) (hM : IsWeylMatrix τ M) (v : Fin τ.rank → ℤ)
    (hlin : LinearIndependent ℤ fun j : Fin τ.rank => (M ^ (j : ℕ)) *ᵥ v)
    (hspan : Submodule.span ℤ (Set.range fun j : Fin τ.rank => (M ^ (j : ℕ)) *ᵥ v) = ⊤)
    (hdet : M.charpoly.coeff 0 = 1 ∨ M.charpoly.coeff 0 = -1)
    (hne : M.charpoly.eval (Nat.card K : ℤ) ≠ 0)
    (hA : ∀ α : Fin τ.rank → ℤ, IsRoot τ α → ∃ A : ℤ[X],
      (∀ β, (Polynomial.aeval M A) *ᵥ β ∈ orbitLattice M α) ∧
        ¬ (p : ℤ) ∣ A.eval (Nat.card K : ℤ))
    (hord : p ^ (Nat.card (adjointGroup τ K)).factorization p =
      p ^ (M.charpoly.eval (Nat.card K : ℤ)).natAbs.factorization p) :
    CyclicSylowConclusion τ K p (M.charpoly.eval (Nat.card K : ℤ)).natAbs d := by
  classical
  obtain ⟨w, hw⟩ := hM
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype K := Fintype.ofFinite K
  have : Finite (ModGL τ K) := finite_modGL
  obtain ⟨f, hℓ, hf⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hℓ⟩
  have hq : Nat.card K = ringChar K ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hf
  have : CharP K (ringChar K) := ringChar.charP K
  let L := AlgebraicClosure K
  have : CharP L (ringChar K) := charP_of_injective_algebraMap (algebraMap K L).injective _
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  let Fr : L →+* L := iterateFrobenius L (ringChar K) (f : ℕ)
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hq]
    exact iterateFrobenius_def (ringChar K) (f : ℕ) c
  have hℓq : ringChar K ∣ Nat.card K := by
    rw [hq]
    exact dvd_pow_self _ f.ne_zero
  obtain ⟨g0, hg0C, hg0⟩ := lang_conjugator τ K (ℓ := ringChar K) (f := (f : ℕ)) f.pos L w
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
  have hrat' : ∀ (X : Subgroup (ModGL τ L)) [Finite X], X ≤ adjointGroup τ L →
      (∀ x ∈ X, Units.map (entrywiseHom Fr) x = x) → ι.range.relIndex X ∣ d ∧
        ∀ p : ℕ, p.Prime → 3 < p → ∀ P : Subgroup (ModGL τ L), P ≤ X → IsPGroup p P →
          P ≤ ι.range := by
    intro X _ hXC hXF
    rw [hrange]
    exact hrat L Fr hFr X hXC hXF
  have hcentL : ∀ x ∈ torusGroup τ L, orderOf x = p →
      (∀ a : Fin τ.rank → Lˣ, x = rootDiagUnit τ a →
        ∀ α : Fin τ.rank → ℤ, IsRoot τ α → rootChar a α ≠ 1) →
      ∀ y ∈ adjointGroup τ L, y * x = x * y → y ∈ torusGroup τ L :=
    fun x hxH hxp hreg y hy hcomm => by
      have : Algebra.IsAlgebraic K L := inferInstance
      exact torus_of_commuting_regular K hp hcent hxH hxp hreg hy hcomm
  have hT0 := twistedTorus_eq_map_twistedFixedTuples w Fr
  have hinj0 : Function.Injective (rootDiagUnitHom τ L) := rootDiagUnit_injective
  obtain ⟨hcycT, hcardT⟩ := isCyclic_and_card_twistedFixedTuples w M hw v hlin hspan Fr hFr
    (ℓ := ringChar K) hℓ hℓq hdet hne
  have hcyc : IsCyclic (twistedTorus (canonicalRep (coxeterSystem τ) L w) Fr) := by
    rw [hT0]
    exact (Subgroup.equivMapOfInjective (twistedFixedTuples w Fr) (rootDiagUnitHom τ L)
      hinj0).isCyclic.1 hcycT
  have hcard : Nat.card (twistedTorus (canonicalRep (coxeterSystem τ) L w) Fr) =
      (M.charpoly.eval (Nat.card K : ℤ)).natAbs := by
    rw [hT0, Subgroup.card_map_of_injective hinj0]
    exact hcardT
  have hreg : ∀ x ∈ twistedTorus (canonicalRep (coxeterSystem τ) L w) Fr, orderOf x = p →
      ∀ a : Fin τ.rank → Lˣ, x = rootDiagUnit τ a →
        ∀ α : Fin τ.rank → ℤ, IsRoot τ α → rootChar a α ≠ 1 := by
    intro x hx hxp a hxa α hα
    rw [hT0] at hx
    obtain ⟨a', ha', rfl⟩ := hx
    have hxa' : rootDiagUnit τ a' = rootDiagUnit τ a := hxa
    have haa : a' = a := rootDiagUnit_injective hxa'
    rw [← haa]
    have hxp' : orderOf (rootDiagUnit τ a') = p := hxp
    obtain ⟨A, hA1, hA2⟩ := hA α hα
    exact rootChar_ne_one_of_mem_twistedFixedTuples w M hw Fr hFr hp ha'
      (pow_eq_one_of_orderOf_rootDiagUnit hxp') (ne_one_of_orderOf_rootDiagUnit hp hxp') A hA1 hA2
  exact cyclic_sylow_of_twisted_torus d ι hι hιC (Units.map (entrywiseHom Fr)) hιΦ
    (canonicalRep (coxeterSystem τ) L w) g0 hg0C hg0 hp hp3 (Int.natAbs_ne_zero.2 hne)
    hrat' hcentL hcyc hcard hreg hord

theorem cyclic_torus_prime_centralizers : CyclicTorusTheorem := by
  intro τ d hτ M hM v hlin hspan hdet K _ _ p hp hp7 _ hne hA hord
  refine cyclic_sylow_untwisted τ d K hp (by omega) ?_ ?_ M hM v hlin hspan hdet hne hA hord
  · intro L _ _ _ Fr hFr X _ hXC hXF
    have : Algebra.IsAlgebraic K L := inferInstance
    exact finite_fixed_subgroup_rational d hτ Fr hFr X hXC hXF
  · intro M' _ _ hpM x hxH hxp hreg
    exact E_regular_large_prime_toral_centralizer τ
      (by rcases hτ with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp) M' hp hp7 hpM hxH hxp hreg

theorem cyclic_torus_prime_centralizers_F4 : CyclicTorusTheoremF4 := by
  intro M hM v hlin hspan hdet K _ _ p hp hp3 _ hne hA hord
  refine cyclic_sylow_untwisted .F4 1 K hp hp3 ?_ ?_ M hM v hlin hspan hdet hne hA hord
  · intro L _ _ _ Fr hFr X _ hXC hXF
    have hXle : X ≤ (adjointGroup Tag.F4 K).map (baseChangeGL (algebraMap K L)) := by
      intro x hx
      rw [← (G2_F4_exact_finite_field_fixed_root_matrices Tag.F4 (Or.inr rfl) K L Fr hFr).1]
      exact ⟨hXC hx, hXF x hx⟩
    exact ⟨Nat.dvd_one.2 (Subgroup.relIndex_eq_one.2 hXle), fun _ _ _ P hPX _ => hPX.trans hXle⟩
  · intro M' _ _ hpM x hxH hxp hreg
    exact F4_regular_prime_toral_centralizer M' hp hp3 hpM hxH hxp hreg

end CFSG.RankThree.PartOne.KE
