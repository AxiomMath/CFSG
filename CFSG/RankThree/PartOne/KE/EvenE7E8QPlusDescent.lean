module

public import CFSG.RankThree.PartOne.KE.EvenE7E8QPlusWeyl
public import CFSG.RankThree.PartOne.KE.EvenE7E8QPlusTorus
public import CFSG.RankThree.Chevalley.SteinbergBNTwistedE6QuadraticExclusion
public import CFSG.LieType.Chevalley.EvenCanonicalFieldCentralizer

public section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Chevalley (cartanFunctional cartanFunctional_apply sixTorus_weylElt_ne_one)

theorem qplus_frobenius_fixed_mem {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) {K L : Type} [Field K]
    [Finite K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] [CharP K 2] (Fr : L →+* L)
    (hFr : ∀ c, Fr c = c ^ Nat.card K) {x : ModGL τ L} (hx : x ∈ adjointGroup τ L)
    (hF : Units.map (entrywiseHom Fr) x = x) :
    x ∈ (adjointGroup τ K).map (baseChangeGL (algebraMap K L)) := by
  classical
  obtain ⟨S, hS⟩ := exists_finset_descent hx
  obtain ⟨E, hEf, hSE, hKE⟩ := exists_finite_subfield_of_finset (K := K) S
  obtain ⟨y, hy, rfl⟩ := hS E hSE
  obtain ⟨σE, -, hJ, hfix⟩ := exists_subfieldFrobenius_data (τ := τ) Fr hFr E hKE
  have hyΓ := hfix y hy hF
  have : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  rw [entrywiseFixedGroup_eq_fixedFieldImage_of_ringChar_two (Or.inr (Or.inr (Or.inr hτ)))
    (ringChar.eq E 2) σE] at hyΓ
  rw [← hJ]
  exact Subgroup.mem_map_of_mem _ hyΓ

theorem qplus_exists_zeta (L : Type) [Field L] [CharP L 2] [IsAlgClosed L] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) : ∃ ζ : Lˣ, orderOf ζ = p := by
  have : NeZero (p : L) := ⟨by
    intro h
    have := (CharP.cast_eq_zero_iff L 2 p).1 h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 this).symm⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L p
  refine ⟨(hζ.isUnit hp.ne_zero).unit, ?_⟩
  rw [← orderOf_units, IsUnit.unit_spec, ← hζ.eq_orderOf]

theorem qplus_frobenius_zeta {L : Type} [Field L] {f p : ℕ} (Fr : L →+* L)
    (hFr : ∀ c, Fr c = c ^ 2 ^ f) {ζ : Lˣ} (hζ : orderOf ζ = p) (hpq : p ∣ 2 ^ f + 1) :
    Units.map Fr.toMonoidHom ζ = ζ⁻¹ := by
  have h1 : ζ ^ (2 ^ f) * ζ = 1 := by
    rw [← pow_succ]
    exact orderOf_dvd_iff_pow_eq_one.1 (by rw [hζ]; exact hpq)
  refine Units.ext ?_
  change Fr (ζ : L) = ((ζ⁻¹ : Lˣ) : L)
  rw [hFr, ← Units.val_pow_eq_pow_val, eq_inv_of_mul_eq_one_left h1]

theorem qplus_map_rootDiagUnit {τ : Tag} {L : Type} [Field L] (Fr : L →+* L)
    (a : Fin τ.rank → Lˣ) :
    Units.map (entrywiseHom Fr) (rootDiagUnit τ a) =
      rootDiagUnit τ fun i => Units.map Fr.toMonoidHom (a i) :=
  Units.ext (entrywise_rootDiag Fr a)

theorem qplusZ_conj_map_qplusTheta {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) {L : Type} [Field L]
    [CharP L 2] {f p : ℕ} (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ 2 ^ f) {ζ : Lˣ}
    (hζ : orderOf ζ = p) (hpq : p ∣ 2 ^ f + 1) (v : Fin τ.rank → ZMod p) :
    qplusZ τ L * Units.map (entrywiseHom Fr) (qplusTheta τ ζ v) * (qplusZ τ L)⁻¹ =
      qplusTheta τ ζ v := by
  have hζF := qplus_frobenius_zeta Fr hFr hζ hpq
  rw [qplusTheta, qplus_map_rootDiagUnit]
  have h : (fun i => Units.map Fr.toMonoidHom (ζ ^ qplusExp τ v i)) =
      (fun l => ζ ^ qplusExp τ v l)⁻¹ := by
    funext i
    rw [map_zpow, hζF, Pi.inv_apply, inv_zpow]
  rw [h, qplusZ_conj_rootDiagUnit hτ, inv_inv]

theorem qplus_orderOf_weylElt {τ : Tag} {K : Type} [Field K] [CharP K 2] (i : Fin τ.rank) :
    orderOf (weylElt τ K i 1) = 2 := by
  refine orderOf_eq_prime (p := 2) ?_ (sixTorus_weylElt_ne_one i)
  rw [sq, weylElt_one_mul_self, qplus_torusElt_neg_one]

theorem qplus_exists_hom_of_range {G M N : Type*} [Group G] [Group M] [Group N] (ι : G →* N)
    (hι : Function.Injective ι) (φ : M →* N) (h : ∀ x, φ x ∈ ι.range) :
    ∃ ψ : M →* G, ∀ x, ι (ψ x) = φ x :=
  ⟨(MonoidHom.ofInjective hι).symm.toMonoidHom.comp (φ.codRestrict ι.range h), fun x => by simp⟩

end CFSG.RankThree.PartOne.KE
