module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section1
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.ClassFunctionHelpers
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Character.Divisibility
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.Induction
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.Algebra.Group.Action.End
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.GroupTheory.GroupAction.OfQuotient
public import Mathlib.RingTheory.Polynomial.RationalRoot
public import Mathlib.RingTheory.Localization.Rat

namespace CFSG
end CFSG
open CFSG

/-!
# Bender--Glauberman Lemma 1.9 (the Glauberman correspondence)

For a finite `2`-group `S` acting by automorphisms on a finite `2'`-group
`U`, the irreducible characters of `U` fixed by `S` are in bijection with
the irreducible characters of the fixed-point subgroup `B = C_U(S)`, and
corresponding characters are congruent modulo `2` on `B`.

The proof follows the paper: the order-two case is treated through the
semidirect product `G = U ⋊ S`, the Brauer--Suzuki machinery, and
Lemma 1.7(iii); the general case is reduced by a central involution.
-/

noncomputable section

open scoped BigOperators
open scoped Pointwise
open scoped TensorProduct

namespace CFSG.BenderGlauberman

open GorensteinWalter
open Theory.Character

attribute [local instance] Fintype.ofFinite
attribute [local instance] Classical.propDecidable

universe u v

/-- Irreducible characters (the project's `IrrBG19` is defined in a module we do
not import here, to keep this file independent of the Section 2 WIP). -/
public abbrev IrrBG19 (G : Type u) [Group G] : Type u :=
  {φ : ClassFunction G // IsIrreducibleCharacter φ}

/-- The fixed-point subgroup `C_U(S)` of an action of `S` on `U`. -/
public def fixedSubgroup (S : Type u) (U : Type u) [Group S] [Group U]
    [MulDistribMulAction S U] : Subgroup U where
  carrier := {u : U | ∀ s : S, s • u = u}
  one_mem' := by intro s; simp
  mul_mem' := by
    intro u v hu hv s
    rw [MulDistribMulAction.smul_mul]
    rw [hu s, hv s]
  inv_mem' := by
    intro u hu s
    rw [smul_inv', hu s]

/-- Membership in the fixed-point subgroup: every `s` fixes `u`. -/
public theorem mem_fixedSubgroup_iff (S : Type u) (U : Type u) [Group S] [Group U]
    [MulDistribMulAction S U] (u : U) :
    u ∈ fixedSubgroup S U ↔ ∀ s : S, s • u = u := by
  rfl

/-- A subgroup of the acting group acts on the same group by restriction. -/
public instance instSubgroupMulDistribMulAction {S U : Type u} [Group S] [Group U]
    [MulDistribMulAction S U] (H : Subgroup S) : MulDistribMulAction H U where
  smul h u := (h : S) • u
  one_smul := by
    intro u
    change (1 : S) • u = u
    simp
  mul_smul := by
    intro a b u
    change (((a * b : H) : S) • u) = (a : S) • ((b : S) • u)
    rw [← mul_smul]
    simp
  smul_one := by
    intro h
    change (h : S) • (1 : U) = 1
    simp
  smul_mul := by
    intro h a b
    change (h : S) • (a * b) = ((h : S) • a) * ((h : S) • b)
    exact MulDistribMulAction.smul_mul (h : S) a b

/-- An irreducible character of `U` fixed by the action of `S`. -/
public def FixedIrr (S : Type u) (U : Type u) [Group S] [Group U]
    [MulDistribMulAction S U] (α : IrrBG19 U) : Prop :=
  ∀ s : S, (fun u : U => α.1 (s • u)) = α.1

/-- The `s`-conjugate of a class function of `U` under the action. -/
public def actionConj (S : Type u) (U : Type u) [Group S] [Group U]
    [MulDistribMulAction S U] (s : S) (φ : ClassFunction U) : ClassFunction U :=
  fun u => φ (s • u)

section ProductCharacters

variable {G : Type u} {H : Type v} [Group G] [Group H] [Fintype G] [Fintype H]

/-- The pointwise product character on a direct product. -/
@[expose] public def prodCharBG19 (χ : ClassFunction G) (ψ : ClassFunction H) :
    ClassFunction (G × H) :=
  fun p => χ p.1 * ψ p.2

omit [Fintype G] [Fintype H] in
/-- Product of characters is a character. -/
public theorem prodChar_isCharacterBG19 (χ : ClassFunction G) (ψ : ClassFunction H)
    (hχ : IsCharacter χ) (hψ : IsCharacter ψ) : IsCharacter (prodCharBG19 χ ψ) := by
  rcases hχ with ⟨n, ρ, hρeq⟩
  rcases hψ with ⟨m, σ, hσeq⟩
  let V := Fin n → ℂ
  let W := Fin m → ℂ
  let ρV : Representation ℂ G V := ρ
  let σW : Representation ℂ H W := σ
  let τ : Representation ℂ (G × H) (V ⊗[ℂ] W) :=
    Representation.tprod (ρV.comp (MonoidHom.fst G H)) (σW.comp (MonoidHom.snd G H))
  have hτchar : ∀ p : G × H, τ.character p = prodCharBG19 χ ψ p := by
    intro p
    rw [Representation.char_tensor]
    rw [hρeq, hσeq]
    rfl
  let b := Module.Free.chooseBasis ℂ (V ⊗[ℂ] W)
  let eι : Module.Free.ChooseBasisIndex ℂ (V ⊗[ℂ] W) ≃ Fin (n * m) :=
    Fintype.equivFinOfCardEq (by
      rw [← Module.finrank_eq_card_chooseBasisIndex, Module.finrank_tensorProduct]
      rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card,
        Fintype.card_fin, Fintype.card_fin])
  let e : (V ⊗[ℂ] W) ≃ₗ[ℂ] (Fin (n * m) → ℂ) :=
    (b.repr).trans ((Finsupp.linearEquivFunOnFinite ℂ ℂ
      (Module.Free.ChooseBasisIndex ℂ (V ⊗[ℂ] W))).trans
        (LinearEquiv.funCongrLeft ℂ ℂ eι.symm))
  refine ⟨n * m, charTrans e τ, ?_⟩
  ext p
  rw [← hτchar p]
  exact congrFun (Representation.char_iso (equiv_charTrans e τ)) p

/-- A character transported along a group isomorphism is a character. -/
public theorem isCharacter_congrBG19 {G : Type u} {H : Type v} [Group G] [Group H]
    (e : H ≃* G) {χ : ClassFunction G} (hχ : IsCharacter χ) :
    IsCharacter (fun h : H => χ (e h)) := by
  rcases hχ with ⟨n, ρ, hχeq⟩
  refine ⟨n, ρ.comp e, ?_⟩
  ext h
  rw [hχeq]
  rfl

/-- The `g⁻¹`-form scalar product of two product characters factors as the
product of the scalar products of its factors. -/
public theorem scalarProductInv_prod_mulBG19' (α α' : ClassFunction G) (β β' : ClassFunction H) :
    scalarProductInv (G × H) (fun p : G × H => α p.1 * β p.2)
      (fun p : G × H => α' p.1 * β' p.2) =
    scalarProductInv G α α' * scalarProductInv H β β' := by
  classical
  unfold scalarProductInv
  have hsum : (∑ p : G × H, (α p.1 * β p.2) * (α' p.1⁻¹ * β' p.2⁻¹)) =
      (∑ g : G, α g * α' g⁻¹) * (∑ h : H, β h * β' h⁻¹) := by
    rw [Fintype.sum_prod_type]
    calc
      (∑ g : G, ∑ h : H, (α g * β h) * (α' g⁻¹ * β' h⁻¹))
          = ∑ g : G, (α g * α' g⁻¹) * (∑ h : H, β h * β' h⁻¹) := by
              refine Finset.sum_congr rfl ?_
              intro g hg
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro h hh
              ring
      _ = (∑ g : G, α g * α' g⁻¹) * (∑ h : H, β h * β' h⁻¹) := by
              rw [Finset.sum_mul]
  rw [Nat.card_prod]
  change (↑(Nat.card G * Nat.card H))⁻¹ *
      (∑ p : G × H, (α p.1 * β p.2) * (α' p.1⁻¹ * β' p.2⁻¹)) =
    ((↑(Nat.card G))⁻¹ * (∑ g : G, α g * α' g⁻¹)) *
      ((↑(Nat.card H))⁻¹ * (∑ h : H, β h * β' h⁻¹))
  rw [hsum]
  have hG0 : (Nat.card G : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := G)).ne'
  have hH0 : (Nat.card H : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := H)).ne'
  rw [Nat.cast_mul]
  field_simp [hG0, hH0]

/-- The product of irreducible characters is irreducible. -/
public theorem prodChar_isIrreducibleBG19 (χ : ClassFunction G) (ψ : ClassFunction H)
    (hχ : IsIrreducibleCharacter χ) (hψ : IsIrreducibleCharacter ψ) :
    IsIrreducibleCharacter (prodCharBG19 χ ψ) := by
  refine isIrreducibleCharacter_of_norm_one_inv
    (prodChar_isCharacterBG19 χ ψ (isCharacter_of_isIrreducibleCharacter hχ)
      (isCharacter_of_isIrreducibleCharacter hψ)) ?_
  calc
    scalarProductInv (G × H) (prodCharBG19 χ ψ) (prodCharBG19 χ ψ)
        = scalarProductInv G χ χ * scalarProductInv H ψ ψ :=
          scalarProductInv_prod_mulBG19' χ χ ψ ψ
    _ = 1 := by
          rw [isIrreducible_norm_inv_one hχ, isIrreducible_norm_inv_one hψ]
          norm_num

/-- An irreducible character is an irreducible conj-class character. -/
public theorem isIrreducibleConjCharacter_of_isIrreducibleCharacterBG19 {G : Type u} [Group G] [Finite G]
    {φ : ClassFunction G} (hφ : IsIrreducibleCharacter φ) :
    IsIrreducibleConjCharacter (toConjClassFunction φ (irreducibleCharacter_isClassFunction hφ)) := by
  classical
  let : Fintype G := Fintype.ofFinite G
  rcases hφ with ⟨n, ρ, hρ, hφeq⟩
  constructor
  · refine ⟨n, ρ, ?_⟩
    cases hφeq
    exact toConjClassFunction_eq_of_apply (phi := ρ.character)
      (hphi := irreducibleCharacter_isClassFunction (φ := ρ.character) ⟨n, ρ, hρ, rfl⟩)
      (Phi := characterClassFunction ρ) (by intro g; rfl)
  · rw [classFunctionInner_toConjClassFunction]
    exact irreducible_scalarProduct_self ⟨n, ρ, hρ, hφeq⟩

/-- An irreducible conj-class character is an irreducible character. -/
public theorem isIrreducibleCharacter_ofConjClassFunctionBG19 {G : Type u} [Group G] [Finite G]
    {χ : ConjClassFunction G} (hχ : IsIrreducibleConjCharacter χ) :
    IsIrreducibleCharacter (ofConjClassFunction χ) := by
  classical
  let : Fintype G := Fintype.ofFinite G
  rcases hχ.1 with ⟨n, ρ, hρ⟩
  have : Representation.IsIrreducible ρ := by
    apply (irreducible_iff_character_norm_one (ρ := ρ)).2
    simpa [hρ] using hχ.2
  refine ⟨n, ρ, inferInstance, ?_⟩
  rw [hρ]
  exact ofConjClassFunction_characterClassFunction (G := G) (V := Fin n → ℂ) (rho := ρ)

/-- The number of irreducible characters equals the number of conjugacy classes. -/
public theorem fintype_card_irr_eq_conjClassesBG19 (G : Type u) [Group G] [Fintype G] :
    Fintype.card (IrrBG19 G) = Nat.card (ConjClasses G) := by
  classical
  let : Finite G := Finite.of_fintype G
  rcases Theory.Character.card_irreducible_characters_eq_card_conjClasses (G := G) with
    ⟨ι, hι, χ, hχ, hcard⟩
  let : Fintype ι := hι
  let f : ι → IrrBG19 G := fun i =>
    ⟨ofConjClassFunction (χ i), isIrreducibleCharacter_ofConjClassFunctionBG19 (hχ.1 i)⟩
  have hf_inj : Function.Injective f := by
    intro i j hij
    apply hχ.2.2
    have hpoint : ofConjClassFunction (χ i) = ofConjClassFunction (χ j) :=
      congrArg Subtype.val hij
    ext c
    rcases ConjClasses.exists_rep c with ⟨g, rfl⟩
    exact congrFun hpoint g
  have hf_surj : Function.Surjective f := by
    intro ν
    have hνConj : IsIrreducibleConjCharacter
        (toConjClassFunction ν.1 (irreducibleCharacter_isClassFunction ν.2)) :=
      isIrreducibleConjCharacter_of_isIrreducibleCharacterBG19 ν.2
    rcases hχ.2.1 _ hνConj with ⟨i, hi⟩
    refine ⟨i, Subtype.ext ?_⟩
    change ofConjClassFunction (χ i) = ν.1
    rw [hi]
    ext g
    rfl
  have hbij : Function.Bijective f := ⟨hf_inj, hf_surj⟩
  calc
    Fintype.card (IrrBG19 G) = Fintype.card ι :=
      Fintype.card_congr (Equiv.ofBijective f hbij).symm
    _ = Nat.card (ConjClasses G) := hcard

/-- In a commutative finite group, the number of conjugacy classes is the group
order. -/
public theorem nat_card_conjClasses_eq_card_of_isMulCommutativeBG19 (G : Type u) [Group G]
    [IsMulCommutative G] [Fintype G] :
    Nat.card (ConjClasses G) = Nat.card G := by
  classical
  let : Finite G := Finite.of_fintype G
  have h := card_comm_eq_card_conjClasses_mul_card G
  have hcomm : Nat.card {p : G × G // Commute p.1 p.2} = Nat.card G * Nat.card G := by
    let e : G × G ≃ {p : G × G // Commute p.1 p.2} := Equiv.ofBijective
      (fun p : G × G => ⟨p, (isMulCommutative_iff.mp (inferInstance : IsMulCommutative G)) p.1 p.2⟩)
      (by
        constructor
        · intro p q hEq
          exact Prod.ext (congrArg (fun x : {p : G × G // Commute p.1 p.2} => x.1.1) hEq)
            (congrArg (fun x : {p : G × G // Commute p.1 p.2} => x.1.2) hEq)
        · intro q
          exact ⟨(q.1.1, q.1.2), rfl⟩)
    exact (Nat.card_congr e).symm.trans (Nat.card_prod G G)
  have h' : Nat.card (ConjClasses G) * Nat.card G = Nat.card G * Nat.card G := by
    rw [← h, hcomm]
  exact Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := G)) (by simpa [mul_comm] using h')

/-- For a finite cyclic group, the number of irreducible characters is the group
order. -/
public theorem fintype_card_irr_eq_card_of_isCyclicBG19 (G : Type u) [Group G] [IsCyclic G] [Fintype G] :
    Fintype.card (IrrBG19 G) = Nat.card G := by
  let : Finite G := Finite.of_fintype G
  let : CommGroup G := IsCyclic.commGroup
  rw [fintype_card_irr_eq_conjClassesBG19 G, nat_card_conjClasses_eq_card_of_isMulCommutativeBG19 G]

/-- The irreducible character associated to a homomorphism into `ℂˣ`. -/
public def linearCharIrrBG19 {G : Type u} [Group G] [Fintype G] (φ : G →* ℂˣ) : IrrBG19 G :=
  ⟨fun x => ((φ x : ℂˣ) : ℂ), (isLinearCharacter_of_hom φ).1⟩

/-- Distinct homomorphisms give distinct irreducible characters. -/
public theorem linearCharIrr_injectiveBG19 {G : Type u} [Group G] [Fintype G] :
    Function.Injective (linearCharIrrBG19 (G := G)) := by
  intro φ ψ hEq
  apply MonoidHom.ext
  intro x
  apply Units.ext
  exact congrFun (congrArg Subtype.val hEq) x

/-- For a finite cyclic group, every irreducible character is linear (i.e. comes
from a homomorphism). -/
public theorem isLinearCharacter_of_isIrreducible_of_isCyclicBG19 {G : Type u} [Group G]
    [IsCyclic G] [Fintype G] {χ : ClassFunction G} (hχ : IsIrreducibleCharacter χ) :
    IsLinearCharacter χ := by
  classical
  let : Finite G := Finite.of_fintype G
  let : CommGroup G := IsCyclic.commGroup
  have hcard : Fintype.card (IrrBG19 G) = Fintype.card (G →* ℂˣ) := by
    exact (fintype_card_irr_eq_card_of_isCyclicBG19 G).trans
      (CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity G ℂ).symm |>.trans
        (by rw [Nat.card_eq_fintype_card])
  have hsurj : Function.Surjective (linearCharIrrBG19 (G := G)) :=
    ((Fintype.bijective_iff_injective_and_card (linearCharIrrBG19 (G := G))).2
      ⟨linearCharIrr_injectiveBG19 (G := G), hcard.symm⟩).2
  let ν : IrrBG19 G := ⟨χ, hχ⟩
  rcases hsurj ν with ⟨φ, hφ⟩
  have hχeq : χ = fun x => ((φ x : ℂˣ) : ℂ) := by
    exact (congrArg Subtype.val hφ).symm
  rw [hχeq]
  exact isLinearCharacter_of_hom φ

/-- Every nonzero character contains an irreducible constituent. -/
public theorem exists_irr_constituent_of_characterBG19 {G : Type u} [Group G] [Fintype G]
    {ψ : ClassFunction G} (hψ : IsCharacter ψ) (hne : ψ ≠ 0) :
    ∃ χ : ClassFunction G, IsIrreducibleCharacter χ ∧ scalarProduct G χ ψ ≠ 0 := by
  classical
  have hgen : IsGeneralizedCharacter ψ := ⟨ψ, 0, hψ, isCharacter_zero, by
    ext x
    simp⟩
  rcases char_decomp_generalized hgen with ⟨ι, hι, χs, ms, hirr, hdist, hψsum⟩
  let : Fintype ι := hι
  have hsome : ∃ i, ms i ≠ 0 := by
    by_contra hnone
    have hall : ∀ i, ms i = 0 := by
      intro i
      by_contra h
      exact hnone ⟨i, h⟩
    apply hne
    rw [hψsum]
    funext x
    simp [hall]
  rcases hsome with ⟨i₀, hms⟩
  refine ⟨χs i₀, hirr i₀, ?_⟩
  have hsp : scalarProduct G (χs i₀) ψ = (ms i₀ : ℂ) := by
    rw [hψsum]
    rw [scalarProduct_decomp_left (χ := χs i₀) (χs := χs) (ms := ms)
      (hχ := hirr i₀) (hχs := hirr)]
    calc
      (∑ i, (ms i : ℂ) * (if χs i = χs i₀ then 1 else 0))
          = (ms i₀ : ℂ) * (if χs i₀ = χs i₀ then 1 else 0) :=
              Finset.sum_eq_single (s := Finset.univ)
                (f := fun i : ι => (ms i : ℂ) * (if χs i = χs i₀ then 1 else 0)) i₀
                (by
                  intro j hj hji
                  have hne' : χs j ≠ χs i₀ := hdist j i₀ hji
                  simp [hne'])
                (by
                  intro hnot
                  exact (hnot (Finset.mem_univ i₀)).elim)
      _ = (ms i₀ : ℂ) := by simp
  rw [hsp]
  exact_mod_cast hms

omit [Fintype G] [Fintype H] in
private theorem isConj_prod_iff (x y : G × H) :
    IsConj x y ↔ IsConj x.1 y.1 ∧ IsConj x.2 y.2 := by
  constructor
  · intro h
    exact ⟨(MonoidHom.fst G H).map_isConj h, (MonoidHom.snd G H).map_isConj h⟩
  · rintro ⟨hx, hy⟩
    rw [isConj_iff] at hx hy ⊢
    rcases hx with ⟨a, ha⟩
    rcases hy with ⟨b, hb⟩
    refine ⟨(a, b), ?_⟩
    ext
    · exact ha
    · exact hb

private noncomputable def conjClassesProdEquiv : ConjClasses (G × H) ≃
    ConjClasses G × ConjClasses H :=
  (Quotient.congrRight (fun x y => isConj_prod_iff x y)).trans
    (Setoid.prodQuotientEquiv (IsConj.setoid G) (IsConj.setoid H)).symm

/-- The irreducible characters of a product are exactly the products of
irreducible characters of the factors. -/
public noncomputable def prodIrrBG19 : IrrBG19 G × IrrBG19 H → IrrBG19 (G × H) := fun p =>
  let χ : IrrBG19 G := p.1
  let ψ : IrrBG19 H := p.2
  ⟨prodCharBG19 χ.1 ψ.1, prodChar_isIrreducibleBG19 χ.1 ψ.1 χ.2 ψ.2⟩

public theorem prodIrr_injectiveBG19 : Function.Injective (prodIrrBG19 (G := G) (H := H)) := by
  rintro ⟨χ, ψ⟩ ⟨χ', ψ'⟩ hEq
  have hEqC : prodCharBG19 χ.1 ψ.1 = prodCharBG19 χ'.1 ψ'.1 :=
    congrArg Subtype.val hEq
  have hnorm : scalarProductInv (G × H) (prodCharBG19 χ.1 ψ.1)
      (prodCharBG19 χ'.1 ψ'.1) = 1 := by
    rw [hEqC]
    exact isIrreducible_norm_inv_one
      (prodChar_isIrreducibleBG19 χ'.1 ψ'.1 χ'.2 ψ'.2)
  have hfactor : scalarProductInv (G × H) (prodCharBG19 χ.1 ψ.1)
      (prodCharBG19 χ'.1 ψ'.1) =
      scalarProductInv G χ.1 χ'.1 * scalarProductInv H ψ.1 ψ'.1 :=
    scalarProductInv_prod_mulBG19' χ.1 χ'.1 ψ.1 ψ'.1
  rw [hfactor] at hnorm
  have h1 : scalarProductInv G χ.1 χ'.1 ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hnorm
    norm_num at hnorm
  have h2 : scalarProductInv H ψ.1 ψ'.1 ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hnorm
    norm_num at hnorm
  have hp : χ = χ' := by
    apply Subtype.ext
    by_contra hne
    have hsp : scalarProductInv G χ.1 χ'.1 = 0 :=
      isIrreducible_orthogonal_inv χ.2 χ'.2 (by
        intro hEq
        exact hne hEq)
    exact h1 hsp
  have hq : ψ = ψ' := by
    apply Subtype.ext
    by_contra hne
    have hsp : scalarProductInv H ψ.1 ψ'.1 = 0 :=
      isIrreducible_orthogonal_inv ψ.2 ψ'.2 (by
        intro hEq
        exact hne hEq)
    exact h2 hsp
  exact Prod.ext hp hq

public theorem prodIrr_cardBG19 : Fintype.card (IrrBG19 G × IrrBG19 H) = Fintype.card (IrrBG19 (G × H)) := by
  have hprod : Nat.card (ConjClasses (G × H)) =
      Nat.card (ConjClasses G) * Nat.card (ConjClasses H) := by
    calc
      Nat.card (ConjClasses (G × H)) =
          Nat.card (ConjClasses G × ConjClasses H) :=
            Nat.card_congr (conjClassesProdEquiv (G := G) (H := H))
      _ = Nat.card (ConjClasses G) * Nat.card (ConjClasses H) := Nat.card_prod _ _
  rw [Fintype.card_prod, fintype_card_irr_eq_conjClassesBG19 G,
    fintype_card_irr_eq_conjClassesBG19 H, fintype_card_irr_eq_conjClassesBG19 (G × H)]
  exact hprod.symm

public theorem prodIrr_surjectiveBG19 : Function.Surjective (prodIrrBG19 (G := G) (H := H)) :=
  ((Fintype.bijective_iff_injective_and_card (prodIrrBG19 (G := G) (H := H))).2
    ⟨prodIrr_injectiveBG19 (G := G) (H := H), prodIrr_cardBG19 (G := G) (H := H)⟩).2

/-- Every irreducible character of a direct product is a product of irreducible
characters of the factors. -/
public theorem irreducibleCharacter_eq_prodCharBG19 (φ : ClassFunction (G × H))
    (hφ : IsIrreducibleCharacter φ) :
    ∃ χ : IrrBG19 G, ∃ ψ : IrrBG19 H, prodCharBG19 χ.1 ψ.1 = φ := by
  let ν : IrrBG19 (G × H) := ⟨φ, hφ⟩
  rcases prodIrr_surjectiveBG19 (G := G) (H := H) ν with ⟨p, hp⟩
  let χ : IrrBG19 G := p.1
  let ψ : IrrBG19 H := p.2
  exact ⟨χ, ψ, by
    exact congrArg Subtype.val hp⟩

end ProductCharacters

section Parity

variable {G : Type u} [Group G] [Fintype G]

/-- The scalar product of an irreducible character with a character is a
natural number (the multiplicity of the irreducible in the character). -/
public theorem scalarProduct_irr_char_nat {χ ψ : ClassFunction G}
    (hχ : IsIrreducibleCharacter χ) (hψ : IsCharacter ψ) :
    ∃ r : ℕ, (r : ℂ) = scalarProduct G χ ψ := by
  classical
  rcases hχ with ⟨n, ρχ, hρχ, hχeq⟩
  rcases hψ with ⟨m, ρψ, hψeq⟩
  have : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (by exact_mod_cast (Nat.card_pos (α := G)).ne')
  have hfin : scalarProductInv G χ ψ =
      (Module.finrank ℂ (Representation.IntertwiningMap ρψ ρχ) : ℂ) := by
    have h := Representation.card_inv_mul_sum_char_mul_char_eq_finrank (ρ := ρψ) (σ := ρχ)
    simpa [scalarProductInv, characterProduct, hχeq, hψeq] using h
  have hb : star (scalarProduct G χ ψ) = scalarProductInv G χ ψ :=
    star_scalarProduct_eq_inv_of_char (isCharacter_of_isIrreducibleCharacter ⟨n, ρχ, ⟨hρχ, hχeq⟩⟩)
  refine ⟨Module.finrank ℂ (Representation.IntertwiningMap ρψ ρχ), ?_⟩
  have h1 : scalarProduct G χ ψ = star (scalarProductInv G χ ψ) := by
    rw [← hb, star_star]
  have h2 : star (scalarProductInv G χ ψ) =
      star ((Module.finrank ℂ (Representation.IntertwiningMap ρψ ρχ) : ℂ)) := by
    rw [hfin]
  have h3 : star ((Module.finrank ℂ (Representation.IntertwiningMap ρψ ρχ) : ℂ)) =
      (Module.finrank ℂ (Representation.IntertwiningMap ρψ ρχ) : ℂ) := by simp
  have h4 : (Module.finrank ℂ (Representation.IntertwiningMap ρψ ρχ) : ℂ) =
      ((Module.finrank ℂ (Representation.IntertwiningMap ρψ ρχ) : ℕ) : ℂ) := by norm_num
  exact (h1.trans (h2.trans (h3.trans h4))).symm

/-- The degree of an irreducible character of a `2'`-group is odd. -/
public theorem irr_degree_odd {U : Type u} [Group U] [Fintype U]
    (hU2' : Nat.Coprime 2 (Nat.card U)) (α : IrrBG19 U) :
    ∃ d : ℕ, Odd d ∧ (d : ℂ) = α.1 1 := by
  classical
  rcases α with ⟨φ, hφ⟩
  rcases hφ with ⟨n, ρ, hρ, hφeq⟩
  have h2ndvd : ¬ 2 ∣ Nat.card U := by
    intro h2
    have hg : (2 : ℕ).gcd (Nat.card U) = 1 := hU2'.gcd_eq_one
    have h2g : 2 ∣ (2 : ℕ).gcd (Nat.card U) := Nat.dvd_gcd (dvd_refl 2) h2
    rw [hg] at h2g
    norm_num at h2g
  have hUodd : Odd (Nat.card U) := by
    rw [Nat.odd_iff]
    have hcases : Nat.card U % 2 = 0 ∨ Nat.card U % 2 = 1 := by omega
    rcases hcases with h0 | h1
    · exfalso
      exact h2ndvd (Nat.dvd_of_mod_eq_zero h0)
    · exact h1
  have hnfin : Module.finrank ℂ (Fin n → ℂ) = n := by
    rw [Module.finrank_pi, Fintype.card_fin]
  have hdvd : n ∣ Nat.card U := by
    simpa [hnfin] using (irreducible_dimension_dvd_group_order ρ)
  have hn : Odd n := Odd.of_dvd_nat hUodd hdvd
  refine ⟨n, hn, ?_⟩
  change (n : ℂ) = φ 1
  rw [hφeq, Representation.char_one, Module.finrank_pi, Fintype.card_fin]

/-- Restriction of a class function on `U` to a subgroup `B`. -/
public def restrictChar {U : Type u} [Group U] (B : Subgroup U)
    (α : ClassFunction U) : ClassFunction (↥B) := fun b => α b

/-- Every irreducible character of a `2'`-group restricts to `B` with some
irreducible constituent of odd multiplicity. -/
public theorem exists_odd_multiplicity_restrict {U : Type u} [Group U] [Fintype U]
    (B : Subgroup U) (hU2' : Nat.Coprime 2 (Nat.card U)) (α : IrrBG19 U) :
    ∃ β : IrrBG19 (↥B), ∃ m : ℕ, Odd m ∧
      (m : ℂ) = scalarProduct (↥B) (restrictChar B α.1) β.1 := by
  classical
  let φ : ClassFunction (↥B) := restrictChar B α.1
  have hφchar : IsCharacter φ :=
    isCharacter_restrict B (isCharacter_of_isIrreducibleCharacter α.2)
  have hφgen : IsGeneralizedCharacter φ :=
    ⟨φ, 0, hφchar, isCharacter_zero, by ext x; simp⟩
  have hB2' : Nat.Coprime 2 (Nat.card (↥B)) := by
    exact Nat.Coprime.coprime_dvd_right (B.card_subgroup_dvd_card) hU2'
  have hcoeff (ν : IrrBG19 (↥B)) : ∃ m : ℕ,
      (m : ℂ) = scalarProduct (↥B) φ ν.1 :=
    by
      rcases scalarProduct_irr_char_nat (χ := ν.1) (ψ := φ) ν.2 hφchar with ⟨r, hr⟩
      refine ⟨r, ?_⟩
      calc
        (r : ℂ) = scalarProduct (↥B) ν.1 φ := hr
        _ = star (scalarProduct (↥B) ν.1 φ) := by
              rw [hr.symm]
              simp
        _ = scalarProduct (↥B) φ ν.1 := scalarProduct_conj ν.1 φ
  let m : IrrBG19 (↥B) → ℕ := fun ν => Classical.choose (hcoeff ν)
  have hm (ν : IrrBG19 (↥B)) : (m ν : ℂ) = scalarProduct (↥B) φ ν.1 :=
    Classical.choose_spec (hcoeff ν)
  have hdeg (ν : IrrBG19 (↥B)) : ∃ d : ℕ, Odd d ∧ (d : ℂ) = ν.1 1 :=
    irr_degree_odd hB2' ν
  let d : IrrBG19 (↥B) → ℕ := fun ν => Classical.choose (hdeg ν)
  have hd (ν : IrrBG19 (↥B)) : Odd (d ν) ∧ (d ν : ℂ) = ν.1 1 :=
    Classical.choose_spec (hdeg ν)
  rcases irr_degree_odd hU2' α with ⟨a, haOdd, ha⟩
  have hsum1 : φ 1 = ∑ ν : IrrBG19 (↥B), (m ν : ℂ) * (d ν : ℂ) := by
    have h := classFunction_eq_sum_irr_coeffs (G := ↥B) hφgen (1 : ↥B)
    rw [h]
    refine Finset.sum_congr rfl ?_
    intro ν hν
    rw [hm ν, (hd ν).2]
  have hsum1' : (a : ℂ) = ∑ ν : IrrBG19 (↥B), (m ν : ℂ) * (d ν : ℂ) := by
    calc
      (a : ℂ) = α.1 1 := ha
      _ = φ 1 := rfl
      _ = ∑ ν : IrrBG19 (↥B), (m ν : ℂ) * (d ν : ℂ) := hsum1
  by_contra hnone
  push_neg at hnone
  have hEvenProd : ∀ ν : IrrBG19 (↥B), Even (m ν * d ν) := by
    intro ν
    have hEvenM : Even (m ν) := by
      by_contra hOdd
      exact (hnone ν (m ν) (Nat.not_even_iff_odd.mp hOdd)) (hm ν)
    exact Even.mul_right hEvenM (d ν)
  have hEvenSum : Even (∑ ν : IrrBG19 (↥B), m ν * d ν) := by
    exact Finset.even_sum (fun ν : IrrBG19 (↥B) => m ν * d ν) (by intro ν hν; exact hEvenProd ν)
  have hsumNat : (∑ ν : IrrBG19 (↥B), (m ν : ℂ) * (d ν : ℂ)) =
      ((∑ ν : IrrBG19 (↥B), m ν * d ν : ℕ) : ℂ) := by
    norm_num
  have hNatEq : a = ∑ ν : IrrBG19 (↥B), m ν * d ν := by
    exact_mod_cast (hsum1'.trans hsumNat)
  have hEvenA : Even a := by
    rw [hNatEq]
    exact hEvenSum
  exact (Nat.not_even_iff_odd.mpr haOdd) hEvenA

end Parity

section OrbitRepresentatives

variable {G : Type u} [Group G] [Fintype G]

/-- Every class function lies in its own `Λ`-orbit. -/
public theorem orbit_self_mem (H0 U : Subgroup G) [Fintype ↥(LambdaHom H0 U)]
    (ν : ClassFunction (↥H0)) : ν ∈ orbit H0 U ν := by
  classical
  rw [orbit]
  refine Finset.mem_image.mpr ⟨1, Finset.mem_univ _, ?_⟩
  have h1 : LambdaChar (1 : ↥(LambdaHom H0 U)).1 = (1 : ClassFunction (↥H0)) := by
    ext x
    change (((1 : ↥(LambdaHom H0 U)).1 x : ℂˣ) : ℂ) = 1
    simp
  rw [h1, one_mul]

/-- Orbits are equal-or-disjoint: membership in an orbit identifies it. -/
public theorem orbit_eq_of_memBG19 (H0 U : Subgroup G) [Fintype ↥(LambdaHom H0 U)]
    {μ ν : ClassFunction (↥H0)} (hμ : μ ∈ orbit H0 U ν) :
    orbit H0 U μ = orbit H0 U ν := by
  classical
  rcases (Finset.mem_image.mp hμ) with ⟨l, hl, rfl⟩
  apply Finset.ext
  intro φ
  constructor
  · intro hφ
    rcases (Finset.mem_image.mp hφ) with ⟨l', hl', hEq⟩
    refine Finset.mem_image.mpr ⟨l' * l, Finset.mem_univ _, ?_⟩
    change LambdaChar ((l' * l : ↥(LambdaHom H0 U)).1) * ν = φ
    rw [← hEq]
    ext x
    simp [LambdaChar, mul_assoc]
  · intro hφ
    rcases (Finset.mem_image.mp hφ) with ⟨l', hl', hEq⟩
    refine Finset.mem_image.mpr ⟨l' * l⁻¹, Finset.mem_univ _, ?_⟩
    rw [← hEq]
    change LambdaChar ((l' * l⁻¹ : ↥(LambdaHom H0 U)).1) * (LambdaChar l.1 * ν) =
      LambdaChar l'.1 * ν
    ext x
    simp [LambdaChar, mul_assoc]

/-- The finite set of all `Λ`-orbits. -/
private noncomputable def orbitSet (H0 U : Subgroup G) [Fintype ↥(LambdaHom H0 U)] :
    Finset (Finset (ClassFunction (↥H0))) := by
  classical
  exact (Finset.univ : Finset (IrrBG19 (↥H0))).image
    (fun ν : IrrBG19 (↥H0) => orbit H0 U ν.1)

private lemma orbitSet_mem_nonempty (H0 U : Subgroup G) [Fintype ↥(LambdaHom H0 U)]
    {L : Finset (ClassFunction (↥H0))} (hL : L ∈ orbitSet H0 U) : L.Nonempty := by
  rcases Finset.mem_image.mp hL with ⟨ν, hν, hLν⟩
  refine ⟨ν.1, ?_⟩
  rw [← hLν]
  exact orbit_self_mem H0 U ν.1

/-- A system of orbit representatives for the `Λ`-orbits of `IrrBG19(H0)`. -/
private theorem exists_orbit_representatives (H0 U : Subgroup G)
    [Fintype ↥(LambdaHom H0 U)] :
    ∃ (ι : Type u) (_ : Fintype ι) (rep : ι → ClassFunction (↥H0)),
      (∀ i : ι, IsIrreducibleCharacter (rep i)) ∧
      (∀ ν : {ν : ClassFunction (↥H0) // IsIrreducibleCharacter ν},
        ∃! i : ι, ν.1 ∈ orbit H0 U (rep i)) := by
  classical
  let ι : Type u := {L : Finset (ClassFunction (↥H0)) // L ∈ orbitSet H0 U}
  let rep : ι → ClassFunction (↥H0) := fun L =>
    Classical.choose (orbitSet_mem_nonempty H0 U L.2)
  refine ⟨ι, inferInstance, rep, ?_, ?_⟩
  · intro L
    rcases Finset.mem_image.mp L.2 with ⟨ν, hν, hLν⟩
    have hspec : rep L ∈ L.1 := Classical.choose_spec (orbitSet_mem_nonempty H0 U L.2)
    have hνL' : rep L ∈ orbit H0 U ν.1 := hLν ▸ hspec
    exact orbit_mem_isIrreducible H0 U ν.2 hνL'
  · intro ν
    refine ⟨⟨orbit H0 U ν.1, Finset.mem_image.mpr ⟨ν, Finset.mem_univ ν, rfl⟩⟩, ?_, ?_⟩
    · have hspec : rep ⟨orbit H0 U ν.1,
          Finset.mem_image.mpr ⟨ν, Finset.mem_univ ν, rfl⟩⟩ ∈ orbit H0 U ν.1 :=
        Classical.choose_spec (orbitSet_mem_nonempty H0 U
          (Finset.mem_image.mpr ⟨ν, Finset.mem_univ ν, rfl⟩ :
            orbit H0 U ν.1 ∈ orbitSet H0 U))
      change ν.1 ∈ orbit H0 U
        (rep ⟨orbit H0 U ν.1, Finset.mem_image.mpr ⟨ν, Finset.mem_univ ν, rfl⟩⟩)
      rw [orbit_eq_of_memBG19 H0 U hspec]
      exact orbit_self_mem H0 U ν.1
    · intro L hLmem
      have hEqOrbit : L.1 = orbit H0 U ν.1 := by
        have hspec : rep L ∈ L.1 := Classical.choose_spec (orbitSet_mem_nonempty H0 U L.2)
        rcases Finset.mem_image.mp L.2 with ⟨μ, hμ, hLμ⟩
        have ho1 : orbit H0 U (rep L) = orbit H0 U ν.1 :=
          (orbit_eq_of_memBG19 H0 U hLmem).symm
        have ho2 : orbit H0 U (rep L) = orbit H0 U μ.1 := by
          rw [← hLμ] at hspec
          exact orbit_eq_of_memBG19 H0 U hspec
        have ho3 : orbit H0 U μ.1 = L.1 := hLμ
        rw [← ho1, ho2, ho3]
      apply Subtype.ext
      exact hEqOrbit

end OrbitRepresentatives

section OrderTwoGroup

/-- In a `2'`-group, the only element of order dividing two is the identity. -/
public theorem sq_eq_one_of_coprime_two {U : Type u} [Group U]
    (hU2' : Nat.Coprime 2 (Nat.card U)) {x : U} (hx : x ^ 2 = 1) : x = 1 := by
  classical
  have horder_dvd_card : orderOf x ∣ Nat.card U := orderOf_dvd_natCard x
  have horder_dvd_two : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hx
  have hcop : (orderOf x).Coprime 2 :=
    (Nat.Coprime.coprime_dvd_right horder_dvd_card hU2').symm
  have horder : orderOf x = 1 := Nat.Coprime.eq_one_of_dvd hcop horder_dvd_two
  exact (orderOf_eq_one_iff.mp horder)

/-- In a group of order two, every element squares to one. -/
public theorem sq_eq_one_of_card_two {S : Type u} [Group S] (hS2 : Nat.card S = 2) :
    ∀ s : S, s ^ 2 = 1 := by
  classical
  rcases (Nat.card_eq_two_iff' (1 : S)).1 hS2 with ⟨s0, hs0⟩
  intro s
  by_cases hs : s = 1
  · subst s
    simp
  · have hss : s = s0 := hs0.2 s hs
    rw [hss]
    -- s0^2 = 1 because the only nontrivial element has order 2
    have hs0ne : s0 ≠ 1 := hs0.1
    have hs0pow : s0 ^ 2 = 1 := by
      -- s0^2 is either 1 or s0; not s0 since s0≠1
      by_contra h
      have hcases : s0 ^ 2 = 1 ∨ s0 ^ 2 = s0 := by
        have hall : ∀ y : S, y = 1 ∨ y = s0 := by
          intro y
          by_cases hy : y = 1
          · exact Or.inl hy
          · exact Or.inr (hs0.2 y hy)
        exact hall (s0 ^ 2)
      rcases hcases with h1 | h2
      · contradiction
      · have hs0eq1 : s0 = 1 := by
          have hsq : s0 * s0 = s0 := by simpa [pow_two] using h2
          exact mul_left_cancel (a := s0) (b := s0) (c := 1) (by simpa using hsq)
        exact hs0ne hs0eq1
    exact hs0pow

end OrderTwoGroup

section FiniteInvolution

/-- An involution on a finite set with odd cardinality has a fixed point. -/
public theorem exists_fixed_of_involution_odd_card {α : Type u} [Fintype α]
    (f : Equiv.Perm α) (hf : f ^ 2 = 1) (hodd : Odd (Fintype.card α)) :
    ∃ a : α, f a = a := by
  have hnot : ¬ 2 ∣ Fintype.card α := by
    intro h2
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact Equiv.Perm.exists_fixed_point_of_prime (p := 2) (n := 1) hnot (σ := f)
    (by simpa using hf)

/-- A finite group whose order is coprime to `2` has odd cardinality. -/
public theorem odd_natCard_of_coprime_two {G : Type u} [Group G] [Fintype G]
    (hG2 : Nat.Coprime 2 (Nat.card G)) : Odd (Nat.card G) := by
  rw [Nat.odd_iff]
  have h2ndvd : ¬ 2 ∣ Nat.card G := by
    intro h2
    have hg : (2 : ℕ).gcd (Nat.card G) = 1 := hG2.gcd_eq_one
    have h2g : 2 ∣ (2 : ℕ).gcd (Nat.card G) := Nat.dvd_gcd (dvd_refl 2) h2
    rw [hg] at h2g
    norm_num at h2g
  have hcases : Nat.card G % 2 = 0 ∨ Nat.card G % 2 = 1 := by omega
  rcases hcases with h0 | h1
  · exfalso
    exact h2ndvd (Nat.dvd_of_mod_eq_zero h0)
  · exact h1

end FiniteInvolution

section CongruenceIntegers

/-- Integer congruence implies mod-2 divisibility: `a ≡ b (mod 2)` with
`a b : ℤ` gives `2 ∣ a - b`. -/
public theorem CongruentModTwo.eq_of_int {a b : ℤ}
    (h : CongruentModTwo (a : ℂ) (b : ℂ)) : (2 : ℤ) ∣ a - b := by
  classical
  rcases h with ⟨w, hw, hw'⟩
  let q : ℚ := ((a - b : ℤ) : ℚ) / 2
  have hwq : w = (q : ℂ) := by
    have h1 : ((a - b : ℤ) : ℂ) = 2 * w := by
      simpa using hw'
    have h2 : ((a - b : ℤ) : ℂ) = (q : ℂ) * 2 := by
      dsimp [q]
      norm_num
    have h3 : 2 * w = (q : ℂ) * 2 := by
      rw [← h1, h2]
    have h4 : 2 * w = 2 * (q : ℂ) := by
      simpa [mul_comm] using h3
    exact mul_left_cancel₀ (two_ne_zero : (2 : ℂ) ≠ 0) h4
  have hqint : IsIntegral ℤ q := by
    have hw'2 : IsIntegral ℤ (q : ℂ) := by
      rwa [← hwq]
    exact (isIntegral_algebraMap_iff (R := ℤ) (A := ℚ) (B := ℂ)).mp hw'2
  have hqIsInt : IsLocalization.IsInteger ℤ q :=
    UniqueFactorizationMonoid.integer_of_integral hqint
  rw [Rat.isLocalizationIsInteger_iff] at hqIsInt
  rcases hqIsInt with ⟨z, hz⟩
  have hzab : ((a - b : ℤ) : ℚ) = ((2 * z : ℤ) : ℚ) := by
    have hq2 : q = (z : ℚ) := hz.symm
    have hz2' : ((a - b : ℤ) : ℚ) / 2 = (z : ℚ) := by
      simpa [q] using hq2
    calc
      ((a - b : ℤ) : ℚ) = ((a - b : ℤ) : ℚ) / 2 * 2 := by norm_num
      _ = (z : ℚ) * 2 := by rw [hz2']
      _ = ((2 * z : ℤ) : ℚ) := by
        rw [Int.cast_mul]
        ring
  have hzab' : (a - b : ℤ) = 2 * z := by
    exact_mod_cast hzab
  exact ⟨z, hzab'⟩

/-- An odd natural number is not congruent to zero modulo two. -/
public theorem CongruentModTwo.not_zero_of_odd_nat {n : ℕ} (hn : Odd n) :
    ¬ CongruentModTwo 0 (n : ℂ) := by
  intro h
  have hdvd : (2 : ℤ) ∣ (0 - (n : ℤ)) :=
    CongruentModTwo.eq_of_int (a := 0) (b := (n : ℤ)) (by simpa using h)
  rcases hdvd with ⟨k, hk⟩
  have hk' : (2 : ℤ) ∣ (n : ℤ) := by
    use -k
    omega
  have h2n : 2 ∣ n := Int.ofNat_dvd.mp hk'
  rcases hn with ⟨c, hc⟩
  rcases h2n with ⟨m, hm⟩
  omega

/-- Uniqueness of the mod-2 correspondent on a subgroup of a `2'`-group:
if two irreducible characters of `B` are both congruent to the same class
function on `B`, they are equal. -/
public theorem congruence_unique {U : Type u} [Group U] [Fintype U]
    (B : Subgroup U) (hU2' : Nat.Coprime 2 (Nat.card U))
    {α : ClassFunction U} {β β' : ClassFunction (↥B)}
    (hβ : IsIrreducibleCharacter β) (hβ' : IsIrreducibleCharacter β')
    (h1 : ∀ b : ↥B, CongruentModTwo (α b) (β b))
    (h2 : ∀ b : ↥B, CongruentModTwo (α b) (β' b)) : β = β' := by
  classical
  by_contra hne
  have hB2' : Nat.Coprime 2 (Nat.card (↥B)) := by
    exact Nat.Coprime.coprime_dvd_right (B.card_subgroup_dvd_card) hU2'
  have hBodd : Odd (Nat.card (↥B)) := by
    rw [Nat.odd_iff]
    have h2ndvd : ¬ 2 ∣ Nat.card (↥B) := by
      intro h2
      have hg : (2 : ℕ).gcd (Nat.card (↥B)) = 1 := hB2'.gcd_eq_one
      have h2g : 2 ∣ (2 : ℕ).gcd (Nat.card (↥B)) := Nat.dvd_gcd (dvd_refl 2) h2
      rw [hg] at h2g
      norm_num at h2g
    have hcases : Nat.card (↥B) % 2 = 0 ∨ Nat.card (↥B) % 2 = 1 := by omega
    rcases hcases with h0 | h1
    · exfalso
      exact h2ndvd (Nat.dvd_of_mod_eq_zero h0)
    · exact h1
  have hββ : ∀ b : ↥B, CongruentModTwo ((β b) - (β' b)) 0 := by
    intro b
    have hb : CongruentModTwo (β b) (β' b) :=
      CongruentModTwo.trans (CongruentModTwo.symm (h1 b)) (h2 b)
    have hsub := CongruentModTwo.sub (a := β b) (b := β' b) (c := β' b) (d := β' b) hb
      (CongruentModTwo.refl (β' b))
    simpa using hsub
  rcases hβ with ⟨n, ρ, hρ, hβeq⟩
  have hβcopy : IsIrreducibleCharacter β := ⟨n, ρ, hρ, hβeq⟩
  have hterm : ∀ b : ↥B, CongruentModTwo ((β b - β' b) * β b⁻¹) 0 := by
    intro b
    exact CongruentModTwo.mul_zero_left (hββ b)
      (by simpa [hβeq] using (character_value_isIntegral ρ (b⁻¹)))
  have hsum0 : CongruentModTwo (∑ b : ↥B, (β b - β' b) * β b⁻¹) 0 := by
    exact CongruentModTwo.sum_zero hterm
  have hsum_self : (∑ b : ↥B, β b * β b⁻¹) = (Nat.card (↥B) : ℂ) := by
    have hcp : characterProduct (↥B) β β = 1 := irreducibleCharacter_self hβcopy
    have hdef : characterProduct (↥B) β β =
        (Nat.card (↥B) : ℂ)⁻¹ * (∑ b : ↥B, β b * β b⁻¹) := rfl
    have hne0 : (Nat.card (↥B) : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.card_pos (α := ↥B)).ne'
    calc
      (∑ b : ↥B, β b * β b⁻¹) = (Nat.card (↥B) : ℂ) * characterProduct (↥B) β β := by
        rw [hdef]
        field_simp [hne0]
      _ = (Nat.card (↥B) : ℂ) := by simp [hcp]
  have hsum_orth : (∑ b : ↥B, β' b * β b⁻¹) = 0 := by
    have hcp : characterProduct (↥B) β' β = 0 :=
      irreducibleCharacters_orthogonal hβ' hβcopy (fun h => hne h.symm)
    have hdef : characterProduct (↥B) β' β =
        (Nat.card (↥B) : ℂ)⁻¹ * (∑ b : ↥B, β' b * β b⁻¹) := rfl
    have hne0 : (Nat.card (↥B) : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.card_pos (α := ↥B)).ne'
    calc
      (∑ b : ↥B, β' b * β b⁻¹) = (Nat.card (↥B) : ℂ) * characterProduct (↥B) β' β := by
        rw [hdef]
        field_simp [hne0]
      _ = 0 := by simp [hcp]
  have hsum_eq : (∑ b : ↥B, (β b - β' b) * β b⁻¹) = (Nat.card (↥B) : ℂ) := by
    calc
      (∑ b : ↥B, (β b - β' b) * β b⁻¹)
          = (∑ b : ↥B, β b * β b⁻¹) - (∑ b : ↥B, β' b * β b⁻¹) := by
              simp [sub_mul, Finset.sum_sub_distrib]
      _ = (∑ b : ↥B, β b * β b⁻¹) := by rw [hsum_orth, sub_zero]
      _ = (Nat.card (↥B) : ℂ) := hsum_self
  have hBcong : CongruentModTwo (Nat.card (↥B) : ℂ) 0 := by
    rw [← hsum_eq]
    exact hsum0
  exact CongruentModTwo.not_zero_of_odd_nat (n := Nat.card (↥B)) hBodd hBcong.symm

/-- Two irreducible characters congruent modulo `2` everywhere are equal. -/
public theorem eq_of_congruent_irr {U : Type u} [Group U] [Fintype U]
    (hU2' : Nat.Coprime 2 (Nat.card U)) {β β' : IrrBG19 U}
    (h : ∀ u : U, CongruentModTwo (β.1 u) (β'.1 u)) : β = β' := by
  apply Subtype.ext
  funext u
  have hβT : IsIrreducibleCharacter (fun x : ↥(⊤ : Subgroup U) => β.1 x.1) := by
    simpa using (isIrreducibleCharacter_congr (Subgroup.topEquiv (G := U)) β.2)
  have hβ'T : IsIrreducibleCharacter (fun x : ↥(⊤ : Subgroup U) => β'.1 x.1) := by
    simpa using (isIrreducibleCharacter_congr (Subgroup.topEquiv (G := U)) β'.2)
  have hEq := congruence_unique (U := U) (B := ⊤) hU2'
    (α := β.1)
    (β := fun x : ↥(⊤ : Subgroup U) => β.1 x.1)
    (β' := fun x : ↥(⊤ : Subgroup U) => β'.1 x.1)
    hβT hβ'T
    (fun x => CongruentModTwo.refl (β.1 x.1)) (fun x => h x.1)
  exact congrFun hEq ⟨u, trivial⟩

/-- The irreducible characters are invariant under group isomorphism. -/
public noncomputable def irrCongr {G : Type u} {H : Type u} [Group G] [Group H]
    [Fintype G] [Fintype H] (e : H ≃* G) : IrrBG19 G ≃ IrrBG19 H where
  toFun α := ⟨fun h : H => α.1 (e h), isIrreducibleCharacter_congr e α.2⟩
  invFun β := ⟨fun g : G => β.1 (e.symm g), isIrreducibleCharacter_congr e.symm β.2⟩
  left_inv α := by
    apply Subtype.ext
    funext g
    change α.1 (e (e.symm g)) = α.1 g
    rw [e.apply_symm_apply]
  right_inv β := by
    apply Subtype.ext
    funext h
    change β.1 (e.symm (e h)) = β.1 h
    rw [e.symm_apply_apply]

/-- The conjugate of an irreducible character under the action of `S`. -/
public noncomputable def actionIrr {S U : Type u} [Group S] [Group U]
    [Fintype S] [Fintype U]
    [MulDistribMulAction S U] (s : S) (α : IrrBG19 U) : IrrBG19 U :=
  ⟨fun u => α.1 (s • u),
    isIrreducibleCharacter_congr
      (MulDistribMulAction.toMulEquiv (M := U) (G := S) s) α.2⟩

/-- Conjugating a character fixed by a subgroup `H` by an element commuting
with `H` keeps it fixed by `H`. -/
public theorem actionIrr_fixed_of_forall_commute {S U : Type u} [Group S] [Group U]
    [Fintype S] [Fintype U]
    [MulDistribMulAction S U] (H : Subgroup S) {s : S}
    (hs : ∀ h : ↥H, (h : S) * s = s * (h : S))
    {α : IrrBG19 U} (hα : FixedIrr (↥H) U α) :
    FixedIrr (↥H) U (actionIrr s α) := by
  rw [FixedIrr]
  intro h
  funext u
  change α.1 (s • ((h : S) • u)) = α.1 (s • u)
  have hcomm : (h : S) * s = s * (h : S) := hs h
  have h1 : s • ((h : S) • u) = (h : S) • (s • u) := by
    rw [← mul_smul, ← mul_smul]
    congr 1
    exact hcomm.symm
  rw [h1]
  exact congrFun (hα h) (s • u)

/-- The fixed subgroup of a single automorphism. -/
public def autFixedBy {U : Type u} [Group U] (σ : MulAut U) : Subgroup U where
  carrier := {u : U | σ u = u}
  one_mem' := by simp
  mul_mem' := by
    intro u v hu hv
    change σ (u * v) = u * v
    rw [map_mul σ u v, hu, hv]
  inv_mem' := by
    intro u hu
    change σ u⁻¹ = u⁻¹
    rw [map_inv σ u, hu]

/-- Membership in the fixed subgroup of an automorphism. -/
public theorem mem_autFixedBy_iff {U : Type u} [Group U] (σ : MulAut U) (u : U) :
    u ∈ autFixedBy σ ↔ σ u = u := by
  rfl

/-- An irreducible character fixed by an automorphism. -/
public def FixedIrrAut {U : Type u} [Group U] (σ : MulAut U) (α : IrrBG19 U) : Prop :=
  (fun u : U => α.1 (σ u)) = α.1

end CongruenceIntegers

section SemidirectSetup

variable {S U : Type u} [Group S] [Group U] [Fintype S] [Fintype U]
variable [MulDistribMulAction S U]

/-- The semidirect product `U ⋊ S` attached to the action. -/
public abbrev SemiProduct (S : Type u) (U : Type u) [Group S] [Group U]
    [MulDistribMulAction S U] : Type u :=
  SemidirectProduct U S (MulDistribMulAction.toMulAut S U)

/-- The image of the fixed subgroup `B = C_U(S)` in `U ⋊ S`. -/
public abbrev Bimg (S : Type u) (U : Type u) [Group S] [Group U]
    [MulDistribMulAction S U] : Subgroup (SemiProduct S U) :=
  (SemidirectProduct.inl.comp (fixedSubgroup S U).subtype).range

/-- The embedding `S × B → U ⋊ S` whose image is `H0`. -/
public noncomputable def h0Hom (S : Type u) (U : Type u) [Group S] [Group U]
    [MulDistribMulAction S U] : fixedSubgroup S U × S →* SemiProduct S U := by
  let fn : fixedSubgroup S U →* SemiProduct S U :=
    SemidirectProduct.inl.comp (fixedSubgroup S U).subtype
  let fg : S →* SemiProduct S U := SemidirectProduct.inr
  let φ : S →* MulAut (fixedSubgroup S U) := 1
  let h : ∀ s : S, fn.comp (φ s).toMonoidHom =
      (MulAut.conj (fg s)).toMonoidHom.comp fn := by
    intro s
    apply MonoidHom.ext
    intro b
    have hb : (SemidirectProduct.inl (b : U) : SemiProduct S U) =
        SemidirectProduct.inr s * SemidirectProduct.inl (b : U) *
          (SemidirectProduct.inr s)⁻¹ := by
      apply SemidirectProduct.ext
      · simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right, SemidirectProduct.left_inl, SemidirectProduct.right_inl, SemidirectProduct.left_inr, SemidirectProduct.right_inr, SemidirectProduct.inv_left, one_mul, mul_one, MulDistribMulAction.toMulAut_apply, MulDistribMulAction.toMulEquiv_apply]
        rw [b.2 s, smul_smul, mul_inv_cancel, one_smul, inv_one, mul_one]
      · simp only [SemidirectProduct.mul_right, SemidirectProduct.right_inl, SemidirectProduct.right_inr, SemidirectProduct.inv_right, mul_one]
        rw [mul_inv_cancel]
    simpa [fn, fg, φ] using hb
  exact (SemidirectProduct.lift fn fg h).comp
    (SemidirectProduct.mulEquivProd (N := fixedSubgroup S U) (G := S)).symm.toMonoidHom

/-- The subgroup `H0 = S × B` of the semidirect product. -/
public def H0sub (S : Type u) (U : Type u) [Group S] [Group U]
    [MulDistribMulAction S U] : Subgroup (SemiProduct S U) where
  carrier := {x | x.left ∈ fixedSubgroup S U}
  one_mem' := by
    intro x
    simp
  mul_mem' := by
    intro x y hx hy
    change (x * y).left ∈ fixedSubgroup S U
    rw [SemidirectProduct.mul_left]
    have hyfix : x.right • y.left = y.left := by
      exact (mem_fixedSubgroup_iff S U y.left).1 hy x.right
    simpa [hyfix] using (fixedSubgroup S U).mul_mem hx hy
  inv_mem' := by
    intro x hx
    change x⁻¹.left ∈ fixedSubgroup S U
    rw [SemidirectProduct.inv_left]
    have hxfix : x.right⁻¹ • x.left⁻¹ = x.left⁻¹ := by
      exact (mem_fixedSubgroup_iff S U x.left⁻¹).1
        ((fixedSubgroup S U).inv_mem hx) x.right⁻¹
    simpa [hxfix] using (fixedSubgroup S U).inv_mem hx

/-- Membership in `H0 = S × B`: the `U`-component lies in `B`. -/
public theorem mem_H0sub_iff (S : Type u) (U : Type u) [Group S] [Group U]
    [MulDistribMulAction S U] (x : SemiProduct S U) :
    x ∈ H0sub S U ↔ x.left ∈ fixedSubgroup S U := by
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The explicit value of `h0Hom`: `(b,s) ↦ (b,s)` in the semidirect product. -/
public theorem h0Hom_apply (S : Type u) (U : Type u) [Group S] [Group U]
    [MulDistribMulAction S U] (p : fixedSubgroup S U × S) :
    h0Hom S U p = (⟨(p.1 : U), p.2⟩ : SemiProduct S U) := by
  unfold h0Hom
  simp only [MonoidHom.comp_apply]
  simp [SemidirectProduct.lift, SemidirectProduct.mulEquivProd]

/-- The embedding `h0Hom` is injective. -/
public theorem h0Hom_injective (S : Type u) (U : Type u) [Group S] [Group U]
    [MulDistribMulAction S U] : Function.Injective (h0Hom S U) := by
  intro p q hEq
  apply Prod.ext
  · apply Subtype.ext
    have hL := congrArg (fun x : SemiProduct S U => x.left) hEq
    rw [h0Hom_apply, h0Hom_apply] at hL
    exact hL
  · have hR := congrArg (fun x : SemiProduct S U => x.right) hEq
    rw [h0Hom_apply, h0Hom_apply] at hR
    exact hR

/-- The isomorphism `H0 ≃ B × S` induced by `h0Hom`. -/
public noncomputable def H0equiv (S : Type u) (U : Type u) [Group S] [Group U]
    [MulDistribMulAction S U] : H0sub S U ≃* fixedSubgroup S U × S where
  toFun x := (⟨x.1.left, (mem_H0sub_iff S U x.1).1 x.2⟩, x.1.right)
  invFun p := ⟨h0Hom S U p, (mem_H0sub_iff S U (h0Hom S U p)).2 (by
    rw [h0Hom_apply]
    exact p.1.2)⟩
  left_inv x := by
    apply Subtype.ext
    change h0Hom S U (⟨x.1.left, (mem_H0sub_iff S U x.1).1 x.2⟩, x.1.right) = x.1
    rw [h0Hom_apply]
  right_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      change (h0Hom S U p).left = p.1
      simp [h0Hom_apply]
    · change (h0Hom S U p).right = p.2
      simp [h0Hom_apply]
  map_mul' x y := by
    apply Prod.ext
    · apply Subtype.ext
      change ((x : SemiProduct S U) * (y : SemiProduct S U)).left =
        (x : SemiProduct S U).left * (y : SemiProduct S U).left
      rw [SemidirectProduct.mul_left]
      have hyfix : (x : SemiProduct S U).right • (y : SemiProduct S U).left =
          (y : SemiProduct S U).left := by
        exact (mem_fixedSubgroup_iff S U (y : SemiProduct S U).left).1
          ((mem_H0sub_iff S U (y : SemiProduct S U)).1 y.2) (x : SemiProduct S U).right
      simp [hyfix]
    · change ((x : SemiProduct S U) * (y : SemiProduct S U)).right =
        (x : SemiProduct S U).right * (y : SemiProduct S U).right
      rw [SemidirectProduct.mul_right]

/-- The subgroup `B × {1}` of `B × S`; the image of `Bimg` under `H0equiv`. -/
public abbrev Bprod (B S : Type u) [Group B] [Group S] : Subgroup (B × S) :=
  (⊤ : Subgroup B).prod ⊥

/-- `B × {1}` is normal in `B × S`. -/
public theorem Bprod_normal (B S : Type u) [Group B] [Group S] :
    (Bprod B S).Normal := by
  constructor
  · intro n hn g
    have hn2 : n.2 = 1 := by
      simpa [Bprod] using (Subgroup.mem_prod.mp hn).2
    apply Subgroup.mem_prod.mpr
    constructor
    · trivial
    · change (g * n * g⁻¹).2 = 1
      change g.2 * n.2 * g.2⁻¹ = 1
      rw [hn2, mul_one, mul_inv_cancel]

/-- `Bimg ≤ H0sub`: the fixed subgroup of `U` lies inside `S × B`. -/
public theorem Bimg_le_H0 (S : Type u) (U : Type u) [Group S] [Group U]
    [MulDistribMulAction S U] : Bimg S U ≤ H0sub S U := by
  intro g hg
  rcases hg with ⟨b, hb⟩
  rw [mem_H0sub_iff]
  rw [← hb]
  exact b.2

/-- Membership in `Bimg` inside `H0sub`, transported to `B × S`. -/
public theorem mem_H0equiv_Bimg_iff (S : Type u) (U : Type u) [Group S] [Group U]
    [MulDistribMulAction S U] (y : fixedSubgroup S U × S) :
    y ∈ Subgroup.map (H0equiv S U) ((Bimg S U).subgroupOf (H0sub S U)) ↔
      y ∈ Bprod (fixedSubgroup S U) S := by
  classical
  let e : H0sub S U ≃* fixedSubgroup S U × S := H0equiv S U
  constructor
  · intro hy
    rcases (Subgroup.mem_map.mp hy) with ⟨x, hx, rfl⟩
    have hxmem : (x : SemiProduct S U) ∈ Bimg S U := by
      simpa [Bimg] using (Subgroup.mem_subgroupOf.mp hx)
    rcases hxmem with ⟨b, hb⟩
    have hxval : (x : SemiProduct S U) = SemidirectProduct.inl (b : U) := hb.symm
    have hval : (h0Hom S U (e x) : SemiProduct S U) = (x : SemiProduct S U) := by
      change ((e.symm (e x) : H0sub S U) : SemiProduct S U) = (x : SemiProduct S U)
      rw [e.symm_apply_apply]
    have hx0 : h0Hom S U (e x) = SemidirectProduct.inl (b : U) := by
      rw [hval]
      exact hxval
    have hy2 : (e x).2 = 1 := by
      have hR := congrArg (fun z : SemiProduct S U => z.right) hx0
      rw [h0Hom_apply] at hR
      simpa using hR
    exact Subgroup.mem_prod.mpr ⟨trivial, by simpa using hy2⟩
  · intro hy
    refine ⟨(e.symm y), ?_, by simp [e]⟩
    have hy2 : y.2 = 1 := by
      have hy' : (y.1, y.2) ∈ Bprod (fixedSubgroup S U) S := hy
      simpa [Bprod] using (Subgroup.mem_prod.mp hy').2
    have hval : ((e.symm y : SemiProduct S U)) =
        SemidirectProduct.inl (y.1 : U) := by
      change h0Hom S U y =
        SemidirectProduct.inl (y.1 : U)
      rw [h0Hom_apply]
      apply SemidirectProduct.ext
      · rfl
      · simpa using hy2
    exact Subgroup.mem_subgroupOf.mpr (by
      rw [hval]
      exact ⟨y.1, rfl⟩)

/-- The image of `Bimg` under `H0equiv` is exactly `B × {1}`. -/
public theorem H0equiv_map_Bimg (S : Type u) (U : Type u) [Group S] [Group U]
    [MulDistribMulAction S U] :
    Subgroup.map (H0equiv S U) ((Bimg S U).subgroupOf (H0sub S U)) =
      Bprod (fixedSubgroup S U) S := by
  apply Subgroup.ext
  intro y
  exact mem_H0equiv_Bimg_iff S U y

/-- `Bimg` is normal in `H0 = S × B`. -/
public theorem Bimg_subgroupOf_normal (S : Type u) (U : Type u) [Group S] [Group U]
    [MulDistribMulAction S U] :
    ((Bimg S U).subgroupOf (H0sub S U)).Normal := by
  let K : Subgroup (H0sub S U) := (Bimg S U).subgroupOf (H0sub S U)
  have hMapNormal :
      (Subgroup.map (H0equiv S U : H0sub S U →* fixedSubgroup S U × S) K).Normal := by
    rw [H0equiv_map_Bimg]
    exact Bprod_normal (fixedSubgroup S U) S
  exact hMapNormal.of_map_injective (H0equiv S U).injective

/-- In the order-two case, `B` has index `2` in `H0 = S × B`. -/
public theorem Bimg_subgroupOf_index (S : Type u) (U : Type u) [Group S] [Group U]
    [MulDistribMulAction S U] (hS2 : Nat.card S = 2) :
    ((Bimg S U).subgroupOf (H0sub S U)).index = 2 := by
  have hmap := H0equiv_map_Bimg S U
  let K : Subgroup (H0sub S U) := (Bimg S U).subgroupOf (H0sub S U)
  calc
    K.index = (Subgroup.map (↑(H0equiv S U)) K).index := by
          rw [← Subgroup.index_map_equiv K (H0equiv S U)]
    _ = (Bprod (fixedSubgroup S U) S).index := by rw [hmap]
    _ = (⊥ : Subgroup S).index := by simp [Bprod, Subgroup.index_prod]
    _ = Nat.card S := by simp
    _ = 2 := hS2

/-- A group of order two is commutative. -/
public theorem comm_of_card_two {S : Type u} [Group S] (hS2 : Nat.card S = 2) :
    ∀ a b : S, a * b = b * a := by
  classical
  rcases (Nat.card_eq_two_iff' (1 : S)).1 hS2 with ⟨s, hs⟩
  intro a b
  by_cases ha1 : a = 1
  · subst a
    simp
  · have has : a = s := hs.2 a ha1
    by_cases hb1 : b = 1
    · subst b
      simp
    · have hbs : b = s := hs.2 b hb1
      rw [has, hbs]

/-- Commutators of `H0 = S × B` lie in `B` when `S` has order two. -/
public theorem Bimg_subgroupOf_comm (S : Type u) (U : Type u) [Group S] [Group U]
    [MulDistribMulAction S U] (hS2 : Nat.card S = 2) :
    ∀ x y : H0sub S U,
      (x * y) / (y * x) ∈ (Bimg S U).subgroupOf (H0sub S U) := by
  have hScomm : ∀ a b : S, a * b = b * a := comm_of_card_two hS2
  intro x y
  let e : H0sub S U ≃* fixedSubgroup S U × S := H0equiv S U
  have hprod : (e x * e y) /
      (H0equiv S U y * H0equiv S U x) ∈ Bprod (fixedSubgroup S U) S := by
    apply Subgroup.mem_prod.mpr
    constructor
    · trivial
    · change ((H0equiv S U x * H0equiv S U y) /
        (H0equiv S U y * H0equiv S U x)).2 = 1
      simp [div_eq_mul_inv, mul_inv_rev]
      rw [hScomm ((H0equiv S U x).2) ((H0equiv S U y).2)]
      group
  have hzMap : e ((x * y) / (y * x)) ∈
      Subgroup.map (↑e) ((Bimg S U).subgroupOf (H0sub S U)) := by
    have hEq : e ((x * y) / (y * x)) = (e x * e y) / (e y * e x) := by
      simp [map_mul]
    have hprod' : e ((x * y) / (y * x)) ∈ Bprod (fixedSubgroup S U) S := by
      simpa [hEq] using hprod
    exact (mem_H0equiv_Bimg_iff S U (e ((x * y) / (y * x)))).2 hprod'
  rcases (Subgroup.mem_map.mp hzMap) with ⟨k, hk, hkEq⟩
  have hk_symm : k = e.symm (e ((x * y) / (y * x))) := by
    apply e.injective
    rw [e.apply_symm_apply]
    simpa using hkEq
  rw [hk_symm] at hk
  simpa [e.symm_apply_apply] using hk

/-- `T = H0 \ Bimg`: the elements of `H0` with nontrivial `S`-component. -/
public def Tset (S : Type u) (U : Type u) [Group S] [Group U]
    [MulDistribMulAction S U] : Set (SemiProduct S U) :=
  {x | x ∈ H0sub S U ∧ (x : SemiProduct S U) ∉ Bimg S U}

/-- Membership in `Bimg`: the `S`-component is trivial. -/
public theorem mem_Bimg_iff (S : Type u) (U : Type u) [Group S] [Group U]
    [MulDistribMulAction S U] (x : SemiProduct S U) :
    x ∈ Bimg S U ↔ x.right = 1 ∧ x.left ∈ fixedSubgroup S U := by
  constructor
  · intro hx
    rcases hx with ⟨b, hb⟩
    rw [← hb]
    constructor <;> simp
  · rintro ⟨hright, hleft⟩
    refine ⟨⟨x.left, hleft⟩, ?_⟩
    apply SemidirectProduct.ext <;> simp [hright]

/-- Membership in `T`: an `H0`-element whose `S`-component is nontrivial. -/
public theorem mem_Tset_iff (S : Type u) (U : Type u) [Group S] [Group U]
    [MulDistribMulAction S U] (x : SemiProduct S U) :
    x ∈ Tset S U ↔ x.left ∈ fixedSubgroup S U ∧ x.right ≠ 1 := by
  constructor
  · intro hx
    exact ⟨(mem_H0sub_iff S U x).1 hx.1, by
      intro hright
      apply hx.2
      exact (mem_Bimg_iff S U x).2 ⟨hright, (mem_H0sub_iff S U x).1 hx.1⟩⟩
  · intro hx
    exact ⟨(mem_H0sub_iff S U x).2 hx.1, by
      intro hB
      exact hx.2 ((mem_Bimg_iff S U x).1 hB).1⟩

end SemidirectSetup

section OrderTwoSemidirect

variable {S U : Type u} [Group S] [Group U] [Fintype S] [Fintype U]
variable [MulDistribMulAction S U]

/-- The semidirect product is a finite type when both factors are. -/
public noncomputable instance instFiniteSemiProduct : Finite (SemiProduct S U) :=
  Finite.of_equiv (U × S)
    { toFun := fun p : U × S => ⟨p.1, p.2⟩
      invFun := fun x : SemiProduct S U => (x.left, x.right)
      left_inv := by intro p; rfl
      right_inv := by intro x; cases x; rfl }

/-- The image of `U` in the semidirect product `U ⋊ S`. -/
public def USub (S : Type u) (U : Type u) [Group S] [Group U]
    [MulDistribMulAction S U] : Subgroup (SemiProduct S U) where
  carrier := {x | x.right = 1}
  one_mem' := by
    simp
  mul_mem' := by
    intro x y hx hy
    change (x * y).right = 1
    rw [SemidirectProduct.mul_right, hx, hy]
    simp
  inv_mem' := by
    intro x hx
    change x⁻¹.right = 1
    rw [SemidirectProduct.inv_right, hx]
    simp

omit [Fintype S] [Fintype U] in
/-- Membership in `USub`: the `S`-component is trivial. -/
public theorem mem_USub_iff (x : SemiProduct S U) : x ∈ USub S U ↔ x.right = 1 := by
  rfl

omit [Fintype S] [Fintype U] in
/-- `USub` is normal in the semidirect product. -/
public theorem USub_normal : (USub S U).Normal := by
  constructor
  intro x hx g
  rw [mem_USub_iff] at hx ⊢
  simp [SemidirectProduct.mul_right, SemidirectProduct.inv_right, hx]

public instance instUSubNormal (S U : Type u) [Group S] [Group U] [Fintype S] [Fintype U]
    [MulDistribMulAction S U] : (USub S U).Normal :=
  USub_normal (S := S) (U := U)

/-- The group isomorphism `U ≃ USub`. -/
public noncomputable def usubEquiv (S : Type u) (U : Type u) [Group S] [Group U]
    [MulDistribMulAction S U] : U ≃* ↥(USub S U) where
  toFun u := ⟨(SemidirectProduct.inl u : SemiProduct S U),
    by
      change (SemidirectProduct.inl u : SemiProduct S U).right = 1
      simp⟩
  invFun x := x.1.left
  left_inv := by intro u; rfl
  right_inv := by
    intro y
    apply Subtype.ext
    change (SemidirectProduct.inl (y.1.left) : SemiProduct S U) = y.1
    apply SemidirectProduct.ext
    · rfl
    · exact y.2.symm
  map_mul' := by
    intro u v
    apply Subtype.ext
    exact map_mul (SemidirectProduct.inl) u v

omit [Fintype S] in
/-- In the order-two case, `USub` has index two. -/
public theorem USub_index (hS2 : Nat.card S = 2) : (USub S U).index = 2 := by
  have hmain := Subgroup.card_mul_index (USub S U)
  have hU : Nat.card ↥(USub S U) = Nat.card U := Nat.card_congr (usubEquiv S U).toEquiv.symm
  have hG : Nat.card (SemiProduct S U) = Nat.card U * Nat.card S := SemidirectProduct.card
  have hpos : 0 < Nat.card U := Nat.card_pos (α := U)
  calc
    (USub S U).index = Nat.card S :=
      Nat.eq_of_mul_eq_mul_left hpos (by
        rw [← hG]
        rw [← hU]
        exact hmain)
    _ = 2 := hS2

omit [Fintype S] [Fintype U] in
/-- `Bimg ≤ USub`: the fixed subgroup of `U` lies in `U`. -/
public theorem Bimg_le_USub : Bimg S U ≤ USub S U := by
  intro x hx
  rw [mem_USub_iff]
  exact ((mem_Bimg_iff S U x).1 hx).1

omit [Fintype S] [Fintype U] in
/-- `USub ∩ H0sub = Bimg`. -/
public theorem USub_inf_H0sub_eq_Bimg : (USub S U ⊓ H0sub S U) = Bimg S U := by
  apply Subgroup.ext
  intro x
  constructor
  · intro hx
    exact (mem_Bimg_iff S U x).2
      ⟨(mem_USub_iff x).1 (Subgroup.mem_inf.mp hx).1,
        (mem_H0sub_iff S U x).1 (Subgroup.mem_inf.mp hx).2⟩
  · intro hx
    exact Subgroup.mem_inf.mpr
      ⟨(mem_USub_iff x).2 ((mem_Bimg_iff S U x).1 hx).1,
        (mem_H0sub_iff S U x).2 ((mem_Bimg_iff S U x).1 hx).2⟩

/-- The non-identity element of a group of order two. -/
public noncomputable def s2 (hS2 : Nat.card S = 2) : S :=
  Classical.choose ((Nat.card_eq_two_iff' (1 : S)).1 hS2)

omit [Fintype S] in
/-- `s2` is not the identity. -/
public theorem s2_ne_one (hS2 : Nat.card S = 2) : s2 hS2 ≠ 1 :=
  (Classical.choose_spec ((Nat.card_eq_two_iff' (1 : S)).1 hS2)).1

omit [Fintype S] in
/-- In a group of order two, every element is `1` or `s2`. -/
public theorem s_eq_one_or_s2 (hS2 : Nat.card S = 2) (s : S) :
    s = 1 ∨ s = s2 hS2 :=
  by
  by_cases hs : s = 1
  · exact Or.inl hs
  · exact Or.inr ((Classical.choose_spec ((Nat.card_eq_two_iff' (1 : S)).1 hS2)).2 s hs)

omit [Fintype S] in
/-- `s2` is an involution. -/
public theorem s2_sq (hS2 : Nat.card S = 2) : (s2 hS2) ^ 2 = 1 :=
  sq_eq_one_of_card_two hS2 (s2 hS2)

/-- The element `(1, s2)` of the semidirect product. -/
public noncomputable def tElm (hS2 : Nat.card S = 2) : SemiProduct S U :=
  SemidirectProduct.inr (s2 hS2)

omit [Fintype S] [Fintype U] in
/-- `tElm` is not in `USub`. -/
public theorem tElm_not_mem_USub (hS2 : Nat.card S = 2) : tElm hS2 ∉ USub S U := by
  rw [mem_USub_iff]
  simp [tElm, s2_ne_one hS2]

omit [Fintype S] [Fintype U] in
/-- `tElm` lies in `H0sub`. -/
public theorem tElm_mem_H0sub (hS2 : Nat.card S = 2) : tElm hS2 ∈ H0sub S U := by
  rw [mem_H0sub_iff]
  simp [tElm]

/-- `tElm` lies in `Tset`. -/
public theorem tElm_mem_Tset (hS2 : Nat.card S = 2) : tElm hS2 ∈ Tset S U := by
  exact (mem_Tset_iff S U (tElm hS2)).2 ⟨by simp [tElm], by simp [tElm, s2_ne_one hS2]⟩

/-- Elements of `Tset` have even order. -/
public theorem Tset_even_order (hS2 : Nat.card S = 2) {x : SemiProduct S U}
    (hx : x ∈ Tset S U) : 2 ∣ orderOf x := by
  have hxr : x.right ≠ 1 := ((mem_Tset_iff S U x).1 hx).2
  have hxr2 : x.right = s2 hS2 := (s_eq_one_or_s2 hS2 x.right).resolve_left hxr
  have hproj : (SemidirectProduct.rightHom x) = s2 hS2 := by
    change x.right = s2 hS2
    exact hxr2
  have hpow : (SemidirectProduct.rightHom x) ^ (orderOf x) = 1 := by
    rw [← SemidirectProduct.rightHom.map_pow, pow_orderOf_eq_one, map_one]
  have hdvd : orderOf (SemidirectProduct.rightHom x) ∣ orderOf x :=
    orderOf_dvd_of_pow_eq_one hpow
  have hord2 : orderOf (s2 hS2) = 2 := by
    have hd : orderOf (s2 hS2) ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (by simp [s2_sq hS2])
    have hne : orderOf (s2 hS2) ≠ 1 := by
      intro h
      exact s2_ne_one hS2 (orderOf_eq_one_iff.mp h)
    exact ((Nat.dvd_prime Nat.prime_two).mp hd).resolve_left hne
  rw [hproj, hord2] at hdvd
  exact hdvd

/-- Elements of `USub` have odd order. -/
public theorem USub_odd_order (hU2' : Nat.Coprime 2 (Nat.card U)) {x : SemiProduct S U}
    (hx : x ∈ USub S U) : Odd (orderOf x) := by
  let u : U := x.left
  have hxEq : x = SemidirectProduct.inl u := by
    apply SemidirectProduct.ext <;> simp [(mem_USub_iff (S := S) (U := U) x).1 hx, u]
  rw [hxEq]
  have hord : orderOf (SemidirectProduct.inl u : SemiProduct S U) = orderOf u :=
    by
    apply le_antisymm
    · apply Nat.le_of_dvd (orderOf_pos u)
      apply orderOf_dvd_iff_pow_eq_one.mpr
      change (SemidirectProduct.inl u : SemiProduct S U) ^ orderOf u = 1
      rw [← SemidirectProduct.inl.map_pow, pow_orderOf_eq_one, map_one]
    · apply Nat.le_of_dvd (orderOf_pos (SemidirectProduct.inl u : SemiProduct S U))
      apply orderOf_dvd_iff_pow_eq_one.mpr
      have hpow : (SemidirectProduct.inl u : SemiProduct S U) ^
          orderOf (SemidirectProduct.inl u : SemiProduct S U) = 1 :=
        pow_orderOf_eq_one (SemidirectProduct.inl u : SemiProduct S U)
      have hEq : (SemidirectProduct.inl (u ^ orderOf (SemidirectProduct.inl u : SemiProduct S U)) :
            SemiProduct S U) = (SemidirectProduct.inl (1 : U) : SemiProduct S U) := by
        rw [SemidirectProduct.inl.map_pow]
        exact hpow
      exact SemidirectProduct.inl_inj.mp hEq
  have hcop : Nat.Coprime 2 (orderOf u) := by
    exact Nat.Coprime.coprime_dvd_right (orderOf_dvd_natCard u) hU2'
  rw [hord]
  rw [Nat.odd_iff]
  have hcases : orderOf u % 2 = 0 ∨ orderOf u % 2 = 1 := by omega
  rcases hcases with h0 | h1
  · exfalso
    have h2dvd : 2 ∣ orderOf u := Nat.dvd_of_mod_eq_zero h0
    have hg : (2 : ℕ).gcd (orderOf u) = 1 := hcop.gcd_eq_one
    have h2g : 2 ∣ (2 : ℕ).gcd (orderOf u) := Nat.dvd_gcd (dvd_refl 2) h2dvd
    rw [hg] at h2g
    norm_num at h2g
  · exact h1

/-- Elements of `Bimg` have odd order. -/
public theorem Bimg_odd_order (hU2' : Nat.Coprime 2 (Nat.card U)) {x : SemiProduct S U}
    (hx : x ∈ Bimg S U) : Odd (orderOf x) :=
  USub_odd_order (U := U) (S := S) hU2' (Bimg_le_USub (S := S) (U := U) hx)

/-- A triple product of `S`-fixed elements is `S`-fixed. -/
public theorem fixedSubgroup_mul_mul (S : Type u) (U : Type u) [Group S] [Group U]
    [MulDistribMulAction S U] {a b c : U} (ha : a ∈ fixedSubgroup S U)
    (hb : b ∈ fixedSubgroup S U) (hc : c ∈ fixedSubgroup S U) :
    a * b * c ∈ fixedSubgroup S U := by
  rw [mem_fixedSubgroup_iff S U]
  intro s
  have hsa : s • a = a := (mem_fixedSubgroup_iff S U a).1 ha s
  have hsb : s • b = b := (mem_fixedSubgroup_iff S U b).1 hb s
  have hsc : s • c = c := (mem_fixedSubgroup_iff S U c).1 hc s
  simp [MulDistribMulAction.smul_mul, smul_inv', hsa, hsb, hsc]

/-- Order is preserved under conjugation. -/
public theorem orderOf_conj_eq {G : Type u} [Group G] (g x : G) :
    orderOf (g * x * g⁻¹) = orderOf x := by
  simpa [MulAut.conj_apply] using
    (orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).toEquiv.injective x)

/-- The set `C(u) = u·B·(s2•u)⁻¹` of first components of conjugates of `T`. -/
public def twistedConjSet (S : Type u) (U : Type u) [Group S] [Group U]
    [MulDistribMulAction S U] (hS2 : Nat.card S = 2) (u : U) : Set U :=
  {c : U | ∃ b : ↥(fixedSubgroup S U), c = u * (b : U) * ((s2 hS2) • u)⁻¹}

omit [Fintype S] [Fintype U] in
/-- Conjugating an element of `T` by `g`: the `S`-component stays `s2` and the
`U`-component is `g.left·x.left·(s2•g.left)⁻¹`. -/
public theorem conj_Tset_left_right (hS2 : Nat.card S = 2) (g x : SemiProduct S U)
    (hx : x ∈ Tset S U) :
    (g * x * g⁻¹).right = s2 hS2 ∧
      (g * x * g⁻¹).left = g.left * (x.left : U) * ((s2 hS2) • g.left)⁻¹ := by
  have hxr : x.right = s2 hS2 :=
    (s_eq_one_or_s2 hS2 x.right).resolve_left ((mem_Tset_iff S U x).1 hx).2
  have hxl : x.left ∈ fixedSubgroup S U := ((mem_Tset_iff S U x).1 hx).1
  have hxlf : ∀ s : S, s • x.left = x.left := (mem_fixedSubgroup_iff S U x.left).1 hxl
  constructor
  · by_cases hg : g.right = 1
    · simp [SemidirectProduct.mul_right, SemidirectProduct.inv_right, hg, hxr, comm_of_card_two hS2]
    · have hg2 : g.right = s2 hS2 := (s_eq_one_or_s2 hS2 g.right).resolve_left hg
      simp [hg2, hxr]
  · by_cases hg : g.right = 1
    · simp [SemidirectProduct.mul_left, SemidirectProduct.inv_left, hg, hxr, hxlf, smul_inv', mul_assoc]
    · have hg2 : g.right = s2 hS2 := (s_eq_one_or_s2 hS2 g.right).resolve_left hg
      simp [SemidirectProduct.mul_left, SemidirectProduct.inv_left, hg2, hxr, hxlf, smul_inv', mul_assoc]

omit [Fintype U] in
/-- The image of `T` under conjugation by `g` consists exactly of the elements
with `S`-component `s2` and `U`-component in `C(g.left)`. -/
public theorem conj_Tset_image (hS2 : Nat.card S = 2) (g : SemiProduct S U) :
    (fun t : SemiProduct S U => g * t * g⁻¹) '' Tset S U =
      {y : SemiProduct S U | y.right = s2 hS2 ∧
        ∃ b : ↥(fixedSubgroup S U),
          y.left = g.left * (b : U) * ((s2 hS2) • g.left)⁻¹} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨(conj_Tset_left_right hS2 g x hx).1,
      ⟨⟨x.left, ((mem_Tset_iff S U x).1 hx).1⟩, (conj_Tset_left_right hS2 g x hx).2⟩⟩
  · rintro ⟨hyr, b, hb⟩
    let x : SemiProduct S U := ⟨(b : U), s2 hS2⟩
    have hx' : x ∈ Tset S U := by
      exact (mem_Tset_iff S U x).2 ⟨b.2, by
        intro h
        apply s2_ne_one hS2
        simpa [x] using h⟩
    have hlr := conj_Tset_left_right hS2 g x hx'
    refine ⟨x, hx', ?_⟩
    apply SemidirectProduct.ext
    · rw [hb]
      exact hlr.2
    · rw [hyr]
      exact hlr.1

/-- If `g.left` is fixed by `S`, the conjugate of `T` by `g` is `T` itself. -/
public theorem conj_Tset_eq_self_of_left_fixed (hS2 : Nat.card S = 2)
    {g : SemiProduct S U} (hg : g.left ∈ fixedSubgroup S U) :
    (fun t : SemiProduct S U => g * t * g⁻¹) '' Tset S U = Tset S U := by
  rw [conj_Tset_image hS2 g]
  ext y
  constructor
  · rintro ⟨hyr, b, hb⟩
    rw [mem_Tset_iff S U]
    constructor
    · rw [hb]
      have hgfix : (s2 hS2) • g.left = g.left :=
        (mem_fixedSubgroup_iff S U g.left).1 hg (s2 hS2)
      rw [hgfix]
      exact fixedSubgroup_mul_mul S U hg b.2 ((fixedSubgroup S U).inv_mem hg)
    · intro h
      exact s2_ne_one hS2 (by simpa [hyr] using h)
  · intro hy
    rw [mem_Tset_iff S U] at hy
    have hyr : y.right = s2 hS2 := (s_eq_one_or_s2 hS2 y.right).resolve_left hy.2
    have hb' : g.left⁻¹ * (y.left : U) * g.left ∈ fixedSubgroup S U := by
      rw [mem_fixedSubgroup_iff S U]
      intro s
      have hgs : s • g.left = g.left := (mem_fixedSubgroup_iff S U g.left).1 hg s
      have hys : s • (y.left : U) = y.left := (mem_fixedSubgroup_iff S U y.left).1 hy.1 s
      simp [MulDistribMulAction.smul_mul, smul_inv', hgs, hys]
    have hgfix : (s2 hS2) • g.left = g.left :=
      (mem_fixedSubgroup_iff S U g.left).1 hg (s2 hS2)
    refine ⟨hyr, ⟨⟨g.left⁻¹ * (y.left : U) * g.left, hb'⟩, ?_⟩⟩
    calc
      y.left = g.left * (g.left⁻¹ * (y.left : U) * g.left) * g.left⁻¹ := by group
      _ = g.left * (g.left⁻¹ * (y.left : U) * g.left) * ((s2 hS2) • g.left)⁻¹ := by
        rw [hgfix]

omit [Fintype S] in
/-- The fixed-point lemma: if `B ∩ C(u) ≠ ∅` for the twisted conjugate set
`C(u) = u·B·(s2•u)⁻¹`, then `u ∈ B`. -/
public theorem fixed_of_twisted_intersection (hS2 : Nat.card S = 2)
    (hU2' : Nat.Coprime 2 (Nat.card U)) {u : U}
    (h : ∃ b₁ b₂ : ↥(fixedSubgroup S U),
      u * (b₁ : U) * ((s2 hS2) • u)⁻¹ = b₂) :
    u ∈ fixedSubgroup S U := by
  classical
  let s0 : S := s2 hS2
  let B : Subgroup U := fixedSubgroup S U
  rcases h with ⟨b₁, b₂, hb⟩
  let w : U := u⁻¹ * (s0 • u)
  have hs0sq : s0 * s0 = 1 := by
    rw [← pow_two]
    simpa [s0] using s2_sq hS2
  have h1 : u * (b₁ : U) * ((s0 • u)⁻¹) = (b₂ : U) := hb
  have hs0u : s0 • u = u * w := by
    simp [w]
  have hsub1 : (s0 • u)⁻¹ = w⁻¹ * u⁻¹ := by
    rw [hs0u, mul_inv_rev]
  have h1' : (s0 • u) * (b₁ : U) * u⁻¹ = (b₂ : U) := by
    -- apply s0 to both sides of h1
    calc
      (s0 • u) * (b₁ : U) * u⁻¹ = s0 • (u * (b₁ : U) * ((s0 • u)⁻¹)) := by
        simp [smul_inv', smul_smul, hs0sq, (mem_fixedSubgroup_iff S U (b₁ : U)).1 b₁.2 s0]
      _ = s0 • (b₂ : U) := by rw [← h1]
      _ = (b₂ : U) := (mem_fixedSubgroup_iff S U (b₂ : U)).1 b₂.2 s0
  have hsw : s0 • w = w⁻¹ := by
    simp [w, smul_inv', smul_smul, hs0sq, mul_inv_rev]
  have h1w : u * ((b₁ : U) * w⁻¹) * u⁻¹ = u * (w * (b₁ : U)) * u⁻¹ := by
    calc
      u * ((b₁ : U) * w⁻¹) * u⁻¹ = u * (b₁ : U) * ((s0 • u)⁻¹) := by
        rw [hsub1]
        group
      _ = (b₂ : U) := h1
      _ = (s0 • u) * (b₁ : U) * u⁻¹ := h1'.symm
      _ = u * (w * (b₁ : U)) * u⁻¹ := by
        rw [hs0u]
        group
  have hstar : (b₁ : U) * w⁻¹ = w * (b₁ : U) := by
    have hc : u * ((b₁ : U) * w⁻¹) = u * (w * (b₁ : U)) := by
      exact mul_right_cancel h1w
    exact mul_left_cancel hc
  have hsw' : s0 • w⁻¹ = w := by
    simpa [hsw] using (smul_inv' s0 w).symm
  have hstar' : (b₁ : U) * w = w⁻¹ * (b₁ : U) := by
    calc
      (b₁ : U) * w = s0 • ((b₁ : U) * w⁻¹) := by
        rw [MulDistribMulAction.smul_mul]
        simp [(mem_fixedSubgroup_iff S U (b₁ : U)).1 b₁.2 s0, hsw']
      _ = s0 • (w * (b₁ : U)) := by rw [hstar]
      _ = w⁻¹ * (b₁ : U) := by
        rw [MulDistribMulAction.smul_mul]
        simp [hsw, (mem_fixedSubgroup_iff S U (b₁ : U)).1 b₁.2 s0]
  have hconj : (b₁ : U) * w * (b₁ : U)⁻¹ = w⁻¹ := by
    calc
      (b₁ : U) * w * (b₁ : U)⁻¹ = (w⁻¹ * (b₁ : U)) * (b₁ : U)⁻¹ := by rw [hstar']
      _ = w⁻¹ := by group
  let φ : MulAut U := MulAut.conj (b₁ : U)
  have hφw : φ w = w⁻¹ := by
    simpa [φ, MulAut.conj_apply] using hconj
  have hφw' : φ w⁻¹ = w := by
    rw [map_inv φ w, hφw, inv_inv]
  have hφpow (n : ℕ) :
      (φ ^ n) • w = (if Even n then w else w⁻¹) ∧
        (φ ^ n) • w⁻¹ = (if Even n then w⁻¹ else w) := by
    classical
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ]
        rw [mul_smul, mul_smul]
        rw [show φ • w = w⁻¹ by simpa [MulAut.smul_def] using hφw]
        rw [show φ • w⁻¹ = w by simpa [MulAut.smul_def] using hφw']
        by_cases hn : Even n
        · have hn' : ¬ Even (n + 1) := by
            rw [Nat.even_iff] at hn ⊢
            omega
          simp [hn, hn', ih.1, ih.2]
        · have hn' : Even (n + 1) := by
            rw [Nat.even_iff] at hn ⊢
            omega
          simp [hn, hn', ih.1, ih.2]
  have hodd : Odd (orderOf (b₁ : U)) := by
    have hcop : Nat.Coprime 2 (orderOf (b₁ : U)) := by
      exact Nat.Coprime.coprime_dvd_right (orderOf_dvd_natCard (b₁ : U)) hU2'
    rw [Nat.odd_iff]
    have hcases : orderOf (b₁ : U) % 2 = 0 ∨ orderOf (b₁ : U) % 2 = 1 := by omega
    rcases hcases with h0 | h1
    · exfalso
      have h2dvd : 2 ∣ orderOf (b₁ : U) := Nat.dvd_of_mod_eq_zero h0
      have hg : (2 : ℕ).gcd (orderOf (b₁ : U)) = 1 := hcop.gcd_eq_one
      have h2g : 2 ∣ (2 : ℕ).gcd (orderOf (b₁ : U)) := Nat.dvd_gcd (dvd_refl 2) h2dvd
      rw [hg] at h2g
      norm_num at h2g
    · exact h1
  rcases hodd with ⟨k, hk⟩
  have hnot : ¬ Even (2 * k + 1) := by
    rw [Nat.even_iff]
    omega
  have hφpoww : (φ ^ (orderOf (b₁ : U))) • w = w⁻¹ := by
    rw [hk]
    rw [(hφpow (2 * k + 1)).1, if_neg hnot]
  have hφone : φ ^ (orderOf (b₁ : U)) = 1 := by
    change (MulAut.conj (b₁ : U)) ^ (orderOf (b₁ : U)) = 1
    rw [← map_pow MulAut.conj (b₁ : U) (orderOf (b₁ : U))]
    rw [pow_orderOf_eq_one]
    ext x
    simp []
  have hw : w = w⁻¹ := by
    have hw' : (φ ^ (orderOf (b₁ : U))) • w = w := by
      rw [hφone]
      simp
    rw [hφpoww] at hw'
    exact hw'.symm
  have hw2 : w ^ 2 = 1 := by
    rw [pow_two]
    conv_lhs => arg 2; rw [hw]
    group
  have hw1 : w = 1 := sq_eq_one_of_coprime_two hU2' hw2
  have hs0u1 : s0 • u = u := by
    have hwdef : u⁻¹ * (s0 • u) = 1 := by simpa [w] using hw1
    calc
      s0 • u = u * (u⁻¹ * (s0 • u)) := by group
      _ = u * 1 := by rw [hwdef]
      _ = u := by simp
  rw [mem_fixedSubgroup_iff S U]
  intro s
  by_cases hs : s = 1
  · subst s
    simp
  · have hss : s = s0 := (s_eq_one_or_s2 hS2 s).resolve_left hs
    rw [hss]
    exact hs0u1

/-- `Tset` is a TI-set when `|S| = 2` and `|U|` is odd. -/
public theorem Tset_TI (hS2 : Nat.card S = 2) (hU2' : Nat.Coprime 2 (Nat.card U)) :
    IsTISet (Tset S U) := by
  unfold IsTISet
  intro g
  by_cases hEq : (fun t : SemiProduct S U => g * t * g⁻¹) '' Tset S U = Tset S U
  · exact Or.inl hEq
  · right
    ext y
    constructor
    · intro hy
      rcases hy with ⟨hyT, hyImg⟩
      rcases hyImg with ⟨x, hxT, hxy⟩
      have hleft : g.left ∈ fixedSubgroup S U := by
        exact fixed_of_twisted_intersection hS2 hU2'
          ⟨⟨x.left, ((mem_Tset_iff S U x).1 hxT).1⟩,
           ⟨y.left, ((mem_Tset_iff S U y).1 hyT).1⟩, by
            change g.left * (x.left : U) * ((s2 hS2) • g.left)⁻¹ = (y.left : U)
            have hyEq : (g * x * g⁻¹).left = y.left :=
              congrArg (fun z : SemiProduct S U => z.left) hxy
            rw [← hyEq]
            exact (conj_Tset_left_right hS2 g x hxT).2.symm⟩
      exfalso
      exact hEq (conj_Tset_eq_self_of_left_fixed hS2 hleft)
    · intro hy
      simp at hy

/-- The normalizer of `Tset` is exactly `H0sub`. -/
public theorem Tset_normalizer (hS2 : Nat.card S = 2)
    (hU2' : Nat.Coprime 2 (Nat.card U)) :
    Subgroup.normalizer (Tset S U) = H0sub S U := by
  apply le_antisymm
  · intro g hg
    rw [Subgroup.mem_set_normalizer_iff] at hg
    have hgt : g * tElm hS2 * g⁻¹ ∈ Tset S U :=
      (hg (tElm hS2)).1 (tElm_mem_Tset hS2)
    have hleft : g.left ∈ fixedSubgroup S U := by
      have hlr := (conj_Tset_left_right hS2 g (tElm hS2) (tElm_mem_Tset hS2)).2
      exact fixed_of_twisted_intersection hS2 hU2'
        ⟨⟨(1 : U), (fixedSubgroup S U).one_mem'⟩, ⟨(g * tElm hS2 * g⁻¹).left,
          ((mem_Tset_iff S U (g * tElm hS2 * g⁻¹)).1 hgt).1⟩, by
            have hlr2' : (g * tElm hS2 * g⁻¹).left =
                g.left * (1 : U) * ((s2 hS2) • g.left)⁻¹ := by
              simpa [tElm] using hlr
            exact hlr2'.symm⟩
    rw [mem_H0sub_iff]
    exact hleft
  · intro g hg
    rw [Subgroup.mem_set_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hgl : g.left ∈ fixedSubgroup S U := (mem_H0sub_iff S U g).1 hg
      have hxr : x.right = s2 hS2 :=
        (s_eq_one_or_s2 hS2 x.right).resolve_left ((mem_Tset_iff S U x).1 hx).2
      have hxlf : x.left ∈ fixedSubgroup S U := ((mem_Tset_iff S U x).1 hx).1
      have hgfix : (s2 hS2) • g.left = g.left :=
        (mem_fixedSubgroup_iff S U g.left).1 hgl (s2 hS2)
      have hlr := conj_Tset_left_right hS2 g x hx
      rw [mem_Tset_iff S U]
      constructor
      · rw [hlr.2]
        rw [hgfix]
        exact fixedSubgroup_mul_mul S U hgl hxlf ((fixedSubgroup S U).inv_mem hgl)
      · intro h
        exact s2_ne_one hS2 (by simpa [hlr.1] using h)
    · intro hx
      -- x = g⁻¹·(g·x·g⁻¹)·g and g⁻¹ ∈ H0sub
      have hginv : g⁻¹ ∈ H0sub S U := (H0sub S U).inv_mem hg
      have hgl : g⁻¹.left ∈ fixedSubgroup S U := (mem_H0sub_iff S U g⁻¹).1 hginv
      have hxr : (g * x * g⁻¹).right = s2 hS2 :=
        (s_eq_one_or_s2 hS2 (g * x * g⁻¹).right).resolve_left
          ((mem_Tset_iff S U (g * x * g⁻¹)).1 hx).2
      have hxlf : (g * x * g⁻¹).left ∈ fixedSubgroup S U :=
        ((mem_Tset_iff S U (g * x * g⁻¹)).1 hx).1
      have hgfix : (s2 hS2) • g⁻¹.left = g⁻¹.left :=
        (mem_fixedSubgroup_iff S U g⁻¹.left).1 hgl (s2 hS2)
      have hlr := conj_Tset_left_right hS2 g⁻¹ (g * x * g⁻¹) hx
      -- x = g⁻¹·(g·x·g⁻¹)·g: use group identity
      rw [mem_Tset_iff S U]
      constructor
      · -- x.left ∈ B: x = g⁻¹·y·g, y = g·x·g⁻¹; y.left = g⁻¹.left·x.left·(s2•g⁻¹.left)⁻¹
        -- from hlr: x.left = g⁻¹.left·y.left·(s2•g⁻¹.left)⁻¹
        have hyEq' : (x.left : U) =
            g⁻¹.left * ((g * x * g⁻¹).left : U) * ((s2 hS2) • g⁻¹.left)⁻¹ := by
          have hxEq : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
          have hlr2 : (g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹).left =
              g⁻¹.left * ((g * x * g⁻¹).left : U) * ((s2 hS2) • g⁻¹.left)⁻¹ := hlr.2
          rw [hxEq] at hlr2
          exact hlr2
        have hxmem : (x.left : U) ∈ fixedSubgroup S U := by
          rw [hyEq']
          rw [hgfix]
          exact fixedSubgroup_mul_mul S U hgl hxlf ((fixedSubgroup S U).inv_mem hgl)
        exact hxmem
      · -- x.right ≠ 1
        intro h
        have hxr' : x.right = 1 := h
        -- x.right = g⁻¹.right·y.right·g⁻¹.right⁻¹ = s2 (since y.right = s2, S abelian)
        have hyr : (g * x * g⁻¹).right = s2 hS2 :=
          (s_eq_one_or_s2 hS2 (g * x * g⁻¹).right).resolve_left
            ((mem_Tset_iff S U (g * x * g⁻¹)).1 hx).2
        have hxrEq : x.right = s2 hS2 := by
          -- x = g⁻¹·y·g: right components: g⁻¹.right·y.right·g.right
          have hxEq : x = g⁻¹ * (g * x * g⁻¹) * g := by group
          rw [hxEq]
          by_cases hg1 : g.right = 1
          · simp [SemidirectProduct.mul_right, SemidirectProduct.inv_right, hyr, hg1]
          · have hg2 : g.right = s2 hS2 := (s_eq_one_or_s2 hS2 g.right).resolve_left hg1
            simp [SemidirectProduct.mul_right, SemidirectProduct.inv_right, hyr,
              hg2, comm_of_card_two hS2]
        exact s2_ne_one hS2 ((hxr' ▸ hxrEq).symm)

end OrderTwoSemidirect

section OrderTwoCorrespondence

variable {S U : Type u} [Group S] [Group U] [Fintype S] [Fintype U]
variable [MulDistribMulAction S U]

/-- The semidirect product of two finite groups is finite. -/
public noncomputable instance instFintypeSemiProduct : Fintype (SemiProduct S U) :=
  by
    classical
    have : Finite (SemiProduct S U) := inferInstance
    exact Fintype.ofFinite (SemiProduct S U)

example : Fintype (SemiProduct S U) := inferInstance

/-- The constant-one class function is the trivial irreducible character. -/
public theorem isIrreducibleCharacter_one (G : Type u) [Group G] [Fintype G] :
    IsIrreducibleCharacter (1 : ClassFunction G) := by
  classical
  refine isIrreducibleCharacter_of_norm_one_inv ?_ ?_
  · refine ⟨1, Representation.trivial ℂ G (Fin 1 → ℂ), ?_⟩
    ext g
    simp [Representation.trivial, Representation.character]
  · unfold scalarProductInv
    have hsum : (∑ g : G, (1 : ClassFunction G) g * (1 : ClassFunction G) g⁻¹) =
        (Nat.card G : ℂ) := by
      simp [Finset.sum_const, Nat.card_eq_fintype_card]
    rw [hsum]
    have hne : (Nat.card G : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.card_pos (α := G)).ne'
    field_simp [hne]

/-- The trivial irreducible character of a finite group. -/
public noncomputable def oneIrr (G : Type u) [Group G] [Fintype G] : IrrBG19 G :=
  ⟨(1 : ClassFunction G), isIrreducibleCharacter_one G⟩

/-- The nontrivial homomorphism from a group of order two to `ℂˣ`. -/
public noncomputable def sigHom (hS2 : Nat.card S = 2) : S →* ℂˣ where
  toFun s := if s = 1 then 1 else -1
  map_one' := by simp
  map_mul' := by
    intro a b
    by_cases ha : a = 1 <;> by_cases hb : b = 1
    · simp [ha, hb]
    · simp [ha, hb]
    · simp [ha, hb]
    · have has : a = s2 hS2 := (s_eq_one_or_s2 hS2 a).resolve_left ha
      have hbs : b = s2 hS2 := (s_eq_one_or_s2 hS2 b).resolve_left hb
      rw [has, hbs]
      rw [← pow_two, s2_sq hS2]
      simp [s2_ne_one hS2]

/-- The nontrivial linear character of a group of order two. -/
public noncomputable def sigChar (hS2 : Nat.card S = 2) : ClassFunction S :=
  fun s => ((sigHom hS2 s : ℂˣ) : ℂ)

/-- `sigChar` is a linear character. -/
public theorem sigChar_isLinear (hS2 : Nat.card S = 2) :
    IsLinearCharacter (sigChar hS2) :=
  isLinearCharacter_of_hom (sigHom hS2)

omit [Fintype S] in
/-- `sigChar` takes value `1` at the identity. -/
public theorem sigChar_apply_one (hS2 : Nat.card S = 2) : sigChar hS2 1 = 1 := by
  simp [sigChar, sigHom]

omit [Fintype S] in
/-- `sigChar` takes value `-1` at the nonidentity element. -/
public theorem sigChar_apply_s2 (hS2 : Nat.card S = 2) : sigChar hS2 (s2 hS2) = -1 := by
  simp [sigChar, sigHom, s2_ne_one hS2]

/-- `sigChar` is not the trivial character. -/
public theorem sigChar_ne_one (hS2 : Nat.card S = 2) : sigChar hS2 ≠ (1 : ClassFunction S) := by
  intro h
  have hz := congrFun h (s2 hS2)
  rw [sigChar_apply_s2 hS2, Pi.one_apply] at hz
  norm_num at hz

/-- The nontrivial irreducible character of a group of order two. -/
public noncomputable def sigIrr (hS2 : Nat.card S = 2) : IrrBG19 S :=
  ⟨sigChar hS2, (sigChar_isLinear hS2).1⟩

/-- The trivial and nontrivial characters of a group of order two differ. -/
public theorem oneIrr_ne_sigIrr (hS2 : Nat.card S = 2) : oneIrr S ≠ sigIrr hS2 := by
  intro h
  have hz := congrArg (fun α : IrrBG19 S => α.1 (s2 hS2)) h
  have hz' : (1 : ClassFunction S) (s2 hS2) = sigChar hS2 (s2 hS2) := by
    simpa [oneIrr, sigIrr] using hz
  rw [sigChar_apply_s2 hS2, Pi.one_apply] at hz'
  exact (by norm_num : (1 : ℂ) ≠ -1) hz'

omit [Fintype S] in
/-- A group of order two has exactly two conjugacy classes. -/
public theorem conjClassesS_card (hS2 : Nat.card S = 2) :
    Nat.card (ConjClasses S) = 2 := by
  classical
  rw [(Nat.card_eq_two_iff' (ConjClasses.mk (1 : S))).2]
  refine ⟨ConjClasses.mk (s2 hS2), ?_, ?_⟩
  · intro hEq
    have hc := ConjClasses.mk_eq_mk_iff_isConj.mp hEq
    rw [isConj_iff] at hc
    rcases hc with ⟨a, ha⟩
    exact s2_ne_one hS2 (by simpa using ha)
  · intro c hc
    rcases ConjClasses.exists_rep c with ⟨x, rfl⟩
    have hx : x ≠ 1 := by
      intro hx
      apply hc
      rw [hx]
    have hx2 : x = s2 hS2 := (s_eq_one_or_s2 hS2 x).resolve_left hx
    rw [hx2]

/-- The group of order two has exactly two irreducible characters. -/
public theorem irrS_card (hS2 : Nat.card S = 2) : Fintype.card (IrrBG19 S) = 2 := by
  rw [fintype_card_irr_eq_conjClassesBG19, Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
  exact conjClassesS_card hS2

/-- Every irreducible character of a group of order two is trivial or `sigChar`. -/
public theorem irrS_eq_one_or_sig (hS2 : Nat.card S = 2) (σ : IrrBG19 S) :
    σ = oneIrr S ∨ σ = sigIrr hS2 := by
  classical
  let f : Bool → IrrBG19 S := fun b => if b then oneIrr S else sigIrr hS2
  have hinj : Function.Injective f := by
    intro b b' h
    cases b <;> cases b' <;> simp [f] at h ⊢
    · exact (oneIrr_ne_sigIrr hS2 h.symm).elim
    · exact (oneIrr_ne_sigIrr hS2 h).elim
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).2 ⟨hinj, by simp [irrS_card hS2]⟩
  rcases hbij.2 σ with ⟨b, hb⟩
  cases b
  · simp [f] at hb
    exact Or.inr hb.symm
  · simp [f] at hb
    exact Or.inl hb.symm

/-- A class function on `H0 = S × B` built from a class function `σ` of `S` and
`β` of `B`. -/
public def h0Char (S : Type u) (U : Type u) [Group S] [Group U]
    [MulDistribMulAction S U] (σ : ClassFunction S)
    (β : ClassFunction (↥(fixedSubgroup S U))) : ClassFunction (↥(H0sub S U)) :=
  fun x => β ⟨x.1.left, (mem_H0sub_iff S U x.1).1 x.2⟩ * σ x.1.right

/-- The explicit value of `h0Char`: `σ` of the `S`-component times `β` of the
`B`-component. -/
public theorem h0Char_apply (S : Type u) (U : Type u) [Group S] [Group U]
    [MulDistribMulAction S U] (σ : ClassFunction S)
    (β : ClassFunction (↥(fixedSubgroup S U))) (x : ↥(H0sub S U)) :
    h0Char S U σ β x = β ⟨x.1.left, (mem_H0sub_iff S U x.1).1 x.2⟩ * σ x.1.right := by
  rfl

/-- The value of `H0equiv` on an element of `H0sub`. -/
public theorem h0equiv_apply (S : Type u) (U : Type u) [Group S] [Group U]
    [MulDistribMulAction S U] (x : ↥(H0sub S U)) :
    H0equiv S U x = (⟨x.1.left, (mem_H0sub_iff S U x.1).1 x.2⟩, x.1.right) := by
  rfl

/-- `h0Char` is the pullback of the product character along `H0equiv`. -/
public theorem h0Char_eq_prodChar (S : Type u) (U : Type u) [Group S] [Group U]
    [MulDistribMulAction S U] (σ : ClassFunction S)
    (β : ClassFunction (↥(fixedSubgroup S U))) :
    h0Char S U σ β = fun x : ↥(H0sub S U) => prodCharBG19 β σ (H0equiv S U x) := by
  funext x
  rw [h0Char_apply, h0equiv_apply]
  simp [prodCharBG19]

/-- `h0Char` of an irreducible pair is irreducible. -/
public theorem h0Char_isIrreducible (S : Type u) (U : Type u) [Group S] [Group U]
    [Fintype S] [Fintype U] [MulDistribMulAction S U] (σ : IrrBG19 S)
    (β : IrrBG19 (↥(fixedSubgroup S U))) :
    IsIrreducibleCharacter (h0Char S U σ.1 β.1) := by
  rw [h0Char_eq_prodChar]
  exact isIrreducibleCharacter_congr (H0equiv S U)
    (prodChar_isIrreducibleBG19 (G := ↥(fixedSubgroup S U)) (H := S) β.1 σ.1 β.2 σ.2)

/-- The irreducible characters of `H0 = S × B` are exactly the products of the
irreducible characters of `S` and `B`. -/
public noncomputable def h0IrrEquiv (S : Type u) (U : Type u) [Group S] [Group U]
    [Fintype S] [Fintype U] [MulDistribMulAction S U] :
    IrrBG19 S × IrrBG19 (↥(fixedSubgroup S U)) ≃ IrrBG19 (↥(H0sub S U)) := by
  classical
  let e1 : IrrBG19 (↥(fixedSubgroup S U)) × IrrBG19 S ≃ IrrBG19 (↥(fixedSubgroup S U) × S) :=
    Equiv.ofBijective (prodIrrBG19 (G := ↥(fixedSubgroup S U)) (H := S))
      ⟨prodIrr_injectiveBG19 (G := ↥(fixedSubgroup S U)) (H := S),
        prodIrr_surjectiveBG19 (G := ↥(fixedSubgroup S U)) (H := S)⟩
  let e2 : IrrBG19 (↥(fixedSubgroup S U) × S) ≃ IrrBG19 (↥(H0sub S U)) :=
    irrCongr (H0equiv S U)
  let eSwap : IrrBG19 S × IrrBG19 (↥(fixedSubgroup S U)) ≃
      IrrBG19 (↥(fixedSubgroup S U)) × IrrBG19 S :=
    Equiv.prodComm _ _
  exact eSwap.trans (e1.trans e2)

set_option backward.isDefEq.respectTransparency false in
/-- The value of `h0IrrEquiv` on a pair is `h0Char`. -/
public theorem h0IrrEquiv_apply (S : Type u) (U : Type u) [Group S] [Group U]
    [Fintype S] [Fintype U] [MulDistribMulAction S U] (σ : IrrBG19 S)
    (β : IrrBG19 (↥(fixedSubgroup S U))) :
    h0IrrEquiv S U (σ, β) = ⟨h0Char S U σ.1 β.1, h0Char_isIrreducible S U σ β⟩ := by
  classical
  apply Subtype.ext
  funext x
  simp [h0IrrEquiv, irrCongr, prodIrrBG19, Equiv.prodComm]
  rw [h0Char_eq_prodChar]

/-- The element `(b, s2)` of `H0 = S × B`. -/
public noncomputable def tB (hS2 : Nat.card S = 2) (b : ↥(fixedSubgroup S U)) :
    ↥(H0sub S U) :=
  ⟨h0Hom S U (b, s2 hS2), (mem_H0sub_iff S U (h0Hom S U (b, s2 hS2))).2 (by
    rw [h0Hom_apply]
    exact b.2)⟩

omit [Fintype S] [Fintype U] in
/-- The underlying semidirect-product element of `tB b` is `(b, s2)`. -/
public theorem tB_apply (hS2 : Nat.card S = 2) (b : ↥(fixedSubgroup S U)) :
    (tB hS2 b : SemiProduct S U) = ⟨(b : U), s2 hS2⟩ := by
  unfold tB
  change (h0Hom S U (b, s2 hS2) : SemiProduct S U) = ⟨(b : U), s2 hS2⟩
  rw [h0Hom_apply]

omit [Fintype S] [Fintype U] in
/-- `tB b` lies in `Tset`. -/
public theorem tB_mem_Tset (hS2 : Nat.card S = 2) (b : ↥(fixedSubgroup S U)) :
    (tB hS2 b : SemiProduct S U) ∈ Tset S U := by
  rw [mem_Tset_iff, tB_apply]
  exact ⟨b.2, s2_ne_one hS2⟩

/-- The difference `ν_β - ν'_β` where `ν'_β` is twisted by the nontrivial
character of `S`. -/
public def delta (S : Type u) (U : Type u) [Group S] [Group U]
    [Fintype S] [Fintype U] [MulDistribMulAction S U] (hS2 : Nat.card S = 2)
    (β : ClassFunction (↥(fixedSubgroup S U))) : ClassFunction (↥(H0sub S U)) :=
  h0Char S U (oneIrr S).1 β - h0Char S U (sigIrr hS2).1 β

/-- `delta β` is supported on `Tset`. -/
public theorem delta_supportedOn_Tset (hS2 : Nat.card S = 2)
    (β : ClassFunction (↥(fixedSubgroup S U))) :
    supportedOn (delta S U hS2 β) {x : ↥(H0sub S U) | (x : SemiProduct S U) ∈ Tset S U} := by
  intro x hxT
  have hxB : (x : SemiProduct S U) ∈ Bimg S U := by
    by_contra hnot
    exact hxT ⟨x.2, hnot⟩
  have hxr : x.1.right = 1 := ((mem_Bimg_iff S U (x : SemiProduct S U)).1 hxB).1
  unfold delta
  change h0Char S U (1 : ClassFunction S) β x -
      h0Char S U (sigChar hS2) β x = 0
  simp [h0Char_apply]
  rw [hxr]
  simp [sigChar_apply_one]

/-- The value of `delta β` at `tB b` is `2 β b`. -/
public theorem delta_apply_Tset (hS2 : Nat.card S = 2)
    (β : IrrBG19 (↥(fixedSubgroup S U))) (b : ↥(fixedSubgroup S U)) :
    delta S U hS2 β.1 (tB hS2 b) = 2 * β.1 b := by
  unfold delta
  change h0Char S U (1 : ClassFunction S) β.1 (tB hS2 b) -
      h0Char S U (sigChar hS2) β.1 (tB hS2 b) = 2 * β.1 b
  simp [h0Char_apply, tB_apply]
  rw [sigChar_apply_s2]
  ring

/-- `delta β` is a class function. -/
public theorem h0Char_isClassFunction (S : Type u) (U : Type u) [Group S] [Group U]
    [MulDistribMulAction S U] (σ : ClassFunction S) (hσ : IsClassFunction σ)
    (β : ClassFunction (↥(fixedSubgroup S U))) (hβ : IsClassFunction β) :
    IsClassFunction (h0Char S U σ β) := by
  rw [h0Char_eq_prodChar]
  intro x g
  change prodCharBG19 β σ (H0equiv S U (g * x * g⁻¹)) = prodCharBG19 β σ (H0equiv S U x)
  have hconj : H0equiv S U (g * x * g⁻¹) =
      H0equiv S U g * H0equiv S U x * (H0equiv S U g)⁻¹ := by
    rw [map_mul, map_mul, map_inv]
  rw [hconj]
  simp [prodCharBG19]
  have hβ' : β ((H0equiv S U g).1 * (H0equiv S U x).1 * (H0equiv S U g).1⁻¹) =
      β (H0equiv S U x).1 := by
    exact hβ (H0equiv S U x).1 (H0equiv S U g).1
  have hσ' : σ ((H0equiv S U g).2 * (H0equiv S U x).2 * (H0equiv S U g).2⁻¹) =
      σ (H0equiv S U x).2 := by
    exact hσ (H0equiv S U x).2 (H0equiv S U g).2
  rw [hβ', hσ']

/-- `delta β` is a class function. -/
public theorem delta_isClassFunction (hS2 : Nat.card S = 2)
    (β : ClassFunction (↥(fixedSubgroup S U))) (hβ : IsClassFunction β) :
    IsClassFunction (delta S U hS2 β) := by
  intro x g
  unfold delta
  have h1 : h0Char S U (1 : ClassFunction S) β (g * x * g⁻¹) =
      h0Char S U (1 : ClassFunction S) β x := by
    exact h0Char_isClassFunction (S := S) (U := U) (1 : ClassFunction S)
      (by intro a b; simp) β hβ x g
  have h2 : h0Char S U (sigChar hS2) β (g * x * g⁻¹) =
      h0Char S U (sigChar hS2) β x := by
    exact h0Char_isClassFunction (S := S) (U := U) (sigChar hS2)
      (irreducibleCharacter_isClassFunction (sigChar_isLinear hS2).1) β hβ x g
  change h0Char S U (1 : ClassFunction S) β (g * x * g⁻¹) -
      h0Char S U (sigChar hS2) β (g * x * g⁻¹) =
    h0Char S U (1 : ClassFunction S) β x - h0Char S U (sigChar hS2) β x
  rw [h1, h2]

/-- `delta β` is a generalized character. -/
public theorem delta_isGeneralizedCharacter (hS2 : Nat.card S = 2)
    (β : IrrBG19 (↥(fixedSubgroup S U))) :
    IsGeneralizedCharacter (delta S U hS2 β.1) := by
  refine ⟨h0Char S U (oneIrr S).1 β.1, h0Char S U (sigIrr hS2).1 β.1, ?_, ?_, ?_⟩
  · exact isCharacter_of_isIrreducibleCharacter (h0Char_isIrreducible S U (oneIrr S) β)
  · exact isCharacter_of_isIrreducibleCharacter (h0Char_isIrreducible S U (sigIrr hS2) β)
  · simp [delta]

/-- The induced `delta β` on the whole semidirect product. -/
public def deltaStar (S : Type u) (U : Type u) [Group S] [Group U]
    [Fintype S] [Fintype U] [MulDistribMulAction S U] (hS2 : Nat.card S = 2)
    (β : IrrBG19 (↥(fixedSubgroup S U))) : ClassFunction (SemiProduct S U) :=
  inducedClassFunction (H0sub S U) (delta S U hS2 β.1)

/-- The scalar product is linear in the first argument. -/
public theorem scalarProduct_sub_left {G : Type u} [Group G] [Fintype G]
    (φ₁ φ₂ ψ : ClassFunction G) :
    scalarProduct G (φ₁ - φ₂) ψ = scalarProduct G φ₁ ψ - scalarProduct G φ₂ ψ := by
  rw [sub_eq_add_neg, scalarProduct_add_left, scalarProduct_neg_left]
  ring

public theorem induced_Tset_eq_self (hS2 : Nat.card S = 2)
    (hU2' : Nat.Coprime 2 (Nat.card U)) {δ : ClassFunction (↥(H0sub S U))}
    (hδ : IsClassFunction δ)
    (hδT : supportedOn δ {x : ↥(H0sub S U) | (x : SemiProduct S U) ∈ Tset S U})
    {g : SemiProduct S U} (hg : g ∈ Tset S U) :
    inducedClassFunction (H0sub S U) δ g =
      δ ⟨g, (mem_H0sub_iff S U g).2 ((mem_Tset_iff S U g).1 hg).1⟩ := by
  classical
  let hgH : g ∈ H0sub S U := (mem_H0sub_iff S U g).2 ((mem_Tset_iff S U g).1 hg).1
  unfold inducedClassFunction
  have hsum : (∑ x : SemiProduct S U, inducedSummand δ g x) =
      (Nat.card (↥(H0sub S U)) : ℂ) * δ ⟨g, hgH⟩ := by
    calc
      (∑ x : SemiProduct S U, inducedSummand δ g x)
          = ∑ x : SemiProduct S U, (if (x : SemiProduct S U) ∈ H0sub S U
              then δ ⟨g, hgH⟩ else 0) := by
              refine Finset.sum_congr rfl ?_
              intro x hx
              by_cases hxH : x ∈ H0sub S U
              · have hmem : x⁻¹ * g * x ∈ H0sub S U := by
                  exact (H0sub S U).mul_mem ((H0sub S U).mul_mem
                    ((H0sub S U).inv_mem hxH) hgH) hxH
                have hsummand : inducedSummand δ g x = δ ⟨g, hgH⟩ := by
                  unfold inducedSummand
                  rw [dif_pos hmem]
                  have hc := hδ ⟨g, hgH⟩ ⟨x⁻¹, (H0sub S U).inv_mem hxH⟩
                  have harg : (⟨x⁻¹, (H0sub S U).inv_mem hxH⟩ * ⟨g, hgH⟩ *
                      ⟨x⁻¹, (H0sub S U).inv_mem hxH⟩⁻¹ : ↥(H0sub S U)) =
                      ⟨x⁻¹ * g * x, hmem⟩ := by
                    apply Subtype.ext
                    simp
                  rw [← harg]
                  exact hc
                simp [hxH]
                exact hsummand
              · -- x ∉ H0: both sides vanish (TI-set argument)
                have hz : inducedSummand δ g x = 0 :=
                  inducedSummand_zero_of_not_normalizer (Tset_TI hS2 hU2')
                    (Tset_normalizer hS2 hU2') δ hδT hg hxH
                simp [hxH, hz]
      _ = (Nat.card (↥(H0sub S U)) : ℂ) * δ ⟨g, hgH⟩ := by
              -- factor the constant out and count the elements of H0
              have hfactor : (∑ x : SemiProduct S U,
                  (if x ∈ H0sub S U then δ ⟨g, hgH⟩ else 0)) =
                  (∑ x : SemiProduct S U,
                    (if x ∈ H0sub S U then (1 : ℂ) else 0)) * δ ⟨g, hgH⟩ := by
                rw [Finset.sum_mul]
                refine Finset.sum_congr rfl ?_
                intro x hx
                by_cases hxH : x ∈ H0sub S U <;> simp [hxH]
              rw [hfactor, Finset.sum_boole]
              -- the number of elements of H0 equals Nat.card ↥H0
              have hcard : Nat.card (↥(H0sub S U)) =
                  (Finset.univ.filter (fun x : SemiProduct S U => x ∈ H0sub S U)).card := by
                rw [Nat.card_eq_fintype_card]
                rw [← Finset.card_univ]
                -- the filter over univ is in bijection with the subtype
                refine Finset.card_bij (s := Finset.univ)
                  (t := Finset.univ.filter (fun x : SemiProduct S U => x ∈ H0sub S U))
                  (fun x : ↥(H0sub S U) => fun _ => (x : SemiProduct S U)) ?_ ?_ ?_
                · intro x hx
                  exact Finset.mem_filter.mpr ⟨Finset.mem_univ (x : SemiProduct S U), x.2⟩
                · intro a ha b hb hEq
                  apply Subtype.ext
                  exact hEq
                · intro x hx
                  rw [Finset.mem_filter] at hx
                  refine ⟨⟨x, hx.2⟩, ?_, ?_⟩
                  · simp
                  · rfl
              rw [hcard]
  calc
    (Nat.card (↥(H0sub S U)) : ℂ)⁻¹ *
        (∑ x : SemiProduct S U, inducedSummand δ g x)
        = (Nat.card (↥(H0sub S U)) : ℂ)⁻¹ *
            ((Nat.card (↥(H0sub S U)) : ℂ) * δ ⟨g, hgH⟩) := by
            rw [hsum]
    _ = δ ⟨g, hgH⟩ := by
            have hne : (Nat.card (↥(H0sub S U)) : ℂ) ≠ 0 := by
              exact_mod_cast (Nat.card_pos (α := ↥(H0sub S U))).ne'
            field_simp [hne]

/-- The scalar product on `H0` is the double sum over `H0` itself. -/
public theorem scalarProduct_doubleSum_self {G : Type u} [Group G] [Fintype G]
    (H0 : Subgroup G) {δ1 δ2 : ClassFunction (↥H0)} (hδ2 : IsClassFunction δ2) :
    scalarProduct (↥H0) δ1 δ2 =
      ((Nat.card (↥H0) : ℂ)⁻¹ * (Nat.card (↥H0) : ℂ)⁻¹) *
        ∑ z : ↥H0, ∑ h : ↥H0, pairingSummand H0 δ1 δ2 (z : G) h := by
  classical
  have hdbl : (∑ z : ↥H0, ∑ h : ↥H0, pairingSummand H0 δ1 δ2 (z : G) h) =
      (Nat.card (↥H0) : ℂ) * (∑ h : ↥H0, δ1 h * star (δ2 h)) := by
    calc
      (∑ z : ↥H0, ∑ h : ↥H0, pairingSummand H0 δ1 δ2 (z : G) h)
          = ∑ z : ↥H0, ∑ h : ↥H0, δ1 h * star (δ2 h) := by
              refine Finset.sum_congr rfl ?_
              intro z hz
              refine Finset.sum_congr rfl ?_
              intro h hh
              have hmem : (z : G)⁻¹ * (h : G) * (z : G) ∈ H0 := by
                exact H0.mul_mem (H0.mul_mem (Subgroup.inv_mem (H := H0) z.2) h.2) z.2
              unfold pairingSummand
              rw [dif_pos hmem]
              have hc := hδ2 h ⟨z⁻¹, Subgroup.inv_mem (H := H0) z.2⟩
              have harg : (⟨(z : G)⁻¹, Subgroup.inv_mem (H := H0) z.2⟩ * h *
                  ⟨(z : G)⁻¹, Subgroup.inv_mem (H := H0) z.2⟩⁻¹ : ↥H0) =
                  ⟨(z : G)⁻¹ * (h : G) * (z : G), hmem⟩ := by
                apply Subtype.ext
                simp
              rw [← harg, hc]
      _ = (Nat.card (↥H0) : ℂ) * (∑ h : ↥H0, δ1 h * star (δ2 h)) := by
              simp [Finset.sum_const, Nat.card_eq_fintype_card]
  calc
    scalarProduct (↥H0) δ1 δ2
        = (Nat.card (↥H0) : ℂ)⁻¹ * (∑ h : ↥H0, δ1 h * star (δ2 h)) := rfl
    _ = ((Nat.card (↥H0) : ℂ)⁻¹ * (Nat.card (↥H0) : ℂ)⁻¹) *
          ((Nat.card (↥H0) : ℂ) * (∑ h : ↥H0, δ1 h * star (δ2 h))) := by
          have hne : (Nat.card (↥H0) : ℂ) ≠ 0 := by
            exact_mod_cast (Nat.card_pos (α := ↥H0)).ne'
          field_simp [hne]
    _ = ((Nat.card (↥H0) : ℂ)⁻¹ * (Nat.card (↥H0) : ℂ)⁻¹) *
          (∑ z : ↥H0, ∑ h : ↥H0, pairingSummand H0 δ1 δ2 (z : G) h) := by
          rw [hdbl]

/-- The scalar product of two `h0Char`'s is `1` exactly when both factors agree. -/
public theorem h0Char_scalar (hS2 : Nat.card S = 2) (σ σ' : IrrBG19 S)
    (β β' : IrrBG19 (↥(fixedSubgroup S U))) :
    scalarProduct (↥(H0sub S U)) (h0Char S U σ.1 β.1) (h0Char S U σ'.1 β'.1) =
      if σ = σ' ∧ β = β' then 1 else 0 := by
  classical
  have hiff : (h0Char S U σ.1 β.1 = h0Char S U σ'.1 β'.1) ↔ (σ = σ' ∧ β = β') := by
    constructor
    · intro h
      have hEq : h0IrrEquiv S U (σ, β) = h0IrrEquiv S U (σ', β') := by
        rw [h0IrrEquiv_apply, h0IrrEquiv_apply]
        apply Subtype.ext
        exact h
      have hpair := (h0IrrEquiv S U).injective hEq
      exact ⟨congrArg Prod.fst hpair, congrArg Prod.snd hpair⟩
    · rintro ⟨rfl, rfl⟩
      rfl
  calc
    scalarProduct (↥(H0sub S U)) (h0Char S U σ.1 β.1) (h0Char S U σ'.1 β'.1)
        = if h0Char S U σ.1 β.1 = h0Char S U σ'.1 β'.1 then 1 else 0 :=
          scalarProduct_irr_ite (h0Char_isIrreducible S U σ β) (h0Char_isIrreducible S U σ' β')
    _ = if σ = σ' ∧ β = β' then 1 else 0 := by
          by_cases hA : h0Char S U σ.1 β.1 = h0Char S U σ'.1 β'.1
          · have hB : σ = σ' ∧ β = β' := hiff.mp hA
            simp [hB]
          · have hB : ¬ (σ = σ' ∧ β = β') := fun h => hA (hiff.mpr h)
            simp [hA, hB]

/-- The Brauer--Suzuki pairing for the `δ_β*`'s: they are orthogonal and have
norm two. -/
public theorem deltaStar_pairing (hS2 : Nat.card S = 2)
    (hU2' : Nat.Coprime 2 (Nat.card U))
    (β β' : IrrBG19 (↥(fixedSubgroup S U))) :
    scalarProduct (SemiProduct S U) (deltaStar S U hS2 β) (deltaStar S U hS2 β') =
      if β = β' then 2 else 0 := by
  classical
  let δ : ClassFunction (↥(H0sub S U)) := delta S U hS2 β.1
  let δ' : ClassFunction (↥(H0sub S U)) := delta S U hS2 β'.1
  have hδT : supportedOn δ {x : ↥(H0sub S U) | (x : SemiProduct S U) ∈ Tset S U} := by
    simpa [δ] using delta_supportedOn_Tset hS2 β.1
  have hδ'T : supportedOn δ' {x : ↥(H0sub S U) | (x : SemiProduct S U) ∈ Tset S U} := by
    simpa [δ'] using delta_supportedOn_Tset hS2 β'.1
  have hδc : IsClassFunction δ := by
    simpa [δ] using delta_isClassFunction hS2 β.1 (irreducibleCharacter_isClassFunction β.2)
  have hδ'c : IsClassFunction δ' := by
    simpa [δ'] using delta_isClassFunction hS2 β'.1 (irreducibleCharacter_isClassFunction β'.2)
  have h1 : scalarProduct (SemiProduct S U) (inducedClassFunction (H0sub S U) δ)
      (inducedClassFunction (H0sub S U) δ') =
      ((Nat.card (↥(H0sub S U)) : ℂ)⁻¹ * (Nat.card (↥(H0sub S U)) : ℂ)⁻¹) *
        ∑ z : SemiProduct S U, ∑ h : ↥(H0sub S U),
          pairingSummand (H0sub S U) δ δ' z h :=
    pairing_induced_expand (K := H0sub S U) δ δ'
  have h2 : (∑ z : SemiProduct S U, ∑ h : ↥(H0sub S U),
        pairingSummand (H0sub S U) δ δ' z h) =
      ∑ z : ↥(H0sub S U), ∑ h : ↥(H0sub S U),
        pairingSummand (H0sub S U) δ δ' (z : SemiProduct S U) h :=
    pairing_sum_eq_sum_subgroup (H0 := H0sub S U) (H := H0sub S U) (T := Tset S U)
      (Tset_TI hS2 hU2') (Tset_normalizer hS2 hU2') δ δ' hδT hδ'T
  have hBS : scalarProduct (SemiProduct S U) (inducedClassFunction (H0sub S U) δ)
      (inducedClassFunction (H0sub S U) δ') = scalarProduct (↥(H0sub S U)) δ δ' := by
    calc
      scalarProduct (SemiProduct S U) (inducedClassFunction (H0sub S U) δ)
          (inducedClassFunction (H0sub S U) δ') =
          ((Nat.card (↥(H0sub S U)) : ℂ)⁻¹ * (Nat.card (↥(H0sub S U)) : ℂ)⁻¹) *
            ∑ z : SemiProduct S U, ∑ h : ↥(H0sub S U),
              pairingSummand (H0sub S U) δ δ' z h := h1
      _ = ((Nat.card (↥(H0sub S U)) : ℂ)⁻¹ * (Nat.card (↥(H0sub S U)) : ℂ)⁻¹) *
              ∑ z : ↥(H0sub S U), ∑ h : ↥(H0sub S U),
                pairingSummand (H0sub S U) δ δ' (z : SemiProduct S U) h := by
              rw [h2]
      _ = ((Nat.card (↥(H0sub S U)) : ℂ)⁻¹ * (Nat.card (↥(H0sub S U)) : ℂ)⁻¹) *
              ∑ z : ↥(H0sub S U), ∑ h : ↥(H0sub S U),
                pairingSummand (H0sub S U) δ δ' (z : SemiProduct S U) h := rfl
      _ = scalarProduct (↥(H0sub S U)) δ δ' := by
              exact (scalarProduct_doubleSum_self (H0 := H0sub S U) hδ'c).symm
  have horth : scalarProduct (↥(H0sub S U)) δ δ' = if β = β' then 2 else 0 := by
    unfold δ δ'
    calc
      scalarProduct (↥(H0sub S U))
          (h0Char S U (1 : ClassFunction S) β.1 - h0Char S U (sigChar hS2) β.1)
          (h0Char S U (1 : ClassFunction S) β'.1 - h0Char S U (sigChar hS2) β'.1)
          = scalarProduct (↥(H0sub S U))
              (h0Char S U (1 : ClassFunction S) β.1 - h0Char S U (sigChar hS2) β.1)
              (h0Char S U (1 : ClassFunction S) β'.1) -
              scalarProduct (↥(H0sub S U))
              (h0Char S U (1 : ClassFunction S) β.1 - h0Char S U (sigChar hS2) β.1)
              (h0Char S U (sigChar hS2) β'.1) := by
              rw [scalarProduct_sub_right]
      _ = (scalarProduct (↥(H0sub S U)) (h0Char S U (1 : ClassFunction S) β.1)
              (h0Char S U (1 : ClassFunction S) β'.1) -
              scalarProduct (↥(H0sub S U)) (h0Char S U (sigChar hS2) β.1)
              (h0Char S U (1 : ClassFunction S) β'.1)) -
              (scalarProduct (↥(H0sub S U)) (h0Char S U (1 : ClassFunction S) β.1)
              (h0Char S U (sigChar hS2) β'.1) -
              scalarProduct (↥(H0sub S U)) (h0Char S U (sigChar hS2) β.1)
              (h0Char S U (sigChar hS2) β'.1)) := by
              rw [scalarProduct_sub_left, scalarProduct_sub_left]
      _ = if β = β' then 2 else 0 := by
              rw [show (1 : ClassFunction S) = (oneIrr S).1 by rfl]
              rw [show sigChar hS2 = (sigIrr hS2).1 by rfl]
              rw [h0Char_scalar hS2 (oneIrr S) (oneIrr S) β β',
                h0Char_scalar hS2 (sigIrr hS2) (oneIrr S) β β',
                h0Char_scalar hS2 (oneIrr S) (sigIrr hS2) β β',
                h0Char_scalar hS2 (sigIrr hS2) (sigIrr hS2) β β']
              by_cases hββ' : β = β'
              · simp [hββ', oneIrr_ne_sigIrr hS2, (oneIrr_ne_sigIrr hS2).symm]
                norm_num
              · simp [hββ', oneIrr_ne_sigIrr hS2, (oneIrr_ne_sigIrr hS2).symm]
  change scalarProduct (SemiProduct S U) (inducedClassFunction (H0sub S U) δ)
      (inducedClassFunction (H0sub S U) δ') = if β = β' then 2 else 0
  rw [hBS, horth]

end OrderTwoCorrespondence

section InducedCharacter

variable {G : Type u} [Group G] [Fintype G]

/-- Standardize a representation on a finite-dimensional space to `Fin n → ℂ`. -/
public noncomputable def standardizeRepresentation {V : Type u} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) :
    Representation ℂ G (Fin (Module.finrank ℂ V) → ℂ) := by
  let b : Module.Basis (Fin (Module.finrank ℂ V)) ℂ V := Module.finBasis ℂ V
  let e : V ≃ₗ[ℂ] (Fin (Module.finrank ℂ V) → ℂ) := b.equivFun
  refine { toFun := fun g => e.conj (ρ g), map_one' := ?_, map_mul' := ?_ }
  · ext x
    simp [LinearEquiv.conj_apply]
  · intro g h
    ext x
    simp [LinearEquiv.conj_apply, map_mul]

omit [Fintype G] in
/-- The standardized representation has the same character. -/
public theorem standardizeRepresentation_character {V : Type u} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (g : G) :
    (standardizeRepresentation ρ).character g = ρ.character g := by
  dsimp [standardizeRepresentation, Representation.character]
  exact LinearMap.trace_conj' (R := ℂ) (M := V)
    (N := Fin (Module.finrank ℂ V) → ℂ) (ρ g)
    (Module.Basis.equivFun (Module.finBasis ℂ V))

/-- The class-function induction of a character is a character. -/
public theorem isCharacter_induced (H : Subgroup G) {φ : ClassFunction (↥H)}
    (hφ : IsCharacter φ) : IsCharacter (inducedClassFunction H φ) := by
  rcases hφ with ⟨n, ρ, rfl⟩
  have : FiniteDimensional ℂ (Representation.IndV H.subtype ρ) :=
    Theory.Representation.finiteDimensional_ind H ρ
  let σ : Representation ℂ G (Representation.IndV H.subtype ρ) :=
    Representation.ind H.subtype ρ
  refine ⟨Module.finrank ℂ (Representation.IndV H.subtype ρ), standardizeRepresentation σ, ?_⟩
  ext g
  calc
    inducedClassFunction H ρ.character g
        = (Nat.card (↥H) : ℂ)⁻¹ * ∑ x : G,
            if hx : x⁻¹ * g * x ∈ H then ρ.character ⟨x⁻¹ * g * x, hx⟩ else 0 := by
          unfold inducedClassFunction
          rfl
    _ = (Nat.card (↥H) : ℂ)⁻¹ *
          ∑ x ∈ (@Finset.univ G (Fintype.ofFinite G)),
            if hx : x * g * x⁻¹ ∈ H then ρ.character ⟨x * g * x⁻¹, hx⟩ else 0 := by
          congr 1
          refine Finset.sum_bij (fun x hx => x⁻¹) (s := Finset.univ)
            (t := (@Finset.univ G (Fintype.ofFinite G)))
            ?_ ?_ ?_ ?_
          · intro x hx
            exact @Finset.mem_univ G (Fintype.ofFinite G) x⁻¹
          · intro a ha b hb hEq
            exact inv_injective hEq
          · intro x hx
            refine ⟨x⁻¹, @Finset.mem_univ G inferInstance x⁻¹, ?_⟩
            simp
          · intro x hx
            by_cases hxH : x⁻¹ * g * x ∈ H
            · have hxH' : (x⁻¹) * g * (x⁻¹)⁻¹ ∈ H := by simpa using hxH
              simp [hxH]
            · simp [hxH]
    _ = σ.character g := (Theory.Representation.induced_character_formula H ρ g).symm
    _ = (standardizeRepresentation σ).character g :=
          (standardizeRepresentation_character σ g).symm

/-- The class-function induction of a generalized character is a generalized
character. -/
public theorem isGeneralizedCharacter_induced (H : Subgroup G) {φ : ClassFunction (↥H)}
    (hφ : IsGeneralizedCharacter φ) : IsGeneralizedCharacter (inducedClassFunction H φ) := by
  rcases hφ with ⟨χ, ψ, hχ, hψ, hφeq⟩
  refine ⟨inducedClassFunction H χ, inducedClassFunction H ψ,
    isCharacter_induced H hχ, isCharacter_induced H hψ, ?_⟩
  rw [hφeq]
  exact inducedClassFunction_sub H χ ψ

/-- The scalar product is invariant under a group isomorphism (pulling back). -/
public theorem scalarProduct_equiv_invariance {H : Type u} [Group H] [Fintype H]
    (e : G ≃* H) (φ ψ : ClassFunction H) :
    scalarProduct H φ ψ =
      scalarProduct G (fun g : G => φ (e g)) (fun g : G => ψ (e g)) := by
  classical
  unfold scalarProduct
  have hcard : (Nat.card H : ℂ)⁻¹ = (Nat.card G : ℂ)⁻¹ := by
    congr 1
    exact congrArg (fun n : ℕ => (n : ℂ)) (Nat.card_congr e.toEquiv.symm)
  rw [hcard]
  have hsum : (∑ h : H, φ h * star (ψ h)) = (∑ g : G, φ (e g) * star (ψ (e g))) := by
    exact (Equiv.sum_comp e.toEquiv (fun y : H => φ y * star (ψ y))).symm
  rw [hsum]

end InducedCharacter

section GlaubermanCorrespondence

variable {S U : Type u} [Group S] [Group U] [Fintype S] [Fintype U]
variable [MulDistribMulAction S U]

omit [Fintype S] [Fintype U] in
/-- An element of `USub` is the image of its left component. -/
public theorem usub_eq_inl (x : ↥(USub S U)) :
    (x : SemiProduct S U) = SemidirectProduct.inl x.1.left := by
  apply SemidirectProduct.ext
  · rfl
  · have hx : x.1.right = 1 := (mem_USub_iff x.1).1 x.2
    simp [hx]

omit [Fintype S] [Fintype U] in
/-- Conjugation of `inl u` by `inl v` in the semidirect product. -/
public theorem inl_conj_inl (v u : U) :
    (SemidirectProduct.inl v : SemiProduct S U)⁻¹ *
        (SemidirectProduct.inl u : SemiProduct S U) *
        (SemidirectProduct.inl v : SemiProduct S U) =
      (SemidirectProduct.inl (v⁻¹ * u * v) : SemiProduct S U) := by
  apply SemidirectProduct.ext <;> simp

omit [Fintype S] [Fintype U] in
/-- Conjugation of `inl w` by `inr s` in the semidirect product. -/
public theorem inr_smul_inl (s : S) (w : U) :
    (SemidirectProduct.inr s : SemiProduct S U) *
        (SemidirectProduct.inl w : SemiProduct S U) *
        (SemidirectProduct.inr s : SemiProduct S U)⁻¹ =
      (SemidirectProduct.inl (s • w) : SemiProduct S U) := by
  apply SemidirectProduct.ext <;> simp [MulDistribMulAction.toMulAut_apply]

/-- The class function on `G = U ⋊ S` induced from `α ∈ IrrBG19(U)`. -/
public noncomputable def alphaInduced (α : IrrBG19 U) : ClassFunction (SemiProduct S U) :=
  inducedClassFunction (USub S U) (fun x : ↥(USub S U) => α.1 x.1.left)

/-- `α^G` is a character. -/
public theorem alphaInduced_isCharacter (α : IrrBG19 U) :
    IsCharacter (alphaInduced (S := S) (U := U) α) := by
  unfold alphaInduced
  have hα' : IsIrreducibleCharacter (fun x : ↥(USub S U) => α.1 x.1.left) := by
    change IsIrreducibleCharacter (fun x : ↥(USub S U) => α.1 ((usubEquiv S U).symm x))
    exact isIrreducibleCharacter_congr (usubEquiv S U).symm α.2
  exact isCharacter_induced (USub S U)
    (isCharacter_of_isIrreducibleCharacter hα')

omit [Fintype S] [Fintype U] in
/-- Conjugation of `inl u` by `inl v * inr s` in the semidirect product. -/
public theorem conj_inl_mul_inr (s : S) (v u : U) :
    ((SemidirectProduct.inl v : SemiProduct S U) * SemidirectProduct.inr s)⁻¹ *
        (SemidirectProduct.inl u : SemiProduct S U) *
        ((SemidirectProduct.inl v : SemiProduct S U) * SemidirectProduct.inr s) =
      (SemidirectProduct.inl (s⁻¹ • (v⁻¹ * u * v)) : SemiProduct S U) := by
  apply SemidirectProduct.ext <;> simp [MulDistribMulAction.toMulAut_apply]

/-- The value of `α^G` on `U` is `2α` when `α` is fixed by `S`. -/
public theorem alphaInduced_restrict (hS2 : Nat.card S = 2) (α : IrrBG19 U)
    (hα : FixedIrr S U α) (u : U) :
    alphaInduced (S := S) (U := U) α (SemidirectProduct.inl u) = 2 * α.1 u := by
  classical
  have hne : (Nat.card (↥(USub S U)) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := ↥(USub S U))).ne'
  have hcard : Nat.card (SemiProduct S U) = 2 * Nat.card (↥(USub S U)) := by
    have hmain := Subgroup.card_mul_index (USub S U)
    have hU : Nat.card ↥(USub S U) = Nat.card U :=
      Nat.card_congr (usubEquiv S U).toEquiv.symm
    have hG : Nat.card (SemiProduct S U) = Nat.card U * Nat.card S := SemidirectProduct.card
    have hpos : 0 < Nat.card U := Nat.card_pos (α := U)
    calc
      Nat.card (SemiProduct S U) = Nat.card U * Nat.card S := hG
      _ = Nat.card U * 2 := by rw [hS2]
      _ = Nat.card ↥(USub S U) * 2 := by rw [hU]
      _ = 2 * Nat.card ↥(USub S U) := by rw [mul_comm]
  have hsummand (x : SemiProduct S U) :
      (if hx : x⁻¹ * SemidirectProduct.inl u * x ∈ USub S U then
        (fun y : ↥(USub S U) => α.1 y.1.left) ⟨x⁻¹ * SemidirectProduct.inl u * x, hx⟩ else 0) =
      α.1 u := by
    have hmemx : x⁻¹ * SemidirectProduct.inl u * x ∈ USub S U := by
      simpa using ((USub_normal (S := S) (U := U)).conj_mem (SemidirectProduct.inl u)
        (by rw [mem_USub_iff]; rfl) x⁻¹)
    rw [dif_pos hmemx]
    change α.1 (⟨x⁻¹ * SemidirectProduct.inl u * x, hmemx⟩ : ↥(USub S U)).1.left = α.1 u
    rcases (s_eq_one_or_s2 hS2 x.right) with hxr | hxr
    · have hxEq : (x : SemiProduct S U) = SemidirectProduct.inl x.left := by
        apply SemidirectProduct.ext <;> simp [hxr]
      have hEq : (⟨x⁻¹ * SemidirectProduct.inl u * x, hmemx⟩ : ↥(USub S U)).1.left =
          x.left⁻¹ * u * x.left := by
        have hEq' : (⟨x⁻¹ * SemidirectProduct.inl u * x, hmemx⟩ : ↥(USub S U)).1 =
            SemidirectProduct.inl (x.left⁻¹ * u * x.left) := by
          change x⁻¹ * SemidirectProduct.inl u * x =
            SemidirectProduct.inl (x.left⁻¹ * u * x.left)
          rw [hxEq, inl_conj_inl]
          simp
        exact congrArg (fun z : SemiProduct S U => z.left) hEq'
      rw [hEq]
      simpa using (irreducibleCharacter_isClassFunction α.2 u x.left⁻¹)
    · have hxEq : (x : SemiProduct S U) =
        (SemidirectProduct.inl x.left : SemiProduct S U) *
          SemidirectProduct.inr (s2 hS2) := by
        apply SemidirectProduct.ext <;> simp [hxr]
      have hEq : (⟨x⁻¹ * SemidirectProduct.inl u * x, hmemx⟩ : ↥(USub S U)).1.left =
          (s2 hS2)⁻¹ • (x.left⁻¹ * u * x.left) := by
        have hEq' : (⟨x⁻¹ * SemidirectProduct.inl u * x, hmemx⟩ : ↥(USub S U)).1 =
            SemidirectProduct.inl ((s2 hS2)⁻¹ • (x.left⁻¹ * u * x.left)) := by
          change x⁻¹ * SemidirectProduct.inl u * x =
            SemidirectProduct.inl ((s2 hS2)⁻¹ • (x.left⁻¹ * u * x.left))
          rw [hxEq, conj_inl_mul_inr]
          simp
        exact congrArg (fun z : SemiProduct S U => z.left) hEq'
      rw [hEq]
      have hfix : α.1 ((s2 hS2)⁻¹ • (x.left⁻¹ * u * x.left)) =
          α.1 (x.left⁻¹ * u * x.left) := by
        exact congrFun (hα (s2 hS2)⁻¹) (x.left⁻¹ * u * x.left)
      rw [hfix]
      simpa using (irreducibleCharacter_isClassFunction α.2 u x.left⁻¹)
  have hsum : (∑ x : SemiProduct S U,
      if hx : x⁻¹ * SemidirectProduct.inl u * x ∈ USub S U then
        (fun y : ↥(USub S U) => α.1 y.1.left) ⟨x⁻¹ * SemidirectProduct.inl u * x, hx⟩ else 0) =
      (Nat.card (SemiProduct S U) : ℂ) * α.1 u := by
    calc
      (∑ x : SemiProduct S U,
          if hx : x⁻¹ * SemidirectProduct.inl u * x ∈ USub S U then
            (fun y : ↥(USub S U) => α.1 y.1.left) ⟨x⁻¹ * SemidirectProduct.inl u * x, hx⟩ else 0)
          = ∑ x : SemiProduct S U, α.1 u := by
              refine Finset.sum_congr rfl ?_
              intro x hx
              exact hsummand x
      _ = (Nat.card (SemiProduct S U) : ℂ) * α.1 u := by
              simp [Finset.sum_const, Nat.card_eq_fintype_card]
  unfold alphaInduced inducedClassFunction
  rw [hsum, hcard]
  field_simp [hne]
  rw [Nat.cast_mul]
  ring

set_option backward.isDefEq.respectTransparency false in
/-- The star-norm of `α^G` is `2` when `α` is fixed. -/
public theorem alphaInduced_norm (hS2 : Nat.card S = 2) (α : IrrBG19 U) (hα : FixedIrr S U α) :
    scalarProduct (SemiProduct S U) (alphaInduced (S := S) (U := U) α)
      (alphaInduced (S := S) (U := U) α) = 2 := by
  classical
  let δ : ClassFunction (↥(USub S U)) := fun x => α.1 x.1.left
  have hsp1 : scalarProduct (↥(USub S U)) δ δ = 1 := by
    have h := scalarProduct_equiv_invariance (G := U) (H := ↥(USub S U))
      (usubEquiv S U) δ δ
    rw [h]
    have hα' : (fun u : U => δ (usubEquiv S U u)) = α.1 := by
      funext u
      simp [δ, usubEquiv]
    rw [hα']
    simpa using (scalarProduct_irr_ite α.2 α.2)
  have hχcls : IsClassFunction (alphaInduced (S := S) (U := U) α) :=
    isCharacter_isClassFunction (alphaInduced_isCharacter α)
  have hFrob : scalarProduct (SemiProduct S U) (alphaInduced (S := S) (U := U) α)
      (alphaInduced (S := S) (U := U) α) =
      scalarProduct (↥(USub S U)) δ (fun x : ↥(USub S U) =>
        alphaInduced (S := S) (U := U) α (x : SemiProduct S U)) := by
    simpa [alphaInduced, δ] using
      (frobenius_reciprocity (G := SemiProduct S U) (H := USub S U) δ hχcls)
  calc
    scalarProduct (SemiProduct S U) (alphaInduced (S := S) (U := U) α)
        (alphaInduced (S := S) (U := U) α)
        = scalarProduct (↥(USub S U)) δ
            (fun x : ↥(USub S U) => alphaInduced (S := S) (U := U) α (x : SemiProduct S U)) := hFrob
    _ = scalarProduct (↥(USub S U)) δ (((2 : ℂ) • δ)) := by
            congr 1
            funext x
            have hx : (x : SemiProduct S U) = SemidirectProduct.inl x.1.left := usub_eq_inl x
            calc
              alphaInduced (S := S) (U := U) α (x : SemiProduct S U)
                  = alphaInduced (S := S) (U := U) α (SemidirectProduct.inl x.1.left) := by
                      conv_lhs =>
                        rw [hx]
              _ = 2 * α.1 x.1.left := alphaInduced_restrict hS2 α hα x.1.left
              _ = (((2 : ℂ) • δ)) x := by simp [δ]
    _ = 2 * scalarProduct (↥(USub S U)) δ δ := by
            have hsmul := scalarProduct_smul_right (G := ↥(USub S U)) (2 : ℂ) δ δ
            rw [hsmul]
            simp
            ring
    _ = 2 := by
            rw [hsp1]
            norm_num

/-- A fixed character of norm-two induces to the sum of two distinct
irreducible characters. -/
public theorem alphaInduced_decompose (hS2 : Nat.card S = 2) (α : IrrBG19 U) (hα : FixedIrr S U α) :
    ∃ χ₁ χ₂ : ClassFunction (SemiProduct S U),
      IsIrreducibleCharacter χ₁ ∧ IsIrreducibleCharacter χ₂ ∧ χ₁ ≠ χ₂ ∧
      alphaInduced (S := S) (U := U) α = χ₁ + χ₂ :=
  char_norm_two_decomp (alphaInduced_isCharacter α) (alphaInduced_norm hS2 α hα)

/-- The restriction of an irreducible character of `G` to `U` is a character. -/
public theorem restrict_isCharacter {χ : ClassFunction (SemiProduct S U)}
    (hχ : IsIrreducibleCharacter χ) :
    IsCharacter (fun u : U => χ (SemidirectProduct.inl u)) := by
  have hres : IsCharacter (fun x : ↥(USub S U) => χ (x : SemiProduct S U)) :=
    isCharacter_restrict (USub S U) (isCharacter_of_isIrreducibleCharacter hχ)
  change IsCharacter (fun u : U => χ ((usubEquiv S U u : ↥(USub S U)) : SemiProduct S U))
  exact isCharacter_congrBG19 (usubEquiv S U) hres

/-- The scalar product of `α` with a constituent of `α^G` of scalar product
one is one. -/
public theorem restrict_scalarProduct_alpha (hS2 : Nat.card S = 2) (α : IrrBG19 U)
    (hα : FixedIrr S U α) {χ : ClassFunction (SemiProduct S U)}
    (hχ : IsIrreducibleCharacter χ)
    (hsp : scalarProduct (SemiProduct S U) χ (alphaInduced (S := S) (U := U) α) = 1) :
    scalarProduct U α.1 (fun u : U => χ (SemidirectProduct.inl u)) = 1 := by
  classical
  let δ : ClassFunction (↥(USub S U)) := fun x => α.1 x.1.left
  let φ : ClassFunction (↥(USub S U)) := fun x => χ (x : SemiProduct S U)
  have h1 := scalarProduct_restrict_induced (H := USub S U)
    (hχ := irreducibleCharacter_isClassFunction hχ)
    (δ := δ)
  have hφδ : scalarProduct (↥(USub S U)) φ δ = 1 := by
    simpa [alphaInduced, δ, φ] using h1.trans hsp
  have h2 := scalarProduct_equiv_invariance (G := U) (H := ↥(USub S U))
    (usubEquiv S U) φ δ
  have hψα : scalarProduct U (fun u : U => χ (SemidirectProduct.inl u)) α.1 = 1 := by
    change scalarProduct U (fun g : U => φ (usubEquiv S U g))
      (fun g : U => δ (usubEquiv S U g)) = 1
    rw [← h2]
    exact hφδ
  have hconj := scalarProduct_conj (fun u : U => χ (SemidirectProduct.inl u)) α.1
  rw [← hconj, hψα]
  simp

/-- A constituent of `α^G` with scalar product one and the same degree
restricts to `α` on `U`. -/
public theorem restrict_constituent_of_sp_one (hS2 : Nat.card S = 2) (α : IrrBG19 U)
    (hα : FixedIrr S U α) {χ : ClassFunction (SemiProduct S U)}
    (hχ : IsIrreducibleCharacter χ)
    (hsp : scalarProduct (SemiProduct S U) χ (alphaInduced (S := S) (U := U) α) = 1)
    (hdeg : χ 1 = α.1 1) (u : U) : χ (SemidirectProduct.inl u) = α.1 u := by
  classical
  let ψ : ClassFunction U := fun x => χ (SemidirectProduct.inl x)
  have hψchar : IsCharacter ψ := by
    simpa [ψ] using (restrict_isCharacter (χ := χ) hχ)
  have hspα : scalarProduct U α.1 ψ = 1 := by
    simpa [ψ] using (restrict_scalarProduct_alpha hS2 α hα hχ hsp)
  have hEq : ψ = α.1 :=
    char_eq_irreducible_of_scalarProduct_one_and_degree (G := U) hψchar α.2 hspα
      (by simpa [ψ] using hdeg)
  exact congrFun hEq u

/-- Every irreducible constituent of `α^G` restricts to `α` on `U`. -/
public theorem alphaInduced_restrict_constituent (hS2 : Nat.card S = 2) (α : IrrBG19 U)
    (hα : FixedIrr S U α) {χ : ClassFunction (SemiProduct S U)}
    (hχ : IsIrreducibleCharacter χ)
    (hχψ : scalarProduct (SemiProduct S U) χ (alphaInduced (S := S) (U := U) α) ≠ 0) :
    ∀ u : U, χ (SemidirectProduct.inl u) = α.1 u := by
  classical
  rcases alphaInduced_decompose hS2 α hα with ⟨χ₁, χ₂, hχ₁, hχ₂, hne, hsum⟩
  have hsp₁ : scalarProduct (SemiProduct S U) χ₁ (alphaInduced (S := S) (U := U) α) = 1 := by
    rw [hsum]
    rw [scalarProduct_add_right]
    simp [scalarProduct_irr_ite hχ₁ hχ₁, scalarProduct_irr_ite hχ₁ hχ₂, hne]
  have hsp₂ : scalarProduct (SemiProduct S U) χ₂ (alphaInduced (S := S) (U := U) α) = 1 := by
    rw [hsum]
    rw [scalarProduct_add_right]
    simp [scalarProduct_irr_ite hχ₂ hχ₁, scalarProduct_irr_ite hχ₂ hχ₂, hne.symm]
  have hdeg_sum : χ₁ 1 + χ₂ 1 = 2 * α.1 1 := by
    have h := congrFun hsum (1 : SemiProduct S U)
    have hα1 : alphaInduced (S := S) (U := U) α 1 = 2 * α.1 1 := by
      simpa using (alphaInduced_restrict hS2 α hα (1 : U))
    have h' : alphaInduced (S := S) (U := U) α 1 = χ₁ 1 + χ₂ 1 := by simpa using h
    rw [hα1] at h'
    exact h'.symm
  have hle₁ := irreducible_char_degree_le_of_scalarProduct_one (G := U)
    (ψ := fun u : U => χ₁ (SemidirectProduct.inl u)) (χ := α.1)
    (restrict_isCharacter hχ₁) α.2 (restrict_scalarProduct_alpha hS2 α hα hχ₁ hsp₁)
  rcases hle₁ with ⟨r₁, d₁, hdegψ₁, hdegα₁, hle₁'⟩
  have hle₂ := irreducible_char_degree_le_of_scalarProduct_one (G := U)
    (ψ := fun u : U => χ₂ (SemidirectProduct.inl u)) (χ := α.1)
    (restrict_isCharacter hχ₂) α.2 (restrict_scalarProduct_alpha hS2 α hα hχ₂ hsp₂)
  rcases hle₂ with ⟨r₂, d₂, hdegψ₂, hdegα₂, hle₂'⟩
  have h₁ : χ₁ 1 = (r₁ : ℂ) := by simpa using hdegψ₁
  have h₂ : χ₂ 1 = (r₂ : ℂ) := by simpa using hdegψ₂
  have hd : d₁ = d₂ := by
    exact_mod_cast (hdegα₁.symm.trans hdegα₂)
  have hdegsum : (r₁ : ℂ) + (r₂ : ℂ) = 2 * (d₁ : ℂ) := by
    calc
      (r₁ : ℂ) + (r₂ : ℂ) = χ₁ 1 + χ₂ 1 := by rw [← h₁, ← h₂]
      _ = 2 * α.1 1 := hdeg_sum
      _ = 2 * (d₁ : ℂ) := by rw [hdegα₁]
  have hdegsum_nat : r₁ + r₂ = 2 * d₁ := by
    exact_mod_cast hdegsum
  have hd₁eq : r₁ = d₁ := by omega
  have hd₂eq : r₂ = d₁ := by omega
  have hdeg₁ : χ₁ 1 = α.1 1 := by
    rw [h₁, hdegα₁]
    exact congrArg (fun k : ℕ => (k : ℂ)) hd₁eq
  have hdeg₂ : χ₂ 1 = α.1 1 := by
    rw [h₂, hdegα₁]
    exact congrArg (fun k : ℕ => (k : ℂ)) hd₂eq
  have hχmem : χ = χ₁ ∨ χ = χ₂ := by
    have hspχ : scalarProduct (SemiProduct S U) χ (χ₁ + χ₂) ≠ 0 := by
      simpa [hsum] using hχψ
    by_contra hnone
    push_neg at hnone
    have hcalc : scalarProduct (SemiProduct S U) χ (χ₁ + χ₂) =
        (if χ = χ₁ then (1 : ℂ) else 0) + (if χ = χ₂ then (1 : ℂ) else 0) := by
      rw [scalarProduct_add_right]
      rw [scalarProduct_irr_ite hχ hχ₁, scalarProduct_irr_ite hχ hχ₂]
    rw [hcalc] at hspχ
    simp [hnone.1, hnone.2] at hspχ
  rcases hχmem with rfl | rfl
  · intro u
    exact restrict_constituent_of_sp_one hS2 α hα hχ₁ hsp₁ hdeg₁ u
  · intro u
    exact restrict_constituent_of_sp_one hS2 α hα hχ₂ hsp₂ hdeg₂ u

end GlaubermanCorrespondence

section OrderTwoLambda

variable {S U : Type u} [Group S] [Group U] [Fintype S] [Fintype U]
variable [MulDistribMulAction S U]

/-- The sign character of `U ⋊ S` obtained from the `S`-component. -/
public noncomputable def lambdaHom (hS2 : Nat.card S = 2) : SemiProduct S U →* ℂˣ where
  toFun g := sigHom hS2 g.right
  map_one' := by simp [sigHom]
  map_mul' := by
    intro g h
    rw [SemidirectProduct.mul_right]
    exact (sigHom hS2).map_mul' g.right h.right

/-- The sign character of `U ⋊ S` obtained from the `S`-component. -/
public noncomputable def lambdaChar (hS2 : Nat.card S = 2) : ClassFunction (SemiProduct S U) :=
  fun g => ((lambdaHom hS2 g : ℂˣ) : ℂ)

/-- The value of `lambdaChar` at an element with trivial `S`-component is `1`. -/
public theorem lambdaChar_apply_right_one (hS2 : Nat.card S = 2) (g : SemiProduct S U)
    (hg : g.right = 1) : lambdaChar hS2 g = 1 := by
  simp [lambdaChar, lambdaHom, hg, sigHom]

/-- The value of `lambdaChar` at an element with nontrivial `S`-component is `-1`. -/
public theorem lambdaChar_apply_right_ne_one (hS2 : Nat.card S = 2) (g : SemiProduct S U)
    (hg : g.right ≠ 1) : lambdaChar hS2 g = -1 := by
  have hg' : g.right = s2 hS2 := (s_eq_one_or_s2 hS2 g.right).resolve_left hg
  simp [lambdaChar, lambdaHom, hg', sigHom, s2_ne_one hS2]

/-- `lambdaChar` is a linear character. -/
public theorem lambdaChar_isLinear (hS2 : Nat.card S = 2) :
    IsLinearCharacter (fun g : SemiProduct S U => ((lambdaHom hS2 g : ℂˣ) : ℂ)) := by
  have h := isLinearCharacter_of_hom (G := SemiProduct S U) (φ := lambdaHom hS2)
  simpa using h

/-- `alphaInduced` vanishes at elements with nontrivial `S`-component. -/
public theorem alphaInduced_vanishes_of_right_ne_one (hS2 : Nat.card S = 2) (α : IrrBG19 U)
    (g : SemiProduct S U) (hg : g.right ≠ 1) :
    alphaInduced (S := S) (U := U) α g = 0 := by
  classical
  unfold alphaInduced inducedClassFunction
  rw [Finset.sum_eq_zero]
  · simp
  intro x hx
  have hmem : ¬ (x⁻¹ * g * x) ∈ USub S U := by
    rw [mem_USub_iff]
    intro h
    have h' : (x⁻¹ * g * x).right = 1 := h
    rw [SemidirectProduct.mul_right, SemidirectProduct.mul_right,
      SemidirectProduct.inv_right] at h'
    have hg' : x.right⁻¹ * g.right * x.right = g.right := by
      calc
        x.right⁻¹ * g.right * x.right = g.right * x.right⁻¹ * x.right := by
          rw [comm_of_card_two hS2 (x.right⁻¹) (g.right)]
        _ = g.right := by group
    exact hg (by rw [← hg']; exact h')
  simp [hmem]

/-- `alphaInduced` is invariant under twisting by `lambdaChar`. -/
public theorem alphaInduced_mul_lambda (hS2 : Nat.card S = 2) (α : IrrBG19 U) :
    (fun g : SemiProduct S U => alphaInduced (S := S) (U := U) α g * lambdaChar hS2 g) =
      alphaInduced (S := S) (U := U) α := by
  classical
  funext g
  by_cases hg : g.right = 1
  · rw [lambdaChar_apply_right_one hS2 g hg]
    ring
  · have hz : alphaInduced (S := S) (U := U) α g = 0 :=
      alphaInduced_vanishes_of_right_ne_one hS2 α g hg
    rw [hz]
    simp

/-- The two irreducible constituents of `α^G`. -/
public noncomputable def alphaPair (hS2 : Nat.card S = 2) (α : IrrBG19 U) (hα : FixedIrr S U α) :
    ClassFunction (SemiProduct S U) × ClassFunction (SemiProduct S U) :=
  (Classical.choose (alphaInduced_decompose hS2 α hα),
    Classical.choose (Classical.choose_spec (alphaInduced_decompose hS2 α hα)))

public theorem alphaPair_spec (hS2 : Nat.card S = 2) (α : IrrBG19 U) (hα : FixedIrr S U α) :
    IsIrreducibleCharacter (alphaPair hS2 α hα).1 ∧
      IsIrreducibleCharacter (alphaPair hS2 α hα).2 ∧
      (alphaPair hS2 α hα).1 ≠ (alphaPair hS2 α hα).2 ∧
      alphaInduced (S := S) (U := U) α =
        (alphaPair hS2 α hα).1 + (alphaPair hS2 α hα).2 :=
  by
  classical
  let hdec := alphaInduced_decompose hS2 α hα
  have hspec : IsIrreducibleCharacter (Classical.choose hdec) ∧
      IsIrreducibleCharacter (Classical.choose (Classical.choose_spec hdec)) ∧
      Classical.choose hdec ≠ Classical.choose (Classical.choose_spec hdec) ∧
      alphaInduced (S := S) (U := U) α =
        Classical.choose hdec + Classical.choose (Classical.choose_spec hdec) :=
    Classical.choose_spec (Classical.choose_spec hdec)
  simpa [alphaPair] using hspec

public theorem alphaPair_irr₁ (hS2 : Nat.card S = 2) (α : IrrBG19 U) (hα : FixedIrr S U α) :
    IsIrreducibleCharacter (alphaPair hS2 α hα).1 :=
  (alphaPair_spec hS2 α hα).1

public theorem alphaPair_irr₂ (hS2 : Nat.card S = 2) (α : IrrBG19 U) (hα : FixedIrr S U α) :
    IsIrreducibleCharacter (alphaPair hS2 α hα).2 :=
  (alphaPair_spec hS2 α hα).2.1

public theorem alphaPair_distinct (hS2 : Nat.card S = 2) (α : IrrBG19 U) (hα : FixedIrr S U α) :
    (alphaPair hS2 α hα).1 ≠ (alphaPair hS2 α hα).2 :=
  (alphaPair_spec hS2 α hα).2.2.1

public theorem alphaPair_sum (hS2 : Nat.card S = 2) (α : IrrBG19 U) (hα : FixedIrr S U α) :
    alphaInduced (S := S) (U := U) α =
      (alphaPair hS2 α hα).1 + (alphaPair hS2 α hα).2 :=
  (alphaPair_spec hS2 α hα).2.2.2

/-- The scalar product on `G` of class functions supported on a subgroup `H` of
index two is half the scalar product of their restrictions. -/
public theorem scalarProduct_support_subgroup {G : Type u} [Group G] [Fintype G]
    (H : Subgroup G) (hindex : H.index = 2) (φ ψ : ClassFunction G)
    (hφ : ∀ g : G, g ∉ H → φ g = 0) (hψ : ∀ g : G, g ∉ H → ψ g = 0) :
    scalarProduct G φ ψ = (2 : ℂ)⁻¹ * scalarProduct (↥H) (fun x => φ x) (fun x => ψ x) := by
  classical
  have hsplit : (∑ g : G, φ g * star (ψ g)) =
      ∑ g : G, (if g ∈ H then φ g * star (ψ g) else 0) := by
    refine Finset.sum_congr rfl ?_
    intro g hg
    by_cases hgH : g ∈ H <;> simp [hgH, hφ, hψ]
  have hfilter : (∑ g : G, (if g ∈ H then φ g * star (ψ g) else 0)) =
      ∑ x : ↥H, φ x * star (ψ x) := by
    rw [← Finset.sum_filter]
    refine Finset.sum_bij (fun x hx => (⟨x, (Finset.mem_filter.mp hx).2⟩ : ↥H)) ?_ ?_ ?_ ?_
    · intro x hx
      simp
    · intro a ha b hb hEq
      exact congrArg Subtype.val hEq
    · intro x hx
      refine ⟨(x : G), ?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ (x : G), x.2⟩
      · rfl
    · intro a ha
      rfl
  have hcard : (Nat.card G : ℂ) = 2 * (Nat.card ↥H : ℂ) := by
    have hcardNat : Nat.card G = 2 * Nat.card ↥H := by
      calc
        Nat.card G = Nat.card ↥H * H.index := (Subgroup.card_mul_index H).symm
        _ = Nat.card ↥H * 2 := by rw [hindex]
        _ = 2 * Nat.card ↥H := by rw [mul_comm]
    exact_mod_cast hcardNat
  unfold scalarProduct
  rw [hsplit, hfilter, hcard]
  have hne : (Nat.card ↥H : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := ↥H)).ne'
  field_simp [hne]

/-- A scalar product of a class function with itself is a nonnegative real. -/
public theorem scalarProduct_self_nonneg {G : Type u} [Group G] [Fintype G]
    (φ : ClassFunction G) :
    ∃ r : ℝ, 0 ≤ r ∧ scalarProduct G φ φ = (r : ℂ) := by
  classical
  let S : ℝ := ∑ g : G, Complex.normSq (φ g)
  let T : ℝ := (Nat.card G : ℝ)⁻¹ * S
  refine ⟨T, ?_, ?_⟩
  · exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (Finset.sum_nonneg (fun g hg => Complex.normSq_nonneg _))
  · unfold scalarProduct
    have hsum : (∑ g : G, φ g * star (φ g)) = (S : ℂ) := by
      calc
        (∑ g : G, φ g * star (φ g)) = (∑ g : G, (Complex.normSq (φ g) : ℂ)) := by
          refine Finset.sum_congr rfl ?_
          intro g hg
          rw [← Complex.mul_conj (φ g)]
          congr 1
        _ = (S : ℂ) := by
              dsimp [S]
              norm_cast
    calc
      (Nat.card G : ℂ)⁻¹ * (∑ g : G, φ g * star (φ g))
          = (Nat.card G : ℂ)⁻¹ * (S : ℂ) := by
          rw [hsum]
      _ = (T : ℂ) := by
          dsimp [T]
          rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv]
          rw [Complex.ofReal_mul]

end OrderTwoLambda

section OrderTwoConstituents

variable {S U : Type u} [Group S] [Group U] [Fintype S] [Fintype U]
variable [MulDistribMulAction S U]

/-- Twisting the first argument of the scalar product by `lambdaChar` may be
moved to the second argument (since `lambdaChar` is real-valued). -/
public theorem scalarProduct_mul_lambda (hS2 : Nat.card S = 2)
    (φ ψ : ClassFunction (SemiProduct S U)) :
    scalarProduct (SemiProduct S U) (φ * lambdaChar hS2) ψ =
      scalarProduct (SemiProduct S U) φ (ψ * lambdaChar hS2) := by
  classical
  unfold scalarProduct
  congr 1
  refine Finset.sum_congr rfl ?_
  intro g hg
  have hLam : star (lambdaChar hS2 g) = lambdaChar hS2 g := by
    by_cases hg1 : g.right = 1
    · rw [lambdaChar_apply_right_one hS2 g hg1]
      simp
    · rw [lambdaChar_apply_right_ne_one hS2 g hg1]
      simp
  rw [Pi.mul_apply]
  rw [Pi.mul_apply]
  rw [StarMul.star_mul]
  rw [hLam]
  ring

set_option backward.isDefEq.respectTransparency false in
/-- The second constituent of `α^G` is the first twisted by `lambdaChar`. -/
public theorem alphaPair₂_eq_mul_lambda (hS2 : Nat.card S = 2) (α : IrrBG19 U)
    (hα : FixedIrr S U α) :
    (alphaPair hS2 α hα).2 = (alphaPair hS2 α hα).1 * lambdaChar hS2 := by
  classical
  let χ₁ : ClassFunction (SemiProduct S U) := (alphaPair hS2 α hα).1
  let χ₂ : ClassFunction (SemiProduct S U) := (alphaPair hS2 α hα).2
  have hχ₁ : IsIrreducibleCharacter χ₁ := alphaPair_irr₁ hS2 α hα
  have hχ₂ : IsIrreducibleCharacter χ₂ := alphaPair_irr₂ hS2 α hα
  have hne : χ₁ ≠ χ₂ := alphaPair_distinct hS2 α hα
  have hsum : alphaInduced (S := S) (U := U) α = χ₁ + χ₂ := alphaPair_sum hS2 α hα
  have hChiLam : IsIrreducibleCharacter (χ₁ * lambdaChar hS2) := by
    have h := isIrreducibleCharacter_mul_linear (lambdaChar_isLinear hS2) hχ₁
    convert h using 1
    funext g
    simp [Pi.mul_apply, lambdaChar]
    ring
  -- χ₁λ is a constituent of α^G; it cannot equal χ₁, so it equals χ₂
  have hne1 : χ₁ * lambdaChar hS2 ≠ χ₁ := by
    intro hEq
    have hzT : ∀ g : SemiProduct S U, g.right ≠ 1 → χ₁ g = 0 := by
      intro g hg
      have hLam : lambdaChar hS2 g = -1 := lambdaChar_apply_right_ne_one hS2 g hg
      have hz' := congrFun hEq g
      have hz'' : χ₁ g * (-1 : ℂ) = χ₁ g := by simpa [hLam] using hz'
      have : -(χ₁ g) = χ₁ g := by simpa using hz''
      have hsum' : χ₁ g + χ₁ g = 0 := by
        have hc : χ₁ g + -(χ₁ g) = 0 := add_neg_cancel (χ₁ g)
        rwa [this] at hc
      have htwo : (2 : ℂ) * χ₁ g = 0 := by simpa [two_mul] using hsum'
      exact (mul_eq_zero.mp htwo).resolve_left (by norm_num : (2 : ℂ) ≠ 0)
    have hspG : scalarProduct (SemiProduct S U) χ₁ χ₁ = 1 :=
      irreducible_scalarProduct_self hχ₁
    have hhalf : scalarProduct (SemiProduct S U) χ₁ χ₁ = (2 : ℂ)⁻¹ *
        scalarProduct (↥(USub S U))
          (fun x => χ₁ (x : SemiProduct S U))
          (fun x => χ₁ (x : SemiProduct S U)) := by
      refine scalarProduct_support_subgroup (USub S U) (USub_index hS2) χ₁ χ₁ ?_ ?_
      · intro g hg
        apply hzT
        intro h
        exact hg ((mem_USub_iff g).2 h)
      · intro g hg
        apply hzT
        intro h
        exact hg ((mem_USub_iff g).2 h)
    have hU : scalarProduct (↥(USub S U))
        (fun x => χ₁ (x : SemiProduct S U))
        (fun x => χ₁ (x : SemiProduct S U)) = 1 := by
      have hsp := scalarProduct_equiv_invariance (G := U) (H := ↥(USub S U))
        (usubEquiv S U) (fun x : ↥(USub S U) => χ₁ (x : SemiProduct S U))
        (fun x : ↥(USub S U) => χ₁ (x : SemiProduct S U))
      rw [hsp]
      have hφ : (fun u : U => χ₁ ((usubEquiv S U u : ↥(USub S U)) : SemiProduct S U)) = α.1 := by
        funext u
        simpa [usubEquiv] using
          (alphaInduced_restrict_constituent hS2 α hα hχ₁
            (by
              rw [hsum]
              rw [scalarProduct_add_right]
              simp [scalarProduct_irr_ite hχ₁ hχ₁, scalarProduct_irr_ite hχ₁ hχ₂, hne]
              ) u)
      rw [hφ]
      simpa using (scalarProduct_irr_ite α.2 α.2)
    have hhalf' : scalarProduct (SemiProduct S U) χ₁ χ₁ = (2 : ℂ)⁻¹ := by
      rw [hhalf, hU]
      norm_num
    have hone : (2 : ℂ)⁻¹ = 1 := by
      rw [← hhalf', hspG]
    norm_num at hone
  have hspLam : scalarProduct (SemiProduct S U) (χ₁ * lambdaChar hS2)
      (alphaInduced (S := S) (U := U) α) ≠ 0 := by
    have hsp : scalarProduct (SemiProduct S U) (χ₁ * lambdaChar hS2)
        (alphaInduced (S := S) (U := U) α) =
        scalarProduct (SemiProduct S U) χ₁ (alphaInduced (S := S) (U := U) α) := by
      rw [scalarProduct_mul_lambda]
      congr 1
      funext g
      exact congrFun (alphaInduced_mul_lambda hS2 α) g
    rw [hsp]
    rw [hsum]
    rw [scalarProduct_add_right]
    simp [scalarProduct_irr_ite hχ₁ hχ₁, scalarProduct_irr_ite hχ₁ hχ₂, hne]
  have hχ₂' : χ₁ * lambdaChar hS2 = χ₂ := by
    by_contra hne'
    have hz : scalarProduct (SemiProduct S U) (χ₁ * lambdaChar hS2)
        (alphaInduced (S := S) (U := U) α) = 0 := by
      rw [hsum]
      rw [scalarProduct_add_right]
      simp [scalarProduct_irr_ite hChiLam hχ₁, scalarProduct_irr_ite hChiLam hχ₂, hne1, hne']
    exact hspLam hz
  exact hχ₂'.symm

/-- The two constituents sum to zero outside `USub`. -/
public theorem alphaPair_sum_zero_of_right_ne_one (hS2 : Nat.card S = 2) (α : IrrBG19 U)
    (hα : FixedIrr S U α) (g : SemiProduct S U) (hg : g.right ≠ 1) :
    (alphaPair hS2 α hα).1 g + (alphaPair hS2 α hα).2 g = 0 := by
  rw [alphaPair₂_eq_mul_lambda hS2 α hα]
  have hLam : lambdaChar hS2 g = -1 := lambdaChar_apply_right_ne_one hS2 g hg
  simp [Pi.mul_apply, hLam]

/-- The difference of the two constituents of `α^G`. -/
public noncomputable def alphaDelta (hS2 : Nat.card S = 2) (α : IrrBG19 U) (hα : FixedIrr S U α) :
    ClassFunction (SemiProduct S U) :=
  (alphaPair hS2 α hα).1 - (alphaPair hS2 α hα).2

/-- `alphaDelta` is a generalized character. -/
public theorem alphaDelta_isGeneralizedCharacter (hS2 : Nat.card S = 2) (α : IrrBG19 U)
    (hα : FixedIrr S U α) :
    IsGeneralizedCharacter (alphaDelta hS2 α hα) := by
  refine ⟨(alphaPair hS2 α hα).1, (alphaPair hS2 α hα).2,
    isCharacter_of_isIrreducibleCharacter (alphaPair_irr₁ hS2 α hα),
    isCharacter_of_isIrreducibleCharacter (alphaPair_irr₂ hS2 α hα), ?_⟩
  rfl

/-- `alphaDelta` has scalar-product norm two. -/
public theorem alphaDelta_norm (hS2 : Nat.card S = 2) (α : IrrBG19 U) (hα : FixedIrr S U α) :
    scalarProduct (SemiProduct S U) (alphaDelta hS2 α hα) (alphaDelta hS2 α hα) = 2 := by
  classical
  let χ₁ : ClassFunction (SemiProduct S U) := (alphaPair hS2 α hα).1
  let χ₂ : ClassFunction (SemiProduct S U) := (alphaPair hS2 α hα).2
  have hχ₁ : IsIrreducibleCharacter χ₁ := alphaPair_irr₁ hS2 α hα
  have hχ₂ : IsIrreducibleCharacter χ₂ := alphaPair_irr₂ hS2 α hα
  have hne : χ₁ ≠ χ₂ := alphaPair_distinct hS2 α hα
  calc
    scalarProduct (SemiProduct S U) (alphaDelta hS2 α hα) (alphaDelta hS2 α hα)
        = scalarProduct (SemiProduct S U) (χ₁ - χ₂) (χ₁ - χ₂) := rfl
    _ = scalarProduct (SemiProduct S U) (χ₁ - χ₂) χ₁ -
          scalarProduct (SemiProduct S U) (χ₁ - χ₂) χ₂ := by
          rw [scalarProduct_sub_right]
    _ = (scalarProduct (SemiProduct S U) χ₁ χ₁ -
          scalarProduct (SemiProduct S U) χ₂ χ₁) -
          (scalarProduct (SemiProduct S U) χ₁ χ₂ -
            scalarProduct (SemiProduct S U) χ₂ χ₂) := by
          rw [scalarProduct_sub_left, scalarProduct_sub_left]
    _ = 2 := by
          simp [scalarProduct_irr_ite hχ₁ hχ₁, scalarProduct_irr_ite hχ₂ hχ₁,
            scalarProduct_irr_ite hχ₁ hχ₂, scalarProduct_irr_ite hχ₂ hχ₂, hne, hne.symm]
          norm_num

/-- `alphaDelta` vanishes on the `U`-part. -/
public theorem alphaDelta_apply_right_one (hS2 : Nat.card S = 2) (α : IrrBG19 U)
    (hα : FixedIrr S U α) (g : SemiProduct S U) (hg : g.right = 1) :
    alphaDelta hS2 α hα g = 0 := by
  have hEq₁ : (alphaPair hS2 α hα).1 g = α.1 g.left := by
    have hres : (alphaPair hS2 α hα).1 (SemidirectProduct.inl g.left) = α.1 g.left :=
      alphaInduced_restrict_constituent hS2 α hα (alphaPair_irr₁ hS2 α hα)
        (by
          rw [alphaPair_sum hS2 α hα]
          rw [scalarProduct_add_right]
          simp [scalarProduct_irr_ite (alphaPair_irr₁ hS2 α hα) (alphaPair_irr₁ hS2 α hα),
            scalarProduct_irr_ite (alphaPair_irr₁ hS2 α hα) (alphaPair_irr₂ hS2 α hα),
            alphaPair_distinct hS2 α hα]
          ) g.left
    have hgEq : g = SemidirectProduct.inl g.left := by
      apply SemidirectProduct.ext <;> simp [hg]
    rw [hgEq]
    exact hres
  have hEq₂ : (alphaPair hS2 α hα).2 g = α.1 g.left := by
    have hres : (alphaPair hS2 α hα).2 (SemidirectProduct.inl g.left) = α.1 g.left :=
      alphaInduced_restrict_constituent hS2 α hα (alphaPair_irr₂ hS2 α hα)
        (by
          rw [alphaPair_sum hS2 α hα]
          rw [scalarProduct_add_right]
          simp [scalarProduct_irr_ite (alphaPair_irr₂ hS2 α hα) (alphaPair_irr₁ hS2 α hα), scalarProduct_irr_ite (alphaPair_irr₂ hS2 α hα) (alphaPair_irr₂ hS2 α hα), (alphaPair_distinct hS2 α hα).symm]
          ) g.left
    have hgEq : g = SemidirectProduct.inl g.left := by
      apply SemidirectProduct.ext <;> simp [hg]
    rw [hgEq]
    exact hres
  simp [alphaDelta, hEq₁, hEq₂]

/-- `alphaDelta` vanishes on all of `USub`. -/
public theorem alphaDelta_apply_mem_USub (hS2 : Nat.card S = 2) (α : IrrBG19 U)
    (hα : FixedIrr S U α) (g : SemiProduct S U) (hg : g ∈ USub S U) :
    alphaDelta hS2 α hα g = 0 :=
  alphaDelta_apply_right_one hS2 α hα g ((mem_USub_iff g).1 hg)

end OrderTwoConstituents

section OrderTwoForward

variable {S U : Type u} [Group S] [Group U] [Fintype S] [Fintype U]
variable [MulDistribMulAction S U]

/-- A sum over a group of order two splits into the two elements. -/
public theorem sum_S_eq_two (hS2 : Nat.card S = 2) (f : S → ℂ) :
    (∑ s : S, f s) = f 1 + f (s2 hS2) := by
  classical
  have huniv : (Finset.univ : Finset S) = {1, s2 hS2} := by
    apply Finset.ext
    intro s
    constructor
    · intro hs
      rcases s_eq_one_or_s2 hS2 s with h | h
      · simp [h]
      · simp [h]
    · intro hs
      simpa using hs
  rw [huniv]
  simp [Finset.sum_insert, Finset.sum_singleton, (s2_ne_one hS2).symm]

/-- A sum over the irreducible characters of a group of order two splits. -/
public theorem sum_irrS_eq_two (hS2 : Nat.card S = 2) (f : IrrBG19 S → ℂ) :
    (∑ σ : IrrBG19 S, f σ) = f (oneIrr S) + f (sigIrr hS2) := by
  classical
  have huniv : (Finset.univ : Finset (IrrBG19 S)) = {oneIrr S, sigIrr hS2} := by
    apply Finset.ext
    intro σ
    constructor
    · intro hs
      rcases irrS_eq_one_or_sig hS2 σ with h | h
      · simp [h]
      · simp [h]
    · intro hs
      simpa using hs
  rw [huniv]
  simp [Finset.sum_insert, Finset.sum_singleton, oneIrr_ne_sigIrr hS2]

/-- The scalar product of a Fourier sum with a basis character is the
corresponding coefficient. -/
public theorem scalarProduct_fourier {B : Type u} [Group B] [Fintype B]
    (c : IrrBG19 B → ℂ) (γ₀ : IrrBG19 B) :
    scalarProduct B (fun b : B => ∑ γ : IrrBG19 B, c γ * γ.1 b) γ₀.1 = c γ₀ := by
  classical
  have hfun : (fun b : B => ∑ γ : IrrBG19 B, c γ * γ.1 b) =
      ∑ γ : IrrBG19 B, (c γ • γ.1) := by
    funext b
    rw [Finset.sum_apply]
    rfl
  rw [hfun]
  rw [scalarProduct_sum_left]
  simp_rw [scalarProduct_smul_left]
  rw [Finset.sum_eq_single γ₀]
  · simp [scalarProduct_irr_ite γ₀.2 γ₀.2]
  · intro γ hγ hne
    by_cases hEq : γ.1 = γ₀.1
    · exfalso
      exact hne (Subtype.ext hEq)
    · simp [scalarProduct_irr_ite γ.2 γ₀.2, hEq]
  · intro h
    exact (h (Finset.mem_univ γ₀)).elim

/-- The element `(b, 1)` of `H0 = S × B`. -/
public noncomputable def inlB (S : Type u) (U : Type u) [Group S] [Group U]
    [MulDistribMulAction S U] (b : ↥(fixedSubgroup S U)) : ↥(H0sub S U) :=
  ⟨h0Hom S U (b, 1), (mem_H0sub_iff S U (h0Hom S U (b, 1))).2 (by
    rw [h0Hom_apply]
    exact b.2)⟩

/-- The underlying semidirect-product element of `inlB b` is `(b, 1)`. -/
public theorem inlB_apply (S : Type u) (U : Type u) [Group S] [Group U]
    [MulDistribMulAction S U] (b : ↥(fixedSubgroup S U)) :
    (inlB S U b : SemiProduct S U) = ⟨(b : U), 1⟩ := by
  unfold inlB
  change (h0Hom S U (b, 1) : SemiProduct S U) = ⟨(b : U), 1⟩
  rw [h0Hom_apply]

/-- The sum over `H0 = S × B` splits into the two cosets of `B`. -/
public theorem sum_H0_split (hS2 : Nat.card S = 2) (f : ↥(H0sub S U) → ℂ) :
    (∑ h : ↥(H0sub S U), f h) =
      (∑ b : ↥(fixedSubgroup S U), f (inlB S U b)) +
      (∑ b : ↥(fixedSubgroup S U), f (tB hS2 b)) := by
  classical
  let hh : ↥(fixedSubgroup S U) × S → ↥(H0sub S U) := fun p =>
    ⟨h0Hom S U p, (mem_H0sub_iff S U (h0Hom S U p)).2 (by
      rw [h0Hom_apply]
      exact p.1.2)⟩
  have hsum1 : (∑ h : ↥(H0sub S U), f h) =
      ∑ p : ↥(fixedSubgroup S U) × S, f (hh p) := by
    exact Fintype.sum_equiv (H0equiv S U) (fun h => f h) (fun p => f (hh p)) (by
      intro x
      congr 1
      apply Subtype.ext
      symm
      change (h0Hom S U (H0equiv S U x) : SemiProduct S U) = (x : SemiProduct S U)
      rw [h0equiv_apply, h0Hom_apply])
  calc
    (∑ h : ↥(H0sub S U), f h) = ∑ p : ↥(fixedSubgroup S U) × S, f (hh p) := hsum1
    _ = ∑ b : ↥(fixedSubgroup S U), (f (hh (b, 1)) + f (hh (b, s2 hS2))) := by
          rw [Fintype.sum_prod_type]
          refine Finset.sum_congr rfl ?_
          intro b hb
          exact sum_S_eq_two hS2 (fun s => f (hh (b, s)))
    _ = (∑ b : ↥(fixedSubgroup S U), f (inlB S U b)) +
        (∑ b : ↥(fixedSubgroup S U), f (tB hS2 b)) := by
          rw [Finset.sum_add_distrib]
          congr 1

end OrderTwoForward

section OrderTwoForwardDefs

variable {S U : Type u} [Group S] [Group U] [Fintype S] [Fintype U]
variable [MulDistribMulAction S U]

/-- The twisted restriction `χ₁(t·)` of the first constituent of `α^G`. -/
public noncomputable def betaChar (hS2 : Nat.card S = 2) (α : IrrBG19 U) (hα : FixedIrr S U α) :
    ClassFunction (↥(fixedSubgroup S U)) :=
  fun b => (alphaPair hS2 α hα).1 (tB hS2 b)

/-- The coefficient of `1 ⊗ γ` in the restriction of `χ₁` to `H0`. -/
public noncomputable def coeffA (hS2 : Nat.card S = 2) (α : IrrBG19 U) (hα : FixedIrr S U α)
    (γ : IrrBG19 (↥(fixedSubgroup S U))) : ℂ :=
  scalarProduct (↥(H0sub S U))
    (fun x : ↥(H0sub S U) => (alphaPair hS2 α hα).1 (x : SemiProduct S U))
    ((h0IrrEquiv S U (oneIrr S, γ)).1)

/-- The coefficient of `sig ⊗ γ` in the restriction of `χ₁` to `H0`. -/
public noncomputable def coeffB (hS2 : Nat.card S = 2) (α : IrrBG19 U) (hα : FixedIrr S U α)
    (γ : IrrBG19 (↥(fixedSubgroup S U))) : ℂ :=
  scalarProduct (↥(H0sub S U))
    (fun x : ↥(H0sub S U) => (alphaPair hS2 α hα).1 (x : SemiProduct S U))
    ((h0IrrEquiv S U (sigIrr hS2, γ)).1)

end OrderTwoForwardDefs

section OrderTwoForwardCoeffs

variable {S U : Type u} [Group S] [Group U] [Fintype S] [Fintype U]
variable [MulDistribMulAction S U]

/-- The coefficient `coeffA` is a natural number. -/
public theorem coeffA_nat (hS2 : Nat.card S = 2) (α : IrrBG19 U) (hα : FixedIrr S U α)
    (γ : IrrBG19 (↥(fixedSubgroup S U))) : ∃ n : ℕ, (n : ℂ) = coeffA hS2 α hα γ := by
  classical
  let φ : ClassFunction (↥(H0sub S U)) :=
    fun x => (alphaPair hS2 α hα).1 (x : SemiProduct S U)
  let χ : ClassFunction (↥(H0sub S U)) := (h0IrrEquiv S U (oneIrr S, γ)).1
  have hχ : IsIrreducibleCharacter χ := (h0IrrEquiv S U (oneIrr S, γ)).2
  have hφchar : IsCharacter φ := isCharacter_restrict (H0sub S U)
    (isCharacter_of_isIrreducibleCharacter (alphaPair_irr₁ hS2 α hα))
  rcases scalarProduct_irr_char_nat (χ := χ) (ψ := φ) hχ hφchar with ⟨r, hr⟩
  refine ⟨r, ?_⟩
  calc
    (r : ℂ) = scalarProduct (↥(H0sub S U)) χ φ := hr
    _ = star (scalarProduct (↥(H0sub S U)) χ φ) := by
          rw [← hr]
          simp
    _ = scalarProduct (↥(H0sub S U)) φ χ := scalarProduct_conj χ φ

/-- The coefficient `coeffB` is a natural number. -/
public theorem coeffB_nat (hS2 : Nat.card S = 2) (α : IrrBG19 U) (hα : FixedIrr S U α)
    (γ : IrrBG19 (↥(fixedSubgroup S U))) : ∃ n : ℕ, (n : ℂ) = coeffB hS2 α hα γ := by
  classical
  let φ : ClassFunction (↥(H0sub S U)) :=
    fun x => (alphaPair hS2 α hα).1 (x : SemiProduct S U)
  let χ : ClassFunction (↥(H0sub S U)) := (h0IrrEquiv S U (sigIrr hS2, γ)).1
  have hχ : IsIrreducibleCharacter χ := (h0IrrEquiv S U (sigIrr hS2, γ)).2
  have hφchar : IsCharacter φ := isCharacter_restrict (H0sub S U)
    (isCharacter_of_isIrreducibleCharacter (alphaPair_irr₁ hS2 α hα))
  rcases scalarProduct_irr_char_nat (χ := χ) (ψ := φ) hχ hφchar with ⟨r, hr⟩
  refine ⟨r, ?_⟩
  calc
    (r : ℂ) = scalarProduct (↥(H0sub S U)) χ φ := hr
    _ = star (scalarProduct (↥(H0sub S U)) χ φ) := by
          rw [← hr]
          simp
    _ = scalarProduct (↥(H0sub S U)) φ χ := scalarProduct_conj χ φ

/-- `χ₂` agrees with `χ₁` on the `B`-part of `H0`. -/
public theorem chi₂_inlB_eq_chi₁ (hS2 : Nat.card S = 2) (α : IrrBG19 U) (hα : FixedIrr S U α)
    (b : ↥(fixedSubgroup S U)) :
    (alphaPair hS2 α hα).2 (inlB S U b : SemiProduct S U) =
      (alphaPair hS2 α hα).1 (inlB S U b : SemiProduct S U) := by
  rw [alphaPair₂_eq_mul_lambda hS2 α hα]
  simp [Pi.mul_apply, lambdaChar, lambdaHom, inlB_apply, sigHom]

/-- `χ₂` is the negative of `χ₁` on the `T`-part of `H0`. -/
public theorem chi₂_tB_eq_neg_chi₁ (hS2 : Nat.card S = 2) (α : IrrBG19 U) (hα : FixedIrr S U α)
    (b : ↥(fixedSubgroup S U)) :
    (alphaPair hS2 α hα).2 (tB hS2 b : SemiProduct S U) =
      - (alphaPair hS2 α hα).1 (tB hS2 b : SemiProduct S U) := by
  rw [alphaPair₂_eq_mul_lambda hS2 α hα]
  simp [Pi.mul_apply, lambdaChar, lambdaHom, tB_apply, sigHom, s2_ne_one hS2]

omit [Fintype U] in
/-- The value of `1 ⊗ γ` on the `B`-part of `H0`. -/
public theorem h0Char_one_inlB (hS2 : Nat.card S = 2) (γ : IrrBG19 (↥(fixedSubgroup S U)))
    (b : ↥(fixedSubgroup S U)) :
    h0Char S U (oneIrr S).1 γ.1 (inlB S U b) = γ.1 b := by
  unfold inlB
  simp [h0Char_apply, h0Hom_apply, oneIrr]

omit [Fintype U] in
/-- The value of `sig ⊗ γ` on the `B`-part of `H0`. -/
public theorem h0Char_sig_inlB (hS2 : Nat.card S = 2) (γ : IrrBG19 (↥(fixedSubgroup S U)))
    (b : ↥(fixedSubgroup S U)) :
    h0Char S U (sigIrr hS2).1 γ.1 (inlB S U b) = γ.1 b := by
  unfold inlB
  simp [h0Char_apply, h0Hom_apply, sigIrr, sigChar_apply_one]

omit [Fintype U] in
/-- The value of `1 ⊗ γ` on the `T`-part of `H0`. -/
public theorem h0Char_one_tB (hS2 : Nat.card S = 2) (γ : IrrBG19 (↥(fixedSubgroup S U)))
    (b : ↥(fixedSubgroup S U)) :
    h0Char S U (oneIrr S).1 γ.1 (tB hS2 b) = γ.1 b := by
  unfold tB
  simp [h0Char_apply, h0Hom_apply, oneIrr]

omit [Fintype U] in
/-- The value of `sig ⊗ γ` on the `T`-part of `H0`. -/
public theorem h0Char_sig_tB (hS2 : Nat.card S = 2) (γ : IrrBG19 (↥(fixedSubgroup S U)))
    (b : ↥(fixedSubgroup S U)) :
    h0Char S U (sigIrr hS2).1 γ.1 (tB hS2 b) = - γ.1 b := by
  unfold tB
  simp [h0Char_apply, h0Hom_apply, sigIrr, sigChar_apply_s2]

/-- The scalar product of the restriction of `χ₂` with `1 ⊗ γ` is the
coefficient `coeffB`. -/
public theorem coeffA_chi₂ (hS2 : Nat.card S = 2) (α : IrrBG19 U) (hα : FixedIrr S U α)
    (γ : IrrBG19 (↥(fixedSubgroup S U))) :
    scalarProduct (↥(H0sub S U))
      (fun x : ↥(H0sub S U) => (alphaPair hS2 α hα).2 (x : SemiProduct S U))
      ((h0IrrEquiv S U (oneIrr S, γ)).1) =
    coeffB hS2 α hα γ := by
  classical
  let χ₁ : ClassFunction (SemiProduct S U) := (alphaPair hS2 α hα).1
  let χ₂ : ClassFunction (SemiProduct S U) := (alphaPair hS2 α hα).2
  have hν : (h0IrrEquiv S U (oneIrr S, γ)).1 = h0Char S U (oneIrr S).1 γ.1 := by
    rw [h0IrrEquiv_apply]
  have hμ : (h0IrrEquiv S U (sigIrr hS2, γ)).1 = h0Char S U (sigIrr hS2).1 γ.1 := by
    rw [h0IrrEquiv_apply]
  unfold coeffB scalarProduct
  rw [hν, hμ]
  congr 1
  rw [sum_H0_split hS2 (fun x : ↥(H0sub S U) =>
    χ₂ (x : SemiProduct S U) * star (h0Char S U (oneIrr S).1 γ.1 x))]
  rw [sum_H0_split hS2 (fun x : ↥(H0sub S U) =>
    χ₁ (x : SemiProduct S U) * star (h0Char S U (sigIrr hS2).1 γ.1 x))]
  congr 1
  · refine Finset.sum_congr rfl ?_
    intro b hb
    change (alphaPair hS2 α hα).2 (inlB S U b : SemiProduct S U) *
        star (h0Char S U (oneIrr S).1 γ.1 (inlB S U b)) =
      (alphaPair hS2 α hα).1 (inlB S U b : SemiProduct S U) *
        star (h0Char S U (sigIrr hS2).1 γ.1 (inlB S U b))
    rw [chi₂_inlB_eq_chi₁ hS2 α hα b, h0Char_one_inlB hS2 γ b, h0Char_sig_inlB hS2 γ b]
  · refine Finset.sum_congr rfl ?_
    intro b hb
    change (alphaPair hS2 α hα).2 (tB hS2 b : SemiProduct S U) *
        star (h0Char S U (oneIrr S).1 γ.1 (tB hS2 b)) =
      (alphaPair hS2 α hα).1 (tB hS2 b : SemiProduct S U) *
        star (h0Char S U (sigIrr hS2).1 γ.1 (tB hS2 b))
    rw [chi₂_tB_eq_neg_chi₁ hS2 α hα b, h0Char_one_tB hS2 γ b, h0Char_sig_tB hS2 γ b]
    simp

/-- The scalar product of the restriction of `χ₂` with `sig ⊗ γ` is the
coefficient `coeffA`. -/
public theorem coeffB_chi₂ (hS2 : Nat.card S = 2) (α : IrrBG19 U) (hα : FixedIrr S U α)
    (γ : IrrBG19 (↥(fixedSubgroup S U))) :
    scalarProduct (↥(H0sub S U))
      (fun x : ↥(H0sub S U) => (alphaPair hS2 α hα).2 (x : SemiProduct S U))
      ((h0IrrEquiv S U (sigIrr hS2, γ)).1) =
    coeffA hS2 α hα γ := by
  classical
  let χ₁ : ClassFunction (SemiProduct S U) := (alphaPair hS2 α hα).1
  let χ₂ : ClassFunction (SemiProduct S U) := (alphaPair hS2 α hα).2
  have hν : (h0IrrEquiv S U (sigIrr hS2, γ)).1 = h0Char S U (sigIrr hS2).1 γ.1 := by
    rw [h0IrrEquiv_apply]
  have hμ : (h0IrrEquiv S U (oneIrr S, γ)).1 = h0Char S U (oneIrr S).1 γ.1 := by
    rw [h0IrrEquiv_apply]
  unfold coeffA scalarProduct
  rw [hν, hμ]
  congr 1
  rw [sum_H0_split hS2 (fun x : ↥(H0sub S U) =>
    χ₂ (x : SemiProduct S U) * star (h0Char S U (sigIrr hS2).1 γ.1 x))]
  rw [sum_H0_split hS2 (fun x : ↥(H0sub S U) =>
    χ₁ (x : SemiProduct S U) * star (h0Char S U (oneIrr S).1 γ.1 x))]
  congr 1
  · refine Finset.sum_congr rfl ?_
    intro b hb
    change (alphaPair hS2 α hα).2 (inlB S U b : SemiProduct S U) *
        star (h0Char S U (sigIrr hS2).1 γ.1 (inlB S U b)) =
      (alphaPair hS2 α hα).1 (inlB S U b : SemiProduct S U) *
        star (h0Char S U (oneIrr S).1 γ.1 (inlB S U b))
    rw [chi₂_inlB_eq_chi₁ hS2 α hα b, h0Char_sig_inlB hS2 γ b, h0Char_one_inlB hS2 γ b]
  · refine Finset.sum_congr rfl ?_
    intro b hb
    change (alphaPair hS2 α hα).2 (tB hS2 b : SemiProduct S U) *
        star (h0Char S U (sigIrr hS2).1 γ.1 (tB hS2 b)) =
      (alphaPair hS2 α hα).1 (tB hS2 b : SemiProduct S U) *
        star (h0Char S U (oneIrr S).1 γ.1 (tB hS2 b))
    rw [chi₂_tB_eq_neg_chi₁ hS2 α hα b, h0Char_sig_tB hS2 γ b, h0Char_one_tB hS2 γ b]
    simp

/-- The Fourier expansion of the twisted restriction `χ₁(t·)` of the first
constituent of `α^G`. -/
public theorem betaChar_fourier (hS2 : Nat.card S = 2) (α : IrrBG19 U) (hα : FixedIrr S U α)
    (b : ↥(fixedSubgroup S U)) :
    betaChar hS2 α hα b =
      ∑ γ : IrrBG19 (↥(fixedSubgroup S U)),
        (coeffA hS2 α hα γ - coeffB hS2 α hα γ) * γ.1 b := by
  classical
  let χ₁ : ClassFunction (SemiProduct S U) := (alphaPair hS2 α hα).1
  let χ₂ : ClassFunction (SemiProduct S U) := (alphaPair hS2 α hα).2
  have hχ₁ : IsIrreducibleCharacter χ₁ := alphaPair_irr₁ hS2 α hα
  have hχ₂ : IsIrreducibleCharacter χ₂ := alphaPair_irr₂ hS2 α hα
  let ψ : ClassFunction (↥(H0sub S U)) :=
    fun x => χ₁ (x : SemiProduct S U) - χ₂ (x : SemiProduct S U)
  have hψgen : IsGeneralizedCharacter ψ := by
    refine ⟨fun x => χ₁ (x : SemiProduct S U), fun x => χ₂ (x : SemiProduct S U), ?_, ?_, ?_⟩
    · exact isCharacter_restrict (H0sub S U) (isCharacter_of_isIrreducibleCharacter hχ₁)
    · exact isCharacter_restrict (H0sub S U) (isCharacter_of_isIrreducibleCharacter hχ₂)
    · rfl
  have hδ2 : 2 * betaChar hS2 α hα b = ψ (tB hS2 b) := by
    unfold ψ betaChar
    change 2 * (alphaPair hS2 α hα).1 (tB hS2 b) =
      (alphaPair hS2 α hα).1 (tB hS2 b) - (alphaPair hS2 α hα).2 (tB hS2 b)
    rw [chi₂_tB_eq_neg_chi₁ hS2 α hα b]
    ring
  have hspA : ∀ γ : IrrBG19 (↥(fixedSubgroup S U)),
      scalarProduct (↥(H0sub S U)) ψ (h0Char S U (oneIrr S).1 γ.1) =
        coeffA hS2 α hα γ - coeffB hS2 α hα γ := by
    intro γ
    have hν₁ : ((h0IrrEquiv S U (oneIrr S, γ)).1 : ClassFunction (↥(H0sub S U))) =
        h0Char S U (oneIrr S).1 γ.1 := by
      rw [h0IrrEquiv_apply]
    unfold ψ
    change scalarProduct (↥(H0sub S U))
      ((fun x : ↥(H0sub S U) => (alphaPair hS2 α hα).1 (x : SemiProduct S U)) -
        (fun x : ↥(H0sub S U) => (alphaPair hS2 α hα).2 (x : SemiProduct S U)))
      (h0Char S U (oneIrr S).1 γ.1) = coeffA hS2 α hα γ - coeffB hS2 α hα γ
    rw [scalarProduct_sub_left]
    rw [← hν₁]
    rw [coeffA_chi₂ hS2 α hα γ]
    rfl
  have hspB : ∀ γ : IrrBG19 (↥(fixedSubgroup S U)),
      scalarProduct (↥(H0sub S U)) ψ (h0Char S U (sigIrr hS2).1 γ.1) =
        coeffB hS2 α hα γ - coeffA hS2 α hα γ := by
    intro γ
    have hν₂ : ((h0IrrEquiv S U (sigIrr hS2, γ)).1 : ClassFunction (↥(H0sub S U))) =
        h0Char S U (sigIrr hS2).1 γ.1 := by
      rw [h0IrrEquiv_apply]
    unfold ψ
    change scalarProduct (↥(H0sub S U))
      ((fun x : ↥(H0sub S U) => (alphaPair hS2 α hα).1 (x : SemiProduct S U)) -
        (fun x : ↥(H0sub S U) => (alphaPair hS2 α hα).2 (x : SemiProduct S U)))
      (h0Char S U (sigIrr hS2).1 γ.1) = coeffB hS2 α hα γ - coeffA hS2 α hα γ
    rw [scalarProduct_sub_left]
    rw [← hν₂]
    rw [coeffB_chi₂ hS2 α hα γ]
    rfl
  have hfourier : ψ (tB hS2 b) =
      2 * (∑ γ : IrrBG19 (↥(fixedSubgroup S U)),
        (coeffA hS2 α hα γ - coeffB hS2 α hα γ) * γ.1 b) := by
    have hψval := classFunction_eq_sum_irr_coeffs (G := ↥(H0sub S U)) hψgen (tB hS2 b)
    rw [hψval]
    have hre : (∑ ν : IrrBG19 (↥(H0sub S U)),
          scalarProduct (↥(H0sub S U)) ψ ν.1 * ν.1 (tB hS2 b)) =
        ∑ p : IrrBG19 S × IrrBG19 (↥(fixedSubgroup S U)),
          scalarProduct (↥(H0sub S U)) ψ ((h0IrrEquiv S U p).1) *
            ((h0IrrEquiv S U p).1) (tB hS2 b) := by
      exact Fintype.sum_equiv (h0IrrEquiv S U).symm
        (fun ν => scalarProduct (↥(H0sub S U)) ψ ν.1 * ν.1 (tB hS2 b))
        (fun p => scalarProduct (↥(H0sub S U)) ψ ((h0IrrEquiv S U p).1) *
          ((h0IrrEquiv S U p).1) (tB hS2 b))
        (by intro ν; rw [Equiv.apply_symm_apply])
    rw [hre]
    rw [Fintype.sum_prod_type]
    rw [sum_irrS_eq_two hS2]
    rw [two_mul]
    congr 1
    · refine Finset.sum_congr rfl ?_
      intro γ hγ
      rw [h0IrrEquiv_apply]
      change scalarProduct (↥(H0sub S U)) ψ (h0Char S U (oneIrr S).1 γ.1) *
          h0Char S U (oneIrr S).1 γ.1 (tB hS2 b) = (coeffA hS2 α hα γ - coeffB hS2 α hα γ) * γ.1 b
      rw [h0Char_one_tB hS2 γ b, hspA]
    · refine Finset.sum_congr rfl ?_
      intro γ hγ
      rw [h0IrrEquiv_apply]
      change scalarProduct (↥(H0sub S U)) ψ (h0Char S U (sigIrr hS2).1 γ.1) *
          h0Char S U (sigIrr hS2).1 γ.1 (tB hS2 b) = (coeffA hS2 α hα γ - coeffB hS2 α hα γ) * γ.1 b
      rw [h0Char_sig_tB hS2 γ b, hspB]
      ring
  have h2 : 2 * betaChar hS2 α hα b =
      2 * (∑ γ : IrrBG19 (↥(fixedSubgroup S U)),
        (coeffA hS2 α hα γ - coeffB hS2 α hα γ) * γ.1 b) := by
    rw [hδ2, hfourier]
  exact (mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) h2)

end OrderTwoForwardCoeffs

section ScalarProductBessel

variable {G : Type u} [Group G] [Fintype G]

/-- A finite Bessel inequality for the project's scalar product: if the
vectors `w i` are pairwise orthogonal and each has scalar-product norm two,
then the squared projection coefficients of `v` on the `w i` satisfy
`∑ |(v,w i)|² / 2 ≤ (v,v)`. -/
public theorem scalarProduct_bessel_family {ι : Type u} [Fintype ι]
    (v : ClassFunction G) (w : ι → ClassFunction G)
    (hww : ∀ i, scalarProduct G (w i) (w i) = 2)
    (horth : ∀ i j, i ≠ j → scalarProduct G (w i) (w j) = 0) :
    ∃ r : ℝ, 0 ≤ r ∧
      (scalarProduct G v v -
          (∑ i, (scalarProduct G v (w i) * star (scalarProduct G v (w i))) / 2) =
        (r : ℂ)) := by
  classical
  let a : ι → ℂ := fun i => scalarProduct G v (w i) / 2
  let u : ClassFunction G := v - ∑ i, a i • w i
  have hsum1 : scalarProduct G (∑ i, a i • w i) v =
      ∑ i, a i * star (scalarProduct G v (w i)) := by
    rw [scalarProduct_sum_left]
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [scalarProduct_smul_left]
    rw [scalarProduct_conj]
  have hsum2 : scalarProduct G v (∑ i, a i • w i) =
      ∑ i, star (a i) * scalarProduct G v (w i) := by
    rw [scalarProduct_sum_right]
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [scalarProduct_smul_right]
    ring
  have hsum3 : scalarProduct G (∑ i, a i • w i) (∑ i, a i • w i) =
      ∑ i, a i * star (a i) * 2 := by
    classical
    calc
      scalarProduct G (∑ i, a i • w i) (∑ i, a i • w i)
          = ∑ i, ∑ j, scalarProduct G (a i • w i) (a j • w j) := by
              rw [scalarProduct_sum_left]
              congr 1
              funext i
              rw [scalarProduct_sum_right]
      _ = ∑ i, a i * star (a i) * 2 := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              rw [Finset.sum_eq_single i]
              · rw [scalarProduct_smul_left, scalarProduct_smul_right, hww i]
                ring
              · intro j hj hji
                rw [scalarProduct_smul_left, scalarProduct_smul_right, horth i j hji.symm]
                ring
              · intro hnot
                exact (hnot (Finset.mem_univ i)).elim
  have hspu : scalarProduct G u u =
      scalarProduct G v v -
        (∑ i, (scalarProduct G v (w i) * star (scalarProduct G v (w i))) / 2) := by
    unfold u
    rw [scalarProduct_sub_right]
    rw [scalarProduct_sub_left]
    rw [scalarProduct_sub_left]
    rw [hsum2, hsum1]
    rw [hsum3]
    -- `∑ aᵢ·star aᵢ·2 = ∑ (cᵢ·star cᵢ)/2` after subtracting
    -- `<S,v> + <v,S>`.
    have hcross : (∑ i, a i * star (scalarProduct G v (w i))) +
        (∑ i, star (a i) * scalarProduct G v (w i)) =
        ∑ i, scalarProduct G v (w i) * star (scalarProduct G v (w i)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro i hi
      dsimp [a]
      rw [map_div₀]
      have hstar2 : (starRingEnd ℂ) (2 : ℂ) = (2 : ℂ) := by
        simpa using (Complex.conj_ofNat 2)
      rw [hstar2]
      ring
    have hdiag : (∑ i, a i * star (a i) * 2) =
        ∑ i, scalarProduct G v (w i) * star (scalarProduct G v (w i)) / 2 := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      dsimp [a]
      rw [map_div₀]
      have hstar2 : (starRingEnd ℂ) (2 : ℂ) = (2 : ℂ) := by
        simpa using (Complex.conj_ofNat 2)
      rw [hstar2]
      ring
    calc
      scalarProduct G v v -
            (∑ i, a i * star (scalarProduct G v (w i))) -
            ((∑ i, star (a i) * scalarProduct G v (w i)) -
              (∑ i, a i * star (a i) * 2))
          = scalarProduct G v v -
              (∑ i, a i * star (scalarProduct G v (w i))) -
              (∑ i, star (a i) * scalarProduct G v (w i)) +
              (∑ i, a i * star (a i) * 2) := by ring
      _ = scalarProduct G v v -
              ((∑ i, a i * star (scalarProduct G v (w i))) +
                (∑ i, star (a i) * scalarProduct G v (w i))) +
              (∑ i, a i * star (a i) * 2) := by ring
      _ = scalarProduct G v v -
              (∑ i, scalarProduct G v (w i) * star (scalarProduct G v (w i))) +
              (∑ i, a i * star (a i) * 2) := by rw [hcross]
      _ = scalarProduct G v v -
              (∑ i, scalarProduct G v (w i) * star (scalarProduct G v (w i))) +
              (∑ i, scalarProduct G v (w i) * star (scalarProduct G v (w i)) / 2) := by rw [hdiag]
      _ = scalarProduct G v v -
              (∑ i, scalarProduct G v (w i) * star (scalarProduct G v (w i)) / 2) := by
              have hS : (∑ i, scalarProduct G v (w i) * star (scalarProduct G v (w i)) / 2) =
                  (∑ i, scalarProduct G v (w i) * star (scalarProduct G v (w i))) / 2 := by
                rw [Finset.sum_div]
              rw [hS]
              ring
  rcases scalarProduct_self_nonneg (φ := u) with ⟨r, hr0, hr⟩
  refine ⟨r, hr0, ?_⟩
  rw [hspu.symm, hr]

end ScalarProductBessel

section IntSquareHelper

/-- If the sum of the squares of the absolute values of integers is one, then
exactly one integer is `±1` and all others are zero. -/
public theorem int_sq_sum_eq_one {ι : Type u} [Fintype ι] (d : ι → ℤ)
    (hsum : (∑ i, ((d i).natAbs : ℕ) ^ 2) = 1) :
    ∃ i, (d i = 1 ∨ d i = -1) ∧ ∀ j, j ≠ i → d j = 0 := by
  classical
  have hne_sum : (∑ i, ((d i).natAbs : ℕ) ^ 2) ≠ 0 := by
    intro h
    rw [h] at hsum
    norm_num at hsum
  obtain ⟨i, hi, hnei⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ)
      (f := fun j => ((d j).natAbs : ℕ) ^ 2) hne_sum
  have hle_i : ((d i).natAbs : ℕ) ^ 2 ≤ 1 := by
    have h := Finset.single_le_sum (s := Finset.univ)
      (f := fun j => ((d j).natAbs : ℕ) ^ 2) (fun j hj => Nat.zero_le _) hi
    simpa [hsum] using h
  have hsq_i : ((d i).natAbs : ℕ) ^ 2 = 1 := by omega
  have hna_i : (d i).natAbs = 1 := by
    have hmul : (d i).natAbs * (d i).natAbs = 1 := by simpa [pow_two] using hsq_i
    have hcases : (d i).natAbs = 0 ∨ (d i).natAbs = 1 ∨ 2 ≤ (d i).natAbs := by omega
    rcases hcases with h0 | h1 | hge
    · rw [h0] at hmul
      norm_num at hmul
    · exact h1
    · have hge' : 4 ≤ (d i).natAbs * (d i).natAbs := by nlinarith
      rw [hmul] at hge'
      norm_num at hge'
  have hd_i : d i = 1 ∨ d i = -1 := by
    have h := (Int.natAbs_eq_natAbs_iff (a := d i) (b := 1)).1 (by simp [hna_i])
    simpa using h
  have hother : ∀ j, j ≠ i → d j = 0 := by
    intro j hji
    have hsplit := Finset.sum_erase_add (s := Finset.univ)
      (f := fun k => ((d k).natAbs : ℕ) ^ 2) (a := i) hi
    have hsum_erase : Finset.sum (Finset.univ.erase i)
        (fun k => ((d k).natAbs : ℕ) ^ 2) = 0 := by
      omega
    have hmemj : j ∈ Finset.univ.erase i := by simp [hji]
    have hle := Finset.single_le_sum (s := Finset.univ.erase i)
      (f := fun k => ((d k).natAbs : ℕ) ^ 2) (fun k hk => Nat.zero_le _) hmemj
    have htermj : ((d j).natAbs : ℕ) ^ 2 = 0 := by
      nlinarith [hsum_erase, hle]
    have hna_j : (d j).natAbs = 0 := by
      have hmul : (d j).natAbs * (d j).natAbs = 0 := by simpa [pow_two] using htermj
      by_contra hne
      have hge : 1 ≤ (d j).natAbs := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hne)
      have hge' : 1 ≤ (d j).natAbs * (d j).natAbs := by nlinarith
      rw [hmul] at hge'
      norm_num at hge'
    omega
  refine ⟨i, hd_i, ?_⟩
  intro j hji
  exact hother j hji

end IntSquareHelper

section ProjectionLemmas

variable {G : Type u} [Group G] [Fintype G]

/-- The scalar product is positive definite: zero norm forces the class
function to vanish. -/
public theorem scalarProduct_self_eq_zero (φ : ClassFunction G) :
    scalarProduct G φ φ = 0 → φ = 0 := by
  classical
  intro h
  funext g
  have hne : (Nat.card G : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := G)).ne'
  have h' : (∑ x : G, φ x * star (φ x)) = 0 := by
    have hm := congrArg (fun z : ℂ => (Nat.card G : ℂ) * z) h
    unfold scalarProduct at hm
    field_simp [hne] at hm
    simpa using hm
  have hsumC : ((∑ x : G, Complex.normSq (φ x) : ℝ) : ℂ) = 0 := by
    calc
      ((∑ x : G, Complex.normSq (φ x) : ℝ) : ℂ) =
          ∑ x : G, ((Complex.normSq (φ x) : ℝ) : ℂ) := by norm_num
      _ = ∑ x : G, φ x * star (φ x) := by
        refine Finset.sum_congr rfl ?_
        intro x hx
        simpa using (Complex.mul_conj (φ x)).symm
      _ = 0 := h'
  have hsumR : (∑ x : G, Complex.normSq (φ x) : ℝ) = 0 := by
    exact_mod_cast hsumC
  have hle := Finset.single_le_sum (s := Finset.univ)
      (f := fun x => Complex.normSq (φ x))
      (fun x hx => Complex.normSq_nonneg _) (Finset.mem_univ g)
  have hle' : Complex.normSq (φ g) ≤ 0 := by simpa [hsumR] using hle
  have hnorm : Complex.normSq (φ g) = 0 :=
    le_antisymm hle' (Complex.normSq_nonneg _)
  exact Complex.normSq_eq_zero.mp hnorm

/-- If `v` has norm two, `w` has norm two, and their scalar product has
norm-square four, then `v` is the projection of `w` onto the line of `w`
(with coefficient `c / 2`). -/
public theorem scalarProduct_span_eq_of_norm_eq (v w : ClassFunction G)
    (hvv : scalarProduct G v v = 2) (hww : scalarProduct G w w = 2)
    (c : ℂ) (hvw : scalarProduct G v w = c) (hc : c * star c = 4) :
    v = (c / 2) • w := by
  have hu : scalarProduct G (v - (c / 2) • w) (v - (c / 2) • w) = 0 := by
    rw [scalarProduct_sub_right]
    rw [scalarProduct_sub_left]
    rw [scalarProduct_sub_left]
    rw [scalarProduct_smul_left]
    rw [← scalarProduct_conj (φ := v) (ψ := w)]
    rw [hvw]
    rw [scalarProduct_smul_right]
    rw [hvw]
    rw [scalarProduct_smul_left]
    rw [scalarProduct_smul_right]
    rw [hww]
    have hc' : star (c / 2) = star c / 2 := by
      change (starRingEnd ℂ) (c / 2) = (starRingEnd ℂ) c / 2
      rw [map_div₀]
      have h2 : (starRingEnd ℂ) (2 : ℂ) = (2 : ℂ) := by
        simpa using (Complex.conj_ofNat 2)
      rw [h2]
    rw [hc']
    rw [hvv]
    field_simp [hc]
    rw [hc]
    ring
  exact sub_eq_zero.mp (scalarProduct_self_eq_zero (v - (c / 2) • w) hu)

end ProjectionLemmas

section OrderTwoCorrespondenceCore

variable {S U : Type u} [Group S] [Group U] [Fintype S] [Fintype U]
variable [MulDistribMulAction S U]

/-- Values of irreducible characters are algebraic integers. -/
public theorem irr_value_isIntegral {G : Type u} [Group G] [Fintype G]
    (χ : IrrBG19 G) (g : G) : IsIntegral ℤ (χ.1 g) := by
  rcases χ.2 with ⟨n, ρ, hρ, hχeq⟩
  rw [hχeq]
  exact character_value_isIntegral ρ g

/-- The Fourier coefficient `coeffA - coeffB` is an integer. -/
public theorem coeffDelta_int (hS2 : Nat.card S = 2) (α : IrrBG19 U) (hα : FixedIrr S U α)
    (γ : IrrBG19 (↥(fixedSubgroup S U))) :
    ∃ k : ℤ, (k : ℂ) = coeffA hS2 α hα γ - coeffB hS2 α hα γ := by
  rcases coeffA_nat hS2 α hα γ with ⟨a, ha⟩
  rcases coeffB_nat hS2 α hα γ with ⟨b, hb⟩
  refine ⟨(a : ℤ) - (b : ℤ), ?_⟩
  norm_num
  rw [ha, hb]

/-- The scalar product of `αΔ = χ₁ − χ₂` with `δ_γ*` is twice the Fourier
coefficient of `β_char` at `γ`. -/
public theorem scalarProduct_alphaDelta_deltaStar (hS2 : Nat.card S = 2)
    (α : IrrBG19 U) (hα : FixedIrr S U α)
    (γ : IrrBG19 (↥(fixedSubgroup S U))) :
    scalarProduct (SemiProduct S U) (alphaDelta hS2 α hα)
        (deltaStar S U hS2 γ) =
      2 * (coeffA hS2 α hα γ - coeffB hS2 α hα γ) := by
  classical
  let χ₁ : ClassFunction (SemiProduct S U) := (alphaPair hS2 α hα).1
  let χ₂ : ClassFunction (SemiProduct S U) := (alphaPair hS2 α hα).2
  have hχ₁ : IsIrreducibleCharacter χ₁ := alphaPair_irr₁ hS2 α hα
  have hχ₂ : IsIrreducibleCharacter χ₂ := alphaPair_irr₂ hS2 α hα
  have hgen : IsGeneralizedCharacter (alphaDelta hS2 α hα) :=
    alphaDelta_isGeneralizedCharacter hS2 α hα
  have hfr := scalarProduct_restrict_induced (G := SemiProduct S U) (H := H0sub S U)
    (χ := alphaDelta hS2 α hα)
    (isClassFunction_of_isGeneralizedCharacter hgen)
    (delta S U hS2 γ.1)
  have hsp1 : scalarProduct (↥(H0sub S U))
        (fun x : ↥(H0sub S U) => alphaDelta hS2 α hα (x : SemiProduct S U))
        (h0Char S U (oneIrr S).1 γ.1) =
      coeffA hS2 α hα γ - coeffB hS2 α hα γ := by
    have hν : ((h0IrrEquiv S U (oneIrr S, γ)).1 : ClassFunction (↥(H0sub S U))) =
        h0Char S U (oneIrr S).1 γ.1 := by
      rw [h0IrrEquiv_apply]
    change scalarProduct (↥(H0sub S U))
        ((fun x : ↥(H0sub S U) => χ₁ (x : SemiProduct S U)) -
          (fun x : ↥(H0sub S U) => χ₂ (x : SemiProduct S U)))
        (h0Char S U (oneIrr S).1 γ.1) = _
    rw [scalarProduct_sub_left]
    have hA : scalarProduct (↥(H0sub S U))
        (fun x : ↥(H0sub S U) => χ₁ (x : SemiProduct S U))
        (h0Char S U (oneIrr S).1 γ.1) = coeffA hS2 α hα γ := by
      unfold coeffA
      rw [← hν]
    have hB : scalarProduct (↥(H0sub S U))
        (fun x : ↥(H0sub S U) => χ₂ (x : SemiProduct S U))
        (h0Char S U (oneIrr S).1 γ.1) = coeffB hS2 α hα γ := by
      unfold coeffB
      rw [← hν]
      simpa [χ₂, coeffB] using (coeffA_chi₂ hS2 α hα γ)
    rw [hA, hB]
  have hsp2 : scalarProduct (↥(H0sub S U))
        (fun x : ↥(H0sub S U) => alphaDelta hS2 α hα (x : SemiProduct S U))
        (h0Char S U (sigIrr hS2).1 γ.1) =
      coeffB hS2 α hα γ - coeffA hS2 α hα γ := by
    have hν : ((h0IrrEquiv S U (sigIrr hS2, γ)).1 : ClassFunction (↥(H0sub S U))) =
        h0Char S U (sigIrr hS2).1 γ.1 := by
      rw [h0IrrEquiv_apply]
    change scalarProduct (↥(H0sub S U))
        ((fun x : ↥(H0sub S U) => χ₁ (x : SemiProduct S U)) -
          (fun x : ↥(H0sub S U) => χ₂ (x : SemiProduct S U)))
        (h0Char S U (sigIrr hS2).1 γ.1) = _
    rw [scalarProduct_sub_left]
    have hA : scalarProduct (↥(H0sub S U))
        (fun x : ↥(H0sub S U) => χ₁ (x : SemiProduct S U))
        (h0Char S U (sigIrr hS2).1 γ.1) = coeffB hS2 α hα γ := by
      unfold coeffB
      rw [← hν]
    have hB : scalarProduct (↥(H0sub S U))
        (fun x : ↥(H0sub S U) => χ₂ (x : SemiProduct S U))
        (h0Char S U (sigIrr hS2).1 γ.1) = coeffA hS2 α hα γ := by
      unfold coeffA
      rw [← hν]
      simpa [χ₂, coeffA] using (coeffB_chi₂ hS2 α hα γ)
    rw [hA, hB]
  calc
    scalarProduct (SemiProduct S U) (alphaDelta hS2 α hα) (deltaStar S U hS2 γ)
        = scalarProduct (↥(H0sub S U))
            (fun x : ↥(H0sub S U) => alphaDelta hS2 α hα (x : SemiProduct S U))
            (delta S U hS2 γ.1) := hfr.symm
    _ = scalarProduct (↥(H0sub S U))
            (fun x : ↥(H0sub S U) => alphaDelta hS2 α hα (x : SemiProduct S U))
            (h0Char S U (oneIrr S).1 γ.1 - h0Char S U (sigIrr hS2).1 γ.1) := rfl
    _ = (coeffA hS2 α hα γ - coeffB hS2 α hα γ) -
          (coeffB hS2 α hα γ - coeffA hS2 α hα γ) := by
          rw [scalarProduct_sub_right, hsp1, hsp2]
    _ = 2 * (coeffA hS2 α hα γ - coeffB hS2 α hα γ) := by ring

/-- `β_char(1) ≠ 0`: the twisted restriction is not the zero class function. -/
public theorem betaChar_one_ne_zero (hS2 : Nat.card S = 2) (hU2' : Nat.Coprime 2 (Nat.card U))
    (α : IrrBG19 U) (hα : FixedIrr S U α) :
    betaChar hS2 α hα (1 : ↥(fixedSubgroup S U)) ≠ 0 := by
  classical
  let χ₁ : ClassFunction (SemiProduct S U) := (alphaPair hS2 α hα).1
  have hχ₁ : IsIrreducibleCharacter χ₁ := alphaPair_irr₁ hS2 α hα
  have hspχ₁ : scalarProduct (SemiProduct S U) χ₁
      (alphaInduced (S := S) (U := U) α) ≠ 0 := by
    change scalarProduct (SemiProduct S U) (alphaPair hS2 α hα).1
        (alphaInduced (S := S) (U := U) α) ≠ 0
    rw [alphaPair_sum hS2 α hα]
    rw [scalarProduct_add_right]
    simp [scalarProduct_irr_ite (alphaPair_irr₁ hS2 α hα) (alphaPair_irr₁ hS2 α hα),
      scalarProduct_irr_ite (alphaPair_irr₁ hS2 α hα) (alphaPair_irr₂ hS2 α hα),
      alphaPair_distinct hS2 α hα]
  have hdeg : χ₁ 1 = α.1 1 := by
    have h := alphaInduced_restrict_constituent hS2 α hα hχ₁ hspχ₁ (1 : U)
    simpa using h
  have ht : IsInvolution (SemidirectProduct.inr (s2 hS2) : SemiProduct S U) := by
    constructor
    · intro h
      exact s2_ne_one hS2 (SemidirectProduct.inr_injective h)
    · change (SemidirectProduct.inr (s2 hS2) : SemiProduct S U) ^ 2 = 1
      rw [← map_pow, s2_sq hS2, map_one]
  have hcong := character_congr_mod_two_of_involution (G := SemiProduct S U)
    (isCharacter_of_isIrreducibleCharacter hχ₁) ht (by rw [mul_one, one_mul])
  have hcong1 : CongruentModTwo (χ₁ (SemidirectProduct.inr (s2 hS2))) (α.1 1) := by
    simpa [hdeg] using hcong
  have htB : (tB hS2 (1 : ↥(fixedSubgroup S U)) : SemiProduct S U) =
      SemidirectProduct.inr (s2 hS2) := by
    rw [tB_apply]
    apply SemidirectProduct.ext <;> simp
  rcases irr_degree_odd hU2' α with ⟨d, hd_odd, hd⟩
  intro hzero
  have hz : χ₁ (SemidirectProduct.inr (s2 hS2)) = 0 := by
    unfold betaChar at hzero
    rw [htB] at hzero
    change (alphaPair hS2 α hα).1 (SemidirectProduct.inr (s2 hS2)) = 0
    exact hzero
  have hbad : CongruentModTwo 0 (d : ℂ) := by
    simpa [hz, hd] using hcong1
  exact CongruentModTwo.not_zero_of_odd_nat hd_odd hbad

/-- In the order-two case every fixed irreducible `α` has a unique signed
irreducible constituent of the twisted restriction `β_char = χ₁(t·)`: the
correspondent of Lemma 1.9. -/
public theorem betaChar_unique_signed_coeff (hS2 : Nat.card S = 2)
    (hU2' : Nat.Coprime 2 (Nat.card U)) (α : IrrBG19 U) (hα : FixedIrr S U α) :
    ∃ γ : IrrBG19 (↥(fixedSubgroup S U)), ∃ d : ℤ, (d = 1 ∨ d = -1) ∧
      (∀ δ : IrrBG19 (↥(fixedSubgroup S U)),
        coeffA hS2 α hα δ - coeffB hS2 α hα δ = if δ = γ then (d : ℂ) else 0) ∧
      betaChar hS2 α hα = fun b => (d : ℂ) * γ.1 b := by
  classical
  let dF : IrrBG19 (↥(fixedSubgroup S U)) → ℤ := fun γ =>
    Classical.choose (coeffDelta_int hS2 α hα γ)
  have hdF : ∀ γ, (dF γ : ℂ) = coeffA hS2 α hα γ - coeffB hS2 α hα γ := fun γ =>
    Classical.choose_spec (coeffDelta_int hS2 α hα γ)
  have hstarD : ∀ γ, star ((dF γ : ℤ) : ℂ) = ((dF γ : ℤ) : ℂ) := by
    intro γ
    simpa using (Complex.conj_ofReal (dF γ : ℤ))
  rcases scalarProduct_bessel_family (G := SemiProduct S U)
      (v := alphaDelta hS2 α hα)
      (w := fun γ => deltaStar S U hS2 γ)
      (by intro γ; rw [deltaStar_pairing hS2 hU2' γ γ]; simp)
      (by intro γ δ hne; rw [deltaStar_pairing hS2 hU2' γ δ]; simp [hne])
    with ⟨r, hr0, hb⟩
  have hsum_sp : (∑ γ : IrrBG19 (↥(fixedSubgroup S U)),
        (scalarProduct (SemiProduct S U) (alphaDelta hS2 α hα)
            (deltaStar S U hS2 γ) * star (scalarProduct (SemiProduct S U)
              (alphaDelta hS2 α hα) (deltaStar S U hS2 γ))) / 2 : ℂ) =
      2 * (∑ γ : IrrBG19 (↥(fixedSubgroup S U)), ((dF γ : ℤ) : ℂ)^2) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr (M := ℂ) (s₁ := Finset.univ) (s₂ := Finset.univ)
      (f := fun γ : IrrBG19 (↥(fixedSubgroup S U)) =>
        (scalarProduct (SemiProduct S U) (alphaDelta hS2 α hα)
            (deltaStar S U hS2 γ) * star (scalarProduct (SemiProduct S U)
              (alphaDelta hS2 α hα) (deltaStar S U hS2 γ))) / 2)
      (g := fun γ : IrrBG19 (↥(fixedSubgroup S U)) => 2 * ((dF γ : ℤ) : ℂ)^2)
      rfl (by
      intro γ hγ
      rw [scalarProduct_alphaDelta_deltaStar hS2 α hα γ]
      simp only [← hdF γ]
      rw [star_mul]
      have hstar2 : star (2 : ℂ) = (2 : ℂ) := by
        simpa using (Complex.conj_ofNat 2)
      rw [hstar2, hstarD γ]
      ring)
  have hb' : (2 : ℂ) - 2 * (∑ γ : IrrBG19 (↥(fixedSubgroup S U)),
      ((dF γ : ℤ) : ℂ)^2) = (r : ℂ) := by
    rw [alphaDelta_norm hS2 α hα] at hb
    rw [hsum_sp] at hb
    simpa using hb
  let N : ℕ := ∑ γ : IrrBG19 (↥(fixedSubgroup S U)), ((dF γ).natAbs : ℕ)^2
  have hsq_term : ∀ γ : IrrBG19 (↥(fixedSubgroup S U)),
      (((((dF γ).natAbs : ℕ)^2 : ℕ) : ℂ)) = ((dF γ : ℤ) : ℂ)^2 := by
    intro γ
    by_cases h : 0 ≤ dF γ
    · have hnat : ((dF γ).natAbs : ℤ) = dF γ := by
        rw [Int.natAbs_of_nonneg h]
      have hnatC : (((dF γ).natAbs : ℕ) : ℂ) = ((dF γ : ℤ) : ℂ) := by
        simpa using (congrArg (fun z : ℤ => (z : ℂ)) hnat)
      rw [Nat.cast_pow, hnatC]
    · have hneg : dF γ < 0 := lt_of_not_ge h
      have hnat : ((dF γ).natAbs : ℤ) = - dF γ := by
        have hposneg : 0 ≤ - dF γ := le_of_lt (neg_pos.mpr hneg)
        rw [← Int.natAbs_neg, Int.natAbs_of_nonneg hposneg]
      have hnatC : (((dF γ).natAbs : ℕ) : ℂ) = ((- dF γ : ℤ) : ℂ) := by
        simpa using (congrArg (fun z : ℤ => (z : ℂ)) hnat)
      rw [Nat.cast_pow, hnatC]
      norm_num
  have hN : (N : ℂ) = ∑ γ : IrrBG19 (↥(fixedSubgroup S U)), ((dF γ : ℤ) : ℂ)^2 := by
    unfold N
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl ?_
    intro γ hγ
    exact hsq_term γ
  have hbR : (2 : ℝ) - 2 * (N : ℝ) = r := by
    have h := congrArg Complex.re hb'
    rw [← hN] at h
    simpa using h
  have hNle : N ≤ 1 := by
    have hNleR : (N : ℝ) ≤ 1 := by nlinarith [hr0, hbR]
    exact_mod_cast hNleR
  have hN0 : N ≠ 0 := by
    intro hN0
    have hd_all : ∀ γ, dF γ = 0 := by
      have hsum0 : (∑ γ : IrrBG19 (↥(fixedSubgroup S U)), ((dF γ).natAbs : ℕ)^2) = 0 := by
        simp [N, hN0]
      intro γ
      have hterm : ((dF γ).natAbs : ℕ)^2 = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg
          (fun _ _ => Nat.zero_le _)).1 hsum0 γ (Finset.mem_univ _)
      have hmul : (dF γ).natAbs * (dF γ).natAbs = 0 := by simpa [pow_two] using hterm
      by_contra hne
      have hna_ne : (dF γ).natAbs ≠ 0 := by omega
      have hge : 1 ≤ (dF γ).natAbs := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hna_ne)
      have hge' : 1 ≤ (dF γ).natAbs * (dF γ).natAbs := by nlinarith
      rw [hmul] at hge'
      norm_num at hge'
    have hb0 : betaChar hS2 α hα = 0 := by
      funext b
      rw [betaChar_fourier hS2 α hα b]
      simp [← hdF, hd_all]
    exact betaChar_one_ne_zero hS2 hU2' α hα (by simpa using congrFun hb0 (1 : ↥(fixedSubgroup S U)))
  have hN1 : N = 1 := by omega
  have hNsum : (∑ γ : IrrBG19 (↥(fixedSubgroup S U)), ((dF γ).natAbs : ℕ)^2) = 1 := by
    simp [N, hN1]
  rcases int_sq_sum_eq_one dF hNsum with ⟨γ, hdγ, hother⟩
  refine ⟨γ, dF γ, hdγ, ?_, ?_⟩
  · intro δ
    by_cases hδ : δ = γ
    · subst δ
      simp [hdF γ]
    · have h0 : dF δ = 0 := hother δ hδ
      have hcoeff : coeffA hS2 α hα δ - coeffB hS2 α hα δ = 0 := by
        rw [← hdF δ, h0]
        norm_num
      simp [hδ, hcoeff]
  · funext b
    rw [betaChar_fourier hS2 α hα b]
    rw [Finset.sum_eq_single γ]
    · rw [hdF γ]
    · intro δ hδ hne
      have h0 : dF δ = 0 := hother δ hne
      have hcoeff : coeffA hS2 α hα δ - coeffB hS2 α hα δ = 0 := by
        rw [← hdF δ, h0]
        norm_num
      rw [hcoeff]
      simp
    · intro hnot
      exact (hnot (Finset.mem_univ γ)).elim

/-- The order-two Glauberman correspondent of a fixed irreducible character. -/
public noncomputable def orderTwoCorr (hS2 : Nat.card S = 2)
    (hU2' : Nat.Coprime 2 (Nat.card U)) (α : IrrBG19 U) (hα : FixedIrr S U α) :
    IrrBG19 (↥(fixedSubgroup S U)) :=
  Classical.choose (betaChar_unique_signed_coeff hS2 hU2' α hα)

/-- The order-two correspondent is congruent to `α` on `B = C_U(S)`. -/
public theorem orderTwoCorr_congr (hS2 : Nat.card S = 2)
    (hU2' : Nat.Coprime 2 (Nat.card U)) (α : IrrBG19 U) (hα : FixedIrr S U α)
    (b : ↥(fixedSubgroup S U)) :
    CongruentModTwo (α.1 b) ((orderTwoCorr hS2 hU2' α hα).1 b) := by
  classical
  let γ := orderTwoCorr hS2 hU2' α hα
  have hspec := Classical.choose_spec (betaChar_unique_signed_coeff hS2 hU2' α hα)
  rcases hspec with ⟨d, hd, hcoeff, hbeta⟩
  have hspχ₁ : scalarProduct (SemiProduct S U) (alphaPair hS2 α hα).1
      (alphaInduced (S := S) (U := U) α) ≠ 0 := by
    rw [alphaPair_sum hS2 α hα]
    rw [scalarProduct_add_right]
    simp [scalarProduct_irr_ite (alphaPair_irr₁ hS2 α hα) (alphaPair_irr₁ hS2 α hα),
      scalarProduct_irr_ite (alphaPair_irr₁ hS2 α hα) (alphaPair_irr₂ hS2 α hα),
      alphaPair_distinct hS2 α hα]
  have hχ₁u : ∀ u : U, (alphaPair hS2 α hα).1 (SemidirectProduct.inl u) = α.1 u :=
    alphaInduced_restrict_constituent hS2 α hα (alphaPair_irr₁ hS2 α hα) hspχ₁
  have hbfix : (s2 hS2) • (b : U) = b := (mem_fixedSubgroup_iff S U (b : U)).1 b.2 (s2 hS2)
  let t : SemiProduct S U := SemidirectProduct.inr (s2 hS2)
  let u : SemiProduct S U := SemidirectProduct.inl (b : U)
  have ht : IsInvolution t := by
    dsimp [t]
    constructor
    · intro h
      exact s2_ne_one hS2 (SemidirectProduct.inr_injective h)
    · change (SemidirectProduct.inr (s2 hS2) : SemiProduct S U) ^ 2 = 1
      rw [← map_pow, s2_sq hS2, map_one]
  have hcomm : t * u = u * t := by
    dsimp [t, u]
    apply SemidirectProduct.ext <;> simp [hbfix]
  have hodd : Odd (orderOf u) := by
    dsimp [u]
    exact USub_odd_order hU2' (by simp [mem_USub_iff])
  have hcop : Nat.Coprime 2 (orderOf u) := (Nat.coprime_two_left).2 hodd
  have hχ₁gen : IsGeneralizedCharacter (alphaPair hS2 α hα).1 :=
    ⟨(alphaPair hS2 α hα).1, 0,
      isCharacter_of_isIrreducibleCharacter (alphaPair_irr₁ hS2 α hα),
      isCharacter_zero, by ext x; simp⟩
  have hu : u ∈ centralizerIn (⊤ : Subgroup (SemiProduct S U)) t := by
    simp [centralizerIn, Subgroup.mem_centralizer_iff, hcomm]
  have h16 := lemma_1_6 (G := SemiProduct S U)
    ((alphaPair hS2 α hα).1) hχ₁gen ht hu hcop
  have htu : t * u = (tB hS2 b : SemiProduct S U) := by
    rw [tB_apply]
    dsimp [t, u]
    apply SemidirectProduct.ext <;> simp [hbfix]
  have hφu : (alphaPair hS2 α hα).1 u = α.1 b := by
    dsimp [u]
    exact hχ₁u (b : U)
  have hφtu : (alphaPair hS2 α hα).1 (t * u) = betaChar hS2 α hα b := by
    rw [htu]
    rfl
  have hαβ : CongruentModTwo (betaChar hS2 α hα b) (α.1 b) := by
    simpa [hφu, hφtu] using h16
  have hβγ : CongruentModTwo (betaChar hS2 α hα b) (γ.1 b) := by
    rw [hbeta]
    change CongruentModTwo ((d : ℂ) * γ.1 b) (γ.1 b)
    rcases hd with h1 | hneg
    · subst d
      simpa using (CongruentModTwo.refl (γ.1 b))
    · subst d
      refine ⟨-(γ.1 b), (irr_value_isIntegral γ b).neg, ?_⟩
      simp
      ring
  exact CongruentModTwo.trans (CongruentModTwo.symm hαβ) hβγ

/-- The order-two correspondence is injective. -/
public theorem orderTwoCorr_injective (hS2 : Nat.card S = 2)
    (hU2' : Nat.Coprime 2 (Nat.card U)) :
    Function.Injective (fun α : {α : IrrBG19 U // FixedIrr S U α} =>
      orderTwoCorr hS2 hU2' α.1 α.2) := by
  classical
  intro α α' hEq
  let γ : IrrBG19 (↥(fixedSubgroup S U)) := orderTwoCorr hS2 hU2' α.1 α.2
  have hγ' : orderTwoCorr hS2 hU2' α'.1 α'.2 = γ := by
    simpa [γ] using hEq.symm
  have hspec := Classical.choose_spec (betaChar_unique_signed_coeff hS2 hU2' α.1 α.2)
  rcases hspec with ⟨d, hd, hcoeff, hbeta⟩
  have hspec' := Classical.choose_spec (betaChar_unique_signed_coeff hS2 hU2' α'.1 α'.2)
  rcases hspec' with ⟨d', hd', hcoeff', hbeta'⟩
  have hc_d : (d : ℂ) = 1 ∨ (d : ℂ) = -1 := by
    rcases hd with h1 | hneg
    · left; rw [h1]; norm_num
    · right; rw [hneg]; norm_num
  have hc_d' : (d' : ℂ) = 1 ∨ (d' : ℂ) = -1 := by
    rcases hd' with h1 | hneg
    · left; rw [h1]; norm_num
    · right; rw [hneg]; norm_num
  have hproj : alphaDelta hS2 α.1 α.2 = (d : ℂ) • deltaStar S U hS2 γ := by
    have hvw : scalarProduct (SemiProduct S U) (alphaDelta hS2 α.1 α.2)
        (deltaStar S U hS2 γ) = 2 * (d : ℂ) := by
      have hγdef : γ = Classical.choose (betaChar_unique_signed_coeff hS2 hU2' α.1 α.2) := rfl
      rw [scalarProduct_alphaDelta_deltaStar hS2 α.1 α.2 γ]
      rw [hcoeff γ, hγdef, if_pos rfl]
    have hc : (2 * (d : ℂ)) * star (2 * (d : ℂ)) = 4 := by
      rcases hc_d with h1 | hneg
      · rw [h1]
        norm_num
      · rw [hneg]
        norm_num
    have hproj0 := scalarProduct_span_eq_of_norm_eq (G := SemiProduct S U)
      (alphaDelta hS2 α.1 α.2) (deltaStar S U hS2 γ)
      (alphaDelta_norm hS2 α.1 α.2)
      (by rw [deltaStar_pairing hS2 hU2' γ γ]; simp)
      (2 * (d : ℂ)) hvw hc
    have hcoef : (2 * (d : ℂ)) / 2 = (d : ℂ) := by ring
    simpa [hcoef] using hproj0
  have hproj' : alphaDelta hS2 α'.1 α'.2 = (d' : ℂ) • deltaStar S U hS2 γ := by
    have hvw : scalarProduct (SemiProduct S U) (alphaDelta hS2 α'.1 α'.2)
        (deltaStar S U hS2 γ) = 2 * (d' : ℂ) := by
      have hγdef : γ = Classical.choose (betaChar_unique_signed_coeff hS2 hU2' α'.1 α'.2) := hγ'.symm
      rw [scalarProduct_alphaDelta_deltaStar hS2 α'.1 α'.2 γ]
      rw [hcoeff' γ, hγdef, if_pos rfl]
    have hc : (2 * (d' : ℂ)) * star (2 * (d' : ℂ)) = 4 := by
      rcases hc_d' with h1 | hneg
      · rw [h1]
        norm_num
      · rw [hneg]
        norm_num
    have hproj0 := scalarProduct_span_eq_of_norm_eq (G := SemiProduct S U)
      (alphaDelta hS2 α'.1 α'.2) (deltaStar S U hS2 γ)
      (alphaDelta_norm hS2 α'.1 α'.2)
      (by rw [deltaStar_pairing hS2 hU2' γ γ]; simp)
      (2 * (d' : ℂ)) hvw hc
    have hcoef : (2 * (d' : ℂ)) / 2 = (d' : ℂ) := by ring
    simpa [hcoef] using hproj0
  have hEqDelta : alphaDelta hS2 α.1 α.2 = alphaDelta hS2 α'.1 α'.2 ∨
      alphaDelta hS2 α.1 α.2 = - alphaDelta hS2 α'.1 α'.2 := by
    rw [hproj, hproj']
    rcases hc_d with h1 | hneg
    · rcases hc_d' with h1' | hneg'
      · left
        rw [h1, h1']
      · right
        rw [h1, hneg']
        simp
    · rcases hc_d' with h1' | hneg'
      · right
        rw [hneg, h1']
        simp
      · left
        rw [hneg, hneg']
  let χ₁ : ClassFunction (SemiProduct S U) := (alphaPair hS2 α.1 α.2).1
  let χ₁' : ClassFunction (SemiProduct S U) := (alphaPair hS2 α'.1 α'.2).1
  let χ₂' : ClassFunction (SemiProduct S U) := (alphaPair hS2 α'.1 α'.2).2
  have hχ₁ : IsIrreducibleCharacter χ₁ := alphaPair_irr₁ hS2 α.1 α.2
  have hχ₁' : IsIrreducibleCharacter χ₁' := alphaPair_irr₁ hS2 α'.1 α'.2
  have hχ₂' : IsIrreducibleCharacter χ₂' := alphaPair_irr₂ hS2 α'.1 α'.2
  have hspαΔ : scalarProduct (SemiProduct S U) χ₁ (alphaDelta hS2 α.1 α.2) = 1 := by
    change scalarProduct (SemiProduct S U) (alphaPair hS2 α.1 α.2).1
        ((alphaPair hS2 α.1 α.2).1 - (alphaPair hS2 α.1 α.2).2) = 1
    rw [scalarProduct_sub_right]
    simp [scalarProduct_irr_ite (alphaPair_irr₁ hS2 α.1 α.2) (alphaPair_irr₁ hS2 α.1 α.2),
      scalarProduct_irr_ite (alphaPair_irr₁ hS2 α.1 α.2) (alphaPair_irr₂ hS2 α.1 α.2),
      alphaPair_distinct hS2 α.1 α.2]
  have hspχ₁α' : scalarProduct (SemiProduct S U) χ₁ (alphaDelta hS2 α'.1 α'.2) ≠ 0 := by
    rcases hEqDelta with hEq | hEq
    · rw [← hEq]
      rw [hspαΔ]
      norm_num
    · have hEq' : alphaDelta hS2 α'.1 α'.2 = - alphaDelta hS2 α.1 α.2 := by
        rw [hEq]
        simp
      rw [hEq']
      rw [scalarProduct_neg_right]
      rw [hspαΔ]
      norm_num
  have hsp1 : scalarProduct (SemiProduct S U) χ₁ χ₁' =
      if χ₁ = χ₁' then 1 else 0 := scalarProduct_irr_ite hχ₁ hχ₁'
  have hsp2 : scalarProduct (SemiProduct S U) χ₁ χ₂' =
      if χ₁ = χ₂' then 1 else 0 := scalarProduct_irr_ite hχ₁ hχ₂'
  have hmem : χ₁ = χ₁' ∨ χ₁ = χ₂' := by
    by_contra hnone
    have hne1 : χ₁ ≠ χ₁' := by intro h; exact hnone (Or.inl h)
    have hne2 : χ₁ ≠ χ₂' := by intro h; exact hnone (Or.inr h)
    have hz : scalarProduct (SemiProduct S U) χ₁ (alphaDelta hS2 α'.1 α'.2) = 0 := by
      change scalarProduct (SemiProduct S U) χ₁
          ((alphaPair hS2 α'.1 α'.2).1 - (alphaPair hS2 α'.1 α'.2).2) = 0
      rw [scalarProduct_sub_right, hsp1, hsp2, if_neg hne1, if_neg hne2]
      norm_num
    exact hspχ₁α' hz
  ext u
  have hαu : χ₁ (SemidirectProduct.inl u) = (α.1 : ClassFunction U) u :=
    alphaInduced_restrict_constituent hS2 α.1 α.2 hχ₁
      (by
        change scalarProduct (SemiProduct S U) (alphaPair hS2 α.1 α.2).1
            (alphaInduced (S := S) (U := U) α.1) ≠ 0
        rw [alphaPair_sum hS2 α.1 α.2]
        rw [scalarProduct_add_right]
        simp [scalarProduct_irr_ite (alphaPair_irr₁ hS2 α.1 α.2) (alphaPair_irr₁ hS2 α.1 α.2),
          scalarProduct_irr_ite (alphaPair_irr₁ hS2 α.1 α.2) (alphaPair_irr₂ hS2 α.1 α.2),
          alphaPair_distinct hS2 α.1 α.2]) u
  rcases hmem with hEqχ | hEqχ
  · have hα'u : χ₁' (SemidirectProduct.inl u) = (α'.1 : ClassFunction U) u :=
      alphaInduced_restrict_constituent hS2 α'.1 α'.2 hχ₁'
        (by
          change scalarProduct (SemiProduct S U) (alphaPair hS2 α'.1 α'.2).1
              (alphaInduced (S := S) (U := U) α'.1) ≠ 0
          rw [alphaPair_sum hS2 α'.1 α'.2]
          rw [scalarProduct_add_right]
          simp [scalarProduct_irr_ite (alphaPair_irr₁ hS2 α'.1 α'.2) (alphaPair_irr₁ hS2 α'.1 α'.2),
            scalarProduct_irr_ite (alphaPair_irr₁ hS2 α'.1 α'.2) (alphaPair_irr₂ hS2 α'.1 α'.2),
            alphaPair_distinct hS2 α'.1 α'.2]) u
    calc
      (α.1 : ClassFunction U) u = χ₁ (SemidirectProduct.inl u) := hαu.symm
      _ = χ₁' (SemidirectProduct.inl u) := by rw [hEqχ]
      _ = (α'.1 : ClassFunction U) u := hα'u
  · have hα'u : χ₂' (SemidirectProduct.inl u) = (α'.1 : ClassFunction U) u :=
      alphaInduced_restrict_constituent hS2 α'.1 α'.2 hχ₂'
        (by
          change scalarProduct (SemiProduct S U) (alphaPair hS2 α'.1 α'.2).2
              (alphaInduced (S := S) (U := U) α'.1) ≠ 0
          rw [alphaPair_sum hS2 α'.1 α'.2]
          rw [scalarProduct_add_right]
          simp [scalarProduct_irr_ite (alphaPair_irr₂ hS2 α'.1 α'.2) (alphaPair_irr₁ hS2 α'.1 α'.2), scalarProduct_irr_ite (alphaPair_irr₂ hS2 α'.1 α'.2) (alphaPair_irr₂ hS2 α'.1 α'.2), (alphaPair_distinct hS2 α'.1 α'.2).symm]) u
    calc
      (α.1 : ClassFunction U) u = χ₁ (SemidirectProduct.inl u) := hαu.symm
      _ = χ₂' (SemidirectProduct.inl u) := by rw [hEqχ]
      _ = (α'.1 : ClassFunction U) u := hα'u

end OrderTwoCorrespondenceCore

section ConjClassBridge

variable {G : Type u} [Group G] [Fintype G]

/-- Irreducible characters are in bijection with irreducible class functions
on conjugacy classes. -/
public noncomputable def irrConjEquiv (G : Type u) [Group G] [Fintype G] :
    IrrBG19 G ≃ {χ : ConjClassFunction G // IsIrreducibleConjCharacter χ} where
  toFun α := ⟨toConjClassFunction α.1 (irreducibleCharacter_isClassFunction α.2),
    isIrreducibleConjCharacter_of_isIrreducibleCharacterBG19 α.2⟩
  invFun χ := ⟨ofConjClassFunction χ.1, isIrreducibleCharacter_ofConjClassFunctionBG19 χ.2⟩
  left_inv α := by
    apply Subtype.ext
    funext g
    simp [ofConjClassFunction, toConjClassFunction_apply]
  right_inv χ := by
    apply Subtype.ext
    ext c
    rcases ConjClasses.exists_rep c with ⟨g, rfl⟩
    simp [ofConjClassFunction, toConjClassFunction_apply]

variable {S U : Type u} [Group S] [Group U] [Fintype S] [Fintype U]
variable [MulDistribMulAction S U]

/-- The action of the non-trivial element of `S` on the irreducible characters
of `U` (in the order-two case). -/
public noncomputable def irrS2Action (hS2 : Nat.card S = 2) (α : IrrBG19 U) : IrrBG19 U :=
  ⟨fun u => α.1 ((s2 hS2) • u),
    isIrreducibleCharacter_congr (MulDistribMulAction.toMulEquiv (M := U) (G := S) (s2 hS2)) α.2⟩

omit [Fintype S] in
/-- In the order-two case, an irreducible character is fixed by the whole
action exactly when it is fixed by the non-trivial element. -/
public theorem FixedIrr_iff_irrS2Action (hS2 : Nat.card S = 2) (α : IrrBG19 U) :
    FixedIrr S U α ↔ irrS2Action hS2 α = α := by
  constructor
  · intro hα
    apply Subtype.ext
    simpa [irrS2Action] using hα (s2 hS2)
  · intro hEq s
    funext u
    rcases s_eq_one_or_s2 hS2 s with hs | hs
    · subst hs
      simp
    · subst hs
      simpa [irrS2Action] using congrFun (congrArg Subtype.val hEq) u

/-- Transport an irreducible character of `U` to the normal copy `USub`. -/
public noncomputable def irrUSubOfU (α : IrrBG19 U) : IrrBG19 (↥(USub S U)) :=
  ⟨fun x => α.1 x.1.left,
    by
      change IsIrreducibleCharacter (fun x : ↥(USub S U) => α.1 ((usubEquiv S U).symm x))
      exact isIrreducibleCharacter_congr (usubEquiv S U).symm α.2⟩

/-- Transport an irreducible character of `USub` back to `U`. -/
public noncomputable def irrUOfUSub (α : IrrBG19 (↥(USub S U))) : IrrBG19 U :=
  ⟨fun u => α.1 (usubEquiv S U u),
    by
      change IsIrreducibleCharacter (fun u : U => α.1 (usubEquiv S U u))
      exact isIrreducibleCharacter_congr (usubEquiv S U) α.2⟩

omit [Fintype S] [Fintype U] in
/-- Conjugation by `inr s` moves an element of `USub` by `s⁻¹` on the left
component. -/
public theorem inr_inv_mul_USub_mul_inr (s : S) (x : ↥(USub S U)) :
    (SemidirectProduct.inr s : SemiProduct S U)⁻¹ * (x : SemiProduct S U) *
        SemidirectProduct.inr s =
      SemidirectProduct.inl (s⁻¹ • x.1.left) := by
  apply SemidirectProduct.ext
  · simp [SemidirectProduct.mul_left, SemidirectProduct.mul_right, SemidirectProduct.inv_right]
  · have hxr : (x : SemiProduct S U).right = 1 :=
      (mem_USub_iff (S := S) (U := U) (x : SemiProduct S U)).1 x.2
    simp [SemidirectProduct.mul_right, SemidirectProduct.inv_right, hxr]

/-- The action on `USub` induced by conjugation with the non-trivial element. -/
public noncomputable def irrUSubS2Action (hS2 : Nat.card S = 2)
    (α : IrrBG19 (↥(USub S U))) : IrrBG19 (↥(USub S U)) :=
  irrUSubOfU (irrS2Action hS2 (irrUOfUSub α))

/-- If `α` is fixed by `S`, its transfer to `USub` is fixed by the induced
order-two action. -/
public theorem irrUSubS2Action_fixed_of_FixedIrr (hS2 : Nat.card S = 2)
    (α : IrrBG19 U) (hα : FixedIrr S U α) :
    irrUSubS2Action hS2 (irrUSubOfU α) = irrUSubOfU α := by
  apply Subtype.ext
  funext x
  simp [irrUSubS2Action, irrS2Action, irrUOfUSub, irrUSubOfU]
  exact congrFun (hα (s2 hS2)) x.1.left

set_option backward.isDefEq.respectTransparency false in
/-- If the transfer of `α` is fixed by the induced order-two action, then `α`
is fixed by the whole action. -/
public theorem FixedIrr_of_irrUSubS2Action_fixed (hS2 : Nat.card S = 2)
    (α : IrrBG19 U) (hα : irrUSubS2Action hS2 (irrUSubOfU α) = irrUSubOfU α) :
    FixedIrr S U α := by
  rw [FixedIrr_iff_irrS2Action hS2 α]
  apply Subtype.ext
  funext u
  have h := congrFun (congrArg Subtype.val hα) (usubEquiv S U u)
  simpa [irrUSubS2Action, irrS2Action, irrUOfUSub, irrUSubOfU, usubEquiv] using h

/-- Transferring to `USub` and back is the identity. -/
public theorem irrUSubOfU_irrUOfUSub (x : IrrBG19 (↥(USub S U))) :
    irrUSubOfU (S := S) (U := U) (irrUOfUSub (S := S) (U := U) x) = x := by
  apply Subtype.ext
  funext y
  apply congrArg x.1
  apply Subtype.ext
  apply SemidirectProduct.ext
  · rfl
  · exact y.2.symm

/-- Transferring from `USub` to `U` and back is the identity. -/
public theorem irrUOfUSub_irrUSubOfU (α : IrrBG19 U) :
    irrUOfUSub (S := S) (U := U) (irrUSubOfU (S := S) (U := U) α) = α := by
  apply Subtype.ext
  funext u
  rfl

/-- The Brauer permutation on irreducible class functions agrees with the
explicit `S`-action on irreducible characters of `U`. -/
public theorem irrConjEquiv_perm (hS2 : Nat.card S = 2)
    (α : IrrBG19 (↥(USub S U))) :
    irreducibleConjClassFunctionPerm (USub S U) (SemidirectProduct.inr (s2 hS2))
        (irrConjEquiv (↥(USub S U)) α) =
      irrConjEquiv (↥(USub S U)) (irrUSubS2Action hS2 α) := by
  apply Subtype.ext
  ext c
  rcases ConjClasses.exists_rep c with ⟨y, rfl⟩
  simp [irrConjEquiv, irreducibleConjClassFunctionPerm, classFunctionConjLinearEquiv, conjClassesConjPerm_symm_mk, toConjClassFunction_apply, irrUSubS2Action, irrS2Action, irrUOfUSub, irrUSubOfU]
  have hinv : (s2 hS2)⁻¹ = s2 hS2 := by
    apply inv_eq_of_mul_eq_one_right
    simpa [pow_two] using s2_sq hS2
  have harg : (normalSubgroupConjMulEquiv (USub S U) (SemidirectProduct.inr (s2 hS2))).symm y =
      (⟨SemidirectProduct.inl (s2 hS2 • (y : SemiProduct S U).left),
        by simp [mem_USub_iff]⟩ : ↥(USub S U)) := by
    apply Subtype.ext
    change (SemidirectProduct.inr (s2 hS2) : SemiProduct S U)⁻¹ * (y : SemiProduct S U) *
        SemidirectProduct.inr (s2 hS2) = SemidirectProduct.inl (s2 hS2 • (y : SemiProduct S U).left)
    rw [inr_inv_mul_USub_mul_inr, hinv]
  rw [harg]
  rfl

/-- In the order-two case, characters of `U` fixed by `S` are in bijection
with the fixed points of the Brauer permutation on irreducible class functions
of the normal copy `USub`. -/
public noncomputable def fixedIrrEquivPerm (hS2 : Nat.card S = 2) :
    {α : IrrBG19 U // FixedIrr S U α} ≃
      ↥(Function.fixedPoints (irreducibleConjClassFunctionPerm (USub S U)
        (SemidirectProduct.inr (s2 hS2)))) :=
  Equiv.ofBijective
    (fun α => ⟨irrConjEquiv (↥(USub S U)) (irrUSubOfU (S := S) (U := U) α.1),
      by
        rw [Function.mem_fixedPoints_iff]
        rw [irrConjEquiv_perm hS2]
        congr 1
        exact irrUSubS2Action_fixed_of_FixedIrr hS2 α.1 α.2⟩)
    ⟨by
      intro α β h
      apply Subtype.ext
      have hval : (irrConjEquiv (↥(USub S U))) (irrUSubOfU (S := S) (U := U) α.1) =
          (irrConjEquiv (↥(USub S U))) (irrUSubOfU (S := S) (U := U) β.1) :=
        by
          exact congrArg (fun q : {p : {χ : ConjClassFunction (↥(USub S U)) //
              IsIrreducibleConjCharacter χ} // p ∈ Function.fixedPoints
                  (irreducibleConjClassFunctionPerm (USub S U)
                    (SemidirectProduct.inr (s2 hS2)))} => q.1) h
      have htr : irrUSubOfU (S := S) (U := U) α.1 = irrUSubOfU (S := S) (U := U) β.1 :=
        (irrConjEquiv (↥(USub S U))).injective hval
      have htr2 := congrArg (irrUOfUSub (S := S) (U := U)) htr
      simpa [irrUOfUSub_irrUSubOfU] using htr2,
      by
      intro p
      let x : {χ : ConjClassFunction (↥(USub S U)) // IsIrreducibleConjCharacter χ} := p.1
      let a : IrrBG19 U := irrUOfUSub (S := S) (U := U) ((irrConjEquiv (↥(USub S U))).symm x)
      have hx : irrUSubOfU (S := S) (U := U) a =
          (irrConjEquiv (↥(USub S U))).symm x := by
        simp [a, irrUSubOfU_irrUOfUSub]
      have hact : irrUSubS2Action hS2 ((irrConjEquiv (↥(USub S U))).symm x) =
          (irrConjEquiv (↥(USub S U))).symm x := by
        apply (irrConjEquiv (↥(USub S U))).injective
        rw [← irrConjEquiv_perm hS2]
        rw [Equiv.apply_symm_apply]
        exact p.2
      have hfix : FixedIrr S U a := by
        apply FixedIrr_of_irrUSubS2Action_fixed hS2 a
        simpa [hx] using hact
      refine ⟨⟨a, hfix⟩, ?_⟩
      apply Subtype.ext
      change (irrConjEquiv (↥(USub S U)) (irrUSubOfU (S := S) (U := U) a)) = p.1
      rw [hx]
      rw [Equiv.apply_symm_apply]⟩

end ConjClassBridge

section FixedConjClassBridge

variable {S U : Type u} [Group S] [Group U] [Fintype S] [Fintype U]
variable [MulDistribMulAction S U]

/-- The automorphism of `U` induced by the non-trivial element in the
order-two case. -/
public def orderTwoAut (hS2 : Nat.card S = 2) : U ≃* U :=
  MulDistribMulAction.toMulEquiv (M := U) (G := S) (s2 hS2)

/-- The order-two automorphism is an involution. -/
public theorem orderTwoAut_sq (hS2 : Nat.card S = 2) :
    (orderTwoAut (S := S) (U := U) hS2).toEquiv ^ 2 = 1 := by
  ext u
  change (s2 hS2) • ((s2 hS2) • u) = u
  rw [← mul_smul]
  simpa [pow_two] using congrArg (fun s : S => s • u) (s2_sq hS2)

omit [Fintype S] in
/-- In a group of order two, the non-trivial element is its own inverse. -/
public theorem s2_inv (hS2 : Nat.card S = 2) : (s2 hS2)⁻¹ = s2 hS2 := by
  apply inv_eq_of_mul_eq_one_right
  simpa [pow_two] using s2_sq hS2

set_option backward.isDefEq.respectTransparency false in
/-- A conjugacy class of `USub` is fixed by conjugation with `inr s2` exactly
when its left component is conjugate to its image under the action of `s2`. -/
public theorem fixedClass_iff_conj (hS2 : Nat.card S = 2)
    (x : ↥(USub S U)) :
    ConjClasses.mk x ∈ Function.fixedPoints
        (conjClassesConjPerm (USub S U) (SemidirectProduct.inr (s2 hS2))) ↔
      IsConj ((s2 hS2) • x.1.left) x.1.left := by
  let σ : Equiv.Perm (ConjClasses (↥(USub S U))) :=
    conjClassesConjPerm (USub S U) (SemidirectProduct.inr (s2 hS2))
  rw [Function.mem_fixedPoints_iff]
  have hσsymm : σ (ConjClasses.mk x) = ConjClasses.mk x ↔
      σ.symm (ConjClasses.mk x) = ConjClasses.mk x := by
    constructor
    · intro h
      calc
        σ.symm (ConjClasses.mk x) = σ.symm (σ (ConjClasses.mk x)) := by rw [h]
        _ = ConjClasses.mk x := σ.symm_apply_apply (ConjClasses.mk x)
    · intro h
      calc
        σ (ConjClasses.mk x) = σ (σ.symm (ConjClasses.mk x)) := by rw [h]
        _ = ConjClasses.mk x := σ.apply_symm_apply (ConjClasses.mk x)
  rw [hσsymm]
  rw [conjClassesConjPerm_symm_mk]
  rw [ConjClasses.mk_eq_mk_iff_isConj]
  change IsConj (⟨(SemidirectProduct.inr (s2 hS2) : SemiProduct S U)⁻¹ * (x : SemiProduct S U) *
      SemidirectProduct.inr (s2 hS2), by
        rw [mem_USub_iff]
        simp [SemidirectProduct.mul_right, SemidirectProduct.inv_right,
          (mem_USub_iff x.1).1 x.2]⟩ : ↥(USub S U)) x ↔
      IsConj ((s2 hS2) • x.1.left) x.1.left
  constructor
  · intro h
    have h' := (usubEquiv S U).symm.toMonoidHom.map_isConj h
    have ha : (usubEquiv S U).symm
        (⟨(SemidirectProduct.inr (s2 hS2) : SemiProduct S U)⁻¹ * (x : SemiProduct S U) *
          SemidirectProduct.inr (s2 hS2), by
            rw [mem_USub_iff]
            simp [SemidirectProduct.mul_right, SemidirectProduct.inv_right,
              (mem_USub_iff x.1).1 x.2]⟩ : ↥(USub S U)) = (s2 hS2) • x.1.left := by
      change ((SemidirectProduct.inr (s2 hS2) : SemiProduct S U)⁻¹ * (x : SemiProduct S U) *
          SemidirectProduct.inr (s2 hS2)).left = (s2 hS2) • x.1.left
      rw [inr_inv_mul_USub_mul_inr, s2_inv hS2]
      rfl
    have h'' : IsConj ((s2 hS2) • x.1.left) x.1.left := by
      convert h' using 1
      · exact ha.symm
      · simp [usubEquiv]
    exact h''
  · intro h
    have h' := (usubEquiv S U).toMonoidHom.map_isConj h
    have ha : (⟨(SemidirectProduct.inr (s2 hS2) : SemiProduct S U)⁻¹ * (x : SemiProduct S U) *
        SemidirectProduct.inr (s2 hS2), by
          rw [mem_USub_iff]
          simp [SemidirectProduct.mul_right, SemidirectProduct.inv_right,
            (mem_USub_iff x.1).1 x.2]⟩ : ↥(USub S U)) =
        usubEquiv S U ((s2 hS2) • x.1.left) := by
      apply Subtype.ext
      change (SemidirectProduct.inr (s2 hS2) : SemiProduct S U)⁻¹ * (x : SemiProduct S U) *
          SemidirectProduct.inr (s2 hS2) = SemidirectProduct.inl ((s2 hS2) • x.1.left)
      rw [inr_inv_mul_USub_mul_inr, s2_inv hS2]
    have hx : x = usubEquiv S U x.1.left := by
      apply Subtype.ext
      exact usub_eq_inl x
    rw [ha, hx]
    exact h'

/-- A fixed point of the order-two automorphism lies in the fixed subgroup. -/
public theorem mem_fixedSubgroup_of_orderTwoAut_fixed (hS2 : Nat.card S = 2)
    {u : U} (h : (s2 hS2) • u = u) : u ∈ fixedSubgroup S U := by
  rw [mem_fixedSubgroup_iff S U]
  intro s
  rcases s_eq_one_or_s2 hS2 s with hs | hs
  · subst s
    simp
  · subst s
    exact h

omit [Fintype S] [Fintype U] in
/-- If the class of `u` is stable under the order-two automorphism, then the
automorphism sends every element of that class back into the class. -/
public theorem orderTwoAut_mem_orbit (hS2 : Nat.card S = 2) {u x : U}
    (hx : x ∈ MulAction.orbit (ConjAct U) u)
    (hcl : IsConj ((s2 hS2) • u) u) :
    (s2 hS2) • x ∈ MulAction.orbit (ConjAct U) u := by
  rw [ConjAct.mem_orbit_conjAct]
  rw [ConjAct.mem_orbit_conjAct] at hx
  rcases isConj_iff.mp hx with ⟨v, hv⟩
  rcases isConj_iff.mp hcl with ⟨w, hw⟩
  refine isConj_iff.mpr ⟨w * ((s2 hS2) • v), ?_⟩
  calc
    (w * ((s2 hS2) • v)) * ((s2 hS2) • x) * (w * ((s2 hS2) • v))⁻¹
        = w * (((s2 hS2) • v) * ((s2 hS2) • x) * ((s2 hS2) • v)⁻¹) * w⁻¹ := by
            group
    _ = w * ((s2 hS2) • (v * x * v⁻¹)) * w⁻¹ := by
            congr 1
            rw [MulDistribMulAction.smul_mul, MulDistribMulAction.smul_mul, smul_inv']
    _ = w * ((s2 hS2) • u) * w⁻¹ := by rw [hv]
    _ = u := hw

/-- The order-two automorphism restricts to an involution on a stable
conjugacy class. -/
public noncomputable def orbitAutEquiv (hS2 : Nat.card S = 2) {u : U}
    (hcl : IsConj ((s2 hS2) • u) u) :
    MulAction.orbit (ConjAct U) u ≃ MulAction.orbit (ConjAct U) u where
  toFun x := ⟨(s2 hS2) • x.1, orderTwoAut_mem_orbit hS2 x.2 hcl⟩
  invFun x := ⟨(s2 hS2) • x.1, orderTwoAut_mem_orbit hS2 x.2 hcl⟩
  left_inv x := by
    apply Subtype.ext
    change (s2 hS2) • ((s2 hS2) • x.1) = x.1
    rw [← mul_smul]
    simpa [pow_two] using congrArg (fun s : S => s • x.1) (s2_sq hS2)
  right_inv x := by
    apply Subtype.ext
    change (s2 hS2) • ((s2 hS2) • x.1) = x.1
    rw [← mul_smul]
    simpa [pow_two] using congrArg (fun s : S => s • x.1) (s2_sq hS2)

omit [Fintype S] [Fintype U] in
/-- The automorphism on a stable conjugacy class is an involution. -/
public theorem orbitAutEquiv_sq (hS2 : Nat.card S = 2) {u : U}
    (hcl : IsConj ((s2 hS2) • u) u) :
    (orbitAutEquiv hS2 hcl) ^ 2 = 1 := by
  ext x
  change (s2 hS2) • ((s2 hS2) • x.1) = x.1
  rw [← mul_smul]
  simpa [pow_two] using congrArg (fun s : S => s • x.1) (s2_sq hS2)

/-- A conjugacy class in a `2'`-group has odd cardinality. -/
public theorem conjClass_odd_card (hU2' : Nat.Coprime 2 (Nat.card U))
    (u : U) : Odd (Nat.card (MulAction.orbit (ConjAct U) u)) := by
  classical
  let O : Type u := MulAction.orbit (ConjAct U) u
  have hfinO : Finite O := by
    dsimp [O]
    infer_instance
  have : Fintype O := Fintype.ofFinite (α := O)
  let St : Type u := MulAction.stabilizer (ConjAct U) u
  have hfinSt : Finite St := by
    dsimp [St]
    infer_instance
  have : Fintype St := Fintype.ofFinite (α := St)
  have hc := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct U) u
  have hoddConj : Odd (Fintype.card (ConjAct U)) := by
    have hodd := odd_natCard_of_coprime_two (G := U) hU2'
    simpa [Nat.card_eq_fintype_card] using hodd
  have hprod : Odd (Fintype.card O * Fintype.card St) := by
    rw [hc]
    exact hoddConj
  have hoddO : Odd (Fintype.card O) := (Nat.odd_mul.mp hprod).1
  rw [Nat.card_eq_fintype_card]
  exact hoddO

/-- A stable conjugacy class under the order-two automorphism contains a
fixed point, i.e. an element of `B = C_U(S)`. -/
public theorem exists_fixed_of_stable_conjClass (hS2 : Nat.card S = 2)
    (hU2' : Nat.Coprime 2 (Nat.card U)) {u : U}
    (hcl : IsConj ((s2 hS2) • u) u) :
    ∃ x : U, x ∈ fixedSubgroup S U ∧ IsConj x u := by
  classical
  let O : Type u := MulAction.orbit (ConjAct U) u
  have hfinO : Finite O := by
    dsimp [O]
    infer_instance
  have : Fintype O := Fintype.ofFinite (α := O)
  have hoddO : Odd (Fintype.card O) := by
    rw [← Nat.card_eq_fintype_card]
    exact conjClass_odd_card hU2' u
  have hfix := exists_fixed_of_involution_odd_card (α := O)
    (orbitAutEquiv (S := S) (U := U) hS2 hcl)
    (orbitAutEquiv_sq (S := S) (U := U) hS2 hcl) hoddO
  rcases hfix with ⟨x, hx⟩
  refine ⟨x.1, ?_, ?_⟩
  · apply mem_fixedSubgroup_of_orderTwoAut_fixed hS2
    exact congrArg Subtype.val hx
  · exact (ConjAct.mem_orbit_conjAct (g := x.1) (h := u)).1 x.2

/-- The set of elements conjugating `x` to `y`. -/
public def conjugatorSet (x y : U) : Set U :=
  {a : U | a * x * a⁻¹ = y}

/-- The set of conjugators from `x` to `y` is in bijection with the
centralizer of `x`. -/
public noncomputable def conjugatorSetEquivCentralizer (x y : U) (a0 : U)
    (ha0 : a0 ∈ conjugatorSet x y) :
    conjugatorSet x y ≃ ↥(Subgroup.centralizer ({x} : Set U)) where
  toFun a := ⟨a0⁻¹ * a.1, by
    have hc : a.1 * x * a.1⁻¹ = y := a.2
    have h0 : a0 * x * a0⁻¹ = y := ha0
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hz : (a0⁻¹ * a.1) * x * (a0⁻¹ * a.1)⁻¹ = x := by
      calc
        (a0⁻¹ * a.1) * x * (a0⁻¹ * a.1)⁻¹
            = a0⁻¹ * (a.1 * x * a.1⁻¹) * a0 := by group
        _ = a0⁻¹ * y * a0 := by rw [hc]
        _ = x := by
              calc
                a0⁻¹ * y * a0 = a0⁻¹ * (a0 * x * a0⁻¹) * a0 := by rw [h0]
                _ = x := by group
    exact mul_inv_eq_iff_eq_mul.mp hz⟩
  invFun c := ⟨a0 * c.1, by
    have hc : c.1 * x = x * c.1 := by
      exact (Subgroup.mem_centralizer_singleton_iff (g := x) (k := c.1)).mp c.2
    calc
      (a0 * c.1) * x * (a0 * c.1)⁻¹
          = a0 * (c.1 * x * c.1⁻¹) * a0⁻¹ := by group
      _ = a0 * x * a0⁻¹ := by rw [mul_inv_eq_iff_eq_mul.mpr hc]
      _ = y := ha0⟩
  left_inv a := by
    apply Subtype.ext
    change a0 * (a0⁻¹ * a.1) = a.1
    group
  right_inv c := by
    apply Subtype.ext
    change a0⁻¹ * (a0 * c.1) = c.1
    group

/-- The set of conjugators from `x` to `y` has odd cardinality when `U` is
a `2'`-group and the set is nonempty. -/
public theorem conjugatorSet_odd_card (hU2' : Nat.Coprime 2 (Nat.card U))
    {x y : U} (a0 : U) (ha0 : a0 ∈ conjugatorSet x y) :
    Odd (Nat.card (conjugatorSet x y)) := by
  classical
  let C : Type u := conjugatorSet x y
  have hfinC : Finite C := by
    dsimp [C]
    infer_instance
  have : Fintype C := Fintype.ofFinite (α := C)
  let Z : Type u := ↥(Subgroup.centralizer ({x} : Set U))
  have hfinZ : Finite Z := by
    dsimp [Z]
    infer_instance
  have : Fintype Z := Fintype.ofFinite (α := Z)
  have hcard : Fintype.card C = Fintype.card Z := by
    exact Fintype.card_congr (conjugatorSetEquivCentralizer x y a0 ha0)
  have hoddZ : Odd (Nat.card (Subgroup.centralizer ({x} : Set U))) := by
    exact odd_natCard_of_coprime_two (G := ↥(Subgroup.centralizer ({x} : Set U)))
      (Nat.Coprime.coprime_dvd_right
        (Subgroup.card_subgroup_dvd_card (Subgroup.centralizer ({x} : Set U))) hU2')
  have hoddZF : Odd (Fintype.card Z) := by
    simpa [Z, Nat.card_eq_fintype_card] using hoddZ
  have hoddC : Odd (Fintype.card C) := by
    rw [hcard]
    exact hoddZF
  rw [Nat.card_eq_fintype_card]
  exact hoddC

omit [Fintype S] [Fintype U] in
/-- The order-two automorphism sends a conjugator from `x` to `y` to another
conjugator when both endpoints are fixed. -/
public theorem orderTwoAut_mem_conjugatorSet (hS2 : Nat.card S = 2)
    {x y : U} (hx : x ∈ fixedSubgroup S U) (hy : y ∈ fixedSubgroup S U)
    {a : U} (ha : a ∈ conjugatorSet x y) :
    (s2 hS2) • a ∈ conjugatorSet x y := by
  have hx2 : (s2 hS2) • x = x := (mem_fixedSubgroup_iff S U x).1 hx (s2 hS2)
  have hy2 : (s2 hS2) • y = y := (mem_fixedSubgroup_iff S U y).1 hy (s2 hS2)
  change (s2 hS2) • a * x * ((s2 hS2) • a)⁻¹ = y
  calc
    (s2 hS2) • a * x * ((s2 hS2) • a)⁻¹
        = (s2 hS2) • a * ((s2 hS2) • x) * ((s2 hS2) • a)⁻¹ := by rw [hx2]
    _ = (s2 hS2) • (a * x * a⁻¹) := by
          rw [MulDistribMulAction.smul_mul, MulDistribMulAction.smul_mul, smul_inv']
    _ = y := by
          rw [ha]
          exact hy2

/-- The order-two automorphism restricts to an involution on the set of
conjugators from a fixed point to a fixed point. -/
public noncomputable def conjugatorAutEquiv (hS2 : Nat.card S = 2)
    {x y : U} (hx : x ∈ fixedSubgroup S U) (hy : y ∈ fixedSubgroup S U) :
    conjugatorSet x y ≃ conjugatorSet x y where
  toFun a := ⟨(s2 hS2) • a.1, orderTwoAut_mem_conjugatorSet hS2 hx hy a.2⟩
  invFun a := ⟨(s2 hS2) • a.1, orderTwoAut_mem_conjugatorSet hS2 hx hy a.2⟩
  left_inv a := by
    apply Subtype.ext
    change (s2 hS2) • ((s2 hS2) • a.1) = a.1
    rw [← mul_smul]
    simpa [pow_two] using congrArg (fun s : S => s • a.1) (s2_sq hS2)
  right_inv a := by
    apply Subtype.ext
    change (s2 hS2) • ((s2 hS2) • a.1) = a.1
    rw [← mul_smul]
    simpa [pow_two] using congrArg (fun s : S => s • a.1) (s2_sq hS2)

/-- If two fixed points are conjugate in `U`, then they are conjugate in
`B = C_U(S)`. -/
public theorem exists_fixed_conjugator (hS2 : Nat.card S = 2)
    (hU2' : Nat.Coprime 2 (Nat.card U)) {x y : U}
    (hx : x ∈ fixedSubgroup S U) (hy : y ∈ fixedSubgroup S U)
    (h : IsConj x y) :
    ∃ b : ↥(fixedSubgroup S U), (b : U) * x * (b : U)⁻¹ = y := by
  classical
  rcases isConj_iff.mp h with ⟨a0, ha0⟩
  let C : Type u := conjugatorSet x y
  have hfinC : Finite C := by
    dsimp [C]
    infer_instance
  have : Fintype C := Fintype.ofFinite (α := C)
  have hoddC : Odd (Fintype.card C) := by
    rw [← Nat.card_eq_fintype_card]
    exact conjugatorSet_odd_card hU2' a0 ha0
  have hfix := exists_fixed_of_involution_odd_card (α := C)
    (conjugatorAutEquiv (S := S) (U := U) hS2 hx hy)
    (by
      ext a
      change (s2 hS2) • ((s2 hS2) • a.1) = a.1
      rw [← mul_smul]
      simpa [pow_two] using congrArg (fun s : S => s • a.1) (s2_sq hS2))
    hoddC
  rcases hfix with ⟨a, ha⟩
  refine ⟨⟨a.1, mem_fixedSubgroup_of_orderTwoAut_fixed hS2
    (congrArg Subtype.val ha)⟩, a.2⟩

/-- A canonical fixed representative of a stable conjugacy class, chosen in
`B = C_U(S)`. -/
public noncomputable def fixedClassRep (hS2 : Nat.card S = 2)
    (hU2' : Nat.Coprime 2 (Nat.card U)) (x : ↥(USub S U))
    (hx : ConjClasses.mk x ∈ Function.fixedPoints
      (conjClassesConjPerm (USub S U) (SemidirectProduct.inr (s2 hS2)))) :
    ↥(fixedSubgroup S U) :=
  ⟨Classical.choose (exists_fixed_of_stable_conjClass hS2 hU2'
      ((fixedClass_iff_conj hS2 x).1 hx)),
    (Classical.choose_spec (exists_fixed_of_stable_conjClass hS2 hU2'
      ((fixedClass_iff_conj hS2 x).1 hx))).1⟩

/-- The canonical fixed representative is conjugate to the original element. -/
public theorem fixedClassRep_isConj (hS2 : Nat.card S = 2)
    (hU2' : Nat.Coprime 2 (Nat.card U)) (x : ↥(USub S U))
    (hx : ConjClasses.mk x ∈ Function.fixedPoints
      (conjClassesConjPerm (USub S U) (SemidirectProduct.inr (s2 hS2)))) :
    IsConj (fixedClassRep hS2 hU2' x hx : U) x.1.left :=
  (Classical.choose_spec (exists_fixed_of_stable_conjClass hS2 hU2'
    ((fixedClass_iff_conj hS2 x).1 hx))).2

/-- The canonical fixed representative is conjugate to any fixed element of
the same class. -/
public theorem fixedClassRep_conj (hS2 : Nat.card S = 2)
    (hU2' : Nat.Coprime 2 (Nat.card U)) (x : ↥(USub S U))
    (hx : ConjClasses.mk x ∈ Function.fixedPoints
      (conjClassesConjPerm (USub S U) (SemidirectProduct.inr (s2 hS2))))
    {b : ↥(fixedSubgroup S U)} (hb : IsConj (b : U) x.1.left) :
    IsConj (fixedClassRep hS2 hU2' x hx : U) (b : U) :=
  (fixedClassRep_isConj hS2 hU2' x hx).trans hb.symm

set_option backward.isDefEq.respectTransparency false in
/-- The canonical fixed representative gives a well-defined map from fixed
conjugacy classes of `USub` to conjugacy classes of `B`. -/
public theorem fixedClassRep_mk_eq (hS2 : Nat.card S = 2)
    (hU2' : Nat.Coprime 2 (Nat.card U)) {x y : ↥(USub S U)}
    (hx : ConjClasses.mk x ∈ Function.fixedPoints
      (conjClassesConjPerm (USub S U) (SemidirectProduct.inr (s2 hS2))))
    (hy : ConjClasses.mk y ∈ Function.fixedPoints
      (conjClassesConjPerm (USub S U) (SemidirectProduct.inr (s2 hS2))))
    (hxy : IsConj x y) :
    ConjClasses.mk (fixedClassRep hS2 hU2' x hx) =
      ConjClasses.mk (fixedClassRep hS2 hU2' y hy) := by
  have hxyU : IsConj x.1.left y.1.left := by
    have h := (usubEquiv S U).symm.toMonoidHom.map_isConj hxy
    simpa [usubEquiv] using h
  let rX : U := fixedClassRep hS2 hU2' x hx
  let rY : U := fixedClassRep hS2 hU2' y hy
  have hX : IsConj rX x.1.left := fixedClassRep_isConj hS2 hU2' x hx
  have hY : IsConj rY y.1.left := fixedClassRep_isConj hS2 hU2' y hy
  have hr : IsConj rX rY := hX.trans (hxyU.trans hY.symm)
  rcases exists_fixed_conjugator hS2 hU2'
    (fixedClassRep hS2 hU2' x hx).2 (fixedClassRep hS2 hU2' y hy).2 hr with ⟨b, hb⟩
  apply ConjClasses.mk_eq_mk_iff_isConj.2
  refine isConj_iff.mpr ⟨b, ?_⟩
  apply Subtype.ext
  exact hb

/-- The map from conjugacy classes of `USub` to conjugacy classes of `B`,
choosing a fixed representative when the class is stable. -/
public noncomputable def fixedClassToB (hS2 : Nat.card S = 2)
    (hU2' : Nat.Coprime 2 (Nat.card U)) :
    ConjClasses (↥(USub S U)) → ConjClasses (↥(fixedSubgroup S U)) := by
  classical
  exact Quotient.lift
    (fun x : ↥(USub S U) =>
      if hx : ConjClasses.mk x ∈ Function.fixedPoints
          (conjClassesConjPerm (USub S U) (SemidirectProduct.inr (s2 hS2))) then
        ConjClasses.mk (fixedClassRep hS2 hU2' x hx)
      else ConjClasses.mk 1)
    (by
      intro x y hxy
      have hEq : ConjClasses.mk x = ConjClasses.mk y :=
        ConjClasses.mk_eq_mk_iff_isConj.mpr hxy
      by_cases hx : ConjClasses.mk x ∈ Function.fixedPoints
          (conjClassesConjPerm (USub S U) (SemidirectProduct.inr (s2 hS2)))
      · have hy : ConjClasses.mk y ∈ Function.fixedPoints
            (conjClassesConjPerm (USub S U) (SemidirectProduct.inr (s2 hS2))) := by
          rw [Function.mem_fixedPoints_iff, ← hEq]
          exact hx
        simp [hx, hy]
        exact fixedClassRep_mk_eq hS2 hU2' hx hy hxy
      · have hy : ¬ ConjClasses.mk y ∈ Function.fixedPoints
            (conjClassesConjPerm (USub S U) (SemidirectProduct.inr (s2 hS2))) := by
          intro hy
          apply hx
          rw [Function.mem_fixedPoints_iff, hEq]
          exact hy
        simp [hx, hy])

/-- The value of `fixedClassToB` on a stable class. -/
public theorem fixedClassToB_mk (hS2 : Nat.card S = 2)
    (hU2' : Nat.Coprime 2 (Nat.card U)) (x : ↥(USub S U))
    (hx : ConjClasses.mk x ∈ Function.fixedPoints
      (conjClassesConjPerm (USub S U) (SemidirectProduct.inr (s2 hS2)))) :
    fixedClassToB hS2 hU2' (ConjClasses.mk x) =
      ConjClasses.mk (fixedClassRep hS2 hU2' x hx) := by
  unfold fixedClassToB
  change (if hx' : ConjClasses.mk x ∈ Function.fixedPoints
      (conjClassesConjPerm (USub S U) (SemidirectProduct.inr (s2 hS2))) then
        ConjClasses.mk (fixedClassRep hS2 hU2' x hx')
      else ConjClasses.mk 1) =
    ConjClasses.mk (fixedClassRep hS2 hU2' x hx)
  simp [hx]

set_option backward.isDefEq.respectTransparency false in
/-- In the order-two case, fixed conjugacy classes of `USub` under
conjugation by `inr s2` are in bijection with conjugacy classes of
`B = C_U(S)`. -/
public noncomputable def fixedClassEquiv (hS2 : Nat.card S = 2)
    (hU2' : Nat.Coprime 2 (Nat.card U)) :
    ↥(Function.fixedPoints (conjClassesConjPerm (USub S U)
        (SemidirectProduct.inr (s2 hS2)))) ≃
      ConjClasses (↥(fixedSubgroup S U)) where
  toFun p := fixedClassToB hS2 hU2' p.1
  invFun c := by
    classical
    let eB : ↥(fixedSubgroup S U) →* ↥(USub S U) :=
      (usubEquiv S U).toMonoidHom.comp (fixedSubgroup S U).subtype
    refine ⟨ConjClasses.map eB c, ?_⟩
    rcases ConjClasses.exists_rep c with ⟨b, rfl⟩
    simp [ConjClasses.map]
    change ConjClasses.mk (eB b) ∈ Function.fixedPoints
        (conjClassesConjPerm (USub S U) (SemidirectProduct.inr (s2 hS2)))
    rw [fixedClass_iff_conj hS2 (eB b)]
    have hb : (s2 hS2) • (b : U) = (b : U) :=
      (mem_fixedSubgroup_iff S U (b : U)).1 b.2 (s2 hS2)
    simpa [eB, usubEquiv, hb] using (IsConj.refl (b : U))
  left_inv p := by
    classical
    let eB : ↥(fixedSubgroup S U) →* ↥(USub S U) :=
      (usubEquiv S U).toMonoidHom.comp (fixedSubgroup S U).subtype
    rcases p with ⟨c, hc⟩
    rcases ConjClasses.exists_rep c with ⟨x, rfl⟩
    have hto := fixedClassToB_mk hS2 hU2' x hc
    apply Subtype.ext
    change ConjClasses.map eB (fixedClassToB hS2 hU2' (ConjClasses.mk x)) =
      ConjClasses.mk x
    rw [hto]
    simp [ConjClasses.map]
    apply ConjClasses.mk_eq_mk_iff_isConj.2
    have h := fixedClassRep_isConj hS2 hU2' x hc
    have h' := (usubEquiv S U).toMonoidHom.map_isConj h
    have hx : x = usubEquiv S U x.1.left := by
      apply Subtype.ext
      exact usub_eq_inl x
    change IsConj ((usubEquiv S U) (fixedClassRep hS2 hU2' x hc)) x
    convert h' using 1
    · rfl
    · simpa [usubEquiv] using hx
  right_inv c := by
    classical
    rcases ConjClasses.exists_rep c with ⟨b, rfl⟩
    let eB : ↥(fixedSubgroup S U) →* ↥(USub S U) :=
      (usubEquiv S U).toMonoidHom.comp (fixedSubgroup S U).subtype
    have hfix : ConjClasses.mk (eB b) ∈ Function.fixedPoints
        (conjClassesConjPerm (USub S U) (SemidirectProduct.inr (s2 hS2))) := by
      rw [fixedClass_iff_conj hS2 (eB b)]
      have hb : (s2 hS2) • (b : U) = (b : U) :=
        (mem_fixedSubgroup_iff S U (b : U)).1 b.2 (s2 hS2)
      simpa [eB, usubEquiv, hb] using (IsConj.refl (b : U))
    have hto := fixedClassToB_mk hS2 hU2' (eB b) hfix
    change fixedClassToB hS2 hU2' (ConjClasses.mk (eB b)) = ConjClasses.mk b
    rw [hto]
    have hbU : IsConj (b : U) (eB b).1.left := by
      simpa [eB, usubEquiv] using (IsConj.refl (b : U))
    have hconjU := fixedClassRep_conj hS2 hU2' (eB b) hfix hbU
    rcases exists_fixed_conjugator hS2 hU2'
      (fixedClassRep hS2 hU2' (eB b) hfix).2 b.2 hconjU with ⟨a, ha⟩
    apply ConjClasses.mk_eq_mk_iff_isConj.2
    refine isConj_iff.mpr ⟨a, ?_⟩
    apply Subtype.ext
    exact ha

/-- In the order-two case, the number of fixed irreducible characters of `U`
equals the number of irreducible characters of `B = C_U(S)`. -/
public theorem orderTwo_card_fixedIrr (hS2 : Nat.card S = 2)
    (hU2' : Nat.Coprime 2 (Nat.card U)) :
    Nat.card {α : IrrBG19 U // FixedIrr S U α} =
      Nat.card (IrrBG19 (↥(fixedSubgroup S U))) := by
  classical
  calc
    Nat.card {α : IrrBG19 U // FixedIrr S U α}
        = Nat.card (Function.fixedPoints
            (irreducibleConjClassFunctionPerm (USub S U)
              (SemidirectProduct.inr (s2 hS2)))) :=
          Nat.card_congr (fixedIrrEquivPerm (S := S) (U := U) hS2)
    _ = Nat.card (Function.fixedPoints
          (conjClassesConjPerm (USub S U) (SemidirectProduct.inr (s2 hS2)))) := by
          rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq]
          exact fixed_irreducible_ncard_eq_fixed_conjClasses (USub S U)
            (SemidirectProduct.inr (s2 hS2))
    _ = Nat.card (ConjClasses (↥(fixedSubgroup S U))) :=
          Nat.card_congr (fixedClassEquiv hS2 hU2')
    _ = Nat.card (IrrBG19 (↥(fixedSubgroup S U))) := by
          simp [Nat.card_eq_fintype_card,
            fintype_card_irr_eq_conjClassesBG19 (↥(fixedSubgroup S U))]

/-- In the order-two case, the Glauberman correspondence is a bijection. -/
public noncomputable def orderTwoIrrEquiv (hS2 : Nat.card S = 2)
    (hU2' : Nat.Coprime 2 (Nat.card U)) :
    {α : IrrBG19 U // FixedIrr S U α} ≃ IrrBG19 (↥(fixedSubgroup S U)) := by
  classical
  let A : Type u := {α : IrrBG19 U // FixedIrr S U α}
  let B : Type u := IrrBG19 (↥(fixedSubgroup S U))
  let f : A → B := fun α => orderTwoCorr hS2 hU2' α.1 α.2
  have hInj : Function.Injective f := by
    simpa [f] using orderTwoCorr_injective hS2 hU2'
  have hFinA : Finite A := by
    dsimp [A]
    infer_instance
  have hFinB : Finite B := by
    dsimp [B]
    infer_instance
  have : Fintype A := Fintype.ofFinite (α := A)
  have : Fintype B := Fintype.ofFinite (α := B)
  have hCardF : Fintype.card A = Fintype.card B := by
    have hCard := orderTwo_card_fixedIrr hS2 hU2'
    simpa [A, B, Nat.card_eq_fintype_card] using hCard
  exact Equiv.ofBijective f (by
    simpa using (Fintype.bijective_iff_injective_and_card f).2 ⟨hInj, hCardF⟩)

/-- The order-two bijection preserves the mod-2 congruence. -/
public theorem orderTwoIrrEquiv_congr (hS2 : Nat.card S = 2)
    (hU2' : Nat.Coprime 2 (Nat.card U)) (α : IrrBG19 U) (hα : FixedIrr S U α)
    (b : ↥(fixedSubgroup S U)) :
    CongruentModTwo (α.1 b) ((orderTwoIrrEquiv hS2 hU2' ⟨α, hα⟩).1 b) := by
  simpa [orderTwoIrrEquiv] using orderTwoCorr_congr hS2 hU2' α hα b

/-- The fixed subgroup of a subgroup action is the same subgroup as
`FixedPoints.subgroup`. -/
public noncomputable def fixedSubgroupEquivFixedPoints (H : Subgroup S) :
    fixedSubgroup (↥H) U ≃* FixedPoints.subgroup H U where
  toFun u := ⟨u.1, by
    rw [FixedPoints.mem_subgroup]
    intro h
    change h • u.1 = u.1
    simpa using u.2 h⟩
  invFun u := ⟨u.1, by
    rw [mem_fixedSubgroup_iff (↥H) U u.1]
    intro h
    change h • u.1 = u.1
    simpa using (FixedPoints.mem_subgroup H U u.1).1 u.2 h⟩
  left_inv u := by
    apply Subtype.ext
    rfl
  right_inv u := by
    apply Subtype.ext
    rfl
  map_mul' u v := by
    apply Subtype.ext
    rfl

/-- The quotient group acts on the fixed-point subgroup of `H`. -/
public noncomputable def quotientSmulFixedSubgroup (H : Subgroup S) [H.Normal]
    (q : S ⧸ H) (u : ↥(fixedSubgroup (↥H) U)) :
    ↥(fixedSubgroup (↥H) U) :=
  Quotient.liftOn q
    (fun s : S => ⟨s • (u : U), by
      rw [mem_fixedSubgroup_iff (↥H) U]
      intro h
      have hmem : s⁻¹ * (h : S) * s ∈ H := by
        simpa using (inferInstance : H.Normal).conj_mem (h : S) h.2 s⁻¹
      have hu : ((s⁻¹ * (h : S) * s : S) • (u : U)) = (u : U) :=
        u.2 ⟨s⁻¹ * (h : S) * s, hmem⟩
      calc
        (h : S) • (s • (u : U)) = ((h : S) * s) • (u : U) := by rw [← mul_smul]
        _ = (s * (s⁻¹ * (h : S) * s)) • (u : U) := by congr 1; group
        _ = s • ((s⁻¹ * (h : S) * s) • (u : U)) := by rw [mul_smul]
        _ = s • (u : U) := by rw [hu]⟩)
    (by
      intro s t hst
      apply Subtype.ext
      have hrel : s⁻¹ * t ∈ H :=
        QuotientGroup.leftRel_apply.mp hst
      have hu : ((s⁻¹ * t : S) • (u : U)) = (u : U) :=
        u.2 ⟨s⁻¹ * t, hrel⟩
      calc
        s • (u : U) = s • (((s⁻¹ * t : S) • (u : U))) := by rw [hu]
        _ = (s * (s⁻¹ * t)) • (u : U) := by rw [← mul_smul]
        _ = t • (u : U) := by congr 1; group)

public noncomputable instance instQuotientMulDistribMulActionFixedSubgroup
    (H : Subgroup S) [H.Normal] :
    MulDistribMulAction (S ⧸ H) (↥(fixedSubgroup (↥H) U)) where
  smul := quotientSmulFixedSubgroup H
  one_smul := by
    intro u
    change quotientSmulFixedSubgroup H (((1 : S) : S ⧸ H)) u = u
    rw [quotientSmulFixedSubgroup, Quotient.liftOn_mk]
    simp
  mul_smul := by
    intro a b u
    change quotientSmulFixedSubgroup H (a * b) u =
      quotientSmulFixedSubgroup H a (quotientSmulFixedSubgroup H b u)
    refine Quotient.inductionOn a ?_
    refine Quotient.inductionOn b ?_
    intro s t
    change quotientSmulFixedSubgroup H (QuotientGroup.mk (t * s)) u =
      quotientSmulFixedSubgroup H (QuotientGroup.mk t)
        (quotientSmulFixedSubgroup H (QuotientGroup.mk s) u)
    rw [quotientSmulFixedSubgroup, Quotient.liftOn_mk]
    simp [quotientSmulFixedSubgroup]
    exact mul_smul t s (u : U)
  smul_one := by
    intro q
    change quotientSmulFixedSubgroup H q (1 : ↥(fixedSubgroup (↥H) U)) =
      (1 : ↥(fixedSubgroup (↥H) U))
    apply Subtype.ext
    refine Quotient.inductionOn q ?_
    intro s
    simp [quotientSmulFixedSubgroup]
  smul_mul := by
    intro q a b
    change quotientSmulFixedSubgroup H q (a * b) =
      quotientSmulFixedSubgroup H q a * quotientSmulFixedSubgroup H q b
    apply Subtype.ext
    refine Quotient.inductionOn q ?_
    intro s
    simp [quotientSmulFixedSubgroup]

/-- The order-two correspondence transported to the fixed-point subgroup. -/
public noncomputable def orderTwoLiftEquiv (H : Subgroup S) [H.Normal]
    (hH2 : Nat.card (↥H) = 2) (hU2' : Nat.Coprime 2 (Nat.card U)) :
    {α : IrrBG19 U // FixedIrr (↥H) U α} ≃ IrrBG19 (↥(fixedSubgroup (↥H) U)) :=
  orderTwoIrrEquiv (S := ↥H) (U := U) hH2 hU2'

/-- The transported order-two correspondent is still congruent to `α` on the
fixed-point subgroup. -/
public theorem orderTwoLiftEquiv_congr (H : Subgroup S) [H.Normal]
    (hH2 : Nat.card (↥H) = 2) (hU2' : Nat.Coprime 2 (Nat.card U))
    (α : IrrBG19 U) (hα : FixedIrr (↥H) U α)
    (b : ↥(fixedSubgroup (↥H) U)) :
    CongruentModTwo (α.1 (b : U))
      ((orderTwoLiftEquiv H hH2 hU2' ⟨α, hα⟩).1 b) := by
  simpa [orderTwoLiftEquiv] using
    orderTwoIrrEquiv_congr (S := ↥H) (U := U) hH2 hU2' α hα b

/-- If `α` is fixed by the whole group, its order-two correspondent is fixed by
the quotient action. -/
public theorem orderTwoLiftEquiv_fixed_of_FixedIrr (H : Subgroup S) [H.Normal]
    (hH2 : Nat.card (↥H) = 2) (hU2' : Nat.Coprime 2 (Nat.card U))
    {α : IrrBG19 U} (hαS : FixedIrr S U α) (hαH : FixedIrr (↥H) U α) :
    FixedIrr (S ⧸ H) (↥(fixedSubgroup (↥H) U))
      (orderTwoLiftEquiv H hH2 hU2' ⟨α, hαH⟩) := by
  classical
  let U1 : Type u := ↥(fixedSubgroup (↥H) U)
  let S1 : Type u := S ⧸ H
  have hU1' : Nat.Coprime 2 (Nat.card U1) := by
    exact Nat.Coprime.coprime_dvd_right
      (Subgroup.card_subgroup_dvd_card (fixedSubgroup (↥H) U)) hU2'
  rw [FixedIrr]
  intro q
  let β : IrrBG19 U1 := orderTwoLiftEquiv H hH2 hU2' ⟨α, hαH⟩
  let β' : IrrBG19 U1 :=
    ⟨fun u => β.1 (q • u),
      isIrreducibleCharacter_congr
        (MulDistribMulAction.toMulEquiv (M := U1) (G := S1) q) β.2⟩
  have hββ' : β = β' := by
    apply eq_of_congruent_irr hU1' (β := β) (β' := β')
    intro u
    have hβu : CongruentModTwo (α.1 (u : U)) (β.1 u) := by
      simpa [β] using orderTwoLiftEquiv_congr H hH2 hU2' α hαH u
    have hβqu : CongruentModTwo (α.1 ((q • u : U1) : U)) (β.1 (q • u)) := by
      simpa [β] using orderTwoLiftEquiv_congr H hH2 hU2' α hαH (q • u)
    have hαfix : α.1 ((q • u : U1) : U) = α.1 (u : U) := by
      have hq : (q.out : S1) = q := q.out_eq
      rw [← hq]
      have hsmul : (((q.out : S1) • u : U1) : U) = q.out • (u : U) := by
        change (quotientSmulFixedSubgroup H (q.out : S1) u).1 = q.out • (u : U)
        rw [quotientSmulFixedSubgroup, Quotient.liftOn_mk]
      rw [hsmul]
      exact congrFun (hαS q.out) (u : U)
    exact CongruentModTwo.trans (CongruentModTwo.symm hβu)
      (by simpa [hαfix] using hβqu)
  change (fun u : U1 => β.1 (q • u)) = β.1
  simpa [β'] using (congrArg Subtype.val hββ').symm

/-- If the order-two correspondent is fixed by the quotient, then the original
character is fixed by the whole group. -/
public theorem orderTwoLiftEquiv_injective_fixed (H : Subgroup S) [H.Normal]
    (hH2 : Nat.card (↥H) = 2) (hU2' : Nat.Coprime 2 (Nat.card U))
    {s : S} (hcomm : ∀ h : ↥H, (h : S) * s = s * (h : S))
    {α : IrrBG19 U} (hαH : FixedIrr (↥H) U α)
    (hβ : FixedIrr (S ⧸ H) (↥(fixedSubgroup (↥H) U))
      (orderTwoLiftEquiv H hH2 hU2' ⟨α, hαH⟩)) :
    actionIrr s α = α := by
  classical
  let U1 : Type u := ↥(fixedSubgroup (↥H) U)
  let S1 : Type u := S ⧸ H
  have hU1' : Nat.Coprime 2 (Nat.card U1) := by
    exact Nat.Coprime.coprime_dvd_right
      (Subgroup.card_subgroup_dvd_card (fixedSubgroup (↥H) U)) hU2'
  let e : {α : IrrBG19 U // FixedIrr (↥H) U α} ≃ IrrBG19 U1 :=
    orderTwoLiftEquiv H hH2 hU2'
  let α' : IrrBG19 U := actionIrr s α
  have hα'H : FixedIrr (↥H) U α' :=
    actionIrr_fixed_of_forall_commute H hcomm hαH
  let β : IrrBG19 U1 := e ⟨α, hαH⟩
  let β' : IrrBG19 U1 := e ⟨α', hα'H⟩
  have hββ' : β' = β := by
    apply eq_of_congruent_irr hU1' (β := β') (β' := β)
    intro u
    have h1 : CongruentModTwo (β'.1 u) (α'.1 (u : U)) := by
      simpa [β'] using (CongruentModTwo.symm
        (orderTwoLiftEquiv_congr H hH2 hU2' α' hα'H u))
    have hu : CongruentModTwo (α.1 (u : U)) (β.1 u) := by
      simpa [β] using orderTwoLiftEquiv_congr H hH2 hU2' α hαH u
    let q : S1 := (s : S1)
    have hsu : CongruentModTwo (α.1 ((q • u : U1) : U)) (β.1 (q • u)) := by
      simpa [β] using orderTwoLiftEquiv_congr H hH2 hU2' α hαH (q • u)
    have hfix : β.1 (q • u) = β.1 u := congrFun (hβ q) u
    have hsmul : ((q • u : U1) : U) = s • (u : U) := by
      dsimp [q]
      change (quotientSmulFixedSubgroup H ((s : S) : S1) u).1 = s • (u : U)
      rw [quotientSmulFixedSubgroup, Quotient.liftOn_mk]
    have h2 : CongruentModTwo (α'.1 (u : U)) (α.1 (u : U)) := by
      change CongruentModTwo (α.1 (s • (u : U))) (α.1 (u : U))
      have hsu' : CongruentModTwo (α.1 (s • (u : U))) (β.1 u) := by
        simpa [hsmul, hfix] using hsu
      exact CongruentModTwo.trans hsu' (CongruentModTwo.symm hu)
    exact CongruentModTwo.trans h1 (CongruentModTwo.trans h2 hu)
  have hpair : (⟨α', hα'H⟩ : {α : IrrBG19 U // FixedIrr (↥H) U α}) = ⟨α, hαH⟩ := by
    exact e.injective hββ'
  exact congrArg Subtype.val hpair

/-- If the order-two correspondent is fixed by the quotient, then the original
character is fixed by the whole group. -/
public theorem FixedIrr_of_orderTwoLiftEquiv_fixed (H : Subgroup S) [H.Normal]
    (hH2 : Nat.card (↥H) = 2) (hU2' : Nat.Coprime 2 (Nat.card U))
    (hcomm : ∀ s : S, ∀ h : ↥H, (h : S) * s = s * (h : S))
    {α : IrrBG19 U} (hαH : FixedIrr (↥H) U α)
    (hβ : FixedIrr (S ⧸ H) (↥(fixedSubgroup (↥H) U))
      (orderTwoLiftEquiv H hH2 hU2' ⟨α, hαH⟩)) :
    FixedIrr S U α := by
  rw [FixedIrr]
  intro s
  exact congrArg Subtype.val
    (orderTwoLiftEquiv_injective_fixed H hH2 hU2' (hcomm s) hαH hβ)

set_option backward.isDefEq.respectTransparency false in
/-- Reducing by a central involution: fixed characters of `U` under `S` are
in bijection with fixed characters of the fixed-point subgroup under the
quotient. -/
public noncomputable def orderTwoLiftEquivFixed (H : Subgroup S) [H.Normal]
    (hH2 : Nat.card (↥H) = 2) (hU2' : Nat.Coprime 2 (Nat.card U))
    (hcomm : ∀ s : S, ∀ h : ↥H, (h : S) * s = s * (h : S)) :
    {α : IrrBG19 U // FixedIrr S U α} ≃
      {β : IrrBG19 (↥(fixedSubgroup (↥H) U)) //
        FixedIrr (S ⧸ H) (↥(fixedSubgroup (↥H) U)) β} where
  toFun p := by
    let e : {α : IrrBG19 U // FixedIrr (↥H) U α} ≃
        IrrBG19 (↥(fixedSubgroup (↥H) U)) := orderTwoLiftEquiv H hH2 hU2'
    let αH : FixedIrr (↥H) U p.1 := by
      intro h
      change (fun u : U => p.1.1 ((h : S) • u)) = p.1.1
      exact p.2 (h : S)
    exact ⟨e ⟨p.1, αH⟩,
      orderTwoLiftEquiv_fixed_of_FixedIrr H hH2 hU2' p.2 αH⟩
  invFun q := by
    let e : {α : IrrBG19 U // FixedIrr (↥H) U α} ≃
        IrrBG19 (↥(fixedSubgroup (↥H) U)) := orderTwoLiftEquiv H hH2 hU2'
    exact ⟨(e.symm q.1).1,
      FixedIrr_of_orderTwoLiftEquiv_fixed H hH2 hU2' hcomm (e.symm q.1).2
      (by
        change FixedIrr (S ⧸ H) (↥(fixedSubgroup (↥H) U)) (e (e.symm q.1))
        simpa using q.2)⟩
  left_inv p := by
    apply Subtype.ext
    let e : {α : IrrBG19 U // FixedIrr (↥H) U α} ≃
        IrrBG19 (↥(fixedSubgroup (↥H) U)) := orderTwoLiftEquiv H hH2 hU2'
    let αH : FixedIrr (↥H) U p.1 := by
      intro h
      change (fun u : U => p.1.1 ((h : S) • u)) = p.1.1
      exact p.2 (h : S)
    have h := e.left_inv ⟨p.1, αH⟩
    simpa [αH] using congrArg Subtype.val h
  right_inv q := by
    apply Subtype.ext
    let e : {α : IrrBG19 U // FixedIrr (↥H) U α} ≃
        IrrBG19 (↥(fixedSubgroup (↥H) U)) := orderTwoLiftEquiv H hH2 hU2'
    have h := e.right_inv q.1
    simpa using h

/-- The fixed subgroup of the quotient action on the fixed-point subgroup is
the same as the fixed subgroup of the whole action. -/
public noncomputable def fixedSubgroupQuotientEquiv (H : Subgroup S) [H.Normal] :
    fixedSubgroup (S ⧸ H) (↥(fixedSubgroup (↥H) U)) ≃*
      fixedSubgroup S U where
  toFun b := ⟨b.1.1, by
    rw [mem_fixedSubgroup_iff S U b.1.1]
    intro s
    have hb := congrArg Subtype.val (b.2 (s : S ⧸ H))
    have hsmul : (((s : S ⧸ H) • b.1 : ↥(fixedSubgroup (↥H) U)) : U) =
        s • (b.1.1 : U) := by
      change (quotientSmulFixedSubgroup H ((s : S) : S ⧸ H) b.1).1 =
        s • (b.1.1 : U)
      rw [quotientSmulFixedSubgroup, Quotient.liftOn_mk]
    exact hsmul.symm.trans hb⟩
  invFun u := ⟨⟨u.1, by
    rw [mem_fixedSubgroup_iff (↥H) U u.1]
    intro h
    change (h : S) • (u : U) = u.1
    exact u.2 (h : S)⟩, by
    rw [mem_fixedSubgroup_iff (S ⧸ H) (↥(fixedSubgroup (↥H) U))
      (⟨u.1, by
        rw [mem_fixedSubgroup_iff (↥H) U u.1]
        intro h
        change (h : S) • (u : U) = u.1
        exact u.2 (h : S)⟩ : ↥(fixedSubgroup (↥H) U))]
    intro q
    apply Subtype.ext
    change (quotientSmulFixedSubgroup H q
      (⟨u.1, by
        rw [mem_fixedSubgroup_iff (↥H) U u.1]
        intro h
        change (h : S) • (u : U) = u.1
        exact u.2 (h : S)⟩ : ↥(fixedSubgroup (↥H) U))).1 = u.1
    refine Quotient.inductionOn q ?_
    intro s
    simp [quotientSmulFixedSubgroup]
    exact u.2 s⟩
  left_inv b := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv u := by
    apply Subtype.ext
    rfl
  map_mul' b c := by
    apply Subtype.ext
    rfl

omit [Fintype S] [Fintype U] in
/-- The inverse of the quotient fixed-subgroup equivalence preserves the
underlying element. -/
public theorem fixedSubgroupQuotientEquiv_symm_val (H : Subgroup S) [H.Normal]
    (b : fixedSubgroup S U) :
    ((((fixedSubgroupQuotientEquiv H).symm b :
        fixedSubgroup (S ⧸ H) (↥(fixedSubgroup (↥H) U))) : ↥(fixedSubgroup (↥H) U)) : U) =
      (b : U) := by
  rfl

/-- If `S` is trivial, the fixed subgroup is all of `U`. -/
public noncomputable def fixedSubgroupEquivTop (hS1 : Nat.card S = 1) :
    fixedSubgroup S U ≃* U where
  toFun u := u.1
  invFun u := ⟨u, by
    rw [mem_fixedSubgroup_iff S U u]
    intro s
    have hcardF : Fintype.card S = 1 := by
      simpa [Nat.card_eq_fintype_card] using hS1
    rcases Fintype.card_eq_one_iff_nonempty_unique.mp hcardF with ⟨instU⟩
    let : Unique S := instU
    have hs : s = 1 := Subsingleton.elim s 1
    simp [hs]⟩
  left_inv u := by
    apply Subtype.ext
    rfl
  right_inv u := by
    rfl
  map_mul' u v := by
    rfl

omit [Fintype S] in
/-- The cyclic subgroup generated by a central element is normal. -/
public theorem zpowers_central_normal (z : S) (hz : z ∈ Subgroup.center S) :
    (Subgroup.zpowers z).Normal where
  conj_mem := by
    intro x hx g
    rcases Subgroup.mem_zpowers_iff.mp hx with ⟨k, rfl⟩
    have hcomm : Commute g z := (commute_iff_eq g z).mpr (Subgroup.mem_center_iff.mp hz g)
    have hzpow : g * z ^ k = z ^ k * g := (hcomm.zpow_right k).eq
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, by
      rw [hzpow, mul_inv_cancel_right]⟩

/-- A nontrivial finite `2`-group has a central involution. -/
public theorem exists_central_involution (hS2 : IsPGroup 2 S) [Nontrivial S] :
    ∃ z : S, orderOf z = 2 ∧ z ∈ Subgroup.center S := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCenter : IsPGroup 2 (Subgroup.center S) :=
    hS2.to_subgroup (Subgroup.center S)
  have : Nontrivial (Subgroup.center S) :=
    IsPGroup.center_nontrivial hS2
  have hcard : ∃ n > 0, Nat.card (Subgroup.center S) = 2 ^ n :=
    hCenter.nontrivial_iff_card.mp inferInstance
  rcases hcard with ⟨n, hn, hcn⟩
  have hdiv : 2 ∣ Nat.card (Subgroup.center S) := by
    rw [hcn]
    exact dvd_pow_self 2 (ne_of_gt hn)
  rcases exists_prime_orderOf_dvd_card' (G := Subgroup.center S) 2 hdiv with ⟨z0, hz0⟩
  exact ⟨z0.1, (Subgroup.orderOf_coe z0).trans hz0, z0.2⟩

/-- Glauberman correspondence (Bender--Glauberman Lemma 1.9). -/
public theorem glauberman_correspondence {S U : Type u} [Group S] [Group U]
    [Fintype S] [Fintype U] [MulDistribMulAction S U]
    (hS2 : IsPGroup 2 S) (hU2' : Nat.Coprime 2 (Nat.card U)) :
    ∃ e : {α : IrrBG19 U // FixedIrr S U α} ≃ IrrBG19 (↥(fixedSubgroup S U)),
      ∀ α b, CongruentModTwo (α.1.1 (b : U)) ((e α).1 b) := by
  classical
  let motive : ℕ → Prop := fun n =>
    ∀ (S' U' : Type u) (_ : Group S') (_ : Group U') (_ : Fintype S')
      (_ : Fintype U') (_ : MulDistribMulAction S' U'),
      Nat.card S' = n → IsPGroup 2 S' → Nat.Coprime 2 (Nat.card U') →
        ∃ e : {α : IrrBG19 U' // FixedIrr S' U' α} ≃ IrrBG19 (↥(fixedSubgroup S' U')),
          ∀ α b, CongruentModTwo (α.1.1 (b : U')) ((e α).1 b)
  exact Nat.strong_induction_on (p := motive) (n := Nat.card S) (by
  intro n ih
  intro S' U' _ _ _ _ _
  intro hcard hS2 hU2'
  by_cases hn : n = 1
  · have hS1 : Nat.card S' = 1 := by rw [hcard, hn]
    let eU : {α : IrrBG19 U' // FixedIrr S' U' α} ≃ IrrBG19 U' := {
      toFun p := p.1
      invFun α := ⟨α, by
        intro s
        have hcardF : Fintype.card S' = 1 := by
          simpa [Nat.card_eq_fintype_card] using hS1
        rcases Fintype.card_eq_one_iff_nonempty_unique.mp hcardF with ⟨instU⟩
        let : Unique S' := instU
        have hs : s = 1 := Subsingleton.elim s 1
        simp [hs]⟩
      left_inv p := by
        apply Subtype.ext
        rfl
      right_inv α := rfl
    }
    let eB : IrrBG19 U' ≃ IrrBG19 (↥(fixedSubgroup S' U')) :=
      irrCongr (fixedSubgroupEquivTop (S := S') (U := U') hS1)
    refine ⟨eU.trans eB, ?_⟩
    intro α b
    have hEq : ((eU.trans eB α).1 b) = α.1.1 (b : U') := by
      simp [eU, eB, irrCongr, fixedSubgroupEquivTop]
    rw [hEq]
    exact CongruentModTwo.refl (α.1.1 (b : U'))
  · have hcardF : Fintype.card S' = n := by
      simpa [Nat.card_eq_fintype_card] using hcard
    have hnpos : 0 < n := by
      have : 0 < Nat.card S' := Nat.card_pos (α := S')
      omega
    have hgt : 1 < n := by omega
    have hgtF : 1 < Fintype.card S' := by simpa [hcardF] using hgt
    have : Nontrivial S' :=
      (Fintype.one_lt_card_iff_nontrivial (α := S')).mp hgtF
    rcases exists_central_involution hS2 with ⟨z, hzorder, hzcenter⟩
    let H : Subgroup S' := Subgroup.zpowers z
    have : H.Normal := zpowers_central_normal z hzcenter
    have hH2 : Nat.card (↥H) = 2 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_zpowers, hzorder]
    let U1 : Type u := ↥(fixedSubgroup (↥H) U')
    let S1 : Type u := S' ⧸ H
    have hU1' : Nat.Coprime 2 (Nat.card U1) := by
      exact Nat.Coprime.coprime_dvd_right
        ((fixedSubgroup (↥H) U').card_subgroup_dvd_card) hU2'
    have hS1_2 : IsPGroup 2 S1 := hS2.to_quotient H
    have hlt : Nat.card S1 < n := by
      have hprod := Subgroup.card_eq_card_quotient_mul_card_subgroup H
      have hprod' : n = Nat.card S1 * 2 := by
        rw [← hcard, hprod, hH2]
      have hpos : 0 < Nat.card S1 := Nat.card_pos (α := S1)
      omega
    have hcomm : ∀ s : S', ∀ h : ↥H, (h : S') * s = s * (h : S') := by
      intro s h
      rcases Subgroup.mem_zpowers_iff.mp h.2 with ⟨k, hk⟩
      have hsc : Commute s z :=
        (commute_iff_eq s z).mpr (Subgroup.mem_center_iff.mp hzcenter s)
      have hzpow : z ^ k * s = s * z ^ k := (hsc.zpow_right k).eq.symm
      rw [← hk]
      exact hzpow
    rcases ih (Nat.card S1) hlt S1 U1 (by infer_instance) (by infer_instance)
      (by infer_instance) (by infer_instance) (by infer_instance) rfl hS1_2 hU1'
      with ⟨e1, hcongr1⟩
    let e0 : {α : IrrBG19 U' // FixedIrr S' U' α} ≃
        {β : IrrBG19 U1 // FixedIrr S1 U1 β} := orderTwoLiftEquivFixed H hH2 hU2' hcomm
    let eB : fixedSubgroup S1 U1 ≃* fixedSubgroup S' U' := fixedSubgroupQuotientEquiv H
    let e : {α : IrrBG19 U' // FixedIrr S' U' α} ≃ IrrBG19 (↥(fixedSubgroup S' U')) :=
      e0.trans (e1.trans (irrCongr eB.symm))
    refine ⟨e, ?_⟩
    intro α b
    let βpair : {β : IrrBG19 U1 // FixedIrr S1 U1 β} := e0 α
    let β : IrrBG19 U1 := βpair.1
    let betaHat : IrrBG19 (↥(fixedSubgroup S1 U1)) := e1 βpair
    have hαH : FixedIrr (↥H) U' α.1 := by
      intro h
      change (fun u : U' => α.1.1 ((h : S') • u)) = α.1.1
      exact α.2 (h : S')
    have hβcongr : ∀ u : U1, CongruentModTwo (α.1.1 (u : U')) (β.1 u) := by
      intro u
      change CongruentModTwo (α.1.1 (u : U')) ((e0 α).1.1 u)
      simpa [e0, orderTwoLiftEquivFixed, βpair, β] using
        orderTwoLiftEquiv_congr H hH2 hU2' α.1 hαH u
    let b1 : fixedSubgroup S1 U1 := eB.symm b
    have hβhat : CongruentModTwo (β.1 (b1 : U1)) (betaHat.1 b1) := by
      simpa [βpair, β, betaHat] using hcongr1 βpair b1
    have hval : (((b1 : fixedSubgroup S1 U1) : U1) : U') = (b : U') :=
      fixedSubgroupQuotientEquiv_symm_val H b
    have hA : CongruentModTwo (α.1.1 (b : U')) (β.1 (b1 : U1)) := by
      have h2 := hβcongr (b1 : U1)
      simpa [hval] using h2
    have hB : CongruentModTwo (β.1 (b1 : U1)) ((e α).1 b) := by
      simpa [e, e0, orderTwoLiftEquivFixed, βpair, β, betaHat, eB,
        irrCongr] using hβhat
    exact CongruentModTwo.trans hA hB)
    S U inferInstance inferInstance inferInstance inferInstance inferInstance
      rfl hS2 hU2'

end FixedConjClassBridge

end CFSG.BenderGlauberman
