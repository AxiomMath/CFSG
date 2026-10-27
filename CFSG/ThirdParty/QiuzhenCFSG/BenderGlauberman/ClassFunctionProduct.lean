module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section2.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.ClassFunction

namespace CFSG
end CFSG
open CFSG

/-!
# Bender--Glauberman: direct-product character machinery

Generic facts about irreducible characters of direct products used by
Section 3: the product of irreducible characters is irreducible, every
irreducible character of `A × B` is a product of irreducibles of the factors,
and every irreducible character of a finite cyclic group is linear.
-/

noncomputable section

open scoped BigOperators
open scoped TensorProduct

namespace CFSG.BenderGlauberman

open Theory.Character

-- Local instances matching `Theory.Character`'s subgroup-sum convention; see
-- `BenderGlauberman/ClassFunction.lean`.
attribute [local instance] Fintype.ofFinite
attribute [local instance] Classical.propDecidable

universe u v

variable {G : Type u} {H : Type v} [Group G] [Group H] [Fintype G] [Fintype H]

/-- The pointwise product character on a direct product. -/
@[expose] public def prodChar (χ : ClassFunction G) (ψ : ClassFunction H) : ClassFunction (G × H) :=
  fun p => χ p.1 * ψ p.2

omit [Fintype G] [Fintype H] in
/-- Product of characters is a character. -/
public theorem prodChar_isCharacter (χ : ClassFunction G) (ψ : ClassFunction H)
    (hχ : IsCharacter χ) (hψ : IsCharacter ψ) : IsCharacter (prodChar χ ψ) := by
  rcases hχ with ⟨n, ρ, hρeq⟩
  rcases hψ with ⟨m, σ, hσeq⟩
  let V := Fin n → ℂ
  let W := Fin m → ℂ
  let ρV : Representation ℂ G V := ρ
  let σW : Representation ℂ H W := σ
  let τ : Representation ℂ (G × H) (V ⊗[ℂ] W) :=
    Representation.tprod (ρV.comp (MonoidHom.fst G H)) (σW.comp (MonoidHom.snd G H))
  have hτchar : ∀ p : G × H, τ.character p = prodChar χ ψ p := by
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
public theorem isCharacter_congr {G : Type u} {H : Type v} [Group G] [Group H]
    (e : H ≃* G) {χ : ClassFunction G} (hχ : IsCharacter χ) :
    IsCharacter (fun h : H => χ (e h)) := by
  rcases hχ with ⟨n, ρ, hχeq⟩
  refine ⟨n, ρ.comp e, ?_⟩
  ext h
  rw [hχeq]
  rfl

/-- The `g⁻¹`-form scalar product of two product characters factors as the
product of the scalar products of its factors. -/
public theorem scalarProductInv_prod_mul' (α α' : ClassFunction G) (β β' : ClassFunction H) :
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
public theorem prodChar_isIrreducible (χ : ClassFunction G) (ψ : ClassFunction H)
    (hχ : IsIrreducibleCharacter χ) (hψ : IsIrreducibleCharacter ψ) :
    IsIrreducibleCharacter (prodChar χ ψ) := by
  refine isIrreducibleCharacter_of_norm_one_inv
    (prodChar_isCharacter χ ψ (isCharacter_of_isIrreducibleCharacter hχ)
      (isCharacter_of_isIrreducibleCharacter hψ)) ?_
  calc
    scalarProductInv (G × H) (prodChar χ ψ) (prodChar χ ψ)
        = scalarProductInv G χ χ * scalarProductInv H ψ ψ :=
          scalarProductInv_prod_mul' χ χ ψ ψ
    _ = 1 := by
          rw [isIrreducible_norm_inv_one hχ, isIrreducible_norm_inv_one hψ]
          norm_num

/-- An irreducible character is an irreducible conj-class character. -/
public theorem isIrreducibleConjCharacter_of_isIrreducibleCharacter {G : Type u} [Group G] [Finite G]
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
public theorem isIrreducibleCharacter_ofConjClassFunction {G : Type u} [Group G] [Finite G]
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
public theorem fintype_card_irr_eq_conjClasses (G : Type u) [Group G] [Fintype G] :
    Fintype.card (Irr G) = Nat.card (ConjClasses G) := by
  classical
  let : Finite G := Finite.of_fintype G
  rcases Theory.Character.card_irreducible_characters_eq_card_conjClasses (G := G) with
    ⟨ι, hι, χ, hχ, hcard⟩
  let : Fintype ι := hι
  let f : ι → Irr G := fun i =>
    ⟨ofConjClassFunction (χ i), isIrreducibleCharacter_ofConjClassFunction (hχ.1 i)⟩
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
      isIrreducibleConjCharacter_of_isIrreducibleCharacter ν.2
    rcases hχ.2.1 _ hνConj with ⟨i, hi⟩
    refine ⟨i, Subtype.ext ?_⟩
    change ofConjClassFunction (χ i) = ν.1
    rw [hi]
    ext g
    rfl
  have hbij : Function.Bijective f := ⟨hf_inj, hf_surj⟩
  calc
    Fintype.card (Irr G) = Fintype.card ι :=
      Fintype.card_congr (Equiv.ofBijective f hbij).symm
    _ = Nat.card (ConjClasses G) := hcard

/-- In a commutative finite group, the number of conjugacy classes is the group
order. -/
public theorem nat_card_conjClasses_eq_card_of_isMulCommutative (G : Type u) [Group G]
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
public theorem fintype_card_irr_eq_card_of_isCyclic (G : Type u) [Group G] [IsCyclic G] [Fintype G] :
    Fintype.card (Irr G) = Nat.card G := by
  let : Finite G := Finite.of_fintype G
  let : CommGroup G := IsCyclic.commGroup
  rw [fintype_card_irr_eq_conjClasses G, nat_card_conjClasses_eq_card_of_isMulCommutative G]

/-- The irreducible character associated to a homomorphism into `ℂˣ`. -/
public def linearCharIrr {G : Type u} [Group G] [Fintype G] (φ : G →* ℂˣ) : Irr G :=
  ⟨fun x => ((φ x : ℂˣ) : ℂ), (isLinearCharacter_of_hom φ).1⟩

/-- Distinct homomorphisms give distinct irreducible characters. -/
public theorem linearCharIrr_injective {G : Type u} [Group G] [Fintype G] :
    Function.Injective (linearCharIrr (G := G)) := by
  intro φ ψ hEq
  apply MonoidHom.ext
  intro x
  apply Units.ext
  exact congrFun (congrArg Subtype.val hEq) x

/-- For a finite cyclic group, every irreducible character is linear (i.e. comes
from a homomorphism). -/
public theorem isLinearCharacter_of_isIrreducible_of_isCyclic {G : Type u} [Group G]
    [IsCyclic G] [Fintype G] {χ : ClassFunction G} (hχ : IsIrreducibleCharacter χ) :
    IsLinearCharacter χ := by
  classical
  let : Finite G := Finite.of_fintype G
  let : CommGroup G := IsCyclic.commGroup
  have hcard : Fintype.card (Irr G) = Fintype.card (G →* ℂˣ) := by
    exact (fintype_card_irr_eq_card_of_isCyclic G).trans
      (CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity G ℂ).symm |>.trans
        (by rw [Nat.card_eq_fintype_card])
  have hsurj : Function.Surjective (linearCharIrr (G := G)) :=
    ((Fintype.bijective_iff_injective_and_card (linearCharIrr (G := G))).2
      ⟨linearCharIrr_injective (G := G), hcard.symm⟩).2
  let ν : Irr G := ⟨χ, hχ⟩
  rcases hsurj ν with ⟨φ, hφ⟩
  have hχeq : χ = fun x => ((φ x : ℂˣ) : ℂ) := by
    exact (congrArg Subtype.val hφ).symm
  rw [hχeq]
  exact isLinearCharacter_of_hom φ

/-- Every nonzero character contains an irreducible constituent. -/
public theorem exists_irr_constituent_of_character {G : Type u} [Group G] [Fintype G]
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
public noncomputable def prodIrr : Irr G × Irr H → Irr (G × H) := fun p =>
  let χ : Irr G := p.1
  let ψ : Irr H := p.2
  ⟨prodChar χ.1 ψ.1, prodChar_isIrreducible χ.1 ψ.1 χ.2 ψ.2⟩

public theorem prodIrr_injective : Function.Injective (prodIrr (G := G) (H := H)) := by
  rintro ⟨χ, ψ⟩ ⟨χ', ψ'⟩ hEq
  have hEqC : prodChar χ.1 ψ.1 = prodChar χ'.1 ψ'.1 :=
    congrArg Subtype.val hEq
  have hnorm : scalarProductInv (G × H) (prodChar χ.1 ψ.1)
      (prodChar χ'.1 ψ'.1) = 1 := by
    rw [hEqC]
    exact isIrreducible_norm_inv_one
      (prodChar_isIrreducible χ'.1 ψ'.1 χ'.2 ψ'.2)
  have hfactor : scalarProductInv (G × H) (prodChar χ.1 ψ.1)
      (prodChar χ'.1 ψ'.1) =
      scalarProductInv G χ.1 χ'.1 * scalarProductInv H ψ.1 ψ'.1 :=
    scalarProductInv_prod_mul' χ.1 χ'.1 ψ.1 ψ'.1
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

public theorem prodIrr_card : Fintype.card (Irr G × Irr H) = Fintype.card (Irr (G × H)) := by
  have hprod : Nat.card (ConjClasses (G × H)) =
      Nat.card (ConjClasses G) * Nat.card (ConjClasses H) := by
    calc
      Nat.card (ConjClasses (G × H)) =
          Nat.card (ConjClasses G × ConjClasses H) :=
            Nat.card_congr (conjClassesProdEquiv (G := G) (H := H))
      _ = Nat.card (ConjClasses G) * Nat.card (ConjClasses H) := Nat.card_prod _ _
  rw [Fintype.card_prod, fintype_card_irr_eq_conjClasses G,
    fintype_card_irr_eq_conjClasses H, fintype_card_irr_eq_conjClasses (G × H)]
  exact hprod.symm

public theorem prodIrr_surjective : Function.Surjective (prodIrr (G := G) (H := H)) :=
  ((Fintype.bijective_iff_injective_and_card (prodIrr (G := G) (H := H))).2
    ⟨prodIrr_injective (G := G) (H := H), prodIrr_card (G := G) (H := H)⟩).2

/-- Every irreducible character of a direct product is a product of irreducible
characters of the factors. -/
public theorem irreducibleCharacter_eq_prodChar (φ : ClassFunction (G × H))
    (hφ : IsIrreducibleCharacter φ) :
    ∃ χ : Irr G, ∃ ψ : Irr H, prodChar χ.1 ψ.1 = φ := by
  let ν : Irr (G × H) := ⟨φ, hφ⟩
  rcases prodIrr_surjective (G := G) (H := H) ν with ⟨p, hp⟩
  let χ : Irr G := p.1
  let ψ : Irr H := p.2
  exact ⟨χ, ψ, by
    exact congrArg Subtype.val hp⟩

end CFSG.BenderGlauberman
