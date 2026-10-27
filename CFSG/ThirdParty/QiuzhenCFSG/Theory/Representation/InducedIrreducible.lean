module

public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Character.BrauerPermutation
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.SolvableDimension
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.Induction
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.ConjugateRep
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.RepEquiv

namespace CFSG
end CFSG
open CFSG

/-!
# Irreducibility of induced representations

Isaacs, *Character Theory of Finite Groups*, Theorem 6.34, for ordinary
complex irreducible representations: under a centralizer hypothesis, the
inertia subgroup of an irreducible representation of a normal subgroup equals
the subgroup, and the induced representation is irreducible.
-/

noncomputable section


namespace CFSG.Theory.Representation

open _root_.Representation


theorem isaacs_6_34_inertia
    {G : Type*} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal]
    (hcentralizer : forall n : N, n ≠ 1 ->
      Subgroup.centralizer ({(n : G)} : Set G) ≤ N)
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (phi : Representation ℂ N V)
    (hphi : Representation.IsIrreducible phi)
    (hnonprincipal : ¬ Nonempty (phi ≃ₗ Representation.trivial ℂ N ℂ)) :
    forall g : G,
      Nonempty (phi ≃ₗ Theory.Representation.conjugateRep (G := G) (H := N) phi g) ↔
        g ∈ N := by
  let : Representation.IsIrreducible phi := hphi
  intro g
  constructor
  · intro hequiv
    by_contra hg
    let chi : Theory.Character.ConjClassFunction N :=
      Theory.Character.characterClassFunction phi
    let tau : Representation ℂ N ℂ := Representation.trivial ℂ N ℂ
    have htau : Representation.IsIrreducible tau :=
      Theory.Character.trivial_complex_irreducible
    let : Representation.IsIrreducible tau := htau
    let e := Classical.choice hequiv
    have hchiIrr : Theory.Character.IsIrreducibleConjCharacter chi :=
      Theory.Character.isIrreducibleCharacter_characterClassFunction phi hphi
    have htauIrr :
        Theory.Character.IsIrreducibleConjCharacter
          (Theory.Character.characterClassFunction tau) :=
      Theory.Character.isIrreducibleCharacter_characterClassFunction tau htau
    have hcharNe :
        chi ≠ Theory.Character.characterClassFunction tau := by
      intro hchars
      apply hnonprincipal
      have hcard : ¬ ringChar ℂ ∣ Nat.card N := by
        rw [show ringChar ℂ = 0 from ringChar.eq_zero, zero_dvd_iff]
        exact Nat.ne_of_gt Nat.card_pos
      rcases Theory.Character.equiv_of_irreducible_char_eq
          (ρ := tau) (σ := phi) hcard (by
            funext x
            have hx := congrFun (show
              Theory.Character.characterClassFunction phi =
                Theory.Character.characterClassFunction tau from hchars) (ConjClasses.mk x)
            exact hx.symm) with ⟨he⟩
      exact ⟨Theory.Representation.RepEquiv.mk he.toLinearEquiv he.isIntertwining'⟩
    have hchiFix :
        Theory.Character.classFunctionConjLinearEquiv N g⁻¹ chi = chi := by
      dsimp [chi]
      rw [Theory.Character.classFunctionConjLinearEquiv_characterClassFunction]
      ext c
      rcases ConjClasses.exists_rep c with ⟨x, rfl⟩
      change (show Representation ℂ N V from
        phi.comp (Theory.Character.normalSubgroupConjMulEquiv N g⁻¹).symm.toMonoidHom).character x =
          phi.character x
      have hconj :
          (Theory.Character.normalSubgroupConjMulEquiv N g⁻¹).symm =
            Theory.Character.normalSubgroupConjMulEquiv N g := by
        ext y
        simp [Theory.Character.normalSubgroupConjMulEquiv, mul_assoc]
      rw [hconj]
      change (Theory.Representation.conjugateRep phi g).character x = phi.character x
      exact (congrFun (Representation.char_iso
        (Representation.Equiv.mk e.toLinearEquiv e.isIntertwining')) x).symm
    have htauFix :
        Theory.Character.classFunctionConjLinearEquiv N g⁻¹
            (Theory.Character.characterClassFunction tau) =
          Theory.Character.characterClassFunction tau := by
      rw [Theory.Character.classFunctionConjLinearEquiv_characterClassFunction]
      ext c
      rcases ConjClasses.exists_rep c with ⟨x, rfl⟩
      rfl
    rcases Theory.Character.exists_nontrivial_fixed_conjClass_of_two_fixed_irreducible
        N g⁻¹ hchiIrr htauIrr hchiFix htauFix hcharNe with
      ⟨x, hxne, hxconj⟩
    rcases isConj_iff.mp hxconj with ⟨n, hn⟩
    have hnG :
        (n : G) * (g⁻¹ * (x : G) * g) * (n : G)⁻¹ = (x : G) := by
      simpa [Theory.Character.normalSubgroupConjMulEquiv] using congrArg Subtype.val hn
    have ha :
        g⁻¹ * (x : G) * g = (n : G)⁻¹ * (x : G) * (n : G) := by
      calc
        g⁻¹ * (x : G) * g =
            ((n : G)⁻¹ * (n : G)) * (g⁻¹ * (x : G) * g) *
              ((n : G)⁻¹ * (n : G)) := by simp
        _ = (n : G)⁻¹ *
              ((n : G) * (g⁻¹ * (x : G) * g) * (n : G)⁻¹) *
                (n : G) := by simp [mul_assoc]
        _ = (n : G)⁻¹ * (x : G) * (n : G) := by rw [hnG]
    have hcconj :
        (g * (n : G)⁻¹) * (x : G) * (g * (n : G)⁻¹)⁻¹ = (x : G) := by
      calc
        (g * (n : G)⁻¹) * (x : G) * (g * (n : G)⁻¹)⁻¹ =
            g * ((n : G)⁻¹ * (x : G) * (n : G)) * g⁻¹ := by
              simp [mul_assoc]
        _ = g * (g⁻¹ * (x : G) * g) * g⁻¹ := by rw [← ha]
        _ = (x : G) := by simp [mul_assoc]
    have hcmem : g * (n : G)⁻¹ ∈ N := by
      apply hcentralizer x hxne
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (mul_inv_eq_iff_eq_mul.mp hcconj)
    have hgn : (g * (n : G)⁻¹) * (n : G) ∈ N :=
      N.mul_mem hcmem n.property
    apply hg
    simpa [mul_assoc] using hgn
  · intro hg
    exact ⟨conj_equiv_of_mem phi ⟨g, hg⟩⟩

def isaacs_6_34_standardRep
    {F G V : Type*} [Field F] [Group G]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (rho : Representation F G V) :
    Representation F G (ULift (Fin (Module.finrank F V) → F)) :=
  let e : V ≃ₗ[F] ULift (Fin (Module.finrank F V) → F) :=
    (Module.finBasis F V).equivFun.trans ULift.moduleEquiv.symm
  { toFun := fun g => e.conj (rho g)
    map_one' := by
      ext x
      simp [LinearEquiv.conj_apply]
    map_mul' := by
      intro g h
      ext x
      simp [LinearEquiv.conj_apply, map_mul] }

def isaacs_6_34_standardRepEquiv
    {F G V : Type*} [Field F] [Group G]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (rho : Representation F G V) : rho ≃ₗ isaacs_6_34_standardRep rho := by
  let e : V ≃ₗ[F] ULift (Fin (Module.finrank F V) → F) :=
    (Module.finBasis F V).equivFun.trans ULift.moduleEquiv.symm
  refine Theory.Representation.RepEquiv.mk e ?_
  intro g
  ext v
  simp [isaacs_6_34_standardRep, e, LinearEquiv.conj_apply]

def isaacs_6_34_coindRepEquivOfRepEquiv
    {F G H V W : Type*} [Field F] [Group G] [Group H]
    [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    (i : H →* G) {rho : Representation F H V} {sigma : Representation F H W}
    (e : rho ≃ₗ sigma) :
    Representation.coind i rho ≃ₗ Representation.coind i sigma := by
  let f := Representation.coindMap i e.toRepMap
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      funext g
      have h : e (x.1 g) = e (y.1 g) := congrArg (fun z => z.1 g) hxy
      exact e.injective h
    · intro y
      let x := Representation.coindMap i e.symm.toRepMap y
      refine ⟨x, ?_⟩
      apply Subtype.ext
      funext g
      change e (e.symm (y.1 g)) = y.1 g
      exact e.apply_symm_apply _
  refine Theory.Representation.RepEquiv.mk (LinearEquiv.ofBijective f.toLinearMap hf) ?_
  exact f.isIntertwining'

/-- Isaacs, Character Theory of Finite Groups, Theorem 6.34. -/
public theorem isaacs_theorem_6_34
    {G : Type*} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal]
    (hcentralizer : forall n : N, n ≠ 1 ->
      Subgroup.centralizer ({(n : G)} : Set G) ≤ N) :
    (forall {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
      (phi : Representation ℂ N V),
      Representation.IsIrreducible phi ->
        ¬ Nonempty (phi ≃ₗ Representation.trivial ℂ N ℂ) ->
          (forall g : G,
            Nonempty (phi ≃ₗ
              Theory.Representation.conjugateRep (G := G) (H := N) phi g) ↔ g ∈ N) ∧
            Representation.IsIrreducible (Representation.ind N.subtype phi)) ∧
      (forall {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
        (chi : Representation ℂ G W),
        Representation.IsIrreducible chi ->
          ¬ N ≤ chi.ker ->
            exists (V : Type*) (instAddV : AddCommGroup V) (instModuleV : Module ℂ V)
              (instFiniteV : FiniteDimensional ℂ V),
              letI : AddCommGroup V := instAddV
              letI : Module ℂ V := instModuleV
              letI : FiniteDimensional ℂ V := instFiniteV
              exists phi : Representation ℂ N V,
                Representation.IsIrreducible phi ∧
                  Nonempty (chi ≃ₗ Representation.ind N.subtype phi)) := by
  constructor
  · intro V _ _ _ phi hphi hnonprincipal
    let : Representation.IsIrreducible phi := hphi
    have hinertia := isaacs_6_34_inertia N hcentralizer phi hphi hnonprincipal
    have hnconj :
        ∀ x : G, (x : G ⧸ N) ≠ 1 →
          ¬ Nonempty (phi ≃ₗ Theory.Representation.conjugateRep phi x) := by
      intro x hx he
      have hxN : x ∈ N := (hinertia x).mp he
      apply hx
      simpa [QuotientGroup.eq_one_iff] using hxN
    have hcoind :
        Representation.IsIrreducible (Representation.coind N.subtype phi) :=
      coindRep_irreducible_of_noNontrivialConj phi hnconj
    let eICm := Theory.Representation.indCoindEquiv N phi
    let eIC : Representation.ind N.subtype phi ≃ₗ Representation.coind N.subtype phi :=
      Theory.Representation.RepEquiv.mk eICm.toLinearEquiv eICm.isIntertwining'
    exact ⟨hinertia, (Theory.Representation.RepEquiv.irreducible_euqiv eIC).mpr hcoind⟩
  · intro W _ _ _ chi hchi hN
    let : Representation.IsIrreducible chi := hchi
    let chiN : Representation ℂ N W := chi.comp N.subtype
    have hcr : chiN.IsCompletelyReducible :=
      Representation.isCompletelyReducible_of_ringChar_eq_zero_or_prime_coprime
        (ρ := chiN) (Or.inl ringChar.eq_zero)
    have htop : ¬ (⊤ : Subgroup N) ≤ chiN.ker := by
      intro htopKer
      apply hN
      intro n hn
      have hn' := htopKer (show (⟨n, hn⟩ : N) ∈ (⊤ : Subgroup N) by trivial)
      simpa [chiN] using hn'
    obtain ⟨m, hmSimple, hmNontrivial⟩ :=
      @exists_simple_submodule_not_le_ker_of_semisimple
        N inferInstance ℂ inferInstance W inferInstance inferInstance chiN hcr
        (⊤ : Subgroup N) htop
    let M : Subrepresentation chiN := Subrepresentation.ofSubmodule' m
    have hMirr : Representation.IsIrreducible M.toRepresentation :=
      irreducible_subrepresentation_of_simple_asModuleSubmodule chiN hmSimple
    let : Representation.IsIrreducible M.toRepresentation := hMirr
    let : FiniteDimensional ℂ M.toSubmodule :=
      FiniteDimensional.of_injective M.toSubmodule.subtype Subtype.val_injective
    have hMnonprincipal :
        ¬ Nonempty (M.toRepresentation ≃ₗ Representation.trivial ℂ N ℂ) := by
      rintro ⟨e⟩
      apply hmNontrivial
      intro n _
      rw [MonoidHom.mem_ker]
      ext v
      have hv : M.toRepresentation n v = v :=
        e.injective (by simpa using e.isIntertwining n v)
      simpa [M] using congrArg Subtype.val hv
    have hMinertia :=
      isaacs_6_34_inertia N hcentralizer M.toRepresentation hMirr hMnonprincipal
    have hMnconj :
        ∀ x : G, (x : G ⧸ N) ≠ 1 →
          ¬ Nonempty (M.toRepresentation ≃ₗ
            Theory.Representation.conjugateRep M.toRepresentation x) := by
      intro x hx he
      have hxN : x ∈ N := (hMinertia x).mp he
      apply hx
      simpa [QuotientGroup.eq_one_iff] using hxN
    let ecoind : chi ≃ₗ Representation.coind N.subtype M.toRepresentation :=
      coindEquivOfSubrep_noNontrivialConj chi (Or.inl ringChar.eq_zero) M hMnconj
    let phi := isaacs_6_34_standardRep M.toRepresentation
    let eStd : M.toRepresentation ≃ₗ phi :=
      isaacs_6_34_standardRepEquiv M.toRepresentation
    let eCoind :
        Representation.coind N.subtype M.toRepresentation ≃ₗ
          Representation.coind N.subtype phi :=
      isaacs_6_34_coindRepEquivOfRepEquiv N.subtype eStd
    let eICm := (Theory.Representation.indCoindEquiv N phi).symm
    let eIC : Representation.coind N.subtype phi ≃ₗ Representation.ind N.subtype phi :=
      Theory.Representation.RepEquiv.mk eICm.toLinearEquiv eICm.isIntertwining'
    have hphi : Representation.IsIrreducible phi :=
      (Theory.Representation.RepEquiv.irreducible_euqiv eStd).mp hMirr
    refine ⟨ULift (Fin (Module.finrank ℂ M.toSubmodule) → ℂ), inferInstance, inferInstance,
      inferInstance, ?_⟩
    exact ⟨phi, hphi, ⟨ecoind.trans (eCoind.trans eIC)⟩⟩

end CFSG.Theory.Representation
