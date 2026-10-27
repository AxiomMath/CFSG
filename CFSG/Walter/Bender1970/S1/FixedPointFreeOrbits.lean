module

public import Mathlib.RepresentationTheory.Invariants
import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.PermutationBasisOrbits

public section

namespace CFSG.Walter

open Module

variable {K G V : Type*} [Field K] [Group G] [AddCommGroup V] [Module K V]

theorem finrank_eq_card_mul_finrank_invariants_of_basis {ι : Type*} [Finite G] [Finite ι]
    [MulAction G ι] (σ : Representation K G V) (b : Basis ι K V)
    (hb : ∀ (g : G) (i : ι), σ g (b i) = b (g • i))
    (hfree : ∀ (g : G) (i : ι), g • i = i → g = 1) :
    finrank K V = Nat.card G * finrank K σ.invariants := by
  classical
  have := Fintype.ofFinite G
  have := Fintype.ofFinite ι
  rw [CFSG.Theory.Representation.permutedBasis_fixedSubspace_finrank_eq_orbitQuotient_card σ b hb,
    finrank_eq_nat_card_basis b]
  have hB := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group G ι
  rw [Finset.sum_eq_single (1 : G)] at hB
  · have h1 : Fintype.card (MulAction.fixedBy ι (1 : G)) = Fintype.card ι :=
      Fintype.card_congr (Equiv.subtypeUnivEquiv fun i => by simp)
    simp only [Fintype.card_eq_nat_card] at hB h1
    rw [← h1, hB, mul_comm]
  · intro g _ hg
    exact Fintype.card_eq_zero_iff.mpr ⟨fun i => hg (hfree g i i.2)⟩
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem finrank_eq_card_mul_finrank_invariants_of_iSupIndep {X : Type*} [Finite G]
    [FiniteDimensional K V] [MulAction G X] (σ : Representation K G V) (E : X → Submodule K V)
    (hind : iSupIndep E) (htop : ⨆ x, E x = ⊤)
    (hmap : ∀ (g : G) (x : X), ∀ v ∈ E x, σ g v ∈ E (g • x))
    (hfree : ∀ (g : G) (x : X), g • x = x → E x ≠ ⊥ → g = 1) :
    finrank K V = Nat.card G * finrank K σ.invariants := by
  classical
  have hinj (g : G) : Function.Injective (σ g) := fun v w h => by
    simpa using congrArg (σ g⁻¹) h
  have heq (g : G) (x : X) : (E x).map (σ g) = E (g • x) := by
    refine le_antisymm (Submodule.map_le_iff_le_comap.mpr fun v hv => hmap g x v hv)
      fun w hw => ⟨σ g⁻¹ w, ?_, by simp⟩
    simpa using hmap g⁻¹ (g • x) w hw
  let Y : SubMulAction G X :=
    { carrier := {x | E x ≠ ⊥}
      smul_mem' := fun g x (hx : E x ≠ ⊥) => by
        change E (g • x) ≠ ⊥
        rw [← heq]
        exact fun h => hx (Submodule.map_injective_of_injective (hinj g)
          (h.trans (Submodule.map_bot _).symm)) }
  have : Finite Y := by
    have := hind.fintypeNeBotOfFiniteDimensional
    exact Finite.of_equiv {x // E x ≠ ⊥} (Equiv.subtypeEquivRight fun x => Iff.rfl)
  let Q := MulAction.orbitRel.Quotient G Y
  let φ : G × Q → Y := fun p => p.1 • p.2.out
  have hφ_inj : Function.Injective φ := by
    rintro ⟨g, q⟩ ⟨g', q'⟩ (h : g • q.out = g' • q'.out)
    have hq : (Quotient.mk _ q.out : Q) = Quotient.mk _ q'.out :=
      Quotient.sound ⟨g⁻¹ * g', by dsimp only; rw [mul_smul, ← h, inv_smul_smul]⟩
    obtain rfl : q = q' := by rwa [Quotient.out_eq, Quotient.out_eq] at hq
    have h' : (g'⁻¹ * g) • q.out = q.out := by rw [mul_smul, h, inv_smul_smul]
    exact Prod.ext (inv_mul_eq_one.mp (hfree _ _ (congrArg Subtype.val h') q.out.2)).symm rfl
  have hφ_surj : Function.Surjective φ := by
    intro y
    obtain ⟨g, hg⟩ := Quotient.mk_out (s := MulAction.orbitRel G Y) y
    exact ⟨(g⁻¹, Quotient.mk _ y), by simp only [φ]; rw [← hg, inv_smul_smul]⟩
  let F : G × Q → Submodule K V := fun p => E (φ p)
  have hFind : iSupIndep F := (hind.comp Subtype.val_injective).comp hφ_inj
  have hFtop : ⨆ p, F p = ⊤ := by
    rw [← htop, ← iSup_ne_bot_subtype E]
    exact hφ_surj.iSup_comp fun y : Y => E y
  have hint : DirectSum.IsInternal F :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hFind hFtop
  let d : Q → ℕ := fun q => finrank K (E q.out)
  let β (q : Q) : Basis (Fin (d q)) K (E q.out) := Module.finBasis K (E q.out)
  have hEq (p : G × Q) : (E (p.2.out : X)).map (σ p.1) = F p := heq p.1 p.2.out
  let e (p : G × Q) : E (p.2.out : X) ≃ₗ[K] F p :=
    (Submodule.equivMapOfInjective (σ p.1) (hinj p.1) _).trans (LinearEquiv.ofEq _ _ (hEq p))
  let v (p : G × Q) : Basis (Fin (d p.2)) K (F p) := (β p.2).map (e p)
  let b := hint.collectedBasis v
  have hb (a : Σ p : G × Q, Fin (d p.2)) : b a = σ a.1.1 (β a.1.2 a.2) := by
    simp [b, v, e, DirectSum.IsInternal.collectedBasis_coe]
  let _ : MulAction G (Σ p : G × Q, Fin (d p.2)) :=
    { smul := fun g a => ⟨(g * a.1.1, a.1.2), a.2⟩
      one_smul := fun a => Sigma.ext (Prod.ext (one_mul _) rfl) HEq.rfl
      mul_smul := fun g h a => Sigma.ext (Prod.ext (mul_assoc _ _ _) rfl) HEq.rfl }
  refine finrank_eq_card_mul_finrank_invariants_of_basis σ b (fun g a => ?_) (fun g a h => ?_)
  · change σ g (b a) = b ⟨(g * a.1.1, a.1.2), a.2⟩
    rw [hb, hb, map_mul, Module.End.mul_apply]
  · have h1 : g * a.1.1 = a.1.1 := congrArg (fun a : Σ p : G × Q, Fin (d p.2) => a.1.1) h
    exact mul_right_cancel (h1.trans (one_mul _).symm)

end CFSG.Walter
