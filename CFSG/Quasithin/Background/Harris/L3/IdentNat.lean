module

public import CFSG.Quasithin.Background.Harris.L3.Cases
public import CFSG.Quasithin.Background.Harris.L3.IdentDual

public section

namespace CFSG.Quasithin.G11.Harris.L3

open Matrix CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem natShape_injective {L : Subgroup (GLV V)} {F : Type} [Field F] {π : SL(3, F) →* ↥L}
    (h : NatShape L π) : Function.Injective π := by
  obtain ⟨ψ, hψ, E, hE⟩ := h
  rw [injective_iff_map_eq_one]
  intro g hg
  have h1 : ((ψ g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = 1 := by
    have hall : ∀ x : Fin 3 → F, ((ψ g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ x = x := by
      intro x
      obtain ⟨w, rfl⟩ := E.surjective x
      rw [← hE g w, repOfHom_apply, hg]
      rfl
    ext i j
    have := congrFun (hall (Pi.single j 1)) i
    simpa [Matrix.mulVec_single_one, Matrix.one_apply, Pi.single_apply] using this
  have h2 : ψ g = 1 := Subtype.ext h1
  rw [← hψ g, h2, map_one]

@[expose] def lowTv {F : Type} [Field F] (j : Fin 3) (hj : j ≠ 2) (a : F) : SL(3, F) :=
  ⟨transvection 2 j a, det_transvection_of_ne 2 j hj.symm a⟩

theorem coe_lowTv {F : Type} [Field F] (j : Fin 3) (hj : j ≠ 2) (a : F) :
    ((lowTv j hj a : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = transvection 2 j a := rfl

theorem transvection_mulVec' {F : Type} [Field F] (k l : Fin 3) (t : F) (u : Fin 3 → F) :
    transvection k l t *ᵥ u = u + (Pi.single k (t * u l) : Fin 3 → F) := by
  rw [Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec]
  rfl

theorem not_selfDual_natShape [Finite V] {L : Subgroup (GLV V)} {F : Type} [Field F] [Finite F]
    {π : SL(3, F) →* ↥L} (h : NatShape L π) : ¬ SelfDual L ⊤ := by
  classical
  intro hsd
  obtain ⟨ψ, hψ, E, hE⟩ := h
  have hact : ∀ (j : Fin 3) (hj : j ≠ 2) (a : F) (w : V),
      E (((π (ψ (lowTv j hj a)) : ↥L) : GLV V) w) = E w + Pi.single 2 (a * E w j) := by
    intro j hj a w
    have := hE (ψ (lowTv j hj a)) w
    rw [hψ, coe_lowTv, transvection_mulVec'] at this
    exact this
  let Q : Set (GLV V) := {q | ∃ (j : Fin 3) (hj : j ≠ 2) (a : F),
    q = ((π (ψ (lowTv j hj a)) : ↥L) : GLV V)}
  have hQ : Q ⊆ (L : Set (GLV V)) := by
    rintro q ⟨j, hj, a, rfl⟩
    exact (π _).2
  let θ : V →+ F × F := AddMonoidHom.prod
    ((Pi.evalAddMonoidHom (fun _ : Fin 3 => F) 0).comp E.toAddMonoidHom)
    ((Pi.evalAddMonoidHom (fun _ : Fin 3 => F) 1).comp E.toAddMonoidHom)
  have hW : ∀ q ∈ Q, ∀ v, (q : GLV V) v - v ∈ kerSub θ := by
    rintro q ⟨j, hj, a, rfl⟩ v
    rw [mem_kerSub]
    have h1 := hact j hj a v
    have h2 : E (((π (ψ (lowTv j hj a)) : ↥L) : GLV V) v - v) =
        Pi.single 2 (a * E v j) := by rw [map_sub, h1]; abel
    have h0 : (0 : Fin 3) ≠ 2 := by decide
    have h1' : (1 : Fin 3) ≠ 2 := by decide
    ext
    · show E _ 0 = 0
      rw [h2]; simp [h0]
    · show E _ 1 = 0
      rw [h2]; simp [h1']
  have hbound := card_le_mul_card_fixed hsd Q hQ (kerSub θ) hW
  have hWc : Nat.card (kerSub θ) ≤ Nat.card F := by
    refine Nat.card_le_card_of_injective (fun w => E w.1 2) fun a b hab => ?_
    have ha := (mem_kerSub θ a.1).1 a.2
    have hb := (mem_kerSub θ b.1).1 b.2
    have ha0 : E a.1 0 = 0 := congrArg Prod.fst ha
    have ha1 : E a.1 1 = 0 := congrArg Prod.snd ha
    have hb0 : E b.1 0 = 0 := congrArg Prod.fst hb
    have hb1 : E b.1 1 = 0 := congrArg Prod.snd hb
    apply Subtype.ext
    apply E.injective
    funext i
    fin_cases i
    · exact ha0.trans hb0.symm
    · exact ha1.trans hb1.symm
    · exact hab
  have hCc : Nat.card {y : V // ∀ q ∈ Q, (q : GLV V) y = y} ≤ Nat.card F := by
    refine Nat.card_le_card_of_injective (fun w => E w.1 2) fun a b hab => ?_
    have key : ∀ y : {y : V // ∀ q ∈ Q, (q : GLV V) y = y}, E y.1 0 = 0 ∧ E y.1 1 = 0 := by
      intro y
      have hf : ∀ (j : Fin 3) (hj : j ≠ 2), E y.1 j = 0 := by
        intro j hj
        have h1 := hact j hj 1 y.1
        rw [y.2 _ ⟨j, hj, 1, rfl⟩] at h1
        have h2 := congrFun (add_eq_left.mp h1.symm) 2
        simpa using h2
      exact ⟨hf 0 (by decide), hf 1 (by decide)⟩
    apply Subtype.ext
    apply E.injective
    funext i
    fin_cases i
    · exact (key a).1.trans (key b).1.symm
    · exact (key a).2.trans (key b).2.symm
    · exact hab
  have hV : Nat.card V = Nat.card F ^ 3 := by
    rw [Nat.card_congr E.toEquiv, Nat.card_fun, Nat.card_fin]
  have h2 : 2 ≤ Nat.card F := Finite.one_lt_card
  have : Nat.card F ^ 3 ≤ Nat.card F * Nat.card F :=
    hV ▸ hbound.trans (Nat.mul_le_mul hWc hCc)
  nlinarith

theorem isNaturalMatrixModule_of_natShape {L : Subgroup (GLV V)} {F : Type} [Field F]
    [Algebra (ZMod 2) F] {π : SL(3, F) →* ↥L} (hπ : Function.Surjective π) (h : NatShape L π) :
    IsNaturalMatrixModule L (StatedSL 3 F) := by
  have hinj := natShape_injective h
  obtain ⟨ψ, hψ, E, hE⟩ := h
  let πe : SL(3, F) ≃* ↥L := MulEquiv.ofBijective π ⟨hinj, hπ⟩
  let ψe : SL(3, F) ≃* SL(3, F) := MulEquiv.mk' (Equiv.mk ψ ψ hψ hψ) ψ.map_mul
  let φ : ↥L ≃* ↥(StatedSL 3 F) :=
    πe.symm.trans (ψe.trans (specialLinearGroupEquivStatedSL 3 F))
  let Ez : V ≃ₗ[ZMod 2] (Fin 3 → F) :=
    LinearEquiv.mk (AddMonoidHom.toZModLinearMap 2 E.toAddMonoidHom) E.symm E.left_inv E.right_inv
  refine ⟨φ, Ez, fun l v => ?_⟩
  have h1 := hE (πe.symm l) v
  have h2 : repOfHom L π (πe.symm l) v = ((l : ↥L) : GLV V) v := by
    rw [repOfHom_apply]
    exact congrArg (fun x : ↥L => (x : GLV V) v) (πe.apply_symm_apply l)
  rw [h2] at h1
  exact h1

theorem card_of_natShape {L : Subgroup (GLV V)} {F : Type} [Field F] {π : SL(3, F) →* ↥L}
    (h : NatShape L π) : Nat.card V = Nat.card F ^ 3 := by
  obtain ⟨ψ, hψ, E, hE⟩ := h
  rw [Nat.card_congr E.toEquiv, Nat.card_fun, Nat.card_fin]

end CFSG.Quasithin.G11.Harris.L3
