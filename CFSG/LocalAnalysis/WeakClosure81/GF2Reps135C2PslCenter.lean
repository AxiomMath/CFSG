module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open
open CFSG.Blueprint (LieModel)

private def c2slcen_psi {W : Type} [CommGroup W] {L : Subgroup (MulAut W)}
    (z : ↥L) : AddMonoid.End (Additive W) where
  toFun w := Additive.ofMul ((z : MulAut W) (Additive.toMul w))
  map_zero' := by simp
  map_add' := by
    intro a b
    simp only [toMul_add, map_mul, ofMul_mul]

private lemma c2slcen_psi_apply {W : Type} [CommGroup W] {L : Subgroup (MulAut W)}
    (z : ↥L) (w : Additive W) :
    c2slcen_psi z w = Additive.ofMul ((z : MulAut W) (Additive.toMul w)) := rfl

private lemma c2slcen_psi_mem {W : Type} [CommGroup W] {L : Subgroup (MulAut W)}
    {z : ↥L} (hz : z ∈ Subgroup.center ↥L) : c2slcen_psi z ∈ LEnd L := by
  change ∀ g ∈ L, ∀ w : Additive W,
    c2slcen_psi z (Additive.ofMul (g (Additive.toMul w))) =
      Additive.ofMul (g (Additive.toMul (c2slcen_psi z w)))
  intro g hg w
  have hcg : g * (z : MulAut W) = (z : MulAut W) * g :=
    congrArg (fun e : ↥L => (e : MulAut W)) ((Subgroup.mem_center_iff.mp hz) ⟨g, hg⟩)
  have h3 : ∀ x : W, g ((z : MulAut W) x) = (z : MulAut W) (g x) :=
    fun x => congrArg (fun e : MulAut W => e x) hcg
  show Additive.ofMul ((z : MulAut W) (g (Additive.toMul w))) =
    Additive.ofMul (g ((z : MulAut W) (Additive.toMul w)))
  rw [h3 (Additive.toMul w)]

private lemma c2slcen_eq_one_of_mem_center {W : Type} [CommGroup W]
    {L : Subgroup (MulAut W)} (hend : Nat.card (LEnd L) = 2) {z : ↥L}
    (hz : z ∈ Subgroup.center ↥L) : z = 1 := by
  have hmem : c2slcen_psi z ∈ LEnd L := c2slcen_psi_mem hz
  obtain ⟨x, y, hxy, -⟩ := Nat.card_eq_two_iff.mp hend
  haveI : Nontrivial (LEnd L) := ⟨x, y, hxy⟩
  obtain ⟨y₀, -, hyuniq⟩ := (Nat.card_eq_two_iff' (0 : LEnd L)).mp hend
  have hy1 : y₀ = 1 := (hyuniq 1 (one_ne_zero : (1 : LEnd L) ≠ 0)).symm
  have hpsi : (⟨c2slcen_psi z, hmem⟩ : LEnd L) = 0 ∨
      (⟨c2slcen_psi z, hmem⟩ : LEnd L) = 1 := by
    by_cases h : (⟨c2slcen_psi z, hmem⟩ : LEnd L) = 0
    · exact Or.inl h
    · exact Or.inr (by rw [hyuniq _ h, hy1])
  have hzW : (z : MulAut W) = 1 := by
    refine MulEquiv.ext fun w => ?_
    rcases hpsi with h0 | h1
    · have hval : c2slcen_psi z = 0 := congrArg Subtype.val h0
      have h := congrArg (fun e : AddMonoid.End (Additive W) => e (Additive.ofMul w)) hval
      have hw : (z : MulAut W) w = 1 := by
        have h' : Additive.ofMul ((z : MulAut W) w) = 0 := by
          simpa [c2slcen_psi_apply] using h
        simpa using h'
      have hw1 : w = 1 := (z : MulAut W).injective (by rw [hw, map_one])
      rw [hw, hw1]
      simp
    · have hval : c2slcen_psi z = 1 := congrArg Subtype.val h1
      have h := congrArg (fun e : AddMonoid.End (Additive W) => e (Additive.ofMul w)) hval
      exact (Additive.ofMul (α := W)).injective (by simpa [c2slcen_psi_apply] using h)
  exact Subtype.ext hzW

theorem w135c2_lieModel_of_lend_card_two {W : Type} [CommGroup W] {L : Subgroup (MulAut W)}
    (hend : Nat.card (LEnd L) = 2) {t : StatedLieTag} {n p f : ℕ}
    (hlie : LieModel (↥L ⧸ Subgroup.center ↥L) t n p f) : LieModel ↥L t n p f := by
  have hcenter : Subgroup.center ↥L = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    exact c2slcen_eq_one_of_mem_center hend hz
  let e : (↥L ⧸ Subgroup.center ↥L) ≃* ↥L :=
    (QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot
  exact CFSG.Blueprint.LieModel.of_mulEquiv e hlie

end CFSG.LocalAnalysis.WeakClosure81
