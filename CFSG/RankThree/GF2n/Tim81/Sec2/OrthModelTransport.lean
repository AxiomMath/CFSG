module

public import CFSG.RankThree.GF2n.Tim81.Sec2.SL2Small
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7Conj
public import CFSG.RankThree.GF2n.Tim81.Sec2.OrthModelCard

public section

namespace CFSG.RankThree.GF2n.Tim81.Sec2

open scoped MatrixGroups

open CFSG.Quasithin.JonesParshall CFSG.Quasithin.B45L2
open CFSG.QuasithinUnique.Setup.X7 CFSG.QuasithinUnique.Setup.SL2Modules

variable {F : Type} [Field F] [Fintype F] [CharP F 2] {l : ℕ}
  (hF : Fintype.card F = 2 ^ (2 * l)) (hl : 1 ≤ l)
  {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
  {ρ : Representation (ZMod 2) SL(2, F) W} (hρ : IsOrthModule hF ρ)

theorem fieldAut_image_sylow (A : Subgroup SL(2, F))
    (hA2 : ∀ a ∈ A, a * a = 1) (hA : Nat.card A = 2 ^ (2 * l)) (j : ℕ) :
    (∀ a ∈ A.map (fieldAut F j), a * a = 1) ∧
      Nat.card (A.map (fieldAut F j)) = 2 ^ (2 * l) := by
  constructor
  · rintro a ⟨b, hb, rfl⟩
    rw [← map_mul, hA2 b hb, map_one]
  · rw [Subgroup.card_map_of_injective (fieldAutEquiv j).injective]
    exact hA

variable [Algebra (ZMod 2) F]

theorem fixedSub_fieldAut_mem {j : ℕ} {β : W ≃+ ↥(hermA l F)}
    (hβ : ∀ g w, β (ρ g w) = hermAct l (sig_sig hF) (fieldAut F j g) (β w))
    (A : Subgroup SL(2, F)) (w : W) :
    w ∈ fixedSub ρ A ↔ β w ∈ fixedSub (hermRep l hF) (A.map (fieldAut F j)) := by
  constructor
  · intro hw g hg
    obtain ⟨a, ha, rfl⟩ := hg
    rw [hermRep_apply, ← hβ]
    exact congrArg β (hw a ha)
  · intro hw a ha
    apply β.injective
    rw [hβ]
    exact hw (fieldAut F j a) ⟨a, ha, rfl⟩

theorem IsOrthModule.card_fixedSub (hρ : IsOrthModule hF ρ) (A : Subgroup SL(2, F))
    (hA2 : ∀ a ∈ A, a * a = 1) (hA : Nat.card A = 2 ^ (2 * l)) :
    Nat.card ↥(fixedSub ρ A) = 2 ^ l := by
  obtain ⟨j, β, hβ⟩ := hρ
  have hs := fieldAut_image_sylow A hA2 hA j
  have hcard : Nat.card ↥(fixedSub ρ A) =
      Nat.card ↥(fixedSub (hermRep l hF) (A.map (fieldAut F j))) :=
    Nat.card_congr (Equiv.subtypeEquiv β.toEquiv fun w => fixedSub_fieldAut_mem (hF := hF) (j := j) hβ A w)
  rw [hcard]
  have hAeq : Nat.card (A.map (fieldAut F j)) = Nat.card F := by
    rw [hs.2, Nat.card_eq_fintype_card, hF]
  obtain ⟨x, hx⟩ := eq_conj_rootGroup (A.map (fieldAut F j)) hs.1 hAeq
  have hEq : A.map (fieldAut F j) = upperSylow.map (MulAut.conj x).toMonoidHom := by
    ext a
    rw [hx a]
    constructor
    · intro ha
      exact ⟨x⁻¹ * a * x, ha, by simp [MulAut.conj_apply]; group⟩
    · rintro ⟨s, hs, rfl⟩
      change x⁻¹ * (x * s * x⁻¹) * x ∈ upperSylow
      simpa [mul_assoc] using hs
  rw [hEq, fixedSub_map_conj]
  have hinj : Function.Injective (hermRep l hF x : ↥(hermA l F) → ↥(hermA l F)) := by
    intro u v h
    have := congrArg (hermRep l hF x⁻¹) h
    simpa using this
  exact (Nat.card_congr (Submodule.equivMapOfInjective (hermRep l hF x) hinj
    (fixedSub (hermRep l hF) upperSylow)).symm).trans (card_fixedSub_upperSylow (hF := hF))

end CFSG.RankThree.GF2n.Tim81.Sec2
