module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfE6Toral
public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeA2BlockTwoCore
public import CFSG.GroupTheory.ElemAbelianClosure

public noncomputable section

namespace CFSG.StandardType.E6RankFive

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.TableBExc.E6Three


theorem e6RankFive_primeField_toralTarget
    {Γ : Type} [CommGroup Γ] [Finite Γ]
    (hexp : ∀ a : Γ, a ^ 3 = 1) (hcard : 3 ^ 5 ≤ Nat.card Γ)
    (ζ : (AlgebraicClosure (ZMod 2))ˣ) (hζ : ζ ^ 3 = 1) (hζo : orderOf ζ = 3)
    (f : Γ →* adjointGroup Tag.E6 (AlgebraicClosure (ZMod 2)))
    (hf : Function.Injective f) :
    ∃ v : Γ → (Fin Tag.E6.rank → ZMod 3),
      ∃ g ∈ adjointGroup Tag.E6 (AlgebraicClosure (ZMod 2)),
        ∀ a : Γ,
          g * (f a : ModGL Tag.E6 (AlgebraicClosure (ZMod 2))) * g⁻¹ =
            rootDiagUnit Tag.E6 (zetaVec ζ hζ (v a)) := by
  classical
  let k := AlgebraicClosure (ZMod 2)
  let f' : Γ →* ModGL Tag.E6 k := (Subgroup.subtype (adjointGroup Tag.E6 k)).comp f
  have hf' : Function.Injective f' := by
    intro a b h
    exact hf (Subtype.ext h)
  let E : Subgroup (ModGL Tag.E6 k) := f'.range
  have hEel : CFSG.Open.IsElemAbelian 3 E :=
    CFSG.StandardType.isElemAbelian_range (p := 3)
      (fun a b => mul_comm a b) hexp f'
  have hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x :=
    fun x hx y hy => CFSG.Open.IsElemAbelian.comm hEel hx hy
  have hEexp : ∀ x ∈ E, x ^ 3 = 1 := fun x hx => hEel.2 x hx
  have hEadj : E ≤ adjointGroup Tag.E6 k := by
    rintro _ ⟨a, rfl⟩
    exact (f a).2
  have hEcard : Nat.card E = Nat.card Γ := Nat.card_range_of_injective hf'
  have hE5 : 3 ^ 5 ≤ Nat.card E := by
    rw [hEcard]
    exact hcard
  have hKnot3 : ¬ 3 ∣ Nat.card (ZMod 2) := by
    rw [Nat.card_zmod]
    norm_num
  obtain ⟨g, hgG, hgE⟩ :=
    CFSG.StandardType.ExcFramesHalf.bigElemAbelianToralBar_E6_three
      (ZMod 2) hKnot3 E hEadj hEcomm hEexp hE5
  have hf'pow : ∀ a : Γ, (f' a) ^ 3 = 1 := by
    intro a
    rw [← map_pow, hexp a, map_one]
  have hu3 : ∀ a : Γ, (g⁻¹ * f' a * g) ^ 3 = 1 := by
    intro a
    have hg : g⁻¹ * f' a * g = g⁻¹ * f' a * (g⁻¹)⁻¹ := by simp
    rw [hg, conj_pow, hf'pow a]
    group
  have hu_mem : ∀ a : Γ, g⁻¹ * f' a * g ∈ torusGroup Tag.E6 k :=
    fun a => hgE (f' a) ⟨a, rfl⟩
  choose v hv using fun a =>
    CFSG.StandardType.NoOffTwE6Three.exists_zetaVec_eq_of_mem_torusGroup_pow_three
      (Ω := k) hζ hζo (hu_mem a) (hu3 a)
  refine ⟨v, g⁻¹, inv_mem hgG, fun a => ?_⟩
  simpa [f', inv_inv] using hv a

end CFSG.StandardType.E6RankFive
