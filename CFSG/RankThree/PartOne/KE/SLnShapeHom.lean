module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LieType.Chevalley.LangFiniteSubfieldCongruence
public import CFSG.LinearAlgebra.LinearGroups.Generation
public import CFSG.RankThree.Chevalley.G2SplitPrimeToralCentralizers

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped MatrixGroups

variable {τ : Tag} {L : Type} [Field L] {ν : ℕ}

theorem exists_aut_of_rootData_hom (ρ : SL(ν, L) →* ModGL τ L) (hρinj : Function.Injective ρ)
    (r : Fin ν → Fin ν → (Fin τ.rank → ℤ)) (ε : Fin ν → Fin ν → Lˣ)
    (hgen : ∀ (i j : Fin ν) (hij : i ≠ j) (t : L),
      ρ (Matrix.SpecialLinearGroup.transvection hij t) = pinnedX τ L (r i j) ((ε i j : L) * t))
    (Fr : L →+* L) (hFr : Function.Bijective Fr) (Ψ : ModGL τ L →* ModGL τ L)
    (hΨinj : Function.Injective Ψ)
    (tgt : Fin ν → Fin ν → Fin ν × Fin ν) (htne : ∀ i j, i ≠ j → (tgt i j).1 ≠ (tgt i j).2)
    (htsurj : ∀ i j, i ≠ j → ∃ i' j', i' ≠ j' ∧ tgt i' j' = (i, j))
    (hΨ : ∀ i j, i ≠ j → ∃ b : Lˣ, ∀ c : L, Ψ (pinnedX τ L (r i j) c) =
      pinnedX τ L (r (tgt i j).1 (tgt i j).2) ((b : L) * Fr c)) :
    ∃ Φ' : SL(ν, L) ≃* SL(ν, L),
      (∀ X, Ψ (ρ X) = ρ (Φ' X)) ∧
      ∃ b : Fin ν → Fin ν → Lˣ, ∀ (i j : Fin ν) (hij : i ≠ j) (t : L),
        ((Φ' (Matrix.SpecialLinearGroup.transvection hij t) : SL(ν, L)) :
          Matrix (Fin ν) (Fin ν) L) = 1 + single (tgt i j).1 (tgt i j).2 ((b i j : L) * Fr t) := by
  classical
  choose! b hb using hΨ
  let b' : Fin ν → Fin ν → Lˣ := fun i j =>
    (ε (tgt i j).1 (tgt i j).2)⁻¹ * b i j * Units.map (Fr : L →* L) (ε i j)
  let ψ : SL(ν, L) →* ModGL τ L := Ψ.comp ρ
  have hψapply : ∀ X, ψ X = Ψ (ρ X) := fun X => rfl
  have hψgen : ∀ (i j : Fin ν) (hij : i ≠ j) (t : L),
      ψ (Matrix.SpecialLinearGroup.transvection hij t) =
        ρ (Matrix.SpecialLinearGroup.transvection (htne i j hij) ((b' i j : L) * Fr t)) := by
    intro i j hij t
    rw [hψapply, hgen i j hij t, hgen _ _ (htne i j hij)]
    rw [hb i j hij]
    congr 1
    simp only [b', Units.val_mul, Units.coe_map, map_mul, MonoidHom.coe_ofClass,
      Units.val_inv_eq_inv_val]
    field_simp
  have hrangeψ : ψ.range ≤ ρ.range := by
    rw [MonoidHom.range_eq_map, ← CFSG.LinearGroups.special_linear_elementary_generation (n := ν)
      (K := L), Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
    rintro _ ⟨i, j, hij, t, rfl⟩
    exact ⟨_, (hψgen i j hij t).symm⟩
  let e : SL(ν, L) ≃* ρ.range := MonoidHom.ofInjective hρinj
  let Φ'' : SL(ν, L) →* SL(ν, L) :=
    e.symm.toMonoidHom.comp (ψ.codRestrict ρ.range fun X => hrangeψ ⟨X, rfl⟩)
  have hΦ'' : ∀ X, ρ (Φ'' X) = ψ X := fun X => by
    have h := e.apply_symm_apply ⟨ψ X, hrangeψ ⟨X, rfl⟩⟩
    exact congrArg Subtype.val h
  have hψinj : Function.Injective ψ := hΨinj.comp hρinj
  have hΦ''inj : Function.Injective Φ'' := fun X Y h =>
    hψinj (by rw [← hΦ'' X, ← hΦ'' Y, h])
  have hΦ''gen : ∀ (i j : Fin ν) (hij : i ≠ j) (t : L),
      Φ'' (Matrix.SpecialLinearGroup.transvection hij t) =
        Matrix.SpecialLinearGroup.transvection (htne i j hij) ((b' i j : L) * Fr t) := by
    intro i j hij t
    apply hρinj
    rw [hΦ'', hψgen]
  have hΦ''surj : Function.Surjective Φ'' := by
    rw [← MonoidHom.range_eq_top, eq_top_iff,
      ← CFSG.LinearGroups.special_linear_elementary_generation (n := ν) (K := L),
      Subgroup.closure_le]
    rintro _ ⟨i', j', hij', c, rfl⟩
    obtain ⟨i, j, hij, htg⟩ := htsurj i' j' hij'
    obtain ⟨h1, h2⟩ := Prod.ext_iff.1 htg
    subst h1
    subst h2
    obtain ⟨t, ht⟩ := hFr.2 (((b' i j)⁻¹ : Lˣ) * c)
    refine ⟨Matrix.SpecialLinearGroup.transvection hij t, ?_⟩
    rw [hΦ''gen]
    congr 2
    rw [ht, ← mul_assoc, Units.mul_inv, one_mul]
  refine ⟨MulEquiv.ofBijective Φ'' ⟨hΦ''inj, hΦ''surj⟩,
    fun X => (hψapply X).symm.trans (hΦ'' X).symm, b', fun i j hij t => ?_⟩
  change ((Φ'' (Matrix.SpecialLinearGroup.transvection hij t) : SL(ν, L)) :
    Matrix (Fin ν) (Fin ν) L) = _
  rw [hΦ''gen, CFSG.LinearGroups.coe_transvection]

end CFSG.RankThree.PartOne.KE
