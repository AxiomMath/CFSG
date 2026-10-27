module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownChevGeom
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownOmegaPlusSub
public import CFSG.RankThree.PartOne.KC.SymplecticSubfieldCentralizer

public section

namespace CFSG.StandardType

open CFSG.Assembly
open CFSG.ComponentClassification.UnbalancedCatalog (descentField mem_descentField)
open CFSG.RankThree.PartOne.KCSpComm (card_descentField)

namespace FieldFixOmegaPlus

private theorem dvd_two_pow_div_sub_one {p n : ℕ} (hp : p.Prime) (hn : p ∣ n)
    (h : p ∣ 2 ^ n - 1) : p ∣ 2 ^ (n / p) - 1 := by
  haveI := Fact.mk hp
  obtain ⟨m, rfl⟩ := hn
  rw [Nat.mul_div_cancel_left m hp.pos]
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub Nat.one_le_two_pow] at h ⊢
  have key : (2 : ZMod p) ^ (p * m) = (2 : ZMod p) ^ m := by
    rw [mul_comm, pow_mul, ZMod.pow_card]
  simpa only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one, key] using h

variable {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ}

theorem exists_fixGeom (hm : 4 ≤ m) {n p : ℕ} (hn : 1 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = 2 ^ n) (hpk : p ∣ 2 ^ (n / p) - 1)
    (hS : IsSimpleGroup (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m))))
    (hna : ∃ a b : LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m)), a * b ≠ b * a)
    {f : MulAut (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m)))}
    (hf : f ∈ LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K m))))
    (hord : orderOf f = p) :
    LargeEvenRecipeOmegaPlus m (2 ^ (n / p)) fun R₀ _ I₀ _ =>
      IsSimpleGroup R₀ ∧ (∃ a b : R₀, a * b ≠ b * a) ∧ ∃ θ₀ : ggFixDer f ≃* R₀,
        GGFixGeom (LargeEvenInnSet (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m)))) f I₀
          θ₀ := by
  have hm1 : 1 ≤ m := by omega
  have hm3 : 3 ≤ m := by omega
  obtain ⟨σ, hσf⟩ := RecipeFieldOmega.congr_plusEquiv_of_mem_field hm1 hf
  have hinj : Function.Injective (AutOm.fieldAutP (K := K) m) :=
    (injective_iff_map_eq_one _).2 fun τ h => AutOm.eq_one_of_fieldAutP_eq_one hm3 h
  have hσ : orderOf σ = p := by
    rw [← orderOf_injective (AutOm.fieldAutP m) hinj σ, ← hσf, MulEquiv.orderOf_eq]
    exact hord
  set k := descentField σ with hkdef
  have hσk : ∀ x, x ∈ k ↔ σ x = x := fun x => mem_descentField
  obtain ⟨-, hcard⟩ := card_descentField Nat.prime_two hn hK hσ
  have hpk₀ : p ∣ Nat.card k - 1 := by rw [hcard]; exact hpk
  have hS₀ : IsSimpleGroup (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus k m))) :=
    CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_statedProj_statedOmega_quadPlus hm3
  have hna₀ : ∃ a b : LargeEvenProj (LargeEvenOmega (LargeEvenQPlus k m)), a * b ≠ b * a := by
    obtain ⟨ζ, -, hζ, hζ1, -⟩ := TableBOrth.exists_zeta (K := k) hp hp2 hpk₀
    obtain ⟨x, y, hxy⟩ := TableBOrth.exists_not_commute_omegaPlus hζ hζ1 (hp.odd_of_ne_two hp2)
      (by omega : 2 ≤ m)
    set e := TableBOrth.projMkEquiv
      (TableBOrth.scalars_subgroupOf_omegaPlus_eq_bot (K := k) hm1)
    exact ⟨e x, e y, fun h => hxy (e.injective (by rw [map_mul, map_mul, h]))⟩
  have hZ : Subgroup.center (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m))) = ⊥ := by
    obtain ⟨x, y, hxy⟩ := hna
    exact TableBOrth.center_eq_bot_of_simple hxy
  have hrange : (subfieldInj k hm1).range = ggFixSub f := by
    ext r
    rw [mem_range_subfieldInj_iff k hp hp2 hσ hσk hm3 hσf r, mem_ggFixSub]
  let e : LargeEvenProj (LargeEvenOmega (LargeEvenQPlus k m)) ≃* ↥(ggFixSub f) :=
    (MonoidHom.ofInjective (subfieldInj_injective k hm1)).trans (MulEquiv.subgroupCongr hrange)
  haveI := hS₀
  exact ⟨k, inferInstance, inferInstance, hcard, hS₀, hna₀,
    ggFixGeom_of_inn hna₀ hZ (fun _ h => h) (fun _ h => h) e⟩

end FieldFixOmegaPlus

open FieldFixOmegaPlus in
theorem ggFieldFixKnown_omegaPlus : GGFieldFixKnown GGFieldFixOmegaPlusLabel := by
  intro p lab hp hp2 hlab hS
  obtain ⟨⟨hpn, hpq, hrow⟩, ht⟩ := hS
  have h4 : 4 ≤ lab.rank := by
    rcases hrow with (h | h | h) | ⟨h | h, -⟩ | ⟨-, h4, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;>
      first | exact h4 | (rw [ht] at h; cases h)
  have hn : 1 ≤ lab.n := hlab.1
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht h4 hn hpn hpq ⊢
  subst ht
  refine largeEvenLabelAll_omegaPlus (lab := ⟨.D, l, n⟩) rfl h4 fun K _ _ _ hK => ?_
  intro hS hna f hf hord
  have h3 : l ≠ 3 := by omega
  dsimp only [LargeEvenRawDatum]
  simp only [h3, ↓reduceIte]
  exact exists_fixGeom h4 hn hp hp2 hK (dvd_two_pow_div_sub_one hp hpn hpq) hS hna hf hord

end CFSG.StandardType

end
