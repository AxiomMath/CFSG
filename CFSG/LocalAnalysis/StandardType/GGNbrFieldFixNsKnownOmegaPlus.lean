module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownOmegaPlus
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixNsDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly
open CFSG.ComponentClassification.UnbalancedCatalog (descentField mem_descentField)
open CFSG.RankThree.PartOne.KCSpComm (card_descentField)

namespace FieldFixOmegaPlusNs

open FieldFixOmegaPlus

theorem exists_odd_prime_dvd_card_sub_one {k : Type} [Field k] [Finite k] [CharP k 2]
    (hk : 4 ≤ Nat.card k) : ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ∣ Nat.card k - 1 := by
  have hcard : 2 ∣ Nat.card k := by
    haveI := Fintype.ofFinite k
    obtain ⟨n, -, hn⟩ := FiniteField.card k 2
    rw [Nat.card_eq_fintype_card, hn]
    exact dvd_pow_self 2 (PNat.ne_zero n)
  have hN : Nat.card k - 1 ≠ 1 := by omega
  refine ⟨(Nat.card k - 1).minFac, Nat.minFac_prime hN, fun h2 => ?_, Nat.minFac_dvd _⟩
  have := Nat.minFac_dvd (Nat.card k - 1)
  rw [h2] at this
  omega

theorem exists_not_commute_projOmegaPlus {k : Type} [Field k] [Finite k] [CharP k 2]
    (hk : 4 ≤ Nat.card k) {m : ℕ} (hm : 3 ≤ m) :
    ∃ a b : LargeEvenProj (LargeEvenOmega (LargeEvenQPlus k m)), a * b ≠ b * a := by
  obtain ⟨r, hr, hr2, hrk⟩ := exists_odd_prime_dvd_card_sub_one hk
  obtain ⟨ζ, -, hζ, hζ1, -⟩ := TableBOrth.exists_zeta (K := k) hr hr2 hrk
  obtain ⟨x, y, hxy⟩ := TableBOrth.exists_not_commute_omegaPlus hζ hζ1 (hr.odd_of_ne_two hr2)
    (by omega : 2 ≤ m)
  set e := TableBOrth.projMkEquiv
    (TableBOrth.scalars_subgroupOf_omegaPlus_eq_bot (K := k) (by omega : 1 ≤ m))
  exact ⟨e x, e y, fun h => hxy (e.injective (by rw [map_mul, map_mul, h]))⟩

variable {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ}

theorem exists_fixGeom (hm : 4 ≤ m) {n p : ℕ} (hn : 1 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = 2 ^ n) (hq : 4 ≤ 2 ^ (n / p))
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
  have hS₀ : IsSimpleGroup (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus k m))) :=
    CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_statedProj_statedOmega_quadPlus hm3
  have hna₀ : ∃ a b : LargeEvenProj (LargeEvenOmega (LargeEvenQPlus k m)), a * b ≠ b * a :=
    exists_not_commute_projOmegaPlus (k := k) (by rw [hcard]; exact hq) hm3
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

end FieldFixOmegaPlusNs

open FieldFixOmegaPlusNs in
theorem ggFieldFixKnown_omegaPlusNs :
    GGFieldFixKnown fun p lab => GGFieldFixNsLabel p lab ∧ lab.tag = .D := by
  intro p lab hp hp2 hlab hS
  obtain ⟨⟨hpn, ⟨-, hrow⟩, ⟨-, hrow₀⟩⟩, ht⟩ := hS
  have h4 : 4 ≤ lab.rank := by
    rcases hrow with ⟨hBC, -⟩ | ⟨-, h4, -⟩ | ⟨hT, -⟩
    · rcases hBC with h | h <;> rw [ht] at h <;> cases h
    · exact h4
    · rw [ht] at hT; cases hT
  have hq : 4 ≤ 2 ^ (lab.n / p) := by
    rcases hrow₀ with ⟨hBC, -⟩ | ⟨hD, -, -, h2⟩ | ⟨hT, -, h2⟩
    · rcases hBC with h | h <;> rw [ht] at h <;> cases h
    · calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (lab.n / p) := Nat.pow_le_pow_right (by norm_num) h2
    · rw [ht] at hT; cases hT
  have hn : 1 ≤ lab.n := hlab.1
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht h4 hn hpn hq
  subst ht
  refine largeEvenLabelAll_omegaPlus (lab := ⟨.D, l, n⟩) rfl h4 fun K _ _ _ hK => ?_
  intro hS hna f hf hord
  have h3 : l ≠ 3 := by omega
  dsimp only [LargeEvenRawDatum]
  simp only [h3, ↓reduceIte]
  exact exists_fixGeom h4 hn hp hp2 hK hq hS hna hf hord

end CFSG.StandardType

end
