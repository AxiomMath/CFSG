module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUAut
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.UnitaryPair
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.A2ActualPart4

@[expose] public section

public noncomputable section

namespace CFSG.StandardType.F4ExplicitPos.RationalA2

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Chevalley

open CFSG.Open CFSG.LieType.Chevalley.RootOps CFSG.LieType.Steinberg.Adjoint

open CFSG.RankThree.Chevalley CFSG.RankThree.Classical2 CFSG.RankThree.E6

open CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KF4

open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

open CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.StandardType.F4ExplicitPos.A2Actual CFSG.StandardType.F4ExplicitPos.UnitaryPair

open scoped MatrixGroups

variable {τ : Tag} {L : Type} [Field L] {ν : ℕ}

theorem exists_aut_of_rootData_hom_native
    (ρ : SL(ν, L) →* ModGL τ L)
    (hρinj : Function.Injective ρ) (r : Fin ν → Fin ν → (Fin τ.rank → ℤ))
    (ε : Fin ν → Fin ν → Lˣ)
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

theorem inducedAut_split
    {ρ : SL(3, L) →* ModGL τ L} {r : Fin 3 → Fin 3 → Fin τ.rank → ℤ}
    (h : IsSLFrame ρ r) (hinj : Function.Injective ρ) (Fr : L →+* L)
    (hFr : Function.Bijective Fr) (Ψ : ModGL τ L →* ModGL τ L) (hΨinj : Function.Injective Ψ)
    (π : Equiv.Perm (Fin 3))
    (hΨ : ∀ i j, i ≠ j → ∃ b : Lˣ, ∀ c : L,
      Ψ (pinnedX τ L (r i j) c) = pinnedX τ L (r (π i) (π j)) ((b : L) * Fr c)) :
    ∃ Φ' : SL(3, L) ≃* SL(3, L),
      (∀ X, Ψ (ρ X) = ρ (Φ' X)) ∧
      ∃ b : Fin 3 → Fin 3 → Lˣ, ∀ (i j : Fin 3) (hij : i ≠ j) (t : L),
        ((Φ' (Matrix.SpecialLinearGroup.transvection hij t) : SL(3, L)) :
          Matrix (Fin 3) (Fin 3) L) = 1 + single (π i) (π j) ((b i j : L) * Fr t) := by
  classical
  choose! ε hε using fun (i j : Fin 3) (hij : i ≠ j) => h.transv i j hij
  exact exists_aut_of_rootData_hom_native ρ hinj r ε hε Fr hFr Ψ hΨinj
    (fun i j => (π i, π j)) (fun i j hij => π.injective.ne hij)
    (fun i j hij => ⟨π.symm i, π.symm j, π.symm.injective.ne hij, by simp⟩) hΨ

theorem inducedAut_unitary
    {ρ : SL(3, L) →* ModGL τ L} {r : Fin 3 → Fin 3 → Fin τ.rank → ℤ}
    (h : IsSLFrame ρ r) (hinj : Function.Injective ρ) (Fr : L →+* L)
    (hFr : Function.Bijective Fr) (Ψ : ModGL τ L →* ModGL τ L) (hΨinj : Function.Injective Ψ)
    (π : Equiv.Perm (Fin 3))
    (hΨ : ∀ i j, i ≠ j → ∃ b : Lˣ, ∀ c : L,
      Ψ (pinnedX τ L (r i j) c) = pinnedX τ L (r (π j) (π i)) ((b : L) * Fr c)) :
    ∃ Φ' : SL(3, L) ≃* SL(3, L),
      (∀ X, Ψ (ρ X) = ρ (Φ' X)) ∧
      ∃ b : Fin 3 → Fin 3 → Lˣ, ∀ (i j : Fin 3) (hij : i ≠ j) (t : L),
        ((Φ' (Matrix.SpecialLinearGroup.transvection hij t) : SL(3, L)) :
          Matrix (Fin 3) (Fin 3) L) = 1 + single (π j) (π i) ((b i j : L) * Fr t) := by
  classical
  choose! ε hε using fun (i j : Fin 3) (hij : i ≠ j) => h.transv i j hij
  exact exists_aut_of_rootData_hom_native ρ hinj r ε hε Fr hFr Ψ hΨinj
    (fun i j => (π j, π i)) (fun i j hij => (π.injective.ne hij).symm)
    (fun i j hij => ⟨π.symm j, π.symm i, (π.symm.injective.ne hij).symm, by simp⟩) hΨ

theorem split_full_intertwining {ℓ f : ℕ} {k : Type} [Field k] {Ω : Type} [Field Ω]
    [Algebra k Ω] {n : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hk : Nat.card k = ℓ ^ f)
    [IsAlgClosure k Ω] (hn : 3 ≤ n) (σ : Ω →+* Ω) (hσc : ∀ c, σ c = c ^ ℓ ^ f)
    (π : Equiv.Perm (Fin n)) (Φ : SL(n, Ω) ≃* SL(n, Ω))
    (b : Fin n → Fin n → Ωˣ)
    (hΦ : ∀ (i j : Fin n) (hij : i ≠ j) (t : Ω),
      ((Φ (Matrix.SpecialLinearGroup.transvection hij t) : SL(n, Ω)) :
        Matrix (Fin n) (Fin n) Ω) = 1 + single (π i) (π j) ((b i j : Ω) * t ^ ℓ ^ f)) :
    ∃ H : SL(n, Ω),
      (∀ X : SL(n, Ω), Φ (H * X * H⁻¹) =
        H * Matrix.SpecialLinearGroup.map σ X * H⁻¹) ∧
      (∀ X : SL(n, Ω), X ∈ fixSubgroup Φ ↔
        ∃ Y : SL(n, k), X = H * Matrix.SpecialLinearGroup.map (algebraMap k Ω) Y * H⁻¹) := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; exact (pow_pos hℓ.pos f).ne')
  have : Fintype k := Fintype.ofFinite k
  have : CharP k ℓ := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hk])
  have : CharP Ω ℓ := charP_of_injective_algebraMap (algebraMap k Ω).injective ℓ
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  have hσ' : ∀ c, σ c = c ^ ℓ ^ f := hσc
  have hσ : ⇑σ = (· ^ ℓ ^ f) := funext hσ'
  obtain ⟨A, hA⟩ := exists_conj_map_of_root_permuting hn σ π Φ.toMonoidHom b
    (fun i j hij t => by rw [MulEquiv.coe_toMonoidHom, hΦ, hσ'])
  have hA' : ∀ X : SL(n, Ω), ((Φ X : SL(n, Ω)) : Matrix (Fin n) (Fin n) Ω) =
      (A : Matrix (Fin n) (Fin n) Ω) * (X : Matrix (Fin n) (Fin n) Ω).map (· ^ ℓ ^ f) *
        (↑A⁻¹ : Matrix (Fin n) (Fin n) Ω) := fun X => by
    have := hA X
    rwa [MulEquiv.coe_toMonoidHom, hσ] at this
  obtain ⟨B, hB⟩ := exists_specialLinear_conj_eq (by omega : 1 ≤ n) A
  have hΦB : ∀ X : SL(n, Ω), Φ X = B * Matrix.SpecialLinearGroup.map σ X * B⁻¹ := fun X =>
    Subtype.ext (by
      rw [hA' X, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
        Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, hB, hσ])
  obtain ⟨-, hlang⟩ := matrix_frobenius_lang hℓ hf hk (by omega : 1 ≤ n)
    (Matrix.SpecialLinearGroup.toGL B)
  obtain ⟨H, hHdet, hBH⟩ := hlang B.2
  set Hs : SL(n, Ω) := ⟨H, hHdet⟩ with hHsdef
  have hBHs : B = Hs⁻¹ * Matrix.SpecialLinearGroup.map σ Hs := Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.map_apply_coe,
      RingHom.mapMatrix_apply, hσ, coe_inv_eq_nonsing_inv]
    change (Matrix.SpecialLinearGroup.toGL B : Matrix (Fin n) (Fin n) Ω) = _
    rw [hBH, Matrix.coe_units_inv])
  have hΦH : ∀ X, Φ X = Hs⁻¹ * Matrix.SpecialLinearGroup.map σ (Hs * X * Hs⁻¹) * Hs := fun X => by
    rw [hΦB, hBHs, map_mul, map_mul, map_inv]
    group
  have hσfix : ∀ W : SL(n, Ω), Matrix.SpecialLinearGroup.map σ W = W ↔
      ∃ Y : SL(n, k), Matrix.SpecialLinearGroup.map (algebraMap k Ω) Y = W := by
    intro W
    rw [exists_map_algebraMap_eq_iff hℓ hf hk W, ← hσ]
    constructor
    · intro h
      have := congrArg (fun Z : SL(n, Ω) => (Z : Matrix (Fin n) (Fin n) Ω)) h
      simpa only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply] using this
    · intro h
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, h]
  have hfix : ∀ X : SL(n, Ω), X ∈ fixSubgroup Φ ↔
      ∃ Y : SL(n, k), X = Hs⁻¹ * Matrix.SpecialLinearGroup.map (algebraMap k Ω) Y * Hs⁻¹⁻¹ := by
    intro X
    rw [mem_fixSubgroup, hΦH, inv_inv]
    constructor
    · intro h
      have hW : Matrix.SpecialLinearGroup.map σ (Hs * X * Hs⁻¹) = Hs * X * Hs⁻¹ := by
        calc Matrix.SpecialLinearGroup.map σ (Hs * X * Hs⁻¹) =
            Hs * (Hs⁻¹ * Matrix.SpecialLinearGroup.map σ (Hs * X * Hs⁻¹) * Hs) * Hs⁻¹ := by
              group
          _ = Hs * X * Hs⁻¹ := by rw [h]
      obtain ⟨Y, hY⟩ := (hσfix _).mp hW
      refine ⟨Y, ?_⟩
      rw [hY]
      group
    · rintro ⟨Y, rfl⟩
      have hW : Hs * (Hs⁻¹ * Matrix.SpecialLinearGroup.map (algebraMap k Ω) Y * Hs) * Hs⁻¹ =
          Matrix.SpecialLinearGroup.map (algebraMap k Ω) Y := by group
      rw [hW, (hσfix _).mpr ⟨Y, rfl⟩]
  refine ⟨Hs⁻¹, ?_, ?_⟩
  · intro X
    simp only [inv_inv]
    rw [hΦH (Hs⁻¹ * X * Hs),
      show Hs * (Hs⁻¹ * X * Hs) * Hs⁻¹ = X by group]
  · simpa using hfix

end CFSG.StandardType.F4ExplicitPos.RationalA2
end

end
