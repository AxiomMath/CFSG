module

public import CFSG.RankThree.Classical2.TwistedE6Phi3Torus
public import CFSG.RankThree.E6.LargePrimeStabilizers
public import CFSG.LieType.Chevalley.LangRootRankOneTorus

public noncomputable section

namespace CFSG.RankThree.Classical2

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix

section General

variable {τ : Tag} {K : Type} [Field K]

theorem mem_torusGroup_of_mapsRootLines_one {g : ModGL τ K} (hg : g ∈ monomialSubgroup τ K)
    (h1 : MapsRootLines g 1) : g ∈ torusGroup τ K := by
  obtain ⟨-, ⟨ρ, -, hρ, -, -, hker⟩, -⟩ := Weyl_normalizer_quotient τ K
  have hρ1 : ρ ⟨g, hg⟩ = 1 := MapsRootLines.unique (R := K) (hρ ⟨g, hg⟩) h1
  have hker1 : (⟨g, hg⟩ : monomialSubgroup τ K) ∈ ρ.ker := hρ1
  rw [hker] at hker1
  exact hker1

theorem canonicalRep_rootReflection_mem {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    canonicalRep (coxeterSystem τ) K (rootReflection α) ∈
      torusGroup τ K ⊔ (rootSubgroup τ K α ⊔ rootSubgroup τ K (-α)) := by
  obtain ⟨hL, -, hN, -⟩ := exceptional_Lang_root_rank_one_torus_transport τ K hα
  obtain ⟨hnN, hρn⟩ := hN 1
  have hnL : rootWeylSL2 τ K α 1 ∈ rootSubgroup τ K α ⊔ rootSubgroup τ K (-α) := by
    rw [← hL]
    exact ⟨_, rfl⟩
  have hmaps : MapsRootLines (rootWeylSL2 τ K α 1) (rootReflection α) := by
    rw [← hρn]
    exact mapsRootLines_weylQuotientHom (R := K) ⟨rootWeylSL2 τ K α 1, hnN⟩
  have hcN : canonicalRep (coxeterSystem τ) K (rootReflection α) ∈ monomialSubgroup τ K :=
    Subgroup.mem_sup_right (canonicalRep_mem_closure (coxeterSystem τ) K _)
  have hh : canonicalRep (coxeterSystem τ) K (rootReflection α) * (rootWeylSL2 τ K α 1)⁻¹ ∈
      torusGroup τ K := by
    refine mem_torusGroup_of_mapsRootLines_one (mul_mem hcN (inv_mem hnN)) ?_
    have h := (mapsRootLines_canonicalRep (R := K) (rootReflection α)).mul hmaps.inv
    rwa [mul_inv_cancel] at h
  have e : canonicalRep (coxeterSystem τ) K (rootReflection α) =
      (canonicalRep (coxeterSystem τ) K (rootReflection α) * (rootWeylSL2 τ K α 1)⁻¹) *
        rootWeylSL2 τ K α 1 := by group
  rw [e]
  exact mul_mem (Subgroup.mem_sup_left hh) (Subgroup.mem_sup_right hnL)

theorem canonicalRep_mem_of_mem_closure {S : Set (Fin τ.rank → ℤ)}
    (hS : ∀ α ∈ S, IsRoot τ α ∧ -α ∈ S) {w : WeylGroup τ}
    (hw : w ∈ Subgroup.closure {s | ∃ α ∈ S, s = rootReflection α}) :
    canonicalRep (coxeterSystem τ) K w ∈ torusGroup τ K ⊔ rootSpan τ K S := by
  induction hw using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨α, hα, rfl⟩ := hx
    have hle : rootSubgroup τ K α ⊔ rootSubgroup τ K (-α) ≤ rootSpan τ K S :=
      sup_le (le_iSup₂_of_le (f := fun β (_ : β ∈ S) => rootSubgroup τ K β) α hα le_rfl)
        (le_iSup₂_of_le (f := fun β (_ : β ∈ S) => rootSubgroup τ K β) (-α) (hS α hα).2 le_rfl)
    exact sup_le_sup_left hle (torusGroup τ K) (canonicalRep_rootReflection_mem (hS α hα).1)
  | one =>
    rw [canonicalRep_one]
    exact one_mem _
  | mul x y _ _ hx hy =>
    obtain ⟨k, hk, hxy⟩ := canonicalRep_mul_mem (R := K) x y
    have e : canonicalRep (coxeterSystem τ) K (x * y) =
        k⁻¹ * (canonicalRep (coxeterSystem τ) K x * canonicalRep (coxeterSystem τ) K y) := by
      rw [hxy, inv_mul_cancel_left]
    rw [e]
    exact mul_mem (Subgroup.mem_sup_left (inv_mem hk)) (mul_mem hx hy)
  | inv x _ hx =>
    obtain ⟨k, hk, hxy⟩ := canonicalRep_mul_mem (R := K) x x⁻¹
    rw [mul_inv_cancel, canonicalRep_one, mul_one] at hxy
    have e : canonicalRep (coxeterSystem τ) K x⁻¹ = (canonicalRep (coxeterSystem τ) K x)⁻¹ * k := by
      rw [← hxy, inv_mul_cancel_left]
    rw [e]
    exact mul_mem (inv_mem hx) (Subgroup.mem_sup_left hk)

theorem toralCentralizer_eq_sup (a : Fin τ.rank → Kˣ)
    (hW : ∀ w ∈ rootCharStabilizer a,
      w ∈ Subgroup.closure {s | ∃ α ∈ rootCharKernel a, s = rootReflection α}) :
    toralCentralizer τ K a = torusGroup τ K ⊔ rootSpan τ K (rootCharKernel a) := by
  have hS : ∀ α ∈ rootCharKernel a, IsRoot τ α ∧ -α ∈ rootCharKernel a := fun α hα =>
    ⟨hα.1, CFSG.LieType.Chevalley.IsRoot.neg hα.1, by rw [rootChar_neg', hα.2, inv_one]⟩
  have hcl : Subgroup.closure ((fun w => canonicalRep (coxeterSystem τ) K w) ''
      rootCharStabilizer a) ≤ torusGroup τ K ⊔ rootSpan τ K (rootCharKernel a) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨w, hw, rfl⟩
    exact canonicalRep_mem_of_mem_closure hS (hW w hw)
  rw [(Chevalley_toral_centralizer_Bruhat_factors τ K a).2.2.2, sup_eq_left.2 hcl]

end General

section Characters

variable {Ω : Type} [Field Ω]

theorem rootChar_zetaPow_eq_one_iff {p : ℕ} [NeZero p] {ζ : Ωˣ} (hζ : IsPrimitiveRoot ζ p)
    (z : Fin Tag.E6.rank → ZMod p) (v : Fin Tag.E6.rank → ℤ) :
    rootChar (fun i => ζ ^ (z i).val) v = 1 ↔ charVal z v = 0 := by
  have h : rootChar (fun i => ζ ^ (z i).val) v = ζ ^ (∑ i, v i * ((z i).val : ℤ)) := by
    rw [rootChar, zpow_finsetSum]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← zpow_natCast, ← zpow_mul, mul_comm]
  rw [h, hζ.zpow_eq_one_iff_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd, charVal]
  push_cast
  simp only [ZMod.natCast_zmod_val]

theorem rootCharKernel_zetaPow {p : ℕ} [NeZero p] {ζ : Ωˣ} (hζ : IsPrimitiveRoot ζ p)
    (z : Fin Tag.E6.rank → ZMod p) :
    rootCharKernel (fun i => ζ ^ (z i).val) = rootKernel z := by
  ext α
  exact and_congr_right fun _ => rootChar_zetaPow_eq_one_iff hζ z α

theorem mem_rootCharStabilizer_zetaPow {p : ℕ} [NeZero p] {ζ : Ωˣ} (hζ : IsPrimitiveRoot ζ p)
    (z : Fin Tag.E6.rank → ZMod p) (w : WeylGroup Tag.E6) :
    w ∈ rootCharStabilizer (fun i => ζ ^ (z i).val) ↔ w ∈ dualWeylStabilizer z := by
  refine forall_congr' fun v => ?_
  rw [← mul_inv_eq_one, ← rootChar_sub, rootChar_zetaPow_eq_one_iff hζ, charVal_sub,
    sub_eq_zero]

theorem toralCentralizer_zetaPow_eq {p : ℕ} [Fact p.Prime] (hp5 : 5 < p) {ζ : Ωˣ}
    (hζ : IsPrimitiveRoot ζ p) (z : Fin Tag.E6.rank → ZMod p) :
    toralCentralizer Tag.E6 Ω (fun i => ζ ^ (z i).val) =
      torusGroup Tag.E6 Ω ⊔ rootSpan Tag.E6 Ω (rootKernel z) := by
  rw [toralCentralizer_eq_sup, rootCharKernel_zetaPow hζ]
  intro w hw
  rw [rootCharKernel_zetaPow hζ, ← dualWeylStabilizer_eq_closure hp5 z]
  exact (mem_rootCharStabilizer_zetaPow hζ z w).1 hw

end Characters

section Torsion

variable {Ω : Type} [Field Ω] {Fr : Ω →+* Ω}

theorem exists_eq_rootDiagUnit_eisenstein [IsAlgClosed Ω] {q p : ℕ} (hFr : ∀ c, Fr c = c ^ q)
    {ζ : Ωˣ} (hζ : IsPrimitiveRoot ζ p) [NeZero p] {x : ModGL Tag.E6 Ω}
    (hx : x ∈ phi3TorusTorsion Ω Fr p) (hr : (-(q : ZMod p)) ^ 2 - -(q : ZMod p) + 1 = 0) :
    ∃ a b : ZMod p,
      x = rootDiagUnit Tag.E6 (fun i => ζ ^ (eisensteinColumn (-(q : ZMod p)) a b i).val) := by
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hx.1.1
  have hbker : b ∈ (monomialHom (G := Ωˣ) (phi3Matrix q)ᵀ).ker :=
    (phi3Theta_rootDiagUnit_eq_iff hFr b).mp (by rw [← hb]; exact hx.1.2.2)
  have hbp : ∀ i, b i ^ p = 1 := by
    have h1 : rootDiagUnit Tag.E6 (b ^ p) = rootDiagUnit Tag.E6 1 := by
      rw [rootDiagUnit_one]
      change rootDiagUnitHom Tag.E6 Ω (b ^ p) = 1
      rw [map_pow]
      change rootDiagUnit Tag.E6 b ^ p = 1
      rw [← hb]
      exact hx.2
    intro i
    exact congrFun (rootDiagUnit_injective h1) i
  have hmem : ∀ i, ∃ m : ℤ, ζ ^ m = b i := fun i => by
    have : b i ∈ rootsOfUnity p Ω := (mem_rootsOfUnity p (b i)).mpr (hbp i)
    rw [← hζ.zpowers_eq] at this
    obtain ⟨m, hm⟩ := this
    exact ⟨m, hm⟩
  choose m hm using hmem
  set z : Fin Tag.E6.rank → ZMod p := fun i => (m i : ZMod p) with hz
  have hzb : (fun i => ζ ^ (z i).val) = b := by
    funext i
    have h1 := zpow_mod_orderOf ζ (m i)
    rw [← hζ.eq_orderOf] at h1
    rw [← hm i, ← zpow_natCast, hz, ZMod.val_intCast, h1]
  have hzc : (dualMatrix (ZMod p) e6CoxeterSq) *ᵥ z = (-(q : ZMod p)) • z := by
    rw [← phi3Matrix_transpose_mulVec_eq_zero_iff q z, ← zetaPow_mem_ker_monomialHom_iff hζ, hzb]
    exact hbker
  refine ⟨z (e6Index 4), z (e6Index 5), ?_⟩
  rw [← eq_eisensteinColumn_of_dualMatrix_mulVec hr hzc, hzb, hb]

theorem rootKernel_eisenstein_trichotomy {p : ℕ} [Fact p.Prime] (hp3 : 3 < p) {r : ZMod p}
    (hr : r ^ 2 - r + 1 = 0) {a b : ZMod p} (hab : (a, b) ≠ 0) :
    rootKernel (eisensteinColumn r a b) = ∅ ∨
      (∃ w : WeylGroup Tag.E6,
        (w • ·) '' rootKernel (eisensteinColumn r a b) = parabolicRoots Tag.E6 support13) ∨
      ∃ w : WeylGroup Tag.E6,
        (w • ·) '' rootKernel (eisensteinColumn r a b) = parabolicRoots Tag.E6 supportA2A2 := by
  obtain ⟨-, -, -, -, h⟩ := E6_Coxeter_square_eight_Eisenstein_root_kernel_lines
  obtain ⟨-, -, -, hne, -, hA2A2, hA2⟩ := h p hp3 r hr
  by_cases h0 : (rootKernel (eisensteinColumn r a b)).Nonempty
  · obtain ⟨k, hk⟩ := (hne a b hab).1 h0
    by_cases hk4 : k.val < 4
    · obtain ⟨w, hw, -⟩ := hA2A2 k hk4
      exact Or.inr (Or.inr ⟨w, (hw a b hab hk).1⟩)
    · obtain ⟨w, hw, -⟩ := hA2 k (by omega)
      exact Or.inr (Or.inl ⟨w, (hw a b hab hk).1⟩)
  · exact Or.inl (Set.not_nonempty_iff_eq_empty.1 h0)

end Torsion

section RootKernel

variable {Ω : Type} [Field Ω]

@[expose] def torusRootKernel (x : ModGL Tag.E6 Ω) : Set (Fin Tag.E6.rank → ℤ) :=
  {α | IsRoot Tag.E6 α ∧ ∃ b, x = rootDiagUnit Tag.E6 b ∧ rootChar b α = 1}

theorem torusRootKernel_rootDiagUnit (b : Fin Tag.E6.rank → Ωˣ) :
    torusRootKernel (rootDiagUnit Tag.E6 b) = rootCharKernel b := by
  ext α
  refine and_congr_right fun _ => ⟨?_, fun h => ⟨b, rfl, h⟩⟩
  rintro ⟨b', hb', h⟩
  rwa [rootDiagUnit_injective hb'.symm] at h

theorem exists_eq_rootDiagUnit_zetaPow {p : ℕ} [NeZero p] {ζ : Ωˣ} (hζ : IsPrimitiveRoot ζ p)
    {x : ModGL Tag.E6 Ω} (hx : x ∈ torusGroup Tag.E6 Ω) (hxp : x ^ p = 1) :
    ∃ z : Fin Tag.E6.rank → ZMod p, x = rootDiagUnit Tag.E6 (fun i => ζ ^ (z i).val) := by
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hx
  have hbp : ∀ i, b i ^ p = 1 := by
    have h1 : rootDiagUnit Tag.E6 (b ^ p) = rootDiagUnit Tag.E6 1 := by
      rw [rootDiagUnit_one]
      change rootDiagUnitHom Tag.E6 Ω (b ^ p) = 1
      rw [map_pow]
      change rootDiagUnit Tag.E6 b ^ p = 1
      rw [← hb]
      exact hxp
    intro i
    exact congrFun (rootDiagUnit_injective h1) i
  have hmem : ∀ i, ∃ m : ℤ, ζ ^ m = b i := fun i => by
    have : b i ∈ rootsOfUnity p Ω := (mem_rootsOfUnity p (b i)).mpr (hbp i)
    rw [← hζ.zpowers_eq] at this
    obtain ⟨m, hm⟩ := this
    exact ⟨m, hm⟩
  choose m hm using hmem
  refine ⟨fun i => (m i : ZMod p), ?_⟩
  rw [hb]
  congr 1
  funext i
  have h1 := zpow_mod_orderOf ζ (m i)
  rw [← hζ.eq_orderOf] at h1
  rw [← hm i, ← zpow_natCast, ZMod.val_intCast, h1]

theorem centralizer_eq_sup_of_pow_eq_one [IsAlgClosed Ω] {p : ℕ} [Fact p.Prime] (hp5 : 5 < p)
    (hpΩ : (p : Ω) ≠ 0) {x : ModGL Tag.E6 Ω} (hx : x ∈ torusGroup Tag.E6 Ω) (hxp : x ^ p = 1) :
    adjointGroup Tag.E6 Ω ⊓ Subgroup.centralizer {x} =
      torusGroup Tag.E6 Ω ⊔ rootSpan Tag.E6 Ω (torusRootKernel x) := by
  have : NeZero (p : Ω) := ⟨hpΩ⟩
  have := IsSepClosed.hasEnoughRootsOfUnity Ω p
  obtain ⟨ζ₀, hζ₀⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω p
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  set ζ : Ωˣ := (hζ₀.isUnit hp0).unit with hζdef
  have hζ : IsPrimitiveRoot ζ p := IsPrimitiveRoot.coe_units_iff.mp (by
    rw [hζdef, IsUnit.unit_spec]
    exact hζ₀)
  obtain ⟨z, rfl⟩ := exists_eq_rootDiagUnit_zetaPow hζ hx hxp
  rw [torusRootKernel_rootDiagUnit, rootCharKernel_zetaPow hζ, ← toralCentralizer_zetaPow_eq hp5 hζ]
  rfl

end RootKernel

end CFSG.RankThree.Classical2
