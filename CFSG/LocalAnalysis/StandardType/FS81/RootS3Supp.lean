module

public import CFSG.LargeExtraspecial.OrthoF2Pairs57
public import CFSG.ClassicalInvolution.WeakCT.Defs
public import CFSG.LocalAnalysis.StandardType.FS81.RootS3SuppAux

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open scoped MatrixGroups
open Matrix

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.LargeExtraspecial CFSG.RankThree.OrthogonalInvolutions CFSG.ClassicalInvolution.WeakCT
open SuppAux

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {q : QuadraticForm (ZMod 2) V}

@[expose] noncomputable def subCommSpace (Z : Subgroup (V ≃ₗ[ZMod 2] V)) : Submodule (ZMod 2) V :=
  ⨆ z ∈ Z, commSpace z

structure IsRootS3Like (q : QuadraticForm (ZMod 2) V) (o : Subgroup (V ≃ₗ[ZMod 2] V)) : Prop where
  typeA : ∀ s ∈ o, s * s = 1 → s ≠ 1 → IsTypeA q s 2
  disj : ∀ s ∈ o, ∀ s' ∈ o, s * s = 1 → s' * s' = 1 → s ≠ 1 → s' ≠ 1 → s ≠ s' →
    commSpace s ⊓ commSpace s' = ⊥

theorem subCommSpace_map_conj (Z : Subgroup (V ≃ₗ[ZMod 2] V)) (w : V ≃ₗ[ZMod 2] V) :
    subCommSpace (Z.map (MulAut.conj w).toMonoidHom) = (subCommSpace Z).map (w : V →ₗ[ZMod 2] V) := by
  have hreindex : (⨆ z ∈ Z.map (MulAut.conj w).toMonoidHom, commSpace z) =
      ⨆ y ∈ Z, commSpace ((MulAut.conj w).toMonoidHom y) := by
    refine le_antisymm (iSup_le fun z => iSup_le fun hz => ?_)
      (iSup_le fun y => iSup_le fun hy => ?_)
    · obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hz
      exact le_iSup₂_of_le y hy le_rfl
    · exact le_iSup₂_of_le _ (Subgroup.mem_map_of_mem _ hy) le_rfl
  rw [subCommSpace, subCommSpace, hreindex]
  have hcomm : ∀ y ∈ Z,
      commSpace ((MulAut.conj w).toMonoidHom y) = (commSpace y).map (w : V →ₗ[ZMod 2] V) := by
    intro y _
    rw [show (MulAut.conj w).toMonoidHom y = w * y * w⁻¹ from MulAut.conj_apply w y,
      commSpace_conj]
  have hcongr : (⨆ y ∈ Z, commSpace ((MulAut.conj w).toMonoidHom y)) =
      ⨆ y ∈ Z, (commSpace y).map (w : V →ₗ[ZMod 2] V) :=
    iSup_congr fun y => iSup_congr fun hy => hcomm y hy
  rw [hcongr]
  simp_rw [Submodule.map_iSup]

theorem exists_conj_of_linearBlockStandardPair {X : Type} [Group X] {W U U' : Subgroup X}
    (h : LinearBlockStandardPair (ZMod 2) W U U') :
    ∃ w ∈ W, U' = U.map (MulAut.conj w).toMonoidHom := by
  obtain ⟨θ, c, hW, -, hdisj⟩ := h
  let φ : SL(3, ZMod 2) →* X := θ.comp (MulAut.conj c⁻¹).toMonoidHom
  have hφapply : ∀ x, φ x = θ (c⁻¹ * x * c) := by
    intro x
    simp [φ, MulAut.conj_apply]
  have hφmem : ∀ x, φ x ∈ W := by
    intro x
    rw [← hW]
    exact ⟨c⁻¹ * x * c, (hφapply x).symm⟩
  rcases hdisj with ⟨hU, hU'⟩ | ⟨hU', hU⟩
  · have hUφ : U = (B12 (ZMod 2)).map φ := by
      rw [← hU, Subgroup.map_map]
    have hU'φ : U' = (B23 (ZMod 2)).map φ := by
      rw [← hU', Subgroup.map_map]
    refine ⟨φ swapSL, hφmem swapSL, ?_⟩
    calc U' = (B23 (ZMod 2)).map φ := hU'φ
      _ = ((B12 (ZMod 2)).map (MulAut.conj swapSL).toMonoidHom).map φ := by
            rw [map_conj_swapSL_B12]
      _ = ((B12 (ZMod 2)).map φ).map (MulAut.conj (φ swapSL)).toMonoidHom := by
            rw [map_conj_map]
      _ = U.map (MulAut.conj (φ swapSL)).toMonoidHom := by rw [← hUφ]
  · have hUφ : U = (B23 (ZMod 2)).map φ := by
      rw [← hU, Subgroup.map_map]
    have hU'φ : U' = (B12 (ZMod 2)).map φ := by
      rw [← hU', Subgroup.map_map]
    refine ⟨φ swapSL, hφmem swapSL, ?_⟩
    calc U' = (B12 (ZMod 2)).map φ := hU'φ
      _ = ((B23 (ZMod 2)).map (MulAut.conj swapSL).toMonoidHom).map φ := by
            rw [map_conj_swapSL_B23]
      _ = ((B23 (ZMod 2)).map φ).map (MulAut.conj (φ swapSL)).toMonoidHom := by
            rw [map_conj_map]
      _ = U.map (MulAut.conj (φ swapSL)).toMonoidHom := by rw [← hUφ]

theorem exists_singular_pair_of_standardPair (hq : q.polarBilin.Nondegenerate)
    {W Z o : Subgroup (V ≃ₗ[ZMod 2] V)} (hW : W ≤ TauCeti.QuadraticMap.orthogonalGroup q)
    (hpair : LinearBlockStandardPair (ZMod 2) W Z o) (ho : IsRootS3Like q o) :
    ∃ u u' : V, u ∈ subCommSpace Z ⊓ subCommSpace o ∧ u' ∈ subCommSpace Z ⊓ subCommSpace o ∧
      u ≠ 0 ∧ u' ≠ 0 ∧ u ≠ u' ∧ q u = 0 ∧ q u' = 0 := by
  obtain ⟨θ, c, hWθ, hker, hdisj⟩ := hpair
  let φ : SL(3, ZMod 2) →* (V ≃ₗ[ZMod 2] V) := θ.comp (MulAut.conj c⁻¹).toMonoidHom
  have hφapply : ∀ x, φ x = θ (c⁻¹ * x * c) := by
    intro x
    simp [φ, MulAut.conj_apply]
  have hθinj : Function.Injective θ := by
    intro x y hxy
    have hmem : x * y⁻¹ ∈ θ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, mul_inv_cancel]
    have hc := hker hmem
    rw [center_SL3_two_eq_bot, Subgroup.mem_bot] at hc
    exact mul_inv_eq_one.mp hc
  have hφinj : Function.Injective φ := by
    intro x y hxy
    have h' : c⁻¹ * x * c = c⁻¹ * y * c := by
      apply hθinj
      simpa [hφapply] using hxy
    simpa [mul_assoc] using congrArg (fun z => c * z * c⁻¹) h'
  have hφmem : ∀ x, φ x ∈ W := by
    intro x
    rw [← hWθ]
    exact ⟨c⁻¹ * x * c, (hφapply x).symm⟩
  rcases hdisj with ⟨hU, hU'⟩ | ⟨hU', hU⟩
  · have hZφ : Z = (B12 (ZMod 2)).map φ := by
      rw [← hU, Subgroup.map_map]
    have hoφ : o = (B23 (ZMod 2)).map φ := by
      rw [← hU', Subgroup.map_map]
    have h12o : φ sl3E12 ∈ o := by
      rw [hoφ]
      exact Subgroup.mem_map_of_mem φ sl3E12_mem_B23
    have hA12 : IsTypeA q (φ sl3E12) 2 :=
      ho.typeA _ h12o (by rw [← map_mul, sl3E12_sq, map_one])
        (fun h => sl3E12_ne_one (hφinj (by rw [h, map_one])))
    have hA01 : IsTypeA q (φ sl3E01) 2 :=
      isTypeA_image_of_mul_eq hW hφmem hA12 conj_E01_E12
    have hA10 : IsTypeA q (φ sl3E10) 2 :=
      isTypeA_image_of_mul_eq hW hφmem hA12 conj_E10_E12
    have hA21 : IsTypeA q (φ sl3E21) 2 :=
      isTypeA_image_of_mul_eq hW hφmem hA12 conj_E21_E12
    have hAa1 : IsTypeA q (φ (sl3E01 * sl3E21)) 2 :=
      isTypeA_image_of_mul_eq hW hφmem hA12 conj_A1_E12
    have hAa2 : IsTypeA q (φ (sl3E10 * sl3E12)) 2 :=
      isTypeA_image_of_mul_eq hW hφmem hA12 conj_A2_E12
    have hcomm1 : φ sl3E01 * φ sl3E21 = φ sl3E21 * φ sl3E01 := by
      rw [← map_mul, ← map_mul, sl3E01_comm_sl3E21]
    have hcomm2 : φ sl3E10 * φ sl3E12 = φ sl3E12 * φ sl3E10 := by
      rw [← map_mul, ← map_mul, sl3E10_comm_sl3E12]
    have hprod1 : IsTypeA q (φ sl3E01 * φ sl3E21) 2 := by
      rw [← map_mul]
      exact hAa1
    have hprod2 : IsTypeA q (φ sl3E10 * φ sl3E12) 2 := by
      rw [← map_mul]
      exact hAa2
    obtain ⟨u, hu, hu0⟩ := exists_ne_zero_mem_inf_of_commute hq hA01 hA21 hprod1 hcomm1
    obtain ⟨u', hu', hu'0⟩ := exists_ne_zero_mem_inf_of_commute hq hA10 hA12 hprod2 hcomm2
    have h01Z : φ sl3E01 ∈ Z := by
      rw [hZφ]
      exact Subgroup.mem_map_of_mem φ sl3E01_mem_B12
    have h21o : φ sl3E21 ∈ o := by
      rw [hoφ]
      exact Subgroup.mem_map_of_mem φ sl3E21_mem_B23
    have h10Z : φ sl3E10 ∈ Z := by
      rw [hZφ]
      exact Subgroup.mem_map_of_mem φ sl3E10_mem_B12
    have hneβ : φ sl3E21 ≠ φ sl3E12 := fun h => sl3E21_ne_sl3E12 (hφinj h)
    have hinfβ : commSpace (φ sl3E21) ⊓ commSpace (φ sl3E12) = ⊥ :=
      ho.disj _ h21o _ h12o hA21.2.2.1 hA12.2.2.1 hA21.2.1 hA12.2.1 hneβ
    refine ⟨u, u', ?_, ?_, hu0, hu'0, ?_, ?_, ?_⟩
    · exact ⟨(le_iSup₂_of_le (φ sl3E01) h01Z le_rfl : commSpace (φ sl3E01) ≤ subCommSpace Z) hu.1,
        (le_iSup₂_of_le (φ sl3E21) h21o le_rfl : commSpace (φ sl3E21) ≤ subCommSpace o) hu.2⟩
    · exact ⟨(le_iSup₂_of_le (φ sl3E10) h10Z le_rfl : commSpace (φ sl3E10) ≤ subCommSpace Z) hu'.1,
        (le_iSup₂_of_le (φ sl3E12) h12o le_rfl : commSpace (φ sl3E12) ≤ subCommSpace o) hu'.2⟩
    · intro h
      have hmem : u ∈ commSpace (φ sl3E21) ⊓ commSpace (φ sl3E12) :=
        ⟨hu.2, by rw [h]; exact hu'.2⟩
      rw [hinfβ, Submodule.mem_bot] at hmem
      exact hu0 hmem
    · exact hA01.2.2.2.2 u hu.1
    · exact hA10.2.2.2.2 u' hu'.1
  · have hZφ : Z = (B23 (ZMod 2)).map φ := by
      rw [← hU, Subgroup.map_map]
    have hoφ : o = (B12 (ZMod 2)).map φ := by
      rw [← hU', Subgroup.map_map]
    have h01o : φ sl3E01 ∈ o := by
      rw [hoφ]
      exact Subgroup.mem_map_of_mem φ sl3E01_mem_B12
    have hA01 : IsTypeA q (φ sl3E01) 2 :=
      ho.typeA _ h01o (by rw [← map_mul, sl3E01_sq, map_one])
        (fun h => sl3E01_ne_one (hφinj (by rw [h, map_one])))
    have hA10 : IsTypeA q (φ sl3E10) 2 :=
      isTypeA_image_of_mul_eq hW hφmem hA01 conj_E10_E01
    have hA12 : IsTypeA q (φ sl3E12) 2 :=
      isTypeA_image_of_mul_eq hW hφmem hA01 conj_E12_E01
    have hA21 : IsTypeA q (φ sl3E21) 2 :=
      isTypeA_image_of_mul_eq hW hφmem hA01 conj_E21_E01
    have hAa1 : IsTypeA q (φ (sl3E01 * sl3E21)) 2 :=
      isTypeA_image_of_mul_eq hW hφmem hA01 conj_A1_E01
    have hAa2 : IsTypeA q (φ (sl3E10 * sl3E12)) 2 :=
      isTypeA_image_of_mul_eq hW hφmem hA01 conj_A2_E01
    have hcomm1 : φ sl3E01 * φ sl3E21 = φ sl3E21 * φ sl3E01 := by
      rw [← map_mul, ← map_mul, sl3E01_comm_sl3E21]
    have hcomm2 : φ sl3E10 * φ sl3E12 = φ sl3E12 * φ sl3E10 := by
      rw [← map_mul, ← map_mul, sl3E10_comm_sl3E12]
    have hprod1 : IsTypeA q (φ sl3E01 * φ sl3E21) 2 := by
      rw [← map_mul]
      exact hAa1
    have hprod2 : IsTypeA q (φ sl3E10 * φ sl3E12) 2 := by
      rw [← map_mul]
      exact hAa2
    obtain ⟨u, hu, hu0⟩ := exists_ne_zero_mem_inf_of_commute hq hA01 hA21 hprod1 hcomm1
    obtain ⟨u', hu', hu'0⟩ := exists_ne_zero_mem_inf_of_commute hq hA10 hA12 hprod2 hcomm2
    have h21Z : φ sl3E21 ∈ Z := by
      rw [hZφ]
      exact Subgroup.mem_map_of_mem φ sl3E21_mem_B23
    have h12Z : φ sl3E12 ∈ Z := by
      rw [hZφ]
      exact Subgroup.mem_map_of_mem φ sl3E12_mem_B23
    have h10o : φ sl3E10 ∈ o := by
      rw [hoφ]
      exact Subgroup.mem_map_of_mem φ sl3E10_mem_B12
    have hneβ : φ sl3E01 ≠ φ sl3E10 := fun h => sl3E01_ne_sl3E10 (hφinj h)
    have hinfβ : commSpace (φ sl3E01) ⊓ commSpace (φ sl3E10) = ⊥ :=
      ho.disj _ h01o _ h10o hA01.2.2.1 hA10.2.2.1 hA01.2.1 hA10.2.1 hneβ
    refine ⟨u, u', ?_, ?_, hu0, hu'0, ?_, ?_, ?_⟩
    · exact ⟨(le_iSup₂_of_le (φ sl3E21) h21Z le_rfl : commSpace (φ sl3E21) ≤ subCommSpace Z) hu.2,
        (le_iSup₂_of_le (φ sl3E01) h01o le_rfl : commSpace (φ sl3E01) ≤ subCommSpace o) hu.1⟩
    · exact ⟨(le_iSup₂_of_le (φ sl3E12) h12Z le_rfl : commSpace (φ sl3E12) ≤ subCommSpace Z) hu'.2,
        (le_iSup₂_of_le (φ sl3E10) h10o le_rfl : commSpace (φ sl3E10) ≤ subCommSpace o) hu'.1⟩
    · intro h
      have hmem : u ∈ commSpace (φ sl3E01) ⊓ commSpace (φ sl3E10) :=
        ⟨hu.1, by rw [h]; exact hu'.1⟩
      rw [hinfβ, Submodule.mem_bot] at hmem
      exact hu0 hmem
    · exact hA01.2.2.2.2 u hu.1
    · exact hA10.2.2.2.2 u' hu'.1

theorem subCommSpace_eq_sup_of_standardPairs (hq : q.polarBilin.Nondegenerate)
    {W₁ W₂ Z o₁ o₂ : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hW₁ : W₁ ≤ TauCeti.QuadraticMap.orthogonalGroup q)
    (hW₂ : W₂ ≤ TauCeti.QuadraticMap.orthogonalGroup q)
    (h₁ : LinearBlockStandardPair (ZMod 2) W₁ Z o₁)
    (h₂ : LinearBlockStandardPair (ZMod 2) W₂ Z o₂)
    (ho₁ : IsRootS3Like q o₁) (ho₂ : IsRootS3Like q o₂)
    (hdim : Module.finrank (ZMod 2) (subCommSpace o₁) = 4)
    (horth : ∀ a ∈ subCommSpace o₁, ∀ b ∈ subCommSpace o₂, QuadraticMap.polar q a b = 0)
    (hnd : ∀ a ∈ subCommSpace o₁, (∀ b ∈ subCommSpace o₁, QuadraticMap.polar q a b = 0) → a = 0) :
    subCommSpace Z = (subCommSpace Z ⊓ subCommSpace o₁) ⊔ (subCommSpace Z ⊓ subCommSpace o₂) ∧
    (∃ u u', subCommSpace Z ⊓ subCommSpace o₁ = Submodule.span (ZMod 2) {u, u'} ∧
      q u = 0 ∧ q u' = 0 ∧ QuadraticMap.polar q u u' = 1) ∧
    (∃ u u', subCommSpace Z ⊓ subCommSpace o₂ = Submodule.span (ZMod 2) {u, u'} ∧
      q u = 0 ∧ q u' = 0 ∧ QuadraticMap.polar q u u' = 1) := by
  obtain ⟨w₁, hw₁W, ho₁_eq⟩ := exists_conj_of_linearBlockStandardPair h₁
  have hw₁O : w₁ ∈ TauCeti.QuadraticMap.orthogonalGroup q := hW₁ hw₁W
  have hmap₁ : subCommSpace o₁ = (subCommSpace Z).map (w₁ : V →ₗ[ZMod 2] V) := by
    rw [ho₁_eq, subCommSpace_map_conj]
  have hdimZ : Module.finrank (ZMod 2) (subCommSpace Z) = 4 := by
    rw [← hdim, hmap₁, LinearEquiv.finrank_map_eq]
  have hndZ : ∀ a ∈ subCommSpace Z,
      (∀ b ∈ subCommSpace Z, QuadraticMap.polar q a b = 0) → a = 0 := by
    intro a ha hortha
    have hw₁aO : w₁ a ∈ subCommSpace o₁ := by
      rw [hmap₁]
      exact Submodule.mem_map_of_mem ha
    have hzero : w₁ a = 0 := by
      refine hnd (w₁ a) hw₁aO fun b hb => ?_
      rw [hmap₁] at hb
      obtain ⟨c, hc, rfl⟩ := hb
      change QuadraticMap.polar q (w₁ a) (w₁ c) = 0
      rw [CFSG.ClassicalGroups.Orthogonal.polar_map_of_mem hw₁O]
      exact hortha c hc
    exact w₁.injective (by rw [hzero, map_zero])
  obtain ⟨u₁, u₁', hu₁, hu₁', hu₁0, hu₁'0, hu₁ne, hqu₁, hqu₁'⟩ :=
    exists_singular_pair_of_standardPair hq hW₁ h₁ ho₁
  obtain ⟨u₂, u₂', hu₂, hu₂', hu₂0, hu₂'0, hu₂ne, hqu₂, hqu₂'⟩ :=
    exists_singular_pair_of_standardPair hq hW₂ h₂ ho₂
  set A₁ : Submodule (ZMod 2) V := subCommSpace Z ⊓ subCommSpace o₁ with hA₁
  set A₂ : Submodule (ZMod 2) V := subCommSpace Z ⊓ subCommSpace o₂ with hA₂
  have hspan₁ : Submodule.span (ZMod 2) {u₁, u₁'} ≤ A₁ := by
    rw [Submodule.span_le]
    intro x hx
    rw [hA₁]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hu₁
    · exact hu₁'
  have hspan₂ : Submodule.span (ZMod 2) {u₂, u₂'} ≤ A₂ := by
    rw [Submodule.span_le]
    intro x hx
    rw [hA₂]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hu₂
    · exact hu₂'
  have hli₁ : LinearIndependent (ZMod 2) ![u₁, u₁'] := by
    rw [LinearIndependent.pair_iff' hu₁0]
    intro a
    rcases OrthoF2.zmod2_eq_zero_or_eq_one a with rfl | rfl
    · simp only [zero_smul]
      exact fun h => hu₁'0 h.symm
    · simpa only [one_smul] using hu₁ne
  have hli₂ : LinearIndependent (ZMod 2) ![u₂, u₂'] := by
    rw [LinearIndependent.pair_iff' hu₂0]
    intro a
    rcases OrthoF2.zmod2_eq_zero_or_eq_one a with rfl | rfl
    · simp only [zero_smul]
      exact fun h => hu₂'0 h.symm
    · simpa only [one_smul] using hu₂ne
  have hrange₁ : (Set.range ![u₁, u₁'] : Set V) = {u₁, u₁'} := by
    ext x
    simp [or_comm]
  have hrange₂ : (Set.range ![u₂, u₂'] : Set V) = {u₂, u₂'} := by
    ext x
    simp [or_comm]
  have hfr₁ : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) {u₁, u₁'}) = 2 := by
    have h := finrank_span_eq_card hli₁
    rw [Fintype.card_fin, hrange₁] at h
    exact h
  have hfr₂ : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) {u₂, u₂'}) = 2 := by
    have h := finrank_span_eq_card hli₂
    rw [Fintype.card_fin, hrange₂] at h
    exact h
  have hle₁ : 2 ≤ Module.finrank (ZMod 2) A₁ :=
    calc 2 = Module.finrank (ZMod 2) (Submodule.span (ZMod 2) {u₁, u₁'}) := hfr₁.symm
      _ ≤ Module.finrank (ZMod 2) A₁ := Submodule.finrank_mono hspan₁
  have hle₂ : 2 ≤ Module.finrank (ZMod 2) A₂ :=
    calc 2 = Module.finrank (ZMod 2) (Submodule.span (ZMod 2) {u₂, u₂'}) := hfr₂.symm
      _ ≤ Module.finrank (ZMod 2) A₂ := Submodule.finrank_mono hspan₂
  have hA₁_le : A₁ ≤ subCommSpace Z := by rw [hA₁]; exact inf_le_left
  have hA₂_le : A₂ ≤ subCommSpace Z := by rw [hA₂]; exact inf_le_left
  have hdisj : A₁ ⊓ A₂ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hx₁, hx₂⟩ := Submodule.mem_inf.mp hx
    rw [hA₁] at hx₁
    rw [hA₂] at hx₂
    have hxO₁ : x ∈ subCommSpace o₁ := hx₁.2
    have hxO₂ : x ∈ subCommSpace o₂ := hx₂.2
    have hx0 : x = 0 := hnd x hxO₁ fun b hb => by
      rw [QuadraticMap.polar_comm]
      exact horth b hb x hxO₂
    rw [Submodule.mem_bot]
    exact hx0
  have hsup_le : A₁ ⊔ A₂ ≤ subCommSpace Z := sup_le hA₁_le hA₂_le
  have hdim_sup : Module.finrank (ZMod 2) ↥(A₁ ⊔ A₂) = 4 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq A₁ A₂
    rw [hdisj, finrank_bot] at h
    have hle : Module.finrank (ZMod 2) ↥(A₁ ⊔ A₂) ≤ 4 := by
      have := Submodule.finrank_mono hsup_le
      rwa [hdimZ] at this
    omega
  have hsup_eq : A₁ ⊔ A₂ = subCommSpace Z :=
    Submodule.eq_of_le_of_finrank_eq hsup_le (by rw [hdim_sup, hdimZ])
  have hsum : Module.finrank (ZMod 2) A₁ + Module.finrank (ZMod 2) A₂ = 4 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq A₁ A₂
    rw [hdisj, finrank_bot, hdim_sup] at h
    omega
  have hfin₁ : Module.finrank (ZMod 2) A₁ = 2 := by omega
  have hfin₂ : Module.finrank (ZMod 2) A₂ = 2 := by omega
  have hspan₁_eq : A₁ = Submodule.span (ZMod 2) {u₁, u₁'} :=
    (Submodule.eq_of_le_of_finrank_eq hspan₁ (by rw [hfin₁, hfr₁])).symm
  have hspan₂_eq : A₂ = Submodule.span (ZMod 2) {u₂, u₂'} :=
    (Submodule.eq_of_le_of_finrank_eq hspan₂ (by rw [hfin₂, hfr₂])).symm
  have hpolar₁ : QuadraticMap.polar q u₁ u₁' = 1 := by
    apply OrthoF2.zmod2_eq_one_of_ne_zero
    intro hp0
    have horth_all : ∀ b ∈ subCommSpace Z, QuadraticMap.polar q u₁ b = 0 := by
      intro b hb
      have hb' : b ∈ A₁ ⊔ A₂ := by rw [hsup_eq]; exact hb
      obtain ⟨a, ha, d, hd, rfl⟩ := Submodule.mem_sup.mp hb'
      have ha0 : QuadraticMap.polar q u₁ a = 0 := by
        rw [hspan₁_eq] at ha
        obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp ha
        rw [QuadraticMap.polar_add_right, QuadraticMap.polar_smul_right,
          QuadraticMap.polar_smul_right,
          CFSG.ClassicalGroups.Orthogonal.polar_self_eq_zero hqu₁, hp0]
        simp
      have hd0 : QuadraticMap.polar q u₁ d = 0 := by
        rw [hA₂] at hd
        exact horth u₁ hu₁.2 d hd.2
      rw [QuadraticMap.polar_add_right, ha0, hd0, add_zero]
    exact hu₁0 (hndZ u₁ hu₁.1 horth_all)
  have hpolar₂ : QuadraticMap.polar q u₂ u₂' = 1 := by
    apply OrthoF2.zmod2_eq_one_of_ne_zero
    intro hp0
    have horth_all : ∀ b ∈ subCommSpace Z, QuadraticMap.polar q u₂ b = 0 := by
      intro b hb
      have hb' : b ∈ A₁ ⊔ A₂ := by rw [hsup_eq]; exact hb
      obtain ⟨a, ha, d, hd, rfl⟩ := Submodule.mem_sup.mp hb'
      have ha0 : QuadraticMap.polar q u₂ a = 0 := by
        rw [hA₁] at ha
        rw [QuadraticMap.polar_comm]
        exact horth a ha.2 u₂ hu₂.2
      have hd0 : QuadraticMap.polar q u₂ d = 0 := by
        rw [hspan₂_eq] at hd
        obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hd
        rw [QuadraticMap.polar_add_right, QuadraticMap.polar_smul_right,
          QuadraticMap.polar_smul_right,
          CFSG.ClassicalGroups.Orthogonal.polar_self_eq_zero hqu₂, hp0]
        simp
      rw [QuadraticMap.polar_add_right, ha0, hd0, add_zero]
    exact hu₂0 (hndZ u₂ hu₂.1 horth_all)
  refine ⟨hsup_eq.symm, ⟨u₁, u₁', hspan₁_eq, hqu₁, hqu₁', hpolar₁⟩,
    ⟨u₂, u₂', hspan₂_eq, hqu₂, hqu₂', hpolar₂⟩⟩

end CFSG.StandardType.FrameRoute.FS81
