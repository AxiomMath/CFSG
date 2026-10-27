module

public import CFSG.RankThree.PartOne.KLAY.D4
public import CFSG.RankThree.PartOne.KE.SigmaCentralizer

public section

namespace CFSG.RankThree.PartOne.KLAY

open CFSG CFSG.LocalCores CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KFU CFSG.RankThree.Classical
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Timmesfeld.ExceptionalOrders (rootList mem_rootList)

open scoped Pointwise

variable {p f : ℕ} {K : Type} [Field K] {σ : K →+* K}

theorem twistHom_simpleRootSL2 (σ : K →+* K) (i : Fin TwistTag.D4.tag.rank) (B : SL2 K) :
    twistHom TwistTag.D4 K σ (simpleRootSL2 TwistTag.D4.tag K i B) =
      simpleRootSL2 TwistTag.D4.tag K (TwistTag.D4.perm i) (Matrix.SpecialLinearGroup.map σ B) := by
  have h : (twistHom TwistTag.D4 K σ).comp (simpleRootSL2 TwistTag.D4.tag K i) =
      (simpleRootSL2 TwistTag.D4.tag K (TwistTag.D4.perm i)).comp
        (Matrix.SpecialLinearGroup.map σ) := by
    refine MonoidHom.eq_of_eqOn_dense sl2_closure_upper_lower fun g hg => ?_
    rcases hg with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · change twistHom TwistTag.D4 K σ (simpleRootSL2 TwistTag.D4.tag K i (uSL c)) =
        simpleRootSL2 TwistTag.D4.tag K (TwistTag.D4.perm i)
          (Matrix.SpecialLinearGroup.map σ (uSL c))
      rw [simpleRootSL2_uSL, twistHom_xUnit, map_uSL, simpleRootSL2_uSL]
    · change twistHom TwistTag.D4 K σ (simpleRootSL2 TwistTag.D4.tag K i (vSL c)) =
        simpleRootSL2 TwistTag.D4.tag K (TwistTag.D4.perm i)
          (Matrix.SpecialLinearGroup.map σ (vSL c))
      rw [simpleRootSL2_vSL, twistHom_yUnit, map_vSL, simpleRootSL2_vSL]
  exact DFunLike.congr_fun h B

theorem commute_outer {i j : Fin TwistTag.D4.tag.rank} (hi : i ≠ KFU.d4i2)
    (hj : j ≠ KFU.d4i2) (hij : i ≠ j) (A B : SL2 K) :
    Commute (simpleRootSL2 TwistTag.D4.tag K i A) (simpleRootSL2 TwistTag.D4.tag K j B) := by
  have h : ∀ k : Fin TwistTag.D4.tag.rank, k ≠ KFU.d4i2 →
      k ∈ TwistTag.D4.orbit (⟨0, by decide⟩ : Fin TwistTag.D4.foldedTag.rank) := by
    intro k hk
    rcases KFU.fin_D4_cases k with rfl | rfl | rfl | rfl
    · decide
    · decide
    · exact absurd rfl hk
    · decide
  exact commute_rankOneHom (t := TwistTag.D4) (h i hi) (h j hj) hij A B

@[expose] noncomputable def muD4 (K : Type) [Field K] :
    SL2 K × (SL2 K × SL2 K) →* ModGL TwistTag.D4.tag K :=
  (simpleRootSL2 TwistTag.D4.tag K KFU.d4i0).noncommCoprod
    ((simpleRootSL2 TwistTag.D4.tag K KFU.d4i1).noncommCoprod
      (simpleRootSL2 TwistTag.D4.tag K KFU.d4i3)
      fun A B => commute_outer (by decide) (by decide) (by decide) A B)
    fun A ⟨B, C⟩ => by
      rw [MonoidHom.noncommCoprod_apply]
      exact (commute_outer (by decide) (by decide) (by decide) A B).mul_right
        (commute_outer (by decide) (by decide) (by decide) A C)

theorem muD4_apply (A B C : SL2 K) :
    muD4 K (A, (B, C)) = simpleRootSL2 TwistTag.D4.tag K KFU.d4i0 A *
      (simpleRootSL2 TwistTag.D4.tag K KFU.d4i1 B * simpleRootSL2 TwistTag.D4.tag K KFU.d4i3 C) :=
  rfl

theorem muD4_injective [CharP K 2] : Function.Injective (muD4 K) := by
  rintro ⟨A, B, C⟩ ⟨A', B', C'⟩ h
  rw [muD4_apply, muD4_apply] at h
  have h13 : Function.Injective
      ((simpleRootSL2 TwistTag.D4.tag K KFU.d4i1).noncommCoprod
        (simpleRootSL2 TwistTag.D4.tag K KFU.d4i3)
        fun A B => commute_outer (by decide) (by decide) (by decide) A B) := by
    rintro ⟨B, C⟩ ⟨B', C'⟩ h'
    rw [MonoidHom.noncommCoprod_apply, MonoidHom.noncommCoprod_apply] at h'
    obtain ⟨hB, hC⟩ := eq_of_mul_eq_mul_of_commute
      (simpleRootSL2_injective_of_charTwo KFU.d4i1) (simpleRootSL2_injective_of_charTwo KFU.d4i3)
      (fun A B => commute_outer (by decide) (by decide) (by decide) A B) h'
    exact Prod.ext hB hC
  obtain ⟨hA, hBC⟩ := eq_of_mul_eq_mul_of_commute (simpleRootSL2_injective_of_charTwo KFU.d4i0)
    h13 (fun A ⟨B, C⟩ => by
      rw [MonoidHom.noncommCoprod_apply]
      exact (commute_outer (by decide) (by decide) (by decide) A B).mul_right
        (commute_outer (by decide) (by decide) (by decide) A C))
    (g := (simpleRootSL2 TwistTag.D4.tag K KFU.d4i1).noncommCoprod
        (simpleRootSL2 TwistTag.D4.tag K KFU.d4i3)
        fun A B => commute_outer (by decide) (by decide) (by decide) A B)
    (B := (B, C)) (B' := (B', C')) (by simpa [MonoidHom.noncommCoprod_apply] using h)
  rw [hA]
  simp only [Prod.mk.injEq] at hBC
  rw [hBC.1, hBC.2]

@[expose] def d4S : Set (Fin TwistTag.D4.tag.rank → ℤ) :=
  {Pi.single KFU.d4i0 1, -Pi.single KFU.d4i0 1, Pi.single KFU.d4i1 1, -Pi.single KFU.d4i1 1,
    Pi.single KFU.d4i3 1, -Pi.single KFU.d4i3 1}

theorem isRoot_of_mem_d4S {α : Fin TwistTag.D4.tag.rank → ℤ} (h : α ∈ d4S) :
    IsRoot TwistTag.D4.tag α := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl
  · exact IsRoot.basis _
  · exact IsRoot.neg (IsRoot.basis _)
  · exact IsRoot.basis _
  · exact IsRoot.neg (IsRoot.basis _)
  · exact IsRoot.basis _
  · exact IsRoot.neg (IsRoot.basis _)

theorem neg_mem_d4S {α : Fin TwistTag.D4.tag.rank → ℤ} (h : α ∈ d4S) : -α ∈ d4S := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [d4S]

theorem coord_d4S {α : Fin TwistTag.D4.tag.rank → ℤ} (h : α ∈ d4S) : α KFU.d4i2 = 0 := by
  have h20 : KFU.d4i2 ≠ KFU.d4i0 := by decide
  have h21 : KFU.d4i2 ≠ KFU.d4i1 := by decide
  have h23 : KFU.d4i2 ≠ KFU.d4i3 := by decide
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [h20, h21, h23]

theorem simpleRootSL2_mem_rootSpan_d4S {i : Fin TwistTag.D4.tag.rank}
    (hi : Pi.single i 1 ∈ d4S) (A : SL2 K) :
    simpleRootSL2 TwistTag.D4.tag K i A ∈ rootSpan TwistTag.D4.tag K d4S := by
  have h := KE.rootRankOneGroup_le_rootSpan (τ := TwistTag.D4.tag) (L := K)
    (isRoot_of_mem_d4S hi) hi (neg_mem_d4S hi) ⟨A, by rw [rootSL2_single]⟩
  exact h

theorem exists_of_mem_rootSpan_d4S {x : ModGL TwistTag.D4.tag K}
    (hx : x ∈ rootSpan TwistTag.D4.tag K d4S) : ∃ A B C : SL2 K, x = muD4 K (A, (B, C)) := by
  have hle : rootSpan TwistTag.D4.tag K d4S ≤ (muD4 K).range := by
    refine iSup₂_le fun α hα => ?_
    rw [rootSubgroup, Subgroup.closure_le]
    rintro _ ⟨c, rfl⟩
    rcases hα with rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨(uSL c, (1, 1)), ?_⟩
      rw [muD4_apply, map_one, map_one, mul_one, mul_one, simpleRootSL2_uSL, pinnedX_single]
    · refine ⟨(vSL c, (1, 1)), ?_⟩
      rw [muD4_apply, map_one, map_one, mul_one, mul_one, simpleRootSL2_vSL, pinnedX_neg_single]
    · refine ⟨(1, (uSL c, 1)), ?_⟩
      rw [muD4_apply, map_one, map_one, mul_one, one_mul, simpleRootSL2_uSL, pinnedX_single]
    · refine ⟨(1, (vSL c, 1)), ?_⟩
      rw [muD4_apply, map_one, map_one, mul_one, one_mul, simpleRootSL2_vSL, pinnedX_neg_single]
    · refine ⟨(1, (1, uSL c)), ?_⟩
      rw [muD4_apply, map_one, map_one, one_mul, one_mul, simpleRootSL2_uSL, pinnedX_single]
    · refine ⟨(1, (1, vSL c)), ?_⟩
      rw [muD4_apply, map_one, map_one, one_mul, one_mul, simpleRootSL2_vSL, pinnedX_neg_single]
  obtain ⟨⟨A, B, C⟩, h⟩ := hle hx
  exact ⟨A, B, C, h.symm⟩

@[expose] noncomputable def phi3 (σ : K →+* K) : SL2 K →* ModGL TwistTag.D4.tag K :=
  (muD4 K).comp ((MonoidHom.id (SL2 K)).prod ((Matrix.SpecialLinearGroup.map σ).prod
    (Matrix.SpecialLinearGroup.map (σ.comp σ))))

theorem phi3_apply (A : SL2 K) :
    phi3 σ A = muD4 K (A, (Matrix.SpecialLinearGroup.map σ A,
      Matrix.SpecialLinearGroup.map (σ.comp σ) A)) :=
  rfl

theorem map_cube (hP : D4Param p f K σ) (A : SL2 K) :
    Matrix.SpecialLinearGroup.map σ (Matrix.SpecialLinearGroup.map (σ.comp σ) A) = A := by
  apply Subtype.ext
  ext i j
  simp [Matrix.SpecialLinearGroup.map_apply_coe, hP.sigma_cube]

theorem map_map_eq_comp (A : SL2 K) :
    Matrix.SpecialLinearGroup.map σ (Matrix.SpecialLinearGroup.map σ A) =
      Matrix.SpecialLinearGroup.map (σ.comp σ) A := by
  apply Subtype.ext
  ext i j
  simp [Matrix.SpecialLinearGroup.map_apply_coe]

theorem twistHom_phi3 (hP : D4Param p f K σ) (A : SL2 K) :
    twistHom TwistTag.D4 K σ (phi3 σ A) = phi3 σ A := by
  obtain ⟨e0, e1, e3, -⟩ := perm_D4_values
  rw [phi3_apply, muD4_apply, map_mul, map_mul, twistHom_simpleRootSL2, twistHom_simpleRootSL2,
    twistHom_simpleRootSL2, e0, e1, e3, map_map_eq_comp, map_cube hP]
  have c01 := commute_outer (K := K) (i := KFU.d4i0) (j := KFU.d4i1) (by decide) (by decide)
    (by decide) A (Matrix.SpecialLinearGroup.map σ A)
  have c03 := commute_outer (K := K) (i := KFU.d4i0) (j := KFU.d4i3) (by decide) (by decide)
    (by decide) A (Matrix.SpecialLinearGroup.map (σ.comp σ) A)
  rw [← c03.eq, ← mul_assoc, ← c01.eq, mul_assoc]

theorem phi3_mem_twistedFixedGroup (hP : D4Param p f K σ) (A : SL2 K) :
    phi3 σ A ∈ twistedFixedGroup TwistTag.D4 K σ := by
  refine (mem_twistedFixedGroup_iff_twistHom TwistTag.D4 K σ).2 ⟨?_, twistHom_phi3 hP A⟩
  rw [phi3_apply, muD4_apply]
  exact mul_mem (simpleRootSL2_mem_adjointGroup _ _)
    (mul_mem (simpleRootSL2_mem_adjointGroup _ _) (simpleRootSL2_mem_adjointGroup _ _))

theorem phi3_mem_graphFixedRootGroup (hP : D4Param p f K σ) (A : SL2 K) :
    phi3 σ A ∈ graphFixedRootGroup TwistTag.D4 K σ := by
  have h : (graphFixedRootGroup TwistTag.D4 K σ).comap (phi3 σ) = ⊤ := by
    rw [eq_top_iff, ← sl2_closure_upper_lower, Subgroup.closure_le]
    rintro g (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · change phi3 σ (uSL c) ∈ graphFixedRootGroup TwistTag.D4 K σ
      refine graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
        ⟨?_, phi3_mem_twistedFixedGroup hP _⟩
      rw [phi3_apply, muD4_apply, map_uSL, map_uSL, simpleRootSL2_uSL, simpleRootSL2_uSL,
        simpleRootSL2_uSL]
      exact mul_mem (xUnit_mem_posUnipotent _ _)
        (mul_mem (xUnit_mem_posUnipotent _ _) (xUnit_mem_posUnipotent _ _))
    · change phi3 σ (vSL c) ∈ graphFixedRootGroup TwistTag.D4 K σ
      refine graphFixedNegUnipotent_le_graphFixedRootGroup _ _ _
        ⟨?_, phi3_mem_twistedFixedGroup hP _⟩
      rw [phi3_apply, muD4_apply, map_vSL, map_vSL, simpleRootSL2_vSL, simpleRootSL2_vSL,
        simpleRootSL2_vSL]
      exact mul_mem (yUnit_mem_negUnipotent _ _)
        (mul_mem (yUnit_mem_negUnipotent _ _) (yUnit_mem_negUnipotent _ _))
  have hA : A ∈ (graphFixedRootGroup TwistTag.D4 K σ).comap (phi3 σ) := by
    rw [h]
    exact Subgroup.mem_top A
  exact hA

@[expose] noncomputable def phi3C (hP : D4Param p f K σ) :
    SL2 K →* ↥(graphFixedRootGroup TwistTag.D4 K σ) :=
  (phi3 σ).codRestrict (graphFixedRootGroup TwistTag.D4 K σ) (phi3_mem_graphFixedRootGroup hP)

theorem coe_phi3C (hP : D4Param p f K σ) (A : SL2 K) :
    ((phi3C hP A : ↥(graphFixedRootGroup TwistTag.D4 K σ)) : ModGL TwistTag.D4.tag K) =
      phi3 σ A :=
  rfl

theorem phi3C_injective [CharP K 2] (hP : D4Param p f K σ) :
    Function.Injective (phi3C hP) := by
  intro A A' h
  have h1 : phi3 σ A = phi3 σ A' := congrArg Subtype.val h
  rw [phi3_apply, phi3_apply] at h1
  exact (Prod.ext_iff.1 (muD4_injective h1)).1

theorem graphFixedRootGroup_inf_rootSpan_eq [CharP K 2] (hP : D4Param p f K σ) :
    (phi3C hP).range.map (graphFixedRootGroup TwistTag.D4 K σ).subtype =
      graphFixedRootGroup TwistTag.D4 K σ ⊓ rootSpan TwistTag.D4.tag K d4S := by
  ext x
  constructor
  · rintro ⟨_, ⟨A, rfl⟩, rfl⟩
    refine ⟨(phi3C hP A).2, ?_⟩
    change phi3 σ A ∈ _
    rw [phi3_apply, muD4_apply]
    exact mul_mem (simpleRootSL2_mem_rootSpan_d4S (Or.inl rfl) _)
      (mul_mem (simpleRootSL2_mem_rootSpan_d4S (Or.inr (Or.inr (Or.inl rfl))) _)
        (simpleRootSL2_mem_rootSpan_d4S (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) _))
  · rintro ⟨hxC, hxQ⟩
    obtain ⟨A, B, C, rfl⟩ := exists_of_mem_rootSpan_d4S hxQ
    have hfix := ((mem_twistedFixedGroup_iff_twistHom TwistTag.D4 K σ).1
      (graphFixedRootGroup_le TwistTag.D4 K σ hxC)).2
    obtain ⟨e0, e1, e3, -⟩ := perm_D4_values
    rw [muD4_apply, map_mul, map_mul, twistHom_simpleRootSL2, twistHom_simpleRootSL2,
      twistHom_simpleRootSL2, e0, e1, e3] at hfix
    have c01 := commute_outer (K := K) (i := KFU.d4i0) (j := KFU.d4i1) (by decide) (by decide)
      (by decide) (Matrix.SpecialLinearGroup.map σ C) (Matrix.SpecialLinearGroup.map σ A)
    have c03 := commute_outer (K := K) (i := KFU.d4i0) (j := KFU.d4i3) (by decide) (by decide)
      (by decide) (Matrix.SpecialLinearGroup.map σ C) (Matrix.SpecialLinearGroup.map σ B)
    have hmu : muD4 K (Matrix.SpecialLinearGroup.map σ C, (Matrix.SpecialLinearGroup.map σ A,
        Matrix.SpecialLinearGroup.map σ B)) = muD4 K (A, (B, C)) := by
      simp only [muD4_apply]
      rw [← hfix, ← c03.eq, ← mul_assoc, c01.eq, mul_assoc]
    have hinj := Prod.ext_iff.1 (muD4_injective hmu)
    obtain ⟨hA, hBC⟩ := hinj
    obtain ⟨hB, hC⟩ := Prod.ext_iff.1 hBC
    simp only at hA hB hC
    subst hB
    subst hC
    refine ⟨phi3C hP A, ⟨A, rfl⟩, ?_⟩
    change phi3 σ A = _
    rw [phi3_apply, map_map_eq_comp]

set_option maxRecDepth 100000 in
theorem d4_root_check_three :
    ∀ β ∈ rootList TwistTag.D4.tag, (β KFU.d4i2).natAbs ≤ 2 ∧
      (β KFU.d4i2 = 0 →
        (β = Pi.single KFU.d4i0 1 ∨ β = -Pi.single KFU.d4i0 1 ∨ β = Pi.single KFU.d4i1 1 ∨
          β = -Pi.single KFU.d4i1 1 ∨ β = Pi.single KFU.d4i3 1 ∨ β = -Pi.single KFU.d4i3 1)) := by
  decide +kernel

theorem d4_kernel_three (h5 : 5 ≤ p) {b : Kˣ} (hb : IsPrimitiveRoot b p) :
    rootCharKernel (d4Tuple 1 b) ⊆ d4S := by
  rintro β ⟨hβ, hχ⟩
  rw [rootChar_d4, d4Tuple_zero, d4Tuple_one, d4Tuple_two, d4Tuple_three, one_zpow, one_zpow,
    one_zpow, one_mul, one_mul, mul_one] at hχ
  have hdvd := (hb.zpow_eq_one_iff_dvd _).1 hχ
  obtain ⟨hle, hzero⟩ := d4_root_check_three β ((mem_rootList).2 hβ)
  have hn : β KFU.d4i2 = 0 := by
    have h1 : p ∣ (β KFU.d4i2).natAbs := Int.natCast_dvd.1 hdvd
    have := Nat.eq_zero_of_dvd_of_lt h1 (by omega)
    omega
  exact hzero hn

theorem d4_centralizer_mem_three (hp : p.Prime) (h5 : 5 ≤ p)
    {a : Fin TwistTag.D4.tag.rank → Kˣ} (hap : ∀ i, a i ^ p = 1) (ha1 : a ≠ 1)
    (hker : rootCharKernel a ⊆ d4S)
    {y : ModGL TwistTag.D4.tag K} (hy : y ∈ adjointGroup TwistTag.D4.tag K)
    (hc : y * rootDiagUnit TwistTag.D4.tag a = rootDiagUnit TwistTag.D4.tag a * y) :
    y ∈ (torusGroup TwistTag.D4.tag K : Set (ModGL TwistTag.D4.tag K)) *
      (rootSpan TwistTag.D4.tag K d4S : Set (ModGL TwistTag.D4.tag K)) :=
  KE.mem_torus_mul_rootSpan_of_commute hp (KGD.not_dvd_card_weylGroup_D4 hp (by omega)) hap ha1
    (fun α hα => isRoot_of_mem_d4S hα) (fun α hα => neg_mem_d4S hα) hker hy hc

theorem conjSL_map_of_fixed (ι : K →+* K) (χ : Kˣ) (hχ : ι (χ : K) = χ) (A : SL2 K) :
    conjSL (diagUnitOne χ) (Matrix.SpecialLinearGroup.map ι A) =
      Matrix.SpecialLinearGroup.map ι (conjSL (diagUnitOne χ) A) := by
  have h := map_conjSL_diagUnitOne ι χ A
  rwa [show Units.map (ι : K →* K) χ = χ from Units.ext hχ] at h

theorem d4_act_three (hP : D4Param p f K σ) (b : Fin 2 → rootsOfUnity p K) (A : SL2 K) :
    tp3M hP b * phi3C hP A * (tp3M hP b)⁻¹ =
      phi3C hP (conjSL (diagUnitOne ((b 1 : rootsOfUnity p K) : Kˣ)) A) := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_tp3M, coe_phi3C, coe_phi3C,
    tp3Hom_apply]
  set χ : Kˣ := ((b 1 : rootsOfUnity p K) : Kˣ) with hχ
  set a : Fin TwistTag.D4.tag.rank → Kˣ := d4Tuple χ ((b 0 : rootsOfUnity p K) : Kˣ) with ha
  have hχp : χ ^ p = 1 := (mem_rootsOfUnity p _).1 (b 1).2
  have hσ : σ (χ : K) = χ := hP.sigma_fix χ hχp
  have hσσ : (σ.comp σ) (χ : K) = χ := by
    change σ (σ (χ : K)) = χ
    rw [hσ, hσ]
  have key : ∀ (i : Fin TwistTag.D4.tag.rank) (M : SL2 K), a i = χ →
      rootDiagUnit TwistTag.D4.tag a * simpleRootSL2 TwistTag.D4.tag K i M *
        (rootDiagUnit TwistTag.D4.tag a)⁻¹ =
      simpleRootSL2 TwistTag.D4.tag K i (conjSL (diagUnitOne χ) M) := by
    intro i M hi
    have h := rootDiagUnit_conj_rootSL2 a (IsRoot.basis i) M
    rw [rootSL2_single, rootChar_single, hi] at h
    exact h
  rw [phi3_apply, muD4_apply, phi3_apply, muD4_apply]
  have e : ∀ X Y Z d : ModGL TwistTag.D4.tag K, d * (X * (Y * Z)) * d⁻¹ =
      (d * X * d⁻¹) * ((d * Y * d⁻¹) * (d * Z * d⁻¹)) := fun X Y Z d => by group
  rw [e, key KFU.d4i0 _ (d4Tuple_zero _ _), key KFU.d4i1 _ (d4Tuple_one _ _),
    key KFU.d4i3 _ (d4Tuple_three _ _), conjSL_map_of_fixed σ χ hσ,
    conjSL_map_of_fixed (σ.comp σ) χ hσσ]

theorem d4_SL2Torus_three (hP : D4Param p f K σ) {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ p) :
    SL2Torus p (phi3C hP) (Tp3 hP) := by
  have : Finite K := hP.finite
  have hchar : CharP K 2 := ringChar.of_eq hP.ringChar_eq_two
  have hinj := phi3C_injective hP
  have h5 := hP.five_le
  refine ⟨hinj, fun t ht => Tp3_exp hP t ht, ?_, ?_, ?_⟩
  · rintro t ⟨b, rfl⟩
    exact ⟨((b 1 : rootsOfUnity p K) : Kˣ), fun A => d4_act_three hP b A⟩
  · intro s hs
    have hmem : ∀ n : ℤ, s ^ n ∈ rootsOfUnity p K := fun n => by
      rw [mem_rootsOfUnity, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hs,
        one_zpow]
    have hσ : σ (s : K) = s := hP.sigma_fix s hs
    refine ⟨![⟨s ^ (-3 : ℤ), hmem (-3)⟩, ⟨s ^ (2 : ℤ), hmem 2⟩], Subtype.ext ?_⟩
    rw [coe_tp3M, coe_phi3C, tp3Hom_apply, phi3_apply, muD4_apply, map_HSL, map_HSL,
      simpleRootSL2_HSL, simpleRootSL2_HSL, simpleRootSL2_HSL,
      show Units.map (σ : K →* K) s = s from Units.ext hσ,
      show Units.map ((σ.comp σ : K →+* K) : K →* K) s = s from Units.ext (by
        change σ (σ (s : K)) = s
        rw [hσ, hσ]),
      torusElt_eq_rootDiagUnit, torusElt_eq_rootDiagUnit, torusElt_eq_rootDiagUnit,
      ← rootDiagUnit_mul, ← rootDiagUnit_mul]
    congr 1
    funext j
    rcases KFU.fin_D4_cases j with rfl | rfl | rfl | rfl
    · simp [d4Tuple_zero, show TwistTag.D4.tag.cartan KFU.d4i0 KFU.d4i0 = 2 by decide,
        show TwistTag.D4.tag.cartan KFU.d4i1 KFU.d4i0 = 0 by decide,
        show TwistTag.D4.tag.cartan KFU.d4i3 KFU.d4i0 = 0 by decide]
    · simp [d4Tuple_one, show TwistTag.D4.tag.cartan KFU.d4i0 KFU.d4i1 = 0 by decide,
        show TwistTag.D4.tag.cartan KFU.d4i1 KFU.d4i1 = 2 by decide,
        show TwistTag.D4.tag.cartan KFU.d4i3 KFU.d4i1 = 0 by decide]
    · simp [d4Tuple_two, show TwistTag.D4.tag.cartan KFU.d4i0 KFU.d4i2 = -1 by decide,
        show TwistTag.D4.tag.cartan KFU.d4i1 KFU.d4i2 = -1 by decide,
        show TwistTag.D4.tag.cartan KFU.d4i3 KFU.d4i2 = -1 by decide]
      group
    · simp [d4Tuple_three, show TwistTag.D4.tag.cartan KFU.d4i0 KFU.d4i3 = 0 by decide,
        show TwistTag.D4.tag.cartan KFU.d4i1 KFU.d4i3 = 0 by decide,
        show TwistTag.D4.tag.cartan KFU.d4i3 KFU.d4i3 = 2 by decide]
  · have hz : ζ ^ p = 1 := hζ.pow_eq_one
    let z : rootsOfUnity p K := ⟨ζ, (mem_rootsOfUnity p ζ).2 hz⟩
    refine ⟨tp3M hP ![1, z], ⟨_, rfl⟩, fun h => ?_⟩
    have h1 := d4_act_three hP ![1, z] (uSL 1)
    rw [h1, conjSL_diagUnitOne_uSL] at h
    have hu : (uSL (((![1, z] 1 : rootsOfUnity p K) : Kˣ) * 1 : K) : SL2 K) = uSL 1 := hinj h
    have := congrArg (fun X : SL2 K => (X : Matrix (Fin 2) (Fin 2) K) 0 1) hu
    simp only [coe_uSL, mul_one] at this
    have hζ1 : ζ = 1 := Units.ext (by simpa [z] using this)
    exact hζ.ne_one (by omega) hζ1

theorem d4_layerD_three (hP : D4Param p f K σ) {z : rootsOfUnity p K}
    (hz : IsPrimitiveRoot (z : Kˣ) p) :
    layerD (tp3M hP ![z, 1]) = (phi3C hP).range := by
  classical
  have : Finite K := hP.finite
  have hchar : CharP K 2 := ringChar.of_eq hP.ringChar_eq_two
  have hp := hP.prime
  have h5 := hP.five_le
  have hζp : (z : Kˣ) ^ p = 1 := hz.pow_eq_one
  have hζ1 : (z : Kˣ) ≠ 1 := hz.ne_one (by omega)
  have h4 : 4 ≤ Nat.card K := by
    have hpf : p ≤ 2 ^ f - 1 := Nat.le_of_dvd (by
      have := Nat.one_lt_two_pow (n := f) (by have := hP.one_le; omega)
      omega) hP.dvd
    have h6 : 6 ^ 3 ≤ (2 ^ f) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    rw [hP.card]
    omega
  set bM : ↥(graphFixedRootGroup TwistTag.D4 K σ) := tp3M hP ![z, 1] with hbM
  let a₀ : Fin TwistTag.D4.tag.rank → Kˣ := d4Tuple 1 (z : Kˣ)
  have hbMd : ((bM : ↥(graphFixedRootGroup TwistTag.D4 K σ)) : ModGL TwistTag.D4.tag K) =
      rootDiagUnit TwistTag.D4.tag a₀ := rfl
  have hap : ∀ i, a₀ i ^ p = 1 := fun i => by
    rcases KFU.fin_D4_cases i with rfl | rfl | rfl | rfl
    · rw [show a₀ KFU.d4i0 = 1 from d4Tuple_zero _ _]; exact one_pow p
    · rw [show a₀ KFU.d4i1 = 1 from d4Tuple_one _ _]; exact one_pow p
    · rw [show a₀ KFU.d4i2 = (z : Kˣ) from d4Tuple_two _ _]; exact hζp
    · rw [show a₀ KFU.d4i3 = 1 from d4Tuple_three _ _]; exact one_pow p
  have ha1 : a₀ ≠ 1 := fun h => hζ1 (by
    have := congrFun h KFU.d4i2
    rwa [show a₀ KFU.d4i2 = (z : Kˣ) from d4Tuple_two _ _] at this)
  have hker : rootCharKernel a₀ ⊆ d4S := d4_kernel_three h5 hz
  have hSker : d4S ⊆ rootCharKernel a₀ := by
    intro α hα
    refine ⟨isRoot_of_mem_d4S hα, ?_⟩
    rw [rootChar_d4, show a₀ KFU.d4i0 = 1 from d4Tuple_zero _ _,
      show a₀ KFU.d4i1 = 1 from d4Tuple_one _ _, show a₀ KFU.d4i2 = (z : Kˣ) from d4Tuple_two _ _,
      show a₀ KFU.d4i3 = 1 from d4Tuple_three _ _, coord_d4S hα]
    simp
  have hSL := d4_SL2Torus_three hP hz
  refine inSubgroup_perfectResidual_centralizer_eq (graphFixedRootGroup TwistTag.D4 K σ) bM
    (torusGroup TwistTag.D4.tag K) (rootSpan TwistTag.D4.tag K d4S)
    (triangular_borel_structure.{0, 0} TwistTag.D4.tag K).1
    (KE.torusGroup_le_normalizer_rootSpan fun α hα => isRoot_of_mem_d4S hα) ?_ ?_
    (phi3C hP).range (graphFixedRootGroup_inf_rootSpan_eq hP) (hSL.isQuasisimple_range h4).1
  · intro x hx
    rw [hbMd]
    exact rootSpan_le_centralizer_of_char_one (fun α hα => hSker hα) hx
  · intro y hy
    have hc := congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hy)
    have hyadj : (y : ModGL TwistTag.D4.tag K) ∈ adjointGroup TwistTag.D4.tag K :=
      ((mem_twistedFixedGroup_iff_twistHom TwistTag.D4 K σ).1
        (graphFixedRootGroup_le TwistTag.D4 K σ y.2)).1
    exact d4_centralizer_mem_three hp h5 hap ha1 hker hyadj hc

end CFSG.RankThree.PartOne.KLAY
