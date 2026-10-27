module

public import CFSG.RankThree.Chevalley.SteinbergCAF4NonregularSp4
public import CFSG.RankThree.Chevalley.SteinbergBNF4NativeB2
public import CFSG.RankThree.Chevalley.SteinbergCEF4EvenQPlusTorus
public import CFSG.RankThree.Lattice.SteinbergBIListMatrix

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.E6 F4Weyl
  CFSG.LieType.AlgebraicGroups Matrix SteinbergBN
  CFSG.LocalAnalysis.ComponentInitial.FourGroupEvenCanonical CFSG.RankThree.Classical EvenF4QPlus

theorem exists_finite_mem_map_adjointGroup
    {τ : Tag} (hτ : τ = .G2 ∨ τ = .F4) (K : Type)
    [Field K] [Finite K] {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    {k : ModGL τ Ω} (hk : k ∈ adjointGroup τ Ω) :
    ∃ M : IntermediateField K Ω, FiniteDimensional K M ∧
      k ∈ (adjointGroup τ M).map (baseChangeGL (algebraMap M Ω)) := by
  classical
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have : Algebra.IsIntegral K Ω := (IsAlgClosure.isAlgebraic (R := K) (K := Ω)).isIntegral
  set S : Set Ω := Set.range fun p : Label τ × Label τ =>
    (k : Module.End Ω (RootModule τ Ω)) (Finsupp.single p.1 1) p.2 with hS
  have : Finite S := Set.finite_range _ |>.to_subtype
  set M : IntermediateField K Ω := IntermediateField.adjoin K S with hM
  have hMfin : FiniteDimensional K M :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  have : Finite M := Module.finite_of_finite K
  obtain ⟨Fr, hFr⟩ := exists_ringHom_pow_card M Ω
  have hbij : Function.Bijective Fr := frobenius_bijective (k := M) Fr hFr
  have hfixS : ∀ s ∈ S, Fr s = s := fun s hs => by
    have hsM : s ∈ M := IntermediateField.subset_adjoin K S hs
    have : Fintype M := Fintype.ofFinite M
    rw [hFr, Nat.card_eq_fintype_card]
    have h := FiniteField.pow_card (⟨s, hsM⟩ : M)
    exact congrArg Subtype.val h
  have hkfix : Units.map (entrywiseHom Fr) k = k := by
    refine Units.ext (Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_)
    change entrywise Fr (k : Module.End Ω (RootModule τ Ω)) (Finsupp.single b 1) =
      (k : Module.End Ω (RootModule τ Ω)) (Finsupp.single b 1)
    rw [entrywise_single]
    ext b'
    rw [Finsupp.mapRange_apply]
    exact hfixS _ ⟨(b, b'), rfl⟩
  refine ⟨M, hMfin, ?_⟩
  rw [← frobenius_fixed_eq_map_of_bijective hτ Fr hFr hbij]
  exact Subgroup.mem_inf.2 ⟨hk, hkfix⟩

section Monomial

variable {L : Type} [Field L]

theorem exists_rootDiagUnit_conj_eq_on_subsystemGroup
    {m : ModGL .F4 L}
    (hm : m ∈ monomialSubgroup .F4 L) {w : WeylGroup .F4} (hmw : MapsRootLines m w)
    (h1 : w • (Pi.single 1 1 : Fin Tag.F4.rank → ℤ) = Pi.single 1 1)
    (h2 : w • (Pi.single 2 1 : Fin Tag.F4.rank → ℤ) = Pi.single 2 1) :
    ∃ c : Fin Tag.F4.rank → Lˣ, ∀ z ∈ subsystemGroup .F4 L {1, 2},
      m * z * m⁻¹ = rootDiagUnit .F4 c * z * (rootDiagUnit .F4 c)⁻¹ := by
  classical
  obtain ⟨s, hs⟩ := exists_conj_rootSL2_eq hm hmw (isRoot_single .F4 1) h1
  obtain ⟨t, ht⟩ := exists_conj_rootSL2_eq hm hmw (isRoot_single .F4 2) h2
  set c : Fin Tag.F4.rank → Lˣ := fun j => if j = 1 then s else if j = 2 then t else 1 with hc
  have hc1 : rootChar c (Pi.single 1 1) = s := by
    rw [rootChar_pi_single, hc]
    simp
  have hc2 : rootChar c (Pi.single 2 1) = t := by
    rw [rootChar_pi_single, hc]
    simp
  have key : ∀ j ∈ ({1, 2} : Set (Fin Tag.F4.rank)), ∀ A : SL2 L,
      m * rootSL2 .F4 L (Pi.single j 1) A * m⁻¹ =
        rootDiagUnit .F4 c * rootSL2 .F4 L (Pi.single j 1) A * (rootDiagUnit .F4 c)⁻¹ := by
    rintro j (rfl | rfl) A
    · rw [hs, rootDiagUnit_conj_rootSL2 c (isRoot_single .F4 1), hc1]
    · rw [ht, rootDiagUnit_conj_rootSL2 c (isRoot_single .F4 2), hc2]
  have hgen : Set.EqOn (MulAut.conj m).toMonoidHom (MulAut.conj (rootDiagUnit .F4 c)).toMonoidHom
      {g | ∃ i ∈ ({1, 2} : Set (Fin Tag.F4.rank)), ∃ a : L,
        g = xUnit .F4 L i a ∨ g = yUnit .F4 L i a} := by
    rintro _ ⟨j, hj, a, rfl | rfl⟩
    · obtain ⟨A, hA⟩ : xUnit .F4 L j a ∈ (rootSL2 .F4 L (Pi.single j 1)).range := by
        rw [range_rootSL2_of_isRoot (isRoot_single .F4 j)]
        exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨a, pinnedX_single .F4 L j a⟩)
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [← hA]
      exact key j hj A
    · obtain ⟨A, hA⟩ : yUnit .F4 L j a ∈ (rootSL2 .F4 L (Pi.single j 1)).range := by
        rw [range_rootSL2_of_isRoot (isRoot_single .F4 j)]
        exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨a, pinnedX_neg_single .F4 L j a⟩)
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [← hA]
      exact key j hj A
  exact ⟨c, fun z hz => MonoidHom.eqOn_closure hgen hz⟩

end Monomial

theorem exists_mem_subsystemGroup_mapsRootLines
    {L : Type} [Field L] {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) :
    ∃ v ∈ subsystemGroup .F4 L {1, 2}, v ∈ monomialSubgroup .F4 L ∧
      MapsRootLines v ((simple .F4 1 * simple .F4 2) ^ ε) := by
  have hW : ∀ i ∈ ({1, 2} : Set (Fin Tag.F4.rank)),
      weylElt .F4 L i 1 ∈ subsystemGroup .F4 L {1, 2} := fun i hi => by
    rw [← simpleRootSL2_WSL i]
    have h : (simpleRootSL2 .F4 L i).range ≤ subsystemGroup .F4 L {1, 2} := by
      rw [range_simpleRootSL2, Subgroup.closure_le]
      rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
      exacts [xUnit_mem_subsystemGroup hi c, yUnit_mem_subsystemGroup hi c]
    exact h ⟨_, rfl⟩
  rcases hε with rfl | rfl
  · refine ⟨weylElt .F4 L 1 1 * weylElt .F4 L 2 1, mul_mem (hW 1 (Or.inl rfl))
      (hW 2 (Or.inr rfl)), mul_mem (weylElt_mem_monomialSubgroup 1)
      (weylElt_mem_monomialSubgroup 2), ?_⟩
    rw [zpow_one]
    exact (mapsRootLines_weylElt 1).mul (mapsRootLines_weylElt 2)
  · refine ⟨weylElt .F4 L 2 1 * weylElt .F4 L 1 1, mul_mem (hW 2 (Or.inr rfl))
      (hW 1 (Or.inl rfl)), mul_mem (weylElt_mem_monomialSubgroup 2)
      (weylElt_mem_monomialSubgroup 1), ?_⟩
    rw [_root_.zpow_neg_one, _root_.mul_inv_rev, simple_inv, simple_inv]
    exact (mapsRootLines_weylElt 2).mul (mapsRootLines_weylElt 1)

theorem exists_subsystemGroup_inf_fixed_eq
    (K : Type) [Field K] [Finite K] (Ω : Type)
    [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (F : Ω →+* Ω) (hF : ∀ c, F c = c ^ Nat.card K)
    {m : ModGL .F4 Ω} (hm : m ∈ monomialSubgroup .F4 Ω) {w : WeylGroup .F4}
    (hmw : MapsRootLines m w) {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (hw1 : w • (Pi.single 1 1 : Fin Tag.F4.rank → ℤ) =
      ((simple .F4 1 * simple .F4 2) ^ ε) • Pi.single 1 1)
    (hw2 : w • (Pi.single 2 1 : Fin Tag.F4.rank → ℤ) =
      ((simple .F4 1 * simple .F4 2) ^ ε) • Pi.single 2 1) :
    ∃ a ∈ subsystemGroup .F4 Ω {1, 2},
      subsystemGroup .F4 Ω {1, 2} ⊓ (twistedEntrywise m F).eqLocus (MonoidHom.id _) =
        ((subsystemGroup .F4 K {1, 2}).map (baseChangeGL (algebraMap K Ω))).map
          (MulAut.conj a).toMonoidHom := by
  classical
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  set Q := subsystemGroup .F4 Ω {1, 2} with hQ
  obtain ⟨v, hvQ, hvN, hvw⟩ := exists_mem_subsystemGroup_mapsRootLines (L := Ω) hε
  set m' := v⁻¹ * m with hm'
  have hm'N : m' ∈ monomialSubgroup .F4 Ω := mul_mem (inv_mem hvN) hm
  have hm'w := hvw.inv.mul hmw
  obtain ⟨c₀, hc₀⟩ := exists_rootDiagUnit_conj_eq_on_subsystemGroup hm'N hm'w
    (by rw [mul_smul, hw1, inv_smul_smul]) (by rw [mul_smul, hw2, inv_smul_smul])
  set h₀ := rootDiagUnit .F4 c₀ with hh₀
  have hh₀H : h₀ ∈ torusGroup .F4 Ω := F4_rootDiagUnit_mem_torusGroup c₀
  have hFQ : ∀ z ∈ Q, Units.map (entrywiseHom F) z ∈ Q := fun z hz =>
    baseChangeGL_mem_subsystemGroup F hz
  have hθ : ∀ z ∈ Q, twistedEntrywise m F z =
      v * (h₀ * Units.map (entrywiseHom F) z * h₀⁻¹) * v⁻¹ := fun z hz => by
    rw [twistedEntrywise_apply, ← hc₀ _ (hFQ z hz), hm']
    group
  obtain ⟨-, -, hrbij, -, -, -, -, -, hrbc, hrconj, -⟩ :=
    F4_native_B2_faithful_Sp4_all_characteristics Ω
  obtain ⟨-, -, hrbijK, -, -, -, -, -, hrbcK, -, -⟩ :=
    F4_native_B2_faithful_Sp4_all_characteristics K
  set a₀ : Ω := ((rootChar c₀ (Pi.single 1 1) : Ωˣ) : Ω) with ha₀
  set b₀ : Ω := ((rootChar c₀ (Pi.single 2 1) : Ωˣ) : Ω) with hb₀
  have ha₀0 : a₀ ≠ 0 := Units.ne_zero _
  have hb₀0 : b₀ ≠ 0 := Units.ne_zero _
  have hev1 : (h₀ : Module.End Ω (RootModule .F4 Ω)) (rootVec .F4 Ω (Pi.single 1 1)) =
      a₀ • rootVec .F4 Ω (Pi.single 1 1) := rootDiag_rootVec c₀ (isRoot_single .F4 1)
  have hev2 : (h₀ : Module.End Ω (RootModule .F4 Ω)) (rootVec .F4 Ω (Pi.single 2 1)) =
      b₀ • rootVec .F4 Ω (Pi.single 2 1) := rootDiag_rootVec c₀ (isRoot_single .F4 2)
  obtain ⟨⟨hN, hD⟩, hsim⟩ := hrconj h₀ hh₀H a₀ b₀ hev1 hev2
  set D : Matrix (Fin 4) (Fin 4) Ω := diagonal ![a₀ * b₀ ^ 2, a₀ * b₀, b₀, 1] with hDdef
  have hDdet : D.det ≠ 0 := by
    rw [hDdef, Matrix.det_diagonal, Fin.prod_univ_four]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, mul_one]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero ha₀0 (pow_ne_zero 2 hb₀0))
      (mul_ne_zero ha₀0 hb₀0)) hb₀0
  set Du : GL (Fin 4) Ω := Matrix.GeneralLinearGroup.mkOfDetNeZero D hDdet with hDu
  obtain ⟨μ, hμ⟩ := IsAlgClosed.exists_pow_nat_eq (a₀ * b₀ ^ 2) (by norm_num : 0 < 2)
  have hμ0 : μ ≠ 0 := fun h0 => by
    rw [h0, zero_pow two_ne_zero] at hμ
    exact mul_ne_zero ha₀0 (pow_ne_zero 2 hb₀0) hμ.symm
  set Su : GL (Fin 4) Ω := Matrix.GeneralLinearGroup.scalar (Fin 4) (Units.mk0 μ⁻¹
    (inv_ne_zero hμ0)) with hSu
  have hSu_comm : ∀ X : GL (Fin 4) Ω, Su * X = X * Su := fun X => by
    apply Units.ext
    simp only [Units.val_mul, hSu, Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0]
    rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul,
      Matrix.mul_smul, Matrix.mul_one]
  set Rv : GL (Fin 4) Ω := ((f4B2Rep Ω ⟨v, hvQ⟩ : matrixIsometryGroup (f4J0 Ω)) :
    GL (Fin 4) Ω) with hRv
  set B : GL (Fin 4) Ω := Rv * Su * Du with hB
  have hBval : (B : Matrix (Fin 4) (Fin 4) Ω) = (Rv : Matrix (Fin 4) (Fin 4) Ω) * (μ⁻¹ • D) := by
    have hSD : ((Su * Du : GL (Fin 4) Ω) : Matrix (Fin 4) (Fin 4) Ω) = μ⁻¹ • D := by
      simp only [Units.val_mul, hSu, hDu, Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0]
      rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul]
      rfl
    rw [hB, mul_assoc, Units.val_mul, hSD]
  have hBsp : B ∈ matrixIsometryGroup (f4J0 Ω) := by
    have hRvsp : Rv ∈ matrixIsometryGroup (f4J0 Ω) := (f4B2Rep Ω ⟨v, hvQ⟩).2
    rw [mem_matrixIsometryGroup] at hRvsp ⊢
    have hμ2 : μ⁻¹ * μ⁻¹ * (a₀ * b₀ ^ 2) = 1 := by
      rw [← hμ]
      field_simp
    rw [hBval, Matrix.transpose_mul, Matrix.transpose_smul]
    calc (μ⁻¹ • Dᵀ) * (Rv : Matrix (Fin 4) (Fin 4) Ω)ᵀ * f4J0 Ω *
          ((Rv : Matrix (Fin 4) (Fin 4) Ω) * (μ⁻¹ • D)) =
        (μ⁻¹ • Dᵀ) * ((Rv : Matrix (Fin 4) (Fin 4) Ω)ᵀ * f4J0 Ω *
          (Rv : Matrix (Fin 4) (Fin 4) Ω)) * (μ⁻¹ • D) := by simp only [Matrix.mul_assoc]
      _ = (μ⁻¹ * μ⁻¹) • (Dᵀ * f4J0 Ω * D) := by
          rw [hRvsp, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      _ = f4J0 Ω := by rw [hsim, smul_smul, hμ2, one_smul]
  have hθQ : ∀ z ∈ Q, twistedEntrywise m F z ∈ Q := fun z hz => by
    rw [hθ z hz]
    exact mul_mem (mul_mem hvQ (hN _ (hFQ z hz))) (inv_mem hvQ)
  have hrθ : ∀ z : Q, (f4B2Rep Ω ⟨twistedEntrywise m F z, hθQ z z.2⟩ : GL (Fin 4) Ω) =
      B * Matrix.GeneralLinearGroup.map F (f4B2Rep Ω z : GL (Fin 4) Ω) * B⁻¹ := fun z => by
    obtain ⟨hσ, hFz⟩ := hrbc Ω F z
    have hzσ : Units.map (entrywiseHom F) (z : ModGL .F4 Ω) = baseChangeGL F (z : ModGL .F4 Ω) :=
      units_map_entrywiseHom_eq_baseChangeGL_self F _
    have e1 : (⟨twistedEntrywise m F z, hθQ z z.2⟩ : Q) =
        ⟨v, hvQ⟩ * ⟨h₀ * baseChangeGL F (z : ModGL .F4 Ω) * h₀⁻¹, hN _ hσ⟩ *
          ⟨v, hvQ⟩⁻¹ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hθ z z.2, hzσ]
    have e2 : ((f4B2Rep Ω ⟨h₀ * baseChangeGL F (z : ModGL .F4 Ω) * h₀⁻¹, hN _ hσ⟩ :
        matrixIsometryGroup (f4J0 Ω)) : GL (Fin 4) Ω) =
        Du * Matrix.GeneralLinearGroup.map F (f4B2Rep Ω z : GL (Fin 4) Ω) * Du⁻¹ := by
      apply Units.ext
      have h := hD ⟨baseChangeGL F (z : ModGL .F4 Ω), hσ⟩
      rw [hFz] at h
      rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv]
      exact h
    rw [e1, map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, e2]
    change Rv * (Du * Matrix.GeneralLinearGroup.map F (f4B2Rep Ω z : GL (Fin 4) Ω) * Du⁻¹) *
      Rv⁻¹ = B * Matrix.GeneralLinearGroup.map F (f4B2Rep Ω z : GL (Fin 4) Ω) * B⁻¹
    rw [hB]
    calc Rv * (Du * Matrix.GeneralLinearGroup.map F (f4B2Rep Ω z : GL (Fin 4) Ω) * Du⁻¹) *
          Rv⁻¹ = Rv * (Su * (Du * Matrix.GeneralLinearGroup.map F (f4B2Rep Ω z :
            GL (Fin 4) Ω) * Du⁻¹) * Su⁻¹) * Rv⁻¹ := by
          rw [hSu_comm, mul_inv_cancel_right]
      _ = Rv * Su * Du * Matrix.GeneralLinearGroup.map F (f4B2Rep Ω z : GL (Fin 4) Ω) *
          (Rv * Su * Du)⁻¹ := by group
  obtain ⟨P, hP, hset⟩ := f4Sp_frobenius_lang K B hBsp
  obtain ⟨a', ha'⟩ := hrbij.2 ⟨P, hP⟩
  have hFmap : ∀ X : GL (Fin 4) Ω, (X : Matrix (Fin 4) (Fin 4) Ω).map (· ^ Nat.card K) =
      (Matrix.GeneralLinearGroup.map F X : GL (Fin 4) Ω) := fun X => by
    ext i j
    simp [hF]
  have himg : ∀ g : subsystemGroup .F4 K {1, 2},
      ∃ hg : baseChangeGL (algebraMap K Ω) (g : ModGL .F4 K) ∈ Q,
        (f4B2Rep Ω ⟨_, hg⟩ : GL (Fin 4) Ω) =
          Matrix.GeneralLinearGroup.map (algebraMap K Ω) (f4B2Rep K g : GL (Fin 4) K) := by
    intro g
    obtain ⟨hg, h⟩ := hrbcK Ω (algebraMap K Ω) g
    exact ⟨hg, Units.ext h⟩
  refine ⟨a', a'.2, ?_⟩
  ext z
  constructor
  · rintro ⟨hzQ, hzθ⟩
    have hzθ' : twistedEntrywise m F z = z := hzθ
    have hfix : (f4B2Rep Ω ⟨z, hzQ⟩ : GL (Fin 4) Ω) ∈
        {X : GL (Fin 4) Ω | X ∈ matrixIsometryGroup (f4J0 Ω) ∧
          (B : Matrix (Fin 4) (Fin 4) Ω) * (X : Matrix (Fin 4) (Fin 4) Ω).map (· ^ Nat.card K) *
            (↑B⁻¹ : Matrix (Fin 4) (Fin 4) Ω) = X} := by
      refine ⟨(f4B2Rep Ω ⟨z, hzQ⟩).2, ?_⟩
      have e : (⟨twistedEntrywise m F z, hθQ z hzQ⟩ : Q) = ⟨z, hzQ⟩ := Subtype.ext hzθ'
      rw [hFmap, ← Units.val_mul, ← Units.val_mul, ← hrθ ⟨z, hzQ⟩]
      change (((f4B2Rep Ω ⟨twistedEntrywise m F z, hθQ z hzQ⟩ : matrixIsometryGroup (f4J0 Ω)) :
        GL (Fin 4) Ω) : Matrix (Fin 4) (Fin 4) Ω) = _
      rw [e]
    rw [hset] at hfix
    obtain ⟨Y, hY, hYz⟩ := hfix
    obtain ⟨g, hg⟩ := hrbijK.2 ⟨Y, hY⟩
    obtain ⟨hgQ, hgr⟩ := himg g
    refine ⟨baseChangeGL (algebraMap K Ω) (g : ModGL .F4 K), ⟨g, g.2, rfl⟩, ?_⟩
    have hinj := hrbij.1
    have h1 : f4B2Rep Ω (⟨a', a'.2⟩ * ⟨_, hgQ⟩ * ⟨a', a'.2⟩⁻¹) = f4B2Rep Ω ⟨z, hzQ⟩ := by
      apply Subtype.ext
      rw [map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hgr,
        ← hYz, hg]
      congr 2
      · rw [show (⟨a', a'.2⟩ : Q) = a' from rfl, ha']
      · rw [show (⟨a', a'.2⟩ : Q) = a' from rfl, ha']
    have h2 := congrArg Subtype.val (hinj h1)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact h2
  · rintro ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    obtain ⟨hgQ, hgr⟩ := himg ⟨g, hg⟩
    have hzQ : (a' : ModGL .F4 Ω) * baseChangeGL (algebraMap K Ω) g * (a' : ModGL .F4 Ω)⁻¹ ∈
        Q := mul_mem (mul_mem a'.2 hgQ) (inv_mem a'.2)
    refine ⟨hzQ, ?_⟩
    change twistedEntrywise m F _ = _
    have hmem : (f4B2Rep Ω ⟨_, hzQ⟩ : GL (Fin 4) Ω) ∈
        (fun Y => P * Matrix.GeneralLinearGroup.map (algebraMap K Ω) Y * P⁻¹) ''
          (matrixIsometryGroup (f4J0 K) : Set (GL (Fin 4) K)) := by
      refine ⟨f4B2Rep K ⟨g, hg⟩, (f4B2Rep K ⟨g, hg⟩).2, ?_⟩
      have e : (⟨_, hzQ⟩ : Q) = a' * ⟨_, hgQ⟩ * a'⁻¹ := rfl
      rw [e, map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
        hgr, ha']
    rw [← hset] at hmem
    obtain ⟨-, hfx⟩ := hmem
    rw [hFmap, ← Units.val_mul, ← Units.val_mul, ← hrθ ⟨_, hzQ⟩] at hfx
    have h1 := hrbij.1 (Subtype.ext (Units.ext hfx))
    exact congrArg Subtype.val h1

section Centralizer

variable {L : Type} [Field L]

theorem subsystemGroup_le_adjointGroup_F4
    (J : Set (Fin Tag.F4.rank)) :
    subsystemGroup .F4 L J ≤ adjointGroup .F4 L := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨i, -, c, rfl | rfl⟩
  exacts [xUnit_mem_adjointGroup i c, yUnit_mem_adjointGroup i c]

theorem subsystemGroup_le_centralizer_of_torusRootChar
    {z : ModGL .F4 L}
    (hz : z ∈ torusGroup .F4 L) (h1 : torusRootChar z (Pi.single 1 1) = 1)
    (h2 : torusRootChar z (Pi.single 2 1) = 1) :
    subsystemGroup .F4 L {1, 2} ≤ Subgroup.centralizer {z} := by
  obtain ⟨c, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hz
  have hneg : ∀ j, torusRootChar (rootDiagUnit .F4 c) (Pi.single j 1) = 1 →
      torusRootChar (rootDiagUnit .F4 c) (-Pi.single j 1) = 1 := fun j hj => by
    rw [torusRootChar_rootDiagUnit c (isRoot_single .F4 j)] at hj
    rw [torusRootChar_rootDiagUnit c (IsRoot.neg (isRoot_single .F4 j)), rootChar_neg',
      Units.val_inv_eq_inv_val, hj, inv_one]
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨j, hj, a, rfl | rfl⟩
  · have hχ : torusRootChar (rootDiagUnit .F4 c) (Pi.single j 1) = 1 := by
      rcases hj with rfl | rfl
      exacts [h1, h2]
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff, ← pinnedX_single]
    exact ((commute_pinnedX_iff hz (isRoot_single .F4 j)).2 hχ a).symm
  · have hχ : torusRootChar (rootDiagUnit .F4 c) (Pi.single j 1) = 1 := by
      rcases hj with rfl | rfl
      exacts [h1, h2]
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff, ← pinnedX_neg_single]
    exact ((commute_pinnedX_iff hz (IsRoot.neg (isRoot_single .F4 j))).2 (hneg j hχ) a).symm

theorem mem_torusGroup_of_commute_simple_gens
    {h₀ v₀ : ModGL .F4 L}
    (hh₀ : h₀ ∈ torusGroup .F4 L) (hv₀ : v₀ ∈ subsystemGroup .F4 L {1, 2})
    (hc : ∀ i ∈ ({1, 2} : Set (Fin Tag.F4.rank)),
      h₀ * v₀ * xUnit .F4 L i 1 = xUnit .F4 L i 1 * (h₀ * v₀) ∧
        h₀ * v₀ * yUnit .F4 L i 1 = yUnit .F4 L i 1 * (h₀ * v₀)) :
    h₀ * v₀ ∈ torusGroup .F4 L ∧ torusRootChar (h₀ * v₀) (Pi.single 1 1) = 1 ∧
      torusRootChar (h₀ * v₀) (Pi.single 2 1) = 1 := by
  classical
  obtain ⟨-, -, hrbij, hgen, -, hdiag, -, -, -, hrconj, -⟩ :=
    F4_native_B2_faithful_Sp4_all_characteristics L
  set a := torusRootChar h₀ (Pi.single 1 1) with ha
  set b := torusRootChar h₀ (Pi.single 2 1) with hb
  have ha0 : a ≠ 0 := torusRootChar_ne_zero (torusGroup_le_diagonalGroup hh₀) _
  have hb0 : b ≠ 0 := torusRootChar_ne_zero (torusGroup_le_diagonalGroup hh₀) _
  obtain ⟨⟨hN, hD⟩, -⟩ := hrconj h₀ hh₀ a b
    (apply_rootVec_of_mem_torusGroup hh₀ (isRoot_single .F4 1))
    (apply_rootVec_of_mem_torusGroup hh₀ (isRoot_single .F4 2))
  set D : Matrix (Fin 4) (Fin 4) L := diagonal ![a * b ^ 2, a * b, b, 1] with hDdef
  have hDdet : IsUnit D.det := by
    rw [hDdef, Matrix.det_diagonal, Fin.prod_univ_four]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, mul_one]
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero ha0 (pow_ne_zero 2 hb0)) (mul_ne_zero ha0 hb0))
      hb0).isUnit
  set r := f4B2Rep L with hr
  set Mv : Matrix (Fin 4) (Fin 4) L :=
    (((r ⟨v₀, hv₀⟩ : matrixIsometryGroup (f4J0 L)) : GL (Fin 4) L) : Matrix (Fin 4) (Fin 4) L)
    with hMv
  have hDdet' : D.det ≠ 0 := hDdet.ne_zero
  set Dg : GL (Fin 4) L := Matrix.GeneralLinearGroup.mkOfDetNeZero D hDdet' with hDg
  have hDgv : (Dg : Matrix (Fin 4) (Fin 4) L) = D := rfl
  have hconjD : ∀ z : subsystemGroup .F4 L {1, 2},
      ((r ⟨h₀ * z * h₀⁻¹, hN z z.2⟩ : matrixIsometryGroup (f4J0 L)) : GL (Fin 4) L) =
        Dg * (r z : GL (Fin 4) L) * Dg⁻¹ := fun z => by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv, hDgv]
    exact hD z
  set Rv : GL (Fin 4) L := ((r ⟨v₀, hv₀⟩ : matrixIsometryGroup (f4J0 L)) : GL (Fin 4) L)
    with hRv
  have hcomm : ∀ q : subsystemGroup .F4 L {1, 2}, h₀ * v₀ * q = q * (h₀ * v₀) →
      (Dg * Rv) * (r q : GL (Fin 4) L) = (r q : GL (Fin 4) L) * (Dg * Rv) := by
    intro q hq
    have hvq : v₀ * q * v₀⁻¹ ∈ subsystemGroup .F4 L {1, 2} :=
      mul_mem (mul_mem hv₀ q.2) (inv_mem hv₀)
    have e : (⟨h₀ * (v₀ * q * v₀⁻¹) * h₀⁻¹, hN _ hvq⟩ : subsystemGroup .F4 L {1, 2}) = q := by
      apply Subtype.ext
      change h₀ * (v₀ * (q : ModGL .F4 L) * v₀⁻¹) * h₀⁻¹ = q
      calc h₀ * (v₀ * (q : ModGL .F4 L) * v₀⁻¹) * h₀⁻¹ =
            h₀ * v₀ * q * (h₀ * v₀)⁻¹ := by group
        _ = q * (h₀ * v₀) * (h₀ * v₀)⁻¹ := by rw [hq]
        _ = q := by group
    have e2 : (⟨v₀ * q * v₀⁻¹, hvq⟩ : subsystemGroup .F4 L {1, 2}) =
        ⟨v₀, hv₀⟩ * q * ⟨v₀, hv₀⟩⁻¹ := rfl
    have h1 : (r q : GL (Fin 4) L) = Dg * (Rv * (r q : GL (Fin 4) L) * Rv⁻¹) * Dg⁻¹ := by
      calc (r q : GL (Fin 4) L) =
            ((r ⟨h₀ * (v₀ * q * v₀⁻¹) * h₀⁻¹, hN _ hvq⟩ : matrixIsometryGroup (f4J0 L)) :
              GL (Fin 4) L) := by rw [e]
        _ = Dg * ((r ⟨v₀ * q * v₀⁻¹, hvq⟩ : matrixIsometryGroup (f4J0 L)) : GL (Fin 4) L) *
              Dg⁻¹ := hconjD ⟨v₀ * q * v₀⁻¹, hvq⟩
        _ = Dg * (Rv * (r q : GL (Fin 4) L) * Rv⁻¹) * Dg⁻¹ := by
            rw [e2, map_mul, map_mul, map_inv]
            rfl
    calc Dg * Rv * (r q : GL (Fin 4) L) =
          (Dg * (Rv * (r q : GL (Fin 4) L) * Rv⁻¹) * Dg⁻¹) * (Dg * Rv) := by group
      _ = (r q : GL (Fin 4) L) * (Dg * Rv) := by rw [← h1]
  obtain ⟨hx1, hy1, hx2, hy2⟩ := hgen 1
  have hmat : ∀ q : subsystemGroup .F4 L {1, 2}, h₀ * v₀ * q = q * (h₀ * v₀) →
      ((Dg * Rv : GL (Fin 4) L) : Matrix (Fin 4) (Fin 4) L) *
          (((r q : matrixIsometryGroup (f4J0 L)) : GL (Fin 4) L) : Matrix (Fin 4) (Fin 4) L) =
        (((r q : matrixIsometryGroup (f4J0 L)) : GL (Fin 4) L) : Matrix (Fin 4) (Fin 4) L) *
          ((Dg * Rv : GL (Fin 4) L) : Matrix (Fin 4) (Fin 4) L) := fun q hq => by
    rw [← Units.val_mul, ← Units.val_mul, hcomm q hq]
  have hq1 := hmat (qx (left_mem_pair 1 2) 1) (by rw [coe_qx]; exact (hc 1 (Or.inl rfl)).1)
  have hq2 := hmat (qy (left_mem_pair 1 2) 1) (by rw [coe_qy]; exact (hc 1 (Or.inl rfl)).2)
  have hq3 := hmat (qx (right_mem_pair 1 2) 1) (by rw [coe_qx]; exact (hc 2 (Or.inr rfl)).1)
  have hq4 := hmat (qy (right_mem_pair 1 2) 1) (by rw [coe_qy]; exact (hc 2 (Or.inr rfl)).2)
  rw [hx1] at hq1
  rw [hy1] at hq2
  rw [hx2] at hq3
  rw [hy2] at hq4
  have hscal := eq_smul_one_of_commute_f4B2_gens hq1 hq2 hq3 hq4
  obtain ⟨d, hd⟩ : ∃ d : Fin 4 → L, (Rv : Matrix (Fin 4) (Fin 4) L) = diagonal d := by
    obtain ⟨μ, hμ⟩ : ∃ μ : L, μ = ((Dg * Rv : GL (Fin 4) L) : Matrix (Fin 4) (Fin 4) L) 0 0 :=
      ⟨_, rfl⟩
    rw [← hμ] at hscal
    refine ⟨μ • (D⁻¹).diag, ?_⟩
    have h2 : (Rv : Matrix (Fin 4) (Fin 4) L) =
        (↑Dg⁻¹ : Matrix (Fin 4) (Fin 4) L) * ((Dg * Rv : GL (Fin 4) L) :
          Matrix (Fin 4) (Fin 4) L) := by
      rw [← Units.val_mul, inv_mul_cancel_left]
    rw [h2, hscal, Matrix.mul_smul, Matrix.mul_one, Matrix.coe_units_inv, hDgv, hDdef,
      Matrix.inv_diagonal, Matrix.diag_diagonal, Matrix.diagonal_smul]
  obtain ⟨t, u, htu⟩ := hdiag Rv (r ⟨v₀, hv₀⟩).2 d hd
  have hv₀H : v₀ ∈ torusGroup .F4 L := by
    have h3 := hrbij.1 (Subtype.ext (Units.ext htu) :
      r ⟨torusElt Tag.F4 L 1 t * torusElt Tag.F4 L 2 u, torusElt_pair_mem 1 2 t u⟩ =
        r ⟨v₀, hv₀⟩)
    have h4 := congrArg Subtype.val h3
    simp only at h4
    rw [← h4]
    exact mul_mem (torusElt_mem_torusGroup 1 t) (torusElt_mem_torusGroup 2 u)
  have hz : h₀ * v₀ ∈ torusGroup .F4 L := mul_mem hh₀ hv₀H
  have hχ : ∀ i ∈ ({1, 2} : Set (Fin Tag.F4.rank)), torusRootChar (h₀ * v₀) (Pi.single i 1) = 1 :=
    fun i hi => by
      have e := conj_pinnedX_of_mem_torusGroup hz (isRoot_single .F4 i) 1
      rw [pinnedX_single, (hc i hi).1, mul_inv_cancel_right, ← pinnedX_single] at e
      have e' := pinnedX_injective .F4 L _ e
      rw [mul_one] at e'
      exact e'.symm
  exact ⟨hz, hχ 1 (Or.inl rfl), hχ 2 (Or.inr rfl)⟩

theorem torusGroup_le_normalizer_subsystemGroup_F4 :
    torusGroup .F4 L ≤ Subgroup.normalizer (subsystemGroup .F4 L {1, 2} : Set (ModGL .F4 L)) := by
  rw [subsystemGroup_eq_rootSpan]
  exact torusGroup_le_normalizer_rootSpan fun _ hα => hα.1

theorem mem_centralizer_conj_subsystemGroup_iff
    {K : Type} [Field K] (f : K →+* L)
    {a : ModGL .F4 L} (ha : a ∈ subsystemGroup .F4 L {1, 2}) {z : ModGL .F4 L}
    (hz : z ∈ torusGroup .F4 L ⊔ subsystemGroup .F4 L {1, 2}) :
    z ∈ Subgroup.centralizer ((((subsystemGroup .F4 K {1, 2}).map (baseChangeGL f)).map
        (MulAut.conj a).toMonoidHom : Subgroup (ModGL .F4 L)) : Set (ModGL .F4 L)) ↔
      z ∈ torusGroup .F4 L ∧ torusRootChar z (Pi.single 1 1) = 1 ∧
        torusRootChar z (Pi.single 2 1) = 1 := by
  have hN := torusGroup_le_normalizer_subsystemGroup_F4 (L := L)
  have hU : (((subsystemGroup .F4 K {1, 2}).map (baseChangeGL f)).map
      (MulAut.conj a).toMonoidHom : Subgroup (ModGL .F4 L)) ≤ subsystemGroup .F4 L {1, 2} := by
    rintro _ ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    exact mul_mem (mul_mem ha (baseChangeGL_mem_subsystemGroup f hg)) (inv_mem ha)
  constructor
  · intro hzc
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hN] at hz
    obtain ⟨h₀, hh₀, v₀, hv₀, rfl⟩ := hz
    beta_reduce at hzc ⊢
    have hv₀' : h₀⁻¹ * a⁻¹ * h₀ * v₀ * a ∈ subsystemGroup .F4 L {1, 2} := by
      have h1 : h₀⁻¹ * a⁻¹ * h₀ ∈ subsystemGroup .F4 L {1, 2} := by
        have := (Subgroup.mem_normalizer_iff.1 (hN (inv_mem hh₀)) a⁻¹).1 (inv_mem ha)
        simpa only [inv_inv] using this
      exact mul_mem (mul_mem h1 hv₀) ha
    have hcz : ∀ x ∈ subsystemGroup .F4 K {1, 2}, a⁻¹ * (h₀ * v₀) * a * baseChangeGL f x =
        baseChangeGL f x * (a⁻¹ * (h₀ * v₀) * a) := fun x hx => by
      have h1 := Subgroup.mem_centralizer_iff.1 hzc (a * baseChangeGL f x * a⁻¹)
        ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      calc a⁻¹ * (h₀ * v₀) * a * baseChangeGL f x =
            a⁻¹ * ((h₀ * v₀) * (a * baseChangeGL f x * a⁻¹)) * a := by group
        _ = a⁻¹ * ((a * baseChangeGL f x * a⁻¹) * (h₀ * v₀)) * a := by rw [h1]
        _ = baseChangeGL f x * (a⁻¹ * (h₀ * v₀) * a) := by group
    have he : a⁻¹ * (h₀ * v₀) * a = h₀ * (h₀⁻¹ * a⁻¹ * h₀ * v₀ * a) := by group
    obtain ⟨hzH, h1, h2⟩ := mem_torusGroup_of_commute_simple_gens hh₀ hv₀' fun i hi => by
      rw [← he]
      have hx := hcz _ (xUnit_mem_subsystemGroup hi 1)
      have hy := hcz _ (yUnit_mem_subsystemGroup hi 1)
      rw [baseChangeGL_xUnit, map_one] at hx
      rw [baseChangeGL_yUnit, map_one] at hy
      exact ⟨hx, hy⟩
    rw [← he] at hzH h1 h2
    have hca : a * (a⁻¹ * (h₀ * v₀) * a) = (a⁻¹ * (h₀ * v₀) * a) * a :=
      Subgroup.mem_centralizer_singleton_iff.1
        (subsystemGroup_le_centralizer_of_torusRootChar hzH h1 h2 ha)
    have hzz : h₀ * v₀ = a⁻¹ * (h₀ * v₀) * a := by
      calc h₀ * v₀ = a * (a⁻¹ * (h₀ * v₀) * a) * a⁻¹ := by group
        _ = a⁻¹ * (h₀ * v₀) * a := by rw [hca, mul_inv_cancel_right]
    rw [hzz]
    exact ⟨hzH, h1, h2⟩
  · rintro ⟨hzH, h1, h2⟩
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.1
      (subsystemGroup_le_centralizer_of_torusRootChar hzH h1 h2 (hU hx))

end Centralizer

end CFSG.RankThree.Chevalley
