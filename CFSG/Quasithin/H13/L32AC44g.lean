module

public import CFSG.Quasithin.H13.L32AC44e

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Assembly.LowTwoRank Matrix CFSG.QuasithinUnique.Setup.X7a CFSG.Quasithin
  CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups Pointwise

namespace SL3N

variable {F : Type} [Field F] [CharP F 2]

@[expose] noncomputable def chi (F : Type) [Field F] [CharP F 2] : ↥(borel F) →* Fˣ × Fˣ where
  toFun g := (Units.mk0 _ (diag00_ne_zero (e10 g.2) (e20 g.2) (e21 g.2)),
    Units.mk0 _ (diag22_ne_zero (e10 g.2) (e20 g.2) (e21 g.2)))
  map_one' := by
    ext
    · exact Matrix.one_apply_eq 0
    · exact Matrix.one_apply_eq 2
  map_mul' g h := by
    ext
    · exact mul00 h.2
    · exact mul22 g.2

@[expose] noncomputable def diagSL (a c : Fˣ) : SL(3, F) :=
  ⟨!![(a : F), 0, 0; 0, (((a * c)⁻¹ : Fˣ) : F), 0; 0, 0, (c : F)], by
    have ha := a.ne_zero
    have hc := c.ne_zero
    simp [Matrix.det_fin_three]
    field_simp⟩

theorem diagSL_mem_borel [Finite F] (a c : Fˣ) : diagSL a c ∈ borel F := by
  refine Subgroup.mem_normalizer_fintype fun u hu => ?_
  obtain ⟨x, y, z, rfl⟩ := mem_upperUni.mp hu
  have ha : (a : F) ≠ 0 := a.ne_zero
  have hc : (c : F) ≠ 0 := c.ne_zero
  have key : diagSL a c * up3 x y z =
      up3 (x * ((a : F) * c)⁻¹ * (c : F)⁻¹) (y * a * (c : F)⁻¹) (z * a * (a * c)) *
        diagSL a c := by
    apply Subtype.ext
    show ((diagSL a c : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *
        (up3 x y z : Matrix (Fin 3) (Fin 3) F) =
      (up3 (x * ((a : F) * c)⁻¹ * (c : F)⁻¹) (y * a * (c : F)⁻¹) (z * a * (a * c)) :
        Matrix (Fin 3) (Fin 3) F) * (diagSL a c : Matrix (Fin 3) (Fin 3) F)
    rw [up3_coe, up3_coe]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [diagSL, upMat, Matrix.mul_apply, Fin.sum_univ_three] <;> field_simp
  rw [key, mul_inv_cancel_right]
  exact mem_upperUni.mpr ⟨_, _, _, rfl⟩

theorem chi_surjective [Finite F] : Function.Surjective (chi F) := by
  rintro ⟨a, c⟩
  refine ⟨⟨diagSL a c, diagSL_mem_borel a c⟩, ?_⟩
  ext
  · rfl
  · rfl

theorem ker_chi : (chi F).ker = (upperUni F).subgroupOf (borel F) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro h
    have h0 := congrArg (fun p : Fˣ × Fˣ => (p.1 : F)) h
    have h2 := congrArg (fun p : Fˣ × Fˣ => (p.2 : F)) h
    exact mem_upperUni_of g.2 h0 h2
  · intro h
    ext
    · exact upperUni_00 h
    · exact upperUni_22 h

theorem relIndex_upperUni_borel [Finite F] :
    (upperUni F).relIndex (borel F) = Nat.card Fˣ * Nat.card Fˣ := by
  rw [Subgroup.relIndex, ← ker_chi, Subgroup.index_ker, MonoidHom.range_eq_top.mpr chi_surjective,
    Subgroup.card_top, Nat.card_prod]

end SL3N

theorem relIndex_normalizer_eq_nine {N : Type} [CommGroup N] [Finite N]
    {X : Subgroup (MulAut N)} {U : Subgroup N} (hX : BinaryNaturalSL X U ⊥ 3 2)
    {S : Subgroup (MulAut N)} (hS : IsSylowTwoOf S X) :
    S.relIndex (X ⊓ Subgroup.normalizer (S : Set (MulAut N))) = 9 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨F, _, _, hF, π, hπ⟩ := hX
  have : Fintype F := Fintype.ofFinite F
  have hF' : Fintype.card F = 2 ^ 2 := by rw [Fintype.card_eq_nat_card, hF]
  have : CharP F 2 :=
    finite_field_prime_power_characteristic Nat.prime_two (by norm_num : 1 ≤ 2) hF
  have hinj := G64.RealizesVia.injective_of_faithful' (FFModel.nat_faithful _) hπ
  let Φ : SL(3, F) ≃* ↥X :=
    (specialLinearGroupEquivStatedSL 3 F).trans (MulEquiv.ofBijective π ⟨hinj, hπ.1⟩)
  set S' : Subgroup SL(3, F) := (S.subgroupOf X).comap Φ.toMonoidHom with hS'
  have hS'2 : IsPGroup 2 ↥S' := by
    have h1 : IsPGroup 2 ↥(S.subgroupOf X) :=
      hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
    exact h1.comap_of_injective Φ.toMonoidHom Φ.injective
  have hS'i : ¬ 2 ∣ S'.index := by
    rw [hS', Subgroup.index_comap_of_surjective _ Φ.surjective]
    exact hS.2.2
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq SL(3, F)
    ((isPGroup_upperUni hF).toSylow (SL3N.not_two_dvd_index_upperUni hF'))
    (hS'2.toSylow hS'i)
  have hgS : ∀ γ : SL(3, F), γ ∈ S' ↔ g⁻¹ * γ * g ∈ upperUni F := by
    intro γ
    have h1 : S' = MulAut.conj g • upperUni F := by
      have := congrArg (fun P : Sylow 2 SL(3, F) => (P : Subgroup SL(3, F))) hg
      simp only [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe] at this
      exact this.symm
    rw [h1, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, MulAut.smul_def,
      MulAut.conj_apply, inv_inv]
  let Ψ : SL(3, F) ≃* ↥X := (MulAut.conj g).trans Φ
  have hΨ : ∀ u, Ψ u = Φ (g * u * g⁻¹) := fun u => rfl
  have hΨU : (upperUni F).map Ψ.toMonoidHom = S.subgroupOf X := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      show Ψ u ∈ S.subgroupOf X
      rw [hΨ]
      have : g * u * g⁻¹ ∈ S' := by
        rw [hgS]
        have e : g⁻¹ * (g * u * g⁻¹) * g = u := by group
        rw [e]
        exact hu
      exact this
    · intro hx
      refine ⟨g⁻¹ * Φ.symm x * g, (hgS _).mp ?_, ?_⟩
      · show Φ (Φ.symm x) ∈ S.subgroupOf X
        rw [MulEquiv.apply_symm_apply]
        exact hx
      · show Ψ (g⁻¹ * Φ.symm x * g) = x
        rw [hΨ]
        have e : g * (g⁻¹ * Φ.symm x * g) * g⁻¹ = Φ.symm x := by group
        rw [e, MulEquiv.apply_symm_apply]
  have hΨN : (SL3N.borel F).map Ψ.toMonoidHom =
      (X ⊓ Subgroup.normalizer (S : Set (MulAut N))).subgroupOf X := by
    have hnorm : Subgroup.normalizer ((S.subgroupOf X : Subgroup ↥X) : Set ↥X) =
        (X ⊓ Subgroup.normalizer (S : Set (MulAut N))).subgroupOf X := by
      ext x
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_normalizer_iff, Subgroup.mem_inf,
        Subgroup.mem_normalizer_iff]
      constructor
      · intro h
        refine ⟨x.2, fun z => ⟨fun hz => (h ⟨z, hS.1 hz⟩).mp hz, fun hz => ?_⟩⟩
        have hzX : z ∈ X := by
          have h1 : (x : MulAut N) * z * (x : MulAut N)⁻¹ ∈ X := hS.1 hz
          have e : z = (x : MulAut N)⁻¹ * ((x : MulAut N) * z * (x : MulAut N)⁻¹) * x := by
            group
          rw [e]
          exact X.mul_mem (X.mul_mem (X.inv_mem x.2) h1) x.2
        exact (h ⟨z, hzX⟩).mpr hz
      · rintro ⟨-, h⟩ z
        exact h z
    rw [← hnorm, ← hΨU]
    exact Subgroup.map_equiv_normalizer_eq _ Ψ
  rw [← Subgroup.relIndex_subgroupOf (inf_le_left : X ⊓ _ ≤ X), ← hΨU, ← hΨN,
    Subgroup.relIndex_map_map_of_injective _ _ Ψ.injective, SL3N.relIndex_upperUni_borel,
    Nat.card_eq_fintype_card (α := Fˣ), Fintype.card_units, hF']
  norm_num

theorem card_mulAut_le_six {Y : Type} [Group Y] [Finite Y] (hY : Nat.card Y = 4) :
    Nat.card (MulAut Y) ≤ 6 := by
  classical
  have : Fintype Y := Fintype.ofFinite Y
  let φ : MulAut Y → Equiv.Perm {y : Y // y ≠ 1} := fun σ =>
    { toFun := fun y => ⟨σ y, fun h => y.2 (σ.injective (h.trans (map_one σ).symm))⟩
      invFun := fun y => ⟨σ.symm y, fun h => y.2 (σ.symm.injective (h.trans
        (map_one σ.symm).symm))⟩
      left_inv := fun y => Subtype.ext (σ.symm_apply_apply y)
      right_inv := fun y => Subtype.ext (σ.apply_symm_apply y) }
  have hφ : Function.Injective φ := by
    intro σ τ h
    refine MulEquiv.ext fun y => ?_
    by_cases hy : y = 1
    · rw [hy, map_one, map_one]
    · exact congrArg Subtype.val (Equiv.congr_fun h ⟨y, hy⟩)
  have h1 := Nat.card_le_card_of_injective φ hφ
  have h3 : Nat.card {y : Y // y ≠ 1} = 3 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq,
      ← Nat.card_eq_fintype_card, hY]
  calc Nat.card (MulAut Y) ≤ Nat.card (Equiv.Perm {y : Y // y ≠ 1}) := h1
    _ = 6 := by
      rw [Nat.card_perm, h3]
      rfl

end CFSG.Quasithin.H13.L32A.C
