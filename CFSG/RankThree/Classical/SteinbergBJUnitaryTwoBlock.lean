module

public import CFSG.RankThree.CentralLiftU.UnitaryThreeLift
public import CFSG.LieType.Steinberg.CentralExt.UnitaryThreeSylow
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple

public section

namespace CFSG.RankThree.Classical

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LieType.Steinberg CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

theorem isQuasisimple_SL2 {F : Type*} [Field F] (h4 : ∃ s : Finset F, s.card = 4) :
    CFSG.IsQuasisimple (SpecialLinearGroup (Fin 2) F) := by
  have hperf := CFSG.LinearGroups.special_linear_isPerfect (K := F) (n := 2) le_rfl (Or.inr h4)
  obtain ⟨-, hsimple, -⟩ := CFSG.LinearGroups.linear_projective_simple (K := F) (n := 2) le_rfl
    (Or.inr h4)
  refine ⟨hperf, hsimple, ?_⟩
  by_contra hab
  push Not at hab
  have hle : commutator (SpecialLinearGroup (Fin 2) F) ≤
      Subgroup.center (SpecialLinearGroup (Fin 2) F) := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [← QuotientGroup.eq_one_iff]
    change (QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin 2) F))) ⁅x, y⁆ = 1
    rw [map_commutatorElement, commutatorElement_def, hab (QuotientGroup.mk' _ x),
      mul_inv_cancel_right, mul_inv_cancel]
  rw [Group.isPerfect_def.mp hperf] at hle
  obtain ⟨a, b, hne⟩ := exists_pair_ne
    (SpecialLinearGroup (Fin 2) F ⧸ Subgroup.center (SpecialLinearGroup (Fin 2) F))
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  exact hne (QuotientGroup.eq.mpr (hle (Subgroup.mem_top _)))

theorem card_center_SL2 {F : Type*} [Field F] :
    Nat.card (Subgroup.center (SpecialLinearGroup (Fin 2) F)) = Nat.card {r : F // r ^ 2 = 1} := by
  classical
  refine (Nat.card_congr (Equiv.ofBijective
    (fun r : {r : F // r ^ 2 = 1} => (⟨⟨scalar (Fin 2) (r.1 : F), by
        rw [scalar_apply, det_diagonal, Fin.prod_univ_two, ← sq, r.2]⟩,
      Matrix.SpecialLinearGroup.mem_center_iff.mpr ⟨r.1, by rw [Fintype.card_fin, r.2], rfl⟩⟩ :
        Subgroup.center (SpecialLinearGroup (Fin 2) F))) ⟨?_, ?_⟩)).symm
  · intro r s hrs
    have := congrArg (fun A : Subgroup.center (SpecialLinearGroup (Fin 2) F) =>
      ((A : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0) hrs
    simp only [scalar_apply, diagonal_apply_eq] at this
    exact Subtype.ext this
  · rintro ⟨A, hA⟩
    obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
    rw [Fintype.card_fin] at hr
    exact ⟨⟨r, hr⟩, Subtype.ext (Subtype.ext hrA)⟩

theorem card_sq_eq_one_subfield {K : Type*} [Field K] (F : Subfield K) :
    Nat.card {r : F // r ^ 2 = 1} = Nat.card {c : K // c ^ 2 = 1} := by
  refine Nat.card_congr (Equiv.ofBijective (fun r => ⟨(r.1 : K), by
    rw [← SubmonoidClass.coe_pow, r.2, OneMemClass.coe_one]⟩) ⟨?_, ?_⟩)
  · intro r s hrs
    have := congrArg Subtype.val hrs
    exact Subtype.ext (Subtype.ext this)
  · rintro ⟨c, hc⟩
    have hc' : c = 1 ∨ c = -1 := by
      have : (c - 1) * (c + 1) = 0 := by linear_combination hc
      rcases mul_eq_zero.mp this with h | h
      · exact Or.inl (sub_eq_zero.mp h)
      · exact Or.inr (eq_neg_of_add_eq_zero_left h)
    rcases hc' with rfl | rfl
    · exact ⟨⟨1, one_pow 2⟩, rfl⟩
    · exact ⟨⟨-1, by rw [neg_one_sq]⟩, rfl⟩

section Plane

variable {ℓ f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K)
  {V : Type*} [AddCommGroup V] [Module K V]

theorem nonempty_sesqSpecialUnitaryGroup_mulEquiv_SL2 [FiniteDimensional K V]
    {B : V →ₛₗ[h.bar] V →ₗ[K] K} (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    (hV : Module.finrank K V = 2) :
    Nonempty (sesqSpecialUnitaryGroup B ≃* SpecialLinearGroup (Fin 2) h.fixedField) := by
  have : Fact ℓ.Prime := ⟨h.prime⟩
  have := h.finite
  have : CharP K ℓ := h.charP
  obtain ⟨e₀, he₀⟩ := h.exists_orthonormal_basis hB hBl
  set e := e₀.reindex (finCongr hV) with he
  have he' : ∀ i j, B (e i) (e j) = if i = j then 1 else 0 := by
    intro i j
    rw [he, Module.Basis.reindex_apply, Module.Basis.reindex_apply, he₀]
    simp only [EmbeddingLike.apply_eq_iff_eq]
  obtain ⟨Ψ₁⟩ :=
    CFSG.RankThree.CentralLiftU.nonempty_sesqSpecialUnitaryGroup_mulEquiv_SUid h e he'
  rw [CFSG.RankThree.CentralLiftU.barEquiv_eq_unitaryInvolution h] at Ψ₁
  have hF := card_eq_sq_of_unitaryFieldData h
  obtain ⟨ζ, hζ0, hζ⟩ := exists_unitaryInvolution_eq_neg hF
  obtain ⟨P, hP⟩ := exists_wittMatrix hF 2
  rw [fixedField_eq_fixedSubfield h]
  exact ⟨Ψ₁.trans ((hypEquiv hζ0 hζ).trans (conjEquiv P hP)).symm⟩

@[expose] noncomputable def scalarUnit {c : K} (hc : c ≠ 0) : LinearMap.GeneralLinearGroup K V :=
  ⟨c • LinearMap.id, c⁻¹ • LinearMap.id, by rw [smul_mul_smul, mul_inv_cancel₀ hc, one_smul]; rfl,
    by rw [smul_mul_smul, inv_mul_cancel₀ hc, one_smul]; rfl⟩

theorem coe_scalarUnit {c : K} (hc : c ≠ 0) :
    ((scalarUnit hc : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) = c • LinearMap.id :=
  rfl

theorem sq_eq_one_iff' {c : K} : c ^ 2 = 1 ↔ c = 1 ∨ c = -1 := by
  constructor
  · intro hc
    have : (c - 1) * (c + 1) = 0 := by linear_combination hc
    rcases mul_eq_zero.mp this with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  · rintro (rfl | rfl) <;> simp

theorem scalarUnit_mem [FiniteDimensional K V] {B : V →ₛₗ[h.bar] V →ₗ[K] K}
    (hV : Module.finrank K V = 2) {c : K} (hc2 : c ^ 2 = 1) (hc : c ≠ 0) :
    scalarUnit hc ∈ sesqSpecialUnitaryGroup B := by
  rw [mem_sesqSpecialUnitaryGroup, mem_sesqUnitaryGroup, coe_scalarUnit]
  have hbar : h.bar c = c := by
    rcases sq_eq_one_iff'.mp hc2 with rfl | rfl
    · exact map_one h.bar
    · rw [map_neg, map_one]
  refine ⟨fun x y => ?_, ?_⟩
  · simp only [LinearMap.smul_apply, LinearMap.id_apply, map_smulₛₗ, LinearMap.smul_apply,
      hbar, smul_eq_mul, RingHom.id_apply]
    rw [← mul_assoc, ← sq, hc2, one_mul]
  · rw [LinearMap.det_smul, LinearMap.det_id, hV, mul_one, hc2]

theorem mem_center_sesqSpecialUnitaryGroup_iff [FiniteDimensional K V]
    {B : V →ₛₗ[h.bar] V →ₗ[K] K} (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    (hV : Module.finrank K V = 2) (g : sesqSpecialUnitaryGroup B) :
    g ∈ Subgroup.center (sesqSpecialUnitaryGroup B) ↔ ∃ c : K, c ^ 2 = 1 ∧
      ((g : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) = c • LinearMap.id := by
  classical
  have := h.finite
  obtain ⟨φ⟩ := nonempty_sesqSpecialUnitaryGroup_mulEquiv_SL2 h hB hBl hV
  have : Finite (sesqSpecialUnitaryGroup B) := Finite.of_equiv _ φ.symm.toEquiv
  have hVnt : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by rw [hV]; norm_num)
  have hne : ∀ {c : K}, c ^ 2 = 1 → c ≠ 0 := fun hc h0 => by
    rw [h0, zero_pow two_ne_zero] at hc
    exact zero_ne_one hc
  let Zs : Subgroup (sesqSpecialUnitaryGroup B) :=
    { carrier := {g | ∃ c : K, c ^ 2 = 1 ∧
        ((g : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) = c • LinearMap.id}
      one_mem' := ⟨1, one_pow 2, by rw [one_smul]; rfl⟩
      mul_mem' := by
        rintro a b ⟨c, hc, hac⟩ ⟨d, hd, hbd⟩
        refine ⟨c * d, by rw [mul_pow, hc, hd, one_mul], ?_⟩
        change ((a : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) *
          ((b : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) = _
        rw [hac, hbd]
        ext x
        simp [smul_smul, mul_comm]
      inv_mem' := by
        rintro a ⟨c, hc, hac⟩
        refine ⟨c, hc, ?_⟩
        have haa : a * a = 1 := by
          apply Subtype.ext
          apply Units.ext
          change ((a : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) *
            ((a : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) = 1
          rw [hac]
          ext x
          simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.id_apply, smul_smul,
            Module.End.one_apply]
          rw [← sq, hc, one_smul]
        rw [inv_eq_of_mul_eq_one_right haa]
        exact hac }
  have hZs : ∀ g, g ∈ Zs ↔ ∃ c : K, c ^ 2 = 1 ∧
      ((g : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) = c • LinearMap.id := fun g => Iff.rfl
  have hZsc : Zs ≤ Subgroup.center (sesqSpecialUnitaryGroup B) := by
    rintro a ⟨c, -, hac⟩
    rw [Subgroup.mem_center_iff]
    intro b
    refine Subtype.ext (Units.ext ?_)
    change ((b : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) *
        ((a : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) =
      ((a : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) *
        ((b : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V)
    rw [hac]
    ext x
    simp
  have hcardZs : Nat.card Zs = Nat.card {c : K // c ^ 2 = 1} := by
    refine (Nat.card_congr (Equiv.ofBijective (fun c : {c : K // c ^ 2 = 1} =>
      (⟨⟨scalarUnit (hne c.2), scalarUnit_mem h hV c.2 (hne c.2)⟩, ⟨c, c.2, rfl⟩⟩ : Zs))
      ⟨?_, ?_⟩)).symm
    · intro c d hcd
      have h1 := congrArg (fun z : Zs =>
        (((z : sesqSpecialUnitaryGroup B) : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V)) hcd
      simp only [coe_scalarUnit] at h1
      obtain ⟨v, hv⟩ := exists_ne (0 : V)
      have h2 := LinearMap.congr_fun h1 v
      simp only [LinearMap.smul_apply, LinearMap.id_apply] at h2
      exact Subtype.ext (smul_left_injective K hv h2)
    · rintro ⟨a, c, hc, hac⟩
      refine ⟨⟨c, hc⟩, Subtype.ext (Subtype.ext (Units.ext ?_))⟩
      change c • LinearMap.id = ((a : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V)
      rw [hac]
  have hcardC : Nat.card (Subgroup.center (sesqSpecialUnitaryGroup B)) =
      Nat.card (Subgroup.center (SpecialLinearGroup (Fin 2) h.fixedField)) := by
    rw [← Subgroup.map_center_eq φ, Subgroup.card_map_of_injective φ.injective]
  have hle : Nat.card (Subgroup.center (sesqSpecialUnitaryGroup B)) ≤ Nat.card Zs := by
    rw [hcardC, card_center_SL2, card_sq_eq_one_subfield, hcardZs]
  have heq := Subgroup.eq_of_le_of_card_ge hZsc hle
  rw [← heq, hZs]

theorem isQuasisimple_sesqSpecialUnitaryGroup [FiniteDimensional K V]
    {B : V →ₛₗ[h.bar] V →ₗ[K] K} (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    (hV : Module.finrank K V = 2) (hq : 4 ≤ ℓ ^ f) :
    CFSG.IsQuasisimple (sesqSpecialUnitaryGroup B) := by
  obtain ⟨φ⟩ := nonempty_sesqSpecialUnitaryGroup_mulEquiv_SL2 h hB hBl hV
  have := h.finite
  have h4 : ∃ s : Finset h.fixedField, s.card = 4 := by
    have := Fintype.ofFinite h.fixedField
    have hle : 4 ≤ (Finset.univ : Finset h.fixedField).card := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card, UnitaryFieldData.card_fixedField h]
      exact hq
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq hle
    exact ⟨s, hs⟩
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv φ.symm (isQuasisimple_SL2 h4)

end Plane

section Block

variable {ℓ f : ℕ} {K : Type} [Field K]

@[expose] def coordBlock (ℓ f : ℕ) (K : Type) [Field K] (c : Fin 3) :
    Subgroup (unitarySU ℓ f K 3) where
  carrier := {g | ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ Pi.single c 1 = Pi.single c 1}
  mul_mem' {g g'} hg hg' := by
    change (((g * g' : unitarySU ℓ f K 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ _ = _
    rw [Subgroup.coe_mul, Units.val_mul, ← Matrix.mulVec_mulVec]
    rw [show ((g' : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ _ = _ from hg']
    exact hg
  one_mem' := by
    change (((1 : unitarySU ℓ f K 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ _ = _
    rw [Subgroup.coe_one, Units.val_one, Matrix.one_mulVec]
  inv_mem' {g} hg := by
    change (((g⁻¹ : unitarySU ℓ f K 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ _ = _
    have hg' : ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ Pi.single c 1 =
        Pi.single c 1 := hg
    conv_lhs => rw [← hg']
    rw [Matrix.mulVec_mulVec, Subgroup.coe_inv, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec]

theorem mem_coordBlock {c : Fin 3} {g : unitarySU ℓ f K 3} :
    g ∈ coordBlock ℓ f K c ↔
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ Pi.single c 1 = Pi.single c 1 :=
  Iff.rfl

theorem injective_unitaryProj_comp_coordBlock (h : UnitaryFieldData ℓ f K) (c : Fin 3) :
    Function.Injective ((unitaryProj h 3).comp (coordBlock ℓ f K c).subtype) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hgZ : (g : unitarySU ℓ f K 3) ∈ unitaryScalars h 3 := by
    rw [← ker_unitaryProj h 3]
    exact hg
  obtain ⟨a, -, -, ha⟩ := mem_unitaryScalars.mp hgZ
  have hfix := g.2
  rw [mem_coordBlock, ha, Matrix.GeneralLinearGroup.coe_scalar, scalar_apply,
    ← smul_one_eq_diagonal, smul_mulVec, one_mulVec] at hfix
  have ha1 : (a : K) = 1 := by
    have := congrFun hfix c
    simpa using this
  have ha1' : a = 1 := Units.ext ha1
  refine Subtype.ext (Subtype.ext ?_)
  rw [Subgroup.coe_one, Subgroup.coe_one, ha, ha1', map_one]

theorem one_col_eq_single (c : Fin 3) :
    (fun k => ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) k c) = Pi.single c 1 := by
  funext k
  rw [Units.val_one, Matrix.one_apply, Pi.single_apply]

theorem nonempty_coordBlock_mulEquiv (h : UnitaryFieldData ℓ f K) (c : Fin 3) :
    Nonempty (coordBlock ℓ f K c ≃* SpecialLinearGroup (Fin 2) h.fixedField) := by
  have : Fact ℓ.Prime := ⟨h.prime⟩
  have := h.finite
  have : CharP K ℓ := h.charP
  have hF := card_eq_sq_of_unitaryFieldData h
  have heq : SUgram h.bar (1 : Matrix (Fin 3) (Fin 3) K) = unitarySU ℓ f K 3 :=
    (SUgram_bar_one h 3).trans (SUid_eq_statedSU hF 3)
  obtain ⟨ψ⟩ := nonempty_coordPairSubgroup_mulEquiv h (G₀ := 1) 1 (by
    rw [Units.val_one, ctr_one, Matrix.mul_one, Matrix.mul_one]) c
  have hmem : ∀ g : GL (Fin 3) K, (g : Matrix (Fin 3) (Fin 3) K) *ᵥ
      (fun k => ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) k c) =
        (fun k => ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) k c) ↔
      (g : Matrix (Fin 3) (Fin 3) K) *ᵥ Pi.single c 1 = Pi.single c 1 := fun g => by
    rw [one_col_eq_single]
  let e : coordBlock ℓ f K c ≃* coordPairSubgroup h.bar 1 1 c :=
    { toFun := fun g => ⟨⟨g.1.1, by rw [heq]; exact g.1.2⟩, (hmem _).mpr g.2⟩
      invFun := fun g => ⟨⟨g.1.1, by rw [← heq]; exact g.1.2⟩, (hmem _).mp g.2⟩
      left_inv := fun g => rfl
      right_inv := fun g => rfl
      map_mul' := fun g g' => rfl }
  exact ⟨e.trans ψ⟩

theorem isQuasisimple_map_coordBlock (h : UnitaryFieldData ℓ f K) (c : Fin 3)
    (hq : 4 ≤ ℓ ^ f) : CFSG.IsQuasisimple ((coordBlock ℓ f K c).map (unitaryProj h 3)) := by
  obtain ⟨ψ⟩ := nonempty_coordBlock_mulEquiv h c
  have hinj := injective_unitaryProj_comp_coordBlock h c
  have hrange : ((unitaryProj h 3).comp (coordBlock ℓ f K c).subtype).range =
      (coordBlock ℓ f K c).map (unitaryProj h 3) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  let e := (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  have := h.finite
  have h4 : ∃ s : Finset h.fixedField, s.card = 4 := by
    have := Fintype.ofFinite h.fixedField
    have hle : 4 ≤ (Finset.univ : Finset h.fixedField).card := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card, UnitaryFieldData.card_fixedField h]
      exact hq
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq hle
    exact ⟨s, hs⟩
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (ψ.symm.trans e) (isQuasisimple_SL2 h4)

end Block

theorem unitary_two_block_quasisimple_structure {ℓ f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData ℓ f K) {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (B : V →ₛₗ[h.bar] V →ₗ[K] K) (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    (hV : Module.finrank K V = 2) :
    (Nonempty (sesqSpecialUnitaryGroup B ≃* SpecialLinearGroup (Fin 2) h.fixedField) ∧
      (∀ g : sesqSpecialUnitaryGroup B, g ∈ Subgroup.center (sesqSpecialUnitaryGroup B) ↔
        ∃ c : K, c ^ 2 = 1 ∧
          ((g : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) = c • LinearMap.id) ∧
      (4 ≤ ℓ ^ f → Group.IsPerfect (sesqSpecialUnitaryGroup B) ∧
        IsSimpleGroup (sesqSpecialUnitaryGroup B ⧸ Subgroup.center (sesqSpecialUnitaryGroup B)) ∧
        ∃ a b : sesqSpecialUnitaryGroup B ⧸ Subgroup.center (sesqSpecialUnitaryGroup B),
          a * b ≠ b * a)) ∧
    ∀ c : Fin 3, Function.Injective ((unitaryProj h 3).comp (coordBlock ℓ f K c).subtype) ∧
      Nonempty (coordBlock ℓ f K c ≃* SpecialLinearGroup (Fin 2) h.fixedField) ∧
      (4 ≤ ℓ ^ f → CFSG.IsQuasisimple ((coordBlock ℓ f K c).map (unitaryProj h 3))) :=
  ⟨⟨nonempty_sesqSpecialUnitaryGroup_mulEquiv_SL2 h hB hBl hV,
    mem_center_sesqSpecialUnitaryGroup_iff h hB hBl hV,
    fun hq => isQuasisimple_sesqSpecialUnitaryGroup h hB hBl hV hq⟩, fun c =>
    ⟨injective_unitaryProj_comp_coordBlock h c, nonempty_coordBlock_mulEquiv h c,
      fun hq => isQuasisimple_map_coordBlock h c hq⟩⟩

end CFSG.RankThree.Classical
