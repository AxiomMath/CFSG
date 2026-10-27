module

public import CFSG.RankThree.Chevalley.SteinbergBUF4CyclotomicFourSetup
public import CFSG.RankThree.Chevalley.SteinbergCAF4CyclotomicFourTorus
public import CFSG.RankThree.Coprime.EvenCenterSectionCover
public import CFSG.RankThree.Chevalley.SteinbergBNF4NativeB2
public import CFSG.RankThree.Chevalley.SteinbergBUF4CyclotomicFourDescent
public import CFSG.RankThree.Chevalley.SteinbergBUF4CyclotomicFourTools

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley F4Weyl RootSpace EvenF4QPlus
  CFSG.LieType.AlgebraicGroups
open scoped Pointwise

theorem cyclotomic_four_centralizer_and_D (K : Type) [Field K] [Finite K] [CharP K 2]
    (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (F : Ω →+* Ω)
    (hF : ∀ c, F c = c ^ Nat.card K) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (K₄ : IntermediateField K Ω) (hK₄ : Module.finrank K K₄ = 4) (n g : ModGL .F4 Ω)
    (hn : n = canonicalRep (coxeterSystem .F4) Ω (f4Coxeter ^ 3)) (hg : g ∈ adjointGroup .F4 Ω)
    (hgn : g⁻¹ * Units.map (entrywiseHom F) g = n) (Γ T₀ : Subgroup (ModGL .F4 Ω))
    (hΓ : Γ = conjEntrywiseImage K g⁻¹) (hT₀ : T₀ = torusGroup .F4 Ω ⊓ Γ) (x : ModGL .F4 Ω)
    (hx : x ∈ T₀) (hxp : orderOf x = p) (u : WeylGroup .F4) (ε : ℤ)
    (hu : (fun α => u • α) '' {α | IsRoot .F4 α ∧ torusRootChar x α = 1} =
      parabolicRoots .F4 {f4Index 1, f4Index 2})
    (huw : ∀ z ∈ Submodule.span ℝ (ofLattice '' parabolicRoots .F4 {f4Index 1, f4Index 2}),
      weylAct .F4 (u * f4Coxeter ^ 3 * u⁻¹) z =
        weylAct .F4 ((simple .F4 (f4Index 1) * simple .F4 (f4Index 2)) ^ ε) z)
    (h y : ModGL .F4 Ω) (hh : h = canonicalRep (coxeterSystem .F4) Ω u) (hy : y = h * x * h⁻¹)
    (Γ₁ D : Subgroup (ModGL .F4 Ω)) (hΓ₁ : Γ₁ = Γ.map (MulAut.conj h).toMonoidHom)
    (hD : D = Γ₁ ⊓ Subgroup.centralizer {y}) :
    (((adjointGroup .F4 K₄).map (baseChangeGL (algebraMap K₄ Ω)) ⊓ Subgroup.centralizer {y} :
        Subgroup (ModGL .F4 Ω)) : Set (ModGL .F4 Ω)) =
      ((torusGroup .F4 K₄).map (baseChangeGL (algebraMap K₄ Ω)) : Set (ModGL .F4 Ω)) *
        ((subsystemGroup .F4 K₄ {1, 2}).map (baseChangeGL (algebraMap K₄ Ω)) :
          Set (ModGL .F4 Ω)) ∧
    ∃ σ : K₄ ≃+* K₄, (∀ b, σ b = b ^ Nat.card K) ∧
      (∀ α : Fin Tag.F4.rank → ℤ, α 0 = 0 → α 3 = 0 →
        (u * f4Coxeter ^ 3 * u⁻¹) • α = ((simple Tag.F4 1 * simple Tag.F4 2) ^ ε) • α) ∧
      D = ((torusGroup .F4 K₄ ⊔ subsystemGroup .F4 K₄ {1, 2}) ⊓
        ((MulAut.conj (canonicalRep (coxeterSystem .F4) K₄
            (u * f4Coxeter ^ 3 * u⁻¹))).toMonoidHom.comp
          (Units.map (entrywiseHom σ.toRingHom))).eqLocus (MonoidHom.id _)).map
            (baseChangeGL (algebraMap K₄ Ω)) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have : CharP Ω 2 := charP_of_injective_algebraMap (algebraMap K Ω).injective 2
  have : FiniteDimensional K K₄ := Module.finite_of_finrank_eq_succ hK₄
  have : Finite K₄ := Module.finite_of_finite K
  have : CharP K₄ 2 := charP_of_injective_algebraMap (algebraMap K K₄).injective 2
  set ι : K₄ →+* Ω := algebraMap K₄ Ω with hι
  have hinj := baseChangeGL_injective (τ := Tag.F4) ι
  obtain ⟨-, hCA⟩ := F4_cyclotomic_four_torus_and_regular_prime_centralizers K Ω F hF n hn
  obtain ⟨-, -, -, -, h2⟩ := hCA g hg hgn Γ T₀ (T₀.map (MulAut.conj g).toMonoidHom) hΓ hT₀ rfl
  obtain ⟨-, hT₀K₄, hΓK₄, -, -⟩ := h2 ‹_› K₄ hK₄
  obtain ⟨x₀, hx₀H, hx₀⟩ := hT₀K₄ hx
  have hhι : baseChangeGL ι (canonicalRep (coxeterSystem .F4) K₄ u) = h := by
    rw [hh]
    exact baseChangeGL_canonicalRep ι u
  set y₀ := canonicalRep (coxeterSystem .F4) K₄ u * x₀ *
    (canonicalRep (coxeterSystem .F4) K₄ u)⁻¹ with hy₀
  have hyι : baseChangeGL ι y₀ = y := by
    rw [hy₀, map_mul, map_mul, map_inv, hhι, hx₀, hy]
  have hu' : (fun α => u • α) '' {α | IsRoot .F4 α ∧ torusRootChar (baseChangeGL ι x₀) α = 1} =
      parabolicRoots .F4 {1, 2} := by
    rw [hx₀]
    exact hu
  obtain ⟨c, hc, hcp, hc1, hker⟩ :=
    exists_rootDiagUnit_of_conj ι hp hx₀H (by rw [hx₀]; exact hxp) u hu'
  have hL₀ : adjointGroup .F4 K₄ ⊓ Subgroup.centralizer {y₀} =
      torusGroup .F4 K₄ ⊔ subsystemGroup .F4 K₄ {1, 2} := by
    rw [hy₀, hc]
    exact adjointGroup_inf_centralizer_rootDiagUnit_eq hp hp3 hcp hc1 hker
  have hnorm : torusGroup .F4 K₄ ≤ Subgroup.normalizer
      (subsystemGroup .F4 K₄ {1, 2} : Set (ModGL .F4 K₄)) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro z
    have hT := (F4_native_B2_faithful_Sp4_all_characteristics K₄).2.2.2.2.2.2.2.2.2.1
    obtain ⟨⟨hN, -⟩, -⟩ := hT t ht _ _ (apply_rootVec_of_mem_torusGroup ht (isRoot_single _ 1))
      (apply_rootVec_of_mem_torusGroup ht (isRoot_single _ 2))
    obtain ⟨⟨hN', -⟩, -⟩ := hT t⁻¹ (inv_mem ht) _ _
      (apply_rootVec_of_mem_torusGroup (inv_mem ht) (isRoot_single _ 1))
      (apply_rootVec_of_mem_torusGroup (inv_mem ht) (isRoot_single _ 2))
    constructor
    · exact hN z
    · intro hz
      have := hN' _ hz
      have e : t⁻¹ * (t * z * t⁻¹) * t⁻¹⁻¹ = z := by group
      rwa [e] at this
  have hC : ((adjointGroup .F4 K₄).map (baseChangeGL ι) ⊓ Subgroup.centralizer {y} :
      Subgroup (ModGL .F4 Ω)) = (torusGroup .F4 K₄ ⊔ subsystemGroup .F4 K₄ {1, 2}).map
        (baseChangeGL ι) := by
    rw [← hL₀]
    ext z
    constructor
    · intro hz
      obtain ⟨hzC, hzc⟩ := Subgroup.mem_inf.1 hz
      obtain ⟨z₀, hz₀, rfl⟩ := hzC
      rw [Subgroup.mem_centralizer_singleton_iff, ← hyι, ← map_mul, ← map_mul] at hzc
      exact ⟨z₀, Subgroup.mem_inf.2 ⟨hz₀, Subgroup.mem_centralizer_singleton_iff.2
        (hinj hzc)⟩, rfl⟩
    · rintro ⟨z₀, hz₀, rfl⟩
      obtain ⟨hz₀C, hz₀c⟩ := Subgroup.mem_inf.1 hz₀
      rw [Subgroup.mem_centralizer_singleton_iff] at hz₀c
      refine Subgroup.mem_inf.2 ⟨⟨z₀, hz₀C, rfl⟩, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff, ← hyι, ← map_mul, ← map_mul, hz₀c]
  refine ⟨?_, ?_⟩
  · rw [hC, Subgroup.coe_map, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hnorm,
      Set.image_mul]
    rfl
  obtain ⟨σ, hσ, hFσ⟩ := exists_frob_restrict F (fun c => by rw [hF, Nat.card_eq_fintype_card])
    K₄
  refine ⟨σ, fun b => by rw [hσ b, Nat.card_eq_fintype_card],
    fun α h0 h3 => smul_eq_of_weylAct_eq huw α h0 h3, ?_⟩
  set v := u * f4Coxeter ^ 3 * u⁻¹ with hv
  have hm : baseChangeGL ι (canonicalRep (coxeterSystem .F4) K₄ v) = h * n * h⁻¹ := by
    rw [baseChangeGL_canonicalRep, hh, hn, canonicalRep_conj_eq_of_charTwo]
  have hhC : h ∈ (adjointGroup .F4 K₄).map (baseChangeGL ι) :=
    ⟨_, canonicalRep_mem_adjointGroup _ K₄ u, hhι⟩
  have hFh : Units.map (entrywiseHom F) h = h := by
    rw [hh]
    exact entrywise_canonicalRep (RingEquiv.ofBijective F (frobenius_bijective (k := K) F hF)) u
  have hΓ₁ch : ∀ z, z ∈ Γ₁ ↔ z ∈ (adjointGroup .F4 K₄).map (baseChangeGL ι) ∧
      h * n * h⁻¹ * Units.map (entrywiseHom F) z * (h * n * h⁻¹)⁻¹ = z := by
    intro z
    rw [hΓ₁, Subgroup.mem_map_equiv, hΓK₄, Subgroup.mem_inf]
    change (MulAut.conj h).symm z ∈ _ ∧ twistedEntrywise n F ((MulAut.conj h).symm z) =
      (MulAut.conj h).symm z ↔ _
    rw [MulAut.conj_symm_apply, twistedEntrywise_apply, map_mul, map_mul, map_inv, hFh]
    constructor
    · rintro ⟨hz, hfix⟩
      refine ⟨?_, ?_⟩
      · have e : z = h * (h⁻¹ * z * h) * h⁻¹ := by group
        rw [e]
        exact mul_mem (mul_mem hhC hz) (inv_mem hhC)
      · calc h * n * h⁻¹ * Units.map (entrywiseHom F) z * (h * n * h⁻¹)⁻¹ =
            h * (n * (h⁻¹ * Units.map (entrywiseHom F) z * h) * n⁻¹) * h⁻¹ := by group
          _ = h * (h⁻¹ * z * h) * h⁻¹ := by rw [hfix]
          _ = z := by group
    · rintro ⟨hz, hfix⟩
      refine ⟨mul_mem (mul_mem (inv_mem hhC) hz) hhC, ?_⟩
      calc n * (h⁻¹ * Units.map (entrywiseHom F) z * h) * n⁻¹ =
          h⁻¹ * (h * n * h⁻¹ * Units.map (entrywiseHom F) z * (h * n * h⁻¹)⁻¹) * h := by group
        _ = h⁻¹ * z * h := by rw [hfix]
  rw [hD, ← hyι, ← hL₀]
  exact inf_centralizer_eq_map_fixed ι F σ.toRingHom hFσ hΓ₁ch hm rfl

theorem cyclotomic_four_D_structure (K : Type) [Field K] [Finite K] [CharP K 2] (Ω : Type)
    [Field Ω] [Algebra K Ω] (K₄ : IntermediateField K Ω) (hK₄ : Module.finrank K K₄ = 4)
    (σ : K₄ ≃+* K₄) (hσ : ∀ b, σ b = b ^ Nat.card K) (v : WeylGroup .F4) (ε : ℤ)
    (hε : ε = 1 ∨ ε = -1)
    (hv : ∀ α : Fin Tag.F4.rank → ℤ, α 0 = 0 → α 3 = 0 →
      v • α = ((simple Tag.F4 1 * simple Tag.F4 2) ^ ε) • α)
    (D R : Subgroup (ModGL .F4 Ω))
    (hD : D = ((torusGroup .F4 K₄ ⊔ subsystemGroup .F4 K₄ {1, 2}) ⊓
        ((MulAut.conj (canonicalRep (coxeterSystem .F4) K₄ v)).toMonoidHom.comp
          (Units.map (entrywiseHom σ.toRingHom))).eqLocus (MonoidHom.id _)).map
            (baseChangeGL (algebraMap K₄ Ω)))
    (hR : R = ⁅D, D⁆) :
    ∃ Z₀ P : Subgroup (ModGL .F4 Ω),
      Z₀ ≤ (torusGroup .F4 K₄).map (baseChangeGL (algebraMap K₄ Ω)) ∧ Odd (Nat.card Z₀) ∧
      (∃ a ∈ subsystemGroup .F4 K₄ {1, 2},
        (∀ z, z ∈ P ↔ ∃ y' ∈ subsystemGroup .F4 K {1, 2},
          z = baseChangeGL (algebraMap K₄ Ω) a * baseChangeGL (algebraMap K Ω) y' *
            (baseChangeGL (algebraMap K₄ Ω) a)⁻¹) ∧
        ∀ A : SL2 K, baseChangeGL (algebraMap K₄ Ω) (a * rootSL2 .F4 K₄ (Pi.single 1 1)
          (Matrix.SpecialLinearGroup.map (algebraMap K K₄) A) * a⁻¹) ∈ P) ∧
      (∃ e : Z₀ × P ≃* D, ∀ q, (e q : ModGL .F4 Ω) = q.1 * q.2) ∧
      (Subgroup.center D).map D.subtype = Z₀ ∧
      (4 ≤ Nat.card K → R = P ∧ Nonempty (P ≃* EvenQuartic.spJ K) ∧ IsSimpleGroup R ∧
        Group.IsPerfect R ∧ ∃ r₁ r₂ : R, r₁ * r₂ ≠ r₂ * r₁) ∧
      (Nat.card K = 2 → R = ⁅P, P⁆ ∧
        (∃ e : P ≃* Equiv.Perm (Fin 6),
          ∀ z : P, (z : ModGL .F4 Ω) ∈ R ↔ e z ∈ alternatingGroup (Fin 6)) ∧
        IsSimpleGroup R ∧ Group.IsPerfect R ∧ ∃ r₁ r₂ : R, r₁ * r₂ ≠ r₂ * r₁) ∧
      CFSG.layer R = ⊤ ∧ R ≠ ⊥ ∧ D ⊓ Subgroup.centralizer (R : Set (ModGL .F4 Ω)) = Z₀ := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : FiniteDimensional K K₄ := Module.finite_of_finrank_eq_succ hK₄
  have : CharP K₄ 2 := charP_of_injective_algebraMap (algebraMap K K₄).injective 2
  have hσ' : ∀ b, σ b = b ^ Fintype.card K := fun b => by rw [hσ, Nat.card_eq_fintype_card]
  obtain ⟨Zf, QK, a, ha, hZfH, hZfodd, hZfcomm, hQK, hQKQ, hLfix, hdisj0, hsp, hQKiso, hρ⟩ :=
    exists_levi_fixed_data hK₄ σ hσ' v ε hε hv
  set ι : K₄ →+* Ω := algebraMap K₄ Ω with hι
  have hinj := baseChangeGL_injective (τ := Tag.F4) ι
  set Z₀ := Zf.map (baseChangeGL ι) with hZ₀
  set P := QK.map (baseChangeGL ι) with hP
  have hDsup : Z₀ ⊔ P = D := by rw [hD, hLfix, Subgroup.map_sup]
  have hdisj : Z₀ ⊓ P = ⊥ := by
    rw [hZ₀, hP, ← Subgroup.map_inf_eq _ _ _ hinj, hdisj0, Subgroup.map_bot]
  have hHcomm := (triangular_borel_structure.{0, 0} Tag.F4 K₄).1
  have hZab : ∀ z ∈ Z₀, ∀ z' ∈ Z₀, z * z' = z' * z := by
    rintro _ ⟨z, hz, rfl⟩ _ ⟨z', hz', rfl⟩
    rw [← map_mul, ← map_mul, hHcomm z (hZfH hz) z' (hZfH hz')]
  have hcomm : ∀ z ∈ Z₀, ∀ x ∈ P, z * x = x * z := by
    rintro _ ⟨z, hz, rfl⟩ _ ⟨x, hx, rfl⟩
    rw [← map_mul, ← map_mul, hZfcomm z hz x (hQKQ hx)]
  obtain ⟨eQ⟩ := hQKiso
  set e₁ : P ≃* subsystemGroup .F4 K {1, 2} :=
    (QK.equivMapOfInjective _ hinj).symm.trans eQ with he₁
  have hZK := center_subsystemGroup_one_two (K := K)
  have hZP : ∀ x ∈ P, (∀ x' ∈ P, x' * x = x * x') → x = 1 := by
    intro x hx hc
    have h : e₁ ⟨x, hx⟩ ∈ Subgroup.center (subsystemGroup .F4 K {1, 2}) := by
      rw [Subgroup.mem_center_iff]
      intro s
      obtain ⟨y, rfl⟩ := e₁.surjective s
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hc _ y.2)
    rw [hZK, Subgroup.mem_bot, MulEquiv.map_eq_one_iff] at h
    exact congrArg Subtype.val h
  have h2dvd : 2 ∣ Nat.card K := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact prime_dvd_card (K := K) 2
  have hcases : Nat.card K = 2 ∨ 4 ≤ Nat.card K := by
    have h1 : 2 ≤ Nat.card K := by
      have := Fintype.one_lt_card (α := K)
      rw [Nat.card_eq_fintype_card]
      omega
    obtain ⟨k, hk⟩ := h2dvd
    omega
  have hsym : Nat.card K = 2 → Nonempty (P ≃*
      CFSG.ComponentClassification.PresentationLocal.sympFour) := fun h2 => by
    obtain ⟨e₂⟩ := nonempty_subsystemGroup_one_two_mulEquiv_sympFour (K := K)
      (by rw [← Nat.card_eq_fintype_card]; exact h2)
    exact ⟨e₁.trans e₂⟩
  have hCR : ∀ x ∈ P, (∀ r ∈ ⁅P, P⁆, r * x = x * r) → x = 1 := by
    rcases hcases with h2 | h4
    · obtain ⟨e₂⟩ := hsym h2
      exact fun x hx hc => eq_one_of_commute_commutator_of_mulEquiv e₂
        CFSG.ComponentClassification.PresentationLocal.centralizer_commutator_sympFour hx hc
    · obtain ⟨hsimple, hperf, hnab⟩ := isSimpleGroup_subsystemGroup_one_two (K := K) h4
      exact (simple_factor_facts hperf hnab e₁).2.2.1
  obtain ⟨hprod, hcenter, hRP, hcent⟩ :=
    levi_fixed_group_theory hZab hcomm hdisj hDsup hR hZP hCR
  have hRfacts : IsSimpleGroup R ∧ Group.IsPerfect R ∧ ∃ r₁ r₂ : R, r₁ * r₂ ≠ r₂ * r₁ := by
    rcases hcases with h2 | h4
    · obtain ⟨e₂⟩ := hsym h2
      obtain ⟨eR⟩ := nonempty_commutator_mulEquiv e₂
      rw [hRP]
      have := CFSG.ComponentClassification.PresentationLocal.isSimpleGroup_commutator_sympFour
      have hpc := CFSG.ComponentClassification.PresentationLocal.isPerfect_commutator_sympFour
      refine ⟨(MulEquiv.isSimpleGroup_congr eR).2 this,
        Group.IsPerfect.ofSurjective (f := eR.symm.toMonoidHom) eR.symm.surjective, ?_⟩
      have hnc :=
        CFSG.ComponentClassification.PresentationLocal.not_isMulCommutative_commutator_sympFour
      by_contra hc
      push Not at hc
      exact hnc ⟨⟨fun a b => by
        have := hc (eR.symm a) (eR.symm b)
        rw [← map_mul, ← map_mul] at this
        exact eR.symm.injective this⟩⟩
    · obtain ⟨hsimple, hperf, hnab⟩ := isSimpleGroup_subsystemGroup_one_two (K := K) h4
      obtain ⟨hPP, -, -, hsP, hpP, hnP⟩ := simple_factor_facts hperf hnab e₁
      have hRP' : R = P := hRP.trans hPP
      subst hRP'
      exact ⟨hsP, hpP, hnP⟩
  obtain ⟨hRs, hRp, hRn⟩ := hRfacts
  have hRqs : CFSG.IsQuasisimple R :=
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup (Q := R) hRn).1
  have hRbot : R ≠ ⊥ := by
    have : Nontrivial R := IsSimpleGroup.toNontrivial
    exact (Subgroup.nontrivial_iff_ne_bot R).1 this
  refine ⟨Z₀, P, ?_, ?_, ⟨a, ha, fun z => ?_, fun A => ⟨_, hρ A, rfl⟩⟩, hprod, hcenter,
    fun h4 => ?_, fun h2 => ?_, CFSG.RankThree.Coprime.layer_eq_top_of_isQuasisimple hRqs,
    hRbot, hcent⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact ⟨z, hZfH hz, rfl⟩
  · rw [hZ₀, Subgroup.card_map_of_injective hinj]
    exact hZfodd
  · rw [hP, Subgroup.mem_map]
    constructor
    · rintro ⟨g₀, hg₀, rfl⟩
      obtain ⟨y', hy', rfl⟩ := (hQK g₀).1 hg₀
      refine ⟨y', hy', ?_⟩
      rw [map_mul, map_mul, map_inv, baseChangeGL_baseChangeGL,
        ← IsScalarTower.algebraMap_eq]
    · rintro ⟨y', hy', rfl⟩
      refine ⟨a * baseChangeGL (algebraMap K K₄) y' * a⁻¹, (hQK _).2 ⟨y', hy', rfl⟩, ?_⟩
      rw [map_mul, map_mul, map_inv, baseChangeGL_baseChangeGL,
        ← IsScalarTower.algebraMap_eq]
  · obtain ⟨hsimple, hperf, hnab⟩ := isSimpleGroup_subsystemGroup_one_two (K := K) h4
    obtain ⟨hPP, -⟩ := simple_factor_facts hperf hnab e₁
    obtain ⟨eS⟩ := hsp
    exact ⟨hRP.trans hPP, ⟨(QK.equivMapOfInjective _ hinj).symm.trans eS⟩, hRs, hRp, hRn⟩
  · obtain ⟨e₂⟩ := hsym h2
    refine ⟨hRP, ⟨e₂.trans (MulEquiv.ofBijective _
      ⟨CFSG.ComponentClassification.PresentationLocal.omegaPerm_injective,
        CFSG.ComponentClassification.PresentationLocal.omegaPerm_surjective⟩), fun z => ?_⟩,
      hRs, hRp, hRn⟩
    rw [hRP, mem_commutator_iff_of_mulEquiv e₂,
      CFSG.ComponentClassification.PresentationLocal.commutator_sympFour, Subgroup.mem_comap]
    rfl

theorem map_centralizer_eq_map_conj (K : Type) [Field K] (Ω : Type) [Field Ω] [Algebra K Ω]
    (g : ModGL .F4 Ω) (Γ : Subgroup (ModGL .F4 Ω)) (hΓ : Γ = conjEntrywiseImage K g⁻¹)
    (x h y : ModGL .F4 Ω) (hy : y = h * x * h⁻¹) (Γ₁ D : Subgroup (ModGL .F4 Ω))
    (hΓ₁ : Γ₁ = Γ.map (MulAut.conj h).toMonoidHom) (hD : D = Γ₁ ⊓ Subgroup.centralizer {y})
    (x₀ : adjointGroup .F4 K)
    (hx₀x : baseChangeGL (algebraMap K Ω) (x₀ : ModGL .F4 K) = g * x * g⁻¹) :
    (Subgroup.centralizer {x₀}).map
        ((baseChangeGL (algebraMap K Ω)).comp (adjointGroup .F4 K).subtype) =
      D.map (MulAut.conj (g * h⁻¹)).toMonoidHom := by
  set ιK : K →+* Ω := algebraMap K Ω with hιK
  have hinjK := baseChangeGL_injective (τ := Tag.F4) ιK
  ext z
  rw [Subgroup.mem_map_equiv, hD, Subgroup.mem_inf, hΓ₁, Subgroup.mem_map_equiv, hΓ,
    Subgroup.mem_centralizer_singleton_iff, hy]
  simp only [MulAut.conj_symm_apply]
  constructor
  · rintro ⟨r, hr, rfl⟩
    have hr' := congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hr)
    simp only [Subgroup.coe_mul] at hr'
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
    have hr'' : baseChangeGL ιK (r : ModGL .F4 K) * (g * x * g⁻¹) =
        g * x * g⁻¹ * baseChangeGL ιK (r : ModGL .F4 K) := by
      rw [← hx₀x, ← map_mul, ← map_mul, hr']
    refine ⟨⟨r, r.2, ?_⟩, ?_⟩
    · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [← hιK]
      group
    · calc (g * h⁻¹)⁻¹ * baseChangeGL ιK (r : ModGL .F4 K) * (g * h⁻¹) * (h * x * h⁻¹) =
          h * g⁻¹ * (baseChangeGL ιK (r : ModGL .F4 K) * (g * x * g⁻¹)) * g * h⁻¹ := by group
        _ = h * g⁻¹ * (g * x * g⁻¹ * baseChangeGL ιK (r : ModGL .F4 K)) * g * h⁻¹ := by
            rw [hr'']
        _ = _ := by group
  · rintro ⟨⟨r, hr, hre⟩, hc⟩
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hre
    have hz : baseChangeGL ιK r = z := by
      calc baseChangeGL ιK r = g * (g⁻¹ * baseChangeGL ιK r * g⁻¹⁻¹) * g⁻¹ := by group
        _ = g * (h⁻¹ * ((g * h⁻¹)⁻¹ * z * (g * h⁻¹)) * h) * g⁻¹ := by rw [hre]
        _ = z := by group
    refine ⟨⟨r, hr⟩, Subgroup.mem_centralizer_singleton_iff.2 ?_, ?_⟩
    · apply Subtype.ext
      apply hinjK
      simp only [Subgroup.coe_mul, map_mul]
      rw [hx₀x, hz]
      calc z * (g * x * g⁻¹) = (g * h⁻¹) * (((g * h⁻¹)⁻¹ * z * (g * h⁻¹)) * (h * x * h⁻¹)) *
          (g * h⁻¹)⁻¹ := by group
        _ = (g * h⁻¹) * ((h * x * h⁻¹) * ((g * h⁻¹)⁻¹ * z * (g * h⁻¹))) * (g * h⁻¹)⁻¹ := by
            rw [hc]
        _ = _ := by group
    · simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
      exact hz

theorem cyclotomic_four_transport (K : Type) [Field K] (Ω : Type) [Field Ω] [Algebra K Ω]
    (K₄ : IntermediateField K Ω) (g : ModGL .F4 Ω)
    (hgK₄ : g ∈ (adjointGroup .F4 K₄).map (baseChangeGL (algebraMap K₄ Ω)))
    (Γ : Subgroup (ModGL .F4 Ω)) (hΓ : Γ = conjEntrywiseImage K g⁻¹) (x : ModGL .F4 Ω)
    (hxΓ : x ∈ Γ) (h y : ModGL .F4 Ω)
    (hhK₄ : h ∈ (adjointGroup .F4 K₄).map (baseChangeGL (algebraMap K₄ Ω)))
    (hy : y = h * x * h⁻¹) (Γ₁ D : Subgroup (ModGL .F4 Ω))
    (hΓ₁ : Γ₁ = Γ.map (MulAut.conj h).toMonoidHom) (hD : D = Γ₁ ⊓ Subgroup.centralizer {y})
    (a : ModGL .F4 K₄) (ha : a ∈ adjointGroup .F4 K₄)
    (hρD : ∀ A : SL2 K, baseChangeGL (algebraMap K₄ Ω) (a * rootSL2 .F4 K₄ (Pi.single 1 1)
      (Matrix.SpecialLinearGroup.map (algebraMap K K₄) A) * a⁻¹) ∈ D) :
    ∃ x₀ : adjointGroup .F4 K,
      baseChangeGL (algebraMap K Ω) (x₀ : ModGL .F4 K) = g * x * g⁻¹ ∧
      (Subgroup.centralizer {x₀}).map
          ((baseChangeGL (algebraMap K Ω)).comp (adjointGroup .F4 K).subtype) =
        D.map (MulAut.conj (g * h⁻¹)).toMonoidHom ∧
      ∃ R₀ : Subgroup (adjointGroup .F4 K), R₀ ≤ Subgroup.centralizer {x₀} ∧
        ∃ k ∈ adjointGroup .F4 K₄,
          (R₀.map ((baseChangeGL (algebraMap K K₄)).comp (adjointGroup .F4 K).subtype)).map
              (MulAut.conj k).toMonoidHom =
            ((rootSL2 .F4 K₄ (Pi.single 1 1)).comp
              (Matrix.SpecialLinearGroup.map (algebraMap K K₄))).range := by
  classical
  set ιK : K →+* Ω := algebraMap K Ω with hιK
  set ι : K₄ →+* Ω := algebraMap K₄ Ω with hι
  have hinjK := baseChangeGL_injective (τ := Tag.F4) ιK
  have hinj := baseChangeGL_injective (τ := Tag.F4) ι
  have hcomp : ∀ r : ModGL .F4 K, baseChangeGL ι (baseChangeGL (algebraMap K K₄) r) =
      baseChangeGL ιK r := fun r => by
    rw [baseChangeGL_baseChangeGL, hι, hιK, ← IsScalarTower.algebraMap_eq]
  rw [hΓ] at hxΓ
  obtain ⟨x₁, hx₁, hx₁x⟩ := hxΓ
  set x₀ : adjointGroup .F4 K := ⟨x₁, hx₁⟩ with hx₀
  have hx₀x : baseChangeGL ιK (x₀ : ModGL .F4 K) = g * x * g⁻¹ := by
    change baseChangeGL ιK x₁ = g * x * g⁻¹
    rw [← hx₁x]
    change baseChangeGL ιK x₁ = g * (g⁻¹ * baseChangeGL ιK x₁ * g⁻¹⁻¹) * g⁻¹
    group
  have hCx := map_centralizer_eq_map_conj K Ω g Γ hΓ x h y hy Γ₁ D hΓ₁ hD x₀ hx₀x
  refine ⟨x₀, hx₀x, hCx, ?_⟩
  obtain ⟨g₀, hg₀, rfl⟩ := hgK₄
  obtain ⟨h₀, hh₀, rfl⟩ := hhK₄
  set b₀ := g₀ * h₀⁻¹ * a with hb₀
  have hb₀C : b₀ ∈ adjointGroup .F4 K₄ := mul_mem (mul_mem hg₀ (inv_mem hh₀)) ha
  set ρK := ((rootSL2 .F4 K₄ (Pi.single 1 1)).comp
    (Matrix.SpecialLinearGroup.map (algebraMap K K₄))).range with hρK
  have hclaim : ∀ s ∈ ρK, ∃ r ∈ Subgroup.centralizer {x₀},
      baseChangeGL ιK (r : ModGL .F4 K) = baseChangeGL ι (b₀ * s * b₀⁻¹) := by
    rintro _ ⟨A, rfl⟩
    have hmem : baseChangeGL ι (b₀ * (rootSL2 .F4 K₄ (Pi.single 1 1)
        (Matrix.SpecialLinearGroup.map (algebraMap K K₄) A)) * b₀⁻¹) ∈
          D.map (MulAut.conj (baseChangeGL ι g₀ * (baseChangeGL ι h₀)⁻¹)).toMonoidHom := by
      refine ⟨_, hρD A, ?_⟩
      change baseChangeGL ι g₀ * (baseChangeGL ι h₀)⁻¹ * baseChangeGL ι (a *
          rootSL2 .F4 K₄ (Pi.single 1 1) (Matrix.SpecialLinearGroup.map (algebraMap K K₄) A) *
            a⁻¹) * (baseChangeGL ι g₀ * (baseChangeGL ι h₀)⁻¹)⁻¹ = _
      rw [hb₀]
      simp only [map_mul, map_inv]
      group
    rw [← hCx] at hmem
    obtain ⟨r, hr, hre⟩ := hmem
    exact ⟨r, hr, hre⟩
  refine ⟨(ρK.comap ((MulAut.conj b₀⁻¹).toMonoidHom.comp ((baseChangeGL (algebraMap K K₄)).comp
    (adjointGroup .F4 K).subtype))) ⊓ Subgroup.centralizer {x₀}, inf_le_right, b₀⁻¹,
    inv_mem hb₀C, ?_⟩
  apply le_antisymm
  · rintro _ ⟨_, ⟨r, hr, rfl⟩, rfl⟩
    exact (Subgroup.mem_inf.1 hr).1
  · intro s hs
    obtain ⟨r, hr, hre⟩ := hclaim s hs
    have hr' : baseChangeGL (algebraMap K K₄) (r : ModGL .F4 K) = b₀ * s * b₀⁻¹ :=
      hinj (by rw [hcomp, hre])
    have hks : b₀⁻¹ * baseChangeGL (algebraMap K K₄) (r : ModGL .F4 K) * b₀⁻¹⁻¹ = s := by
      rw [hr']
      group
    refine ⟨_, ⟨r, Subgroup.mem_inf.2 ⟨?_, hr⟩, rfl⟩, ?_⟩
    · change b₀⁻¹ * baseChangeGL (algebraMap K K₄) (r : ModGL .F4 K) * b₀⁻¹⁻¹ ∈ ρK
      rw [hks]
      exact hs
    · exact hks

theorem even_F4_cyclotomic_four_nonregular_derived_centralizer {f : ℕ} (hf : 1 ≤ f)
    (K : Type) [Field K] (hK : Nat.card K = 2 ^ f) (Ω : Type) [Field Ω] [Algebra K Ω]
    [IsAlgClosure K Ω] (F : Ω →+* Ω) (hF : ∀ c, F c = c ^ Nat.card K) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (K₄ : IntermediateField K Ω) (hK₄ : Module.finrank K K₄ = 4)
    (n g : ModGL .F4 Ω) (hn : n = canonicalRep (coxeterSystem .F4) Ω (f4Coxeter ^ 3))
    (hg : g ∈ adjointGroup .F4 Ω) (hgn : g⁻¹ * Units.map (entrywiseHom F) g = n)
    (Γ T₀ : Subgroup (ModGL .F4 Ω)) (hΓ : Γ = conjEntrywiseImage K g⁻¹)
    (hT₀ : T₀ = torusGroup .F4 Ω ⊓ Γ) (x : ModGL .F4 Ω) (hx : x ∈ T₀) (hxp : orderOf x = p)
    (u : WeylGroup .F4) (ε : ℤ) (hε : ε = 1 ∨ ε = -1)
    (hu : (fun α => u • α) '' {α | IsRoot .F4 α ∧ torusRootChar x α = 1} =
      parabolicRoots .F4 {f4Index 1, f4Index 2})
    (huw : ∀ z ∈ Submodule.span ℝ (ofLattice '' parabolicRoots .F4 {f4Index 1, f4Index 2}),
      weylAct .F4 (u * f4Coxeter ^ 3 * u⁻¹) z =
        weylAct .F4 ((simple .F4 (f4Index 1) * simple .F4 (f4Index 2)) ^ ε) z)
    (h y : ModGL .F4 Ω) (hh : h = canonicalRep (coxeterSystem .F4) Ω u) (hy : y = h * x * h⁻¹)
    (Γ₁ D R : Subgroup (ModGL .F4 Ω)) (hΓ₁ : Γ₁ = Γ.map (MulAut.conj h).toMonoidHom)
    (hD : D = Γ₁ ⊓ Subgroup.centralizer {y}) (hR : R = ⁅D, D⁆) :
    (((adjointGroup .F4 K₄).map (baseChangeGL (algebraMap K₄ Ω)) ⊓ Subgroup.centralizer {y} :
        Subgroup (ModGL .F4 Ω)) : Set (ModGL .F4 Ω)) =
      ((torusGroup .F4 K₄).map (baseChangeGL (algebraMap K₄ Ω)) : Set (ModGL .F4 Ω)) *
        ((subsystemGroup .F4 K₄ {1, 2}).map (baseChangeGL (algebraMap K₄ Ω)) :
          Set (ModGL .F4 Ω)) ∧
    ∃ Z₀ P : Subgroup (ModGL .F4 Ω),
      Z₀ ≤ (torusGroup .F4 K₄).map (baseChangeGL (algebraMap K₄ Ω)) ∧ Odd (Nat.card Z₀) ∧
      (∃ a ∈ subsystemGroup .F4 K₄ {1, 2},
        (∀ z, z ∈ P ↔ ∃ y' ∈ subsystemGroup .F4 K {1, 2},
          z = baseChangeGL (algebraMap K₄ Ω) a * baseChangeGL (algebraMap K Ω) y' *
            (baseChangeGL (algebraMap K₄ Ω) a)⁻¹) ∧
        ∀ A : SL2 K, baseChangeGL (algebraMap K₄ Ω) (a * rootSL2 .F4 K₄ (Pi.single 1 1)
          (Matrix.SpecialLinearGroup.map (algebraMap K K₄) A) * a⁻¹) ∈ P) ∧
      (∃ e : Z₀ × P ≃* D, ∀ q, (e q : ModGL .F4 Ω) = q.1 * q.2) ∧
      (Subgroup.center D).map D.subtype = Z₀ ∧
      (4 ≤ Nat.card K → R = P ∧ Nonempty (P ≃* EvenQuartic.spJ K) ∧ IsSimpleGroup R ∧
        Group.IsPerfect R ∧ ∃ r₁ r₂ : R, r₁ * r₂ ≠ r₂ * r₁) ∧
      (Nat.card K = 2 → R = ⁅P, P⁆ ∧
        (∃ e : P ≃* Equiv.Perm (Fin 6),
          ∀ z : P, (z : ModGL .F4 Ω) ∈ R ↔ e z ∈ alternatingGroup (Fin 6)) ∧
        IsSimpleGroup R ∧ Group.IsPerfect R ∧ ∃ r₁ r₂ : R, r₁ * r₂ ≠ r₂ * r₁) ∧
      CFSG.layer R = ⊤ ∧ R ≠ ⊥ ∧ D ⊓ Subgroup.centralizer (R : Set (ModGL .F4 Ω)) = Z₀ ∧
      ∃ x₀ : adjointGroup .F4 K,
        baseChangeGL (algebraMap K Ω) (x₀ : ModGL .F4 K) = g * x * g⁻¹ ∧
        (Subgroup.centralizer {x₀}).map
            ((baseChangeGL (algebraMap K Ω)).comp (adjointGroup .F4 K).subtype) =
          D.map (MulAut.conj (g * h⁻¹)).toMonoidHom ∧
        ∃ R₀ : Subgroup (adjointGroup .F4 K), R₀ ≤ Subgroup.centralizer {x₀} ∧
          ∃ k ∈ adjointGroup .F4 K₄,
            (R₀.map ((baseChangeGL (algebraMap K K₄)).comp (adjointGroup .F4 K).subtype)).map
                (MulAut.conj k).toMonoidHom =
              ((rootSL2 .F4 K₄ (Pi.single 1 1)).comp
                (Matrix.SpecialLinearGroup.map (algebraMap K K₄))).range := by
  classical
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  obtain ⟨hC, σ, hσ, hv, hDeq⟩ := cyclotomic_four_centralizer_and_D K Ω F hF hp hp3 K₄ hK₄ n g
    hn hg hgn Γ T₀ hΓ hT₀ x hx hxp u ε hu huw h y hh hy Γ₁ D hΓ₁ hD
  obtain ⟨Z₀, P, hZ₀H, hZ₀odd, ⟨a, ha, hPmem, hρP⟩, hprod, hcenter, h4, h2, hlayer, hRbot,
    hcent⟩ := cyclotomic_four_D_structure K Ω K₄ hK₄ σ hσ (u * f4Coxeter ^ 3 * u⁻¹) ε hε hv D R
      hDeq hR
  obtain ⟨-, hCA⟩ := F4_cyclotomic_four_torus_and_regular_prime_centralizers K Ω F hF n hn
  obtain ⟨-, -, -, -, hchar⟩ := hCA g hg hgn Γ T₀ (T₀.map (MulAut.conj g).toMonoidHom) hΓ hT₀ rfl
  obtain ⟨hgK₄, -, -, -, -⟩ := hchar ‹_› K₄ hK₄
  have hxΓ : x ∈ Γ := (hT₀ ▸ hx).2
  have hhK₄ : h ∈ (adjointGroup .F4 K₄).map (baseChangeGL (algebraMap K₄ Ω)) :=
    ⟨_, canonicalRep_mem_adjointGroup _ K₄ u, by rw [hh]; exact baseChangeGL_canonicalRep _ u⟩
  obtain ⟨e, he⟩ := hprod
  have hPD : P ≤ D := fun z hz => by
    have := (e (1, ⟨z, hz⟩)).2
    rwa [he, Subgroup.coe_one, one_mul] at this
  have hρD : ∀ A : SL2 K, baseChangeGL (algebraMap K₄ Ω) (a * rootSL2 .F4 K₄ (Pi.single 1 1)
      (Matrix.SpecialLinearGroup.map (algebraMap K K₄) A) * a⁻¹) ∈ D := fun A => hPD (hρP A)
  exact ⟨hC, Z₀, P, hZ₀H, hZ₀odd, ⟨a, ha, hPmem, hρP⟩, ⟨e, he⟩, hcenter, h4, h2, hlayer, hRbot,
    hcent, cyclotomic_four_transport K Ω K₄ g hgK₄ Γ hΓ x hxΓ h y hhK₄ hy Γ₁ D hΓ₁ hD a
      (subsystemGroup_le_adjointGroup_of_any _ ha) hρD⟩

end CFSG.RankThree.Chevalley
