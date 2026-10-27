module

public import CFSG.LocalAnalysis.StandardType.GGRCWeylCard
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthWeylOrdD
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallPosModelled
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini
public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs

public section

namespace CFSG.TwoNodeSmall

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem pws_card_coxeterA (n : ℕ) :
    Nat.card (CoxeterMatrix.A n).Group = natFact (n + 1) := by
  rw [CFSG.StandardType.l05nK3a_card_coxeterA n, ← natFact_eq]

theorem pws_card_coxeterB (n : ℕ) (hn : 2 ≤ n) :
    Nat.card (CoxeterMatrix.B n).Group = 2 ^ n * natFact n := by
  rw [le_antisymm (CFSG.StandardType.card_coxeterB_le n)
        (CFSG.StandardType.SpFrame.card_coxeterB_ge n hn), ← natFact_eq]

theorem pws_card_coxeterD (n : ℕ) (hn : 4 ≤ n) :
    Nat.card (CFSG.StandardType.ggCoxeterMatrixD n).Group = 2 ^ (n - 1) * natFact n := by
  rw [CFSG.StandardType.OrthF3.card_coxeterD_eq n hn, ← natFact_eq]

theorem pws_card_coxeterE7 :
    Nat.card (CoxeterMatrix.E₇).Group = 2903040 := by
  have hc : CFSG.Blueprint.Chevalley.Tag.cartan .E7 = CartanMatrix.E 7 :=
    CFSG.LieType.Chevalley.cartanE_eq 7
  have hmat : CoxeterMatrix.E₇ =
      CFSG.LieType.RootSystem.coxeterMatrix (CFSG.LieType.Chevalley.isFiniteType_cartan .E7) := by
    have h := CFSG.StandardType.coxeterMatrix_eq_of_ggIntCartan
      (C := CFSG.Blueprint.Chevalley.Tag.cartan .E7)
      (M := CoxeterMatrix.E₇) (CFSG.LieType.Chevalley.isFiniteType_cartan .E7)
      (hc.symm ▸ CFSG.StandardType.ggIntCartan_E₇)
    exact h.symm
  have hgroup : CFSG.LieType.Chevalley.WeylGroup .E7 = (CoxeterMatrix.E₇).Group :=
    congrArg CoxeterMatrix.Group hmat.symm
  have hcardW : Nat.card (CFSG.LieType.Chevalley.WeylGroup .E7) =
      Nat.card (CoxeterMatrix.E₇).Group := Nat.card_congr (Equiv.cast hgroup)
  rw [← hcardW]
  exact CFSG.StandardType.NoOffExc.card_weyl_E7

theorem pws_finite_coxeterA (n : ℕ) : Finite (CoxeterMatrix.A n).Group := by
  apply Nat.finite_of_card_ne_zero
  rw [pws_card_coxeterA n, natFact_eq]
  exact Nat.factorial_ne_zero _

theorem pws_finite_coxeterB (n : ℕ) (hn : 2 ≤ n) : Finite (CoxeterMatrix.B n).Group := by
  apply Nat.finite_of_card_ne_zero
  rw [pws_card_coxeterB n hn, natFact_eq]
  exact Nat.mul_ne_zero (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0)) (Nat.factorial_ne_zero n)

theorem pws_finite_coxeterD (n : ℕ) (hn : 4 ≤ n) : Finite (CFSG.StandardType.ggCoxeterMatrixD n).Group := by
  apply Nat.finite_of_card_ne_zero
  rw [pws_card_coxeterD n hn, natFact_eq]
  exact Nat.mul_ne_zero (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0)) (Nat.factorial_ne_zero n)

theorem pws_finite_coxeterE7 :
    Finite (CoxeterMatrix.E₇).Group := by
  apply Nat.finite_of_card_ne_zero
  rw [pws_card_coxeterE7]
  norm_num

theorem pws_reindex_refl {ι : Type} (N : CoxeterMatrix ι) :
    N.reindex (Equiv.refl ι) = N := by
  apply CoxeterMatrix.ext
  funext i j
  simp only [CoxeterMatrix.reindex_apply, Equiv.refl_symm, Equiv.refl_apply]

theorem pws_ggIsWeylMatrix_A (n : ℕ) (hn : 1 ≤ n) :
    CFSG.StandardType.GGIsWeylMatrix (CoxeterMatrix.A n) :=
  Or.inl ⟨n, Equiv.refl (Fin n), hn, Or.inl (pws_reindex_refl _).symm⟩

theorem pws_ggIsWeylMatrix_B (n : ℕ) (hn : 2 ≤ n) :
    CFSG.StandardType.GGIsWeylMatrix (CoxeterMatrix.B n) :=
  Or.inl ⟨n, Equiv.refl (Fin n), le_trans (by norm_num : 1 ≤ 2) hn,
    Or.inr (Or.inl ⟨hn, (pws_reindex_refl _).symm⟩)⟩

theorem pws_ggIsWeylMatrix_D (n : ℕ) (hn : 4 ≤ n) :
    CFSG.StandardType.GGIsWeylMatrix (CFSG.StandardType.ggCoxeterMatrixD n) :=
  Or.inl ⟨n, Equiv.refl (Fin n), le_trans (by norm_num : 1 ≤ 4) hn,
    Or.inr (Or.inr ⟨hn, (pws_reindex_refl _).symm⟩)⟩

theorem pws_ggIsWeylMatrix_E7 : CFSG.StandardType.GGIsWeylMatrix CoxeterMatrix.E₇ :=
  Or.inr (Or.inr (Or.inl ⟨Equiv.refl (Fin 7), (pws_reindex_refl _).symm⟩))

private theorem pws_sigma_sq {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {ι : Type} (σ : ι → V ≃ₗ[ZMod p] V) (c : ι → V)
    (β : ι → Module.Dual (ZMod p) V)
    (hσ : ∀ i v, σ i v = v - β i v • c i) (hβc : ∀ i, β i (c i) = 2) (i : ι) :
    σ i * σ i = 1 := by
  ext v
  change σ i (σ i v) = v
  have hβσ : β i (σ i v) = β i v - β i v * β i (c i) := by
    rw [hσ i v, map_sub, map_smul, smul_eq_mul]
  rw [hσ i (σ i v), hβσ, hβc i, hσ i v]
  have hs : (β i v - β i v * 2 : ZMod p) = -(β i v) := by ring
  rw [hs, neg_smul, sub_neg_eq_add]
  exact sub_add_cancel _ _

private theorem pws_sigma_sub_range {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {ι : Type} (σ : ι → V ≃ₗ[ZMod p] V) (c : ι → V)
    (β : ι → Module.Dual (ZMod p) V)
    (hσ : ∀ i v, σ i v = v - β i v • c i) (i : ι) :
    LinearMap.range ((σ i : V →ₗ[ZMod p] V) - LinearMap.id) ≤
      Submodule.span (ZMod p) ({c i} : Set V) := by
  rintro x ⟨v, rfl⟩
  rw [LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply, hσ i v]
  have h : v - β i v • c i - v = -(β i v) • c i := by module
  rw [h]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton (c i)))

private theorem pws_isRefl {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {ι : Type} (σ : ι → V ≃ₗ[ZMod p] V) (c : ι → V)
    (β : ι → Module.Dual (ZMod p) V)
    (hσ : ∀ i v, σ i v = v - β i v • c i) (hσ2 : ∀ i, σ i * σ i = 1)
    (hσne : ∀ i, σ i ≠ 1) (i : ι) :
    CFSG.StandardType.ZS.IsRefl p (σ i) := by
  refine ⟨hσ2 i, ?_⟩
  have hci : c i ≠ 0 := by
    intro hc
    apply hσne i
    ext v
    simp [hσ i v, hc]
  have hsub := pws_sigma_sub_range σ c β hσ i
  have hrange_ne : LinearMap.range ((σ i : V →ₗ[ZMod p] V) - LinearMap.id) ≠ ⊥ := by
    intro hbot
    apply hσne i
    ext v
    have hmem := LinearMap.mem_range_self ((σ i : V →ₗ[ZMod p] V) - LinearMap.id) v
    rw [hbot] at hmem
    have hv : σ i v - v = 0 := by simpa using hmem
    exact sub_eq_zero.mp hv
  have hrange : LinearMap.range ((σ i : V →ₗ[ZMod p] V) - LinearMap.id) =
      Submodule.span (ZMod p) ({c i} : Set V) := by
    apply le_antisymm hsub
    rw [Submodule.span_singleton_le_iff_mem]
    obtain ⟨w, hwS, hw0⟩ := (Submodule.ne_bot_iff _).mp hrange_ne
    have hwspan : w ∈ Submodule.span (ZMod p) ({c i} : Set V) := hsub hwS
    rw [Submodule.mem_span_singleton] at hwspan
    obtain ⟨a, ha⟩ := hwspan
    have ha0 : a ≠ 0 := by
      intro ha0
      rw [ha0, zero_smul] at ha
      exact hw0 ha.symm
    have hcw : c i = a⁻¹ • w := by
      rw [← ha, smul_smul, inv_mul_cancel₀ ha0, one_smul]
    rw [hcw]
    exact Submodule.smul_mem _ _ hwS
  rw [hrange]
  exact finrank_span_singleton hci

theorem pws_linWeyl_of_simple_system {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {ι : Type} (M : CoxeterMatrix ι)
    (hM : CFSG.StandardType.GGIsWeylMatrix M) [Finite M.Group]
    (R : Subgroup (V ≃ₗ[ZMod p] V)) (σ : ι → V ≃ₗ[ZMod p] V)
    (hσR : ∀ i, σ i ∈ R) (c : ι → V) (β : ι → Module.Dual (ZMod p) V)
    (hσ : ∀ i v, σ i v = v - β i v • c i) (hβc : ∀ i, β i (c i) = 2)
    (hrel : ∀ i j, i ≠ j → (σ i * σ j) ^ (M i j) = 1)
    (hgen : R ≤ Subgroup.closure (Set.range σ)) (hcard : Nat.card M.Group ≤ Nat.card R) :
    CFSG.StandardType.ZS.LinWeyl p R := by
  have hσ2 : ∀ i, σ i * σ i = 1 := fun i => pws_sigma_sq σ c β hσ hβc i
  have hfam : CoxeterMatrix.IsLiftable M σ := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rw [CoxeterMatrix.diagonal M i, pow_one]
      exact hσ2 i
    · exact hrel i j hij
  let f₀ : M.Group →* (V ≃ₗ[ZMod p] V) :=
    M.toCoxeterSystem.lift ⟨σ, hfam⟩
  have hf₀ : ∀ i, f₀ (M.toCoxeterSystem.simple i) = σ i := by
    intro i
    exact M.toCoxeterSystem.lift_apply_simple hfam i
  have hclosure_le : Subgroup.closure (Set.range σ) ≤ R := by
    refine (Subgroup.closure_le R).mpr ?_
    rintro _ ⟨i, rfl⟩
    exact hσR i
  have hR_eq : R = Subgroup.closure (Set.range σ) := le_antisymm hgen hclosure_le
  have hgen_top : Subgroup.closure (Set.range M.toCoxeterSystem.simple) = ⊤ :=
    M.toCoxeterSystem.subgroup_closure_range_simple
  have hrange : f₀.range = Subgroup.closure (Set.range σ) := by
    calc f₀.range = (⊤ : Subgroup M.Group).map f₀ := (Subgroup.map_top f₀).symm
      _ = (Subgroup.closure (Set.range M.toCoxeterSystem.simple)).map f₀ := by rw [← hgen_top]
      _ = Subgroup.closure (f₀ '' Set.range M.toCoxeterSystem.simple) :=
          MonoidHom.map_closure f₀ _
      _ = Subgroup.closure (Set.range (f₀ ∘ M.toCoxeterSystem.simple)) := by
          rw [← Set.range_comp]
      _ = Subgroup.closure (Set.range σ) := by
          apply congrArg Subgroup.closure
          apply congrArg Set.range
          funext i
          exact hf₀ i
  have hmem : ∀ g : M.Group, f₀ g ∈ R := by
    intro g
    rw [hR_eq, ← hrange]
    exact ⟨g, rfl⟩
  let f₁ : M.Group →* R := MonoidHom.codRestrict f₀ R hmem
  have hf₁ : ∀ i, f₁ (M.toCoxeterSystem.simple i) = ⟨σ i, hσR i⟩ := by
    intro i
    apply Subtype.ext
    change f₀ (M.toCoxeterSystem.simple i) = σ i
    exact hf₀ i
  have hsurj : Function.Surjective f₁ := by
    intro r
    have hr : (r : V ≃ₗ[ZMod p] V) ∈ Subgroup.closure (Set.range σ) := by
      rw [← hR_eq]
      exact r.2
    rw [← hrange] at hr
    obtain ⟨g, hg⟩ := hr
    refine ⟨g, ?_⟩
    apply Subtype.ext
    change f₀ g = (r : V ≃ₗ[ZMod p] V)
    exact hg
  haveI : Fintype M.Group := Fintype.ofFinite _
  haveI : Finite R := Finite.of_surjective f₁ hsurj
  haveI : Fintype R := Fintype.ofFinite _
  have hcard_eq : Fintype.card M.Group = Fintype.card R := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact le_antisymm hcard (Nat.card_le_card_of_surjective f₁ hsurj)
  have hbij : Function.Bijective f₁ :=
    (Fintype.bijective_iff_surjective_and_card f₁).mpr ⟨hsurj, hcard_eq⟩
  let f : M.Group ≃* R := MulEquiv.ofBijective f₁ hbij
  have hσne : ∀ i, σ i ≠ 1 := by
    intro i hσi
    have hsimple_ne : M.toCoxeterSystem.simple i ≠ 1 := by
      intro h
      have h1 := M.toCoxeterSystem.length_simple i
      rw [h] at h1
      simp at h1
    have hf₁i : f₁ (M.toCoxeterSystem.simple i) = 1 := by
      apply Subtype.ext
      change f₀ (M.toCoxeterSystem.simple i) = 1
      rw [hf₀ i, hσi]
    have heq : f₁ (M.toCoxeterSystem.simple i) = f₁ 1 := by rw [hf₁i, map_one]
    exact hsimple_ne (hbij.1 heq)
  refine ⟨ι, M, hM, f, ?_⟩
  intro i
  have hmi : f (M.simple i) = ⟨σ i, hσR i⟩ := by
    apply Subtype.ext
    change f₀ (M.simple i) = σ i
    rw [show M.simple i = M.toCoxeterSystem.simple i from by
      rw [CoxeterMatrix.toCoxeterSystem_simple]]
    exact hf₀ i
  have hfi : (f (M.simple i) : V ≃ₗ[ZMod p] V) = σ i := congrArg Subtype.val hmi
  rw [hfi]
  exact pws_isRefl σ c β hσ hσ2 hσne i

end CFSG.TwoNodeSmall
