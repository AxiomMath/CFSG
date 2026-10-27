module

public import CFSG.RankThree.Chevalley.SteinbergCFERootSL2Traces
public import CFSG.LieType.Chevalley.OrdinaryEOuterOrder
public import CFSG.LieType.Chevalley.OddF4CosetDescent

public section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem trace_apply_of_expression {τ : Tag} {K : Type} [Field K] (η : MulAut (adjointGroup τ K))
    (g : adjointGroup τ K) (a : Fin τ.rank → Kˣ) (σ : K ≃+* K) (ε : ℕ)
    (hexpr : ∀ x : adjointGroup τ K, (η x : ModGL τ K) = (g : ModGL τ K) * rootDiagUnit τ a *
      exactQ τ K ε * Units.map (entrywiseHom σ.toRingHom) (x : ModGL τ K) *
        (exactQ τ K ε)⁻¹ * (rootDiagUnit τ a)⁻¹ * (g : ModGL τ K)⁻¹)
    (x : adjointGroup τ K) :
    LinearMap.trace K (RootModule τ K)
        ((η x : ModGL τ K) : Module.End K (RootModule τ K)) =
      σ (LinearMap.trace K (RootModule τ K)
        ((x : ModGL τ K) : Module.End K (RootModule τ K))) := by
  have e1 : (η x : ModGL τ K) =
      ((g : ModGL τ K) * rootDiagUnit τ a * exactQ τ K ε) *
        Units.map (entrywiseHom σ.toRingHom) (x : ModGL τ K) *
        ((g : ModGL τ K) * rootDiagUnit τ a * exactQ τ K ε)⁻¹ := by
    rw [hexpr x]
    simp only [mul_inv_rev, mul_assoc]
  rw [e1, Units.val_mul, Units.val_mul, LinearMap.trace_conj,
    units_map_entrywiseHom_eq_baseChangeGL, trace_baseChangeGL]
  rfl

theorem ringEquiv_eq_one_of_fixes_root_SL2_traces {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {K : Type} [Field K] [Finite K] (M : Type) [Field M] [Algebra K M] (i : Fin τ.rank)
    (A : GL (Fin 2) M) (h : ModGL τ M) (σ : K ≃+* K)
    (hσ : ∀ B : SL2 K, ∃ y : K, σ y = y ∧ algebraMap K M y = LinearMap.trace M (RootModule τ M)
      ((h * simpleRootSL2 τ M i (conjGL A (Matrix.SpecialLinearGroup.map (algebraMap K M) B)) *
        h⁻¹ : ModGL τ M) : Module.End M (RootModule τ M))) :
    σ = 1 := by
  have hcl := (ordinary_E_root_SL2_full_module_traces_all_characteristics τ hτ).2 K M i A h
  have hS : {x : M | ∃ B : SL2 K, x = LinearMap.trace M (RootModule τ M)
      ((h * simpleRootSL2 τ M i (conjGL A (Matrix.SpecialLinearGroup.map (algebraMap K M) B)) *
        h⁻¹ : ModGL τ M) : Module.End M (RootModule τ M))} ⊆
      (((RingHom.eqLocusField σ.toRingHom (RingHom.id K)).map (algebraMap K M) :
        Subfield M) : Set M) := by
    rintro _ ⟨B, rfl⟩
    obtain ⟨y, hy, hyB⟩ := hσ B
    exact ⟨y, hy, hyB⟩
  have hle := Subfield.closure_le.2 hS
  rw [hcl] at hle
  refine RingEquiv.ext fun c => ?_
  obtain ⟨y, hy, hyc⟩ := hle ⟨c, rfl⟩
  have hyc' : y = c := (algebraMap K M).injective hyc
  subst hyc'
  exact hy

theorem ordinary_E_descended_root_SL2_pointwise_automorphisms_field_free (τ : Tag)
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (K : Type) [Field K] [Finite K]
    (M : Type) [Field M] [Algebra K M] (i : Fin τ.rank) (A : GL (Fin 2) M) (h : ModGL τ M)
    (hU : ∀ B : SL2 K, h * simpleRootSL2 τ M i (conjGL A
        (Matrix.SpecialLinearGroup.map (algebraMap K M) B)) * h⁻¹ ∈
          (adjointGroup τ K).map (baseChangeGL (algebraMap K M)))
    (Z : Subgroup (MulAut (adjointGroup τ K)))
    (hZ : ∀ η ∈ Z, ∀ (u : adjointGroup τ K) (B : SL2 K),
      baseChangeGL (algebraMap K M) (u : ModGL τ K) =
        h * simpleRootSL2 τ M i (conjGL A (Matrix.SpecialLinearGroup.map (algebraMap K M) B)) *
          h⁻¹ → η u = u) :
    (∀ η ∈ Z, ∀ (g : adjointGroup τ K) (a : Fin τ.rank → Kˣ) (σ : K ≃+* K)
        (ε : Fin (exactE τ)),
      (∀ x : adjointGroup τ K, (η x : ModGL τ K) = (g : ModGL τ K) * rootDiagUnit τ a *
        exactQ τ K ε * Units.map (entrywiseHom σ.toRingHom) (x : ModGL τ K) *
          (exactQ τ K ε)⁻¹ * (rootDiagUnit τ a)⁻¹ * (g : ModGL τ K)⁻¹) → σ = 1) ∧
    (τ = .E6 → Nat.card (Z.map (QuotientGroup.mk' (inner (adjointGroup τ K)))) ∣ 6) ∧
    (τ = .E7 → Nat.card (Z.map (QuotientGroup.mk' (inner (adjointGroup τ K)))) ∣ 2) ∧
    (τ = .E8 → ∀ η ∈ Z, η ∈ inner (adjointGroup τ K)) := by
  classical
  have hfield : ∀ η ∈ Z, ∀ (g : adjointGroup τ K) (a : Fin τ.rank → Kˣ) (σ : K ≃+* K)
      (ε : Fin (exactE τ)),
      (∀ x : adjointGroup τ K, (η x : ModGL τ K) = (g : ModGL τ K) * rootDiagUnit τ a *
        exactQ τ K ε * Units.map (entrywiseHom σ.toRingHom) (x : ModGL τ K) *
          (exactQ τ K ε)⁻¹ * (rootDiagUnit τ a)⁻¹ * (g : ModGL τ K)⁻¹) → σ = 1 := by
    intro η hη g a σ ε hexpr
    refine ringEquiv_eq_one_of_fixes_root_SL2_traces hτ M i A h σ fun B => ?_
    obtain ⟨y, hyC, hy⟩ := hU B
    have hfix : η ⟨y, hyC⟩ = ⟨y, hyC⟩ := hZ η hη ⟨y, hyC⟩ B hy
    have h1 := trace_apply_of_expression η g a σ (ε : ℕ) hexpr ⟨y, hyC⟩
    rw [hfix] at h1
    refine ⟨LinearMap.trace K (RootModule τ K)
      ((y : ModGL τ K) : Module.End K (RootModule τ K)), h1.symm, ?_⟩
    rw [← hy, trace_baseChangeGL]
  obtain ⟨Θ, -, hexprΘ, hkerΘ, -, -⟩ := ordinary_E_field_graph_quotient_and_involutions τ hτ K
  obtain ⟨Φ₀, -, hkerΦ₀, hdvd₀⟩ := exists_outer_hom_E (K := K) hτ
  have hkerΘ' : ∀ α : MulAut (adjointGroup τ K),
      α ∈ Θ.ker ↔ ∃ (g : adjointGroup τ K) (a : Fin τ.rank → Kˣ),
        α = MulAut.conj g * rootDiagAut τ K a := by
    intro α
    rw [hkerΘ]
    constructor
    · rintro ⟨g, a, h⟩
      refine ⟨g, a, MulEquiv.ext fun x => Subtype.ext ?_⟩
      rw [h x, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
        coe_rootDiagAut, Subgroup.coe_inv]
      simp only [mul_assoc]
    · rintro ⟨g, a, rfl⟩
      refine ⟨g, a, fun x => ?_⟩
      rw [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
        coe_rootDiagAut, Subgroup.coe_inv]
      simp only [mul_assoc]
  have h1 : rootDiagAut τ K 1 = 1 := (rootDiagAutHom τ K).map_one
  have hinn : inner (adjointGroup τ K) ≤ Θ.ker := by
    rintro _ ⟨g, rfl⟩
    exact (hkerΘ' _).2 ⟨g, 1, by rw [h1, mul_one]⟩
  set ρ := (QuotientGroup.mk' (inner (adjointGroup τ K))).comp (rootDiagAutHom τ K) with hρ
  set Φ := QuotientGroup.lift (inner (adjointGroup τ K)) Θ hinn with hΦ
  have hΦmk : ∀ α : MulAut (adjointGroup τ K), Φ (QuotientGroup.mk α) = Θ α := fun α =>
    QuotientGroup.lift_mk _ hinn α
  have hkerΦ : Φ.ker = ρ.range := by
    refine le_antisymm (fun x hx => ?_) ?_
    · obtain ⟨α, rfl⟩ := QuotientGroup.mk'_surjective (inner (adjointGroup τ K)) x
      rw [MonoidHom.mem_ker, QuotientGroup.mk'_apply, hΦmk] at hx
      obtain ⟨g, a, rfl⟩ := (hkerΘ' _).1 hx
      refine ⟨a, ?_⟩
      change (QuotientGroup.mk (rootDiagAut τ K a) : Outer (adjointGroup τ K)) =
        QuotientGroup.mk' (inner (adjointGroup τ K)) (MulAut.conj g * rootDiagAut τ K a)
      rw [map_mul, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff
        (N := inner (adjointGroup τ K)) (MulAut.conj g)).2 (MonoidHom.mem_range.2 ⟨g, rfl⟩),
        one_mul]
      rfl
    · rintro _ ⟨a, rfl⟩
      change Φ (QuotientGroup.mk (rootDiagAut τ K a)) = 1
      rw [hΦmk]
      exact (hkerΘ' _).2 ⟨1, a, by rw [map_one, one_mul]⟩
  have hD : Nat.card Φ.ker ∣ τ.cartan.det.natAbs := by
    rw [hkerΦ, ← hkerΦ₀]
    exact hdvd₀
  set Zb : Subgroup (Outer (adjointGroup τ K)) :=
    Z.map (QuotientGroup.mk' (inner (adjointGroup τ K))) with hZb
  have hΦ1 : ∀ x ∈ Zb, (Φ x).1 = 1 := by
    rintro _ ⟨η, hη, rfl⟩
    obtain ⟨g, a, σ, ε, hex⟩ := exists_conj_mul_exactNormalAut hτ η
    have hexpr : ∀ x : adjointGroup τ K, (η x : ModGL τ K) = (g : ModGL τ K) *
        rootDiagUnit τ a * exactQ τ K ε * Units.map (entrywiseHom σ.toRingHom) (x : ModGL τ K) *
          (exactQ τ K ε)⁻¹ * (rootDiagUnit τ a)⁻¹ * (g : ModGL τ K)⁻¹ := by
      intro x
      rw [hex, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
        coe_exactNormalAut, Subgroup.coe_inv]
      simp only [mul_assoc]
    rw [QuotientGroup.mk'_apply, hΦmk, hexprΘ η g a σ ε hexpr, hfield η hη g a σ ε hexpr]
  set ψ : Zb →* Multiplicative (ZMod (exactE τ)) :=
    (MonoidHom.snd (RingAut K) (Multiplicative (ZMod (exactE τ)))).comp (Φ.comp Zb.subtype) with hψ
  have hker : Nat.card ψ.ker ∣ Nat.card Φ.ker := by
    have hle : ψ.ker.map Zb.subtype ≤ Φ.ker := by
      rintro _ ⟨x, hx, rfl⟩
      have hx' : (Φ (x : Outer (adjointGroup τ K))).2 = 1 := hx
      exact Prod.ext (hΦ1 x.1 x.2) hx'
    have := Subgroup.card_dvd_of_le hle
    rwa [Subgroup.card_map_of_injective Zb.subtype_injective] at this
  have hrange : Nat.card ψ.range ∣ exactE τ := by
    have h2 := Subgroup.card_subgroup_dvd_card ψ.range
    rwa [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod] at h2
  have hcardZb : Nat.card Zb ∣ τ.cartan.det.natAbs * exactE τ := by
    rw [← Subgroup.card_ker_mul_card_range ψ]
    exact Nat.mul_dvd_mul (hker.trans hD) hrange
  refine ⟨hfield, ?_, ?_, ?_⟩
  · rintro rfl
    rw [det_cartan_E6] at hcardZb
    exact hcardZb
  · rintro rfl
    rw [det_cartan_E7] at hcardZb
    exact hcardZb
  · rintro rfl
    rw [det_cartan_E8] at hcardZb
    have h2 : Nat.card Zb = 1 := Nat.dvd_one.1 hcardZb
    intro η hη
    have hmem : QuotientGroup.mk' (inner (adjointGroup .E8 K)) η ∈ Zb := ⟨η, hη, rfl⟩
    rw [Subgroup.card_eq_one.1 h2] at hmem
    exact (QuotientGroup.eq_one_iff η).1 (Subgroup.mem_bot.1 hmem)

end CFSG.RankThree.PartOne.KE
