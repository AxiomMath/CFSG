module

public import CFSG.RankThree.Chevalley.SteinbergBNF4A2RootTraces
public import CFSG.LieType.Chevalley.OddF4CosetDescent
public import CFSG.RankThree.Classical.SL2SemilinearRoots

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial

namespace OddF4A2Pointwise

variable {K : Type} [Field K]

theorem trace_apply_of_normalForm
    {η : MulAut (adjointGroup Tag.F4 K)}
    {y : adjointGroup Tag.F4 K} {σ : K ≃+* K}
    (h : ∀ x : adjointGroup Tag.F4 K, (η x : ModGL Tag.F4 K) = (y : ModGL Tag.F4 K) *
      Units.map (entrywiseHom σ.toRingHom) (x : ModGL Tag.F4 K) * (y : ModGL Tag.F4 K)⁻¹)
    (x : adjointGroup Tag.F4 K) :
    LinearMap.trace K (RootModule Tag.F4 K)
        ((η x : ModGL Tag.F4 K) : Module.End K (RootModule Tag.F4 K)) =
      σ (LinearMap.trace K (RootModule Tag.F4 K)
        ((x : ModGL Tag.F4 K) : Module.End K (RootModule Tag.F4 K))) := by
  rw [h x, Units.val_mul, Units.val_mul, LinearMap.trace_conj,
    units_map_entrywiseHom_eq_baseChangeGL, trace_baseChangeGL]
  rfl

theorem ringEquiv_eq_one_of_fixes_A2_traces
    [Finite K] (M : Type) [Field M] (ι : K →+* M)
    (κ : F4A2Kind) (P : GL (Fin 2) M) (σ : K ≃+* K)
    (hσ : ∀ A : SL2 K, ∃ t : K, σ t = t ∧ ι t = LinearMap.trace M (RootModule Tag.F4 M)
      (((f4A2Iota M κ (conjGL P (Matrix.SpecialLinearGroup.map ι A)) :
        subsystemGroup Tag.F4 M {κ.i, κ.j}) : ModGL Tag.F4 M) :
          Module.End M (RootModule Tag.F4 M))) :
    σ = 1 := by
  let _ : Algebra K M := ι.toAlgebra
  have hcl := (F4_A2_root_SL2_full_module_traces_all_characteristics κ).2.2.2 K M P 1
  have hS : {x : M | ∃ A : SL2 K, x = LinearMap.trace M (RootModule Tag.F4 M)
      ((1 * ((f4A2Iota M κ (conjGL P (Matrix.SpecialLinearGroup.map (algebraMap K M) A)) :
          subsystemGroup Tag.F4 M {κ.i, κ.j}) : ModGL Tag.F4 M) * 1⁻¹ : ModGL Tag.F4 M) :
        Module.End M (RootModule Tag.F4 M))} ⊆
      (((RingHom.eqLocusField σ.toRingHom (RingHom.id K)).map ι : Subfield M) : Set M) := by
    rintro _ ⟨A, rfl⟩
    obtain ⟨t, ht, htA⟩ := hσ A
    refine ⟨t, ht, ?_⟩
    rw [htA, one_mul, inv_one, mul_one]
    rfl
  have hle := Subfield.closure_le.2 hS
  rw [hcl] at hle
  refine RingEquiv.ext fun c => ?_
  obtain ⟨t, ht, htc⟩ := hle ⟨c, rfl⟩
  have htc' : t = c := ι.injective htc
  subst htc'
  exact ht

end OddF4A2Pointwise

open OddF4A2Pointwise

theorem odd_F4_descended_A2_root_SL2_pointwise_automorphisms_inner
    {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f) (K : Type) [Field K] (hK : Nat.card K = ℓ ^ f) (M : Type)
    [Field M] (ι : K →+* M) (κ : F4A2Kind) (R₀ : Subgroup (adjointGroup Tag.F4 K))
    (g : ModGL Tag.F4 M) (P : GL (Fin 2) M)
    (hR : (R₀.map ((baseChangeGL ι).comp (adjointGroup Tag.F4 K).subtype)).map
        (MulAut.conj g).toMonoidHom =
      ((Matrix.SpecialLinearGroup.map ι).range.map (CFSG.RankThree.Classical.conjSL P)).map
        ((subsystemGroup Tag.F4 M {κ.i, κ.j}).subtype.comp (f4A2Iota M κ))) :
    (∀ η : MulAut (adjointGroup Tag.F4 K), (∀ r ∈ R₀, η r = r) →
      η ∈ (MulAut.conj : adjointGroup Tag.F4 K →* MulAut (adjointGroup Tag.F4 K)).range) ∧
    ∀ η : MulAut (adjointGroup Tag.F4 K), (∀ r ∈ R₀, η r = r) ↔
      ∃ y ∈ Subgroup.centralizer (R₀ : Set (adjointGroup Tag.F4 K)), η = MulAut.conj y := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hℓ.pos f).ne')
  obtain ⟨hNF, -⟩ :=
    odd_F4_and_nonexceptional_G2_automorphism_normal_form hℓ hℓ2 hf K hK Tag.F4 (Or.inl rfl)
  have hmemR : ∀ A : SL2 K, ∃ r ∈ R₀,
      g * baseChangeGL ι (r : ModGL Tag.F4 K) * g⁻¹ =
        ((f4A2Iota M κ (CFSG.RankThree.Classical.conjSL P (Matrix.SpecialLinearGroup.map ι A)) :
          subsystemGroup Tag.F4 M {κ.i, κ.j}) : ModGL Tag.F4 M) := by
    intro A
    have hx : ((f4A2Iota M κ (CFSG.RankThree.Classical.conjSL P
        (Matrix.SpecialLinearGroup.map ι A)) : subsystemGroup Tag.F4 M {κ.i, κ.j}) :
          ModGL Tag.F4 M) ∈
        ((Matrix.SpecialLinearGroup.map ι).range.map (CFSG.RankThree.Classical.conjSL P)).map
          ((subsystemGroup Tag.F4 M {κ.i, κ.j}).subtype.comp (f4A2Iota M κ)) :=
      ⟨_, ⟨_, ⟨A, rfl⟩, rfl⟩, rfl⟩
    rw [← hR] at hx
    obtain ⟨_, ⟨r, hr, rfl⟩, hrx⟩ := hx
    exact ⟨r, hr, hrx⟩
  have hmain : ∀ η : MulAut (adjointGroup Tag.F4 K), (∀ r ∈ R₀, η r = r) →
      η ∈ (MulAut.conj : adjointGroup Tag.F4 K →* MulAut (adjointGroup Tag.F4 K)).range := by
    intro η hη
    obtain ⟨⟨y, σ⟩, hyσ, -⟩ := hNF η
    simp only at hyσ
    have hσ1 : σ = 1 := by
      refine ringEquiv_eq_one_of_fixes_A2_traces M ι κ P σ fun A => ?_
      obtain ⟨r, hr, hrx⟩ := hmemR A
      refine ⟨LinearMap.trace K (RootModule Tag.F4 K)
        ((r : ModGL Tag.F4 K) : Module.End K (RootModule Tag.F4 K)), ?_, ?_⟩
      · have h1 := trace_apply_of_normalForm hyσ r
        rw [hη r hr] at h1
        exact h1.symm
      · change _ = LinearMap.trace M (RootModule Tag.F4 M)
          (((f4A2Iota M κ (CFSG.RankThree.Classical.conjSL P
            (Matrix.SpecialLinearGroup.map ι A)) : subsystemGroup Tag.F4 M {κ.i, κ.j}) :
              ModGL Tag.F4 M) : Module.End M (RootModule Tag.F4 M))
        rw [← hrx, Units.val_mul, Units.val_mul, LinearMap.trace_conj, trace_baseChangeGL]
    subst hσ1
    refine ⟨y, MulEquiv.ext fun x => Subtype.ext ?_⟩
    have e : Units.map (entrywiseHom (1 : K ≃+* K).toRingHom) (x : ModGL Tag.F4 K) = x :=
      Units.ext (entrywise_id _)
    rw [MulAut.conj_apply, hyσ x, e, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  refine ⟨hmain, fun η => ⟨fun hη => ?_, ?_⟩⟩
  · obtain ⟨y, rfl⟩ := hmain η hη
    refine ⟨y, Subgroup.mem_centralizer_iff.2 fun r hr => ?_, rfl⟩
    have h1 := hη r hr
    rw [MulAut.conj_apply] at h1
    calc r * y = y * r * y⁻¹ * y := by rw [h1]
      _ = y * r := by group
  · rintro ⟨y, hy, rfl⟩ r hr
    rw [MulAut.conj_apply, ← (Subgroup.mem_centralizer_iff.1 hy r hr), mul_inv_cancel_right]

end CFSG.RankThree.Chevalley
