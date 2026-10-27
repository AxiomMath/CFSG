module

public import CFSG.RankThree.Chevalley.SteinbergBUF4CyclotomicSixTools
public import CFSG.RankThree.Chevalley.SteinbergCFF4CyclotomicSix
public import CFSG.RankThree.Chevalley.SteinbergBUF4CyclotomicFourDescent

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley F4Weyl RootSpace SteinbergBN
  CFSG.LieType.AlgebraicGroups
open scoped Pointwise

theorem cyclotomic_six_centralizer_and_D (K : Type) [Field K] [Finite K] [CharP K 2]
    (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (F : Ω →+* Ω)
    (hF : ∀ c, F c = c ^ Nat.card K) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (K₆ : IntermediateField K Ω) (hK₆ : Module.finrank K K₆ = 6) (n g : ModGL .F4 Ω)
    (hn : n = canonicalRep (coxeterSystem .F4) Ω f4PhiSix) (hg : g ∈ adjointGroup .F4 Ω)
    (hgn : g⁻¹ * Units.map (entrywiseHom F) g = n) (Γ T₀ : Subgroup (ModGL .F4 Ω))
    (hΓ : Γ = conjEntrywiseImage K g⁻¹) (hT₀ : T₀ = torusGroup .F4 Ω ⊓ Γ) (x : ModGL .F4 Ω)
    (hx : x ∈ T₀) (hxp : orderOf x = p) (u : WeylGroup .F4) {J : Set (Fin Tag.F4.rank)}
    (hu : (fun α => u • α) '' {α | IsRoot .F4 α ∧ torusRootChar x α = 1} =
      parabolicRoots .F4 J)
    (h y : ModGL .F4 Ω) (hh : h = canonicalRep (coxeterSystem .F4) Ω u) (hy : y = h * x * h⁻¹)
    (Γ₁ D : Subgroup (ModGL .F4 Ω)) (hΓ₁ : Γ₁ = Γ.map (MulAut.conj h).toMonoidHom)
    (hD : D = Γ₁ ⊓ Subgroup.centralizer {y}) :
    g ∈ (adjointGroup .F4 K₆).map (baseChangeGL (algebraMap K₆ Ω)) ∧
    (((adjointGroup .F4 K₆).map (baseChangeGL (algebraMap K₆ Ω)) ⊓ Subgroup.centralizer {y} :
        Subgroup (ModGL .F4 Ω)) : Set (ModGL .F4 Ω)) =
      ((torusGroup .F4 K₆).map (baseChangeGL (algebraMap K₆ Ω)) : Set (ModGL .F4 Ω)) *
        ((subsystemGroup .F4 K₆ J).map (baseChangeGL (algebraMap K₆ Ω)) :
          Set (ModGL .F4 Ω)) ∧
    ∃ σ : K₆ ≃+* K₆, (∀ b, σ b = b ^ Nat.card K) ∧
      (∀ z ∈ adjointGroup .F4 K₆, baseChangeGL (algebraMap K₆ Ω) z ∈ Γ₁ ↔
        canonicalRep (coxeterSystem .F4) K₆ (u * f4PhiSix * u⁻¹) *
            Units.map (entrywiseHom σ.toRingHom) z *
          (canonicalRep (coxeterSystem .F4) K₆ (u * f4PhiSix * u⁻¹))⁻¹ = z) ∧
      D = ((torusGroup .F4 K₆ ⊔ subsystemGroup .F4 K₆ J) ⊓
        ((MulAut.conj (canonicalRep (coxeterSystem .F4) K₆
            (u * f4PhiSix * u⁻¹))).toMonoidHom.comp
          (Units.map (entrywiseHom σ.toRingHom))).eqLocus (MonoidHom.id _)).map
            (baseChangeGL (algebraMap K₆ Ω)) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have : CharP Ω 2 := charP_of_injective_algebraMap (algebraMap K Ω).injective 2
  have : FiniteDimensional K K₆ := Module.finite_of_finrank_eq_succ hK₆
  have : Finite K₆ := Module.finite_of_finite K
  have : CharP K₆ 2 := charP_of_injective_algebraMap (algebraMap K K₆).injective 2
  set ι : K₆ →+* Ω := algebraMap K₆ Ω with hι
  have hinj := baseChangeGL_injective (τ := Tag.F4) ι
  obtain ⟨-, -, -, -, hCF⟩ := F4_cyclotomic_six_torus_and_surviving_A2_kernels K Ω F hF n hn
  obtain ⟨-, -, -, -, -, h2⟩ :=
    hCF g hg hgn Γ T₀ (T₀.map (MulAut.conj g).toMonoidHom) hΓ hT₀ rfl
  obtain ⟨hgK₆, hT₀K₆, hΓK₆⟩ := h2 ‹_› K₆ hK₆
  obtain ⟨x₀, hx₀H, hx₀⟩ := hT₀K₆ hx
  have hhι : baseChangeGL ι (canonicalRep (coxeterSystem .F4) K₆ u) = h := by
    rw [hh]
    exact baseChangeGL_canonicalRep ι u
  set y₀ := canonicalRep (coxeterSystem .F4) K₆ u * x₀ *
    (canonicalRep (coxeterSystem .F4) K₆ u)⁻¹ with hy₀
  have hyι : baseChangeGL ι y₀ = y := by
    rw [hy₀, map_mul, map_mul, map_inv, hhι, hx₀, hy]
  have hu' : (fun α => u • α) '' {α | IsRoot .F4 α ∧ torusRootChar (baseChangeGL ι x₀) α = 1} =
      parabolicRoots .F4 J := by
    rw [hx₀]
    exact hu
  obtain ⟨c, hc, hcp, hc1, hker⟩ :=
    exists_rootDiagUnit_of_conj_parabolic ι hp hx₀H (by rw [hx₀]; exact hxp) u hu'
  have hL₀ : adjointGroup .F4 K₆ ⊓ Subgroup.centralizer {y₀} =
      torusGroup .F4 K₆ ⊔ subsystemGroup .F4 K₆ J := by
    rw [hy₀, hc]
    exact adjointGroup_inf_centralizer_rootDiagUnit_eq_parabolic hp hp3 hcp hc1 hker
  have hnorm : torusGroup .F4 K₆ ≤ Subgroup.normalizer
      (subsystemGroup .F4 K₆ J : Set (ModGL .F4 K₆)) := by
    rw [subsystemGroup_eq_rootSpan]
    exact torusGroup_le_normalizer_rootSpan fun α hα => hα.1
  have hC : ((adjointGroup .F4 K₆).map (baseChangeGL ι) ⊓ Subgroup.centralizer {y} :
      Subgroup (ModGL .F4 Ω)) = (torusGroup .F4 K₆ ⊔ subsystemGroup .F4 K₆ J).map
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
  refine ⟨hgK₆, ?_, ?_⟩
  · rw [hC, Subgroup.coe_map, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hnorm,
      Set.image_mul]
    rfl
  obtain ⟨σ, hσ, hFσ⟩ := exists_frob_restrict F (fun c => by rw [hF, Nat.card_eq_fintype_card])
    K₆
  refine ⟨σ, fun b => by rw [hσ b, Nat.card_eq_fintype_card], ?_⟩
  set v := u * f4PhiSix * u⁻¹ with hv
  have hm : baseChangeGL ι (canonicalRep (coxeterSystem .F4) K₆ v) = h * n * h⁻¹ := by
    rw [baseChangeGL_canonicalRep, hh, hn, canonicalRep_conj_eq_of_charTwo]
  have hhC : h ∈ (adjointGroup .F4 K₆).map (baseChangeGL ι) :=
    ⟨_, canonicalRep_mem_adjointGroup _ K₆ u, hhι⟩
  have hFh : Units.map (entrywiseHom F) h = h := by
    rw [hh]
    exact entrywise_canonicalRep (RingEquiv.ofBijective F (frobenius_bijective (k := K) F hF)) u
  have hΓ₁ch : ∀ z, z ∈ Γ₁ ↔ z ∈ (adjointGroup .F4 K₆).map (baseChangeGL ι) ∧
      h * n * h⁻¹ * Units.map (entrywiseHom F) z * (h * n * h⁻¹)⁻¹ = z := by
    intro z
    rw [hΓ₁, Subgroup.mem_map_equiv, hΓK₆, Subgroup.mem_inf]
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
  refine ⟨fun z hz => ?_, ?_⟩
  · rw [hΓ₁ch]
    constructor
    · rintro ⟨-, hfix⟩
      apply hinj
      rw [map_mul, map_mul, map_inv, hm, ← entrywise_baseChangeGL_eq ι F σ.toRingHom hFσ]
      exact hfix
    · intro hfix
      refine ⟨⟨z, hz, rfl⟩, ?_⟩
      rw [entrywise_baseChangeGL_eq ι F σ.toRingHom hFσ, ← hm, ← map_inv, ← map_mul, ← map_mul,
        hfix]
  · rw [hD, ← hyι, ← hL₀]
    exact inf_centralizer_eq_map_fixed ι F σ.toRingHom hFσ hΓ₁ch hm rfl

end CFSG.RankThree.Chevalley
