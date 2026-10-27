module

public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionWitOmLevi

public section

namespace CFSG.StandardType

namespace WitOm

open CFSG.Assembly Matrix

variable {K : Type} [Field K] [Finite K] {ι ι' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι']
  [DecidableEq ι']

theorem exists_component_levi (e : ι ≃ (Fin 2 ⊕ Fin 2) ⊕ ι') {Q : (ι → K) → K}
    {Q' : (ι' → K) → K}
    (hQ : ∀ v, Q v = (∑ i, v (e.symm (.inl (.inl i))) * v (e.symm (.inl (.inr i)))) +
      Q' fun x => v (e.symm (.inr x))) (h4 : 4 ≤ Nat.card K)
    {δ : ι → Kˣ} {ζ : Kˣ} (hζ1 : ζ ≠ 1) (hζ2 : ζ ≠ ζ⁻¹)
    (hδa : ∀ i, δ (e.symm (.inl (.inl i))) = ζ) (hδb : ∀ i, δ (e.symm (.inl (.inr i))) = ζ⁻¹)
    (hδr : ∀ x, δ (e.symm (.inr x)) = 1) {G : Type} [Group G]
    {φ₀ : ↥(LargeEvenOmega Q) →* G} (hφ : Function.Injective φ₀) {d : ↥(LargeEvenOmega Q)}
    (hd : (d : GL ι K) = TauCeti.diagGL δ) :
    ∃ L₁ : Subgroup G, IsComponentOf L₁ (φ₀.range ⊓ Subgroup.centralizer {φ₀ d}) ∧
      Nonempty (↥L₁ ≃* Matrix.SpecialLinearGroup (Fin 2) K) := by
  set U : Subgroup ↥(LargeEvenOmega Q) := (leviSL (K := K) e).range.subgroupOf (LargeEvenOmega Q)
    with hU
  have hle := range_leviSL_le_omega e hQ h4
  have eU : ↥U ≃* Matrix.SpecialLinearGroup (Fin 2) K :=
    (Subgroup.subgroupOfEquivOfLe hle).trans (MonoidHom.ofInjective (leviSL_injective e)).symm
  have hUq : CFSG.IsQuasisimple ↥U := CFSG.LocalCores.isQuasisimple_of_mulEquiv eU.symm
    (CFSG.LieType.HighestRoot.isQuasisimple_SL2_of_four_le h4)
  have hker : φ₀.ker ≤ Subgroup.center ↥(LargeEvenOmega Q) := by
    rw [(MonoidHom.ker_eq_bot_iff φ₀).mpr hφ]
    exact bot_le
  have hmemU : ∀ z : ↥(LargeEvenOmega Q), z ∈ U ↔ (z : GL ι K) ∈ (leviSL (K := K) e).range :=
    fun z => Subgroup.mem_subgroupOf
  have hUd : ∀ z ∈ U, z * d = d * z := by
    intro z hz
    obtain ⟨X, hX⟩ := (hmemU z).mp hz
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hd, ← hX]
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, TauCeti.diagGL_coe]
    exact leviMat_commute e hδa hδb hδr _ _
  have hUn : ∀ c : ↥(LargeEvenOmega Q), c * d = d * c → ∀ z ∈ U, c * z * c⁻¹ ∈ U := by
    intro c hc z hz
    rw [hmemU]
    have hc' : (c : GL ι K) * TauCeti.diagGL δ = TauCeti.diagGL δ * c := by
      rw [← hd]
      exact congrArg Subtype.val hc
    exact conj_mem_range_leviSL e hQ h4 hζ1 hζ2 hδa hδb hδr (TableBOrth.omega_le_orth _ c.2) hc'
      ((hmemU z).mp hz)
  have hle' : U.map φ₀ ≤ φ₀.range ⊓ Subgroup.centralizer {φ₀ d} := by
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨⟨z, rfl⟩, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    rw [← map_mul, ← map_mul, hUd z hz]
  refine ⟨U.map φ₀, ⟨hle', ?_, SURepair.isQuasisimple_map_of_isQuasisimple hker hUq⟩,
    ⟨(U.equivMapOfInjective φ₀ hφ).symm.trans eU⟩⟩
  refine IsSubnormal.step hle' ?_ (IsSubnormal.refl _)
  rw [Subgroup.normal_subgroupOf_iff hle']
  rintro _ y ⟨z, hz, rfl⟩ ⟨⟨c, rfl⟩, hyc⟩
  have hc : c * d = d * c := hφ (by
    have := Subgroup.mem_centralizer_singleton_iff.mp hyc
    rw [map_mul, map_mul]
    exact this)
  exact ⟨c * z * c⁻¹, hUn c hc z hz, by rw [map_mul, map_mul, map_inv]⟩

end WitOm

end CFSG.StandardType
