module

public import CFSG.LocalAnalysis.StandardType.GGRootDetectExcCore

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Universal CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace RootDetectExc

section Diag

variable {τ : Tag} {K : Type} [Field K]

@[expose] def AdjDiagFieldForm (τ : Tag) (K : Type) [Field K] (p : ℕ) : Prop :=
  ∀ β : MulAut (adjointGroup τ K), β ^ p = 1 →
    ∃ (g : adjointGroup τ K) (a : Fin τ.rank → Kˣ) (σ : K ≃+* K), σ ^ p = 1 ∧
      ∀ h : adjointGroup τ K, (β h : ModGL τ K) = (g : ModGL τ K) * rootDiagUnit τ a *
        Units.map (entrywiseHom σ.toRingHom) (h : ModGL τ K) * (rootDiagUnit τ a)⁻¹ *
          (g : ModGL τ K)⁻¹

theorem rootDiagUnit_conj_eltUnit
    (F : RootOperatorFamily τ) (a : Fin τ.rank → Kˣ)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (t : K) :
    rootDiagUnit τ a * F.eltUnit K ⟨γ, hγ⟩ t * (rootDiagUnit τ a)⁻¹ =
      F.eltUnit K ⟨γ, hγ⟩ ((rootChar a γ : K) * t) := by
  have hs := F.pinnedFamilySign_mul_self K γ
  have e1 : ∀ s : K, F.eltUnit K ⟨γ, hγ⟩ s =
      pinnedX τ K γ ((F.pinnedFamilySign γ : K) * s) := by
    intro s
    rw [F.pinnedX_eq_eltUnit K hγ, ← mul_assoc, hs, one_mul]
  rw [e1, e1, rootDiagUnit_conj_pinnedX a hγ]
  congr 1
  ring

end Diag

section Isogeny


variable {τ : Tag} {K : Type} [Field K]

theorem ggPsiInnerDiag_of_isogeny_diag [Finite K] [CharP K 2] (F : RootOperatorFamily τ)
    {S : Type*} [Group S] [Finite S] (Δ : UniversalRootDatum S)
    (hperf : ⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆ = ⊤)
    (hZ : Subgroup.center (adjointGroup τ K) = ⊥)
    {π : S →* adjointGroup τ K} (hπ : Function.Surjective π)
    (hπker : π.ker ≤ Subgroup.center S) (hodd : Odd (Nat.card π.ker))
    (hinv : ∀ δ ∈ Δ.roots, ∀ z ∈ Δ.rootGroup δ, z * z = 1)
    (hdiag : ∀ δ ∈ Δ.roots, ∀ a : Fin τ.rank → Kˣ, ∃ h ∈ ggTorus Δ, ∀ z ∈ Δ.rootGroup δ,
      ((π (h * z * h⁻¹) : adjointGroup τ K) : ModGL τ K) =
        rootDiagUnit τ a * ((π z : adjointGroup τ K) : ModGL τ K) * (rootDiagUnit τ a)⁻¹)
    {p : ℕ} (hp : Odd p) (hform : AdjDiagFieldForm τ K p)
    {G : Type*} [Group G] {ψ : S →* G} (hker : ψ.ker ≤ Subgroup.center S) {c : G}
    (hc : c ∈ Subgroup.normalizer (ψ.range : Set G))
    (hcp : c ^ p ∈ Subgroup.centralizer (ψ.range : Set G)) {γ : Fin Δ.rank → ℤ}
    {α : Root τ} (hroot : ∀ t : K, ∃ z ∈ Δ.rootGroup γ, π z = F.eltElement α t)
    {u : S} (hT : GGTorusOnRoot Δ ψ c γ u) :
    GGPsiInnerDiag Δ ψ c := by
  classical
  obtain ⟨α', hα'⟩ := RootDetect.exists_quotAut (N := Subgroup.center S) rfl hperf hker hc
  have hα'p : α' ^ p = 1 := RootDetect.quotAut_pow_eq_one le_rfl hker hc hα' hcp
  have hkerπ : π.ker = Subgroup.center S := by
    refine le_antisymm hπker fun z hz => ?_
    rw [MonoidHom.mem_ker]
    have hzc : π z ∈ Subgroup.center (adjointGroup τ K) := by
      rw [Subgroup.mem_center_iff]
      intro x
      obtain ⟨y, rfl⟩ := hπ x
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz y]
    rw [hZ] at hzc
    exact hzc
  let e : S ⧸ Subgroup.center S ≃* adjointGroup τ K :=
    (QuotientGroup.quotientMulEquivOfEq hkerπ.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective π hπ)
  have he : ∀ y : S, e (y : S ⧸ Subgroup.center S) = π y := fun y => rfl
  let β : MulAut (adjointGroup τ K) := (e.symm.trans α').trans e
  have hβ : ∀ x, β (e x) = e (α' x) := fun x => by
    change e (α' (e.symm (e x))) = e (α' x)
    rw [MulEquiv.symm_apply_apply]
  have hβpow : ∀ k : ℕ, ∀ x, (β ^ k) (e x) = e ((α' ^ k) x) := by
    intro k
    induction k with
    | zero => intro x; rfl
    | succ k ih =>
      intro x
      rw [pow_succ', MulAut.mul_apply, ih, hβ, pow_succ', MulAut.mul_apply]
  have hβp : β ^ p = 1 := by
    refine MulEquiv.ext fun x => ?_
    obtain ⟨y, rfl⟩ := e.surjective x
    rw [hβpow, hα'p]
    rfl
  obtain ⟨g, a, σ, hσp, hgσ⟩ := hform β hβp
  obtain ⟨W, hW⟩ := RootDetect.exists_conj_of_torusOnRoot Δ hT
  have hconj : ∀ t : K, β (π u * F.eltElement α t * (π u)⁻¹) =
      π W * F.eltElement α t * (π W)⁻¹ := by
    intro t
    obtain ⟨z, hz, hπz⟩ := hroot t
    have h2 := congrArg e (hα' _ _ (hW z hz))
    rw [← hβ, he, he] at h2
    simpa only [map_mul, map_inv, hπz] using h2
  obtain ⟨σu, hσu⟩ : ∃ x : ModGL τ K,
      x = Units.map (entrywiseHom σ.toRingHom) (π u : ModGL τ K) := ⟨_, rfl⟩
  obtain ⟨wW, hwW⟩ : ∃ x : ModGL τ K, x = ((π W : adjointGroup τ K) : ModGL τ K) := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ x : ModGL τ K, x = rootDiagUnit τ a := ⟨_, rfl⟩
  have hNt : ∀ t : K,
      (((wW⁻¹ * (g : ModGL τ K) * d * σu)⁻¹ : (Module.End K (RootModule τ K))ˣ) :
        Module.End K (RootModule τ K)) * F.elt K α t *
        ((wW⁻¹ * (g : ModGL τ K) * d * σu : (Module.End K (RootModule τ K))ˣ) :
          Module.End K (RootModule τ K)) = F.elt K α (σ t) := by
    intro t
    have h1 : ((β (π u * F.eltElement α t * (π u)⁻¹) : adjointGroup τ K) : ModGL τ K) =
        ((π W * F.eltElement α t * (π W)⁻¹ : adjointGroup τ K) : ModGL τ K) := by
      rw [hconj t]
    rw [hgσ] at h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv,
      RootOperatorFamily.coe_eltElement, units_map_entrywiseHom_eltUnit, ← hσu, ← hwW,
      ← hd] at h1
    have h1' : (g : ModGL τ K) * d * σu * F.eltUnit K α (σ t) * σu⁻¹ * d⁻¹ *
        (g : ModGL τ K)⁻¹ = wW * F.eltUnit K α t * wW⁻¹ := by
      rw [← h1]
      group
    have h3 : (wW⁻¹ * (g : ModGL τ K) * d * σu) * F.eltUnit K α (σ t) *
        (wW⁻¹ * (g : ModGL τ K) * d * σu)⁻¹ = F.eltUnit K α t := by
      calc (wW⁻¹ * (g : ModGL τ K) * d * σu) * F.eltUnit K α (σ t) *
            (wW⁻¹ * (g : ModGL τ K) * d * σu)⁻¹ =
          wW⁻¹ * ((g : ModGL τ K) * d * σu * F.eltUnit K α (σ t) * σu⁻¹ * d⁻¹ *
            (g : ModGL τ K)⁻¹) * wW := by group
        _ = F.eltUnit K α t := by rw [h1']; group
    have h4 : (wW⁻¹ * (g : ModGL τ K) * d * σu)⁻¹ * F.eltUnit K α t *
        (wW⁻¹ * (g : ModGL τ K) * d * σu) = F.eltUnit K α (σ t) := by
      rw [← h3]
      group
    exact congrArg Units.val h4
  have hσ : σ = 1 := ringEquiv_eq_one_of_conj_elt F α hp hσp hNt
  have hβg : ∀ h, (β h : ModGL τ K) = (g : ModGL τ K) * rootDiagUnit τ a * (h : ModGL τ K) *
      (rootDiagUnit τ a)⁻¹ * (g : ModGL τ K)⁻¹ := by
    intro h
    rw [hgσ h, hσ]
    have e1 : Units.map (entrywiseHom (1 : K ≃+* K).toRingHom) (h : ModGL τ K) = h := by
      refine Units.ext ?_
      rw [Units.coe_map]
      exact entrywise_ringHomId _
    rw [e1]
  obtain ⟨a₀, rfl⟩ := hπ g
  refine ⟨ψ a₀, ⟨a₀, rfl⟩, fun δ hδ => ?_⟩
  obtain ⟨h, hh, hhz⟩ := hdiag δ hδ a
  refine ⟨h, hh, fun z hz => ?_⟩
  obtain ⟨z₁, hz₁⟩ := RootDetect.exists_conj_preimage hc z
  have hπz₁ : π z₁ = π (a₀ * (h * z * h⁻¹) * a₀⁻¹) := by
    have hq := congrArg e (hα' z z₁ hz₁)
    rw [← hβ, he, he] at hq
    refine Subtype.ext ?_
    rw [← hq, hβg, map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, hhz z hz]
    group
  obtain ⟨ζ, hζ⟩ : ∃ ζ : S, ζ = (a₀ * (h * z * h⁻¹) * a₀⁻¹)⁻¹ * z₁ := ⟨_, rfl⟩
  have hζker : ζ ∈ π.ker := by
    rw [MonoidHom.mem_ker, hζ, map_mul, map_inv, hπz₁, inv_mul_cancel]
  have hζc : ζ ∈ Subgroup.center S := hπker hζker
  have heq : z₁ = a₀ * (h * z * h⁻¹) * a₀⁻¹ * ζ := by rw [hζ]; group
  have hhzh : h * z * h⁻¹ ∈ Δ.rootGroup δ := by
    have hhn : h ∈ Subgroup.normalizer (Δ.rootGroup δ : Set S) := by
      simp only [ggTorus, Subgroup.mem_iInf] at hh
      exact hh δ hδ
    exact (Subgroup.mem_normalizer_iff.mp hhn z).mp hz
  have hw2 : (h * z * h⁻¹) * (h * z * h⁻¹) = 1 := hinv δ hδ _ hhzh
  have hz2 : z * z = 1 := hinv δ hδ z hz
  have hψz₁ : ψ z₁ * ψ z₁ = 1 := by
    calc ψ z₁ * ψ z₁ = c⁻¹ * (ψ z * ψ z) * c := by rw [hz₁]; group
      _ = 1 := by rw [← map_mul, hz2, map_one]; group
  have hzz : z₁ * z₁ = ζ * ζ := by
    have hcomm := Subgroup.mem_center_iff.mp hζc (a₀ * (h * z * h⁻¹) * a₀⁻¹)
    calc z₁ * z₁ = a₀ * (h * z * h⁻¹) * a₀⁻¹ * ζ * (a₀ * (h * z * h⁻¹) * a₀⁻¹ * ζ) := by
          rw [heq]
      _ = a₀ * (h * z * h⁻¹) * a₀⁻¹ * (ζ * (a₀ * (h * z * h⁻¹) * a₀⁻¹)) * ζ := by group
      _ = a₀ * (h * z * h⁻¹) * a₀⁻¹ * (a₀ * (h * z * h⁻¹) * a₀⁻¹ * ζ) * ζ := by rw [hcomm]
      _ = a₀ * ((h * z * h⁻¹) * (h * z * h⁻¹)) * a₀⁻¹ * (ζ * ζ) := by group
      _ = ζ * ζ := by rw [hw2]; group
  have hζ2 : ψ ζ * ψ ζ = 1 := by
    rw [← map_mul, ← hzz, map_mul, hψz₁]
  have hζodd : Odd (orderOf ζ) := by
    have h1 : orderOf (⟨ζ, hζker⟩ : π.ker) ∣ Nat.card π.ker := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    exact hodd.of_dvd_nat h1
  have hψζ : ψ ζ = 1 := by
    obtain ⟨m, hm⟩ := hζodd
    have h1 : ψ ζ ^ orderOf ζ = 1 := by rw [← map_pow, pow_orderOf_eq_one, map_one]
    rw [hm, pow_succ, pow_mul, sq, hζ2, one_pow, one_mul] at h1
    exact h1
  have hcomm' := Subgroup.mem_center_iff.mp hζc a₀⁻¹
  calc (c * ψ a₀)⁻¹ * ψ z * (c * ψ a₀) = (ψ a₀)⁻¹ * (c⁻¹ * ψ z * c) * ψ a₀ := by group
    _ = (ψ a₀)⁻¹ * ψ z₁ * ψ a₀ := by rw [hz₁]
    _ = ψ (a₀⁻¹ * z₁ * a₀) := by rw [map_mul, map_mul, map_inv]
    _ = ψ ((h * z * h⁻¹) * (a₀⁻¹ * ζ * a₀)) := by rw [heq]; group
    _ = ψ ((h * z * h⁻¹) * ζ) := by rw [hcomm', inv_mul_cancel_right]
    _ = ψ (h * z * h⁻¹) := by rw [map_mul, hψζ, mul_one]

end Isogeny

end RootDetectExc

end CFSG.StandardType
