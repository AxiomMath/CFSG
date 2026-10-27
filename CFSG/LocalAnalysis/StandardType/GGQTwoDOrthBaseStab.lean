module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthBaseTau

public section

namespace CFSG.StandardType.QTwo

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG.StandardType CFSG.Assembly

variable {G : Type} [Group G]

private instance qtwoDOrthBase_stab_finite (m : ℕ) : Finite (DVec m ≃ₗ[ZMod 3] DVec m) :=
  Finite.of_injective (fun f : DVec m ≃ₗ[ZMod 3] DVec m => (f : DVec m → DVec m))
    DFunLike.coe_injective

theorem card_dEvenStab_dBasis_eq (m : ℕ) (i j : Fin m) :
    Nat.card ↥(dEvenStab m (dBasis m i)) = Nat.card ↥(dEvenStab m (dBasis m j)) := by
  let π : DVec m ≃ₗ[ZMod 3] DVec m := dPerm m (Equiv.swap i j)
  have hπ : π ∈ dEven m := dPerm_mem_dEven m _
  have hπi : π (dBasis m i) = dBasis m j := by
    change dPerm m (Equiv.swap i j) (dBasis m i) = dBasis m j
    rw [dPerm_apply, Equiv.swap_apply_left]
  have hπj : π (dBasis m j) = dBasis m i := by
    change dPerm m (Equiv.swap i j) (dBasis m j) = dBasis m i
    rw [dPerm_apply, Equiv.swap_apply_right]
  have hπinv : π⁻¹ (dBasis m j) = dBasis m i := by
    rw [← hπi]
    simpa using LinearEquiv.symm_apply_apply π (dBasis m i)
  refine Nat.card_congr ⟨fun g => ⟨π * g.1 * π⁻¹, ?_⟩,
    fun g => ⟨π⁻¹ * g.1 * π, ?_⟩, ?_, ?_⟩
  · have hg : g.1 ∈ dEven m ∧ g.1 (dBasis m i) = dBasis m i := g.2
    change π * g.1 * π⁻¹ ∈ dEven m ∧
      (π * g.1 * π⁻¹) (dBasis m j) = dBasis m j
    constructor
    · exact mul_mem (mul_mem hπ hg.1) (inv_mem hπ)
    · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hπinv, hg.2, hπi]
  · have hg : g.1 ∈ dEven m ∧ g.1 (dBasis m j) = dBasis m j := g.2
    change π⁻¹ * g.1 * π ∈ dEven m ∧
      (π⁻¹ * g.1 * π) (dBasis m i) = dBasis m i
    constructor
    · exact mul_mem (mul_mem (inv_mem hπ) hg.1) hπ
    · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hπi, hg.2, hπinv]
  · intro g
    refine Subtype.ext ?_
    change π⁻¹ * (π * g.1 * π⁻¹) * π = g.1
    group
  · intro g
    refine Subtype.ext ?_
    change π * (π⁻¹ * g.1 * π) * π⁻¹ = g.1
    group

theorem qtwoDOrthBase_acts_stab {Bs X : Subgroup G} {n : ℕ}
    {τ : (Fin (n + 1) → Multiplicative (ZMod 3)) ≃* ↥Bs}
    (hmod : HdRo7D.DCoordModel 3 Bs X n τ) (β : Additive ↥Bs ≃+ DVec (n + 1))
    (hjoin : ∀ a ∈ ggAutomizer X Bs, ∃ w ∈ dEven (n + 1),
      ∀ s : ↥Bs, β (Additive.ofMul (a s)) = w (β (Additive.ofMul s)))
    {j : Fin (n + 1)} {c : ZMod 3} (hc : c ≠ 0)
    (hx : β (Additive.ofMul (τ (Pi.mulSingle 0 (Multiplicative.ofAdd (1 : ZMod 3))))) =
      c • dBasis (n + 1) j) :
    qtwoDActsAs β (ggAutomizer X Bs) (dEvenStab (n + 1) (dBasis (n + 1) j)) := by
  haveI : Fact (Nat.Prime 3) := Nat.fact_prime_three
  let A : Subgroup (MulAut ↥Bs) := ggAutomizer X Bs
  let Lτ : MulAut ↥Bs →* (DVec (n + 1) ≃ₗ[ZMod 3] DVec (n + 1)) :=
    ggLin (p := 3) (tauIota τ)
  let Lβ : MulAut ↥Bs →* (DVec (n + 1) ≃ₗ[ZMod 3] DVec (n + 1)) := ggLin (p := 3) β
  let x₀ : ↥Bs := τ (Pi.mulSingle 0 (Multiplicative.ofAdd (1 : ZMod 3)))
  have hx' : β (Additive.ofMul x₀) = c • dBasis (n + 1) j := hx
  have hτ : A.map Lτ = dEvenStab (n + 1) (dBasis (n + 1) 0) :=
    ggAutomizer_map_ggLin_tauIota hmod
  have hcardτ : Nat.card ↥(A.map Lτ) = Nat.card ↥A :=
    Subgroup.card_map_of_injective (ggLin_injective (p := 3) (tauIota τ))
  have hcardβ : Nat.card ↥(A.map Lβ) = Nat.card ↥A :=
    Subgroup.card_map_of_injective (ggLin_injective (p := 3) β)
  have htau0 : tauIota τ (Additive.ofMul x₀) = dBasis (n + 1) 0 := by
    change tauIota τ (Additive.ofMul
      (τ (Pi.mulSingle 0 (Multiplicative.ofAdd (1 : ZMod 3))))) = dBasis (n + 1) 0
    rw [tauIota_ofMul_tau]
    funext i
    rw [dBasis, Pi.basisFun_apply, Pi.single_apply]
    by_cases h : i = 0
    · subst h; simp
    · simp [h]
  have hfix : ∀ a ∈ A, a x₀ = x₀ := by
    intro a ha
    rw [ggLin_fix_iff (p := 3) (tauIota τ) a x₀, htau0]
    have hmem : Lτ a ∈ dEvenStab (n + 1) (dBasis (n + 1) 0) := by
      rw [← hτ]
      exact Subgroup.mem_map_of_mem Lτ ha
    have hmem' : Lτ a ∈ dEven (n + 1) ∧
        Lτ a (dBasis (n + 1) 0) = dBasis (n + 1) 0 := hmem
    exact hmem'.2
  have hle : A.map Lβ ≤ dEvenStab (n + 1) (dBasis (n + 1) j) := by
    intro g hg
    rcases Subgroup.mem_map.mp hg with ⟨a, ha, haw⟩
    rw [← haw]
    rcases hjoin a ha with ⟨w, hw, hwact⟩
    have hLw : Lβ a = w := by
      refine LinearEquiv.ext fun v => ?_
      obtain ⟨s, rfl⟩ : ∃ s : ↥Bs, β (Additive.ofMul s) = v :=
        ⟨Additive.toMul (β.symm v), by simp⟩
      rw [ggLin_apply_ofMul]
      exact hwact s
    change Lβ a ∈ dEven (n + 1) ∧ Lβ a (dBasis (n + 1) j) = dBasis (n + 1) j
    constructor
    · rw [hLw]
      exact hw
    · have hβx : Lβ a (β (Additive.ofMul x₀)) = β (Additive.ofMul x₀) := by
        rw [ggLin_apply_ofMul, hfix a ha]
      have hsmul : c • Lβ a (dBasis (n + 1) j) = c • dBasis (n + 1) j := by
        rw [← map_smul, ← hx']
        exact hβx
      exact (smul_right_inj hc).mp hsmul
  have hcard : Nat.card ↥(dEvenStab (n + 1) (dBasis (n + 1) j)) ≤
      Nat.card ↥(A.map Lβ) := by
    calc Nat.card ↥(dEvenStab (n + 1) (dBasis (n + 1) j))
        = Nat.card ↥(dEvenStab (n + 1) (dBasis (n + 1) 0)) :=
          (card_dEvenStab_dBasis_eq (n + 1) 0 j).symm
      _ = Nat.card ↥(A.map Lτ) := by rw [hτ]
      _ = Nat.card ↥A := hcardτ
      _ ≤ Nat.card ↥(A.map Lβ) := le_of_eq hcardβ.symm
  have hmapβ : A.map Lβ = dEvenStab (n + 1) (dBasis (n + 1) j) :=
    Subgroup.eq_of_le_of_card_ge hle hcard
  constructor
  · intro a ha
    refine ⟨Lβ a, ?_, fun s => (ggLin_apply_ofMul (p := 3) β a s).symm⟩
    rw [← hmapβ]
    exact Subgroup.mem_map_of_mem Lβ ha
  · intro w hw
    have hw' : w ∈ A.map Lβ := by
      rw [hmapβ]
      exact hw
    rcases Subgroup.mem_map.mp hw' with ⟨a, ha, haw⟩
    exact ⟨a, ha, fun s => by rw [← haw, ggLin_apply_ofMul]⟩

end CFSG.StandardType.QTwo

end
