module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSpContBasic

public section

open Polynomial Module Multiplicative
open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Symplectic
open CFSG.RankThree.Classical (spForm spLin spLin_injective spEnd spSupported mem_spSupported)
open CFSG.RankThree.PartOne (spFixedFactor)
open CFSG.RankThree.PartOne.KCPrimary (primaryFactors primaryComponent mem_primaryComponent
  isCoprime_of_mem_primaryFactors)

namespace CFSG.StandardType

namespace SpNsCont

open CoordSpNs

section Zero

variable {F : Type} [Field F] {n p : ℕ} [NeZero p] {D : Type} [AddCommGroup D] [Module F D]
  {s : ℕ} {κ : Type} {c : D ≃ₗ[F] D} (hc : c ^ p = 1)
  {Φ : ((Fin s → D) × (κ → F)) ≃ₗ[F] (Fin n ⊕ Fin n → F)} {ω : LinearMap.BilinForm F D}
  (hdec : ∀ d d' w w', spForm n F (Φ (d, w)) (Φ (d', w')) =
    ∑ i, ω (d i) (d' i) + spForm n F (Φ (0, w)) (Φ (0, w')))
  (hcω : ∀ x y, ω (c x) (c y) = ω x y)

theorem mem_nonzero_of_primaryComponent {β : Fin s → ZMod p} {k : F[X]}
    (hk : k ∈ primaryFactors (spEnd (torElt hc hdec hcω β)))
    (h1 : (X - 1 : F[X]) ∈ primaryFactors (spEnd (torElt hc hdec hcω β))) (hne : k ≠ X - 1)
    {v : Fin n ⊕ Fin n → F} (hv : v ∈ primaryComponent (spEnd (torElt hc hdec hcω β)) k) :
    (Φ.symm v).2 = 0 ∧ ∀ i, β i = 0 → (Φ.symm v).1 i = 0 := by
  obtain ⟨a, b, hab⟩ := isCoprime_of_mem_primaryFactors hk h1 hne
  rw [mul_comm b] at hab
  have hvw : v = spEnd (torElt hc hdec hcω β) (aeval (spEnd (torElt hc hdec hcω β)) b v) -
      aeval (spEnd (torElt hc hdec hcω β)) b v := by
    have h2 := congrArg (fun q => aeval (spEnd (torElt hc hdec hcω β)) q v) hab
    simp only [map_add, map_mul, map_one, Module.End.mul_apply, Module.End.one_apply, map_sub,
      aeval_X, LinearMap.add_apply, LinearMap.sub_apply] at h2
    rw [mem_primaryComponent.mp hv, map_zero, zero_add] at h2
    exact h2.symm
  set w := aeval (spEnd (torElt hc hdec hcω β)) b v with hw
  have hΦ : Φ.symm v = torD c β (Φ.symm w) - Φ.symm w := by
    rw [hvw, map_sub]
    congr 1
    conv_lhs => rw [← Φ.apply_symm_apply w]
    rw [spEnd_torElt, LinearEquiv.symm_apply_apply]
  rw [hΦ]
  refine ⟨?_, fun i hi => ?_⟩
  · simp [torD_apply']
  · simp [torD_apply', hi]

theorem mem_spFixedFactor_of_fix {β : Fin s → ZMod p}
    (h1 : (X - 1 : F[X]) ∈ primaryFactors (spEnd (torElt hc hdec hcω β))) {Y : StatedSp n F}
    (hYx : Y * torElt hc hdec hcω β = torElt hc hdec hcω β * Y)
    (hY : ∀ y : (Fin s → D) × (κ → F), y.2 = 0 → (∀ i, β i = 0 → y.1 i = 0) →
      frameEnd Φ Y y = y) : Y ∈ spFixedFactor (torElt hc hdec hcω β) := by
  change Y ∈ spSupported (torElt hc hdec hcω β) {X - 1}
  rw [mem_spSupported]
  refine ⟨hYx, fun k hk hkX v hv => ?_⟩
  obtain ⟨h2, h3⟩ := mem_nonzero_of_primaryComponent hc hdec hcω hk h1
    (fun h => hkX (Set.mem_singleton_iff.mpr h)) hv
  have h4 := hY (Φ.symm v) h2 h3
  rw [frameEnd_apply, LinearEquiv.apply_symm_apply] at h4
  exact Φ.symm.injective h4

end Zero

end SpNsCont

open SpNsCont CoordSpNs

theorem ggSpNsZeroContInput_holds : GGSpNsZeroContInput := by
  intro G _ _ F _ _ _ n p _ hp2 hns ψ hψ g _ hgd D _ _ c hbt hc s κ _ Φ ω hdec hcω β L₁ hβ0 hZ2
    hL₁ hLfix t ht
  classical
  have hpp : p.Prime := Fact.out
  have hpF : (p : F) ≠ 0 := TableBSymp.natCast_ne_zero_of_charTwo hpp hp2
  have hprim := NSFrame.root_isPrimitiveRoot (g := g) hpp hpF hgd
  have hζ : AdjoinRoot.root g ^ p = 1 := hprim.pow_eq_one
  have : Nontrivial D := nontrivial_of_blockType hbt
  obtain ⟨i₁, hi₁⟩ : ∃ i, β i ≠ 0 := by
    by_contra h
    push Not at h
    exact hβ0 (funext h)
  obtain ⟨z₀, -, -, hz₀, -⟩ := hZ2
  obtain ⟨f, hf, hK⟩ := exists_card_eq_two_pow (F := F)
  have blocks := spPrimaryBlocks_torElt hc hdec hcω hp2 hbt hζ hprim hi₁ hf hK
  rw [nsCoord_eq_torElt] at hL₁
  obtain ⟨hL', hmapL⟩ := isComponentOf_comap hψ hL₁
  have hxp := torElt_pow_p hc hdec hcω β
  have hmem1 : (X - 1 : F[X]) ∈ primaryFactors (spEnd (torElt hc hdec hcω β)) := by
    by_contra hno
    obtain ⟨d, hd⟩ := exists_ne (0 : D)
    have hbot := CFSG.RankThree.Classical.primaryComponent_eq_bot_of_not_mem
      CFSG.RankThree.Classical.irreducible_X_sub_one CFSG.RankThree.Classical.monic_X_sub_one hno
    have hv : Φ (Pi.single z₀ d, 0) ∈
        primaryComponent (spEnd (torElt hc hdec hcω β)) (X - 1) :=
      single_mem_primaryComponent hc hdec hcω (by
        rw [hz₀, ZMod.val_zero, pow_zero]
        simp)
    rw [hbot, Submodule.mem_bot, Φ.map_eq_zero_iff] at hv
    have h2 := congrArg (fun y : (Fin s → D) × (κ → F) => y.1 z₀) hv
    simp only [Pi.single_eq_same, Prod.fst_zero, Pi.zero_apply] at h2
    exact hd h2
  have hLF : L₁.comap ψ ≤ spFixedFactor (torElt hc hdec hcω β) := by
    intro Y hY
    have hYc := Subgroup.mem_centralizer_singleton_iff.mp (hL'.1 hY)
    obtain ⟨Z, hZ, hZY⟩ := hLfix hY
    rw [hψ hZY] at hZ
    exact mem_spFixedFactor_of_fix hc hdec hcω hmem1 hYc fun y hy2 hy1 =>
      (mem_fixGrp Φ).mp hZ y ⟨hy2, hy1⟩
  obtain ⟨-, hin⟩ := SevSpNs.fixed_case hK hf hpp hp2 hxp blocks hmem1 hL' hLF
  have hu : torElt hc hdec hcω t ∈ spFixedFactor (torElt hc hdec hcω β) := by
    refine mem_spFixedFactor_of_fix hc hdec hcω hmem1 (torElt_comm hc hdec hcω t β)
      fun y _ hy1 => ?_
    rw [frameEnd_torElt]
    refine Prod.ext (funext fun i => ?_) rfl
    change (c ^ (t i).val) (y.1 i) = y.1 i
    by_cases hi : β i = 0
    · rw [hy1 i hi, map_zero]
    · rw [ht i hi, ZMod.val_zero, pow_zero]
      rfl
  rw [nsCoord_eq_torElt, ← hmapL]
  exact Subgroup.mem_map_of_mem ψ (hin _ hu (torElt_pow_p hc hdec hcω t))

end CFSG.StandardType
