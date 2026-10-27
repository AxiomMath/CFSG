module

public import CFSG.RankThree.GF2n.Stroth80.Sec715ConjCited
public import CFSG.RankThree.GF2n.Stroth80.Sec715Triality
public import CFSG.RankThree.GF2n.Stroth80.Omega8SmallTransfer
public import CFSG.RankThree.GF2n.Stroth80.Omega8Siegel
public import CFSG.LieType.D4Small.SmallIrrep

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.Open
open CFSG.LieType.D4Small
open CFSG.LieType.D4Small.D4Datum
open CFSG.StandardType.Triality

private theorem sub_one_eq_smul_rootOp {G : Type*} [Group G] {K : Type*} [Field K]
    [Finite K] [CharP K 2] {X : Type*} [AddCommGroup X] [Module K X] {D : D4Datum G K}
    {ρ : Representation K G X} {j : ℕ}
    (h : IsRootForm D ρ (fun α => rootOp D ρ α (2 ^ j)) j)
    {α : Fin 4 → ℤ} (hα : IsD4Root α) (c : K) :
    (ρ (D.x α c) : X →ₗ[K] X) - LinearMap.id =
      c ^ (2 ^ j) • rootOp D ρ α (2 ^ j) := by
  rw [h α hα c, Module.End.one_eq_id]
  exact add_sub_cancel_left _ _

private theorem range_and_smul_of_isRootForm {G : Type*} [Group G] {K : Type*} [Field K]
    [Finite K] [CharP K 2] {X : Type*} [AddCommGroup X] [Module K X] {D : D4Datum G K}
    {ρ : Representation K G X} {j : ℕ}
    (h : IsRootForm D ρ (fun α => rootOp D ρ α (2 ^ j)) j)
    {α : Fin 4 → ℤ} (hα : IsD4Root α)
    (hE : Module.finrank K (LinearMap.range (rootOp D ρ α (2 ^ j))) = 2)
    {b b' : K} (hb : b ≠ 0) :
    Module.finrank K (LinearMap.range ((ρ (D.x α b) : X →ₗ[K] X) - LinearMap.id)) = 2 ∧
      ∃ c : K, ∀ x : X, ρ (D.x α b') x - x = c • (ρ (D.x α b) x - x) := by
  have hsub : ∀ c : K, (ρ (D.x α c) : X →ₗ[K] X) - LinearMap.id =
      c ^ (2 ^ j) • rootOp D ρ α (2 ^ j) :=
    fun c => sub_one_eq_smul_rootOp h hα c
  have hbpow : b ^ (2 ^ j) ≠ 0 := pow_ne_zero _ hb
  constructor
  · rw [hsub b, LinearMap.range_smul _ _ hbpow]
    exact hE
  · refine ⟨(b' / b) ^ (2 ^ j), fun x => ?_⟩
    have h1 : ρ (D.x α b') x - x = b' ^ (2 ^ j) • rootOp D ρ α (2 ^ j) x := by
      simpa using congrArg (fun f : X →ₗ[K] X => f x) (hsub b')
    have h2 : ρ (D.x α b) x - x = b ^ (2 ^ j) • rootOp D ρ α (2 ^ j) x := by
      simpa using congrArg (fun f : X →ₗ[K] X => f x) (hsub b)
    rw [h1, h2, smul_smul]
    congr 1
    rw [← mul_pow, div_mul_cancel₀ b' hb]

theorem omega8LongRootRank_holds : Omega8LongRootRankStatement := by
  intro K _ _ _ hK H _ φ hφ X _ _ _ ρ hker hirr hnt hdim
  obtain ⟨ρ', hρ'⟩ := exists_statedOmega_factor hφ hker
  have h8 : Module.finrank K X = 8 :=
    (finrank_eq_eight_and_rootForm (D := om8Datum K) (ρ := repOm8 ρ' 1) hK
      (repOm8_irreducible ρ' hφ hρ' hirr 1) (repOm8_nontrivial ρ' hφ hρ' hnt 1) hdim).1
  refine ⟨h8, ?_⟩
  intro u w hli hu hw huw h h' hN hfix hN' hfix' hne
  obtain ⟨A, hA⟩ := exists_conjOm8_siegel u w hli hu hw huw
  have hα : IsD4Root (lv 0 1 true true) := isD4Root_lv 0 1 true true (by decide)
  have hh : φ h ∈ StatedOmega (StatedQuadPlus 4 K) :=
    hφ ▸ MonoidHom.mem_range.mpr ⟨h, rfl⟩
  have hh' : φ h' ∈ StatedOmega (StatedQuadPlus 4 K) :=
    hφ ▸ MonoidHom.mem_range.mpr ⟨h', rfl⟩
  obtain ⟨b, hb⟩ := hA ⟨φ h, hh⟩ hN hfix
  obtain ⟨b', hb'⟩ := hA ⟨φ h', hh'⟩ hN' hfix'
  have hb0 : b ≠ 0 := by
    intro h0
    have hx : (om8Datum K).x (lv 0 1 true true) b = 1 := by
      rw [h0]
      exact (om8Datum K).x_zero hα
    have h1 : (⟨φ h, hh⟩ : StatedOmega (StatedQuadPlus 4 K)) = 1 := by
      rw [hb, hx]
      exact map_one (conjOm8 A)
    exact hne (by simpa using Subtype.ext_iff.mp h1)
  obtain ⟨j, _hj, hroot, hrank⟩ :=
    (finrank_eq_eight_and_rootForm (D := om8Datum K) (ρ := repOm8 ρ' A) hK
      (repOm8_irreducible ρ' hφ hρ' hirr A)
      (repOm8_nontrivial ρ' hφ hρ' hnt A) hdim).2
  have hρh : ((ρ h : X ≃ₗ[K] X) : X →ₗ[K] X) =
      repOm8 ρ' A ((om8Datum K).x (lv 0 1 true true) b) := by
    rw [← hρ' h hh, hb]
    exact (repOm8_apply ρ' A ((om8Datum K).x (lv 0 1 true true) b)).symm
  have hρh' : ((ρ h' : X ≃ₗ[K] X) : X →ₗ[K] X) =
      repOm8 ρ' A ((om8Datum K).x (lv 0 1 true true) b') := by
    rw [← hρ' h' hh', hb']
    exact (repOm8_apply ρ' A ((om8Datum K).x (lv 0 1 true true) b')).symm
  obtain ⟨hr, hc⟩ := range_and_smul_of_isRootForm hroot hα (hrank _ hα) hb0
  refine ⟨?_, ?_⟩
  · rw [hρh]
    exact hr
  · obtain ⟨c, hc⟩ := hc
    refine ⟨c, fun x => ?_⟩
    change ((ρ h' : X →ₗ[K] X)) x - x = c • (((ρ h : X →ₗ[K] X)) x - x)
    rw [hρh', hρh]
    exact hc x

theorem omega8EndScalar_holds : Omega8EndScalarStatement := by
  intro K _ _ _ hK H _ φ hφ X _ _ _ ρ hker hirr hnt hdim T hT
  obtain ⟨ρ', hρ'⟩ := exists_statedOmega_factor hφ hker
  obtain ⟨c, hc⟩ := exists_eq_smul_of_commute (D := om8Datum K) (ρ := repOm8 ρ' 1) hK
    (repOm8_irreducible ρ' hφ hρ' hirr 1) (repOm8_nontrivial ρ' hφ hρ' hnt 1) hdim
    (repOm8_commute ρ' hφ hρ' hT 1)
  refine ⟨c, ?_⟩
  rw [hc, Module.End.one_eq_id]

end CFSG.RankThree.GF2n.Stroth80
