module

public import CFSG.RankThree.PartTwo.Sec6.BThreeCensusSp4
public import CFSG.RankThree.PartTwo.Sec6.BThreeCensusSL3
public import CFSG.RankThree.PartTwo.KFacts.AutPSp4Odd
public import CFSG.RankThree.PartTwo.Sec4.Item47Bridges
import CFSG.GH74.GLS.IVK.L2.Fixed
import CFSG.LocalAnalysis.ComponentInitial.SymplecticPerfectCoverOuterPrime
import CFSG.ClassicalGroups.Symplectic.ProjectivePerfect
import CFSG.RankThree.SubgroupLists.CentralThreeLift
public import CFSG.ClassicalGroups.Symplectic.Simple
public import CFSG.LieType.Chevalley.LangRootArithmetic
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.RankThree.PartTwo.Sec12.Notation
public import CFSG.RankThree.PartTwo.Sec4.Item47Diag
public import CFSG.RankThree.PartTwo.Sec4.Item47Statement
public import CFSG.RankThree.PartTwo.Sec4.Item47Witness
public import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
public import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv
public import CFSG.RankThree.PartTwo.Sec8.Statements
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.RankThree.PartTwo.Sec6.BThreeCensus

open CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (spScalars ker_proj proj_surjective
  conjAut gsp multiplier conjAut_mem_inner_of_isSquare spScalars_le_center)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

local notation "V₄" => Fin 2 ⊕ Fin 2

variable {F : Type} [Field F]

theorem sq_eq_one_of_mem_spScalars {z : StatedSp 2 F} (hz : z ∈ spScalars 2 F) : z ^ 2 = 1 := by
  have hz' := hz
  rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hz'
  obtain ⟨c, hc⟩ := hz'
  have hS := (CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff).mp z.2
  rw [← hc] at hS
  have h1 := congrFun (congrFun hS (Sum.inl 0)) (Sum.inr 0)
  simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_transpose,
    Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.fromBlocks_apply₁₂, Matrix.one_apply_eq] at h1
  have hc2 : c ^ 2 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one, sq,
    ← h1, mul_one])
  apply Subtype.ext
  rw [Subgroup.coe_pow, ← hc, ← map_pow, hc2, map_one, Subgroup.coe_one]

theorem center_statedProj_sp4_eq_bot_of_four_le [Finite F] (h4 : 4 ≤ Nat.card F) :
    Subgroup.center (StatedProj (StatedSp 2 F)) = ⊥ := by
  have hsimple : IsSimpleGroup (StatedProj (StatedSp 2 F)) :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp F 2 (by norm_num)
      (Or.inl (Or.inr h4))
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F)) (n := 4)
    (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact h4)
  have hperf : Group.IsPerfect (StatedProj (StatedSp 2 F)) :=
    CFSG.ClassicalGroups.Symplectic.symplectic_projective_perfect 2 F (Or.inl ⟨s, hs⟩)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (StatedProj (StatedSp 2 F)))
    with h | h
  · exact h
  · exfalso
    have hcomm : ⁅(⊤ : Subgroup (StatedProj (StatedSp 2 F))), ⊤⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr fun x _ y _ =>
        Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top x) y
    have htop : ⁅(⊤ : Subgroup (StatedProj (StatedSp 2 F))), ⊤⁆ = ⊤ := hperf.commutator_eq_top
    obtain ⟨a, ha⟩ := exists_ne (1 : StatedProj (StatedSp 2 F))
    have hmem : a ∈ ⁅(⊤ : Subgroup (StatedProj (StatedSp 2 F))), ⊤⁆ := htop ▸ Subgroup.mem_top a
    rw [hcomm, Subgroup.mem_bot] at hmem
    exact ha hmem

theorem orderOf_ne_three_of_card_prime [Finite F] {p : ℕ} (hp : p.Prime) (hF : Nat.card F = p)
    (σ : F ≃+* F) : orderOf σ ≠ 3 := by
  intro hσ3
  have hcard := CFSG.GH74.GLS.IVK.fixedField_card_pow σ
  rw [hσ3, hF] at hcard
  have hdvd : Nat.card (CFSG.GH74.GLS.IVK.fixedField σ) ∣ p :=
    ⟨Nat.card (CFSG.GH74.GLS.IVK.fixedField σ) ^ 2, by rw [← hcard]; ring⟩
  rcases hp.eq_one_or_self_of_dvd _ hdvd with h1 | h1
  · rw [h1, one_pow] at hcard
    exact hp.one_lt.ne hcard
  · rw [h1] at hcard
    have h2 := hp.two_le
    have : p < p ^ 3 := by
      calc p = p ^ 1 := (pow_one p).symm
        _ < p ^ 3 := Nat.pow_lt_pow_right (by omega) (by norm_num)
    omega

theorem threePrimeB3_statedProj_sp4_prime [Finite F] {p : ℕ}
    [Fact p.Prime] [CharP F p] (hp3 : 3 < p) (hF : Nat.card F = p) :
    ThreePrimeB3 (StatedProj (StatedSp 2 F)) := by
  have hp : p.Prime := Fact.out
  have h4 : 4 ≤ Nat.card F := by omega
  have hodd : ringChar F ≠ 2 := by
    rw [ringChar.eq F p]
    omega
  have h3 : (3 : F) ≠ 0 := three_ne_zero_of_charP (by omega)
  have hsimpleP : IsSimpleGroup (StatedProj (StatedSp 2 F)) :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp F 2 (by norm_num)
      (Or.inl (Or.inr h4))
  have hZ := center_statedProj_sp4_eq_bot_of_four_le h4
  intro β hβ C Y R hC hYC hsn hYp hY3 hRY hRn hRs _
  have hD : β ∈ (conjAut 2 F).range := by
    by_contra hD
    obtain ⟨σ, hσ3, -⟩ := CFSG.RankThree.PartTwo.KFacts.psp4_odd_order_three_field_descent hodd β
      hβ hD
    exact orderOf_ne_three_of_card_prime hp hF σ hσ3
  obtain ⟨A, rfl⟩ := hD
  have hinner : conjAut 2 F A ∈ inner (StatedProj (StatedSp 2 F)) := by
    have h4A : conjAut 2 F A = conjAut 2 F (A ^ 2) ^ 2 := by
      rw [← map_pow, ← pow_mul, map_pow]
      calc conjAut 2 F A = conjAut 2 F A ^ 3 * conjAut 2 F A := by rw [hβ, one_mul]
        _ = conjAut 2 F A ^ (2 * 2) := by rw [← pow_succ]
    rw [h4A]
    refine Subgroup.pow_mem _ (conjAut_mem_inner_of_isSquare ⟨(multiplier 2 F A : F), ?_⟩) 2
    rw [map_pow, Units.val_pow_eq_pow_val, sq]
  obtain ⟨x, hx⟩ := hinner
  have hx3 : x ^ 3 = 1 := by
    have h1 : MulAut.conj (x ^ 3) = 1 := by rw [map_pow, hx, hβ]
    have h2 : x ^ 3 ∈ Subgroup.center (StatedProj (StatedSp 2 F)) := by
      rw [Subgroup.mem_center_iff]
      intro z
      have := congrArg (fun φ : MulAut (StatedProj (StatedSp 2 F)) => φ z) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc z * x ^ 3 = x ^ 3 * z * (x ^ 3)⁻¹ * x ^ 3 := by rw [this]
        _ = x ^ 3 * z := by group
    rw [hZ, Subgroup.mem_bot] at h2
    exact h2
  by_cases hx1 : x = 1
  ·
    have hβ1 : conjAut 2 F A = 1 := by rw [← hx, hx1, map_one]
    have hCtop : C = ⊤ := by
      ext z
      simp [hC z, hβ1]
    have hsimp : IsSimpleGroup C :=
      ((MulEquiv.subgroupCongr hCtop).trans Subgroup.topEquiv).isSimpleGroup
    exact commutator_eq_bot_of_isSimpleGroup_or_isSolvable (Or.inl hsimp) hYC hsn hYp hRY hRn
      hRs
  suffices hY : Y = ⊥ by rw [hY, Subgroup.commutator_bot_right]
  obtain ⟨g₀, hg₀⟩ := proj_surjective (r := 2) (K := F) x
  have hz : g₀ ^ 3 ∈ spScalars 2 F := by
    rw [← ker_proj, MonoidHom.mem_ker, map_pow, hg₀, hx3]
  set g : StatedSp 2 F := g₀ ^ 4 with hg
  have hgx : proj 2 F g = x := by
    rw [hg, map_pow, hg₀]
    calc x ^ 4 = x ^ 3 * x := pow_succ x 3
      _ = x := by rw [hx3, one_mul]
  have hg3 : (g : GL V₄ F) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow]
    have : g ^ 3 = 1 := by
      calc g ^ 3 = ((g₀ ^ 3) ^ 2) ^ 2 := by rw [hg, ← pow_mul, ← pow_mul, ← pow_mul]
        _ = 1 := by rw [sq_eq_one_of_mem_spScalars hz, one_pow]
    rw [this, Subgroup.coe_one]
  have hg1 : (g : GL V₄ F) ≠ 1 := by
    intro h1
    apply hx1
    rw [← hgx, show g = 1 from Subtype.ext h1, map_one]
  have : Group.IsPerfect Y := hYp
  set Ŷ := Y.comap (QuotientGroup.mk' (spScalars 2 F)) with hŶ
  set D := ⁅Ŷ, Ŷ⁆ with hD
  have hDp : Group.IsPerfect D :=
    CFSG.RankThree.SubgroupLists.isPerfect_commutator_comap spScalars_le_center Y
  have hDmap : D.map (proj 2 F) = Y := CFSG.RankThree.SubgroupLists.map_commutator_comap Y
  have hD3 : ¬ 3 ∣ Nat.card D := by
    intro h3D
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨d, hd⟩ := exists_prime_orderOf_dvd_card' 3 h3D
    have hd3 : (d : StatedSp 2 F) ^ 3 = 1 := by
      have h1 := pow_orderOf_eq_one d
      rw [hd] at h1
      rw [← Subgroup.coe_pow, h1, Subgroup.coe_one]
    have hpd : proj 2 F d ∈ Y := hDmap ▸ ⟨d, d.2, rfl⟩
    have hpd1 : proj 2 F d = 1 :=
      eq_one_of_pow_three_of_not_three_dvd hY3 hpd (by rw [← map_pow, hd3, map_one])
    have hdz : (d : StatedSp 2 F) ∈ spScalars 2 F := by
      rw [← ker_proj]
      exact hpd1
    have hd2 := sq_eq_one_of_mem_spScalars hdz
    have hd1 : (d : StatedSp 2 F) = 1 := by
      calc (d : StatedSp 2 F) = (d : StatedSp 2 F) ^ 3 * ((d : StatedSp 2 F) ^ 2)⁻¹ := by group
        _ = 1 := by rw [hd3, hd2, inv_one, one_mul]
    rw [show d = 1 from Subtype.ext hd1, orderOf_one] at hd
    omega
  have hfix : ∀ y ∈ D, (MulAut.conj g).toMonoidHom y = y := by
    refine eq_of_mul_inv_mem_center hDp (MulAut.conj g).toMonoidHom fun y hy => ?_
    apply spScalars_le_center
    rw [← ker_proj, MonoidHom.mem_ker, map_mul, map_inv]
    have hyY : proj 2 F y ∈ Y := hDmap ▸ ⟨y, hy, rfl⟩
    have h1 := (hC _).mp (hYC hyY)
    rw [← hx, MulAut.conj_apply] at h1
    change proj 2 F (g * y * g⁻¹) * (proj 2 F y)⁻¹ = 1
    rw [map_mul, map_mul, map_inv, hgx, h1, mul_inv_cancel]
  set D' : Subgroup (GL V₄ F) := D.map (StatedSp 2 F).subtype with hD'
  have hD'bot : D' = ⊥ := by
    refine eq_bot_of_commute_of_mem_statedSp h3 g.2 hg3 hg1 D' ?_ ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      have h1 := congrArg Subtype.val (hfix y hy)
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_mul,
        Subgroup.coe_inv] at h1
      change (y : GL V₄ F) * (g : GL V₄ F) = (g : GL V₄ F) * (y : GL V₄ F)
      calc (y : GL V₄ F) * (g : GL V₄ F) =
          (g : GL V₄ F) * y * (g : GL V₄ F)⁻¹ * (g : GL V₄ F) := by rw [h1]
        _ = (g : GL V₄ F) * y := by group
    · exact Group.IsPerfect.map _
    · rwa [Subgroup.card_map_of_injective (StatedSp 2 F).subtype_injective]
  have hDbot : D = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective D (StatedSp 2 F).subtype_injective).mp hD'bot
  rw [← hDmap, hDbot, Subgroup.map_bot]

open CFSG.Assembly.RankThreeEven (projSp) in
theorem threePrimeB3_projSp_two_prime {p : ℕ} [Fact p.Prime]
    (hp3 : 3 < p) : ThreePrimeB3 (projSp 2 (GaloisField p 1)) :=
  threePrimeB3_of_mulEquiv (Sec4.projSpEquivStatedProj 2 (GaloisField p 1))
    (threePrimeB3_statedProj_sp4_prime hp3 (by
      rw [GaloisField.card p 1 one_ne_zero, pow_one]))

end CFSG.RankThree.PartTwo.Sec6.BThreeCensus
