module

public import CFSG.RankThree.PartTwo.Sec12.Hering129LOTwoL3Defs
public import CFSG.RankThree.PartTwo.Sec4.Statements
public import CFSG.RankThree.PartTwo.Sec4.LThreePiDefs
import CFSG.RankThree.PartTwo.Sec13.Item138NMod9
import CFSG.RankThree.PartTwo.Sec13.Item138ProofExists
import CFSG.RankThree.PartTwo.Sec4.LThreePiHessian
import CFSG.RankThree.PartTwo.Sec17.Item17Res7ProofL3TwoMod
import CFSG.Models.PGLSimple

public section

namespace CFSG.RankThree.PartTwo.Sec12.Hering129L.OTwoL3

open CFSG.Assembly.RankThreeEven (projImage)
open Matrix (ProjGenLinGroup)
open CFSG.RankThree.PartTwo.Sec4 (slPi PiField ModThree diagTau cycThree)

section Model

variable {π : Bool} {p f : ℕ} {K : Type} [Field K]

theorem mod_e9Q8_projImage (hK : PiField π p f K) (hq : ModThree π (p ^ f)) :
    E9Q8 (projImage (slPi π 3 (p ^ f) K)) := by
  have hπ : π = false → CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K :=
    fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  obtain ⟨τ, hτ, hτ1⟩ := Sec4.exists_tau hK hq
  have h3 := hK.three_ne_zero hq
  have hs := Sec4.one_add_tau_add_sq hτ hτ1
  have hFS := Sec4.fourierGL_mem_slPi hK hq hτ h3 hs
  have hNS := Sec4.conj_mem_slPi hπ (Sec4.phaseGL_mem_glPi hK hq hτ) hFS
  set x₁ : projImage (slPi π 3 (p ^ f) K) :=
    ⟨_, Subgroup.mem_map_of_mem _ (Sec4.diagTau_mem_slPi hπ hq' hτ)⟩
  set x₂ : projImage (slPi π 3 (p ^ f) K) :=
    ⟨_, Subgroup.mem_map_of_mem _ (Sec4.cycThree_mem_slPi hπ)⟩
  set n₁ : projImage (slPi π 3 (p ^ f) K) := ⟨_, Subgroup.mem_map_of_mem _ hFS⟩
  set n₂ : projImage (slPi π 3 (p ^ f) K) := ⟨_, Subgroup.mem_map_of_mem _ hNS⟩
  have h1 : x₁ ^ 3 = 1 := Subtype.ext (by
    change ProjGenLinGroup.mk (diagTau hτ) ^ 3 = 1
    rw [← map_pow, Sec4.diagTau_pow_three hτ, map_one])
  have h2 : x₂ ^ 3 = 1 := Subtype.ext (by
    change ProjGenLinGroup.mk (cycThree : GL (Fin 3) K) ^ 3 = 1
    rw [← map_pow, Sec4.cycThree_pow_three, map_one])
  have h12 : x₁ * x₂ = x₂ * x₁ := Subtype.ext (Sec4.mk_diagTau_cycThree hτ)
  have hx1 : x₁ ≠ 1 := fun h =>
    Sec13.Item138Proof.mk_diagTau_ne_one hτ hτ1 (congrArg Subtype.val h)
  have hx2 : x₂ ∉ Subgroup.zpowers x₁ := fun h => by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    exact Sec13.Item138Proof.mk_cycThree_not_mem_zpowers hτ
      (Subgroup.mem_zpowers_iff.mpr ⟨k, congrArg Subtype.val hk⟩)
  have r11 : n₁ * x₁ * n₁⁻¹ = x₂⁻¹ := Subtype.ext (Sec4.mk_fourier_diagTau hτ h3 hs)
  have r12 : n₁ * x₂ * n₁⁻¹ = x₁ := Subtype.ext (Sec4.mk_fourier_cycThree hτ h3 hs)
  have r21 : n₂ * x₁ * n₂⁻¹ = x₂⁻¹ * x₁⁻¹ := Subtype.ext (Sec4.mk_conjFourier_diagTau hτ h3 hs)
  have r22 : n₂ * x₂ * n₂⁻¹ = x₁ * x₂ * x₁ := Subtype.ext (Sec4.mk_conjFourier_cycThree hτ h3 hs)
  have hsq : x₁ * x₁ = x₁⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_three', h1])
  refine ⟨x₁, x₂, n₁, n₂, h1, h2, h12, hx1, hx2, r11, r12, ?_, ?_⟩
  · rw [r21, ← mul_inv_rev, h12, mul_inv_rev]
  · rw [r22, mul_assoc, ← h12, ← mul_assoc, hsq]

open Sec17.Proof17Res7 in
theorem mod_fourGroup_projImage (hK : PiField π p f K) (hp2 : p ≠ 2) :
    FourGroup (projImage (slPi π 3 (p ^ f) K)) := by
  refine ⟨tM hK hp2 _ isTInv_tOne, tM hK hp2 _ isTInv_tTwo, tM_sq hK hp2 isTInv_tOne,
    tM_sq hK hp2 isTInv_tTwo, tM_ne_one hK hp2 isTInv_tOne, tM_ne_one hK hp2 isTInv_tTwo,
    fun h => ?_, ?_⟩
  · apply tM_ne_one hK hp2 isTInv_tThree
    rw [← tM_one_mul_tM_two, h, ← sq, tM_sq]
  · exact Subtype.ext (by
      change ProjGenLinGroup.mk (tOne K) * ProjGenLinGroup.mk (tTwo K) =
        ProjGenLinGroup.mk (tTwo K) * ProjGenLinGroup.mk (tOne K)
      rw [← map_mul, ← map_mul, tOne_mul_tTwo_comm])

end Model

theorem e9Q8_of_isoLThreePi {L : Type} [Group L] {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e)
    (h : Sec4.IsoLThreePi L p e) : E9Q8 L := by
  obtain ⟨π, K, _, hK, hq, ⟨φ⟩⟩ := Sec13.exists_projImage_model he h
  exact E9Q8.of_mulEquiv φ.symm (mod_e9Q8_projImage hK hq)

theorem fourGroup_of_isoLThreePi {L : Type} [Group L] {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e)
    (hp2 : p ≠ 2) (h : Sec4.IsoLThreePi L p e) : FourGroup L := by
  obtain ⟨π, K, _, hK, -, ⟨φ⟩⟩ := Sec13.exists_projImage_model he h
  exact FourGroup.of_mulEquiv φ.symm (mod_fourGroup_projImage hK hp2)

theorem isSimpleGroup_of_isoLThreePi {L : Type} [Group L] {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e)
    (hp2 : p ≠ 2) (h : Sec4.IsoLThreePi L p e) : IsSimpleGroup L := by
  rcases h with ⟨-, ⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩
  · haveI := CFSG.PGLModel.isSimpleGroup_projSL_of_two_le (n := 3) (GaloisField p e)
      (by norm_num) (Or.inl (by norm_num)) (Or.inl (by norm_num))
    exact φ.isSimpleGroup
  · have hp : p.Prime := Fact.out
    have hq : p ^ e ≠ 2 := by
      have h2 := hp.two_le
      have hpe : p ≤ p ^ e := Nat.le_self_pow (by omega) p
      omega
    haveI := CFSG.PGLModel.isSimpleGroup_projSU_of_admissible (n := 3) (p := p) (f := e)
      ⟨hp, he, le_rfl, fun h => hq (Prod.mk.inj h).2⟩
    exact φ.isSimpleGroup

end CFSG.RankThree.PartTwo.Sec12.Hering129L.OTwoL3
