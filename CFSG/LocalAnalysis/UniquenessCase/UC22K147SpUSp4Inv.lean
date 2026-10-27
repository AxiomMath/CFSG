module

public import CFSG.LocalAnalysis.UniquenessCase.UC22K148Aut
public import CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.FixedSpace
import CFSG.LocalAnalysis.UniquenessCase.UC22K148Vocab
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bDiagram

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.K147SpU

open CFSG.Open Subgroup
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.QuasithinUnique.Setup
open CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations

variable {G : Type} [Group G]

theorem exists_odd_of_diagram {L : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) (e : ↥L ≃* antiSp K) {g : G}
    (hg : ActsNontrivOnDiagramIn L g) :
    ∃ (h : antiSp K) (j : ℕ), j % 2 = 1 ∧ j < 2 * n ∧
      ∀ x x' : ↥L, (x' : G) = g * x * g⁻¹ → e x' = h * (minorAut K ^ j) (e x) * h⁻¹ := by
  obtain ⟨-, θ, hθ, hnot⟩ := hg
  have hZ : Subgroup.center ↥L = ⊥ := K148.AutAux.center_eq_bot_of_equiv_antiSp e
  let κ : ↥L ⧸ Subgroup.center ↥L ≃* ↥L :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have hκ : ∀ x : ↥L, κ.symm x = QuotientGroup.mk x := fun x => by
    apply κ.injective
    rw [MulEquiv.apply_symm_apply]
    rfl
  let ε : ↥L ⧸ Subgroup.center ↥L ≃* antiSp K := κ.trans e
  have hθ' : ∀ x x' : ↥L, (x' : G) = g * x * g⁻¹ → MulAut.congr ε θ (e x) = e x' := by
    intro x x' hx
    have h0 : MulAut.congr ε θ (e x) = ε (θ (ε.symm (e x))) := rfl
    have h1 : ε.symm (e x) = QuotientGroup.mk x := by
      rw [MulEquiv.symm_trans_apply, MulEquiv.symm_apply_apply, hκ]
    rw [h0, h1, hθ x x' hx]
    show e (κ (QuotientGroup.mk x')) = e x'
    rw [← hκ x', MulEquiv.apply_symm_apply]
  obtain ⟨h, j, hj2, hj⟩ := X7b.aut_eq_conj_mul_pow hn hK (MulAut.congr ε θ)
  rcases Nat.even_or_odd j with hev | hodd
  · exfalso
    obtain ⟨k, hk⟩ := hev
    apply hnot
    rw [← uc22p22wi_isInnDiagFieldAut_congr ε θ, hj, hk, ← two_mul]
    exact K148.AutAux.isInnDiagFieldAut_conj_mul_pow_even hn hK h k
  · refine ⟨h, j, Nat.odd_iff.mp hodd, hj2, fun x x' hx => ?_⟩
    rw [← hθ' x x' hx, hj, MulAut.mul_apply, MulAut.conj_apply]

theorem three_mul_le_finrank_range_of_diagram {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) G V) (hρ : Function.Injective ρ) {L : Subgroup G} {n : ℕ}
    (hSp : IsSp4 ↥L n) {g : G} (hg : ActsNontrivOnDiagramIn L g) {z : G} (hz : z ∈ L) (hz2 : z * z = 1)
    (hz1 : z ≠ 1) :
    3 * n ≤ Module.finrank (ZMod 2) (LinearMap.range ((ρ z : V →ₗ[ZMod 2] V) - 1)) := by
  obtain ⟨hn, K, _, _, _, hK, ⟨e⟩⟩ := K148.exists_antiSp_of_isSp4 hSp
  obtain ⟨h, j, hjodd, hj, hconj⟩ := exists_odd_of_diagram (by omega) hK e hg
  have hgN : g ∈ normalizer (L : Set G) := hg.1
  let π : Representation (ZMod 2) (antiSp K) V := ρ.comp (L.subtype.comp e.symm.toMonoidHom)
  have hπ : ∀ x, π x = ρ ((e.symm x : ↥L) : G) := fun x => rfl
  have hπ1 : ∃ x, π x ≠ 1 := by
    have : Nontrivial ↥L := (K148.isSimpleGroup_of_isSp4 hSp).toNontrivial
    obtain ⟨x, hx⟩ := exists_ne (1 : ↥L)
    refine ⟨e x, fun h1 => hx ?_⟩
    rw [hπ, MulEquiv.symm_apply_apply] at h1
    exact Subtype.ext (hρ (h1.trans (map_one ρ).symm))
  have hb : ∀ (x : antiSp K) (w : V), X7b.repLinEquiv ρ g (π x ((X7b.repLinEquiv ρ g).symm w)) =
      π (h * (minorAut K ^ j) x * h⁻¹) w := by
    intro x w
    have hx' : ((e.symm (h * (minorAut K ^ j) x * h⁻¹) : ↥L) : G) = g * (e.symm x : G) * g⁻¹ := by
      have := hconj (e.symm x)
        ⟨g * (e.symm x : G) * g⁻¹, (mem_normalizer_iff.mp hgN _).mp (e.symm x).2⟩ rfl
      rw [MulEquiv.apply_symm_apply] at this
      rw [← this, MulEquiv.symm_apply_apply]
    show ρ g (ρ (e.symm x : G) (ρ g⁻¹ w)) = ρ (e.symm (h * (minorAut K ^ j) x * h⁻¹) : G) w
    rw [hx', map_mul, map_mul]
    rfl
  have hFc : Fintype.card K = 2 ^ n := by rw [← Nat.card_eq_fintype_card]; exact hK
  have hz₀2 : e ⟨z, hz⟩ * e ⟨z, hz⟩ = 1 := by
    rw [← map_mul, show (⟨z, hz⟩ : ↥L) * ⟨z, hz⟩ = 1 from Subtype.ext hz2, map_one]
  have hz₀1 : e ⟨z, hz⟩ ≠ 1 := fun h1 => hz1 (congrArg Subtype.val (e.map_eq_one_iff.mp h1))
  have hπz : π (e ⟨z, hz⟩) = ρ z := by rw [hπ, MulEquiv.symm_apply_apply]
  have := (X7b.binary_diagram_stable_modules_have_large_inner_involution_ranks hn hFc π hπ1
    (X7b.repLinEquiv ρ g) h hjodd hj hb hz₀2 hz₀1).1
  rwa [hπz] at this

end CFSG.LocalAnalysis.UniquenessCase.UC22.K147SpU
